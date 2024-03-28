/*-------------------------------------------------------------------------
 *
 * multirangetypes_selfuncs.c
 *	  Functions for selectivity estimation of multirange operators
 *
 * Estimates are based on histograms of lower and upper bounds, and the
 * fraction of empty multiranges.
 *
 * Portions Copyright (c) 1996-2024, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/utils/adt/multirangetypes_selfuncs.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include <math.h>

#include "access/htup_details.h"
#include "catalog/pg_operator.h"
#include "catalog/pg_statistic.h"
#include "catalog/pg_type.h"
#include "utils/float.h"
#include "utils/fmgrprotos.h"
#include "utils/lsyscache.h"
#include "utils/rangetypes.h"
#include "utils/multirangetypes.h"
#include "utils/selfuncs.h"
#include "utils/typcache.h"

static double calc_multirangesel(TypeCacheEntry *typcache,
								 VariableStatData *vardata,
								 const MultirangeType *constval, Oid operator);
static double default_multirange_selectivity(Oid operator);
static double calc_hist_selectivity(TypeCacheEntry *typcache,
									VariableStatData *vardata,
									const MultirangeType *constval,
									Oid operator);

/*
 * Returns a default selectivity estimate for given operator, when we don't
 * have statistics or cannot use them for some reason.
 */
static double
default_multirange_selectivity(Oid operator)
{
	switch (operator)
	{
		case OID_MULTIRANGE_OVERLAPS_MULTIRANGE_OP:
		case OID_MULTIRANGE_OVERLAPS_RANGE_OP:
		case OID_RANGE_OVERLAPS_MULTIRANGE_OP:
			return 0.01;

		case OID_RANGE_CONTAINS_MULTIRANGE_OP:
		case OID_RANGE_MULTIRANGE_CONTAINED_OP:
		case OID_MULTIRANGE_CONTAINS_RANGE_OP:
		case OID_MULTIRANGE_CONTAINS_MULTIRANGE_OP:
		case OID_MULTIRANGE_RANGE_CONTAINED_OP:
		case OID_MULTIRANGE_MULTIRANGE_CONTAINED_OP:
			return 0.005;

		case OID_MULTIRANGE_CONTAINS_ELEM_OP:
		case OID_MULTIRANGE_ELEM_CONTAINED_OP:

			/*
			 * "multirange @> elem" is more or less identical to a scalar
			 * inequality "A >= b AND A <= c".
			 */
			return DEFAULT_MULTIRANGE_INEQ_SEL;

		case OID_MULTIRANGE_LESS_OP:
		case OID_MULTIRANGE_LESS_EQUAL_OP:
		case OID_MULTIRANGE_GREATER_OP:
		case OID_MULTIRANGE_GREATER_EQUAL_OP:
		case OID_MULTIRANGE_LEFT_RANGE_OP:
		case OID_MULTIRANGE_LEFT_MULTIRANGE_OP:
		case OID_RANGE_LEFT_MULTIRANGE_OP:
		case OID_MULTIRANGE_RIGHT_RANGE_OP:
		case OID_MULTIRANGE_RIGHT_MULTIRANGE_OP:
		case OID_RANGE_RIGHT_MULTIRANGE_OP:
		case OID_MULTIRANGE_OVERLAPS_LEFT_RANGE_OP:
		case OID_RANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
		case OID_MULTIRANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
		case OID_MULTIRANGE_OVERLAPS_RIGHT_RANGE_OP:
		case OID_RANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
		case OID_MULTIRANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
			/* these are similar to regular scalar inequalities */
			return DEFAULT_INEQ_SEL;

		default:

			/*
			 * all multirange operators should be handled above, but just in
			 * case
			 */
			return 0.01;
	}
}

/*
 * multirangesel -- restriction selectivity for multirange operators
 */
Datum
multirangesel(PG_FUNCTION_ARGS)
{
	PlannerInfo *root = (PlannerInfo *) PG_GETARG_POINTER(0);
	Oid			operator = PG_GETARG_OID(1);
	List	   *args = (List *) PG_GETARG_POINTER(2);
	int			varRelid = PG_GETARG_INT32(3);
	VariableStatData vardata;
	Node	   *other;
	bool		varonleft;
	Selectivity selec;
	TypeCacheEntry *typcache = NULL;
	MultirangeType *constmultirange = NULL;
	RangeType  *constrange = NULL;

	/*
	 * If expression is not (variable op something) or (something op
	 * variable), then punt and return a default estimate.
	 */
	if (!get_restriction_variable(root, args, varRelid,
								  &vardata, &other, &varonleft))
		PG_RETURN_FLOAT8(default_multirange_selectivity(operator));

	/*
	 * Can't do anything useful if the something is not a constant, either.
	 */
	if (!IsA(other, Const))
	{
		ReleaseVariableStats(vardata);
		PG_RETURN_FLOAT8(default_multirange_selectivity(operator));
	}

	/*
	 * All the multirange operators are strict, so we can cope with a NULL
	 * constant right away.
	 */
	if (((Const *) other)->constisnull)
	{
		ReleaseVariableStats(vardata);
		PG_RETURN_FLOAT8(0.0);
	}

	/*
	 * If var is on the right, commute the operator, so that we can assume the
	 * var is on the left in what follows.
	 */
	if (!varonleft)
	{
		/* we have other Op var, commute to make var Op other */
		operator = get_commutator(operator);
		if (!operator)
		{
			/* Use default selectivity (should we raise an error instead?) */
			ReleaseVariableStats(vardata);
			PG_RETURN_FLOAT8(default_multirange_selectivity(operator));
		}
	}

	/*
	 * OK, there's a Var and a Const we're dealing with here.  We need the
	 * Const to be of same multirange type as the column, else we can't do
	 * anything useful. (Such cases will likely fail at runtime, but here we'd
	 * rather just return a default estimate.)
	 *
	 * If the operator is "multirange @> element", the constant should be of
	 * the element type of the multirange column. Convert it to a multirange
	 * that includes only that single point, so that we don't need special
	 * handling for that in what follows.
	 */
	if (operator == OID_MULTIRANGE_CONTAINS_ELEM_OP)
	{
		typcache = multirange_get_typcache(fcinfo, vardata.vartype);

		if (((Const *) other)->consttype == typcache->rngtype->rngelemtype->type_id)
		{
			RangeBound	lower,
						upper;

			lower.inclusive = true;
			lower.val = ((Const *) other)->constvalue;
			lower.infinite = false;
			lower.lower = true;
			upper.inclusive = true;
			upper.val = ((Const *) other)->constvalue;
			upper.infinite = false;
			upper.lower = false;
			constrange = range_serialize(typcache->rngtype, &lower, &upper,
										 false, NULL);
			constmultirange = make_multirange(typcache->type_id, typcache->rngtype,
											  1, &constrange);
		}
	}
	else if (operator == OID_RANGE_MULTIRANGE_CONTAINED_OP ||
			 operator == OID_MULTIRANGE_CONTAINS_RANGE_OP ||
			 operator == OID_MULTIRANGE_OVERLAPS_RANGE_OP ||
			 operator == OID_MULTIRANGE_OVERLAPS_LEFT_RANGE_OP ||
			 operator == OID_MULTIRANGE_OVERLAPS_RIGHT_RANGE_OP ||
			 operator == OID_MULTIRANGE_LEFT_RANGE_OP ||
			 operator == OID_MULTIRANGE_RIGHT_RANGE_OP)
	{
		/*
		 * Promote a range in "multirange OP range" just like we do an element
		 * in "multirange OP element".
		 */
		typcache = multirange_get_typcache(fcinfo, vardata.vartype);
		if (((Const *) other)->consttype == typcache->rngtype->type_id)
		{
			constrange = DatumGetRangeTypeP(((Const *) other)->constvalue);
			constmultirange = make_multirange(typcache->type_id, typcache->rngtype,
											  1, &constrange);
		}
	}
	else if (operator == OID_RANGE_OVERLAPS_MULTIRANGE_OP ||
			 operator == OID_RANGE_OVERLAPS_LEFT_MULTIRANGE_OP ||
			 operator == OID_RANGE_OVERLAPS_RIGHT_MULTIRANGE_OP ||
			 operator == OID_RANGE_LEFT_MULTIRANGE_OP ||
			 operator == OID_RANGE_RIGHT_MULTIRANGE_OP ||
			 operator == OID_RANGE_CONTAINS_MULTIRANGE_OP ||
			 operator == OID_MULTIRANGE_ELEM_CONTAINED_OP ||
			 operator == OID_MULTIRANGE_RANGE_CONTAINED_OP)
	{
		/*
		 * Here, the Var is the elem/range, not the multirange.  For now we
		 * just punt and return the default estimate.  In future we could
		 * disassemble the multirange constant to do something more
		 * intelligent.
		 */
	}
	else if (((Const *) other)->consttype == vardata.vartype)
	{
		/* Both sides are the same multirange type */
		typcache = multirange_get_typcache(fcinfo, vardata.vartype);

		constmultirange = DatumGetMultirangeTypeP(((Const *) other)->constvalue);
	}

	/*
	 * If we got a valid constant on one side of the operator, proceed to
	 * estimate using statistics. Otherwise punt and return a default constant
	 * estimate.  Note that calc_multirangesel need not handle
	 * OID_MULTIRANGE_*_CONTAINED_OP.
	 */
	if (constmultirange)
		selec = calc_multirangesel(typcache, &vardata, constmultirange, operator);
	else
		selec = default_multirange_selectivity(operator);

	ReleaseVariableStats(vardata);

	CLAMP_PROBABILITY(selec);

	PG_RETURN_FLOAT8((float8) selec);
}

static double
calc_multirangesel(TypeCacheEntry *typcache, VariableStatData *vardata,
				   const MultirangeType *constval, Oid operator)
{
	double		hist_selec;
	double		selec;
	float4		empty_frac,
				null_frac;

	/*
	 * First look up the fraction of NULLs and empty multiranges from
	 * pg_statistic.
	 */
	if (HeapTupleIsValid(vardata->statsTuple))
	{
		Form_pg_statistic stats;
		AttStatsSlot sslot;

		stats = (Form_pg_statistic) GETSTRUCT(vardata->statsTuple);
		null_frac = stats->stanullfrac;

		/* Try to get fraction of empty multiranges */
		if (get_attstatsslot(&sslot, vardata->statsTuple,
							 STATISTIC_KIND_RANGE_LENGTH_HISTOGRAM,
							 InvalidOid,
							 ATTSTATSSLOT_NUMBERS))
		{
			if (sslot.nnumbers != 1)
				elog(ERROR, "invalid empty fraction statistic");	/* shouldn't happen */
			empty_frac = sslot.numbers[0];
			free_attstatsslot(&sslot);
		}
		else
		{
			/* No empty fraction statistic. Assume no empty ranges. */
			empty_frac = 0.0;
		}
	}
	else
	{
		/*
		 * No stats are available. Follow through the calculations below
		 * anyway, assuming no NULLs and no empty multiranges. This still
		 * allows us to give a better-than-nothing estimate based on whether
		 * the constant is an empty multirange or not.
		 */
		null_frac = 0.0;
		empty_frac = 0.0;
	}

	if (MultirangeIsEmpty(constval))
	{
		/*
		 * An empty multirange matches all multiranges, all empty multiranges,
		 * or nothing, depending on the operator
		 */
		switch (operator)
		{
				/* these return false if either argument is empty */
			case OID_MULTIRANGE_OVERLAPS_RANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_LEFT_RANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_RIGHT_RANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
			case OID_MULTIRANGE_LEFT_RANGE_OP:
			case OID_MULTIRANGE_LEFT_MULTIRANGE_OP:
			case OID_MULTIRANGE_RIGHT_RANGE_OP:
			case OID_MULTIRANGE_RIGHT_MULTIRANGE_OP:
				/* nothing is less than an empty multirange */
			case OID_MULTIRANGE_LESS_OP:
				selec = 0.0;
				break;

				/*
				 * only empty multiranges can be contained by an empty
				 * multirange
				 */
			case OID_RANGE_MULTIRANGE_CONTAINED_OP:
			case OID_MULTIRANGE_MULTIRANGE_CONTAINED_OP:
				/* only empty ranges are <= an empty multirange */
			case OID_MULTIRANGE_LESS_EQUAL_OP:
				selec = empty_frac;
				break;

				/* everything contains an empty multirange */
			case OID_MULTIRANGE_CONTAINS_RANGE_OP:
			case OID_MULTIRANGE_CONTAINS_MULTIRANGE_OP:
				/* everything is >= an empty multirange */
			case OID_MULTIRANGE_GREATER_EQUAL_OP:
				selec = 1.0;
				break;

				/* all non-empty multiranges are > an empty multirange */
			case OID_MULTIRANGE_GREATER_OP:
				selec = 1.0 - empty_frac;
				break;

				/* an element cannot be empty */
			case OID_MULTIRANGE_CONTAINS_ELEM_OP:

				/* filtered out by multirangesel() */
			case OID_RANGE_OVERLAPS_MULTIRANGE_OP:
			case OID_RANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
			case OID_RANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
			case OID_RANGE_LEFT_MULTIRANGE_OP:
			case OID_RANGE_RIGHT_MULTIRANGE_OP:
			case OID_RANGE_CONTAINS_MULTIRANGE_OP:
			case OID_MULTIRANGE_ELEM_CONTAINED_OP:
			case OID_MULTIRANGE_RANGE_CONTAINED_OP:

			default:
				elog(ERROR, "unexpected operator %u", operator);
				selec = 0.0;	/* keep compiler quiet */
				break;
		}
	}
	else
	{
		/*
		 * Calculate selectivity using bound histograms. If that fails for
		 * some reason, e.g no histogram in pg_statistic, use the default
		 * constant estimate for the fraction of non-empty values. This is
		 * still somewhat better than just returning the default estimate,
		 * because this still takes into account the fraction of empty and
		 * NULL tuples, if we had statistics for them.
		 */
		hist_selec = calc_hist_selectivity(typcache, vardata, constval,
										   operator);
		if (hist_selec < 0.0)
			hist_selec = default_multirange_selectivity(operator);

		/*
		 * Now merge the results for the empty multiranges and histogram
		 * calculations, realizing that the histogram covers only the
		 * non-null, non-empty values.
		 */
		if (operator == OID_RANGE_MULTIRANGE_CONTAINED_OP ||
			operator == OID_MULTIRANGE_MULTIRANGE_CONTAINED_OP)
		{
			/* empty is contained by anything non-empty */
			selec = (1.0 - empty_frac) * hist_selec + empty_frac;
		}
		else
		{
			/* with any other operator, empty Op non-empty matches nothing */
			selec = (1.0 - empty_frac) * hist_selec;
		}
	}

	/* all multirange operators are strict */
	selec *= (1.0 - null_frac);

	/* result should be in range, but make sure... */
	CLAMP_PROBABILITY(selec);

	return selec;
}

/*
 * Calculate multirange operator selectivity using histograms of multirange bounds.
 *
 * This estimate is for the portion of values that are not empty and not
 * NULL.
 */
static double
calc_hist_selectivity(TypeCacheEntry *typcache, VariableStatData *vardata,
					  const MultirangeType *constval, Oid operator)
{
	TypeCacheEntry *rng_typcache = typcache->rngtype;
	AttStatsSlot hslot;
	AttStatsSlot lslot;
	int			nhist;
	RangeBound *hist_lower;
	RangeBound *hist_upper;
	int			i;
	RangeBound	const_lower;
	RangeBound	const_upper;
	RangeBound	tmp;
	double		hist_selec;

	/* Can't use the histogram with insecure multirange support functions */
	if (!statistic_proc_security_check(vardata,
									   rng_typcache->rng_cmp_proc_finfo.fn_oid))
		return -1;
	if (OidIsValid(rng_typcache->rng_subdiff_finfo.fn_oid) &&
		!statistic_proc_security_check(vardata,
									   rng_typcache->rng_subdiff_finfo.fn_oid))
		return -1;

	/* Try to get histogram of ranges */
	if (!(HeapTupleIsValid(vardata->statsTuple) &&
		  get_attstatsslot(&hslot, vardata->statsTuple,
						   STATISTIC_KIND_BOUNDS_HISTOGRAM, InvalidOid,
						   ATTSTATSSLOT_VALUES)))
		return -1.0;

	/* check that it's a histogram, not just a dummy entry */
	if (hslot.nvalues < 2)
	{
		free_attstatsslot(&hslot);
		return -1.0;
	}

	/*
	 * Convert histogram of ranges into histograms of its lower and upper
	 * bounds.
	 */
	nhist = hslot.nvalues;
	hist_lower = (RangeBound *) palloc(sizeof(RangeBound) * nhist);
	hist_upper = (RangeBound *) palloc(sizeof(RangeBound) * nhist);
	for (i = 0; i < nhist; i++)
	{
		bool		empty;

		range_deserialize(rng_typcache, DatumGetRangeTypeP(hslot.values[i]),
						  &hist_lower[i], &hist_upper[i], &empty);
		/* The histogram should not contain any empty ranges */
		if (empty)
			elog(ERROR, "bounds histogram contains an empty range");
	}

	/* @> and @< also need a histogram of range lengths */
	if (operator == OID_MULTIRANGE_CONTAINS_RANGE_OP ||
		operator == OID_MULTIRANGE_CONTAINS_MULTIRANGE_OP ||
		operator == OID_MULTIRANGE_RANGE_CONTAINED_OP ||
		operator == OID_MULTIRANGE_MULTIRANGE_CONTAINED_OP)
	{
		if (!(HeapTupleIsValid(vardata->statsTuple) &&
			  get_attstatsslot(&lslot, vardata->statsTuple,
							   STATISTIC_KIND_RANGE_LENGTH_HISTOGRAM,
							   InvalidOid,
							   ATTSTATSSLOT_VALUES)))
		{
			free_attstatsslot(&hslot);
			return -1.0;
		}

		/* check that it's a histogram, not just a dummy entry */
		if (lslot.nvalues < 2)
		{
			free_attstatsslot(&lslot);
			free_attstatsslot(&hslot);
			return -1.0;
		}
	}
	else
		memset(&lslot, 0, sizeof(lslot));

	/* Extract the bounds of the constant value. */
	Assert(constval->rangeCount > 0);
	multirange_get_bounds(rng_typcache, constval, 0,
						  &const_lower, &tmp);
	multirange_get_bounds(rng_typcache, constval, constval->rangeCount - 1,
						  &tmp, &const_upper);

	/*
	 * Calculate selectivity comparing the lower or upper bound of the
	 * constant with the histogram of lower or upper bounds.
	 */
	switch (operator)
	{
		case OID_MULTIRANGE_LESS_OP:

			/*
			 * The regular b-tree comparison operators (<, <=, >, >=) compare
			 * the lower bounds first, and the upper bounds for values with
			 * equal lower bounds. Estimate that by comparing the lower bounds
			 * only. This gives a fairly accurate estimate assuming there
			 * aren't many rows with a lower bound equal to the constant's
			 * lower bound.
			 */
			hist_selec =
				calc_hist_selectivity_scalar(rng_typcache, &const_lower,
											 hist_lower, nhist, false);
			break;

		case OID_MULTIRANGE_LESS_EQUAL_OP:
			hist_selec =
				calc_hist_selectivity_scalar(rng_typcache, &const_lower,
											 hist_lower, nhist, true);
			break;

		case OID_MULTIRANGE_GREATER_OP:
			hist_selec =
				1 - calc_hist_selectivity_scalar(rng_typcache, &const_lower,
												 hist_lower, nhist, false);
			break;

		case OID_MULTIRANGE_GREATER_EQUAL_OP:
			hist_selec =
				1 - calc_hist_selectivity_scalar(rng_typcache, &const_lower,
												 hist_lower, nhist, true);
			break;

		case OID_MULTIRANGE_LEFT_RANGE_OP:
		case OID_MULTIRANGE_LEFT_MULTIRANGE_OP:
			/* var << const when upper(var) < lower(const) */
			hist_selec =
				calc_hist_selectivity_scalar(rng_typcache, &const_lower,
											 hist_upper, nhist, false);
			break;

		case OID_MULTIRANGE_RIGHT_RANGE_OP:
		case OID_MULTIRANGE_RIGHT_MULTIRANGE_OP:
			/* var >> const when lower(var) > upper(const) */
			hist_selec =
				1 - calc_hist_selectivity_scalar(rng_typcache, &const_upper,
												 hist_lower, nhist, true);
			break;

		case OID_MULTIRANGE_OVERLAPS_RIGHT_RANGE_OP:
		case OID_MULTIRANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
			/* compare lower bounds */
			hist_selec =
				1 - calc_hist_selectivity_scalar(rng_typcache, &const_lower,
												 hist_lower, nhist, false);
			break;

		case OID_MULTIRANGE_OVERLAPS_LEFT_RANGE_OP:
		case OID_MULTIRANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
			/* compare upper bounds */
			hist_selec =
				calc_hist_selectivity_scalar(rng_typcache, &const_upper,
											 hist_upper, nhist, true);
			break;

		case OID_MULTIRANGE_OVERLAPS_RANGE_OP:
		case OID_MULTIRANGE_OVERLAPS_MULTIRANGE_OP:
		case OID_MULTIRANGE_CONTAINS_ELEM_OP:

			/*
			 * A && B <=> NOT (A << B OR A >> B).
			 *
			 * Since A << B and A >> B are mutually exclusive events we can
			 * sum their probabilities to find probability of (A << B OR A >>
			 * B).
			 *
			 * "multirange @> elem" is equivalent to "multirange &&
			 * {[elem,elem]}". The caller already constructed the singular
			 * range from the element constant, so just treat it the same as
			 * &&.
			 */
			hist_selec =
				calc_hist_selectivity_scalar(rng_typcache,
											 &const_lower, hist_upper,
											 nhist, false);
			hist_selec +=
				(1.0 - calc_hist_selectivity_scalar(rng_typcache,
													&const_upper, hist_lower,
													nhist, true));
			hist_selec = 1.0 - hist_selec;
			break;

		case OID_MULTIRANGE_CONTAINS_RANGE_OP:
		case OID_MULTIRANGE_CONTAINS_MULTIRANGE_OP:
			hist_selec =
				calc_hist_selectivity_contains(rng_typcache, &const_lower,
											   &const_upper, hist_lower, nhist,
											   lslot.values, lslot.nvalues);
			break;

		case OID_MULTIRANGE_MULTIRANGE_CONTAINED_OP:
		case OID_RANGE_MULTIRANGE_CONTAINED_OP:
			if (const_lower.infinite)
			{
				/*
				 * Lower bound no longer matters. Just estimate the fraction
				 * with an upper bound <= const upper bound
				 */
				hist_selec =
					calc_hist_selectivity_scalar(rng_typcache, &const_upper,
												 hist_upper, nhist, true);
			}
			else if (const_upper.infinite)
			{
				hist_selec =
					1.0 - calc_hist_selectivity_scalar(rng_typcache, &const_lower,
													   hist_lower, nhist, false);
			}
			else
			{
				hist_selec =
					calc_hist_selectivity_contained(rng_typcache, &const_lower,
													&const_upper, hist_lower, nhist,
													lslot.values, lslot.nvalues);
			}
			break;

			/* filtered out by multirangesel() */
		case OID_RANGE_OVERLAPS_MULTIRANGE_OP:
		case OID_RANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
		case OID_RANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
		case OID_RANGE_LEFT_MULTIRANGE_OP:
		case OID_RANGE_RIGHT_MULTIRANGE_OP:
		case OID_RANGE_CONTAINS_MULTIRANGE_OP:
		case OID_MULTIRANGE_ELEM_CONTAINED_OP:
		case OID_MULTIRANGE_RANGE_CONTAINED_OP:

		default:
			elog(ERROR, "unknown multirange operator %u", operator);
			hist_selec = -1.0;	/* keep compiler quiet */
			break;
	}

	free_attstatsslot(&lslot);
	free_attstatsslot(&hslot);

	return hist_selec;
}

/*
 * multirangejoinsel -- join cardinality for multirange operators
 */
Datum
multirangejoinsel(PG_FUNCTION_ARGS)
{
	PlannerInfo *root = (PlannerInfo *) PG_GETARG_POINTER(0);
	Oid			operator = PG_GETARG_OID(1);
	List	   *args = (List *) PG_GETARG_POINTER(2);
	SpecialJoinInfo *sjinfo = (SpecialJoinInfo *) PG_GETARG_POINTER(4);
	VariableStatData vardata1,
				vardata2;
	AttStatsSlot hist1,
				hist2,
				sslot;
	bool		reversed;
	Selectivity selec;
	TypeCacheEntry *typcache = NULL,
			   *rng_typcache = NULL;
	Form_pg_statistic stats1,
				stats2;
	double		empty_frac1,
				empty_frac2,
				null_frac1,
				null_frac2;
	int			nhist1,
				nhist2;
	RangeBound *hist1_lower,
			   *hist1_upper,
			   *hist2_lower,
			   *hist2_upper;
	bool		empty;
	int			i;

	get_join_variables(root, args, sjinfo, &vardata1, &vardata2, &reversed);

	selec = default_multirange_selectivity(operator);

	/* get multirange type cache */
	if (type_is_multirange(vardata1.vartype))
		typcache = multirange_get_typcache(fcinfo, vardata1.vartype);
	else if (type_is_multirange(vardata2.vartype))
		typcache = multirange_get_typcache(fcinfo, vardata2.vartype);

	if (HeapTupleIsValid(vardata1.statsTuple) &&
		get_attstatsslot(&hist1, vardata1.statsTuple,
						 STATISTIC_KIND_BOUNDS_HISTOGRAM, InvalidOid,
						 ATTSTATSSLOT_VALUES) &&
		HeapTupleIsValid(vardata2.statsTuple) &&
		get_attstatsslot(&hist2, vardata2.statsTuple,
						 STATISTIC_KIND_BOUNDS_HISTOGRAM, InvalidOid,
						 ATTSTATSSLOT_VALUES) &&
		typcache)
	{

		/* Initialize underlying range type cache */
		rng_typcache = typcache->rngtype;

		/*
		 * First look up the fraction of NULLs and empty ranges from
		 * pg_statistic.
		 */
		stats1 = (Form_pg_statistic) GETSTRUCT(vardata1.statsTuple);
		stats2 = (Form_pg_statistic) GETSTRUCT(vardata2.statsTuple);

		null_frac1 = stats1->stanullfrac;
		null_frac2 = stats2->stanullfrac;

		/* Try to get fraction of empty ranges for the first variable */
		if (get_attstatsslot(&sslot, vardata1.statsTuple,
							 STATISTIC_KIND_RANGE_LENGTH_HISTOGRAM,
							 InvalidOid,
							 ATTSTATSSLOT_NUMBERS))
		{
			if (sslot.nnumbers != 1)	/* shouldn't happen */
				elog(ERROR, "invalid empty fraction statistic");
			empty_frac1 = sslot.numbers[0];
			free_attstatsslot(&sslot);
		}
		else
		{
			/* No empty fraction statistic. Assume no empty ranges. */
			empty_frac1 = 0.0;
		}

		/* Try to get fraction of empty ranges for the second variable */
		if (get_attstatsslot(&sslot, vardata2.statsTuple,
							 STATISTIC_KIND_RANGE_LENGTH_HISTOGRAM,
							 InvalidOid,
							 ATTSTATSSLOT_NUMBERS))
		{
			if (sslot.nnumbers != 1)	/* shouldn't happen */
				elog(ERROR, "invalid empty fraction statistic");
			empty_frac2 = sslot.numbers[0];
			free_attstatsslot(&sslot);
		}
		else
		{
			/* No empty fraction statistic. Assume no empty ranges. */
			empty_frac2 = 0.0;
		}

		/*
		 * Convert histograms of ranges into histograms of their lower and
		 * upper bounds for the first variable.
		 */
		nhist1 = hist1.nvalues;
		hist1_lower = (RangeBound *) palloc(sizeof(RangeBound) * nhist1);
		hist1_upper = (RangeBound *) palloc(sizeof(RangeBound) * nhist1);
		for (i = 0; i < nhist1; i++)
		{
			range_deserialize(rng_typcache, DatumGetRangeTypeP(hist1.values[i]),
							  &hist1_lower[i], &hist1_upper[i], &empty);
			/* The histogram should not contain any empty ranges */
			if (empty)
				elog(ERROR, "bounds histogram contains an empty range");
		}

		/*
		 * Convert histograms of ranges into histograms of their lower and
		 * upper bounds for the second variable.
		 */
		nhist2 = hist2.nvalues;
		hist2_lower = (RangeBound *) palloc(sizeof(RangeBound) * nhist2);
		hist2_upper = (RangeBound *) palloc(sizeof(RangeBound) * nhist2);
		for (i = 0; i < nhist2; i++)
		{
			range_deserialize(rng_typcache, DatumGetRangeTypeP(hist2.values[i]),
							  &hist2_lower[i], &hist2_upper[i], &empty);
			/* The histogram should not contain any empty ranges */
			if (empty)
				elog(ERROR, "bounds histogram contains an empty range");
		}

		switch (operator)
		{
			case OID_MULTIRANGE_OVERLAPS_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_RANGE_OP:
			case OID_RANGE_OVERLAPS_MULTIRANGE_OP:

				/*
				 * Selectivity of A && B = Selectivity of NOT( A << B || A >>
				 * B ) = 1 - Selectivity of (A.upper < B.lower) - Selectivity
				 * of (B.upper < A.lower)
				 */
				selec = 1;
				selec -= calc_hist_join_selectivity(rng_typcache,
													hist1_upper, nhist1,
													hist2_lower, nhist2);
				selec -= calc_hist_join_selectivity(rng_typcache,
													hist2_upper, nhist2,
													hist1_lower, nhist1);
				break;

			case OID_MULTIRANGE_LESS_EQUAL_OP:

				/*
				 * A <= B
				 *
				 * Start by comparing lower bounds and if they are equal
				 * compare upper bounds
				 *
				 * Negation of OID_RANGE_GREATER_OP.
				 *
				 * Overestimate by comparing only the lower bounds. Higher
				 * accuracy would require us to subtract P(lower1 = lower2) *
				 * P(upper1 > upper2)
				 */
				selec = 1 - calc_hist_join_selectivity(rng_typcache,
													   hist2_lower, nhist2,
													   hist1_lower, nhist1);
				break;

			case OID_MULTIRANGE_LESS_OP:

				/*
				 * A < B
				 *
				 * Start by comparing lower bounds and if they are equal
				 * compare upper bounds
				 *
				 * Underestimate by comparing only the lower bounds. Higher
				 * accuracy would require us to add P(lower1 = lower2) *
				 * P(upper1 < upper2)
				 */
				selec = calc_hist_join_selectivity(rng_typcache,
												   hist1_lower, nhist1,
												   hist2_lower, nhist2);
				break;

			case OID_MULTIRANGE_GREATER_EQUAL_OP:

				/*
				 * A >= B
				 *
				 * Start by comparing lower bounds and if they are equal
				 * compare upper bounds
				 *
				 * Negation of OID_RANGE_LESS_OP.
				 *
				 * Overestimate by comparing only the lower bounds. Higher
				 * accuracy would require us to add P(lower1 = lower2) *
				 * P(upper1 < upper2)
				 */
				selec = 1 - calc_hist_join_selectivity(rng_typcache,
													   hist1_lower, nhist1,
													   hist2_lower, nhist2);
				break;

			case OID_MULTIRANGE_GREATER_OP:

				/*
				 * A > B == B < A
				 *
				 * Start by comparing lower bounds and if they are equal
				 * compare upper bounds
				 *
				 * Underestimate by comparing only the lower bounds. Higher
				 * accuracy would require us to add P(lower1 = lower2) *
				 * P(upper1 > upper2)
				 */
				selec = calc_hist_join_selectivity(rng_typcache,
												   hist2_lower, nhist2,
												   hist1_lower, nhist1);
				break;

			case OID_MULTIRANGE_LEFT_MULTIRANGE_OP:
			case OID_MULTIRANGE_LEFT_RANGE_OP:
			case OID_RANGE_LEFT_MULTIRANGE_OP:
				/* var1 << var2 when upper(var1) < lower(var2) */
				selec = calc_hist_join_selectivity(rng_typcache,
												   hist1_upper, nhist1,
												   hist2_lower, nhist2);
				break;

			case OID_MULTIRANGE_RIGHT_MULTIRANGE_OP:
			case OID_MULTIRANGE_RIGHT_RANGE_OP:
			case OID_RANGE_RIGHT_MULTIRANGE_OP:
				/* var1 >> var2 when upper(var2) < lower(var1) */
				selec = calc_hist_join_selectivity(rng_typcache,
												   hist2_upper, nhist2,
												   hist1_lower, nhist1);
				break;

			case OID_MULTIRANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_LEFT_RANGE_OP:
			case OID_RANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
				/* var1 &< var2 when upper(var1) < upper(var2) */
				selec = calc_hist_join_selectivity(rng_typcache,
												   hist1_upper, nhist1,
												   hist2_upper, nhist2);
				break;

			case OID_MULTIRANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_RIGHT_RANGE_OP:
			case OID_RANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
				/* var1 &> var2 when lower(var2) < lower(var1) */
				selec = calc_hist_join_selectivity(rng_typcache,
												   hist2_lower, nhist2,
												   hist1_lower, nhist1);
				break;

			case OID_MULTIRANGE_MULTIRANGE_CONTAINED_OP:
			case OID_MULTIRANGE_RANGE_CONTAINED_OP:
			case OID_RANGE_MULTIRANGE_CONTAINED_OP:

				/*
				 * var1 <@ var2 is equivalent to lower(var2) <= lower(var1)
				 * and upper(var1) <= upper(var2)
				 *
				 * After negating both sides we get not( lower(var1) <
				 * lower(var2) ) and not( upper(var2) < upper(var1) ),
				 * respectively. Assuming independence, multiply both
				 * selectivities.
				 */
				selec = 1 - calc_hist_join_selectivity(rng_typcache,
													   hist1_lower, nhist1,
													   hist2_lower, nhist2);
				selec *= 1 - calc_hist_join_selectivity(rng_typcache,
														hist2_upper, nhist2,
														hist1_upper, nhist1);
				break;

			case OID_MULTIRANGE_CONTAINS_MULTIRANGE_OP:
			case OID_MULTIRANGE_CONTAINS_RANGE_OP:
			case OID_RANGE_CONTAINS_MULTIRANGE_OP:

				/*
				 * var1 @> var2 is equivalent to lower(var1) <= lower(var2)
				 * and upper(var2) <= upper(var1)
				 *
				 * After negating both sides we get not( lower(var2) <
				 * lower(var1) ) and not( upper(var1) < upper(var2) ),
				 * respectively. Assuming independence, multiply both
				 * selectivities.
				 */
				selec = 1 - calc_hist_join_selectivity(rng_typcache,
													   hist2_lower, nhist2,
													   hist1_lower, nhist1);
				selec *= 1 - calc_hist_join_selectivity(rng_typcache,
														hist1_upper, nhist1,
														hist2_upper, nhist2);
				break;

			case OID_MULTIRANGE_ADJACENT_MULTIRANGE_OP:
			case OID_MULTIRANGE_ADJACENT_RANGE_OP:
			case OID_RANGE_ADJACENT_MULTIRANGE_OP:

				/*
				 * just punt for now, estimation would require equality
				 * selectivity for bounds
				 */
			case OID_MULTIRANGE_CONTAINS_ELEM_OP:
			case OID_MULTIRANGE_ELEM_CONTAINED_OP:

				/*
				 * just punt for now, estimation would require extraction of
				 * histograms for the anyelement
				 */
			default:
				break;
		}


		/* the calculated selectivity only applies to non-empty (multi)ranges */
		selec *= (1 - empty_frac1) * (1 - empty_frac2);

		/*
		 * Depending on the operator, empty (multi)ranges might match
		 * different fractions of the result.
		 */
		switch (operator)
		{
			case OID_MULTIRANGE_LESS_OP:

				/*
				 * empty (multi)range < non-empty (multi)range
				 */
				selec += empty_frac1 * (1 - empty_frac2);
				break;

			case OID_MULTIRANGE_GREATER_OP:

				/*
				 * non-empty (multi)range > empty (multi)range
				 */
				selec += (1 - empty_frac1) * empty_frac2;
				break;

			case OID_MULTIRANGE_MULTIRANGE_CONTAINED_OP:
			case OID_MULTIRANGE_RANGE_CONTAINED_OP:
			case OID_RANGE_MULTIRANGE_CONTAINED_OP:

				/*
				 * empty (multi)range <@ any (multi)range
				 */
			case OID_MULTIRANGE_LESS_EQUAL_OP:

				/*
				 * empty (multi)range <= any (multi)range
				 */
				selec += empty_frac1;
				break;

			case OID_MULTIRANGE_CONTAINS_MULTIRANGE_OP:
			case OID_MULTIRANGE_CONTAINS_RANGE_OP:
			case OID_RANGE_CONTAINS_MULTIRANGE_OP:

				/*
				 * any (multi)range @> empty (multi)range
				 */
			case OID_MULTIRANGE_GREATER_EQUAL_OP:

				/*
				 * any (multi)range >= empty (multi)range
				 */
				selec += empty_frac2;
				break;

			case OID_MULTIRANGE_CONTAINS_ELEM_OP:
			case OID_MULTIRANGE_ELEM_CONTAINED_OP:
			case OID_MULTIRANGE_OVERLAPS_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_RANGE_OP:
			case OID_RANGE_OVERLAPS_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_LEFT_RANGE_OP:
			case OID_RANGE_OVERLAPS_LEFT_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
			case OID_MULTIRANGE_OVERLAPS_RIGHT_RANGE_OP:
			case OID_RANGE_OVERLAPS_RIGHT_MULTIRANGE_OP:
			case OID_MULTIRANGE_LEFT_MULTIRANGE_OP:
			case OID_MULTIRANGE_LEFT_RANGE_OP:
			case OID_RANGE_LEFT_MULTIRANGE_OP:
			case OID_MULTIRANGE_RIGHT_MULTIRANGE_OP:
			case OID_MULTIRANGE_RIGHT_RANGE_OP:
			case OID_RANGE_RIGHT_MULTIRANGE_OP:
			case OID_MULTIRANGE_ADJACENT_MULTIRANGE_OP:
			case OID_MULTIRANGE_ADJACENT_RANGE_OP:
			case OID_RANGE_ADJACENT_MULTIRANGE_OP:
			default:

				/*
				 * these operators always return false when an empty
				 * (multi)range is involved
				 */
				break;

		}

		/* all range operators are strict */
		selec *= (1 - null_frac1) * (1 - null_frac2);

		free_attstatsslot(&hist1);
		free_attstatsslot(&hist2);
	}

	ReleaseVariableStats(vardata1);
	ReleaseVariableStats(vardata2);

	CLAMP_PROBABILITY(selec);

	PG_RETURN_FLOAT8((float8) selec);

}
