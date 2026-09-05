# Formalization progress

Status legend: `open` (not started), `wip` (a subagent is working on it), `sorry` (stated and compiling, proof incomplete), `done` (compiles without `sorry`), `blocked` (waiting on a dependency).

Module layout: construction side under `Nikodym/Construction/` and `Nikodym/MultiQuadratic/`; lower-bound side under `Nikodym/LowerBound/`.

## Construction (upper bound) — `docs/nikodym_construction_lean_blueprint.md`

| Node | Module | Status | Notes |
| --- | --- | --- | --- |
| P01 product-complement criterion | `Construction/ProductCriterion.lean` | done | |
| S01 scaffold interface | `Construction/Scaffold.lean` | done | |
| S02 norm, injectivity, unit gap | `Construction/Scaffold.lean` | done | |
| S03 finite boxes and lattice count | `Construction/Scaffold.lean` | done | |
| D01 digit injectivity | `Construction/Digits.lean` | done | needs S02 |
| D02 decoding inequality | `Construction/Digits.lean` | done | needs S02 |
| Q01 integer parameters | `Construction/Parameters.lean` | done | |
| Q02 thresholds and root bounds | `Construction/Parameters.lean` | done | |
| C01 trace fiber | `Construction/Fibers.lean` | done | needs S03 |
| C02 energy fiber | `Construction/Fibers.lean` | wip | needs S03, D01, Q01 |
| T01 tangent lines | `Construction/Tangent.lean` | done | needs S, D, Q, C |
| E01 size of P | `Construction/Count.lean` | done | needs C, Q02, S03 |
| E02 fixed-scaffold theorem | `Construction/Count.lean` | done | needs P01, T01, E01 |
| K01 Kummer independence | `MultiQuadratic/Kummer.lean` | done | |
| K02 order, embeddings, conjugations | `MultiQuadratic/Order.lean` | done | |
| K03 basis and coordinate bound | `MultiQuadratic/Basis.lean` | done | needs K01, K02 |
| K04 trace integrality | `MultiQuadratic/Basis.lean` | done | needs K03 |
| K05 conjugate norm, small kernel | `MultiQuadratic/Norm.lean` | done | needs K02, K03 |
| L01 Legendre choice | `MultiQuadratic/Legendre.lean` | done | |
| L02 reduction map | `MultiQuadratic/Legendre.lean` | done | needs K02 |
| K06 scaffold instance | `MultiQuadratic/Scaffold.lean` | done | needs K03–K05, L02, S01 |
| M01 exponent arithmetic | `Construction/Arith.lean` | done | |
| M02 final theorem | `Construction/Main.lean` | done | needs E02, K06, L01, M01 |

## Lower bound — `docs/nikodym_bound_lean_blueprint.md`

| Node | Module | Status | Notes |
| --- | --- | --- | --- |
| F01 degree-bounded polynomial spaces | `LowerBound/PolynomialSpaces.lean` | done | |
| F02 restriction spaces, Hilbert function | `LowerBound/Hilbert/Defs.lean` | done | needs F01 |
| F03 point ideals, jets | `LowerBound/Jets/Defs.lean` | done | needs F01 |
| F04 lines and line ideals | `LowerBound/Lines/Basic.lean` | done | needs F01, F02 |
| F05 private families | `LowerBound/PrivateFamily.lean` | done | needs F04 |
| H01 standard monomials | `LowerBound/Hilbert/StandardMonomials.lean` | done | needs F01, F02 |
| H02 weighted shadow inequality | `LowerBound/Hilbert/Shadow.lean` | done | |
| H03 normalized Hilbert inequality | `LowerBound/Hilbert/Normalized.lean` | done | needs H01, H02 |
| I00 algebra interface (`quotDim`, `degree`, `AlgebraInterface`) | `LowerBound/Algebra/Interface.lean` | done | new node; assembly is conditional on it |
| A01 dimension and closed-point height | `LowerBound/Algebra/Dimension.lean` | done | substantial |
| D01 quotient dimension via primes | `LowerBound/Algebra/DimensionExtra.lean` | wip | design doc |
| GL graded lemmas + `homHilbert` | `LowerBound/Algebra/GradedLemmas.lean` | wip | design doc |
| PA polynomial asymptotics, `evPoly` refactor | `LowerBound/Algebra/PolyAsymptotics.lean` | done | design doc |
| TR0–TR2, TR6 base change (Hilbert, jets) | `LowerBound/Algebra/BaseChange.lean` | wip | design doc |
| TR3–TR4 base change (dimension, primes) | `LowerBound/Algebra/BaseChangePrime.lean` | wip | design doc |
| TR5, TR7 assemble `algebraInterface` | `LowerBound/Algebra/BaseChange.lean` | open | needs everything |
| A02 linear Noether normalization | `LowerBound/Algebra/LinearNormalization.lean` | wip | substantial |
| A03 Hilbert polynomials, additivity | `LowerBound/Algebra/HilbertPolynomial.lean` | done | substantial |
| A04 dimension, degree, normalization rank | `LowerBound/Algebra/Degree.lean` | open | substantial |
| A05 affine/homogeneous bridge | `LowerBound/Algebra/Homogenization.lean` | wip | substantial |
| A06′ homogeneous fraction basis, conductor | `LowerBound/Algebra/FreeFiber.lean` | open | |
| A07 graded norm degree control | `LowerBound/Algebra/GradedNorm.lean` | open | substantial |
| A08 uniform Hilbert upper bound | `LowerBound/Hilbert/DegreeUpper.lean` | open | interface theorem |
| A09 graded chart | — | dropped | replaced by A06′/A07′ (design doc) |
| J01 tangent cone, local parameters | `LowerBound/Algebra/LocalParameters.lean` | done | substantial |
| J02 local jet minimum | `LowerBound/Jets/LowerBound.lean` | open | interface theorem |
| B01 hypersurface section degree | `LowerBound/Algebra/HypersurfaceDegree.lean` | open | substantial |
| B02 degree sum over components | `LowerBound/Algebra/ComponentDegree.lean` | open | substantial |
| B03 affine proper-cut interface | `LowerBound/Algebra/ProperCut.lean` | open | interface theorem |
| G01 bounded reduction mod grid power | `LowerBound/Grid/Reduction.lean` | wip | needs F01 |
| G02 CRT for grid point powers | `LowerBound/Grid/CRT.lean` | wip | needs F03 |
| G03 joint grid jet interpolation | `LowerBound/Grid/Jets.lean` | done | needs F02, F03, G01, G02 |
| G04 omitted conditions | `LowerBound/Grid/OmittedConditions.lean` | done | needs G03 |
| L01 jet vanishing on a line | `LowerBound/Lines/Jets.lean` | wip | needs F03, F04 |
| L02 q−1 roots force line identity | `LowerBound/Lines/Vanishing.lean` | wip | needs F04, L01 |
| C01 affine point count | `LowerBound/Counting/Points.lean` | done | needs F03, F05, G03, J02, A08 |
| C02 binomial gap estimate | `LowerBound/Arithmetic/BinomialGap.lean` | wip | |
| C03 Hilbert gap | `LowerBound/Hilbert/Gap.lean` | done | needs H03, A08, C02 |
| C04 interpolation cut | `LowerBound/InterpolationCut.lean` | done | needs F05, G04, J02, C03, L02 |
| C05 multiplicity choice | `LowerBound/Arithmetic/Multiplicity.lean` | done | |
| C06 assigning lines to components | `LowerBound/Counting/Components.lean` | done | needs F05, B03, C04 |
| C07 weighted selection | `LowerBound/Arithmetic/WeightedSelection.lean` | done | |
| C08 curve base case | `LowerBound/Counting/Curves.lean` | done | needs F04, F05, A01, A04, A05 |
| C09 carrier theorem | `LowerBound/CarrierBound.lean` | done (conditional on I00) | needs C01, C04–C08 |
| C10 Nikodym, natural-number form | `LowerBound/Main.lean` | done (conditional on I00) | needs F05, C09 |
| C11 real corollary | `LowerBound/Main.lean` | done (conditional on I00) | needs C10 |

## Log

- 2026-09-05: tracker created; wave 1 launched.
