module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Cotangent.Complex
public import StacksFrontier.Cotangent.LichtenbaumSchlessinger
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonBasic
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonCanonical.HomologyZeroNegOne

/-!
# Comparison of the cotangent complex with the Lichtenbaum–Schlessinger complex

Let `P → B` be a polynomial presentation of an `A`-algebra `B` with chosen generators `f_t` of
its defining ideal, and let `L` be the three-term complex
`Rel/TrivRel → F ⊗_P B → Ω_{P/A} ⊗_P B` attached to these data. There is a canonical map
`L_{B/A} → L` in `D(B)`, and it identifies `L` with the truncation `τ_{≥ -2} L_{B/A}`
([Stacks, Tag 09CG]).

## Main definitions

* `Algebra.Presentation.cotangentToLichtenbaumSchlessinger`: the canonical map `L_{B/A} → L`
  in `D(B)`.
* `Algebra.Presentation.truncGECotangentIsoLichtenbaumSchlessinger`: the isomorphism
  `τ_{≥ -2} L_{B/A} ≅ L` it induces.

## Main results

* `Algebra.Presentation.isIso_descTruncGE_cotangentToLichtenbaumSchlessinger`: the canonical map
  factors uniquely through `τ_{≥ -2} L_{B/A}` and the factorization is an isomorphism.
* `Algebra.Presentation.truncGECotangentIsoLichtenbaumSchlessinger_fac`: that isomorphism is the
  one induced by the canonical map.

## Implementation notes

The canonical map is the class in `D(B)` of the map of complexes
`Algebra.Presentation.lsChainMap`, built as in the source from the standard resolution
`P_• → B` by an `A`-algebra lift `ψ : P_0 → P` of the augmentation, an `A`-biderivation `λ` on
`P_1` with prescribed values on the variables, and the map in degree `-2` sending `dg` to the
class of `λ(d_0 g - d_1 g + d_2 g)`. Its isomorphisms on `H⁰`, `H^{-1}` and `H^{-2}` are
`Algebra.Presentation.isIso_homologyMap_lsChainMap_zero`, `..._negOne` and `..._negTwo`, and the
passage from a chain-level comparison to the truncation is
`StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonBasic`. The independence of the choices
`ψ` and `λ` is `Algebra.Presentation.Q_map_eq_canonicalCotangentToLichtenbaumSchlessinger`.

The cotangent complex in the module universe of `L` and the structure of chain-level comparisons
are defined in `StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonBasic`, as
`Algebra.Presentation.uliftCotangentComplex` and
`Algebra.Presentation.LichtenbaumSchlessingerChainComparison`; this file names them
`Algebra.Presentation.cotangentComplexULift` and
`Algebra.Presentation.LichtenbaumSchlessingerComparison`.

## References

* [Stacks Project, Tag 09CG](https://stacks.math.columbia.edu/tag/09CG)
* [Stacks Project, Tag 09CD](https://stacks.math.columbia.edu/tag/09CD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Algebra.Presentation

attribute [local instance] HasDerivedCategory.standard

/-- The cotangent complex `L_{B/A}`, transported into the universe of `B`-modules in which the
Lichtenbaum–Schlessinger complex of a presentation with variables and relations indexed in a
third universe lives: `Algebra.Presentation.uliftCotangentComplex`. -/
public abbrev cotangentComplexULift (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B]
    [Algebra A B] : CochainComplex (ModuleCat.{max u v w} B) ℤ :=
  uliftCotangentComplex.{u, v, w} A B

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B] [Algebra A B]
  {X T : Type w}

/-- The Lichtenbaum–Schlessinger complex is concentrated in degrees `-2`, `-1` and `0`, hence in
particular vanishes in all degrees `< -2`. -/
public alias isStrictlyGE_lichtenbaumSchlessingerComplex :=
  lichtenbaumSchlessingerComplex_isStrictlyGE_neg_two

/-- The Lichtenbaum–Schlessinger complex vanishes in positive degrees. -/
public alias isStrictlyLE_lichtenbaumSchlessingerComplex :=
  lichtenbaumSchlessingerComplex_isStrictlyLE_zero

/-- The cotangent complex vanishes in positive degrees, hence so does its universe lift. -/
public instance isStrictlyLE_cotangentComplexULift :
    (cotangentComplexULift.{u, v, w} A B).IsStrictlyLE 0 :=
  uliftCotangentComplex_isStrictlyLE_zero

/-- A chain-level comparison between the cotangent complex `L_{B/A}` and the
Lichtenbaum–Schlessinger complex `L` of a presentation:
`Algebra.Presentation.LichtenbaumSchlessingerChainComparison`. -/
public abbrev LichtenbaumSchlessingerComparison (P : Algebra.Presentation A B X T) :=
  LichtenbaumSchlessingerChainComparison.{u, v, w} P

/-- The comparison map of complexes of `B`-modules. -/
public abbrev LichtenbaumSchlessingerComparison.hom {P : Algebra.Presentation A B X T}
    (c : LichtenbaumSchlessingerComparison P) :
    cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex :=
  LichtenbaumSchlessingerChainComparison.hom c

/-- In degree `0` a comparison is an isomorphism on cohomology. -/
public theorem LichtenbaumSchlessingerComparison.isIso_homologyMap_zero
    {P : Algebra.Presentation A B X T} (c : LichtenbaumSchlessingerComparison P) :
    IsIso (HomologicalComplex.homologyMap c.hom 0) :=
  LichtenbaumSchlessingerChainComparison.isIso_homologyMap_zero c

/-- In degree `-1` a comparison is an isomorphism on cohomology. -/
public theorem LichtenbaumSchlessingerComparison.isIso_homologyMap_neg_one
    {P : Algebra.Presentation A B X T} (c : LichtenbaumSchlessingerComparison P) :
    IsIso (HomologicalComplex.homologyMap c.hom (-1)) :=
  LichtenbaumSchlessingerChainComparison.isIso_homologyMap_neg_one c

/-- In degree `-2` a comparison is an isomorphism on cohomology. -/
public theorem LichtenbaumSchlessingerComparison.isIso_homologyMap_neg_two
    {P : Algebra.Presentation A B X T} (c : LichtenbaumSchlessingerComparison P) :
    IsIso (HomologicalComplex.homologyMap c.hom (-2)) :=
  LichtenbaumSchlessingerChainComparison.isIso_homologyMap_neg_two c

/-- A comparison is an isomorphism on cohomology in every degree `≥ -2`. -/
public theorem LichtenbaumSchlessingerComparison.isIso_homologyMap
    {P : Algebra.Presentation A B X T} (c : LichtenbaumSchlessingerComparison P) (i : ℤ)
    (hi : -2 ≤ i) : IsIso (HomologicalComplex.homologyMap c.hom i) :=
  LichtenbaumSchlessingerChainComparison.isIso_homologyMap c i hi

variable (P : Algebra.Presentation A B X T)

/-- The chain-level comparison of the source: `Algebra.Presentation.lsChainMap` with its
isomorphisms on `H⁰`, `H^{-1}` and `H^{-2}`. -/
private def lsChainComparison : LichtenbaumSchlessingerChainComparison.{u, v, w} P where
  hom := P.lsChainMap
  isIso_homologyMap_zero := P.isIso_homologyMap_lsChainMap_zero
  isIso_homologyMap_neg_one := P.isIso_homologyMap_lsChainMap_negOne
  isIso_homologyMap_neg_two := P.isIso_homologyMap_lsChainMap_negTwo

/-- **Stacks 09CG.** The canonical map `L_{B/A} → L` in `D(B)`: the class of the map of
complexes `Algebra.Presentation.lsChainMap`, which is `dψ ⊗ 1`, `λ̄` and `q` in degrees `0`,
`-1` and `-2`. -/
@[stacks 09CG "the canonical map L_{B/A} → L in D(B), the class of the map of complexes
dψ ⊗ 1, λ̄, q built from the choices ψ : P₀ → P and the biderivation λ of the source"]
public def cotangentToLichtenbaumSchlessinger :
    DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B) ⟶
      DerivedCategory.Q.obj (lichtenbaumSchlessingerComplex P).complex :=
  DerivedCategory.Q.map P.lsChainMap

/-- The canonical map is an isomorphism on the cohomology of the derived category in every
degree `≥ -2`. -/
public theorem isIso_homologyFunctor_map_cotangentToLichtenbaumSchlessinger
    (i : ℤ) (hi : -2 ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
      (cotangentToLichtenbaumSchlessinger P)) :=
  isIso_homologyFunctor_map_cotangentToLichtenbaumSchlessingerOfComparison
    (lsChainComparison P) i hi

/-- **Stacks 09CG.** The canonical map `L_{B/A} → L` factors through the truncation
`τ_{≥ -2} L_{B/A}`, since `L` lies in `D^{≥ -2}(B)`, and the factorization is an isomorphism. -/
@[stacks 09CG "the canonical map L_{B/A} → L induces an isomorphism τ_{≥ -2} L_{B/A} → L in
D(B)"]
public theorem isIso_descTruncGE_cotangentToLichtenbaumSchlessinger :
    IsIso (DerivedCategory.TStructure.t.descTruncGE
      (cotangentToLichtenbaumSchlessinger P) (-2)) :=
  isIso_descTruncGE_cotangentToLichtenbaumSchlessingerOfComparison (lsChainComparison P)

/-- **Stacks 09CG.** The isomorphism `τ_{≥ -2} L_{B/A} ≅ L` induced by the canonical map. -/
@[stacks 09CG "the induced map τ_{≥ -2} L_{B/A} → L is an isomorphism in D(B)"]
public def truncGECotangentIsoLichtenbaumSchlessinger :
    (DerivedCategory.TStructure.t.truncGE (-2)).obj
        (DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B)) ≅
      DerivedCategory.Q.obj (lichtenbaumSchlessingerComplex P).complex :=
  haveI := isIso_descTruncGE_cotangentToLichtenbaumSchlessinger P
  asIso (DerivedCategory.TStructure.t.descTruncGE
    (cotangentToLichtenbaumSchlessinger P) (-2))

/-- **Stacks 09CG.** The isomorphism `τ_{≥ -2} L_{B/A} ≅ L` is the one induced by the canonical
map `L_{B/A} → L`: composing it with the projection to the truncation returns that map. -/
@[stacks 09CG "the isomorphism τ_{≥ -2} L_{B/A} → L is induced by the canonical map L_{B/A} → L"]
public theorem truncGECotangentIsoLichtenbaumSchlessinger_fac :
    (DerivedCategory.TStructure.t.truncGEπ (-2)).app
        (DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B)) ≫
      (truncGECotangentIsoLichtenbaumSchlessinger P).hom =
        cotangentToLichtenbaumSchlessinger P :=
  DerivedCategory.TStructure.t.π_descTruncGE _ _

end Algebra.Presentation

end
