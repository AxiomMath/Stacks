module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.Cotangent.Complex
public import StacksFrontier.Cotangent.LichtenbaumSchlessinger

/-!
# Comparison of the cotangent complex with the Lichtenbaum–Schlessinger complex

Let `P → B` be a polynomial presentation of an `A`-algebra `B` with chosen generators `f_t` of
its defining ideal, and let `L` be the three-term complex
`Rel/TrivRel → F ⊗_P B → Ω_{P/A} ⊗_P B` attached to these data. There is a canonical map
`L_{B/A} → L` in `D(B)`, and it identifies `L` with the truncation `τ_{≥ -2} L_{B/A}`.

## Main definitions

* `Algebra.Presentation.cotangentComplexULift`: the cotangent complex `L_{B/A}` in the module
  universe of `L`.
* `Algebra.Presentation.LichtenbaumSchlessingerComparison`: a chain-level comparison, namely a
  map of complexes `L_{B/A} → L` which is an isomorphism on cohomology in all degrees `≥ -2`.
* `Algebra.Presentation.cotangentToLichtenbaumSchlessinger`: the canonical map `L_{B/A} → L`
  in `D(B)`, the image of a chain-level comparison under the localization functor.
* `Algebra.Presentation.truncGECotangentIsoLichtenbaumSchlessinger`: the resulting isomorphism
  `τ_{≥ -2} L_{B/A} ≅ L`.

## Main results

* `Algebra.Presentation.isStrictlyGE_lichtenbaumSchlessingerComplex`: `L` is concentrated in
  degrees `≥ -2`, hence lies in `D^{≥ -2}(B)`.
* `Algebra.Presentation.isIso_descTruncGE_cotangentToLichtenbaumSchlessinger`: the canonical map
  factors uniquely through `τ_{≥ -2} L_{B/A}` and the factorization is an isomorphism.
* `Algebra.Presentation.truncGECotangentIsoLichtenbaumSchlessinger_fac`: that
  isomorphism is the one induced by the canonical map.

## Implementation notes

`L` vanishes outside degrees `-2`, `-1`, `0`, so it lies in `D^{≥ -2}(B)` and every map out of
`L_{B/A}` into it factors uniquely through `τ_{≥ -2} L_{B/A}`. The factorization is an
isomorphism exactly when the map is an isomorphism on cohomology in all degrees `≥ -2`: below
`-2` both sides are acyclic, and at and above `-2` the projection `L_{B/A} → τ_{≥ -2} L_{B/A}`
is already an isomorphism on cohomology. This is the only place where the `t`-structure enters,
and it is what the two assertions below are deduced from.

The chain-level comparison is carried as the explicit datum
`Algebra.Presentation.LichtenbaumSchlessingerComparison`. The source constructs it from a
resolution `P_• → B`: an `A`-algebra lift `P_0 → P` of the augmentation, the `A`-biderivation on
`P_1` with prescribed values on the variables, and the map in degree `-2` sending `dg` to the
class of the value of that biderivation on `d_0 g - d_1 g + d_2 g`; its degreewise invertibility
on cohomology is the computation of `H_0`, `H_1` and `H_2`. Neither the chain map nor those three
computations is available in this library, so both are packaged into this datum.

The variables and the relations of the presentation may be indexed in a universe independent of
that of `B`, so the cotangent complex is transported into the module universe of `L` along
`ModuleCat.uliftFunctor`, an exact and fully faithful functor which is `ULift.moduleEquiv`
degreewise; the target is the complex of the given presentation, unchanged.

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
third universe lives. The transport is the image under `ModuleCat.uliftFunctor`, which is
`ULift.moduleEquiv` degreewise. -/
public def cotangentComplexULift (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B]
    [Algebra A B] : CochainComplex (ModuleCat.{max u v w} B) ℤ :=
  ((ModuleCat.uliftFunctor.{w} B).mapHomologicalComplex _).obj
    (CommAlgCat.cotangentComplex A (CommAlgCat.of A B))

variable {A : Type u} {B : Type (max u v)} [CommRing A] [CommRing B] [Algebra A B]
  {X T : Type w}

/-- The Lichtenbaum–Schlessinger complex is concentrated in degrees `-2`, `-1` and `0`, hence in
particular vanishes in all degrees `< -2`. -/
public instance isStrictlyGE_lichtenbaumSchlessingerComplex
    (P : Algebra.Presentation A B X T) :
    (lichtenbaumSchlessingerComplex P).complex.IsStrictlyGE (-2) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (lichtenbaumSchlessingerComplex P).isZero_X i (by omega) (by omega) (by omega)

/-- The Lichtenbaum–Schlessinger complex vanishes in positive degrees. -/
public instance isStrictlyLE_lichtenbaumSchlessingerComplex
    (P : Algebra.Presentation A B X T) :
    (lichtenbaumSchlessingerComplex P).complex.IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact (lichtenbaumSchlessingerComplex P).isZero_X i (by omega) (by omega) (by omega)

/-- The cotangent complex vanishes in positive degrees, hence so does its universe lift. -/
public instance isStrictlyLE_cotangentComplexULift :
    (cotangentComplexULift.{u, v, w} A B).IsStrictlyLE 0 := by
  have h : (CommAlgCat.cotangentComplex A (CommAlgCat.of A B)).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact CommAlgCat.cotangentComplex_isZero_pos A (CommAlgCat.of A B) i hi
  exact (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff
    (CommAlgCat.cotangentComplex A (CommAlgCat.of A B))
    (ModuleCat.uliftFunctor.{w} B) 0).2 h

/-- A chain-level comparison between the cotangent complex `L_{B/A}` and the
Lichtenbaum–Schlessinger complex `L` of a presentation: a map of complexes of `B`-modules which
is an isomorphism on cohomology in the three degrees `0`, `-1` and `-2` where `L` lives. -/
public structure LichtenbaumSchlessingerComparison (P : Algebra.Presentation A B X T) where
  /-- The comparison map of complexes of `B`-modules. -/
  hom : cotangentComplexULift.{u, v, w} A B ⟶ (lichtenbaumSchlessingerComplex P).complex
  /-- In degree `0` it is an isomorphism on cohomology; both sides are `Ω[B⁄A]`. -/
  isIso_homologyMap_zero : IsIso (HomologicalComplex.homologyMap hom 0)
  /-- In degree `-1` it is an isomorphism on cohomology. -/
  isIso_homologyMap_neg_one : IsIso (HomologicalComplex.homologyMap hom (-1))
  /-- In degree `-2` it is an isomorphism on cohomology. -/
  isIso_homologyMap_neg_two : IsIso (HomologicalComplex.homologyMap hom (-2))

variable {P : Algebra.Presentation A B X T}

/-- A morphism between zero objects is an isomorphism. -/
private theorem isIso_of_isZero_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {Y Z : C} (f : Y ⟶ Z) (hY : IsZero Y) (hZ : IsZero Z) : IsIso f := by
  rw [hY.eq_of_src f (hY.iso hZ).hom]
  infer_instance

/-- A comparison is an isomorphism on cohomology in every degree `≥ -2`: in degrees `0`, `-1`
and `-2` by assumption, and in the positive degrees because both complexes vanish there. -/
public theorem LichtenbaumSchlessingerComparison.isIso_homologyMap
    (c : LichtenbaumSchlessingerComparison P) (i : ℤ) (hi : -2 ≤ i) :
    IsIso (HomologicalComplex.homologyMap c.hom i) := by
  rcases eq_or_ne i 0 with rfl | h0
  · exact c.isIso_homologyMap_zero
  rcases eq_or_ne i (-1) with rfl | h1
  · exact c.isIso_homologyMap_neg_one
  rcases eq_or_ne i (-2) with rfl | h2
  · exact c.isIso_homologyMap_neg_two
  have hpos : (0 : ℤ) < i := by omega
  exact isIso_of_isZero_of_isZero _ (CochainComplex.isZero_of_isLE _ 0 i hpos)
    (CochainComplex.isZero_of_isLE _ 0 i hpos)

/-- **Stacks 09CG.** The canonical map `L_{B/A} → L` in `D(B)` attached to a chain-level
comparison: its image under the localization functor. -/
@[stacks 09CG "the canonical map L_{B/A} → L in D(B), attached to a chain-level comparison
carried as the explicit datum Algebra.Presentation.LichtenbaumSchlessingerComparison"]
public def cotangentToLichtenbaumSchlessinger (c : LichtenbaumSchlessingerComparison P) :
    DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B) ⟶
      DerivedCategory.Q.obj (lichtenbaumSchlessingerComplex P).complex :=
  DerivedCategory.Q.map c.hom

/-- The canonical map is an isomorphism on the cohomology of the derived category in every
degree `≥ -2`, because its chain-level representative is. -/
public theorem isIso_homologyFunctor_map_cotangentToLichtenbaumSchlessinger
    (c : LichtenbaumSchlessingerComparison P) (i : ℤ) (hi : -2 ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} B) i).map
      (cotangentToLichtenbaumSchlessinger c)) := by
  have h := (NatIso.isIso_map_iff
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v w} B) i) c.hom).2
      (c.isIso_homologyMap i hi)
  exact h

/-- **Stacks 09CG.** The canonical map `L_{B/A} → L` factors through the truncation
`τ_{≥ -2} L_{B/A}`, since `L` lies in `D^{≥ -2}(B)`, and the factorization is an isomorphism. -/
public theorem isIso_descTruncGE_cotangentToLichtenbaumSchlessinger
    (c : LichtenbaumSchlessingerComparison P) :
    IsIso (DerivedCategory.TStructure.t.descTruncGE
      (cotangentToLichtenbaumSchlessinger c) (-2)) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  rcases le_or_gt (-2 : ℤ) i with hi | hi
  · have := DerivedCategory.isIso_homologyMap_truncGEπ_app (-2) i hi
      (DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B))
    have := isIso_homologyFunctor_map_cotangentToLichtenbaumSchlessinger c i hi
    exact IsIso.of_isIso_fac_left (f := (DerivedCategory.homologyFunctor
      (ModuleCat.{max u v w} B) i).map _) (by
        rw [← Functor.map_comp, DerivedCategory.TStructure.t.π_descTruncGE])
  · exact isIso_of_isZero_of_isZero _ (DerivedCategory.isZero_of_isGE _ (-2) i hi)
      (DerivedCategory.isZero_of_isGE _ (-2) i hi)

/-- **Stacks 09CG.** The isomorphism `τ_{≥ -2} L_{B/A} ≅ L` induced by the canonical map. -/
@[stacks 09CG "the induced map τ_{≥ -2} L_{B/A} → L is an isomorphism in D(B)"]
public def truncGECotangentIsoLichtenbaumSchlessinger
    (c : LichtenbaumSchlessingerComparison P) :
    (DerivedCategory.TStructure.t.truncGE (-2)).obj
        (DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B)) ≅
      DerivedCategory.Q.obj (lichtenbaumSchlessingerComplex P).complex :=
  haveI := isIso_descTruncGE_cotangentToLichtenbaumSchlessinger c
  asIso (DerivedCategory.TStructure.t.descTruncGE
    (cotangentToLichtenbaumSchlessinger c) (-2))

/-- **Stacks 09CG.** The isomorphism `τ_{≥ -2} L_{B/A} ≅ L` is the one induced by the canonical
map `L_{B/A} → L`: composing it with the projection to the truncation returns that map. -/
@[stacks 09CG "the isomorphism τ_{≥ -2} L_{B/A} → L is induced by the canonical map L_{B/A} → L"]
public theorem truncGECotangentIsoLichtenbaumSchlessinger_fac
    (c : LichtenbaumSchlessingerComparison P) :
    (DerivedCategory.TStructure.t.truncGEπ (-2)).app
        (DerivedCategory.Q.obj (cotangentComplexULift.{u, v, w} A B)) ≫
      (truncGECotangentIsoLichtenbaumSchlessinger c).hom =
        cotangentToLichtenbaumSchlessinger c :=
  DerivedCategory.TStructure.t.π_descTruncGE _ _

end Algebra.Presentation

end
