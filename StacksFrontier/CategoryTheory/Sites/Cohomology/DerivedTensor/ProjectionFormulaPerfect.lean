module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedComplexInduction
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.ConeOfAMorphism
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackAsATriangulatedFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula

/-!
# The dévissage of the projection formula to the structure sheaf, on a ringed topos

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi presented by a morphism of
the underlying sites, and let `E ∈ D(O_C)`.  Equation 21.50.0.1 of [Stacks, Tag 0B56] is a map

`Rf_*E ⊗^L_{O_D} K ⟶ Rf_*(E ⊗^L_{O_C} Lf^*K)`

natural in `K ∈ D(O_D)`.  [Stacks, Tag 0944] asserts that it is an isomorphism when `K` is
perfect.  This module carries out the dévissage step of that proof: **granted invertibility at
every shift of `O_D` placed in every degree, the map is invertible at every shift of every
strictly perfect complex of `O_D`-modules.**

The reduction runs on stupid truncations and split retracts, so it is formal once both sides of
Equation 21.50.0.1 are known to be exact functors of `K`; the exactness is assembled here from
[Stacks, Tag 06YY] (`Lf^*` is exact and commutes with the shift), [Stacks, Tag 06YU] (tensoring
with a fixed object is exact and commutes with the shift) and [Stacks, Tag 07A6] (`Rf_*` is the
right adjoint of `Lf^*`, hence exact and compatible with the shift).

## Main definitions

All in the namespace `Stacks.Cohomology.ProjectionFormulaPerfectDevissage`.

* `singleUnit` — the structure sheaf of a ringed site placed in a given degree of `D(O)`.
* `singleUnitShiftIso` — `O[i]⟦n⟧ ≅ O[i - n]`: a shift of the structure sheaf placed in a degree
  is the structure sheaf placed in another degree.

## Main results

* `isIso_app_of_isStrictlyPerfect` — **on an arbitrary ringed site**, a natural transformation
  between exact functors out of `D(O)` which is invertible at every shift of `O` in every degree
  is invertible at every shift of every strictly perfect complex.  This is the dévissage engine,
  stated with no reference to the projection formula.
* `isIso_projectionFormulaMap_of_isStrictlyPerfect` — the engine applied to Equation 21.50.0.1:
  invertibility at every shift of `O_D[i]` gives invertibility at every shift of every strictly
  perfect complex of `O_D`-modules.
* `isIso_app_singleUnit_shift` — the shifts in the base case are redundant: invertibility at
  `O[i]` for every `i` gives invertibility at every shift of every `O[i]`, for an arbitrary
  natural transformation and in particular for one with no known compatibility with the shift.
* `isIso_app_of_isStrictlyPerfect_of_singleUnit` and
  `isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit` — the engine and its
  application to Equation 21.50.0.1, with the base case asked for only at the unshifted `O_D[i]`.

## Implementation notes

*Why the engine is restated rather than reused.*
`Stacks.Cohomology.StrictlyPerfectInvertibility.isIso_app_of_isStrictlyPerfect`
(in `StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/`,
`ComponentwiseInvertibilityOnStrictlyPerfect.lean`) is the same dévissage for a *ringed space*:
it is stated at `OXMod X` for
`X : RingedSpace.{u, u}`, with the two local sheafification instances of the open-cover site
baked into its context, and `IsStrictlyPerfect` there is the ringed-space structure of
`StacksFrontier/Topology/Sheaves/Cohomology/StrictlyPerfect/FiniteFreeSummands.lean`, not the
site-level one of [Stacks, Tag 08FL].  Neither the statement nor its hypotheses reach a ringed
topos.  Everything it *consumes*, however, is already free of geometry — the three closure
properties of `StacksFrontier/CategoryTheory/Triangulated/ComponentwiseInvertibility.lean`, the
stupid-truncation induction `Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex`
and, on the site side,
`Stacks.SheafOfModules.Tensor.isDirectSummandOfFiniteFree_iff_retract_biproduct` — so what is
done here is the re-gluing, not a second proof.  The site-level version is the one
[Stacks, Tag 0944] needs, since perfectness on a ringed site ([Stacks, Tag 08G5],
`AlgebraicGeometry.RingedSite.IsPerfect`) is defined by local strictly perfect models in the
site-level sense.

*Why the structural data are explicit arguments.*  `F.CommShift ℤ` and `F.IsTriangulated` are
taken as explicit arguments of `isIso_app_of_isStrictlyPerfect`, as in the ringed-space version
and for the same reason: the shift compatibility of the derived tensor product of
[Stacks, Tag 06YU] arrives as the `commShift_right` field of a structure rather than as a global
instance, and the shift compatibility of `Rf_*` depends on `hmos`, which is not an instance and
so cannot be found by instance search.  They are supplied in `letI`s inside the proof of
`isIso_projectionFormulaMap_of_isStrictlyPerfect` rather than exported, so that this module adds
no second spelling of the exactness of the two sides of Equation 21.50.0.1.

*What is not proved here, and why [Stacks, Tag 0944] is not tagged.*  Two inputs of the source's
proof are missing from this development, and neither is supplied by the dévissage.  No
declaration here carries the tag 0944.

* **The base case `K = O_D[n]`.**  The source calls it immediate.  Formally it is
  `Stacks.AlgebraicGeometry.ProjectionFormula.isIso_adjunctionTensorMap_unitObj`, which needs
  four things: the right unitors of the two derived tensor products, the naturality of the one on
  the target of `Lf^*`, a unit comparison `ν : Lf^*(O_D[0]) ≅ O_C[0]`, and the right-unitor
  coherence of the comparison of [Stacks, Tag 07A4].  **Three of the four are available
  unconditionally; the fourth is available at the level of modules and not yet at the level of
  the derived category.**

  The unitors are `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso`
  ([Stacks, Tag 0FPT]) and their naturality is
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso_hom_naturality`, stated for an
  arbitrary ringed site and so serving both sides of `f`.  The unit comparison is
  `Stacks.Sheaves.DerivedPullback.derivedPullbackUnitIso`, invertible by
  `Stacks.Sheaves.DerivedPullback.isIso_derivedPullbackUnitMap_unconditional` with **no
  hypothesis beyond the source's**.  It reduces to the *ordinary* comparison `f^*O_D ⟶ O_C`,
  which is Mathlib's `SheafOfModules.pullbackObjUnitToUnit`; Mathlib's `IsIso` instance for that
  asks the functor presenting `f` to be final, but
  `Stacks.Sheaves.DerivedPullback.isIso_pullbackObjUnitToUnit` proves it invertible outright, by
  identifying it — after composition with an isomorphism — with the inverse of the
  corepresentability isomorphism of [Stacks, Tag 03LU].

  What is missing is the right-unitor coherence of [Stacks, Tag 07A4] *in the derived category*.
  `derivedPullbackTensorIso` is produced by `CategoryTheory.Localization.liftNatIso` and is
  accompanied by no compatibility with the unitors, with the shift or with composition.  Its
  module-level predecessor, the proposition
  `Stacks.Sheaves.DerivedPullback.PullbackToposRightUnitorCoherence`, **is now proved**, by
  `Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence` of the module
  `PullbackToposRightUnitorCoherence` (in `StacksFrontier.CategoryTheory.Sites.Cohomology`,
  folder `DerivedPullback`),
  unconditionally in the morphism of sites.  What is still owed is the passage from it to the
  derived statement: `O_D[0]` is a K-flat complex with flat terms
  (`Stacks.SheafOfModules.isKFlat_single_unit`,
  `Stacks.Sheaves.DerivedPullback.isFlat_single_unit_X`), so the comparison of [Stacks, Tag 07A4]
  at it is computed by `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso`
  (`derivedPullbackTensorIso_hom_app_model`), whose action on each bidegree is
  `Stacks.Sheaves.DerivedPullback.ι_pullbackToposTensorTotalIso_hom` and which for this complex
  has one bidegree per degree; the derived right unitor is
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.rightUnitIso`, whose value at the class
  of a complex is `Stacks.SheafOfModules.tensorComplexUnitIso` by `rightUnitIso_hom_eq`.
  Assembling those into the derived coherence is the one remaining step of this base case, and no
  declaration does it.  The ringed-space analogue of the base case,
  `Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_unitObject`
  ([Stacks, Tag 08EU]), carries all four as explicit hypotheses.
* **The reduction of a perfect complex to a strictly perfect one.**  Perfectness is local on
  `D`, and the locality of invertibility is available —
  `Stacks.SheafOfModules.isIso_of_coversTop_mapDerivedCategory` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/Slice/DerivedIsomorphismLocality.lean` — but
  identifying the restriction of Equation 21.50.0.1 with Equation 21.50.0.1 for the localized
  morphism of [Stacks, Tag 04J0] is [Stacks, Tag 0E48], and for the site-presented morphisms
  used here the only form of it is the abstract hexagon
  `Stacks.AffineProjectionFormula.adjunctionTensorMap_baseChange_square`, whose input
  `Stacks.AffineProjectionFormula.TensorComparisonCompatible` is not discharged for
  `RingedToposSiteHom`.  Discharging it needs the compatibility of [Stacks, Tag 07A4] with
  composition of site-presented morphisms of ringed topoi, which this development does not have;
  the ringed-space analogue
  `Stacks.Cohomology.DerivedRelativeCupProduct.derivedPullbackTensorIso_comparison_square` is
  proved, and for `RingedToposHom` it is
  `Stacks.Sheaves.DerivedPullback.OfToposHom.tensorComparisonCompatible_derivedPullbackTensorIso`,
  the input of
  `Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap_baseChange_square`.
  Independently, the localization square of [Stacks, Tag 04J0] is recorded as a 2-isomorphism of
  `RingedToposHom` (`AlgebraicGeometry.RingedSite.Hom.localizedRingedSquare`), while the hexagon
  at site-presented morphisms asks for a strict equality `g.comp f' = f.comp g'` of
  `RingedToposSiteHom`, which no declaration provides.

## References

* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 0B56](https://stacks.math.columbia.edu/tag/0B56)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.CategoryTheory.ComponentwiseInvertibility
open Stacks.DerivedCategory.BoundedInduction
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.ProjectionFormulaPerfectDevissage

universe u w

attribute [local instance] HasDerivedCategory.standard

/-! ### The dévissage on an arbitrary ringed site -/

section Site

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Sheaves of `O`-modules have finite biproducts: the category is abelian, hence preadditive
with finite products.  Instance search does not take this step on its own at the spelling
`Stacks.SheafOfModules.Tensor.ringSheaf O` of the structure sheaf of rings. -/
local instance hasFiniteBiproductsSheafOfModules :
    HasFiniteBiproducts (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The structure sheaf of the ringed site `(C, O)` placed in degree `i`, as an object of
`D(O)`. -/
abbrev singleUnit (i : ℤ) :
    DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  (DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) i).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- **Invertibility on the shifts of the structure sheaf spreads to strictly perfect complexes,
on an arbitrary ringed site.**  A natural transformation between exact functors out of `D(O)`
which is invertible at the structure sheaf placed in an arbitrary degree and shifted by an
arbitrary amount is invertible at every shift of every strictly perfect complex of
`O`-modules ([Stacks, Tag 08FL]).

The induction is on stupid truncations: a strictly perfect complex is bounded, each of its terms
is a retract of a finite direct sum of copies of `O`, and the extension step is the five lemma
in the derived category applied to the distinguished triangle of a short exact sequence of
complexes.  The property is quantified over all shifts because the extension step needs it at
all shifts. -/
theorem isIso_app_of_isStrictlyPerfect {D : Type*} [Category* D]
    [HasShift D ℤ] [Preadditive D] [HasZeroObject D] [HasFiniteBiproducts D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : DerivedCategory (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤ D)
    (hFs : F.CommShift ℤ) (hGs : G.CommShift ℤ)
    (hFt : letI := hFs; F.IsTriangulated) (hGt : letI := hGs; G.IsTriangulated) (α : F ⟶ G)
    (hunit : ∀ i n : ℤ, IsIso (α.app ((singleUnit O i)⟦n⟧)))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf O) K) :
    ∀ n : ℤ, IsIso (α.app ((DerivedCategory.Q.obj K)⟦n⟧)) := by
  let _ : F.CommShift ℤ := hFs
  let _ : G.CommShift ℤ := hGs
  let _ : F.IsTriangulated := hFt
  let _ : G.IsTriangulated := hGt
  apply property_of_bounded_complex (fun A => ∀ n : ℤ, IsIso (α.app (A⟦n⟧)))
  · intro A B e h n
    exact (α.isIso_app_iff_of_iso ((shiftFunctor _ n).mapIso e)).mp (h n)
  · exact fun A hA n => IsZero.isIso (F.map_isZero ((shiftFunctor _ n).map_isZero hA))
      (G.map_isZero ((shiftFunctor _ n).map_isZero hA)) _
  · exact fun S hS h₁ h₃ => isIso_app_middle_of_all_shifts F G α
      (DerivedCategory.triangleOfSES hS) (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₃
  · exact hK.bounded
  · intro i n
    let H := DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) i ⋙ shiftFunctor _ n
    let β := Functor.whiskerLeft H α
    obtain ⟨m, ⟨r⟩⟩ :=
      (Stacks.SheafOfModules.Tensor.isDirectSummandOfFiniteFree_iff_retract_biproduct O
        (K.X i)).mp (hK.termDirectSummand i)
    exact isIso_app_of_splitRetract (H ⋙ F) (H ⋙ G) β r.i r.r r.retract
      (isIso_app_of_biproduct (H ⋙ F) (H ⋙ G)
        (fun _ : Fin m => SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)) β
        fun _ => hunit i n)

/-- **A shift of the structure sheaf placed in a degree is the structure sheaf placed in another
degree**: `𝒪[i]⟦n⟧ ≅ 𝒪[i - n]`.

It is the component at the structure sheaf of the shift isomorphism carried by the
`CategoryTheory.SingleFunctors` structure that `DerivedCategory.singleFunctors` installs on the
family of single functors; no computation is involved, only the choice of degrees. -/
def singleUnitShiftIso (i n : ℤ) : (singleUnit O i)⟦n⟧ ≅ singleUnit O (i - n) :=
  ((DerivedCategory.singleFunctors
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))).shiftIso
    n (i - n) i (by omega)).app
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- **The shifts of the structure sheaf carry no information beyond its degrees.**  A natural
transformation invertible at the structure sheaf placed in every degree is invertible at every
shift of the structure sheaf placed in every degree.

This is `singleUnitShiftIso` together with `CategoryTheory.NatTrans.isIso_app_iff_of_iso`, and it
needs nothing of `α` — in particular no compatibility with the shift, which is why it applies to
Equation 21.50.0.1, for which no such compatibility is available. -/
theorem isIso_app_singleUnit_shift {D : Type*} [Category* D] [HasShift D ℤ]
    (F G : DerivedCategory (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤ D) (α : F ⟶ G)
    (hunit : ∀ i : ℤ, IsIso (α.app (singleUnit O i))) (i n : ℤ) :
    IsIso (α.app ((singleUnit O i)⟦n⟧)) :=
  (α.isIso_app_iff_of_iso (singleUnitShiftIso O i n)).mpr (hunit (i - n))

/-- **The dévissage with its base case asked for only at the unshifted structure sheaf in each
degree.**  `isIso_app_of_isStrictlyPerfect` quantifies its base case over all shifts, because the
extension step needs the induction hypothesis at all shifts; but at the structure sheaf the shifts
are redundant by `isIso_app_singleUnit_shift`, so the hypothesis the caller has to supply is only
`∀ i, IsIso (α.app (𝒪[i]))`. -/
theorem isIso_app_of_isStrictlyPerfect_of_singleUnit {D : Type*} [Category* D]
    [HasShift D ℤ] [Preadditive D] [HasZeroObject D] [HasFiniteBiproducts D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F G : DerivedCategory (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤ D)
    (hFs : F.CommShift ℤ) (hGs : G.CommShift ℤ)
    (hFt : letI := hFs; F.IsTriangulated) (hGt : letI := hGs; G.IsTriangulated) (α : F ⟶ G)
    (hunit : ∀ i : ℤ, IsIso (α.app (singleUnit O i)))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf O) K) :
    ∀ n : ℤ, IsIso (α.app ((DerivedCategory.Q.obj K)⟦n⟧)) :=
  isIso_app_of_isStrictlyPerfect O F G hFs hGs hFt hGt α
    (isIso_app_singleUnit_shift O F G α hunit) K hK

end Site

/-! ### The dévissage of Equation 21.50.0.1 -/

section Topos

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- Equation 21.50.0.1 of [Stacks, Tag 0B56] as a natural transformation in the complex on the
base. -/
private def projectionFormulaNatTrans
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj E) ⟶
      derivedPullback f ⋙ (derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward f where
  app := ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E
  naturality := fun _ _ k =>
    ProjectionFormulaOnRingedTopoi.projectionFormulaMap_naturality_target f hmos E k

/-- **The dévissage step of [Stacks, Tag 0944].**  For a morphism of ringed topoi
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` presented by a morphism of the underlying sites and an
arbitrary `E ∈ D(O_C)`: if Equation 21.50.0.1 of [Stacks, Tag 0B56] is invertible at every shift
of `O_D` placed in every degree, then it is invertible at every shift of every strictly perfect
complex of `O_D`-modules.

The hypothesis `hunit` is the base case of the source's dévissage, at the shifts of the structure
sheaf; the conclusion is at an arbitrary strictly perfect complex, so the two are not the same
statement and nothing circular is assumed.  The exactness of the two sides of Equation 21.50.0.1
in the complex on the base is assembled in the proof from [Stacks, Tag 06YY] for `Lf^*`,
[Stacks, Tag 06YU] for the derived tensor product and [Stacks, Tag 07A6] for `Rf_*`.

What this does *not* deliver, and why no declaration of this module carries the tag 0944, is the
base case `hunit` itself and the localization on `D` that reduces a perfect complex to a strictly
perfect one; see the module's implementation notes for exactly which declarations are missing. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hunit : ∀ i n : ℤ, IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E
      ((singleUnit Y.O i)⟦n⟧)))
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (n : ℤ) :
    IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E
      ((DerivedCategory.Q.obj P)⟦n⟧)) := by
  let _ : ((derivedTensorProductFunctor X.O).obj E).CommShift ℤ :=
    (canonicalDerivedTensorProduct X.O).commShift_right _
  let _ : ((derivedTensorProductFunctor X.O).obj E).IsTriangulated :=
    (canonicalDerivedTensorProduct X.O).exact_right _
  let _ : (derivedPushforward f).CommShift ℤ :=
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).rightAdjointCommShift ℤ
  let _ : (derivedPullback f).IsTriangulated :=
    DerivedPullbackOnRingedTopoi.derivedPullback_isTriangulated_of_isMorphismOfSites f hmos
  let _ : (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).CommShift ℤ :=
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).commShift_of_leftAdjoint ℤ
  let _ : (derivedPushforward f).IsTriangulated :=
    (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).isTriangulated_rightAdjoint
  let _ : ((derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward f).CommShift ℤ :=
    Functor.CommShift.comp _ _
  exact isIso_app_of_isStrictlyPerfect Y.O
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj E))
    (derivedPullback f ⋙ (derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward f)
    ((canonicalDerivedTensorProduct Y.O).commShift_right _)
    (Functor.CommShift.comp _ _)
    ((canonicalDerivedTensorProduct Y.O).exact_right _)
    inferInstance
    (projectionFormulaNatTrans f hmos E) hunit P hP n

/-- **The dévissage step of [Stacks, Tag 0944], with its base case asked for only at the
unshifted structure sheaf in each degree.**  This is
`isIso_projectionFormulaMap_of_isStrictlyPerfect` with the shifts removed from the hypothesis by
`isIso_app_singleUnit_shift`.

What it costs is nothing, and what it buys is a *shape* for the base case rather than a weaker
base case.  Equation 21.50.0.1 is not known to be compatible with the shift — that is one of the
three compatibilities of [Stacks, Tag 07A4] that `derivedPullbackTensorIso` does not come with —
so nothing here transfers invertibility from `𝒪_D[0]` to its shifts, and this hypothesis is not
weaker than the one of `isIso_projectionFormulaMap_of_isStrictlyPerfect`: the two families of
objects `{𝒪_D[i]⟦n⟧}` and `{𝒪_D[j]}` coincide up to isomorphism, and `singleUnitShiftIso` is
exactly that coincidence.

What it changes is which computation the base case asks for.  Stated over the two parameters, the
hypothesis invites being met by invertibility at `𝒪_D[0]` plus a
`CategoryTheory.NatTrans.CommShift` for Equation 21.50.0.1, which would be the shift
compatibility of [Stacks, Tag 07A4] and is absent.  Stated over the one parameter, it asks instead
for invertibility at the structure sheaf placed in each degree, uniformly in the degree — and
`𝒪_D[j]` is a K-flat complex with flat terms, so the comparison of [Stacks, Tag 07A4] at it is
computed by
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso`, whose action on each bidegree is
`Stacks.Sheaves.DerivedPullback.ι_pullbackToposTensorTotalIso_hom` and which for this complex has
one bidegree per degree.  That route needs the *module*-level right-unitor coherence and no
derived-category shift compatibility at all.  The module-level coherence is now proved, by
`Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence`; what is still owed is its
passage through `pullbackToposTensorTotalIso` to the derived statement.  See the implementation
notes. -/
theorem isIso_projectionFormulaMap_of_isStrictlyPerfect_of_singleUnit
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hunit : ∀ i : ℤ, IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E
      (singleUnit Y.O i)))
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (n : ℤ) :
    IsIso (ProjectionFormulaOnRingedTopoi.projectionFormulaMap f hmos E
      ((DerivedCategory.Q.obj P)⟦n⟧)) :=
  isIso_projectionFormulaMap_of_isStrictlyPerfect f hmos E
    (isIso_app_singleUnit_shift Y.O
      ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj E))
      (derivedPullback f ⋙ (derivedTensorProductFunctor X.O).obj E ⋙ derivedPushforward f)
      (projectionFormulaNatTrans f hmos E) hunit)
    P hP n

end Topos

end Stacks.Cohomology.ProjectionFormulaPerfectDevissage

end
