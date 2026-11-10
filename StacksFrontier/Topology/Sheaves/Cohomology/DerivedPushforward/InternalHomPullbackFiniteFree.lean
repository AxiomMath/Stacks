module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackDevissage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomAdditive
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.DerivedPullbackAdditive

/-!
# The canonical map of Tag 08I3 at a direct summand of a finite free module in degree zero

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `M ∈ D(𝒪_Y)`.  Tag 08I3
provides the canonical map

`Lh^* R𝓗om_{𝒪_Y}(K, M) ⟶ R𝓗om_{𝒪_X}(Lh^*K, Lh^*M)`,

and `Stacks.Cohomology.DerivedInternalHomPullback.isIso_derivedPullbackSheafHomMap_singleUnit`
proves it invertible at `K = 𝒪_Y[0]` with no hypothesis.  `…InternalHomPullbackDevissage` carries
that case to every *retract* of `𝒪_Y[0]`.  This file carries it to every retract of a **finite
direct sum** of copies of `𝒪_Y[0]` — that is, to every `K` which is a direct summand of a finite
free `𝒪_Y`-module placed in degree zero.

That is exactly the class the source's proof of Tag 0GM7 clause (1) ends at: its last sentence is
that `h^*𝓗om(ℰ, ℱ) = 𝓗om(h^*ℰ, ℱ)` *whenever `ℰ` is a direct summand of a finite free
`𝒪_X`-module*.

## What it costs, and what it does not

Nothing beyond additivity.  The invertibility locus of a natural transformation between
**additive** functors is closed under finite split sums, by the same two-line conjugation that
makes it closed under retracts, with the identity of the ambient object written as
`CategoryTheory.Limits.biproduct.total` instead of as `i ≫ r = 𝟙`.  So — unlike
`…InternalHomPullbackDevissage`'s `isIso_derivedPullbackSheafHomMap_of_generatedByOp`, which
reaches the whole thick closure of `𝒪_Y[0]` — **no shift datum, no
`CategoryTheory.Functor.CommShift` and no `CategoryTheory.Functor.IsTriangulated` is used here**,
and in particular the absent contravariant `CommShift` for
`Stacks.SheafOfModules.derivedSheafHom` is not needed.

## Main results

All names are in the namespace `Stacks.Cohomology.DerivedInternalHomPullback`.

* `isIso_app_of_splitSum`: a natural transformation between additive functors is invertible at an
  object presented as a finite split sum as soon as it is invertible at each summand.
* `Transpose.isIso_homComparison_of_splitSum`: the same for the hom-comparison of a functor with
  internal hom, in its first argument.
* `isIso_derivedPullbackSheafHomMap_of_splitSum_singleUnit`: the canonical map of Tag 08I3 is
  invertible at every `K` presented as a finite split sum of copies of `𝒪_Y[0]`, unconditionally.
* `isIso_derivedPullbackSheafHomMap_biproductUnit`: the canonical map of Tag 08I3 is invertible at
  `K = (𝒪_Y[0])^{⊕ m}` for every `m`, unconditionally.
* `isIso_derivedPullbackSheafHomMap_of_retract_biproductUnit`: it is invertible at every retract of
  `(𝒪_Y[0])^{⊕ m}`, unconditionally.

## Nothing here is tagged

What is proved below is clause (1) of Tag 0GM7 **restricted**, not Tag 0GM7, so none of the
declarations carries the tag; the three existing registrations of Tag 0GM7 are untouched.
The restriction is strictly weaker than the one the already-tagged
`isIso_derivedPullbackSheafHomMap_of_retract_singleUnit` carries — a retract of `𝒪_Y[0]` is the
case `m = 1` — and none of the quantified data is vacuous: the split-sum datum is inhabited by
the biproduct inclusions and projections together with
`CategoryTheory.Limits.biproduct.total`, which is
`isIso_derivedPullbackSheafHomMap_biproductUnit` below and holds for every `m : ℕ`, and the
retract datum by `m` arbitrary, `K = (𝒪_Y[0])^{⊕ m}` and `i = r = 𝟙`.

Clause (1) at a general perfect `K`, and clauses (2) and (3), are **not** proved, here or
anywhere in this development.  Perfectness in the sense of Stacks 08CM is a *local* condition and
a perfect object is only locally quasi-isomorphic to a strictly perfect complex; and a strictly
perfect complex is a *bounded complex* of direct summands of finite free modules, so reaching it
from the modules needs the extension step of a dévissage, which is where the shift data this file
avoids would be paid.  See the implementation notes of `…InternalHomPullbackDevissage` and of
`…InternalHomPullbackHomComplexMap`.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace Opposite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

/-! ### The invertibility locus of a natural transformation is closed under finite split sums -/

section SplitSum

/-- **A natural transformation between additive functors is invertible at a finite split sum.**
If `Z` carries maps `ι j : A j ⟶ Z` and `π j : Z ⟶ A j` with `∑ j, π j ≫ ι j = 𝟙 Z` — which is
`CategoryTheory.Limits.biproduct.total` when `Z` is a biproduct — and `η` is invertible at every
`A j`, then it is invertible at `Z`.

The inverse is the obvious sum of conjugates, and the two identities are the naturality of `η` at
`π j` and at `ι j` respectively, followed by the additivity of the two functors.  At a one-element
index type this is `Stacks.DerivedCategoryComparisons.isIso_app_of_retract`. -/
theorem isIso_app_of_splitSum {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] {F G : C ⥤ D} [F.Additive] [G.Additive] (η : F ⟶ G)
    {J : Type*} [Fintype J] {Z : C} (A : J → C)
    (ι : ∀ j, A j ⟶ Z) (π : ∀ j, Z ⟶ A j)
    (hsum : ∑ j : J, π j ≫ ι j = 𝟙 Z)
    (hA : ∀ j, IsIso (η.app (A j))) :
    IsIso (η.app Z) := by
  classical
  have := hA
  refine ⟨⟨∑ j : J, G.map (π j) ≫ inv (η.app (A j)) ≫ F.map (ι j), ?_, ?_⟩⟩
  · have key : ∀ j : J,
        η.app Z ≫ (G.map (π j) ≫ inv (η.app (A j)) ≫ F.map (ι j)) = F.map (π j ≫ ι j) := by
      intro j
      rw [← Category.assoc, ← η.naturality (π j), Category.assoc, IsIso.hom_inv_id_assoc,
        ← F.map_comp]
    rw [Preadditive.comp_sum, Finset.sum_congr rfl (fun j _ => key j), ← F.map_sum, hsum,
      F.map_id]
  · have key : ∀ j : J,
        (G.map (π j) ≫ inv (η.app (A j)) ≫ F.map (ι j)) ≫ η.app Z = G.map (π j ≫ ι j) := by
      intro j
      rw [Category.assoc, Category.assoc, η.naturality (ι j), IsIso.inv_hom_id_assoc,
        ← G.map_comp]
    rw [Preadditive.sum_comp, Finset.sum_congr rfl (fun j _ => key j), ← G.map_sum, hsum,
      G.map_id]

/-- **A split sum in a preadditive category is a split sum in the opposite category**, with the
two families exchanged. -/
theorem op_splitSum {C : Type*} [Category C] [Preadditive C] {J : Type*} [Fintype J]
    {Z : C} (A : J → C) (ι : ∀ j, A j ⟶ Z) (π : ∀ j, Z ⟶ A j)
    (hsum : ∑ j : J, π j ≫ ι j = 𝟙 Z) :
    ∑ j : J, (ι j).op ≫ (π j).op = 𝟙 (op Z) := by
  classical
  simp only [← op_comp]
  rw [← op_sum, hsum, op_id]

end SplitSum

namespace Transpose

/-! ### The hom-comparison at a finite split sum in its first argument -/

section SplitSum

variable {D₁ D₂ : Type*} [Category D₁] [Category D₂] [Preadditive D₁] [Preadditive D₂]
  (P : D₁ ⥤ D₂) (H₁ : D₁ᵒᵖ ⥤ D₁ ⥤ D₁) (H₂ : D₂ᵒᵖ ⥤ D₂ ⥤ D₂)
  (T₁ : D₁ × D₁ ⥤ D₁) (T₂ : D₂ × D₂ ⥤ D₂)
  (e₁ : ∀ A B C : D₁, (A ⟶ (H₁.obj (op B)).obj C) ≃ (T₁.obj (A, B) ⟶ C))
  (e₂ : ∀ A B C : D₂, (A ⟶ (H₂.obj (op B)).obj C) ≃ (T₂.obj (A, B) ⟶ C))
  (m : T₁ ⋙ P ≅ P.prod P ⋙ T₂)

/-- **Invertibility of the comparison passes to a finite split sum in its first argument.**

The two sides of the comparison, read as functors of its first argument on `D₁ᵒᵖ`, are
`Transpose.comparisonSourceFunctor` and `Transpose.comparisonTargetFunctor`; the comparison is
the natural transformation `Transpose.homComparisonNatTrans` between them, which is built from
the two clauses of Tag 08J8 for each of the two bijections and nothing else.  So this is
`isIso_app_of_splitSum` for that transformation, with the split sum transported to the opposite
category by `op_splitSum`.

Carried as hypotheses: the two clauses of Tag 08J8 for each bijection, and the additivity of the
two sides.  **No shift datum and no triangulated structure**, which is what distinguishes this
from `Transpose.isIso_homComparison_of_generatedByOp`. -/
theorem isIso_homComparison_of_splitSum
    (hnat₁ : TensorHomEquivNaturalLeft H₁ T₁ e₁) (hdin₁ : TensorHomEquivDinatural H₁ T₁ e₁)
    (hnat₂ : TensorHomEquivNaturalLeft H₂ T₂ e₂) (hdin₂ : TensorHomEquivDinatural H₂ T₂ e₂)
    (F : D₁)
    [(comparisonSourceFunctor P H₁ F).Additive]
    [(comparisonTargetFunctor P H₂ F).Additive]
    {J : Type*} [Fintype J] {Z : D₁} (A : J → D₁)
    (ι : ∀ j, A j ⟶ Z) (π : ∀ j, Z ⟶ A j)
    (hsum : ∑ j : J, π j ≫ ι j = 𝟙 Z)
    (hA : ∀ j, IsIso (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m (A j) F)) :
    IsIso (homComparison P H₁ H₂ T₁ T₂ e₁ e₂ m Z F) := by
  have h := isIso_app_of_splitSum
    (homComparisonNatTrans P H₁ H₂ T₁ T₂ e₁ e₂ m hnat₁ hdin₁ hnat₂ hdin₂ F)
    (Z := op Z) (fun j => op (A j)) (fun j => (π j).op) (fun j => (ι j).op)
    (op_splitSum A ι π hsum) (fun j => by
      rw [homComparisonNatTrans_app]
      exact hA j)
  rwa [homComparisonNatTrans_app] at h

end SplitSum

end Transpose

/-! ### Tag 08I3 on a ringed space, at a finite free module in degree zero -/

section RingedSpaces

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedPullbackTensor in
attribute [local instance] abelianModulesSheafTensor

-- `Stacks.SheafOfModules.Tensor.ringSheaf` joins the list because the two factors of every
-- composite below are written at different spellings of one sheaf of rings: the derived internal
-- hom is stated over `StructureSheafModules Y.sheaf`, i.e. modules over
-- `(sheafCompose _ (forget₂ CommRingCat RingCat)).obj Y.sheaf`, and the derived pullback over
-- `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y`, i.e. modules over
-- `Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf`.  The two sheaves of rings are equal, but only
-- after unfolding both, which instance search will not do at reducible transparency, so the
-- additivity of each factor is carried at one spelling and never retrieved at the other.  Naming
-- a factor with its type ascribed at the other spelling does not help; the
-- transparency is the lever.
attribute [local implicit_reducible] structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf

-- NO BINDER CARRIES THE ADDITIVITY OF `Lh^*`, and getting that right took the detour recorded in
-- the implementation notes of `…DerivedPushforward.DerivedPullbackAdditive`: in this file's
-- reducibility regime instance search does not find it, so it is proved there, in the regime of
-- `…DerivedPullback.Triangulated`, and supplied here by name in the two declarations that need
-- it.  By name rather than as a local instance, because its morphism argument is explicit and
-- instance search cannot fill an explicit argument.
variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- The left-hand side of the comparison of Tag 08I3, read as a functor of its first argument, is
additive: it is `R𝓗om_{𝒪_Y}(-, M)` — additive by
`AlgebraicGeometry.RingedSite.additive_derivedSheafHom_flip_obj` — followed by the derived
pullback. -/
theorem additive_comparisonSourceFunctor
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (Transpose.comparisonSourceFunctor (derivedPullbackFunctor h)
      (Stacks.SheafOfModules.derivedSheafHom Y.sheaf) M).Additive :=
  letI := derivedPullbackAdditive h
  letI : ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).flip.obj M).Additive :=
    AlgebraicGeometry.RingedSite.additive_derivedSheafHom_flip_obj
      (Stacks.SheafOfModules.ringedSite Y.sheaf) M
  inferInstanceAs
    (((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).flip.obj M ⋙
      derivedPullbackFunctor h).Additive)

/-- The right-hand side of the comparison of Tag 08I3, read as a functor of its first argument, is
additive: it is the opposite of the derived pullback — additive by Mathlib's
`CategoryTheory.Functor.op_additive` — followed by `R𝓗om_{𝒪_X}(-, Lh^*M)`. -/
theorem additive_comparisonTargetFunctor
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)) :
    (Transpose.comparisonTargetFunctor (derivedPullbackFunctor h)
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf) M).Additive :=
  letI := derivedPullbackAdditive h
  letI : ((Stacks.SheafOfModules.derivedSheafHom X.sheaf).flip.obj
      ((derivedPullbackFunctor h).obj M)).Additive :=
    AlgebraicGeometry.RingedSite.additive_derivedSheafHom_flip_obj
      (Stacks.SheafOfModules.ringedSite X.sheaf) ((derivedPullbackFunctor h).obj M)
  inferInstanceAs
    (((derivedPullbackFunctor h).op ⋙
      (Stacks.SheafOfModules.derivedSheafHom X.sheaf).flip.obj
        ((derivedPullbackFunctor h).obj M)).Additive)

attribute [local instance] additive_comparisonSourceFunctor additive_comparisonTargetFunctor

/-- Tag 08I3 is invertible at a finite split sum of objects at which it is invertible. -/
private theorem isIso_derivedPullbackSheafHomMap_of_splitSum
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    {J : Type*} [Fintype J]
    {K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (A : J → DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (ι : ∀ j, A j ⟶ K) (π : ∀ j, K ⟶ A j) (hsum : ∑ j : J, π j ≫ ι j = 𝟙 K)
    (hA : ∀ j, IsIso (derivedPullbackSheafHomMap h (A j) M)) :
    IsIso (derivedPullbackSheafHomMap h K M) :=
  Transpose.isIso_homComparison_of_splitSum (derivedPullbackFunctor h)
    (Stacks.SheafOfModules.derivedSheafHom Y.sheaf)
    (Stacks.SheafOfModules.derivedSheafHom X.sheaf) (internalHomTensorUncurried Y)
    (internalHomTensorUncurried X)
    (fun A B C => (RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite Y.sheaf) A B C).toEquiv)
    (fun A B C => (RingedSite.derivedCurryHomEquiv
      (Stacks.SheafOfModules.ringedSite X.sheaf) A B C).toEquiv)
    (pullbackTensorIso h)
    (tensorHomEquivNaturalLeft_ringedSpace Y) (tensorHomEquivDinatural_ringedSpace Y)
    (tensorHomEquivNaturalLeft_ringedSpace X) (tensorHomEquivDinatural_ringedSpace X) M
    A ι π hsum hA


/-- **Tag 08I3 is invertible at every `K` presented as a finite split sum of copies of
`𝒪_Y[0]`, unconditionally.**  For an arbitrary morphism of ringed spaces `h`, an arbitrary
`M ∈ D(𝒪_Y)` and families `ι j : 𝒪_Y[0] ⟶ K`, `π j : K ⟶ 𝒪_Y[0]` indexed by a finite type with
`∑ j, π j ≫ ι j = 𝟙 K`, the canonical map

`Lh^* R𝓗om_{𝒪_Y}(K, M) ⟶ R𝓗om_{𝒪_X}(Lh^*K, Lh^*M)`

is an isomorphism.

It is `Transpose.isIso_homComparison_of_splitSum` with the unit case
`isIso_derivedPullbackSheafHomMap_singleUnit` supplied at every summand, so no unitor binder
survives, and with the four clauses of Tag 08J8 discharged by
`tensorHomEquivNaturalLeft_ringedSpace` and `tensorHomEquivDinatural_ringedSpace` on each side.
No shift datum and no triangulated structure is used. -/
theorem isIso_derivedPullbackSheafHomMap_of_splitSum_singleUnit
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    {J : Type*} [Fintype J]
    {K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (ι : ∀ _ : J, Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y ⟶ K)
    (π : ∀ _ : J, K ⟶ Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y)
    (hsum : ∑ j : J, π j ≫ ι j = 𝟙 K) :
    IsIso (derivedPullbackSheafHomMap h K M) :=
  isIso_derivedPullbackSheafHomMap_of_splitSum h M
    (fun _ => Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y) ι π hsum
    (fun _ => isIso_derivedPullbackSheafHomMap_singleUnit h M)

/-- **Tag 08I3 is invertible at `K = (𝒪_Y[0])^{⊕ m}`, unconditionally**, for every natural
number `m`.  This is `isIso_derivedPullbackSheafHomMap_of_splitSum_singleUnit` at the biproduct
inclusions and projections, whose split-sum identity is Mathlib's
`CategoryTheory.Limits.biproduct.total`. -/
theorem isIso_derivedPullbackSheafHomMap_biproductUnit
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    (m : ℕ) :
    IsIso (derivedPullbackSheafHomMap h
      (⨁ fun _ : Fin m => Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y) M) :=
  isIso_derivedPullbackSheafHomMap_of_splitSum_singleUnit h M
    (biproduct.ι (fun _ : Fin m => Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y))
    (biproduct.π (fun _ : Fin m => Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y))
    biproduct.total

/-- **Tag 08I3 is invertible at every direct summand of `(𝒪_Y[0])^{⊕ m}`, unconditionally.**
For an arbitrary morphism of ringed spaces `h`, an arbitrary `M ∈ D(𝒪_Y)` and any `K` admitting
`i : K ⟶ (𝒪_Y[0])^{⊕ m}` and `r : (𝒪_Y[0])^{⊕ m} ⟶ K` with `i ≫ r = 𝟙 K`, the canonical map of
Tag 08I3 is an isomorphism.

This is the class of `K` at which the source's proof of Tag 0GM7 clause (1) bottoms out: a direct
summand of a finite free `𝒪_Y`-module placed in degree zero.  It is clause (1) of Tag 0GM7
restricted to those `K`, and carries no attribute for that reason; the restriction is not vacuous
(`m = 1`, `i = r = 𝟙` gives `K = 𝒪_Y[0]`), and it is strictly weaker than the restriction the
tagged `isIso_derivedPullbackSheafHomMap_of_retract_singleUnit` carries, which is the case
`m = 1`. -/
theorem isIso_derivedPullbackSheafHomMap_of_retract_biproductUnit
    (M : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y))
    {K : DerivedCategory (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y)}
    (m : ℕ)
    (i : K ⟶ ⨁ fun _ : Fin m => Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y)
    (r : (⨁ fun _ : Fin m => Stacks.Cohomology.DerivedProjectionFormula.singleUnit Y) ⟶ K)
    (hir : i ≫ r = 𝟙 K) :
    IsIso (derivedPullbackSheafHomMap h K M) :=
  isIso_derivedPullbackSheafHomMap_of_splitSum h M (fun _ : Unit => _) (fun _ => r)
    (fun _ => i) (by simp [hir]) (fun _ => isIso_derivedPullbackSheafHomMap_biproductUnit h M m)

end RingedSpaces

end Stacks.Cohomology.DerivedInternalHomPullback

end
