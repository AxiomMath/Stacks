module

public import StacksFrontier.Homology.KFlat.FilteredColimitShifts
public import StacksFrontier.CategoryTheory.Triangulated.ComponentwiseInvertibility
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWatts

/-!
# A morphism of exact, direct-sum-preserving functors out of `D(R)` is invertible as soon as it
is invertible on the shifts of the ring

Let `R` be a ring and let `F, G : D(R) ⥤ D` be exact functors preserving direct sums.  A morphism
`α : F ⟶ G` which is invertible at `R[0]⟦n⟧` for every integer `n` is invertible at every object
of `D(R)`.  This is the dévissage of [Stacks, Tag 09PB] read for a natural transformation: the
shifts of the ring generate `D(R)` under direct sums and distinguished triangles, and
invertibility of a component of `α` is a property of objects of `D(R)` closed under both
operations.

The same statement holds across a triangulated equivalence `T : D(R) ≌ 𝒟`, with the hypothesis
read at the objects `T(R[0]⟦n⟧)`; that is the form in which it applies to the derived category of
quasi-coherent modules on an affine scheme, where `T` is the equivalence `D(A) ≌ D_QCoh(𝒪_{Spec
A})` of [Stacks, Tag 06Z0]
(`AlgebraicGeometry.derivedTilde_isEquivalence`).

## Main results

* `Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_of_shifts_of_regularModule`:
  **the dévissage.**  For exact `F, G : D(R) ⥤ D` preserving direct sums of every shape in the
  module universe, a morphism `α : F ⟶ G` invertible at every `R[0]⟦n⟧` is invertible at every
  object.  No hypothesis on `D` beyond being pretriangulated, and **no
  `CategoryTheory.NatTrans.CommShift` for `α`**.
* `Stacks.CategoryTheory.ComponentwiseInvertibility`
  `.isIso_app_of_shifts_of_regularModule_of_equivalence`: the same conclusion on the target of a
  triangulated equivalence out of `D(R)`.

## Why this is not `StacksDraft.CompactDevissage.isIso_of_isIso_app_regularModule`

That theorem — `StacksFrontier/Homology/Devissage/CompactGeneratedNatTrans.lean:236` — has the same
shape and is **not** usable for the same consumers, for two reasons, both of which the statements
below avoid:

* it asks for `[CategoryTheory.NatTrans.CommShift τ ℤ]`, a compatibility of the transformation
  itself with the shift.  For the projection-formula morphism of [Stacks, Tag 0B53] that datum is
  exactly what the library does not have — it amounts to a shift compatibility of the comparison
  of [Stacks, Tag 079U], recorded as missing at
  `StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/ProjectionFormulaUnitDegrees.lean`.
  The price paid here instead is that the hypothesis is asked for at *every* shift of the ring
  rather than only at the ring; that is what the two-out-of-three lemmas of
  `Stacks.CategoryTheory.ComponentwiseInvertibility` are stated at.
* it asks for `[HasDerivedCategory.{u} (ModuleCat.{u} R)]`, a model whose morphisms live in the
  module universe, because the cell presentation it uses tests compactness at the hom universe.
  The dévissage of [Stacks, Tag 09PB] used below is stated at `HasDerivedCategory.standard`, which
  is the model the derived functors of ringed spaces are built at.

## Implementation notes

*The three two-out-of-three rotations.*  [Stacks, Tag 09PB] asks for all three, at the property
`T K := ∀ n, IsIso (α.app (K⟦n⟧))`.  The third vertex is
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_third_of_distinguished` at the
`n`-fold shift of the triangle, whose two extra inputs at the shift by one come from the
hypothesis at `n + 1` through `shiftFunctorAdd`; the second vertex is
`isIso_app_middle_of_all_shifts` verbatim.  The first vertex is that same lemma at the inverse
rotation, which is `Stacks.Cohomology.DerivedBaseChange.isIso_app_first_of_all_shifts`
(`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/DerivedBaseChangeGlobal.lean:762`);
it is restated privately below rather than imported, because that file is a geometric one and
nothing else here needs it.  The two should be deduplicated into
`StacksFrontier/CategoryTheory/Triangulated/ComponentwiseInvertibility.lean`, where the other
rotations live; that is a repo-tier move and is not done here.

*The direct-sum step* is `CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan`
(`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/EilenbergWatts.lean:77`), which is pure
category theory in a geometric file — hence the import — and is the only statement in the library
about a natural transformation at an *arbitrary* coproduct;
`Stacks.CategoryTheory.ComponentwiseInvertibility.isIso_app_of_biproduct` is finite.  It is
applied to `α` whiskered by the shift, so that the shift in the property is carried along rather
than commuted past the coproduct.

## References

* [Stacks Project, Tag 09PB](https://stacks.math.columbia.edu/tag/09PB)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u v

namespace Stacks.CategoryTheory.ComponentwiseInvertibility

attribute [local instance] HasDerivedCategory.standard

variable {D : Type*} [Category* D] [HasShift D ℤ] [Preadditive D] [HasZeroObject D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

omit [HasShift D ℤ] [Preadditive D] [HasZeroObject D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- Invertibility at every shift of `X` gives invertibility at an iterated shift of `X`: the two
shifts are composed by `CategoryTheory.shiftFunctorAdd`. -/
private theorem isIso_app_shift_add {C : Type*} [Category* C] [HasShift C ℤ]
    {F G : C ⥤ D} (α : F ⟶ G) {X : C} (h : ∀ n : ℤ, IsIso (α.app (X⟦n⟧))) (a b : ℤ) :
    IsIso (α.app ((X⟦a⟧)⟦b⟧)) :=
  (α.isIso_app_iff_of_iso ((shiftFunctorAdd C a b).app X)).1 (h (a + b))

/-- A natural transformation between exact functors, invertible at every shift of the first two
vertices of a distinguished triangle, is invertible at every shift of the third.  This is
`isIso_app_third_of_distinguished` at the shifted triangle. -/
private theorem isIso_app_third_of_all_shifts {C : Type*} [Category* C] [HasShift C ℤ]
    [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₁ : ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)))
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧))) :
    ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧)) := fun n =>
  isIso_app_third_of_distinguished F G α ((shiftFunctor (Triangle C) n).obj T)
    (T.shift_distinguished hT n) (h₁ n) (h₂ n)
    (isIso_app_shift_add α h₁ n 1) (isIso_app_shift_add α h₂ n 1)

/-- A natural transformation between exact functors, invertible at every shift of the second and
third vertices of a distinguished triangle, is invertible at every shift of the first.  This is
`isIso_app_middle_of_all_shifts` at the inverse rotation, and is
`Stacks.Cohomology.DerivedBaseChange.isIso_app_first_of_all_shifts` with the shift and exactness
data taken as instances instead of as explicit arguments. -/
private theorem isIso_app_first_of_all_shifts {C : Type*} [Category* C] [HasShift C ℤ]
    [Preadditive C] [HasZeroObject C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F G : C ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    (α : F ⟶ G) (T : Triangle C) (hT : T ∈ distTriang C)
    (h₂ : ∀ n : ℤ, IsIso (α.app (T.obj₂⟦n⟧)))
    (h₃ : ∀ n : ℤ, IsIso (α.app (T.obj₃⟦n⟧))) :
    ∀ n : ℤ, IsIso (α.app (T.obj₁⟦n⟧)) :=
  isIso_app_middle_of_all_shifts F G α T.invRotate (inv_rot_of_distTriang T hT)
    (isIso_app_shift_add α h₃ (-1)) h₂

section DerivedModuleCat

variable {R : Type u} [Ring R] [Small.{v} R]

/-- **A morphism of exact, direct-sum-preserving functors out of `D(R)` invertible on every shift
of the ring is invertible.**  For a ring `R`, exact functors `F, G : D(R) ⥤ D` preserving
coproducts of every shape indexed by the module universe, and a morphism `α : F ⟶ G` with
`α` invertible at `R[0]⟦n⟧` for every integer `n`, every component of `α` is invertible.

This is the dévissage of [Stacks, Tag 09PB]:
`CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts` at the property
`K ↦ ∀ n, IsIso (α.app (K⟦n⟧))`, whose closure under coproducts is
`CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan` and whose two-out-of-three is the three
rotations of `Stacks.CategoryTheory.ComponentwiseInvertibility`.

`α` is **not** assumed compatible with the shift; that is the whole point of asking the
hypothesis at every shift of the ring rather than at the ring alone.  No hypothesis is placed on
`R` beyond `Small.{v} R`, which only says that the regular module has a copy in the module
universe. -/
theorem isIso_app_of_shifts_of_regularModule
    {F G : DerivedCategory (ModuleCat.{v} R) ⥤ D}
    [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) F]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) G]
    (α : F ⟶ G)
    (h : ∀ n : ℤ, IsIso (α.app
      (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
        (ModuleCat.of R (Shrink.{v} R)))⟦n⟧)))
    (K : DerivedCategory (ModuleCat.{v} R)) : IsIso (α.app K) := by
  have all (L : DerivedCategory (ModuleCat.{v} R)) : ∀ n : ℤ, IsIso (α.app (L⟦n⟧)) := by
    refine (CochainComplex.KFlat.property_of_coproducts_of_two_out_of_three_of_shifts
      (R := R)).2 (fun L : DerivedCategory (ModuleCat.{v} R) =>
        ∀ n : ℤ, IsIso (α.app (L⟦n⟧))) ?_ ?_ ?_ L
    · intro I M _ hM n
      have hF : PreservesColimitsOfShape (Discrete I) F := inferInstance
      have hG : PreservesColimitsOfShape (Discrete I) G := inferInstance
      exact CategoryTheory.NatTrans.isIso_app_of_isColimit_cofan
        (Functor.whiskerLeft (shiftFunctor (DerivedCategory (ModuleCat.{v} R)) n) α)
        (colimit.cocone (Discrete.functor M))
        (isColimitOfPreserves _ (colimit.isColimit (Discrete.functor M)))
        (isColimitOfPreserves _ (colimit.isColimit (Discrete.functor M)))
        (fun i => hM i n)
    · intro Δ hΔ
      exact ⟨isIso_app_third_of_all_shifts F G α Δ hΔ,
        isIso_app_middle_of_all_shifts F G α Δ hΔ,
        isIso_app_first_of_all_shifts F G α Δ hΔ⟩
    · intro k n
      exact isIso_app_shift_add α h k n
  exact (α.isIso_app_iff_of_iso
    ((shiftFunctorZero (DerivedCategory (ModuleCat.{v} R)) ℤ).app K)).1 (all K 0)

/-- **The dévissage across a triangulated equivalence out of `D(R)`.**  Let
`T : D(R) ⥤ 𝒟` be a triangulated equivalence and let `F, G : 𝒟 ⥤ D` be exact functors preserving
coproducts of every shape indexed by the module universe.  A morphism `α : F ⟶ G` invertible at
`T(R[0]⟦n⟧)` for every integer `n` is invertible at every object of `𝒟`.

This is `isIso_app_of_shifts_of_regularModule` applied to `α` whiskered by `T`, transported to an
arbitrary object of `𝒟` along `CategoryTheory.Functor.objObjPreimageIso`.  It is the form the
reduction of [Stacks, Tag 08EU] to an affine base asks for: `𝒟` is `D_QCoh(𝒪_{Spec A})` and `T`
is the equivalence of [Stacks, Tag 06Z0]. -/
theorem isIso_app_of_shifts_of_regularModule_of_equivalence
    {𝒟 : Type*} [Category* 𝒟] [HasShift 𝒟 ℤ] [Preadditive 𝒟] [HasZeroObject 𝒟]
    [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
    (T : DerivedCategory (ModuleCat.{v} R) ⥤ 𝒟) [T.IsEquivalence] [T.CommShift ℤ]
    [T.IsTriangulated]
    {F G : 𝒟 ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ] [F.IsTriangulated] [G.IsTriangulated]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) F]
    [∀ I : Type v, PreservesColimitsOfShape (Discrete I) G]
    (α : F ⟶ G)
    (h : ∀ n : ℤ, IsIso (α.app (T.obj
      (((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj
        (ModuleCat.of R (Shrink.{v} R)))⟦n⟧))))
    (K : 𝒟) : IsIso (α.app K) := by
  have hpre : IsIso ((Functor.whiskerLeft T α).app (T.objPreimage K)) :=
    isIso_app_of_shifts_of_regularModule (Functor.whiskerLeft T α) h _
  exact (α.isIso_app_iff_of_iso (T.objObjPreimageIso K)).1 hpre

end DerivedModuleCat

end Stacks.CategoryTheory.ComponentwiseInvertibility

end
