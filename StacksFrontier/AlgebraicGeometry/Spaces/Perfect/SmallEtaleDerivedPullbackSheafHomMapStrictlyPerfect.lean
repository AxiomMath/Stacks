module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMapUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtale
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.DevissageOnAnySite
public import StacksFrontier.CategoryTheory.Triangulated.RightOpTriangulated

/-!
# The map of Stacks 08I3 on algebraic spaces out of a strictly perfect object

Let `f : X ⟶ Y` be a morphism of algebraic spaces and `K ∈ D(𝒪_Y)` an object with a strictly
perfect model (`AlgebraicGeometry.Space.HasStrictlyPerfectModel`): `K` is isomorphic to a bounded
complex whose terms are retracts of finite free `𝒪_Y`-modules. Then the canonical map of
Stacks 08I3,

`Lf^*R𝓗om(K, L) ⟶ R𝓗om(Lf^*K, Lf^*L)`,

is an isomorphism for every `L ∈ D(𝒪_Y)`.

The proof is the dévissage of the source. Read covariantly, the two sides are the triangulated
functors `K ↦ Lf^*R𝓗om(K, L)` and `K ↦ R𝓗om(Lf^*K, Lf^*L)` from `D(𝒪_Y)` to `D(𝒪_X)ᵒᵖ`
(`AlgebraicGeometry.Space.isTriangulated_smallEtaleDerivedSheafHom_flip_obj` and the exactness
of `Lf^*`), and the map is a natural transformation between them. It is invertible at the
structure sheaf placed in every degree
(`AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_singleFunctor_unit`), so by
`Stacks.Cohomology.StrictlyPerfectDevissage.isIso_app_shift_of_retract_biproduct` it is
invertible at every bounded complex of retracts of finite free modules. The dévissage needs no
compatibility of the transformation with the shifts: the five lemma is applied with the
connecting maps of the two image triangles, and invertibility at every shift is carried along.

## Main results

* `AlgebraicGeometry.Space.isIso_smallEtaleDerivedPullbackSheafHomMap_of_hasStrictlyPerfectModel`:
  the map of Stacks 08I3 is an isomorphism when its source has a strictly perfect model.

## References

* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pretriangulated.Opposite
open Stacks.Cohomology.DerivedInternalHomPullback

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleModel
attribute [local instance 2000] abelian_ringedToposStructureRingSheafModules

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X Y : AlgebraicSpaces B S hS}

/-- The components of `smallEtaleDerivedPullbackSheafHomNatTrans` are the map of Stacks 08I3. -/
theorem smallEtaleDerivedPullbackSheafHomNatTrans_app (f : X ⟶ Y)
    (L K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    (smallEtaleDerivedPullbackSheafHomNatTrans f L).app (op K) =
      smallEtaleDerivedPullbackSheafHomMap f K L :=
  Transpose.homComparisonNatTrans_app _ _ _ _ _ _ _ _ _ _ _ _ L K

/-- **Stacks 08I3 out of an object with a strictly perfect model.** For `f : X ⟶ Y` and `K`
isomorphic to a bounded complex of retracts of finite free `𝒪_Y`-modules, the map
`Lf^*R𝓗om(K, L) ⟶ R𝓗om(Lf^*K, Lf^*L)` is an isomorphism for every `L`. -/
theorem isIso_smallEtaleDerivedPullbackSheafHomMap_of_hasStrictlyPerfectModel (f : X ⟶ Y)
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hK : HasStrictlyPerfectModel B S hS K)
    (L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))) :
    IsIso (smallEtaleDerivedPullbackSheafHomMap f K L) := by
  obtain ⟨P, hP, ⟨a, b, ha, hb⟩, ⟨e⟩⟩ := hK
  let α := smallEtaleDerivedPullbackSheafHomNatTrans f L
  have hfin : {i : ℤ | ¬ IsZero (P.X i)}.Finite :=
    (Set.finite_Icc a b).subset fun i hi =>
      ⟨not_lt.1 fun h => hi (P.isZero_of_isStrictlyGE a i h),
        not_lt.1 fun h => hi (P.isZero_of_isStrictlyLE b i h)⟩
  have hterm : ∀ i : ℤ, ∃ m : ℕ, Nonempty (Retract (P.X i)
      (⨁ fun _ : Fin m => SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y))) :=
    fun i => let ⟨m, ι, p, hιp⟩ := hP i; ⟨m, ⟨⟨ι, p, hιp⟩⟩⟩
  have hunit : ∀ i : ℤ, IsIso ((NatTrans.rightOp α).app ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) i).obj
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Y)))) := by
    intro i
    rw [NatTrans.rightOp_app, isIso_op_iff, smallEtaleDerivedPullbackSheafHomNatTrans_app]
    exact isIso_smallEtaleDerivedPullbackSheafHomMap_singleFunctor_unit f i L
  let : (Transpose.comparisonTargetFunctor (smallEtaleDerivedModulePullback B S hS f)
      (smallEtaleDerivedSheafHom B S hS X) L).CommShift ℤ :=
    inferInstanceAs (((smallEtaleDerivedModulePullback B S hS f).op ⋙
      (smallEtaleDerivedSheafHom B S hS X).flip.obj
        ((smallEtaleDerivedModulePullback B S hS f).obj L)).CommShift ℤ)
  have : (Transpose.comparisonTargetFunctor (smallEtaleDerivedModulePullback B S hS f)
      (smallEtaleDerivedSheafHom B S hS X) L).IsTriangulated :=
    inferInstanceAs (((smallEtaleDerivedModulePullback B S hS f).op ⋙
      (smallEtaleDerivedSheafHom B S hS X).flip.obj
        ((smallEtaleDerivedModulePullback B S hS f).obj L)).IsTriangulated)
  let : (Transpose.comparisonSourceFunctor (smallEtaleDerivedModulePullback B S hS f)
      (smallEtaleDerivedSheafHom B S hS Y) L).CommShift ℤ :=
    inferInstanceAs (((smallEtaleDerivedSheafHom B S hS Y).flip.obj L ⋙
      smallEtaleDerivedModulePullback B S hS f).CommShift ℤ)
  have : (Transpose.comparisonSourceFunctor (smallEtaleDerivedModulePullback B S hS f)
      (smallEtaleDerivedSheafHom B S hS Y) L).IsTriangulated :=
    inferInstanceAs (((smallEtaleDerivedSheafHom B S hS Y).flip.obj L ⋙
      smallEtaleDerivedModulePullback B S hS f).IsTriangulated)
  have h := Stacks.Cohomology.StrictlyPerfectDevissage.isIso_app_shift_of_retract_biproduct
    (Transpose.comparisonTargetFunctor (smallEtaleDerivedModulePullback B S hS f)
      (smallEtaleDerivedSheafHom B S hS X) L).rightOp
    (Transpose.comparisonSourceFunctor (smallEtaleDerivedModulePullback B S hS f)
      (smallEtaleDerivedSheafHom B S hS Y) L).rightOp
    inferInstance inferInstance inferInstance inferInstance (NatTrans.rightOp α) _ hunit P hfin
    hterm 0
  have h₀ : IsIso ((NatTrans.rightOp α).app (DerivedCategory.Q.obj P)) :=
    ((NatTrans.rightOp α).isIso_app_iff_of_iso
      ((shiftFunctorZero _ ℤ).app (DerivedCategory.Q.obj P))).1 h
  rw [NatTrans.rightOp_app, isIso_op_iff] at h₀
  have hK : IsIso (α.app (op K)) := (α.isIso_app_iff_of_iso e.op).1 h₀
  rwa [smallEtaleDerivedPullbackSheafHomNatTrans_app] at hK

end AlgebraicGeometry.Space

end
