module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCupPairing

/-!
# Pullback of cohomology classes along a morphism of ringed spaces

Let `g : Z ⟶ W` be a morphism of ringed spaces. A class in `H^n(W, N)` is carried to a class in
`H^n(Z, Lg^*N)` by the derived unit `N ⟶ Rg_*Lg^*N` followed by the Leray identification
`H^n(W, Rg_* -) = H^n(Z, -)` of [Stacks, Tag 0D5W]
(`Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso`). This is
`Stacks.Cohomology.HomologyPullback.homologyPullback`.

It is natural in `N`, and at a derived direct image it is undone by the counit: followed by the
counit `Lg^*Rg_*M ⟶ M` it is the Leray identification.

## Main results

* `Stacks.Cohomology.HomologyPullback.homologyPullback_naturality`.
* `Stacks.Cohomology.HomologyPullback.homologyPullback_counit`.
* `Stacks.Cohomology.HomologyPullback.homologyPullback_homEquiv`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedGlobalCupProduct Stacks.Cohomology.LerayCupPairing
open Stacks.Cohomology.GlobalKunneth Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.HomologyPullback

attribute [local instance] HasDerivedCategory.standard

variable {Z W : RingedSpace.{u, u}} (g : Z ⟶ W)

/-- For functors `F : C ⥤ D` and `H : D ⥤ ModuleCat R`, the map `H(F(x ≫ y))` applied to an
element `z` is `H(F y)` applied to `H(F x) z`. -/
theorem map_map_comp_apply {C D : Type*} [Category* C] [Category* D] {R : Type u} [Ring R]
    (F : C ⥤ D) (H : D ⥤ ModuleCat.{u} R) {a b c : C} (x : a ⟶ b) (y : b ⟶ c)
    (z : H.obj (F.obj a)) :
    (H.map (F.map (x ≫ y))).hom z = (H.map (F.map y)).hom ((H.map (F.map x)).hom z) := by
  rw [Functor.map_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

/-- **Pullback of cohomology classes** `H^n(W, N) ⟶ H^n(Z, Lg^*N)`: the derived unit, followed by
the Leray identification `H^n(W, Rg_* -) = H^n(Z, -)`. -/
def homologyPullback (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) (n : ℤ) :
    cohomologyModule N n →+ cohomologyModule ((derivedPullback g).obj N) n :=
  ((lerayCohomologyIso g ((derivedPullback g).obj N) n).hom.hom.toAddMonoidHom).comp
    ((DerivedCategory.homologyFunctor _ n).map
      ((baseSections W).map ((derivedAdjunction g).unit.app N))).hom.toAddMonoidHom

/-- The value of `homologyPullback g N n` at `x`: the image of `x` under the derived unit
`N ⟶ Rg_*Lg^*N`, carried along the Leray identification `H^n(W, Rg_*Lg^*N) = H^n(Z, Lg^*N)`. -/
theorem homologyPullback_apply (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing W)))
    (n : ℤ) (x : cohomologyModule N n) :
    homologyPullback g N n x = (lerayCohomologyIso g ((derivedPullback g).obj N) n).hom
      (((DerivedCategory.homologyFunctor _ n).map
        ((baseSections W).map ((derivedAdjunction g).unit.app N))).hom x) :=
  rfl

/-- **Pullback of cohomology classes is natural**: for `b : N ⟶ N'`, pulling back the image of `x`
under `b` is the image under `Lg^* b` of the pullback of `x`. -/
theorem homologyPullback_naturality
    {N N' : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))} (b : N ⟶ N') (n : ℤ)
    (x : cohomologyModule N n) :
    homologyPullback g N' n (((DerivedCategory.homologyFunctor _ n).map
        ((baseSections W).map b)).hom x) =
      ((DerivedCategory.homologyFunctor _ n).map
        ((baseSections Z).map ((derivedPullback g).map b))).hom (homologyPullback g N n x) := by
  have hu : b ≫ (derivedAdjunction g).unit.app N' =
      (derivedAdjunction g).unit.app N ≫ (derivedPushforward g).map ((derivedPullback g).map b) :=
    (derivedAdjunction g).unit.naturality b
  have h₁ : ((DerivedCategory.homologyFunctor _ n).map
        ((baseSections W).map ((derivedAdjunction g).unit.app N'))).hom
        (((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map b)).hom x) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections W).map
        ((derivedPushforward g).map ((derivedPullback g).map b)))).hom
        (((DerivedCategory.homologyFunctor _ n).map
          ((baseSections W).map ((derivedAdjunction g).unit.app N))).hom x) :=
    (map_map_comp_apply (baseSections W) (DerivedCategory.homologyFunctor _ n) _ _ x).symm.trans
      ((congrArg (fun z => ((DerivedCategory.homologyFunctor _ n).map
        ((baseSections W).map z)).hom x) hu).trans
        (map_map_comp_apply (baseSections W) (DerivedCategory.homologyFunctor _ n) _ _ x))
  exact (congrArg (lerayCohomologyIso g ((derivedPullback g).obj N') n).hom h₁).trans
    (lerayCohomologyIso_naturality_apply g ((derivedPullback g).map b) n _)

/-- Pulling back and applying `c` is the Leray identification of the transpose of `c`. -/
private theorem map_homologyPullback_eq_leray_homEquiv
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))}
    (c : (derivedPullback g).obj N ⟶ K) (n : ℤ) (x : cohomologyModule N n) :
    ((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map c)).hom
        (homologyPullback g N n x) =
      (lerayCohomologyIso g K n).hom (((DerivedCategory.homologyFunctor _ n).map
        ((baseSections W).map ((derivedAdjunction g).homEquiv _ _ c))).hom x) := by
  refine (lerayCohomologyIso_naturality_apply g c n _).symm.trans
    (congrArg (lerayCohomologyIso g K n).hom ?_)
  refine (map_map_comp_apply (baseSections W) (DerivedCategory.homologyFunctor _ n) _ _
    x).symm.trans ?_
  rw [Adjunction.homEquiv_unit]

/-- **At a derived direct image, pullback followed by the counit is the Leray identification**:
for `x` in `H^n(W, Rg_*M)`, the image of `g^*x` under the counit `Lg^*Rg_*M ⟶ M` is the class of
`H^n(Z, M)` corresponding to `x`. -/
theorem homologyPullback_counit (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (n : ℤ) (x : cohomologyModule ((derivedPushforward g).obj M) n) :
    ((DerivedCategory.homologyFunctor _ n).map
        ((baseSections Z).map ((derivedAdjunction g).counit.app M))).hom
      (homologyPullback g ((derivedPushforward g).obj M) n x) =
      (lerayCohomologyIso g M n).hom x := by
  have h : (derivedAdjunction g).homEquiv _ _ ((derivedAdjunction g).counit.app M) = 𝟙 _ := by
    rw [Adjunction.homEquiv_unit]
    exact (derivedAdjunction g).right_triangle_components M
  rw [map_homologyPullback_eq_leray_homEquiv, h]
  simp
  rfl

/-- **Pullback followed by a morphism out of `Lg^*N` is the Leray identification of its
transpose**: for `c : Lg^*N ⟶ K`, the class `c(g^*x)` of `H^n(Z, K)` is the class of
`H^n(W, Rg_*K)` obtained from `x` by the transpose `N ⟶ Rg_*K` of `c` under `Lg^* ⊣ Rg_*`. -/
theorem homologyPullback_homEquiv {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))}
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))}
    (c : (derivedPullback g).obj N ⟶ K) (n : ℤ) (x : cohomologyModule N n) :
    ((DerivedCategory.homologyFunctor _ n).map ((baseSections Z).map c)).hom
        (homologyPullback g N n x) =
      (lerayCohomologyIso g K n).hom (((DerivedCategory.homologyFunctor _ n).map
        ((baseSections W).map ((derivedAdjunction g).homEquiv _ _ c))).hom x) :=
  map_homologyPullback_eq_leray_homEquiv g c n x

/-- If the unit class of `W` in degree `n` pulls back to zero, then the pullback of every class of
degree `n`, with coefficients in any `N`, is zero. -/
theorem homologyPullback_eq_zero_of_unitCycleClass (n : ℤ)
    (h : homologyPullback g (DerivedCategory.Q.obj (unitComplex W n)) n (unitCycleClass W n) = 0)
    (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing W))) (x : cohomologyModule N n) :
    homologyPullback g N n x = 0 := by
  obtain ⟨a, rfl⟩ := evalUnit_surjective N n x
  exact (homologyPullback_naturality g a n (unitCycleClass W n)).trans
    ((congrArg _ h).trans (map_zero _))

/-- **The pullback of the unit class is nonzero** as soon as some degree-`n` cohomology group
`H^n(Z, M)` is nonzero. -/
theorem homologyPullback_unitCycleClass_ne_zero (n : ℤ)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (y : cohomologyModule M n) (hy : y ≠ 0) :
    homologyPullback g (DerivedCategory.Q.obj (unitComplex W n)) n (unitCycleClass W n) ≠ 0 := by
  intro h
  apply hy
  have h₀ := homologyPullback_eq_zero_of_unitCycleClass g n h ((derivedPushforward g).obj M)
    ((lerayCohomologyIso g M n).inv y)
  have h₁ := homologyPullback_counit g M n ((lerayCohomologyIso g M n).inv y)
  rw [h₀, map_zero] at h₁
  exact ((Iso.inv_hom_id_apply (lerayCohomologyIso g M n) y).symm.trans h₁.symm)

end Stacks.Cohomology.HomologyPullback

end
