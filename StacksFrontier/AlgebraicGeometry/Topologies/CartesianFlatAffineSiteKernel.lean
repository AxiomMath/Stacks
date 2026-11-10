module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianLocalFactorization
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSite

/-!
# Kernels of cartesian modules on a site of affine schemes with flat factorizations

On a site of affine schemes the kernel of a map of cartesian presheaves of modules is cartesian
over every morphism with flat ring map: base change along a flat ring map is exact. Over an
arbitrary morphism it need not be. This file shows that it is as soon as the site has *flat
factorizations*: every morphism `h : Y ⟶ X` becomes, after restriction to the members `r i` of a
cover of `Y`, a composite `s ≫ b` where `s ≫ a` and `a` and `b` have flat underlying morphisms of
schemes.

## Main results

* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_exact`: the kernel of a map of modules
  cartesian over a flat morphism is cartesian over it.
* `Stacks.FlatAffineSite.isIso_restrictionBaseChange_of_hasFlatFactorizations`: on a site with flat
  factorizations, a module cartesian over every flat morphism is cartesian over every morphism.
* `Stacks.FlatAffineSite.isIso_restrictionBaseChange_kernel`: consequently the kernel of a map of
  cartesian modules is cartesian.

## References

* [Stacks Project, Tag 07B4](https://stacks.math.columbia.edu/tag/07B4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

open scoped ChangeOfRings

universe w m u u₁ v₁ r u' v'

namespace Stacks.PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}

/-- **The kernel of a map of modules cartesian over a flat morphism is cartesian over it.** If
`K → G → F` is objectwise exact with `K → G` injective, the ring map of `f` is flat and the base
change comparisons of `G` and `F` along `f` are isomorphisms, then so is that of `K`. -/
theorem isIso_restrictionBaseChange_of_exact
    {K G F : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
    (ι : K ⟶ G) (φ : G ⟶ F) (hι : ∀ X, Function.Injective (ι.app X))
    (hex : ∀ X, Function.Exact (ι.app X) (φ.app X)) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (hflat : (R.map f).hom.Flat) (hG : IsIso (restrictionBaseChange G f))
    (hF : IsIso (restrictionBaseChange F f)) : IsIso (restrictionBaseChange K f) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let : Module.Flat (R.obj X) (R.obj Y) := hflat
  let θ : ∀ A : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat),
      TensorProduct (R.obj X) (R.obj Y) (A.obj X) →ₗ[R.obj Y] A.obj Y :=
    fun A ↦ (restrictionBaseChange A f).hom
  let lin : ∀ {A B : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)},
      (A ⟶ B) → (A.obj X →ₗ[R.obj X] B.obj X) := fun ψ ↦ (ψ.app X).hom
  let ιX : K.obj X →ₗ[R.obj X] G.obj X := lin ι
  let φX : G.obj X →ₗ[R.obj X] F.obj X := lin φ
  have nat : ∀ {A B : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat)}
      (ψ : A ⟶ B) (z : TensorProduct (R.obj X) (R.obj Y) (A.obj X)),
      θ B (LinearMap.lTensor (R.obj Y) (lin ψ) z) = ψ.app Y (θ A z) := by
    intro A B ψ z
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' => simp [hz, hz']
    | tmul b k =>
      rw [LinearMap.lTensor_tmul]
      change restrictionBaseChange B f (b ⊗ₜ[R.obj X, (R.map f).hom] ψ.app X k) =
        ψ.app Y (restrictionBaseChange A f (b ⊗ₜ[R.obj X, (R.map f).hom] k))
      rw [restrictionBaseChange_tmul, restrictionBaseChange_tmul,
        ← PresheafOfModules.naturality_apply]
      exact ((ψ.app Y).hom.map_smul b (A.map f k)).symm
  have hGb : Function.Bijective (θ G) := (ConcreteCategory.isIso_iff_bijective _).mp hG
  have hFb : Function.Bijective (θ F) := (ConcreteCategory.isIso_iff_bijective _).mp hF
  have hlex : Function.Exact (ιX.lTensor (R.obj Y)) (φX.lTensor (R.obj Y)) :=
    Module.Flat.lTensor_exact (R.obj Y) (hex X)
  have hlinj : Function.Injective (ιX.lTensor (R.obj Y)) :=
    Module.Flat.lTensor_preserves_injective_linearMap ιX (hι X)
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (θ K)
  refine ⟨fun z z' hzz ↦ hlinj <| hGb.1 <|
    (nat ι z).trans <| (congrArg _ hzz).trans (nat ι z').symm, fun k ↦ ?_⟩
  obtain ⟨t, ht⟩ := hGb.2 (ι.app Y k)
  obtain ⟨s, hs⟩ := (hlex t).mp <| hFb.1 <| (nat φ t).trans <| by
    rw [ht, map_zero]
    exact (hex Y).apply_apply_eq_zero k
  exact ⟨s, hι Y ((nat ι s).symm.trans ((congrArg (θ G) hs).trans ht))⟩

end Stacks.PresheafOfModules

namespace Stacks.FlatAffineSite

open Stacks.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (L : C ⥤ Scheme.{u}) (Q : MorphismProperty C)

/-- **Flat factorizations**: every morphism `h : Y ⟶ X` becomes, on the members `r i` of a cover of
`Y`, a composite `r i ≫ h = s ≫ b` where `s ≫ a = t` and `a`, `b`, `t` have flat underlying
morphisms of schemes. -/
def HasFlatFactorizations : Prop :=
  ∀ ⦃X Y : C⦄ (h : Y ⟶ X), ∃ (I : Type w) (W : I → C) (r : ∀ i, W i ⟶ Y), IsCover L Q r ∧
    ∀ i, ∃ (Z : C) (s : W i ⟶ Z) (a : Z ⟶ Y) (b : Z ⟶ X) (t : W i ⟶ Y),
      Flat (L.map a) ∧ Flat (L.map b) ∧ Flat (L.map t) ∧ s ≫ a = t ∧ s ≫ b = r i ≫ h

variable {L Q}

/-- **On a site with flat factorizations, a module cartesian over every flat morphism is cartesian
over every morphism.** -/
theorem isIso_restrictionBaseChange_of_hasFlatFactorizations [∀ X, IsAffine (L.obj X)]
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f))
    (hfac : HasFlatFactorizations.{w} L Q)
    (M : PresheafOfModules.{max m u} (rings L ⋙ forget₂ CommRingCat RingCat))
    (hflat : ∀ ⦃X Y : C⦄ (a : X ⟶ Y), Flat (L.map a) →
      IsIso (restrictionBaseChange.{u₁, v₁, u, m} M a.op))
    {X Y : C} (h : Y ⟶ X) : IsIso (restrictionBaseChange.{u₁, v₁, u, m} M h.op) := by
  obtain ⟨I, W, r, hr, hdata⟩ := hfac h
  have := hr.finite
  have hcr : ∀ i, IsIso (restrictionBaseChange.{u₁, v₁, u, m} M (r i).op) := fun i =>
    hflat _ (hQ _ (hr.mem i))
  have hcrh : ∀ i, IsIso (restrictionBaseChange.{u₁, v₁, u, m} M (r i ≫ h).op) := by
    intro i
    obtain ⟨Z, s, a, b, t, ha, hb, ht, hsa, hsb⟩ := hdata i
    have hs : IsIso (restrictionBaseChange.{u₁, v₁, u, m} M s.op) :=
      isIso_restrictionBaseChange_of_comp_left.{u₁, v₁, u, m} M a.op s.op (hflat a ha)
        (by rw [← op_comp, hsa]; exact hflat t ht)
    rw [← hsb, op_comp]
    exact isIso_restrictionBaseChange_comp M b.op s.op (hflat b hb) hs
  exact isIso_restrictionBaseChange_of_faithfullyFlat_family M h W r
    (faithfullyFlat_rings hQ hr) hcr hcrh

/-- **On a site with flat factorizations the kernel of a map of cartesian modules is
cartesian.** -/
theorem isIso_restrictionBaseChange_kernel [∀ X, IsAffine (L.obj X)]
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f))
    (hfac : HasFlatFactorizations.{w} L Q)
    {K G F : PresheafOfModules.{max m u} (rings L ⋙ forget₂ CommRingCat RingCat)}
    (ι : K ⟶ G) (φ : G ⟶ F) (hι : ∀ X, Function.Injective (ι.app X))
    (hex : ∀ X, Function.Exact (ι.app X) (φ.app X))
    (hG : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), IsIso (restrictionBaseChange.{u₁, v₁, u, m} G f))
    (hF : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y), IsIso (restrictionBaseChange.{u₁, v₁, u, m} F f))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) : IsIso (restrictionBaseChange.{u₁, v₁, u, m} K f) :=
  isIso_restrictionBaseChange_of_hasFlatFactorizations hQ hfac K
    (fun _ _ a ha => isIso_restrictionBaseChange_of_exact ι φ hι hex a.op
      (flat_rings_map a ha) (hG _) (hF _)) f.unop

end Stacks.FlatAffineSite

end
