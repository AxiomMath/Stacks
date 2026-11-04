module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.CohomologyReduction

/-!
# The step `πᵏ F` of the adic filtration as an additive functor

For a morphism `f : X ⟶ Spec A` and `π ∈ A`, every morphism of modules `F ⟶ G` carries `πᵏ F`
into `πᵏ G`, so `F ↦ πᵏ F` is a functor on `X.Modules`, and it is additive. Hence it commutes
with finite direct sums, and so does its first cohomology: `H¹(X, πᵏ 𝒪_X^r)` is the `r`-th power
of `H¹(X, πᵏ 𝒪_X)`. This is what makes the torsion exponent of [Stacks, Tag 0EXF] independent of
the rank: a single exponent `e` for `H¹(X, πᵏ 𝒪_X)` serves every `H¹(X, πᵏ 𝒪_X^r)`.

## Main definitions

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `adicSub`, `adicSubι`: the subsheaf `πᵏ M` and its inclusion, as an object and a morphism of
  `X.Modules`.
* `adicFiltrationFunctor`: the functor `F ↦ πᵏ F`, which is additive.
* `cohomologyAdicFiltrationFunctor`: the functor `F ↦ Hⁱ(X, πᵏ F)`, valued in `A`-modules.

## Main results

* `cohomologyAdicFiltrationFreeEquiv`: `Hⁱ(X, πᵏ 𝒪_X^r) ≃ (Hⁱ(X, πᵏ 𝒪_X))^r`.
* `exists_pow_smul_cohomology_adicSub_free_eq_zero`: **one torsion exponent for every rank.**

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.BaseAdicFiltration Stacks.Algebraization

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (π : A)

/-- The subsheaf `πᵏ M`, as an object of `X.Modules`. -/
def adicSub (k : ℕ) (M : X.Modules) : X.Modules :=
  (adicFiltration f (Ideal.span {π}) k M).toSheafOfModules

/-- The inclusion `πᵏ M ⟶ M`, as a morphism of `X.Modules`. -/
def adicSubι (k : ℕ) (M : X.Modules) : adicSub f π k M ⟶ M :=
  (adicFiltration f (Ideal.span {π}) k M).ι

/-- The inclusion `πᵏ M ⟶ M` is a monomorphism. -/
instance mono_adicSubι (k : ℕ) (M : X.Modules) : Mono (adicSubι f π k M) :=
  Scheme.Modules.mono_submodule_ι _

/-- A morphism `M ⟶ N` restricted to `πᵏ M ⟶ πᵏ N`. -/
def adicFiltrationMap (k : ℕ) {M N : X.Modules} (φ : M ⟶ N) :
    adicSub f π k M ⟶ adicSub f π k N :=
  sheafSubmoduleMap φ _ _ (idealPowerMultiple_le_sheafSubmoduleComap _ k φ _ le_rfl)

/-- The restriction `πᵏ M ⟶ πᵏ N` of `φ : M ⟶ N` commutes with the inclusions into `M` and `N`. -/
@[reassoc]
theorem adicFiltrationMap_comp_ι (k : ℕ) {M N : X.Modules} (φ : M ⟶ N) :
    adicFiltrationMap f π k φ ≫ adicSubι f π k N = adicSubι f π k M ≫ φ :=
  sheafSubmoduleMap_comp_ι _ _ _ _

/-- The functor `F ↦ πᵏ F` on sheaves of modules. -/
def adicFiltrationFunctor (k : ℕ) : X.Modules ⥤ X.Modules where
  obj M := adicSub f π k M
  map φ := adicFiltrationMap f π k φ
  map_id M := by
    refine (mono_adicSubι f π k M).right_cancellation _ _ ?_
    rw [adicFiltrationMap_comp_ι, Category.comp_id, Category.id_comp]
  map_comp {M N P} φ ψ := by
    refine (mono_adicSubι f π k P).right_cancellation _ _ ?_
    rw [adicFiltrationMap_comp_ι, Category.assoc, adicFiltrationMap_comp_ι,
      adicFiltrationMap_comp_ι_assoc]

/-- `F ↦ πᵏ F` is an additive functor. -/
instance adicFiltrationFunctor_additive (k : ℕ) : (adicFiltrationFunctor f π k).Additive where
  map_add {M N} φ ψ := by
    refine (mono_adicSubι f π k N).right_cancellation _ _ ?_
    change adicFiltrationMap f π k (φ + ψ) ≫ adicSubι f π k N =
      (adicFiltrationMap f π k φ + adicFiltrationMap f π k ψ) ≫ adicSubι f π k N
    rw [adicFiltrationMap_comp_ι, Preadditive.add_comp, adicFiltrationMap_comp_ι,
      adicFiltrationMap_comp_ι, Preadditive.comp_add]

/-- Finite biproducts of sheaves of modules on a scheme. -/
local instance hasFiniteBiproducts_modules : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Finite biproducts of sheaves of modules on a scheme, in the `SheafOfModules` spelling. -/
local instance hasFiniteBiproducts_sheafOfModules :
    HasFiniteBiproducts (SheafOfModules.{u} X.ringCatSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The structure sheaf, as an object of `X.Modules`. -/
abbrev unitX : X.Modules := SheafOfModules.unit X.ringCatSheaf

variable (A) in
/-- The functor `F ↦ Hⁱ(X, πᵏ F)`, valued in `A`-modules. -/
abbrev cohomologyAdicFiltrationFunctor (k i : ℕ) : X.Modules ⥤ ModuleCat.{u} A :=
  adicFiltrationFunctor f π k ⋙
    (Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i ⋙
      ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom

/-- **`Hⁱ(X, πᵏ 𝒪_X^r)` is the `r`-th power of `Hⁱ(X, πᵏ 𝒪_X)`.** -/
def cohomologyAdicFiltrationFreeEquiv (k i r : ℕ) :
    cohomologyOver A f i (adicSub f π k (Scheme.Modules.free X (ULift.{u} (Fin r)))) ≃ₗ[A]
      (Fin r → cohomologyOver A f i (adicSub f π k unitX)) := by
  let e1 : Scheme.Modules.free X (ULift.{u} (Fin r)) ≅ ⨁ (fun _ : Fin r => (unitX : X.Modules)) :=
    (biproduct.isoCoproduct (C := X.Modules) (fun _ : ULift.{u} (Fin r) => unitX)).symm ≪≫
      biproduct.whiskerEquiv (f := fun _ : ULift.{u} (Fin r) => (unitX : X.Modules))
        (g := fun _ : Fin r => (unitX : X.Modules)) Equiv.ulift (fun _ => Iso.refl _)
  exact (((cohomologyAdicFiltrationFunctor A f π k i).mapIso e1 ≪≫
    (cohomologyAdicFiltrationFunctor A f π k i).mapBiproduct
      (fun _ : Fin r => (unitX : X.Modules)) ≪≫
      ModuleCat.biproductIsoPi _).toLinearEquiv)

/-- **One torsion exponent for every rank.** For `f` proper over a Noetherian ring there is an
exponent `e` such that, for every `r`, the `π`-power torsion of `H¹(X, πᵏ 𝒪_X^r)` is killed by
`πᵉ`: take `e` for the finite module `H¹(X, πᵏ 𝒪_X)`, of which `H¹(X, πᵏ 𝒪_X^r)` is the `r`-th
power. -/
theorem exists_pow_smul_cohomology_adicSub_free_eq_zero [IsNoetherianRing A] [IsProper f]
    [IsLocallyNoetherian X] (k : ℕ) :
    ∃ e : ℕ, ∀ (r : ℕ) (c : cohomologyOver A f 1
        (adicSub f π k (Scheme.Modules.free X (ULift.{u} (Fin r))))) (i : ℕ),
      π ^ i • c = 0 → π ^ e • c = 0 := by
  have : (unitX : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
  have : (adicSub f π k unitX).IsCoherent := isCoherent_adicFiltration A f π (unitX : X.Modules) k
  have := moduleFinite_cohomologyOver A f (adicSub f π k unitX) 1
  obtain ⟨e, he⟩ := exists_forall_pow_smul_torsionBy_eq_bot (A := A)
    (H := cohomologyOver A f 1 (adicSub f π k unitX)) π
  refine ⟨e, fun r c i hc => ?_⟩
  let L := cohomologyAdicFiltrationFreeEquiv f π k 1 r
  refine L.injective ?_
  rw [map_smul, map_zero]
  funext j
  have hj : π ^ i • L c j = 0 := by
    have := congrFun (show π ^ i • L c = 0 by rw [← map_smul, hc, map_zero]) j
    simpa using this
  have := (pow_smul_torsionBy_eq_bot_iff.1 (he i)) (L c j) hj
  simpa using this

end Stacks.AlgebraicGeometry.FreenessOverDVR
