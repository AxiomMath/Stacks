module

public import StacksFrontier.AlgebraicGeometry.Discriminant.CommonRefinement
public import StacksFrontier.AlgebraicGeometry.Discriminant.DualizingBaseChange.Independence
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceCondition
public import StacksFrontier.RingTheory.TraceElement.FiniteFactor
public import StacksFrontier.RingTheory.TraceElement.ProjectiveTrace

/-!
# The trace-element condition is independent of the factorization

The relative dualizing module of a flat quasi-finite map `A → B` of Noetherian rings is
presented by a choice of finite-open factorization, and two choices are identified by the
canonical comparison `Stacks.Discriminant.dualizingModuleEquiv`. This file shows that the
trace-element condition of Tag 0BT6 is carried along that identification, so that it is a
property of the dualizing module and not of the presentation.

The point is that the restriction map to a finite direct factor `C` does not depend on the
factorization either. Two factorizations are dominated by a common refinement `H` embedded in
the target, and over `H` the comparison is computed on pure tensors; on the trace side, `C` is
already a module over the intermediate algebra of either factorization, and the two traces of
multiplication differ by the map of intermediate algebras because `C` absorbs the scalar
extension along a ring epimorphism.

## Main results

* `Stacks.Discriminant.exists_tensorEquiv_of_isEpi`: for a ring epimorphism `R → B` and an
  algebra `C` over `B` flat over `R`, an intermediate ring `H` injecting into `B` satisfies
  `H ⊗_R C ≅ C`.
* `Stacks.Discriminant.finiteProjectiveTrace_lmul_of_refinement`: the trace of multiplication
  over a refinement of a factorization is the image of the trace over the factorization.
* `Stacks.Discriminant.factorRestriction_congr`: the restriction to a finite factor commutes
  with the canonical comparison of dualizing modules.
* `Stacks.Discriminant.isTraceElement_congr`: Tag 0BT6, independence of factorization.

## References

* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
-/

@[expose] public section

open scoped TensorProduct

universe u v w x y z s t r p q

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-- Let `R → B` be a ring epimorphism and `C` an algebra over `B` that is flat over `R`. For
an intermediate ring `H` injecting into `B`, multiplication is an isomorphism
`H ⊗_R C ≅ C`. This is what makes the trace over `H` computable from the trace over `R`. -/
theorem exists_tensorEquiv_of_isEpi {R B H C : Type*}
    [CommRing R] [CommRing B] [CommRing H] [CommRing C]
    [Algebra R B] [Algebra R H] [Algebra H B] [IsScalarTower R H B]
    [Algebra R C] [Algebra B C] [Algebra H C] [IsScalarTower R B C] [IsScalarTower R H C]
    [Algebra.IsEpi R B] [Module.Flat R C]
    (f : H →ₐ[R] B) (hf : Function.Injective f)
    (hcompat : ∀ h : H, algebraMap H C h = algebraMap B C (f h)) :
    ∃ e : H ⊗[R] C ≃ₗ[H] C, ∀ h c, e (h ⊗ₜ[R] c) = algebraMap H C h * c := by
  let μB : B ⊗[R] C ≃ₗ[B] C := TensorProduct.lid' R B C
  let j : H ⊗[R] C →ₗ[R] B ⊗[R] C :=
    TensorProduct.map f.toLinearMap (LinearMap.id : C →ₗ[R] C)
  have hj : Function.Injective j :=
    Module.Flat.rTensor_preserves_injective_linearMap f.toLinearMap hf
  let μH : H ⊗[R] C →ₗ[H] C := LinearMap.liftBaseChange H (LinearMap.id : C →ₗ[R] C)
  have hcomp : (μB.toLinearMap.restrictScalars R).comp j = μH.restrictScalars R := by
    ext h c
    change μB (f h ⊗ₜ[R] c) = μH (h ⊗ₜ[R] c)
    simp only [μB, μH, TensorProduct.lid'_apply_tmul, LinearMap.liftBaseChange_tmul,
      LinearMap.id_apply, Algebra.smul_def, hcompat]
  have hμH : Function.Injective μH := by
    rw [← LinearMap.coe_restrictScalars R μH, ← hcomp, LinearMap.coe_comp]
    exact μB.injective.comp hj
  refine ⟨LinearEquiv.ofBijective μH ⟨hμH, fun c => ⟨1 ⊗ₜ[R] c, by simp [μH]⟩⟩, fun h c => ?_⟩
  change μH (h ⊗ₜ[R] c) = _
  simp [μH, Algebra.smul_def]

/-- For a refinement `H` of a factorization `F`, the module `C` absorbs the scalar extension from
`F.middle` to `H.middle`, and `C` is a scalar tower over both. -/
private theorem isScalarTower_and_exists_tensorEquiv_of_refinement
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    (F : FiniteOpenFactorization A B) (H : FiniteOpenFactorization A B)
    [Algebra B C] [Algebra F.middle C] [Algebra H.middle C] [Algebra F.middle H.middle]
    [Module.Finite F.middle C] [Module.Projective F.middle C]
    (hH : Function.Injective (algebraMap H.middle B))
    (hr : ∀ a, algebraMap H.middle B (algebraMap F.middle H.middle a) = algebraMap F.middle B a)
    (hFC : ∀ a, algebraMap F.middle C a = algebraMap B C (algebraMap F.middle B a))
    (hHC : ∀ a, algebraMap H.middle C a = algebraMap B C (algebraMap H.middle B a)) :
    IsScalarTower F.middle H.middle C ∧ ∃ e : H.middle ⊗[F.middle] C ≃ₗ[H.middle] C,
      ∀ h c, e (h ⊗ₜ[F.middle] c) = algebraMap H.middle C h * c := by
  have : IsScalarTower F.middle H.middle B := IsScalarTower.of_algebraMap_eq fun a => (hr a).symm
  have : IsScalarTower F.middle B C := IsScalarTower.of_algebraMap_eq hFC
  have : IsScalarTower F.middle H.middle C := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply F.middle B C, ← hr, ← hHC]
  have : Algebra.IsEpi F.middle B := isEpi_of_finiteOpenFactorization F
  exact ⟨inferInstance, exists_tensorEquiv_of_isEpi (IsScalarTower.toAlgHom F.middle H.middle B)
    hH hHC⟩

/-- The trace of multiplication over the intermediate algebra of a refinement is the image,
under the map of intermediate algebras, of the trace over the original factorization. -/
theorem finiteProjectiveTrace_lmul_of_refinement
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    (F : FiniteOpenFactorization A B) (H : FiniteOpenFactorization A B)
    [Algebra B C] [Algebra F.middle C] [Algebra H.middle C]
    [Module.Finite F.middle C] [Module.Projective F.middle C]
    [Module.Finite H.middle C] [Module.Projective H.middle C]
    (hH : Function.Injective (algebraMap H.middle B))
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ a, algebraMap H.middle B (r a) = algebraMap F.middle B a)
    (hFC : ∀ a, algebraMap F.middle C a = algebraMap B C (algebraMap F.middle B a))
    (hHC : ∀ a, algebraMap H.middle C a = algebraMap B C (algebraMap H.middle B a)) (c : C) :
    finiteProjectiveTrace H.middle C (Algebra.lmul H.middle C c) =
      r (finiteProjectiveTrace F.middle C (Algebra.lmul F.middle C c)) := by
  let : Algebra F.middle H.middle := r.toRingHom.toAlgebra
  obtain ⟨_, e, he⟩ := isScalarTower_and_exists_tensorEquiv_of_refinement F H hH hr hFC hHC
  exact finiteProjectiveTrace_lmul_algebraMap e he c

/-- The restriction to a finite direct factor does not depend on the finite-open factorization
used to present the dualizing module: it commutes with the canonical comparison. Both
restrictions are given only by their pure-tensor formula, which is what makes the statement a
statement about the trace rather than about a particular construction. -/
theorem factorRestriction_congr
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [IsNoetherianRing A] [Module.Finite A C] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization A B) (G : FiniteOpenFactorization A B)
    [Algebra F.middle C] [Algebra G.middle C]
    [Module.Finite F.middle C] [Module.Projective F.middle C]
    [Module.Finite G.middle C] [Module.Projective G.middle C]
    (hFC : ∀ a, algebraMap F.middle C a = algebraMap B C (algebraMap F.middle B a))
    (hGC : ∀ a, algebraMap G.middle C a = algebraMap B C (algebraMap G.middle B a))
    (lF : dualizingModule F →+ Module.Dual A C)
    (lG : dualizingModule G →+ Module.Dual A C)
    (hlF : ∀ f b c, lF (dualizingModule.tmul F f b) c =
      f (finiteProjectiveTrace F.middle C (Algebra.lmul F.middle C (algebraMap B C b * c))))
    (hlG : ∀ f b c, lG (dualizingModule.tmul G f b) c =
      f (finiteProjectiveTrace G.middle C (Algebra.lmul G.middle C (algebraMap B C b * c))))
    (ω : dualizingModule F) :
    lG (dualizingModuleEquiv F G ω) = lF ω := by
  obtain ⟨H, ⟨rF, rG⟩, hrF, hrG, hH⟩ := commonFiniteOpenRefinement F G
  let : Algebra H.middle C := ((algebraMap B C).comp (algebraMap H.middle B)).toAlgebra
  have hHC (a : H.middle) : algebraMap H.middle C a =
      algebraMap B C (algebraMap H.middle B a) := rfl
  let : Algebra F.middle H.middle := rF.toRingHom.toAlgebra
  obtain ⟨_, e, -⟩ := isScalarTower_and_exists_tensorEquiv_of_refinement F H hH hrF hFC hHC
  have : Module.Finite H.middle C := Module.Finite.of_surjective e.toLinearMap e.surjective
  have : Module.Projective H.middle C := Module.Projective.of_equiv' e
  obtain ⟨η, rfl⟩ := (dualizingModuleEquiv H F).surjective ω
  rw [← LinearEquiv.trans_apply, dualizingModuleEquiv_trans]
  induction η using dualizingModule.induction_on with
  | tmul f b =>
    have hF := dualizingModuleEquiv_tmul H F H hH (AlgHom.id A H.middle) rF (fun _ => rfl) hrF f b
    have hG := dualizingModuleEquiv_tmul H G H hH (AlgHom.id A H.middle) rG (fun _ => rfl) hrG f b
    simp only [AlgHom.toLinearMap_id, LinearMap.comp_id] at hF hG
    rw [hF, hG]
    ext c
    rw [hlF, hlG]
    change f (rG _) = f (rF _)
    rw [← finiteProjectiveTrace_lmul_of_refinement G H hH rG hrG hGC hHC,
      ← finiteProjectiveTrace_lmul_of_refinement F H hH rF hrF hFC hHC]
  | add η θ hη hθ => simp only [map_add, hη, hθ]

/-- The trace-element condition is carried along the canonical comparison of dualizing
modules in one direction; `Stacks.Discriminant.isTraceElement_congr` upgrades this to an
equivalence. -/
theorem isTraceElement_of_dualizingModuleEquiv
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (τ : dualizingModule F) (hτ : IsTraceElement.{u, v, w, p, q, r} F τ) :
    IsTraceElement.{u, v, x, p, q, r} G (dualizingModuleEquiv F G τ) := by
  intro A₁ _ _ _ C D _ _ _ _ e hfinite
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  let G₁ := FiniteOpenFactorization.baseChange G A₁
  have : Module.Finite A₁ C := hfinite
  let : Algebra (A₁ ⊗[A] B) C := ((RingHom.fst C D).comp e.toRingEquiv.toRingHom).toAlgebra
  have : IsScalarTower A₁ (A₁ ⊗[A] B) C := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A₁ C a = (e (algebraMap A₁ (A₁ ⊗[A] B) a)).1
    rw [e.commutes]
    rfl
  let : Algebra F₁.middle C :=
    ((RingHom.fst C D).comp (e.toRingEquiv.toRingHom.comp F₁.algebraTarget.algebraMap)).toAlgebra
  let : Algebra G₁.middle C :=
    ((RingHom.fst C D).comp (e.toRingEquiv.toRingHom.comp G₁.algebraTarget.algebraMap)).toAlgebra
  let : Algebra G₁.middle D :=
    ((RingHom.snd C D).comp (e.toRingEquiv.toRingHom.comp G₁.algebraTarget.algebraMap)).toAlgebra
  have : IsScalarTower A₁ G₁.middle C := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A₁ C a =
      (e (algebraMap G₁.middle (A₁ ⊗[A] B) (algebraMap A₁ G₁.middle a))).1
    rw [← IsScalarTower.algebraMap_apply A₁ G₁.middle (A₁ ⊗[A] B), e.commutes]
    rfl
  have : IsScalarTower A₁ G₁.middle D := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap A₁ D a =
      (e (algebraMap G₁.middle (A₁ ⊗[A] B) (algebraMap A₁ G₁.middle a))).2
    rw [← IsScalarTower.algebraMap_apply A₁ G₁.middle (A₁ ⊗[A] B), e.commutes]
    rfl
  obtain ⟨hp, hmF, hpF, hres⟩ := hτ A₁ C D e hfinite
  have : Module.Projective A₁ C := hp
  have : Module.Finite F₁.middle C := hmF
  have : Module.Projective F₁.middle C := hpF
  have : Module.Finite G₁.middle C := Module.Finite.of_restrictScalars_finite A₁ G₁.middle C
  have : Module.Flat G₁.middle (A₁ ⊗[A] B) := flat_of_finiteOpenFactorization G₁
  have : Module.Projective G₁.middle C := projective_of_prodEquiv_of_finite e fun _ => rfl
  refine ⟨hp, inferInstance, inferInstance, ?_⟩
  let ρF := finiteFactorRestriction F A₁ C D e (fun _ => rfl) hfinite hp hmF hpF
  let ρG := finiteFactorRestriction G A₁ C D e (fun _ => rfl) hfinite hp inferInstance
    inferInstance
  have hcmp := factorRestriction_congr F₁ G₁ (fun _ => rfl) (fun _ => rfl)
    ρF.1.toAddMonoidHom ρG.1.toAddMonoidHom ρF.2 ρG.2 (dualizingModule.baseChange F A₁ τ)
  rw [dualizingModule.baseChange_congr F G A₁ τ] at hcmp
  exact hcmp.trans hres

/-- **Stacks Project, Tag 0BT6.** The trace-element condition does not depend on the
finite-open factorization chosen to represent the relative dualizing module. The three test
universes are independent of each other and of the universes of the two factorizations. -/
@[stacks 0BT6 "trace_element_property; independence of factorization"]
theorem isTraceElement_congr
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B] [Algebra.QuasiFinite A B]
    (F : FiniteOpenFactorization.{u, v, w} A B)
    (G : FiniteOpenFactorization.{u, v, x} A B)
    (τ : dualizingModule F) :
    IsTraceElement.{u, v, w, s, t, r} F τ ↔
      IsTraceElement.{u, v, x, s, t, r} G (dualizingModuleEquiv F G τ) := by
  refine ⟨isTraceElement_of_dualizingModuleEquiv F G τ, fun hτ => ?_⟩
  have h := isTraceElement_of_dualizingModuleEquiv G F _ hτ
  rwa [← LinearEquiv.trans_apply, dualizingModuleEquiv_trans, dualizingModuleEquiv_refl,
    LinearEquiv.refl_apply] at h

end Stacks.Discriminant

end
