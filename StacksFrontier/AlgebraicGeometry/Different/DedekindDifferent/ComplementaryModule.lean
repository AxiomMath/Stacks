module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Different.Support.DedekindDifferentSetup
public import StacksFrontier.AlgebraicGeometry.Discriminant.ProjectiveTraceContraction
public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceElement

/-!
# The Dedekind complementary module is the relative dualizing module

When the Dedekind different of a finite ring map `A → B` is defined, the trace pairing of the
generic fibre identifies the complementary module with the relative dualizing module
`Hom_A(B, A)` of the finite map.

## Main definitions

* `Stacks.Discriminant.complementaryModuleEquivDualizingModuleWithFormula` is the canonical
  linear equivalence from the Dedekind complementary module to `Hom_A(B, A)`, packaged with its
  defining formula.
* `Stacks.Discriminant.complementaryModuleEquivDualizingModule` is the underlying equivalence.

## Main results

* `Stacks.Discriminant.complementaryModuleEquivDualizingModule_apply` is the defining formula:
  the image of `x` is the functional `b ↦ Tr(bx)`.

## Implementation notes

For a finite map the relative dualizing module is `Hom_A(B, A)`, with the `B`-action
`Stacks.Discriminant.algebraDualModule`. The equivalence is packaged together with its
characterization, so its value is pinned down without unfolding an opaque choice. The defining
equation is written after applying `A → Q(A)`, because membership in the complementary module is
what supplies the element of `A` representing the trace, and the canonical map `A → Q(A)` is
injective.

The generic fibre is étale over the total quotient ring, hence finite projective over it, so its
trace pairing is a perfect pairing by
`Stacks.Discriminant.finiteProjectiveTraceForm_bijective_of_etale`. Transporting a functional on
`B` to one on the generic fibre is localization of modules, which is where the hypothesis that
nonzerodivisors stay nonzerodivisors is not needed: only the localization `A → Q(A)` is used.

## References

* [Stacks Project, Tag 0BW2](https://stacks.math.columbia.edu/tag/0BW2)
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace Stacks.Discriminant

universe u v

attribute [local instance] algebraDualModule

/-- **Stacks Project, Tag 0BW2.** The trace pairing canonically identifies the Dedekind
complementary module with the relative dualizing module `Hom_A(B, A)` of a finite map, together
with the formula characterizing it: the image of `x` is the functional `b ↦ Tr(bx)`. -/
@[stacks 0BW2]
def complementaryModuleEquivDualizingModuleWithFormula
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (setup : DedekindDifferentSetup A B) :
    { e : setup.complementaryModule ≃ₗ[B] Module.Dual A B //
      ∀ (x : setup.complementaryModule) (b : B),
        algebraMap A (FractionRing A) (e x b) =
          setup.trace
            (algebraMap B (B ⊗[A] FractionRing A) b *
              (x : B ⊗[A] FractionRing A)) } := by
  classical
  let S := nonZeroDivisors A
  let K := FractionRing A
  let L := B ⊗[A] K
  let _ : Module.Finite A B := setup.finite
  let _ : Algebra K L := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra.Etale K L := setup.etaleGenericFiber
  let _ : Module.Finite K (K ⊗[A] B) := Module.Finite.base_change A K B
  let eKB : (K ⊗[A] B) ≃ₐ[K] L := Algebra.TensorProduct.commRight A K B
  let _ : Module.Finite K L := Module.Finite.equiv eKB.toLinearEquiv
  let _ : Algebra.Smooth K L := inferInstance
  let _ : Module.Flat K L := Algebra.Smooth.flat K L
  let _ : Module.FinitePresentation K L :=
    Module.FinitePresentation.of_finite_of_finitePresentation K L
  let _ : Module.Projective K L := Module.Flat.projective_of_finitePresentation
  let T : L →ₗ[K] Module.Dual K L := finiteProjectiveTraceForm K L
  have hT : Function.Bijective T := finiteProjectiveTraceForm_bijective_of_etale
  let eA : LocalizedModule S A ≃ₗ[K] K :=
    (LocalizedModule.equivTensorProduct S A).trans
      (TensorProduct.AlgebraTensorModule.rid A K K)
  let eB : LocalizedModule S B ≃ₗ[K] L :=
    (LocalizedModule.equivTensorProduct S B).trans
      (Algebra.TensorProduct.commRight A K B).toLinearEquiv
  have heA (a : A) : eA (LocalizedModule.mk a (1 : S)) = algebraMap A K a := by
    simp [eA, LocalizedModule.equivTensorProduct_apply_mk,
      TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def,
      Localization.mk_one_eq_algebraMap]
  have heB (b : B) : eB (LocalizedModule.mk b (1 : S)) = algebraMap B L b := by
    change Algebra.TensorProduct.commRight A K B
      (LocalizedModule.equivTensorProduct S B (LocalizedModule.mk b 1)) = _
    rw [LocalizedModule.equivTensorProduct_apply_mk,
      Algebra.TensorProduct.commRight_tmul, Localization.mk_one_eq_algebraMap]
    simp only [map_one]
    change b ⊗ₜ[A] (1 : K) =
      Algebra.TensorProduct.includeLeftRingHom (R := A) (A := B) (B := K) b
    rfl
  let extend (φ : Module.Dual A B) : Module.Dual K L :=
    eA.toLinearMap.comp
      ((LocalizedModule.map S φ).comp eB.symm.toLinearMap)
  have hextend (φ : Module.Dual A B) (b : B) :
      extend φ (algebraMap B L b) = algebraMap A K (φ b) := by
    rw [← heB b]
    simp [extend, LocalizedModule.map_mk, heA]
  have hpair (x y : L) : T x y = setup.trace (x * y) := by
    have ht := finiteProjectiveTrace_eq_contract (R := K) (P := L)
      (Algebra.lmul K L (x * y))
    simp only [T, finiteProjectiveTraceForm, LinearMap.compr₂_apply,
      LinearMap.comp_apply]
    change finiteProjectiveTrace K L (Algebra.lmul K L (x * y)) = _
    simpa [DedekindDifferentSetup.trace] using ht
  have hAinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  let P := setup.complementaryModule
  let rep (x : P) (b : B) : A :=
    Classical.choose ((setup.mem_complementaryModule (x : L)).mp x.property b)
  have hrep (x : P) (b : B) :
      algebraMap A K (rep x b) = setup.trace (algebraMap B L b * (x : L)) :=
    Classical.choose_spec ((setup.mem_complementaryModule (x : L)).mp x.property b)
  let F : P →ₗ[B] Module.Dual A B := {
    toFun x :=
      { toFun := fun b => rep x b
        map_add' := by
          intro b c
          apply hAinj
          simpa only [map_add, add_mul, setup.trace.map_add,
            ← hrep x b, ← hrep x c] using hrep x (b + c)
        map_smul' := by
          intro a b
          apply hAinj
          change algebraMap A K (rep x (a • b)) =
            algebraMap A K (a • rep x b)
          calc
            algebraMap A K (rep x (a • b)) =
                setup.trace (algebraMap B L (a • b) * (x : L)) := hrep x (a • b)
            _ = algebraMap A K (a • rep x b) := by
                  have hmap : algebraMap B L (a • b) =
                      algebraMap K L (algebraMap A K a) * algebraMap B L b := by
                    rw [Algebra.smul_def, map_mul,
                      ← IsScalarTower.algebraMap_apply A B L a,
                      ← IsScalarTower.algebraMap_apply A K L a]
                  have hmul : algebraMap B L (a • b) * (x : L) =
                      (algebraMap A K a) • (algebraMap B L b * (x : L)) := by
                    rw [hmap, Algebra.smul_def (R := K) (A := L), mul_assoc]
                  rw [hmul, setup.trace.map_smul, ← hrep x b]
                  simp [smul_eq_mul, map_mul] }
    map_add' := by
      intro x y
      ext b
      apply hAinj
      change algebraMap A K (rep (x + y) b) =
        algebraMap A K (rep x b + rep y b)
      simpa only [map_add, Submodule.coe_add, mul_add, setup.trace.map_add,
        ← hrep x b, ← hrep y b] using hrep (x + y) b
    map_smul' := by
      intro c x
      ext b
      rw [algebraDualModule_smul_apply]
      apply hAinj
      change algebraMap A K (rep (c • x) b) =
        algebraMap A K (rep x (c * b))
      calc
        algebraMap A K (rep (c • x) b) =
            setup.trace (algebraMap B L b * ((c • x : P) : L)) := hrep (c • x) b
        _ = setup.trace (algebraMap B L (c * b) * (x : L)) := by
              congr 1
              rw [Submodule.coe_smul, Algebra.smul_def c (x : L), map_mul]
              ring
        _ = algebraMap A K (rep x (c * b)) := (hrep x (c * b)).symm }
  have hF_extend (x : P) : extend (F x) = T (x : L) := by
    have hloc : (T (x : L)).comp eB.toLinearMap =
        eA.toLinearMap.comp (LocalizedModule.map S (F x)) := by
      apply LinearMap.restrictScalars_injective A
      apply IsLocalizedModule.linearMap_ext S (Algebra.linearMap A K)
        (f := LocalizedModule.mkLinearMap S B)
      ext b
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        LocalizedModule.mkLinearMap_apply]
      change T (x : L) (eB (LocalizedModule.mk b 1)) =
        eA ((LocalizedModule.map S (F x)) (LocalizedModule.mk b 1))
      rw [heB, hpair]
      simp only [LocalizedModule.map_mk]
      rw [heA, mul_comm, ← hrep]
      rfl
    ext z
    have hz := congrArg (fun g : LocalizedModule S B →ₗ[K] K => g (eB.symm z)) hloc
    simpa [extend, LinearMap.comp_apply] using hz.symm
  have hFinj : Function.Injective F := fun x y hxy =>
    Subtype.ext <| hT.1 <| by simpa only [hF_extend] using congrArg extend hxy
  have hFsurj : Function.Surjective F := by
    intro φ
    obtain ⟨x, hx⟩ := hT.2 (extend φ)
    have hval (b : B) :
        setup.trace (algebraMap B L b * x) = algebraMap A K (φ b) := by
      calc
        setup.trace (algebraMap B L b * x) = T x (algebraMap B L b) := by
          rw [hpair, mul_comm]
        _ = extend φ (algebraMap B L b) := by rw [hx]
        _ = algebraMap A K (φ b) := hextend φ b
    have hmem : (x : L) ∈ setup.complementaryModule :=
      (setup.mem_complementaryModule (x : L)).2 fun b => ⟨φ b, (hval b).symm⟩
    refine ⟨⟨x, hmem⟩, ?_⟩
    ext b
    apply hAinj
    exact (hrep ⟨x, hmem⟩ b).trans (by simpa using hval b)
  exact ⟨LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩, hrep⟩

/-- The canonical linear equivalence from the Dedekind complementary module to the relative
dualizing module `Hom_A(B, A)` of a finite map. -/
def complementaryModuleEquivDualizingModule
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (setup : DedekindDifferentSetup A B) :
    setup.complementaryModule ≃ₗ[B] Module.Dual A B :=
  (complementaryModuleEquivDualizingModuleWithFormula setup).1

/-- The canonical equivalence sends `x` to the trace pairing against `x`. -/
theorem complementaryModuleEquivDualizingModule_apply
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (setup : DedekindDifferentSetup A B)
    (x : setup.complementaryModule) (b : B) :
    algebraMap A (FractionRing A) (complementaryModuleEquivDualizingModule setup x b) =
      setup.trace
        (algebraMap B (B ⊗[A] FractionRing A) b * (x : B ⊗[A] FractionRing A)) :=
  (complementaryModuleEquivDualizingModuleWithFormula setup).2 x b

end Stacks.Discriminant

end
