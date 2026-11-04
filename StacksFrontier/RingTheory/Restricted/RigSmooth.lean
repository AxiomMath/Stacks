module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.RingTheory.Restricted.NaiveCotangentHomotopy
public import StacksFrontier.RingTheory.Rig.NaiveCotangent
public import StacksFrontier.RingTheory.Rig.RigSmoothDefs

/-!
# Rig-smooth adic algebras

Let `A` be a Noetherian ring, `I` an ideal of `A`, and `B` an `I`-adically complete `A`-algebra
of finite type modulo `I`. The algebra `B` is rig-smooth over `(A, I)` when one power of `I`
annihilates `Ext¹` from its completed naive cotangent complex to every `B`-module.

## Main results

* `Rig.isRigSmooth_iff`: rig-smoothness may be tested on any single chosen completed
  polynomial presentation.

## Implementation notes

The condition itself, `Rig.IsRigSmooth` (**Stacks 0GAI**), is defined in
`StacksFrontier.RingTheory.Rig.RigSmoothDefs` and imported here; this module is the
presentation-independence half of it.

The completed naive cotangent complex is represented by the two-term cochain complex attached
to a completed polynomial presentation, so the condition is imposed for some such presentation.
The exponent is uniform in the module and in the `Ext` class. That one presentation suffices is
`isRigSmooth_iff`, which transports the annihilation along the homotopy equivalence of
Stacks 0GAE (`Rig.completedNaiveCotangentComplex_homotopyEquiv`).

The action of `I` on `Ext` is expressed through its image in `B`: every element of `I ^ c` acts
trivially on every `Ext` class. The derived-category `Ext` group is taken with the module placed
in degree zero.

## References

* [Stacks Project, Tag 0GAI](https://stacks.math.columbia.edu/tag/0GAI)
* [Stacks Project, Tag 0GAE](https://stacks.math.columbia.edu/tag/0GAE)
-/

@[expose] public noncomputable section

open CategoryTheory
open Rig.CompletedPolynomialPresentation

universe u v

namespace Rig

attribute [local instance] HasDerivedCategory.standard

private theorem ext_annihilation_of_homotopyEquiv
    {A : Type u} [CommRing A] {I : Ideal A}
    {B : AdicFiniteTypeAlgebra.{u, v} A I}
    {K L : CochainComplex (ModuleCat.{max u v} B.carrier) ℤ}
    (e : HomotopyEquiv K L) (c : ℕ)
    (h : ∀ (N : ModuleCat.{max u v} B.carrier)
      (x : DerivedCategory.Ext (DerivedCategory.Q.obj K)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      ∀ a : A, a ∈ I ^ c → (algebraMap A B.carrier a) • x = 0) :
    ∀ (N : ModuleCat.{max u v} B.carrier)
      (x : DerivedCategory.Ext (DerivedCategory.Q.obj L)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      ∀ a : A, a ∈ I ^ c → (algebraMap A B.carrier a) • x = 0 := by
  have he : QuasiIso e.hom := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso (e.toHomologyIso i).hom
    infer_instance
  let α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L := DerivedCategory.Q.map e.hom
  let β : DerivedCategory.Q.obj L ⟶ DerivedCategory.Q.obj K := DerivedCategory.Q.map e.inv
  have hβα : β ≫ α = 𝟙 _ := by
    dsimp [α, β]
    calc
      DerivedCategory.Q.map e.inv ≫ DerivedCategory.Q.map e.hom =
          DerivedCategory.Q.map (e.inv ≫ e.hom) := by rw [DerivedCategory.Q.map_comp]
      _ = DerivedCategory.Q.map (𝟙 _) := DerivedCategory.Q_map_eq_of_homotopy
        (ModuleCat.{max u v} B.carrier) e.homotopyInvHomId
      _ = 𝟙 _ := by simp
  intro N x a ha
  have hkill : (algebraMap A B.carrier a) • (α ≫ x) = 0 := by
    simpa only [ShiftedHom.mk₀_comp] using
      h N ((ShiftedHom.mk₀ 0 rfl α).comp x (by simp)) a ha
  have hpre := congrArg (fun z => β ≫ z) hkill
  rw [CategoryTheory.Linear.comp_smul, ← Category.assoc] at hpre
  simpa [hβα] using hpre

/-- Rig-smoothness can be tested on any fixed completed polynomial presentation of `B`.
The exponent is uniform over all `B`-modules and their Ext classes. -/
theorem isRigSmooth_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    IsRigSmooth B ↔
      ∃ c : ℕ, ∀ (N : ModuleCat.{max u v} B.carrier)
        (x : DerivedCategory.Ext
          (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
        ∀ a : A, a ∈ I ^ c → (algebraMap A B.carrier a) • x = 0 := by
  refine ⟨fun ⟨P₀, c, h⟩ => ?_, fun ⟨c, h⟩ => ⟨P, c, h⟩⟩
  obtain ⟨e⟩ := completedNaiveCotangentComplex_homotopyEquiv (A := A) I B P₀ P
  exact ⟨c, ext_annihilation_of_homotopyEquiv e c h⟩

end Rig

end
