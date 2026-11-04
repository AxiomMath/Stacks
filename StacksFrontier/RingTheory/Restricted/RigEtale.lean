module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Restricted.RigSmooth
public import StacksFrontier.RingTheory.Rig.RigSmoothDefs

/-!
# Rig-étale adic algebras

Let `A` be a Noetherian ring, `I` an ideal of `A`, and `B` an `I`-adically complete `A`-algebra
of finite type modulo `I`. The algebra `B` is rig-étale over `(A, I)` when some power of `I`
annihilates its completed naive cotangent complex in the derived category of `B`-modules. A
rig-étale algebra is rig-smooth: annihilating the identity of the complex annihilates every
`Ext` class out of it, by composition.

## Main results

* `Rig.isRigEtale_iff`: rig-étaleness may be checked on any single chosen completed polynomial
  presentation.
* `Rig.isRigSmooth_of_isRigEtale`: a rig-étale adically finite type algebra is rig-smooth.

## Implementation notes

The condition itself, `Rig.IsRigEtale` (**Stacks 0GAY**), is defined in
`StacksFrontier.RingTheory.Rig.RigSmoothDefs` and imported here; this module is the
presentation-independence half of it, together with the implication to rig-smoothness.

The completed naive cotangent complex is expressed using a completed polynomial presentation.
The predicate quantifies over all such presentations, avoiding a choice, and allows the
annihilating power of `I` to depend on the presentation. It is an abbreviation, so its witness
and annihilation equation are directly available. That one presentation already suffices is
`isRigEtale_iff`, which transports the annihilation along the homotopy equivalence of
Stacks 0GAE (`Rig.completedNaiveCotangentComplex_homotopyEquiv`).

The implication to rig-smoothness picks the chosen completed polynomial presentation, uses the
annihilation of the identity it supplies, and composes it with an arbitrary `Ext` class in
degree one. This is the library's single statement of Stacks 0GB1:
`StacksFrontier.RingTheory.Rig.RigEtaleLifting`, the other half of the rig-étale theory, supplies
that step only pointwise, as `Rig.ext_eq_zero_of_smul_id_eq_zero`, and is a sibling of this
module rather than a dependency of it.

## References

* [Stacks Project, Tag 0GAY](https://stacks.math.columbia.edu/tag/0GAY)
* [Stacks Project, Tag 0GB1](https://stacks.math.columbia.edu/tag/0GB1)
* [Stacks Project, Tag 0GAE](https://stacks.math.columbia.edu/tag/0GAE)
-/

@[expose] public noncomputable section

open CategoryTheory
open Rig.CompletedPolynomialPresentation

universe u v

namespace Rig

attribute [local instance] HasDerivedCategory.standard

private theorem scalar_id_eq_zero_iff_of_iso {R : Type*} [Semiring R]
    {C : Type*} [Category C] [Preadditive C] [Linear R C] {X Y : C}
    (i : X ≅ Y) (r : R) : r • 𝟙 X = 0 ↔ r • 𝟙 Y = 0 := by
  have key {X Y : C} (i : X ≅ Y) (h : r • 𝟙 X = 0) : r • 𝟙 Y = 0 :=
    calc
      r • 𝟙 Y = i.inv ≫ (r • 𝟙 X) ≫ i.hom := by simp [Linear.smul_comp, Linear.comp_smul]
      _ = 0 := by simp [h]
  exact ⟨key i, key i.symm⟩

/-- Rig-étaleness may be checked on any completed polynomial presentation: the
annihilation condition in the derived category is independent of the presentation. -/
theorem isRigEtale_iff {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (P : CompletedPolynomialPresentation I B) :
    IsRigEtale B ↔
      ∃ c : ℕ, ∀ a : A, a ∈ I ^ c →
        (algebraMap A B.carrier a) •
          𝟙 ((DerivedCategory.Q (C := ModuleCat.{max u v} B.carrier)).obj
            (completedNaiveCotangentComplex B P).cochainComplex) = 0 := by
  refine ⟨fun h => h P, ?_⟩
  rintro ⟨c, hc⟩ Q
  obtain ⟨e⟩ := completedNaiveCotangentComplex_homotopyEquiv I B P Q
  let C := ModuleCat.{max u v} B.carrier
  let K := (completedNaiveCotangentComplex B P).cochainComplex
  let L := (completedNaiveCotangentComplex B Q).cochainComplex
  let i : (DerivedCategory.Q (C := C)).obj K ≅ (DerivedCategory.Q (C := C)).obj L :=
    ((DerivedCategory.quotientCompQhIso C).app K).symm ≪≫
      (DerivedCategory.Qh (C := C)).mapIso (HomotopyCategory.isoOfHomotopyEquiv e) ≪≫
      (DerivedCategory.quotientCompQhIso C).app L
  exact ⟨c, fun a ha => (scalar_id_eq_zero_iff_of_iso i (algebraMap A B.carrier a)).mp (hc a ha)⟩

/-- **Stacks 0GB1.** A rig-étale adically finite type algebra over `(A, I)` is rig-smooth. -/
@[stacks 0GB1]
theorem isRigSmooth_of_isRigEtale {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} (B : AdicFiniteTypeAlgebra.{u, v} A I)
    (hB : IsRigEtale B) : IsRigSmooth B :=
  let P := completedPolynomialPresentation I (Ideal.fg_of_isNoetherianRing I) B
  ⟨P, by
    obtain ⟨c, hc⟩ := hB P
    refine ⟨c, fun N x a ha => ?_⟩
    calc
      (algebraMap A B.carrier a) • x =
          (ShiftedHom.mk₀ (0 : ℤ) rfl
            ((algebraMap A B.carrier a) • 𝟙
              ((DerivedCategory.Q (C := ModuleCat.{max u v} B.carrier)).obj
                (completedNaiveCotangentComplex B P).cochainComplex))).comp x
              (show (1 : ℤ) + 0 = 1 by simp) := by simp
      _ = 0 := by rw [hc a ha]; simp⟩

end Rig

end
