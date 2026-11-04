module

public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedMcQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissible
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.RingTheory.Nilpotent.Ideal
public import StacksFrontier.SetTheory.Cardinal.SizeBound
import all StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum

/-!
# Countably indexed affine formal algebraic spaces as formal spectra: the refined forms

For Stacks 0AN1: the strengthened and newly added declarations of the 2026-10 chapter-87 round
that belong with `StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrum`.
A declaration of that module whose statement the round strengthened keeps its original
statement there; its strengthened form lives here under a primed name.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [instance] SpfPresentation.commRing SpfPresentation.topology
  SpfPresentation.topologicalRing SpfPresentation.linearTopology

/-! ### Conditions (2), (3) and (4) -/

/-! ### Conditions (3) and (5): the inverse limit description -/

section Limit

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

variable {R : Type*} [CommRing R] {J : ℕ → Ideal R}

end Limit

/-! ### Conditions (2) and (1) -/

attribute [local instance] sheaf_hasColimits

/-- A weakly admissible ring with countably generated zero neighbourhoods carrying a quotient
system over `S` is smaller than the cutoff of the site.

A chain `Iₙ` of weak ideals of definition basing the topology embeds `A` into `∏ₙ A/Iₙ`, by
separatedness. Each `#(A/Iₙ)` is below the cutoff because the quotient spectrum lies in the
site, hence so is their supremum `μ`, the cutoff having uncountable cofinality; the cutoff being
a strong prelimit then keeps `μ ^ ℵ₀`, and therefore `#A`, below it. -/
theorem mk_lt_cutoff_of_isCountablyGenerated {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (D : QuotientSystem B S hS A) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hc : (nhds (0 : A)).IsCountablyGenerated) : Cardinal.mk A < B.cutoff := by
  obtain ⟨I, hanti, hweak, hbasis⟩ := exists_antitone_weakIdeal_basis hA hc
  -- each quotient by a member of the chain is small, hence so is their supremum
  have hquot (n : ℕ) : Cardinal.mk (A ⧸ I n) < B.cutoff := by
    have hsite : (Spec (.of (A ⧸ I n))).size < B.cutoff := D.inSite ⟨I n, hweak n⟩
    rw [Scheme.size_Spec] at hsite
    exact lt_of_le_of_lt (le_max_right _ _) hsite
  have hsup : (⨆ n : ULift.{u} ℕ, Cardinal.mk (A ⧸ I n.down)) < B.cutoff :=
    Cardinal.iSup_lt_of_lt_cof_ord (α := ULift.{u} ℕ)
      ((Cardinal.mk_le_aleph0 :
        Cardinal.mk (ULift.{u} ℕ) ≤ Cardinal.aleph0).trans_lt B.aleph0_lt_cutoff_cof)
      fun n ↦ hquot n.down
  -- separatedness embeds `A` into the product of the quotients
  have hinj : Function.Injective (fun a : A ↦ fun n : ℕ ↦ Ideal.Quotient.mk (I n) a) := by
    intro a b hab
    exact eq_of_forall_sub_mem hA.2.2 hbasis fun n ↦
      Ideal.Quotient.eq.mp (congrFun hab n)
  refine lt_of_le_of_lt ?_ (Cardinal.power_aleph0_lt_of_isStrongPrelimit
    B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hsup)
  calc Cardinal.mk A ≤ Cardinal.mk ((n : ℕ) → A ⧸ I n) := Cardinal.mk_le_of_injective hinj
    _ ≤ (⨆ n : ULift.{u} ℕ, Cardinal.mk (A ⧸ I n.down)) ^ Cardinal.aleph0 := by
        rw [Cardinal.mk_pi]
        calc Cardinal.prod (fun n : ℕ ↦ Cardinal.mk (A ⧸ I n))
            ≤ Cardinal.prod (fun _ : ℕ ↦
                ⨆ n : ULift.{u} ℕ, Cardinal.mk (A ⧸ I n.down)) :=
              Cardinal.prod_le_prod _ _ fun n ↦ le_ciSup
                (f := fun k : ULift.{u} ℕ ↦ Cardinal.mk (A ⧸ I k.down))
                Cardinal.bddAbove_of_small (ULift.up n)
          _ = (⨆ n : ULift.{u} ℕ, Cardinal.mk (A ⧸ I n.down)) ^ Cardinal.aleph0 := by
              simp

end AlgebraicGeometry.FormalSpace

end
