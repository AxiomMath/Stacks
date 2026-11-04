module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DirectedQuotientsPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrumRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.McQuillan
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionLimitPresentation

/-!
# Recognising a sequential presentation as a formal spectrum

A sequential presentation of a sheaf `X` by quotients of a topological ring `A` is a
presentation indexed by the directed preorder `ℕ`. Consequently `X` is the formal spectrum of
`A`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.SequentialQuotients.toDirected`: the directed presentation
  indexed by `ℕ` underlying a sequential presentation.

## Main results

* `AlgebraicGeometry.FormalSpace.SequentialQuotients.proj_comp_le'`: the surjections onto the
  stages are compatible with every transition morphism.
* `AlgebraicGeometry.FormalSpace.SequentialQuotients.exists_quotientSystem_formalSpectrum_iso'`:
  a sheaf with a sequential presentation is isomorphic to a formal spectrum.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Filter

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

namespace SequentialQuotients

variable {B S hS} {X : FppfSheaf B S hS} {A : Type u} [CommRing A] [TopologicalSpace A]

/-- The surjections onto the stages are compatible with every transition morphism, not only
with the successor ones. -/
theorem proj_comp_le' (P : SequentialQuotients B S hS X A) {m n : ℕ} (h : m ≤ n) :
    (((BigAffineFppf.toScheme B S hS).map
      (P.diagram.map (homOfLE h))).appTop).hom.comp (P.proj n) = P.proj m := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [show homOfLE (le_refl m) = 𝟙 m from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    ext a
    simp
  | succ n h ih =>
    have hcomp : P.diagram.map (homOfLE (h.trans (Nat.le_succ n))) =
        P.diagram.map (homOfLE h) ≫ P.diagram.map (homOfLE (Nat.le_succ n)) := by
      rw [← Functor.map_comp]
      congr 1
    rw [hcomp, Functor.map_comp, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
      RingHom.comp_assoc, P.proj_comp n]
    exact ih

/-- The presentation indexed by the nonempty directed preorder `ℕ` underlying a sequential
presentation. -/
def toDirected (P : SequentialQuotients B S hS X A) : DirectedQuotients B S hS X A ℕ where
  diagram := P.diagram
  isThickening := P.isThickening
  colimitIso := P.colimitIso
  proj := P.proj
  proj_surjective := P.proj_surjective
  proj_comp := fun {_ _} h ↦ P.proj_comp_le h
  isWeakIdealOfDefinition_ker := P.isWeakIdealOfDefinition_ker
  hasBasis_nhds_zero := P.hasBasis_nhds_zero

/-- A sheaf presented as the colimit of a sequence of affine thickenings whose section rings are
the quotients of a linearly topologized ring `A` by a fundamental system of weak ideals of
definition is the formal spectrum of `A`. -/
@[stacks 0AIC "(4) implies (1), for a sequential presentation"]
theorem exists_quotientSystem_formalSpectrum_iso' (P : SequentialQuotients B S hS X A) :
    ∃ Q : QuotientSystem B S hS A, Nonempty (X ≅ formalSpectrum Q) :=
  P.toDirected.exists_quotientSystem_formalSpectrum_iso

end SequentialQuotients

end AlgebraicGeometry.FormalSpace

end
