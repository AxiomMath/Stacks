module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonalBootstrap
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionTheorem
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSizeBound
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionTangentSpace
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionFormalObjectCompatibility
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionArtinTheorem
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionOpenVersality

/-!
# The separatedness hypotheses of Artin's theorem on contractions (Stacks 0GIC)

Without separatedness hypotheses on `X'` or `W`, the axioms `[1]`, `[4]`, `[5]` give a limit
preserving solution of the contraction problem whose open part is the complement of `T`.

## Main results

* `exists_solution_of_solutions`: Artin's theorem on contractions, with the diagonal of the
  contraction functor obtained from solutions of the separated case.
* `separatednessRemark_of`: from completion algebraization for separated `X'`, the diagonal of
  the contraction functor is relatively representable and solutions exist.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- **Artin's theorem with the diagonal from the bootstrap.** With the diagonal of `F` obtained
from `relativelyRepresentable_diag_contractionFunctor_of_solutions`, which uses no separatedness
of `X'` or `W`, the axioms `[1]`, `[4]`, `[5]` give a limit preserving solution whose open part is
the complement of `T`. -/
theorem exists_solution_of_solutions
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (hsol : ∀ {V : Scheme.{u}} {hV : B.Contains V} (c' : ContractionSituation B V hV),
      (∀ v : V, IsFiniteTypePoint v → IsGRing (V.presheaf.stalk v)) →
      Space.IsSeparated B V hV (terminal.from c'.X') →
      FormalSpace.IsSeparatedMorphism B V hV (terminal.from c'.W) →
      ∃ (E : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u) (s : Solution c' E),
        Set.range (Space.pointsMap B V hV s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B V hV) E)
    (hlim : LimitPreserving.{u, u + 1, u, u, u + 1, u}
      (LocallyNoetherianOver.toScheme B S hS) (contractionFunctor c))
    (heff : LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c))
    (hopen : LocallyNoetherianOver.HasOpenVersality B S hS (contractionFunctor c)) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : Solution c X),
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X :=
  exists_solution_of_satisfiesArtinAxioms c hG
    (c.relativelyRepresentable_diag_contractionFunctor_of_solutions hG hsol hlim)
    { sizeBounded := by
        obtain ⟨T₀, hT₀⟩ := contractionFunctor_sizeBounded c
        exact ⟨T₀, fun U K _ hU hlft => (Cardinal.lift_id'.{u, u + 1} _).trans_le
          (hT₀ U K hU hlft)⟩
      isSheaf := contractionFunctor_satisfiesEtaleSheafProperty B S hS c
      limitPreserving := hlim
      satisfiesRS := contractionFunctor_satisfiesRS c
      finiteDimensionalTangentSpaces := hasFiniteDimensionalTangentSpaces c
      effective := heff
      openVersality := hopen }

/-- If every contraction situation with separated `X'` has completion algebraization, then the
diagonal of the contraction functor of `c` is relatively representable, a solution with open part
the complement of `T` exists when `c` has completion algebraization, and one exists when `X'` is
separated. -/
theorem separatednessRemark_of
    (halgSep : ∀ {V : Scheme.{u}} {hV : B.Contains V} (c' : ContractionSituation B V hV),
      Space.IsSeparated B V hV (terminal.from c'.X') → c'.HasCompletionAlgebraization)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    (uliftYoneda.{u + 1} (C := LocallyNoetherianOver B S hS)).relativelyRepresentable
        (diag (contractionFunctor c)) ∧
      (c.HasCompletionAlgebraization → ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (s : Solution c X), Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ) ∧
      (Space.IsSeparated B S hS (terminal.from c.X') → ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
        (s : Solution c X), Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ) := by
  have hsol : ∀ {V : Scheme.{u}} {hV : B.Contains V} (c' : ContractionSituation B V hV),
      (∀ v : V, IsFiniteTypePoint v → IsGRing (V.presheaf.stalk v)) →
      Space.IsSeparated B V hV (terminal.from c'.X') →
      FormalSpace.IsSeparatedMorphism B V hV (terminal.from c'.W) →
      ∃ (E : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u) (s : Solution c' E),
        Set.range (Space.pointsMap B V hV s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B V hV) E :=
    fun c' hG' hX hW => exists_solution_of_hasEffectiveFormalObjects c' hG' hX hW
      (c'.hasEffectiveFormalObjects_of_hasCompletionAlgebraization (halgSep c' hX))
  have h2 : c.HasCompletionAlgebraization → ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
      (s : Solution c X), Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ := by
    intro halg
    obtain ⟨X, s, hU, -⟩ := c.exists_solution_of_solutions hG hsol
      (limitPreserving_contractionFunctor c)
      (c.hasEffectiveFormalObjects_of_hasCompletionAlgebraization halg)
      (contractionFunctor_hasOpenVersality c)
    exact ⟨X, s, hU⟩
  exact ⟨c.relativelyRepresentable_diag_contractionFunctor_of_solutions hG hsol
    (limitPreserving_contractionFunctor c), h2, fun hX => h2 (halgSep c hX)⟩

end AlgebraicGeometry.Artin.ContractionSituation

end
