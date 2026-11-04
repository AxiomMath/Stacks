module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionDiagonal
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleSheafPropertyUnconditional
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionOpenVersality
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionRimSchlessinger
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSizeBound
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionTangentSpace
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionTheorem

/-!
# Assembling Artin's axioms for the contraction functor

In Situation 0GH8 with `X'` and `W` separated over `S`, this file feeds the axioms proved for
Artin's contraction functor `F` (the diagonal by Stacks 0GHF, `[-1]` by the size bound, `[0]` by
Stacks 0GHG, `[1]` by Stacks 0GI5, `[2]` by Stacks 0GI6, `[3]` by Stacks 0GI7, `[5]` by
Stacks 0GIA) into Stacks 0GE7 and Stacks 0GHC. The axiom `[4]` (effectivity of formal objects) is
taken here as the explicit hypothesis `heff` of
`AlgebraicGeometry.Artin.ContractionSituation.exists_solution_of_hasEffectiveFormalObjects`; this
is an intermediate step, not the theorem of Stacks 0GIB.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Contraction from axiom `[4]`.** In Situation 0GH8, suppose the local rings of `S` at finite
type points are G-rings and `X'`, `W` are separated over `S`. If the formal objects of Artin's
contraction functor `F` are effective (`heff`), then there is a solution `(f : X' ⟶ X, T, a)` with
`|U| = |X| ∖ T` whose target `X` is limit preserving. -/
theorem exists_solution_of_hasEffectiveFormalObjects (c : ContractionSituation B S hS)
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s))
    (hX' : Space.IsSeparated B S hS (terminal.from c.X'))
    (hW : FormalSpace.IsSeparatedMorphism B S hS (terminal.from c.W))
    (heff : LocallyNoetherianOver.HasEffectiveFormalObjects B S hS (contractionFunctor c)) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (s : Solution c X),
      Set.range (Space.pointsMap B S hS s.U.toFunctor s.U.ι) = s.Tᶜ ∧
        LimitPreserving.{u, u, u, u, u + 1, u} (BigFppfOver.toScheme B S hS) X :=
  exists_solution_of_satisfiesArtinAxioms c hG
    (relative_isClosedImmersion_diag_contractionFunctor c hX' hW).rep
    { sizeBounded := by
        obtain ⟨T₀, hT₀⟩ := contractionFunctor_sizeBounded c
        exact ⟨T₀, fun U K _ hU hlft => (Cardinal.lift_id'.{u, u + 1} _).trans_le
          (hT₀ U K hU hlft)⟩
      isSheaf := contractionFunctor_satisfiesEtaleSheafProperty B S hS c
      limitPreserving := limitPreserving_contractionFunctor c
      satisfiesRS := contractionFunctor_satisfiesRS c
      finiteDimensionalTangentSpaces := hasFiniteDimensionalTangentSpaces c
      effective := heff
      openVersality := contractionFunctor_hasOpenVersality c }

end AlgebraicGeometry.Artin.ContractionSituation

end
