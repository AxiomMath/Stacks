module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep
public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.StepFull
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Induction
import all StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.OneAffineOpenStep
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.InductionSupplement

/-!
# Additions to `OneAffineOpenStep`

Supplementary declarations for the module above, kept in their own module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.FiniteTypeApproximation

section Step

end Step

section Relative

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵈ ⥤ Scheme.{u}) [∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
  [∀ i, QuasiCompact (terminal.from (D.obj i))]

/-- **Stacks 07RN with a cofinal reindexing.** The approximation of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation.nonempty_of_isLimit` can be chosen so that
every index of the given system on `U` is dominated by the image of an index of the new system;
restricting the given system along the reindexing therefore keeps its limit. This is what the
proof of Stacks 07SU uses when it replaces the index set by the one found by Stacks 07RN. -/
theorem exists_isCofinal_of_isLimit (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) [CompactSpace (U : Scheme.{u})]
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    ∃ Q : FiniteTypeApproximation D S U p, IsCofinal Q :=
  exists_isCofinal_of_isOneAffineOpenStep D isOneAffineOpenStep S U p hp

end Relative

end AlgebraicGeometry.Scheme.FiniteTypeApproximation

end

