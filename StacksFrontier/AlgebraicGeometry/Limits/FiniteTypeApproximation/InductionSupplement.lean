module

public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Induction
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.Comp
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.Reduction
import all StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.Induction

/-!
# Additions to `Induction`

Supplementary declarations for the module above, kept in their own module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Scheme.Opens

variable {S : Scheme.{u}} (T : S.Opens)

variable {U : S.Opens} (hU : U ≤ T)

end Scheme.Opens

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.FiniteTypeApproximation

attribute [local instance] indexPreorder indexNonempty indexDirected

section Cofinal

variable {I : Type u} [Preorder I] {D : Iᵒᵈ ⥤ Scheme.{u}} {S : Scheme.{u}} {U : S.Opens}
  {p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D}

end Cofinal

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵈ ⥤ Scheme.{u})
  [∀ {i j : Iᵒᵈ} (f : i ⟶ j), IsAffineHom (D.map f)]
  [∀ i, LocallyOfFiniteType (terminal.from (D.obj i))]
  [∀ i, QuasiCompact (terminal.from (D.obj i))]

/-- **Cofinal Noetherian approximation relative to a quasi-compact open, from the single-affine
case.** The approximation of `exists_of_isOneAffineOpenStep` can be taken cofinal: every index
of the given system is dominated by the image of an index of the approximating system, so
restricting the given system along the reindexing does not change its limit. -/
theorem exists_isCofinal_of_isOneAffineOpenStep (hstep : IsOneAffineOpenStep.{u})
    (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (U : S.Opens) [CompactSpace (U : Scheme.{u})]
    (p : (Functor.const Iᵒᵈ).obj (U : Scheme.{u}) ⟶ D)
    (hp : IsLimit (Cone.mk (U : Scheme.{u}) p)) :
    ∃ Q : FiniteTypeApproximation D S U p, IsCofinal Q := by
  obtain ⟨n, A, hA⟩ := Scheme.exists_finite_affineOpens_sup_eq_top S U
  exact exists_aux hstep S ‹_› ‹_› n D (fun f ↦ inferInstance)
    (fun i ↦ inferInstance) (fun i ↦ inferInstance) U ‹_›
    (fun l ↦ ((A l : S.affineOpens) : S.Opens)) (fun l ↦ (A l).2) hA p hp

end AlgebraicGeometry.Scheme.FiniteTypeApproximation

end

