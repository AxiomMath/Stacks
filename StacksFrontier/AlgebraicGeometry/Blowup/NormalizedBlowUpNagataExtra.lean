module

public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUpNagata

/-!
# The normalized blowup of a point is the blowup when the blowup is normal

## Main definitions

* `Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp`: when the blowup at `x` is normal, the
  normalized blowup is the blowup, compatibly with the maps to `X`
  (`Stacks.Blowup.normalizedBlowUpSchemeIsoBlowUp_hom_blowUpToBase`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Blowup

/-- **The normalized blowup is the blowup when the blowup is normal**: if the blowup of `X` at a
closed point `x` is normal, its normalization is an isomorphism, and this is that isomorphism from
the normalized blowup to the blowup. -/
def normalizedBlowUpSchemeIsoBlowUp {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X))
    [IsNormal (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))] :
    normalizedBlowUpScheme X hX x hx ≅
      AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) :=
  haveI := Scheme.isIso_normalization_of_isNormal
    (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))
    (finite_irreducibleComponents_blowUp _ hX)
  asIso (Scheme.normalization
    (AlgebraicGeometry.blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))
    (finite_irreducibleComponents_blowUp _ hX))

/-- Under `normalizedBlowUpSchemeIsoBlowUp`, the normalized blowup morphism is the blowup
morphism. -/
@[reassoc (attr := simp)]
theorem normalizedBlowUpSchemeIsoBlowUp_hom_blowUpToBase {X : Scheme.{u}}
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X))
    [IsNormal (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)))] :
    (normalizedBlowUpSchemeIsoBlowUp hX x hx).hom ≫
        AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)) =
      normalizedBlowUp X hX x hx :=
  rfl


end Stacks.Blowup

end
