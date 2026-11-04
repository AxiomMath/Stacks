module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatSheafSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections

/-!
# The ring map from the base ring to the functions on an étale chart

In Situation [Stacks, Tag 0CX4] let `A = lim Aₙ` and let `U` be an étale chart of `X`. The chart
maps to `X` and `X` maps to `Spec A`, so the ring `Γ(U, 𝒪_U)` of functions on the chart is an
`A`-algebra. This is the ring map along which the derived sections `RΓ(U, -)` over the chart are
read as complexes of `A`-modules in [Stacks, Tag 0CX8] and [Stacks, Tag 0CX9].

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.chartBaseRingHom`: the ring map
  `A ⟶ Γ(U, 𝒪_U)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-- The ring map `A = lim Aₙ ⟶ Γ(U, 𝒪_U)` of an étale chart `U` of `X`: the global sections of
the composite `U ⟶ X ⟶ Spec A`, preceded by the identification `A ≅ Γ(Spec A, 𝒪)`. -/
def chartBaseRingHom (U : SmallEtale D.B D.S D.containsLimitBase D.X.left.1) :
    (limit D.system : CommRingCat.{u}) →+*
      chartRing D.B D.S D.containsLimitBase D.X.left.1 D.X.left.2 U :=
  ((BigFppfOver.toScheme D.B D.S D.containsLimitBase).map
      (yoneda.preimage (U.1.hom ≫ D.X.hom.hom))).appTop.hom.comp
    (Scheme.ΓSpecIso (limit D.system)).inv.hom

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space

end
