module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuotientByIdeal
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.InverseImageComparison

/-!
# Inverse image of pro-étale sheaves of modules commutes with restriction to `Λ`

Let `Λ` be a commutative ring and `I ⊆ Λ` an ideal. A sheaf of `Λ ⧸ I`-modules on the small
pro-étale site is a sheaf of `Λ`-modules by restriction of coefficients
(`Stacks.ModuleSheaf.restrictQuotientScalars`), and inverse image along a morphism of schemes
commutes with this: restriction of coefficients is a left adjoint, so it preserves the colimits
computing the left Kan extension, and it preserves sheafification.

## Main definitions

* `AlgebraicGeometry.ProEtale.restrictQuotientScalarsProetaleModuleInverseImageIso`: the
  comparison isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ModuleSheaf

universe w v u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] proetalePostcompose_isContinuous

variable (Λ : Type v) [CommRing Λ] (I : Ideal Λ)

/-- **Inverse image commutes with restriction of coefficients along `Λ → Λ ⧸ I`.** -/
def restrictQuotientScalarsProetaleModuleInverseImageIso {Z X : Scheme.{u}} (g : Z ⟶ X)
    (G : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) v w} (Λ ⧸ I))) :
    (Stacks.ModuleSheaf.restrictQuotientScalars.{u + 1, u, max (u + 1) v w}
        (Scheme.ProEt.topology Z) Λ I).obj
        ((proetaleModuleInverseImage.{u, v, w} g (Λ ⧸ I)).obj G) ≅
      (proetaleModuleInverseImage.{u, v, w} g Λ).obj
        ((Stacks.ModuleSheaf.restrictQuotientScalars.{u + 1, u, max (u + 1) v w}
          (Scheme.ProEt.topology X) Λ I).obj G) := by
  let bc := Scheme.proetaleBaseChange g
  let adj := ModuleCat.restrictCoextendScalarsAdj.{max (u + 1) w} (Ideal.Quotient.mk I)
  let R := ModuleCat.restrictScalars.{max (u + 1) v w} (Ideal.Quotient.mk I)
  have : (Scheme.ProEt.topology Z).PreservesSheafification R :=
    Sheaf.preservesSheafification_of_adjunction _ adj
  have hc : PreservesColimitsOfSize.{u, u + 1} R := adj.leftAdjoint_preservesColimits
  have hcolim (W : Z.ProEtᵒᵖ) : PreservesColimitsOfShape (CostructuredArrow bc.op W) R :=
    @PreservesColimitsOfSize.preservesColimitsOfShape _ _ _ _ _ hc _ _
  exact (sheafCompose _ R).mapIso
      ((proetaleModuleInverseImageIsoSheafPullback.{u, v, w} (Λ ⧸ I) g).app G) ≪≫
    (bc.sheafPullbackSheafComposeIso (ModuleCat.{max (u + 1) v w} (Λ ⧸ I))
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology Z) R G).symm ≪≫
    ((bc.sheafAdjunctionContinuous (ModuleCat.{max (u + 1) v w} Λ) (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z)).leftAdjointUniq
        (proetaleModuleInverseImageAdjunction.{u, v, w} Λ g)).app _

end AlgebraicGeometry.ProEtale

end
