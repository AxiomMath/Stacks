module

public import StacksFrontier.AlgebraicGeometry.Spaces.ReesSpectrumSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSpacePresentedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatGlobalSectionsRingHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# The global functions of the space of a Rees spectrum

For an affine object `T` of the site and a finitely generated ideal `J` of `A = Γ(T₀, ⊤)`, the
ring of global functions of the algebraic space `h_{Spec A[Jt]}` is the Rees algebra `A[Jt]`.

## Main definitions

* `AlgebraicGeometry.Space.globalSectionsReesSpectrumEquiv`: `Γ(h_{Spec A[Jt]}, 𝒪) ≃+* A[Jt]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) (hJ : J.FG)

/-- `Γ(h_{Spec A[Jt]}, 𝒪) ≃+* A[Jt]`: evaluation at the terminal identity chart followed by
`Γ(Spec R, ⊤) ≅ R`. -/
def globalSectionsReesSpectrumEquiv :
    RingCat.sectionsSubring
        (structureRingSheaf B S hS (schemeSpace (reesSpectrumOver B S hS T J hJ))).obj
      ≃+* reesAlgebra J :=
  (globalSectionsChartRingEquiv B S hS (schemeSpace (reesSpectrumOver B S hS T J hJ))
    (isTerminalIdEtaleChart B S hS (reesSpectrumOver B S hS T J hJ))).trans
    (Scheme.ΓSpecIso (.of (reesAlgebra J))).commRingCatIsoToRingEquiv

end AlgebraicGeometry.Space

end
