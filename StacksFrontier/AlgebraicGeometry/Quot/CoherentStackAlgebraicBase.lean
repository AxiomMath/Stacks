module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperHenselianLimit
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackArtinCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineFinitePresentationFactorization

/-!
# Artin's criterion for `Coh_{X/V}` over `Spec ℤ`, `V` a scheme locally of finite presentation

The base case of the proof of Stacks 09DS. Over the base `Spec ℤ` (the terminal scheme), which
is locally Noetherian with G-rings as local rings (Stacks 07PX), let `f : X ⟶ V` be a morphism of
finite presentation of algebraic spaces whose target is the algebraic space of a scheme `V` of
the site, locally of finite presentation over `ℤ`. Then Stacks 07Y4 applies to `Coh_{X/V}`, the
inputs being those of
`AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG_of_artinInputs`.

## Main results

* `AlgebraicGeometry.isGRing_stalk_terminal`: its local rings are G-rings.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_terminal_from_yoneda`: a scheme of the
  site locally of finite presentation over the base is, as an algebraic space.
* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_coherentCFG_overIntegers`.

## References

* [Stacks Project, Tag 09DS](https://stacks.math.columbia.edu/tag/09DS)
* [Stacks Project, Tag 07Y4](https://stacks.math.columbia.edu/tag/07Y4)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe z u

namespace AlgebraicGeometry

/-- **The local rings of `Spec ℤ` are G-rings** (Stacks 07PX). -/
theorem isGRing_stalk_terminal (s : ⊤_ Scheme.{u}) :
    IsGRing ((⊤_ Scheme.{u}).presheaf.stalk s) := by
  have : LocallyOfFiniteType (terminal.from (⊤_ Scheme.{u})) := by
    rw [Subsingleton.elim (terminal.from (⊤_ Scheme.{u})) (𝟙 _)]
    infer_instance
  exact isGRing_stalk_of_locallyOfFiniteType_terminal s

namespace Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

end Space

end AlgebraicGeometry

namespace AlgebraicGeometry.Space.CoherentSituation

variable {B : BigFppfSite.{u}} {hZ : B.Contains (⊤_ Scheme.{u})}
  (D : CoherentSituation B (⊤_ Scheme.{u}) hZ)

/-- **Stacks 07Y4 for `Coh_{X/V}` over `Spec ℤ`, `V` a scheme of the site locally of finite
presentation over `ℤ`.** Granted the representability of the diagonal (Stacks 08W6), axiom [-1],
the finiteness of tangent spaces (Stacks 08W8), the effectivity of formal objects (Stacks 08W9)
and of square-zero systems (Flatness on Spaces, Theorem 0CXB), `Coh_{X/V}` is an algebraic
stack. -/
theorem isAlgebraicStack_coherentCFG_overIntegers (V : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hV : LocallyOfFinitePresentation (B.inclusion.map V.hom))
    (eY : D.Y.1 ≅ yoneda.obj V)
    (hdiag : Stack.HasRepresentableDiagonal B _ hZ D.coherentCFG)
    (hsize : Stack.IsSizeBounded B _ hZ D.coherentCFG)
    (htangent : Stack.HasFiniteDimensionalTangentSpaces B _ hZ D.coherentCFG)
    (heffective : ∀ ξ : Deformation.Artin.FormalObject B _ hZ D.coherentCFG.val.p,
      Deformation.Artin.FormalObject.IsEffective B _ hZ D.coherentCFG.val.p
        D.coherentCFG.property ξ)
    (hsq : Deformation.Artin.IsSquareZeroEffective B _ hZ D.coherentCFG.val.p
      D.coherentCFG.isFiberedInGroupoids) :
    Stack.IsAlgebraicStack.{u, z, u + 1, u + 1} B _ hZ D.coherentCFG.val := by
  have hY : IsLocallyOfFinitePresentation B _ hZ (terminal.from D.Y.1) := by
    have h : terminal.from D.Y.1 = eY.hom ≫ terminal.from (yoneda.obj V) := terminal.hom_ext _ _
    rw [h]
    exact (Space.holdsOnEveryEtaleChart_iso_comp_iff B _ hZ _ eY.hom _).2
      (isLocallyOfFinitePresentation_terminal_from_yoneda B _ _ V hV)
  exact D.isAlgebraicStack_coherentCFG_of_artinInputs hY hdiag hsize htangent heffective hsq
    (fun s _ => isGRing_stalk_terminal s)

end AlgebraicGeometry.Space.CoherentSituation

end
