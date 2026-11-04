module

public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.LocalGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
import all StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.Topology.Dimension.KrullSupplement

/-!
# Ideal sheaves of base changes of closed immersions of algebraic spaces

For a closed immersion `i : Y ⟶ X` of algebraic spaces, the ideal sheaf of the base change of `i`
along a composite `yoneda.map r ≫ p` is the inverse image along `r` of that along `p`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y : AlgebraicSpaces B S hS}

/-- The ideal sheaf of the canonical base change of a closed immersion `i : Y ⟶ X` of algebraic
spaces along `yoneda.map r ≫ p` is the inverse image, along `r`, of the ideal sheaf of its
canonical base change along `p`. -/
theorem schemeKer_snd_comp_of_isClosedImmersion (i : Y ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom)
    {A A' : BigFppfOver B S hS} (p : yoneda.obj A ⟶ X.1) (r : A' ⟶ A) :
    ((BigFppfOver.toScheme B S hS).map (hi.rep.snd (yoneda.map r ≫ p))).ker =
      (((BigFppfOver.toScheme B S hS).map (hi.rep.snd p)).ker).comap
        ((BigFppfOver.toScheme B S hS).map r) := by
  obtain ⟨l, hsq⟩ := exists_isPullback_snd_comp B S hS hi.rep p r _ rfl
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd p)) := hi.property_snd p
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd p))
      ((BigFppfOver.toScheme B S hS).map r),
    ← Scheme.Hom.ker_comp_of_isIso hsq.flip.isoPullback.hom,
    hsq.flip.isoPullback_hom_fst]

section Charts

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

end Charts

section Sections

variable (X' : AlgebraicSpaces B S hS) (W : ClosedSubspaces B S hS X'.1)

end Sections

end AlgebraicGeometry.Space

end

