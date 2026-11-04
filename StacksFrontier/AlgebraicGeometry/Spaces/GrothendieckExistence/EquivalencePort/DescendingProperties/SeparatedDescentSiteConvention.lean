module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Connected
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomFpqcLocal
public import StacksFrontier.AlgebraicGeometry.EventualLimitProperties.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.Separated
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineChartSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparated
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeComposite
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescentBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Limits.DescendingMorphismPropertiesSiteConvention
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.CofilteredLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFormallySmooth

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# SeparatedDescent under the site convention

The declarations below accompany
`StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent`: they state its
results under the chapter's standing convention of Section 70.2 (tag 07SD) on the size of the
site, in the form the absolute Noetherian approximation of Stacks 07SU consumes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe u

namespace AlgebraicGeometry.Space

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Separatedness over an affine base is absolute separatedness -/

section AbsoluteOverAffine

variable (hZ : B.Contains (⊤_ Scheme.{u})) {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

end AbsoluteOverAffine

/-! ### Products of affine objects over an affine base -/

/-! ### Charts of two stages of an inverse system -/

section ChartSystem

variable {I : Type u} [Category.{u} I] (i₀ : I)
  (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (U₀ : BigAffineFppf B S hS)
  (f₀ : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj U₀) ⟶ D.obj i₀)

end ChartSystem

/-! ### The kernel pair of a finer chart as a base change -/

/-! ### Descending a closed immersion into a product of charts -/

section ProductDiagrams

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (hSaff : IsAffine S)
  (V : K ⥤ BigFppfOver B S hS)
  (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hK : #K < B.cutoff.ord.cof)

end ProductDiagrams

section ProductDiagramsSiteSmall

variable {K : Type u} [Category.{u} K] [IsCofiltered K] (hSaff : IsAffine S)
  (V : K ⥤ BigFppfOver B S hS)
  (hVaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj j)))
  (hK : BigFppfOver.IsSiteSmallDiagram V)

/-- A site-small cofiltered diagram of charts whose image under a monomorphism-preserving
endofunctor is affine has a limit preserved by the underlying scheme functor. -/
private theorem preservesLimit_toScheme_comp_of_isSiteSmallDiagram
    (Φ : BigFppfOver B S hS ⥤ BigFppfOver B S hS) [Φ.PreservesMonomorphisms]
    (hK : BigFppfOver.IsSiteSmallDiagram V)
    (hpaff : ∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj ((V ⋙ Φ).obj j))) :
    PreservesLimit (V ⋙ Φ) (BigFppfOver.toScheme B S hS) :=
  BigFppfOver.preservesLimit_toScheme_of_isSiteSmallDiagram (V ⋙ Φ) hpaff (hK.comp Φ)

include hSaff hVaff hK in
/-- For a cofiltered diagram of affine charts small for the site, the underlying scheme functor
preserves the limit of the products of the charts with a fixed affine object on the right, the
input of `AlgebraicGeometry.Space.exists_isClosedImmersion_comp_prodMap_π_of_preservesLimit`. -/
theorem C1573.preservesLimit_toScheme_prod_left_of_isSiteSmallDiagram {Z : BigFppfOver B S hS}
    (hZaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)) :
    PreservesLimit (V ⋙ prod.functor.obj Z) (BigFppfOver.toScheme B S hS) := by
  have _ : (prod.functor.obj Z).PreservesMonomorphisms :=
    ⟨fun f _ => prod.map_mono (𝟙 Z) f⟩
  exact preservesLimit_toScheme_comp_of_isSiteSmallDiagram B S hS V _ hK fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ hZaff (hVaff j)

include hSaff hVaff hK in
/-- For a cofiltered diagram of affine charts small for the site, the underlying scheme functor
preserves the limit of the products of the charts with a fixed affine object on the left, the
input of `AlgebraicGeometry.Space.exists_isClosedImmersion_pullback_snd_prodMap_of_preservesLimit`.
-/
theorem C1573.preservesLimit_toScheme_prod_right_of_isSiteSmallDiagram {Z : BigFppfOver B S hS}
    (hZaff : IsAffine ((BigFppfOver.toScheme B S hS).obj Z)) :
    PreservesLimit (V ⋙ prod.functor.flip.obj Z) (BigFppfOver.toScheme B S hS) := by
  have _ : (prod.functor.flip.obj Z).PreservesMonomorphisms :=
    ⟨fun f _ => prod.map_mono f (𝟙 Z)⟩
  exact preservesLimit_toScheme_comp_of_isSiteSmallDiagram B S hS V _ hK fun j =>
    isAffine_toScheme_obj_prod_of_isAffine_base B S hS hSaff _ _ (hVaff j) hZaff

end ProductDiagramsSiteSmall

/-! ### Relocalization to a larger base scheme -/

section Relocalize

variable {S' : Scheme.{u}} (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

end Relocalize

/-! ### The view over the terminal scheme is already absolute -/

section OverIntegers

variable (hZ : B.Contains (⊤_ Scheme.{u}))

end OverIntegers

/-! ### Separatedness descends to a stage -/

section Descent

variable (hZ : B.Contains (⊤_ Scheme.{u}))

namespace DescentSituation

end DescentSituation

end Descent

/-! ### Separatedness over a base algebraic space at a late stage -/

section SeparatedOverBase

variable (hZ : B.Contains (⊤_ Scheme.{u})) {T Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable {I : Type u} [Preorder I]

section BaseChangeOver

variable [IsDirected I (· ≤ ·)] (D : DescentSituation B S hS hZ I)
  (hY : IsAlgebraicSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
  (t : D.system ⟶ (Functor.const Iᵒᵖ).obj Y) (g : D.limitCone.pt ⟶ Y)
  (hg : ∀ j, D.limitCone.π.app j ≫ t.app j = g) (U : BigFppfOver B S hS)
  (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)) (u : yoneda.obj U ⟶ Y)

end BaseChangeOver

end SeparatedOverBase

end AlgebraicGeometry.Space

end
