module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingProductSupplement
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRepresentableSupplement
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
import all StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType

/-!
# Supplement to `DiagonalLocallyOfFiniteType`

The results of this module extend those of
`StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType`.
They use imports, universe variables or `open` declarations that the base module does not
have, and are kept in a module of their own so that its header is unchanged.

## Main results

* `isLocallyOfFiniteType_diagonal_univ`
-/

/-! ### The generalizations made by this development

The declarations below restate, under weaker hypotheses or at more general universes, declarations
of this file whose statements are kept as they are above. Each carries the name of the declaration
it generalizes with the suffix `_univ` (or `Univ` for a definition). -/

universe u₁ v₁ u₂ v₂ u₃ v₃ vI wI u v w

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w} (BigFppfOver B S hS))

/-- **Stacks 0CXI.** Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme
`S` whose diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces. If `𝒳` is limit
preserving then `Δ` is locally of finite type.

The base change of `Δ` along a scheme-valued point of `𝒳 × 𝒳` over `U` is the presheaf of
vertical morphisms between the two components of that point, so a section of the representing
algebraic space over an affine inverse limit is a vertical morphism there, and limit preservation
of `𝒳` makes it the restriction of one at a finite stage. The surjectivity criterion of Stacks
0CM6 turns that into local finite presentation of the representing space over `U`, and Stacks
0464 into local finite type. -/
theorem isLocallyOfFiniteType_diagonal_univ
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS (diagonal.{u, v, w} B S hS 𝒳).hom)
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, u, u, max (u + 1) v w, max u v} B S hS 𝒳) :
    HasRelativeProperty.{u, max u v, max (u + 1) v w, u} B S hS
      (Space.locallyOfFiniteTypeProperty B S hS)
      (diagonal.{u, v, w} B S hS 𝒳) hΔ := by
  classical
  refine (hasRelativeProperty_iff_based.{u, max u v, max (u + 1) v w, u} B S hS
    (Space.locallyOfFiniteTypeProperty B S hS)
    (diagonal.{u, v, w} B S hS 𝒳) hΔ).mpr ?_
  refine hasRelativeProperty_of_affine_locallyOfFinitePresentation_univ.{u, max u v,
      max (u + 1) v w, max u v, max (u + 1) v w, u, u} B S hS
    (Space.locallyOfFiniteTypeProperty B S hS) (diagonal.{u, v, w} B S hS 𝒳).hom hΔ
    (isLimitPreservingOverTerminal_product.{u, u, u} B S hS 𝒳 h𝒳) ?_
  intro U _hUaff _hUlfp y hy F hF ⟨eF⟩
  -- the property of the representing space does not depend on the base
  have hri : (Space.locallyOfFiniteTypeProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := Space.locallyOfFiniteTypeProperty B S hS)
  rw [prop_algebraicSpaceMap_iff B S hS (Space.locallyOfFiniteTypeProperty B S hS) U F hF]
  refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
    (@AlgebraicGeometry.LocallyOfFiniteType.{u}) F).mpr ?_
  refine Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B U.left.1 U.left.2 ?_
  refine Space.isLocallyOfFinitePresentation_of_affineLimit_surjective B U.left.1 U.left.2 hF
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _)
    (Space.toYonedaId B U.left.1 U.left.2 F) ?_
  intro I _ _ D c hc hDaff hcaff x yy _hxy
  have : Nonempty I := IsCofiltered.nonempty
  -- the representing space is the presheaf of vertical morphisms
  have hp := 𝒳.isFiberedInGroupoids
  have hfib : 𝒳.val.p.IsFibered := hp.isFibered
  obtain ⟨e⟩ :=
    (TwoFibreProductOver.DiagonalFibre.nonempty_equivalenceOver_fst_iff hp hy F).mp ⟨eF⟩
  let pe := PresheafOfCategories.PointwiseEquiv.ofUliftIso e
  -- the system of affine schemes over `U` as a system over `S`
  have haff : ∀ i, IsAffineOver B S hS ((D ⋙ Over.map U.hom).obj i) := fun i => hDaff i
  have hcaff' : IsAffineOver B S hS ((Over.map U.hom).obj c.pt) := hcaff
  set D' : I ⥤ BigAffineFppf B S hS :=
    (IsAffineOver B S hS).lift (D ⋙ Over.map U.hom) haff with hD'def
  set c' : Cone D' :=
    { pt := ⟨(Over.map U.hom).obj c.pt, hcaff'⟩
      π :=
        { app := fun i => ObjectProperty.homMk ((Over.map U.hom).map (c.π.app i))
          naturality := fun i j f => by
            apply ObjectProperty.hom_ext
            show 𝟙 _ ≫ (Over.map U.hom).map (c.π.app j) =
              (Over.map U.hom).map (c.π.app i) ≫ (Over.map U.hom).map (D.map f)
            rw [Category.id_comp, ← Functor.map_comp, c.w f] } } with hc'def
  have hc' : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c') := hc
  -- limit preservation of `𝒳` gives descent of vertical morphisms
  have : (Deformation.Artin.colimitComparison 𝒳.val.p
      (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c')).Full := (h𝒳 I D' c' hc').full
  have hdesc : Deformation.Artin.DescentHom 𝒳.val.p (D ⋙ Over.map U.hom)
      ((Over.map U.hom).mapCone c) :=
    Deformation.Artin.descentHom_of_full 𝒳.val.p hp
      (D' ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c')
  -- descend the section
  obtain ⟨k, χ, hχ⟩ :=
    TwoFibreProductOver.DiagonalFibre.VertHom.exists_restrict_eq_of_descentHom hp
      (TwoFibreProductOver.DiagonalFibre.h1' hy) (TwoFibreProductOver.DiagonalFibre.h2' hy)
      D c hdesc ((pe.equiv (op c.pt)).symm x)
  refine ⟨colimit.ι (D.op ⋙ F) (op k) (pe.equiv (op (D.obj k)) χ), ?_, ?_⟩
  · rw [colimit.ι_desc_apply]
    refine Eq.trans ?_ ((pe.equiv (op c.pt)).apply_symm_apply x)
    rw [← hχ, ← TwoFibreProductOver.DiagonalFibre.VertHom.presheaf_map]
    exact (pe.naturality (c.π.app k).op χ).symm
  · have : Subsingleton (colimit (D.op ⋙ yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))) := by
      refine subsingleton_colimit _ (fun j => ?_)
      exact ⟨fun a b => Over.mkIdTerminal.hom_ext a b⟩
    exact this.elim _ _

end AlgebraicGeometry.Stack

end
