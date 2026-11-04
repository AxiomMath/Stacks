module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentationAssembly
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SymmetricAlgebraSheafUngradedLift
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsDirectImageAlgebraFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FinitePresentationQuotientQcqs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-affine morphism of finite type to a qcqs space is closed in one of finite presentation

This file proves Stacks 0871 for a general quasi-compact, quasi-separated algebraic space as
target: a morphism `f : X ⟶ Y` of algebraic spaces over `S` which is locally of finite type and
quasi-affine, with `Y` quasi-compact and quasi-separated, factors as a closed immersion
`X ⟶ X'` followed by a morphism `X' ⟶ Y` of finite presentation.

## Main results

* `exists_symmetricAlgebra_algebraHom_of_hom_underlyingModule`: a morphism of modules from a
  quasi-coherent module of finite presentation into an algebra sheaf extends to a morphism out of a
  quasi-coherent algebra of finite presentation reaching the same sections.
* `exists_isFiniteTypeOnSite_submodule_of_finset`: finitely many sections of a quasi-coherent
  module over an affine étale chart of a quasi-compact quasi-separated algebraic space lie in a
  quasi-coherent submodule of finite type.
* `exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom_of_qcqs`: a quasi-affine
  morphism locally of finite type to a quasi-compact quasi-separated algebraic space is a closed
  immersion followed by a morphism of finite presentation.

## References

* [Stacks Project, Tag 0871](https://stacks.math.columbia.edu/tag/0871)
* [Stacks Project, Tag 086Y](https://stacks.math.columbia.edu/tag/086Y)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace SheafOfModules

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat}

/-- A sheaf of modules of finite presentation on a site is quasi-coherent. -/
@[ega "0 5.2.5" "more general"]
theorem IsFinitePresentationOnSite.isQuasicoherentOnSite {M : SheafOfModules R}
    (h : M.IsFinitePresentationOnSite) : M.IsQuasicoherentOnSite where
  locally_hasGlobalPresentation U := by
    obtain ⟨I, V, f, hcov, hp⟩ := h.locally_hasFiniteGlobalPresentation U
    exact ⟨I, V, f, hcov, fun i => (hp i).hasGlobalPresentation⟩

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A morphism of modules from a quasi-coherent module of finite presentation into an algebra
sheaf extends to a morphism out of a quasi-coherent algebra of finite presentation reaching the
same sections**: the symmetric algebra, with the ungraded lift of the morphism. -/
theorem exists_symmetricAlgebra_algebraHom_of_hom_underlyingModule (W : AlgebraicSpaces B S hS)
    (A : AlgebraSheaf.{u, u} B S hS W.1 W.2)
    (G : SheafOfModules.{u} (structureRingSheaf B S hS W)) (hG : G.IsQuasicoherentOnSite)
    (hfp : SheafOfModules.IsFinitePresentationOnSite G) (p : G ⟶ AlgebraSheaf.underlyingModule A)
    (U : SmallEtale B S hS W.1) (s : Set (A.right.obj.obj (op U)))
    (hs : s ⊆ Set.range (p.val.app (op U))) :
    ∃ (C : QuasicoherentAlgebra B S hS W) (_ : AlgebraSheaf.SectionsBelowCutoff B S hS C.obj),
      C.obj.IsFinitePresentation ∧ ∃ φ : C.obj ⟶ A, s ⊆ Set.range (φ.right.hom.app (op U)) := by
  refine ⟨⟨symmetricAlgebraSheaf B S hS W G, isQuasicoherent_symmetricAlgebraSheaf B S hS W G hG⟩,
    sectionsBelowCutoff_symmetricAlgebraSheaf B S hS W G hG hfp,
    isFinitePresentation_symmetricAlgebraSheaf B S hS W G hG hfp,
    SymAlgSheaf.algebraLift B S hS W A G p, fun t ht => ?_⟩
  obtain ⟨g, rfl⟩ := hs ht
  exact ⟨_, SymAlgSheaf.algebraLift_ungradedIncl_gen B S hS W A G p (op U) g⟩

/-- **Finitely many sections of a quasi-coherent module over an affine étale chart of a
quasi-compact quasi-separated algebraic space lie in a quasi-coherent submodule of finite
type.** -/
theorem exists_isFiniteTypeOnSite_submodule_of_finset (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : F.IsQuasicoherentOnSite) (U : SmallEtale B S hS X.1) (hU : IsAffine (chartScheme U))
    (s : Finset (F.val.obj (op U))) :
    ∃ N : F.Submodule, SheafOfModules.IsFiniteTypeOnSite N.toSheafOfModules ∧
      N.toSheafOfModules.IsQuasicoherentOnSite ∧ ∀ σ ∈ s, σ ∈ N.obj (op U) := by
  have hcart := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 F hF
  obtain ⟨D, hD⟩ := (chartExtensionProperty_id (hX := X.2) hZ hqc hqs hcart).exists_forall_mem
    hcart s (fun _ => U) (fun _ => U.1.hom) (fun _ => Category.comp_id _) (fun _ => hU) id
  exact ⟨D.toSubmodule F, D.isFiniteTypeOnSite_toSubmodule hcart,
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X.1 X.2 _).2
      (D.isCartesianOnAffineCharts_toSubmodule hcart), fun σ hσ => hD σ hσ⟩

/-- The sections of a submodule over an affine chart are reached by a quotient map from a
quasi-coherent module onto the (quasi-coherent) submodule. -/
theorem subset_range_comp_ι_of_epi {X : AlgebraicSpaces B S hS}
    {F : Modules.{u, u} B S hS X.1 X.2} (N : F.Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherentOnSite) {G : Modules.{u, u} B S hS X.1 X.2}
    (hG : G.IsQuasicoherentOnSite) (π : G ⟶ N.toSheafOfModules) (hπ : Epi π)
    (U : SmallEtale B S hS X.1)
    (hU : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (s : Set (F.val.obj (op U))) (hs : ∀ σ ∈ s, σ ∈ N.obj (op U)) :
    s ⊆ Set.range ((π ≫ N.ι).val.app (op U)) := by
  intro σ hσ
  obtain ⟨g, hg⟩ := surjective_val_app_of_epi_of_isQuasicoherentOnSite π hπ hG hN U hU
    (⟨σ, hs σ hσ⟩ : N.toSheafOfModules.val.obj (op U))
  exact ⟨g, congrArg (fun t : N.toSheafOfModules.val.obj (op U) => N.ι.val.app (op U) t) hg⟩

/-- Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is locally of finite type and quasi-affine, with `Y` quasi-compact and
quasi-separated.  Then there are a morphism of finite presentation `f' : X' ⟶ Y` and a closed
immersion `i : X ⟶ X'` with `i ≫ f' = f`. -/
@[stacks 0871]
theorem exists_isFinitePresentation_isClosedImmersion_of_isQuasiAffineHom_of_qcqs
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hft : IsLocallyOfFiniteType B S hS f) (hfqa : IsQuasiAffineHom B S hS f)
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y) :
    ∃ (X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (f' : X' ⟶ Y) (i : X ⟶ X'),
      IsAlgebraicSpace B S hS X' ∧ IsFinitePresentation B S hS f' ∧
        IsClosedImmersion B S hS i ∧ i ≫ f' = f := by
  let Ys : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let g : Xs ⟶ Ys := ObjectProperty.homMk (P := IsAlgebraicSpace B S hS) (X := Xs) (Y := Ys) f
  have hfpre : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f :=
    ((isQuasiAffineHom_tfae_of_isAlgebraicSpace hX hY f).out 2 1).mp hfqa
  have hfqc : IsQuasiCompact B S hS f :=
    isQuasiCompact_of_presheaf_quasiCompact B S hS
      (MorphismProperty.relative_monotone (MorphismProperty.monotone_inverseImage _
        (fun X' Y' k (hk : @_root_.AlgebraicGeometry.IsQuasiAffineHom X' Y' k) => by
          have := hk; exact (inferInstance : QuasiCompact k))) _ hfpre)
  have hfqs : IsQuasiSeparated B S hS f :=
    (isQuasiSeparated_iff_presheaf B S hS f hX hY hfpre.rep).2
      (MorphismProperty.relative_monotone (MorphismProperty.monotone_inverseImage _
        (fun X' Y' k (hk : @_root_.AlgebraicGeometry.IsQuasiAffineHom X' Y' k) => by
          have := hk; exact (inferInstance : QuasiSeparated k))) _ hfpre)
  obtain ⟨U, hU, s, hs⟩ := exists_finset_forall_algebraHom_exists_isClosedImmersion B S hS
    B.contains_terminal g hfqa hft hYqc hYqs
  let F : Modules.{u, u} B S hS Ys.1 Ys.2 :=
    AlgebraSheaf.underlyingModule (pushforwardAlgebra B S hS (Over.mk g))
  have hF : F.IsQuasicoherentOnSite :=
    isQuasicoherent_pushforwardAlgebra_unconditional B S hS (Over.mk g) hfqc hfqs
  let s' : Finset (F.val.obj (op U)) := s
  obtain ⟨N, hNft, hNqc, hsN⟩ := exists_isFiniteTypeOnSite_submodule_of_finset B S hS
    B.contains_terminal (X := Ys) hYqc hYqs F hF U hU s'
  have := hNft
  obtain ⟨G, hGfp, π, hπ⟩ := exists_epi_of_isFinitePresentationOnSite_of_isFiniteType B S hS
    B.contains_terminal hY hYqc hYqs N.toSheafOfModules hNqc
  have hGqc : G.IsQuasicoherentOnSite := hGfp.isQuasicoherentOnSite
  have hrange : (s' : Set (F.val.obj (op U))) ⊆ Set.range ((π ≫ N.ι).val.app (op U)) :=
    subset_range_comp_ι_of_epi B S hS N hNqc hGqc π hπ U hU (s' : Set _) (fun σ hσ => hsN σ hσ)
  obtain ⟨C, hC, hCfp, φ, hφ⟩ := exists_symmetricAlgebra_algebraHom_of_hom_underlyingModule B S hS
    Ys (pushforwardAlgebra B S hS (Over.mk g)) G hGqc hGfp (π ≫ N.ι) U (s : Set _) hrange
  exact hs C hC hCfp φ hφ
end AlgebraicGeometry.Space

end
