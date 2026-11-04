module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.OpenCoverAtlas
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveMorFunctorsBounded
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ProjectiveSpaceHilbertModels
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationSizeBounds

/-!
# The Hilbert models of `ℙⁿ_U ⟶ U` have atlases of bounded size

The model of the Hilbert presheaf of `ℙⁿ_U ⟶ U` built in
`StacksFrontier/AlgebraicGeometry/Quot/C1590Private/ProjectiveSpaceHilbertModels.lean` is glued from
the open subspaces `Quot^P`, `P ∈ ℚ[t]`, each represented by `U × X_P`, where
`X_P = Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` (`AlgebraicGeometry.C1590Private.hilbertQuotScheme`) does not depend on
`U`. So `Quot^P` has the identity atlas of `U × X_P`, of size at most `max |U| |X_P|`. The
coproduct of these atlases, indexed by the countable `ℚ[t]`, is an atlas of `∐ Quot^P` of size
at most `κ = max ℵ₀ (max μ (sup_P |X_P|))` (bounded Stacks 02WQ,
`AlgebraicGeometry.Space.isAlgebraicSpaceAtlasSizeLE_coproduct`), and followed by the open covering
`∐ Quot^P ⟶ Quot` it is an atlas of the model
(`AlgebraicGeometry.C1590Private.atlas_comp_of_open_cover`). The cutoff of the site has
uncountable cofinality, so `κ` is below the cutoff.

## Main results

* `AlgebraicGeometry.C1590Private.projectiveSpaceHilbertModelsBounded`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.C1590Private

open ProjectiveQuot ProjectiveQuotOverSpace

universe u

variable {B : BigFppfSite.{u}} (n : ℕ) (U : BigFppfOver B integerBase B.contains_integerBase)

local notation "𝒯" => BigFppfOver.toScheme B integerBase B.contains_integerBase

/-- The site over `Spec ℤ` has binary products. -/
local instance : HasBinaryProducts (BigFppfOver B integerBase B.contains_integerBase) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- The underlying scheme of a product in the site over `Spec ℤ` is no larger than the larger of
the two factors. -/
theorem size_prod_le (X Y : BigFppfOver B integerBase B.contains_integerBase) :
    ((𝒯).obj (X ⨯ Y)).size ≤ max ((𝒯).obj X).size ((𝒯).obj Y).size := by
  rw [Scheme.size_congr ((𝒯).mapIso (prodIsoPullback X Y))]
  exact Space.size_pullback_le B integerBase B.contains_integerBase _ _

/-- A representable presheaf is an algebraic space with the identity atlas. -/
theorem isAlgebraicSpaceAtlasSizeLE_yoneda (V : BigFppfOver B integerBase B.contains_integerBase) :
    Space.IsAlgebraicSpaceAtlasSizeLE B integerBase B.contains_integerBase (yoneda.obj V)
      ((𝒯).obj V).size :=
  ⟨isAlgebraicSpace_yoneda B integerBase B.contains_integerBase V, V, 𝟙 _,
    presheaf_id_of_iso B integerBase B.contains_integerBase _ (fun _ _ f hf => by
      have : IsIso f := hf
      show Surjective ((𝒯).map f)
      infer_instance) V,
    presheaf_id_of_iso B integerBase B.contains_integerBase _ (fun _ _ f hf => by
      have : IsIso f := hf
      show Etale ((𝒯).map f)
      infer_instance) V, le_rfl⟩

/-- **`Quot^P` has an atlas of size at most `max |U| |X_P|`**, namely the identity of
`U × X_P`. -/
theorem isAlgebraicSpaceAtlasSizeLE_hilbertModelSubfunctor (P : Polynomial ℚ) :
    Space.IsAlgebraicSpaceAtlasSizeLE B integerBase B.contains_integerBase
      (hilbertModelSubfunctor n U P).toFunctor
      (max ((𝒯).obj U).size (hilbertQuotScheme.{u} n P).size) := by
  have e' := ((Functor.FullyFaithful.ofFullyFaithful uliftFunctor.{u + 1, u}).whiskeringRight
    (BigFppfOver B integerBase B.contains_integerBase)ᵒᵖ).preimageIso
      (hilbertModelSubfunctorIso n U P ≪≫ hilbertSubfunctorReprIso P)
  exact ((isAlgebraicSpaceAtlasSizeLE_yoneda _).of_iso e').mono (size_prod_le _ _)

/-- The supremum over `P` of the sizes of `X_P = Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}` is below the cutoff. -/
theorem iSup_size_hilbertQuotScheme_lt (B : BigFppfSite.{u}) :
    ⨆ P : ULift.{u} (Polynomial ℚ), (hilbertQuotScheme.{u} n P.down).size < B.cutoff :=
  Cardinal.iSup_lt_of_lt_cof_ord (lt_of_le_of_lt Cardinal.mk_le_aleph0 B.aleph0_lt_cutoff_cof)
    fun P => contains_hilbertQuotScheme B n P.down

/-- **The Hilbert model of `ℙⁿ_U ⟶ U` has an atlas of size at most `κ`**, for every infinite
cardinal `κ` below the cutoff bounding `U` and every `X_P`. -/
theorem exists_atlas_projectiveSpaceHilbertModel {κ : Cardinal.{u}} (hℵ : ℵ₀ ≤ κ)
    (hκ : κ < B.cutoff) (hU : ((𝒯).obj U).size ≤ κ)
    (hX : ∀ P : Polynomial ℚ, (hilbertQuotScheme.{u} n P).size ≤ κ) :
    ∃ (A : BigFppfOver B integerBase B.contains_integerBase)
      (a : yoneda.obj A ⟶ (projectiveSpaceHilbertModel n U).presheaf),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (𝒯))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (𝒯))) a ∧
      ((𝒯).obj A).size ≤ κ := by
  have hF : ∀ P : ULift.{u} (Polynomial ℚ),
      Space.IsAlgebraicSpaceAtlasSizeLE B integerBase B.contains_integerBase
        (hilbertModelSubfunctor n U P.down).toFunctor κ := fun P =>
    (isAlgebraicSpaceAtlasSizeLE_hilbertModelSubfunctor n U P.down).mono (max_le hU (hX P.down))
  obtain ⟨-, W, v, hvs, hve, hW⟩ := Space.isAlgebraicSpaceAtlasSizeLE_coproduct B integerBase
    B.contains_integerBase
    (fun P : ULift.{u} (Polynomial ℚ) => (hilbertModelSubfunctor n U P.down).toFunctor)
    hℵ hκ (Cardinal.mk_le_aleph0.trans hℵ) hF (∐ hilbertModelSheaves n U)
    (Sigma.ι (hilbertModelSheaves n U)) (coproductIsCoproduct _)
  obtain ⟨hs, he⟩ := atlas_comp_of_open_cover B integerBase B.contains_integerBase _
    (isAlgebraicSpace_projectiveSpaceQuotModel n U) (ULift.{u} (Polynomial ℚ))
    (hilbertModelSheaves n U) _ (Sigma.ι (hilbertModelSheaves n U)) (coproductIsCoproduct _)
    (hilbertModelCoproductDesc n U).hom (fun P => by
      rw [ι_hilbertModelCoproductDesc]
      exact isOpenImmersion_hilbertModelSubfunctor_ι n U P.down)
    (isLocallySurjective_hilbertModelCoproductDesc n U) v hvs hve
  exact ⟨W, v ≫ (hilbertModelCoproductDesc n U).hom, hs, he, hW⟩

variable (B) in
/-- **Hilbert models of projective spaces with atlases of bounded size.** For `U` of size at most
`μ`, the model of the Hilbert presheaf of `ℙⁿ_U ⟶ U` has an atlas of size at most
`max ℵ₀ (max μ (sup_P |Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}|))`, which is below the cutoff. -/
theorem projectiveSpaceHilbertModelsBounded (hZ : B.Contains integerBase) :
    ProjectiveSpaceHilbertModelsBounded B hZ := by
  intro n μ hμ
  have hκ := max_lt B.aleph0_lt_cutoff (max_lt hμ (iSup_size_hilbertQuotScheme_lt n B))
  refine ⟨_, hκ, fun U _ hU => ?_⟩
  obtain ⟨A, a, hs, he, hA⟩ := exists_atlas_projectiveSpaceHilbertModel n U (le_max_left _ _) hκ
    (hU.trans ((le_max_left _ _).trans (le_max_right _ _))) fun P =>
      (le_ciSup Cardinal.bddAbove_of_small (ULift.up P : ULift.{u} (Polynomial ℚ))).trans
        ((le_max_right _ _).trans (le_max_right _ _))
  exact ⟨projectiveSpaceHilbertModel n U, A, a, isAlgebraicSpace_projectiveSpaceHilbertModel n U,
    hs, he, hA⟩

end AlgebraicGeometry.C1590Private

end
