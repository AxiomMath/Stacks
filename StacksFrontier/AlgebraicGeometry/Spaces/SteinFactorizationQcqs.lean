module

public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationGeneral

/-!
# The Stein factorization of a universally closed morphism: `f'_* 𝒪_X = 𝒪_{Y'}`

Let `f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S`, let
`ν : Y' ⟶ Y` be the normalization of `Y` in `X` (`AlgebraicGeometry.Space.normalizationInQcqsHom`)
and `f' : X ⟶ Y'` the canonical factorization (`AlgebraicGeometry.Space.toNormalizationInQcqs`).
Then `f'` is quasi-separated, the identity of `Y'` exhibits `Y'` as the normalization of `Y'` in
`X` along `f'`, and, when `f` is universally closed, the structure map `𝒪_{Y'} ⟶ f'_* 𝒪_X` is an
isomorphism.

## Main results

* `AlgebraicGeometry.Space.isQuasiSeparated_toNormalizationInQcqs`: `f'` is quasi-separated.
* `AlgebraicGeometry.Space.isRelativeNormalization_id_toNormalizationInQcqs`: `Y'` is the
  normalization of itself in `X`.
* `AlgebraicGeometry.Space.isIso_fSharp_toNormalizationInQcqs`: `f'_* 𝒪_X = 𝒪_{Y'}` for a
  universally closed `f`.
* `AlgebraicGeometry.Space.isIso_commRingSheafHom_of_bijective_app`: a morphism of sheaves of
  commutative rings on the small étale site which is bijective on every chart is invertible.

## References

* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0A0Q](https://stacks.math.columbia.edu/tag/0A0Q)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 04XW](https://stacks.math.columbia.edu/tag/04XW)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 03KR](https://stacks.math.columbia.edu/tag/03KR)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- A morphism of sheaves of commutative rings on the small étale site of an algebraic space
which is bijective on every chart is an isomorphism. -/
theorem isIso_commRingSheafHom_of_bijective_app {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {R R' : Sheaf (SmallEtale.topology B S hS F) CommRingCat.{u}} (φ : R ⟶ R')
    (h : ∀ U, Function.Bijective (φ.hom.app U)) : IsIso φ := by
  have : IsIso ((sheafToPresheaf _ _).map φ) := by
    have : ∀ U, IsIso (((sheafToPresheaf _ _).map φ).app U) := fun U =>
      (ConcreteCategory.isIso_iff_bijective _).2 (h U)
    exact NatIso.isIso_of_isIso_app _
  exact isIso_of_reflects_iso _ (sheafToPresheaf _ _)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-- The canonical morphism `f' : X ⟶ Y'` to the normalization of `Y` in `X` is
quasi-separated. -/
theorem isQuasiSeparated_toNormalizationInQcqs :
    IsQuasiSeparated B S hS (toNormalizationInQcqs f hfqc hfqs).hom := by
  refine isQuasiSeparated_of_comp B S hS _ (normalizationInQcqsHom B S hS f hfqc hfqs).hom ?_
  rw [← ObjectProperty.FullSubcategory.comp_hom, toNormalizationInQcqs_comp]
  exact hfqs

/-- **`Y'` is the normalization of itself in `X`**: the identity of `Y'` exhibits `Y'` as the
normalization of `Y'` in `X` along `f'`. -/
theorem isRelativeNormalization_id_toNormalizationInQcqs :
    IsRelativeNormalization B S hS (toNormalizationInQcqs f hfqc hfqs).hom
      (𝟙 (normalizationInQcqs B S hS f hfqc hfqs).1) (toNormalizationInQcqs f hfqc hfqs).hom :=
  (isRelativeNormalization_normalizationInQcqs f hfqc hfqs).comparison Y.2
    (normalizationInQcqs B S hS f hfqc hfqs).2 (isIntegralHom_normalizationInQcqsHom f hfqc hfqs)
    (Category.comp_id _) (Category.id_comp _)

/-- The map `𝟙_* 𝒪_{Y'} ⟶ f'_* 𝒪_X` of `𝒪_{Y'}`-algebras induced by `f'` is invertible when `f`
is universally closed. -/
theorem isIso_pushforwardAlgebraMap_overHomToId_toNormalizationInQcqs
    (huc : UniversallyClosed B S hS f.hom) :
    IsIso (pushforwardAlgebraMap B S hS
      (overHomToId B S hS (toNormalizationInQcqs f hfqc hfqs))) := by
  have huc' := universallyClosed_toNormalizationInQcqs B S hS f hfqc hfqs huc
  have hqc' := isQuasiCompact_toNormalizationInQcqs B S hS f hfqc hfqs
  have hqs' := isQuasiSeparated_toNormalizationInQcqs f hfqc hfqs
  obtain ⟨φ, ⟨hφ1, hφ2⟩, -⟩ := existsUnique_iso_normalizationInQcqs_of_isRelativeNormalization
    (toNormalizationInQcqs f hfqc hfqs) hqc' hqs' (normalizationInQcqs B S hS f hfqc hfqs).2
    (isRelativeNormalization_id_toNormalizationInQcqs f hfqc hfqs)
  let N := normalizationInQcqsAffineOver B S hS (toNormalizationInQcqs f hfqc hfqs) hqc' hqs'
  let I := idAffineOver B S hS (normalizationInQcqs B S hS f hfqc hfqs)
  let Φ : N.obj ⟶ I.obj := Over.homMk (ObjectProperty.homMk φ.hom) (ObjectProperty.hom_ext _ hφ2)
  let Φinv : I.obj ⟶ N.obj :=
    Over.homMk (ObjectProperty.homMk φ.inv) (ObjectProperty.hom_ext _ (by
      change φ.inv ≫ (normalizationInQcqsHom B S hS _ hqc' hqs').hom = 𝟙 _
      rw [← hφ2, Category.comp_id, Iso.inv_hom_id]))
  have hΦ : Φ ≫ Φinv = 𝟙 _ := Over.OverMorphism.ext (ObjectProperty.hom_ext _ φ.hom_inv_id)
  have hΦ' : Φinv ≫ Φ = 𝟙 _ := Over.OverMorphism.ext (ObjectProperty.hom_ext _ φ.inv_hom_id)
  have hfac : toNormalizationInQcqsOver (toNormalizationInQcqs f hfqc hfqs) hqc' hqs' ≫ Φ =
      overHomToId B S hS (toNormalizationInQcqs f hfqc hfqs) :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hφ1)
  have : IsIso (pushforwardAlgebraMap B S hS Φ) :=
    ⟨pushforwardAlgebraMap B S hS Φinv,
      by rw [← pushforwardAlgebraMap_comp, hΦ', pushforwardAlgebraMap_id],
      by rw [← pushforwardAlgebraMap_comp, hΦ, pushforwardAlgebraMap_id]⟩
  have := isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed
    (toNormalizationInQcqs f hfqc hfqs) hqc' hqs' huc'
  rw [← hfac, pushforwardAlgebraMap_comp]
  infer_instance

/-- **`f'_* 𝒪_X = 𝒪_{Y'}`.** For a universally closed `f`, the structure map `𝒪_{Y'} ⟶ f'_* 𝒪_X`
of the canonical morphism `f' : X ⟶ Y'` to the normalization of `Y` in `X` is an isomorphism of
sheaves of rings on the small étale site of `Y'`. -/
theorem isIso_fSharp_toNormalizationInQcqs (huc : UniversallyClosed B S hS f.hom) :
    IsIso (smallEtaleRingedToposHom B S hS (toNormalizationInQcqs f hfqc hfqs)).fSharp := by
  have := isIso_pushforwardAlgebraMap_overHomToId_toNormalizationInQcqs f hfqc hfqs huc
  let e := asIso (pushforwardAlgebraMap B S hS
    (overHomToId B S hS (toNormalizationInQcqs f hfqc hfqs)))
  have hbij : ∀ U : (SmallEtale B S hS (normalizationInQcqs B S hS f hfqc hfqs).1)ᵒᵖ,
      Function.Bijective ((smallEtaleRingedToposHom B S hS
        (toNormalizationInQcqs f hfqc hfqs)).fSharp.hom.app U) := by
    intro U
    have h1 : ∀ x, (e.inv.right.hom.app U) (e.hom.right.hom.app U x) = x :=
      AlgebraSheaf.iso_inv_right_app_hom_right_app e U
    have h2 : ∀ y, (e.hom.right.hom.app U) (e.inv.right.hom.app U y) = y :=
      AlgebraSheaf.iso_inv_right_app_hom_right_app e.symm U
    have hb : Function.Bijective (e.hom.right.hom.app U) :=
      ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩
    have heq : ⇑((smallEtaleRingedToposHom B S hS
        (toNormalizationInQcqs f hfqc hfqs)).fSharp.hom.app U) =
        ⇑(e.hom.right.hom.app U) ∘ (pushforwardAlgebra B S hS
          (idAffineOver B S hS (normalizationInQcqs B S hS f hfqc hfqs)).obj).algebraMap U := by
      funext r
      exact (pushforwardAlgebraMap_overHomToId_algebraMap B S hS
        (toNormalizationInQcqs f hfqc hfqs) U r).symm
    rw [heq]
    exact hb.comp (bijective_pushforwardAlgebra_id_algebraMap B S hS _ U)
  exact isIso_commRingSheafHom_of_bijective_app _ hbij

end AlgebraicGeometry.Space

end
