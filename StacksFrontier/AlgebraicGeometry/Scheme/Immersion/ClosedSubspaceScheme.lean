module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IntoAffine
public import StacksFrontier.AlgebraicGeometry.Schemes.ClosedImmersions.Pullback

/-!
# The source of a closed immersion into a scheme is a scheme

Let `X` be a scheme and let `i : Z ⟶ X` be a closed immersion of locally ringed spaces. Over an
affine open `U = Spec R` of `X` the inverse image of `U` is `Spec (R ⧸ I)` for an ideal `I` of
`R`, compatibly with the canonical affine presentation of `U`. Those affine pieces cover `Z`, so
`Z` carries a scheme structure; in particular every closed subspace of a scheme is a scheme.

## Main definitions

* `Stacks.ClosedImmersion.closedSubscheme` is the scheme structure on the closed subspace cut out
  by a locally generated ideal sheaf, and `Stacks.ClosedImmersion.closedSubschemeInclusion` its
  closed immersion into the ambient scheme.

## Main results

* `Stacks.ClosedImmersion.exists_ideal_iso_quotient_of_isAffineOpen`: the inverse image of an
  affine open is the spectrum of a quotient of its ring of sections.
* `Stacks.ClosedImmersion.exists_scheme_of_isClosedImmersion`: the source of a closed immersion
  into a scheme admits a scheme structure on its underlying locally ringed space.
* `Stacks.ClosedImmersion.exists_scheme_of_closedSubspace`: the closed subspace cut out by a
  locally generated ideal sheaf on a scheme is a scheme.

## Implementation notes

The affine-local statement is reduced to [Stacks, Tag 01IH], the classification of closed
immersions into an affine scheme. Getting there uses the inverse-image ideal of Tag 01HQ twice:
once along `U.ι` to cut the closed subspace of `U` out of the closed subspace of `X`, and once
along `hU.isoSpec.inv` to transport it to `Spec Γ(X, U)`. Both squares are fibre squares, so the
pullback `Z ×_X U` of locally ringed spaces is identified with the closed subspace of
`Spec Γ(X, U)`, to which Tag 01IH applies.

Mathlib bundles the affine-neighbourhood condition into `AlgebraicGeometry.Scheme`, so the
conclusion that `Z` is a scheme is phrased as the existence of a scheme whose *underlying locally
ringed space is `Z` itself* — an equality, not merely an isomorphism — so that the ideal sheaf and
the inclusion of `Z` are unchanged by passing to the scheme. The local affine condition is
verified through `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme`: around a point
`z` of `Z` the projection `Z ×_X U ⟶ Z` for an affine open `U` containing `i z` is an open
immersion whose image contains `z`, and its source is an affine scheme by the affine-local
statement.

## References

* [Stacks Project, Tag 01HQ](https://stacks.math.columbia.edu/tag/01HQ)
* [Stacks Project, Tag 01IH](https://stacks.math.columbia.edu/tag/01IH)
* [Stacks Project, Tag 01IN](https://stacks.math.columbia.edu/tag/01IN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.ClosedImmersion

/-! ### The affine-local description -/

/-- The affine-local description, with the closed subspace of `X` realizing the ideal sheaf and
the affine presentation of `U` supplied as data. -/
private theorem exists_ideal_iso_quotient_aux {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace)
    (J : SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    (k : J ⟶ SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace)) [Mono k]
    (hJ : Nonempty (SheafOfModules.LocalGeneratorsData.{u} J))
    (eX : Z ≅ (closedSubspace X.toLocallyRingedSpace J k hJ).space)
    (heX : eX.hom ≫ (closedSubspace X.toLocallyRingedSpace J k hJ).inclusion = i)
    (U : X.Opens)
    (eU : (U : Scheme).toLocallyRingedSpace ≅ (Spec Γ(X, U)).toLocallyRingedSpace) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback i U.ι.toLRSHom ≅
        (Spec (CommRingCat.of (Γ(X, U) ⧸ I))).toLocallyRingedSpace),
      pullback.snd i U.ι.toLRSHom ≫ eU.hom =
        e.hom ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom := by
  have hpb₁ : IsPullback (pullbackClosedSubspace U.ι.toLRSHom J k hJ).inclusion
      (restrictedMap U.ι.toLRSHom J k hJ ≫ eX.inv) U.ι.toLRSHom i :=
    (restrictedMap_isPullback U.ι.toLRSHom J k hJ).of_iso (Iso.refl _) (Iso.refl _) eX.symm
      (Iso.refl _) (by simp) (by simp) (by simp)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, (Iso.inv_comp_eq eX).2 heX.symm])
  have htriv : IsPullback
      ((pullbackClosedSubspace U.ι.toLRSHom J k hJ).inclusion ≫ eU.hom)
      (𝟙 (pullbackClosedSubspace U.ι.toLRSHom J k hJ).space) eU.inv
      (pullbackClosedSubspace U.ι.toLRSHom J k hJ).inclusion :=
    IsPullback.of_vert_isIso ⟨by rw [Category.assoc, eU.hom_inv_id, Category.comp_id,
      Category.id_comp]⟩
  have hpb₂ := restrictedMap_isPullback eU.inv (pullbackIdeal U.ι.toLRSHom J k)
    (pullbackIdealInclusion U.ι.toLRSHom J k)
    (pullbackIdeal_locallyGenerated U.ι.toLRSHom J k hJ)
  have he₂ := hpb₂.isoIsPullback_hom_fst _ _ htriv
  obtain ⟨I, ⟨e₂q, he₂q⟩, -⟩ := existsUnique_ideal_iso_quotientSpec
    (pullbackClosedSubspace eU.inv (pullbackIdeal U.ι.toLRSHom J k)
      (pullbackIdealInclusion U.ι.toLRSHom J k)
      (pullbackIdeal_locallyGenerated U.ι.toLRSHom J k hJ)).inclusion
  refine ⟨I, hpb₁.flip.isoPullback.symm ≪≫
    (hpb₂.isoIsPullback _ _ htriv).symm ≪≫
    e₂q, ?_⟩
  refine ((congrArg (fun z ↦ z ≫ eU.hom)
    ((Iso.eq_inv_comp hpb₁.flip.isoPullback).2 hpb₁.flip.isoPullback_hom_snd)).trans
    ((Category.assoc _ _ _).trans ?_))
  refine (congrArg (fun z ↦ hpb₁.flip.isoPullback.inv ≫ z) (((Iso.eq_inv_comp _).2 he₂).trans
    (congrArg (fun z ↦ _ ≫ z) he₂q))).trans ?_
  exact (congrArg (fun z ↦ hpb₁.flip.isoPullback.inv ≫ z) (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm

/-- Over an affine open `U` of a scheme `X`, a closed immersion of locally ringed spaces
`i : Z ⟶ X` is, compatibly with the canonical presentation of `U` as `Spec Γ(X, U)`, the spectrum
of a quotient of `Γ(X, U)`. -/
@[stacks 01IN "affine_local_quotient"]
theorem exists_ideal_iso_quotient_of_isAffineOpen (X : Scheme.{u}) (Z : LocallyRingedSpace.{u})
    (i : Z ⟶ X.toLocallyRingedSpace) [hi : IsClosedImmersion i.toShHom]
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback i U.ι.toLRSHom ≅
        (Spec (CommRingCat.of (Γ(X, U) ⧸ I))).toLocallyRingedSpace),
      pullback.snd i U.ι.toLRSHom ≫ hU.isoSpec.hom.toLRSHom =
        e.hom ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).toLRSHom := by
  have hk : Mono (kernel.ι (SheafOfModules.unitToPushforwardObjUnit
    (structureSheafHom i.toShHom))) := equalizer.ι_mono
  obtain ⟨eX, heX, -⟩ := existsUnique_iso_closedSubspace i
  exact exists_ideal_iso_quotient_aux i (idealSheaf i.toShHom)
    (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom i.toShHom)))
    hi.kernel_locallyGenerated eX heX U
    (Scheme.forgetToLocallyRingedSpace.mapIso hU.isoSpec)

/-! ### The source is a scheme -/

/-- The source of a closed immersion of locally ringed spaces into a scheme carries a scheme
structure. -/
@[stacks 01IN "source_is_scheme"]
theorem exists_scheme_of_isClosedImmersion (X : Scheme.{u}) (Z : LocallyRingedSpace.{u})
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i.toShHom] :
    ∃ Z' : Scheme.{u}, Z'.toLocallyRingedSpace = Z := by
  refine ⟨LocallyRingedSpace.IsOpenImmersion.scheme Z fun z ↦ ?_, rfl⟩
  let U : X.Opens := (X.affineCover.f (X.affineCover.idx (i.base z))).opensRange
  obtain ⟨I, e, -⟩ :=
    exists_ideal_iso_quotient_of_isAffineOpen X Z i U (isAffineOpen_opensRange _)
  let j := pullback.fst i U.ι.toLRSHom
  let e' := e ≪≫ eqToIso (Spec.toLocallyRingedSpace_obj _).symm
  refine ⟨CommRingCat.of (Γ(X, U) ⧸ I), e'.inv ≫ j, ?_, inferInstance⟩
  rw [show Set.range (e'.inv ≫ j).base = Set.range j.base by
    simpa only [LocallyRingedSpace.comp_base, TopCat.coe_comp] using
      ((TopCat.epi_iff_surjective _).mp (by
        change Epi ((LocallyRingedSpace.forgetToSheafedSpace ⋙
          SheafedSpace.forgetToPresheafedSpace ⋙ PresheafedSpace.forget _).map e'.inv)
        infer_instance)).range_comp j.base]
  let F := LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace
  refine show (show F.obj Z from z) ∈ Set.range (F.map (pullback.fst i U.ι.toLRSHom)).base from ?_
  rw [← congrArg PresheafedSpace.Hom.base
    (PreservesPullback.iso_hom_fst F i U.ι.toLRSHom),
    PresheafedSpace.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr,
    Set.image_univ]
  · let G := PresheafedSpace.forget CommRingCat
    change (show G.obj (F.obj Z) from z) ∈
      Set.range (G.map (pullback.fst (F.map i) (F.map U.ι.toLRSHom)))
    rw [← PreservesPullback.iso_hom_fst G (F.map i) (F.map U.ι.toLRSHom), TopCat.coe_comp,
      Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ, TopCat.pullback_fst_range]
    · exact ⟨⟨i.base z, X.affineCover.covers (i.base z)⟩, rfl⟩
    · exact (TopCat.epi_iff_surjective _).mp inferInstance
  · exact (TopCat.epi_iff_surjective _).mp inferInstance

/-- The scheme structure on the source of a closed immersion of locally ringed spaces into a
scheme, carried by that locally ringed space itself. -/
def sourceScheme (X : Scheme.{u}) (Z : LocallyRingedSpace.{u}) (i : Z ⟶ X.toLocallyRingedSpace)
    [IsClosedImmersion i.toShHom] : Scheme.{u} where
  toLocallyRingedSpace := Z
  local_affine := (Classical.choose_spec (exists_scheme_of_isClosedImmersion X Z i)) ▸
    (Classical.choose (exists_scheme_of_isClosedImmersion X Z i)).local_affine

/-- The underlying locally ringed space of `sourceScheme X Z i` is `Z`. -/
@[simp]
theorem sourceScheme_toLocallyRingedSpace (X : Scheme.{u}) (Z : LocallyRingedSpace.{u})
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i.toShHom] :
    (sourceScheme X Z i).toLocallyRingedSpace = Z := rfl

/-- A closed immersion of locally ringed spaces into a scheme, read as a morphism of schemes. -/
def sourceSchemeHom (X : Scheme.{u}) (Z : LocallyRingedSpace.{u})
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i.toShHom] : sourceScheme X Z i ⟶ X :=
  ⟨i⟩

/-- The morphism of locally ringed spaces underlying `sourceSchemeHom X Z i` is `i`. -/
@[simp]
theorem sourceSchemeHom_toLRSHom (X : Scheme.{u}) (Z : LocallyRingedSpace.{u})
    (i : Z ⟶ X.toLocallyRingedSpace) [IsClosedImmersion i.toShHom] :
    (sourceSchemeHom X Z i).toLRSHom = i := rfl

/-! ### Closed subspaces of schemes are schemes -/

/-- The closed subspace of a scheme cut out by a locally generated ideal sheaf carries a scheme
structure on its underlying locally ringed space. -/
@[stacks 01IN "closed_subspace_is_scheme"]
theorem exists_scheme_of_closedSubspace (X : Scheme.{u})
    (J : SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    [Mono j] (hJ : Nonempty (SheafOfModules.LocalGeneratorsData.{u} J)) :
    ∃ Z : Scheme.{u}, Z.toLocallyRingedSpace =
      (closedSubspace X.toLocallyRingedSpace J j hJ).space :=
  exists_scheme_of_isClosedImmersion X _ (closedSubspace X.toLocallyRingedSpace J j hJ).inclusion

/-- The closed subscheme cut out by a locally generated ideal sheaf, with underlying locally
ringed space exactly the closed subspace of [Stacks, Tag 01HN]. -/
def closedSubscheme (X : Scheme.{u})
    (J : SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    [Mono j] (hJ : Nonempty (SheafOfModules.LocalGeneratorsData.{u} J)) : Scheme.{u} where
  toLocallyRingedSpace := (closedSubspace X.toLocallyRingedSpace J j hJ).space
  local_affine :=
    (Classical.choose_spec (exists_scheme_of_closedSubspace X J j hJ)) ▸
      (Classical.choose (exists_scheme_of_closedSubspace X J j hJ)).local_affine

/-- The underlying locally ringed space of the closed subscheme is the closed subspace cut out
by the ideal sheaf. -/
@[simp]
theorem closedSubscheme_toLocallyRingedSpace (X : Scheme.{u})
    (J : SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    [Mono j] (hJ : Nonempty (SheafOfModules.LocalGeneratorsData.{u} J)) :
    (closedSubscheme X J j hJ).toLocallyRingedSpace =
      (closedSubspace X.toLocallyRingedSpace J j hJ).space := rfl

/-- The canonical closed immersion of the closed subscheme into the ambient scheme. -/
def closedSubschemeInclusion (X : Scheme.{u})
    (J : SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    [Mono j] (hJ : Nonempty (SheafOfModules.LocalGeneratorsData.{u} J)) :
    closedSubscheme X J j hJ ⟶ X :=
  ⟨(closedSubspace X.toLocallyRingedSpace J j hJ).inclusion⟩

/-- The inclusion of the closed subscheme into the ambient scheme is a closed immersion. -/
instance closedSubschemeInclusion_isClosedImmersion (X : Scheme.{u})
    (J : SheafOfModules.{u} (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    (j : J ⟶ SheafOfModules.unit (structureSheafRing X.toLocallyRingedSpace.toRingedSpace))
    [Mono j] (hJ : Nonempty (SheafOfModules.LocalGeneratorsData.{u} J)) :
    IsClosedImmersion (closedSubschemeInclusion X J j hJ).toLRSHom.toShHom :=
  closedSubspace_isClosedImmersion X.toLocallyRingedSpace J j hJ

end Stacks.ClosedImmersion

end
