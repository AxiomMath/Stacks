module

public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessLocalRingApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.LocalRingBaseChange

/-!
# Uniqueness of contractions near a point (Stacks 0E89)

Let `S` be a scheme and `s ∈ S` a point. Let `f : X ⟶ S` and `gᵢ : Yᵢ ⟶ S`, `i = 1, 2`, be
families of curves and `cᵢ : X ⟶ Yᵢ` morphisms over `S`. Suppose there is an isomorphism
`Y₁,ₛ ≅ Y₂,ₛ` of fibres compatible with `c₁,ₛ` and `c₂,ₛ`, and that `c₁,ₛ,* 𝒪_{Xₛ} = 𝒪_{Y₁,ₛ}` and
`R¹c₁,ₛ,* 𝒪_{Xₛ} = 0`. Then there are an open neighbourhood `U` of `s` and an isomorphism
`Y₁,U ≅ Y₂,U` of families of curves over `U` compatible with the given isomorphism of fibres and
with `c₁` and `c₂` ([Stacks, Tag 0E89]).

Over `Spec 𝒪_{S,s}`, the spectrum of a local ring with closed point `s`, the statement is
`AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isLocalRing_of_siteObject`. Since
`Spec 𝒪_{S,s}` is the limit of the affine open neighbourhoods of `s`, the isomorphism over
`Spec 𝒪_{S,s}` and its compatibility with the `cᵢ` are already defined over one of them
([Stacks, Tag 07SK], `AlgebraicGeometry.Space.exists_iso_stage_of_iso`).

## Main results

* `AlgebraicGeometry.Space.exists_iso_near_point_of_iso_fibre`: an isomorphism of the fibres
  over `s` of two contractions of a family of curves extends to an open neighbourhood of `s`.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 07SK](https://stacks.math.columbia.edu/tag/07SK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Space

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The fibre of a base change over a point factoring through it.** If `P = P₁ ≫ P₂`, the base
change along `P₁` of the base change of `h` along `P₂` is the base change of `h` along `P`. -/
theorem exists_iso_pullback_pullback_of_comp {Z T T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (h : Z ⟶ T) (P₁ : T₁ ⟶ T₂) (P₂ : T₂ ⟶ T) (P : T₁ ⟶ T) (hP : P₁ ≫ P₂ = P) :
    ∃ τ : pullback (pullback.snd h P₂) P₁ ≅ pullback h P,
      τ.hom ≫ pullback.fst h P = pullback.fst _ _ ≫ pullback.fst _ _ ∧
      τ.hom ≫ pullback.snd h P = pullback.snd _ _ := by
  have sq : IsPullback (pullback.fst (pullback.snd h P₂) P₁ ≫ pullback.fst h P₂)
      (pullback.snd (pullback.snd h P₂) P₁) h P := by
    rw [← hP]
    exact (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback _ _)
  exact ⟨sq.isoPullback, sq.isoPullback_hom_fst, sq.isoPullback_hom_snd⟩

end General

section Integers

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

local notation "𝒯" => BigFppfOver.toScheme B integerBase hZ

/-- The spectrum of the residue field of a point `s` of a scheme `S` of the site. -/
abbrev pointFieldObject (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S) :
    BigFppfOver B integerBase hZ :=
  integerSiteObject B hZ (B.residueField_spec_contains S.left.property s)

/-- The point `Spec κ(s) ⟶ S`. -/
def pointFieldMap (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S) :
    pointFieldObject S s ⟶ S :=
  Over.homMk (ObjectProperty.homMk (((𝒯).obj S).fromSpecResidueField s))
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The spectrum `Spec 𝒪_{S,s}` of the local ring of `S` at `s`. -/
abbrev localSchemeObject (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S) :
    BigFppfOver B integerBase hZ :=
  integerSiteObject B hZ (B.contains_spec_stalk_of_contains S.left.property s)

/-- The canonical morphism `Spec 𝒪_{S,s} ⟶ S`. -/
def localSchemeMap (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S) :
    localSchemeObject S s ⟶ S :=
  Over.homMk (ObjectProperty.homMk (((𝒯).obj S).fromSpecStalk s))
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The closed point `Spec κ(s) ⟶ Spec 𝒪_{S,s}`. -/
abbrev localSchemeClosedPoint (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S) :
    pointFieldObject S s ⟶ localSchemeObject S s :=
  integerSiteMap B hZ _ _ (Spec.map (((𝒯).obj S).residue s))

/-- The closed point `Spec κ(s) ⟶ Spec 𝒪_{S,s}` followed by `Spec 𝒪_{S,s} ⟶ S` is the point
`Spec κ(s) ⟶ S`. -/
theorem localSchemeClosedPoint_localSchemeMap (S : BigFppfOver B integerBase hZ)
    (s : (𝒯).obj S) :
    localSchemeClosedPoint S s ≫ localSchemeMap S s = pointFieldMap S s := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (((𝒯).obj S).residue s) ≫ ((𝒯).obj S).fromSpecStalk s =
    ((𝒯).obj S).fromSpecResidueField s
  rfl

/-- The base change of an algebraic space along a morphism of the site is an algebraic space. -/
private theorem isAlgebraicSpace_pullback_yoneda {S U : BigFppfOver B integerBase hZ}
    (j : U ⟶ S) {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} (g : Y ⟶ yoneda.obj S)
    (hY : IsAlgebraicSpace B integerBase hZ Y) :
    IsAlgebraicSpace B integerBase hZ (pullback g (yoneda.map j)) :=
  isAlgebraicSpace_pullback B integerBase hZ _ _ hY (isAlgebraicSpace_yoneda B integerBase hZ U)
    (isAlgebraicSpace_yoneda B integerBase hZ S)

/-- The base change of a morphism of finite presentation along a morphism of the site is of finite
presentation. -/
private theorem isFinitePresentation_snd_pullback_yoneda {S U : BigFppfOver B integerBase hZ}
    (j : U ⟶ S) {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S}
    (hY : IsAlgebraicSpace B integerBase hZ Y) (hg : IsFinitePresentation B integerBase hZ g) :
    IsFinitePresentation B integerBase hZ (pullback.snd g (yoneda.map j)) :=
  isFinitePresentation_of_isPullback B integerBase hZ (isAlgebraicSpace_pullback_yoneda j g hY) hY
    (isAlgebraicSpace_yoneda B integerBase hZ U) (isAlgebraicSpace_yoneda B integerBase hZ S)
    (IsPullback.of_hasPullback _ _) hg

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **[Stacks, Tag 0E89] over `Spec 𝒪_{S,s}`.** Under the hypotheses of
`AlgebraicGeometry.Space.exists_iso_near_point_of_iso_fibre`, the base changes of `Y₁` and `Y₂`
to `Spec 𝒪_{S,s}` are isomorphic, compatibly with the `cᵢ` and with the given isomorphism of the
fibres over `s`. This is the local case
`AlgebraicGeometry.Space.exists_iso_of_closedFibre_of_isLocalRing_of_siteObject`, the fibres over
the closed point of `Spec 𝒪_{S,s}` being the fibres over `s`. -/
theorem exists_iso_stalk_of_iso_fibre (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S)
    {X Y₁ Y₂ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B integerBase hZ X) (hY₁ : IsAlgebraicSpace B integerBase hZ Y₁)
    (hY₂ : IsAlgebraicSpace B integerBase hZ Y₂)
    (f : X ⟶ yoneda.obj S) (g₁ : Y₁ ⟶ yoneda.obj S) (g₂ : Y₂ ⟶ yoneda.obj S)
    (hfl : IsFlat B integerBase hZ f) (hpr : IsProper B integerBase hZ f)
    (hfp : IsFinitePresentation B integerBase hZ f)
    (hd : HasRelativeDimensionLE 1 B integerBase hZ f)
    (hfl₁ : IsFlat B integerBase hZ g₁) (hpr₁ : IsProper B integerBase hZ g₁)
    (hfp₁ : IsFinitePresentation B integerBase hZ g₁)
    (hd₁ : HasRelativeDimensionLE 1 B integerBase hZ g₁)
    (hfl₂ : IsFlat B integerBase hZ g₂) (hpr₂ : IsProper B integerBase hZ g₂)
    (hfp₂ : IsFinitePresentation B integerBase hZ g₂)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = f) (hc₂ : c₂ ≫ g₂ = f)
    {FX F₁ : BigFppfOver B integerBase hZ}
    (eX : yoneda.obj FX ≅ pullback f (yoneda.map (pointFieldMap S s)))
    (e₁ : yoneda.obj F₁ ≅ pullback g₁ (yoneda.map (pointFieldMap S s)))
    (tX : FX ⟶ pointFieldObject S s) (t₁ : F₁ ⟶ pointFieldObject S s)
    (heX : eX.hom ≫ pullback.snd f (yoneda.map (pointFieldMap S s)) = yoneda.map tX)
    (he₁ : e₁.hom ≫ pullback.snd g₁ (yoneda.map (pointFieldMap S s)) = yoneda.map t₁)
    (a₁ : FX ⟶ F₁)
    (ha₁ : yoneda.map a₁ ≫ e₁.hom =
      eX.hom ≫ pullback.map f (yoneda.map (pointFieldMap S s)) g₁
        (yoneda.map (pointFieldMap S s)) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁]) (by simp))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁)))
    (φ : pullback g₁ (yoneda.map (pointFieldMap S s)) ≅
      pullback g₂ (yoneda.map (pointFieldMap S s)))
    (hφ : φ.hom ≫ pullback.snd g₂ (yoneda.map (pointFieldMap S s)) =
      pullback.snd g₁ (yoneda.map (pointFieldMap S s)))
    (hφc : pullback.map f (yoneda.map (pointFieldMap S s)) g₁
        (yoneda.map (pointFieldMap S s)) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁]) (by simp) ≫ φ.hom =
      pullback.map f (yoneda.map (pointFieldMap S s)) g₂
        (yoneda.map (pointFieldMap S s)) c₂ (𝟙 _) (𝟙 _) (by simp [hc₂]) (by simp)) :
    ∃ ψ : pullback g₁ (yoneda.map (localSchemeMap S s)) ≅
        pullback g₂ (yoneda.map (localSchemeMap S s)),
      ψ.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      pullback.map f (yoneda.map (localSchemeMap S s)) g₁ (yoneda.map (localSchemeMap S s)) c₁ (𝟙 _)
          (𝟙 _) (by simp [hc₁]) (by simp) ≫ ψ.hom =
        pullback.map f (yoneda.map (localSchemeMap S s)) g₂ (yoneda.map (localSchemeMap S s)) c₂
          (𝟙 _) (𝟙 _) (by simp [hc₂]) (by simp) ∧
      pullback.map g₁ (yoneda.map (pointFieldMap S s)) g₁ (yoneda.map (localSchemeMap S s))
          (𝟙 _) (yoneda.map (localSchemeClosedPoint S s)) (𝟙 _) (by simp)
          (by rw [Category.comp_id, ← Functor.map_comp, localSchemeClosedPoint_localSchemeMap]) ≫
          ψ.hom =
        φ.hom ≫ pullback.map g₂ (yoneda.map (pointFieldMap S s)) g₂
          (yoneda.map (localSchemeMap S s)) (𝟙 _) (yoneda.map (localSchemeClosedPoint S s)) (𝟙 _)
          (by simp)
          (by rw [Category.comp_id, ← Functor.map_comp,
            localSchemeClosedPoint_localSchemeMap]) := by
  have hk : (yoneda.map (localSchemeClosedPoint S s)) ≫ (yoneda.map (localSchemeMap S s)) =
      (yoneda.map (pointFieldMap S s)) := by
    rw [← Functor.map_comp, localSchemeClosedPoint_localSchemeMap]
  have hXW := isAlgebraicSpace_pullback_yoneda (localSchemeMap S s) f hX
  have hY₁W := isAlgebraicSpace_pullback_yoneda (localSchemeMap S s) g₁ hY₁
  have hY₂W := isAlgebraicSpace_pullback_yoneda (localSchemeMap S s) g₂ hY₂
  obtain ⟨hflW, hprW, hfpW, hdW⟩ := curveFamilyConditions_of_isPullback B integerBase hZ
    (IsPullback.of_hasPullback f (yoneda.map (localSchemeMap S s))) hX hXW hfl hpr hfp hd
  obtain ⟨hfl₁W, hpr₁W, hfp₁W, hd₁W⟩ := curveFamilyConditions_of_isPullback B integerBase hZ
    (IsPullback.of_hasPullback g₁ (yoneda.map (localSchemeMap S s))) hY₁ hY₁W hfl₁ hpr₁ hfp₁ hd₁
  obtain ⟨hfl₂W, hpr₂W, hfp₂W⟩ := isFlat_isProper_isFinitePresentation_of_isPullback B integerBase
    hZ (IsPullback.of_hasPullback g₂ (yoneda.map (localSchemeMap S s))) hY₂ hY₂W hfl₂ hpr₂ hfp₂
  obtain ⟨τX, hτXf, hτXs⟩ := exists_iso_pullback_pullback_of_comp B integerBase hZ f _ _ _ hk
  obtain ⟨τ₁, hτ₁f, hτ₁s⟩ := exists_iso_pullback_pullback_of_comp B integerBase hZ g₁ _ _ _ hk
  obtain ⟨τ₂, hτ₂f, hτ₂s⟩ := exists_iso_pullback_pullback_of_comp B integerBase hZ g₂ _ _ _ hk
  have hτc : ∀ {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S}
      (c : X ⟶ Y) (hc : c ≫ g = f)
      (τ : pullback (pullback.snd g (yoneda.map (localSchemeMap S s)))
          (yoneda.map (localSchemeClosedPoint S s)) ≅ pullback g (yoneda.map (pointFieldMap S s)))
      (_ : τ.hom ≫ pullback.fst g (yoneda.map (pointFieldMap S s)) =
        pullback.fst _ _ ≫ pullback.fst _ _)
      (_ : τ.hom ≫ pullback.snd g (yoneda.map (pointFieldMap S s)) = pullback.snd _ _),
      pullback.map (pullback.snd f (yoneda.map (localSchemeMap S s)))
          (yoneda.map (localSchemeClosedPoint S s))
          (pullback.snd g (yoneda.map (localSchemeMap S s)))
          (yoneda.map (localSchemeClosedPoint S s))
          (pullback.map f (yoneda.map (localSchemeMap S s)) g (yoneda.map (localSchemeMap S s)) c
            (𝟙 _) (𝟙 _) (by simp [hc]) (by simp)) (𝟙 _) (𝟙 _)
          (by simp) (by simp) ≫ τ.hom =
        τX.hom ≫ pullback.map f (yoneda.map (pointFieldMap S s)) g (yoneda.map (pointFieldMap S s))
          c (𝟙 _) (𝟙 _) (by simp [hc]) (by simp) := by
    intro Y g c hc τ hτf hτs
    apply pullback.hom_ext
    · simp [hτf, reassoc_of% hτXf]
    · simp [hτs, hτXs]
  have hτc₁ := hτc c₁ hc₁ τ₁ hτ₁f hτ₁s
  have hι : (Iso.refl (Spec (.of (ResidueField ((𝒯).obj S |>.presheaf.stalk s))))).hom ≫
      (𝒯).map (localSchemeClosedPoint S s) ≫
        (Iso.refl (Spec (.of ((𝒯).obj S |>.presheaf.stalk s)))).hom =
      ContractionUniquenessComplete.closedPoint ((𝒯).obj S |>.presheaf.stalk s) := by
    simp only [Iso.refl_hom, Category.id_comp]
    rfl
  obtain ⟨ψ, hψg, hψc, hψf⟩ := exists_iso_of_closedFibre_of_isLocalRing_of_siteObject
    ((𝒯).obj S |>.presheaf.stalk s) (W := localSchemeObject S s) (Iso.refl _) hXW hY₁W hY₂W
    (pullback.snd f (yoneda.map (localSchemeMap S s)))
    (pullback.snd g₁ (yoneda.map (localSchemeMap S s)))
    (pullback.snd g₂ (yoneda.map (localSchemeMap S s))) hflW hprW hfpW hdW hfl₁W
    hpr₁W hfp₁W hd₁W hfl₂W hpr₂W hfp₂W
    (pullback.map f (yoneda.map (localSchemeMap S s)) g₁ (yoneda.map (localSchemeMap S s)) c₁
      (𝟙 _) (𝟙 _) (by simp [hc₁]) (by simp))
    (pullback.map f (yoneda.map (localSchemeMap S s)) g₂ (yoneda.map (localSchemeMap S s)) c₂
      (𝟙 _) (𝟙 _) (by simp [hc₂]) (by simp)) (by simp) (by simp)
    (localSchemeClosedPoint S s) (Iso.refl _) hι (eX ≪≫ τX.symm) (e₁ ≪≫ τ₁.symm) tX t₁
    (by rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← heX, ← hτXs, Iso.inv_hom_id_assoc])
    (by rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he₁, ← hτ₁s, Iso.inv_hom_id_assoc])
    a₁ (by
      rw [Iso.trans_hom, Iso.symm_hom, Iso.trans_hom, Iso.symm_hom, reassoc_of% ha₁]
      simp only [Category.assoc]
      refine congrArg (eX.hom ≫ ·) ?_
      rw [Iso.comp_inv_eq, Category.assoc, hτc₁, Iso.inv_hom_id_assoc])
    h0 hR (τ₁ ≪≫ φ ≪≫ τ₂.symm)
    (by rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Category.assoc, Category.assoc,
      ← hτ₂s, Iso.inv_hom_id_assoc, hφ, hτ₁s])
    (by rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, reassoc_of% hτc₁, reassoc_of% hφc,
      ← Category.assoc, ← hτc c₂ hc₂ τ₂ hτ₂f hτ₂s, Category.assoc, Iso.hom_inv_id,
      Category.comp_id])
  refine ⟨ψ, hψg, hψc, ?_⟩
  have hfib : ∀ {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S}
      (τ : pullback (pullback.snd g (yoneda.map (localSchemeMap S s)))
          (yoneda.map (localSchemeClosedPoint S s)) ≅ pullback g (yoneda.map (pointFieldMap S s)))
      (_ : τ.hom ≫ pullback.fst g (yoneda.map (pointFieldMap S s)) =
        pullback.fst _ _ ≫ pullback.fst _ _)
      (_ : τ.hom ≫ pullback.snd g (yoneda.map (pointFieldMap S s)) = pullback.snd _ _),
      pullback.map g (yoneda.map (pointFieldMap S s)) g (yoneda.map (localSchemeMap S s)) (𝟙 _)
          (yoneda.map (localSchemeClosedPoint S s)) (𝟙 _) (by simp) (by rw [Category.comp_id, hk]) =
        τ.inv ≫ pullback.fst _ _ := by
    intro Y g τ hτf hτs
    rw [Iso.eq_inv_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, hτf]
      simp
    · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hτs]
      exact pullback.condition.symm
  rw [hfib τ₁ hτ₁f hτ₁s, hfib τ₂ hτ₂f hτ₂s, Category.assoc, hψf]
  simp

/-- **An isomorphism of models over `U` is an isomorphism of the base changes to `U`.** If
`Xⱼ`, `Y₁ⱼ`, `Y₂ⱼ` are, through cartesian squares, the base changes of `X`, `Y₁`, `Y₂` along
`j : U ⟶ S`, with `cₖⱼ` modelling the `cₖ`, an isomorphism `ψⱼ : Y₁ⱼ ≅ Y₂ⱼ` over `U` with
`c₁ⱼ ≫ ψⱼ = c₂ⱼ` gives an isomorphism of the fibre products `Y₁ ×_S U ≅ Y₂ ×_S U` over `U`
compatible with the `cₖ`; and if the fibre maps `mₖ` over a point `k'` of `U` are compatible with
`ψⱼ` and `φ`, so are the canonical fibre maps. -/
theorem exists_iso_pullback_of_isPullback_models {S U K : BigFppfOver B integerBase hZ}
    (jU : U ⟶ S) (kS : K ⟶ S) (k' : K ⟶ U) (hk : k' ≫ jU = kS)
    {X Y₁ Y₂ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {f : X ⟶ yoneda.obj S}
    {g₁ : Y₁ ⟶ yoneda.obj S} {g₂ : Y₂ ⟶ yoneda.obj S} (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂)
    (hc₁ : c₁ ≫ g₁ = f) (hc₂ : c₂ ≫ g₂ = f)
    (φ : pullback g₁ (yoneda.map kS) ≅ pullback g₂ (yoneda.map kS))
    {Xj Y₁j Y₂j : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {fXj : Xj ⟶ yoneda.obj U}
    {g₁j : Y₁j ⟶ yoneda.obj U} {g₂j : Y₂j ⟶ yoneda.obj U} {pX : Xj ⟶ X} {p₁ : Y₁j ⟶ Y₁}
    {p₂ : Y₂j ⟶ Y₂} (sqX : IsPullback pX fXj f (yoneda.map jU))
    (sq₁ : IsPullback p₁ g₁j g₁ (yoneda.map jU)) (sq₂ : IsPullback p₂ g₂j g₂ (yoneda.map jU))
    (c₁j : Xj ⟶ Y₁j) (c₂j : Xj ⟶ Y₂j) (hc₁j : c₁j ≫ g₁j = fXj) (hc₂j : c₂j ≫ g₂j = fXj)
    (hcp₁ : c₁j ≫ p₁ = pX ≫ c₁) (hcp₂ : c₂j ≫ p₂ = pX ≫ c₂) (ψj : Y₁j ≅ Y₂j)
    (hψg : ψj.hom ≫ g₂j = g₁j) (hψc : c₁j ≫ ψj.hom = c₂j)
    (m₁ : pullback g₁ (yoneda.map kS) ⟶ Y₁j) (m₂ : pullback g₂ (yoneda.map kS) ⟶ Y₂j)
    (hm₁p : m₁ ≫ p₁ = pullback.fst _ _) (hm₂p : m₂ ≫ p₂ = pullback.fst _ _)
    (hm₁g : m₁ ≫ g₁j = pullback.snd _ _ ≫ yoneda.map k')
    (hm₂g : m₂ ≫ g₂j = pullback.snd _ _ ≫ yoneda.map k')
    (hm : m₁ ≫ ψj.hom = φ.hom ≫ m₂) :
    ∃ ψ : pullback g₁ (yoneda.map jU) ≅ pullback g₂ (yoneda.map jU),
      ψ.hom ≫ pullback.snd g₂ (yoneda.map jU) = pullback.snd g₁ (yoneda.map jU) ∧
      pullback.map f (yoneda.map jU) g₁ (yoneda.map jU) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁])
          (by simp) ≫ ψ.hom =
        pullback.map f (yoneda.map jU) g₂ (yoneda.map jU) c₂ (𝟙 _) (𝟙 _) (by simp [hc₂])
          (by simp) ∧
      pullback.map g₁ (yoneda.map kS) g₁ (yoneda.map jU) (𝟙 _) (yoneda.map k') (𝟙 _) (by simp)
          (by rw [Category.comp_id, ← Functor.map_comp, hk]) ≫ ψ.hom =
        φ.hom ≫ pullback.map g₂ (yoneda.map kS) g₂ (yoneda.map jU) (𝟙 _) (yoneda.map k') (𝟙 _)
          (by simp) (by rw [Category.comp_id, ← Functor.map_comp, hk]) := by
  refine ⟨sq₁.isoPullback.symm ≪≫ ψj ≪≫ sq₂.isoPullback, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_hom_snd, hψg,
      IsPullback.isoPullback_inv_snd]
  · have hmod : ∀ {Y Yj : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S}
        {gj : Yj ⟶ yoneda.obj U} {p : Yj ⟶ Y} (sq : IsPullback p gj g (yoneda.map jU))
        (c : X ⟶ Y) (hc : c ≫ g = f) (cj : Xj ⟶ Yj) (hcj : cj ≫ gj = fXj)
        (hcp : cj ≫ p = pX ≫ c),
        pullback.map f (yoneda.map jU) g (yoneda.map jU) c (𝟙 _) (𝟙 _) (by simp [hc]) (by simp) =
          sqX.isoPullback.inv ≫ cj ≫ sq.isoPullback.hom := by
      intro Y Yj g gj p sq c hc cj hcj hcp
      apply pullback.hom_ext
      · simp only [Category.assoc, IsPullback.isoPullback_hom_fst]
        rw [hcp, IsPullback.isoPullback_inv_fst_assoc]
        simp
      · simp only [Category.assoc, IsPullback.isoPullback_hom_snd, hcj,
          IsPullback.isoPullback_inv_snd]
        simp
    rw [hmod sq₁ c₁ hc₁ c₁j hc₁j hcp₁, hmod sq₂ c₂ hc₂ c₂j hc₂j hcp₂]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      reassoc_of% hψc]
  · have hfib : ∀ {Y Yj : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S}
        {gj : Yj ⟶ yoneda.obj U} {p : Yj ⟶ Y} (sq : IsPullback p gj g (yoneda.map jU))
        (m : pullback g (yoneda.map kS) ⟶ Yj) (_ : m ≫ p = pullback.fst _ _)
        (_ : m ≫ gj = pullback.snd _ _ ≫ yoneda.map k'),
        pullback.map g (yoneda.map kS) g (yoneda.map jU) (𝟙 _) (yoneda.map k') (𝟙 _) (by simp)
            (by rw [Category.comp_id, ← Functor.map_comp, hk]) = m ≫ sq.isoPullback.hom := by
      intro Y Yj g gj p sq m hmp hmg
      apply pullback.hom_ext
      · simp only [Category.assoc, IsPullback.isoPullback_hom_fst, hmp]
        simp
      · simp only [Category.assoc, IsPullback.isoPullback_hom_snd, hmg]
        simp
    rw [hfib sq₁ m₁ hm₁p hm₁g, hfib sq₂ m₂ hm₂p hm₂g]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc,
      reassoc_of% hm]

/-- An open of a scheme of the site is in the site. -/
theorem contains_affineNhds_opens (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S)
    (i : Scheme.AffineNhds ((𝒯).obj S) s) : B.Contains i.opens.toScheme :=
  Scheme.size_lt_of_isOpenImmersion i.opens.ι S.left.property

/-- The affine open neighbourhoods of a point `s` of a scheme `S` of the site, as a diagram of the
site of the integers. -/
def integerAffineNhdsDiagram (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S) :
    (Scheme.AffineNhds ((𝒯).obj S) s)ᵒᵖ ⥤ BigFppfOver B integerBase hZ :=
  (ObjectProperty.lift _ (Scheme.AffineNhds.diagram ((𝒯).obj S) s)
    (fun i => contains_affineNhds_opens S s i.unop) :
      _ ⥤ B.Schemes) ⋙ schemeOverIntegers B

/-- The canonical morphism from `Spec 𝒪_{S,s}` to an affine open neighbourhood of `s`. -/
def integerAffineNhdsPi (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S)
    (i : (Scheme.AffineNhds ((𝒯).obj S) s)ᵒᵖ) :
    localSchemeObject S s ⟶ (integerAffineNhdsDiagram (hZ := hZ) S s).obj i :=
  integerSiteMap B hZ _ _ ((Scheme.affineNhdsSpecStalkCone ((𝒯).obj S) s).π.app i)

/-- The cone of the affine open neighbourhoods of `s` with vertex `Spec 𝒪_{S,s}`. -/
def integerAffineNhdsCone (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S) :
    Cone (integerAffineNhdsDiagram (hZ := hZ) S s) where
  pt := localSchemeObject S s
  π :=
    { app i := integerAffineNhdsPi S s i
      naturality {_ _} e := Over.OverMorphism.ext (ObjectProperty.hom_ext _
        ((Scheme.affineNhdsSpecStalkCone ((𝒯).obj S) s).π.naturality e)) }

/-- **`Spec 𝒪_{S,s}` is the limit of the affine open neighbourhoods of `s`, in the site.** -/
def isLimitIntegerAffineNhdsCone (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S) :
    IsLimit ((𝒯).mapCone (integerAffineNhdsCone (hZ := hZ) S s)) :=
  let hl := Scheme.isLimitAffineNhdsSpecStalkCone ((𝒯).obj S) s
  let α : Scheme.AffineNhds.diagram ((𝒯).obj S) s ≅ integerAffineNhdsDiagram (hZ := hZ) S s ⋙ 𝒯 :=
    NatIso.ofComponents (fun i => Iso.refl _) (fun {i j} e => by
      simp only [Iso.refl_hom]
      rfl)
  ((IsLimit.postcomposeHomEquiv α _).symm hl).ofIsoLimit (Cone.ext (Iso.refl _) fun i => by
    change (Scheme.affineNhdsSpecStalkCone ((𝒯).obj S) s).π.app i ≫ 𝟙 _ =
      𝟙 _ ≫ (Scheme.affineNhdsSpecStalkCone ((𝒯).obj S) s).π.app i
    simp)

/-- The inclusion of an affine open neighbourhood of `s` into `S`. -/
def integerAffineNhdsMap (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S)
    (i : (Scheme.AffineNhds ((𝒯).obj S) s)ᵒᵖ) :
    (integerAffineNhdsDiagram (hZ := hZ) S s).obj i ⟶ S :=
  Over.homMk (ObjectProperty.homMk (Scheme.Opens.ι i.unop.opens))
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- The morphism `Spec 𝒪_{S,s} ⟶ U` to an affine open neighbourhood `U` of `s`, followed by the
inclusion `U ⟶ S`, is the canonical morphism `Spec 𝒪_{S,s} ⟶ S`. -/
theorem integerAffineNhdsPi_integerAffineNhdsMap (S : BigFppfOver B integerBase hZ)
    (s : (𝒯).obj S) (i : (Scheme.AffineNhds ((𝒯).obj S) s)ᵒᵖ) :
    integerAffineNhdsPi S s i ≫ integerAffineNhdsMap S s i = localSchemeMap S s :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.Opens.fromSpecStalkOfMem_ι _ _ _))

/-- The inclusions of the affine open neighbourhoods of `s` into `S` commute with the inclusions
between neighbourhoods. -/
theorem integerAffineNhdsDiagram_map_integerAffineNhdsMap (S : BigFppfOver B integerBase hZ)
    (s : (𝒯).obj S) {i j : (Scheme.AffineNhds ((𝒯).obj S) s)ᵒᵖ} (e : i ⟶ j) :
    (integerAffineNhdsDiagram (hZ := hZ) S s).map e ≫ integerAffineNhdsMap S s j =
      integerAffineNhdsMap S s i :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.homOfLE_ι _ (leOfHom e.unop)))

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- Let `S` be a scheme and `s ∈ S` a point. Let `f : X ⟶ S` and `gᵢ : Yᵢ ⟶ S`, `i = 1, 2`, be
families of curves (algebraic spaces, flat, proper, of finite presentation and of relative
dimension at most one over `S`) and `cᵢ : X ⟶ Yᵢ` morphisms over `S`. Let `φ : Y₁,ₛ ≅ Y₂,ₛ` be an
isomorphism of the fibres over `Spec κ(s) ⟶ S` compatible with `c₁,ₛ` and `c₂,ₛ`. Suppose
`c₁,ₛ,* 𝒪_{Xₛ} = 𝒪_{Y₁,ₛ}` and `R¹c₁,ₛ,* 𝒪_{Xₛ} = 0`; these are read on the morphism of schemes
`a₁ : F_X ⟶ F₁` which `c₁,ₛ` is through presentations `e_X`, `e₁` of the fibres `Xₛ` and `Y₁,ₛ`
by schemes (the fibres of a family of curves over a field are schemes, [Stacks, Tag 0ADD],
`AlgebraicGeometry.Space.exists_presentation_of_curveFamilyConditions_of_field`). Then there are
an open neighbourhood `j : U ⟶ S` of `s` and an isomorphism `ψ : Y₁ ×_S U ≅ Y₂ ×_S U` over `U`,
compatible with `c₁` and `c₂` and with `φ` (through the factorisation `k` of `Spec κ(s) ⟶ S`
through `U`). -/
@[stacks 0E89 "Families of curves are read as in `AlgebraicGeometry.CurveFamily` (Stacks 0D4Z): \
algebraic spaces `X`, `Y₁`, `Y₂` with morphisms to `S` which are flat, proper, of finite \
presentation and of relative dimension at most one. The fibres over `s` are the fibre products \
along `Spec κ(s) ⟶ S`; the hypotheses on `c₁,ₛ` are read on the morphism of schemes presenting \
it (the fibres being schemes by Stacks 0ADD)."]
theorem exists_iso_near_point_of_iso_fibre (S : BigFppfOver B integerBase hZ) (s : (𝒯).obj S)
    {X Y₁ Y₂ : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B integerBase hZ X) (hY₁ : IsAlgebraicSpace B integerBase hZ Y₁)
    (hY₂ : IsAlgebraicSpace B integerBase hZ Y₂)
    (f : X ⟶ yoneda.obj S) (g₁ : Y₁ ⟶ yoneda.obj S) (g₂ : Y₂ ⟶ yoneda.obj S)
    (hfl : IsFlat B integerBase hZ f) (hpr : IsProper B integerBase hZ f)
    (hfp : IsFinitePresentation B integerBase hZ f)
    (hd : HasRelativeDimensionLE 1 B integerBase hZ f)
    (hfl₁ : IsFlat B integerBase hZ g₁) (hpr₁ : IsProper B integerBase hZ g₁)
    (hfp₁ : IsFinitePresentation B integerBase hZ g₁)
    (hd₁ : HasRelativeDimensionLE 1 B integerBase hZ g₁)
    (hfl₂ : IsFlat B integerBase hZ g₂) (hpr₂ : IsProper B integerBase hZ g₂)
    (hfp₂ : IsFinitePresentation B integerBase hZ g₂)
    (c₁ : X ⟶ Y₁) (c₂ : X ⟶ Y₂) (hc₁ : c₁ ≫ g₁ = f) (hc₂ : c₂ ≫ g₂ = f)
    {FX F₁ : BigFppfOver B integerBase hZ}
    (eX : yoneda.obj FX ≅ pullback f (yoneda.map (pointFieldMap S s)))
    (e₁ : yoneda.obj F₁ ≅ pullback g₁ (yoneda.map (pointFieldMap S s)))
    (tX : FX ⟶ pointFieldObject S s) (t₁ : F₁ ⟶ pointFieldObject S s)
    (heX : eX.hom ≫ pullback.snd f (yoneda.map (pointFieldMap S s)) = yoneda.map tX)
    (he₁ : e₁.hom ≫ pullback.snd g₁ (yoneda.map (pointFieldMap S s)) = yoneda.map t₁)
    (a₁ : FX ⟶ F₁)
    (ha₁ : yoneda.map a₁ ≫ e₁.hom =
      eX.hom ≫ pullback.map f (yoneda.map (pointFieldMap S s)) g₁
        (yoneda.map (pointFieldMap S s)) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁]) (by simp))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit ((𝒯).map a₁)))
    (hR : IsZero (firstDirectImageStructureSheaf ((𝒯).map a₁)))
    (φ : pullback g₁ (yoneda.map (pointFieldMap S s)) ≅
      pullback g₂ (yoneda.map (pointFieldMap S s)))
    (hφ : φ.hom ≫ pullback.snd g₂ (yoneda.map (pointFieldMap S s)) =
      pullback.snd g₁ (yoneda.map (pointFieldMap S s)))
    (hφc : pullback.map f (yoneda.map (pointFieldMap S s)) g₁
        (yoneda.map (pointFieldMap S s)) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁]) (by simp) ≫ φ.hom =
      pullback.map f (yoneda.map (pointFieldMap S s)) g₂
        (yoneda.map (pointFieldMap S s)) c₂ (𝟙 _) (𝟙 _) (by simp [hc₂]) (by simp)) :
    ∃ (U : BigFppfOver B integerBase hZ) (j : U ⟶ S),
      _root_.AlgebraicGeometry.IsOpenImmersion ((𝒯).map j) ∧
      s ∈ Set.range ((𝒯).map j) ∧
      ∃ (ψ : pullback g₁ (yoneda.map j) ≅ pullback g₂ (yoneda.map j))
        (k : pointFieldObject S s ⟶ U),
        ψ.hom ≫ pullback.snd g₂ (yoneda.map j) = pullback.snd g₁ (yoneda.map j) ∧
        pullback.map f (yoneda.map j) g₁ (yoneda.map j) c₁ (𝟙 _) (𝟙 _) (by simp [hc₁])
            (by simp) ≫ ψ.hom =
          pullback.map f (yoneda.map j) g₂ (yoneda.map j) c₂ (𝟙 _) (𝟙 _) (by simp [hc₂])
            (by simp) ∧
        ∃ (hk : k ≫ j = pointFieldMap S s),
          pullback.map g₁ (yoneda.map (pointFieldMap S s)) g₁ (yoneda.map j) (𝟙 _) (yoneda.map k)
              (𝟙 _) (by simp) (by rw [Category.comp_id, ← Functor.map_comp, hk]) ≫ ψ.hom =
            φ.hom ≫ pullback.map g₂ (yoneda.map (pointFieldMap S s)) g₂ (yoneda.map j) (𝟙 _)
              (yoneda.map k) (𝟙 _) (by simp)
              (by rw [Category.comp_id, ← Functor.map_comp, hk]) := by
  obtain ⟨ψst, hψs, hψc, hψf⟩ := exists_iso_stalk_of_iso_fibre S s hX hY₁ hY₂ f g₁ g₂ hfl hpr hfp
    hd hfl₁ hpr₁ hfp₁ hd₁ hfl₂ hpr₂ hfp₂ c₁ c₂ hc₁ hc₂ eX e₁ tX t₁ heX he₁ a₁ ha₁ h0 hR φ hφ hφc
  have hc := isLimitIntegerAffineNhdsCone (hZ := hZ) S s
  have hD : ∀ j, IsAffine ((𝒯).obj ((integerAffineNhdsDiagram (hZ := hZ) S s).obj j)) :=
    fun j => j.unop.2.1
  have P : FinitePresentationSpacesOver.IsFinitePresentationColimit B integerBase hZ
      (integerAffineNhdsDiagram (hZ := hZ) S s) (localSchemeObject S s) (integerAffineNhdsPi S s)
      (fun {_ _} e => (integerAffineNhdsCone (hZ := hZ) S s).w e) :=
    isFinitePresentationColimit_of_isLimit_of_isAffine hD hc
  obtain ⟨i₀⟩ : Nonempty (Scheme.AffineNhds ((𝒯).obj S) s) := inferInstance
  have hfac₀ : yoneda.map (integerAffineNhdsPi S s (op i₀)) ≫
      yoneda.map (integerAffineNhdsMap S s (op i₀)) = yoneda.map (localSchemeMap S s) := by
    rw [← Functor.map_comp, integerAffineNhdsPi_integerAffineNhdsMap]
  have sqX := isPullback_lift_of_isPullback_of_fac B integerBase hZ
    (IsPullback.of_hasPullback f (yoneda.map (localSchemeMap S s))) _ _ hfac₀
  have sq₁ := isPullback_lift_of_isPullback_of_fac B integerBase hZ
    (IsPullback.of_hasPullback g₁ (yoneda.map (localSchemeMap S s))) _ _ hfac₀
  have sq₂ := isPullback_lift_of_isPullback_of_fac B integerBase hZ
    (IsPullback.of_hasPullback g₂ (yoneda.map (localSchemeMap S s))) _ _ hfac₀
  have hcq : ∀ {Y : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S} (c : X ⟶ Y)
      (hc : c ≫ g = f),
      pullback.map f (yoneda.map (localSchemeMap S s)) g (yoneda.map (localSchemeMap S s)) c
          (𝟙 _) (𝟙 _) (by simp [hc]) (by simp) ≫
        pullback.lift (pullback.fst g (yoneda.map (localSchemeMap S s)))
          (pullback.snd g (yoneda.map (localSchemeMap S s)) ≫
            yoneda.map (integerAffineNhdsPi S s (op i₀)))
          (by rw [Category.assoc, hfac₀, pullback.condition]) =
      pullback.lift (pullback.fst f (yoneda.map (localSchemeMap S s)))
          (pullback.snd f (yoneda.map (localSchemeMap S s)) ≫
            yoneda.map (integerAffineNhdsPi S s (op i₀)))
          (by rw [Category.assoc, hfac₀, pullback.condition]) ≫
        pullback.map f (yoneda.map (integerAffineNhdsMap S s (op i₀))) g
          (yoneda.map (integerAffineNhdsMap S s (op i₀))) c (𝟙 _) (𝟙 _) (by simp [hc])
          (by simp) := by
    intro Y g c hc
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  obtain ⟨j, e, Xj, Y₁j, Y₂j, fXj, g₁j, g₂j, rX, r₁, r₂, c₁j, c₂j, q₁j, q₂j, ψj, sqrX, sqr₁,
      sqr₂, hcj₁, hcj₂, hcr₁, hcr₂, hψjg, hψjc, hq₁r, hq₂r, hq₁g, hq₂g, hψq⟩ :=
    exists_iso_stage_of_iso P (op i₀) (isAlgebraicSpace_pullback_yoneda _ f hX)
      (isAlgebraicSpace_pullback_yoneda _ g₁ hY₁) (isAlgebraicSpace_pullback_yoneda _ g₂ hY₂)
      (isFinitePresentation_snd_pullback_yoneda _ hX hfp)
      (isFinitePresentation_snd_pullback_yoneda _ hY₁ hfp₁)
      (isFinitePresentation_snd_pullback_yoneda _ hY₂ hfp₂)
      sqX sq₁ sq₂ _ _ (by simp) (by simp) _ _ (by simp) (by simp) (hcq c₁ hc₁)
      (hcq c₂ hc₂) ψst
      hψs hψc
  have hjj := integerAffineNhdsDiagram_map_integerAffineNhdsMap (hZ := hZ) S s e
  have paste : ∀ {Y Yj : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S}
      {gj : Yj ⟶ yoneda.obj ((integerAffineNhdsDiagram (hZ := hZ) S s).obj j)}
      {r : Yj ⟶ pullback g (yoneda.map (integerAffineNhdsMap S s (op i₀)))}
      (_ : IsPullback r gj (pullback.snd g (yoneda.map (integerAffineNhdsMap S s (op i₀))))
        (yoneda.map ((integerAffineNhdsDiagram (hZ := hZ) S s).map e))),
      IsPullback (r ≫ pullback.fst g (yoneda.map (integerAffineNhdsMap S s (op i₀)))) gj g
        (yoneda.map (integerAffineNhdsMap S s j)) := by
    intro Y Yj g gj r sqr
    rw [← hjj, Functor.map_comp]
    exact sqr.paste_horiz (IsPullback.of_hasPullback g _)
  have hk : (localSchemeClosedPoint S s ≫ integerAffineNhdsPi S s j) ≫ integerAffineNhdsMap S s j =
      pointFieldMap S s := by
    rw [Category.assoc, integerAffineNhdsPi_integerAffineNhdsMap,
      localSchemeClosedPoint_localSchemeMap]
  have hcp : ∀ {Y Yj : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S}
      {r : Yj ⟶ pullback g (yoneda.map (integerAffineNhdsMap S s (op i₀)))} (c : X ⟶ Y)
      (hc : c ≫ g = f) (cj : Xj ⟶ Yj)
      (_ : cj ≫ r = rX ≫ pullback.map f (yoneda.map (integerAffineNhdsMap S s (op i₀))) g
        (yoneda.map (integerAffineNhdsMap S s (op i₀))) c (𝟙 _) (𝟙 _) (by simp [hc]) (by simp)),
      cj ≫ r ≫ pullback.fst g (yoneda.map (integerAffineNhdsMap S s (op i₀))) =
        (rX ≫ pullback.fst f (yoneda.map (integerAffineNhdsMap S s (op i₀)))) ≫ c := by
    intro Y Yj g r c hc cj hcr
    rw [← Category.assoc, hcr]
    simp only [Category.assoc, pullback.lift_fst]
  have hmp : ∀ {Y Yj : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S}
      {r : Yj ⟶ pullback g (yoneda.map (integerAffineNhdsMap S s (op i₀)))}
      (q : pullback g (yoneda.map (localSchemeMap S s)) ⟶ Yj)
      (_ : q ≫ r = pullback.lift (pullback.fst g (yoneda.map (localSchemeMap S s)))
        (pullback.snd g (yoneda.map (localSchemeMap S s)) ≫
          yoneda.map (integerAffineNhdsPi S s (op i₀)))
        (by rw [Category.assoc, hfac₀, pullback.condition])),
      (pullback.map g (yoneda.map (pointFieldMap S s)) g (yoneda.map (localSchemeMap S s)) (𝟙 _)
          (yoneda.map (localSchemeClosedPoint S s)) (𝟙 _) (by simp)
          (by rw [Category.comp_id, ← Functor.map_comp, localSchemeClosedPoint_localSchemeMap]) ≫
          q) ≫ r ≫ pullback.fst g (yoneda.map (integerAffineNhdsMap S s (op i₀))) =
        pullback.fst _ _ := by
    intro Y Yj g r q hqr
    rw [Category.assoc, reassoc_of% hqr]
    simp only [pullback.lift_fst, Category.comp_id]
  have hmg : ∀ {Y Yj : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {g : Y ⟶ yoneda.obj S}
      {gj : Yj ⟶ yoneda.obj ((integerAffineNhdsDiagram (hZ := hZ) S s).obj j)}
      (q : pullback g (yoneda.map (localSchemeMap S s)) ⟶ Yj)
      (_ : q ≫ gj =
        pullback.snd g (yoneda.map (localSchemeMap S s)) ≫ yoneda.map (integerAffineNhdsPi S s j)),
      (pullback.map g (yoneda.map (pointFieldMap S s)) g (yoneda.map (localSchemeMap S s)) (𝟙 _)
          (yoneda.map (localSchemeClosedPoint S s)) (𝟙 _) (by simp)
          (by rw [Category.comp_id, ← Functor.map_comp, localSchemeClosedPoint_localSchemeMap]) ≫
          q) ≫ gj =
        pullback.snd _ _ ≫ yoneda.map (localSchemeClosedPoint S s ≫ integerAffineNhdsPi S s j) := by
    intro Y Yj g gj q hqg
    rw [Category.assoc, hqg]
    simp only [pullback.lift_snd_assoc, Functor.map_comp, Category.assoc]
  obtain ⟨ψ, h1, h2, h3⟩ := exists_iso_pullback_of_isPullback_models (integerAffineNhdsMap S s j)
    (pointFieldMap S s) _ hk c₁ c₂ hc₁ hc₂ φ (paste sqrX) (paste sqr₁) (paste sqr₂) c₁j c₂j hcj₁
    hcj₂ (hcp c₁ hc₁ c₁j hcr₁) (hcp c₂ hc₂ c₂j hcr₂) ψj hψjg hψjc _ _ (hmp q₁j hq₁r)
    (hmp q₂j hq₂r) (hmg q₁j hq₁g) (hmg q₂j hq₂g)
    (by rw [Category.assoc, ← hψq, reassoc_of% hψf])
  refine ⟨_, integerAffineNhdsMap S s j, ?_, ?_, ψ, _, h1, h2, hk, h3⟩
  · change _root_.AlgebraicGeometry.IsOpenImmersion (Scheme.Opens.ι j.unop.opens)
    infer_instance
  · change s ∈ Set.range (Scheme.Opens.ι j.unop.opens)
    rw [Scheme.Opens.range_ι]
    exact j.unop.2.2

end Integers

end AlgebraicGeometry.Space

end
