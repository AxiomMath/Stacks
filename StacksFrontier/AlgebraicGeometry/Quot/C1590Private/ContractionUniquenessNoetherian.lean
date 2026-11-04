module

public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.ContractionUniquenessNoetherianLocal
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Preimage
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FlatNeighbourhoodOfSpecialFibre

/-!
# Uniqueness of contractions near a point of a locally Noetherian base

Let `S` be a locally Noetherian scheme and `s ∈ S`, let `X`, `Y₁`, `Y₂` be proper flat schemes of
finite presentation over `S` and let `cᵢ : X ⟶ Yᵢ` be morphisms over `S`. Suppose the fibres
`Y₁,ₛ`, `Y₂,ₛ` over `Spec κ(s)` are identified compatibly with `c₁,ₛ`, `c₂,ₛ`, that the fibres of
`c₁,ₛ` have dimension at most one, and that `𝒪_{Y₁,ₛ} ≅ c₁,ₛ,*𝒪_{Xₛ}` and `R¹c₁,ₛ,*𝒪_{Xₛ} = 0`.
Then there are an open neighbourhood `U` of `s` and an isomorphism `Y₁|_U ≅ Y₂|_U` over `U`
compatible with `c₁` and `c₂`.

This is the reduction of [Stacks, Tag 0E89] from an open neighbourhood to the local ring: over
`Spec 𝒪_{S,s}` the Noetherian local case
(`AlgebraicGeometry.C1590Private.exists_iso_comp_eq_of_specialFibre_of_isNoetherianLocal`) gives
the isomorphism, and since `Spec 𝒪_{S,s}` is the limit of the affine open neighbourhoods of `s`
([Stacks, Tag 01YX]), the isomorphism, its inverse and the identities they satisfy spread out to
some neighbourhood ([Stacks, Tag 01ZC]).

## Main results

* `AlgebraicGeometry.C1590Private.exists_preimage_hom_of_stalk`,
  `AlgebraicGeometry.C1590Private.exists_le_eq_of_stalk`: spreading out of morphisms from
  `Y ×_S Spec 𝒪_{S,s}`, and of equalities between them.
* `AlgebraicGeometry.C1590Private.exists_open_iso_of_residueFibre_of_isLocallyNoetherian`: the
  statement above.

## References

* [Stacks Project, Tag 0E89](https://stacks.math.columbia.edu/tag/0E89)
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
* [Stacks Project, Tag 01YX](https://stacks.math.columbia.edu/tag/01YX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1590Private

/-! ### Spreading out from the local scheme at a point -/

section Spread

variable {S Y Z : Scheme.{u}} (f : Y ⟶ S) (g : Z ⟶ S) (s : S)

/-- The open immersions `f⁻¹(W) ⟶ Y ⟶ S` of the preimages of the affine neighbourhoods of `s`, as a
natural transformation to the constant diagram `S`. -/
def preimageAffineOpenNhdsToBase :
    preimageAffineOpenNhdsDiagram f s ⟶ (Functor.const (AffineOpenNhds S s)).obj S where
  app W := (f ⁻¹ᵁ W.opens).ι ≫ f
  naturality {_ _} e :=
    (preimageAffineOpenNhdsDiagram_map_ι_assoc f s e f).trans (Category.comp_id _).symm

/-- **A morphism out of `Y ×_S Spec 𝒪_{S,s}` spreads out** to the preimage of an affine
neighbourhood of `s`, when `Y ⟶ S` is quasi-compact and quasi-separated and the target is locally
of finite presentation over `S` ([Stacks, Tag 01ZC]). -/
theorem exists_preimage_hom_of_stalk [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation g] (a : pullback f (S.fromSpecStalk s) ⟶ Z)
    (ha : a ≫ g = pullback.fst f (S.fromSpecStalk s) ≫ f) :
    ∃ (W : AffineOpenNhds S s) (b : (f ⁻¹ᵁ W.opens).toScheme ⟶ Z),
      preimageSpecStalkLeg f s W ≫ b = a ∧ b ≫ g = (f ⁻¹ᵁ W.opens).ι ≫ f :=
  Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (preimageAffineOpenNhdsDiagram f s) (preimageAffineOpenNhdsToBase f s) g
    (preimageSpecStalkCone f s) (isLimitPreimageSpecStalkCone f s) a (by
      ext W
      exact (preimageSpecStalkLeg_ι_assoc f s W f).trans ha.symm)

/-- **Two morphisms out of `f⁻¹(W)` agreeing on `Y ×_S Spec 𝒪_{S,s}` agree on the preimage of a
smaller affine neighbourhood**, when `Y ⟶ S` is quasi-compact and the target is locally of finite
type over `S` ([Stacks, Tag 01ZC]). -/
theorem exists_le_eq_of_stalk [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType g]
    {W : AffineOpenNhds S s} (b b' : (f ⁻¹ᵁ W.opens).toScheme ⟶ Z)
    (hb : b ≫ g = (f ⁻¹ᵁ W.opens).ι ≫ f) (hb' : b' ≫ g = (f ⁻¹ᵁ W.opens).ι ≫ f)
    (h : preimageSpecStalkLeg f s W ≫ b = preimageSpecStalkLeg f s W ≫ b') :
    ∃ (W' : AffineOpenNhds S s) (hW' : W'.opens ≤ W.opens),
      Y.homOfLE (f.preimage_mono hW') ≫ b = Y.homOfLE (f.preimage_mono hW') ≫ b' := by
  obtain ⟨W', e, he⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (preimageAffineOpenNhdsDiagram f s) (preimageAffineOpenNhdsToBase f s) g
    (preimageSpecStalkCone f s) (isLimitPreimageSpecStalkCone f s) b b' hb.symm hb'.symm h
  exact ⟨W', AffineOpenNhds.opens_le e, he⟩

/-- The legs of the cone `Y ×_S Spec 𝒪_{S,s} ⟶ f⁻¹(W)` are compatible with the inclusions. -/
@[reassoc (attr := simp)]
theorem preimageSpecStalkLeg_homOfLE {W W' : AffineOpenNhds S s} (h : W'.opens ≤ W.opens) :
    preimageSpecStalkLeg f s W' ≫ Y.homOfLE (f.preimage_mono h) = preimageSpecStalkLeg f s W := by
  rw [← cancel_mono (f ⁻¹ᵁ W.opens).ι, Category.assoc, Scheme.homOfLE_ι, preimageSpecStalkLeg_ι,
    preimageSpecStalkLeg_ι]

end Spread

/-! ### Morphisms into preimages of opens -/

section ToPreimage

variable {S T Y : Scheme.{u}} (f : Y ⟶ S) (U : S.Opens)

/-- A morphism into `Y` whose composite with `f : Y ⟶ S` lands in `U` factors through `f⁻¹(U)`. -/
def toPreimage (g : T ⟶ Y) (hg : ∀ x, f (g x) ∈ U) : T ⟶ (f ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ U).ι g (by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hg x)

/-- The factorisation `toPreimage f U g hg` composed with the inclusion `f⁻¹(U) ⟶ Y` is `g`. -/
@[reassoc (attr := simp)]
theorem toPreimage_ι (g : T ⟶ Y) (hg : ∀ x, f (g x) ∈ U) : toPreimage f U g hg ≫ (f ⁻¹ᵁ U).ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The points of a morphism over `S` from `f'⁻¹(U)` land in the preimage of `U`. -/
theorem mem_of_comp_eq {Y' : Scheme.{u}} {f' : Y' ⟶ S} (g : (f' ⁻¹ᵁ U).toScheme ⟶ Y)
    (hg : g ≫ f = (f' ⁻¹ᵁ U).ι ≫ f') (x : (f' ⁻¹ᵁ U).toScheme) : f (g x) ∈ U := by
  rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]
  exact x.2

end ToPreimage

/-! ### Spreading out an isomorphism from the local scheme at a point -/

section SpreadIso

variable {S : Scheme.{u}} (s : S)

/-- A morphism `f⁻¹(U₀) ⟶ Z'` over `S` restricts along `U ≤ U₀` to a morphism
`f⁻¹(U) ⟶ f'⁻¹(U)` over `S`. -/
private theorem exists_comp_ι_eq_homOfLE_comp {Z Z' : Scheme.{u}} (f : Z ⟶ S) (f' : Z' ⟶ S)
    {U U₀ : S.Opens} (g : U ≤ U₀) (b : (f ⁻¹ᵁ U₀).toScheme ⟶ Z') (hb : b ≫ f' = (f ⁻¹ᵁ U₀).ι ≫ f) :
    ∃ Ψ : (f ⁻¹ᵁ U).toScheme ⟶ (f' ⁻¹ᵁ U).toScheme,
      Ψ ≫ (f' ⁻¹ᵁ U).ι = Z.homOfLE (f.preimage_mono g) ≫ b ∧
      Ψ ≫ (f' ⁻¹ᵁ U).ι ≫ f' = (f ⁻¹ᵁ U).ι ≫ f := by
  have h : (Z.homOfLE (f.preimage_mono g) ≫ b) ≫ f' = (f ⁻¹ᵁ U).ι ≫ f := by
    rw [Category.assoc, hb, Scheme.homOfLE_ι_assoc]
  exact ⟨toPreimage f' U _ (mem_of_comp_eq f' U _ h), toPreimage_ι .., by
    rw [toPreimage_ι_assoc, h]⟩

/-- An equality of morphisms out of `f⁻¹(W)` restricts to the preimage of any smaller open. -/
private theorem homOfLE_comp_eq_of_le {Z T : Scheme.{u}} (f : Z ⟶ S) {U V W : S.Opens} (g : U ≤ V)
    (d : V ≤ W) {b b' : (f ⁻¹ᵁ W).toScheme ⟶ T}
    (h : Z.homOfLE (f.preimage_mono d) ≫ b = Z.homOfLE (f.preimage_mono d) ≫ b') :
    Z.homOfLE (f.preimage_mono (g.trans d)) ≫ b = Z.homOfLE (f.preimage_mono (g.trans d)) ≫ b' := by
  rw [← Scheme.homOfLE_homOfLE Z (f.preimage_mono g) (f.preimage_mono d), Category.assoc, h,
    Category.assoc]

/-- **An isomorphism `Y₁ ×_S Spec 𝒪_{S,s} ≅ Y₂ ×_S Spec 𝒪_{S,s}` over `Spec 𝒪_{S,s}` spreads out**
to morphisms between the preimages of an affine neighbourhood of `s`, over `S`, restricting to the
isomorphism and its inverse ([Stacks, Tag 01ZC]). -/
theorem exists_preimage_homs_of_iso_stalk {Y₁ Y₂ : Scheme.{u}} (fY₁ : Y₁ ⟶ S) (fY₂ : Y₂ ⟶ S)
    [QuasiCompact fY₁] [QuasiSeparated fY₁] [LocallyOfFinitePresentation fY₁]
    [QuasiCompact fY₂] [QuasiSeparated fY₂] [LocallyOfFinitePresentation fY₂]
    (ψ : pullback fY₁ (S.fromSpecStalk s) ≅ pullback fY₂ (S.fromSpecStalk s))
    (hψ : ψ.hom ≫ pullback.snd _ _ = pullback.snd _ _) :
    ∃ (W : AffineOpenNhds S s) (H₁ : (fY₁ ⁻¹ᵁ W.opens).toScheme ⟶ (fY₂ ⁻¹ᵁ W.opens).toScheme)
      (H₂ : (fY₂ ⁻¹ᵁ W.opens).toScheme ⟶ (fY₁ ⁻¹ᵁ W.opens).toScheme),
      H₁ ≫ (fY₂ ⁻¹ᵁ W.opens).ι ≫ fY₂ = (fY₁ ⁻¹ᵁ W.opens).ι ≫ fY₁ ∧
      H₂ ≫ (fY₁ ⁻¹ᵁ W.opens).ι ≫ fY₁ = (fY₂ ⁻¹ᵁ W.opens).ι ≫ fY₂ ∧
      preimageSpecStalkLeg fY₁ s W ≫ H₁ = ψ.hom ≫ preimageSpecStalkLeg fY₂ s W ∧
      preimageSpecStalkLeg fY₂ s W ≫ H₂ = ψ.inv ≫ preimageSpecStalkLeg fY₁ s W := by
  have hψinv : ψ.inv ≫ pullback.snd fY₁ (S.fromSpecStalk s) =
      pullback.snd fY₂ (S.fromSpecStalk s) := by
    rw [← hψ, ψ.inv_hom_id_assoc]
  obtain ⟨W₁, b₁, hb₁, hb₁g⟩ := exists_preimage_hom_of_stalk fY₁ fY₂ s
    (ψ.hom ≫ pullback.fst fY₂ (S.fromSpecStalk s)) (by
      rw [Category.assoc, pullback.condition, reassoc_of% hψ, pullback.condition])
  obtain ⟨W₂, b₂, hb₂, hb₂g⟩ := exists_preimage_hom_of_stalk fY₂ fY₁ s
    (ψ.inv ≫ pullback.fst fY₁ (S.fromSpecStalk s)) (by
      rw [Category.assoc, pullback.condition, reassoc_of% hψinv, pullback.condition])
  set W₀ := IsCofiltered.min W₁ W₂
  set U₀ := W₀.opens
  have e₁ : U₀ ≤ W₁.opens := AffineOpenNhds.opens_le (IsCofiltered.minToLeft W₁ W₂)
  have e₂ : U₀ ≤ W₂.opens := AffineOpenNhds.opens_le (IsCofiltered.minToRight W₁ W₂)
  obtain ⟨H₁, hH₁, hH₁g⟩ := exists_comp_ι_eq_homOfLE_comp fY₁ fY₂ e₁ b₁ hb₁g
  obtain ⟨H₂, hH₂, hH₂g⟩ := exists_comp_ι_eq_homOfLE_comp fY₂ fY₁ e₂ b₂ hb₂g
  refine ⟨W₀, H₁, H₂, hH₁g, hH₂g, ?_, ?_⟩
  · rw [← cancel_mono (fY₂ ⁻¹ᵁ U₀).ι, Category.assoc, Category.assoc, hH₁,
      preimageSpecStalkLeg_homOfLE_assoc fY₁ s e₁, hb₁, preimageSpecStalkLeg_ι]
  · rw [← cancel_mono (fY₁ ⁻¹ᵁ U₀).ι, Category.assoc, Category.assoc, hH₂,
      preimageSpecStalkLeg_homOfLE_assoc fY₂ s e₂, hb₂, preimageSpecStalkLeg_ι]

/-- **Morphisms between the preimages of `U₀` which are mutually inverse on the preimages of
`U ≤ U₀` restrict to an isomorphism over `U`**, compatible with `c₁` and `c₂` when `a₀ ≫ H₁`
restricts to `c₂`. -/
theorem exists_iso_preimage_of_homOfLE_comp_eq {X Y₁ Y₂ : Scheme.{u}} {fX : X ⟶ S}
    {fY₁ : Y₁ ⟶ S} {fY₂ : Y₂ ⟶ S} {c₁ : X ⟶ Y₁} {c₂ : X ⟶ Y₂} {U U₀ : S.Opens} (g : U ≤ U₀)
    (H₁ : (fY₁ ⁻¹ᵁ U₀).toScheme ⟶ (fY₂ ⁻¹ᵁ U₀).toScheme)
    (H₂ : (fY₂ ⁻¹ᵁ U₀).toScheme ⟶ (fY₁ ⁻¹ᵁ U₀).toScheme)
    (hH₁ : H₁ ≫ (fY₂ ⁻¹ᵁ U₀).ι ≫ fY₂ = (fY₁ ⁻¹ᵁ U₀).ι ≫ fY₁)
    (hH₂ : H₂ ≫ (fY₁ ⁻¹ᵁ U₀).ι ≫ fY₁ = (fY₂ ⁻¹ᵁ U₀).ι ≫ fY₂)
    (h₁ : Y₁.homOfLE (fY₁.preimage_mono g) ≫ H₁ ≫ H₂ ≫ (fY₁ ⁻¹ᵁ U₀).ι =
      Y₁.homOfLE (fY₁.preimage_mono g) ≫ (fY₁ ⁻¹ᵁ U₀).ι)
    (h₂ : Y₂.homOfLE (fY₂.preimage_mono g) ≫ H₂ ≫ H₁ ≫ (fY₂ ⁻¹ᵁ U₀).ι =
      Y₂.homOfLE (fY₂.preimage_mono g) ≫ (fY₂ ⁻¹ᵁ U₀).ι)
    (a₀ : (fX ⁻¹ᵁ U₀).toScheme ⟶ (fY₁ ⁻¹ᵁ U₀).toScheme)
    (ha₀ : a₀ ≫ (fY₁ ⁻¹ᵁ U₀).ι = (fX ⁻¹ᵁ U₀).ι ≫ c₁)
    (h₃ : X.homOfLE (fX.preimage_mono g) ≫ a₀ ≫ H₁ ≫ (fY₂ ⁻¹ᵁ U₀).ι =
      X.homOfLE (fX.preimage_mono g) ≫ (fX ⁻¹ᵁ U₀).ι ≫ c₂) :
    ∃ ψ : (fY₁ ⁻¹ᵁ U).toScheme ≅ (fY₂ ⁻¹ᵁ U).toScheme,
      ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι ≫ fY₂ = (fY₁ ⁻¹ᵁ U).ι ≫ fY₁ ∧
      ∀ a : (fX ⁻¹ᵁ U).toScheme ⟶ (fY₁ ⁻¹ᵁ U).toScheme,
        a ≫ (fY₁ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₁ →
          a ≫ ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₂ := by
  set r₁ := Y₁.homOfLE (fY₁.preimage_mono g)
  set r₂ := Y₂.homOfLE (fY₂.preimage_mono g)
  set rX := X.homOfLE (fX.preimage_mono g)
  have hr₁ : r₁ ≫ (fY₁ ⁻¹ᵁ U₀).ι = (fY₁ ⁻¹ᵁ U).ι := Scheme.homOfLE_ι _ _
  have hr₂ : r₂ ≫ (fY₂ ⁻¹ᵁ U₀).ι = (fY₂ ⁻¹ᵁ U).ι := Scheme.homOfLE_ι _ _
  have hrX : rX ≫ (fX ⁻¹ᵁ U₀).ι = (fX ⁻¹ᵁ U).ι := Scheme.homOfLE_ι _ _
  obtain ⟨Ψ₁, hΨ₁, hΨ₁g⟩ := exists_comp_ι_eq_homOfLE_comp fY₁ fY₂ g (H₁ ≫ (fY₂ ⁻¹ᵁ U₀).ι)
    (by rwa [Category.assoc])
  obtain ⟨Ψ₂, hΨ₂, hΨ₂g⟩ := exists_comp_ι_eq_homOfLE_comp fY₂ fY₁ g (H₂ ≫ (fY₁ ⁻¹ᵁ U₀).ι)
    (by rwa [Category.assoc])
  have hΨ₁r : Ψ₁ ≫ r₂ = r₁ ≫ H₁ := by
    rw [← cancel_mono (fY₂ ⁻¹ᵁ U₀).ι, Category.assoc, hr₂, hΨ₁, Category.assoc]
  have hΨ₂r : Ψ₂ ≫ r₁ = r₂ ≫ H₂ := by
    rw [← cancel_mono (fY₁ ⁻¹ᵁ U₀).ι, Category.assoc, hr₁, hΨ₂, Category.assoc]
  refine ⟨⟨Ψ₁, Ψ₂, ?_, ?_⟩, ?_, fun a ha => ?_⟩
  · rw [← cancel_mono (fY₁ ⁻¹ᵁ U).ι, Category.assoc, hΨ₂, ← hr₁, reassoc_of% hΨ₁r,
      Category.id_comp, h₁]
  · rw [← cancel_mono (fY₂ ⁻¹ᵁ U).ι, Category.assoc, hΨ₁, ← hr₂, reassoc_of% hΨ₂r,
      Category.id_comp, h₂]
  · exact hΨ₁g
  · have har : a ≫ r₁ = rX ≫ a₀ := by
      rw [← cancel_mono (fY₁ ⁻¹ᵁ U₀).ι, Category.assoc, hr₁, ha, Category.assoc, ha₀,
        reassoc_of% hrX]
    rw [hΨ₁, reassoc_of% har, h₃, reassoc_of% hrX]

/-- **An isomorphism of base changes to `Spec 𝒪_{S,s}` compatible with `c₁` and `c₂` spreads out**
to an isomorphism `Y₁|_U ≅ Y₂|_U` over an open `U ∋ s`, compatible with `c₁` and `c₂`
([Stacks, Tag 01ZC]). -/
theorem exists_open_iso_of_iso_pullback_fromSpecStalk {X Y₁ Y₂ : Scheme.{u}} (fX : X ⟶ S)
    (fY₁ : Y₁ ⟶ S) (fY₂ : Y₂ ⟶ S) [QuasiCompact fX] [QuasiSeparated fX] [QuasiCompact fY₁]
    [QuasiSeparated fY₁] [LocallyOfFinitePresentation fY₁] [QuasiCompact fY₂]
    [QuasiSeparated fY₂] [LocallyOfFinitePresentation fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (ψ : pullback fY₁ (S.fromSpecStalk s) ≅ pullback fY₂ (S.fromSpecStalk s))
    (hψ : ψ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hcψ : fibreHom (S.fromSpecStalk s) fX fY₁ c₁ hc₁ ≫ ψ.hom =
      fibreHom (S.fromSpecStalk s) fX fY₂ c₂ hc₂) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ ψ : (fY₁ ⁻¹ᵁ U).toScheme ≅ (fY₂ ⁻¹ᵁ U).toScheme,
      ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι ≫ fY₂ = (fY₁ ⁻¹ᵁ U).ι ≫ fY₁ ∧
      ∀ a : (fX ⁻¹ᵁ U).toScheme ⟶ (fY₁ ⁻¹ᵁ U).toScheme,
        a ≫ (fY₁ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₁ →
          a ≫ ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₂ := by
  obtain ⟨W₀, H₁, H₂, hH₁g, hH₂g, hL₁, hL₂⟩ := exists_preimage_homs_of_iso_stalk s fY₁ fY₂ ψ hψ
  -- the identities, and the compatibility with `c₁` and `c₂`, hold near `s`
  obtain ⟨V₁, d₁, hd₁⟩ := exists_le_eq_of_stalk fY₁ fY₁ s (W := W₀)
    (H₁ ≫ H₂ ≫ (fY₁ ⁻¹ᵁ W₀.opens).ι) (fY₁ ⁻¹ᵁ W₀.opens).ι
    (by rw [Category.assoc, Category.assoc, hH₂g, hH₁g]) rfl
    (by rw [reassoc_of% hL₁, reassoc_of% hL₂, ψ.hom_inv_id_assoc])
  obtain ⟨V₂, d₂, hd₂⟩ := exists_le_eq_of_stalk fY₂ fY₂ s (W := W₀)
    (H₂ ≫ H₁ ≫ (fY₂ ⁻¹ᵁ W₀.opens).ι) (fY₂ ⁻¹ᵁ W₀.opens).ι
    (by rw [Category.assoc, Category.assoc, hH₁g, hH₂g]) rfl
    (by rw [reassoc_of% hL₂, reassoc_of% hL₁, ψ.inv_hom_id_assoc])
  set a₀ := toPreimage fY₁ W₀.opens ((fX ⁻¹ᵁ W₀.opens).ι ≫ c₁)
    (mem_of_comp_eq fY₁ W₀.opens _ (by rw [Category.assoc, hc₁]))
  have hLX : preimageSpecStalkLeg fX s W₀ ≫ a₀ =
      fibreHom (S.fromSpecStalk s) fX fY₁ c₁ hc₁ ≫ preimageSpecStalkLeg fY₁ s W₀ := by
    rw [← cancel_mono (fY₁ ⁻¹ᵁ W₀.opens).ι, Category.assoc, Category.assoc, toPreimage_ι,
      preimageSpecStalkLeg_ι, preimageSpecStalkLeg_ι_assoc]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨V₃, d₃, hd₃⟩ := exists_le_eq_of_stalk fX fY₂ s (W := W₀)
    (a₀ ≫ H₁ ≫ (fY₂ ⁻¹ᵁ W₀.opens).ι) ((fX ⁻¹ᵁ W₀.opens).ι ≫ c₂)
    (by rw [Category.assoc, Category.assoc, hH₁g, toPreimage_ι_assoc, Category.assoc, hc₁])
    (by rw [Category.assoc, hc₂])
    (by
      rw [reassoc_of% hLX, reassoc_of% hL₁, preimageSpecStalkLeg_ι, reassoc_of% hcψ,
        preimageSpecStalkLeg_ι_assoc]
      exact pullback.lift_fst _ _ _)
  -- the final neighbourhood
  set V₁₂ := IsCofiltered.min V₁ V₂
  set W := IsCofiltered.min V₁₂ V₃
  have g₁₂ : W.opens ≤ V₁₂.opens := AffineOpenNhds.opens_le (IsCofiltered.minToLeft V₁₂ V₃)
  have g₁ := g₁₂.trans (AffineOpenNhds.opens_le (IsCofiltered.minToLeft V₁ V₂))
  have g₂ := g₁₂.trans (AffineOpenNhds.opens_le (IsCofiltered.minToRight V₁ V₂))
  have g₃ : W.opens ≤ V₃.opens := AffineOpenNhds.opens_le (IsCofiltered.minToRight V₁₂ V₃)
  refine ⟨W.opens, W.mem_opens, exists_iso_preimage_of_homOfLE_comp_eq (g₁.trans d₁) H₁ H₂
    hH₁g hH₂g ?_ ?_ a₀ (toPreimage_ι _ _ _ _) ?_⟩
  · exact homOfLE_comp_eq_of_le fY₁ g₁ d₁ hd₁
  · exact homOfLE_comp_eq_of_le fY₂ g₂ d₂ hd₂
  · exact homOfLE_comp_eq_of_le fX g₃ d₃ hd₃

end SpreadIso

/-! ### Base change of the fibre data -/

section BaseChange

variable {S T T₀ K X Y₁ Y₂ : Scheme.{u}} {j : T ⟶ S} {t : K ⟶ S} {t' : T₀ ⟶ T} {τ : T₀ ⟶ K}

/-- **The fibre data pass to a flat change of point.** Let `t' : T₀ ⟶ T` lie over
`t : K ⟶ S` along `j : T ⟶ S` through a flat `τ : T₀ ⟶ K`. An isomorphism `Y₁,ₜ ≅ Y₂,ₜ` over `K`
compatible with `c₁,ₜ` and `c₂,ₜ`, together with the conditions on `c₁,ₜ`, gives the same data
for the base changes of `X`, `Y₁`, `Y₂` along `j` at `t'`. -/
theorem fibreData_pullback_of_comp_eq (hst : t' ≫ j = τ ≫ t) [Flat τ]
    (fX : X ⟶ S) (fY₁ : Y₁ ⟶ S) (fY₂ : Y₂ ⟶ S) (c₁ : X ⟶ Y₁) [IsProper c₁]
    (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (φ : pullback fY₁ t ≅ pullback fY₂ t) (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : fibreHom t fX fY₁ c₁ hc₁ ≫ φ.hom = fibreHom t fX fY₂ c₂ hc₂)
    (hdim : ∀ y, topologicalKrullDim ((fibreHom t fX fY₁ c₁ hc₁).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit (fibreHom t fX fY₁ c₁ hc₁)))
    (hR : IsZero (((Scheme.Modules.pushforward (fibreHom t fX fY₁ c₁ hc₁)).rightDerived 1).obj
      (SheafOfModules.unit (pullback fX t).ringCatSheaf))) :
    ∃ φ' : pullback (pullback.snd fY₁ j) t' ≅ pullback (pullback.snd fY₂ j) t',
      φ'.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      fibreHom t' (pullback.snd fX j) (pullback.snd fY₁ j) (fibreHom j fX fY₁ c₁ hc₁)
          (fibreHom_snd j fX fY₁ c₁ hc₁) ≫ φ'.hom =
        fibreHom t' (pullback.snd fX j) (pullback.snd fY₂ j) (fibreHom j fX fY₂ c₂ hc₂)
          (fibreHom_snd j fX fY₂ c₂ hc₂) ∧
      (∀ y, topologicalKrullDim ((fibreHom t' (pullback.snd fX j) (pullback.snd fY₁ j)
        (fibreHom j fX fY₁ c₁ hc₁) (fibreHom_snd j fX fY₁ c₁ hc₁)).fiber y) ≤
          ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsIso (Scheme.Modules.unitToPushforwardUnit (fibreHom t' (pullback.snd fX j)
        (pullback.snd fY₁ j) (fibreHom j fX fY₁ c₁ hc₁) (fibreHom_snd j fX fY₁ c₁ hc₁))) ∧
      IsZero (((Scheme.Modules.pushforward (fibreHom t' (pullback.snd fX j)
        (pullback.snd fY₁ j) (fibreHom j fX fY₁ c₁ hc₁)
          (fibreHom_snd j fX fY₁ c₁ hc₁))).rightDerived 1).obj
            (SheafOfModules.unit (pullback (pullback.snd fX j) t').ringCatSheaf)) := by
  have PY₁ := isPullback_fibreMap hst fY₁ (pullback.snd fY₁ j) (pullback.fst fY₁ j)
    pullback.condition.symm (IsPullback.of_hasPullback fY₁ j)
  have PY₂ := isPullback_fibreMap hst fY₂ (pullback.snd fY₂ j) (pullback.fst fY₂ j)
    pullback.condition.symm (IsPullback.of_hasPullback fY₂ j)
  have H₁ := isPullback_fibreHom hst fX fY₁ (pullback.snd fX j) (pullback.snd fY₁ j)
    (pullback.fst fX j) (pullback.fst fY₁ j) pullback.condition.symm pullback.condition.symm
    c₁ hc₁ _ (fibreHom_snd j fX fY₁ c₁ hc₁) (pullback.lift_fst _ _ _)
    (isPullback_pullbackMap_fst j c₁ hc₁)
  have H₂ := isPullback_fibreHom hst fX fY₂ (pullback.snd fX j) (pullback.snd fY₂ j)
    (pullback.fst fX j) (pullback.fst fY₂ j) pullback.condition.symm pullback.condition.symm
    c₂ hc₂ _ (fibreHom_snd j fX fY₂ c₂ hc₂) (pullback.lift_fst _ _ _)
    (isPullback_pullbackMap_fst j c₂ hc₂)
  have : Flat (fibreMap hst fY₁ (pullback.snd fY₁ j) (pullback.fst fY₁ j)
      pullback.condition.symm) :=
    MorphismProperty.of_isPullback PY₁.flip inferInstance
  have : IsProper (fibreHom t fX fY₁ c₁ hc₁) :=
    MorphismProperty.of_isPullback (isPullback_fibreHom_fst _ fX fY₁ c₁ hc₁) inferInstance
  refine ⟨isoOfIsPullback PY₁ PY₂ φ hφ, isoOfIsPullback_hom_snd PY₁ PY₂ φ hφ, ?_,
    fun y => Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_of_isPullback
      H₁ 1 y (hdim _), fibreConditions_of_isPullback H₁ hdim h0 hR⟩
  refine PY₂.hom_ext ?_ ?_
  · rw [Category.assoc, isoOfIsPullback_hom_fst, ← reassoc_of% H₁.w]
    exact (fibreMap hst fX (pullback.snd fX j) (pullback.fst fX j)
      pullback.condition.symm ≫= hφc).trans H₂.w
  · rw [Category.assoc, isoOfIsPullback_hom_snd, fibreHom_snd, fibreHom_snd]

end BaseChange

/-! ### The case of a locally Noetherian base -/

section LocallyNoetherian

variable {S : Scheme.{u}} [IsLocallyNoetherian S] (s : S)

/-- **Uniqueness of contractions near a point of a locally Noetherian base** (the reduction of
[Stacks, Tag 0E89] to the local ring). Let `S` be locally Noetherian, `s ∈ S`, let `X`, `Y₁`, `Y₂`
be proper flat schemes of finite presentation over `S` and `cᵢ : X ⟶ Yᵢ` morphisms over `S`. Let
`φ : Y₁,ₛ ≅ Y₂,ₛ` be an isomorphism of the fibres over `Spec κ(s)` with `c₁,ₛ ≫ φ = c₂,ₛ`. If the
fibres of `c₁,ₛ` have dimension at most one, `𝒪_{Y₁,ₛ} ≅ c₁,ₛ,*𝒪_{Xₛ}` and
`R¹c₁,ₛ,*𝒪_{Xₛ} = 0`, there are an open `U ∋ s` and an isomorphism `ψ : Y₁|_U ≅ Y₂|_U` over `U`
compatible with `c₁` and `c₂`. -/
theorem exists_open_iso_of_residueFibre_of_isLocallyNoetherian {X Y₁ Y₂ : Scheme.{u}}
    (fX : X ⟶ S) (fY₁ : Y₁ ⟶ S) (fY₂ : Y₂ ⟶ S)
    [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX] [IsProper fY₁] [Flat fY₁]
    [LocallyOfFinitePresentation fY₁] [IsProper fY₂] [Flat fY₂] [LocallyOfFinitePresentation fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (φ : pullback fY₁ (S.fromSpecResidueField s) ≅ pullback fY₂ (S.fromSpecResidueField s))
    (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : fibreHom (S.fromSpecResidueField s) fX fY₁ c₁ hc₁ ≫ φ.hom =
      fibreHom (S.fromSpecResidueField s) fX fY₂ c₂ hc₂)
    (hdim : ∀ y, topologicalKrullDim
      ((fibreHom (S.fromSpecResidueField s) fX fY₁ c₁ hc₁).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit
      (fibreHom (S.fromSpecResidueField s) fX fY₁ c₁ hc₁)))
    (hR : IsZero (((Scheme.Modules.pushforward
      (fibreHom (S.fromSpecResidueField s) fX fY₁ c₁ hc₁)).rightDerived 1).obj
        (SheafOfModules.unit (pullback fX (S.fromSpecResidueField s)).ringCatSheaf))) :
    ∃ U : S.Opens, s ∈ U ∧ ∃ ψ : (fY₁ ⁻¹ᵁ U).toScheme ≅ (fY₂ ⁻¹ᵁ U).toScheme,
      ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι ≫ fY₂ = (fY₁ ⁻¹ᵁ U).ι ≫ fY₁ ∧
      ∀ a : (fX ⁻¹ᵁ U).toScheme ⟶ (fY₁ ⁻¹ᵁ U).toScheme,
        a ≫ (fY₁ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₁ →
          a ≫ ψ.hom ≫ (fY₂ ⁻¹ᵁ U).ι = (fX ⁻¹ᵁ U).ι ≫ c₂ := by
  have : IsProper c₁ := by
    subst hc₁
    exact IsProper.of_comp c₁ fY₁
  set j := S.fromSpecStalk s
  -- the base change to `Spec 𝒪_{S,s}`
  set fX' : pullback fX j ⟶ Spec (.of (S.presheaf.stalk s)) := pullback.snd fX j
  set fY₁' : pullback fY₁ j ⟶ Spec (.of (S.presheaf.stalk s)) := pullback.snd fY₁ j
  set fY₂' : pullback fY₂ j ⟶ Spec (.of (S.presheaf.stalk s)) := pullback.snd fY₂ j
  -- the closed point of `Spec 𝒪_{S,s}` is the residue field point of `s`
  have : IsLocalHom (CommRingCat.ofHom
      (IsLocalRing.residue (S.presheaf.stalk s))).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue (S.presheaf.stalk s)))
  obtain ⟨φ₀, hφ₀⟩ := exists_comp_fromSpecResidueField
    (ContractionUniquenessComplete.closedPoint (S.presheaf.stalk s) ≫ j) s
      ((congrArg j.base Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)
  set τ := Spec.map φ₀
  have : Flat τ :=
    (Stacks.AlgebraicGeometry.TopDegreeBaseChange.flat_and_surjective_specMap_of_field φ₀).1
  obtain ⟨φ', hφ', hφc', hdim', h0', hR'⟩ :=
    fibreData_pullback_of_comp_eq hφ₀.symm fX fY₁ fY₂ c₁ hc₁ c₂ hc₂ φ hφ hφc hdim h0 hR
  -- the Noetherian local case
  obtain ⟨ψΛ, hψΛ, hcψΛ⟩ := exists_iso_comp_eq_of_specialFibre_of_isNoetherianLocal fX' fY₁' fY₂'
    (fibreHom j fX fY₁ c₁ hc₁) (fibreHom_snd j fX fY₁ c₁ hc₁) (fibreHom j fX fY₂ c₂ hc₂)
    (fibreHom_snd j fX fY₂ c₂ hc₂) φ' hφ' hφc' hdim' h0' hR'
  exact exists_open_iso_of_iso_pullback_fromSpecStalk s fX fY₁ fY₂ c₁ hc₁ c₂ hc₂ ψΛ hψΛ hcψΛ

end LocallyNoetherian

/-! ### Fibres over a field-valued point -/

section FieldPoint

variable {S : Scheme.{u}}

/-- The base change along `τ` of `c_{t''}` is `c_t`, through the identifications of `X_t` and `Y_t`
with the base changes along `τ` of `X_{t''}` and `Y_{t''}`. -/
theorem pullbackMap_fibreHom_eq_isoPullback {K T X Y : Scheme.{u}} {t'' : K ⟶ S} {t : T ⟶ S}
    {τ : T ⟶ K} {fX : X ⟶ S} {fY : Y ⟶ S} {c : X ⟶ Y} (hc : c ≫ fY = fX)
    {a : pullback fX t ⟶ pullback fX t''} {b : pullback fY t ⟶ pullback fY t''}
    (PX : IsPullback a (pullback.snd fX t) (pullback.snd fX t'') τ)
    (PY : IsPullback b (pullback.snd fY t) (pullback.snd fY t'') τ)
    (w : a ≫ fibreHom t'' fX fY c hc = fibreHom t fX fY c hc ≫ b) :
    pullback.map (pullback.snd fX t'') τ (pullback.snd fY t'') τ (fibreHom t'' fX fY c hc)
      (𝟙 _) (𝟙 _) (by simp) (by simp) =
      PX.isoPullback.inv ≫ fibreHom t fX fY c hc ≫ PY.isoPullback.hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, IsPullback.isoPullback_hom_fst, pullback.lift_fst]
    rw [← w, ← Category.assoc, IsPullback.isoPullback_inv_fst]
  · simp only [Category.assoc, IsPullback.isoPullback_hom_snd, pullback.lift_snd,
      Category.comp_id, IsPullback.isoPullback_inv_snd]

/-- **The fibre conditions at a field-valued point descend to the residue field.** Let
`t : Spec K ⟶ S` be a field-valued point over `s`, factoring as `Spec K ⟶ Spec κ(s) ⟶ S`. An
isomorphism `Y₁,ₜ ≅ Y₂,ₜ` over `K` compatible with `c₁,ₜ` and `c₂,ₜ`, together with the conditions
on `c₁,ₜ`, gives an isomorphism `Y₁,ₛ ≅ Y₂,ₛ` over `κ(s)` compatible with `c₁,ₛ` and `c₂,ₛ` and the
conditions on `c₁,ₛ`: the conditions descend along the faithfully flat `Spec K ⟶ Spec κ(s)`, they
make `c₁,ₛ` scheme-theoretically dominant, and the isomorphism then descends
(`AlgebraicGeometry.exists_iso_desc_of_isSchemeTheoreticallyDominant`). -/
theorem fibreData_residueField_of_fieldPoint {K : Type u} [Field K] (t : Spec (.of K) ⟶ S) (s : S)
    (hs : t (IsLocalRing.closedPoint K) = s) {X Y₁ Y₂ : Scheme.{u}}
    (fX : X ⟶ S) (fY₁ : Y₁ ⟶ S) (fY₂ : Y₂ ⟶ S) [IsProper fX] [IsProper fY₁] [IsProper fY₂]
    (c₁ : X ⟶ Y₁) (hc₁ : c₁ ≫ fY₁ = fX) (c₂ : X ⟶ Y₂) (hc₂ : c₂ ≫ fY₂ = fX)
    (φ : pullback fY₁ t ≅ pullback fY₂ t) (hφ : φ.hom ≫ pullback.snd _ _ = pullback.snd _ _)
    (hφc : fibreHom t fX fY₁ c₁ hc₁ ≫ φ.hom = fibreHom t fX fY₂ c₂ hc₂)
    (hdim : ∀ y, topologicalKrullDim ((fibreHom t fX fY₁ c₁ hc₁).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞))
    (h0 : IsIso (Scheme.Modules.unitToPushforwardUnit (fibreHom t fX fY₁ c₁ hc₁)))
    (hR : IsZero (((Scheme.Modules.pushforward (fibreHom t fX fY₁ c₁ hc₁)).rightDerived 1).obj
      (SheafOfModules.unit (pullback fX t).ringCatSheaf))) :
    ∃ φ' : pullback fY₁ (S.fromSpecResidueField s) ≅ pullback fY₂ (S.fromSpecResidueField s),
      φ'.hom ≫ pullback.snd _ _ = pullback.snd _ _ ∧
      fibreHom (S.fromSpecResidueField s) fX fY₁ c₁ hc₁ ≫ φ'.hom =
        fibreHom (S.fromSpecResidueField s) fX fY₂ c₂ hc₂ ∧
      (∀ y, topologicalKrullDim
        ((fibreHom (S.fromSpecResidueField s) fX fY₁ c₁ hc₁).fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞)) ∧
      IsIso (Scheme.Modules.unitToPushforwardUnit
        (fibreHom (S.fromSpecResidueField s) fX fY₁ c₁ hc₁)) ∧
      IsZero (((Scheme.Modules.pushforward
        (fibreHom (S.fromSpecResidueField s) fX fY₁ c₁ hc₁)).rightDerived 1).obj
          (SheafOfModules.unit (pullback fX (S.fromSpecResidueField s)).ringCatSheaf)) := by
  have : IsProper c₁ := by
    subst hc₁
    exact IsProper.of_comp c₁ fY₁
  obtain ⟨ρ, hρ⟩ := exists_comp_fromSpecResidueField t s hs
  set t'' := S.fromSpecResidueField s
  set τ := Spec.map ρ
  obtain ⟨_, _⟩ :=
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.flat_and_surjective_specMap_of_field ρ
  have hst : t ≫ 𝟙 S = τ ≫ t'' := by rw [Category.comp_id, hρ]
  have hid : ∀ {Z : Scheme.{u}} (fZ : Z ⟶ S), fZ ≫ 𝟙 S = 𝟙 Z ≫ fZ := fun fZ => by simp
  have hidp : ∀ {Z : Scheme.{u}} (fZ : Z ⟶ S), IsPullback (𝟙 Z) fZ fZ (𝟙 S) := fun fZ =>
    IsPullback.of_horiz_isIso ⟨rfl⟩
  have PX := isPullback_fibreMap hst fX fX (𝟙 X) (hid fX) (hidp fX)
  have PY₁ := isPullback_fibreMap hst fY₁ fY₁ (𝟙 Y₁) (hid fY₁) (hidp fY₁)
  have PY₂ := isPullback_fibreMap hst fY₂ fY₂ (𝟙 Y₂) (hid fY₂) (hidp fY₂)
  have H₁ := isPullback_fibreHom hst fX fY₁ fX fY₁ (𝟙 X) (𝟙 Y₁) (hid fX) (hid fY₁) c₁ hc₁ c₁ hc₁
    (by simp) (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have H₂ := isPullback_fibreHom hst fX fY₂ fX fY₂ (𝟙 X) (𝟙 Y₂) (hid fX) (hid fY₂) c₂ hc₂ c₂ hc₂
    (by simp) (IsPullback.of_horiz_isIso ⟨by simp⟩)
  -- the conditions descend
  have : Flat (fibreMap hst fY₁ fY₁ (𝟙 Y₁) (hid fY₁)) :=
    MorphismProperty.of_isPullback PY₁.flip inferInstance
  have : Surjective (fibreMap hst fY₁ fY₁ (𝟙 Y₁) (hid fY₁)) :=
    MorphismProperty.of_isPullback PY₁.flip inferInstance
  have : IsProper (fibreHom t'' fX fY₁ c₁ hc₁) :=
    MorphismProperty.of_isPullback (isPullback_fibreHom_fst t'' fX fY₁ c₁ hc₁) inferInstance
  have hdim'' : ∀ y, topologicalKrullDim ((fibreHom t'' fX fY₁ c₁ hc₁).fiber y) ≤
      ((1 : ℕ) : WithBot ℕ∞) := fun y => by
    obtain ⟨y', rfl⟩ := (fibreMap hst fY₁ fY₁ (𝟙 Y₁) (hid fY₁)).surjective y
    exact Stacks.AlgebraicGeometry.TopDegreeBaseChange.topologicalKrullDim_fiber_le_of_isPullback'
      H₁ 1 y' (hdim y')
  obtain ⟨h0'', hR''⟩ := fibreConditions_of_isPullback_of_surjective H₁ hdim'' h0 hR
  -- the isomorphism descends
  have : IsSchemeTheoreticallyDominant (fibreHom t'' fX fY₁ c₁ hc₁) :=
    isSchemeTheoreticallyDominant_of_isIso_unitToPushforwardUnit _
  have : IsProper (pullback.snd fY₂ t'') := MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback fY₂ t'') inferInstance
  let ψ₀ := PY₁.isoPullback.symm ≪≫ φ ≪≫ PY₂.isoPullback
  have hover : ψ₀.hom ≫ pullback.snd (pullback.snd fY₂ t'') τ =
      pullback.snd (pullback.snd fY₁ t'') τ := by simp [ψ₀, hφ]
  have hψ₀ : pullback.map (pullback.snd fX t'') τ (pullback.snd fY₁ t'') τ
      (fibreHom t'' fX fY₁ c₁ hc₁) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ ψ₀.hom =
      pullback.map (pullback.snd fX t'') τ (pullback.snd fY₂ t'') τ
      (fibreHom t'' fX fY₂ c₂ hc₂) (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    refine (congrArg (· ≫ ψ₀.hom) (pullbackMap_fibreHom_eq_isoPullback hc₁ PX PY₁ H₁.w)).trans
      (Eq.trans ?_ (pullbackMap_fibreHom_eq_isoPullback hc₂ PX PY₂ H₂.w).symm)
    simp [ψ₀, reassoc_of% hφc]
  obtain ⟨φ', hφ', -, hφc'⟩ := exists_iso_desc_of_isSchemeTheoreticallyDominant τ
    (fibreHom t'' fX fY₁ c₁ hc₁) (fibreHom_snd _ _ _ _ _) (fibreHom t'' fX fY₂ c₂ hc₂)
    (fibreHom_snd _ _ _ _ _) ψ₀ hover hψ₀
  exact ⟨φ', hφ', hφc', hdim'', h0'', hR''⟩

end FieldPoint

end AlgebraicGeometry.C1590Private

end
