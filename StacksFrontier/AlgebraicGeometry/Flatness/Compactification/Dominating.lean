module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.CompactificationsUnconditional
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SchemeTheoreticImage

/-!
# Two compactifications are dominated by a third

Let `f : X ⟶ Y` be a morphism of schemes and let `j₁ : X ⟶ X̄₁`, `j₂ : X ⟶ X̄₂` be two
compactifications of `X` over `Y` whose open immersions are quasi-compact. The scheme-theoretic
image `W` of `(j₁, j₂) : X ⟶ X̄₁ ×_Y X̄₂` is again a compactification of `X` over `Y`, and the
two projections `W ⟶ X̄ᵢ` are morphisms of compactifications along which `X` is cartesian:
`X = W ×_{X̄ᵢ} X`. This is the step of [Stacks, Tag 0F7I] which shows that the category of
compactifications is cofiltered.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.dominating`: the compactification `W`.
* `AlgebraicGeometry.CompactificationOf.dominatingFst`, `dominatingSnd`: the morphisms
  `W ⟶ X̄₁` and `W ⟶ X̄₂` of compactifications.

## Main results

* `AlgebraicGeometry.isPullback_toImage_of_comp_eq_openImmersion`: if `σ : X ⟶ P` followed by a
  separated morphism `p : P ⟶ Z` is a quasi-compact open immersion `ι`, then `X` is the inverse
  image of `ι` in the scheme-theoretic image of `σ`.
* `AlgebraicGeometry.CompactificationOf.isPullback_dominatingFst`,
  `AlgebraicGeometry.CompactificationOf.isPullback_dominatingSnd`: the two morphisms are
  cartesian over the interior.

## References

* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0CNG](https://stacks.math.columbia.edu/tag/0CNG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The scheme-theoretic image of a partial section over a quasi-compact open.** Let
`p : P ⟶ Z` be separated and `σ : X ⟶ P` a morphism such that `σ ≫ p = ι` is a quasi-compact
open immersion. Then the square formed by `σ.toImage`, the identity of `X`, `σ.imageι ≫ p` and
`ι` is cartesian: over the open `ι(X)` of `Z` the scheme-theoretic image of `σ` is `X` itself
(Tag 0CNG). -/
theorem isPullback_toImage_of_comp_eq_openImmersion {X P Z : Scheme.{u}} (σ : X ⟶ P)
    (p : P ⟶ Z) [IsSeparated p] (ι : X ⟶ Z) [IsOpenImmersion ι] [QuasiCompact ι]
    (h : σ ≫ p = ι) :
    IsPullback σ.toImage (𝟙 X) (σ.imageι ≫ p) ι := by
  let V : Z.Opens := ι.opensRange
  have hV : IsRetrocompact (V : Set Z) := by
    intro U hU hUopen
    rw [show (V : Set Z) = Set.range ι by simp [V, Scheme.Hom.coe_opensRange],
      Set.inter_comm, ← Set.image_preimage_eq_inter_range]
    exact (QuasiCompact.isCompact_preimage U hUopen hU).image ι.continuous
  have hr : Set.range V.ι = Set.range ι := by simp [V, Scheme.Hom.coe_opensRange]
  let e : V.toScheme ≅ X := IsOpenImmersion.isoOfRangeEq V.ι ι hr
  have he : e.hom ≫ ι = V.ι := IsOpenImmersion.isoOfRangeEq_hom_fac V.ι ι hr
  have hs : (e.hom ≫ σ) ≫ p = V.ι := by rw [Category.assoc, h, he]
  have key := isIso_pullback_snd_imageι_comp_of_section p V hV (e.hom ≫ σ) hs
  have hker : (e.hom ≫ σ).ker = σ.ker := Scheme.Hom.ker_comp_of_isIso _ _
  have key : IsIso (pullback.snd (σ.imageι ≫ p) V.ι) := by
    change IsIso (pullback.snd (σ.ker.subschemeι ≫ p) V.ι)
    rwa [← hker]
  have hw : σ.toImage ≫ σ.imageι ≫ p = e.inv ≫ V.ι := by
    rw [Scheme.Hom.toImage_imageι_assoc, h, ← he, Iso.inv_hom_id_assoc]
  let t : X ⟶ pullback (σ.imageι ≫ p) V.ι := pullback.lift σ.toImage e.inv hw
  have ht : t ≫ pullback.snd (σ.imageι ≫ p) V.ι = e.inv := pullback.lift_snd _ _ _
  have : IsIso t := IsIso.of_isIso_fac_right ht
  refine (IsPullback.of_hasPullback (σ.imageι ≫ p) V.ι).of_iso (asIso t).symm (Iso.refl _) e
    (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
    exact pullback.lift_fst _ _ _
  · rw [Category.comp_id, Iso.symm_hom, asIso_inv]
    symm
    apply IsIso.inv_eq_of_hom_inv_id
    rw [reassoc_of% ht, Iso.inv_hom_id]
  · simp
  · simp [he]

namespace CompactificationOf

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (j₁ j₂ : CompactificationOf (Over.mk f))

/-- The morphism `(j₁, j₂) : X ⟶ X̄₁ ×_Y X̄₂`. -/
abbrev dominatingLift : X ⟶ pullback j₁.toBase j₂.toBase :=
  pullback.lift j₁.immersion j₂.immersion
    (by rw [immersion_toBase_general, immersion_toBase_general])

/-- The ambient scheme of the dominating compactification: the scheme-theoretic image of
`(j₁, j₂) : X ⟶ X̄₁ ×_Y X̄₂`. -/
abbrev dominatingSpace : Scheme.{u} := (dominatingLift j₁ j₂).image

/-- The projection of the dominating compactification to `X̄₁`. -/
abbrev dominatingFstMap : dominatingSpace j₁ j₂ ⟶ j₁.space :=
  (dominatingLift j₁ j₂).imageι ≫ pullback.fst j₁.toBase j₂.toBase

/-- The projection of the dominating compactification to `X̄₂`. -/
abbrev dominatingSndMap : dominatingSpace j₁ j₂ ⟶ j₂.space :=
  (dominatingLift j₁ j₂).imageι ≫ pullback.snd j₁.toBase j₂.toBase

variable [QuasiCompact j₁.immersion] [QuasiCompact j₂.immersion]

omit [QuasiCompact j₂.immersion] in
/-- Over the interior of `X̄₁`, the scheme-theoretic image of `(j₁, j₂)` is `X`. -/
theorem isPullback_dominatingFstMap :
    IsPullback (dominatingLift j₁ j₂).toImage (𝟙 X) (dominatingFstMap j₁ j₂) j₁.immersion :=
  isPullback_toImage_of_comp_eq_openImmersion _ _ _ (pullback.lift_fst _ _ _)

omit [QuasiCompact j₁.immersion] in
/-- Over the interior of `X̄₂`, the scheme-theoretic image of `(j₁, j₂)` is `X`. -/
theorem isPullback_dominatingSndMap :
    IsPullback (dominatingLift j₁ j₂).toImage (𝟙 X) (dominatingSndMap j₁ j₂) j₂.immersion :=
  isPullback_toImage_of_comp_eq_openImmersion _ _ _ (pullback.lift_snd _ _ _)

/-- The morphism `X ⟶ W` into the scheme-theoretic image of `(j₁, j₂)` is an open immersion. -/
instance isOpenImmersion_dominatingLift_toImage :
    IsOpenImmersion (dominatingLift j₁ j₂).toImage :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_dominatingFstMap j₁ j₂).flip inferInstance

/-- **The dominating compactification.** The open immersion of `X` into the scheme-theoretic
image `W` of `(j₁, j₂) : X ⟶ X̄₁ ×_Y X̄₂`, which is closed in `X̄₁ ×_Y X̄₂` and hence proper
over `Y`. -/
def dominating : CompactificationOf (Over.mk f) :=
  ⟨StructuredArrow.mk (Y := Over.mk (dominatingFstMap j₁ j₂ ≫ j₁.toBase))
      (Over.homMk (U := Over.mk f) (V := Over.mk (dominatingFstMap j₁ j₂ ≫ j₁.toBase))
        (dominatingLift j₁ j₂).toImage (by
          simpa only [Over.mk_hom, dominatingFstMap, Category.assoc,
            Scheme.Hom.toImage_imageι_assoc, pullback.lift_fst_assoc] using
            immersion_toBase_general j₁)),
    ⟨(inferInstance : IsOpenImmersion (dominatingLift j₁ j₂).toImage),
      (inferInstance : IsProper (dominatingFstMap j₁ j₂ ≫ j₁.toBase))⟩⟩

omit [QuasiCompact j₂.immersion] in
/-- The ambient scheme of `dominating j₁ j₂` is `dominatingSpace j₁ j₂`. -/
@[simp]
lemma dominating_space : (dominating j₁ j₂).space = dominatingSpace j₁ j₂ := rfl

omit [QuasiCompact j₂.immersion] in
/-- The open immersion of `dominating j₁ j₂` is the corestriction `X ⟶ W` of `(j₁, j₂)`. -/
@[simp]
lemma dominating_immersion : (dominating j₁ j₂).immersion = (dominatingLift j₁ j₂).toImage :=
  rfl

omit [QuasiCompact j₂.immersion] in
/-- The structure morphism of `dominating j₁ j₂` is the composite `W ⟶ X̄₁ ⟶ Y`. -/
@[simp]
lemma dominating_toBase :
    (dominating j₁ j₂).toBase = dominatingFstMap j₁ j₂ ≫ j₁.toBase := rfl

/-- The morphism of compactifications `W ⟶ X̄₁`. -/
def dominatingFst : dominating j₁ j₂ ⟶ j₁ :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk (dominatingFstMap j₁ j₂) rfl) (by
      ext
      change (dominatingLift j₁ j₂).toImage ≫ dominatingFstMap j₁ j₂ = j₁.immersion
      simp only [dominatingFstMap, Scheme.Hom.toImage_imageι_assoc, pullback.lift_fst]))

/-- The morphism of compactifications `W ⟶ X̄₂`. -/
def dominatingSnd : dominating j₁ j₂ ⟶ j₂ :=
  ObjectProperty.homMk (StructuredArrow.homMk
    (Over.homMk (dominatingSndMap j₁ j₂) (by
      simp [dominating, pullback.condition])) (by
      ext
      change (dominatingLift j₁ j₂).toImage ≫ dominatingSndMap j₁ j₂ = j₂.immersion
      simp only [dominatingSndMap, Scheme.Hom.toImage_imageι_assoc, pullback.lift_snd]))

omit [QuasiCompact j₂.immersion] in
/-- The underlying morphism of schemes of `dominatingFst j₁ j₂` is `dominatingFstMap j₁ j₂`. -/
@[simp]
lemma dominatingFst_map : Hom.map (dominatingFst j₁ j₂) = dominatingFstMap j₁ j₂ := rfl

omit [QuasiCompact j₂.immersion] in
/-- The underlying morphism of schemes of `dominatingSnd j₁ j₂` is `dominatingSndMap j₁ j₂`. -/
@[simp]
lemma dominatingSnd_map : Hom.map (dominatingSnd j₁ j₂) = dominatingSndMap j₁ j₂ := rfl

omit [QuasiCompact j₂.immersion] in
/-- `X` is cartesian along `W ⟶ X̄₁`. -/
theorem isPullback_dominatingFst :
    IsPullback (dominating j₁ j₂).immersion (𝟙 X) (Hom.map (dominatingFst j₁ j₂))
      j₁.immersion :=
  isPullback_dominatingFstMap j₁ j₂

/-- `X` is cartesian along `W ⟶ X̄₂`. -/
theorem isPullback_dominatingSnd :
    IsPullback (dominating j₁ j₂).immersion (𝟙 X) (Hom.map (dominatingSnd j₁ j₂))
      j₂.immersion :=
  isPullback_dominatingSndMap j₁ j₂

end CompactificationOf

end AlgebraicGeometry

end
