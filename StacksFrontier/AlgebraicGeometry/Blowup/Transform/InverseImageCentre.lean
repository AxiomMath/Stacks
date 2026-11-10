module

public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalCartier
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.DenseOpen
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The strict transform under the blowup of the inverse-image centre

Let `S'` be the blowup of `S` in a quasi-coherent ideal `ℐ` and let `f : X ⟶ S` be a scheme
over `S`. The strict transform of `X` inside `X ×_S S'` is the blowup of `X` in the inverse
image `ℐ·𝒪_X` of `ℐ`, canonically over `X`; and for a sheaf of `𝒪_X`-modules `F` the strict
transform of `F` is the direct image, along the resulting closed immersion `X' ⟶ X ×_S S'`, of
the strict transform of `F` relative to the blowup of `X`.

## Main definitions

* `AlgebraicGeometry.blowUpLift`: the classifying morphism to a blowup: an `X`-scheme on which
  the centre becomes an effective Cartier divisor maps to the blowup over `X`.
* `AlgebraicGeometry.strictTransformBlowUpIso`: the strict transform of `X` in `X ×_S S'` is
  isomorphic, over `X`, to the blowup of `X` in `ℐ·𝒪_X`.
* `AlgebraicGeometry.strictTransformBlowUpι`: the closed immersion `X' ⟶ X ×_S S'` that
  isomorphism supplies, with `X'` presented as the base change `X ×_X X'`.
* `AlgebraicGeometry.strictTransformSheafBlowUpIso`: the strict transform of `F` is isomorphic
  to the direct image along `AlgebraicGeometry.strictTransformBlowUpι` of the strict transform of
  `F` relative to the blowup of `X`.

## Main results

* `AlgebraicGeometry.blowUpLift_comp` and `AlgebraicGeometry.blowUpLift_unique`: the
  classifying morphism lies over the base and is the only such morphism.
* `AlgebraicGeometry.isEffectiveCartierDivisor_comap_imageι_comp`: an effective Cartier divisor
  stays an effective Cartier divisor after pulling back to the scheme-theoretic image of an
  affine morphism that avoids it.
* `AlgebraicGeometry.isCartierOver_strictTransform`: on the strict transform of `X` the inverse
  image of `ℐ` is an effective Cartier divisor.
* `AlgebraicGeometry.exceptionalPreimage_eq_preimage_support_comap`: the inverse image of the
  exceptional divisor in `X ×_S S'` is the inverse image of the centre `ℐ·𝒪_X` under the
  projection to `X`.
* `AlgebraicGeometry.exists_strictTransformSheafBlowUpIso`: the isomorphism of
  `AlgebraicGeometry.strictTransformSheafBlowUpIso` can be chosen to identify the two quotient
  maps out of `pr_X^* F`.

## References

* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

section Lift

variable {X Y : Scheme.{u}} (I : X.IdealSheafData) (g : Y ⟶ X)

/-- The classifying morphism to the blowup: if the inverse image of `I` on `Y` is an effective
Cartier divisor, then `Y` maps to the blowup of `X` in `I` over `X`. -/
def blowUpLift (hg : Stacks.Blowup.IsCartierOver I (Over.mk g)) : Y ⟶ blowUp I :=
  ((Classical.choice (Classical.choose_spec (Stacks.Blowup.isTerminal_blowUp I))).from
    (⟨Over.mk g, hg⟩ : Stacks.Blowup.CartierOver I)).hom.left

/-- The classifying morphism to the blowup lies over the base. -/
theorem blowUpLift_comp (hg : Stacks.Blowup.IsCartierOver I (Over.mk g)) :
    blowUpLift I g hg ≫ blowUpToBase I = g :=
  Over.w ((Classical.choice (Classical.choose_spec
    (Stacks.Blowup.isTerminal_blowUp I))).from (⟨Over.mk g, hg⟩ :
      Stacks.Blowup.CartierOver I)).hom

/-- The classifying morphism to the blowup is the unique morphism over the base. -/
theorem blowUpLift_unique (hg : Stacks.Blowup.IsCartierOver I (Over.mk g))
    (h : Y ⟶ blowUp I) (hh : h ≫ blowUpToBase I = g) : h = blowUpLift I g hg :=
  congrArg (fun k ↦ k.hom.left)
    ((Classical.choice (Classical.choose_spec (Stacks.Blowup.isTerminal_blowUp I))).hom_ext
      (ObjectProperty.homMk (Over.homMk h hh))
      ((Classical.choice (Classical.choose_spec (Stacks.Blowup.isTerminal_blowUp I))).from
        (⟨Over.mk g, hg⟩ : Stacks.Blowup.CartierOver I)))

end Lift

/-- An effective Cartier divisor on `S` whose support is avoided by an affine morphism
`j : Z ⟶ T` over `S` stays an effective Cartier divisor after pulling it back to the
scheme-theoretic image of `j`. -/
theorem isEffectiveCartierDivisor_comap_imageι_comp {Z T S : Scheme.{u}} (j : Z ⟶ T)
    [IsAffineHom j] (g : T ⟶ S) (D : S.IdealSheafData)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D)
    (havoid : ∀ z : Z, g (j z) ∉ D.support) :
    Stacks.Divisors.IsEffectiveCartierDivisor (D.comap (j.imageι ≫ g)) := by
  have htop : D.comap (j ≫ g) = ⊤ := by
    refine (Scheme.IdealSheafData.support_eq_bot_iff _).mp ?_
    rw [Scheme.IdealSheafData.support_comap]
    exact TopologicalSpace.Closeds.ext (Set.eq_empty_iff_forall_notMem.mpr havoid)
  have hKtop : (D.comap (j.imageι ≫ g)).comap j.toImage = ⊤ := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Category.assoc,
      Scheme.Hom.toImage_imageι, htop]
  refine (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal
    (D.comap (j.imageι ≫ g))).mpr fun x hx ↦ ?_
  have hxD : (j.imageι ≫ g) x ∈ D.supportSet := by
    have h : x ∈ (D.comap (j.imageι ≫ g)).support :=
      Scheme.IdealSheafData.mem_supportSet_iff_mem_support.mp hx
    rwa [Scheme.IdealSheafData.support_comap] at h
  obtain ⟨U, hU, hxU, t, ht, e, he⟩ :=
    (Stacks.Divisors.isEffectiveCartierDivisor_iff_affineLocal D).mp hD _ hxD
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open
      (show j.imageι x ∈ g ⁻¹ᵁ U from hxU) (g ⁻¹ᵁ U).isOpen
  let U' : S.affineOpens := ⟨U, hU⟩
  let V' : T.affineOpens := ⟨V, hV⟩
  let W : j.image.affineOpens := ⟨j.imageι ⁻¹ᵁ V, hV.preimage j.imageι⟩
  have hWU : W.1 ≤ (j.imageι ≫ g) ⁻¹ᵁ U := fun y hy ↦ hVU hy
  let a := ((j.imageι ≫ g).appLE U' W hWU).hom t
  have hgen : (D.comap (j.imageι ≫ g)).ideal W = Ideal.span {a} := by
    rw [Stacks.IdealSheaf.ideal_comap_appLE D (j.imageι ≫ g) U' W hWU,
      Stacks.Divisors.ideal_eq_quotient_of_chart D U hU (Ideal.span {t}) e he,
      Ideal.map_span, Set.image_singleton]
  have hpre : j.toImage ⁻¹ᵁ W.1 = j ⁻¹ᵁ V := by
    change j.toImage ⁻¹ᵁ (j.imageι ⁻¹ᵁ V) = _
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toImage_imageι]
  let VZ : Z.affineOpens := ⟨j.toImage ⁻¹ᵁ W.1, by rw [hpre]; exact hV.preimage j⟩
  have hunit : IsUnit ((j.toImage.app W).hom a) := by
    refine Ideal.span_singleton_eq_top.mp ?_
    have h := Stacks.IdealSheaf.ideal_comap_appLE (D.comap (j.imageι ≫ g)) j.toImage W VZ le_rfl
    rw [hKtop, Scheme.IdealSheafData.ideal_top, Pi.top_apply, hgen, Ideal.map_span,
      Set.image_singleton, Scheme.Hom.appLE_eq_app] at h
    exact h.symm
  have ha : IsRegular a := by
    have hinj := j.toImage_app_injective V'
    refine ⟨fun b c hbc ↦ hinj (hunit.isRegular.left ?_),
      fun b c hbc ↦ hinj (hunit.isRegular.right ?_)⟩ <;>
    simpa only [map_mul] using congrArg (j.toImage.app W).hom hbc
  obtain ⟨e', he'⟩ := Stacks.Divisors.exists_quotient_chart_of_ideal_span
    (D.comap (j.imageι ≫ g)) W.1 W.2 a hgen
  exact ⟨W.1, W.2, hxV, a, ha, e', he'⟩

section StrictTransform

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℐ : S.IdealSheafData)

/-- The inclusion of the complement of the inverse image of the exceptional divisor into
`X ×_S S'` is an affine morphism. -/
instance isAffineHom_exceptionalComplement_ι :
    IsAffineHom
      (Stacks.StrictTransform.exceptionalComplement f (blowUpToBase ℐ)
        (exceptionalIdeal ℐ)).ι :=
  MorphismProperty.of_isPullback
    (isPullback_morphismRestrict (pullback.snd f (blowUpToBase ℐ))
      (exceptionalIdeal ℐ).support.compl)
    (Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor (exceptionalIdeal ℐ)
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal ℐ))

/-- On the strict transform of `X` in `X ×_S S'`, the inverse image of the centre `ℐ` is an
effective Cartier divisor. -/
theorem isCartierOver_strictTransform :
    Stacks.Blowup.IsCartierOver (ℐ.comap f)
      (Over.mk ((Stacks.StrictTransform.ideal f (blowUpToBase ℐ)
        (exceptionalIdeal ℐ)).subschemeι ≫ pullback.fst f (blowUpToBase ℐ))) := by
  have hc := isEffectiveCartierDivisor_comap_imageι_comp
    (Stacks.StrictTransform.exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).ι
    (pullback.snd f (blowUpToBase ℐ)) (exceptionalIdeal ℐ)
    (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal ℐ) (fun z ↦ z.property)
  change Stacks.Divisors.IsEffectiveCartierDivisor
    ((ℐ.comap f).comap ((Stacks.StrictTransform.ideal f (blowUpToBase ℐ)
      (exceptionalIdeal ℐ)).subschemeι ≫ pullback.fst f (blowUpToBase ℐ)))
  rw [Stacks.StrictTransform.ideal_eq_ker_ι]
  have heq : (ℐ.comap f).comap
      ((Stacks.StrictTransform.exceptionalComplement f (blowUpToBase ℐ)
        (exceptionalIdeal ℐ)).ι.imageι ≫ pullback.fst f (blowUpToBase ℐ)) =
      (exceptionalIdeal ℐ).comap
        ((Stacks.StrictTransform.exceptionalComplement f (blowUpToBase ℐ)
          (exceptionalIdeal ℐ)).ι.imageι ≫ pullback.snd f (blowUpToBase ℐ)) := by
    rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp]
    congr 1
    simp only [Category.assoc, pullback.condition]
  rwa [heq]

/-- The comparison morphism from the blowup of `X` in the inverse image of `ℐ` to the base
change `X ×_S S'`, whose components are the structure morphism of the blowup to `X` and the
classifying morphism to the blowup `S'` of `S` in `ℐ`. -/
def blowUpComapToBaseChange :
    blowUp (ℐ.comap f) ⟶ Limits.pullback f (blowUpToBase ℐ) :=
  pullback.lift (blowUpToBase (ℐ.comap f))
    (blowUpLift ℐ (blowUpToBase (ℐ.comap f) ≫ f) (by
      change Stacks.Divisors.IsEffectiveCartierDivisor
        (ℐ.comap (blowUpToBase (ℐ.comap f) ≫ f))
      rw [Scheme.IdealSheafData.comap_comp]
      exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (ℐ.comap f)))
    (blowUpLift_comp ℐ _ _).symm

/-- The comparison morphism `blowUpComapToBaseChange` composed with the first projection of
`X ×_S S'` is the structure morphism of the blowup of `X` in `ℐ·𝒪_X`. -/
@[simp]
theorem blowUpComapToBaseChange_fst :
    blowUpComapToBaseChange f ℐ ≫ pullback.fst f (blowUpToBase ℐ) =
      blowUpToBase (ℐ.comap f) :=
  pullback.lift_fst _ _ _

/-- The defining ideal of the strict transform is contained in the kernel of the comparison
morphism `AlgebraicGeometry.blowUpComapToBaseChange`. -/
theorem ideal_strictTransform_le_ker_blowUpComapToBaseChange :
    Stacks.StrictTransform.ideal f (blowUpToBase ℐ) (exceptionalIdeal ℐ) ≤
      (blowUpComapToBaseChange f ℐ).ker := by
  set G := blowUpComapToBaseChange f ℐ with hG
  set V : (blowUp (ℐ.comap f)).Opens := (exceptionalIdeal (ℐ.comap f)).support.compl with hV
  have hD := Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (ℐ.comap f)
  have hVdom : IsSchemeTheoreticallyDominant V.ι :=
    Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense V
      (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor _ hD)
  have hGsnd : G ≫ pullback.snd f (blowUpToBase ℐ) =
      blowUpLift ℐ (blowUpToBase (ℐ.comap f) ≫ f) (by
        change Stacks.Divisors.IsEffectiveCartierDivisor
          (ℐ.comap (blowUpToBase (ℐ.comap f) ≫ f))
        rw [Scheme.IdealSheafData.comap_comp]
        exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (ℐ.comap f)) :=
    pullback.lift_snd _ _ _
  have hsupp : (exceptionalIdeal (ℐ.comap f)).support =
      (G ≫ pullback.snd f (blowUpToBase ℐ)).base ⁻¹' (exceptionalIdeal ℐ).support := by
    have h : (exceptionalIdeal ℐ).comap (G ≫ pullback.snd f (blowUpToBase ℐ)) =
        exceptionalIdeal (ℐ.comap f) := by
      rw [exceptionalIdeal, exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp, hGsnd,
        blowUpLift_comp, Scheme.IdealSheafData.comap_comp]
    rw [← h, Scheme.IdealSheafData.support_comap]
    rfl
  have hrange : Set.range (V.ι ≫ G) ⊆
      Set.range (Stacks.StrictTransform.exceptionalComplement f (blowUpToBase ℐ)
        (exceptionalIdeal ℐ)).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    have hz : V.ι z ∉ ((exceptionalIdeal (ℐ.comap f)).support :
        Set (blowUp (ℐ.comap f))) := z.property
    rwa [hsupp] at hz
  rw [Stacks.StrictTransform.ideal_eq_ker_ι]
  calc _ ≤ (IsOpenImmersion.lift _ (V.ι ≫ G) hrange ≫ _).ker := Scheme.Hom.le_ker_comp _ _
    _ = G.ker := by
      rw [IsOpenImmersion.lift_fac, Scheme.Hom.ker_comp, V.ι.ker_eq_bot,
        Scheme.IdealSheafData.map_bot]

/-- The strict transform of `X` under the blowup of `S` in `ℐ` is the blowup of `X` in the
inverse image of `ℐ`, canonically as `X`-schemes. -/
@[stacks 080E "scheme", sga "5 VII 9.5" "First clause only"]
def strictTransformBlowUpIso :
    Over.mk ((Stacks.StrictTransform.ideal f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).subschemeι ≫
      pullback.fst f (blowUpToBase ℐ)) ≅ Over.mk (blowUpToBase (ℐ.comap f)) := by
  classical
  set J := Stacks.StrictTransform.ideal f (blowUpToBase ℐ) (exceptionalIdeal ℐ) with hJ
  set r := J.subschemeι ≫ pullback.fst f (blowUpToBase ℐ) with hr
  set b := blowUpToBase (ℐ.comap f) with hb
  have hc : Stacks.Blowup.IsCartierOver (ℐ.comap f) (Over.mk r) :=
    isCartierOver_strictTransform f ℐ
  have hcart : Stacks.Blowup.IsCartierOver ℐ (Over.mk (b ≫ f)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (ℐ.comap (b ≫ f))
    rw [Scheme.IdealSheafData.comap_comp]
    exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (ℐ.comap f)
  set p := blowUpLift (ℐ.comap f) r hc with hp'
  have hp : p ≫ b = r := blowUpLift_comp (ℐ.comap f) r hc
  set G := blowUpComapToBaseChange f ℐ with hG
  have hGsnd : G ≫ pullback.snd f (blowUpToBase ℐ) = blowUpLift ℐ (b ≫ f) hcart :=
    pullback.lift_snd _ _ _
  set q := G.toImage ≫ J.inclusion (ideal_strictTransform_le_ker_blowUpComapToBaseChange f ℐ)
    with hq
  have hqi : q ≫ J.subschemeι = G := by
    rw [hq, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι,
      Scheme.Hom.toImage_imageι]
  have hqr : q ≫ r = b := by
    rw [hr, ← Category.assoc, hqi, hG, blowUpComapToBaseChange_fst]
  have hcs : Stacks.Blowup.IsCartierOver ℐ (Over.mk (r ≫ f)) := by
    change Stacks.Divisors.IsEffectiveCartierDivisor (ℐ.comap (r ≫ f))
    rw [Scheme.IdealSheafData.comap_comp]
    exact hc
  have hqp : q ≫ p = 𝟙 _ := by
    have hcomp : (q ≫ p) ≫ b = b := by rw [Category.assoc, hp, hqr]
    exact (blowUpLift_unique (ℐ.comap f) b
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (ℐ.comap f)) _ hcomp).trans
      (blowUpLift_unique (ℐ.comap f) b
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (ℐ.comap f)) _
        (Category.id_comp b)).symm
  have hpq : p ≫ q = 𝟙 _ := by
    refine (cancel_mono J.subschemeι).mp ?_
    rw [Category.assoc, hqi, Category.id_comp]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hG, blowUpComapToBaseChange_fst, hp, hr]
    · have hleft : (p ≫ G ≫ pullback.snd f (blowUpToBase ℐ)) ≫ blowUpToBase ℐ = r ≫ f := by
        rw [hGsnd, Category.assoc, blowUpLift_comp, ← Category.assoc, hp]
      have hright : (J.subschemeι ≫ pullback.snd f (blowUpToBase ℐ)) ≫ blowUpToBase ℐ =
          r ≫ f := by
        rw [hr, Category.assoc, Category.assoc, pullback.condition]
      rw [Category.assoc]
      exact (blowUpLift_unique ℐ (r ≫ f) hcs _ hleft).trans
        (blowUpLift_unique ℐ (r ≫ f) hcs _ hright).symm
  exact
    { hom := Over.homMk p hp
      inv := Over.homMk q hqr
      hom_inv_id := by ext; exact hpq
      inv_hom_id := by ext; exact hqp }

end StrictTransform

section StrictTransformModule

open Scheme.Modules Stacks.StrictTransform

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℐ : S.IdealSheafData)

/-- The isomorphism between the base change `X ×_X X'` of `X` along the blowup `X'` of `X` in
`ℐ·𝒪_X` and the strict transform of `X` in `X ×_S S'`, given by the second projection followed
by `AlgebraicGeometry.strictTransformBlowUpIso`. -/
def strictTransformBlowUpComapIso :
    baseChange (𝟙 X) (blowUpToBase (ℐ.comap f)) ≅
      (ideal f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).subscheme :=
  asIso (pullback.snd (𝟙 X) (blowUpToBase (ℐ.comap f))) ≪≫
    ((Over.forget X).mapIso (strictTransformBlowUpIso f ℐ)).symm

/-- The closed immersion `X' ⟶ X ×_S S'` of the blowup `X'` of `X` in `ℐ·𝒪_X` onto the strict
transform, with `X'` presented as the base change `X ×_X X'`. -/
def strictTransformBlowUpι :
    baseChange (𝟙 X) (blowUpToBase (ℐ.comap f)) ⟶ baseChange f (blowUpToBase ℐ) :=
  (strictTransformBlowUpComapIso f ℐ).hom ≫
    (ideal f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).subschemeι

/-- `AlgebraicGeometry.strictTransformBlowUpι` is a closed immersion. -/
instance isClosedImmersion_strictTransformBlowUpι :
    IsClosedImmersion (strictTransformBlowUpι f ℐ) := by
  rw [strictTransformBlowUpι]
  infer_instance

/-- `AlgebraicGeometry.strictTransformBlowUpι` is a morphism over `X`: composing it with the
projection of `X ×_S S'` to `X` gives the projection of `X ×_X X'` to `X`. -/
lemma strictTransformBlowUpι_fst :
    strictTransformBlowUpι f ℐ ≫ pullback.fst f (blowUpToBase ℐ) =
      pullback.fst (𝟙 X) (blowUpToBase (ℐ.comap f)) := by
  have hw := (strictTransformBlowUpIso f ℐ).inv.w
  rw [strictTransformBlowUpι, strictTransformBlowUpComapIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map, asIso_hom,
    Category.assoc]
  rw [show (strictTransformBlowUpIso f ℐ).inv.left ≫
      (ideal f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).subschemeι ≫
        pullback.fst f (blowUpToBase ℐ) = blowUpToBase (ℐ.comap f) from hw]
  simpa using (pullback.condition (f := 𝟙 X) (g := blowUpToBase (ℐ.comap f))).symm

/-- The inverse image of the exceptional divisor in `X ×_S S'` is also the inverse image of the
centre `ℐ·𝒪_X` under the projection to `X`. -/
lemma exceptionalPreimage_eq_preimage_support_comap :
    exceptionalPreimage f (blowUpToBase ℐ) (exceptionalIdeal ℐ) =
      (pullback.fst f (blowUpToBase ℐ)).base ⁻¹' (ℐ.comap f).support := by
  have hExc : ((exceptionalIdeal ℐ).support : Set (blowUp ℐ)) =
      (blowUpToBase ℐ).base ⁻¹' (ℐ.support : Set S) := by
    rw [exceptionalIdeal, Scheme.IdealSheafData.support_comap]; rfl
  have hPull : ((ℐ.comap f).support : Set X) = f.base ⁻¹' (ℐ.support : Set S) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  ext y
  change (pullback.snd f (blowUpToBase ℐ)) y ∈ ((exceptionalIdeal ℐ).support : Set (blowUp ℐ)) ↔
    (pullback.fst f (blowUpToBase ℐ)) y ∈ ((ℐ.comap f).support : Set X)
  rw [hExc, hPull]
  have hy := congrArg (fun k : baseChange f (blowUpToBase ℐ) ⟶ S => k y)
    (pullback.condition (f := f) (g := blowUpToBase ℐ))
  change (pullback.snd f (blowUpToBase ℐ) ≫ blowUpToBase ℐ) y ∈ (ℐ.support : Set S) ↔
    (pullback.fst f (blowUpToBase ℐ) ≫ f) y ∈ (ℐ.support : Set S)
  exact ⟨fun h => hy.symm ▸ h, fun h => hy ▸ h⟩

/-- The inverse image under `AlgebraicGeometry.strictTransformBlowUpι` of the inverse image of
the exceptional divisor of `S'` is its counterpart for the blowup of `X`. -/
lemma preimage_exceptionalPreimage_strictTransformBlowUpι :
    (strictTransformBlowUpι f ℐ).base ⁻¹'
        exceptionalPreimage f (blowUpToBase ℐ) (exceptionalIdeal ℐ) =
      exceptionalPreimage (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) := by
  rw [exceptionalPreimage_eq_preimage_support_comap f ℐ,
    exceptionalPreimage_eq_preimage_support_comap (𝟙 X) (ℐ.comap f),
    Scheme.IdealSheafData.comap_id]
  ext z
  have hz := congrArg (fun k : baseChange (𝟙 X) (blowUpToBase (ℐ.comap f)) ⟶ X => k z)
    (strictTransformBlowUpι_fst f ℐ)
  change (strictTransformBlowUpι f ℐ ≫ pullback.fst f (blowUpToBase ℐ)) z ∈
      ((ℐ.comap f).support : Set X) ↔
    (pullback.fst (𝟙 X) (blowUpToBase (ℐ.comap f))) z ∈ ((ℐ.comap f).support : Set X)
  exact Iff.of_eq (congrArg (fun x => x ∈ ((ℐ.comap f).support : Set X)) hz)

/-- The open form of `AlgebraicGeometry.preimage_exceptionalPreimage_strictTransformBlowUpι`. -/
lemma preimage_exceptionalComplement_strictTransformBlowUpι :
    strictTransformBlowUpι f ℐ ⁻¹ᵁ
        exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ) =
      exceptionalComplement (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) := by
  apply TopologicalSpace.Opens.ext
  change (strictTransformBlowUpι f ℐ).base ⁻¹'
      (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ) :
        Set (baseChange f (blowUpToBase ℐ))) = _
  rw [← compl_compl (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ) :
      Set (baseChange f (blowUpToBase ℐ))),
    ← exceptionalPreimage_eq_compl, Set.preimage_compl,
    preimage_exceptionalPreimage_strictTransformBlowUpι, exceptionalPreimage_eq_compl,
    compl_compl]

/-- The closed form of `AlgebraicGeometry.preimage_exceptionalPreimage_strictTransformBlowUpι`,
with the subset of `X ×_S S'` written as the complement of the open complement. -/
lemma preimage_compl_exceptionalComplement_strictTransformBlowUpι :
    (strictTransformBlowUpι f ℐ).base ⁻¹'
        (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ) :
          Set (baseChange f (blowUpToBase ℐ)))ᶜ =
      exceptionalPreimage (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) := by
  rw [← exceptionalPreimage_eq_compl, preimage_exceptionalPreimage_strictTransformBlowUpι]

/-- The factorization of the inclusion of the complement of the inverse image of the exceptional
divisor through the strict transform `X ×_X X'`, which is its scheme-theoretic image. -/
def exceptionalComplementToBlowUpComap :
    (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).toScheme ⟶
      baseChange (𝟙 X) (blowUpToBase (ℐ.comap f)) :=
  (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).ι.toImage ≫
    Scheme.IdealSheafData.inclusion
      (le_of_eq (ideal_eq_ker_ι f (blowUpToBase ℐ) (exceptionalIdeal ℐ))) ≫
    (strictTransformBlowUpComapIso f ℐ).inv

/-- `AlgebraicGeometry.exceptionalComplementToBlowUpComap` is a section of
`AlgebraicGeometry.strictTransformBlowUpι` over the complement of the inverse image of the
exceptional divisor. -/
lemma exceptionalComplementToBlowUpComap_comp :
    exceptionalComplementToBlowUpComap f ℐ ≫ strictTransformBlowUpι f ℐ =
      (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).ι := by
  rw [exceptionalComplementToBlowUpComap, strictTransformBlowUpι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]

/-- The base-change comparison `g^* pr_X^* F ≅ pr_X'^* F` for
`g = AlgebraicGeometry.strictTransformBlowUpι`, which is a morphism over `X`. -/
def pullbackStrictTransformBlowUpIso (F : X.Modules) :
    (Scheme.Modules.pullback (strictTransformBlowUpι f ℐ)).obj
        ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase ℐ))).obj F) ≅
      (Scheme.Modules.pullback (pullback.fst (𝟙 X) (blowUpToBase (ℐ.comap f)))).obj F :=
  (Scheme.Modules.pullbackComp (strictTransformBlowUpι f ℐ)
      (pullback.fst f (blowUpToBase ℐ))).app F ≪≫
    (Scheme.Modules.pullbackCongr (strictTransformBlowUpι_fst f ℐ)).app F

/-- For `g = AlgebraicGeometry.strictTransformBlowUpι`, the unit of `g^* ⊣ g_*` at `pr_X^* F`
followed by `g_*` of the quotient map onto the strict transform over `X` is an epimorphism. -/
instance epi_unit_comp_pushforward_map_π (F : X.Modules) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction (strictTransformBlowUpι f ℐ)).unit.app
          ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase ℐ))).obj F) ≫
        (Scheme.Modules.pushforward (strictTransformBlowUpι f ℐ)).map
          ((pullbackStrictTransformBlowUpIso f ℐ F).hom ≫
            π (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) F)) := by
  have hfull := Stacks.ClosedImmersion.full_pushforward (strictTransformBlowUpι f ℐ)
  have hfaith := Stacks.ClosedImmersion.faithful_pushforward (strictTransformBlowUpι f ℐ)
  have hpe : (Scheme.Modules.pushforward (strictTransformBlowUpι f ℐ)).PreservesEpimorphisms :=
    inferInstanceAs ((RingedSpaceModuleAdjunction.modulePushforward
      (strictTransformBlowUpι f ℐ).toLRSHom.toShHom).PreservesEpimorphisms)
  have hunit := Stacks.ClosedImmersion.epi_unit_app (strictTransformBlowUpι f ℐ)
    ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase ℐ))).obj F)
  exact epi_comp _ _

/-- The unit of restriction to the complement of the inverse image of the exceptional divisor is
a monomorphism at the direct image along `AlgebraicGeometry.strictTransformBlowUpι` of the
strict transform of `F` over `X`: that direct image has no nonzero sections supported on the
inverse image of the exceptional divisor. -/
instance mono_unit_app_pushforward_sheaf_blowUpComap (F : X.Modules) :
    Mono ((restrictAdjunction
      (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).ι).unit.app
      ((Scheme.Modules.pushforward (strictTransformBlowUpι f ℐ)).obj
        (sheaf (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) F))) :=
  mono_unit_app_of_supportedSections_eq_zero _ _ fun U s hs =>
    supportedSections_pushforward_eq_zero _ _
      (preimage_compl_exceptionalComplement_strictTransformBlowUpι f ℐ) _
      (supportedSections_sheaf_eq_zero (𝟙 X) (blowUpToBase (ℐ.comap f))
        (exceptionalIdeal (ℐ.comap f)) F) U s hs

/-- For `g = AlgebraicGeometry.strictTransformBlowUpι`, the unit of `g^* ⊣ g_*` at `pr_X^* F`
followed by `g_*` of the quotient map onto the strict transform over `X` becomes an isomorphism
on the complement of the inverse image of the exceptional divisor. -/
instance isIso_restrictFunctor_map_unit_comp_pushforward_map_π (F : X.Modules) :
    IsIso ((restrictFunctor
      (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ)).ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (strictTransformBlowUpι f ℐ)).unit.app
          ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase ℐ))).obj F) ≫
        (Scheme.Modules.pushforward (strictTransformBlowUpι f ℐ)).map
          ((pullbackStrictTransformBlowUpIso f ℐ F).hom ≫
            π (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) F))) := by
  have hfull := Stacks.ClosedImmersion.full_pushforward (strictTransformBlowUpι f ℐ)
  have hfaith := Stacks.ClosedImmersion.faithful_pushforward (strictTransformBlowUpι f ℐ)
  have h1 := isIso_restrictFunctor_map_unit_of_section (strictTransformBlowUpι f ℐ)
    (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ))
    (exceptionalComplementToBlowUpComap f ℐ) (exceptionalComplementToBlowUpComap_comp f ℐ)
    ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase ℐ))).obj F)
  have hπ := isIso_restrictFunctor_map_π (𝟙 X) (blowUpToBase (ℐ.comap f))
    (exceptionalIdeal (ℐ.comap f)) F
  have h2 : IsIso ((restrictFunctor
      (exceptionalComplement (𝟙 X) (blowUpToBase (ℐ.comap f))
        (exceptionalIdeal (ℐ.comap f))).ι).map
      ((pullbackStrictTransformBlowUpIso f ℐ F).hom ≫
        π (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) F)) := by
    rw [Functor.map_comp]
    infer_instance
  have h3 := isIso_restrictFunctor_map_pushforward_map (strictTransformBlowUpι f ℐ)
    (exceptionalComplement f (blowUpToBase ℐ) (exceptionalIdeal ℐ))
    (preimage_exceptionalComplement_strictTransformBlowUpι f ℐ) _ h2
  rw [Functor.map_comp]
  infer_instance

/-- There is an isomorphism between the strict transform of `F` and the direct image along
`g : X' ⟶ X ×_S S'` of the strict transform of `F` relative to the blowup of `X` in `ℐ·𝒪_X`
under which the quotient map out of `pr_X^* F` becomes the unit of `g^* ⊣ g_*` followed by `g_*`
of the quotient map over `X`. -/
theorem exists_strictTransformSheafBlowUpIso (F : X.Modules) :
    ∃ e : sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F ≅
        (Scheme.Modules.pushforward (strictTransformBlowUpι f ℐ)).obj
          (sheaf (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) F),
      π f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F ≫ e.hom =
        (Scheme.Modules.pullbackPushforwardAdjunction (strictTransformBlowUpι f ℐ)).unit.app
            ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase ℐ))).obj F) ≫
          (Scheme.Modules.pushforward (strictTransformBlowUpι f ℐ)).map
            ((pullbackStrictTransformBlowUpIso f ℐ F).hom ≫
              π (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) F) :=
  exists_iso f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F _

/-- For a sheaf of `𝒪_X`-modules `F`, the strict
transform of `F` under the blowup of `S` in `ℐ` is canonically the direct image, along the closed
immersion `X' ⟶ X ×_S S'` of part (1), of the strict transform of `F` relative to the blowup of
`X` in the inverse image `ℐ·𝒪_X`. The sheaf `F` is not assumed quasi-coherent. -/
@[stacks 080E "sheaf"]
def strictTransformSheafBlowUpIso (F : X.Modules) :
    sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F ≅
      (Scheme.Modules.pushforward (strictTransformBlowUpι f ℐ)).obj
        (sheaf (𝟙 X) (blowUpToBase (ℐ.comap f)) (exceptionalIdeal (ℐ.comap f)) F) :=
  (exists_strictTransformSheafBlowUpIso f ℐ F).choose

end StrictTransformModule

end AlgebraicGeometry

end
