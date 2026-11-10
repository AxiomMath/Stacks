module

public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Dominance
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense

/-!
# An open subscheme is scheme-theoretically dense in its scheme-theoretic closure

Let `V` be an open subscheme of a scheme `X` whose inclusion is quasi-compact. The
scheme-theoretic closure of `V` is the scheme-theoretic image
`AlgebraicGeometry.Scheme.Hom.image` of `V.ι`, the closed subscheme cut out by `V.ι.ker`. This
file proves that `V`, viewed inside that closed subscheme, is scheme-theoretically dense there,
and that the closed subscheme is an isomorphism over `V`.

Both statements are what makes a strict transform recognisable as the scheme-theoretic image of
the part of a base change lying away from the exceptional divisor; see
`StacksFrontier/AlgebraicGeometry/StrictTransform/CompositionScheme.lean`.

Also collected here is the comparison of two closed immersions into a common target which agree
on a scheme-theoretically dense open of one of them: they are isomorphic, compatibly.

## Main definitions

* `Stacks.SchemeTheoreticImage.toPreimage`: the factorization of
  `AlgebraicGeometry.Scheme.Hom.toImage` through the inverse image of `V` in the
  scheme-theoretic closure.
* `Stacks.SchemeTheoreticImage.toSubscheme`: the morphism from `V` into the closed subscheme cut
  out by any ideal sheaf equal to `V.ι.ker`.

## Main results

* `Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDense_of_dominant` and
  `Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDominant_of_dense`: for an open subscheme
  with quasi-compact inclusion, scheme-theoretic density and scheme-theoretic dominance of the
  inclusion are the same condition.
* `Stacks.SchemeTheoreticImage.isIso_imageι_restrict`: the scheme-theoretic closure of an open
  subscheme is an isomorphism over that open.
* `Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDense_preimage_imageι`: **an open subscheme
  with quasi-compact inclusion is scheme-theoretically dense in its scheme-theoretic closure**,
  with `Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDense_preimage_subschemeι` the form
  stated for an ideal sheaf presented as a kernel.
* `Stacks.SchemeTheoreticImage.exists_iso_of_isSchemeTheoreticallyDense`: two closed immersions
  into a common target with a shared scheme-theoretically dense open are isomorphic over it.

## Implementation notes

Scheme-theoretic density of an open is `∀ V, IsSchemeTheoreticallyDominant ((V.ι ⁻¹ᵁ U).ι)`,
quantified over *all* opens `V`, and is therefore stronger than dominance of `U.ι` alone. The
two are nevertheless equivalent once `U.ι` is quasi-compact, because
`AlgebraicGeometry.Scheme.Hom.app_injective` then upgrades dominance from affine opens to all
opens and `AlgebraicGeometry.isSchemeTheoreticallyDense_opensRange_iff_mono` reads density off
injectivity of the comorphism. That is the only place quasi-compactness is used.

`Stacks.SchemeTheoreticImage.isIso_imageι_restrict` is proved by exhibiting
`Stacks.SchemeTheoreticImage.toPreimage` as a section of `V.ι.imageι ∣_ V`: that restriction is a
monomorphism because its composite with `V.ι` is one, and a monomorphism with a section is an
isomorphism.

The statements about an ideal sheaf `I` carry the hypothesis `I = V.ι.ker` and are proved by
`subst`, rather than being stated for `V.ι.ker` directly, because the ambient scheme of the open
`I.subschemeι ⁻¹ᵁ V` depends on `I`: rewriting `I` inside that type is a rewrite under a
dependent type, whereas substituting the variable is free. The consumers in
`StacksFrontier/AlgebraicGeometry/StrictTransform/CompositionScheme.lean` supply
`Stacks.StrictTransform.ideal_eq_ker_ι`.

## References

* [Stacks Project, Tag 01RB](https://stacks.math.columbia.edu/tag/01RB)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.SchemeTheoreticImage

variable {X Y : Scheme.{u}}

/-- An open subscheme whose inclusion is quasi-compact and scheme-theoretically dominant is
scheme-theoretically dense. -/
public theorem isSchemeTheoreticallyDense_of_dominant (U : X.Opens)
    [IsSchemeTheoreticallyDominant U.ι] [QuasiCompact U.ι] :
    Scheme.Opens.IsSchemeTheoreticallyDense U := by
  have h := (AlgebraicGeometry.isSchemeTheoreticallyDense_opensRange_iff_mono U.ι).2
    (Stacks.Divisors.mono_c_of_forall_app_injective _ fun V ↦ U.ι.app_injective V)
  rwa [Scheme.Opens.opensRange_ι] at h

/-- The inclusion of a scheme-theoretically dense open subscheme is scheme-theoretically
dominant. -/
public theorem isSchemeTheoreticallyDominant_of_dense (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) : IsSchemeTheoreticallyDominant U.ι := by
  have hm : Mono U.ι.c :=
    (isSchemeTheoreticallyDense_opensRange_iff_mono U.ι).mp
      (by simpa only [Scheme.Opens.opensRange_ι] using hU)
  refine ⟨le_bot_iff.mp fun V ↦ ?_⟩
  refine (U.ι.ideal_ker_le V).trans ?_
  have hi : Function.Injective (U.ι.app V.1).hom :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback _).mp
      ((NatTrans.mono_iff_mono_app _).mp hm (op V.1))
  exact le_of_eq ((RingHom.injective_iff_ker_eq_bot _).mp hi)

/-- The scheme-theoretic closure of an open subscheme meets it in the inverse image of that
open. -/
public lemma range_toImage_le (V : X.Opens) :
    Set.range (V.ι.toImage).base ⊆ (V.ι.imageι ⁻¹ᵁ V : (V.ι.image).Opens) := by
  rintro _ ⟨x, rfl⟩
  change (V.ι.toImage ≫ V.ι.imageι) x ∈ (V : Set X)
  rw [V.ι.toImage_imageι]
  exact x.2

/-- The factorization of `AlgebraicGeometry.Scheme.Hom.toImage` for an open immersion through the
inverse image of that open in the scheme-theoretic closure. -/
public def toPreimage (V : X.Opens) : V.toScheme ⟶ (V.ι.imageι ⁻¹ᵁ V : (V.ι.image).Opens) :=
  IsOpenImmersion.lift (V.ι.imageι ⁻¹ᵁ V).ι V.ι.toImage (by simpa using range_toImage_le V)

/-- `Stacks.SchemeTheoreticImage.toPreimage` followed by the inclusion of the inverse image of `V`
is `AlgebraicGeometry.Scheme.Hom.toImage`. -/
@[reassoc]
public lemma toPreimage_ι (V : X.Opens) :
    toPreimage V ≫ (V.ι.imageι ⁻¹ᵁ V).ι = V.ι.toImage :=
  IsOpenImmersion.lift_fac _ _ _

/-- `Stacks.SchemeTheoreticImage.toPreimage` is a section of the restriction of
`AlgebraicGeometry.Scheme.Hom.imageι` over `V`. -/
public lemma toPreimage_imageι (V : X.Opens) :
    toPreimage V ≫ (V.ι.imageι ∣_ V) = 𝟙 _ := by
  rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, toPreimage_ι,
    V.ι.toImage_imageι, Category.id_comp]

/-- **The scheme-theoretic closure of an open subscheme is an isomorphism over that open.** The
restriction is a monomorphism because its composite with `V.ι` is one, and
`Stacks.SchemeTheoreticImage.toPreimage` is a section of it. -/
public theorem isIso_imageι_restrict (V : X.Opens) : IsIso (V.ι.imageι ∣_ V) := by
  have hm : Mono (V.ι.imageι ∣_ V) := by
    have : Mono ((V.ι.imageι ∣_ V) ≫ V.ι) := by rw [morphismRestrict_ι]; infer_instance
    exact mono_of_mono _ V.ι
  have : IsSplitEpi (V.ι.imageι ∣_ V) := ⟨⟨toPreimage V, toPreimage_imageι V⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- `Stacks.SchemeTheoreticImage.toPreimage` is an isomorphism. -/
public theorem isIso_toPreimage (V : X.Opens) : IsIso (toPreimage V) := by
  have := isIso_imageι_restrict V
  have h1 : IsIso (toPreimage V ≫ (V.ι.imageι ∣_ V)) := by
    rw [toPreimage_imageι]; infer_instance
  exact IsIso.of_isIso_comp_right (toPreimage V) (V.ι.imageι ∣_ V)

/-- The inclusion of the inverse image of an open subscheme `V` in its scheme-theoretic closure is
scheme-theoretically dominant. -/
public theorem isSchemeTheoreticallyDominant_preimage_imageι (V : X.Opens) [QuasiCompact V.ι] :
    IsSchemeTheoreticallyDominant (V.ι.imageι ⁻¹ᵁ V : (V.ι.image).Opens).ι := by
  have : IsSchemeTheoreticallyDominant V.ι.toImage := isSchemeTheoreticallyDominant_toImage V.ι
  refine ⟨le_bot_iff.mp ?_⟩
  rw [← V.ι.toImage.ker_eq_bot, ← toPreimage_ι V]
  exact Scheme.Hom.le_ker_comp _ _

/-- The inclusion of the inverse image of an open subscheme `V` with quasi-compact inclusion in its
scheme-theoretic closure is quasi-compact. -/
public theorem quasiCompact_preimage_imageι (V : X.Opens) [QuasiCompact V.ι] :
    QuasiCompact (V.ι.imageι ⁻¹ᵁ V : (V.ι.image).Opens).ι := by
  have := isIso_toPreimage V
  have hq : QuasiCompact (inv (toPreimage V) ≫ V.ι.toImage) := inferInstance
  rw [← toPreimage_ι V, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at hq
  exact hq

/-- **An open subscheme with quasi-compact inclusion is scheme-theoretically dense in its
scheme-theoretic closure.** -/
public theorem isSchemeTheoreticallyDense_preimage_imageι (V : X.Opens) [QuasiCompact V.ι] :
    Scheme.Opens.IsSchemeTheoreticallyDense (V.ι.imageι ⁻¹ᵁ V : (V.ι.image).Opens) :=
  have := isSchemeTheoreticallyDominant_preimage_imageι V
  have := quasiCompact_preimage_imageι V
  isSchemeTheoreticallyDense_of_dominant _

/-- `Stacks.SchemeTheoreticImage.isSchemeTheoreticallyDense_preimage_imageι` for an ideal sheaf
presented as the kernel of the inclusion of an open subscheme. -/
public theorem isSchemeTheoreticallyDense_preimage_subschemeι (I : X.IdealSheafData)
    (V : X.Opens) (hI : I = V.ι.ker) [QuasiCompact V.ι] :
    Scheme.Opens.IsSchemeTheoreticallyDense (I.subschemeι ⁻¹ᵁ V : (I.subscheme).Opens) := by
  subst hI
  exact isSchemeTheoreticallyDense_preimage_imageι V

/-- The morphism from an open subscheme `V` into the closed subscheme cut out by any ideal sheaf
equal to the kernel of `V.ι`. -/
public def toSubscheme (I : X.IdealSheafData) (V : X.Opens) (hI : I = V.ι.ker) :
    V.toScheme ⟶ I.subscheme :=
  IsClosedImmersion.lift I.subschemeι V.ι (by rw [Scheme.IdealSheafData.ker_subschemeι, hI])

/-- `Stacks.SchemeTheoreticImage.toSubscheme` followed by the closed immersion of the subscheme is
the inclusion of `V`. -/
@[reassoc]
public lemma toSubscheme_subschemeι (I : X.IdealSheafData) (V : X.Opens) (hI : I = V.ι.ker) :
    toSubscheme I V hI ≫ I.subschemeι = V.ι :=
  IsClosedImmersion.lift_fac _ _ _

/-- For an open subscheme with quasi-compact inclusion, `Stacks.SchemeTheoreticImage.toSubscheme`
is scheme-theoretically dominant. -/
public theorem isSchemeTheoreticallyDominant_toSubscheme (I : X.IdealSheafData) (V : X.Opens)
    (hI : I = V.ι.ker) [QuasiCompact V.ι] :
    IsSchemeTheoreticallyDominant (toSubscheme I V hI) := by
  subst hI
  have h : toSubscheme (V.ι.ker) V rfl = V.ι.toImage := by
    rw [← cancel_mono V.ι.imageι, toSubscheme_subschemeι, V.ι.toImage_imageι]
  rw [h]
  exact isSchemeTheoreticallyDominant_toImage V.ι

/-- **Two closed immersions sharing a scheme-theoretically dense open are isomorphic over it.**

The data is: a closed immersion `jj` into `BCJ'`, a closed immersion `mm : BCJ' ⟶ BCJ`, an
identification `GG : BCJ ≅ BCK`, a closed immersion `kk : XK ⟶ BCK` whose kernel is that of an
open `VK` of `BCK`, and a scheme-theoretically dominant `tau` from an open `VJ1` of `BCJ'` onto
the source of `jj` which `jj` takes back to the inclusion of `VJ1`. The open `PP` of `VJ1` is
scheme-theoretically dominant, and `aa`, `ww`, `vv` identify the inverse image of `VK` under
`GG` with `PP`.

The conclusion is the comparison isomorphism of the two closed subschemes, compatible with the
immersions. -/
public theorem exists_iso_of_isSchemeTheoreticallyDense {BCJ BCJ' BCK XJ XK : Scheme.{u}}
    (jj : XJ ⟶ BCJ') (mm : BCJ' ⟶ BCJ) (GG : BCJ ≅ BCK) (kk : XK ⟶ BCK)
    [IsClosedImmersion jj] [IsClosedImmersion mm] [IsClosedImmersion kk]
    (VJ1 : BCJ'.Opens) (VK : BCK.Opens)
    (tau : VJ1.toScheme ⟶ XJ) (htau : tau ≫ jj = VJ1.ι)
    [IsSchemeTheoreticallyDominant tau]
    (PP : VJ1.toScheme.Opens) [IsSchemeTheoreticallyDominant PP.ι]
    (hkk : kk.ker = VK.ι.ker)
    (aa : (GG.hom ⁻¹ᵁ VK).toScheme ⟶ BCJ') (haa : aa ≫ mm = (GG.hom ⁻¹ᵁ VK).ι)
    (ww : (GG.hom ⁻¹ᵁ VK).toScheme ⟶ PP.toScheme)
    (hww : ww ≫ PP.ι ≫ VJ1.ι = aa)
    (vv : PP.toScheme ⟶ (GG.hom ⁻¹ᵁ VK).toScheme)
    (hvv : vv ≫ (GG.hom ⁻¹ᵁ VK).ι = PP.ι ≫ VJ1.ι ≫ mm) :
    ∃ g : XJ ≅ XK, g.hom ≫ kk = jj ≫ mm ≫ GG.hom := by
  have hww' : ww ≫ PP.ι ≫ VJ1.ι ≫ mm = (GG.hom ⁻¹ᵁ VK).ι := by
    rw [← haa, ← hww]; simp only [Category.assoc]
  have hwv : ww ≫ vv = 𝟙 _ := by
    rw [← cancel_mono (GG.hom ⁻¹ᵁ VK).ι, Category.id_comp, Category.assoc, hvv, hww']
  have hva : vv ≫ aa = PP.ι ≫ VJ1.ι := by
    rw [← cancel_mono mm, Category.assoc, haa, hvv]; simp only [Category.assoc]
  have hmono : Mono (PP.ι ≫ VJ1.ι) := inferInstance
  have hvw : vv ≫ ww = 𝟙 _ := by
    rw [← cancel_mono (PP.ι ≫ VJ1.ι), Category.id_comp, Category.assoc, hww, hva]
  have hvvIso : IsIso vv := ⟨⟨ww, hvw, hwv⟩⟩
  have hu : (PP.ι ≫ VJ1.ι ≫ mm ≫ GG.hom).ker = VK.ι.ker := by
    have h1 : PP.ι ≫ VJ1.ι ≫ mm ≫ GG.hom = (vv ≫ (GG.hom ∣_ VK)) ≫ VK.ι := by
      conv_rhs => rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hvv]
      simp only [Category.assoc]
    rw [h1, Scheme.Hom.ker_comp_of_isIso]
  have hd : (PP.ι ≫ VJ1.ι ≫ mm ≫ GG.hom).ker = (jj ≫ mm ≫ GG.hom).ker := by
    have h2 : PP.ι ≫ VJ1.ι ≫ mm ≫ GG.hom = (PP.ι ≫ tau) ≫ (jj ≫ mm ≫ GG.hom) := by
      conv_lhs => rw [← htau]
      simp only [Category.assoc]
    rw [h2, Scheme.Hom.ker_comp, (PP.ι ≫ tau).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hker : (jj ≫ mm ≫ GG.hom).ker = kk.ker := by rw [← hd, hu, hkk]
  have : IsClosedImmersion (jj ≫ mm ≫ GG.hom) := inferInstance
  have ht : IsClosedImmersion.lift kk (jj ≫ mm ≫ GG.hom) hker.ge ≫ kk = jj ≫ mm ≫ GG.hom :=
    IsClosedImmersion.lift_fac _ _ _
  have : IsIso (IsClosedImmersion.lift kk (jj ≫ mm ≫ GG.hom) hker.ge) :=
    IsClosedImmersion.isIso_of_ker_eq (jj ≫ mm ≫ GG.hom) kk _ ht hker
  exact ⟨asIso (IsClosedImmersion.lift kk (jj ≫ mm ≫ GG.hom) hker.ge), ht⟩

end Stacks.SchemeTheoreticImage

end
