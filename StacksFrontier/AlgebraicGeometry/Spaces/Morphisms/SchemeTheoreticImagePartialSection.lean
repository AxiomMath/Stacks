module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# The scheme-theoretic image of a section over a quasi-compact open subspace

Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over a scheme `S` contained in a
big fppf site `B`, let `V ⊆ Y` be an open subspace whose inclusion `V ⟶ Y` is quasi-compact,
and let `s : V ⟶ X` be a section of `f` over `V`, that is `s ≫ f = 𝟙 V`.  Write `Y'` for the
scheme-theoretic image of `s` of Stacks 082X, a closed subspace of `X`, and give it the
morphism `Y' ⟶ Y` obtained by composing its inclusion with `f`.

## Main results

* `AlgebraicGeometry.Space.isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section`
  is **Stacks 0CP3**: `Y' ⟶ Y` is an isomorphism over `V`.  "Isomorphism over `V`" is stated
  as the second projection `Y' ×_Y V ⟶ V` of the base change along `V ⟶ Y` being an
  isomorphism; no claim is made about `Y' ⟶ Y` away from `V`.

## Implementation notes

The notion of scheme-theoretic image used here is the one of Stacks 082X carried by
`AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor`, the smallest closed subspace of the
target through which the morphism factors.  The bundled
`AlgebraicGeometry.Space.schemeTheoreticImage` packages the same subfunctor with the proof
that it is a closed subspace, so the statement is unchanged if one uses it instead.

The proof follows the source.  Put `P = X ×_Y V`, the restriction of `X` over `V`, with
projections `pr₁ : P ⟶ X`, an open immersion and hence étale, and `pr₂ : P ⟶ V`, a separated
morphism by Stacks 03KL since `f` is separated.  The section `s` lifts to `t : V ⟶ P` with
`t ≫ pr₁ = s` and `t ≫ pr₂ = 𝟙 V`, so `t` is a section of a separated morphism and therefore
a closed immersion by part (3) of Stacks 03KP; its range is then a closed subspace of `P`, so
the scheme-theoretic image of `t` is its range.

Separatedness of `f` also makes `f` quasi-separated, so Stacks 03KS turns quasi-compactness of
`V ⟶ Y`, which is `s ≫ f`, into quasi-compactness of `s`.  That is the hypothesis of part (3)
of Stacks 082Z, applied to `s` and the étale morphism `pr₁`: the scheme-theoretic image of the
base change `V ×_X P ⟶ P` of `s` is the inverse image along `pr₁` of `Y'`.  Since `pr₁` is a
monomorphism, that base change has the same range as `t`, hence the same scheme-theoretic
image.  Together, `pr₁⁻¹(Y')` is the range of `t`.

Finally `Y' ×_Y V` maps monomorphically to `P` by `m`, with `m ≫ pr₁` factoring through `Y'`,
so the range of `m` lies in `pr₁⁻¹(Y')`, the range of `t`; and `pr₂` restricted to the range
of `t` is an isomorphism, `t` being a section of `pr₂`.  Hence the projection `Y' ×_Y V ⟶ V`,
which is `m ≫ pr₂`, is a monomorphism.  It is also a split epimorphism, the factorization of
`s` through `Y'` providing a section, and a split epimorphism which is a monomorphism is an
isomorphism.

## References

* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
* [Stacks Project, Tag 03KS](https://stacks.math.columbia.edu/tag/03KS)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 0CP3](https://stacks.math.columbia.edu/tag/0CP3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section PartialSection

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasPullbacks_presheaf_SchemeTheoreticImagePartialSection :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_SchemeTheoreticImagePartialSection
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Discrete limits of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance hasLimitsOfShape_discrete_presheaf_SchemeTheoreticImagePartialSection
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- The scheme-theoretic image of a morphism depends only on the range of that morphism, being
the infimum of the closed subspaces of the target containing it. -/
private theorem schemeTheoreticImageSubfunctor_congr'
    {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y) (f' : X' ⟶ Y)
    (h : Subfunctor.range f = Subfunctor.range f') :
    schemeTheoreticImageSubfunctor B S hS f = schemeTheoreticImageSubfunctor B S hS f' := by
  simp only [schemeTheoreticImageSubfunctor, h]

/-- The scheme-theoretic image of a closed immersion with algebraic source is its range: the
range is a closed subspace through which the morphism factors, so minimality of the image
gives one inclusion and the factorization gives the other. -/
private theorem schemeTheoreticImageSubfunctor_eq_range_of_isClosedImmersion'
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    schemeTheoreticImageSubfunctor B S hS f = Subfunctor.range f :=
  le_antisymm
    (schemeTheoreticImageSubfunctor_le B S hS f
      (isClosedSubspace_range_of_isClosedImmersion B S hS f hX hf) le_rfl)
    (range_le_schemeTheoreticImageSubfunctor B S hS f)

/-- If a morphism `q` composed with `p` factors through a subfunctor `Z` of the target of `p`,
then the range of `q` lies in the inverse image of `Z` along `p`. -/
private theorem range_le_preimage_of_factor' {F F' G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (q : F ⟶ F') (p : F' ⟶ G) (Z : Subfunctor G) (r : F ⟶ Z.toFunctor)
    (h : q ≫ p = r ≫ Z.ι) :
    Subfunctor.range q ≤ Z.preimage p := by
  rw [← Subfunctor.image_le_iff, ← Subfunctor.range_comp, h]
  simpa only [Subfunctor.range_ι] using Subfunctor.range_comp_le r Z.ι

/-- **Stacks 0CP3.** Let `f : X ⟶ Y` be a separated morphism of algebraic spaces over `S`, let
`V ⊆ Y` be an open subspace whose inclusion into `Y` is quasi-compact, and let `s : V ⟶ X`
satisfy `s ≫ f = 𝟙 V`.  Let `Y'` be the scheme-theoretic image of `s`, a closed subspace of
`X`, and let `Y' ⟶ Y` be its inclusion followed by `f`.  Then **`Y' ⟶ Y` is an isomorphism
over `V`**: the projection `Y' ×_Y V ⟶ V` of its base change along `V ⟶ Y` is an
isomorphism. -/
@[stacks 0CP3]
theorem isIso_pullback_snd_schemeTheoreticImageSubfunctor_comp_of_section
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hf : IsSeparated B S hS f)
    (V : Subfunctor Y) (hV : IsOpenSubspace B S hS V)
    (hVqc : IsQuasiCompact B S hS V.ι)
    (s : V.toFunctor ⟶ X) (hs : s ≫ f = V.ι) :
    IsIso (pullback.snd ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι) := by
  classical
  -- `P = X ×_Y V` is the restriction of `X` over `V`.
  have hP : IsAlgebraicSpace B S hS (pullback f V.ι) :=
    isAlgebraicSpace_pullback B S hS f V.ι hX hV.1 hY
  -- The section `s` lifts to a section `t` of the projection `P ⟶ V`.
  let t : V.toFunctor ⟶ pullback f V.ι :=
    pullback.lift s (𝟙 V.toFunctor) (by simpa using hs)
  have htfst : t ≫ pullback.fst f V.ι = s := pullback.lift_fst _ _ _
  have htsnd : t ≫ pullback.snd f V.ι = 𝟙 V.toFunctor := pullback.lift_snd _ _ _
  -- `t` is a section of a separated morphism, hence a closed immersion (Stacks 03KP (3)).
  have htci : IsClosedImmersion B S hS t :=
    isClosedImmersion_of_isSeparated_of_section B S hS (pullback.snd f V.ι)
      (isSeparated_pullback B S hS f V.ι hf) t htsnd
  have : Mono t := mono_of_section B S hS (pullback.snd f V.ι) t htsnd
  -- `s` is quasi-compact: `s ≫ f = V.ι` is, and `f` is quasi-separated (Stacks 03KS).
  have hsqc : IsQuasiCompact B S hS s :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS s f hV.1 hY
      (by rw [hs]; exact hVqc) (isQuasiSeparated_of_isSeparated B S hS hf)
  -- The projection `P ⟶ X` is an open immersion, hence étale, and a monomorphism.
  have hfstOI : IsOpenImmersion B S hS (pullback.fst f V.ι) :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      (IsPullback.of_hasPullback f V.ι).flip hV.2
  have : Mono (pullback.fst f V.ι) := mono_of_presheaf_isOpenImmersion hfstOI
  have hfstEtale : IsEtale B S hS (pullback.fst f V.ι) :=
    isEtale_of_presheaf_etale B S hS (presheaf_etale_of_isOpenImmersion B S hS hfstOI)
  -- Stacks 082Z (3) for the quasi-compact `s` and the étale `pullback.fst f V.ι`.
  have h082Z : schemeTheoreticImageSubfunctor B S hS
        (pullback.snd s (pullback.fst f V.ι)) =
      (schemeTheoreticImageSubfunctor B S hS s).preimage (pullback.fst f V.ι) :=
    schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' B S hS
      s (pullback.fst f V.ι) hV.1 hX hP hsqc hfstEtale
  -- That base change of `s` has the same range as `t`.
  have hgraph : pullback.fst s (pullback.fst f V.ι) ≫ t =
      pullback.snd s (pullback.fst f V.ι) := by
    refine (cancel_mono (pullback.fst f V.ι)).1 ?_
    rw [Category.assoc, htfst]
    exact pullback.condition
  have hrange : Subfunctor.range (pullback.snd s (pullback.fst f V.ι)) =
      Subfunctor.range t := by
    refine le_antisymm ?_ ?_
    · rw [← hgraph]
      exact Subfunctor.range_comp_le _ _
    · rw [show t = pullback.lift (𝟙 V.toFunctor) t (by rw [Category.id_comp, htfst]) ≫
          pullback.snd s (pullback.fst f V.ι) from (pullback.lift_snd _ _ _).symm]
      exact Subfunctor.range_comp_le _ _
  -- Hence the inverse image of `Y'` in `P` is the range of `t`.
  have hpre : (schemeTheoreticImageSubfunctor B S hS s).preimage (pullback.fst f V.ι) =
      Subfunctor.range t :=
    h082Z.symm.trans
      ((schemeTheoreticImageSubfunctor_congr' B S hS _ t hrange).trans
        (schemeTheoreticImageSubfunctor_eq_range_of_isClosedImmersion' B S hS hV.1 t htci))
  -- The comparison `m : Y' ×_Y V ⟶ P`.
  let m : pullback ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι ⟶ pullback f V.ι :=
    pullback.lift
      (pullback.fst ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι ≫
        (schemeTheoreticImageSubfunctor B S hS s).ι)
      (pullback.snd ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι)
      (by rw [Category.assoc]; exact pullback.condition)
  have hmfst : m ≫ pullback.fst f V.ι =
      pullback.fst ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι ≫
        (schemeTheoreticImageSubfunctor B S hS s).ι := pullback.lift_fst _ _ _
  have hmsnd : m ≫ pullback.snd f V.ι =
      pullback.snd ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι :=
    pullback.lift_snd _ _ _
  have hmmono : Mono m := mono_of_mono_fac hmfst
  -- The range of `m` lies in the range of `t`.
  have hmle : Subfunctor.range m ≤ Subfunctor.range t := by
    rw [← hpre]
    exact range_le_preimage_of_factor' B S hS m (pullback.fst f V.ι) _
      (pullback.fst ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι) hmfst
  -- So `m`, and with it the projection to `V`, factors through the range of `t`.
  have hm' : Subfunctor.lift m hmle ≫ (Subfunctor.range t).ι = m := Subfunctor.lift_ι _ _
  have : Mono (Subfunctor.lift m hmle) := mono_of_mono_fac hm'
  -- The projection `P ⟶ V` restricted to the range of `t` is an isomorphism.
  have hkey : Subfunctor.toRange t ≫ ((Subfunctor.range t).ι ≫ pullback.snd f V.ι) =
      𝟙 V.toFunctor := by
    rw [← Category.assoc, Subfunctor.toRange_ι, htsnd]
  have : IsIso (Subfunctor.toRange t ≫
      ((Subfunctor.range t).ι ≫ pullback.snd f V.ι)) := by
    rw [hkey]; infer_instance
  have : IsIso ((Subfunctor.range t).ι ≫ pullback.snd f V.ι) :=
    IsIso.of_isIso_comp_left (Subfunctor.toRange t) _
  -- Therefore the projection `Y' ×_Y V ⟶ V` is a monomorphism.
  have hproj : pullback.snd ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι =
      Subfunctor.lift m hmle ≫ ((Subfunctor.range t).ι ≫ pullback.snd f V.ι) := by
    rw [← Category.assoc, hm', hmsnd]
  have : Mono (pullback.snd ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι) := by
    have hm1 : Mono (Subfunctor.lift m hmle) := mono_of_mono_fac hm'
    have hm2 : Mono ((Subfunctor.range t).ι ≫ pullback.snd f V.ι) := IsIso.mono_of_iso _
    rw [hproj]; exact @mono_comp _ _ _ _ _ _ hm1 _ hm2
  -- It is also split by the factorization of `s` through `Y'`.
  let σ : V.toFunctor ⟶ pullback ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι :=
    pullback.lift (toSchemeTheoreticImage B S hS s) (𝟙 V.toFunctor)
      (by rw [← Category.assoc, toSchemeTheoreticImage_ι, hs, Category.id_comp])
  have hσ : σ ≫ pullback.snd ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι =
      𝟙 V.toFunctor := pullback.lift_snd _ _ _
  have : IsSplitEpi (pullback.snd ((schemeTheoreticImageSubfunctor B S hS s).ι ≫ f) V.ι) :=
    ⟨⟨σ, hσ⟩⟩
  exact isIso_of_mono_of_isSplitEpi _

end PartialSection

end AlgebraicGeometry.Space

end
