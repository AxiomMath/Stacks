module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.LiftSize
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.RepresentableFromAffineEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.SchemeThickening
import StacksFrontier.AlgebraicGeometry.FormalSpace.StageThickening

/-!
# The dependent product of an étale chart along a representable thickening

Let `S` be a scheme contained in a big fppf site `B`, let `ι : I ⟶ X` be a morphism of fppf
sheaves which is a thickening after base change along every affine point of `X`, and let
`c : h_U ⟶ I` be a chart of `I` which is étale and represented by objects of the site after base
change along every point of `I`, with a size bound. Then the dependent product `Π_ι h_U ⟶ X`
(`AlgebraicGeometry.FormalSpace.DependentProduct.liftAlong`) is representable by algebraic spaces
and étale: over an affine point `T ⟶ X` it is the étale lift, across the thickening
`T ×_X I ⟶ T`, of the étale object `(T ×_X I) ×_I U` (Stacks 039R), by the base change formula
for the dependent product.

This is how an étale chart of one stage of a system of algebraic spaces along thickenings is
transported to the later stages and to the colimit (the step of the proof of Stacks 0AIU which
cites Stacks 05ZH).

## Main results

* `AlgebraicGeometry.FormalSpace.DependentProduct.etaleAffinePullbackBounded_liftAlongBase`:
  the base changes of `Π_ι h_U ⟶ X` along affine points are étale objects of bounded size.
* `AlgebraicGeometry.FormalSpace.DependentProduct.isRepresentableEtale_liftAlongBase`: hence
  `Π_ι h_U ⟶ X` is representable by algebraic spaces and étale.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

namespace AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The hypothesis on `ι`: its base change along every affine point is a thickening of objects
of the site. -/
abbrev IsAffineThickeningOver {I X : FppfSheaf B S hS} (ι : I ⟶ X) : Prop :=
  ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
    ∀ t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ X,
    ∃ (T₀ : BigFppfOver B S hS) (k : T₀ ⟶ T)
      (i₀ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T₀ ⟶ I),
      IsPullback ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k) i₀ t ι ∧
      Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k)

/-- The hypothesis on `c`: its base change along every point of `I` is an étale object of the
site, of size at most `g₀` of the size of the point. -/
abbrev IsEtaleChartBounded {I : FppfSheaf B S hS} {U : BigFppfOver B S hS}
    (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ I)
    (g₀ : Cardinal.{u} → Cardinal.{u}) : Prop :=
  ∀ (T₀ : BigFppfOver B S hS) (x : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T₀ ⟶ I),
    ∃ (L₀ : BigFppfOver B S hS) (q₀ : L₀ ⟶ T₀)
      (r₀ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj L₀ ⟶
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U),
      IsPullback ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q₀) r₀ x c ∧
      Etale ((BigFppfOver.toScheme B S hS).map q₀) ∧
      ((BigFppfOver.toScheme B S hS).obj L₀).size ≤ g₀ ((BigFppfOver.toScheme B S hS).obj T₀).size

/-- **The base change of the dependent product of an étale chart along a point whose base change
to the thickening is given.** Let `ι : I ⟶ X`, `c : h_U ⟶ I`, let `t : h_T ⟶ X` be a point with
`h_T ×_X I = h_{T₀}` along a thickening `k : T₀ ⟶ T`, and let `L₀` represent the base change of
`c` to `T₀`, étale over `T₀`. Then the base change of `Π_ι h_U ⟶ X` along `t` is represented by
the étale lift `L` of `L₀` across `k`. -/
theorem exists_isPullback_liftAlongBase_of_isThickening {I X : FppfSheaf B S hS} (ι : I ⟶ X)
    {U : BigFppfOver B S hS} (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ I)
    {T T₀ : BigFppfOver B S hS} (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ X)
    (k : T₀ ⟶ T) (i₀ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T₀ ⟶ I)
    (hpb : IsPullback ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k) i₀ t ι)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    {L₀ : BigFppfOver B S hS} (q₀ : L₀ ⟶ T₀)
    (r₀ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj L₀ ⟶
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U)
    (hpb' : IsPullback ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q₀) r₀ i₀ c)
    (hq₀ : Etale ((BigFppfOver.toScheme B S hS).map q₀)) :
    ∃ (L : BigFppfOver B S hS) (q : L ⟶ T) (c₀ : L₀ ⟶ L)
      (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj L ⟶ liftAlong B S hS ι c),
      IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map q)
        (liftAlongBase B S hS ι c) t ∧
      Etale ((BigFppfOver.toScheme B S hS).map q) ∧ IsPullback c₀ q₀ q k := by
  obtain ⟨L, q, c₀, hq, hsq, -, φ, hφ⟩ := exists_iso_liftAlong_of_isThickening k hk q₀ hq₀
  have hbc := isPullback_liftAlongBaseChange r₀ (isSectionwisePullback_of_isPullback B S hS hpb)
    (isSectionwisePullback_of_isPullback B S hS hpb') hpb.w hpb'.w.symm
  refine ⟨L, q, c₀, φ.hom ≫ liftAlongBaseChange r₀ (isSectionwisePullback_of_isPullback B S hS hpb)
    hpb'.w.symm, ?_, hq, hsq⟩
  refine hbc.of_iso φ.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp
  · rw [← hφ]; simp

/-- A base change of a thickening of objects of the site is a thickening. -/
private theorem isThickening_map_of_isPullback {A₀ A T T₀ : BigFppfOver B S hS} {f : T₀ ⟶ T}
    {g : T₀ ⟶ A₀} {h : T ⟶ A} {k : A₀ ⟶ A} (hsq : IsPullback f g h k)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k)) :
    Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map f) := by
  have := hasPullbacks_bigFppfOver B S hS
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have := AlgebraicGeometry.FormalSpace.isThickening_isStableUnderBaseChange.{u}
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback (hsq.flip.map _) hk

/-- **The base changes of the dependent product of an étale chart along affine points.** -/
theorem etaleAffinePullbackBounded_liftAlongBase {I X : FppfSheaf B S hS} (ι : I ⟶ X)
    {U : BigFppfOver B S hS} (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ I)
    (hι : IsAffineThickeningOver ι) {g₀ : Cardinal.{u} → Cardinal.{u}} (hg₀ : Monotone g₀)
    (hc : IsEtaleChartBounded c g₀) :
    EtaleAffinePullbackBounded B S hS (liftAlongBase B S hS ι c) (fun κ ↦ max (g₀ κ) κ) := by
  intro T hT t
  set F := BigFppfOver.toScheme B S hS with hF
  obtain ⟨T₀, k, i₀, hpb, hk⟩ := hι T hT t
  obtain ⟨L₀, q₀, r₀, hpb', hq₀, hL₀⟩ := hc T₀ i₀
  obtain ⟨L, q, c₀, r, hr, hq, hsq⟩ :=
    exists_isPullback_liftAlongBase_of_isThickening ι c t k i₀ hpb hk q₀ r₀ hpb' hq₀
  refine ⟨L, q, r, hr, hq, ?_⟩
  -- the size of the lift
  have := hasPullbacks_bigFppfOver B S hS
  have hth := isThickening_map_of_isPullback hsq hk
  have := hth.1
  have := hk.1
  have : Etale (F.map q) := hq
  have hT₀ : (F.obj T₀).size ≤ (F.obj T).size := Scheme.size_le_of_mono_quasiCompact (F.map k)
  refine (Scheme.size_le_of_etale_of_isClosedImmersion (F.map q) (F.map c₀) hth.2).trans ?_
  exact max_le_max (hL₀.trans (hg₀ hT₀)) le_rfl

/-- **The dependent product of an étale chart along a representable thickening is
representable by algebraic spaces and étale.** -/
theorem isRepresentableEtale_liftAlongBase {I X : FppfSheaf B S hS} (ι : I ⟶ X)
    {U : BigFppfOver B S hS} (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ I)
    (hι : IsAffineThickeningOver ι) {g₀ : Cardinal.{u} → Cardinal.{u}} (hg₀ : Monotone g₀)
    (hg₀c : ∀ κ, κ < B.cutoff → g₀ κ < B.cutoff) (hc : IsEtaleChartBounded c g₀) :
    IsRepresentableEtale B S hS (liftAlongBase B S hS ι c) :=
  isRepresentableEtale_of_etale_over_affinePoints B S hS _
    (fun _ _ h ↦ max_le_max (hg₀ h) h) (fun κ hκ ↦ max_lt (hg₀c κ hκ) hκ)
    (etaleAffinePullbackBounded_liftAlongBase ι c hι hg₀ hc)

/-- **The dependent product along a composite with a monomorphism, base changed along the
monomorphism, is the dependent product along the first factor.** -/
theorem isPullback_liftAlong_comp_mono {I M X : FppfSheaf B S hS} (β : I ⟶ M) (σ : M ⟶ X)
    [Mono σ] {W : FppfSheaf B S hS} (c : W ⟶ I) :
    IsPullback (liftAlongBaseChange (𝟙 W) (isSectionwisePullback_of_isPullback B S hS
        ((IsPullback.of_id_snd (f := β)).comp_mono σ))
        (by rw [Category.id_comp, Category.comp_id]))
      (liftAlongBase B S hS β c) (liftAlongBase B S hS (β ≫ σ) c) σ := by
  refine isPullback_liftAlongBaseChange (𝟙 _) _
    (isSectionwisePullback_of_isPullback B S hS (IsPullback.of_id_snd (f := c)))
    (Category.id_comp _).symm (by rw [Category.id_comp, Category.comp_id])

/-- **The source of a morphism representable by algebraic spaces into an algebraic space is an
algebraic space**: the base change of an étale atlas of the target is an étale atlas of the
source, an algebraic space by representability, surjecting onto it. -/
theorem isAlgebraicSpaceULift_of_isRepresentableByAlgebraicSpacesULift
    {U X : FppfSheaf B S hS} (Φ : U ⟶ X)
    (hΦ : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS Φ.hom)
    (hX : Space.IsAlgebraicSpaceULift.{u + 1} B S hS X.obj) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS U.obj := by
  obtain ⟨V, f, hfS, hfE⟩ := hX.exists_atlas
  have hb := IsPullback.of_hasPullback f Φ.hom
  refine Space.isAlgebraicSpaceULift_of_relative_surjective_etale B S hS U.property (hΦ V f)
    (pullback.snd f Φ.hom) ?_ ?_
  · exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hb hfS
  · exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hb hfE

/-- **A base change of a thickening of the site is a thickening over every point.** If
`β : E₀ ⟶ E₁` is a base change of `h_k` for a thickening `k : A₀ ⟶ A` of objects of the site,
then the base change of `β` along any point `h_T ⟶ E₁` is the thickening `T ×_A A₀ ⟶ T`. -/
theorem isAffineThickeningOver_of_isPullback {E₀ E₁ : FppfSheaf B S hS} {A₀ A : BigFppfOver B S hS}
    (β : E₀ ⟶ E₁) (p₀ : E₀ ⟶ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj A₀)
    (p₁ : E₁ ⟶ (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj A) (k : A₀ ⟶ A)
    (hsq : IsPullback β p₀ p₁ ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k))
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k)) :
    IsAffineThickeningOver β := by
  intro T _ t
  have := hasPullbacks_bigFppfOver B S hS
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  obtain ⟨t', ht'⟩ : ∃ t' : T ⟶ A,
      (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map t' = t ≫ p₁ :=
    ⟨_, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map_preimage (t ≫ p₁)⟩
  have hP : IsPullback ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (pullback.fst t' k))
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (pullback.snd t' k)) (t ≫ p₁)
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map k) := by
    rw [← ht']; exact (IsPullback.of_hasPullback t' k).map _
  refine ⟨pullback t' k, pullback.fst t' k,
    hsq.lift ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (pullback.fst t' k) ≫ t)
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map (pullback.snd t' k))
      (by rw [Category.assoc]; exact hP.w), ?_, ?_⟩
  · refine (IsPullback.of_right ?_ (hsq.lift_fst _ _ _) hsq.flip).flip
    rw [hsq.lift_snd]
    exact hP.flip
  · exact isThickening_map_of_isPullback (IsPullback.of_hasPullback t' k) hk

/-- A morphism whose base changes along points are thickenings is a thickening over every
affine point. -/
theorem isAffineThickeningOver_of_relative {I X : FppfSheaf B S hS} (ι : I ⟶ X)
    (h : (MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (BigFppfOver.topology B S hS).uliftYoneda.{u + 1} ι) :
    IsAffineThickeningOver ι := by
  intro T _ t
  obtain ⟨T₀, k, i₀, hpb⟩ := h.1 t
  exact ⟨T₀, k, i₀, hpb.flip, h.2 t i₀ k hpb⟩

/-- **The dependent product along a monomorphism, base changed along it.** If `β ≫ σ = i` with
`σ` a monomorphism, the base change of `Π_i W` along `σ` is `Π_β W`. -/
theorem isPullback_liftAlong_of_eq_comp {I M X : FppfSheaf B S hS} (β : I ⟶ M) (σ : M ⟶ X)
    [Mono σ] (i : I ⟶ X) (hi : β ≫ σ = i) {W : FppfSheaf B S hS} (c : W ⟶ I) :
    ∃ r : liftAlong B S hS β c ⟶ liftAlong B S hS i c,
      IsPullback r (liftAlongBase B S hS β c) (liftAlongBase B S hS i c) σ := by
  subst hi
  exact ⟨_, isPullback_liftAlong_comp_mono β σ c⟩

/-- **The dependent product along the identity is the sheaf itself.** -/
theorem nonempty_iso_liftAlong_id {I W : FppfSheaf B S hS} (c : W ⟶ I) :
    Nonempty (W ≅ liftAlong B S hS (𝟙 I) c) := by
  have hi : ∀ T : BigFppfOver B S hS,
      Function.Injective ((𝟙 I : I ⟶ I).hom.app (Opposite.op T)) :=
    fun _ _ _ h ↦ h
  have h := isPullback_liftAlongSection B S hS hi (p := c)
  have := h.isIso_fst_of_isIso
  exact ⟨asIso (liftAlongSection B S hS hi)⟩

end AlgebraicGeometry.FormalSpace.DependentProduct

end
