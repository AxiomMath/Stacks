module

public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProductModuleLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.QcqsOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward

/-!
# Presentations of a quasi-compact quasi-separated base change by schemes

For a quasi-compact and quasi-separated base change `Y₀ = h_{T i₀} ⨯ X₀` of an algebraic space,
this file fixes an affine scheme `U₀` étale and surjective over `Y₀`, its kernel pair `R₀`, a
quasi-compact scheme, and the scheme `K₀ = R₀ ×_{U₀} R₀` of composable pairs of arrows of the
groupoid `(U₀, R₀)`, also quasi-compact. Their base changes along the stages of a limit are
presentations of the base changes `h_{T j} ⨯ X₀`.

## Main definitions

* `AlgebraicGeometry.Space.ProductChartData`: the data `(U₀, R₀, K₀)` and their maps.

## Main results

* `AlgebraicGeometry.Space.nonempty_productChartData`: such data exist for a quasi-compact and
  quasi-separated base change.
* `AlgebraicGeometry.Space.isPullback_productChartPairMap_of_isPullback`: base change along
  `V ⟶ T i₀` preserves a cartesian square of schemes over `h_{T i₀} ⨯ X₀`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (X₀ : AlgebraicSpaces B S hS)

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ProductChartPresentation :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- A cospan of presheaves on the big fppf site has a limit. -/
local instance (priority := high) hasPullback_presheaf_ProductChartPresentation
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Base change of cartesian squares -/

section BaseChange

variable {T₀ : BigFppfOver B S hS} {U₀ R₁ R₂ K : BigFppfOver B S hS}
  (a : yoneda.obj U₀ ⟶ (productSpace X₀ T₀).1)

/-- The morphism of charts `productChartPairMap X₀ a g a' hg k` is the base change along
`k : V ⟶ T₀` of `g`, viewed as a morphism of schemes over `T₀`. -/
theorem productChartPairMap_eq_overPullback {R₀ : BigFppfOver B S hS} (g : R₀ ⟶ U₀)
    (a' : yoneda.obj R₀ ⟶ (productSpace X₀ T₀).1) (hg : yoneda.map g ≫ a = a')
    {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    productChartPairMap X₀ a g a' hg k =
      (Over.forget V).map ((Over.pullback k).map (Over.homMk g
        (productChartBase_comp X₀ a g a' hg).symm :
          Over.mk (productChartBase X₀ a') ⟶ Over.mk (productChartBase X₀ a))) := by
  apply pullback.hom_ext
  · simp only [productChartPairMap, pullback.lift_fst]
    exact (pullback.lift_fst _ _ _).symm
  · simp only [productChartPairMap, pullback.lift_snd, Category.comp_id]
    exact (pullback.lift_snd _ _ _).symm

/-- **Base change of a cartesian square of schemes over `h_{T₀} ⨯ X₀`** along `k : V ⟶ T₀` is
cartesian. -/
theorem isPullback_productChartPairMap_of_isPullback {p : K ⟶ R₁} {q : K ⟶ R₂} {s : R₁ ⟶ U₀}
    {t : R₂ ⟶ U₀} (h : IsPullback p q s t)
    (a₁ : yoneda.obj R₁ ⟶ (productSpace X₀ T₀).1) (hs : yoneda.map s ≫ a = a₁)
    (a₁' : yoneda.obj R₂ ⟶ (productSpace X₀ T₀).1) (ht : yoneda.map t ≫ a = a₁')
    (a₂ : yoneda.obj K ⟶ (productSpace X₀ T₀).1) (hp : yoneda.map p ≫ a₁ = a₂)
    (hq : yoneda.map q ≫ a₁' = a₂) {V : BigFppfOver B S hS} (k : V ⟶ T₀) :
    IsPullback (productChartPairMap X₀ a₁ p a₂ hp k) (productChartPairMap X₀ a₁' q a₂ hq k)
      (productChartPairMap X₀ a s a₁ hs k) (productChartPairMap X₀ a t a₁' ht k) := by
  have hO : IsPullback (Over.homMk p (productChartBase_comp X₀ a₁ p a₂ hp).symm :
        Over.mk (productChartBase X₀ a₂) ⟶ Over.mk (productChartBase X₀ a₁))
      (Over.homMk q (productChartBase_comp X₀ a₁' q a₂ hq).symm :
        Over.mk (productChartBase X₀ a₂) ⟶ Over.mk (productChartBase X₀ a₁'))
      (Over.homMk s (productChartBase_comp X₀ a s a₁ hs).symm :
        Over.mk (productChartBase X₀ a₁) ⟶ Over.mk (productChartBase X₀ a))
      (Over.homMk t (productChartBase_comp X₀ a t a₁' ht).symm :
        Over.mk (productChartBase X₀ a₁') ⟶ Over.mk (productChartBase X₀ a)) :=
    IsPullback.of_map (Over.forget T₀) (Over.OverMorphism.ext h.w) h
  simpa only [productChartPairMap_eq_overPullback] using
    (hO.map (Over.pullback k)).map (Over.forget V)

end BaseChange

/-! ### The presentation data -/

variable {I : Type u} [Category.{u} I] (T : I ⥤ BigFppfOver B S hS) (i₀ : I)

/-- An affine étale surjective chart `a₀ : h_{U₀} ⟶ h_{T i₀} ⨯ X₀`, its kernel pair
`t₀, s₀ : R₀ ⟶ U₀` with `R₀` quasi-compact, and the composable pairs `p₀, q₀ : K₀ ⟶ R₀`
(`p₀ ≫ s₀ = q₀ ≫ t₀`) with their composite `c₀ : K₀ ⟶ R₀`, `K₀` quasi-compact. -/
structure ProductChartData where
  /-- The affine chart. -/
  U₀ : BigFppfOver B S hS
  /-- The chart morphism. -/
  a₀ : yoneda.obj U₀ ⟶ (productSpace X₀ (T.obj i₀)).1
  isAffine : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)
  etale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf a₀
  surjective : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)).presheaf a₀
  /-- The kernel pair. -/
  R₀ : BigFppfOver B S hS
  compactR : CompactSpace ((BigFppfOver.toScheme B S hS).obj R₀)
  /-- The target of an arrow. -/
  t₀ : R₀ ⟶ U₀
  /-- The source of an arrow. -/
  s₀ : R₀ ⟶ U₀
  isPullback : IsPullback (yoneda.map t₀) (yoneda.map s₀) a₀ a₀
  /-- The composable pairs. -/
  K₀ : BigFppfOver B S hS
  compactK : CompactSpace ((BigFppfOver.toScheme B S hS).obj K₀)
  /-- The arrow applied second. -/
  p₀ : K₀ ⟶ R₀
  /-- The arrow applied first. -/
  q₀ : K₀ ⟶ R₀
  /-- The composite arrow. -/
  c₀ : K₀ ⟶ R₀
  isPullbackK : IsPullback p₀ q₀ s₀ t₀
  c₀_t : c₀ ≫ t₀ = p₀ ≫ t₀
  c₀_s : c₀ ≫ s₀ = q₀ ≫ s₀

/-- A representable object isomorphic to a pullback of representables is the vertex of a cartesian
square whose projections come from morphisms of schemes. -/
private theorem isPullback_yoneda_map_preimage_of_iso {P Q K : BigFppfOver B S hS} {Z}
    (f : yoneda.obj P ⟶ Z) (g : yoneda.obj Q ⟶ Z) (e : yoneda.obj K ≅ pullback f g) :
    IsPullback (yoneda.map (Yoneda.fullyFaithful.preimage (e.hom ≫ pullback.fst f g)))
      (yoneda.map (Yoneda.fullyFaithful.preimage (e.hom ≫ pullback.snd f g))) f g := by
  rw [Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage]
  exact IsPullback.of_iso_pullback ⟨by rw [Category.assoc, Category.assoc, pullback.condition]⟩
    e rfl rfl

/-- **Presentation data exist** for a quasi-compact and quasi-separated base change. -/
theorem nonempty_productChartData (hZ : B.Contains (⊤_ Scheme.{u}))
    (hqc : IsQuasiCompactSpace B S hS (productSpace X₀ (T.obj i₀)).1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ (productSpace X₀ (T.obj i₀)).1) :
    Nonempty (ProductChartData X₀ T i₀) := by
  obtain ⟨U₀, a₀, hU₀, hs₀, ha₀'⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _
      (productSpace X₀ (T.obj i₀)).2).mp hqc
  have ha₀ := (isEtale_iff_presheaf_of_yoneda B S hS a₀).mp ha₀'
  obtain ⟨W, hW, ⟨eW⟩⟩ := (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine B S hS hZ _
    (productSpace X₀ (T.obj i₀)).2).mp hqs U₀ U₀ a₀ a₀ hU₀ hU₀
  let t₀ : W ⟶ U₀ := Yoneda.fullyFaithful.preimage (eW.hom ≫ pullback.fst a₀ a₀)
  let s₀ : W ⟶ U₀ := Yoneda.fullyFaithful.preimage (eW.hom ≫ pullback.snd a₀ a₀)
  have hk : IsPullback (yoneda.map t₀) (yoneda.map s₀) a₀ a₀ :=
    isPullback_yoneda_map_preimage_of_iso a₀ a₀ eW
  have hU₀qs : IsAbsolutelyQuasiSeparated B S hS hZ (yoneda.obj U₀) :=
    isAbsolutelyQuasiSeparated_of_isAffineSpace B S hS hZ (isAffineSpace_yoneda B S hS U₀ hU₀)
  obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback B S hS hZ _
    (isAlgebraicSpace_yoneda B S hS U₀)).mp hU₀qs W W (yoneda.map s₀) (yoneda.map t₀) hW hW
  let p₀ : K₀ ⟶ W := Yoneda.fullyFaithful.preimage (eK.hom ≫ pullback.fst _ _)
  let q₀ : K₀ ⟶ W := Yoneda.fullyFaithful.preimage (eK.hom ≫ pullback.snd _ _)
  have hK : IsPullback (yoneda.map p₀) (yoneda.map q₀) (yoneda.map s₀) (yoneda.map t₀) :=
    isPullback_yoneda_map_preimage_of_iso _ _ eK
  have hK' : IsPullback p₀ q₀ s₀ t₀ := IsPullback.of_map yoneda
    (Yoneda.fullyFaithful.map_injective (by rw [Functor.map_comp, Functor.map_comp]; exact hK.w))
    hK
  have hw : (yoneda.map p₀ ≫ yoneda.map t₀) ≫ a₀ = (yoneda.map q₀ ≫ yoneda.map s₀) ≫ a₀ := by
    simp only [Category.assoc]
    rw [hk.w, ← Category.assoc, hK.w, Category.assoc, hk.w]
  let c₀ : K₀ ⟶ W := Yoneda.fullyFaithful.preimage (hk.lift _ _ hw)
  have hc : yoneda.map c₀ = hk.lift _ _ hw := Yoneda.fullyFaithful.map_preimage _
  refine ⟨⟨U₀, a₀, hU₀, ha₀, hs₀, W, hW, t₀, s₀, hk, K₀, hK₀, p₀, q₀, c₀, hK', ?_, ?_⟩⟩
  · exact Yoneda.fullyFaithful.map_injective (by rw [Functor.map_comp, Functor.map_comp, hc,
      hk.lift_fst])
  · exact Yoneda.fullyFaithful.map_injective (by rw [Functor.map_comp, Functor.map_comp, hc,
      hk.lift_snd])

end AlgebraicGeometry.Space

end
