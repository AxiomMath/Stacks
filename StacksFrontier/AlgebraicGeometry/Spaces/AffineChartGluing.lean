module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasMorphismDescent

/-!
# Gluing a morphism to a sheaf from its values on affine étale charts

Let `F` be a presheaf on the big fppf site of a scheme `S` and let `W` be a sheaf there. Suppose
given, for every affine object `T` of the site and every étale morphism `b : yoneda.obj T ⟶ F`, a
morphism `k T b : yoneda.obj T ⟶ W`, and suppose the family is compatible with restriction along
morphisms of such charts, that is along a morphism `r : T ⟶ U` of the site with `b` restricted
along it. Then the family glues: along any étale `b : yoneda.obj U ⟶ F` with `U` arbitrary there
is a morphism `yoneda.obj U ⟶ W` restricting to it on every affine chart of `U`, and if `F` is a
sheaf and `b` is in addition surjective the glued morphism descends to `F`.

Étaleness of a chart is `AlgebraicGeometry.Space.IsEtale` of Stacks 03FR, which for a morphism
with representable source is the relatively representable étale property
(`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda`); for such morphisms composition is
Stacks 03FT.

## Main results

* `AlgebraicGeometry.Space.chartHoms_agree`: two affine charts of `F` that agree after pulling
  back to a common object give the same morphism to `W` there.
* `AlgebraicGeometry.Space.exists_hom_yoneda_of_chartHoms`: the family glues along an étale
  chart with arbitrary source.
* `AlgebraicGeometry.Space.exists_hom_of_chartHoms`: along a surjective étale atlas the glued
  morphism descends to `F`.

## References

* [Stacks Project, Tag 021S](https://stacks.math.columbia.edu/tag/021S)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {F W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  (hW : Presheaf.IsSheaf (BigFppfOver.topology B S hS) W)
  (k : ∀ T : BigFppfOver B S hS, IsAffineOver B S hS T →
    ∀ b : yoneda.obj T ⟶ F, IsEtale B S hS b → (yoneda.obj T ⟶ W))
  (hk : ∀ (T U : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
    (hU : IsAffineOver B S hS U) (r : T ⟶ U) (b : yoneda.obj U ⟶ F)
    (hb : IsEtale B S hS b) (hrb : IsEtale B S hS (yoneda.map r ≫ b)),
    yoneda.map r ≫ k U hU b hb = k T hT (yoneda.map r ≫ b) hrb)

include hW hk

/-- **Two affine charts of `F` pulled back to a common object give the same morphism to `W`
there.** If `r : R ⟶ T` and `s : R ⟶ U` carry the étale affine charts `b` and `c` to the same
morphism `yoneda.obj R ⟶ F`, and this morphism is étale, then the values of the family at `b` and
`c` restrict to the same morphism `yoneda.obj R ⟶ W`. -/
theorem chartHoms_agree
    (T U R : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (hU : IsAffineOver B S hS U)
    (b : yoneda.obj T ⟶ F) (c : yoneda.obj U ⟶ F)
    (hb : IsEtale B S hS b) (hc : IsEtale B S hS c)
    (r : R ⟶ T) (s : R ⟶ U) (hrs : yoneda.map r ≫ b = yoneda.map s ≫ c)
    (hrb : IsEtale B S hS (yoneda.map r ≫ b)) :
    yoneda.map r ≫ k T hT b hb = yoneda.map s ≫ k U hU c hc := by
  obtain ⟨I, V, π, hV, hπ, hcover⟩ := BigFppfOver.exists_affine_etale_cover B S hS R
  refine hom_ext_of_cover B S hS hW R V π hcover fun i => ?_
  have hvb : IsEtale B S hS (yoneda.map (π i ≫ r) ≫ b) := by
    simpa only [Functor.map_comp, Category.assoc] using isEtale_comp B S hS (hπ i) hrb
  have hvc : IsEtale B S hS (yoneda.map (π i ≫ s) ≫ c) := by
    simpa only [Functor.map_comp, Category.assoc, hrs] using hvb
  have heq : yoneda.map (π i ≫ r) ≫ b = yoneda.map (π i ≫ s) ≫ c := by
    simpa only [Functor.map_comp, Category.assoc] using congrArg (yoneda.map (π i) ≫ ·) hrs
  calc yoneda.map (π i) ≫ yoneda.map r ≫ k T hT b hb
      = k (V i) (hV i) (yoneda.map (π i ≫ r) ≫ b) hvb := by
        simpa only [Functor.map_comp, Category.assoc] using
          hk (V i) T (hV i) hT (π i ≫ r) b hb hvb
    _ = k (V i) (hV i) (yoneda.map (π i ≫ s) ≫ c) hvc := by congr 1
    _ = yoneda.map (π i) ≫ yoneda.map s ≫ k U hU c hc := by
        simpa only [Functor.map_comp, Category.assoc] using
          (hk (V i) U (hV i) hU (π i ≫ s) c hc hvc).symm

/-- Two affine étale charts `yoneda.map f ≫ b` and `yoneda.map g ≫ b` have equal values of the
family on the pullback of `f` and `g`, when `g` is étale. -/
private theorem pullback_chartHoms_agree
    {T V U : BigFppfOver B S hS} (hT : IsAffineOver B S hS T) (hV : IsAffineOver B S hS V)
    (f : T ⟶ U) (g : V ⟶ U) (b : yoneda.obj U ⟶ F) (hg : IsEtale B S hS (yoneda.map g))
    (hfb : IsEtale B S hS (yoneda.map f ≫ b)) (hgb : IsEtale B S hS (yoneda.map g ≫ b)) :
    yoneda.map (pullback.fst f g) ≫ k T hT (yoneda.map f ≫ b) hfb =
      yoneda.map (pullback.snd f g) ≫ k V hV (yoneda.map g ≫ b) hgb :=
  chartHoms_agree B S hS hW k hk T V (pullback f g) hT hV _ _ hfb hgb
    (pullback.fst f g) (pullback.snd f g)
    (by simp only [← Category.assoc, ← Functor.map_comp, pullback.condition])
    (isEtale_comp B S hS
      (isEtale_of_isPullback_yoneda B S hS ((IsPullback.of_hasPullback f g).map yoneda).flip hg)
      hfb)

/-- **The family glues along an étale chart with arbitrary source.** For an étale
`b : yoneda.obj U ⟶ F` there is a morphism `yoneda.obj U ⟶ W` whose restriction along every
`r : T ⟶ U` with `T` affine and `yoneda.map r ≫ b` étale is the value of the family at
`yoneda.map r ≫ b`. -/
theorem exists_hom_yoneda_of_chartHoms
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ F) (hb : IsEtale B S hS b) :
    ∃ l : yoneda.obj U ⟶ W, ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T)
      (r : T ⟶ U) (hrb : IsEtale B S hS (yoneda.map r ≫ b)),
      yoneda.map r ≫ l = k T hT (yoneda.map r ≫ b) hrb := by
  classical
  obtain ⟨I, V, π, hV, hπ, hcover⟩ := BigFppfOver.exists_affine_etale_cover B S hS U
  have hbi (i : I) : IsEtale B S hS (yoneda.map (π i) ≫ b) := isEtale_comp B S hS (hπ i) hb
  have hsf : Presieve.IsSheafFor W (Presieve.ofArrows V π) :=
    (Presieve.isSheafFor_iff_generate (P := W) _).mpr
      (((isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) W).mp hW) _ hcover)
  have hx : Presieve.Arrows.PullbackCompatible W π
      fun i => yonedaEquiv (k (V i) (hV i) (yoneda.map (π i) ≫ b) (hbi i)) := by
    intro i j
    have he := pullback_chartHoms_agree B S hS hW k hk (hV i) (hV j) (π i) (π j) b (hπ j)
      (hbi i) (hbi j)
    simpa only [yonedaEquiv_naturality] using congrArg yonedaEquiv he
  obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff_pullbacks W π).mp hsf _ hx
  refine ⟨yonedaEquiv.symm s, fun T hT r hrb => ?_⟩
  have hl (i : I) : yoneda.map (π i) ≫ yonedaEquiv.symm s =
      k (V i) (hV i) (yoneda.map (π i) ≫ b) (hbi i) := by
    refine yonedaEquiv.injective ?_
    rw [← yonedaEquiv_naturality]
    simpa only [Equiv.apply_symm_apply] using hs i
  have hc : Sieve.generate (Presieve.ofArrows (fun i => pullback r (π i))
      fun i => pullback.fst r (π i)) ∈ BigFppfOver.topology B S hS T := by
    change Sieve.ofArrows _ _ ∈ _
    rw [Sieve.ofArrows_eq_pullback_of_isPullback π fun i => IsPullback.of_hasPullback r (π i)]
    exact (BigFppfOver.topology B S hS).pullback_stable r hcover
  refine hom_ext_of_cover B S hS hW T _ _ hc fun i => ?_
  rw [pullback_chartHoms_agree B S hS hW k hk hT (hV i) r (π i) b (hπ i) hrb (hbi i), ← hl]
  simp only [← Category.assoc, ← Functor.map_comp, pullback.condition]

/-- **Along a surjective étale atlas the glued morphism descends to `F`.** If `F` is a sheaf and
`b : yoneda.obj U ⟶ F` is étale and surjective, there is a morphism `F ⟶ W` whose composite with
every affine chart `yoneda.map r ≫ b` of `F` through `b` is the value of the family there. -/
theorem exists_hom_of_chartHoms
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (U : BigFppfOver B S hS) (b : yoneda.obj U ⟶ F) (hb : IsEtale B S hS b)
    (hsurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    ∃ l : F ⟶ W, ∀ (T : BigFppfOver B S hS) (hT : IsAffineOver B S hS T) (r : T ⟶ U)
      (hrb : IsEtale B S hS (yoneda.map r ≫ b)),
      yoneda.map r ≫ b ≫ l = k T hT (yoneda.map r ≫ b) hrb := by
  obtain ⟨lU, hlU⟩ := exists_hom_yoneda_of_chartHoms B S hS hW k hk U b hb
  have hcompat (R : BigFppfOver B S hS) (r s : R ⟶ U)
      (hR : IsPullback (yoneda.map r) (yoneda.map s) b b) :
      yoneda.map r ≫ lU = yoneda.map s ≫ lU := by
    have hr : IsEtale B S hS (yoneda.map r) :=
      isEtale_of_isPullback_yoneda B S hS hR.flip hb
    have hrb : IsEtale B S hS (yoneda.map r ≫ b) := isEtale_comp B S hS hr hb
    obtain ⟨I, V, π, hV, hπ, hc⟩ := BigFppfOver.exists_affine_etale_cover B S hS R
    refine hom_ext_of_cover B S hS hW R V π hc fun i => ?_
    have hri : IsEtale B S hS (yoneda.map (π i ≫ r) ≫ b) := by
      simpa only [Functor.map_comp, Category.assoc] using isEtale_comp B S hS (hπ i) hrb
    have he : yoneda.map (π i ≫ r) ≫ b = yoneda.map (π i ≫ s) ≫ b := by
      simpa only [Functor.map_comp, Category.assoc] using congrArg (yoneda.map (π i) ≫ ·) hR.w
    have hsi : IsEtale B S hS (yoneda.map (π i ≫ s) ≫ b) := he ▸ hri
    calc yoneda.map (π i) ≫ yoneda.map r ≫ lU
        = k (V i) (hV i) (yoneda.map (π i ≫ r) ≫ b) hri := by
          simpa only [Functor.map_comp, Category.assoc] using hlU (V i) (hV i) (π i ≫ r) hri
      _ = k (V i) (hV i) (yoneda.map (π i ≫ s) ≫ b) hsi := by congr 1
      _ = yoneda.map (π i) ≫ yoneda.map s ≫ lU := by
          simpa only [Functor.map_comp, Category.assoc] using
            (hlU (V i) (hV i) (π i ≫ s) hsi).symm
  obtain ⟨l, hl, -⟩ := existsUnique_hom_of_atlas_invariant B S hS hF hW b hsurj
    ((isEtale_iff_presheaf_of_yoneda B S hS b).1 hb) lU hcompat
  refine ⟨l, fun T hT r hrb => ?_⟩
  rw [hl]
  exact hlU T hT r hrb

end AlgebraicGeometry.Space

end
