module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.Comap
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ClosedSubspaceApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AffineChartOfAffineThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChangeOrder
public import StacksFrontier.AlgebraicGeometry.Thickenings.KernelGlobalSections

/-!
# The scheme-theoretic image of a closed subscheme of an affine chart

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let
`φ : h_V ⟶ X` be a surjective étale chart with `V` affine, and suppose that the scheme `R`
representing `V ×_X V`, with projections `t s : R ⟶ V`, is affine as well.  For a closed
subscheme `Z ⊆ V` with ideal `J ⊆ Γ(V)`, the composite `Z ⟶ V ⟶ X` is quasi-compact, so by
Stacks 082Z the chart ideal of its scheme-theoretic image `H ⊆ X` on `V` is the kernel of
`Γ(V) ⟶ Γ(Z ×_X V)`.  Since `Z ×_X V = Z ×_{V, t} R` maps to `V` through `s`, this kernel is

  `s♯⁻¹(t♯(J) · Γ(R))`.

Pulling back along the diagonal `V ⟶ R` shows that it is contained in `J`.

The second part of the file reads the order of a thickening off a single surjective étale
chart: if the chart ideal of a closed subspace `H ⊆ X` on `V` has vanishing `(n+1)`st power and
`H` has all the points of `X`, then `H` is an `n`th-order thickening of `X`.  Every étale chart
`W` of `X` is covered by `W ×_X V`, which lies over `V`; there the chart ideal of `H` is pulled
back from `V`, so its `(n+1)`st power vanishes, and the vanishing descends to `W`.

## Main results

* `AlgebraicGeometry.Space.definingIdealAt_schemeTheoreticImage_chart`: the chart ideal of the
  scheme-theoretic image of `Z ⟶ V ⟶ X` is `s♯⁻¹(t♯(J) · Γ(R))`.
* `AlgebraicGeometry.Space.comap_map_le_of_isPullback`: that ideal is contained in `J`.
* `AlgebraicGeometry.Space.isNthOrderThickening_of_chartKer_pow_eq_bot`: the order of a
  thickening is read on one surjective étale chart.

## References

* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Image

variable {X : AlgebraicSpaces B S hS} {V R : BigFppfOver B S hS}
  (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
  (hR : IsAffine ((BigFppfOver.toScheme B S hS).obj R)) {φ : yoneda.obj V ⟶ X.1}
  (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
  {t s : R ⟶ V} (hpb : IsPullback (yoneda.map t) (yoneda.map s) φ φ)

include hV hR hs he hpb in
/-- **The chart ideal of the scheme-theoretic image of a closed subscheme of an affine chart.**
Let `φ : h_V ⟶ X` be a surjective étale chart with `V` affine whose kernel pair `R`, with
projections `t s : R ⟶ V`, is affine, and let `ν : Z ⟶ V` be a closed immersion with ideal
`J = ker(Γ(V) ⟶ Γ(Z))`.  The defining ideal on the chart `V` of the scheme-theoretic image of
`Z ⟶ V ⟶ X` is `s♯⁻¹(t♯(J) · Γ(R))`.

The composite is quasi-compact, so by Stacks 082Z the defining ideal is the kernel of
`Γ(V) ⟶ Γ(Z ×_X V)`.  Pasting cartesian squares identifies `Z ×_X V ⟶ R` with the base change of
`ν` along `t`, a closed immersion of affine schemes with ideal `t♯(J) · Γ(R)`, and its composite
with `s` is the projection to `V`. -/
theorem definingIdealAt_schemeTheoreticImage_chart {Z : BigFppfOver B S hS} (ν : Z ⟶ V)
    [hν : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ν)] :
    definingIdealAt B S hS X (schemeTheoreticImage B S hS (yoneda.map ν ≫ φ) X.2)
        (op (chartOfSurjectiveEtale B S hS X he)) =
      ((RingHom.ker ((BigFppfOver.toScheme B S hS).map ν).appTop.hom).map
        ((BigFppfOver.toScheme B S hS).map t).appTop.hom).comap
        ((BigFppfOver.toScheme B S hS).map s).appTop.hom := by
  set F := BigFppfOver.toScheme B S hS
  -- Quasi-compactness of `Z ⟶ V ⟶ X`.
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
        F).IsStableUnderBaseChange :=
    MorphismProperty.inverseImage_isStableUnderBaseChange _ _
  have hqcν : IsQuasiCompact B S hS (yoneda.map ν) :=
    isQuasiCompact_of_presheaf_quasiCompact B S hS
      ((MorphismProperty.relative_map_iff
        (P := MorphismProperty.inverseImage
          (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) F)
        (F := yoneda)).2 (inferInstance : QuasiCompact (F.map ν)))
  have hqc : IsQuasiCompact B S hS (yoneda.map ν ≫ φ) :=
    IsQuasiCompact.comp B S hS (isAlgebraicSpace_yoneda B S hS V) X.2 hqcν
      (isQuasiCompact_of_isPullback_of_isAffine B S hS hV hR φ hs he t s hpb)
  let f : schemeSpace Z ⟶ X := ObjectProperty.homMk (yoneda.map ν ≫ φ)
  have h082 : definingIdealSheaf B S hS X
      (schemeTheoreticImage B S hS (yoneda.map ν ≫ φ) X.2) = kernelIdealSheaf B S hS f :=
    definingIdealSheaf_schemeTheoreticImage_eq_kernelIdealSheaf B S hS f hqc
  have hrep : yoneda.relativelyRepresentable f.hom :=
    X.2.diagonal_representable.of_diag _
  have hval := congrArg
    (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
      N.obj (op (chartOfSurjectiveEtale B S hS X he))) h082
  simp only [definingIdealSheaf_obj, kernelIdealSheaf_obj] at hval
  rw [hval, ker_structureSharp_eq B S hS f hrep, chartPullbackRingHom_chartBaseChangeArrow,
    Scheme.Γ_map_op]
  -- The cartesian square `Z ×_X V`.
  set π₁ := hrep.fst' φ
  set π₂ := hrep.snd φ
  have hP : IsPullback (yoneda.map π₁) (yoneda.map π₂) (yoneda.map ν ≫ φ) φ :=
    hrep.isPullback' φ
  obtain ⟨c, hc⟩ := yoneda.map_surjective
    (hpb.lift (yoneda.map π₁ ≫ yoneda.map ν) (yoneda.map π₂)
      ((Category.assoc _ _ _).trans hP.w))
  have hct : yoneda.map c ≫ yoneda.map t = yoneda.map π₁ ≫ yoneda.map ν := by
    rw [hc, IsPullback.lift_fst]
  have hcs : yoneda.map c ≫ yoneda.map s = yoneda.map π₂ := by
    rw [hc]
    exact IsPullback.lift_snd _ _ _ _
  have hleft : IsPullback (yoneda.map c) (yoneda.map π₁) (yoneda.map t) (yoneda.map ν) := by
    refine IsPullback.of_right ?_ hct hpb.flip
    rw [hcs]
    exact hP.flip
  have hsq := (IsPullback.of_map_of_faithful yoneda hleft).map F
  have hkerc : (F.map c).ker =
      Scheme.IdealSheafData.ofIdealTop
        ((RingHom.ker (F.map ν).appTop.hom).map (F.map t).appTop.hom) := by
    rw [← hsq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, Scheme.ker_of_isAffine,
      Stacks.AlgebraicGeometry.comap_ofIdealTop]
  have hkerc' : RingHom.ker (F.map c).appTop.hom =
      (RingHom.ker (F.map ν).appTop.hom).map (F.map t).appTop.hom := by
    have h := Scheme.ker_of_isAffine (F.map c)
    rw [hkerc] at h
    exact (Scheme.IdealSheafData.equivOfIsAffine.symm.injective h).symm
  have hπ₂ : F.map π₂ = F.map c ≫ F.map s := by
    rw [← F.map_comp]
    exact congrArg F.map (yoneda.map_injective (hcs.symm.trans (yoneda.map_comp c s).symm))
  have key : RingHom.ker (F.map π₂).appTop.hom =
      ((RingHom.ker (F.map ν).appTop.hom).map (F.map t).appTop.hom).comap
        (F.map s).appTop.hom := by
    rw [hπ₂, Scheme.Hom.comp_appTop]
    change RingHom.ker ((F.map c).appTop.hom.comp (F.map s).appTop.hom) = _
    rw [← RingHom.comap_ker, hkerc']
  exact key

include hpb in
/-- **The chart ideal of the image is contained in the ideal of the closed subscheme.** For
the diagonal `δ : V ⟶ R`, both composites `δ ≫ t` and `δ ≫ s` are the identity, so
`x = δ♯(s♯ x) ∈ δ♯(t♯(J) · Γ(R)) ⊆ J` whenever `s♯ x ∈ t♯(J) · Γ(R)`. -/
theorem comap_map_le_of_isPullback (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    (J.map ((BigFppfOver.toScheme B S hS).map t).appTop.hom).comap
      ((BigFppfOver.toScheme B S hS).map s).appTop.hom ≤ J := by
  set F := BigFppfOver.toScheme B S hS
  obtain ⟨δ, hδ⟩ := yoneda.map_surjective (hpb.lift (𝟙 _) (𝟙 _) rfl)
  have hδt : δ ≫ t = 𝟙 V :=
    yoneda.map_injective (by rw [Functor.map_comp, hδ, IsPullback.lift_fst, yoneda.map_id])
  have hδs : δ ≫ s = 𝟙 V :=
    yoneda.map_injective (by rw [Functor.map_comp, hδ, IsPullback.lift_snd, yoneda.map_id])
  have hcomp : ∀ g : R ⟶ V, δ ≫ g = 𝟙 V →
      (F.map δ).appTop.hom.comp (F.map g).appTop.hom = RingHom.id _ := by
    intro g hg
    rw [← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop, ← F.map_comp, hg, F.map_id,
      Scheme.Hom.id_appTop, CommRingCat.hom_id]
  intro x hx
  have hmem := Ideal.mem_map_of_mem (F.map δ).appTop.hom (Ideal.mem_comap.1 hx)
  rw [Ideal.map_map, hcomp t hδt, Ideal.map_id] at hmem
  have hx' : (F.map δ).appTop.hom ((F.map s).appTop.hom x) = x := by
    rw [← RingHom.comp_apply, hcomp s hδs, RingHom.id_apply]
  rwa [hx'] at hmem

end Image

/-! ### The order of a thickening, read on one surjective étale chart -/

/-- **The order of a thickening is read on one surjective étale chart.** Let `φ : h_V ⟶ X` be
a surjective étale chart and let `H ⊆ X` be a closed subspace containing all points of `X`.  If
the chart ideal sheaf of `H` on `V` has vanishing `(n+1)`st power, then `H` is an `n`th-order
thickening of `X`.

An étale chart `W` of `X` is covered by `W ×_X V`, which maps to `V`; the chart ideal of `H` on
`W ×_X V` is the inverse image of that on `V`, so its `(n+1)`st power vanishes, hence so does
that of the ideal of global functions it cuts out, and the vanishing descends from the covering
to `W`. -/
theorem isNthOrderThickening_of_chartKer_pow_eq_bot {X : AlgebraicSpaces B S hS}
    {V : BigFppfOver B S hS} {φ : yoneda.obj V ⟶ X.1}
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (H : ClosedSubspaces B S hS X.1)
    (hH : Function.Surjective (pointsMap B S hS H.1.toFunctor H.1.ι)) (n : ℕ)
    (hn : chartKer B S hS X H φ ^ (n + 1) = ⊥) :
    IsNthOrderThickening B S hS n X H.1 := by
  set F := BigFppfOver.toScheme B S hS
  refine ⟨⟨H.2, hH⟩, fun W => ?_⟩
  have hrep : yoneda.relativelyRepresentable φ := he.rep
  set T : BigFppfOver B S hS := hrep.pullback W.1.hom
  set π : T ⟶ W.1.left := hrep.snd W.1.hom
  obtain ⟨m, hm⟩ := yoneda.map_surjective (hrep.fst W.1.hom)
  have hpb : IsPullback (yoneda.map m) (yoneda.map π) φ W.1.hom := by
    rw [hm]
    exact hrep.isPullback W.1.hom
  have hstE : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) F)) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hstS : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) F)) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hπEt : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) F).presheaf
        (yoneda.map π) :=
    MorphismProperty.of_isPullback hpb he
  have hπSurj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) F).presheaf
        (yoneda.map π) :=
    MorphismProperty.of_isPullback hpb hs
  have hπEt' : MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) F π :=
    MorphismProperty.of_relative_map hπEt
  have hπSurj' : MorphismProperty.inverseImage
      (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) F π :=
    MorphismProperty.of_relative_map hπSurj
  have hπEtale : AlgebraicGeometry.Etale (F.map π) := hπEt'
  have hπSurjective : AlgebraicGeometry.Surjective (F.map π) := hπSurj'
  let W' : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map π ≫ W.1.hom),
      etale_comp_of_scheme B S hS π W.1.hom hπEtale W.2⟩
  let a : W' ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk π rfl)
  have hcov : Presieve.ofArrows
      (fun _ : PUnit.{u + 1} => F.obj ((SmallEtale.toOver B S hS X.1).obj W'))
      (fun _ => F.map ((SmallEtale.toOver B S hS X.1).map a)) ∈
      Scheme.etalePrecoverage (F.obj ((SmallEtale.toOver B S hS X.1).obj W)) :=
    (AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff (@AlgebraicGeometry.Etale.{u})).mpr
      ⟨fun x => ⟨PUnit.unit, hπSurjective.1 x⟩, fun _ => hπEtale⟩
  refine definingIdealAt_pow_eq_bot_of_ofArrows B S hS X H n W (fun _ : PUnit.{u + 1} => W')
    (fun _ => a) (SmallEtale.ofArrows_mem_topology B S hS X.1 _ _ hcov) fun _ => ?_
  have hψ : yoneda.map m ≫ φ = W'.1.hom := by
    rw [hm]
    exact hrep.w W.1.hom
  have hker : (F.map (H.2.2.rep.snd W'.1.hom)).ker ^ (n + 1) = ⊥ := by
    rw [← chartKer_eq B S hS X H W'.1.hom, ← comap_chartKer B S hS X H φ m _ hψ,
      ← Stacks.IdealSheaf.comap_pow, hn, Scheme.IdealSheafData.comap_bot]
  rw [definingIdealAt_eq_ker, Scheme.Γ_map_op]
  exact Scheme.ker_appTop_pow_eq_bot _ inferInstance hker

end AlgebraicGeometry.Space

end
