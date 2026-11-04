module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartCoverDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison

/-!
# Étale charts of the source of an integral universally injective morphism

Let `f : Y ⟶ X` be an integral and universally injective morphism of algebraic spaces over a
scheme `S`. Base change along `f` of étale scheme charts of `X` is the functor
`AlgebraicGeometry.Space.smallBaseChange` of Stacks 03G2, part (4). This file proves that this
functor is cover dense for the small étale topology of `Y`: every étale chart of `Y` is covered
by base changes along `f` of étale charts of `X`.

This is the cover-density half of the geometric input to Stacks 0AEH, the analogue for an
integral universally injective morphism of the closed-immersion statement
`AlgebraicGeometry.Space.smallBaseChange_isCoverDense_of_isClosedImmersion`.

## Main results

* `AlgebraicGeometry.Space.smallBaseChange_isCoverDense_of_isIntegralHom_of_universallyInjective`:
  base change of étale scheme charts along an integral universally injective morphism of
  algebraic spaces is cover dense.

## Implementation notes

The covering family of a given chart `V ⟶ Y` is produced on underlying schemes. Choosing a
surjective étale scheme atlas `W ⟶ X` and base changing it along `f` gives a morphism of schemes
`W ×_X Y ⟶ W` which is integral and a homeomorphism onto a closed subset
(`AlgebraicGeometry.Space.isClosedEmbedding_toScheme_map_snd`), and the fibre product
`V ×_Y (W ×_X Y)` is a scheme étale over `W ×_X Y` and surjective over `V`. Étale Cohomology
04DW — property (C) — dominates that fibre product by a surjection out of the base change along
`W ×_X Y ⟶ W` of a single scheme étale over `W`.

Property (C) exercises no size control on that étale scheme, so it cannot be read inside the
size-bounded site. Shrinking it to its affine opens repairs this: an affine scheme étale over
`W` is quasi-compact and locally of finite type over `W` and therefore no larger than `W`
(Stacks 04T7), and the induced opens of the base change still cover it. Each such affine is an
étale chart of `X` through the atlas, and
`AlgebraicGeometry.Space.representablePullbackMap_isPullback_scheme` identifies its base change
along `f` with the corresponding fibre product of schemes, which is what produces the morphism
to `V`.

Unlike the closed-immersion argument, which has Stacks 04FW and so may take the dominating
pieces to be *isomorphic* to base changes, property (C) supplies only a surjection. That is
enough here: cover density asks for joint surjectivity and nothing more.

Joint surjectivity of the resulting family is checked on points, and the passage from a jointly
point-surjective family to a covering sieve of the small étale topology goes through the
spaces-étale site of Stacks 03G0, whose covering families are exactly the jointly
point-surjective ones: the comparison functor of Stacks 03G1 is a dense subsite inclusion, so a
sieve is covering for the small étale topology exactly when its image is covering for the
spaces-étale topology.

## References

* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Morphisms of the site from morphisms of schemes -/

/-- The morphism of schemes underlying a morphism of the big fppf site of `S` commutes with the
structure morphisms to `S`. -/
private theorem toScheme_map_comp_structure (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {T T' : BigFppfOver B S hS} (ψ : T ⟶ T') :
    (BigFppfOver.toScheme B S hS).map ψ ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom :=
  (B.inclusion.map_comp ψ.left T'.hom).symm.trans
    (congrArg (fun q => B.inclusion.map q) (Over.w ψ))

/-! ### The covering family of a chart of the source -/

/-- Every étale chart of the source `Y` of an integral universally injective morphism
`f : Y ⟶ X` admits a family of morphisms from base changes along `f` of étale charts of `X`
which is jointly surjective on the points of the underlying schemes. -/
private theorem exists_baseChange_chart_cover_of_integral (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable f.hom) (hint : IsIntegralHom B S hS f.hom)
    (hui : UniversallyInjective B S hS f.hom) (V : SmallEtale B S hS Y.1) :
    ∃ (κ : Type (u + 1)) (C : κ → SmallEtale B S hS X.1)
      (φ : ∀ k, (smallBaseChange B S hS f hrep).obj (C k) ⟶ V),
      ∀ x : (BigFppfOver.toScheme B S hS).obj V.1.left,
        ∃ (k : κ) (y : (BigFppfOver.toScheme B S hS).obj
            ((smallBaseChange B S hS f hrep).obj (C k)).1.left),
          (BigFppfOver.toScheme B S hS).map ((φ k).hom.left) y = x := by
  classical
  obtain ⟨W, atl, hatlSurj, hatlEtale⟩ := X.property.exists_atlas
  -- The atlas as an étale chart of `X`, and its base change along `f`.
  let Wc : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk atl, hatlEtale⟩
  let jW : hrep.pullback Wc.1.hom ⟶ W := hrep.snd Wc.1.hom
  let g : yoneda.obj (hrep.pullback Wc.1.hom) ⟶ Y.1 := hrep.fst Wc.1.hom
  have hjWemb : Topology.IsClosedEmbedding
      ((BigFppfOver.toScheme B S hS).map jW).base :=
    isClosedEmbedding_toScheme_map_snd B S hS Y.property X.property hrep hint hui Wc.1.hom
  -- The fibre product of `V` with the base-changed atlas.
  let pV : V.property.rep.pullback g ⟶ V.1.left := V.property.rep.fst' g
  let qV : V.property.rep.pullback g ⟶ hrep.pullback Wc.1.hom := V.property.rep.snd g
  have hqVet : Etale ((BigFppfOver.toScheme B S hS).map qV) := V.property.property_snd g
  have hVpb : IsPullback (yoneda.map pV) (yoneda.map qV) V.1.hom g :=
    V.property.rep.isPullback' g
  have hpVsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map pV) := by
    have hgsurj : (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g :=
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (hrep.isPullback Wc.1.hom).flip hatlSurj
    have hraw : (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map pV) :=
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hVpb.flip hgsurj
    have hiv : (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) pV := MorphismProperty.of_relative_map hraw
    have : Surjective ((BigFppfOver.toScheme B S hS).map pV) := hiv
    exact Scheme.Hom.surjective _
  -- Property (C), Étale Cohomology 04DW, for the base change of `f` over the atlas.
  let jWs := (BigFppfOver.toScheme B S hS).map jW
  have : _root_.AlgebraicGeometry.IsIntegralHom jWs :=
    isIntegralHom_toScheme_map_snd B S hS Y.property X.property hrep hint Wc.1.hom
  obtain ⟨Vc, vc, hvcet, dom, hdomsurj, hdomfac⟩ :=
    Stacks.EtaleCohomology.hasPropertyC_of_isIntegralHom_of_isClosedEmbedding jWs hjWemb
      ((BigFppfOver.toScheme B S hS).map qV) hqVet
  have : Etale vc := hvcet
  let dom' : pullback vc jWs ⟶
      (BigFppfOver.toScheme B S hS).obj (V.property.rep.pullback g) :=
    (pullbackSymmetry vc jWs).hom ≫ dom
  have hdom'fac : dom' ≫ (BigFppfOver.toScheme B S hS).map qV = pullback.snd vc jWs :=
    by simp only [dom', Category.assoc, hdomfac, pullbackSymmetry_hom_comp_fst]
  have hdom'surj : Function.Surjective dom' := by
    have := hdomsurj
    exact (inferInstance : Surjective dom').surj
  -- Affine opens of the dominating étale scheme, and the induced cover of the base change.
  let AO : Vc.OpenCover := Vc.affineOpenCover.openCover
  let CovA : (pullback vc jWs).OpenCover := AO.pullback₁ (pullback.fst vc jWs)
  have : ∀ a : Vc.affineOpenCover.I₀, AlgebraicGeometry.IsOpenImmersion (AO.f a) :=
    AO.map_prop
  have hsize : ∀ a : Vc.affineOpenCover.I₀, B.Contains (AO.X a) := by
    intro a
    exact (Scheme.size_le_of_locallyOfFiniteType (AO.f a ≫ vc)).trans_lt W.left.property
  -- The affine opens as étale charts of `X` through the atlas.
  let Av : ∀ a : Vc.affineOpenCover.I₀,
      B.obj (hsize a) ⟶ (BigFppfOver.forget B S hS).obj W := fun a =>
    B.inclusion.preimage (show B.inclusion.obj (B.obj (hsize a)) ⟶
      B.inclusion.obj ((BigFppfOver.forget B S hS).obj W) from AO.f a ≫ vc)
  let Aov : ∀ a : Vc.affineOpenCover.I₀, BigFppfOver B S hS := fun a =>
    Over.mk (Av a ≫ W.hom)
  let Amap : ∀ a : Vc.affineOpenCover.I₀, Aov a ⟶ W := fun a => Over.homMk (Av a) rfl
  have hAmap : ∀ a, (BigFppfOver.toScheme B S hS).map (Amap a) = AO.f a ≫ vc := fun a =>
    B.inclusion.map_preimage _
  have hAet : ∀ a, Etale ((BigFppfOver.toScheme B S hS).map (Amap a)) := by
    intro a
    rw [hAmap a]
    infer_instance
  let C : Vc.affineOpenCover.I₀ → SmallEtale B S hS X.1 := fun a =>
    ⟨CostructuredArrow.mk (yoneda.map (Amap a) ≫ Wc.1.hom),
      etale_comp_of_scheme B S hS (Amap a) Wc.1.hom (hAet a) hatlEtale⟩
  let Cchart : ∀ a, C a ⟶ Wc := fun a =>
    ObjectProperty.homMk (CostructuredArrow.homMk (Amap a) rfl)
  -- Each base-changed chart is the fibre product of schemes over the atlas.
  have hQpb : ∀ a, IsPullback
      ((BigFppfOver.toScheme B S hS).map (hrep.snd (C a).1.hom))
      ((BigFppfOver.toScheme B S hS).map
        (representablePullbackMap B S hS f hrep (Cchart a)))
      (AO.f a ≫ vc) jWs := by
    intro a
    have h := (representablePullbackMap_isPullback_scheme B S hS f hrep (Cchart a)).flip
    rwa [show ((Cchart a).hom.left) = Amap a from rfl, hAmap a] at h
  have hTpb : ∀ a : Vc.affineOpenCover.I₀, IsPullback
      (pullback.snd (pullback.fst vc jWs) (AO.f a))
      (CovA.f a ≫ pullback.snd vc jWs)
      (AO.f a ≫ vc) jWs := fun a =>
    IsPullback.paste_vert
      (IsPullback.of_hasPullback (pullback.fst vc jWs) (AO.f a)).flip
      (IsPullback.of_hasPullback vc jWs)
  -- The comparison isomorphism and the resulting morphism to `V`.
  let cmp : ∀ a : Vc.affineOpenCover.I₀,
      (BigFppfOver.toScheme B S hS).obj (hrep.pullback (C a).1.hom) ≅ CovA.X a := fun a =>
    (hQpb a).isoIsPullback _ _ (hTpb a)
  let n : ∀ a : Vc.affineOpenCover.I₀,
      (BigFppfOver.toScheme B S hS).obj (hrep.pullback (C a).1.hom) ⟶
        (BigFppfOver.toScheme B S hS).obj (V.property.rep.pullback g) := fun a =>
    (cmp a).hom ≫ CovA.f a ≫ dom'
  have hnq : ∀ a, n a ≫ (BigFppfOver.toScheme B S hS).map qV =
      (BigFppfOver.toScheme B S hS).map
        (representablePullbackMap B S hS f hrep (Cchart a)) := by
    intro a
    calc n a ≫ (BigFppfOver.toScheme B S hS).map qV
        = (cmp a).hom ≫ CovA.f a ≫ (dom' ≫ (BigFppfOver.toScheme B S hS).map qV) := by
          simp only [n, Category.assoc]
      _ = (cmp a).hom ≫ (CovA.f a ≫ pullback.snd vc jWs) := by rw [hdom'fac]
      _ = _ := (hQpb a).isoIsPullback_hom_snd _ _ (hTpb a)
  have hnovw : ∀ a, n a ≫ B.inclusion.map (V.property.rep.pullback g).hom =
      B.inclusion.map (hrep.pullback (C a).1.hom).hom := by
    intro a
    rw [← toScheme_map_comp_structure B S hS qV, ← Category.assoc, hnq a]
    exact toScheme_map_comp_structure B S hS
      (representablePullbackMap B S hS f hrep (Cchart a))
  let nov : ∀ a : Vc.affineOpenCover.I₀,
      hrep.pullback (C a).1.hom ⟶ V.property.rep.pullback g := fun a =>
    siteHomOfSchemeHom B S hS (n a) (hnovw a)
  have hnovmap : ∀ a, (BigFppfOver.toScheme B S hS).map (nov a) = n a := fun a =>
    siteHomOfSchemeHom_map B S hS (n a) (hnovw a)
  have hnovq : ∀ a, nov a ≫ qV = representablePullbackMap B S hS f hrep (Cchart a) := by
    intro a
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, hnovmap a, hnq a]
  let φ : ∀ a : Vc.affineOpenCover.I₀,
      (smallBaseChange B S hS f hrep).obj (C a) ⟶ V := fun a =>
    ObjectProperty.homMk (CostructuredArrow.homMk (nov a ≫ pV) (by
      calc yoneda.map (nov a ≫ pV) ≫ V.1.hom
          = (yoneda.map (nov a) ≫ yoneda.map pV) ≫ V.1.hom :=
            congrArg (fun q => q ≫ V.1.hom) (yoneda.map_comp (nov a) pV)
        _ = yoneda.map (nov a) ≫ yoneda.map pV ≫ V.1.hom := Category.assoc _ _ _
        _ = yoneda.map (nov a) ≫ yoneda.map qV ≫ g :=
            congrArg (fun q => yoneda.map (nov a) ≫ q) hVpb.w
        _ = yoneda.map (nov a ≫ qV) ≫ g :=
            (Category.assoc _ _ _).symm.trans
              (congrArg (fun q => q ≫ g) (yoneda.map_comp (nov a) qV).symm)
        _ = yoneda.map (representablePullbackMap B S hS f hrep (Cchart a)) ≫ g :=
            congrArg (fun q => yoneda.map q ≫ g) (hnovq a)
        _ = hrep.fst (C a).1.hom :=
            CostructuredArrow.w ((smallBaseChange B S hS f hrep).map (Cchart a)).hom))
  have hmapφ : ∀ a, (BigFppfOver.toScheme B S hS).map ((φ a).hom.left) =
      ((cmp a).hom ≫ CovA.f a ≫ dom') ≫ (BigFppfOver.toScheme B S hS).map pV := fun a =>
    ((BigFppfOver.toScheme B S hS).map_comp (nov a) pV).trans
      (congrArg (fun q => q ≫ (BigFppfOver.toScheme B S hS).map pV) (hnovmap a))
  refine ⟨ULift.{u + 1} Vc.affineOpenCover.I₀, fun k => C k.down, fun k => φ k.down, ?_⟩
  intro x
  obtain ⟨z, hz⟩ := hpVsurj x
  obtain ⟨p, hp⟩ := hdom'surj z
  obtain ⟨a, y, hy⟩ := CovA.exists_eq p
  refine ⟨ULift.up a, (cmp a).inv y, ?_⟩
  rw [hmapφ a]
  show (BigFppfOver.toScheme B S hS).map pV
    (dom' (CovA.f a ((cmp a).hom ((cmp a).inv y)))) = x
  rw [scheme_iso_hom_inv_apply, hy, hp, hz]

/-! ### Cover density -/

/-- **Cover density of chart base change along an integral universally injective morphism.**
Let `f : Y ⟶ X` be an integral and universally injective morphism of algebraic spaces over a
scheme `S`. Base change along `f` of étale scheme charts of `X` is cover dense for the small
étale topology of `Y`: every étale chart of `Y` is covered by base changes along `f` of étale
charts of `X`.

This is the cover-density input to Stacks 0AEH; the geometry is Étale Cohomology 04DW, property
(C) for the base change of `f` over an étale scheme atlas of `X`, which applies because that
base change is integral and a homeomorphism onto a closed subset. -/
theorem smallBaseChange_isCoverDense_of_isIntegralHom_of_universallyInjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hrep : yoneda.relativelyRepresentable f.hom) (hint : IsIntegralHom B S hS f.hom)
    (hui : UniversallyInjective B S hS f.hom) :
    (smallBaseChange B S hS f hrep).IsCoverDense (SmallEtale.topology B S hS Y.1) := by
  refine ⟨fun V => ?_⟩
  obtain ⟨K, C, φ, hjoint⟩ :=
    exists_baseChange_chart_cover_of_integral B S hS f hrep hint hui V
  let E : PreZeroHypercover.{u + 1} ((comparisonFunctor B S hS Y).obj V) :=
    { I₀ := K
      X := fun k => (comparisonFunctor B S hS Y).obj
        ((smallBaseChange B S hS f hrep).obj (C k))
      f := fun k => (comparisonFunctor B S hS Y).map (φ k) }
  have hE : SpacesEtale.IsCovering B S hS Y ⟨(comparisonFunctor B S hS Y).obj V, E⟩ := by
    intro x
    obtain ⟨k, y, hy⟩ := hjoint (pointsToScheme B S hS V.1.left x)
    obtain ⟨w, hw⟩ := surjective_pointsToScheme B S hS
      ((SmallEtale.toOver B S hS Y.1).obj ((smallBaseChange B S hS f hrep).obj (C k))) y
    refine ⟨k, w, injective_pointsToScheme B S hS V.1.left ?_⟩
    show pointsToScheme B S hS V.1.left (pointsMap B S hS _
      (yoneda.map ((SmallEtale.toOver B S hS Y.1).map (φ k))) w) = _
    rwa [pointsToScheme_pointsMap_yoneda, hw]
  have hle : Sieve.generate E.presieve₀ ≤
      (Sieve.coverByImage (smallBaseChange B S hS f hrep) V).functorPushforward
        (comparisonFunctor B S hS Y) := by
    rw [Sieve.generate_le_iff]
    intro T₀ h hh
    have hmem := Sieve.image_mem_functorPushforward (comparisonFunctor B S hS Y)
      (Sieve.coverByImage (smallBaseChange B S hS f hrep) V)
      (Presieve.in_coverByImage (smallBaseChange B S hS f hrep) (φ hh.idx))
    have hsrc : E.X hh.idx = T₀ := hh.obj_idx
    have hfEq : h = eqToHom hsrc.symm ≫ E.f hh.idx := by
      rw [hh.hom_idx]
      simp
    rw [hfEq]
    exact ((Sieve.coverByImage (smallBaseChange B S hS f hrep) V).functorPushforward
      (comparisonFunctor B S hS Y)).downward_closed hmem (eqToHom hsrc.symm)
  exact (Functor.functorPushforward_mem_iff (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (comparisonFunctor B S hS Y)).mp
    ((SpacesEtale.topology B S hS Y).superset_covering hle
      (Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩))

end AlgebraicGeometry.Space

end
