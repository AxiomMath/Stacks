module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import StacksFrontier.AlgebraicGeometry.Etale.LiftAcrossClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison

/-!
# Étale charts of a closed subspace come from charts of the ambient space

Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a scheme `S`. Base change along
`i` of étale scheme charts of `X` is the functor `AlgebraicGeometry.Space.smallBaseChange` of
Stacks 03G2, part (4). This file proves that this functor is cover dense for the small étale
topology of `Z`: every étale chart of `Z` is covered by base changes along `i` of étale charts
of `X`.

This is the chart-level half of Stacks 04E5, part (1).

## Main results

* `AlgebraicGeometry.Space.smallBaseChange_isCoverDense_of_isClosedImmersion`: base change of
  étale scheme charts along a closed immersion of algebraic spaces is cover dense.

## Implementation notes

The covering family of a given chart `V ⟶ Z` is produced on underlying schemes. Choosing a
surjective étale scheme atlas `W ⟶ X` and base changing it along `i` gives a closed immersion
of schemes `W ×_X Z ⟶ W`, and the fibre product `V ×_Z (W ×_X Z)` is a scheme étale over the
closed subscheme `W ×_X Z` and surjective over `V`. Stacks 04FW covers that fibre product by
Zariski opens each of which is, over `W ×_X Z`, the base change along the closed immersion of
an étale scheme over `W`; shrinking those étale schemes to their affine opens makes them
objects of the size-bounded site, because an affine scheme étale over `W` is quasi-compact and
locally of finite type over `W` and therefore no larger than `W` (Stacks 04T7). Each such
affine is an étale chart of `X` through the atlas, and
`AlgebraicGeometry.Space.representablePullbackMap_isPullback_scheme` identifies its base change
along `i` with the corresponding fibre product of schemes, which is what produces the morphism
to `V`.

Joint surjectivity of the resulting family is checked on points, and the passage from a jointly
point-surjective family to a covering sieve of the small étale topology goes through the
spaces-étale site of Stacks 03G0, whose covering families are exactly the jointly
point-surjective ones: the comparison functor of Stacks 03G1 is a dense subsite inclusion, so a
sieve is covering for the small étale topology exactly when its image is covering for the
spaces-étale topology. This avoids having to exhibit the family as one of the index-bounded
chosen covering families of the big étale site.

## References

* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04E3](https://stacks.math.columbia.edu/tag/04E3)
* [Stacks Project, Tag 04FW](https://stacks.math.columbia.edu/tag/04FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Morphisms of the site from morphisms of schemes -/

/-- A morphism of schemes between the schemes underlying two objects of the big fppf site of `S`
which commutes with their structure morphisms to `S` comes from a morphism of the site. -/
public def siteHomOfSchemeHom (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T T' : BigFppfOver B S hS}
    (m : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj T')
    (hm : m ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom) : T ⟶ T' :=
  Over.homMk (B.inclusion.preimage m) (B.inclusion.map_injective (by
    rwa [Functor.map_comp, Functor.map_preimage]))

/-- `AlgebraicGeometry.Space.siteHomOfSchemeHom` lifts the given morphism of schemes. -/
public theorem siteHomOfSchemeHom_map (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {T T' : BigFppfOver B S hS}
    (m : (BigFppfOver.toScheme B S hS).obj T ⟶ (BigFppfOver.toScheme B S hS).obj T')
    (hm : m ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom) :
    (BigFppfOver.toScheme B S hS).map (siteHomOfSchemeHom B S hS m hm) = m :=
  B.inclusion.map_preimage m

/-- An isomorphism of schemes is bijective on points, read off at a point of its target. -/
public theorem scheme_iso_hom_inv_apply {A C : Scheme.{u}} (ε : A ≅ C) (t : C) :
    ε.hom (ε.inv t) = t := by simp

/-- An isomorphism of schemes is bijective on points, read off at a point of its source. -/
public theorem scheme_iso_inv_hom_apply {A C : Scheme.{u}} (ε : A ≅ C) (t : A) :
    ε.inv (ε.hom t) = t := by simp

/-! ### The covering family of a chart of the closed subspace -/

/-- Every étale chart of a closed subspace `Z` of `X` admits a family of morphisms from base
changes along the closed immersion of étale charts of `X` which is jointly surjective on the
points of the underlying schemes. -/
private theorem exists_baseChange_chart_cover (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (V : SmallEtale B S hS Z.1) :
    ∃ (K : Type (u + 1)) (Y : K → SmallEtale B S hS X.1)
      (φ : ∀ k, (smallBaseChange B S hS i hi.rep).obj (Y k) ⟶ V),
      ∀ x : (BigFppfOver.toScheme B S hS).obj V.1.left,
        ∃ (k : K) (y : (BigFppfOver.toScheme B S hS).obj
            ((smallBaseChange B S hS i hi.rep).obj (Y k)).1.left),
          (BigFppfOver.toScheme B S hS).map ((φ k).hom.left) y = x := by
  classical
  obtain ⟨W, atl, hatlSurj, hatlEtale⟩ := X.property.exists_atlas
  let Wc : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk atl, hatlEtale⟩
  let jW : hi.rep.pullback Wc.1.hom ⟶ W := hi.rep.snd Wc.1.hom
  let g : yoneda.obj (hi.rep.pullback Wc.1.hom) ⟶ Z.1 := hi.rep.fst Wc.1.hom
  have hjWci : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map jW) := hi.property_snd Wc.1.hom
  let pV : V.property.rep.pullback g ⟶ V.1.left := V.property.rep.fst' g
  let qV : V.property.rep.pullback g ⟶ hi.rep.pullback Wc.1.hom := V.property.rep.snd g
  have hqVet : Etale ((BigFppfOver.toScheme B S hS).map qV) := V.property.property_snd g
  have hVpb : IsPullback (yoneda.map pV) (yoneda.map qV) V.1.hom g :=
    V.property.rep.isPullback' g
  have hpVsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map pV) := by
    let P := MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)
    have hgsurj : P.presheaf g :=
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (hi.rep.isPullback Wc.1.hom).flip hatlSurj
    have hraw : P.presheaf (yoneda.map pV) :=
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hVpb.flip hgsurj
    have hiv : P pV := MorphismProperty.of_relative_map hraw
    have : Surjective ((BigFppfOver.toScheme B S hS).map pV) := hiv
    exact Scheme.Hom.surjective _
  -- Stacks 04FW on the closed immersion `W ×_X Z ⟶ W` and the étale `V ×_Z (W ×_X Z)`.
  obtain ⟨Cov, Uamb, fU, hfUet, hCov⟩ :=
    Stacks.Etale.exists_etale_openCover_isomorphic_pullback_of_isClosedImmersion.{u, u + 1}
      ((BigFppfOver.toScheme B S hS).map jW) ((BigFppfOver.toScheme B S hS).map qV)
  choose e he using hCov
  let AO : ∀ j : Cov.I₀, (Uamb j).OpenCover := fun j => (Uamb j).affineOpenCover.openCover
  let CovA : ∀ j : Cov.I₀,
      (pullback (fU j) ((BigFppfOver.toScheme B S hS).map jW)).OpenCover := fun j =>
    (AO j).pullback₁ (pullback.fst (fU j) ((BigFppfOver.toScheme B S hS).map jW))
  have hAUet : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀,
      Etale ((AO k.1).f k.2 ≫ fU k.1) := by
    intro k
    have : Etale (fU k.1) := hfUet k.1
    have : AlgebraicGeometry.IsOpenImmersion ((AO k.1).f k.2) := (AO k.1).map_prop k.2
    infer_instance
  have hsize : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀,
      B.Contains ((AO k.1).X k.2) := fun k => by
    have := hAUet k
    exact (Scheme.size_le_of_locallyOfFiniteType ((AO k.1).f k.2 ≫ fU k.1)).trans_lt
      W.left.property
  let Av : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀,
      B.obj (hsize k) ⟶ (BigFppfOver.forget B S hS).obj W := fun k =>
    B.inclusion.preimage (show B.inclusion.obj (B.obj (hsize k)) ⟶
      B.inclusion.obj ((BigFppfOver.forget B S hS).obj W) from (AO k.1).f k.2 ≫ fU k.1)
  let Aov : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀, BigFppfOver B S hS := fun k =>
    Over.mk (Av k ≫ W.hom)
  let Amap : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀, Aov k ⟶ W := fun k =>
    Over.homMk (Av k) rfl
  have hAmap : ∀ k, (BigFppfOver.toScheme B S hS).map (Amap k) =
      (AO k.1).f k.2 ≫ fU k.1 := fun k => B.inclusion.map_preimage _
  have hAet : ∀ k, Etale ((BigFppfOver.toScheme B S hS).map (Amap k)) := fun k => by
    rw [hAmap k]
    exact hAUet k
  let Y : (Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀) → SmallEtale B S hS X.1 := fun k =>
    ⟨CostructuredArrow.mk (yoneda.map (Amap k) ≫ Wc.1.hom),
      etale_comp_of_scheme B S hS (Amap k) Wc.1.hom (hAet k) hatlEtale⟩
  let Ychart : ∀ k, Y k ⟶ Wc := fun k =>
    ObjectProperty.homMk (CostructuredArrow.homMk (Amap k) rfl)
  have hQpb : ∀ k, IsPullback
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd (Y k).1.hom))
      ((BigFppfOver.toScheme B S hS).map
        (representablePullbackMap B S hS i hi.rep (Ychart k)))
      ((AO k.1).f k.2 ≫ fU k.1) ((BigFppfOver.toScheme B S hS).map jW) := by
    intro k
    have h := (representablePullbackMap_isPullback_scheme B S hS i hi.rep (Ychart k)).flip
    rwa [show ((Ychart k).hom.left) = Amap k from rfl, hAmap k] at h
  have hTpb : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀, IsPullback
      (pullback.snd (pullback.fst (fU k.1) ((BigFppfOver.toScheme B S hS).map jW))
        ((AO k.1).f k.2))
      ((CovA k.1).f k.2 ≫
        pullback.snd (fU k.1) ((BigFppfOver.toScheme B S hS).map jW))
      ((AO k.1).f k.2 ≫ fU k.1) ((BigFppfOver.toScheme B S hS).map jW) := fun k =>
    IsPullback.paste_vert
      (IsPullback.of_hasPullback
        (pullback.fst (fU k.1) ((BigFppfOver.toScheme B S hS).map jW))
        ((AO k.1).f k.2)).flip
      (IsPullback.of_hasPullback (fU k.1) ((BigFppfOver.toScheme B S hS).map jW))
  let κ : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀,
      (BigFppfOver.toScheme B S hS).obj (hi.rep.pullback (Y k).1.hom) ≅
        (CovA k.1).X k.2 := fun k => (hQpb k).isoIsPullback _ _ (hTpb k)
  let n : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀,
      (BigFppfOver.toScheme B S hS).obj (hi.rep.pullback (Y k).1.hom) ⟶
        (BigFppfOver.toScheme B S hS).obj (V.property.rep.pullback g) := fun k =>
    (κ k).hom ≫ (CovA k.1).f k.2 ≫ (e k.1).inv ≫ Cov.f k.1
  have hnq : ∀ k, n k ≫ (BigFppfOver.toScheme B S hS).map qV =
      (BigFppfOver.toScheme B S hS).map
        (representablePullbackMap B S hS i hi.rep (Ychart k)) := by
    intro k
    have hcancel : (e k.1).inv ≫ Cov.f k.1 ≫ (BigFppfOver.toScheme B S hS).map qV =
        pullback.snd (fU k.1) ((BigFppfOver.toScheme B S hS).map jW) := by
      rw [← he k.1, ← Category.assoc, (e k.1).inv_hom_id, Category.id_comp]
    simp only [n, Category.assoc]
    rw [hcancel]
    exact (hQpb k).isoIsPullback_hom_snd _ _ (hTpb k)
  have hnovw : ∀ k, n k ≫ B.inclusion.map (V.property.rep.pullback g).hom =
      B.inclusion.map (hi.rep.pullback (Y k).1.hom).hom := by
    intro k
    rw [← BigFppfOver.toScheme_map_comp_hom qV, ← Category.assoc, hnq k]
    exact BigFppfOver.toScheme_map_comp_hom (representablePullbackMap B S hS i hi.rep (Ychart k))
  let nov : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀,
      hi.rep.pullback (Y k).1.hom ⟶ V.property.rep.pullback g := fun k =>
    siteHomOfSchemeHom B S hS (n k) (hnovw k)
  have hnovmap : ∀ k, (BigFppfOver.toScheme B S hS).map (nov k) = n k := fun k =>
    siteHomOfSchemeHom_map B S hS (n k) (hnovw k)
  have hnovq : ∀ k, nov k ≫ qV = representablePullbackMap B S hS i hi.rep (Ychart k) := by
    intro k
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [Functor.map_comp, hnovmap k, hnq k]
  let φ : ∀ k : Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀,
      (smallBaseChange B S hS i hi.rep).obj (Y k) ⟶ V := fun k =>
    ObjectProperty.homMk (CostructuredArrow.homMk (nov k ≫ pV) (by
      calc yoneda.map (nov k ≫ pV) ≫ V.1.hom
          = (yoneda.map (nov k) ≫ yoneda.map pV) ≫ V.1.hom :=
            congrArg (fun q => q ≫ V.1.hom) (yoneda.map_comp (nov k) pV)
        _ = yoneda.map (nov k) ≫ yoneda.map pV ≫ V.1.hom := Category.assoc _ _ _
        _ = yoneda.map (nov k) ≫ yoneda.map qV ≫ g :=
            congrArg (fun q => yoneda.map (nov k) ≫ q) hVpb.w
        _ = yoneda.map (nov k ≫ qV) ≫ g :=
            (Category.assoc _ _ _).symm.trans
              (congrArg (fun q => q ≫ g) (yoneda.map_comp (nov k) qV).symm)
        _ = yoneda.map (representablePullbackMap B S hS i hi.rep (Ychart k)) ≫ g :=
            congrArg (fun q => yoneda.map q ≫ g) (hnovq k)
        _ = hi.rep.fst (Y k).1.hom :=
            CostructuredArrow.w ((smallBaseChange B S hS i hi.rep).map (Ychart k)).hom))
  have hmapφ : ∀ k, (BigFppfOver.toScheme B S hS).map ((φ k).hom.left) =
      ((κ k).hom ≫ (CovA k.1).f k.2 ≫ (e k.1).inv ≫ Cov.f k.1) ≫
        (BigFppfOver.toScheme B S hS).map pV := fun k =>
    ((BigFppfOver.toScheme B S hS).map_comp (nov k) pV).trans
      (congrArg (fun q => q ≫ (BigFppfOver.toScheme B S hS).map pV) (hnovmap k))
  refine ⟨Σ j : Cov.I₀, (Uamb j).affineOpenCover.I₀, Y, φ, ?_⟩
  intro x
  obtain ⟨z, hz⟩ := hpVsurj x
  obtain ⟨j, w, hw⟩ := Cov.exists_eq z
  obtain ⟨a, y, hy⟩ := (CovA j).exists_eq ((e j).hom w)
  refine ⟨⟨j, a⟩, (κ ⟨j, a⟩).inv y, ?_⟩
  rw [hmapφ ⟨j, a⟩]
  change (BigFppfOver.toScheme B S hS).map pV
    (Cov.f j ((e j).inv ((CovA j).f a ((κ ⟨j, a⟩).hom ((κ ⟨j, a⟩).inv y))))) = x
  rw [scheme_iso_hom_inv_apply, hy, scheme_iso_inv_hom_apply, hw, hz]

/-! ### Cover density -/

/-- **Stacks 04E5, part (1).** Let `i : Z ⟶ X` be a closed immersion of algebraic spaces over a
scheme `S`. Base change along `i` of étale scheme charts of `X` is cover dense for the small
étale topology of `Z`: every étale chart of `Z` is covered by base changes along `i` of étale
charts of `X`. -/
@[stacks 04E5 "part (1): cover density of chart base change"]
theorem smallBaseChange_isCoverDense_of_isClosedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Z X : AlgebraicSpaces B S hS} (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    (smallBaseChange B S hS i hi.rep).IsCoverDense (SmallEtale.topology B S hS Z.1) := by
  constructor
  intro V
  obtain ⟨K, Y, φ, hjoint⟩ := exists_baseChange_chart_cover B S hS i hi V
  let E : PreZeroHypercover.{u + 1} ((comparisonFunctor B S hS Z).obj V) :=
    { I₀ := K
      X := fun k => (comparisonFunctor B S hS Z).obj
        ((smallBaseChange B S hS i hi.rep).obj (Y k))
      f := fun k => (comparisonFunctor B S hS Z).map (φ k) }
  have hE : SpacesEtale.IsCovering B S hS Z ⟨(comparisonFunctor B S hS Z).obj V, E⟩ := by
    intro x
    obtain ⟨k, y, hy⟩ := hjoint (pointsToScheme B S hS V.1.left x)
    obtain ⟨w, hw⟩ := surjective_pointsToScheme B S hS
      ((SmallEtale.toOver B S hS Z.1).obj ((smallBaseChange B S hS i hi.rep).obj (Y k))) y
    refine ⟨k, w, injective_pointsToScheme B S hS V.1.left ?_⟩
    change pointsToScheme B S hS V.1.left (pointsMap B S hS _
      (yoneda.map ((SmallEtale.toOver B S hS Z.1).map (φ k))) w) = _
    rwa [pointsToScheme_pointsMap_yoneda, hw]
  have hgen : Sieve.generate E.presieve₀ ∈
      SpacesEtale.topology B S hS Z ((comparisonFunctor B S hS Z).obj V) :=
    Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩
  have hle : Sieve.generate E.presieve₀ ≤
      (Sieve.coverByImage (smallBaseChange B S hS i hi.rep) V).functorPushforward
        (comparisonFunctor B S hS Z) := by
    rw [Sieve.generate_le_iff]
    intro T₀ h hh
    have hmem := Sieve.image_mem_functorPushforward (comparisonFunctor B S hS Z)
      (Sieve.coverByImage (smallBaseChange B S hS i hi.rep) V)
      (Presieve.in_coverByImage (smallBaseChange B S hS i hi.rep) (φ hh.idx))
    have hsrc : E.X hh.idx = T₀ := hh.obj_idx
    have hfEq : h = eqToHom hsrc.symm ≫ E.f hh.idx := by simp [hh.hom_idx]
    rw [hfEq]
    exact ((Sieve.coverByImage (smallBaseChange B S hS i hi.rep) V).functorPushforward
      (comparisonFunctor B S hS Z)).downward_closed hmem (eqToHom hsrc.symm)
  exact (Functor.functorPushforward_mem_iff (SmallEtale.topology B S hS Z.1)
    (SpacesEtale.topology B S hS Z) (comparisonFunctor B S hS Z)).mp
    ((SpacesEtale.topology B S hS Z).superset_covering hle hgen)

end AlgebraicGeometry.Space

end
