module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.IntegralEtaleSplitting
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricComponentCount
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationGeneralRegistration

/-!
# Lower semicontinuity of the number of geometric connected components

Let `f : X ⟶ Y` be a proper, flat morphism of finite presentation of algebraic spaces over a
scheme `S`.  This file proves **Stacks 0E1D**: the function `n_{X/Y} : |Y| → ℕ∞` of Stacks 0E1B,
counting the connected components of the geometric fibres of `f`, is lower semicontinuous.

## Main results

* `AlgebraicGeometry.Space.lowerSemicontinuous_numberGeometricConnectedComponents`:
  **Stacks 0E1D**.
* `AlgebraicGeometry.Space.exists_etale_isOpen_le_numberGeometricConnectedComponents`: the
  local statement on an affine étale chart, after a further étale base change.
* `AlgebraicGeometry.Space.isPreconnected_setOf_pointsMap_eq_of_isPullback`: the set-theoretic
  fibres of a base change of a morphism with connected geometric fibres are preconnected.
* `AlgebraicGeometry.Space.natCast_le_numberGeometricConnectedComponents` and
  `AlgebraicGeometry.Space.numberGeometricConnectedComponents_le_natCast`: bounds on the number
  of geometric connected components from clopen partitions of the source.

## Implementation notes

The proof follows the source.  Let `X ⟶ Y' ⟶ Y` be the Stein factorization of Stacks 0A1C
(`AlgebraicGeometry.Space.steinFactorization_general_complete`): `f' : X ⟶ Y'` is proper,
surjective and has connected geometric fibres, and `π : Y' ⟶ Y` is integral.  The question is
étale local on `Y` (Stacks 0E1B,
`AlgebraicGeometry.Space.numberGeometricConnectedComponents_baseChange`, and étale morphisms are
open on points), so let `W` be an affine étale chart of `Y` through the point in question.  The
base change `T` of `Y'` to `W` is an affine scheme integral over `W`,
dominated by a compact étale chart of `X ×_Y W`, so it has finite fibres with finite residue
field extensions (Stacks 0E1C, in its scheme-level form).  By Stacks 0BSR, in the form
`AlgebraicGeometry.exists_etale_clopen_splitting_of_isIntegralHom`, after a further étale base
change `W₂ ⟶ W` the scheme `T₂ = T ×_W W₂` is a disjoint union of `m` clopen pieces `E i`, each
meeting the fibre over a point `w₂` above the given point and contributing at most one point to
the geometric fibre over `w₂`, by pure inseparability of the residue field extensions.

The preimages `P i` of the `E i` in `X₂ = X ×_Y W₂` are clopen, and their images in `|W₂|` are
open since `X₂ ⟶ W₂` is flat and of finite presentation (Stacks 042S).  Over the intersection of
these images every geometric fibre meets each `P i`, so it has at least `m` connected
components.  Over `w₂` the trace of each `P i` on the geometric fibre is a fibre of a base
change of `f'` over a single point, hence connected by Stacks 0A1C, so the geometric fibre over
`w₂` has at most `m` connected components.  This is the inequality `n_{X/Y} ≥ n_{X/Y}(y)` near
the given point `y`.

The function takes values in `ℕ∞`, the value set `{0, 1, 2, …, ∞}` of Stacks 0E1B; the proof
shows in passing that the value at every point is finite.

## References

* [Stacks Project, Tag 0E1D](https://stacks.math.columbia.edu/tag/0E1D)
* [Stacks Project, Tag 0E1B](https://stacks.math.columbia.edu/tag/0E1B)
* [Stacks Project, Tag 0A1C](https://stacks.math.columbia.edu/tag/0A1C)
* [Stacks Project, Tag 0E1C](https://stacks.math.columbia.edu/tag/0E1C)
* [Stacks Project, Tag 0BSR](https://stacks.math.columbia.edu/tag/0BSR)
* [Stacks Project, Tag 042S](https://stacks.math.columbia.edu/tag/042S)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.Space

/-! ### Counting connected components through clopen partitions -/

/-- A space with `m` pairwise disjoint nonempty open and closed subsets has at least `m`
connected components. -/
theorem natCast_le_toENat_cardinalMk_connectedComponents {X : Type v} [TopologicalSpace X] {m : ℕ}
    (Q : Fin m → Set X) (hQ : ∀ i, IsClopen (Q i))
    (hdisj : Pairwise fun i j => Disjoint (Q i) (Q j)) (hne : ∀ i, (Q i).Nonempty) :
    (m : ℕ∞) ≤ Cardinal.toENat (Cardinal.mk (ConnectedComponents X)) := by
  choose x hx using hne
  have hinj : Function.Injective fun i => (x i : ConnectedComponents X) := by
    intro i j hij
    by_contra hne
    have hxj : x j ∈ connectedComponent (x i) :=
      ConnectedComponents.coe_eq_coe'.mp hij.symm
    exact Set.disjoint_left.mp (hdisj hne) ((hQ i).connectedComponent_subset (hx i) hxj) (hx j)
  have h := OrderHomClass.mono Cardinal.toENat (Cardinal.lift_mk_le_lift_mk_of_injective hinj)
  simpa [Cardinal.toENat_lift] using h

/-- A space covered by `m` open and closed preconnected subsets has at most `m` connected
components. -/
theorem toENat_cardinalMk_connectedComponents_le_natCast {X : Type v} [TopologicalSpace X] {m : ℕ}
    (Q : Fin m → Set X) (hcov : ∀ x, ∃ i, x ∈ Q i)
    (hconn : ∀ i, IsPreconnected (Q i)) :
    Cardinal.toENat (Cardinal.mk (ConnectedComponents X)) ≤ m := by
  classical
  choose ι hι using hcov
  let φ : ConnectedComponents X → Fin m := fun c => ι c.out
  have hinj : Function.Injective φ := by
    intro c c' hcc'
    have h1 : c'.out ∈ Q (ι c.out) := by
      have : ι c.out = ι c'.out := hcc'
      rw [this]; exact hι _
    have hsub := (hconn (ι c.out)).subset_connectedComponent (hι c.out)
    have h2 : c'.out ∈ connectedComponent c.out := hsub h1
    rw [← c.out_eq, ← c'.out_eq]
    exact (ConnectedComponents.coe_eq_coe'.mpr h2).symm
  have h := OrderHomClass.mono Cardinal.toENat (Cardinal.lift_mk_le_lift_mk_of_injective hinj)
  simpa [Cardinal.toENat_lift] using h

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Fibres of a base change of a morphism with connected geometric fibres -/

/-- A point of `X` lies over the geometric point `ζ` of `G` exactly when it is the image of a point
of the fibre product `X ×_G ζ`. -/
private theorem pointsMap_eq_image_iff_mem_range_pullback_fst
    {X G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ G) (ζ : GeometricPoint B S hS G)
    (x : points B S hS X) :
    pointsMap B S hS X g x = ζ.image ↔
      ∃ η, pointsMap B S hS _ (pullback.fst g (yonedaEquiv.symm ζ.val.value)) η = x := by
  have hsub := subsingleton_points_yoneda_siteObject B S hS ζ.val
  let k : yoneda.obj ζ.val.siteObject ⟶ G := yonedaEquiv.symm ζ.val.value
  have htaut : pointsMap B S hS _ k
      ((FieldValuedPoint.tautological B S hS ζ.val).class B S hS _) = ζ.image := by
    rw [pointsMap_class, FieldValuedPoint.map_tautological]
  constructor
  · intro hx
    obtain ⟨η, hη, -⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback g k) x
      ((FieldValuedPoint.tautological B S hS ζ.val).class B S hS _) (by rw [htaut]; exact hx)
    exact ⟨η, hη⟩
  · rintro ⟨η, rfl⟩
    rw [pointsMap_apply_comm B S hS pullback.condition η, ← htaut]
    exact congrArg _ (hsub.elim _ _)

/-- Factorization of the base change of `f = f' ≫ π` through a base change of `π`: the pullback of
`f` along `t` maps to `T` so that it is a base change of `f'` and lies over the pullback of `π`. -/
private theorem exists_isPullback_factorization
    {X Y Y' G T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {f' : X ⟶ Y'} {π : Y' ⟶ Y}
    (hfac : f' ≫ π = f) {t : G ⟶ Y} {q : T ⟶ Y'} {p : T ⟶ G} (hpb : IsPullback q p π t) :
    ∃ φ : pullback f t ⟶ T, IsPullback (pullback.fst f t) φ f' q ∧ φ ≫ p = pullback.snd f t := by
  have hfac' : (pullback.fst f t ≫ f') ≫ π = pullback.snd f t ≫ t := by
    rw [Category.assoc, hfac]; exact pullback.condition
  have hsnd : hpb.lift _ _ hfac' ≫ p = pullback.snd f t := hpb.lift_snd _ _ _
  refine ⟨hpb.lift _ _ hfac', ?_, hsnd⟩
  refine IsPullback.of_bot ?_ (hpb.lift_fst _ _ _).symm hpb
  rw [hsnd, hfac]
  exact IsPullback.of_hasPullback f t

/-- Let `f' : X ⟶ Y'` have connected fibres over all geometric points of `Y'`, and let
`b : P ⟶ G` be a base change of `f'` along `c : G ⟶ Y'`.  Then the set-theoretic fibres of `b`
on points are preconnected: each is the image of the fibre of `f'` over a geometric point of
`Y'` lying over it. -/
theorem isPreconnected_setOf_pointsMap_eq_of_isPullback
    {X Y' G P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f' : X ⟶ Y'} {c : G ⟶ Y'} {a : P ⟶ X}
    {b : P ⟶ G} (sq : IsPullback a b f' c)
    (hconn : ∀ y : GeometricPoint B S hS Y',
      ConnectedPullback B S hS f' (yonedaEquiv.symm y.val.value))
    (z : points B S hS G) :
    IsPreconnected {x : points B S hS P | pointsMap B S hS P b x = z} := by
  obtain ⟨ζ, rfl⟩ := exists_geometricRepresentative B S hS G z
  let ζ' : GeometricPoint B S hS Y' := ⟨FieldValuedPoint.map B S hS G c ζ.val, ζ.property⟩
  let k : yoneda.obj ζ.val.siteObject ⟶ G := yonedaEquiv.symm ζ.val.value
  have hk : yonedaEquiv.symm ζ'.val.value = k ≫ c :=
    (yonedaEquiv_symm_naturality_right _ c ζ.val.value).symm
  have hsq : IsPullback (pullback.fst b k ≫ a) (pullback.snd b k) f' (k ≫ c) :=
    (IsPullback.of_hasPullback b k).paste_horiz sq
  have h1 : ConnectedPoints B S hS (pullback b k) := by
    have h := hconn ζ'
    rw [ConnectedPullback, hk] at h
    exact connectedSpace_of_presheafIso B S hS hsq.isoPullback.symm h
  have hset : {x : points B S hS P | pointsMap B S hS P b x = ζ.image} =
      Set.range (pointsMap B S hS _ (pullback.fst b k)) :=
    Set.ext (pointsMap_eq_image_iff_mem_range_pullback_fst b ζ)
  rw [hset]
  exact isPreconnected_range (continuous_pointsMap B S hS _)

/-! ### Bounds on the number of geometric connected components -/

/-- If `m` pairwise disjoint open and closed sets of points of `X` all meet the fibre of
`g : X ⟶ G` over `z`, then the fibre of `g` over `z` has at least `m` geometric connected
components. -/
theorem natCast_le_numberGeometricConnectedComponents
    {X G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hG : IsAlgebraicSpace B S hS G) (g : X ⟶ G) {m : ℕ} (Pc : Fin m → Set (points B S hS X))
    (hclopen : ∀ i, IsClopen (Pc i)) (hdisj : Pairwise fun i j => Disjoint (Pc i) (Pc j))
    (z : points B S hS G) (hz : ∀ i, z ∈ pointsMap B S hS X g '' Pc i) :
    (m : ℕ∞) ≤ numberGeometricConnectedComponents B S hS g z := by
  obtain ⟨ζ, rfl⟩ := exists_geometricRepresentative B S hS G z
  rw [numberGeometricConnectedComponents_eq B S hS hX hG g ζ]
  refine natCast_le_toENat_cardinalMk_connectedComponents
    (fun i => pointsMap B S hS _ (pullback.fst g (yonedaEquiv.symm ζ.val.value)) ⁻¹' Pc i)
    (fun i => (hclopen i).preimage (continuous_pointsMap B S hS _))
    (fun i j hij => (hdisj hij).preimage _) fun i => ?_
  obtain ⟨ξ, hξ, hξz⟩ := hz i
  obtain ⟨η, hη⟩ := (pointsMap_eq_image_iff_mem_range_pullback_fst g ζ ξ).mp hξz
  exact ⟨η, by rw [Set.mem_preimage, hη]; exact hξ⟩

/-- If the points of `X` are covered by `m` open and closed sets whose traces on the fibre of
`g : X ⟶ G` over a geometric point `ζ` are preconnected, then that fibre has at most `m`
connected components. -/
theorem numberGeometricConnectedComponents_le_natCast
    {X G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hG : IsAlgebraicSpace B S hS G) (g : X ⟶ G) {m : ℕ} (Pc : Fin m → Set (points B S hS X))
    (hcov : ∀ x, ∃ i, x ∈ Pc i)
    (ζ : GeometricPoint B S hS G)
    (hpre : ∀ i, IsPreconnected (pointsMap B S hS _
      (pullback.fst g (yonedaEquiv.symm ζ.val.value)) ⁻¹' Pc i)) :
    numberGeometricConnectedComponents B S hS g ζ.image ≤ m := by
  rw [numberGeometricConnectedComponents_eq B S hS hX hG g ζ]
  exact toENat_cardinalMk_connectedComponents_le_natCast _ (fun x => hcov _) hpre

/-- The pieces of a geometric fibre cut out by a set `E` of points of a represented intermediate
space are preconnected, provided `E` has at most one point above it over the geometric point.

Let `φ : X₂ ⟶ h_{T₂}` be a base change of a morphism `f' : X ⟶ Y'` with connected geometric
fibres, let `snd₂ : T₂ ⟶ W₂` be a morphism of the site and `ζ` a geometric point of `h_{W₂}`.  If
the fibre product `V = T₂ ×_{W₂} ζ` has at most one point over `E`, then the set of points of
the fibre of `φ ≫ snd₂` over `ζ` whose image in `T₂` lies in `E` is preconnected: it is a fibre
of the base change of `f'` to `h_V`. -/
theorem isPreconnected_preimage_of_subsingleton_pullback
    {X Y' X₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f' : X ⟶ Y'} {T₂ W₂ : BigFppfOver B S hS}
    {q₂ : yoneda.obj T₂ ⟶ Y'} {a₂ : X₂ ⟶ X} {φ : X₂ ⟶ yoneda.obj T₂}
    (sq₂ : IsPullback a₂ φ f' q₂)
    (hconn : ∀ y : GeometricPoint B S hS Y',
      ConnectedPullback B S hS f' (yonedaEquiv.symm y.val.value))
    (snd₂ : T₂ ⟶ W₂) (E : Set ((BigFppfOver.toScheme B S hS).obj T₂))
    (ζ : GeometricPoint B S hS (yoneda.obj W₂))
    (huniq : ∀ v v' : (BigFppfOver.toScheme B S hS).obj
        (pullback snd₂ (ζ.val.value : ζ.val.siteObject ⟶ W₂)),
      (BigFppfOver.toScheme B S hS).map (pullback.fst snd₂ (ζ.val.value : _ ⟶ W₂)) v ∈ E →
      (BigFppfOver.toScheme B S hS).map (pullback.fst snd₂ (ζ.val.value : _ ⟶ W₂)) v' ∈ E →
        v = v') :
    IsPreconnected (pointsMap B S hS _
      (pullback.fst (φ ≫ yoneda.map snd₂) (yonedaEquiv.symm ζ.val.value)) ⁻¹'
        {x | pointsToScheme B S hS T₂ (pointsMap B S hS X₂ φ x) ∈ E}) := by
  set ωs : ζ.val.siteObject ⟶ W₂ := ζ.val.value
  set k : yoneda.obj ζ.val.siteObject ⟶ yoneda.obj W₂ := yonedaEquiv.symm ζ.val.value
  have hk : k = yoneda.map ωs :=
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map ωs).symm
  set g₂ := φ ≫ yoneda.map snd₂
  set V := pullback snd₂ ωs
  have hVy : IsPullback (yoneda.map (pullback.fst snd₂ ωs)) (yoneda.map (pullback.snd snd₂ ωs))
      (yoneda.map snd₂) k := by
    rw [hk]
    exact Functor.map_isPullback yoneda (IsPullback.of_hasPullback snd₂ ωs)
  obtain ⟨bF, hleft, -⟩ := exists_isPullback_factorization (f := g₂) rfl hVy
  have hbFfst : bF ≫ yoneda.map (pullback.fst snd₂ ωs) = pullback.fst g₂ k ≫ φ :=
    hleft.w.symm
  have hfib := isPreconnected_setOf_pointsMap_eq_of_isPullback (hleft.paste_horiz sq₂) hconn
  -- the set in question is a preimage under `bF` of a set with at most one point
  set D : Set (points B S hS (yoneda.obj V)) := {v | (BigFppfOver.toScheme B S hS).map
    (pullback.fst snd₂ ωs) (pointsToScheme B S hS V v) ∈ E}
  have hD : ∀ v ∈ D, ∀ v' ∈ D, v = v' := fun v hv v' hv' =>
    injective_pointsToScheme B S hS V (huniq _ _ hv hv')
  have hset : pointsMap B S hS _ (pullback.fst g₂ k) ⁻¹'
      {x | pointsToScheme B S hS T₂ (pointsMap B S hS X₂ φ x) ∈ E} =
        pointsMap B S hS _ bF ⁻¹' D := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, D]
    rw [← pointsMap_comp_apply, ← hbFfst, pointsMap_comp_apply, pointsToScheme_pointsMap]
    rfl
  rw [hset]
  by_cases hne : ∃ v₀, v₀ ∈ D
  · obtain ⟨v₀, hv₀⟩ := hne
    have h2 : pointsMap B S hS _ bF ⁻¹' D = {ξ | pointsMap B S hS _ bF ξ = v₀} := by
      ext ξ
      exact ⟨fun h => hD _ h _ hv₀, fun h => by rw [Set.mem_preimage, h]; exact hv₀⟩
    rw [h2]
    exact hfib v₀
  · have h2 : pointsMap B S hS _ bF ⁻¹' D = ∅ :=
      Set.eq_empty_of_forall_notMem fun ξ hξ => hne ⟨_, hξ⟩
    rw [h2]
    exact isPreconnected_empty

/-! ### A compact chart dominating a represented target -/

/-- Let `φ : Z ⟶ h_T` be surjective on points from a quasi-compact algebraic space, and let
`p : T ⟶ W` be a morphism of the site with `φ ≫ p` locally of finite type.  Then there is a
morphism `g : U ⟶ T` of the site with `U` compact, surjective on underlying schemes, whose
composite with `p` is locally of finite type. -/
theorem exists_compact_surjective_chart {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T W : BigFppfOver B S hS} (φ : Z ⟶ yoneda.obj T) (p : T ⟶ W)
    (hφ : Function.Surjective (pointsMap B S hS Z φ)) (hqc : IsQuasiCompactSpace B S hS Z)
    (hlft : IsLocallyOfFiniteType B S hS (φ ≫ yoneda.map p)) :
    ∃ (U : BigFppfOver B S hS) (g : U ⟶ T),
      CompactSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
      Function.Surjective ((BigFppfOver.toScheme B S hS).map g) ∧
      LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g ≫
        (BigFppfOver.toScheme B S hS).map p) := by
  obtain ⟨U, a, hUcpt, hasurj, haetale⟩ := hqc
  have hgmap : yoneda.map (Yoneda.fullyFaithful.preimage (a ≫ φ)) = a ≫ φ :=
    Yoneda.fullyFaithful.map_preimage _
  refine ⟨U, Yoneda.fullyFaithful.preimage (a ≫ φ), hUcpt, ?_, ?_⟩
  · have hpts : Function.Surjective (pointsMap B S hS (yoneda.obj U)
        (yoneda.map (Yoneda.fullyFaithful.preimage (a ≫ φ)))) := by
      rw [hgmap, pointsMap_comp]
      exact hφ.comp (isSurjective_of_presheafSurjective B S hS a hasurj)
    have hsurj' : AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map
        (Yoneda.fullyFaithful.preimage (a ≫ φ))) :=
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).mp
        ((surjective_yonedaMap_iff_surjective_pointsMap B S hS _).mpr hpts)
    exact (AlgebraicGeometry.surjective_iff _).mp hsurj'
  · have h := hlft U W a (𝟙 _) (Yoneda.fullyFaithful.preimage (a ≫ φ) ≫ p)
      (presheaf_etale_of_isEtale B S hS haetale) (presheaf_etale_id B S hS W)
      (by rw [Category.comp_id, Functor.map_comp, hgmap, Category.assoc])
    rwa [Functor.map_comp] at h

/-! ### Base change to a represented presheaf -/

/-- The base change of a flat morphism of finite presentation of algebraic spaces along a
morphism from a represented presheaf is flat and of finite presentation. -/
theorem isFlat_and_isFinitePresentation_pullback_snd {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hflat : IsFlat B S hS f) (hfp : IsFinitePresentation B S hS f) {W : BigFppfOver B S hS}
    (g : yoneda.obj W ⟶ Y) :
    IsFlat B S hS (pullback.snd f g) ∧ IsFinitePresentation B S hS (pullback.snd f g) := by
  have hW := isAlgebraicSpace_yoneda B S hS W
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
    (ObjectProperty.homMk g : (⟨yoneda.obj W, hW⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
  exact ⟨(isFlat_isStableUnderBaseChange B S hS).of_isPullback sq hflat,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃A C : AlgebraicSpaces B S hS⦄ (k : A ⟶ C) ↦ IsFinitePresentation B S hS k.hom)
      sq hfp⟩

/-! ### The local statement at an affine chart -/

/-- **The heart of Stacks 0E1D.**  Let `f = π ∘ f'` with `f'` surjective with connected
geometric fibres and `π` integral, `f` flat and of finite presentation, and let `t : h_W ⟶ Y`
come from an affine object `W` of the site, with a point `w` of `h_W`.  After an étale base
change `τ : W₂ ⟶ W` hitting `w` at `w₂`, the number of geometric connected components of the
fibres of the base change of `f` to `h_{W₂}` is, on an open neighbourhood of `w₂`, at least its
value at `w₂`. -/
theorem exists_etale_isOpen_le_numberGeometricConnectedComponents
    {X Y Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (f' : X ⟶ Y') (π : Y' ⟶ Y) (hfac : f' ≫ π = f)
    (hsurj : Function.Surjective (pointsMap B S hS X f'))
    (hconn : ∀ y : GeometricPoint B S hS Y',
      ConnectedPullback B S hS f' (yonedaEquiv.symm y.val.value))
    (hπ : IsIntegralHom B S hS π) (hflat : IsFlat B S hS f)
    (hfp : IsFinitePresentation B S hS f)
    (W : BigFppfOver B S hS) (hWaff : IsAffine ((BigFppfOver.toScheme B S hS).obj W))
    (t : yoneda.obj W ⟶ Y) (w : points B S hS (yoneda.obj W)) :
    ∃ (W₂ : BigFppfOver B S hS) (τ : W₂ ⟶ W), Etale ((BigFppfOver.toScheme B S hS).map τ) ∧
      ∃ w₂ : points B S hS (yoneda.obj W₂), pointsMap B S hS _ (yoneda.map τ) w₂ = w ∧
        ∃ O : Set (points B S hS (yoneda.obj W₂)), IsOpen O ∧ w₂ ∈ O ∧ ∀ z ∈ O,
          numberGeometricConnectedComponents B S hS (pullback.snd f (yoneda.map τ ≫ t)) w₂ ≤
            numberGeometricConnectedComponents B S hS (pullback.snd f (yoneda.map τ ≫ t)) z := by
  classical
  have hWalg := isAlgebraicSpace_yoneda B S hS W
  -- the integral base change `T` of `π`
  obtain ⟨T, p, q, hpb, hTaff, hpint⟩ := hπ W hWaff t
  -- the base change of `f` to `h_W` and its factorization through `h_T`
  obtain ⟨φW, sqW, hφWsnd⟩ := exists_isPullback_factorization hfac hpb
  have hφWsurj : Function.Surjective (pointsMap B S hS _ φW) :=
    surjective_pointsMap_of_isPullback B S hS sqW hsurj
  obtain ⟨hflatW, hfpW⟩ := isFlat_and_isFinitePresentation_pullback_snd hX hY f hflat hfp t
  have hqcW : IsQuasiCompactSpace B S hS (pullback f t) :=
    isQuasiCompactSpace_of_iso B S hS (pullbackSymmetry t f)
      (hfp.2.1 (yoneda.obj W) hWalg (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) t)
  obtain ⟨U, gU, hUcpt, hgUsurj, hgUlft⟩ := exists_compact_surjective_chart φW p hφWsurj hqcW
    (by rw [hφWsnd]; exact isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS hfpW.1)
  -- the étale-local splitting of `T ⟶ W`
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) := hTaff
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W) := hWaff
  have : _root_.AlgebraicGeometry.IsIntegralHom ((BigFppfOver.toScheme B S hS).map p) := hpint
  have := hUcpt
  have := hgUlft
  obtain ⟨R', τ, hτ, w₂, hτw₂, m, hsplit⟩ := exists_etale_clopen_splitting_of_isIntegralHom
    ((BigFppfOver.toScheme B S hS).map gU) ((BigFppfOver.toScheme B S hS).map p) hgUsurj
    (pointsToScheme B S hS W w)
  -- the étale neighbourhood as an object of the site
  have hW₂ : B.Contains (Spec R') :=
    (Scheme.size_le_of_locallyOfFiniteType τ).trans_lt W.left.property
  let W₂ : BigFppfOver B S hS := BigFppfOver.mk B S hS hW₂ (τ ≫ B.inclusion.map W.hom)
  let τ' : W₂ ⟶ W := Over.homMk (ObjectProperty.homMk τ) rfl
  have hτ' : (BigFppfOver.toScheme B S hS).map τ' = τ := rfl
  have hW₂alg := isAlgebraicSpace_yoneda B S hS W₂
  -- the fibre product `T₂ = T ×_W W₂` and its pieces
  let T₂ := pullback p τ'
  let fst₂ : T₂ ⟶ T := pullback.fst p τ'
  let snd₂ : T₂ ⟶ W₂ := pullback.snd p τ'
  have hPs : IsPullback ((BigFppfOver.toScheme B S hS).map fst₂)
      ((BigFppfOver.toScheme B S hS).map snd₂) ((BigFppfOver.toScheme B S hS).map p) τ :=
    Functor.map_isPullback (BigFppfOver.toScheme B S hS) (IsPullback.of_hasPullback p τ')
  obtain ⟨E, hEcl, hEdisj, hEcov, hEmeet, hEuniq⟩ := hsplit _ _ hPs
  have hY2 : IsPullback (yoneda.map fst₂) (yoneda.map snd₂) (yoneda.map p) (yoneda.map τ') :=
    Functor.map_isPullback yoneda (IsPullback.of_hasPullback p τ')
  have hpb₂ := hY2.paste_horiz hpb
  set t₂ := yoneda.map τ' ≫ t with ht₂
  -- the base change of `f` to `h_{W₂}` and its factorization through `h_{T₂}`
  obtain ⟨φ, sq₂, hφsnd⟩ := exists_isPullback_factorization hfac hpb₂
  have hφsurj : Function.Surjective (pointsMap B S hS _ φ) :=
    surjective_pointsMap_of_isPullback B S hS sq₂ hsurj
  have hX₂ : IsAlgebraicSpace B S hS (pullback f t₂) :=
    isAlgebraicSpace_pullback B S hS f t₂ hX hW₂alg hY
  obtain ⟨hflat₂, hfp₂⟩ := isFlat_and_isFinitePresentation_pullback_snd hX hY f hflat hfp t₂
  have hopen : IsOpenMap (pointsMap B S hS _ (pullback.snd f t₂)) :=
    isOpen_of_universallyOpen B S hS hW₂alg _
      (universallyOpen_of_isFlat_of_isLocallyOfFinitePresentation B S hS hX₂ hW₂alg _
        hflat₂ hfp₂.1)
  let Pc : Fin m → Set (points B S hS (pullback f t₂)) := fun i =>
    {x | pointsToScheme B S hS T₂ (pointsMap B S hS _ φ x) ∈ E i}
  have hPccl : ∀ i, IsClopen (Pc i) := fun i =>
    (hEcl i).preimage ((schemePointsHomeomorph B S hS T₂).continuous.comp
      (continuous_pointsMap B S hS φ))
  have hPcdisj : Pairwise fun i j => Disjoint (Pc i) (Pc j) := fun i j hij =>
    (hEdisj hij).preimage _
  have hPccov : ∀ x, ∃ i, x ∈ Pc i := fun x => hEcov _
  -- the open neighbourhood
  let w₂' : points B S hS (yoneda.obj W₂) := (schemePointsHomeomorph B S hS W₂).symm w₂
  have hw₂' : pointsToScheme B S hS W₂ w₂' = w₂ :=
    (schemePointsHomeomorph B S hS W₂).apply_symm_apply w₂
  let O : Set (points B S hS (yoneda.obj W₂)) :=
    ⋂ i, pointsMap B S hS _ (pullback.snd f t₂) '' Pc i
  have hOopen : IsOpen O := isOpen_iInter_of_finite fun i => hopen _ (hPccl i).isOpen
  have hw₂O : w₂' ∈ O := by
    refine Set.mem_iInter.mpr fun i => ?_
    obtain ⟨x, hxE, hxw⟩ := hEmeet i
    obtain ⟨ξ, hξ⟩ := hφsurj ((schemePointsHomeomorph B S hS T₂).symm x)
    refine ⟨ξ, ?_, ?_⟩
    · change pointsToScheme B S hS T₂ (pointsMap B S hS _ φ ξ) ∈ E i
      rw [hξ]
      change (schemePointsHomeomorph B S hS T₂) ((schemePointsHomeomorph B S hS T₂).symm x) ∈ E i
      rwa [Homeomorph.apply_symm_apply]
    · apply injective_pointsToScheme B S hS W₂
      rw [← hφsnd, pointsMap_comp_apply, hξ, pointsToScheme_pointsMap, hw₂']
      change (BigFppfOver.toScheme B S hS).map snd₂
        ((schemePointsHomeomorph B S hS T₂) ((schemePointsHomeomorph B S hS T₂).symm x)) = w₂
      rwa [Homeomorph.apply_symm_apply]
  refine ⟨W₂, τ', hτ, w₂', ?_, O, hOopen, hw₂O, fun z hz => ?_⟩
  · apply injective_pointsToScheme B S hS W
    rwa [pointsToScheme_pointsMap, hw₂', hτ']
  rw [← hφsnd]
  refine le_trans ?_ (natCast_le_numberGeometricConnectedComponents hX₂ hW₂alg _ Pc hPccl
    hPcdisj z ?_)
  · obtain ⟨ζ, hζ⟩ := exists_geometricRepresentative B S hS _ w₂'
    rw [← hζ]
    refine numberGeometricConnectedComponents_le_natCast hX₂ hW₂alg _ Pc hPccov ζ
      fun i => ?_
    refine isPreconnected_preimage_of_subsingleton_pullback sq₂ hconn snd₂ (E i) ζ ?_
    intro v v' hv hv'
    have hω : ∀ x, (BigFppfOver.toScheme B S hS).map
        (ζ.val.value : ζ.val.siteObject ⟶ W₂) x = w₂ := by
      intro x
      have hx : x = IsLocalRing.closedPoint ζ.val.carrier :=
        @Subsingleton.elim _ (inferInstanceAs (Subsingleton (Spec (CommRingCat.of ζ.val.carrier))))
          x _
      rw [hx, ← hw₂', ← hζ]
      rfl
    exact hEuniq ζ.val.carrier ((BigFppfOver.toScheme B S hS).map ζ.val.value) hω _ _
      (Functor.map_isPullback (BigFppfOver.toScheme B S hS)
        (IsPullback.of_hasPullback snd₂ (ζ.val.value : ζ.val.siteObject ⟶ W₂))) i v v' hv hv'
  · rw [hφsnd]
    exact Set.mem_iInter.mp hz

/-! ### Stacks 0E1D -/

variable (B S hS) in
/-- **Stacks 0E1D.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is proper,
flat and of finite presentation.  Then the function `n_{X/Y} : |Y| → ℕ∞` counting the geometric
connected components of the fibres of `f` (Stacks 0E1B,
`AlgebraicGeometry.Space.numberGeometricConnectedComponents`) is lower semicontinuous. -/
@[stacks 0E1D, ega "IV 15.5.9" "more general"]
theorem lowerSemicontinuous_numberGeometricConnectedComponents
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hproper : IsProper B S hS f)
    (hflat : IsFlat B S hS f) (hfp : IsFinitePresentation B S hS f) :
    LowerSemicontinuous (numberGeometricConnectedComponents B S hS f) := by
  intro y c hc
  suffices h : ∃ O : Set (points B S hS Y), IsOpen O ∧ y ∈ O ∧ ∀ y' ∈ O,
      numberGeometricConnectedComponents B S hS f y ≤
        numberGeometricConnectedComponents B S hS f y' by
    obtain ⟨O, hO, hyO, hle⟩ := h
    filter_upwards [hO.mem_nhds hyO] with y' hy' using lt_of_lt_of_le hc (hle y' hy')
  -- the Stein factorization `X ⟶ Y' ⟶ Y` (Stacks 0A1C)
  let XA : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let YA : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let fA : XA ⟶ YA := ObjectProperty.homMk f
  let hfqc := isQuasiCompact_of_universallyClosed B S hS hX hY f hproper.2.2
  let hfqs := isQuasiSeparated_of_isSeparated B S hS hproper.1
  obtain ⟨hcomp, ⟨-, hconn⟩, hint, -, -, -⟩ := steinFactorization_general_complete fA hproper
  have hsurj : IsSurjective B S hS (toNormalizationInQcqs fA hfqc hfqs).hom :=
    isSurjective_of_isRelativeNormalization B S hS
      (isRelativeNormalization_normalizationInQcqs fA hfqc hfqs) hX
      (normalizationInQcqs B S hS fA hfqc hfqs).2
      (isQuasiCompact_toNormalizationInQcqs B S hS fA hfqc hfqs)
      (universallyClosed_toNormalizationInQcqs B S hS fA hfqc hfqs hproper.2.2)
  have hfac : (toNormalizationInQcqs fA hfqc hfqs).hom ≫
      (normalizationInQcqsHom B S hS fA hfqc hfqs).hom = f :=
    congrArg (fun k : XA ⟶ YA => k.hom) hcomp
  -- an affine étale chart at `y`
  obtain ⟨W, t, hWaff, ht, w, hw⟩ := exists_affine_etale_chart_at_point B S hS Y hY y
  obtain ⟨W₂, τ, hτ, w₂, hw₂, O, hO, hw₂O, hle⟩ :=
    exists_etale_isOpen_le_numberGeometricConnectedComponents hX hY f _ _ hfac hsurj hconn hint
      hflat hfp W hWaff t w
  -- transport along the étale morphism `h_{W₂} ⟶ Y`
  have ht₂ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map τ ≫ t) :=
    presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS (etale_yoneda B S hS τ hτ) (isEtale_of_presheaf_etale B S hS ht))
  have hbc := numberGeometricConnectedComponents_baseChange B S hS hX hY
    (isAlgebraicSpace_yoneda B S hS W₂) f (yoneda.map τ ≫ t)
  have hyw₂ : pointsMap B S hS _ (yoneda.map τ ≫ t) w₂ = y := by
    rw [pointsMap_comp_apply, hw₂, hw]
  refine ⟨pointsMap B S hS _ (yoneda.map τ ≫ t) '' O,
    isOpenMap_pointsMap_of_etale B S hS hY W₂ _ ht₂ O hO, ⟨w₂, hw₂O, hyw₂⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  have h := hle z hz
  rw [hbc, Function.comp_apply, Function.comp_apply, hyw₂] at h
  exact h

end AlgebraicGeometry.Space

end
