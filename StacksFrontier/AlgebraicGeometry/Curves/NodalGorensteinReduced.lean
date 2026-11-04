module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Reduced
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodalDichotomy
public import StacksFrontier.AlgebraicGeometry.Curves.Node.Multicross
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFieldExtension
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Dualizing.FlatLocalGorenstein
public import StacksFrontier.RingTheory.Dualizing.GorensteinRegularElement
public import StacksFrontier.RingTheory.Dualizing.GorensteinTransport
public import StacksFrontier.Topology.Dimension.Equidimensional

/-!
# Nodal curves are Gorenstein and geometrically reduced

Let `k` be a field and `X` a locally algebraic `k`-scheme, equidimensional of dimension one,
whose singularities are at worst nodal. Then `X` is Gorenstein and `X` is geometrically reduced
over `k`.

Both assertions are proved by passing to an algebraic closure `k̄` of `k`, where every closed
point is either smooth or an ordinary double point, so that the completed local ring is a power
series ring in one variable or the two-branch multicross ring `k̄[[x, y]]/(xy)`. The latter is a
hypersurface in a regular local ring, hence Gorenstein, and it is reduced.

## Main results

* `Stacks.Curves.isGorensteinLocalRing_of_algEquiv_multicross` — a Noetherian local algebra
  isomorphic to the two-branch multicross ring is Gorenstein.
* `Stacks.Curves.isGorensteinLocalRing_stalk_of_hasMulticrossCompletion` — a local ring whose
  completion is the two-branch multicross ring is Gorenstein.
* `Stacks.Curves.isGorensteinLocalRing_stalk_of_smoothAt` — the local ring at a smooth point of
  a scheme over a field is Gorenstein.
* `Stacks.Curves.isGorensteinLocalRing_stalk_of_isNode` — the local ring at a node is Gorenstein.
* `Stacks.Curves.isGorenstein_of_hasAtWorstNodalSingularities` and
  `Stacks.Curves.geometricallyReduced_of_hasAtWorstNodalSingularities` — the two assertions of
  Tag 0E37.
* `Stacks.Curves.smoothAt_of_not_isClosed_of_hasAtWorstNodalSingularities` — such a curve is
  smooth over `k` at every point which is not closed.
* `Stacks.Curves.hasAtWorstNodalSingularities_baseChange` — at-worst-nodal singularities are
  inherited by the base change along an arbitrary field extension.

## Implementation notes

Being locally algebraic over `k` is local finite type of the structure morphism; being
equidimensional of dimension one is `TopologicalSpace.Equidimensional` together with
`topologicalKrullDim X = 1`. Gorensteinness of a scheme is a condition on the local ring at
every point, while nodality only constrains the closed points; at a point that is not closed the
local ring of a one-dimensional reduced scheme is a field, which settles the remaining case.

Base change of nodality along an *arbitrary* extension `K / k` cannot push a closed point of
`X_K` down to a closed point of `X`: for `X = Spec k[u]` and `K = k(t)` the closed point `u = t`
of `X_K` lies over the generic point of `X`. So the proof splits on whether the image point is
closed, and the two branches are settled by different means — the nodal hypothesis in the closed
case, geometric reducedness in the other. Geometric reducedness is proved first and only for an
algebraic closure, which is why the algebraic case is kept as the private
`hasAtWorstNodalSingularities_baseChange_of_isIntegral` feeding Tag 0E37, and the general
statement comes after it.

## References

* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0C56](https://stacks.math.columbia.edu/tag/0C56)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing MvPowerSeries

universe u

namespace Stacks.Curves

/-! ### Gorenstein local rings at nodes -/

/-- A Noetherian local algebra isomorphic to the two-branch multicross ring is Gorenstein: that
ring is the power-series hypersurface `k[[x, y]]/(xy)`, cut out of a regular local ring by a
single nonzerodivisor. -/
theorem isGorensteinLocalRing_of_algEquiv_multicross (K : Type u) [Field K] (A : Type u)
    [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [Algebra K A]
    (e : A ≃ₐ[K] ↥(multicross K 2)) : Dualizing.IsGorensteinLocalRing A := by
  let R := MvPowerSeries (Fin 2) K
  let f : R := X 0 * X 1
  let _ : IsRegularLocalRing R := MvPowerSeries.isRegularLocalRing K 2
  let _ : IsDomain R := IsRegularLocalRing.isDomain _
  have hX : ∀ i : Fin 2, (X i : R) ≠ 0 := by
    intro i h
    have h' := congrArg (MvPowerSeries.coeff (R := K) (Finsupp.single i 1)) h
    simp [MvPowerSeries.coeff_X] at h'
  have hmem : f ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp [f]
  have hnzd : f ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero (hX 0) (hX 1))
  let _ : Nontrivial (R ⧸ Ideal.span {f}) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (lt_of_le_of_lt (Ideal.span_le.2 (Set.singleton_subset_iff.mpr hmem))
        (inferInstance : (maximalIdeal R).IsMaximal).lt_top).ne
  let _ : IsLocalRing (R ⧸ Ideal.span {f}) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {f}))
      Ideal.Quotient.mk_surjective
  have hQ : Dualizing.IsGorensteinLocalRing (R ⧸ Ideal.span {f}) :=
    (Dualizing.isGorensteinLocalRing_quotient_span_singleton_iff R f hmem hnzd).mp
      (Dualizing.IsRegularLocalRing.isGorensteinLocalRing R)
  exact Dualizing.isGorensteinLocalRing_of_ringEquiv
    (e.trans (quotientAlgEquivMulticross (k := K)).symm).toRingEquiv hQ

/-- A Noetherian local ring whose completion at the maximal ideal is Gorenstein is itself
Gorenstein: the completion map is flat and local, and its closed fibre is the residue field. -/
private theorem isGorensteinLocalRing_of_adicCompletion (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A]
    (h : Dualizing.IsGorensteinLocalRing (AdicCompletion (maximalIdeal A) A)) :
    Dualizing.IsGorensteinLocalRing A := by
  let B := AdicCompletion (maximalIdeal A) A
  let _ : IsNoetherianRing B := AdicCompletion.isNoetherianRing (maximalIdeal A)
  exact ((Dualizing.isGorensteinLocalRing_iff_of_flat A B).mp h).1

/-- If the completed local ring at a point of a locally Noetherian scheme over a field is the
two-branch multicross ring, then the local ring at that point is Gorenstein. -/
theorem isGorensteinLocalRing_stalk_of_hasMulticrossCompletion (K : Type u) [Field K]
    (Y : Scheme.{u}) [Y.Over (AlgebraicGeometry.Spec (.of K))] [IsLocallyNoetherian Y] (y : Y)
    (hy : HasMulticrossCompletion K Y y 2) :
    Dualizing.IsGorensteinLocalRing (Y.presheaf.stalk y) := by
  let R := Y.presheaf.stalk y
  let kToStalk : K →+* R :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (Y ↘ AlgebraicGeometry.Spec (.of K)).appTop ≫
      Y.presheaf.germ ⊤ y trivial).hom
  let _ : Algebra K R := kToStalk.toAlgebra
  exact isGorensteinLocalRing_of_adicCompletion R
    (isGorensteinLocalRing_of_algEquiv_multicross K _ hy.some)

/-- A morphism restricted to an open subscheme of the source and to the top open of the target is
smooth iff the composite of the open immersion with the morphism is. -/
private theorem smooth_resLE_top_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) :
    Smooth (f.resLE ⊤ U le_top) ↔ Smooth (U.ι ≫ f) := by
  have heq : f.resLE ⊤ U le_top = (U.ι ≫ f) ≫ Y.topIso.inv := by
    rw [← Scheme.Hom.resLE_comp_ι f (U := ⊤) (V := U) (e := le_top)]
    simp [Category.assoc]
  rw [heq]
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  simpa using (inferInstance : Smooth (((U.ι ≫ f) ≫ Y.topIso.inv) ≫ Y.topIso.hom))

/-- The local ring at a point at which a scheme is smooth over a field is Gorenstein: it is
regular. -/
theorem isGorensteinLocalRing_stalk_of_smoothAt (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))] [IsLocallyNoetherian X] (x : X)
    (hx : InfinitesimalLifting.SmoothAt (X ↘ AlgebraicGeometry.Spec (.of k)) x) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hxU, hs⟩ := hx
  let z : U.toScheme := ⟨x, hxU⟩
  have _ : Smooth (U.ι ≫ (X ↘ AlgebraicGeometry.Spec (.of k))) :=
    (smooth_resLE_top_iff _ U).mp hs
  have hG : AlgebraicGeometry.IsGorenstein U.toScheme :=
    AlgebraicGeometry.isGorenstein_of_isRegular U.toScheme
      (AlgebraicGeometry.isRegular_of_smooth_over_field
        (U.ι ≫ (X ↘ AlgebraicGeometry.Spec (.of k))))
  exact Dualizing.isGorensteinLocalRing_of_ringEquiv
    (asIso (U.ι.stalkMap z)).commRingCatIsoToRingEquiv (hG.isGorensteinLocalRing z)

/-- The local ring at a node of a locally algebraic scheme over a field is Gorenstein: the
ordinary double point above it after base change to an algebraic closure has Gorenstein local
ring, and Gorensteinness of a local ring is unchanged by an extension of the ground field. -/
theorem isGorensteinLocalRing_stalk_of_isNode (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))] [IsLocallyNoetherian X]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))] (x : X) (hx : IsNode k X x) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) := by
  obtain ⟨-, xbar, hxbar, hodp⟩ := hx
  let K := AlgebraicClosure k
  let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback f g : Scheme.{u})
  let _ : Y.Over (AlgebraicGeometry.Spec (.of K)) := ⟨pullback.snd f g⟩
  have _ : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) := by
    show LocallyOfFiniteType (pullback.snd f g)
    infer_instance
  have _ : IsLocallyNoetherian Y :=
    LocallyOfFiniteType.isLocallyNoetherian (Y ↘ AlgebraicGeometry.Spec (.of K))
  exact (AlgebraicGeometry.isGorensteinLocalRing_stalk_iff_of_locallyOfFiniteType
      k K X f x xbar hxbar).mpr
    (isGorensteinLocalRing_stalk_of_hasMulticrossCompletion K Y xbar hodp.2)

/-- The local ring at a point that is not closed, on a reduced scheme of dimension at most one,
is a field, hence Gorenstein. -/
private theorem isGorensteinLocalRing_stalk_of_not_isClosed (X : Scheme.{u})
    [IsLocallyNoetherian X] [AlgebraicGeometry.IsReduced X]
    (hdim : topologicalKrullDim X ≤ 1) (x : X) (hx : ¬ IsClosed ({x} : Set X)) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) := by
  have hbound : ∀ z : X, Order.coheight z ≤ 1 := by
    intro z
    have h : ((Order.coheight z : ℕ∞) : WithBot ℕ∞) ≤ ((1 : ℕ∞) : WithBot ℕ∞) := by
      rw [← AlgebraicGeometry.ringKrullDim_stalk_eq_coheight]
      exact (AlgebraicGeometry.ringKrullDim_stalk_le_topologicalKrullDim z).trans hdim
    exact WithBot.coe_le_coe.mp h
  have hmax : IsMax x := by
    rw [← Order.coheight_eq_zero]
    obtain ⟨z, hz, hzne⟩ : ∃ z ∈ closure ({x} : Set X), z ≠ x := by
      by_contra hc
      push Not at hc
      exact hx (closure_eq_iff_isClosed.mp
        (Set.Subset.antisymm (fun z hz => hc z hz) subset_closure))
    have hzle : z ≤ x := specializes_iff_mem_closure.mpr hz
    have hzlt : z < x :=
      ⟨hzle, fun hxz => hzne ((hxz : Specializes z x).antisymm (hzle : Specializes x z)).eq⟩
    have hlt : Order.coheight x < Order.coheight z :=
      Order.coheight_strictAnti hzlt (lt_of_le_of_lt (hbound x) (by simp))
    simpa using hlt.trans_le (hbound z)
  let _ : Field (X.presheaf.stalk x) := (AlgebraicGeometry.isField_stalk_of_isMax hmax).toField
  exact Dualizing.IsRegularLocalRing.isGorensteinLocalRing _

/-! ### At-worst-nodal singularities after a field extension -/

/-- Base change along an algebraic field extension carries closed points to closed points: the
morphism of spectra is integral, hence so is its base change, and integral morphisms are
closed. -/
private theorem isClosed_image_baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsIntegral k K] {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    (y : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}))
    (hy : IsClosed ({y} : Set _)) :
    IsClosed ({(pullback.fst f
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y} : Set X) := by
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsIntegralHom g :=
    IsIntegralHom.SpecMap_iff.mpr
      (show (CommRingCat.ofHom (algebraMap k K)).hom.IsIntegral from
        algebraMap_isIntegral_iff.mpr inferInstance)
  let p : (pullback f g : Scheme.{u}) ⟶ X := pullback.fst f g
  have : IsIntegralHom p := inferInstance
  simpa only [Set.image_singleton] using p.isClosedMap {y} hy

/-- Smoothness over a field at a point is inherited by the base change along a field extension
at any point above it. -/
private theorem smoothAt_baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec (.of k))
    (y : (pullback f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) :
      Scheme.{u}))
    (hy : InfinitesimalLifting.SmoothAt f
      ((pullback.fst f
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)) :
    InfinitesimalLifting.SmoothAt
      (pullback.snd f (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))) y := by
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p : (pullback f g : Scheme.{u}) ⟶ X := pullback.fst f g
  let q : (pullback f g : Scheme.{u}) ⟶ AlgebraicGeometry.Spec (.of K) := pullback.snd f g
  obtain ⟨U, hxU, hs⟩ := hy
  let V : (pullback f g : Scheme.{u}).Opens := p ⁻¹ᵁ U
  have hyV : y ∈ V := hxU
  have hpb : IsPullback (p ∣_ U) V.ι U.ι p := isPullback_morphismRestrict p U
  have hbig : IsPullback (p ∣_ U) (V.ι ≫ q) (U.ι ≫ f) g := by
    simpa only [Category.assoc] using hpb.paste_vert (IsPullback.of_hasPullback f g)
  have hsm : Smooth (U.ι ≫ f) := (smooth_resLE_top_iff f U).mp hs
  have hsm' : Smooth (V.ι ≫ q) :=
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback hbig hsm : _)
  exact ⟨V, hyV, (smooth_resLE_top_iff q V).mpr hsm'⟩

/-- At-worst-nodal singularities are inherited by the base change of a one-dimensional locally
algebraic scheme along an *algebraic* field extension. This is the special case of
`Stacks.Curves.hasAtWorstNodalSingularities_baseChange` which Tag 0E37 consumes, and which
therefore has to be available before geometric reducedness is known. -/
private theorem hasAtWorstNodalSingularities_baseChange_of_isIntegral
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsIntegral k K] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X) :
    letI : (pullback (X ↘ AlgebraicGeometry.Spec (.of k))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).Over
        (AlgebraicGeometry.Spec (.of K)) :=
      ⟨pullback.snd _ _⟩
    HasAtWorstNodalSingularities K (pullback (X ↘ AlgebraicGeometry.Spec (.of k))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) := by
  intro y hy
  rcases hnodal _ (isClosed_image_baseChange k K (X ↘ AlgebraicGeometry.Spec (.of k)) y hy) with
    hs | hn
  · exact Or.inl (smoothAt_baseChange k K (X ↘ AlgebraicGeometry.Spec (.of k)) y hs)
  · exact Or.inr ((isNode_iff_of_fieldExtension k K X (X ↘ AlgebraicGeometry.Spec (.of k))
      hdim _ y rfl).mp hn)

/-! ### The two assertions of Tag 0E37 -/

/-- **Stacks Project, Tag 0E37.** A locally algebraic scheme over a field, equidimensional of
dimension one and with at-worst-nodal singularities, is Gorenstein. -/
@[stacks 0E37 "nodal_curve_gorenstein"]
theorem isGorenstein_of_hasAtWorstNodalSingularities (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (_hequidim : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) :
    AlgebraicGeometry.IsGorenstein X := by
  have hN : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ AlgebraicGeometry.Spec (.of k))
  let _ : AlgebraicGeometry.IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  refine { toIsLocallyNoetherian := hN, isGorensteinLocalRing := fun x => ?_ }
  by_cases hx : IsClosed ({x} : Set X)
  · rcases hnodal x hx with hs | hn
    · exact isGorensteinLocalRing_stalk_of_smoothAt k X x hs
    · exact isGorensteinLocalRing_stalk_of_isNode k X x hn
  · exact isGorensteinLocalRing_stalk_of_not_isClosed X (le_of_eq hdim) x hx

/-- **Stacks Project, Tag 0E37.** A locally algebraic scheme over a field, equidimensional of
dimension one and with at-worst-nodal singularities, is geometrically reduced. -/
@[stacks 0E37 "nodal_curve_geometrically_reduced"]
theorem geometricallyReduced_of_hasAtWorstNodalSingularities (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (_hequidim : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) :
    GeometricallyReduced (X ↘ AlgebraicGeometry.Spec (.of k)) := by
  let K := AlgebraicClosure k
  let g : AlgebraicGeometry.Spec (.of K) ⟶ AlgebraicGeometry.Spec (.of k) :=
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))
  let Y := (pullback (X ↘ AlgebraicGeometry.Spec (.of k)) g : Scheme.{u})
  let _ : Y.Over (AlgebraicGeometry.Spec (.of K)) :=
    ⟨pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g⟩
  have _ : LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (.of K)) := by
    show LocallyOfFiniteType (pullback.snd (X ↘ AlgebraicGeometry.Spec (.of k)) g)
    infer_instance
  have hY : AlgebraicGeometry.IsReduced Y :=
    isReduced_of_hasAtWorstNodalSingularities K Y
      (hasAtWorstNodalSingularities_baseChange_of_isIntegral k K X hdim hnodal)
  rw [AlgebraicGeometry.geometricallyReduced_iff_baseChange_fieldExtension k K]
  exact AlgebraicGeometry.geometricallyReduced_of_isReduced _

/-! ### At-worst-nodal singularities after an arbitrary field extension -/

/-- **A nodal curve is smooth over the ground field at every point which is not closed.** Such a
point is the generic point of an irreducible component, the space being one-dimensional; the curve
is geometrically reduced over `k` by Tag 0E37, so by Tag 056V it carries a dense open subscheme
smooth over `k`, and a dense open subset of a locally Noetherian scheme contains every generic
point of an irreducible component. -/
theorem smoothAt_of_not_isClosed_of_hasAtWorstNodalSingularities (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequidim : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) {x : X} (hx : ¬ IsClosed ({x} : Set X)) :
    InfinitesimalLifting.SmoothAt (X ↘ AlgebraicGeometry.Spec (.of k)) x := by
  let f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : AlgebraicGeometry.IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  have hgen : x ∈ genericPoints X :=
    closure_singleton_mem_irreducibleComponents_of_not_isClosed hdim.le hx
  obtain ⟨U, hUdense, hUsmooth⟩ :=
    (AlgebraicGeometry.geometricallyReduced_iff_exists_dense_open_smooth f).mp
      (geometricallyReduced_of_hasAtWorstNodalSingularities k X hequidim hdim hnodal)
  exact ⟨U, AlgebraicGeometry.scheme_genericPoints_mem_dense_open X U.2 hUdense hgen,
    (smooth_resLE_top_iff f U).mpr hUsmooth⟩

/-- **At-worst-nodal singularities are inherited by the base change along an arbitrary extension
of the ground field.** Let `X` be a locally algebraic scheme over a field `k`, equidimensional of
dimension one and with at worst nodal singularities, and let `K / k` be any extension of fields,
algebraic or not. Then the base change `X_K` again has at worst nodal singularities.

Without algebraicity a closed point of `X_K` may lie over a point of `X` which is not closed, so
the two alternatives of `Stacks.Curves.HasAtWorstNodalSingularities` are not read off at the image
point directly: the image point is either closed, where the hypothesis applies, or a generic point,
where `Stacks.Curves.smoothAt_of_not_isClosed_of_hasAtWorstNodalSingularities` applies. Smoothness
then descends to `X_K` because `Smooth` is stable under base change, and nodality descends by
Tag 0C56. -/
theorem hasAtWorstNodalSingularities_baseChange (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequidim : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) :
    letI : (pullback (X ↘ AlgebraicGeometry.Spec (.of k))
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).Over
        (AlgebraicGeometry.Spec (.of K)) :=
      ⟨pullback.snd _ _⟩
    HasAtWorstNodalSingularities K (pullback (X ↘ AlgebraicGeometry.Spec (.of k))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) := by
  intro y _
  set x := (pullback.fst (X ↘ AlgebraicGeometry.Spec (.of k))
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y with hxdef
  obtain hs | hn : InfinitesimalLifting.SmoothAt (X ↘ AlgebraicGeometry.Spec (.of k)) x ∨
      IsNode k X x := by
    by_cases hx : IsClosed ({x} : Set X)
    · exact hnodal x hx
    · exact Or.inl (smoothAt_of_not_isClosed_of_hasAtWorstNodalSingularities k X hequidim hdim
        hnodal hx)
  · exact Or.inl (smoothAt_baseChange k K (X ↘ AlgebraicGeometry.Spec (.of k)) y hs)
  · exact Or.inr ((isNode_iff_of_fieldExtension k K X (X ↘ AlgebraicGeometry.Spec (.of k))
      hdim x y hxdef.symm).mp hn)

end Stacks.Curves

end
