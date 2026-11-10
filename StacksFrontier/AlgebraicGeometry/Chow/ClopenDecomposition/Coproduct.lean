module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces

/-!
# The coproduct of a locally finite family of schemes over a base

Chapter 42 of the Stacks Project writes a cycle on a scheme `T` as `∑ nᵢ [Tᵢ]` for a *locally
finite* family of integral closed subschemes `Tᵢ ⊆ T`, and then replaces `T` by the disjoint
union `∐ Tᵢ`, which is proper over `T` and whose Chow groups are the product of the Chow groups
of the pieces. This file supplies that passage:

* the morphism `∐ Zᵢ ⟶ T` assembled from a locally finite family of proper morphisms is itself
  proper — this is the criterion
  `AlgebraicGeometry.isProper_of_locallyFinite_open_closed_cover` of
  `StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.Properness`, applied to the cover of the
  coproduct by its summands;
* the summands of a coproduct form a decomposition into open and closed subschemes, so the
  product decomposition of the Chow groups proved in
  `StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.OpenImmersionPieces` applies to it;
* a family of cycles on the summands assembles into a single cycle on the coproduct.

Everything here is unconditional.

## Main results

* `Stacks.Chow.isProper_sigmaDesc_of_locallyFinite` — the morphism out of a coproduct assembled
  from a locally finite family of proper morphisms is proper.
* `Stacks.Chow.surjectiveOnStalks_sigmaDesc` — it is surjective on stalks as soon as each
  morphism of the family is.
* `Stacks.Chow.isClopenDecomposition_of_isOpenImmersion_cover` — pairwise disjoint open
  immersions covering a scheme present a decomposition into open and closed subschemes.
* `Stacks.Chow.isClopenDecomposition_opensRange_sigmaι` — the summands of a coproduct of schemes
  present such a decomposition of the coproduct.
* `Stacks.Chow.eq_zero_of_chowGroupRestrict_eq_zero` — a Chow class whose restriction to every
  piece of a decomposition into open and closed subschemes vanishes is zero.
* `Stacks.Chow.flatPullbackChow_eq_zero_iff_chowGroupRestrict_eq_zero` — for an open immersion,
  the vanishing of the flat pullback of a Chow class is the vanishing of its restriction.
* `Stacks.Chow.exists_cycleGroup_of_sigma` — a family of `k`-cycles on the summands of a
  coproduct is the family of restrictions of a single `k`-cycle on the coproduct.

## Implementation notes

The index type is restricted to `Type u` because
`Stacks.Chow.chowGroupClopenRestrictEquiv` is, and because a coproduct of `u`-schemes indexed by
a `u`-type is again a `u`-scheme without invoking `Small`.

Properness of `Sigma.desc` goes through the locally finite cover criterion of
`StacksFrontier.AlgebraicGeometry.Chow.ChowToolkit.Properness` rather than through a
local-at-source argument: `AlgebraicGeometry.UniversallyClosed` and
`AlgebraicGeometry.IsSeparated` are not local at the source, and both genuinely use the local
finiteness of the family — for an infinite family of closed immersions with a common point in
their images the assembled morphism is not closed.

## References

* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Closed maps and local finiteness -/

/-- The closures of a locally finite family of points form a locally finite family: a
neighbourhood meeting the closure of a point meets every neighbourhood of that point, so an open
neighbourhood meeting only finitely many of the points meets only finitely many of the
closures. -/
theorem locallyFinite_closure_singleton {A : Type*} [TopologicalSpace A] {J : Type*}
    (x : J → A) (h : LocallyFinite fun j ↦ ({x j} : Set A)) :
    LocallyFinite fun j ↦ closure ({x j} : Set A) := by
  intro y
  obtain ⟨V, hV, hfinite⟩ := h y
  obtain ⟨V', hV'V, hV'open, hyV'⟩ := mem_nhds_iff.mp hV
  refine ⟨V', hV'open.mem_nhds hyV', hfinite.subset fun j hj ↦ ?_⟩
  obtain ⟨z, hzV', hzclosure⟩ := hj
  have hmeet : (V' ∩ ({x j} : Set A)).Nonempty :=
    (mem_closure_iff_nhds.mp hzV') V' (hV'open.mem_nhds hzclosure)
  have hxV' : x j ∈ V' := by simpa using hmeet
  exact ⟨x j, by simp, hV'V hxV'⟩

/-! ### The summands of a coproduct of schemes -/

/-- The inclusion of a summand into a coproduct of schemes is a closed immersion: it is a
preimmersion with closed range, the range being the image of the closed range of the inclusion
of a summand of a disjoint union of topological spaces. -/
theorem isClosedImmersion_sigmaι {I : Type u} (Z : I → Scheme.{u}) (i : I) :
    IsClosedImmersion (Sigma.ι Z i) := by
  apply IsClosedImmersion.of_isPreimmersion
  have hr : Set.range (Sigma.ι Z i).base = sigmaMk Z '' Set.range (Sigma.mk i) := by
    ext x
    refine ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨⟨i, y⟩, ⟨y, rfl⟩, sigmaMk_mk Z i y⟩
    · rintro ⟨⟨j, y⟩, ⟨y', hy'⟩, hx⟩
      refine ⟨y', ?_⟩
      calc (Sigma.ι Z i) y' = sigmaMk Z ⟨i, y'⟩ := (sigmaMk_mk Z i y').symm
        _ = sigmaMk Z ⟨j, y⟩ := congrArg (sigmaMk Z) hy'
        _ = x := hx
  rw [hr]
  exact (sigmaMk Z).isClosedMap _ isClosed_range_sigmaMk

/-- Every point of a coproduct of schemes lies in the range of a summand inclusion. -/
theorem exists_mem_range_sigmaι {I : Type u} (Z : I → Scheme.{u}) (x : (∐ Z : Scheme.{u})) :
    ∃ i, x ∈ Set.range (Sigma.ι Z i) := by
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk Z).surjective x
  exact ⟨i, y, (sigmaMk_mk Z i y).symm⟩

/-- Distinct summands of a coproduct of schemes have disjoint ranges. -/
theorem pairwise_disjoint_range_sigmaι {I : Type u} (Z : I → Scheme.{u}) :
    Pairwise fun i j ↦ Disjoint (Set.range (Sigma.ι Z i)) (Set.range (Sigma.ι Z j)) :=
  fun _ _ hij ↦ Opens.coe_disjoint.mpr (disjoint_opensRange_sigmaι Z _ _ hij)

/-! ### Properness of the morphism out of a coproduct -/

/-- The morphism out of a coproduct assembled from a family of morphisms surjective on stalks
is surjective on stalks: the property is local at the source. -/
theorem surjectiveOnStalks_sigmaDesc {Y : Scheme.{u}} {I : Type u} (Z : I → Scheme.{u})
    (v : ∀ i, Z i ⟶ Y) [∀ i, SurjectiveOnStalks (v i)] : SurjectiveOnStalks (Sigma.desc v) :=
  IsZariskiLocalAtSource.sigmaDesc (P := @SurjectiveOnStalks) fun _ ↦ inferInstance

/-- **The morphism out of a coproduct assembled from a locally finite family of proper
morphisms is proper.** This is the morphism `∐ Zᵢ ⟶ Y` of the proof of Stacks 02UC. -/
theorem isProper_sigmaDesc_of_locallyFinite {Y : Scheme.{u}} {I : Type u} (Z : I → Scheme.{u})
    (f : ∀ i, Z i ⟶ Y) [∀ i, IsProper (f i)]
    (hfinite : LocallyFinite fun i ↦ Set.range (f i)) : IsProper (Sigma.desc f) := by
  have hj (i : I) : IsClosedImmersion (Sigma.ι Z i) := isClosedImmersion_sigmaι Z i
  have hp (i : I) : IsProper (Sigma.ι Z i ≫ Sigma.desc f) := by
    simpa only [Sigma.ι_comp_desc] using (inferInstance : IsProper (f i))
  have _ : IsZariskiLocalAtSource (@LocallyOfFiniteType) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
      (Q := RingHom.FiniteType)
  have _ : LocallyOfFiniteType (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFiniteType) fun _ ↦ inferInstance
  refine AlgebraicGeometry.isProper_of_locallyFinite_open_closed_cover (Sigma.desc f) (Sigma.ι Z)
    (exists_mem_range_sigmaι Z) ?_ ?_
  · exact Stacks.Topology.locallyFinite_of_disjoint_open_cover _
      (fun i ↦ (Sigma.ι Z i).isOpenEmbedding.isOpen_range) (exists_mem_range_sigmaι Z)
      (pairwise_disjoint_range_sigmaι Z)
  · simpa only [Sigma.ι_comp_desc] using hfinite

/-! ### Decompositions presented by open immersions -/

/-- A pairwise disjoint family of open immersions covering a scheme presents a decomposition of
it into open and closed subschemes. -/
theorem isClopenDecomposition_of_isOpenImmersion_cover {X : Scheme.{u}} {I : Type u}
    {W : I → Scheme.{u}} (m : ∀ i, W i ⟶ X) [∀ i, IsOpenImmersion (m i)]
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (m i))
    (hdisjoint : Pairwise fun i l ↦ Disjoint (Set.range (m i)) (Set.range (m l))) :
    IsClopenDecomposition fun i ↦ (m i).opensRange where
  disjoint i l hil := Opens.coe_disjoint.mp (hdisjoint hil)
  iSup_eq_top := by
    refine top_unique fun x _ ↦ ?_
    obtain ⟨i, hi⟩ := hcover x
    exact Opens.mem_iSup.2 ⟨i, hi⟩

/-- The summands of a coproduct of schemes present a decomposition of the coproduct into open
and closed subschemes. -/
theorem isClopenDecomposition_opensRange_sigmaι {I : Type u} (Z : I → Scheme.{u}) :
    IsClopenDecomposition fun i ↦ (Sigma.ι Z i).opensRange :=
  isClopenDecomposition_of_isOpenImmersion_cover (Sigma.ι Z) (exists_mem_range_sigmaι Z)
    (pairwise_disjoint_range_sigmaι Z)

/-! ### Detecting the zero Chow class on the pieces -/

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]

/-- **A Chow class is zero as soon as its restriction to every piece of a decomposition into
open and closed subschemes is zero.** This is the injectivity half of the product decomposition
`CH_k(X) = ∏ᵢ CH_k(Xᵢ)` used in the proof of Stacks 02UC. -/
theorem eq_zero_of_chowGroupRestrict_eq_zero {I : Type u} {W : I → Scheme.{u}}
    (s : ∀ i, W i ⟶ C.S) [∀ i, LocallyOfFiniteType (s i)] (m : ∀ i, W i ⟶ X)
    [∀ i, IsOpenImmersion (m i)] (hm : ∀ i, m i ≫ sX = s i)
    (h : IsClopenDecomposition fun i ↦ (m i).opensRange) (k : ℤ) (α : chowGroup C sX k)
    (hα : ∀ i, chowGroupRestrict C sX (s i) (m i) (hm i) k α = 0) : α = 0 := by
  have hinj := (chowGroupClopenRestrictEquiv C sX s m hm h k).injective
  refine hinj ?_
  rw [map_zero]
  funext i
  rw [chowGroupClopenRestrictEquiv_apply]
  exact hα i

/-! ### Transport of Chow classes along an equality of degrees -/

/-- The transport of the class of a cycle along an equality of degrees is the class of the
transported cycle. -/
theorem cast_chowGroup_mk {k k' : ℤ} (hk : k = k') (c : CycleGroup C sX k) :
    (hk ▸ QuotientAddGroup.mk' (rationalEquivalences C sX k) c : chowGroup C sX k') =
      QuotientAddGroup.mk' (rationalEquivalences C sX k') (hk ▸ c : CycleGroup C sX k') := by
  cases hk
  rfl

/-- The zero Chow classes in two equal degrees are heterogeneously equal. -/
theorem chowGroup_zero_heq {k k' : ℤ} (hk : k = k') :
    HEq (0 : chowGroup C sX k) (0 : chowGroup C sX k') := by
  cases hk
  rfl

/-! ### Flat pullback along an open immersion, and restriction -/

variable {U : Scheme.{u}} (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (j : U ⟶ X)
  [IsOpenImmersion j] (hj : j ≫ sX = sU) (k : ℤ)

/-- Flat pullback of a cycle along an open immersion, transported from degree `k + 0` to degree
`k`, is restriction of that cycle. -/
theorem cast_flatPullback_eq_cycleGroupRestrict (hk : k + ((0 : ℕ) : ℤ) = k)
    (c : CycleGroup C sX k) :
    (hk ▸ flatPullback C sU sX j hj 0 (relativeDimension_of_isOpenImmersion j) k c :
        CycleGroup C sU k) =
      cycleGroupRestrict C sX sU j hj k c := by
  refine Subtype.ext ?_
  rw [val_cycleGroup_cast C sU hk]
  exact (cycleGroupRestrict_eq_flatPullback C sX sU j hj
    (relativeDimension_of_isOpenImmersion j) k c).symm

/-- For an open immersion, the flat pullback of a Chow class vanishes exactly when its
restriction does. The two differ only by the transport of the degree from `k + 0` to `k`. -/
theorem flatPullbackChow_eq_zero_iff_chowGroupRestrict_eq_zero
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sU sX j hj 0
      (relativeDimension_of_isOpenImmersion j) k) (α : chowGroup C sX k) :
    flatPullbackChow C sU sX j hj 0 (relativeDimension_of_isOpenImmersion j) k hfac α = 0 ↔
      chowGroupRestrict C sX sU j hj k α = 0 := by
  have hk : k + ((0 : ℕ) : ℤ) = k := by simp
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    have hcast : ∀ {m : ℤ} (hm : k + ((0 : ℕ) : ℤ) = m)
        (β : CycleGroup C sU (k + ((0 : ℕ) : ℤ))),
        (β ∈ rationalEquivalences C sU (k + ((0 : ℕ) : ℤ)) ↔
          (hm ▸ β : CycleGroup C sU m) ∈ rationalEquivalences C sU m) := by
      intro m hm β
      cases hm
      exact Iff.rfl
    have h1 : (flatPullbackChow C sU sX j hj 0 (relativeDimension_of_isOpenImmersion j) k hfac
          (QuotientAddGroup.mk c) = 0) ↔
        flatPullback C sU sX j hj 0 (relativeDimension_of_isOpenImmersion j) k c ∈
          rationalEquivalences C sU (k + ((0 : ℕ) : ℤ)) := QuotientAddGroup.eq_zero_iff _
    have h2 : (chowGroupRestrict C sX sU j hj k (QuotientAddGroup.mk c) = 0) ↔
        cycleGroupRestrict C sX sU j hj k c ∈ rationalEquivalences C sU k :=
      QuotientAddGroup.eq_zero_iff _
    rw [h1, h2, hcast hk, cast_flatPullback_eq_cycleGroupRestrict C sX sU j hj k hk c]

/-- Flat pullback of a Chow class along an open immersion, transported from degree `k + 0` to
degree `k`, is restriction of that class. -/
theorem cast_flatPullbackChow_eq_chowGroupRestrict (hk : k + ((0 : ℕ) : ℤ) = k)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sU sX j hj 0
      (relativeDimension_of_isOpenImmersion j) k) (α : chowGroup C sX k) :
    (hk ▸ flatPullbackChow C sU sX j hj 0 (relativeDimension_of_isOpenImmersion j) k hfac α :
        chowGroup C sU k) =
      chowGroupRestrict C sX sU j hj k α := by
  induction α using QuotientAddGroup.induction_on with
  | H c =>
    rw [show flatPullbackChow C sU sX j hj 0 (relativeDimension_of_isOpenImmersion j) k hfac
          (QuotientAddGroup.mk c) =
        QuotientAddGroup.mk' (rationalEquivalences C sU (k + ((0 : ℕ) : ℤ)))
          (flatPullback C sU sX j hj 0 (relativeDimension_of_isOpenImmersion j) k c) from rfl,
      cast_chowGroup_mk, cast_flatPullback_eq_cycleGroupRestrict]
    rfl

/-! ### Cycles on a coproduct -/

/-- **A family of `k`-cycles on the summands of a coproduct is the family of restrictions of a
single `k`-cycle on the coproduct.** The coefficient function is assembled summandwise; its
support is locally finite because each summand is open, and it is supported in
delta-dimension `k` because the summand inclusions are open immersions, which do not change the
relative dimension of a point. -/
theorem exists_cycleGroup_of_sigma {I : Type u} (Z : I → Scheme.{u})
    (s : (∐ Z : Scheme.{u}) ⟶ C.S) [LocallyOfFiniteType s] (t : ∀ i, Z i ⟶ C.S)
    [∀ i, LocallyOfFiniteType (t i)] (ht : ∀ i, Sigma.ι Z i ≫ s = t i) (k : ℤ)
    (a : ∀ i, CycleGroup C (t i) k) :
    ∃ γ : CycleGroup C s k, ∀ i (x : Z i), γ.1 (Sigma.ι Z i x) = (a i).1 x := by
  classical
  set F : (∐ Z : Scheme.{u}) → ℤ :=
    fun x ↦ (a ((sigmaMk Z).symm x).1).1 ((sigmaMk Z).symm x).2 with hFdef
  have hF (i : I) (x : Z i) : F (Sigma.ι Z i x) = (a i).1 x := by
    have ht : (sigmaMk Z).symm (Sigma.ι Z i x) = ⟨i, x⟩ := by
      rw [← sigmaMk_mk Z i x]
      exact (sigmaMk Z).symm_apply_apply ⟨i, x⟩
    exact congrArg (fun z : Σ i, Z i ↦ (a z.1).1 z.2) ht
  have hFne (i : I) (x : Z i) (h : F (Sigma.ι Z i x) ≠ 0) : (a i).1 x ≠ 0 := by
    rwa [hF] at h
  have hlocal : LocallyFiniteSupport F := by
    intro x
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk Z).surjective x
    rw [sigmaMk_mk]
    obtain ⟨V, hV, hfin⟩ := (a i).1.locallyFiniteSupport x
    refine ⟨Sigma.ι Z i '' V, (Sigma.ι Z i).isOpenEmbedding.image_mem_nhds.mpr hV,
      (hfin.image (Sigma.ι Z i)).subset ?_⟩
    rintro y ⟨⟨z, hz, rfl⟩, hy⟩
    refine ⟨z, ⟨hz, ?_⟩, rfl⟩
    exact hFne i z hy
  refine ⟨⟨⟨F, fun _ _ ↦ trivial, fun x _ ↦ hlocal x⟩, ?_⟩, hF⟩
  refine (mem_cyclesOfDimension_iff_forall_point C s k _).2 fun x hx ↦ ?_
  obtain ⟨⟨i, z⟩, rfl⟩ := (sigmaMk Z).surjective x
  rw [sigmaMk_mk] at hx ⊢
  have hd := (mem_cyclesOfDimension_iff_forall_point C (t i) k (a i).1).1 (a i).2 z
    (hFne i z hx)
  rw [← ht i, relativeDimension_comp_isOpenImmersion] at hd
  exact hd

end Stacks.Chow

end
