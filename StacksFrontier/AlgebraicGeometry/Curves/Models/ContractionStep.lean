module

public import StacksFrontier.AlgebraicGeometry.Models.Basic
public import StacksFrontier.AlgebraicGeometry.NodalContraction.CentreFibre
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Flat
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.ProjectiveContraction
public import StacksFrontier.AlgebraicGeometry.RestrictIso

/-!
# Contracting one exceptional curve on a regular projective model

Let `R` be a discrete valuation ring with fraction field `K`, and let `X ⟶ Spec R` be a regular
model, projective over `R`, of a `K`-scheme `C`. If `E ⊆ X` is an exceptional curve of the first
kind, then `E` can be contracted: there is a contraction `b : X ⟶ X'` of `E`, and `X'` is again a
regular model of `C`, projective over `R`. Moreover the special fibre of `X'` has one point of
codimension one fewer than the special fibre of `X`, the missing point being the generic point of
`E`. This is the single step of the proof of [Stacks, Tag 0CD9], and the count of those points is
its termination measure.

The proof follows the source. The curve `E ≅ 𝐏¹_k` has a field of global functions, so it maps
to one point of `Spec R`, and [Stacks, Tag 0C2N] (1) contracts it to a scheme `X'` projective over
`R`. The centre `z` of the contraction is a closed point, so it lies over the closed point of
`Spec R`; hence `b` is an isomorphism over the generic point of `Spec R`, and the generic fibre of
`X'` is that of `X`. The scheme `X'` is regular at `z` by the definition of a contraction and
elsewhere because `b` is an isomorphism away from `z`. Flatness of `X'` over `R` is checked on
stalks (`AlgebraicGeometry.flat_of_isContractionOfExceptionalCurve_of_flat_comp`).

## Main definitions

* `Stacks.Models.codimOneSpecialFibrePoints` — the points of the special fibre of a scheme over
  `Spec R` at which the local ring has dimension one.
* `Stacks.Models.codimOneSpecialFibreCard` — the number of those points.

## Main results

* `Stacks.Models.mem_genericPoints_of_mem_codimOneSpecialFibrePoints` — over a flat scheme each
  such point is the generic point of an irreducible component of the special fibre.
* `Stacks.Models.codimOneSpecialFibrePoints_finite` — over a flat Noetherian scheme there are only
  finitely many such points.
* `Stacks.Models.exists_isContractionOfExceptionalCurve_isModel` — the contraction step above.

## Implementation notes

The termination measure counts points of the special fibre whose local ring is one-dimensional,
not irreducible components of the special fibre. It is read through
`AlgebraicGeometry.ringKrullDim_stalk_eq_coheight`, which turns the dimension of a local ring into
the length of chains of generizations, so that most of the bookkeeping is order-theoretic. Over a
flat scheme a point of the special fibre is never a generic point of the total space, since flat
morphisms lift generizations; this places the generic point of `E` in codimension at least one, and
a closed point of `E`, where the local ring is two-dimensional, places it in codimension at most
one.

## References

* [Stacks Project, Tag 0CD9](https://stacks.math.columbia.edu/tag/0CD9)
* [Stacks Project, Tag 0C2N](https://stacks.math.columbia.edu/tag/0C2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Models

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### The termination measure -/

/-- The points of the special fibre of `p : X ⟶ Spec R` at which the local ring of `X` has Krull
dimension one. -/
def codimOneSpecialFibrePoints {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) : Set X :=
  {x | p x = IsLocalRing.closedPoint R ∧ ringKrullDim (X.presheaf.stalk x) = 1}

/-- The number of points of the special fibre of `p : X ⟶ Spec R` at which the local ring of `X`
has Krull dimension one; it is finite when `X` is Noetherian and flat over `R`
(`Stacks.Models.codimOneSpecialFibrePoints_finite`). -/
def codimOneSpecialFibreCard {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) : ℕ :=
  (codimOneSpecialFibrePoints p).ncard

/-- Membership in `Stacks.Models.codimOneSpecialFibrePoints`, read in the specialization order:
the local ring at `x` is one-dimensional exactly when `x` has coheight one. -/
theorem mem_codimOneSpecialFibrePoints_iff {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) (x : X) :
    x ∈ codimOneSpecialFibrePoints p ↔
      p x = IsLocalRing.closedPoint R ∧ Order.coheight x = 1 := by
  change _ ∧ _ ↔ _
  rw [ringKrullDim_stalk_eq_coheight]
  exact and_congr Iff.rfl (by exact_mod_cast Iff.rfl)

private lemma enat_le_one_of_add_one_le_two {c : ℕ∞} (h : c + 1 ≤ 2) : c ≤ 1 := by
  induction c using ENat.recTopCoe with
  | top => simp at h
  | coe n =>
    norm_cast at h ⊢
    omega

private lemma lt_of_specializes_of_ne {X : Scheme.{u}} {x y : X} (h : y ⤳ x) (hne : y ≠ x) :
    x < y :=
  lt_of_le_not_ge (show x ≤ y from h) fun h' => hne (h.antisymm h').eq

/-- A generization of a point of coheight one is equal to it unless it has coheight zero. -/
private lemma eq_of_specializes_of_coheight_eq_one {X : Scheme.{u}} {x y : X} (h : y ⤳ x)
    (hy : 1 ≤ Order.coheight y) (hx : Order.coheight x = 1) : y = x := by
  by_contra hne
  have := (add_le_add_left hy 1).trans
    (hx ▸ Order.coheight_add_one_le (lt_of_specializes_of_ne h hne))
  norm_num at this

private lemma coheight_eq_ofNat_of_coe {c : ℕ∞} (h : (c : WithBot ℕ∞) = 2) : c = 2 :=
  WithBot.coe_injective (h.trans rfl)

/-- A closed point of the spectrum of a discrete valuation ring is its closed point. -/
theorem eq_closedPoint_of_isClosed_singleton (y : Spec (.of R))
    (hy : IsClosed ({y} : Set (Spec (.of R)))) : y = IsLocalRing.closedPoint R :=
  PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal y).mp hy))

/-- The generic point of `Spec R` is not the closed point. -/
theorem bot_ne_closedPoint : (⊥ : PrimeSpectrum R) ≠ IsLocalRing.closedPoint R := fun h =>
  IsDiscreteValuationRing.not_a_field R (congrArg PrimeSpectrum.asIdeal h).symm

/-- The generic fibre of `Spec R` does not meet the closed point. -/
theorem genericFiberSpec_ne_closedPoint (t : Spec (.of K)) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) t ≠ IsLocalRing.closedPoint R := by
  intro h
  have := t.isPrime
  have h2 := congrArg PrimeSpectrum.asIdeal h
  rw [Spec.map_apply] at h2
  change Ideal.comap (algebraMap R K) t.asIdeal = IsLocalRing.maximalIdeal R at h2
  rw [Ideal.eq_bot_of_prime t.asIdeal, ← RingHom.ker_eq_comap_bot,
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R K)] at h2
  exact IsDiscreteValuationRing.not_a_field R h2.symm

/-- Over a flat `R`-scheme no point of the special fibre is a generic point of the total space:
the generization of the closed point of `Spec R` lifts. -/
theorem one_le_coheight_of_flat {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [Flat p] (y : X)
    (hy : p y = IsLocalRing.closedPoint R) : 1 ≤ Order.coheight y := by
  rw [Order.one_le_iff_ne_zero, Ne, Order.coheight_eq_zero]
  intro hmax
  have hspec : @Specializes (Spec (.of R)) _ (⊥ : PrimeSpectrum R) (p y) := by
    rw [hy]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  obtain ⟨y', hy'y, hpy'⟩ := Flat.generalizingMap p hspec
  rw [(hy'y.antisymm (show y ⤳ y' from hmax (show y ≤ y' from hy'y))).eq, hy] at hpy'
  exact bot_ne_closedPoint hpy'.symm

/-- Over a flat `R`-scheme, a point of the special fibre with one-dimensional local ring has no
proper generization in the special fibre. -/
theorem eq_of_specializes_of_mem_codimOneSpecialFibrePoints {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [Flat p] {x y : X} (hx : x ∈ codimOneSpecialFibrePoints p)
    (hy : p y = IsLocalRing.closedPoint R) (hyx : y ⤳ x) : y = x := by
  exact eq_of_specializes_of_coheight_eq_one hyx (one_le_coheight_of_flat p y hy)
    ((mem_codimOneSpecialFibrePoints_iff p x).mp hx).2

/-- Over a flat `R`-scheme, a point of the special fibre with one-dimensional local ring is the
generic point of an irreducible component of the special fibre. -/
theorem mem_genericPoints_of_mem_codimOneSpecialFibrePoints {X : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) [Flat p] {x : X} (hx : x ∈ codimOneSpecialFibrePoints p) :
    (⟨x, hx.1⟩ : (p ⁻¹' {IsLocalRing.closedPoint R} : Set X)) ∈
      genericPoints (p ⁻¹' {IsLocalRing.closedPoint R} : Set X) := by
  set F : Set X := p ⁻¹' {IsLocalRing.closedPoint R}
  have hFcl : IsClosed F := (IsLocalRing.isClosed_singleton_closedPoint R).preimage p.continuous
  refine ⟨isIrreducible_singleton.closure, fun T hT hle t ht => ?_⟩
  have hTX : IsIrreducible (Subtype.val '' T) := hT.image _ continuous_subtype_val.continuousOn
  obtain ⟨y, hy⟩ := QuasiSober.sober hTX.closure isClosed_closure
  have hyF : y ∈ F := closure_minimal (Subtype.coe_image_subset F T) hFcl hy.mem
  have hxT : (⟨x, hx.1⟩ : F) ∈ T := hle (subset_closure rfl)
  have hyx : y ⤳ x := hy.specializes (subset_closure ⟨_, hxT, rfl⟩)
  have hyt : y ⤳ t.1 := hy.specializes (subset_closure ⟨t, ht, rfl⟩)
  rw [eq_of_specializes_of_mem_codimOneSpecialFibrePoints p hx hyF hyx] at hyt
  rw [← specializes_iff_mem_closure]
  exact Topology.IsInducing.subtypeVal.specializes_iff.mp hyt

/-- Over a flat Noetherian `R`-scheme only finitely many points of the special fibre have a
one-dimensional local ring: each is the generic point of an irreducible component of the special
fibre. -/
theorem codimOneSpecialFibrePoints_finite {X : Scheme.{u}} [IsNoetherian X]
    (p : X ⟶ Spec (.of R)) [Flat p] : (codimOneSpecialFibrePoints p).Finite := by
  have hfin : (genericPoints (p ⁻¹' {IsLocalRing.closedPoint R} : Set X)).Finite :=
    genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  exact (hfin.image Subtype.val).subset fun x hx =>
    ⟨⟨x, hx.1⟩, mem_genericPoints_of_mem_codimOneSpecialFibrePoints p hx, rfl⟩

/-! ### Morphisms which are isomorphisms over an open -/

/-- If `b ∣_ W` is an isomorphism, then `b` preserves the coheight of the points mapping into
`W`. -/
private theorem coheight_eq_of_isIso_morphismRestrict {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.Opens)
    [IsIso (b ∣_ W)] {x : X} (hx : b x ∈ W) : Order.coheight (b x) = Order.coheight x := by
  have hx' : x ∈ b ⁻¹ᵁ W := hx
  have h1 := coheight_eq_of_isOpenImmersion (x := (⟨x, hx'⟩ : (b ⁻¹ᵁ W).toScheme)) (b ⁻¹ᵁ W).ι
  have h2 := coheight_eq_of_isOpenImmersion (x := (⟨x, hx'⟩ : (b ⁻¹ᵁ W).toScheme)) (b ∣_ W)
  have h3 := coheight_eq_of_isOpenImmersion (x := (b ∣_ W) ⟨x, hx'⟩) W.ι
  have h4 : W.ι ((b ∣_ W) ⟨x, hx'⟩) = b x := morphismRestrict_base_coe b W ⟨x, hx'⟩
  rw [← h4, h3, h2, ← h1]
  rfl

/-- If `b ∣_ W` is an isomorphism, then `b` induces isomorphisms of the stalks at the points
mapping into `W`. -/
private theorem isIso_stalkMap_of_isIso_morphismRestrict {X Y : Scheme.{u}} (b : X ⟶ Y)
    (W : Y.Opens) [IsIso (b ∣_ W)] {x : X} (hx : b x ∈ W) : IsIso (b.stalkMap x) := by
  have hx' : x ∈ b ⁻¹ᵁ W := hx
  have h := ((isIso_iff_isIso_stalkMap (b ∣_ W)).mp inferInstance).2 ⟨x, hx'⟩
  rw [← MorphismProperty.isomorphisms.iff] at h ⊢
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (morphismRestrictStalkMap b W ⟨x, hx'⟩)).mp h

/-- If `b ∣_ W` is an isomorphism, then `b` is injective on the preimage of `W`. -/
private theorem injOn_of_isIso_morphismRestrict {X Y : Scheme.{u}} (b : X ⟶ Y) (W : Y.Opens)
    [IsIso (b ∣_ W)] : Set.InjOn b.base (b.base ⁻¹' (W : Set Y)) := by
  intro x₁ h₁ x₂ h₂ h
  have h₁' : x₁ ∈ b ⁻¹ᵁ W := h₁
  have h₂' : x₂ ∈ b ⁻¹ᵁ W := h₂
  have h' : (b ∣_ W) ⟨x₁, h₁'⟩ = (b ∣_ W) ⟨x₂, h₂'⟩ :=
    Subtype.ext ((morphismRestrict_base_coe b W ⟨x₁, h₁'⟩).trans
      (h.trans (morphismRestrict_base_coe b W ⟨x₂, h₂'⟩).symm))
  exact congrArg Subtype.val ((b ∣_ W).isOpenEmbedding.injective h')

/-- Let `b : X ⟶ Y` be surjective with `X` regular and `b ∣_ W` an isomorphism. If `Y` is locally
Noetherian with regular local rings at the points outside `W`, then `Y` is regular. -/
private theorem isRegular_of_isIso_morphismRestrict {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (b : X ⟶ Y) (hb : Function.Surjective b.base) (W : Y.Opens) [IsIso (b ∣_ W)]
    (hX : IsRegular X) (hW : ∀ y, y ∉ W → IsRegularLocalRing (Y.presheaf.stalk y)) :
    IsRegular Y := by
  refine ((isRegular_tfae Y).out 1 2 rfl rfl).mpr ⟨inferInstance, fun y => ?_⟩
  by_cases hy : y ∈ W
  · obtain ⟨x, rfl⟩ := hb y
    have := isIso_stalkMap_of_isIso_morphismRestrict b W hy
    have := (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).2 x
    exact IsRegularLocalRing.of_ringEquiv (asIso (b.stalkMap x)).commRingCatIsoToRingEquiv.symm
  · exact hW y hy

/-- Let `b : X ⟶ Y` be a morphism over `Spec R` such that `b ∣_ W` is an isomorphism, where `W`
contains the generic fibre of `Y`. Then `b` induces an isomorphism of generic fibres. -/
private theorem isIso_pullbackMap_genericFiber {X Y : Scheme.{u}} (b : X ⟶ Y) (g : Y ⟶ Spec (.of R))
    (W : Y.Opens) [IsIso (b ∣_ W)] (hW : ∀ y, y ∉ W → g y = IsLocalRing.closedPoint R) :
    IsIso (pullback.map (b ≫ g) (Spec.map (CommRingCat.ofHom (algebraMap R K))) g
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) b (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
  set ι := Spec.map (CommRingCat.ofHom (algebraMap R K))
  have : IsOpenImmersion ι := genericFiberSpec_isOpenImmersion
  let V : Y.Opens := g ⁻¹ᵁ ι.opensRange
  have hVW : V ≤ W := fun y hy => by
    obtain ⟨t, ht⟩ : g y ∈ Set.range ι := hy
    by_contra hyW
    rw [hW y hyW] at ht
    exact genericFiberSpec_ne_closedPoint t ht
  have : IsIso (b ∣_ V) := Stacks.RestrictIso.isIso_morphismRestrict_of_le b hVW inferInstance
  let eg : pullback g ι ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst g ι) V.ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι])
  let ep : pullback (b ≫ g) ι ≅ (b ⁻¹ᵁ V).toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst (b ≫ g) ι) (b ⁻¹ᵁ V).ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι]
      rfl)
  have hm : pullback.map (b ≫ g) ι g ι b (𝟙 _) (𝟙 _) (by simp) (by simp) =
      ep.hom ≫ (b ∣_ V) ≫ eg.inv := by
    rw [← cancel_mono (pullback.fst g ι)]
    simp [ep, eg, morphismRestrict_ι]
  rw [hm]
  infer_instance

/-- Let `b : X ⟶ Y` be surjective and `b ∣_ W` an isomorphism, where no point outside `W` has
coheight one. Let `η ∈ codimOneSpecialFibrePoints (b ≫ g)` map outside `W` and generize every point
mapping outside `W`. Then `b` loses exactly `η` from the termination measure. -/
private theorem codimOneSpecialFibreCard_lt_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    [IsNoetherian X] (b : X ⟶ Y) (g : Y ⟶ Spec (.of R)) [Flat (b ≫ g)]
    (hb : Function.Surjective b.base) (W : Y.Opens) [IsIso (b ∣_ W)]
    (hW : ∀ y, y ∉ W → Order.coheight y ≠ 1) {η : X}
    (hηS : η ∈ codimOneSpecialFibrePoints (b ≫ g)) (hηW : b η ∉ W)
    (hη : ∀ x, b x ∉ W → η ⤳ x) :
    codimOneSpecialFibreCard g < codimOneSpecialFibreCard (b ≫ g) := by
  have hη1 := ((mem_codimOneSpecialFibrePoints_iff _ η).mp hηS).2
  have hnotD : ∀ x ∈ codimOneSpecialFibrePoints (b ≫ g), x ≠ η → b x ∈ W := by
    intro x hx hxη
    by_contra hbx
    exact hxη (eq_of_specializes_of_coheight_eq_one (hη x hbx) hη1.ge
      ((mem_codimOneSpecialFibrePoints_iff _ x).mp hx).2).symm
  have himage : b.base '' (codimOneSpecialFibrePoints (b ≫ g) \ {η}) =
      codimOneSpecialFibrePoints g := by
    ext y
    refine ⟨?_, fun hy => ?_⟩
    · rintro ⟨x, ⟨hx, hxη⟩, rfl⟩
      obtain ⟨hpx, hcx⟩ := (mem_codimOneSpecialFibrePoints_iff _ x).mp hx
      refine (mem_codimOneSpecialFibrePoints_iff _ _).mpr ⟨?_, ?_⟩
      · rwa [← Scheme.Hom.comp_apply]
      · rw [coheight_eq_of_isIso_morphismRestrict b W (hnotD x hx hxη), hcx]
    · obtain ⟨hgy, hcy⟩ := (mem_codimOneSpecialFibrePoints_iff _ y).mp hy
      obtain ⟨x, rfl⟩ := hb y
      have hxW : b x ∈ W := not_not.mp fun h => hW _ h hcy
      refine ⟨x, ⟨(mem_codimOneSpecialFibrePoints_iff _ x).mpr ⟨?_, ?_⟩, ?_⟩, rfl⟩
      · rwa [Scheme.Hom.comp_apply]
      · rw [← coheight_eq_of_isIso_morphismRestrict b W hxW, hcy]
      · exact fun hxη => hηW (Set.mem_singleton_iff.mp hxη ▸ hxW)
  have hinj : Set.InjOn b.base (codimOneSpecialFibrePoints (b ≫ g) \ {η}) :=
    (injOn_of_isIso_morphismRestrict b W).mono fun x hx => hnotD x hx.1 hx.2
  unfold codimOneSpecialFibreCard
  rw [← himage, hinj.ncard_image]
  exact Set.ncard_sdiff_singleton_lt_of_mem hηS (codimOneSpecialFibrePoints_finite (b ≫ g))

/-! ### The exceptional curve -/

/-- A curve isomorphic to `𝐏¹_k` has more than one point. -/
private theorem nontrivial_support_of_iso_projectiveLineProj {X : Scheme.{u}} (D : X.IdealSheafData)
    (k : Type u) [Field k] (eE : projectiveLineProj k ≅ D.subscheme) :
    (D.support : Set X).Nontrivial := by
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k eE
  have hmem : ∀ d, D.subschemeι d ∈ (D.support : Set X) := fun d => by
    rw [← D.range_subschemeι]
    exact ⟨d, rfl⟩
  rw [← Set.not_subsingleton_iff]
  intro hsub
  have : Subsingleton D.subscheme :=
    ⟨fun d d' => D.subschemeι.isClosedEmbedding.injective (hsub (hmem d) (hmem d'))⟩
  have h2 :=
    (_root_.topologicalKrullDimAt_le_topologicalKrullDim (genericPoint D.subscheme)).trans
      (topologicalKrullDim_zero_of_discreteTopology D.subscheme)
  rw [topologicalKrullDimAt_subscheme_eq_one_of_iso_projectiveLineProj D k eE] at h2
  exact absurd h2 (by decide)

/-- For a contraction `b` of an exceptional curve `D`, the local ring at a closed point of `D` is
two-dimensional. -/
private theorem coheight_eq_two_of_isContractionOfExceptionalCurve {X X' : Scheme.{u}}
    {D : X.IdealSheafData} {b : X ⟶ X'} (hb : IsContractionOfExceptionalCurve D b) {x : X}
    (hxD : x ∈ (D.support : Set X)) (hx : IsClosed ({x} : Set X)) : Order.coheight x = 2 := by
  obtain ⟨z, hz, hregz, hdimz, hDz, ε, hε⟩ := hb.exists_blowUp_iso
  have hbx : b x = z := by
    rw [hDz, Scheme.IdealSheafData.support_comap] at hxD
    simpa [Scheme.IdealSheafData.coe_support_vanishingIdeal] using hxD
  have hy : blowUpToBase _ (ε.hom x) = z := by
    rwa [← Scheme.Hom.comp_apply, hε]
  have hycl : IsClosed ({ε.hom x} : Set _) := by
    have := ε.hom.homeomorph.isClosedMap _ hx
    rwa [Set.image_singleton] at this
  have h2 := ringKrullDim_stalk_blowUp_eq_two_of_mapsTo _ z hz rfl hregz hdimz (ε.hom x) hy hycl
  rw [ringKrullDim_stalk_eq_coheight, coheight_eq_of_isOpenImmersion] at h2
  exact coheight_eq_ofNat_of_coe h2

/-- Let `b` contract an exceptional curve `D ≅ 𝐏¹_k` lying in the special fibre of a flat
`p : X ⟶ Spec R`. Then the generic point of `D` has coheight one. -/
private theorem exists_coheight_eq_one_of_isContractionOfExceptionalCurve {X X' : Scheme.{u}}
    [CompactSpace X] (p : X ⟶ Spec (.of R)) [Flat p] (D : X.IdealSheafData) (k : Type u) [Field k]
    (eE : projectiveLineProj k ≅ D.subscheme) {b : X ⟶ X'}
    (hb : IsContractionOfExceptionalCurve D b)
    (hp : ∀ x ∈ (D.support : Set X), p x = IsLocalRing.closedPoint R) :
    ∃ η ∈ (D.support : Set X), (∀ x ∈ (D.support : Set X), η ⤳ x) ∧ Order.coheight η = 1 := by
  have := isIntegral_subscheme_of_iso_projectiveLineProj D k eE
  set η : X := D.subschemeι (genericPoint D.subscheme)
  have hηD : η ∈ (D.support : Set X) := by
    rw [← D.range_subschemeι]
    exact ⟨_, rfl⟩
  have hηspec : ∀ x ∈ (D.support : Set X), η ⤳ x := by
    rw [← D.range_subschemeι]
    rintro _ ⟨d, rfl⟩
    exact (genericPoint_specializes d).map D.subschemeι.continuous
  obtain ⟨x₀, hx₀D, hx₀cl⟩ := D.support.isClosed.exists_closed_singleton ⟨η, hηD⟩
  have hηx₀ : η ≠ x₀ := fun h => by
    obtain ⟨y, hyD, hyx₀⟩ := (nontrivial_support_of_iso_projectiveLineProj D k eE).exists_ne x₀
    have hηy := hηspec y hyD
    rw [h, specializes_iff_mem_closure, hx₀cl.closure_eq] at hηy
    exact hyx₀ hηy
  refine ⟨η, hηD, hηspec, le_antisymm ?_ (one_le_coheight_of_flat p η (hp η hηD))⟩
  have h := Order.coheight_add_one_le (lt_of_specializes_of_ne (hηspec x₀ hx₀D) hηx₀)
  rw [coheight_eq_two_of_isContractionOfExceptionalCurve hb hx₀D hx₀cl] at h
  exact enat_le_one_of_add_one_le_two h

/-! ### The contraction step -/

/-- **Contracting one exceptional curve on a regular projective model.** Let `p : X ⟶ Spec R`,
with the identification `e` of its generic fibre with `C`, be a model of `C` which is projective
over `R` and has regular total space, and let `E ⊆ X` be an exceptional curve of the first kind,
cut out by `D` and presented as `𝐏¹_k` by `eE`. Then there is a contraction `b : X ⟶ X'` of `E`
over `R` such that `X'` is again a model of `C`, proper and projective over `R`, with regular total
space, and whose special fibre has fewer points with one-dimensional local ring. -/
theorem exists_isContractionOfExceptionalCurve_isModel {C X : Scheme.{u}}
    (c : C ⟶ Spec (.of K)) (p : X ⟶ Spec (.of R))
    (e : C ≅ pullback p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    (hmod : IsModel c p e) (hpr : IsProjective p) (hreg : IsRegular X)
    {D : X.IdealSheafData} {k : Type u} [Field k] {eE : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k eE) :
    ∃ (X' : Scheme.{u}) (b : X ⟶ X') (p' : X' ⟶ Spec (.of R))
      (e' : C ≅ pullback p' (Spec.map (CommRingCat.ofHom (algebraMap R K)))),
      IsContractionOfExceptionalCurve D b ∧ b ≫ p' = p ∧ IsModel c p' e' ∧ IsProper p' ∧
        IsProjective p' ∧ IsRegular X' ∧
          codimOneSpecialFibreCard p' < codimOneSpecialFibreCard p := by
  obtain ⟨hflat, hlft, hqc, hc⟩ := hmod
  obtain ⟨s, hs⟩ := exists_const_on_exceptionalCurve D k eE p
  have hs' : ∀ x ∈ (D.support : Set X), p x = s := by
    rw [← D.range_subschemeι]
    rintro _ ⟨d, rfl⟩
    exact hs d
  -- Tag 0C2N (1): the contraction exists and is projective over `R`
  obtain ⟨X', b, g, hb, hbg, hg⟩ :=
    exists_isContractionOfExceptionalCurve_isProjective p hE s hs' hpr
  subst hbg
  have : IsProper g := hg.isProper
  have : IsNoetherian X' := hb.isNoetherian
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (b ≫ g)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (b ≫ g)
  have : IsNoetherian X := ⟨⟩
  have : Flat (b ≫ g) := hflat
  have : Flat g := flat_of_isContractionOfExceptionalCurve_of_flat_comp D k eE b hb g
  have hsurj := surjective_of_isContractionOfExceptionalCurve D k eE b hb
  obtain ⟨z, hz, hregz, hdimz, hDz, ε, hε⟩ := hb.exists_blowUp_iso
  let W : X'.Opens := ⟨({z} : Set X')ᶜ, hz.isOpen_compl⟩
  have : IsIso (b ∣_ W) :=
    isIso_morphismRestrict_compl_of_blowUp_iso _ z hz
      (Scheme.IdealSheafData.coe_support_vanishingIdeal _) ε hε
  have hW : ∀ y, y ∉ W → y = z := fun y hy => not_not.mp hy
  have hmemD : ∀ x : X, x ∈ (D.support : Set X) ↔ b x = z := fun x => by
    rw [hDz, Scheme.IdealSheafData.support_comap]
    simp [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  have hgz : g z = IsLocalRing.closedPoint R :=
    eq_closedPoint_of_isClosed_singleton _ <| by
      simpa only [Set.image_singleton] using g.isClosedMap _ hz
  have hpD : ∀ x ∈ (D.support : Set X), (b ≫ g) x = IsLocalRing.closedPoint R := fun x hx => by
    rw [Scheme.Hom.comp_apply, (hmemD x).mp hx, hgz]
  obtain ⟨η, hηD, hηspec, hη1⟩ :=
    exists_coheight_eq_one_of_isContractionOfExceptionalCurve (b ≫ g) D k eE hb hpD
  have := isIso_pullbackMap_genericFiber (K := K) b g W fun y hy => by rwa [hW y hy]
  refine ⟨X', b, g, e ≪≫ asIso (pullback.map (b ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) g
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) b (𝟙 _) (𝟙 _) _ _),
    hb, rfl, ⟨inferInstance, inferInstance, inferInstance, by simpa using hc⟩, inferInstance, hg,
    isRegular_of_isIso_morphismRestrict b hsurj W hreg fun y hy => by rwa [hW y hy],
    codimOneSpecialFibreCard_lt_of_isIso_morphismRestrict b g hsurj W (fun y hy => ?_)
      ((mem_codimOneSpecialFibrePoints_iff _ η).mpr ⟨hpD η hηD, hη1⟩)
      (fun h => absurd ((hmemD η).mp hηD) h) fun x hx => hηspec x ((hmemD x).mpr (hW _ hx))⟩
  rw [hW y hy, coheight_eq_ofNat_of_coe ((ringKrullDim_stalk_eq_coheight z).symm.trans hdimz)]
  decide

end Stacks.Models

end
