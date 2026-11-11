module

public import StacksFrontier.AlgebraicGeometry.Blowup.FiniteOverLocalDimensionOne
public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.CodimensionOneDivisor.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.Decomposition
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.F6Rank89.CoheightOfSurface
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.EmbeddedResolution.CartierAfterPointBlowups
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupPrincipalization
public import StacksCore.Tactic.StacksAttribute

/-!
# The inverse image of a closed subscheme of a regular surface along point blowups

Let `X` be a regular quasi-compact scheme of dimension at most two and let `Z ⊆ X` be a closed
subscheme containing no irreducible component of `X` of positive dimension. Then there is a
finite sequence of blowups at closed points `Xₙ → … → X₁ → X` along which the inverse image of
`Z` becomes an effective Cartier divisor.

This is [Stacks, Tag 0BIB](https://stacks.math.columbia.edu/tag/0BIB), proved from the
principalization of [Stacks, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH),
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_principalizing`, with no descent
hypothesis of the kind that the earlier form
`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_comap_isEffectiveCartierDivisor` carries.

## Main results

* `exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isRegular` — on a regular
  quasi-compact scheme of dimension at most two, the inverse image of `Z` becomes an effective
  Cartier divisor after finitely many blowups at closed points: [Stacks, Tag 0BIB].
* `support_colon_subset_sdiff_of_comap_eq` — the ideal quotient `Z : E` is the unit ideal on any
  open on which `Z` and `E` agree.
* `PointBlowupChain.exists_finite_forall_exists_isIso_stalkMap` — a sequence of blowups at closed
  points is a local isomorphism away from a finite set.
* `finite_of_isOpen_subset_support_of_pointBlowupChain` — if the inverse image of `Z` along such a
  sequence is an effective Cartier divisor, then every open subset of `X` contained in `Z` is
  finite: the hypothesis on `Z` cannot be weakened to `Z ≠ X`.
* `not_isEffectiveCartierDivisor_comap_of_infinite` — a closed subscheme cut out by the maximal
  ideal at infinitely many regular two-dimensional points never becomes an effective Cartier
  divisor along such a sequence: quasi-compactness cannot be dropped.
* `isNowhereDense_support_of_ne_bot` — on an irreducible regular scheme the literal reading
  `Z ≠ X` of "proper closed subscheme" implies the one used here.
* `exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isNowhereDense` — the source's proof,
  for `Z` containing no irreducible component of `X`.
* `isOpenImmersion_blowUpToBase_of_isClopen` — blowing up an isolated closed point removes it.

## Implementation notes

*Hypotheses.* A regular scheme in the sense of the source is locally Noetherian with regular local
rings, not necessarily quasi-compact; here `AlgebraicGeometry.IsRegular` together with
`CompactSpace X`. Quasi-compactness cannot be dropped: for `X` the disjoint union of countably
many copies of `𝔸²` over a field and `Z` the union of their origins with the reduced structure,
a finite sequence of blowups at closed points modifies only finitely many of the copies, and on
any other copy the inverse image of `Z` is the reduced origin, whose ideal is not locally
principal (`not_isEffectiveCartierDivisor_comap_of_infinite`). The source's own proof uses
quasi-compactness when it asserts that the closed
subscheme `Z'` "set theoretically consists of finitely many closed points", and the
principalization Tag 0AHH that it applies is stated for Noetherian schemes.

"Proper closed subscheme" is taken in the form: every point in the interior of `Z` is an isolated
closed point of `X`, i.e. every irreducible component of `X` inside `Z` is a point. Such
components cannot be excluded, since blowing up an isolated point removes it; the condition is
implied by `IsNowhereDense (Z.support : Set X)` (no component of `X` inside `Z`), to which the
literal reading `Z ≠ X` is equivalent when `X` is irreducible
(`Stacks.ResolutionOfSurfaces.isNowhereDense_support_of_irreducibleSpace`). It is not enough in
general: for `X = 𝔸² ⊔ 𝔸²` and `Z` one of the two copies, that copy is an infinite open subset of
`X` contained in `Z`, so by `finite_of_isOpen_subset_support_of_pointBlowupChain` no sequence of
blowups at closed points turns `Z` into an effective Cartier divisor.

"Dimension `2`" is relaxed to `topologicalKrullDim X ≤ 2`; nothing in the argument needs a point
of codimension two to exist.

## References

* [Stacks Project, Tag 0BIB](https://stacks.math.columbia.edu/tag/0BIB)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 0AGB](https://stacks.math.columbia.edu/tag/0AGB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- The ideal quotient `Z : E` of two sheaves of ideals is the unit ideal on every open on which
`Z` and `E` agree, so its support lies in the part of the support of `Z` outside such an open. -/
public theorem support_colon_subset_sdiff_of_comap_eq {X : Scheme.{u}} (Z E : X.IdealSheafData)
    (hE : ∀ U : X.affineOpens, (E.ideal U : Submodule Γ(X, U) Γ(X, U)).FG) (U : X.Opens)
    (h : Z.comap U.ι = E.comap U.ι) :
    ((Z.colon E hE).support : Set X) ⊆ (Z.support : Set X) \ (U : Set X) := by
  intro x hx
  refine ⟨Scheme.IdealSheafData.support_antitone
    (show Z ≤ Z.colon E hE from fun _ => Ideal.le_colon) hx, fun hxU => ?_⟩
  obtain ⟨V₀, hV, hxV, hVU₀⟩ := exists_isAffineOpen_mem_and_subset hxU
  set V : X.affineOpens := ⟨V₀, hV⟩ with hVdef
  have hVU : V.1 ≤ U := hVU₀
  have hxV' : x ∈ V.1 := hxV
  clear_value V
  have heq : Z.ideal V = E.ideal V := by
    have hV' : Z.comap V.1.ι = E.comap V.1.ι := by
      have := congrArg (fun K => K.comap (X.homOfLE hVU)) h
      simpa only [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι] using this
    have hv := congrArg
      (fun K : V.1.toScheme.IdealSheafData => K.ideal ⟨⊤, isAffineOpen_top _⟩) hV'
    exact eq_of_heq ((Stacks.Divisors.ideal_comap_top_heq Z V).symm.trans
      ((heq_of_eq hv).trans (Stacks.Divisors.ideal_comap_top_heq E V)))
  have htop : (Z.colon E hE).ideal V = ⊤ := by
    refine (Ideal.eq_top_iff_one _).mpr ?_
    rw [Scheme.IdealSheafData.ideal_colon, heq, Submodule.mem_colon]
    intro a ha
    simpa using ha
  have hzero := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := V) hxV').mp hx
  rw [htop] at hzero
  exact (X.mem_zeroLocus_iff _ _).mp hzero 1 (by trivial) (by simpa using hxV')

/-- An open set contained in the support of an effective Cartier divisor is empty. -/
private theorem eq_empty_of_isOpen_subset_supportSet {Y : Scheme.{u}} {D : Y.IdealSheafData}
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor D) {V : Set Y} (hV : IsOpen V)
    (hVD : V ⊆ D.supportSet) : V = ∅ := by
  have hnd := AlgebraicGeometry.isNowhereDense_supportSet_of_isEffectiveCartierDivisor _ hD
  rw [IsNowhereDense, D.isClosed_supportSet.closure_eq] at hnd
  exact Set.subset_empty_iff.mp (hnd ▸ interior_maximal hVD hV)

/-- Every point outside the support of `M` is the image of a point of the blowup of `M`. -/
private theorem exists_blowUpToBase_eq_of_mem_compl_support {X : Scheme.{u}}
    (M : X.IdealSheafData) {y : X} (hy : y ∈ (M.support.compl : X.Opens)) :
    ∃ z, blowUpToBase M z = y := by
  obtain ⟨z, hz⟩ := (blowUpToBase M ∣_ M.support.compl).surjective ⟨y, hy⟩
  refine ⟨z.1, ?_⟩
  have := congrArg Subtype.val hz
  rwa [morphismRestrict_base_coe] at this

/-- A sequence of blowups at closed points is a local isomorphism away from a finite set of
points of the base: every point outside that set is the image of a point at which the induced
map of local rings is an isomorphism. Each blowup is an isomorphism away from its centre, and the
images of the centres form a finite set. -/
public theorem PointBlowupChain.exists_finite_forall_exists_isIso_stalkMap {X Y : Scheme.{u}}
    {T : Set X} {f : Y ⟶ X} (hf : PointBlowupChain X T Y f) :
    ∃ C : Set X, C.Finite ∧ ∀ x ∉ C, ∃ y : Y, f y = x ∧ IsIso (f.stalkMap y) := by
  induction hf with
  | refl => exact ⟨∅, Set.finite_empty, fun x _ => ⟨x, rfl, inferInstance⟩⟩
  | @step W h hh w hw hwT ih =>
    obtain ⟨C, hC, hiso⟩ := ih
    refine ⟨insert (h.base w) C, hC.insert _, fun x hx => ?_⟩
    obtain ⟨w', hw'x, hw'iso⟩ := hiso x fun hxC => hx (Set.mem_insert_of_mem _ hxC)
    set M : W.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩
    have hw' : w' ∈ (M.support.compl : W.Opens) := by
      change w' ∉ (M.support : Set W)
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      intro hmem
      have hww : w' = w := by simpa using hmem
      exact hx (by rw [← hw'x, hww]; exact Set.mem_insert _ _)
    obtain ⟨z, hz'⟩ := exists_blowUpToBase_eq_of_mem_compl_support M hw'
    have : IsIso ((blowUpToBase M).stalkMap z) :=
      isIso_stalkMap_of_isIso_morphismRestrict (blowUpToBase M) inferInstance
        (U := M.support.compl) (show z ∈ (blowUpToBase M) ⁻¹ᵁ M.support.compl from
          show (blowUpToBase M) z ∈ M.support.compl from hz' ▸ hw')
    refine ⟨z, by simp [hz', hw'x], ?_⟩
    rw [Scheme.Hom.stalkMap_comp]
    have hh : IsIso (h.stalkMap ((blowUpToBase M) z)) := hz' ▸ hw'iso
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hh inferInstance

/-- If the inverse image of a closed subscheme `Z` along a sequence of blowups at closed points
is an effective Cartier divisor, then every open subset of the base contained in `Z` is finite.
In particular a closed subscheme containing an irreducible component with infinitely many points
never becomes an effective Cartier divisor along such a sequence, so "proper closed subscheme"
cannot be read as `Z ≠ X` in Tag 0BIB. -/
public theorem finite_of_isOpen_subset_support_of_pointBlowupChain {X Y : Scheme.{u}}
    {T : Set X} {f : Y ⟶ X} (hf : PointBlowupChain X T Y f) (Z : X.IdealSheafData)
    (hZ : Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap f)) {V : Set X} (hV : IsOpen V)
    (hVZ : V ⊆ (Z.support : Set X)) : V.Finite := by
  obtain ⟨C, hC, hiso⟩ := hf.exists_finite_forall_exists_isIso_stalkMap
  refine hC.subset fun x hxV => by_contra fun hxC => ?_
  obtain ⟨y, rfl, -⟩ := hiso x hxC
  have hempty := eq_empty_of_isOpen_subset_supportSet hZ (hV.preimage f.continuous)
    (fun y' hy' => by
      rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
        Scheme.IdealSheafData.support_comap]
      exact hVZ hy')
  exact (hempty ▸ (show f.base y ∈ V from hxV) : y ∈ (∅ : Set Y))

/-- **Quasi-compactness cannot be dropped from Tag 0BIB.** Let `Z` be a closed subscheme of a
scheme `X` and let `P` be an infinite set of points of `X` with regular two-dimensional local
rings at which the ideal of `Z` is the maximal ideal. Then the inverse image of `Z` along a
sequence of blowups at closed points is never an effective Cartier divisor: some point of `P` is
untouched by the finitely many blowups, and there the ideal of the inverse image is the maximal
ideal of a two-dimensional regular local ring, which is not principal.

For `X` the disjoint union of countably many copies of `𝔸²` over a field and `Z` the union of
their origins with the reduced structure, `X` is a regular scheme of dimension two, `Z` contains
no irreducible component of `X`, and the origins form such a set `P`. -/
public theorem not_isEffectiveCartierDivisor_comap_of_infinite {X Y : Scheme.{u}} {T : Set X}
    {f : Y ⟶ X} (hf : PointBlowupChain X T Y f) (Z : X.IdealSheafData) (P : Set X)
    (hP : P.Infinite) (hreg : ∀ p ∈ P, IsRegularLocalRing (X.presheaf.stalk p))
    (hdim : ∀ p ∈ P, ringKrullDim (X.presheaf.stalk p) = 2)
    (hZ : ∀ p ∈ P, AlgebraicGeometry.IdealSheafData.stalk Z p =
      IsLocalRing.maximalIdeal (X.presheaf.stalk p)) :
    ¬ Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap f) := by
  intro hcart
  obtain ⟨C, hC, hiso⟩ := hf.exists_finite_forall_exists_isIso_stalkMap
  obtain ⟨p, hpP, hpC⟩ := (hP.sdiff hC).nonempty
  obtain ⟨y, rfl, hy⟩ := hiso p hpC
  have := hreg _ hpP
  obtain ⟨g, -, hg⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hcart y
  rw [AlgebraicGeometry.IdealSheafData.stalk_comap, hZ _ hpP] at hg
  let e := (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv
  have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk (f y)) =
      Ideal.span {e.symm g} := by
    have h1 := congrArg (Ideal.map e.symm.toRingHom) hg
    rw [Ideal.map_span, Set.image_singleton] at h1
    have he : (CommRingCat.Hom.hom (Scheme.Hom.stalkMap f y)) = e.toRingHom := rfl
    rw [he] at h1
    simpa only [RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv, RingEquiv.coe_toRingHom]
      using h1
  have hle : (IsLocalRing.maximalIdeal (X.presheaf.stalk (f y))).spanFinrank ≤ 1 := by
    rw [hm]
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite
      (R := X.presheaf.stalk (f y)) (Set.finite_singleton (e.symm g))
  have h2 := IsRegularLocalRing.spanFinrank_maximalIdeal (R := X.presheaf.stalk (f y))
  rw [hdim _ hpP] at h2
  have h2' : (IsLocalRing.maximalIdeal (X.presheaf.stalk (f y))).spanFinrank = 2 := by
    exact_mod_cast h2
  omega

/-- On an irreducible regular scheme a closed subscheme other than the whole scheme contains no
irreducible component: a regular scheme is reduced, so a closed subscheme with full support is
the whole scheme. This is the literal reading `Z ≠ X` of the source's "proper closed subscheme",
in the case in which it suffices. -/
public theorem isNowhereDense_support_of_ne_bot {X : Scheme.{u}} [IrreducibleSpace X]
    (hX : AlgebraicGeometry.IsRegular X) (Z : X.IdealSheafData) (hZ : Z ≠ ⊥) :
    IsNowhereDense (Z.support : Set X) := by
  refine isNowhereDense_support_of_irreducibleSpace Z fun h => hZ ?_
  have : IsNormal X := isNormal_of_isRegular X hX
  have : IsReduced X := isReduced_of_isReduced_stalk X
  exact Scheme.IdealSheafData.support_eq_top_iff.mp
    (SetLike.coe_injective (h.trans TopologicalSpace.Closeds.coe_top.symm))

/-- **Tag 0BIB for a closed subscheme containing no irreducible component.** A closed subscheme
`Z` containing no irreducible component of a regular quasi-compact scheme `X` of dimension at most
two becomes an effective Cartier divisor along a sequence of blowups at closed points, each lying
over a point of `Z`.

The proof is the source's. By the two halves of [Stacks, Tag 0AGB] the largest effective Cartier
divisor `E` inside `Z` agrees with `Z` off a set of points of codimension two, which on a
two-dimensional Noetherian scheme is a finite set of closed points with two-dimensional regular
local rings. The ideal quotient `Z : E` is supported there, `Z = E · (Z : E)`, the principalization
[Stacks, Tag 0AHH] (`exists_pointBlowupChain_principalizing`) makes `Z : E` invertible, and the
inverse image of `E` stays Cartier along any sequence of blowups. -/
public theorem exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isNowhereDense
    (X : Scheme.{u}) [CompactSpace X] (hX : AlgebraicGeometry.IsRegular X)
    (hdim : topologicalKrullDim X ≤ 2) (Z : X.IdealSheafData)
    (hZ : IsNowhereDense (Z.support : Set X)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X (Z.support : Set X) Y f ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap f) := by
  classical
  obtain ⟨hlocNoeth, hstalk⟩ :
      IsLocallyNoetherian X ∧ ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    ((AlgebraicGeometry.isRegular_tfae X).out 1 2 (by simp) (by simp)).mp hX
  have : IsNoetherian X := ⟨⟩
  obtain ⟨D, Z', hD, hZ', hcover⟩ :=
    AlgebraicGeometry.exists_integral_effectiveCartierDivisors_cover X Z hZ (Or.inr hX)
  have hcover' : (Z.support : Set X) ⊆
      (Z' : Set X) ∪ ⋃ I : D, ((I.1 : X.IdealSheafData).support : Set X) := by
    simpa only [Set.iUnion_subtype] using hcover
  obtain ⟨a, hE, hZE, U, hU, hcodim⟩ :=
    AlgebraicGeometry.exists_effectiveCartierDivisor_agree_off_codimension_two X Z
      (fun I : D => (I.1 : X.IdealSheafData)) Z' (fun I => hD I.1 I.2) hZ' hcover'
  set E : X.IdealSheafData := a.prod fun I n => (I.1 : X.IdealSheafData) ^ n with hEdef
  set Q : X.IdealSheafData :=
    Z.colon E (AlgebraicGeometry.fg_ideal_of_isEffectiveCartierDivisor E hE) with hQ
  have hfactor : E * Q = Z :=
    AlgebraicGeometry.mul_colon_eq_of_isEffectiveCartierDivisor E Z hE hZE
  have hcoheight : ∀ x ∈ (Z.support : Set X) \ (U : Set X), Order.coheight x = 2 := by
    intro x hx
    have h2 := hcodim x hx.1 hx.2
    rw [Stacks.AlgebraicGeometry.CodimensionOneDivisor.codimension_closureSingleton_eq_coheight]
      at h2
    exact le_antisymm (WithBot.coe_le_coe.mp
      ((AlgebraicGeometry.coheight_le_topologicalKrullDim x).trans hdim)) h2
  have hpoints : ∀ x ∈ (Z.support : Set X) \ (U : Set X), IsClosed ({x} : Set X) :=
    fun x hx => AlgebraicGeometry.isClosed_singleton_of_coheight_two hdim (hcoheight x hx)
  have hstalkDim : ∀ x ∈ (Z.support : Set X) \ (U : Set X),
      ringKrullDim (X.presheaf.stalk x) = 2 := by
    intro x hx
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hcoheight x hx]
    rfl
  have hfinite : ((Z.support : Set X) \ (U : Set X)).Finite := by
    have hT : IsClosed ((Z.support : Set X) \ (U : Set X)) :=
      Z.support.isClosed.inter U.isOpen.isClosed_compl
    obtain ⟨S, hS, hc, hi, hcov⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hT
    rw [hcov]
    refine hS.sUnion fun s hs => ?_
    obtain ⟨x, hx⟩ := QuasiSober.sober (hi s hs) (hc s hs)
    have hxT : x ∈ (Z.support : Set X) \ (U : Set X) :=
      hcov ▸ Set.mem_sUnion.mpr ⟨s, hs, hx.mem⟩
    rw [← hx.def, (hpoints x hxT).closure_eq]
    exact Set.finite_singleton x
  obtain ⟨Y, f, hchain, hQcartier⟩ :=
    exists_pointBlowupChain_principalizing hfinite.toFinset
      (fun x hx => hpoints x (hfinite.mem_toFinset.mp hx))
      (fun x _ => hstalk x)
      (fun x hx => hstalkDim x (hfinite.mem_toFinset.mp hx))
      Q
      (by
        rw [hfinite.coe_toFinset]
        exact support_colon_subset_sdiff_of_comap_eq Z E _ U hU.symm)
  refine ⟨Y, f, hchain.mono (by rw [hfinite.coe_toFinset]; exact Set.sdiff_subset), ?_⟩
  rw [← hfactor, AlgebraicGeometry.comap_mul]
  exact AlgebraicGeometry.isEffectiveCartierDivisor_mul _ _
    (hchain.isEffectiveCartierDivisor_comap hE) hQcartier

/-- **Blowing up an isolated closed point removes it.** If `x` is a point of a scheme `X` with
`{x}` open and closed, the blowup of `X` in the reduced point `x` is an open immersion onto
`X ∖ {x}`: it is an isomorphism away from `x`, and its exceptional divisor, an effective Cartier
divisor whose support is the open preimage of `x`, is empty. -/
public theorem isOpenImmersion_blowUpToBase_of_isClopen {X : Scheme.{u}} {x : X}
    (hx : IsClopen ({x} : Set X)) :
    IsOpenImmersion (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx.isClosed⟩)) ∧
      Set.range (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx.isClosed⟩)).base =
        {x}ᶜ := by
  set M : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx.isClosed⟩
  have hsupp : (M.support : Set X) = {x} := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hempty : (blowUpToBase M).base ⁻¹' {x} = ∅ := by
    refine eq_empty_of_isOpen_subset_supportSet
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M)
      (hx.isOpen.preimage (blowUpToBase M).continuous) fun z hz => ?_
    rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
      Scheme.IdealSheafData.support_comap]
    change (blowUpToBase M) z ∈ (M.support : Set X)
    rwa [hsupp]
  have hne : ∀ z, (blowUpToBase M) z ≠ x := fun z hz => by
    have : z ∈ (blowUpToBase M).base ⁻¹' {x} := hz
    rwa [hempty] at this
  refine ⟨?_, ?_⟩
  · let V : Bool → X.Opens := fun i => cond i M.support.compl ⟨{x}, hx.isOpen⟩
    have hV : iSup V = ⊤ := by
      refine top_unique fun y _ => ?_
      by_cases hy : y = x
      · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨false, hy⟩
      · refine TopologicalSpace.Opens.mem_iSup.mpr ⟨true, ?_⟩
        change y ∉ (M.support : Set X)
        rwa [hsupp]
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsOpenImmersion) V hV fun i => ?_
    cases i
    · have : IsEmpty ((blowUpToBase M) ⁻¹ᵁ V false).toScheme :=
        ⟨fun z => hne z.1 z.2⟩
      exact isOpenImmersion_of_isEmpty _
    · change IsOpenImmersion (blowUpToBase M ∣_ M.support.compl)
      infer_instance
  · refine Set.Subset.antisymm (fun y ⟨z, hz⟩ => hz ▸ hne z) fun y hy => ?_
    have hy' : y ∈ (M.support.compl : X.Opens) := by
      change y ∉ (M.support : Set X)
      rwa [hsupp]
    exact exists_blowUpToBase_eq_of_mem_compl_support M hy'

/-- In a Noetherian space, an open set all of whose points are open is finite. -/
private theorem finite_of_isOpen_of_forall_isOpen_singleton {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {S : Set X} (_hS : IsOpen S) (h : ∀ x ∈ S, IsOpen ({x} : Set X)) :
    S.Finite := by
  obtain ⟨t, ht⟩ := (NoetherianSpace.isCompact S).elim_finite_subcover
    (fun x : S => ({x.1} : Set X)) (fun x => h x.1 x.2)
    fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, rfl⟩
  refine (t.finite_toSet.image Subtype.val).subset fun y hy => ?_
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hy)
  exact ⟨i, hi, (Set.mem_singleton_iff.mp hyi).symm⟩

/-- **Stacks Project, Tag 0BIB.** Let `X` be a regular scheme of dimension (at most) two which is
quasi-compact, and let `Z ⊆ X` be a closed subscheme containing no irreducible component of `X` of
positive dimension: every point in the interior of `Z` is an isolated closed point of `X`. Then
there is a finite sequence `Xₙ → … → X₁ → X` of blowups at closed points, each lying over a point
of `Z`, such that the inverse image `Zₙ` of `Z` in `Xₙ` is an effective Cartier divisor.

On a locally Noetherian scheme the condition says exactly that every irreducible component of `X`
contained in `Z` is a single point; it holds in particular when `Z` contains no irreducible
component of `X` at all (`IsNowhereDense`). The isolated points of `X` inside `Z` are blown up
first, which removes them (`isOpenImmersion_blowUpToBase_of_isClopen`); what is left of `Z` then
contains no irreducible component, and
`exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isNowhereDense` applies.

Both deviations from the literal source are forced. Without quasi-compactness the statement is
false: `Stacks.ResolutionOfSurfaces.not_forall_isEffectiveCartierDivisor_comap_of_isNowhereDense`
(countably many copies of `𝔸²_ℚ`, `Z` one closed point in each). "Proper closed subscheme" cannot
be read literally as `Z ≠ X`, even for Noetherian `X`:
`Stacks.ResolutionOfSurfaces.not_forall_isEffectiveCartierDivisor_comap_of_ne_bot`
(`X = 𝔸²_ℚ ⊔ 𝔸²_ℚ`, `Z` one copy, a component of dimension two). On an irreducible `X` the literal
reading implies the one used here (`isNowhereDense_support_of_ne_bot`). Both counterexamples are in
the sibling module `CartierInverseImageCounterexamples` (same directory). -/
@[stacks 0BIB "a closed subscheme containing no positive-dimensional irreducible component of a \
regular quasi-compact scheme of dimension at most two becomes an effective Cartier divisor after \
finitely many blowups at closed points lying over it"]
public theorem exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isRegular
    (X : Scheme.{u}) [CompactSpace X] (hX : AlgebraicGeometry.IsRegular X)
    (hdim : topologicalKrullDim X ≤ 2) (Z : X.IdealSheafData)
    (hZ : ∀ x ∈ interior (Z.support : Set X), IsClopen ({x} : Set X)) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X (Z.support : Set X) Y f ∧
      Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap f) := by
  classical
  suffices H : ∀ (n : ℕ) (X : Scheme.{u}) [CompactSpace X], AlgebraicGeometry.IsRegular X →
      topologicalKrullDim X ≤ 2 → ∀ Z : X.IdealSheafData,
      (∀ x ∈ interior (Z.support : Set X), IsClopen ({x} : Set X)) →
      (interior (Z.support : Set X)).Finite → (interior (Z.support : Set X)).ncard = n →
      ∃ (Y : Scheme.{u}) (f : Y ⟶ X), PointBlowupChain X (Z.support : Set X) Y f ∧
        Stacks.Divisors.IsEffectiveCartierDivisor (Z.comap f) by
    have : IsLocallyNoetherian X := ((isRegular_iff_regular_stalks X).mp hX).1
    have : IsNoetherian X := ⟨⟩
    exact H _ X hX hdim Z hZ (finite_of_isOpen_of_forall_isOpen_singleton isOpen_interior
      fun x hx => (hZ x hx).isOpen) rfl
  intro n
  induction n with
  | zero =>
    intro X _ hX hdim Z _ hfin hcard
    have hint : interior (Z.support : Set X) = ∅ := (Set.ncard_eq_zero hfin).mp hcard
    exact exists_pointBlowupChain_comap_isEffectiveCartierDivisor_of_isNowhereDense X hX hdim Z
      (Z.support.isClosed.isNowhereDense_iff.mpr hint)
  | succ n ih =>
    intro X _ hX hdim Z hZ hfin hcard
    obtain ⟨x, hxint⟩ : (interior (Z.support : Set X)).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by omega)
    have hx := hZ x hxint
    set M : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx.isClosed⟩ with hM
    set b := blowUpToBase M
    obtain ⟨hopen, hrange⟩ := isOpenImmersion_blowUpToBase_of_isClopen hx
    have : IsOpenImmersion b := hopen
    have hregX := (isRegular_iff_regular_stalks X).mp hX
    have : IsLocallyNoetherian X := hregX.1
    have : IsNoetherian X := ⟨⟩
    have : IsNoetherian (blowUp M) := isNoetherian_blowUp M
    have hX' : AlgebraicGeometry.IsRegular (blowUp M) :=
      (isRegular_iff_regular_stalks _).mpr ⟨inferInstance, fun z =>
        (isRegularLocalRing_stalk_iff_of_isOpenImmersion b z).mpr (hregX.2 (b z))⟩
    have hdim' : topologicalKrullDim (blowUp M) ≤ 2 := by
      rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk]
      refine iSup_le fun z => ?_
      rw [← ringKrullDim_eq_of_ringEquiv (asIso (b.stalkMap z)).commRingCatIsoToRingEquiv]
      refine le_trans ?_ (topologicalKrullDim_eq_iSup_krullDimOfRing_stalk X ▸ hdim)
      exact le_iSup (fun y : X => ringKrullDim (X.presheaf.stalk y)) (b z)
    set Z' : (blowUp M).IdealSheafData := Z.comap b
    have hsupp' : (Z'.support : Set (blowUp M)) = b.base ⁻¹' (Z.support : Set X) := by
      simp [Z', Scheme.IdealSheafData.support_comap]
    have hint' : interior (Z'.support : Set (blowUp M)) =
        b.base ⁻¹' interior (Z.support : Set X) := by
      rw [hsupp', b.isOpenEmbedding.isOpenMap.preimage_interior_eq_interior_preimage b.continuous]
    have hpre : b.base ⁻¹' interior (Z.support : Set X) =
        b.base ⁻¹' (interior (Z.support : Set X) \ {x}) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_sdiff, Set.mem_singleton_iff, iff_self_and]
      intro _ hzx
      exact (hrange ▸ Set.mem_range_self z : b z ∈ ({x}ᶜ : Set X)) hzx
    have hsub : interior (Z.support : Set X) \ {x} ⊆ Set.range b.base := by
      rw [hrange]
      exact fun y hy => hy.2
    have hZ' : ∀ z ∈ interior (Z'.support : Set (blowUp M)), IsClopen ({z} : Set (blowUp M)) := by
      intro z hz
      rw [hint'] at hz
      have heq : ({z} : Set (blowUp M)) = b.base ⁻¹' {b z} := by
        ext w
        simp only [Set.mem_singleton_iff, Set.mem_preimage]
        exact ⟨fun h => h ▸ rfl, fun h => b.isOpenEmbedding.injective h⟩
      rw [heq]
      exact (hZ _ hz).preimage b.continuous
    have hfin' : (interior (Z'.support : Set (blowUp M))).Finite := by
      rw [hint']
      exact hfin.preimage b.isOpenEmbedding.injective.injOn
    have hcard' : (interior (Z'.support : Set (blowUp M))).ncard = n := by
      rw [hint', hpre,
        Set.ncard_preimage_of_injective_subset_range b.isOpenEmbedding.injective hsub,
        Set.ncard_sdiff_singleton_of_mem hxint, hcard]
      rfl
    obtain ⟨Y, g, hg, hcart⟩ := ih (blowUp M) hX' hdim' Z' hZ' hfin' hcard'
    have hbase : PointBlowupChain X (Z.support : Set X) (blowUp M) b := by
      simpa using (PointBlowupChain.refl (X := X) (T := (Z.support : Set X))).step x hx.isClosed
        (interior_subset hxint)
    refine ⟨Y, g ≫ b, hbase.comp hg fun z hz => ?_, ?_⟩
    · have : z ∈ (Z'.support : Set (blowUp M)) := hz
      rwa [hsupp'] at this
    · rwa [Scheme.IdealSheafData.comap_comp]

end Stacks.ResolutionOfSurfaces

end
