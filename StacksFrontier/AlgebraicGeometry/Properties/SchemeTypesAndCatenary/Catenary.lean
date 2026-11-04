module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.Catenary
public import StacksFrontier.RingTheory.Catenary.Basic
public import StacksFrontier.RingTheory.Catenary.Defs
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Noetherian.CatenaryOpenCovering

/-!
# Locality of catenarity for schemes

A scheme is catenary if and only if it has an open covering by catenary schemes. Equivalently,
the coordinate ring of every affine open is catenary, or this holds on one affine open covering.
Every locally closed subscheme of a catenary scheme is catenary, and a scheme is catenary
exactly when all of its local rings are.

## Main results

* `AlgebraicGeometry.isCatenarySpace_tfae`: the four equivalent local criteria.
* `AlgebraicGeometry.IsCatenarySpace.of_isImmersion`: a locally closed subscheme of a catenary
  scheme is catenary.
* `AlgebraicGeometry.isCatenarySpace_iff_stalk_isCatenary`: catenarity is detected by the local
  rings.

## Implementation notes

The four entries of `List.TFAE` occur in the source's order. Open coverings are families of
scheme opens satisfying `TopologicalSpace.IsOpenCover`. The coordinate ring of an affine open
`U` is `Γ(S, U)`. A locally closed subscheme is represented by an immersion. Catenarity of a
scheme is the canonical topological predicate `IrreducibleClosedsCodim.IsCatenarySpace`, while
catenarity of a ring is `Ring.IsCatenary`; the local ring of `X` at `x` is `X.presheaf.stalk x`.

The passage between `Ring.IsCatenary` and the order-theoretic `Catenary.IsCatenaryOrder` on the
prime spectrum is used by both tags, so it is proved once here.

## References

* [Stacks Project, Tag 02IX](https://stacks.math.columbia.edu/tag/02IX)
* [Stacks Project, Tag 02J0](https://stacks.math.columbia.edu/tag/02J0)
-/

@[expose] public section

open TopologicalSpace IrreducibleClosedsCodim

namespace AlgebraicGeometry

universe u

/-- Catenarity of a ring as a condition on the order of primes of its spectrum. -/
public theorem catenaryOrder_of_ringIsCatenary {R : Type*} [CommRing R]
    (hR : Ring.IsCatenary R) : Catenary.IsCatenaryOrder (PrimeSpectrum R) := by
  intro p q hpq
  obtain ⟨hbound, n, hn⟩ := hR p q hpq
  refine ⟨hbound, fun s t hs ht hs' ht' => ?_⟩
  let s' : LTSeries (PrimeSpectrum R) := ⟨s.length, s.toFun, fun i => (s.step i).lt⟩
  let t' : LTSeries (PrimeSpectrum R) := ⟨t.length, t.toFun, fun i => (t.step i).lt⟩
  exact (hn s' hs ht s.step).trans (hn t' hs' ht' t.step).symm

/-- Catenarity of a ring, stated with `Ring.IsCatenary`, agrees with `IsCatenaryRing`. -/
public theorem ringIsCatenary_iff_primeChain (R : Type*) [CommRing R] :
    Ring.IsCatenary R ↔ _root_.IsCatenaryRing R := by
  classical
  constructor
  · intro h p q hpq
    obtain ⟨⟨N, hN⟩, n, hn⟩ := h p q hpq
    refine ⟨⟨N, fun c => hN c.series c.head_eq c.last_eq⟩, fun c d hc hd => ?_⟩
    exact (hn c.series c.head_eq c.last_eq hc).trans
      (hn d.series d.head_eq d.last_eq hd).symm
  · intro h p q hpq
    obtain ⟨⟨N, hN⟩, heq⟩ := h p q hpq
    refine ⟨⟨N, fun s hs ht => hN ⟨s, hs, ht⟩⟩, ?_⟩
    by_cases hex : ∃ c : PrimeChain R p q, c.IsMaximal
    · obtain ⟨c, hc⟩ := hex
      exact ⟨c.length, fun s hs ht hsat => heq ⟨s, hs, ht⟩ c hsat hc⟩
    · exact ⟨0, fun s hs ht hsat => (hex ⟨⟨s, hs, ht⟩, hsat⟩).elim⟩

/-- A ring whose spectrum is a catenary order is catenary. -/
public theorem ringIsCatenary_of_catenaryOrder {R : Type*} [CommRing R]
    (hR : Catenary.IsCatenaryOrder (PrimeSpectrum R)) : Ring.IsCatenary R := by
  refine (ringIsCatenary_iff_primeChain R).mpr fun p q hpq => ?_
  obtain ⟨⟨N, hN⟩, heq⟩ := hR p q hpq
  refine ⟨⟨N, fun c => hN c.series c.head_eq c.last_eq⟩, fun c d hc hd => ?_⟩
  let c' : RelSeries {(a, b) : PrimeSpectrum R × PrimeSpectrum R | a ⋖ b} :=
    ⟨c.length, c.series.toFun, hc⟩
  let d' : RelSeries {(a, b) : PrimeSpectrum R × PrimeSpectrum R | a ⋖ b} :=
    ⟨d.length, d.series.toFun, hd⟩
  exact heq c' d' c.head_eq c.last_eq d.head_eq d.last_eq

public theorem catenarySpace_of_order {X : Type*} [TopologicalSpace X]
    (hX : Catenary.IsCatenaryOrder (IrreducibleCloseds X)) : IsCatenarySpace X := by
  intro Y Z hYZ
  obtain ⟨⟨N, hN⟩, hlen⟩ := hX Y Z hYZ
  have hfin : topCodim Y Z ≠ ⊤ := by
    apply ne_top_of_le_ne_top (ENat.natCast_ne_top N)
    rw [topCodim_le_iff]
    intro s hs ht
    exact_mod_cast hN s hs ht
  refine ⟨hfin, fun s hs => ?_⟩
  obtain ⟨t, ht, htdim⟩ := exists_maximalChain_length_eq_topCodim Y Z hYZ hfin
  let s' : RelSeries {(a, b) : IrreducibleCloseds X × IrreducibleCloseds X | a ⋖ b} :=
    ⟨s.length, s.toFun, hs.2.2⟩
  let t' : RelSeries {(a, b) : IrreducibleCloseds X × IrreducibleCloseds X | a ⋖ b} :=
    ⟨t.length, t.toFun, ht.2.2⟩
  exact (congrArg (fun n : ℕ => (n : ℕ∞)) (hlen s' t' hs.1 hs.2.1 ht.1 ht.2.1)).trans htdim

public theorem catenaryOrder_of_catenarySpace {X : Type*} [TopologicalSpace X]
    (hX : IsCatenarySpace X) : Catenary.IsCatenaryOrder (IrreducibleCloseds X) := by
  intro Y Z hYZ
  obtain ⟨hfin, heq⟩ := hX Y Z hYZ
  refine ⟨⟨(topCodim Y Z).toNat, ?_⟩, ?_⟩
  · intro s hs ht
    have h := length_le_topCodim Y Z s hs ht
    rw [← ENat.natCast_toNat hfin] at h
    exact_mod_cast h
  · intro s t hs ht hs' ht'
    let s' : LTSeries (IrreducibleCloseds X) :=
      ⟨s.length, s.toFun, fun i => (s.step i).lt⟩
    let t' : LTSeries (IrreducibleCloseds X) :=
      ⟨t.length, t.toFun, fun i => (t.step i).lt⟩
    exact_mod_cast (heq s' ⟨hs, ht, s.step⟩).trans (heq t' ⟨hs', ht', t.step⟩).symm

@[ega "0 16.1.4"]
private theorem ringIsCatenary_iff_primeSpectrum (R : Type*) [CommRing R] :
    Ring.IsCatenary R ↔ IsCatenarySpace (PrimeSpectrum R) :=
  ⟨fun h => catenarySpace_of_order
      ((Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum R).mp
        (catenaryOrder_of_ringIsCatenary h)),
    fun h => ringIsCatenary_of_catenaryOrder
      ((Catenary.isCatenaryRing_iff_isCatenarySpace_primeSpectrum R).mpr
        (catenaryOrder_of_catenarySpace h))⟩

private theorem isCatenarySpace_affineOpen_iff_ring (S : Scheme.{u}) (U : S.affineOpens) :
    IsCatenarySpace (U : S.Opens).toScheme ↔ Ring.IsCatenary Γ(S, U) := by
  let e := U.2.isoSpec.hom.homeomorph
  exact ⟨fun h => (ringIsCatenary_iff_primeSpectrum _).mpr
      (CatenaryTopologicalSpace.isCatenary_of_homeomorph e h),
    fun h => CatenaryTopologicalSpace.isCatenary_of_homeomorph e.symm
      ((ringIsCatenary_iff_primeSpectrum _).mp h)⟩

private theorem isCatenarySpace_iff_openCover (S : Scheme.{u}) :
    IsCatenarySpace S ↔
      ∃ (ι : Type u) (U : ι → S.Opens), IsOpenCover U ∧
        ∀ i, IsCatenarySpace (U i).toScheme := by
  constructor
  · intro hS
    obtain ⟨ι, V, hVopen, hVcover, hVcat⟩ :=
      (CatenaryTopologicalSpace.isCatenary_iff_hasOpenCoveringByCatenarySpaces S).mp hS
    refine ⟨ι, fun i => ⟨V i, hVopen i⟩, ?_, hVcat⟩
    exact Opens.ext (by simpa only [Opens.coe_iSup, Opens.coe_top, Opens.coe_mk] using hVcover)
  · rintro ⟨ι, U, hUcover, hUcat⟩
    apply (CatenaryTopologicalSpace.isCatenary_iff_hasOpenCoveringByCatenarySpaces S).mpr
    refine ⟨ι, fun i => (U i : Set S), fun i => (U i).2, ?_, hUcat⟩
    simpa only [Opens.coe_iSup, Opens.coe_top] using
      congrArg (fun W : S.Opens => (W : Set S)) hUcover

private theorem openCover_iff_allAffineCatenary (S : Scheme.{u}) :
    (∃ (ι : Type u) (U : ι → S.Opens), IsOpenCover U ∧
      ∀ i, IsCatenarySpace (U i).toScheme) ↔
    (∀ U : S.affineOpens, Ring.IsCatenary Γ(S, U)) := by
  constructor
  · rintro ⟨ι, U, hcov, hcat⟩ V
    exact (isCatenarySpace_affineOpen_iff_ring S V).mp
      (CatenaryTopologicalSpace.isCatenary_of_isOpen
        ((isCatenarySpace_iff_openCover S).mpr ⟨ι, U, hcov, hcat⟩) (V : Set S) V.1.2)
  · exact fun h => ⟨S.affineOpens, fun V => (V : S.Opens), iSup_affineOpens_eq_top S,
      fun V => (isCatenarySpace_affineOpen_iff_ring S V).mpr (h V)⟩

private theorem allAffineCatenary_iff_affineCover (S : Scheme.{u}) :
    (∀ U : S.affineOpens, Ring.IsCatenary Γ(S, U)) ↔
      ∃ (ι : Type u) (U : ι → S.affineOpens),
        IsOpenCover (fun i => (U i : S.Opens)) ∧
          ∀ i, Ring.IsCatenary Γ(S, U i) := by
  constructor
  · exact fun h => ⟨S.affineOpens, fun U => U, iSup_affineOpens_eq_top S, h⟩
  · rintro ⟨ι, U, hcov, hcat⟩ V
    exact (openCover_iff_allAffineCatenary S).mp ⟨ι, fun i => (U i : S.Opens), hcov,
      fun i => (isCatenarySpace_affineOpen_iff_ring S (U i)).mpr (hcat i)⟩ V

/-- A scheme is catenary exactly when this holds on an open covering, or when the rings of
sections of every affine open (equivalently, of one affine open covering) are catenary. -/
@[stacks 02IX "local criteria"]
public theorem isCatenarySpace_tfae (S : Scheme.{u}) :
    List.TFAE [
      IsCatenarySpace S,
      ∃ (ι : Type u) (U : ι → S.Opens),
        IsOpenCover U ∧ ∀ i, IsCatenarySpace (U i).toScheme,
      ∀ U : S.affineOpens, Ring.IsCatenary Γ(S, U),
      ∃ (ι : Type u) (U : ι → S.affineOpens),
        IsOpenCover (fun i ↦ (U i : S.Opens)) ∧
          ∀ i, Ring.IsCatenary Γ(S, U i)] := by
  apply List.tfae_of_forall (b := IsCatenarySpace S)
  intro P hP
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
  rcases hP with rfl | rfl | rfl | rfl
  · exact Iff.rfl
  · exact (isCatenarySpace_iff_openCover S).symm
  · exact (openCover_iff_allAffineCatenary S).symm.trans
      (isCatenarySpace_iff_openCover S).symm
  · exact (allAffineCatenary_iff_affineCover S).symm.trans
      ((openCover_iff_allAffineCatenary S).symm.trans
        (isCatenarySpace_iff_openCover S).symm)

/-- A locally closed subscheme of a catenary scheme is catenary. -/
@[stacks 02IX "locally closed subschemes"]
public theorem IsCatenarySpace.of_isImmersion {S Z : Scheme.{u}} (i : Z ⟶ S)
    [IsImmersion i] (hS : IsCatenarySpace S) : IsCatenarySpace Z :=
  CatenaryTopologicalSpace.isCatenary_of_homeomorph i.isEmbedding.toHomeomorph.symm
    (CatenaryTopologicalSpace.isCatenary_of_isLocallyClosed S hS (Set.range i)
      i.isLocallyClosed_range)

/-- A partial order all of whose principal lower sets are catenary is catenary. -/
public theorem catenaryOrder_of_forall_Iic {P : Type u} [PartialOrder P]
    (hP : ∀ q : P, Catenary.IsCatenaryOrder (Set.Iic q)) :
    Catenary.IsCatenaryOrder P := by
  intro p q hpq
  obtain ⟨⟨N, hN⟩, heq⟩ := hP q ⟨p, hpq⟩ ⟨q, le_rfl⟩ hpq
  refine ⟨⟨N, ?_⟩, ?_⟩
  · intro s hs ht
    let t : LTSeries (Set.Iic q) :=
      ⟨s.length, fun i => ⟨s i, by
        simpa only [Set.mem_Iic, ← ht, RelSeries.last] using s.monotone (Fin.le_last i)⟩,
        s.step⟩
    exact hN t (Subtype.ext hs) (Subtype.ext ht)
  · intro s t hs ht hs' ht'
    let sl : LTSeries P := ⟨s.length, s.toFun, fun i => (s.step i).lt⟩
    let tl : LTSeries P := ⟨t.length, t.toFun, fun i => (t.step i).lt⟩
    let sc : RelSeries {(a, b) : Set.Iic q × Set.Iic q | a ⋖ b} :=
      ⟨s.length, fun i => ⟨s i, by
        simpa only [Set.mem_Iic, ← ht, RelSeries.last] using sl.monotone (Fin.le_last i)⟩,
        fun i => (s.step i).of_image (OrderEmbedding.subtype _)⟩
    let tc : RelSeries {(a, b) : Set.Iic q × Set.Iic q | a ⋖ b} :=
      ⟨t.length, fun i => ⟨t i, by
        simpa only [Set.mem_Iic, ← ht', RelSeries.last] using tl.monotone (Fin.le_last i)⟩,
        fun i => (t.step i).of_image (OrderEmbedding.subtype _)⟩
    exact heq sc tc (Subtype.ext hs) (Subtype.ext ht) (Subtype.ext hs') (Subtype.ext ht')

/-- A ring all of whose localizations at primes are catenary is catenary. -/
public theorem ringIsCatenary_of_forall_primeLocalization {R : Type u} [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime] (T : Type u) [CommRing T] [Algebra R T]
      [IsLocalization.AtPrime T p], Ring.IsCatenary T) : Ring.IsCatenary R :=
  ringIsCatenary_of_catenaryOrder <| catenaryOrder_of_forall_Iic fun p =>
    Catenary.isCatenaryOrder_of_orderIso
      (IsLocalization.AtPrime.primeSpectrumOrderIso (Localization.AtPrime p.asIdeal) p.asIdeal)
      (catenaryOrder_of_ringIsCatenary (hR p.asIdeal (Localization.AtPrime p.asIdeal)))

/-- Catenarity of an order transfers along an order embedding with order-connected range. -/
public theorem catenaryOrder_of_orderEmbedding {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (e : P ↪o Q) (he : (Set.range e).OrdConnected)
    (hQ : Catenary.IsCatenaryOrder Q) : Catenary.IsCatenaryOrder P := by
  intro p q hpq
  obtain ⟨⟨N, hN⟩, heq⟩ := hQ (e p) (e q) (e.monotone hpq)
  refine ⟨⟨N, ?_⟩, ?_⟩
  · intro s hs ht
    exact hN (s.map e e.strictMono) (congrArg e hs) (congrArg e ht)
  · intro s t hs ht hs' ht'
    let f : SetRel.Hom {(a, b) : P × P | a ⋖ b} {(a, b) : Q × Q | a ⋖ b} :=
      { toFun := e, map_rel' := fun {a b} h => he.apply_covBy_apply_iff e |>.mpr h }
    exact heq (s.map f) (t.map f) (congrArg e hs) (congrArg e ht)
      (congrArg e hs') (congrArg e ht')

/-- A localization of a catenary ring is catenary. -/
public theorem ringIsCatenary_of_isLocalization {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] (hR : Ring.IsCatenary R) :
    Ring.IsCatenary S := by
  apply ringIsCatenary_of_catenaryOrder
  apply Catenary.isCatenaryOrder_of_orderIso (IsLocalization.primeSpectrumOrderIso M S).symm
  apply catenaryOrder_of_orderEmbedding (OrderEmbedding.subtype _)
  · simp only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype]
    exact ⟨fun _ _ _ hq _ hr => hq.mono_right hr.2⟩
  · exact catenaryOrder_of_ringIsCatenary hR

/-- The local rings of a catenary scheme are catenary. -/
private theorem stalk_isCatenary_of_isCatenarySpace {X : Scheme.{u}}
    (hX : IrreducibleClosedsCodim.IsCatenarySpace X) (x : X) :
    Ring.IsCatenary (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hAll : ∀ V : X.affineOpens, Ring.IsCatenary Γ(X, V) :=
    ((isCatenarySpace_tfae X).out 1 3).mp hX
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  exact ringIsCatenary_of_isLocalization ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl)
    (hAll ⟨U, hU⟩)

/-- A scheme all of whose local rings are catenary is catenary. -/
private theorem isCatenarySpace_of_stalk_isCatenary {X : Scheme.{u}}
    (h : ∀ x : X, Ring.IsCatenary (X.presheaf.stalk x)) :
    IrreducibleClosedsCodim.IsCatenarySpace X := by
  refine ((isCatenarySpace_tfae X).out 1 3).mpr fun U =>
    ringIsCatenary_of_forall_primeLocalization fun p hp T _ _ _ => ?_
  let xU : U.1 := U.2.isoSpec.inv ⟨p, hp⟩
  let x : X := xU.1
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, xU.2⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p :=
    U.2.isLocalization_stalk' ⟨p, hp⟩ xU.2
  exact Ring.IsCatenary.of_surjective
    (IsLocalization.algEquiv p.primeCompl T (X.presheaf.stalk x)).symm.surjective (h x)

/-- A scheme is catenary if and only if each of its local rings is catenary. -/
@[stacks 02J0]
public theorem isCatenarySpace_iff_stalk_isCatenary (X : Scheme.{u}) :
    IrreducibleClosedsCodim.IsCatenarySpace X ↔
      ∀ x : X, Ring.IsCatenary (X.presheaf.stalk x) :=
  ⟨stalk_isCatenary_of_isCatenarySpace, isCatenarySpace_of_stalk_isCatenary⟩

end AlgebraicGeometry

end
