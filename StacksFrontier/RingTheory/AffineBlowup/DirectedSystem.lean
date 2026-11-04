module

public import Mathlib.Order.DirectedInverseSystem
public import StacksFrontier.RingTheory.AffineBlowup.Valuation

/-!
# The directed system of admissible affine blowup charts

Let `(R, 𝔪)` be a local domain with fraction field `K`, and let `A ⊆ K` be a
valuation ring dominating `R`. Stacks Tag 052M (`Stacks.AffineBlowup.stacks052M_main`)
exhibits `A` as the directed union of the subrings `affineBlowupImage I a ⊆ K`
attached to the *admissible pairs* `(I, a)` of `Stacks.AffineBlowup.IsAdmissiblePair`.

Stacks Tag 052M is phrased in terms of the *set* `𝒮` of such subrings. Stacks Tag
053I, which applies Stacks Tag 02JO (3)
(`Module.Flat.eventually_flat_of_directed`) to this union, instead needs the same
data presented as a *directed system of rings indexed by a preordered type*: an
index type, a `Preorder` on it which is `Nonempty` and `IsDirected`, a family of
rings, transition ring homomorphisms forming a `DirectedSystem`, and the
compatible cone of maps into `A` which exhibits `A` as the colimit.

This file builds that presentation on top of Stacks Tag 052M, changing nothing
about the mathematics:

* `Stacks.AffineBlowup.AdmissibleChart R A` is the index type: an admissible pair `(I, a)`
  bundled with its admissibility proof. It is the *pair* that is recorded, not
  merely the subring it presents, which is what makes the explicit common
  refinement `(I J, a b)` of Stacks Tag 052M available as a directedness witness.
* `Stacks.AffineBlowup.AdmissibleChart.subring` sends a chart to its subring of `K`, and the
  `Preorder` instance orders charts by inclusion of these subrings. Nonemptiness
  (`Stacks.AffineBlowup.AdmissibleChart.nonempty_of_maximalIdeal_ne_bot`) comes from
  `Stacks.AffineBlowup.stacks052M_C1_nonempty` and hence needs `𝔪 ≠ 0`; directedness
  (`Stacks.AffineBlowup.AdmissibleChart.isDirected_of_dominates`) comes from the explicit
  refinement `Stacks.AffineBlowup.stacks052M_C3_refinement`.
* `Stacks.AffineBlowup.chartRing`, `Stacks.AffineBlowup.chartMap` and the `DirectedSystem` instance
  are the ring family and its transition maps; every transition map is a subring
  inclusion, so functoriality is definitional.
* `Stacks.AffineBlowup.chartToVal` is the cone into `Stacks.AffineBlowup.valRing A = A`, given by
  clause (4) of admissibility. `Stacks.AffineBlowup.chartToVal_surjective` (from
  `Stacks.AffineBlowup.stacks052M_C4_union`) and
  `Stacks.AffineBlowup.exists_chartMap_eq_zero_of_chartToVal_eq_zero` are exactly the two
  colimit conditions `hσs`/`hσz` in the shape that
  `Module.Flat.eventually_flat_of_directed` consumes.

All statements are relative to a fixed valuation ring `A` dominating `R`; nothing
here is a new mathematical assertion about blowups.
-/

@[expose] public section

namespace Stacks.AffineBlowup

variable {R : Type*} [CommRing R] [IsLocalRing R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

/-- An **admissible chart** for the valuation ring `A`: an admissible pair `(I, a)`
in the sense of `IsAdmissiblePair` (Definition 7' of Stacks Tag 052M), bundled
with the proofs `a ∈ I` and of admissibility.

This is the index type of the directed system of Stacks Tag 052M. Recording the
pair `(I, a)` rather than only the subring `affineBlowupImage I a` it presents is
what makes the explicit product refinement `(I J, a b)` of
`stacks052M_C3_refinement` usable as a directedness witness. -/
structure AdmissibleChart (R : Type*) [CommRing R] [IsLocalRing R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (A : ValuationSubring K) where
  /-- The indexing ideal `I ⊆ 𝔪`. -/
  I : Ideal R
  /-- The denominator `a ∈ I`. -/
  a : R
  /-- The denominator lies in the indexing ideal. -/
  ha : a ∈ I
  /-- The pair `(I, a)` satisfies conditions (1)–(4) of Stacks Tag 052M. -/
  adm : IsAdmissiblePair R A I a ha

namespace AdmissibleChart

variable {A : ValuationSubring K}

/-- The subring `affineBlowupImage I a = {x/aⁿ ∈ K : x ∈ Iⁿ}` of `K` presented by
an admissible chart `(I, a)`. -/
def subring (c : AdmissibleChart R A) : Subring K :=
  affineBlowupImage c.I c.a c.ha

/-- The subring presented by a chart is contained in `A`: this is clause (4) of
admissibility. -/
theorem subring_le (c : AdmissibleChart R A) : c.subring ≤ A.toSubring :=
  c.adm.2.2.2

/-- Charts are ordered by inclusion of the subrings of `K` that they present. The
relation is a preorder rather than a partial order because distinct pairs
`(I, a)` can present the same subring. -/
instance instPreorder : Preorder (AdmissibleChart R A) where
  le c d := c.subring ≤ d.subring
  le_refl _ := le_rfl
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂

/-- Unfolding of the order on charts: `c ≤ d` means `c.subring ≤ d.subring`. -/
theorem le_iff_subring_le {c d : AdmissibleChart R A} : c ≤ d ↔ c.subring ≤ d.subring :=
  Iff.rfl

/-- **The index type is nonempty.** When `𝔪 ≠ 0` there is an admissible pair, by
`stacks052M_C1_nonempty` (take `(I, a) = ((a₀), a₀)` for a nonzero `a₀ ∈ 𝔪`).
The hypothesis `𝔪 ≠ 0` is genuinely needed: for `𝔪 = 0` there is no admissible
pair at all (`no_admissiblePair_of_maximalIdeal_eq_bot`). -/
theorem nonempty_of_maximalIdeal_ne_bot [IsDomain R]
    (hm : IsLocalRing.maximalIdeal R ≠ ⊥) (hdom : Dominates R A) :
    Nonempty (AdmissibleChart R A) := by
  obtain ⟨_, I, a, ha, -, adm⟩ := stacks052M_C1_nonempty hm A hdom
  exact ⟨⟨I, a, ha, adm⟩⟩

/-- **The index type is directed.** Two charts `(I, a)` and `(J, b)` are both
refined by the explicit product chart `(I J, a b)`, which is admissible by
`stacks052M_C3_refinement`. -/
theorem isDirected_of_dominates [IsDomain R] (hdom : Dominates R A) :
    IsDirected (AdmissibleChart R A) (· ≤ ·) := by
  refine ⟨fun c d => ?_⟩
  obtain ⟨hab, hadm, hcle, hdle⟩ :=
    stacks052M_C3_refinement A hdom c.I d.I c.a d.a c.ha d.ha c.adm d.adm
  exact ⟨⟨c.I * d.I, c.a * d.a, hab, hadm⟩, hcle, hdle⟩

end AdmissibleChart

/-- The ring attached to an admissible chart: its subring of `K`, viewed as a type
and carrying the induced `CommRing` structure. This is the family of rings of the
directed system. -/
abbrev chartRing {A : ValuationSubring K} (c : AdmissibleChart R A) : Type _ :=
  ↥c.subring

/-- The valuation ring `A` viewed as a type, i.e. the colimit of the directed
system of `chartRing`s (Stacks Tag 052M, part (2)). -/
abbrev valRing (A : ValuationSubring K) : Type _ :=
  ↥A.toSubring

/-- The transition map of the directed system: for `c ≤ d` the subring of `c` is
contained in that of `d`, and the transition map is that inclusion. -/
def chartMap {A : ValuationSubring K} (c d : AdmissibleChart R A) (h : c ≤ d) :
    chartRing c →+* chartRing d :=
  Subring.inclusion h

/-- The transition map `chartMap c d h` does not change an element's value in `K`. -/
@[simp]
theorem coe_chartMap {A : ValuationSubring K} {c d : AdmissibleChart R A} (h : c ≤ d)
    (y : chartRing c) : (chartMap c d h y : K) = (y : K) :=
  rfl

/-- The chart rings and their inclusions form a directed system: the transition
maps are subring inclusions, so identities and composites are definitional. -/
instance instDirectedSystemChartRing {A : ValuationSubring K} :
    DirectedSystem (fun c : AdmissibleChart R A => chartRing c)
      (fun c d h => chartMap c d h) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- The cone of the directed system into `A`: clause (4) of admissibility says the
subring of a chart is contained in `A`, and `chartToVal` is that inclusion. -/
def chartToVal {A : ValuationSubring K} (c : AdmissibleChart R A) :
    chartRing c →+* valRing A :=
  Subring.inclusion c.subring_le

/-- The map `chartToVal c` does not change an element's value in `K`. -/
@[simp]
theorem coe_chartToVal {A : ValuationSubring K} (c : AdmissibleChart R A) (y : chartRing c) :
    (chartToVal c y : K) = (y : K) :=
  rfl

/-- **The cone is compatible with the transition maps**, pointwise form: both sides
are the inclusion of `c.subring` into `A`. -/
theorem chartToVal_chartMap {A : ValuationSubring K} {c d : AdmissibleChart R A} (h : c ≤ d)
    (y : chartRing c) : chartToVal d (chartMap c d h y) = chartToVal c y :=
  rfl

/-- **The cone is compatible with the transition maps**, in the form
`chartToVal d ∘ chartMap c d h = chartToVal c`. -/
theorem chartToVal_comp_chartMap {A : ValuationSubring K} {c d : AdmissibleChart R A}
    (h : c ≤ d) : (chartToVal d).comp (chartMap c d h) = chartToVal c :=
  RingHom.ext fun y => chartToVal_chartMap h y

/-- **The cone is jointly surjective**: every element of `A` already lies in the
ring of some admissible chart. This is the forward direction of
`stacks052M_C4_union`, i.e. the substance of Stacks Tag 052M, and it is the
hypothesis `hσs` of `Module.Flat.eventually_flat_of_directed`. -/
theorem chartToVal_surjective [IsDomain R] (hm : IsLocalRing.maximalIdeal R ≠ ⊥)
    (A : ValuationSubring K) (hdom : Dominates R A) :
    ∀ x : valRing A, ∃ (c : AdmissibleChart R A) (y : chartRing c), chartToVal c y = x := by
  intro x
  obtain ⟨_, ⟨I, a, ha, rfl, adm⟩, hxB⟩ := (stacks052M_C4_union hm A hdom x).mp x.2
  exact ⟨⟨I, a, ha, adm⟩, ⟨x, hxB⟩, rfl⟩

/-- Each cone map is injective, being the inclusion of one subring of `K` into
another. -/
theorem chartToVal_injective {A : ValuationSubring K} (c : AdmissibleChart R A) :
    Function.Injective (chartToVal c) :=
  Subring.inclusion_injective _

/-- **Nothing is killed by the cone**: if an element of a chart ring maps to `0` in
`A`, it was already `0`, since the cone maps are inclusions of subrings of the
field `K`. -/
theorem eq_zero_of_chartToVal_eq_zero {A : ValuationSubring K} (c : AdmissibleChart R A)
    (y : chartRing c) (h : chartToVal c y = 0) : y = 0 :=
  chartToVal_injective c (by rw [h, map_zero])

/-- **Nothing is killed by the cone**, in the form required as the hypothesis `hσz`
of `Module.Flat.eventually_flat_of_directed`: an element of a chart ring that dies
in `A` already dies at some later stage of the system — here already at `c`
itself, by `eq_zero_of_chartToVal_eq_zero`. -/
theorem exists_chartMap_eq_zero_of_chartToVal_eq_zero {A : ValuationSubring K}
    (c : AdmissibleChart R A) (y : chartRing c) (h : chartToVal c y = 0) :
    ∃ (d : AdmissibleChart R A) (hd : c ≤ d), chartMap c d hd y = 0 :=
  ⟨c, le_rfl, by rw [eq_zero_of_chartToVal_eq_zero c y h, map_zero]⟩

end Stacks.AffineBlowup
