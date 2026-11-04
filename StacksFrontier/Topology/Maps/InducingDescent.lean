module

public import StacksFrontier.Topology.Maps.OpenSurjectiveDescent

/-!
# Testing whether a map is inducing after an open surjective base change

Consider four maps of topological spaces fitting into a commutative square

```text
A --a--> C
|        |
p        q
|        |
v        v
B --b--> D
```

in which `b` is open and surjective, `a` and `q` are continuous, and in which the canonical map
`A → B ×_D C` is surjective — that is, every pair `(y, c)` with `b y = q c` is of the form
`(p x, a x)`. Then `q` is inducing as soon as `p` is: the topology of `C` is the one induced
from `D`.

This completes the pair of descent statements in
`StacksFrontier.Topology.Maps.OpenSurjectiveDescent`, which treat openness and closedness of `q`
under the same hypotheses, with the statement needed when the conclusion is about the topology
of `C` rather than about images of subsets of `C`.

## Main results

* `isInducing_of_isInducing_comm_of_isOpenMap_surjective`: `q` is inducing as soon as `p` is.
* `isInducing_of_isInducing_fibreProduct`: the same for the topological fibre product
  `{z : B × C // b z.1 = q z.2}` in place of `A`, where the hypothesis on the canonical map
  holds automatically.

## Implementation notes

A map is inducing exactly when its topology is both at least and at most the induced one.
Continuity of `q` is one of the two inequalities and has to be assumed — it does not follow,
since `a` is not assumed open. The other inequality is the content: every open `W ⊆ C` is the
`q`-preimage of an open subset of `D`. Its witness is built by pulling `W` back to `A` along
`a`, writing that preimage as `p ⁻¹' Q` for an open `Q ⊆ B` — which is what being inducing
gives for `p` — and pushing `Q` forward to the open set `b '' Q`.

That `q ⁻¹' (b '' Q)` is again `W` uses both remaining hypotheses, one for each inclusion. A
point `c` with `q c = b y` and `y ∈ Q` is `a x` for some `x` with `p x = y`, by surjectivity of
the canonical map, and then `x ∈ p ⁻¹' Q = a ⁻¹' W` puts `c` in `W`. Conversely a point of `W`
is `a x` for some `x`, because `b` surjective and the canonical map surjective together make
`a` surjective, and then `b (p x) = q (a x)` exhibits `q (a x)` in `b '' Q`.

The hypotheses are exactly those of the openness and closedness statements next door, plus
continuity of `q`, so a situation already set up for those needs nothing further.
-/

@[expose] public section

open Function Set

variable {A B C D : Type*}

/-- The canonical map `A → B ×_D C` being surjective, together with surjectivity of `b`, makes
the top map `a` of the square surjective. -/
theorem surjective_of_surjective_pair_of_surjective
    {p : A → B} {a : A → C} {q : C → D} {b : B → D} (hbsurj : Surjective b)
    (hsurj : ∀ (y : B) (c : C), b y = q c → ∃ x, p x = y ∧ a x = c) :
    Surjective a := by
  intro c
  obtain ⟨y, hy⟩ := hbsurj (q c)
  obtain ⟨x, -, hx⟩ := hsurj y c hy
  exact ⟨x, hx⟩

/-- Being inducing descends along an open surjection: in a commutative square `b ∘ p = q ∘ a`
with `b` open and surjective, `a` and `q` continuous, and the canonical map `A → B ×_D C`
surjective, `q` is inducing as soon as `p` is. -/
theorem isInducing_of_isInducing_comm_of_isOpenMap_surjective
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    {p : A → B} {a : A → C} {q : C → D} {b : B → D}
    (hcomm : ∀ x, b (p x) = q (a x)) (hb : IsOpenMap b) (hbsurj : Surjective b)
    (ha : Continuous a) (hq : Continuous q)
    (hsurj : ∀ (y : B) (c : C), b y = q c → ∃ x, p x = y ∧ a x = c)
    (hp : Topology.IsInducing p) : Topology.IsInducing q := by
  refine ⟨le_antisymm (continuous_iff_le_induced.mp hq) fun W hW ↦ ?_⟩
  rw [isOpen_induced_iff]
  obtain ⟨Q, hQ, hQeq⟩ := hp.isOpen_iff.mp (hW.preimage ha)
  refine ⟨b '' Q, hb _ hQ, ?_⟩
  ext c
  constructor
  · rintro ⟨y, hyQ, hy⟩
    obtain ⟨x, rfl, rfl⟩ := hsurj y c hy
    have hx : x ∈ p ⁻¹' Q := hyQ
    rwa [hQeq] at hx
  · intro hcW
    obtain ⟨x, rfl⟩ := surjective_of_surjective_pair_of_surjective hbsurj hsurj c
    have hx : x ∈ a ⁻¹' W := hcW
    rw [← hQeq] at hx
    exact ⟨p x, hx, hcomm x⟩

/-- Whether a map is inducing can be tested after base change along an open surjection: if `b`
is open and surjective, `q` is continuous and the first projection of the topological fibre
product `{z : B × C // b z.1 = q z.2}` is inducing, then `q` is inducing. -/
theorem isInducing_of_isInducing_fibreProduct [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] {q : C → D} {b : B → D} (hb : IsOpenMap b) (hbsurj : Surjective b)
    (hq : Continuous q)
    (hp : Topology.IsInducing fun z : {z : B × C // b z.1 = q z.2} ↦ z.val.1) :
    Topology.IsInducing q :=
  isInducing_of_isInducing_comm_of_isOpenMap_surjective
    (fun z ↦ z.property) hb hbsurj continuous_subtype_val.snd hq
    (fun y c h ↦ ⟨⟨(y, c), h⟩, rfl, rfl⟩) hp

end
