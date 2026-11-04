module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Maps.Basic

/-!
# Testing closedness and openness of a map after an open surjective base change

Consider four maps of topological spaces fitting into a commutative square

```text
A --a--> C
|        |
p        q
|        |
v        v
B --b--> D
```

in which `b` is open and surjective, `a` is continuous, and in which the canonical map
`A → B ×_D C` is surjective — that is, every pair `(y, c)` with `b y = q c` is of the form
`(p x, a x)`. Then `q` is closed as soon as `p` is, and `q` is open as soon as `p` is.

The whole content is one set identity, `preimage_image_eq_image_preimage_of_comm_of_surjective`:
under those hypotheses `b ⁻¹' (q '' T) = p '' (a ⁻¹' T)` for every `T ⊆ C`. An open surjection
reflects openness and closedness of subsets, so a property of `q '' T` can be read off from
`p '' (a ⁻¹' T)`.

This is the topological core of the argument of **Stacks 0512**, which characterizes a
universally closed morphism of algebraic stacks representable by algebraic spaces as one for
which `|𝒵 ×_𝒴 𝒳| → |𝒵|` is closed for every algebraic stack `𝒵` over `𝒴`. Given a scheme `V`
and a surjective smooth `V → 𝒵`, the square above with `A = |V ×_𝒴 𝒳|`, `B = |V|`,
`C = |𝒵 ×_𝒴 𝒳|` and `D = |𝒵|` has exactly these properties, so closedness of the left vertical
map — which is the hypothesis, since `V ×_𝒴 𝒳 → V` is a universally closed morphism of
algebraic spaces — gives closedness of the right vertical one. The surjectivity hypothesis on
`A → B ×_D C` is supplied there by **Stacks 04XH**, that `|𝒵 ×_𝒴 𝒳| → |𝒵| ×_{|𝒴|} |𝒳|` is
surjective.

The same set identity is the computation `b ⁻¹' (a '' W) = (d ∘ e) '' (f ⁻¹' W)` in the proof
of **Stacks 04XL** that a surjective flat morphism of finite presentation from an algebraic
space is open on points, with the roles of the two vertical maps exchanged; that is why both an
open and a closed version are recorded here. The lemmas are stated for bare topological spaces
and carry no algebraic geometry.

## Main results

* `IsOpenMap.isOpen_of_isOpen_preimage`, `IsOpenMap.isClosed_of_isClosed_preimage`: an open
  surjection reflects openness, resp. closedness, of subsets of its target.
* `preimage_image_eq_image_preimage_of_comm_of_surjective`: the set identity
  `b ⁻¹' (q '' T) = p '' (a ⁻¹' T)`.
* `surjective_pair_of_surjective_toFibreProduct`: the surjectivity hypothesis of the descent
  lemmas, from surjectivity of the canonical map `A → B ×_D C`.
* `isClosedMap_of_isClosedMap_comm_of_isOpenMap_surjective`,
  `isOpenMap_of_isOpenMap_comm_of_isOpenMap_surjective`: closedness, resp. openness, of `q`
  from that of `p`.
* `isClosedMap_of_isClosedMap_fibreProduct`, `isOpenMap_of_isOpenMap_fibreProduct`: the same
  two statements for the topological fibre product `{z : B × C // b z.1 = q z.2}` in place of
  `A`, where the hypothesis on the canonical map holds automatically.

## References

* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
-/

@[expose] public section

open Function Set

variable {A B C D : Type*}

/-- An open surjection reflects openness: if `b` is open and surjective and `b ⁻¹' E` is open,
then `E` is open. Continuity of `b` is not needed. -/
theorem IsOpenMap.isOpen_of_isOpen_preimage [TopologicalSpace B] [TopologicalSpace D]
    {b : B → D} (hb : IsOpenMap b) (hbsurj : Surjective b) {E : Set D}
    (hE : IsOpen (b ⁻¹' E)) : IsOpen E := by
  rw [← hbsurj.image_preimage E]
  exact hb _ hE

/-- An open surjection reflects closedness: if `b` is open and surjective and `b ⁻¹' E` is
closed, then `E` is closed. Continuity of `b` is not needed. -/
theorem IsOpenMap.isClosed_of_isClosed_preimage [TopologicalSpace B] [TopologicalSpace D]
    {b : B → D} (hb : IsOpenMap b) (hbsurj : Surjective b) {E : Set D}
    (hE : IsClosed (b ⁻¹' E)) : IsClosed E := by
  rw [← isOpen_compl_iff]
  refine hb.isOpen_of_isOpen_preimage hbsurj ?_
  rw [preimage_compl, isOpen_compl_iff]
  exact hE

/-- For a commutative square `b ∘ p = q ∘ a` whose canonical map `A → B ×_D C` is surjective,
the `b`-preimage of the `q`-image of a set is the `p`-image of its `a`-preimage.

The inclusion `⊇` is commutativity of the square; the inclusion `⊆` is the surjectivity
hypothesis, applied to a point `y` of `B` and a point of `T` with the same image in `D`. -/
theorem preimage_image_eq_image_preimage_of_comm_of_surjective
    {p : A → B} {a : A → C} {q : C → D} {b : B → D}
    (hcomm : ∀ x, b (p x) = q (a x))
    (hsurj : ∀ (y : B) (c : C), b y = q c → ∃ x, p x = y ∧ a x = c)
    (T : Set C) : b ⁻¹' (q '' T) = p '' (a ⁻¹' T) := by
  ext y
  constructor
  · rintro ⟨c, hcT, hc⟩
    obtain ⟨x, hx1, hx2⟩ := hsurj y c hc.symm
    exact ⟨x, by simp only [mem_preimage, hx2]; exact hcT, hx1⟩
  · rintro ⟨x, hxT, rfl⟩
    exact ⟨a x, hxT, (hcomm x).symm⟩

/-- The surjectivity hypothesis of the descent lemmas below, in the form in which the geometric
input supplies it: surjectivity of the canonical map from `A` to the fibre product
`{z : B × C // b z.1 = q z.2}`. -/
theorem surjective_pair_of_surjective_toFibreProduct
    {p : A → B} {a : A → C} {q : C → D} {b : B → D} (hcomm : ∀ x, b (p x) = q (a x))
    (he : Surjective fun x : A ↦ (⟨(p x, a x), hcomm x⟩ : {z : B × C // b z.1 = q z.2})) :
    ∀ (y : B) (c : C), b y = q c → ∃ x, p x = y ∧ a x = c := by
  intro y c h
  obtain ⟨x, hx⟩ := he ⟨(y, c), h⟩
  exact ⟨x, congrArg (fun z : {z : B × C // b z.1 = q z.2} ↦ z.val.1) hx,
    congrArg (fun z : {z : B × C // b z.1 = q z.2} ↦ z.val.2) hx⟩

/-- Closedness descends along an open surjection: in a commutative square `b ∘ p = q ∘ a` with
`b` open and surjective, `a` continuous, and the canonical map `A → B ×_D C` surjective, `q` is
a closed map as soon as `p` is. -/
theorem isClosedMap_of_isClosedMap_comm_of_isOpenMap_surjective
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    {p : A → B} {a : A → C} {q : C → D} {b : B → D}
    (hcomm : ∀ x, b (p x) = q (a x)) (hb : IsOpenMap b) (hbsurj : Surjective b)
    (ha : Continuous a)
    (hsurj : ∀ (y : B) (c : C), b y = q c → ∃ x, p x = y ∧ a x = c)
    (hp : IsClosedMap p) : IsClosedMap q := by
  intro T hT
  refine hb.isClosed_of_isClosed_preimage hbsurj ?_
  rw [preimage_image_eq_image_preimage_of_comm_of_surjective hcomm hsurj]
  exact hp _ (hT.preimage ha)

/-- Openness descends along an open surjection: in a commutative square `b ∘ p = q ∘ a` with
`b` open and surjective, `a` continuous, and the canonical map `A → B ×_D C` surjective, `q` is
an open map as soon as `p` is. -/
theorem isOpenMap_of_isOpenMap_comm_of_isOpenMap_surjective
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    {p : A → B} {a : A → C} {q : C → D} {b : B → D}
    (hcomm : ∀ x, b (p x) = q (a x)) (hb : IsOpenMap b) (hbsurj : Surjective b)
    (ha : Continuous a)
    (hsurj : ∀ (y : B) (c : C), b y = q c → ∃ x, p x = y ∧ a x = c)
    (hp : IsOpenMap p) : IsOpenMap q := by
  intro T hT
  refine hb.isOpen_of_isOpen_preimage hbsurj ?_
  rw [preimage_image_eq_image_preimage_of_comm_of_surjective hcomm hsurj]
  exact hp _ (hT.preimage ha)

/-- Closedness of a map can be tested after base change along an open surjection: if `b` is
open and surjective and the first projection of the topological fibre product
`{z : B × C // b z.1 = q z.2}` is closed, then `q` is closed. -/
theorem isClosedMap_of_isClosedMap_fibreProduct [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] {q : C → D} {b : B → D} (hb : IsOpenMap b) (hbsurj : Surjective b)
    (hp : IsClosedMap fun z : {z : B × C // b z.1 = q z.2} ↦ z.val.1) :
    IsClosedMap q :=
  isClosedMap_of_isClosedMap_comm_of_isOpenMap_surjective
    (fun z ↦ z.property) hb hbsurj (continuous_subtype_val.snd)
    (fun y c h ↦ ⟨⟨(y, c), h⟩, rfl, rfl⟩) hp

/-- Openness of a map can be tested after base change along an open surjection: if `b` is open
and surjective and the first projection of the topological fibre product
`{z : B × C // b z.1 = q z.2}` is open, then `q` is open. -/
theorem isOpenMap_of_isOpenMap_fibreProduct [TopologicalSpace B] [TopologicalSpace C]
    [TopologicalSpace D] {q : C → D} {b : B → D} (hb : IsOpenMap b) (hbsurj : Surjective b)
    (hp : IsOpenMap fun z : {z : B × C // b z.1 = q z.2} ↦ z.val.1) :
    IsOpenMap q :=
  isOpenMap_of_isOpenMap_comm_of_isOpenMap_surjective
    (fun z ↦ z.property) hb hbsurj (continuous_subtype_val.snd)
    (fun y c h ↦ ⟨⟨(y, c), h⟩, rfl, rfl⟩) hp

end
