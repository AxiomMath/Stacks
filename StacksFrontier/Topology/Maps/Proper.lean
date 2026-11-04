module

public import Mathlib.Topology.Maps.Proper.UniversallyClosed
public import Mathlib.Topology.SeparatedMap
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed, Bourbaki-proper, quasi-proper, universally closed and proper maps

Stacks tag 005O, the five notions the Stacks project attaches to a continuous map
`f : X → Y`. As the source itself warns, "the notation in the following definition may be
slightly different from what you are used to".

What Mathlib already has:

* (1) *closed* is `IsClosedMap`, registered below.
* (2) *Bourbaki-proper* is Mathlib's `IsProperMap` up to two differences: Mathlib defines
  properness by a filter condition and *derives* the product characterisation, and it forms the
  product in the other order (`X × Z → Y × Z` rather than `Z × X → Z × Y`). `IsBourbakiProperMap`
  below keeps the source's order, and `isProperMap_iff_isBourbakiProperMap` identifies the two.
* (3), (4), (5) have no Mathlib counterpart. Mathlib's `isProperMap_iff_isCompact_preimage` is
  close to (3) but needs `Y` compactly generated and, again, is about `IsProperMap`; Mathlib has
  no notion of a map being closed after base change along an arbitrary `g : Z → Y`, which is
  what (4) is; and (5) is (4) together with separatedness, for which we reuse Mathlib's
  `IsSeparatedMap` (already registered for Stacks 0CY1, the source's definition of separated).

The fibre product `Z ×_Y X` is Mathlib's `Function.Pullback g f`, the subspace
`{p : Z × X // g p.1 = f p.2}` of `Z × X`, and `f' : Z ×_Y X → Z` is `Function.Pullback.fst`.
-/

@[expose] public section

open Function Topology

namespace StacksDraft.Topology

universe u v w

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/- **Stacks 005O (1).** The source's "closed map" — the image of every closed subset is closed —
is Mathlib's `IsClosedMap`, definitionally the same statement. -/
add_to_stacks 005O "(1) A map is closed if the image of every closed subset is closed."
  IsClosedMap
add_to_ega "I 2.2.6" IsClosedMap
add_to_ega "II 7.2.1" IsClosedMap

/-- **Stacks 005O (2).** `f` is *Bourbaki-proper* if `Z × X → Z × Y` is closed for every
topological space `Z`. As in Mathlib's `isProperMap_iff_universally_closed`, `Z` is quantified
over one universe at a time; `IsProperMap.isBourbakiProperMap` below supplies the statement in
every universe at once. -/
@[stacks 005O "(2)"]
def IsBourbakiProperMap (f : X → Y) : Prop :=
  ∀ (Z : Type w) [TopologicalSpace Z], IsClosedMap (Prod.map (id : Z → Z) f)

/-- **Stacks 005O (3).** `f` is *quasi-proper* if the inverse image of every quasi-compact
subset of `Y` is quasi-compact. -/
@[stacks 005O "(3)"]
def IsQuasiProperMap (f : X → Y) : Prop :=
  ∀ V : Set Y, IsCompact V → IsCompact (f ⁻¹' V)

/-- **Stacks 005O (4).** `f` is *universally closed* if for every continuous `g : Z → Y` the
base change `f' : Z ×_Y X → Z` is a closed map. -/
@[stacks 005O "(4)"]
def IsUniversallyClosedMap (f : X → Y) : Prop :=
  ∀ (Z : Type w) [TopologicalSpace Z] (g : Z → Y), Continuous g →
    IsClosedMap (Function.Pullback.fst : Function.Pullback g f → Z)

/-- **Stacks 005O (5).** `f` is *proper* if it is separated and universally closed. Separatedness
is Mathlib's `IsSeparatedMap`, which Stacks 0CY1 defines by the diagonal `X → X ×_Y X` being a
closed map; `isSeparatedMap_iff_isClosedMap` is that equivalence. -/
@[stacks 005O "(5)", sga "4 Vbis 4.1.0" "proper morphism def"]
def IsProperMap (f : X → Y) : Prop :=
  IsSeparatedMap f ∧ IsUniversallyClosedMap.{u, v, w} f

/-! ### Bourbaki-properness is Mathlib's `IsProperMap` -/

/-- Swapping the two factors of a product turns a closed `Prod.map f g` into a closed
`Prod.map g f`. -/
private theorem isClosedMap_prodMap_swap {A B C D : Type*} [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D] {f : A → B} {g : C → D}
    (h : IsClosedMap (Prod.map f g)) : IsClosedMap (Prod.map g f) :=
  ((Homeomorph.prodComm B D).isClosedMap.comp h).comp (Homeomorph.prodComm C A).isClosedMap

/-- A Mathlib-proper map is Bourbaki-proper, in every universe. -/
theorem _root_.IsProperMap.isBourbakiProperMap (h : _root_.IsProperMap f) :
    IsBourbakiProperMap.{u, v, w} f := by
  intro Z _
  exact isClosedMap_prodMap_swap (h.universally_closed Z)

/-- Mathlib's `IsProperMap` is exactly continuity together with the source's
Bourbaki-properness. Compare `isProperMap_iff_universally_closed`, which is the same statement
with the two factors of the product interchanged. -/
theorem isProperMap_iff_isBourbakiProperMap :
    _root_.IsProperMap f ↔ Continuous f ∧ IsBourbakiProperMap.{u, v, u} f := by
  refine ⟨fun h => ⟨h.continuous, h.isBourbakiProperMap⟩, fun ⟨hf, h⟩ => ?_⟩
  rw [isProperMap_iff_universally_closed]
  refine ⟨hf, fun Z _ => ?_⟩
  exact isClosedMap_prodMap_swap (h Z)

/-! ### Mathlib-proper maps are universally closed in the fibre-product sense -/

/-- A Mathlib-proper map is universally closed in the sense of Stacks 005O (4): for every
continuous `g : Z → Y` the base change `Z ×_Y X → Z` is a closed map. Mathlib's
`IsProperMap.universally_closed` is the product form (`X × Z → Y × Z` is closed); the fibre
product `Z ×_Y X` is the preimage of the graph of `g` in `Z × X`, and the image of a closed
subset `C` of it under the first projection is the preimage of the closed set
`Prod.map id f '' C` under `z ↦ (z, g z)`. -/
theorem _root_.IsProperMap.isUniversallyClosedMap (h : _root_.IsProperMap f) :
    IsUniversallyClosedMap.{u, v, w} f := by
  intro Z _ g hg s hs
  obtain ⟨C, hC, rfl⟩ := isClosed_induced_iff.1 hs
  have himg : (Pullback.fst : Pullback g f → Z) '' (Subtype.val ⁻¹' C) =
      (fun z : Z => (z, g z)) ⁻¹' (Prod.map (id : Z → Z) f '' C) := by
    ext z
    constructor
    · rintro ⟨⟨⟨z', x⟩, (hzx : g z' = f x)⟩, hmem, rfl⟩
      exact ⟨(z', x), hmem, Prod.ext rfl hzx.symm⟩
    · rintro ⟨⟨z', x⟩, hmem, heq⟩
      obtain ⟨rfl, hfx⟩ := Prod.ext_iff.1 heq
      exact ⟨⟨(z', x), hfx.symm⟩, hmem, rfl⟩
  rw [himg]
  exact (h.isBourbakiProperMap Z C hC).preimage (continuous_id.prodMk hg)

/-- **Stacks 08YD.** A continuous map from a quasi-compact space to a Hausdorff space is
universally closed (Stacks 005O (4)). Mathlib supplies the two halves of the argument:
`Continuous.isProperMap` (a continuous map from a compact space to a Hausdorff space is proper)
and `IsProperMap.universally_closed` (proper maps are closed after any product); the lemma
`IsProperMap.isUniversallyClosedMap` converts the product form into the source's
fibre-product form. -/
@[stacks 08YD]
theorem isUniversallyClosedMap_of_compactSpace [CompactSpace X] [T2Space Y]
    (hf : Continuous f) : IsUniversallyClosedMap.{u, v, w} f :=
  hf.isProperMap.isUniversallyClosedMap

/-! ### Universally closed maps are closed -/

/-- The graph map `x ↦ (f x, x)`, a homeomorphism from `X` onto `Y ×_Y X`. It witnesses that
base changing `f` along `id : Y → Y` gives back `f`. -/
def graphPullback (f : X → Y) (x : X) : Function.Pullback (id : Y → Y) f := ⟨(f x, x), rfl⟩

/-- For continuous `f`, the graph map `x ↦ (f x, x)` is a closed embedding of `X` into
`Y ×_Y X`. It is injective and continuous, and it is a closed map because its image of a
subset `t` is the preimage of `t` under the continuous second projection. -/
lemma isClosedEmbedding_graphPullback (hf : Continuous f) :
    IsClosedEmbedding (graphPullback f) := by
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap
    (continuous_induced_rng.2 (hf.prodMk continuous_id))
    (fun _ _ hab => congrArg (fun p => p.val.2) hab) (fun t ht => ?_)
  have himg : graphPullback f '' t =
      (fun p : Function.Pullback (id : Y → Y) f => p.val.2) ⁻¹' t := by
    ext ⟨⟨y, x⟩, (hyx : id y = f x)⟩
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨a, ha, hEq⟩
      obtain rfl : a = x := congrArg (fun p => p.val.2) hEq
      exact ha
    · exact fun hx => ⟨x, hx, Subtype.ext (Prod.ext hyx.symm rfl)⟩
  rw [himg]
  exact ht.preimage continuous_subtype_val.snd

/-- A universally closed map is closed: base change along `id : Y → Y` recovers `f` itself.
This is the sanity check that Stacks 005O (4) is not vacuous. -/
theorem IsUniversallyClosedMap.isClosedMap (hf : Continuous f)
    (h : IsUniversallyClosedMap.{u, v, v} f) : IsClosedMap f := by
  intro s hs
  have himg : f '' s = Function.Pullback.fst '' (graphPullback f '' s) := by
    rw [Set.image_image]
    rfl
  rw [himg]
  exact h Y id continuous_id _ ((isClosedEmbedding_graphPullback hf).isClosedMap _ hs)

/-- A proper map, in the sense of Stacks 005O (5), is closed. -/
theorem IsProperMap.isClosedMap (hf : Continuous f) (h : IsProperMap.{u, v, v} f) :
    IsClosedMap f :=
  h.2.isClosedMap hf

end StacksDraft.Topology
