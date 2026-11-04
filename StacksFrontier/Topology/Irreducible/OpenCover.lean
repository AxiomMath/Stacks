module

public import Mathlib.Topology.Irreducible

/-!
# Irreducibility from an open cover

A set is irreducible as soon as it is covered by open sets over which it is irreducible and any
two of the nonempty pieces meet. This is how irreducibility is glued from an affine cover: the
pieces are open, so each of them is dense in the whole, and two dense pieces that meet force two
nonempty opens to meet.

Openness of the pieces is essential: two distinct lines through the origin are irreducible and
meet, and their union is not irreducible.

## Main results

* `isPreirreducible_of_isOpen_cover`: the preirreducibility of a set from an open cover.
* `isIrreducible_of_isOpen_cover`: the same with nonemptiness, giving irreducibility.

## Implementation notes

The hypothesis on a pair of pieces is that `S ∩ Vᵢ ∩ Vⱼ` is nonempty whenever `S ∩ Vᵢ` and
`S ∩ Vⱼ` both are, which is weaker than asking that the two pieces meet in a point of either
one alone — it is exactly what the proof uses, applying preirreducibility of `S ∩ Vᵢ` to the
opens `u` and `Vᵢ ∩ Vⱼ` and then preirreducibility of `S ∩ Vⱼ` to the opens `u ∩ Vᵢ` and `v`.
-/

@[expose] public section

variable {T : Type*} [TopologicalSpace T] {S : Set T} {ι : Sort*}

/-- **Preirreducibility from an open cover.** A set covered by open sets over which it is
preirreducible, any two nonempty pieces of which meet inside the set, is preirreducible. -/
theorem isPreirreducible_of_isOpen_cover (V : ι → Set T) (hV : ∀ i, IsOpen (V i))
    (hcover : S ⊆ ⋃ i, V i)
    (hirr : ∀ i, (S ∩ V i).Nonempty → IsPreirreducible (S ∩ V i))
    (hmeet : ∀ i j, (S ∩ V i).Nonempty → (S ∩ V j).Nonempty → (S ∩ V i ∩ V j).Nonempty) :
    IsPreirreducible S := by
  rintro u v hu hv ⟨x, hxS, hxu⟩ ⟨y, hyS, hyv⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hcover hxS)
  obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp (hcover hyS)
  have hi : (S ∩ V i).Nonempty := ⟨x, hxS, hxi⟩
  have hj : (S ∩ V j).Nonempty := ⟨y, hyS, hyj⟩
  have hij : (S ∩ V i ∩ (V i ∩ V j)).Nonempty := by
    obtain ⟨w, ⟨hwS, hwi⟩, hwj⟩ := hmeet i j hi hj
    exact ⟨w, ⟨hwS, hwi⟩, hwi, hwj⟩
  obtain ⟨z, ⟨hzS, hzi⟩, hzu, -, hzj⟩ :=
    hirr i hi u (V i ∩ V j) hu ((hV i).inter (hV j)) ⟨x, ⟨hxS, hxi⟩, hxu⟩ hij
  obtain ⟨w, ⟨hwS, -⟩, ⟨hwu, -⟩, hwv⟩ :=
    hirr j hj (u ∩ V i) v (hu.inter (hV i)) hv ⟨z, ⟨hzS, hzj⟩, hzu, hzi⟩ ⟨y, ⟨hyS, hyj⟩, hyv⟩
  exact ⟨w, hwS, hwu, hwv⟩

/-- **Irreducibility from an open cover.** A nonempty set covered by open sets over which it is
irreducible, any two nonempty pieces of which meet inside the set, is irreducible. -/
theorem isIrreducible_of_isOpen_cover (hne : S.Nonempty) (V : ι → Set T)
    (hV : ∀ i, IsOpen (V i)) (hcover : S ⊆ ⋃ i, V i)
    (hirr : ∀ i, (S ∩ V i).Nonempty → IsIrreducible (S ∩ V i))
    (hmeet : ∀ i j, (S ∩ V i).Nonempty → (S ∩ V j).Nonempty → (S ∩ V i ∩ V j).Nonempty) :
    IsIrreducible S :=
  ⟨hne, isPreirreducible_of_isOpen_cover V hV hcover (fun i hi => (hirr i hi).2) hmeet⟩

end
