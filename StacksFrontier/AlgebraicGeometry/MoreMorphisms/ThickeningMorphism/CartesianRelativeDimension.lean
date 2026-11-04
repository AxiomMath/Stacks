module

public import Mathlib.Topology.Homeomorph.Lemmas
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.DeformationFiniteOrder.Fibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Cartesian

/-!
# Relative dimension across a cartesian morphism of thickenings

Let

```
X --f--→ S
|        |
i        j
↓        ↓
X' -f'-→ S'
```

be a cartesian square of schemes in which `j` is a thickening. Then `f` and `f'` have the same
fibres: every point of `S'` is the image of a point `s` of `S`, the residue field of `S'` at
`j s` agrees with the residue field of `S` at `s` because a closed immersion is surjective on
stalks, and the square being cartesian identifies the fibre of `f` over `s` with the fibre of
`f'` over `j s`. Relative dimension is a condition on the fibres alone, so it transfers in both
directions; this file records that, and assembles it with the local finite type clause of Stacks
09ZW into part (4) of that tag: for a *finite-order* thickening `j`, the morphism `f` is locally
of finite type of relative dimension `d` exactly when `f'` is.

## Main results

* `Stacks.Thickenings.relativeDimension_iff_of_isThickening`: the fibrewise half, with no
  hypothesis on the order of the thickening.
* `Stacks.Thickenings.locallyOfFiniteType_and_relativeDimension_iff_of_isFiniteOrderThickening`:
  **Stacks 09ZW**, part (4).

## Implementation notes

Being locally of finite type of relative dimension `d` is a conjunction of two conditions, and
part (4) is stated as that conjunction. Since `AlgebraicGeometry.RelativeDimension` carries local
finite type as an instance argument, the conjunction is written as an existential over that
instance, `∃ _ : LocallyOfFiniteType f, RelativeDimension f d`, which is the only way to say
"locally of finite type *and* of relative dimension `d`" in one proposition. Its first half is
part (2) of the same tag.

The isomorphism of fibres is `Stacks.Thickenings.isIso_fiberMapOfIsPullback`, and only its
underlying homeomorphism of topological spaces is used, since
`AlgebraicGeometry.RelativeDimension` is a condition on the topology of the fibres:
nonemptiness, equidimensionality and topological Krull dimension. The first two of those are not
known in the library to be invariant under a homeomorphism, so that invariance is proved here;
for equidimensionality it comes from the induced bijection on irreducible components, Stacks
037A.

The hypothesis that the source inclusion `i` is a thickening is not taken: it plays no role in
the fibrewise half, and in part (4) it is the base change of `j`.

## References

* [Stacks Project, Tag 037A](https://stacks.math.columbia.edu/tag/037A)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 09ZW](https://stacks.math.columbia.edu/tag/09ZW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.Thickenings

universe u

/-! ### Homeomorphism invariance of the fibrewise conditions -/

/-- A homeomorphism carries a subspace onto a homeomorphic subspace, so the two have the same
topological Krull dimension. -/
private theorem topologicalKrullDim_image_eq {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) (Z : Set A) :
    topologicalKrullDim Z = topologicalKrullDim (e '' Z) :=
  IsHomeomorph.topologicalKrullDim_eq _ (e.image Z).isHomeomorph

/-- **Stacks 037A** for a homeomorphism: the image of an irreducible component is an irreducible
component. -/
private theorem image_mem_irreducibleComponents_of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) {Z : Set A} (hZ : Z ∈ irreducibleComponents A) :
    e '' Z ∈ irreducibleComponents B :=
  image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
    (fun _ => (Set.subsingleton_singleton.preimage e.injective).isPreirreducible)
    e.surjective hZ

/-- Equidimensionality is invariant under a homeomorphism: the homeomorphism matches the
irreducible components of the two spaces and preserves their dimensions. -/
private theorem equidimensional_iff_of_homeomorph {A B : Type*} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) : Equidimensional A ↔ Equidimensional B := by
  constructor
  · intro h W hW W' hW'
    rw [topologicalKrullDim_image_eq e.symm W, topologicalKrullDim_image_eq e.symm W']
    exact h _ (image_mem_irreducibleComponents_of_homeomorph e.symm hW) _
      (image_mem_irreducibleComponents_of_homeomorph e.symm hW')
  · intro h Z hZ Z' hZ'
    rw [topologicalKrullDim_image_eq e Z, topologicalKrullDim_image_eq e Z']
    exact h _ (image_mem_irreducibleComponents_of_homeomorph e hZ) _
      (image_mem_irreducibleComponents_of_homeomorph e hZ')

/-! ### Relative dimension -/

variable {X X' S S' : Scheme.{u}} {i : X ⟶ X'} {j : S ⟶ S'} {f : X ⟶ S} {f' : X' ⟶ S'}

/-- **Relative dimension is invariant under a cartesian morphism of thickenings.** In a
cartesian square whose base inclusion `j` is a thickening, the fibre of `f` over a point `s` is
isomorphic to the fibre of `f'` over `j s`, and every point of `S'` is of the form `j s`, so one
of the two morphisms has relative dimension `d` exactly when the other does. No finiteness
condition on the thickening is used. -/
theorem relativeDimension_iff_of_isThickening (hj : IsThickening j)
    (hcart : IsPullback i f f' j) [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (d : ℕ) :
    RelativeDimension f d ↔ RelativeDimension f' d := by
  have hiso : ∀ s : S, IsIso (fiberMapOfIsPullback hcart s) :=
    fun s => isIso_fiberMapOfIsPullback hj hcart s
  have he : ∀ s : S, (f.fiber s) ≃ₜ (f'.fiber (j s)) :=
    fun s => (fiberMapOfIsPullback hcart s).homeomorph
  have hdim (s : S) : topologicalKrullDim (f.fiber s) = topologicalKrullDim (f'.fiber (j s)) :=
    IsHomeomorph.topologicalKrullDim_eq _ (he s).isHomeomorph
  have hne (s : S) : Nonempty (f.fiber s) ↔ Nonempty (f'.fiber (j s)) :=
    (he s).toEquiv.nonempty_congr
  have hequi (s : S) : Equidimensional (f.fiber s) ↔ Equidimensional (f'.fiber (j s)) :=
    equidimensional_iff_of_homeomorph (he s)
  rw [relativeDimension_iff f d, relativeDimension_iff f' d]
  constructor
  · intro h s' hs'
    obtain ⟨s, rfl⟩ := hj.2 s'
    obtain ⟨h₁, h₂⟩ := h s ((hne s).mpr hs')
    exact ⟨(hequi s).mp h₁, (hdim s).symm.trans h₂⟩
  · intro h s hs
    obtain ⟨h₁, h₂⟩ := h (j s) ((hne s).mp hs)
    exact ⟨(hequi s).mpr h₁, (hdim s).trans h₂⟩

/-- **Stacks 09ZW, part (4).** Being locally of finite type of relative dimension `d` ascends
and descends across a cartesian morphism of thickenings when the thickening of the base has
finite order.

The property is the conjunction of local finite type and relative dimension `d`, and the
statement is that conjunction; its first half is part (2) of the same tag. -/
@[stacks 09ZW "relative_dimension"]
theorem locallyOfFiniteType_and_relativeDimension_iff_of_isFiniteOrderThickening
    (i : X ⟶ X') (j : S ⟶ S') (f : X ⟶ S) (f' : X' ⟶ S')
    (hj : IsFiniteOrderThickening j) (hcart : IsPullback i f f' j) (d : ℕ) :
    (∃ _ : LocallyOfFiniteType f, RelativeDimension f d) ↔
      (∃ _ : LocallyOfFiniteType f', RelativeDimension f' d) := by
  constructor
  · rintro ⟨hft, hd⟩
    have := (locallyOfFiniteType_iff_of_isFiniteOrderThickening i j f f' hj hcart).mp hft
    exact ⟨this, (relativeDimension_iff_of_isThickening hj.isThickening hcart d).mp hd⟩
  · rintro ⟨hft', hd'⟩
    have := (locallyOfFiniteType_iff_of_isFiniteOrderThickening i j f f' hj hcart).mpr hft'
    exact ⟨this, (relativeDimension_iff_of_isThickening hj.isThickening hcart d).mpr hd'⟩

end Stacks.Thickenings

end
