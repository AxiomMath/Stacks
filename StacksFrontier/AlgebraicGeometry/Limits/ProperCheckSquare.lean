module

public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemma
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.ImmersionClosedness

/-!
# Checking properness on a Chow modification

Let `f : X ⟶ S` be separated and locally of finite type and let

```
X' ---i---> ℙⁿ_S
|            |
π            |
v            v
X ----f----> S
```

be a commutative square in which `π : X' ⟶ X` is proper and **surjective**, the top morphism
`i` is an immersion into projective `n`-space over `S`, and the right-hand vertical morphism is
the structure morphism of `ℙⁿ_S`. This is the square of
[Stacks, Tag 05LZ](https://stacks.math.columbia.edu/tag/05LZ), and the point of it is that every
morphism in it other than `f` is proper a priori: `π` is proper by assumption, `ℙⁿ_S ⟶ S` is
proper always, and `i` is proper as soon as it is a closed immersion. Properness of `f` is
therefore equivalent to `i` being a closed immersion.

Both directions are elementary once the square is given. If `i` is a closed immersion then
`π ≫ f = i ≫ (ℙⁿ_S ↘ S)` is universally closed, and a morphism whose composition with a
surjection is universally closed is itself universally closed, so `f` is proper. Conversely, if
`f` is proper then `π ≫ f` is proper, hence so is `i ≫ (ℙⁿ_S ↘ S)`; cancelling the separated
morphism `ℙⁿ_S ⟶ S` makes `i` proper, and a proper immersion has closed range and so is a closed
immersion.

A square of this shape exists for every separated morphism of finite type over a quasi-compact
quasi-separated base, by Chow's lemma ([Stacks, Tag 0202](https://stacks.math.columbia.edu/tag/0202),
whose conclusion is `AlgebraicGeometry.HasChowModification`); the square produced there has `i`
an immersion, and the last result below upgrades it to a closed immersion when `f` is proper.

## Main results

* `AlgebraicGeometry.isProper_of_surjective_of_isClosedImmersion_projectiveSpace`: a separated
  morphism locally of finite type that fits into the square with `π` surjective and `i` a closed
  immersion is proper.
* `AlgebraicGeometry.isClosedImmersion_projectiveSpace_of_isProper`: if `f` is proper and `π` is
  proper, then the immersion `i` of the square is a closed immersion.
* `AlgebraicGeometry.isProper_iff_isClosedImmersion_projectiveSpace`: given the square with `π`
  proper surjective and `i` an immersion, `f` is proper if and only if `i` is a closed immersion.
* `AlgebraicGeometry.exists_surjective_isClosedImmersion_projectiveSpace_of_isProper`: a proper
  morphism admitting a Chow modification admits the square of Tag 05LZ with `π` proper surjective
  and `i` a **closed** immersion.

## Implementation notes

Finite type of `f` is not needed in full: properness is separatedness together with universal
closedness and being locally of finite type, so the quasi-compactness half of finite type plays
no role and is omitted from the hypotheses.

Properness of `ℙⁿ_S ⟶ S` is `AlgebraicGeometry.ProjectiveSpace.instIsProperOver`, and its
separatedness — all that the cancellation needs — follows from it.

## References

* [Stacks Project, Tag 05LZ](https://stacks.math.columbia.edu/tag/05LZ)
* [Stacks Project, Tag 0205](https://stacks.math.columbia.edu/tag/0205)
* [Stacks Project, Tag 0202](https://stacks.math.columbia.edu/tag/0202)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 03GN](https://stacks.math.columbia.edu/tag/03GN)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X S X' : Scheme.{u}} {n : ℕ}

/-- **Properness is checked on a Chow modification.** Let `f : X ⟶ S` be separated and locally
of finite type, let `π : X' ⟶ X` be surjective and let `i : X' ⟶ ℙⁿ_S` be a closed immersion
with `π ≫ f = i ≫ (ℙⁿ_S ↘ S)`. Then `f` is proper.

Every morphism of the square other than `f` is proper, so the composite `π ≫ f` is universally
closed; since `π` is surjective, `f` is universally closed too, and properness needs nothing
further. -/
theorem isProper_of_surjective_of_isClosedImmersion_projectiveSpace (f : X ⟶ S) (π : X' ⟶ X)
    (i : X' ⟶ ProjectiveSpace n S) [Surjective π] [IsClosedImmersion i] [IsSeparated f]
    [LocallyOfFiniteType f] (w : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) :
    IsProper f :=
  have : UniversallyClosed (π ≫ f) := by rw [w]; infer_instance
  have := UniversallyClosed.of_comp_surjective π f
  ⟨⟩

/-- **A Chow modification of a proper morphism immerses as a closed subscheme of projective
space.** Let `f : X ⟶ S` and `π : X' ⟶ X` be proper and let `i : X' ⟶ ℙⁿ_S` be an immersion with
`π ≫ f = i ≫ (ℙⁿ_S ↘ S)`. Then `i` is a closed immersion.

The composite `i ≫ (ℙⁿ_S ↘ S)` equals the proper morphism `π ≫ f`, and `ℙⁿ_S ⟶ S` is separated,
so `i` is proper; a proper immersion is universally closed and hence a closed immersion. -/
theorem isClosedImmersion_projectiveSpace_of_isProper (f : X ⟶ S) (π : X' ⟶ X)
    (i : X' ⟶ ProjectiveSpace n S) [IsProper f] [IsProper π] [IsImmersion i]
    (w : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) :
    IsClosedImmersion i :=
  have : IsProper (i ≫ (ProjectiveSpace n S ↘ S)) := by rw [← w]; infer_instance
  have : IsProper i := IsProper.of_comp i (ProjectiveSpace n S ↘ S)
  (isClosedImmersion_iff_universallyClosed i).mpr inferInstance

/-- **The properness criterion of [Stacks, Tag 0205] read off the square of Tag 05LZ.** Given a
commutative square `π ≫ f = i ≫ (ℙⁿ_S ↘ S)` with `π : X' ⟶ X` proper surjective, `i : X' ⟶ ℙⁿ_S`
an immersion and `f : X ⟶ S` separated and locally of finite type, the morphism `f` is proper if
and only if `i` is a closed immersion. -/
theorem isProper_iff_isClosedImmersion_projectiveSpace (f : X ⟶ S) (π : X' ⟶ X)
    (i : X' ⟶ ProjectiveSpace n S) [IsProper π] [Surjective π] [IsImmersion i] [IsSeparated f]
    [LocallyOfFiniteType f] (w : π ≫ f = i ≫ (ProjectiveSpace n S ↘ S)) :
    IsProper f ↔ IsClosedImmersion i :=
  ⟨fun h ↦ have := h; isClosedImmersion_projectiveSpace_of_isProper f π i w,
    fun h ↦ have := h; isProper_of_surjective_of_isClosedImmersion_projectiveSpace f π i w⟩

/-- **The square of [Stacks, Tag 05LZ].** Let `f : X ⟶ S` be proper and admit a Chow
modification. Then there are an `n`, a scheme `X'`, a proper **surjective** morphism
`π : X' ⟶ X` and a **closed immersion** `i : X' ⟶ ℙⁿ_S` with
`π ≫ f = i ≫ (ℙⁿ_S ↘ S)`, that is, a commutative square

```
X' ---i---> ℙⁿ_S
|            |
π            |
v            v
X ----f----> S
```

over `S` whose left vertical morphism is surjective and whose top morphism is a closed immersion
into projective space over `S`.

Chow's lemma supplies the square with `i` merely an immersion; properness of `f` upgrades it to a
closed immersion. -/
@[stacks 05LZ]
theorem exists_surjective_isClosedImmersion_projectiveSpace_of_isProper (f : X ⟶ S) [IsProper f]
    (hf : HasChowModification f) :
    ∃ (n : ℕ) (X' : Scheme.{u}) (π : X' ⟶ X) (i : X' ⟶ ProjectiveSpace n S),
      IsProper π ∧ Surjective π ∧ IsClosedImmersion i ∧
        π ≫ f = i ≫ (ProjectiveSpace n S ↘ S) := by
  obtain ⟨n, X'', π, i, hπ, hπsurj, hi, w⟩ := hf
  have := hπ
  have := hi
  exact ⟨n, X'', π, i, hπ, hπsurj, isClosedImmersion_projectiveSpace_of_isProper f π i w, w⟩

end AlgebraicGeometry
