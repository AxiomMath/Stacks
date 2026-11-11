module

import Mathlib.FieldTheory.SeparablyGenerated
import StacksCore.Tactic.StacksAttribute

public import StacksFrontier.FieldTheory.Separable.TFAE

/-!
# A separably generated field extension is separable

Following [stacks, 030O], a field extension `K/k` is *separably generated* if there is a
transcendence basis `s` of `K/k` such that `K` is separable algebraic over `k(s)` (a *separating*
transcendence basis), and `K/k` is *separable* if every subextension `k ⊆ L ⊆ K` with `L` finitely
generated over `k` is separably generated over `k`. A separating transcendence basis of `K/k` need
not restrict to one of `L/k`; nevertheless a separably generated extension is separable: for every
finitely generated subextension `L/k` there is a finite separating transcendence basis of `L/k`.

## Main results

* `Algebra.isSeparableExtension_tower_bot_of_isSeparableExtension`,
  `IntermediateField.isSeparableExtension_tower_bot`: a subextension of a separable extension is
  separable, separability being that of Definition 030O (2) [stacks, 030P].
* `exists_isTranscendenceBasis_and_isSeparable_of_isSeparable_adjoin_of_essFiniteType`: if `K/k`
  has a separating transcendence basis and `k ⊆ L ⊆ K` with `L/k` finitely generated, then `L/k`
  has a finite separating transcendence basis.

## Implementation notes

"Separably generated" is spelled out as
`∃ t, IsTranscendenceBasis k t ∧ Algebra.IsSeparable (IntermediateField.adjoin k t) L`, the shape
used by `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`; Mathlib's
`Algebra.IsSeparable` is separability of an algebraic extension. The subextension is an abstract
field `L` in a tower `k → L → K`, which specializes to `L : IntermediateField k K`, and "finitely
generated field extension" is `Algebra.EssFiniteType k L` (`IntermediateField.fg_top_iff`).

## References

* [Stacks Project, Tag 030P](https://stacks.math.columbia.edu/tag/030P)
* [Stacks Project, Tag 030X](https://stacks.math.columbia.edu/tag/030X)
-/

@[expose] public section

/-- Tag 030P: if `K/k` is separable in the sense of Definition 030O (2), then so is `K'/k` for every
field `K'` in a tower `k → K' → K`. A subextension `L` of `K'/k` finitely generated over `k` is
isomorphic over `k` to its image in `K`, which is finitely generated over `k`, hence separably
generated over `k`; a separating transcendence basis of the image transports back along the
isomorphism. -/
@[stacks 030P "tower form; separable is `Algebra.IsSeparableExtension`, Definition 030O (2)"]
public theorem Algebra.isSeparableExtension_tower_bot_of_isSeparableExtension
    (k K' K : Type*) [Field k] [Field K'] [Field K] [Algebra k K'] [Algebra k K] [Algebra K' K]
    [IsScalarTower k K' K] [Algebra.IsSeparableExtension k K] :
    Algebra.IsSeparableExtension k K' := by
  refine ⟨fun L _ ↦ ?_⟩
  let f : K' →ₐ[k] K := IsScalarTower.toAlgHom k K' K
  let e : L.map f ≃ₐ[k] L := (L.equivMap f).symm
  have : Algebra.EssFiniteType k (L.map f) :=
    (Algebra.EssFiniteType.iff_of_algEquiv e).mpr ‹_›
  obtain ⟨s, hs, hsep⟩ :=
    (Algebra.IsSeparableExtension.isSeparablyGenerated (k := k) (L.map f)
      ).isSeparable
  have hmap : (IntermediateField.adjoin k s).map (e : L.map f →ₐ[k] L)
      = IntermediateField.adjoin k (e '' s) := IntermediateField.adjoin_map k s _
  refine ⟨e '' s, (e.isTranscendenceBasis hs).to_subtype_range'
    (by rw [Set.range_comp, Subtype.range_coe]), ?_⟩
  exact Algebra.IsSeparable.of_equiv_equiv
    ((IntermediateField.intermediateFieldMap e (IntermediateField.adjoin k s)).trans
      (IntermediateField.equivOfEq hmap)).toRingEquiv e.toRingEquiv (by ext x; rfl)

/-- Tag 030P: if `K/k` is separable in the sense of Definition 030O (2), then for every
subextension `K/K'/k` the extension `K'/k` is separable. -/
@[stacks 030P "separable is `Algebra.IsSeparableExtension`, Definition 030O (2)"]
public theorem IntermediateField.isSeparableExtension_tower_bot {k K : Type*} [Field k] [Field K]
    [Algebra k K] [Algebra.IsSeparableExtension k K] (K' : IntermediateField k K) :
    Algebra.IsSeparableExtension k K' :=
  Algebra.isSeparableExtension_tower_bot_of_isSeparableExtension k K' K

namespace Stacks.Separable.SeparablyGenerated

/-- A geometrically reduced, finitely generated field extension is separably generated, by a finite
separating transcendence basis. -/
private theorem exists_isTranscendenceBasis_and_isSeparable_of_isGeometricallyReduced (k L : Type*)
    [Field k] [Field L] [Algebra k L] [Algebra.EssFiniteType k L]
    [Algebra.IsGeometricallyReduced k L] :
    ∃ t : Finset L,
      IsTranscendenceBasis k ((↑) : t → L) ∧
        Algebra.IsSeparable (IntermediateField.adjoin k (t : Set L)) L := by
  obtain ⟨p, hp⟩ := ExpChar.exists k
  obtain hp' | rfl := expChar_is_prime_or_one (R := k) p
  · have H := ((Algebra.isSeparableExtension_tfae k L p).out 4 2).mp ‹_›
    exact
      exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType p hp'
        fun t ht ↦ H _ ht
  · have : CharZero k := charZero_of_expChar_one' k
    exact exists_isTranscendenceBasis_and_isSeparable_of_perfectField k L

/-- If `K/k` has a separating transcendence basis `s`, then every field `L` in a tower
`k → L → K` that is finitely generated over `k` has a finite separating transcendence basis. -/
public theorem solution {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra L K] [IsScalarTower k L K] [Algebra.EssFiniteType k L] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k s) K) :
    ∃ t : Finset L,
      IsTranscendenceBasis k ((↑) : t → L) ∧
        Algebra.IsSeparable (IntermediateField.adjoin k (t : Set L)) L := by
  have : Algebra.IsSeparablyGenerated k K := ⟨s, hs, hsep⟩
  have : Algebra.IsGeometricallyReduced k K :=
    Stacks.GeometricallyReduced.Separability.isGeometricallyReduced_of_isSeparablyGenerated k K
  have : Algebra.IsGeometricallyReduced k L :=
    .of_injective (IsScalarTower.toAlgHom k L K) (algebraMap L K).injective
  exact exists_isTranscendenceBasis_and_isSeparable_of_isGeometricallyReduced k L

end Stacks.Separable.SeparablyGenerated

/-- A separably generated field extension is separable. Let `K/k` be a field extension with a
separating transcendence basis `s`, that is, a transcendence basis of `K/k` such that `K` is
separable algebraic over `k(s)`. Then every subextension `k ⊆ L ⊆ K` which is finitely generated
over `k` again has a separating transcendence basis: there is a finite transcendence basis `t` of
`L/k` such that `L` is separable algebraic over `k(t)`. -/
@[stacks 030X]
public theorem exists_isTranscendenceBasis_and_isSeparable_of_isSeparable_adjoin_of_essFiniteType
    {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra L K]
    [IsScalarTower k L K] [Algebra.EssFiniteType k L] {s : Set K}
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k s) K) :
    ∃ t : Finset L,
      IsTranscendenceBasis k ((↑) : t → L) ∧
        Algebra.IsSeparable (IntermediateField.adjoin k (t : Set L)) L :=
  Stacks.Separable.SeparablyGenerated.solution (s := s) (K := K) hs hsep
