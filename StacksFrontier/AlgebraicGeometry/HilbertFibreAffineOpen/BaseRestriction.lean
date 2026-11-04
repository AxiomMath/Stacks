module

public import StacksFrontier.AlgebraicGeometry.HilbertFibreAffineOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteSetInBasicOpen

/-!
# The hypothesis of the Hilbert-scheme criterion is inherited by an open of the base

Stacks Tag 0B9A represents the degree-`d` Hilbert functor of `X` over `S` under the assumption
that every `d`-tuple of points lying in a single fibre of `X ⟶ S` is contained in an affine open
of `X`. The assumption this file is about is the *set* form
`AlgebraicGeometry.HasAffineFinitePointsInFibres`, an affine open around every finite set of
points of a fibre, which is strictly stronger — it implies the `d`-tuple form for every `d` at
once, and is not implied by it (see the counterexample in the module docstring of
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorOpenAmbient.lean`). This file proves that
the set form is inherited by the restriction of the morphism over an open of the base.

`Stacks.HilbertFibreAffineOpen.hasAffineFinitePointsInFibres_of_iSup_eq_top` is the converse
direction, that the assumption is *implied* by its instances over the members of an open cover of
the base. Together the two say the assumption is local on the base.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.HasAffineFinitePointsInFibres.morphismRestrict` — the fibrewise affineness
  condition passes to the restriction of the morphism over an open of the base.
* `AlgebraicGeometry.exists_isAffineOpen_forall_mem_morphismRestrict` — the same in the
  `d`-tuple form in which Stacks Tag 0B9A states its hypothesis, so that the hypothesis of that
  proposition for `X ⟶ S` yields its hypothesis for `f ⁻¹ᵁ V ⟶ V`.

## Implementation notes

*Why this is needed for Tag 0B9A.* The source proves Tag 0B9A by reducing to an affine base and
then applying the gluing criterion of Stacks 01JJ to the subfunctors of families supported in an
affine open of `X`; condition (2)(a) of the criterion is representability of those subfunctors,
which is Stacks 0B99 and is stated for an *affine* base. Whichever way the reduction to an affine
base is carried out — the source's relative glueing, or a single application of the criterion
with the subfunctors indexed by pairs consisting of an affine open `V` of `S` and an affine open
of `f ⁻¹ᵁ V` — it needs the hypothesis of Tag 0B9A for `f ⁻¹ᵁ V ⟶ V`, which is what is proved
here. The route this development takes in the end is the second one, so the restriction to an
affine base is absorbed into the chart index and the statements here are not used by it; see
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorRepresentableAmbient.lean` for Tag 0B9A,
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorSupportedInOpen.lean` and
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorZariskiSheaf.lean` for the conditions of the
criterion, and
`StacksFrontier/AlgebraicGeometry/Picard/HilbertFunctorAffineRepresentable.lean` for what Stacks
0B99 carries. **No declaration here carries the `@[stacks 0B9A]` attribute**: this is an
input to a step of the proof, not one of the conditions the criterion consumes.

*Why the statement is not trivial.* An affine open of `X` containing the finite set need not be
contained in `f ⁻¹ᵁ V`, so it is not an affine open of `f ⁻¹ᵁ V`. It has to be shrunk, and
shrinking an affine open around a *finite* set inside a prescribed open is prime avoidance,
`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_subset_of_finite`. The resulting basic open is
affine, and being contained in `f ⁻¹ᵁ V` it is an affine open of that open subscheme by
`AlgebraicGeometry.IsAffineOpen.preimage_of_isOpenImmersion`.

## References

* [Stacks Project, Tag 0B9A](https://stacks.math.columbia.edu/tag/0B9A)
* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
* [Stacks Project, Tag 00DS](https://stacks.math.columbia.edu/tag/00DS)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The fibrewise affineness condition passes to an open of the base.** If every finite set of
points of `X` lying in a single fibre of `f : X ⟶ S` is contained in an affine open of `X`, then
for every open `V ⊆ S` the same holds for the restriction `f ∣_ V : f ⁻¹ᵁ V ⟶ V`.

The finite set is pushed into `X`, where the hypothesis produces an affine open containing it.
That affine open need not sit inside `f ⁻¹ᵁ V`, so it is shrunk by prime avoidance,
`AlgebraicGeometry.IsAffineOpen.exists_basicOpen_subset_of_finite`, to a basic open which does;
a basic open of an affine open is affine, and an affine open of `X` contained in `f ⁻¹ᵁ V` is an
affine open of `f ⁻¹ᵁ V`. -/
theorem HasAffineFinitePointsInFibres.morphismRestrict {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : HasAffineFinitePointsInFibres f) (V : S.Opens) :
    HasAffineFinitePointsInFibres (f ∣_ V) := by
  intro s E hE hEs
  -- Push `E` into `X`; it is finite and lies in the fibre over `s`.
  have hE'fin : (Subtype.val '' E : Set X).Finite := hE.image _
  have hE'fib : ∀ x ∈ (Subtype.val '' E : Set X), f.base x = s.1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← morphismRestrict_base_coe f V y, hEs y hy]
  obtain ⟨U, hU, hEU⟩ := hf s.1 _ hE'fin hE'fib
  -- `E` lies in `f ⁻¹ᵁ V` as well, so prime avoidance shrinks `U` into `f ⁻¹ᵁ V`.
  have hEV : (Subtype.val '' E : Set X) ⊆ ((f ⁻¹ᵁ V : X.Opens) : Set X) := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  obtain ⟨r, hrE, hrV⟩ := hU.exists_basicOpen_subset_of_finite hE'fin hEU (f ⁻¹ᵁ V) hEV
  -- The basic open is affine and contained in `f ⁻¹ᵁ V`, hence an affine open of `f ⁻¹ᵁ V`.
  refine ⟨(f ⁻¹ᵁ V).ι ⁻¹ᵁ X.basicOpen r,
    (hU.basicOpen r).preimage_of_isOpenImmersion (f ⁻¹ᵁ V).ι ?_, fun y hy => ?_⟩
  · rw [Scheme.Opens.opensRange_ι]
    exact hrV
  · exact hrE ⟨y, hy, rfl⟩

/-- **The hypothesis of Stacks Tag 0B9A for an open of the base.** If every `d`-tuple of points
lying in a single fibre of `f : X ⟶ S` is contained in an affine open of `X` — for every `d` at
once, in the set form `AlgebraicGeometry.HasAffineFinitePointsInFibres` — then for every open
`V ⊆ S` every `d`-tuple of points lying in a single fibre of `f ∣_ V : f ⁻¹ᵁ V ⟶ V` is contained
in an affine open of `f ⁻¹ᵁ V`.

This is the shape in which the proof of Tag 0B9A consumes its hypothesis after reducing to an
affine base. -/
theorem exists_isAffineOpen_forall_mem_morphismRestrict {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : HasAffineFinitePointsInFibres f) (V : S.Opens) (d : ℕ) (s : V.toScheme)
    (x : Fin d → (f ⁻¹ᵁ V).toScheme) (hx : ∀ i, (f ∣_ V).base (x i) = s) :
    ∃ U : (f ⁻¹ᵁ V).toScheme.Opens, IsAffineOpen U ∧ ∀ i, x i ∈ U :=
  Stacks.HilbertFibreAffineOpen.exists_isAffineOpen_forall_mem_of_hasAffineFinitePointsInFibres
    (hf.morphismRestrict V) d s x hx

end AlgebraicGeometry

end
