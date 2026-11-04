module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibres
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Universally bounded fibres of a morphism from a scheme to an algebraic space

A morphism `f : U ⟶ X` from a scheme over `S` to an algebraic space over `S` has
*universally bounded fibres* when one integer `n` bounds the degree over `k` of the fibre
product `Spec k ×_X U` for every field `k` and every field-valued point `Spec k ⟶ X`. Each
such fibre product is required to be a finite scheme over `k`, so that it has a degree at
all.

## Main definitions

No new definitions are introduced: the condition on `f` is
`AlgebraicGeometry.Space.HasUniversallyBoundedFibers`, defined in
`StacksFrontier/AlgebraicGeometry/Spaces/Decent/UniversallyBoundedFibres.lean`.

## Main results

* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_bound` builds the condition from
  one explicit bound.
* `AlgebraicGeometry.Space.HasUniversallyBoundedFibers.exists_isFiniteLocallyFree` records
  the consequence that every field-valued fibre is a finite locally free scheme over the
  field, with the rank forgotten.

## Implementation notes

A field-valued point of `X` is taken as a morphism `yoneda.obj T ⟶ X` out of an object `T`
of the big fppf site over `S` whose underlying scheme is isomorphic to `Spec k`; the site is
closed under nothing in particular, so the isomorphism rather than an equality is what can
be asked for. The fibre product is not formed as a limit in the presheaf category but
specified by a cartesian square `IsPullback i (yoneda.map p) f ξ` whose upper left corner is
again representable, by an object `V` of the site. This is the form in which the condition is
used: what a consumer needs is the structure morphism `p : V ⟶ T` of the fibre over the
field, and the degree of the fibre is the rank of that morphism as a finite locally free
morphism, `Stacks.Morphisms.IsFiniteLocallyFreeOfRank` of Stacks 02KA. Representability of
the square is therefore part of the condition and not a consequence of it; nothing here
assumes that `X` is an algebraic space, and the condition is stated for an arbitrary
presheaf, exactly as the source's quantifier over field-valued points allows.

The name. This is the condition of Stacks 03JL on a morphism to an algebraic space, not the
condition of Stacks 03J4 on a morphism of schemes; the latter is
`AlgebraicGeometry.HasUniversallyBoundedFibers`, and the two are different objects, with
different arguments — 03J4 quantifies over the points of the target scheme and uses the fibre
over the residue field at each, while 03JL quantifies over all field-valued points of a
presheaf. Following the naming policy of the algebraic-space layer the space-level condition
keeps its source spelling inside the namespace `AlgebraicGeometry.Space`. Inside that
namespace a bare `HasUniversallyBoundedFibers` therefore resolves to this one; write
`_root_.AlgebraicGeometry.HasUniversallyBoundedFibers` for the scheme-level condition of
03J4.

## References

* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X)

/-- One explicit bound on the degrees of the field-valued fibres makes those fibres
universally bounded. -/
theorem hasUniversallyBoundedFibers_of_bound (n : ℤ)
    (h : ∀ (k : Type u) [Field k] (T : BigFppfOver B S hS),
      ((BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k)) →
      ∀ ξ : yoneda.obj T ⟶ X,
        ∃ (V : BigFppfOver B S hS) (p : V ⟶ T)
          (i : yoneda.obj V ⟶ yoneda.obj U) (r : ℕ),
          (r : ℤ) ≤ n ∧
            Stacks.Morphisms.IsFiniteLocallyFreeOfRank
              ((BigFppfOver.toScheme B S hS).map p) r ∧
            IsPullback i (yoneda.map p) f ξ) :
    HasUniversallyBoundedFibers B S hS U f :=
  ⟨n, h⟩

/-- If the fibres of `f` are universally bounded then the fibre over any field-valued point
of the target is represented by an object of the site whose structure morphism to the field
is finite locally free, the rank being forgotten. -/
theorem HasUniversallyBoundedFibers.exists_isFiniteLocallyFree
    (hf : HasUniversallyBoundedFibers B S hS U f) (k : Type u) [Field k]
    (T : BigFppfOver B S hS)
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (CommRingCat.of k))
    (ξ : yoneda.obj T ⟶ X) :
    ∃ (V : BigFppfOver B S hS) (p : V ⟶ T) (i : yoneda.obj V ⟶ yoneda.obj U),
      Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map p) ∧
        IsPullback i (yoneda.map p) f ξ := by
  obtain ⟨n, hn⟩ := hf
  obtain ⟨V, p, i, r, -, hr, hsq⟩ := hn k T e ξ
  exact ⟨V, p, i,
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ r (h := hr), hsq⟩

end AlgebraicGeometry.Space

end
