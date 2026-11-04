module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorGenericModuleStalkMem
public import StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection

/-!
# The first collection of Stacks 0EPS, from a presentation on the generic charts

Let `X` be a locally Noetherian integral algebraic space over `S`, let `ℒ` be an `𝒪_X`-module
and let `s` be a meromorphic section of `ℒ`.  The first of the two collections of Stacks 0EPS is

`{Z ⊂ X | Z a prime divisor with generic point ξ and s ∉ ℒ_ξ}`,

and this file proves it locally finite from one geometric input: a nonempty open subset
`U ⊆ |X|` over whose points `s` is an honest section of `ℒ` on the *generic chart* of every
prime divisor whose generic point lies in `U`.

That input is what the first sentence of the source's proof produces — "there exists a nonempty
open subspace `U ⊆ X` such that `s` corresponds to a section of `Γ(U, ℒ)` which generates `ℒ`
over `U`" — read at the elementary étale neighbourhoods
`AlgebraicGeometry.Space.PrimeDivisor.genericEtaleChart` rather than on an open subspace.  It is
the only thing between this statement and Stacks 0EPS's first collection, and it needs no lift
of `c_ξ`: the canonical morphism already factors through the generic chart.

## Main results

* `AlgebraicGeometry.Space.locallyFinite_primeDivisor_not_memGenericModuleStalk`: the first
  collection of Stacks 0EPS is locally finite, given the nonempty open subset and the
  presentation of `s` as an honest section over the generic chart of every prime divisor whose
  generic point lies in it.

## Implementation notes

The predicate is taken at a family `RR` of henselizations, one for each prime divisor, with its
standing hypotheses as `∀`-quantified instance arguments — the same device
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection` uses for the family of orders
of vanishing.  A single prime divisor's condition does not depend on the choice of
henselization, but the library has no transport statement for it, so the family is carried.

No invertibility of `ℒ` is needed here: the descent of honesty along an étale covering, which is
where invertibility enters, is not used, because `c_ξ` factors through the generic chart on the
nose.  Invertibility is needed to *produce* the hypothesis `hhon` from a presentation on some
other chart, by
`AlgebraicGeometry.Space.exists_eval_eq_toMeromorphicSectionValue_of_sieve`.

Regularity of `s` — Stacks 0ENB,
`AlgebraicGeometry.Space.IsRegularMeromorphicSection` — is likewise absent: it is the source's
hypothesis on `s`, and it is what the missing first sentence of the proof is derived from, not
something this step consumes.  So this statement does **not** carry Stacks 0EPS; the two
existing carriers in
`StacksFrontier.AlgebraicGeometry.Spaces.DivisorOfMeromorphicSection` continue to record what is
established, and the implementation notes there say what remains.

## References

* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X)
    (RR : PrimeDivisor B S hS X → Type u) [∀ Z, CommRing (RR Z)] [∀ Z, IsLocalRing (RR Z)]
    [∀ Z : PrimeDivisor B S hS X,
      Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point) (RR Z)]
    [∀ Z : PrimeDivisor B S hS X, IsLocalRing.IsHenselization
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)
      (IsLocalRing.ResidueField
        ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
          (Z.genericChart B S hS hX hdec).point)) (RR Z)]
    (hRR : ∀ Z : PrimeDivisor B S hS X, B.Contains (Spec (.of (RR Z))))

include hX hdec in
/-- **The first collection of Stacks 0EPS, from a presentation of `s` on the generic charts.**
Let `X` be a locally Noetherian integral algebraic space over `S`, let `ℒ` be an `𝒪_X`-module
and let `s` be a meromorphic section of `ℒ`.  Suppose there is a nonempty open subset
`U ⊆ |X|` such that for every prime divisor `Z` whose generic point lies in `U` the section `s`
is, over the generic chart of `Z`, the image of an honest section of `ℒ`.  Then the prime
divisors `Z` with `s ∉ ℒ_{ξ_Z}` are locally finite in `|X|`.

The generic point of such a prime divisor avoids `U`, because `c_ξ` factors through the generic
chart, so a presentation of `s` as an honest section there puts the germ of `s` at `ξ` in the
image of `ℒ_ξ` by
`AlgebraicGeometry.Space.PrimeDivisor.memGenericModuleStalk_of_eval_genericEtaleChart_eq`;
local finiteness is then the Stacks 0EE5 step
`AlgebraicGeometry.Space.locallyFinite_primeDivisor_of_genericPoint_notMem`. -/
theorem locallyFinite_primeDivisor_not_memGenericModuleStalk
    (hN : HasEtaleLocalProperty B S hS X (fun Y : Scheme.{u} ↦ IsLocallyNoetherian Y))
    (hirr : IrreducibleSpace (points B S hS X)) (L : Modules.{u, u} B S hS X hX)
    (s : MeromorphicSection.{u, u} B S hS X hX L)
    [DecidablePred fun Z : PrimeDivisor B S hS X ↦
      ¬ Z.MemGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s]
    (U : Set (points B S hS X)) (hUopen : IsOpen U) (hUne : U.Nonempty)
    (hhon : ∀ Z : PrimeDivisor B S hS X, Z.genericPoint B S hS X ∈ U →
      ∃ e : L.val.obj (op (Z.genericEtaleChart B S hS hX hdec)),
        s.eval (op (Z.genericEtaleChart B S hS hX hdec)) =
          toMeromorphicSectionValue B S hS X hX L (Z.genericEtaleChart B S hS hX hdec) e) :
    LocallyFinite fun Z : PrimeDivisor B S hS X ↦
      if ¬ Z.MemGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s then
        Z.support B S hS X
      else ∅ := by
  refine locallyFinite_primeDivisor_of_genericPoint_notMem B S hS hX hN hirr
    (fun Z ↦ ¬ Z.MemGenericModuleStalk B S hS hX hdec (RR Z) (hRR Z) L s) U hUopen hUne
    (fun Z hZ ↦ ?_)
  intro hmem
  obtain ⟨e, he⟩ := hhon Z hmem
  exact hZ (Z.memGenericModuleStalk_of_eval_genericEtaleChart_eq B S hS hX hdec (RR Z) (hRR Z)
    L s e he)

end AlgebraicGeometry.Space

end
