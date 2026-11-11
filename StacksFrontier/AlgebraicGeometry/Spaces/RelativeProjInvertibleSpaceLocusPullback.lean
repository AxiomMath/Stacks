module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpace

/-!
# The open subspace `U(ψ)` of Stacks 0D2Y and its pullback along `X' ⟶ X`

[Stacks, Tag 0D2Y] is a situation.  It fixes a scheme `S`, an algebraic space `Y` over `S`, a
quasi-coherent graded `𝒪_Y`-algebra `𝒜` with relative Proj `π : Proj_Y(𝒜) ⟶ Y`, a morphism of
algebraic spaces `f : X ⟶ Y` over `S`, an invertible `𝒪_X`-module `ℒ` and a homomorphism of
graded `𝒪_X`-algebras `ψ : f^*𝒜 ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}`.  It lets `U(ψ) ⊆ X` be the open subspace
with

  `|U(ψ)| = ⋃_{d ≥ 1} {locus where f^*𝒜_d ⟶ ℒ^{⊗ d} is surjective}`,

and asserts that formation of `U(ψ) ⊆ X` commutes with pullback by any morphism `X' ⟶ X`.

The situation `(S, Y, 𝒜)` is `AlgebraicGeometry.Space.RelativeProjSituation` (Situation 0849:
`Y` an algebraic space over `S`, `𝒜` a quasi-coherent graded `𝒪_Y`-algebra, given with its
restrictions to the scheme points of `Y` and the comparisons between them).  The pair `(ℒ, ψ)`
over `f : X ⟶ Y` is `AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction`,
presented by its restrictions to the scheme points of `X`, and the open subspace `U(ψ)` is
`…InvertibleTwistingRestriction.locus`, both from
`StacksFrontier/AlgebraicGeometry/Spaces/RelativeProjInvertibleSpace.lean`.  This file adds the
pullback of `(ℒ, ψ)` along an arbitrary morphism `g : X' ⟶ X` and the compatibility of `U(ψ)`
with it, and collects the whole situation in `tag0D2Y`.

## Main definitions

* `…InvertibleTwistingRestriction.comap`: the pullback `(g^*ℒ, g^*ψ)` along `g : X' ⟶ X`, a pair
  over `f ∘ g : X' ⟶ Y`.

## Main results

* `…InvertibleTwistingRestriction.locus_comap`: **`U(g^*ψ) = g^{-1}(U(ψ))`** as subfunctors of
  `X'`, for every morphism `g : X' ⟶ X`.
* `…InvertibleTwistingRestriction.tag0D2Y`: the situation as a whole: `U(ψ)` is an open
  subspace of `X`, its preimage along a scheme point `x : T ⟶ X` is the open subscheme
  `U(x^*ψ)` of `T`, a point of `T` lies in `U(x^*ψ)` exactly when some positive-degree component
  of `x^*ψ` is surjective on a neighbourhood of it, and `U(g^*ψ) = g^{-1}(U(ψ))`.

## References

* [Stacks Project, Tag 0D2Y](https://stacks.math.columbia.edu/tag/0D2Y)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

universe u m

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

variable {s : RelativeProjSituation.{u, m}}
  {X X' : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f) (g : X' ⟶ X)

/-- **The pullback `(g^*ℒ, g^*ψ)` of `(ℒ, ψ)` along a morphism `g : X' ⟶ X`**, a pair over
`f ∘ g : X' ⟶ Y`.  A scheme point `x' : T ⟶ X'` is the scheme point `g ∘ x'` of `X`, and the
restrictions of `g^*ℒ` and `g^*ψ` to `x'` are those of `ℒ` and `ψ` to `g ∘ x'`, with the same
identifications along morphisms of test schemes. -/
@[stacks 0D2Y "the pullback (g^*L, g^*psi) of the data along a morphism of algebraic spaces \
g : X' -> X, a pair over f o g : X' -> Y"]
def comap : s.InvertibleTwistingRestriction (g ≫ f) where
  line T x := R.line T (x ≫ g)
  isInvertible T x := R.isInvertible T (x ≫ g)
  twisting T x := R.twisting T (x ≫ g)
  lineIso τ x := R.lineIso τ (x ≫ g)
  twisting_map τ x := R.twisting_map τ (x ≫ g)

/-- The open that `U(g^*ψ)` cuts on a scheme point `x'` of `X'` is the open that `U(ψ)` cuts on
`g ∘ x'`. -/
theorem locusOpen_comap (T : BigFppfOver s.site s.base s.containsBase) (x : yoneda.obj T ⟶ X') :
    (R.comap g).locusOpen T x = R.locusOpen T (x ≫ g) :=
  rfl

/-- **Formation of `U(ψ) ⊆ X` commutes with pullback by any morphism `g : X' ⟶ X`**
([Stacks, Tag 0D2Y]): the open subspace `U(g^*ψ)` of `X'` is the preimage `g^{-1}(U(ψ))`, that
is `X' ×_X U(ψ)`. -/
@[stacks 0D2Y "formation of U(psi) commutes with pullback by any morphism g : X' -> X: \
U(g^*psi) = g^{-1}(U(psi)) as subspaces of X'"]
theorem locus_comap : (R.comap g).locus = R.locus.preimage g := by
  ext T a
  obtain ⟨T⟩ := T
  have ha : g.app (op T) a = yonedaEquiv (yonedaEquiv.symm a ≫ g) := by
    rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  change a ∈ (R.comap g).locus.obj (op T) ↔ g.app (op T) a ∈ R.locus.obj (op T)
  rw [ha, R.mem_locus_iff, ← locusOpen_comap, ← (R.comap g).mem_locus_iff,
    Equiv.apply_symm_apply]

/-- **[Stacks, Tag 0D2Y].**  For the situation `(S, Y, 𝒜)`, a morphism `f : X ⟶ Y` from an
algebraic space `X` and `(ℒ, ψ)` over it:

1. `U(ψ)` is an open subspace of `X`;
2. its preimage along any scheme point `x : T ⟶ X` is the open subscheme `U(x^*ψ)` of `T`;
3. a point of `T` lies in `U(x^*ψ)` exactly when it has an open neighbourhood over which some
   component `x^*ψ_d`, `d ≥ 1`, is surjective, so `|U(ψ)|` is the union over `d ≥ 1` of the loci
   where `f^*𝒜_d ⟶ ℒ^{⊗ d}` is surjective;
4. formation of `U(ψ)` commutes with pullback by any morphism `g : X' ⟶ X`:
   `U(g^*ψ) = g^{-1}(U(ψ))`. -/
@[stacks 0D2Y "the open subspace U(psi) of X: it is open, its preimage along a scheme point \
x : T -> X is U(x^*psi), its points are those near which some f^*A_d -> L^d with d >= 1 is \
surjective, and U(g^*psi) = g^{-1}(U(psi)) for every morphism g : X' -> X"]
theorem tag0D2Y (hX : IsAlgebraicSpace s.site s.base s.containsBase X) :
    IsOpenSubspace s.site s.base s.containsBase R.locus ∧
    (∀ (T : BigFppfOver s.site s.base s.containsBase) (x : yoneda.obj T ⟶ X),
      R.locus.preimage x = subspaceOfOpens s.site s.base s.containsBase T (R.locusOpen T x)) ∧
    (∀ (T : BigFppfOver s.site s.base s.containsBase) (x : yoneda.obj T ⟶ X)
      (y : (BigFppfOver.toScheme s.site s.base s.containsBase).obj T),
      y ∈ R.locusOpen T x ↔
        ∃ (V : ((BigFppfOver.toScheme s.site s.base s.containsBase).obj T).Opens) (k : ℕ),
          0 < k ∧ y ∈ V ∧ Epi (((R.twisting T x).pullback V.ι).app (k : ℤ))) ∧
    (∀ {X' : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} (g : X' ⟶ X),
      (R.comap g).locus = R.locus.preimage g) :=
  ⟨R.isOpenSubspace_locus hX, R.preimage_locus, R.mem_locusOpen_iff_exists_epi,
    fun g => R.locus_comap g⟩

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction
