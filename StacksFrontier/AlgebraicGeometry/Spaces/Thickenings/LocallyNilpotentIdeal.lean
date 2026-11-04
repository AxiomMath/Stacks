module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSharpInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.NoetherianFiniteOrder

/-!
# The ideal of a thickening of algebraic spaces is locally nilpotent

Let `i_X : X ⟶ X'` be a thickening of algebraic spaces over a scheme `S`, and let
`𝓘 = Ker(i_X^♯) ⊆ 𝒪_{X'}` be its ideal sheaf on the small étale site of `X'`.  The running text of
Section 05ZJ of the Stacks project ("Thickenings", More on Morphisms of Spaces) records that any
local section of `𝓘` is locally nilpotent.  This file proves it.

## Main results

* `AlgebraicGeometry.Space.exists_sieve_isNilpotent_of_mem_definingIdealAt`: **Section 05ZJ**,
  every section of `𝓘` over an arbitrary étale chart of `X'` becomes nilpotent on the members
  of a covering sieve of that chart.

## Implementation notes

The sections of `𝓘` over an étale chart `U` of `X'` are the defining ideal
`AlgebraicGeometry.Space.definingIdealAt`, the kernel of the structure map of the inclusion at
`U`, which `AlgebraicGeometry.Space.definingIdealAt_eq_ker` identifies with the kernel of
pullback of regular functions along the closed immersion of schemes `X ×_{X'} U ⟶ U`.  That
closed immersion is surjective, being a base change of the inclusion of a thickening
(`AlgebraicGeometry.Space.presheafSurjective_of_isSurjective`).  A regular function killed by a
surjective morphism has empty basic open, so on an affine chart it is nilpotent; this affine case
is `AlgebraicGeometry.Space.isNilpotent_of_mem_definingIdealAt_of_isThickening`, from
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.NoetherianFiniteOrder`.  For an
arbitrary chart, the affine étale charts are cover dense in the small étale site (Stacks 04JS),
so the arrows factoring through an affine chart form a covering sieve, and restriction along
such an arrow carries a nilpotent to a nilpotent.

The source says "locally" without naming the topology; the small étale topology of `X'` is the
one in which `𝓘` is a sheaf, and through Equation 05ZL it is the same as that of `X`.

## References

* [Stacks Project, Tag 05ZJ](https://stacks.math.columbia.edu/tag/05ZJ)
* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- **Section 05ZJ: the ideal of a thickening is locally nilpotent.** Let `G ⊂ X` be a
thickening of algebraic spaces over `S`, with ideal sheaf `𝓘 = Ker(i^♯) ⊆ 𝒪_X` on the small
étale site of `X`.  Every local section `s` of `𝓘`, over an arbitrary étale chart `U` of `X`, is
locally nilpotent: there is a covering sieve of `U` along each of whose arrows the restriction of
`s` is nilpotent.

The covering sieve is that of the arrows factoring through an affine étale chart, which covers
by Stacks 04JS; on an affine chart the section is nilpotent by
`AlgebraicGeometry.Space.isNilpotent_of_mem_definingIdealAt_of_isThickening`. -/
@[stacks 05ZJ "any local section of the kernel I = Ker(i_X^#) of a thickening i_X : X -> X' is \
locally nilpotent (the paragraph after Lemma 05ZP), on the small etale site of X'"]
theorem exists_sieve_isNilpotent_of_mem_definingIdealAt (hG : IsThickening B S hS X G)
    (U : SmallEtale B S hS X.1)
    (s : ToType ((structureRingSheaf B S hS X).obj.obj (op U)))
    (hs : s ∈ definingIdealAt B S hS X ⟨G, hG.1⟩ (op U)) :
    ∃ T : Sieve U, T ∈ SmallEtale.topology B S hS X.1 U ∧
      ∀ (V : SmallEtale B S hS X.1) (m : V ⟶ U), T m →
        IsNilpotent (((structureRingSheaf B S hS X).obj.map m.op).hom s) := by
  have : (AffineEtale.inclusion B S hS X.1).IsCoverDense (SmallEtale.topology B S hS X.1) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS X.1 X.2).2.isCoverDense'
  refine ⟨_, (AffineEtale.inclusion B S hS X.1).is_cover_of_isCoverDense
    (SmallEtale.topology B S hS X.1) U, ?_⟩
  rintro V f ⟨⟨A, l, m, rfl⟩⟩
  have hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj
      ((AffineEtale.inclusion B S hS X.1).obj A)) := A.property
  have hmem := definingIdealAt_map B S hS X ⟨G, hG.1⟩ m.op s hs
  have hnil := isNilpotent_of_mem_definingIdealAt_of_isThickening B S hS hG _ hA _ hmem
  have hcomp : ((structureRingSheaf B S hS X).obj.map (l ≫ m).op).hom s =
      ((structureRingSheaf B S hS X).obj.map l.op).hom
        (((structureRingSheaf B S hS X).obj.map m.op).hom s) := by
    rw [op_comp, Functor.map_comp]
    rfl
  rw [hcomp]
  exact hnil.map _

add_to_stacks 05ZJ "the sentence after Equation 05ZM: the closed immersion i_X : X -> X' \
corresponds to the surjective map i_X^# : O_{X'} -> O_X, read on the small etale site of X as \
i_X^{-1}O_{X'} -> O_X (stated for every closed immersion)"
  AlgebraicGeometry.Space.isLocallySurjective_structureSharpInverseImage

end AlgebraicGeometry.Space

end
