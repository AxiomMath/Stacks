module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.DualComplexOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Duals.LocallyStrictlyPerfectDualComplex
import StacksCore.Tactic.StacksAttribute

/-!
# The dual complex under the hypothesis of the tag

[Stacks, Tag 0FPR] assumes of `ℱ^•` exactly this: *for every object `U` of the site there
exists a covering `{U_i → U}` such that `ℱ^•|_{U_i}` is strictly perfect.* This file writes
that hypothesis down — `Stacks.SheafOfModules.Strict.IsLocallyStrictlyPerfect` — and derives
from it the two conditions the dual complex of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Duals/DualComplexOfModules.lean` is built from:
every term is locally a direct summand of a finite free module, and the complex is locally
bounded. The dual complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` is then available under the tag's own
hypothesis rather than under the termwise half of it.

Strict perfectness is [Stacks, Tag 08FL], `IsStrictlyPerfect`, and it is a conjunction: the
complex vanishes outside a finite set of degrees, and each of its terms is a direct summand of
a finite free module. Restricting the quantifier over the members of the covering to one degree
at a time gives the first condition; keeping the finite set of degrees that the member supplies
gives the second.

## Main definitions

* `Stacks.SheafOfModules.Strict.IsLocallyStrictlyPerfect`: the hypothesis of
  [Stacks, Tag 0FPR].
* `Stacks.SheafOfModules.Strict.dualComplexOfLocallyStrictlyPerfect`: **the dual complex `𝒢^•`
  of [Stacks, Tag 0FPR], under the tag's own hypothesis.**

## Main results

* `Stacks.SheafOfModules.Strict.isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect`:
  each term of a locally strictly perfect complex is locally a direct summand of a finite free
  module — the termwise hypothesis of [Stacks, Tag 0FNY], and the hypothesis under which
  `Stacks.SheafOfModules.Strict.dualComplex` is built.
* `Stacks.SheafOfModules.Strict.isLocallyBounded_of_isLocallyStrictlyPerfect`: a locally
  strictly perfect complex is locally bounded, in the shape
  `Stacks.SheafOfModules.Strict.isLocallyBounded_of_exactPairing` produces for a complex with a
  left dual.

## Implementation notes

**Why the hypothesis is not a global finite set of degrees.** The finite set of surviving
degrees supplied by `IsStrictlyPerfect.bounded` depends on the member of the covering, and
different members may supply different sets with no common bound; local boundedness is
therefore strictly weaker than boundedness, and the complex of a left dual is only locally
bounded ([Stacks, Tag 0FPA], `isLocallyBounded_of_exactPairing`).
`Stacks.SheafOfModules.Strict.exactPairingDualComplex` consumes one global finite set, because
`η = ∑ ηₙ` is assembled there as a finite sum of morphisms. Under the hypothesis below that sum
is only locally finite, and the morphism it defines is produced from its components instead;
that is `Stacks.SheafOfModules.Strict.exactPairingDualComplexOfLocallyStrictlyPerfect`, the
left-dual assertion of [Stacks, Tag 0FPR] under this hypothesis.

**The two universes of the index type.** `IsDirectSummandOfFiniteFree` compares a module with
`SheafOfModules.free (ULift.{max u v} (Fin n))`, while
`IsLocallyDirectSummandOfFiniteFree` asks for *some* finite index type in `Type (max u v)`;
`isDirectSummandOfFiniteFree_iff_free` is the passage, at the equal universes the ringed-site
consumers work in, and `ULift.{max u v} (Fin n)` is the index type it hands over.

## References

* [Stacks Project, Tag 0FPR](https://stacks.math.columbia.edu/tag/0FPR)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0FNY](https://stacks.math.columbia.edu/tag/0FNY)
* [Stacks Project, Tag 0FPA](https://stacks.math.columbia.edu/tag/0FPA)
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

noncomputable section

universe v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (K : CochainComplex (Mod R) ℤ)

/-- **The hypothesis of [Stacks, Tag 0FPR].** Every object `U` of the site has a covering sieve
on whose members the restriction of `ℱ^•` is a strictly perfect complex of [Stacks, Tag 08FL]:
bounded, with every term a direct summand of a finite free module.

This is the first conclusion of [Stacks, Tag 0FPS],
`Stacks.SheafOfModules.Strict.exists_cover_isStrictlyPerfect_of_exactPairing`, so the two tags
are converse to one another over this predicate; the second conclusion of that tag identifies
the left dual with the complex built here. -/
def IsLocallyStrictlyPerfect : Prop :=
  ∀ U : C, ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), T g →
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf R).over V)
      (restrictComplexOver R K V)

variable {R K}

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **A locally strictly perfect complex is locally bounded.** On a member of the covering all
but finitely many terms restrict to zero; the finite set of surviving degrees is the one the
member's strict perfectness supplies, and it depends on the member.

This is the hypothesis [Stacks, Tag 0FPA] produces for a complex with a left dual, so a complex
satisfying the hypothesis of [Stacks, Tag 0FPR] satisfies the conclusion of [Stacks, Tag 0FPA]
on the nose. -/
theorem isLocallyBounded_of_isLocallyStrictlyPerfect (hK : IsLocallyStrictlyPerfect R K)
    (U : C) :
    ∃ T : Sieve U, T ∈ J U ∧ ∀ ⦃V : C⦄ (g : V ⟶ U), T g →
      ∃ S : Finset ℤ, ∀ n ∉ S, IsZero ((K.X n).over V) := by
  classical
  obtain ⟨T, hT, hsp⟩ := hK U
  refine ⟨T, hT, fun V g hg => ⟨(hsp g hg).bounded.toFinset, fun n hn => ?_⟩⟩
  by_contra hz
  exact hn ((hsp g hg).bounded.mem_toFinset.2 hz)

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **Every term of a locally strictly perfect complex is locally a direct summand of a finite
free module.** This is the termwise hypothesis of [Stacks, Tag 0FNY], under which the dual sheaf
`SheafHom(ℱ^n, 𝒪)` is a left dual of `ℱ^n`, and it is what
`Stacks.SheafOfModules.Strict.dualComplex` is built from. One covering serves every degree: the
covering of [Stacks, Tag 0FPR] is a single one on whose members the *whole* complex is strictly
perfect. -/
theorem isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect
    (hK : IsLocallyStrictlyPerfect R K) (n : ℤ) :
    IsLocallyDirectSummandOfFiniteFree R.obj (isSheaf_ringSheaf R) (K.X n) := by
  intro U
  obtain ⟨T, hT, hsp⟩ := hK U
  refine ⟨T, hT, fun V g hg => ?_⟩
  obtain ⟨m, i, r, hir⟩ :=
    (isDirectSummandOfFiniteFree_iff_free _ _).1 ((hsp g hg).termDirectSummand n)
  exact ⟨ULift.{max u v} (Fin m), inferInstance, ⟨⟨i, r, hir⟩⟩⟩

variable (R K)

/-- **The dual complex `𝒢^• = SheafHom^•(ℱ^•, 𝒪)` of [Stacks, Tag 0FPR], under the hypothesis
of the tag.** Its degree-`j` term is the dual sheaf `SheafHom(ℱ^{-j}, 𝒪)` and its differential
is the signed transpose `d_𝒢^j = -(-1)^j (d_ℱ^{-j-1})^∨`, exactly as in
`Stacks.SheafOfModules.Strict.dualComplex`; what is new is that the hypothesis is the tag's own
local one, not the termwise condition extracted from it. -/
def dualComplexOfLocallyStrictlyPerfect (hK : IsLocallyStrictlyPerfect R K) :
    CochainComplex (Mod R) ℤ :=
  dualComplex R K (isLocallyDirectSummandOfFiniteFree_X_of_isLocallyStrictlyPerfect hK)

/-- The terms of the dual complex of a locally strictly perfect complex are the dual sheaves of
the terms of `ℱ^•` in the opposite degrees. -/
theorem dualComplexOfLocallyStrictlyPerfect_X (hK : IsLocallyStrictlyPerfect R K) (j : ℤ) :
    (dualComplexOfLocallyStrictlyPerfect R K hK).X j =
      dualSheaf R.obj (isSheaf_ringSheaf R) (K.X (-j)) :=
  rfl

end Stacks.SheafOfModules.Strict

end

end
