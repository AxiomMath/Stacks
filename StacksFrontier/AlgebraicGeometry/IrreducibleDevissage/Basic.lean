module

public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Filtration
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic

/-!
# The irreducible case of [Stacks, Tag 01YF], reduced to one submodule

`Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage` is the single
outstanding hypothesis of [Stacks, Tag 01YG] in this repository: with it,
`Stacks.AlgebraicGeometry.IdealPowerSmul.property_of_irreducibleDevissage` is Tag 01YG's statement
verbatim, 01YD having been discharged unconditionally by
`Stacks.AlgebraicGeometry.IdealPowerSmul.hasSupportSplitting`. It is also one of the two remaining
inputs of [Stacks, Tag 02O5]. It asks, for every coherent module `F` with irreducible support,
for a bounded dévissage filtration of `F` whose successive quotients each either are the direct
image of a quasi-coherent ideal sheaf on an integral closed subscheme, or are supported
strictly inside `supp F`.

This file reduces it, losslessly, to a statement with **no filtration in its conclusion and no
mixed quotient class**:

`Stacks.AlgebraicGeometry.IrreducibleDevissage.HasGenericIdealSub` asks for a single coherent
submodule `G ⊆ F`, filtered by direct images of quasi-coherent ideal sheaves alone, whose
cokernel is supported strictly inside `supp F`.

That is exactly the shape steps 3 and 4 of the source's proof deliver, and exactly the shape
[Stacks, Tag 01YE] produces: a monomorphism `i_*(I^{⊕ r}) ⟶ F` that is an isomorphism near the
generic point, the sub being filtered by its `r` factors and the cokernel missing the generic
point, hence supported strictly inside the (irreducible, closed) support. The mixed class and
the filtration bookkeeping that `HasIrreducibleDevissage` carries are discharged here once and
for all by appending one step.

## Main definitions

* `Stacks.AlgebraicGeometry.IrreducibleDevissage.HasGenericIdealSub`: **steps 3 and 4 of the
  proof of [Stacks, Tag 01YF], in one statement.**

## Main results

* `Stacks.AlgebraicGeometry.IrreducibleDevissage.hasIrreducibleDevissage_of_hasGenericIdealSub`:
  **the irreducible case of [Stacks, Tag 01YF] from the generic submodule alone.** Composed with
  `Stacks.AlgebraicGeometry.IdealPowerSmul.property_of_irreducibleDevissage` this gives Tag 01YG's
  statement verbatim with `HasGenericIdealSub X` as its one added hypothesis, and composed with
  `Stacks.AlgebraicGeometry.IdealPowerSmul.isIdealDevissable_of_isCoherent` it gives [Stacks, Tag
  01YF] in extension-closed form on the same one hypothesis.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.isIdealPushforward_of_iso` and
  `isIdealPushforward_or_supp_ssubset_of_iso`: the quotient class of [Stacks, Tag 01YF] and the
  mixed class of `HasIrreducibleDevissage` are invariant under isomorphism.

## Implementation notes

**Why the reduction is lossless and not a restatement.** The filtration `HasIrreducibleDevissage`
asks for is obtained from `HasGenericIdealSub` by appending one step: the `G`-filtration, whose
quotients are ideal pushforwards and so lie in the mixed class on the left disjunct, followed by
`G ⟶ F`, whose cokernel lies in it on the right disjunct. The converse direction is *not*
claimed and is false as stated — a filtration of `F` in the mixed class need not have all its
ideal-pushforward quotients below all its small-support ones. What is true, and is all the
induction of 01YF needs, is the direction proved here.

**The remaining mathematics, named.** `HasGenericIdealSub` is 01Y9 + 01J3 + 01YE. Of these,
01Y9 and 01J3 are now available absolutely — see
`Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isZero_idealPowSmul` and
`Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isIntegral_isClosedImmersion_range_eq` —
and 01YE is absent from this repository and from Mathlib at this pin, as is the statement that
the direct image of a finite coproduct of copies of an ideal sheaf is filtered by its factors.
The step that still blocks the passage from 01YE's conclusion to `HasGenericIdealSub`, i.e. the
reduction of a general coherent `F` to one killed by the ideal of its support, is the
`I`-adic filtration of step 3 together with the fact that its graded pieces are killed by that
ideal. The filtration is cheap now; the graded-piece statement needs exactness of sections over
an affine open on quasi-coherent modules, which this repository does not have — what it has,
in `StacksFrontier/AlgebraicGeometry/SectionsExact/Basic.lean`, is preservation of finite
*limits*, the left-exact half.

**No `@[stacks]` attribute is attached.** Every theorem
below either carries `HasGenericIdealSub X`, a hypothesis Tag 01YG does not have, or is a
fragment of a tag's assertion. None of 01YD, 01YE, 01YF, 01YG and 01YH is formalized here.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentDevissage
open Stacks.AlgebraicGeometry.DevissageBounded

universe u

namespace Stacks.AlgebraicGeometry.IrreducibleDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The cokernel of a morphism of coherent modules is coherent, with both hypotheses explicit. -/
theorem isCoherent_cokernel' {M N : X.Modules} (φ : M ⟶ N) (hM : M.IsCoherent)
    (hN : N.IsCoherent) : (cokernel φ).IsCoherent :=
  have := hM
  have := hN
  AlgebraicGeometry.CoherentAbelian.isCoherent_cokernel φ

/-- The quotient class of [Stacks, Tag 01YF] is invariant under isomorphism. -/
theorem isIdealPushforward_of_iso {M N : X.Modules} (e : M ≅ N)
    (h : IsIdealPushforward M) : IsIdealPushforward N := by
  obtain ⟨Z, i, hi, hZ, I, hI, ⟨f⟩⟩ := h
  exact ⟨Z, i, hi, hZ, I, hI, ⟨e.symm.trans f⟩⟩

/-- The mixed quotient class of
`Stacks.AlgebraicGeometry.DevissageNoetherian.HasIrreducibleDevissage` is invariant under
isomorphism. -/
theorem isIdealPushforward_or_supp_ssubset_of_iso {F M N : X.Modules} (e : M ≅ N)
    (h : IsIdealPushforward M ∨ SheafOfModules.supp M ⊂ SheafOfModules.supp F) :
    IsIdealPushforward N ∨ SheafOfModules.supp N ⊂ SheafOfModules.supp F := by
  rcases h with h | h
  · exact Or.inl (isIdealPushforward_of_iso e h)
  · exact Or.inr (by rwa [← supp_eq_of_iso e])

/-- **Steps 3 and 4 of the proof of [Stacks, Tag 01YF], in one statement.** Every coherent
module with irreducible support has a coherent submodule which is filtered by direct images of
quasi-coherent ideal sheaves on integral closed subschemes, and whose cokernel is supported
strictly inside the support of the module.

This is what [Stacks, Tag 01YE] delivers after step 3 has reduced to the case where the ideal
of the support annihilates the module: the submodule is `i_*(I^{⊕ r})` for `i` the reduced
induced structure on the support, filtered by its `r` factors, and the inclusion is an
isomorphism near the generic point, so its cokernel misses that point and is therefore
supported strictly inside the support. -/
def HasGenericIdealSub (X : Scheme.{u}) : Prop :=
  ∀ F : X.Modules, F.IsCoherent → IsIrreducible (SheafOfModules.supp F) →
    ∃ (G : X.Modules) (ι : G ⟶ F), Mono ι ∧ G.IsCoherent ∧
      HasDevissageWith IsIdealPushforward G ∧
      SheafOfModules.supp (cokernel ι) ⊂ SheafOfModules.supp F

/-- **The irreducible case of [Stacks, Tag 01YF] from the generic submodule alone.** The
filtration `HasIrreducibleDevissage` asks for is the filtration of the submodule, whose
quotients lie in the mixed class on the left disjunct, with the inclusion of the submodule
appended on top, whose cokernel lies in it on the right disjunct. -/
theorem hasIrreducibleDevissage_of_hasGenericIdealSub (h : HasGenericIdealSub X) :
    DevissageNoetherian.HasIrreducibleDevissage X := by
  intro F hF hirr
  obtain ⟨G, ι, hmono, hGc, hGd, hsupp⟩ := h F hF hirr
  have hm : Mono ι := hmono
  exact hasDevissageWith_snoc (fun e hM => isIdealPushforward_or_supp_ssubset_of_iso e hM) ι hF
    (isCoherent_cokernel' ι hGc hF) (Or.inr hsupp)
    (ConfinedDevissage.hasDevissageWith_mono (fun _ hM => Or.inl hM) hGd)

end Stacks.AlgebraicGeometry.IrreducibleDevissage

end
