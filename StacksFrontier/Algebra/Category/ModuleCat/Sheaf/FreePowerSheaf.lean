module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# A coproduct of free sheaves of modules is free on the sigma type

Let `(C, J)` be a site and `O` a sheaf of rings on it. Mathlib's `SheafOfModules.free I` is the
coproduct of copies of the structure sheaf indexed by a type `I`, and `SheafOfModules.freeSumIso`
identifies a *binary* coproduct of free sheaves of modules with the free sheaf of modules on the
sum type. This file records the arbitrary-index form of that statement,

`∐ᵢ free (Kᵢ) ≅ free (Σ i, Kᵢ)`,

together with the fact that the comparison is `SheafOfModules.freeMap` of the inclusion
`Kᵢ → Σ i, Kᵢ` on each summand, which determines it since the summands jointly generate a
coproduct.

**Why this is wanted.** Stacks Tag 01CL asserts that the total tensor, exterior and symmetric
algebras `T(F)`, `⋀(F)`, `Sym(F)` of a locally free sheaf of modules are again locally free, and
likewise for quasi-coherence. Its proof is the observation that an infinite direct sum of locally
free sheaves need *not* be locally free — the opens on which the summands trivialise may
intersect in no neighbourhood of a point — together with the fact, established inside the proof of
Tag 01CK, that **one** open neighbourhood trivialises `Tⁿ(F)`, `⋀ⁿ(F)` and `Symⁿ(F)`
simultaneously for every `n`. Once that uniform neighbourhood is in hand, all that remains of Tag
01CL is to recognise a coproduct of free sheaves of modules as a free sheaf of modules, which is
what is proved here and which is the source's closing "The lemma follows".

## Main definitions

* `SheafOfModules.freeSigmaIso` : the identification `∐ᵢ free (Kᵢ) ≅ free (Σ i, Kᵢ)`. It is
  `CategoryTheory.Limits.sigmaSigmaIso` for the constant family `fun _ _ => unit O`, because
  `SheafOfModules.free I` is *by definition* `∐ (fun _ : I => unit O)`; the content of the
  declaration is the ascribed type, which folds those nested coproducts back into `free`.

## Main results

* `SheafOfModules.ι_freeSigmaIso_hom` : the comparison restricted to the `i`-th summand is
  `SheafOfModules.freeMap` of `fun j => ⟨i, j⟩`. This pins the comparison down.
* `SheafOfModules.ιFree_freeSigmaIso_hom` : the same identity read on the generating sections —
  the generator of the `i`-th summand indexed by `j` goes to the generator indexed by `⟨i, j⟩`.
* `SheafOfModules.nonempty_iso_free_coprod` : the consumer-facing form. If every `P i` is
  isomorphic to some free sheaf of modules, then so is `∐ P`. This is the shape a graded algebra
  sheaf is fed to it in: `P` is the family of homogeneous pieces, and the hypothesis is the
  conclusion of Tag 01CK on a neighbourhood that works for all of them at once.

## Implementation notes

**No Stacks tag is claimed, deliberately.** This file carries neither `@[stacks 01CL]` nor
`@[stacks 01CK]`. The mathematical content of Tag 01CL is the *uniformity* of the trivialising
neighbourhood, which is a statement about the proof of Tag 01CK; the coproduct bookkeeping below
is the formal step that uniformity feeds, and tagging it would assert a result whose substance
lies elsewhere. Both tags now have a route through this library and
`nonempty_iso_free_coprod` is on it: clause (6) of Tag 01CK is
`Stacks.SheafOfModules.isLocallyFree_tensorPower`, `isLocallyFree_exteriorPower` and
`isLocallyFree_symmetricPower` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreePowers`, which also establishes the
uniformity, and clause (2) of Tag 01CL is
`Stacks.SheafOfModules.isLocallyFree_tensorAlgebraSheaf_of_isLocallyFree` and its two companions
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFreeAlgebras`, which consume this file
through `Stacks.SheafOfModules.isLocallyFree_coprod_of_small`.

**The index universe is forced, not chosen.** `SheafOfModules.free` takes a type in the *same*
universe `u` as the sections of the sheaf of rings, so for `free (Σ i, K i)` to be well-typed the
sigma type must land in `Type u`; with `K i : Type u` that means the index type must satisfy
`max v u = u`. Taking `ι : Type u` is therefore the general case, and nothing is narrowed by
stating the results there. An index type in a strictly lower universe — such as the `ℕ` grading of
a graded algebra sheaf when `u > 0` — is reindexed through `Equiv.ulift` and
`CategoryTheory.Limits.Sigma.whiskerEquiv`, which is the same move `nonempty_iso_free_coprod`
already makes for the family of isomorphisms.

**Why `sigmaSigmaIso` suffices, and why no proof below uses `rw`.** `free I` unfolds to
`∐ (fun _ : I => unit O)`, so `∐ᵢ free (Kᵢ)` and the sigma-indexed `∐_{p : Σ i, Kᵢ} unit O` are
literally the two sides of `sigmaSigmaIso` at the constant family; the isomorphism is not
reconstructed here, only its folded type and its behaviour on summands. That folding is also why
every proof below is a term, built from `Sigma.ι_desc`, `Cofan.IsColimit.hom_ext` and
`ιFree_freeMap`. A goal mixing the folded spelling `free (K i)` with the unfolded
`∐ (fun _ : K i => unit O)` is definitionally fine but *not* type-correct at `implicit`
transparency, so `rw` refuses it — concretely, `rw [← Category.assoc]` on the statement of
`ι_freeSigmaIso_hom` fails with a pattern-matching error whose real cause is that
`Limits.Sigma.hom_ext` has produced the unfolded spelling. Term-mode `:=`, `Eq.trans` and
`congrArg` at an ascribed type are defeq-tolerant and go through unchanged.

## References

* [Stacks Project, Tag 01CL](https://stacks.math.columbia.edu/tag/01CL)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

universe u v₁ u₁

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {O : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

section Sigma

variable {ι : Type u} (K : ι → Type u)

/-- **A coproduct of free sheaves of modules is the free sheaf of modules on the sigma type.**
This is the arbitrary-index form of `SheafOfModules.freeSumIso`.

Since `SheafOfModules.free I` is by definition the coproduct of copies of `unit O` indexed by `I`,
the two sides here are the two sides of `CategoryTheory.Limits.sigmaSigmaIso` for the constant
family; the content of the declaration is the ascribed type, which folds those nested coproducts
back into `free`. -/
noncomputable def freeSigmaIso [HasCoproduct fun i => free (R := O) (K i)] :
    (∐ fun i => free (R := O) (K i)) ≅ free (R := O) (Σ i, K i) :=
  sigmaSigmaIso K fun _ (_ : K _) => unit O

/-- The comparison `SheafOfModules.freeSigmaIso` restricted to the `i`-th summand is
`SheafOfModules.freeMap` of the inclusion `K i → Σ i, K i`. The summands jointly generate the
coproduct, so this determines the comparison. -/
@[reassoc (attr := simp)]
lemma ι_freeSigmaIso_hom [HasCoproduct fun i => free (R := O) (K i)] (i : ι) :
    Sigma.ι (fun i => free (R := O) (K i)) i ≫ (freeSigmaIso (O := O) K).hom =
      freeMap fun j => (⟨i, j⟩ : Σ i, K i) :=
  (Sigma.ι_desc _ i).trans
    (Cofan.IsColimit.hom_ext (isColimitFreeCofan (R := O) (K i)) _ _ fun j =>
      (Sigma.ι_desc _ j).trans (ιFree_freeMap (R := O) (fun j => (⟨i, j⟩ : Σ i, K i)) j).symm)

/-- `SheafOfModules.freeSigmaIso` read on the generating sections: the generator of the `i`-th
summand indexed by `j : K i` goes to the generator indexed by `⟨i, j⟩`. -/
lemma ιFree_freeSigmaIso_hom [HasCoproduct fun i => free (R := O) (K i)] (i : ι) (j : K i) :
    ιFree (R := O) j ≫ Sigma.ι (fun i => free (R := O) (K i)) i ≫
        (freeSigmaIso (O := O) K).hom =
      ιFree (R := O) (⟨i, j⟩ : Σ i, K i) :=
  (congrArg
      (fun f : free (R := O) (K i) ⟶ free (R := O) (Σ i, K i) => ιFree (R := O) j ≫ f)
      (ι_freeSigmaIso_hom (O := O) K i)).trans
    (ιFree_freeMap (R := O) (fun j => (⟨i, j⟩ : Σ i, K i)) j)

end Sigma

/-- **A coproduct of sheaves of modules each of which is free is free.** This is the form Stacks
Tag 01CL consumes: `P` is the family of homogeneous pieces of a graded algebra sheaf, and the
hypothesis is the conclusion of Tag 01CK on a single open neighbourhood trivialising every piece
at once. -/
theorem nonempty_iso_free_coprod {ι : Type u} {P : ι → SheafOfModules.{u} O} (K : ι → Type u)
    [HasCoproduct P] [HasCoproduct fun i => free (R := O) (K i)]
    (he : ∀ i, Nonempty (P i ≅ free (R := O) (K i))) :
    Nonempty ((∐ P) ≅ free (R := O) (Σ i, K i)) :=
  ⟨(Sigma.whiskerEquiv (Equiv.refl ι) fun i => (he i).some.symm).trans (freeSigmaIso K)⟩

end SheafOfModules

end
