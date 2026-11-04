module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Coverings of a quasi-compact object and the extension by zero of the structure sheaf

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let `{U_i → U}_{i ∈ I}` be a
covering of `U`. Stacks 0G1W asserts that if `U` is quasi-compact then there is a *finite*
subset `I' ⊆ I` for which the sequence

`⊕_{i, i' ∈ I'} j_{U_i ×_U U_{i'}!} O_{U_i ×_U U_{i'}} ⟶ ⊕_{i ∈ I'} j_{U_i!} O_{U_i} ⟶
  j_{U!} O_U ⟶ 0`

is exact. **This file proves the right-hand half of that assertion**: exactness at `j_{U!} O_U`,
i.e. that `⊕_{i ∈ I'} j_{U_i!} O_{U_i} ⟶ j_{U!} O_U` is an epimorphism. Exactness in the middle
is not proved here; it needs the fibre products `U_i ×_U U_{i'}` to exist and the sheaf-axiom
exactness of Stacks 0G1L, neither of which the surjectivity half uses.

The proof is Stacks' own, and it is short because it never mentions local surjectivity. In a
preadditive category a morphism is an epimorphism exactly when it is left-cancellable, so the
assertion is about the morphisms *out of* `j_{U!} O_U`; and Stacks 0G1V — available here as
`Stacks.SheafOfModules.extensionByZeroUnitHomEquiv` — says those are the sections of the target
over `U`, with `Stacks.SheafOfModules.extensionByZeroUnitHomEquiv_map` saying that composing
with `j_{U_i!} O_{U_i} ⟶ j_{U!} O_U` restricts the section to `U_i`. So "the family is jointly
epimorphic" *is* the separatedness half of the sheaf axiom for the target, and it holds for
**every** covering family, finite or not. Quasi-compactness enters at one point only: it
produces a finite subfamily which is still a covering.

## Main results

* `Stacks.SheafOfModules.QuasiCompact.exists_finite_restrictIndex_sieve₀_mem`: **a covering
  family of a quasi-compact object has a finite subfamily which is still a covering.** This is
  the sieve-level content of Stacks 090H.
* `Stacks.SheafOfModules.isSeparated_presheaf` and
  `Stacks.SheafOfModules.eq_of_map_eq_of_sieve₀_mem`: the separatedness half of the sheaf axiom
  for a sheaf of modules, in the form "two sections which agree after restriction along the
  members of a covering family agree".
* `Stacks.SheafOfModules.extensionByZeroUnit_hom_ext_of_sieve₀_mem`: **the family
  `j_{U_i!} O_{U_i} ⟶ j_{U!} O_U` attached to a covering family of `U` is jointly epimorphic**,
  for any covering family.
* `Stacks.SheafOfModules.epi_sigmaDesc_extensionByZeroUnitMap`: the same assertion read off the
  direct sum.
* `Stacks.SheafOfModules.exists_finite_epi_sigmaDesc_extensionByZeroUnitMap`: **Stacks Project,
  Tag 0G1W, the surjectivity half.**

## Implementation notes

**Why there is no finiteness hypothesis on the covering family in the middle results.** The
Hom-side argument gives the epimorphism for an arbitrary covering family; the finite subfamily
is extracted afterwards. Stating the general form separately is what keeps quasi-compactness out
of the sheaf-theoretic step, and it is the form a consumer with an already-finite covering wants.

**Index universes.** `CategoryTheory.GrothendieckTopology.IsQuasiCompactObject` quantifies over
families indexed by `Type (max u₁ v₁)`, because every covering sieve of an object is generated
by a family indexed by that type; the covering families here therefore carry that index type,
which is forced by the definition and not a choice. The coproduct of the corresponding family of
sheaves of modules then exists: `SheafOfModules.{max u₁ v₁ w t} R` has colimits of every shape
in `Type (max u₁ v₁)`, since `PresheafOfModules` does and the module universe dominates
`max u₁ v₁`.

**Why the sheafification instances are re-derived.** The module universe is
`max u₁ v₁ w t`, which is the universe `Stacks.SheafOfModules.extensionByZeroUnit` already uses;
at that universe `HasSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat` are
not hypotheses but theorems, because the site is essentially small there. The two local
instances below are exactly that derivation. They duplicate two `private` declarations of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroUnit`, which a public declaration
of another module cannot refer to; if those are ever made public this file should cite them
instead.

**`PreZeroHypercover.Hom.sieve₀_le_sieve₀` is what makes the quasi-compactness extraction four
lines.** The refinement `𝒱 ⟶ 𝒰` supplied by quasi-compactness has finite index image, and
rewriting it as a refinement of the *restricted* family `{U_i → U}_{i ∈ I'}` — same `h₀`, same
`w₀`, with the index map factored through the range — turns the conclusion into a single
application of that Mathlib lemma. The analogous statement in
`StacksFrontier.CategoryTheory.Sites.QuasiCompact.ObjectsAndColimits` is `private`.

## References

* [Stacks Project, Tag 0G1W](https://stacks.math.columbia.edu/tag/0G1W)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 090H](https://stacks.math.columbia.edu/tag/090H)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u₁ v₁ w t

namespace Stacks.SheafOfModules

/-! ### A finite subfamily of a covering of a quasi-compact object -/

namespace QuasiCompact

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- A covering of a quasi-compact object has a finite subfamily which is still a covering. -/
theorem exists_finite_restrictIndex_sieve₀_mem {U : C}
    (hU : J.IsQuasiCompactObject U) (𝒰 : PreZeroHypercover.{max u₁ v₁} U)
    (h𝒰 : 𝒰.sieve₀ ∈ J U) :
    ∃ T : Set 𝒰.I₀, T.Finite ∧
      (𝒰.restrictIndex (Subtype.val : T → 𝒰.I₀)).sieve₀ ∈ J U := by
  obtain ⟨𝒱, φ, h𝒱, hfin⟩ := hU 𝒰 h𝒰
  refine ⟨Set.range φ.s₀, hfin, J.superset_covering ?_ h𝒱⟩
  exact PreZeroHypercover.Hom.sieve₀_le_sieve₀
    { s₀ := fun j => ⟨φ.s₀ j, j, rfl⟩, h₀ := φ.h₀, w₀ := φ.w₀ }

end QuasiCompact

/-! ### Separatedness of a sheaf of modules -/

section Separated

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- The presheaf of sets of sections of a sheaf of modules is separated for the topology. -/
theorem isSeparated_presheaf (N : SheafOfModules.{t} R) :
    Presieve.IsSeparated J (N.val.presheaf ⋙ forget AddCommGrpCat.{t}) :=
  ((isSheaf_iff_isSheaf_of_type ..).1
    ((sheafCompose J (forget AddCommGrpCat.{t})).obj ⟨_, N.isSheaf⟩).2).isSeparated

/-- **Two sections of a sheaf of modules which agree after restriction along the members of a
covering family agree.** -/
theorem eq_of_map_eq_of_sieve₀_mem (N : SheafOfModules.{t} R) {U : C}
    (𝒰 : PreZeroHypercover.{max u₁ v₁} U) (h𝒰 : 𝒰.sieve₀ ∈ J U)
    {s₁ s₂ : ToType (N.val.obj (op U))}
    (h : ∀ i, N.val.map (𝒰.f i).op s₁ = N.val.map (𝒰.f i).op s₂) : s₁ = s₂ := by
  refine (Presieve.isSeparatedFor_iff_generate.2
    (isSeparated_presheaf N _ h𝒰)).ext ?_
  rintro V f ⟨i⟩
  exact h i

end Separated

/-! ### Stacks 0G1W, the surjectivity half -/

section Epi

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

variable (R : Sheaf J RingCat.{w})

/-- **The family of extensions by zero attached to a covering family of `U` is jointly
epimorphic out of `j_{U!} O_U`.** By Stacks 0G1V a morphism `j_{U!} O_U ⟶ N` is a section of
`N` over `U` and its composite with `j_{U_i!} O_{U_i} ⟶ j_{U!} O_U` is the restriction of that
section to `U_i`, so this is exactly the separatedness half of the sheaf axiom for `N`. -/
theorem extensionByZeroUnit_hom_ext_of_sieve₀_mem {U : C}
    (𝒰 : PreZeroHypercover.{max u₁ v₁} U) (h𝒰 : 𝒰.sieve₀ ∈ J U)
    {N : SheafOfModules.{max u₁ v₁ w t} R}
    (p₁ p₂ : extensionByZeroUnit.{u₁, v₁, w, t} R U ⟶ N)
    (h : ∀ i, extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒰.f i) ≫ p₁ =
      extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒰.f i) ≫ p₂) :
    p₁ = p₂ :=
  (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R U N).injective
    (eq_of_map_eq_of_sieve₀_mem N 𝒰 h𝒰 fun i =>
      ((extensionByZeroUnitHomEquiv_map.{u₁, v₁, w, t} R (𝒰.f i) N p₁).symm.trans
        (congrArg (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R (𝒰.X i) N) (h i))).trans
        (extensionByZeroUnitHomEquiv_map.{u₁, v₁, w, t} R (𝒰.f i) N p₂))

/-- **The map from the direct sum of the extensions by zero attached to a covering family of `U`
to `j_{U!} O_U` is an epimorphism.** -/
theorem epi_sigmaDesc_extensionByZeroUnitMap {U : C}
    (𝒰 : PreZeroHypercover.{max u₁ v₁} U) (h𝒰 : 𝒰.sieve₀ ∈ J U) :
    Epi (Sigma.desc fun i => extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒰.f i)) :=
  ⟨fun {N} p₁ p₂ hp =>
    extensionByZeroUnit_hom_ext_of_sieve₀_mem R 𝒰 h𝒰 p₁ p₂ fun i => by
      rw [← Sigma.ι_desc (fun j => extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒰.f j)) i,
        Category.assoc, Category.assoc, hp]⟩

/-- **Stacks Project, Tag 0G1W**, the surjectivity half. If `U` is a quasi-compact object of a
ringed site and `{U_i → U}_{i ∈ I}` is a covering of `U`, then there is a finite subset
`I' ⊆ I` for which
`⊕_{i ∈ I'} j_{U_i!} O_{U_i} ⟶ j_{U!} O_U`
is already an epimorphism, i.e. the sequence of the source is exact at `j_{U!} O_U`. -/
@[stacks 0G1W "the surjectivity half: a finite subfamily of a covering of a quasi-compact
  object already gives an epimorphism onto the extension by zero"]
theorem exists_finite_epi_sigmaDesc_extensionByZeroUnitMap {U : C}
    (hU : J.IsQuasiCompactObject U) (𝒰 : PreZeroHypercover.{max u₁ v₁} U)
    (h𝒰 : 𝒰.sieve₀ ∈ J U) :
    ∃ T : Set 𝒰.I₀, T.Finite ∧
      Epi (Sigma.desc fun i : T => extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒰.f i.1)) := by
  obtain ⟨T, hTfin, hTcov⟩ :=
    QuasiCompact.exists_finite_restrictIndex_sieve₀_mem hU 𝒰 h𝒰
  exact ⟨T, hTfin,
    epi_sigmaDesc_extensionByZeroUnitMap.{u₁, v₁, w, t} R
      (𝒰.restrictIndex (Subtype.val : T → 𝒰.I₀)) hTcov⟩

end Epi

end Stacks.SheafOfModules

end
