module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroRefinePresentation
public import Mathlib.CategoryTheory.Abelian.Refinements
public import StacksCore.Tactic.StacksAttribute

/-!
# Extensions of modules with finite presentations by extensions by zero

Let `C` be a site with a distinguished collection `B` of objects satisfying the three conditions
of Stacks 0937 and let `R` be a sheaf of rings on `C`. **Stacks 093G** says that the sheaves of
`R`-modules admitting a finite presentation by extensions by zero (Stacks 093D, the predicate
`Stacks.SheafOfModules.HasFiniteExtensionByZeroPresentation`) are stable under extensions: if

`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0`

is a short exact sequence of sheaves of modules and both `F₁` and `F₃` have such a presentation,
then so does `F₂`.

## Main definitions

* `Stacks.SheafOfModules.sumGeneratorsInl`, `Stacks.SheafOfModules.sumGeneratorsInr`,
  `Stacks.SheafOfModules.sumGeneratorsDesc`: the two inclusions into, and the universal
  morphism out of, a direct sum of extensions by zero indexed by a sum type. Together with
  `Stacks.SheafOfModules.sumGeneratorsFst` and `Stacks.SheafOfModules.sumGeneratorsSnd` these
  present `⊕_{ι ⊕ κ} j_{U!} O_U` as the biproduct of its two blocks.

## Main results

* `Stacks.SheafOfModules.epi_kernelMap_of_epi_of_exact`: **the snake lemma's surjectivity**, in
  the form the proof of Stacks 093G needs. In an abelian category, for a commutative square
  `φ ≫ g = ρ ≫ c` over an exact `F₁ ⟶ F₂ ⟶ F₃` with `F₁ ⟶ F₂` a monomorphism, the induced
  morphism `Ker φ ⟶ Ker c` is an epimorphism as soon as `ρ` is one and the first column is
  covered, i.e. there is `ν` with `ν ≫ φ = a ≫ f`, `ν ≫ ρ = 0` and `a` an epimorphism.
* `Stacks.SheafOfModules.epi_of_epi_kernelMap_comp`: the complementary statement. A morphism
  into `Ker φ` is an epimorphism once its restriction to one block generates `Ker c` and its
  restriction to the other generates the relations of `a`.
* `Stacks.SheafOfModules.exists_hypercover_lift_extensionByZeroUnit`: a covering by
  distinguished objects along which a morphism out of `j_{W!} O_W` lifts through a given
  epimorphism.
* `Stacks.SheafOfModules.hasFiniteExtensionByZeroPresentation_of_lifted_generators`: the
  assembly step, which produces the presentation of the extension once the generators of the
  quotient's presentation have been lifted into the middle term.
* `Stacks.SheafOfModules.hasFiniteExtensionByZeroPresentation_of_shortExact`:
  **Stacks Project, Tag 093G.**

## Implementation notes

**The statement is the Stacks statement, at the module universe where `Mod(O)` is abelian**, as
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteExtensionByZeroPresentation` (Stacks
093E), whose conventions this file follows: the module universe is `max u₁ v₁ w t`, the one at
which `Stacks.SheafOfModules.extensionByZeroUnit` is constructed. There the site is essentially
small, so `HasSheafify J AddCommGrpCat` and `J.WEqualsLocallyBijective AddCommGrpCat` are
theorems rather than hypotheses and `SheafOfModules` is abelian, which is the standing
convention Stacks works under. The short exact sequence is a `CategoryTheory.ShortComplex`
together with `ShortComplex.ShortExact`; no `HasCokernel` hypothesis and no `ULift` wrapper is
needed.

**Comparison with the statement at an arbitrary module universe.** That statement concerns
`E : ShortComplex (SheafOfModules.{v} R)` at a free module universe `v`, with the Stacks-093D
predicate concluding about `(moduleULift _).obj E.X₂`.

The free `v` is **not** a universe generalization of this statement, and the pin here is not a
choice. The presentation objects `extensionByZeroUnit.{u₁, v₁, w, t} R U` live in
`SheafOfModules.{max u₁ v₁ w t} R`, so the predicate can only speak about modules whose universe
contains `max u₁ v₁ w`, and `max u₁ v₁ w t` with `t` free is exactly "any such universe". The
tagged statement is a *different* statement: a short exact sequence in `SheafOfModules.{v} R` for an
arbitrary `v`, with the conclusion about the universe lift of its middle term. Modulo the
predicate and generator spellings, which are definitionally equal, the statement reduces to exactly
one transfer statement: that `moduleULift` carries a short exact sequence of
`SheafOfModules.{v} R` to a short exact one.

Of that transfer's three components, **the monomorphism half is now a theorem** at an arbitrary
module universe (`Stacks.SheafOfModules.mono_moduleULift_map`), as is the epimorphism half
whenever `E.g` is presented as a cokernel projection
(`Stacks.SheafOfModules.epi_moduleULift_map_cokernel_π`). What is still missing is the
epimorphism half for an *abstract* epimorphism, and exactness. Both fail for the same reason:
`Abelian (SheafOfModules.{v} R)` and `Sheaf.isLocallySurjective_iff_epi'` both require
`HasSheafify J AddCommGrpCat.{v}`, whose only instances
(`CategoryTheory.hasSheafifyEssentiallySmallSite`,
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall`) need the site
to be essentially small at `v`, i.e. `UnivLE.{u₁, v}` and `UnivLE.{v₁, v}`. At a free `v` the
category is therefore not known to be balanced, so `ShortComplex.ShortExact` does not even yield
that `E.g` is a cokernel of `E.f` (`ShortComplex.Exact.gIsCokernel` is stated for a balanced
category), and an abstract epimorphism there carries no local information, since testing one
would need quotients — which are exactly what sheafification provides. The note at
`StacksFrontier/Algebra/Homology/StrictlyPerfectRestriction.lean:118` records the same gap for the
space-level lift.

**Why the snake lemma is stated with explicit data rather than through
`CategoryTheory.ShortComplex.SnakeInput`.** Stacks' step is: the map of short exact sequences
```
0 ⟶ ⊕A_{U_i} ⟶ ⊕A_{U_i} ⊕ ⊕A_{W_i} ⟶ ⊕A_{W_i} ⟶ 0
        |                |                 |
        a                φ                 c
        v                v                 v
0 ⟶    F₁     ⟶         F₂       ⟶       F₃     ⟶ 0
```
has `Coker a = 0`, so the snake sequence gives `Ker φ ↠ Ker c`. Feeding this to Mathlib's
`SnakeInput` means producing the kernel row *and* the cokernel row with their universal
properties, whereas the two-term refinement argument of
`Stacks.SheafOfModules.epi_kernelMap_of_epi_of_exact` needs only `Mono f`, `Epi ρ` and `Epi a`,
and in particular neither the splitness of the top row nor `Epi g`. Mathlib's closest
off-the-shelf form, `CategoryTheory.Abelian.epi_kernel_map_of_isPushout`, asks for the square to
be a pushout; it is one here, but establishing that is strictly more work than the epimorphism it
yields.

The lemma generalizes `Stacks.SheafOfModules.epi_kernelMap_of_epi`
(`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentWeakSerre`), which is the case
`E.X₂ = E.X₃`, `E.g = 𝟙`, `E.X₁ = 0`: a dedup is owed there, and the name here differs because
that one already occupies `epi_kernelMap_of_epi` in this namespace.

**Why the splitting of the generators is passed as `hker`.** The middle object of the top row is
`⊕_{ι ⊕ κ} j_{U!} O_U`, so the statement `y ≫ ρ = 0 → y` factors through `ν` is the kernel
property of the first block. Taking it as a hypothesis of the two abelian lemmas keeps every
manipulation of a sum-indexed direct sum on the sheaf side, in the single spelling
`∐ fun y ↦ extensionByZeroUnit R (Sum.elim U Z y)`; `Stacks.SheafOfModules.sumGeneratorsSplit`
discharges it once.

**`Stacks.SheafOfModules.exists_hypercover_lift_extensionByZeroUnit` is the lifting step without
the finiteness cut.** `Stacks.SheafOfModules.exists_finite_lift_extensionByZeroUnit` returns a
*finite* family, by Stacks 0G1W, but only records that the family is jointly epimorphic, and
Stacks 093F needs the covering sieve. The first lifting step of Stacks 093G hands its covering
straight to Stacks 093F, which performs the finiteness cut itself, so what is wanted here is the
uncut form; it needs no quasi-compactness.

**`Stacks.SheafOfModules.epi_sigmaDesc_sigmaIota'`** is
`Stacks.SheafOfModules.epi_sigmaDesc_sigmaIota` with the outer index type `Fin n` relaxed to any
type in `Type (max u₁ v₁)`, which is where Stacks 0G1W and 093F produce their index sets. The
proof is the same; the two should be merged once the original version is generalized.

The two `local instance`s below are the derivation that `ExtensionByZeroUnit.lean`,
`ExtensionByZeroQuasiCompact.lean`, `ExtensionByZeroUnitULift.lean`, `ExtensionByZeroCech.lean`,
`FiniteExtensionByZeroPresentation.lean` and `ExtensionByZeroRefinePresentation.lean` also carry
privately; a public declaration of another module cannot refer to a `private` one. If they are
ever made public, all seven copies should cite them.

## References

* [Stacks Project, Tag 093G](https://stacks.math.columbia.edu/tag/093G)
* [Stacks Project, Tag 093D](https://stacks.math.columbia.edu/tag/093D)
* [Stacks Project, Tag 093E](https://stacks.math.columbia.edu/tag/093E)
* [Stacks Project, Tag 093F](https://stacks.math.columbia.edu/tag/093F)
* [Stacks Project, Tag 0937](https://stacks.math.columbia.edu/tag/0937)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u₁ v₁ w t

namespace Stacks.SheafOfModules

/-! ### The snake lemma, in the form Stacks 093G uses -/

section AbstractSnake

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- **The surjectivity statement of the snake lemma.** Let `E` be an exact sequence
`F₁ ⟶ F₂ ⟶ F₃` with `F₁ ⟶ F₂` a monomorphism and let
```
Q --φ--> F₂
|        |
ρ        g
v        v
P --c--> F₃
```
commute with `ρ` an epimorphism. Suppose the first column is covered: there are `ν : P₁ ⟶ Q` and
an epimorphism `a : P₁ ⟶ F₁` with `ν ≫ φ = a ≫ f` and `ν ≫ ρ = 0`. Then the induced morphism
`Ker φ ⟶ Ker c` is an epimorphism.

This is the snake lemma for the map of short exact sequences whose rows are
`P₁ ⟶ Q ⟶ P` and `F₁ ⟶ F₂ ⟶ F₃` and whose columns are `a`, `φ`, `c`, in the case `Coker a = 0`;
the hypotheses here are what that argument actually consumes, and in particular the top row need
not be a complex. -/
theorem epi_kernelMap_of_epi_of_exact {E : ShortComplex 𝒜} (hE : E.Exact) [Mono E.f]
    {P₁ P Q : 𝒜} {φ : Q ⟶ E.X₂} {ρ : Q ⟶ P} {c : P ⟶ E.X₃}
    (w : φ ≫ E.g = ρ ≫ c) [Epi ρ] {ν : P₁ ⟶ Q} {a : P₁ ⟶ E.X₁} [Epi a]
    (hν : ν ≫ φ = a ≫ E.f) (hνρ : ν ≫ ρ = 0) :
    Epi (kernel.map φ c ρ E.g w) := by
  rw [epi_iff_surjective_up_to_refinements]
  intro A z
  obtain ⟨A₁, π₁, _, u, hu⟩ := surjective_up_to_refinements_of_epi ρ (z ≫ kernel.ι c)
  have hug : (u ≫ φ) ≫ E.g = 0 := by
    rw [Category.assoc, w, ← Category.assoc, ← hu, Category.assoc, Category.assoc,
      kernel.condition, comp_zero, comp_zero]
  obtain ⟨y, hy⟩ := hE.lift' (u ≫ φ) hug
  obtain ⟨A₂, π₂, _, s, hs⟩ := surjective_up_to_refinements_of_epi a y
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, kernel.lift φ (π₂ ≫ u - s ≫ ν) ?_, ?_⟩
  · rw [Preadditive.sub_comp, Category.assoc, ← hy, ← Category.assoc, hs, Category.assoc,
      ← hν, ← Category.assoc, sub_self]
  · rw [← cancel_mono (kernel.ι c), Category.assoc, Category.assoc, hu, Category.assoc,
      kernel.lift_ι, kernel.lift_ι_assoc, Preadditive.sub_comp, Category.assoc,
      Category.assoc, hνρ, comp_zero, sub_zero]

/-- **The relations of the kernel of the middle column are generated.** In the situation of
`Stacks.SheafOfModules.epi_kernelMap_of_epi_of_exact`, suppose moreover that `a` is the cokernel of
`b : Rel₁ ⟶ P₁` (as an exactness statement), and let `Λ : Rel ⟶ Ker φ` be given together with

* `κ₁ : Rel₁ ⟶ Rel` whose composite with `Λ` is `b` read into `Ker φ` through `ν`, and
* `κ₃ : Rel₃ ⟶ Rel` whose composite with `Λ ≫ (Ker φ ⟶ Ker c)` is an epimorphism.

Then `Λ` is an epimorphism.

Read in the situation of Stacks 093G: `Λ` is the morphism
`⊕A_{V_j} ⊕ ⊕A_{T_j} ⟶ K₂` of the last line of the proof, `κ₁` and `κ₃` are the two block
inclusions, the hypothesis on `κ₃` says that the relations of `F₃` generate `K₃`, and the
hypothesis on `κ₁` says that the relations of `F₁` generate the part of `K₂` lying over
`0 ∈ K₃`. -/
theorem epi_of_epi_kernelMap_comp {E : ShortComplex 𝒜} [Mono E.f]
    {P₁ P Q Rel Rel₁ Rel₃ : 𝒜} {φ : Q ⟶ E.X₂} {ρ : Q ⟶ P} {c : P ⟶ E.X₃}
    (w : φ ≫ E.g = ρ ≫ c)
    {ν : P₁ ⟶ Q} (hker : ∀ ⦃X : 𝒜⦄ (y : X ⟶ Q), y ≫ ρ = 0 → ∃ x : X ⟶ P₁, x ≫ ν = y)
    {a : P₁ ⟶ E.X₁} (hν : ν ≫ φ = a ≫ E.f)
    {b : Rel₁ ⟶ P₁} {hba : b ≫ a = 0} (hex : (ShortComplex.mk b a hba).Exact)
    {Λ : Rel ⟶ kernel φ} {κ₁ : Rel₁ ⟶ Rel} (hκ₁ : κ₁ ≫ Λ ≫ kernel.ι φ = b ≫ ν)
    {κ₃ : Rel₃ ⟶ Rel} (hκ₃ : Epi (κ₃ ≫ Λ ≫ kernel.map φ c ρ E.g w)) :
    Epi Λ := by
  have _ := hκ₃
  rw [epi_iff_surjective_up_to_refinements]
  intro A z
  obtain ⟨A₁, π₁, _, r, hr⟩ := surjective_up_to_refinements_of_epi
    (κ₃ ≫ Λ ≫ kernel.map φ c ρ E.g w) (z ≫ kernel.map φ c ρ E.g w)
  have hmap : (π₁ ≫ z - r ≫ κ₃ ≫ Λ) ≫ kernel.map φ c ρ E.g w = 0 := by
    rw [Preadditive.sub_comp, Category.assoc, hr, Category.assoc, Category.assoc, sub_self]
  have hιρ : kernel.ι φ ≫ ρ = kernel.map φ c ρ E.g w ≫ kernel.ι c := by simp
  obtain ⟨x, hx⟩ := hker ((π₁ ≫ z - r ≫ κ₃ ≫ Λ) ≫ kernel.ι φ) (by
    rw [Category.assoc, hιρ, ← Category.assoc, hmap, zero_comp])
  have hxa : x ≫ a = 0 := by
    rw [← cancel_mono E.f, zero_comp, Category.assoc, ← hν, ← Category.assoc, hx,
      Category.assoc, kernel.condition, comp_zero]
  obtain ⟨A₂, π₂, _, k, hk⟩ := hex.exact_up_to_refinements x hxa
  refine ⟨A₂, π₂ ≫ π₁, inferInstance, k ≫ κ₁ + (π₂ ≫ r) ≫ κ₃, ?_⟩
  have key : π₂ ≫ (π₁ ≫ z - r ≫ κ₃ ≫ Λ) = k ≫ κ₁ ≫ Λ := by
    rw [← cancel_mono (kernel.ι φ), Category.assoc, ← hx, ← Category.assoc, hk,
      Category.assoc, ← hκ₁, Category.assoc, Category.assoc]
  rw [Preadditive.add_comp, Category.assoc, Category.assoc, Category.assoc, Category.assoc,
    ← key, Preadditive.comp_sub]
  abel

end AbstractSnake

variable {C : Type u₁} [Category.{v₁} C]

attribute [local instance] siteHasSheafify siteWEqualsLocallyBijective

/-! ### Direct sums of extensions by zero indexed by a sum type -/

section SumGenerators

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w}) {ι : Type*} {κ : Type*}
  (U : ι → C) (Z : κ → C)
  [HasCoproduct fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)]
  [HasCoproduct fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j)]
  [HasCoproduct fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)]

/-- The inclusion of the first block `⊕_i j_{U_i!} O_{U_i}` into
`⊕_{y ∈ ι ⊕ κ} j_{(U ⊕ Z) y!} O`. -/
noncomputable def sumGeneratorsInl :
    (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) ⟶
      ∐ fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y) :=
  Sigma.desc fun i ↦
    Sigma.ι (fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) (Sum.inl i)

/-- The inclusion of the second block `⊕_j j_{Z_j!} O_{Z_j}`. -/
noncomputable def sumGeneratorsInr :
    (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j)) ⟶
      ∐ fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y) :=
  Sigma.desc fun j ↦
    Sigma.ι (fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) (Sum.inr j)

/-- The morphism out of `⊕_{y ∈ ι ⊕ κ} j_{(U ⊕ Z) y!} O` determined by a morphism out of each
block. -/
noncomputable def sumGeneratorsDesc {N : SheafOfModules.{max u₁ v₁ w t} R}
    (p : (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) ⟶ N)
    (q : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j)) ⟶ N) :
    (∐ fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) ⟶ N :=
  Sigma.desc (Sum.rec
    (fun i ↦ Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i')) i ≫ p)
    (fun j ↦ Sigma.ι (fun j' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j')) j ≫ q))

/-- The projection onto the first block. -/
noncomputable def sumGeneratorsFst :
    (∐ fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i) :=
  sumGeneratorsDesc.{u₁, v₁, w, t} R U Z (𝟙 _) 0

/-- The projection onto the second block. -/
noncomputable def sumGeneratorsSnd :
    (∐ fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) ⟶
      ∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j) :=
  sumGeneratorsDesc.{u₁, v₁, w, t} R U Z 0 (𝟙 _)

omit [HasCoproduct fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j)] in
/-- The `i`-th coprojection followed by `sumGeneratorsInl` is the coprojection at `Sum.inl i`. -/
@[reassoc]
lemma ι_comp_sumGeneratorsInl (i : ι) :
    Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i')) i ≫
        sumGeneratorsInl.{u₁, v₁, w, t} R U Z =
      Sigma.ι (fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) (Sum.inl i) :=
  Sigma.ι_desc _ _

omit [HasCoproduct fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)] in
/-- The `j`-th coprojection followed by `sumGeneratorsInr` is the coprojection at `Sum.inr j`. -/
@[reassoc]
lemma ι_comp_sumGeneratorsInr (j : κ) :
    Sigma.ι (fun j' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j')) j ≫
        sumGeneratorsInr.{u₁, v₁, w, t} R U Z =
      Sigma.ι (fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) (Sum.inr j) :=
  Sigma.ι_desc _ _

/-- `sumGeneratorsDesc p q` restricted to the summand at `Sum.inl i` is the restriction of `p`
to the `i`-th summand. -/
lemma ι_inl_comp_sumGeneratorsDesc {N : SheafOfModules.{max u₁ v₁ w t} R}
    (p : (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) ⟶ N)
    (q : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j)) ⟶ N) (i : ι) :
    Sigma.ι (fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) (Sum.inl i) ≫
        sumGeneratorsDesc.{u₁, v₁, w, t} R U Z p q =
      Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i')) i ≫ p :=
  Sigma.ι_desc _ _

/-- `sumGeneratorsDesc p q` restricted to the summand at `Sum.inr j` is the restriction of `q`
to the `j`-th summand. -/
lemma ι_inr_comp_sumGeneratorsDesc {N : SheafOfModules.{max u₁ v₁ w t} R}
    (p : (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) ⟶ N)
    (q : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j)) ⟶ N) (j : κ) :
    Sigma.ι (fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) (Sum.inr j) ≫
        sumGeneratorsDesc.{u₁, v₁, w, t} R U Z p q =
      Sigma.ι (fun j' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j')) j ≫ q :=
  Sigma.ι_desc _ _

/-- `sumGeneratorsDesc p q` restricted to the first block is `p`. -/
@[reassoc]
lemma sumGeneratorsInl_comp_desc {N : SheafOfModules.{max u₁ v₁ w t} R}
    (p : (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) ⟶ N)
    (q : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j)) ⟶ N) :
    sumGeneratorsInl.{u₁, v₁, w, t} R U Z ≫ sumGeneratorsDesc.{u₁, v₁, w, t} R U Z p q = p :=
  Sigma.hom_ext _ _ fun i ↦
    (ι_comp_sumGeneratorsInl_assoc.{u₁, v₁, w, t} R U Z i
      (sumGeneratorsDesc.{u₁, v₁, w, t} R U Z p q)).trans
      (ι_inl_comp_sumGeneratorsDesc.{u₁, v₁, w, t} R U Z p q i)

/-- `sumGeneratorsDesc p q` restricted to the second block is `q`. -/
@[reassoc]
lemma sumGeneratorsInr_comp_desc {N : SheafOfModules.{max u₁ v₁ w t} R}
    (p : (∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i)) ⟶ N)
    (q : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j)) ⟶ N) :
    sumGeneratorsInr.{u₁, v₁, w, t} R U Z ≫ sumGeneratorsDesc.{u₁, v₁, w, t} R U Z p q = q :=
  Sigma.hom_ext _ _ fun j ↦
    (ι_comp_sumGeneratorsInr_assoc.{u₁, v₁, w, t} R U Z j
      (sumGeneratorsDesc.{u₁, v₁, w, t} R U Z p q)).trans
      (ι_inr_comp_sumGeneratorsDesc.{u₁, v₁, w, t} R U Z p q j)

/-- Two morphisms out of `⊕_{y ∈ ι ⊕ κ} j_{(U ⊕ Z) y!} O` agreeing on both blocks agree. -/
lemma sumGenerators_hom_ext {N : SheafOfModules.{max u₁ v₁ w t} R}
    (p₁ p₂ : (∐ fun y ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z y)) ⟶ N)
    (hl : sumGeneratorsInl.{u₁, v₁, w, t} R U Z ≫ p₁ =
      sumGeneratorsInl.{u₁, v₁, w, t} R U Z ≫ p₂)
    (hr : sumGeneratorsInr.{u₁, v₁, w, t} R U Z ≫ p₁ =
      sumGeneratorsInr.{u₁, v₁, w, t} R U Z ≫ p₂) :
    p₁ = p₂ :=
  Sigma.hom_ext _ _ fun y ↦ by
    cases y with
    | inl i =>
      exact (ι_comp_sumGeneratorsInl_assoc.{u₁, v₁, w, t} R U Z i p₁).symm.trans
        ((Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i')) i ≫= hl).trans
          (ι_comp_sumGeneratorsInl_assoc.{u₁, v₁, w, t} R U Z i p₂))
    | inr j =>
      exact (ι_comp_sumGeneratorsInr_assoc.{u₁, v₁, w, t} R U Z j p₁).symm.trans
        ((Sigma.ι (fun j' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Z j')) j ≫= hr).trans
          (ι_comp_sumGeneratorsInr_assoc.{u₁, v₁, w, t} R U Z j p₂))

/-- The inclusion of the first block followed by the projection onto it is the identity. -/
@[reassoc]
lemma sumGeneratorsInl_comp_fst :
    sumGeneratorsInl.{u₁, v₁, w, t} R U Z ≫ sumGeneratorsFst.{u₁, v₁, w, t} R U Z = 𝟙 _ :=
  sumGeneratorsInl_comp_desc.{u₁, v₁, w, t} R U Z _ _

/-- The inclusion of the first block followed by the projection onto the second is zero. -/
@[reassoc]
lemma sumGeneratorsInl_comp_snd :
    sumGeneratorsInl.{u₁, v₁, w, t} R U Z ≫ sumGeneratorsSnd.{u₁, v₁, w, t} R U Z = 0 :=
  sumGeneratorsInl_comp_desc.{u₁, v₁, w, t} R U Z _ _

/-- The inclusion of the second block followed by the projection onto the first is zero. -/
@[reassoc]
lemma sumGeneratorsInr_comp_fst :
    sumGeneratorsInr.{u₁, v₁, w, t} R U Z ≫ sumGeneratorsFst.{u₁, v₁, w, t} R U Z = 0 :=
  sumGeneratorsInr_comp_desc.{u₁, v₁, w, t} R U Z _ _

/-- The inclusion of the second block followed by the projection onto it is the identity. -/
@[reassoc]
lemma sumGeneratorsInr_comp_snd :
    sumGeneratorsInr.{u₁, v₁, w, t} R U Z ≫ sumGeneratorsSnd.{u₁, v₁, w, t} R U Z = 𝟙 _ :=
  sumGeneratorsInr_comp_desc.{u₁, v₁, w, t} R U Z _ _

/-- `⊕_{y ∈ ι ⊕ κ} j_{(U ⊕ Z) y!} O` is the biproduct of its two blocks. -/
lemma sumGeneratorsSplit :
    sumGeneratorsFst.{u₁, v₁, w, t} R U Z ≫ sumGeneratorsInl.{u₁, v₁, w, t} R U Z +
        sumGeneratorsSnd.{u₁, v₁, w, t} R U Z ≫ sumGeneratorsInr.{u₁, v₁, w, t} R U Z =
      𝟙 _ := by
  refine sumGenerators_hom_ext.{u₁, v₁, w, t} R U Z _ _ ?_ ?_
  · rw [Preadditive.comp_add, Category.comp_id, sumGeneratorsInl_comp_fst_assoc,
      sumGeneratorsInl_comp_snd_assoc, zero_comp, add_zero]
  · rw [Preadditive.comp_add, Category.comp_id, sumGeneratorsInr_comp_fst_assoc,
      sumGeneratorsInr_comp_snd_assoc, zero_comp, zero_add]

/-- A morphism into `⊕_{y ∈ ι ⊕ κ} j_{(U ⊕ Z) y!} O` killed by the projection onto the second
block factors through the inclusion of the first. -/
lemma exists_comp_sumGeneratorsInl {X : SheafOfModules.{max u₁ v₁ w t} R}
    (y : X ⟶ ∐ fun z ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Sum.elim U Z z))
    (hy : y ≫ sumGeneratorsSnd.{u₁, v₁, w, t} R U Z = 0) :
    ∃ x : X ⟶ ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i),
      x ≫ sumGeneratorsInl.{u₁, v₁, w, t} R U Z = y := by
  refine ⟨y ≫ sumGeneratorsFst.{u₁, v₁, w, t} R U Z, ?_⟩
  rw [Category.assoc]
  conv_rhs => rw [← Category.comp_id y, ← sumGeneratorsSplit.{u₁, v₁, w, t} R U Z]
  rw [Preadditive.comp_add, ← Category.assoc y, ← Category.assoc y, hy, zero_comp, add_zero]

/-- The projection onto the second block is a split epimorphism, hence an epimorphism. -/
instance isSplitEpi_sumGeneratorsSnd :
    IsSplitEpi (sumGeneratorsSnd.{u₁, v₁, w, t} R U Z) :=
  IsSplitEpi.mk' ⟨sumGeneratorsInr.{u₁, v₁, w, t} R U Z,
    sumGeneratorsInr_comp_snd.{u₁, v₁, w, t} R U Z⟩

end SumGenerators

/-! ### The lifting step, with the covering sieve -/

section Lifting

variable (S : QuasiCompactObjectsSituation C) (R : Sheaf S.topology RingCat.{w})

/-- **The lifting step of Stacks 093G.** Let `q : A ⟶ G` be an epimorphism of sheaves of
modules and let `ψ : j_{W!} O_W ⟶ G`. Then there is a covering family of `W` by distinguished
objects over each member of which `ψ` lifts through `q`.

Local surjectivity of `q` produces a covering of `W` on which the section of `G` corresponding
to `ψ` under Stacks 0G1V lifts, and condition (1) of Stacks 0937 refines that covering by
distinguished objects. Unlike
`Stacks.SheafOfModules.exists_finite_lift_extensionByZeroUnit` this keeps the covering sieve and
does not cut the family down to a finite one, which is what Stacks 093F consumes. -/
theorem exists_hypercover_lift_extensionByZeroUnit (hEnough : S.HasEnoughObjects)
    {A G : SheafOfModules.{max u₁ v₁ w t} R} (q : A ⟶ G) [Epi q] {W : C}
    (ψ : extensionByZeroUnit.{u₁, v₁, w, t} R W ⟶ G) :
    ∃ 𝒲 : PreZeroHypercover.{max u₁ v₁} W, 𝒲.sieve₀ ∈ S.topology W ∧
      (∀ c, 𝒲.X c ∈ S.objects) ∧
        ∃ d : ∀ c, extensionByZeroUnit.{u₁, v₁, w, t} R (𝒲.X c) ⟶ A,
          ∀ c, d c ≫ q = extensionByZeroUnitMap.{u₁, v₁, w, t} R (𝒲.f c) ≫ ψ := by
  obtain ⟨T, hT, hlift⟩ := EpiMono.exists_covering_of_epi q
    (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R W G ψ)
  obtain ⟨𝒲, h𝒲mem, h𝒲obj, h𝒲sub⟩ := exists_hypercover_subordinate S hEnough hT
  refine ⟨𝒲, h𝒲mem, h𝒲obj, ?_⟩
  choose s hs using fun c ↦ hlift (𝒲.f c) (h𝒲sub c)
  refine ⟨fun c ↦ (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R (𝒲.X c) A).symm (s c),
    fun c ↦ ?_⟩
  refine (extensionByZeroUnitHomEquiv.{u₁, v₁, w, t} R (𝒲.X c) G).injective ?_
  rw [extensionByZeroUnitHomEquiv_naturality, extensionByZeroUnitHomEquiv_map]
  exact (congrArg (fun x ↦ (SheafOfModules.evaluation R (op (𝒲.X c))).map q x)
    (Equiv.apply_symm_apply _ (s c))).trans (hs c)

/-- `Stacks.SheafOfModules.epi_sigmaDesc_sigmaIota` with the outer index type `Fin n` relaxed to
an arbitrary type in `Type (max u₁ v₁)`, which is the universe in which Stacks 0G1W and 093F
produce their index sets. The proof is unchanged. -/
theorem epi_sigmaDesc_sigmaIota' {L : Type (max u₁ v₁)} (X : L → C)
    (ι : L → Type (max u₁ v₁)) (Y : ∀ l, ι l → C) (g : ∀ l c, Y l c ⟶ X l)
    (hepi : ∀ l,
      Epi (Sigma.desc fun c ↦ extensionByZeroUnitMap.{u₁, v₁, w, t} R (g l c))) :
    Epi (Sigma.desc fun x : Σ l, ι l ↦
      extensionByZeroUnitMap.{u₁, v₁, w, t} R (g x.1 x.2) ≫
        Sigma.ι (fun l ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (X l)) x.1) := by
  refine ⟨fun {P} h₁ h₂ hh => Sigma.hom_ext _ _ fun l => ?_⟩
  have _ := hepi l
  refine (cancel_epi (Sigma.desc fun c ↦
    extensionByZeroUnitMap.{u₁, v₁, w, t} R (g l c))).1 (Sigma.hom_ext _ _ fun c => ?_)
  have h := Sigma.ι (fun x : Σ l, ι l ↦
    extensionByZeroUnit.{u₁, v₁, w, t} R (Y x.1 x.2)) (⟨l, c⟩ : Σ l, ι l) ≫= hh
  rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc, Category.assoc, Category.assoc] at h
  simp only [Sigma.ι_desc_assoc]
  exact h

end Lifting

/-! ### Stacks 093G -/

section Extension

variable (S : QuasiCompactObjectsSituation C) (R : Sheaf S.topology RingCat.{w})

/-- The cokernel projection of `b`, followed by an isomorphism, is a cokernel of `b`. -/
private theorem exact_cokernel_π_comp_hom {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {A B X : 𝒜}
    (b : A ⟶ B) (e : cokernel b ≅ X) :
    (ShortComplex.mk b (cokernel.π b ≫ e.hom)
      (by rw [← Category.assoc, cokernel.condition, zero_comp])).Exact :=
  ShortComplex.exact_of_iso
    (ShortComplex.isoMk (S₁ := ShortComplex.mk b (cokernel.π b) (cokernel.condition b))
      (S₂ := ShortComplex.mk b (cokernel.π b ≫ e.hom)
        (by rw [← Category.assoc, cokernel.condition, zero_comp]))
      (Iso.refl _) (Iso.refl _) e (by simp) (by simp))
    (ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel b))

/-- **The assembly step of Stacks 093G.** Suppose given a short exact sequence
`E : F₁ ⟶ F₂ ⟶ F₃`, a finite presentation `b : ⊕_j A_{V_j} ⟶ ⊕_i A_{U_i}` of `F₁`, and a finite
presentation `g : ⊕_l A_{Wr_l} ⟶ ⊕_x A_{Wg_x}` of `F₃` **each of whose generators lifts through
`F₂ ⟶ F₃`**, by `lift`. Then `F₂` has a finite presentation by extensions by zero: it is the
cokernel of
`⊕_j A_{V_j} ⊕ ⊕_{(l,s)} A_{Y_{ls}} ⟶ ⊕_i A_{U_i} ⊕ ⊕_x A_{Wg_x}`,
where the `Y_{ls}` refine the `Wr_l` so far that the relations of `F₃` lift to the kernel
`K₂ = Ker(⊕_i A_{U_i} ⊕ ⊕_x A_{Wg_x} ⟶ F₂)`.

This is the second half of Stacks' proof: the snake lemma
(`Stacks.SheafOfModules.epi_kernelMap_of_epi_of_exact`) makes `K₂ ⟶ K₃` an epimorphism, the
lifting step
(`Stacks.SheafOfModules.exists_finite_lift_extensionByZeroUnit`) applied to *that* epimorphism
produces the `Y_{ls}`, and `Stacks.SheafOfModules.epi_of_epi_kernelMap_comp` then says the two
blocks together generate `K₂`. -/
theorem hasFiniteExtensionByZeroPresentation_of_lifted_generators
    (hEnough : S.HasEnoughObjects) (hqc : S.ObjectsAreQuasiCompact)
    {E : ShortComplex (SheafOfModules.{max u₁ v₁ w t} R)} (hE : E.ShortExact)
    {n m : ℕ} (U : Fin n → C) (V : Fin m → C) (hU : ∀ i, U i ∈ S.objects)
    (hV : ∀ j, V j ∈ S.objects)
    (b : (∐ fun j ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (V j)) ⟶
      ∐ fun i ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (U i))
    (eb : cokernel b ≅ E.X₁)
    {κ : Type (max u₁ v₁)} [Finite κ] (Wg : κ → C) (hWg : ∀ x, Wg x ∈ S.objects)
    {L : Type (max u₁ v₁)} [Finite L] (Wr : L → C) (hWr : ∀ l, Wr l ∈ S.objects)
    (g : (∐ fun l ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Wr l)) ⟶
      ∐ fun x ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Wg x))
    (eg : cokernel g ≅ E.X₃)
    (lift : ∀ x, extensionByZeroUnit.{u₁, v₁, w, t} R (Wg x) ⟶ E.X₂)
    (hlift : ∀ x, lift x ≫ E.g =
      Sigma.ι (fun x' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Wg x')) x ≫
        cokernel.π g ≫ eg.hom) :
    HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R E.X₂ := by
  classical
  have _ := hE.mono_f
  have _ := hE.epi_g
  have _ : Epi (cokernel.π b ≫ eb.hom) := epi_comp _ _
  have hcc : Epi (cokernel.π g ≫ eg.hom) := epi_comp _ _
  -- The chosen lift of the quotient map of `F₃` to `F₂`.
  have hβ : (Sigma.desc lift) ≫ E.g = cokernel.π g ≫ eg.hom :=
    Sigma.hom_ext _ _ fun x ↦ by rw [Sigma.ι_desc_assoc]; exact hlift x
  -- `φ : ⊕_i A_{U_i} ⊕ ⊕_x A_{Wg_x} ⟶ F₂`, and the square over `F₂ ⟶ F₃` it sits in.
  set φ := sumGeneratorsDesc.{u₁, v₁, w, t} R U Wg ((cokernel.π b ≫ eb.hom) ≫ E.f)
    (Sigma.desc lift) with hφdef
  have hsq : φ ≫ E.g = sumGeneratorsSnd.{u₁, v₁, w, t} R U Wg ≫ (cokernel.π g ≫ eg.hom) := by
    rw [hφdef]
    refine sumGenerators_hom_ext.{u₁, v₁, w, t} R U Wg _ _ ?_ ?_
    · rw [sumGeneratorsInl_comp_desc_assoc, sumGeneratorsInl_comp_snd_assoc, zero_comp,
        Category.assoc, E.zero, comp_zero]
    · rw [sumGeneratorsInr_comp_desc_assoc, sumGeneratorsInr_comp_snd_assoc, hβ]
  have hφ : Epi φ := by
    rw [hφdef, Preadditive.epi_iff_cancel_zero]
    intro X h hh
    have h₁ : E.f ≫ h = 0 := by
      have hl := sumGeneratorsInl.{u₁, v₁, w, t} R U Wg ≫= hh
      rw [sumGeneratorsInl_comp_desc_assoc, comp_zero, Category.assoc] at hl
      exact (cancel_epi (cokernel.π b ≫ eb.hom)).1 (hl.trans comp_zero.symm)
    obtain ⟨h', hh'⟩ := hE.exact.desc' h h₁
    have h₂ : h' = 0 := by
      have hr := sumGeneratorsInr.{u₁, v₁, w, t} R U Wg ≫= hh
      rw [sumGeneratorsInr_comp_desc_assoc, comp_zero] at hr
      have _ := hcc
      refine (cancel_epi (cokernel.π g ≫ eg.hom)).1 ?_
      rw [comp_zero, ← hβ, Category.assoc, hh']
      exact hr
    rw [← hh', h₂, comp_zero]
  -- The snake lemma: `K₂ = Ker φ` surjects onto `K₃ = Ker(⊕_x A_{Wg_x} ⟶ F₃)`.
  have hsnake : Epi (kernel.map φ (cokernel.π g ≫ eg.hom)
      (sumGeneratorsSnd.{u₁, v₁, w, t} R U Wg) E.g hsq) :=
    epi_kernelMap_of_epi_of_exact hE.exact hsq
      (sumGeneratorsInl_comp_desc.{u₁, v₁, w, t} R U Wg _ _)
      (sumGeneratorsInl_comp_snd.{u₁, v₁, w, t} R U Wg)
  -- `K₃` is generated by the relations of `F₃`.
  have hgcc : g ≫ (cokernel.π g ≫ eg.hom) = 0 := by
    rw [← Category.assoc, cokernel.condition, zero_comp]
  have hexg := exact_cokernel_π_comp_hom g eg
  have hκ : Epi (kernel.lift (cokernel.π g ≫ eg.hom) g hgcc) := hexg.epi_kernelLift
  -- The second lifting step, applied to the epimorphism `K₂ ⟶ K₃` the snake lemma produced.
  have _ := hsnake
  choose σ hσ Y gY hYobj hYepi ee hee using fun l ↦
    exists_finite_lift_extensionByZeroUnit.{u₁, v₁, w, t} S R hEnough hqc
      (kernel.map φ (cokernel.π g ≫ eg.hom)
        (sumGeneratorsSnd.{u₁, v₁, w, t} R U Wg) E.g hsq) (hWr l)
      (Sigma.ι (fun l' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Wr l')) l ≫
        kernel.lift (cokernel.π g ≫ eg.hom) g hgcc)
  have _ : ∀ l, Finite (σ l) := hσ
  -- The relations of the extension: those of `F₁`, read into `K₂`, and the lifts just chosen.
  have hbν : (b ≫ sumGeneratorsInl.{u₁, v₁, w, t} R U Wg) ≫ φ = 0 := by
    rw [hφdef, Category.assoc, sumGeneratorsInl_comp_desc, ← Category.assoc, ← Category.assoc,
      cokernel.condition, zero_comp, zero_comp]
  set Λ := sumGeneratorsDesc.{u₁, v₁, w, t} R V (fun x : Σ l, σ l ↦ Y x.1 x.2)
    (kernel.lift φ (b ≫ sumGeneratorsInl.{u₁, v₁, w, t} R U Wg) hbν)
    (Sigma.desc fun x : Σ l, σ l ↦ ee x.1 x.2) with hΛdef
  have hΛ : Epi Λ := by
    refine epi_of_epi_kernelMap_comp (E := E) hsq
      (fun _ _ hy ↦ exists_comp_sumGeneratorsInl.{u₁, v₁, w, t} R U Wg _ hy)
      (sumGeneratorsInl_comp_desc.{u₁, v₁, w, t} R U Wg _ _)
      (hex := exact_cokernel_π_comp_hom b eb)
      (κ₁ := sumGeneratorsInl.{u₁, v₁, w, t} R V (fun x : Σ l, σ l ↦ Y x.1 x.2))
      (κ₃ := sumGeneratorsInr.{u₁, v₁, w, t} R V (fun x : Σ l, σ l ↦ Y x.1 x.2))
      ?_ ?_
    · rw [hΛdef, sumGeneratorsInl_comp_desc_assoc, kernel.lift_ι]
    · rw [hΛdef, sumGeneratorsInr_comp_desc_assoc]
      have hfac : (Sigma.desc fun x : Σ l, σ l ↦ ee x.1 x.2) ≫
          kernel.map φ (cokernel.π g ≫ eg.hom)
            (sumGeneratorsSnd.{u₁, v₁, w, t} R U Wg) E.g hsq =
          (Sigma.desc fun x : Σ l, σ l ↦
              extensionByZeroUnitMap.{u₁, v₁, w, t} R (gY x.1 x.2) ≫
                Sigma.ι (fun l ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (Wr l)) x.1) ≫
            kernel.lift (cokernel.π g ≫ eg.hom) g hgcc :=
        Sigma.hom_ext _ _ fun x ↦ by
          rw [Sigma.ι_desc_assoc, Sigma.ι_desc_assoc]
          exact (hee x.1 x.2).trans (Category.assoc _ _ _).symm
      rw [hfac]
      have _ := epi_sigmaDesc_sigmaIota'.{u₁, v₁, w, t} S R Wr σ Y gY hYepi
      have _ := hκ
      exact epi_comp _ _
  -- `F₂` is the cokernel of the relations, since `φ` is an epimorphism with kernel `K₂`.
  have _ := hΛ
  have _ := hφ
  refine hasFiniteExtensionByZeroPresentation_of_finite S R (Sum.elim U Wg)
    (Sum.elim V fun x : Σ l, σ l ↦ Y x.1 x.2) ?_ ?_ (Λ ≫ kernel.ι φ) ?_
  · rintro (i | x)
    exacts [hU i, hWg x]
  · rintro (j | x)
    exacts [hV j, hYobj x.1 x.2]
  · -- `φ` is an epimorphism and `Ker φ ⟶ ⊕ ⟶ F₂` is exact, so `F₂ = Coker(Ker φ ⟶ ⊕)`.
    have hexφ : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).Exact :=
      ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel φ)
    have _ : Mono (cokernel.desc (kernel.ι φ) φ (kernel.condition φ)) :=
      hexφ.mono_cokernelDesc
    have _ : Epi (cokernel.π (kernel.ι φ) ≫
        cokernel.desc (kernel.ι φ) φ (kernel.condition φ)) := by
      rw [cokernel.π_desc]
      exact hφ
    have _ := epi_of_epi (cokernel.π (kernel.ι φ))
      (cokernel.desc (kernel.ι φ) φ (kernel.condition φ))
    have _ := isIso_of_mono_of_epi (cokernel.desc (kernel.ι φ) φ (kernel.condition φ))
    exact cokernelEpiComp Λ (kernel.ι φ) ≪≫
      asIso (cokernel.desc (kernel.ι φ) φ (kernel.condition φ))

/-- **Stacks Project, Tag 093G.** On a site with a distinguished collection of objects which
covers every object, consists of quasi-compact objects and whose coverings have quasi-compact
pairwise fibre products, the sheaves of modules with a finite presentation by extensions by zero
are stable under extensions: if `E` is a short exact sequence of sheaves of modules whose outer
terms have such presentations, so does its middle term.

This is Stacks' own argument. Choose presentations `⊕A_{V_j} ⟶ ⊕A_{U_i} ⟶ F₁ ⟶ 0` and
`⊕A_{T_j} ⟶ ⊕A_{W_i} ⟶ F₃ ⟶ 0`. Since `F₂ ⟶ F₃` is an epimorphism, each generator `A_{W_i}`
lifts to `F₂` after passing to a covering of `W_i` by distinguished objects
(`Stacks.SheafOfModules.exists_hypercover_lift_extensionByZeroUnit`), and Stacks 093F
(`Stacks.SheafOfModules.exists_finite_refinement_isIso_cokernelMap`) replaces the `W_i` by a
finite subfamily of that covering without changing the cokernel. The rest is
`Stacks.SheafOfModules.hasFiniteExtensionByZeroPresentation_of_lifted_generators`. -/
@[stacks 093G]
theorem hasFiniteExtensionByZeroPresentation_of_shortExact (hEnough : S.HasEnoughObjects)
    (hqc : S.ObjectsAreQuasiCompact) (hqs : S.CoverPullbacksAreQuasiCompact)
    (E : ShortComplex (SheafOfModules.{max u₁ v₁ w t} R)) (hE : E.ShortExact)
    (h₁ : HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R E.X₁)
    (h₃ : HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R E.X₃) :
    HasFiniteExtensionByZeroPresentation.{u₁, v₁, w, t} S R E.X₂ := by
  classical
  have _ := hE.epi_g
  obtain ⟨n, m, U, V, hU, hV, b₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨n₃, m₃, W, T, hW, hT, b₃, ⟨e₃⟩⟩ := h₃
  -- Each generator of `F₃` lifts to `F₂` on a covering of `W i` by distinguished objects.
  choose 𝒲 h𝒲cov h𝒲obj d hd using fun i ↦
    exists_hypercover_lift_extensionByZeroUnit.{u₁, v₁, w, t} S R hEnough E.g
      (Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (W i')) i ≫
        (cokernel.π b₃ ≫ e₃.hom))
  -- Stacks 093F cuts those coverings down to finite subfamilies, without changing `Coker b₃`.
  obtain ⟨Tset, 𝒱, hTfin, hTeq, hTcov, L, hLfin, W', hW'obj, gg, pp, hcomm, hqepi, hiso⟩ :=
    exists_finite_refinement_isIso_cokernelMap.{u₁, v₁, w, t} S R hEnough hqc hqs T hW hT
      𝒲 h𝒲cov h𝒲obj b₃
  have hfin : ∀ i, Finite (𝒱 i).I₀ := fun i ↦ by rw [hTeq i]; exact (hTfin i).to_subtype
  have h𝒱obj : ∀ (i : Fin n₃) (k : (𝒱 i).I₀), (𝒱 i).X k ∈ S.objects := fun i ↦ by
    rw [hTeq i]
    exact fun k ↦ h𝒲obj i k.1
  have hliftex : ∀ (i : Fin n₃) (k : (𝒱 i).I₀),
      ∃ dd : extensionByZeroUnit.{u₁, v₁, w, t} R ((𝒱 i).X k) ⟶ E.X₂,
        dd ≫ E.g = extensionByZeroUnitMap.{u₁, v₁, w, t} R ((𝒱 i).f k) ≫
          Sigma.ι (fun i' ↦ extensionByZeroUnit.{u₁, v₁, w, t} R (W i')) i ≫
            (cokernel.π b₃ ≫ e₃.hom) := by
    intro i
    rw [hTeq i]
    exact fun k ↦ ⟨d i k.1, hd i k.1⟩
  choose dd hdd using fun x : Σ i, (𝒱 i).I₀ ↦ hliftex x.1 x.2
  have _ := hiso hcomm
  refine hasFiniteExtensionByZeroPresentation_of_lifted_generators S R hEnough hqc hE U V hU hV
    b₁ e₁ (fun x : Σ i, (𝒱 i).I₀ ↦ (𝒱 x.1).X x.2) (fun x ↦ h𝒱obj x.1 x.2) W' hW'obj gg
    (asIso (cokernel.map gg b₃ pp (refinementAugmentation.{u₁, v₁, w, t} R 𝒱) hcomm) ≪≫ e₃)
    dd fun x ↦ ?_
  rw [Iso.trans_hom, asIso_hom, ← Category.assoc (cokernel.π gg), cokernel.π_desc,
    Category.assoc, ι_comp_refinementAugmentation_assoc]
  exact hdd x

end Extension

end Stacks.SheafOfModules

end
