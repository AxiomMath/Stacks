module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisDirectImageComposition

/-!
# The annihilation of [Stacks, Tag 07Q9] along the tower of `α_p`-covers

[Stacks, Tag 07Q9] proves its conclusion for an iterated `α_p`-cover by writing the cover as a
tower

`X' = X_n ⟶ X_{n - 1} ⟶ ⋯ ⟶ X_0 = X`

of `α_p`-covers, proving that each stage contributes a cone whose cohomology sheaves are
annihilated by `p`, and invoking (TR 4) `n` times to multiply the annihilators into
`p ^ n = q` for the composite.  `...SmallSite.annihilation07Q9_comp` of
`SmallSite/CrisDirectImageComposition.lean` is the single (TR 4) step in the vocabulary of
`...SmallSite.Annihilation07Q9` itself.  **This module runs that step along the whole tower**: a
chain of `n` composable maps of `D⁺(Ab(X_Zar))`, each with `Annihilation07Q9` for `a`, has a
composite with `Annihilation07Q9` for `a ^ n`.  Unconditionally.

## Why the chain form is not a one-line corollary of the binary one

`Stacks.Triangulated.pow_smul_id_eq_zero_of_chainComp` of
`Crystalline/AlphaPCoverCohomologyBound.lean` already propagates an annihilator along a chain,
but it propagates the annihilation of the **cone** and [Stacks, Tag 07Q9]'s conclusion is the
annihilation of the cone's **cohomology sheaves**.  The two are not interchangeable: an object
whose cohomology objects are all killed by `a` need not itself be killed by `a`, so the chain
induction has to be rerun on the cohomology reading, with
`Stacks.Triangulated.mul_smul_id_homologyFunctor_eq_zero_of_comp` — the octahedron axiom followed
by the cohomology long exact sequence — in place of the plain (TR 4) step.  That rerun is
`pow_smul_id_homologyFunctor_eq_zero_of_chainComp` below, and
`...SmallSite.annihilation07Q9_chainComp` is its reading in 07Q9's own vocabulary.

The base case is the empty tower, where the composite is an identity and its cone is a zero
object; the exponent is `a ^ 0 = 1` and a zero object is annihilated by every scalar.  That is
also the content of `annihilation07Q9_one_of_isIso`, which makes `Annihilation07Q9` indifferent
to pre- and postcomposition with isomorphisms (`annihilation07Q9_isIso_comp`,
`annihilation07Q9_comp_isIso`).  Those two matter for the intended use: the composition
functoriality of the comparison map, when it is available, presents the comparison of a composite
cover only up to the isomorphisms `...SmallSite.zariskiPushforwardComp` and
`...SmallSite.crisInverseImageCompCell` — see `...SmallSite.zariskiComparison_comp` of
`SmallSite/CrisZariskiSquareComposition.lean` — and an annihilation statement that did not
absorb them could not be applied to it.

## What this closes, and what it leaves

What it closes is the *propagation* half of the reduction of [Stacks, Tag 07Q9] to the tower: the
per-stage annihilation composes, with the exponent adding, and the exponent of the composite of
`n` stages is the `p ^ n` that `AlgebraicGeometry.exists_hasFiniteBasis_of_isAlphaPCoverComposite`
of `Crystalline/AlphaPCoverDegree.lean` computes as the degree.  No hypothesis is carried: the
statements below are theorems about chains in `D⁺(Ab(X_Zar))`.

What it leaves is two things, and neither is in this file.

1. **The local step.**  That one stage of the tower contributes a cone with cohomology sheaves
   annihilated by `p` is the mathematics of [Stacks, Tag 07Q9], and it is
   [Stacks, Proposition 60.21.3, Tag 07LG] — the computation of the cohomology of a crystal in
   quasi-coherent modules by the de Rham complex of the divided power envelope — paired with
   [Stacks, Lemma 60.25.1, Tag 07Q7] at `a = p` for the extension of [Stacks, Tag 07N1].  The
   07N1 half is in this library on both sides of the `p`-adic completion:
   `Crystalline.exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials` uncompleted and
   `Crystalline.exists_completedHomotopyInverse_pthRootExtension_dividedPowerDifferentials`
   completed, with the split injection `D ⟶ D'` as
   `Crystalline.PthRootExtension.injective_completedToPrimeRing`.  [Stacks, Proposition 07LG] is
   not.
2. **The identification of the composite's comparison map with the composite of the stages'
   comparison maps**, in the derived form.  The underived form is in the library and carries
   nothing: `...SmallSite.zariskiComparison_comp` of
   `SmallSite/CrisZariskiSquareComposition.lean` rests on the coherence
   `...SmallSite.CrisZariskiCellComp`, and that coherence is the theorem
   `...SmallSite.crisZariskiCellComp` of `SmallSite/CrisZariskiCellCompositionProof.lean`, which
   that file turns into the unconditional `...SmallSite.zariskiComparison_comp'`.  The *derived*
   form is in the library too, and also with no hypotheses:
   `...SmallSite.derivedZariskiComparison_comp'` of
   `SmallSite/DerivedCrisZariskiComposition.lean`, from the derived unit of a composite
   (`...SmallSite.derivedCrisUnit_comp_eq`) and the coherence of the three derived squares of
   topoi (`...SmallSite.derivedZariskiSquare_comp`).

So neither the tower nor the identification of the composite's comparison map stands between the
library and [Stacks, Tag 07Q9]; the local step alone does.

## Main results

* `Stacks.Triangulated.pow_smul_id_homologyFunctor_eq_zero_of_chainComp` — **(TR 4) along a
  chain, read on cohomology objects.**  If every stage of a chain in `D⁺(𝒜)` has a cone whose
  cohomology objects are annihilated by `a`, the composite of the first `n` stages has a cone
  whose cohomology objects are annihilated by `a ^ n`.
* `...SmallSite.annihilation07Q9_one_of_isIso` — an isomorphism satisfies `Annihilation07Q9` for
  `1`, its cone being a zero object.
* `...SmallSite.annihilation07Q9_isIso_comp` and `...SmallSite.annihilation07Q9_comp_isIso` —
  `Annihilation07Q9` absorbs an isomorphism on either side.
* `...SmallSite.annihilation07Q9_chainComp` — **the tower globalisation**: a chain of maps each
  with `Annihilation07Q9` for `a` has a composite with `Annihilation07Q9` for `a ^ n`.

## No tag is placed

**Neither [Stacks, Tag 07Q9] nor [Stacks, Tag 07QA] is proved here and no tag attribute is
placed.**  Every statement below is a theorem about chains of morphisms in a derived category
with the per-stage annihilation as an explicit hypothesis on the chain; none of them asserts that
any particular morphism of the crystalline theory satisfies it.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.25.1, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated AlgebraicGeometry

universe w w' v u

noncomputable section

namespace Stacks.Triangulated

/-! ### (TR 4) along a chain, read on cohomology objects -/

section Chain

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
  [IsTriangulated (DerivedCategory.Plus 𝒜)]

omit [IsTriangulated (DerivedCategory.Plus 𝒜)] in
/-- **The cohomology objects of a zero object of `D⁺(𝒜)` are zero**, in the form the base case of
the chain induction consumes: every scalar annihilates them.  The cone of an identity is a zero
object, which is why the empty tower contributes the exponent `a ^ 0 = 1`. -/
theorem smul_id_homologyFunctor_eq_zero_of_isZero {Z : DerivedCategory.Plus 𝒜} (hZ : IsZero Z)
    (a : ℤ) (j : ℤ) :
    a • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj Z) = 0 := by
  have h1 : 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj Z) = 0 := by
    rw [← CategoryTheory.Functor.map_id, hZ.eq_of_src (𝟙 Z) 0, Functor.map_zero]
  rw [h1, smul_zero]

/-- **The (TR 4) step of [Stacks, Tag 07Q9] along the whole tower, read on cohomology objects.**
Let `Y 0 ⟶ Y 1 ⟶ ⋯` be a chain in `D⁺(𝒜)` and let `a` annihilate every cohomology object of the
third term of every distinguished triangle on every stage.  Then `a ^ n` annihilates every
cohomology object of the third term of every distinguished triangle on the composite
`Stacks.Triangulated.chainComp` of the first `n` stages.

This is the chain form of `mul_smul_id_homologyFunctor_eq_zero_of_comp`, and it is **not** the
chain form `pow_smul_id_eq_zero_of_chainComp` of
`Crystalline/AlphaPCoverCohomologyBound.lean` already carries: that one propagates the
annihilation of the cone itself, and an object whose cohomology objects are all killed by `a`
need not be killed by `a`, so neither statement implies the other.  [Stacks, Tag 07Q9]'s
conclusion is about the cohomology sheaves, so it is this reading the tower reduction needs.

The base case is the empty composite, an identity, whose cone is a zero object
(`CategoryTheory.Pretriangulated.Triangle.isZero₃_of_isIso₁`) and therefore has zero cohomology
objects; the exponent there is `a ^ 0 = 1`. -/
theorem pow_smul_id_homologyFunctor_eq_zero_of_chainComp
    (Y : ℕ → DerivedCategory.Plus 𝒜) (g : ∀ i : ℕ, Y i ⟶ Y (i + 1)) (a : ℤ)
    (hg : ∀ (i : ℕ) (W : DerivedCategory.Plus 𝒜) (v : Y (i + 1) ⟶ W)
        (w : W ⟶ (Y i)⟦(1 : ℤ)⟧),
      Triangle.mk (g i) v w ∈ distTriang (DerivedCategory.Plus 𝒜) → ∀ j : ℤ,
        a • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj W) = 0) (n : ℕ) :
    ∀ {Z : DerivedCategory.Plus 𝒜} (v : Y n ⟶ Z) (w : Z ⟶ (Y 0)⟦(1 : ℤ)⟧),
      Triangle.mk (chainComp Y g n) v w ∈ distTriang (DerivedCategory.Plus 𝒜) → ∀ j : ℤ,
        a ^ n • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj Z) = 0 := by
  induction n with
  | zero =>
    intro Z v w hZ j
    have hiso : IsIso (Triangle.mk (chainComp Y g 0) v w).mor₁ := by
      show IsIso (chainComp Y g 0)
      rw [chainComp_zero]
      infer_instance
    have hzero : IsZero Z := Triangle.isZero₃_of_isIso₁ _ hZ hiso
    rw [pow_zero]
    exact smul_id_homologyFunctor_eq_zero_of_isZero hzero 1 j
  | succ n ih =>
    intro Z v w hZ j
    rw [pow_succ]
    exact mul_smul_id_homologyFunctor_eq_zero_of_comp (chainComp Y g n) (g n) (a ^ n) a
      (fun W v' w' hW j' ↦ ih v' w' hW j') (fun W v' w' hW j' ↦ hg n W v' w' hW j') v w hZ j

end Chain

end Stacks.Triangulated

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### `Annihilation07Q9` along the tower -/

section Tower

variable (S₀ : GlobalCrystallineSituation.{u})
  [HasDerivedCategory.{w'} (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})]

/-- **An isomorphism satisfies `Annihilation07Q9` for `1`.**  The third term of a distinguished
triangle whose first map is invertible is a zero object, so all of its cohomology sheaves vanish
and every scalar annihilates them.

This is the empty stage of the tower `X' = X_n ⟶ ⋯ ⟶ X_0 = X`, whose base case in
`AlgebraicGeometry.IsAlphaPCoverComposite` is an isomorphism and not an identity. -/
theorem annihilation07Q9_one_of_isIso
    {A B : DerivedCategory.Plus (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})}
    (e : A ⟶ B) [IsIso e] :
    Annihilation07Q9 S₀ 1 e := by
  intro E v wE hT j
  have hiso : IsIso (Triangle.mk e v wE).mor₁ := by
    show IsIso e
    infer_instance
  have hzero : IsZero E := Triangle.isZero₃_of_isIso₁ _ hT hiso
  exact Stacks.Triangulated.smul_id_homologyFunctor_eq_zero_of_isZero hzero _ j

/-- **`Annihilation07Q9` absorbs an isomorphism on the source side.**  Precomposing with an
isomorphism changes neither the cone nor therefore its cohomology sheaves; formally this is
`...SmallSite.annihilation07Q9_comp` with the exponent `1 * q`. -/
theorem annihilation07Q9_isIso_comp (q : ℕ)
    {A' A B : DerivedCategory.Plus (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})}
    (e : A' ⟶ A) [IsIso e] (α : A ⟶ B) (h : Annihilation07Q9 S₀ q α) :
    Annihilation07Q9 S₀ q (e ≫ α) := by
  have h' := annihilation07Q9_comp S₀ 1 q e α (annihilation07Q9_one_of_isIso S₀ e) h
  rwa [one_mul] at h'

/-- **`Annihilation07Q9` absorbs an isomorphism on the target side**, by the same argument with
the exponent `q * 1`.

Together with `annihilation07Q9_isIso_comp` this is what makes the chain lemma below usable
against a composition functoriality stated only up to isomorphism, as
`...SmallSite.zariskiComparison_comp` is. -/
theorem annihilation07Q9_comp_isIso (q : ℕ)
    {A B B' : DerivedCategory.Plus (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1})}
    (α : A ⟶ B) (e : B ⟶ B') [IsIso e] (h : Annihilation07Q9 S₀ q α) :
    Annihilation07Q9 S₀ q (α ≫ e) := by
  have h' := annihilation07Q9_comp S₀ q 1 α e h (annihilation07Q9_one_of_isIso S₀ e)
  rwa [mul_one] at h'

/-- **The globalisation of [Stacks, Tag 07Q9] over the tower of `α_p`-covers.**  Let
`Y 0 ⟶ Y 1 ⟶ ⋯` be a chain in `D⁺(Ab(X_Zar))` — the comparison maps of the stages of
`X' = X_n ⟶ ⋯ ⟶ X_0 = X` — and suppose each stage satisfies the conclusion of
[Stacks, Tag 07Q9] for `a`.  Then the composite of the first `n` stages satisfies it for `a ^ n`.

At `a = p` this is the source's `p ^ n = q`, with `q` the constant degree of the composite cover:
`AlgebraicGeometry.exists_hasFiniteBasis_of_isAlphaPCoverComposite` of
`Crystalline/AlphaPCoverDegree.lean` computes exactly that degree from the same `n`.

Unconditional, and the whole propagation half of the tower reduction.  The derived composition
functoriality it needs in order to be pointed at `...SmallSite.derivedZariskiComparison` of an
iterated cover is `...SmallSite.derivedZariskiComparison_comp'` of
`SmallSite/DerivedCrisZariskiComposition.lean` — see the module documentation. -/
theorem annihilation07Q9_chainComp (a : ℕ)
    (Y : ℕ → DerivedCategory.Plus (Sheaf (opensTopology S₀) AddCommGrpCat.{u + 1}))
    (α : ∀ i : ℕ, Y i ⟶ Y (i + 1)) (hα : ∀ i : ℕ, Annihilation07Q9 S₀ a (α i)) (n : ℕ) :
    Annihilation07Q9 S₀ (a ^ n) (Stacks.Triangulated.chainComp Y α n) := by
  intro E v wE hT j
  have h := Stacks.Triangulated.pow_smul_id_homologyFunctor_eq_zero_of_chainComp
    Y α (a : ℤ) (fun i W v' w' hW j' ↦ hα i W v' w' hW j') n v wE hT j
  simpa using h

end Tower

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
