module

public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import StacksFrontier.AlgebraicGeometry.Algebraization.AnnihilatorTruncationReduction

/-!
# Annihilating the cone of an iterated cover, and the bound it puts on cohomology

[Stacks, Tag 07Q9] says that for an iterated `α_p`-cover `f : X' ⟶ X` of constant degree `q` and
a crystal in quasi-coherent modules `ℱ` on `Cris(X/S)`, the third term `E` of the triangle

`Ru_{X/S, *}ℱ ⟶ f_*Ru_{X'/S, *}ℱ' ⟶ E ⟶ Ru_{X/S, *}ℱ[1]`

has its cohomology sheaves annihilated by `q`, and [Stacks, Tag 07QA] deduces from this that
`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), ℱ')` has kernel and cokernel annihilated by
`q ^ (i + 1)`.  This module isolates the part of those two arguments which is pure triangulated
and derived-category algebra, and proves it:

* the step of [Stacks, Tag 07Q9] which takes the chain `X' = X_n ⟶ ⋯ ⟶ X_0 = X` of `α_p`-covers
  apart — each stage contributes a cone annihilated by `p`, and the source invokes (TR 4) to
  conclude that the composite has a cone annihilated by `p ^ n = q`;
* the step of [Stacks, Tag 07QA] which converts an annihilator of the cone into annihilators of
  the kernel and of the cokernel of a map on cohomology;
* the passage, used by [Stacks, Tag 07QA] through the spectral sequence
  `H^a(ℋ^b(E)) ⇒ H^{a + b}(E)`, from "the cohomology objects of `E` are annihilated by `q`" to
  "`q ^ (i + 1)` annihilates every map into `E` out of an object concentrated in degrees `≤ 0`",
  which is the derived form of "`q ^ (i + 1)` annihilates `H^i(X, E)`".

## Main definitions

* `Stacks.Triangulated.chainComp` — the composite `Y 0 ⟶ Y n` of the first `n` arrows of a chain
  `Y 0 ⟶ Y 1 ⟶ Y 2 ⟶ ⋯` in a category.

## Main results

* `Stacks.Triangulated.mul_smul_id_eq_zero_of_comp` — **the (TR 4) step for one composition.**  If
  `g` has a cone annihilated by `a` and `h` a cone annihilated by `b`, then `g ≫ h` has a cone
  annihilated by `a * b`.  This is the binary form, and it is the one an induction over
  `AlgebraicGeometry.IsAlphaPCoverComposite` consumes, that predicate's `comp` constructor
  presenting a single composition rather than an `ℕ`-indexed chain.
* `Stacks.Triangulated.pow_smul_id_eq_zero_of_chainComp` — **the (TR 4) step.**  If every stage of
  a chain has a cone annihilated by `a`, then the composite of the first `n` stages has a cone
  annihilated by `a ^ n`.  Proved from the binary form by induction.
* `Stacks.Triangulated.mul_smul_id_eq_zero_of_exact` — **annihilators multiply along an exact
  sequence**: if `X₁ ⟶ X₂ ⟶ X₃` is exact at `X₂` with `a` annihilating `X₁` and `b` annihilating
  `X₃`, then `a * b` annihilates `X₂`.
* `Stacks.Triangulated.mul_smul_id_homologyFunctor_eq_zero_of_comp` — **the (TR 4) step as
  [Stacks, Tag 07Q9] states it**, on the *cohomology objects* of the cone rather than on the cone:
  the octahedron axiom followed by the cohomology long exact sequence of the resulting triangle
  and the previous lemma.  The two readings are not interchangeable — a cone all of whose
  cohomology objects are killed by `a` need not be killed by `a` — and it is this one that 07Q9's
  conclusion asks for.  Its form in terms of
  `Crystalline.GlobalCrystallineSituation.SmallSite.Annihilation07Q9` itself is
  `...SmallSite.annihilation07Q9_comp` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisDirectImageComposition.lean`.
* `Stacks.Triangulated.smul_eq_zero_of_comp_mor₂_eq_zero` — **the kernel bound.**  In a
  distinguished triangle `W ⟶ A ⟶ B ⟶ W⟦1⟧`, if `r` annihilates every map `P ⟶ W` then it
  annihilates every map `P ⟶ A` killed by `A ⟶ B`.
* `Stacks.Triangulated.exists_comp_mor₁_eq_smul` — **the cokernel bound.**  If `r` annihilates
  every map `P ⟶ E`, then `r` times any map `P ⟶ B` factors through `A ⟶ B`.
* `Stacks.Triangulated.smul_id_eq_zero_of_concentrated` — an object of `D(𝒜)` concentrated in a
  single degree is annihilated by any scalar annihilating its one cohomology object.
* `Stacks.Triangulated.pow_smul_id_eq_zero_of_isGE_of_isLE` — **the truncation induction.**  An
  object of `D(𝒜)` concentrated in degrees `a` through `a + n` whose cohomology objects are all
  annihilated by `r` is itself annihilated by `r ^ (n + 1)`.
* `Stacks.Triangulated.pow_smul_eq_zero_of_isLE_of_isGE` — the same bound applied to morphisms:
  for `Q` concentrated in degrees `≥ a` with `H^j(Q)` annihilated by `r` for every `j ≤ b`, the
  scalar `r ^ ((b - a).toNat + 1)` annihilates every morphism `P ⟶ Q` out of an object `P`
  concentrated in degrees `≤ b`.
* `Stacks.Triangulated.pow_smul_eq_zero_of_comp_mor₂_eq_zero` and
  `Stacks.Triangulated.exists_comp_mor₁_eq_pow_smul` — the two bounds above combined: the
  kernel and the cokernel statements with the exponent `(b - a).toNat + 1` in place, which at
  `a = 0`, `b = i` is the `i + 1` of [Stacks, Tag 07QA].
* `Stacks.Triangulated.isGE_obj₃_sub_one` — the cone of a map between objects concentrated in
  degrees `≥ a` is concentrated in degrees `≥ a - 1`.
* `Stacks.Triangulated.isGE_obj₃_of_mono_homologyMap` — **the degree the cokernel bound turns
  on.**  That cone is concentrated in degrees `≥ a` as soon as `ℋ^a` of the first map is a
  monomorphism.  [Stacks, Tag 07QA]'s cokernel exponent is the source's `q ^ (i + 1)` only
  because `ℋ^{-1}(E)` vanishes — the filtration over the degrees `-1, 0, …, i` would otherwise
  give `q ^ (i + 2)` — and this is the lemma that supplies the vanishing from the injectivity of
  the adjunction unit rather than assuming it.  The kernel half needs no such input: its bound is
  a quotient of `H^{i - 1}(X, E)`, so the `i + 1` degrees `-1, 0, …, i - 1` already give the
  source's exponent.

## What is and is not proved

**No tag attribute is placed here.**  What is proved is the list above: the triangulated and
derived-category algebra which the proofs of [Stacks, Tag 07Q9] and [Stacks, Tag 07QA] run on,
stated for an arbitrary (pre)triangulated category and an arbitrary abelian category, with no
crystalline input.  The tags themselves are proved elsewhere:

* [Stacks, Tag 07Q9] is `...SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AlphaPCover07Q9Main.lean`, its conclusion
  being the proposition `...SmallSite.Annihilation07Q9` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AlphaPCoverTriangle.lean`;
* [Stacks, Tag 07QA] is
  `...SmallSite.annihilated_ker_coker_crisModuleCohomologyMap_of_isIteratedAlphaPCover` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/CrisCohomologyBound07QAMain.lean`;
* the cohomological sentence of [Stacks, Tag 07QB] is
  `...SmallSite.relativeFrobeniusToTwist_isIteratedAlphaPCover_cohomologyBound` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AlphaPCoverRelativeFrobenius07QB.lean`.

The terms of the triangle are in the library: `Ru_{X/S, *}` is the derived direct image
`...SmallSite.derivedZariskiDirectImageFunctor` of the abelian `...SmallSite.zariskiDirectImage`
along the crystalline-to-Zariski morphism of [Stacks, Tag 07IL] (both in
`SmallSite/ZariskiDirectImage.lean`; the pushforward is rerun at `AddCommGrpCat.{u + 1}`
coefficients, not taken from `Stacks.Topos.AbelianPushforward.abelianPushforward`, which
internalizes group objects and is a different functor), `f_{Zar,*}` is
`...SmallSite.zariskiPushforward` and `f_{cris}^{-1}` is `...SmallSite.crisInverseImage`.  The
commutation `u_{X/S,*} ∘ f_{cris,*} ≅ f_{Zar,*} ∘ u_{X'/S,*}` is genuine mathematics rather than
assembly — the canonical 2-cell between the two composites runs the *wrong way*
(`...SmallSite.HasFreeCrisZariskiCell` records the direction that is free) — and it is
`...SmallSite.crisZariskiSquare` of `SmallSite/CrisZariskiSquareIso.lean`.  The map
`f^* : H^i(Cris(X/S), ℱ) ⟶ H^i(Cris(X'/S), f_{cris}^{-1}ℱ)` is `...SmallSite.crisCohomologyMap`:
`f_{cris}^{-1}` is exact by `CrystallineThickening.preservesFiniteLimits_lowerShriekAb` of
`SmallSite/LowerShriekAbelianExact.lean`, so `f_{cris, *}` preserves injective abelian sheaves and
the Leray factorization `RΓ(Cris(X'/S), -) ≅ Rf_{cris, *} ⋙ RΓ(Cris(X/S), -)` is
`...SmallSite.derivedCrisGlobalSectionsIso`, with the underived comparison
`...SmallSite.crisGlobalSectionsIso` of `SmallSite/CrisGlobalSectionsIso.lean`.  The bounds of
this module, read on the triangle of [Stacks, Tag 07Q9] in `D(Ab(X_Zar))`
(`...SmallSite.pow_smul_eq_zero_of_kernel_07QA`, `...SmallSite.exists_comp_mor₁_eq_pow_smul_07QA`),
are carried to `f^*` by
`...SmallSite.crisCohomologyMap_comp_crisCohomologyIsoZariskiHypercohomologyPushforward` of
`SmallSite/CrisCohomologyBound07QA.lean`, through the Leray coherence
`...SmallSite.crisZariskiLerayCoherence`.

The mathematical content of [Stacks, Tag 07Q9] is [Stacks, Proposition 07LG], the computation of
the cohomology of a crystal in quasi-coherent modules by the de Rham complex of the divided power
envelope — `...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
`SmallSite/CrystalDeRhamComputesCohomology.lean`, resting on [Stacks, Tag 07JN],
`...SmallSite.computesCohomology_wholeSpaceSystem_of_isSurjectiveComparison` of
`SmallSite/WholeSpaceSystemCohomology.lean` — together with [Stacks, Tag 07Q7] at `a = p` for the
extension `B ⟶ B[z]⟨ξ⟩/(ξ - (z ^ p - λ))` of [Stacks, Tag 07N1]
(`Crystalline.exists_homotopyInverse_pthRootExtension`, and for the completed envelope
`Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension_situation`).  The
proof of 07Q9 applies them over the opens on which the cover is a chain of `α_p`-extensions; the
propagation of a single-stage annihilation along a chain is also available, as
`pow_smul_id_eq_zero_of_chainComp` below for cones and `...SmallSite.annihilation07Q9_chainComp`
for their cohomology sheaves.

The first sentence of [Stacks, Tag 07QB] — that the relative Frobenius of a smooth morphism is an
iterated `α_p`-cover of constant degree `p ^ d` — is proved in
`StacksFrontier/AlgebraicGeometry/Crystalline/FrobeniusAlphaPCover.lean`, and the vocabulary of
iterated `α_p`-covers and of constant degree is in
`StacksFrontier/AlgebraicGeometry/Crystalline/AlphaPCover.lean`.  Neither is used here: the results
of this module are about triangles, not about covers.

## Implementation notes

Annihilation is phrased `r • 𝟙 X = 0` with `r : ℤ`, the idiom of
`StacksFrontier/AlgebraicGeometry/Algebraization/AnnihilatorTruncationReduction.lean`, whose
`Stacks.Algebraization.mul_smul_id_eq_zero_of_distinguished` — a scalar on the first term times a
scalar on the third term annihilates the middle term of a distinguished triangle — is the engine
of both inductions here and is *not* reproved.  Integer scalars are available in any preadditive
category through `CategoryTheory.preadditiveIntLinear`, so no `Linear R` hypothesis is needed.

The chain of a composition `X' = X_n ⟶ ⋯ ⟶ X_0 = X` of `α_p`-covers is read on the cohomological
side, where the arrows go the other way: `chainComp` composes a chain `Y 0 ⟶ Y 1 ⟶ ⋯` and its
`n`-th value is the arrow whose cone the induction bounds.  The induction is on (TR 4) in the
form of Mathlib's `CategoryTheory.Triangulated.someOctahedron`, which for `u₁₂ ≫ u₂₃ = u₁₃`
produces a distinguished triangle `Z₁₂ ⟶ Z₁₃ ⟶ Z₂₃` on the three cones; the base case is the
cone of an identity, which is a zero object.  The hypothesis and the conclusion quantify over
*every* distinguished triangle on the arrow in question rather than naming a cone, which is how
"the distinguished triangle" of the source is read: such a triangle is unique only up to
isomorphism, and the conclusion is invariant under isomorphism.

The kernel and cokernel bounds are stated element-wise on morphisms out of a fixed object `P`
rather than on a `kernel`/`cokernel` object, so that they need no limits in the ambient category
and apply directly to `H^i(X, -) = Hom(ℤ_X, (-)⟦i⟧)`.  Both are one application of
`Triangle.coyoneda_exact₂`, read at the two ends of a distinguished triangle; the kernel bound is
stated for the first two terms of the triangle it is applied to, so a user bounding the kernel of
`H^i(A) ⟶ H^i(B)` applies it to the inverse rotation `E⟦-1⟧ ⟶ A ⟶ B ⟶ E` rather than to the
triangle `A ⟶ B ⟶ E ⟶ A⟦1⟧` itself.  Stating it after the rotation keeps `Triangle.invRotate`,
whose second object is only definitionally `A`, out of the statement.

`pow_smul_id_eq_zero_of_isGE_of_isLE` and `pow_smul_eq_zero_of_isLE_of_isGE` are the
single-scalar form, for a general abelian category, of
`Stacks.Algebraization.prod_smul_id_eq_zero_of_isGE_of_isLE` and
`Stacks.Algebraization.prod_smul_eq_zero_of_isLE_of_isGE`, which are stated for
`D(ModuleCat A)` with one scalar per degree.  The generalisation is needed because the triangle
of [Stacks, Tag 07Q9] lives in a derived category of abelian sheaves on `X`, not of modules, and
the single scalar is what the source's `q` is.  Truncation is Mathlib's canonical t-structure
`DerivedCategory.TStructure.t` and "concentrated in degrees `≤ b`", "`≥ a`" are
`DerivedCategory.IsLE` and `DerivedCategory.IsGE`.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.26.4, Tag 07QA](https://stacks.math.columbia.edu/tag/07QA)
* [Stacks Project, Lemma 60.25.1, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 05QK](https://stacks.math.columbia.edu/tag/05QK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Triangulated

universe w v u

namespace Stacks.Triangulated

/-! ### The chain of covers, and (TR 4) -/

section Chain

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- The composite `Y 0 ⟶ Y n` of the first `n` arrows of a chain `Y 0 ⟶ Y 1 ⟶ Y 2 ⟶ ⋯`.  At
`n = 0` it is the identity of `Y 0`. -/
def chainComp (Y : ℕ → C) (g : ∀ i : ℕ, Y i ⟶ Y (i + 1)) : ∀ n : ℕ, Y 0 ⟶ Y n
  | 0 => 𝟙 (Y 0)
  | n + 1 => chainComp Y g n ≫ g n

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- The empty composite of a chain is the identity. -/
@[simp]
theorem chainComp_zero (Y : ℕ → C) (g : ∀ i : ℕ, Y i ⟶ Y (i + 1)) :
    chainComp Y g 0 = 𝟙 (Y 0) :=
  rfl

omit [Preadditive C] [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- One more stage of a chain is one more composition. -/
@[simp]
theorem chainComp_succ (Y : ℕ → C) (g : ∀ i : ℕ, Y i ⟶ Y (i + 1)) (n : ℕ) :
    chainComp Y g (n + 1) = chainComp Y g n ≫ g n :=
  rfl

/-- **The (TR 4) step of [Stacks, Tag 07Q9], for a single composition.**  Let `a` annihilate the
third term of every distinguished triangle on `g : Y₀ ⟶ Y₁` and let `b` annihilate the third term
of every distinguished triangle on `h : Y₁ ⟶ Y₂`.  Then `a * b` annihilates the third term of
every distinguished triangle on `g ≫ h`.

This is the octahedron axiom: a cone of `g ≫ h` sits in a distinguished triangle whose other two
terms are a cone of `g` and a cone of `h`, and annihilators of the outer terms of a distinguished
triangle multiply to an annihilator of the middle one,
`Stacks.Algebraization.mul_smul_id_eq_zero_of_distinguished`.  It is the binary form of
`pow_smul_id_eq_zero_of_chainComp` below, which it proves, and it is the form an induction over
`AlgebraicGeometry.IsAlphaPCoverComposite` consumes, that predicate's `comp` constructor
presenting a composition of two morphisms rather than an `ℕ`-indexed chain. -/
theorem mul_smul_id_eq_zero_of_comp [IsTriangulated C] {Y₀ Y₁ Y₂ : C}
    (g : Y₀ ⟶ Y₁) (h : Y₁ ⟶ Y₂) (a b : ℤ)
    (hg : ∀ (Z : C) (v : Y₁ ⟶ Z) (w : Z ⟶ Y₀⟦(1 : ℤ)⟧),
      Triangle.mk g v w ∈ distTriang C → a • 𝟙 Z = 0)
    (hh : ∀ (Z : C) (v : Y₂ ⟶ Z) (w : Z ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk h v w ∈ distTriang C → b • 𝟙 Z = 0)
    {Z : C} (v : Y₂ ⟶ Z) (w : Z ⟶ Y₀⟦(1 : ℤ)⟧)
    (hZ : Triangle.mk (g ≫ h) v w ∈ distTriang C) :
    (a * b) • 𝟙 Z = 0 := by
  obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := distinguished_cocone_triangle g
  obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := distinguished_cocone_triangle h
  have hO := someOctahedron (rfl : g ≫ h = g ≫ h) h₁₂ h₂₃ hZ
  exact Stacks.Algebraization.mul_smul_id_eq_zero_of_distinguished
    (Triangle.mk hO.m₁ hO.m₃ (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧')) hO.mem a b
    (hg Z₁₂ v₁₂ w₁₂ h₁₂) (hh Z₂₃ v₂₃ w₂₃ h₂₃)

/-- **The (TR 4) step of [Stacks, Tag 07Q9].**  Let `Y 0 ⟶ Y 1 ⟶ ⋯` be a chain in a triangulated
category and let `a` be a scalar annihilating the third term of every distinguished triangle on
every stage of the chain.  Then `a ^ n` annihilates the third term of every distinguished
triangle on the composite of the first `n` stages.

This is the reduction the source performs on a composition `X' = X_n ⟶ ⋯ ⟶ X_0 = X` of
`α_p`-covers: each stage contributes a cone annihilated by `p`, and the octahedron axiom
multiplies the annihilators, giving `p ^ n = q` for the composite. -/
theorem pow_smul_id_eq_zero_of_chainComp [IsTriangulated C]
    (Y : ℕ → C) (g : ∀ i : ℕ, Y i ⟶ Y (i + 1)) (a : ℤ)
    (hg : ∀ (i : ℕ) (Z : C) (v : Y (i + 1) ⟶ Z) (w : Z ⟶ (Y i)⟦(1 : ℤ)⟧),
      Triangle.mk (g i) v w ∈ distTriang C → a • 𝟙 Z = 0) (n : ℕ) :
    ∀ {Z : C} (v : Y n ⟶ Z) (w : Z ⟶ (Y 0)⟦(1 : ℤ)⟧),
      Triangle.mk (chainComp Y g n) v w ∈ distTriang C → a ^ n • 𝟙 Z = 0 := by
  induction n with
  | zero =>
    intro Z v w hZ
    have hiso : IsIso (Triangle.mk (chainComp Y g 0) v w).mor₁ := by
      change IsIso (chainComp Y g 0)
      rw [chainComp_zero]
      infer_instance
    have hzero : IsZero Z := Triangle.isZero₃_of_isIso₁ _ hZ hiso
    simpa using hzero.eq_of_src (𝟙 Z) 0
  | succ n ih =>
    intro Z v w hZ
    rw [pow_succ]
    exact mul_smul_id_eq_zero_of_comp (chainComp Y g n) (g n) (a ^ n) a
      (fun _ ↦ ih) (hg n) v w hZ

end Chain

/-! ### From an annihilator of the cone to annihilators of a kernel and a cokernel -/

section KernelCokernel

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The kernel bound of [Stacks, Tag 07QA].**  Let `W ⟶ A ⟶ B ⟶ W⟦1⟧` be a distinguished
triangle and let `r` annihilate every morphism `P ⟶ W`.  Then `r` annihilates every morphism
`P ⟶ A` which the map `A ⟶ B` kills, because such a morphism factors through `W ⟶ A`.

Applied to the inverse rotation `E⟦-1⟧ ⟶ A ⟶ B ⟶ E` of the triangle of [Stacks, Tag 07Q9], with
`P` the unit object, this says that a scalar annihilating `H^{i - 1}(X, E)` annihilates the
kernel of `H^i(X, A) ⟶ H^i(X, B)`. -/
theorem smul_eq_zero_of_comp_mor₂_eq_zero (T : Triangle C) (hT : T ∈ distTriang C) {P : C}
    (r : ℤ) (hr : ∀ u : P ⟶ T.obj₁, r • u = 0) (f : P ⟶ T.obj₂)
    (hf : f ≫ T.mor₂ = 0) :
    r • f = 0 := by
  obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ T hT f hf
  rw [hu, ← Linear.smul_comp, hr u, zero_comp]

/-- **The cokernel bound of [Stacks, Tag 07QA].**  Let `A ⟶ B ⟶ E ⟶ A⟦1⟧` be a distinguished
triangle and let `r` annihilate every morphism `P ⟶ E`.  Then `r` times any morphism `P ⟶ B`
factors through `A ⟶ B`.

Read with `P` the unit object and the triangle shifted, this says that `r` annihilates the
cokernel of `H^i(A) ⟶ H^i(B)`: the obstruction to lifting lies in `H^i(E)`. -/
theorem exists_comp_mor₁_eq_smul (T : Triangle C) (hT : T ∈ distTriang C) {P : C} (r : ℤ)
    (hr : ∀ u : P ⟶ T.obj₃, r • u = 0) (f : P ⟶ T.obj₂) :
    ∃ g : P ⟶ T.obj₁, r • f = g ≫ T.mor₁ := by
  refine Triangle.coyoneda_exact₂ T hT (r • f) ?_
  rw [Linear.smul_comp, hr (f ≫ T.mor₂)]

end KernelCokernel

/-! ### Annihilating a bounded object of a derived category -/

section Derived

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

omit [HasDerivedCategory 𝒜] in
/-- **Annihilators multiply along an exact sequence.**  If `X₁ ⟶ X₂ ⟶ X₃` is exact at `X₂` and
`a` annihilates `X₁` while `b` annihilates `X₃`, then `a * b` annihilates `X₂`.

This is the abelian half of the (TR 4) step of [Stacks, Tag 07Q9], which reads the conclusion on
*cohomology objects* rather than on objects of the triangulated category: `b • 1` kills the map to
`X₃`, hence factors through `ker(X₂ ⟶ X₃)`, which exactness presents as a quotient of `X₁` and on
which `a` therefore acts as zero. -/
theorem mul_smul_id_eq_zero_of_exact (S : ShortComplex 𝒜) (hS : S.Exact) (a b : ℤ)
    (ha : a • 𝟙 S.X₁ = 0) (hb : b • 𝟙 S.X₃ = 0) :
    (a * b) • 𝟙 S.X₂ = 0 := by
  have hz : (b • 𝟙 S.X₂) ≫ S.g = 0 := by
    rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id S.g, ← Linear.comp_smul, hb,
      comp_zero]
  have hlift : a • Limits.kernel.lift S.g S.f S.zero = 0 := by
    rw [← cancel_mono (Limits.kernel.ι S.g), Linear.smul_comp, Limits.kernel.lift_ι, zero_comp,
      ← Category.id_comp S.f, ← Linear.smul_comp, ha, zero_comp]
  have hK : a • 𝟙 (Limits.kernel S.g) = 0 := by
    have : Epi (Limits.kernel.lift S.g S.f S.zero) := S.exact_iff_epi_kernel_lift.1 hS
    rw [← cancel_epi (Limits.kernel.lift S.g S.f S.zero), Linear.comp_smul, Category.comp_id,
      hlift, comp_zero]
  calc (a * b) • 𝟙 S.X₂ = a • (b • 𝟙 S.X₂) := mul_smul a b _
    _ = a • (Limits.kernel.lift S.g (b • 𝟙 S.X₂) hz ≫ Limits.kernel.ι S.g) := by
        rw [Limits.kernel.lift_ι]
    _ = Limits.kernel.lift S.g (b • 𝟙 S.X₂) hz ≫ ((a • 𝟙 (Limits.kernel S.g)) ≫
          Limits.kernel.ι S.g) := by
        rw [Linear.smul_comp, Category.id_comp, Linear.comp_smul]
    _ = 0 := by rw [hK, zero_comp, comp_zero]

/-- **The (TR 4) step of [Stacks, Tag 07Q9] read on cohomology sheaves.**  Let `a` annihilate
every cohomology object of the third term of every distinguished triangle on `g : Y₀ ⟶ Y₁`, and
let `b` do the same for `h : Y₁ ⟶ Y₂`.  Then `a * b` annihilates every cohomology object of the
third term of every distinguished triangle on `g ≫ h`.

This, and not `mul_smul_id_eq_zero_of_comp`, is the statement [Stacks, Tag 07Q9] needs: its
conclusion is about the cohomology sheaves of the cone and not about the cone itself, and those
two are not interchangeable — a cone all of whose cohomology objects are killed by `a` need not be
killed by `a`.  The octahedron axiom still supplies the triangle relating the three cones, and the
cohomology long exact sequence of that triangle
(`CategoryTheory.Functor.homologySequence_exact₂`, for the homological functor
`DerivedCategory.Plus.homologyFunctor`) then feeds `mul_smul_id_eq_zero_of_exact`. -/
theorem mul_smul_id_homologyFunctor_eq_zero_of_comp
    [IsTriangulated (DerivedCategory.Plus 𝒜)]
    {Y₀ Y₁ Y₂ : DerivedCategory.Plus 𝒜} (g : Y₀ ⟶ Y₁) (h : Y₁ ⟶ Y₂) (a b : ℤ)
    (hg : ∀ (W : DerivedCategory.Plus 𝒜) (v : Y₁ ⟶ W) (w : W ⟶ Y₀⟦(1 : ℤ)⟧),
      Triangle.mk g v w ∈ distTriang (DerivedCategory.Plus 𝒜) → ∀ j : ℤ,
        a • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj W) = 0)
    (hh : ∀ (W : DerivedCategory.Plus 𝒜) (v : Y₂ ⟶ W) (w : W ⟶ Y₁⟦(1 : ℤ)⟧),
      Triangle.mk h v w ∈ distTriang (DerivedCategory.Plus 𝒜) → ∀ j : ℤ,
        b • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj W) = 0)
    {Z : DerivedCategory.Plus 𝒜} (v : Y₂ ⟶ Z) (w : Z ⟶ Y₀⟦(1 : ℤ)⟧)
    (hZ : Triangle.mk (g ≫ h) v w ∈ distTriang (DerivedCategory.Plus 𝒜)) (j : ℤ) :
    (a * b) • 𝟙 ((DerivedCategory.Plus.homologyFunctor 𝒜 j).obj Z) = 0 := by
  obtain ⟨Z₁₂, v₁₂, w₁₂, h₁₂⟩ := distinguished_cocone_triangle g
  obtain ⟨Z₂₃, v₂₃, w₂₃, h₂₃⟩ := distinguished_cocone_triangle h
  have hO := someOctahedron (rfl : g ≫ h = g ≫ h) h₁₂ h₂₃ hZ
  exact mul_smul_id_eq_zero_of_exact _
    ((DerivedCategory.Plus.homologyFunctor 𝒜 0).homologySequence_exact₂
      (Triangle.mk hO.m₁ hO.m₃ (w₂₃ ≫ v₁₂⟦(1 : ℤ)⟧')) hO.mem j)
    a b (hg Z₁₂ v₁₂ w₁₂ h₁₂ j) (hh Z₂₃ v₂₃ w₂₃ h₂₃ j)

/-- An object of `D(𝒜)` concentrated in the single degree `n` is annihilated by any scalar
annihilating its one cohomology object. -/
theorem smul_id_eq_zero_of_concentrated (r : ℤ) (n : ℤ) (X : DerivedCategory 𝒜) [X.IsLE n]
    [X.IsGE n] (h : r • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 n).obj X) = 0) :
    r • 𝟙 X = 0 := by
  refine hom_eq_zero_of_isLE_isGE X X n _ ?_
  rwa [Functor.map_zsmul, CategoryTheory.Functor.map_id]

/-- In a distinguished triangle `A ⟶ X ⟶ C ⟶ A⟦1⟧` of `D(𝒜)` with `A` concentrated in degrees `≤ b`
and `C` in degrees `≥ b + 1`, a scalar killing `ℋ^j(X)` for `j ≤ b` kills every `ℋ^i(A)`. -/
private theorem smul_id_homologyFunctor_obj₁_eq_zero (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) (r b : ℤ) [T.obj₁.IsLE b] [T.obj₃.IsGE (b + 1)]
    (hX : ∀ j : ℤ, j ≤ b → r • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj T.obj₂) = 0)
    (i : ℤ) : r • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 i).obj T.obj₁) = 0 := by
  by_cases hi : i ≤ b
  · have : IsIso ((DerivedCategory.homologyFunctor 𝒜 i).map T.mor₁) :=
      isIso_homology_mor₁ T hT i
        (DerivedCategory.isZero_of_isGE T.obj₃ (b + 1) i (by omega))
        (DerivedCategory.isZero_of_isGE T.obj₃ (b + 1) (i - 1) (by omega))
    exact Stacks.Algebraization.smul_id_eq_zero_of_iso r
      (asIso ((DerivedCategory.homologyFunctor 𝒜 i).map T.mor₁)) (hX i hi)
  · exact (DerivedCategory.isZero_of_isLE T.obj₁ b i (by omega)).eq_of_src _ _

/-- **The truncation induction.**  An object of `D(𝒜)` concentrated in degrees `a` through
`a + n`, all of whose cohomology objects are annihilated by `r`, is annihilated by `r ^ (n + 1)`.

This is the derived-category form of the filtration argument [Stacks, Tag 07QA] runs through the
spectral sequence `H^a(ℋ^b(E)) ⇒ H^{a + b}(E)`: `n + 1` degrees contribute, each one factor
of `r`. -/
theorem pow_smul_id_eq_zero_of_isGE_of_isLE (r : ℤ) (a : ℤ) (n : ℕ) (X : DerivedCategory 𝒜)
    [X.IsGE a] [X.IsLE (a + n)]
    (hX : ∀ i : ℤ, r • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 i).obj X) = 0) :
    r ^ (n + 1) • 𝟙 X = 0 := by
  induction n generalizing X with
  | zero =>
    have : X.IsLE a := by simpa using (inferInstance : X.IsLE (a + (0 : ℕ)))
    simpa using smul_id_eq_zero_of_concentrated r a X (hX a)
  | succ n ih =>
    set b : ℤ := a + (n : ℤ) with hb
    set T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj X
    have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1) (by omega) X
    have hXle : X.IsLE (b + 1) := by
      have := (inferInstance : X.IsLE (a + ((n + 1 : ℕ) : ℤ)))
      refine DerivedCategory.TStructure.t.isLE_of_le X (a + ((n + 1 : ℕ) : ℤ)) (b + 1) ?_
      push_cast [hb]
      omega
    have h₁ge : T.obj₁.IsGE a := by
      change ((DerivedCategory.TStructure.t.truncLE b).obj X).IsGE a
      infer_instance
    have h₁le : T.obj₁.IsLE (a + n) := by
      change ((DerivedCategory.TStructure.t.truncLE b).obj X).IsLE b
      infer_instance
    have h₃ge : T.obj₃.IsGE (b + 1) := by
      change ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X).IsGE (b + 1)
      infer_instance
    have h₃le : T.obj₃.IsLE (b + 1) := by
      change ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj X).IsLE (b + 1)
      infer_instance
    have hleft : r ^ (n + 1) • 𝟙 T.obj₁ = 0 := by
      exact ih T.obj₁ (smul_id_homologyFunctor_obj₁_eq_zero T hT r b fun j _ => hX j)
    have hright : r • 𝟙 T.obj₃ = 0 := by
      refine smul_id_eq_zero_of_concentrated r (b + 1) T.obj₃ ?_
      have : IsIso ((DerivedCategory.homologyFunctor 𝒜 (b + 1)).map T.mor₂) :=
        isIso_homology_mor₂ T hT (b + 1)
          (DerivedCategory.isZero_of_isLE T.obj₁ b (b + 1) (by omega))
          (DerivedCategory.isZero_of_isLE T.obj₁ b (b + 1 + 1) (by omega))
      exact Stacks.Algebraization.smul_id_eq_zero_of_iso r
        (asIso ((DerivedCategory.homologyFunctor 𝒜 (b + 1)).map T.mor₂)).symm (hX (b + 1))
    rw [pow_succ r (n + 1)]
    exact Stacks.Algebraization.mul_smul_id_eq_zero_of_distinguished T hT _ _ hleft hright

/-- **The bound on morphisms.**  Let `Q` be an object of `D(𝒜)` concentrated in degrees `≥ a`
whose cohomology objects `H^j(Q)` are annihilated by `r` for every `j ≤ b`, and let `P` be
concentrated in degrees `≤ b`.  Then `r ^ ((b - a).toNat + 1)` annihilates every morphism
`P ⟶ Q`.

With `P` the unit object and `Q = E⟦i⟧` this is the bound `q ^ (i + 1)` on `H^i(X, E)` that
[Stacks, Tag 07QA] feeds into the long exact sequence. -/
theorem pow_smul_eq_zero_of_isLE_of_isGE (r : ℤ) (a b : ℤ) (Q : DerivedCategory 𝒜) [Q.IsGE a]
    (hQ : ∀ j : ℤ, j ≤ b → r • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj Q) = 0)
    (P : DerivedCategory 𝒜) [P.IsLE b] (g : P ⟶ Q) :
    r ^ ((b - a).toNat + 1) • g = 0 := by
  set T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) (by omega)).obj Q
  have hT := DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1) (by omega) Q
  have h₁le : T.obj₁.IsLE b := by
    change ((DerivedCategory.TStructure.t.truncLE b).obj Q).IsLE b
    infer_instance
  have h₁ge : T.obj₁.IsGE a := by
    change ((DerivedCategory.TStructure.t.truncLE b).obj Q).IsGE a
    infer_instance
  have h₃ge : T.obj₃.IsGE (b + 1) := by
    change ((DerivedCategory.TStructure.t.truncGE (b + 1)).obj Q).IsGE (b + 1)
    infer_instance
  obtain ⟨k, hk⟩ := Triangle.coyoneda_exact₂ T hT g
    (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ b (b + 1) (by omega)
      inferInstance h₃ge)
  have hkill : r ^ ((b - a).toNat + 1) • 𝟙 T.obj₁ = 0 := by
    by_cases hab : a ≤ b
    · have hle : T.obj₁.IsLE (a + ((b - a).toNat : ℤ)) := by
        refine DerivedCategory.TStructure.t.isLE_of_le T.obj₁ b (a + ((b - a).toNat : ℤ)) ?_
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      exact pow_smul_id_eq_zero_of_isGE_of_isLE r a (b - a).toNat T.obj₁
        (smul_id_homologyFunctor_obj₁_eq_zero T hT r b hQ)
    · exact (DerivedCategory.TStructure.t.isZero T.obj₁ b a (by omega)).eq_of_src _ _
  have hk0 : r ^ ((b - a).toNat + 1) • k = 0 := by
    simpa only [Linear.comp_smul, Category.comp_id, comp_zero] using
      congrArg (fun q => k ≫ q) hkill
  rw [hk]
  calc
    r ^ ((b - a).toNat + 1) • (k ≫ T.mor₁) =
        (r ^ ((b - a).toNat + 1) • k) ≫ T.mor₁ := by rw [Linear.smul_comp]
    _ = 0 := by rw [hk0, zero_comp]

/-- **The vanishing `ℋ^{a - 1}(E) = 0` of the cone, from injectivity on `ℋ^a`.**  Let
`A ⟶ B ⟶ E ⟶ A⟦1⟧` be distinguished in `D(𝒜)` with `B` concentrated in degrees `≥ a` and `E`
concentrated in degrees `≥ a - 1`.  If `ℋ^a(A) ⟶ ℋ^a(B)` is a monomorphism then `E` is
concentrated in degrees `≥ a`.

This is the step [Stacks, Tag 07QA] needs and does not state: its cokernel exponent is the
source's `q ^ (i + 1)` only because `ℋ^{-1}(E)` vanishes, and the filtration count over the
degrees `-1, 0, …, i` would otherwise give `q ^ (i + 2)`.  For the triangle of
[Stacks, Tag 07Q9] the hypothesis is injectivity of `ℋ^0(Ru_{X/S, *}ℱ) ⟶ ℋ^0(f_*Ru_{X'/S, *}ℱ')`,
which comes from injectivity of the adjunction unit `ℱ ⟶ f_{cris, *}f_cris^*ℱ` for an iterated
`α_p`-cover: the direct image `u_{X/S, *}` is left exact and so preserves that monomorphism.
So the vanishing is a theorem about the geometry and not a hypothesis of the source. -/
theorem isGE_obj₃_of_mono_homologyMap (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) (a : ℤ) [T.obj₂.IsGE a] [T.obj₃.IsGE (a - 1)]
    (hmono : Mono ((DerivedCategory.homologyFunctor 𝒜 a).map T.mor₁)) :
    T.obj₃.IsGE a := by
  rw [DerivedCategory.isGE_iff]
  intro j hj
  by_cases hj' : j < a - 1
  · exact DerivedCategory.isZero_of_isGE T.obj₃ (a - 1) j hj'
  · have hja : j + 1 = a := by omega
    exact (DerivedCategory.HomologySequence.exact₃ T hT j a hja).isZero_X₂
      ((DerivedCategory.isZero_of_isGE T.obj₂ a j hj).eq_of_src _ _)
      ((DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT j a hja).1 hmono)

/-- **The cone of a map between objects concentrated in degrees `≥ a` is concentrated in degrees
`≥ a - 1`.**  Rotate the triangle: `E` sits between `B` and `A⟦1⟧`, the first concentrated in
degrees `≥ a` and the second in degrees `≥ a - 1`. -/
theorem isGE_obj₃_sub_one (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) (a : ℤ) [T.obj₁.IsGE a] [T.obj₂.IsGE a] :
    T.obj₃.IsGE (a - 1) :=
  DerivedCategory.TStructure.t.isGE₂ T.rotate (rot_of_distTriang T hT) (a - 1)
    (DerivedCategory.TStructure.t.isGE_of_ge T.obj₂ (a - 1) a (by omega))
    (DerivedCategory.TStructure.t.isGE_shift T.obj₁ a 1 (a - 1) (by omega))

/-- **The kernel bound of [Stacks, Tag 07QA], with the exponent.**  Let
`W ⟶ A ⟶ B ⟶ W⟦1⟧` be distinguished in `D(𝒜)` with `W` concentrated in degrees `≥ a` and all
its cohomology objects in degrees `≤ b` annihilated by `r`, and let `P` be concentrated in
degrees `≤ b`.  Then `r ^ ((b - a).toNat + 1)` annihilates every morphism `P ⟶ A` killed by
`A ⟶ B`.

Taking `a = 0`, `b = i` and `W = E⟦-1⟧` for the third term `E` of the triangle of
[Stacks, Tag 07Q9], the exponent is `i + 1` and the conclusion is that `q ^ (i + 1)` annihilates
the kernel of `H^i(X, Ru_{X/S, *}ℱ) ⟶ H^i(X, f_*Ru_{X'/S, *}ℱ')`. -/
theorem pow_smul_eq_zero_of_comp_mor₂_eq_zero (r : ℤ) (a b : ℤ)
    (T : Triangle (DerivedCategory 𝒜)) (hT : T ∈ distTriang (DerivedCategory 𝒜))
    [T.obj₁.IsGE a]
    (hW : ∀ j : ℤ, j ≤ b → r • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj T.obj₁) = 0)
    (P : DerivedCategory 𝒜) [P.IsLE b] (f : P ⟶ T.obj₂) (hf : f ≫ T.mor₂ = 0) :
    r ^ ((b - a).toNat + 1) • f = 0 :=
  smul_eq_zero_of_comp_mor₂_eq_zero T hT _
    (fun u => pow_smul_eq_zero_of_isLE_of_isGE r a b T.obj₁ hW P u) f hf

/-- **The cokernel bound of [Stacks, Tag 07QA], with the exponent.**  Let
`A ⟶ B ⟶ E ⟶ A⟦1⟧` be distinguished in `D(𝒜)` with `E` concentrated in degrees `≥ a` and all
its cohomology objects in degrees `≤ b` annihilated by `r`, and let `P` be concentrated in
degrees `≤ b`.  Then `r ^ ((b - a).toNat + 1)` times any morphism `P ⟶ B` factors through
`A ⟶ B`.

Taking `a = 0` and `b = i` for the triangle of [Stacks, Tag 07Q9], the exponent is `i + 1` and
the conclusion is that `q ^ (i + 1)` annihilates the cokernel of
`H^i(X, Ru_{X/S, *}ℱ) ⟶ H^i(X, f_*Ru_{X'/S, *}ℱ')`. -/
theorem exists_comp_mor₁_eq_pow_smul (r : ℤ) (a b : ℤ)
    (T : Triangle (DerivedCategory 𝒜)) (hT : T ∈ distTriang (DerivedCategory 𝒜))
    [T.obj₃.IsGE a]
    (hE : ∀ j : ℤ, j ≤ b → r • 𝟙 ((DerivedCategory.homologyFunctor 𝒜 j).obj T.obj₃) = 0)
    (P : DerivedCategory 𝒜) [P.IsLE b] (f : P ⟶ T.obj₂) :
    ∃ g : P ⟶ T.obj₁, r ^ ((b - a).toNat + 1) • f = g ≫ T.mor₁ :=
  exists_comp_mor₁_eq_smul T hT _
    (fun u => pow_smul_eq_zero_of_isLE_of_isGE r a b T.obj₃ hE P u) f

end Derived

end Stacks.Triangulated

end
