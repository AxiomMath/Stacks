module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCover

/-!
# The degree of an `α_p`-cover, and of a composition of them

Let `p` be a prime.  An `α_p`-cover `X' = Spec(C[z]/(z ^ p - c)) ⟶ Spec(C) = X` is finite locally
free of degree `p`, and a composition of `n` of them is finite locally free of degree `p ^ n`.
Hence an iterated `α_p`-cover is, locally on the target, finite locally free of degree a power of
`p`.  This is the unnumbered remark of [Stacks, Section 60.25, Tag 07PZ] that sits between
Lemma 60.25.3 and Lemma 60.25.4 — "an iterated `α_p`-cover `X' → X` is finite locally free, hence
if `X` is connected the degree of `X' → X` is constant and is a power of `p`" — and it is the step
which lets the exponent `p ^ n` that the chain `X' = X_n ⟶ ⋯ ⟶ X_0 = X` produces be read as the
constant degree `q` which [Stacks, Tag 07Q9] states its conclusion with.

The vocabulary is `StacksFrontier/AlgebraicGeometry/Crystalline/AlphaPCover.lean`:
`AlgebraicGeometry.IsAlphaPCover`, `AlgebraicGeometry.IsAlphaPCoverComposite`,
`AlgebraicGeometry.IsIteratedAlphaPCover` and `AlgebraicGeometry.HasConstantDegree`.  Before this
module nothing in the library related any of the first three to the fourth: `HasConstantDegree`
occurred only as a hypothesis of `...SmallSite.Statement07Q9` and as the conclusion of
`AlgebraicGeometry.hasConstantDegree_relativeFrobenius`, which computes the degree of the relative
Frobenius of a smooth morphism directly from a chart rather than through the covers.

## Main definitions

* `AlgebraicGeometry.alphaPTowerComp` — the composite `X_n ⟶ X_0` of the first `n` stages of a
  tower `⋯ ⟶ X_1 ⟶ X_0`.  This is the explicit presentation of the chain
  `X' = X_n ⟶ ⋯ ⟶ X_0 = X` that [Stacks, Tag 07Q9] reduces to, and it is what makes the exponent
  `n` of the degree `p ^ n` the *same* `n` as the number of stages — which the existential of
  `exists_hasFiniteBasis_of_isAlphaPCoverComposite` does not.

## Main results

* `AlgebraicGeometry.hasFiniteBasis_alphaPCoverMap` — the local model `C[z]/(z ^ p - c)` of an
  `α_p`-cover is free of rank `p` on the powers of the adjoined root, read on global sections of
  spectra.
* `AlgebraicGeometry.hasFiniteBasis_of_isAlphaPCover` — **an `α_p`-cover is free of rank `p` on
  global sections**, for `p ≠ 0`.
* `AlgebraicGeometry.exists_hasFiniteBasis_of_isAlphaPCoverComposite` — **a composition of
  `α_p`-covers is free of rank `p ^ n` on global sections**, with `n` the length of the
  composition.
* `AlgebraicGeometry.exists_hasConstantDegree_of_isAlphaPCoverComposite` — over an affine target a
  composition of `α_p`-covers has constant degree `p ^ n`.
* `AlgebraicGeometry.exists_hasFiniteBasis_app_of_isIteratedAlphaPCover` — **an iterated
  `α_p`-cover is, around every point of the target, free of rank a power of `p`.**
* `AlgebraicGeometry.hasFiniteBasis_alphaPTowerComp`,
  `AlgebraicGeometry.isAlphaPCoverComposite_alphaPTowerComp` and
  `AlgebraicGeometry.hasConstantDegree_alphaPTowerComp` — **for a tower presented explicitly, the
  composite of `n` stages is a composition of `α_p`-covers of degree `p ^ n` with that same
  `n`**, over an affine target.
* `AlgebraicGeometry.isAffine_target_of_isAlphaPCover` and
  `AlgebraicGeometry.isAffine_target_of_isAlphaPCoverComposite` — the target of an `α_p`-cover is
  affine, and so is the target of a composition of `α_p`-covers with affine source; the
  companions of `AlgebraicGeometry.isAffine_source_of_isAlphaPCover` and
  `AlgebraicGeometry.isAffine_source_of_isAlphaPCoverComposite`.

## Implementation notes

The degree is tracked through `AlgebraicGeometry.HasFiniteBasis`, the datum of a basis indexed by
`Fin n`, rather than through `Module.rank` directly.  That apparatus is not new: it was written
for `AlgebraicGeometry.hasConstantDegree_relativeFrobenius` and lived as a block of `private`
declarations in
`StacksFrontier/AlgebraicGeometry/Crystalline/FrobeniusAlphaPCover.lean`; this module
uses it, so those declarations are no longer private.  They have nothing to do with the Frobenius
and would be better placed in a module of their own, next to `AlphaPCover.lean`; that move is left
alone here because it would rewrite a file of a thousand lines for no mathematical gain.

The point of carrying a basis rather than a rank is that a basis composes and transports with no
hypothesis on the base ring, whereas `Module.rank` records the rank `p` only over a nontrivial
ring — the zero ring is allowed by `IsAlphaPCover`, and `Spec` of it is empty, where every rank is
zero.  The passage to `HasConstantDegree`, which is a statement about `Module.rank`, therefore
happens once and at a point: an open containing a point of the target is nonempty, which is what
makes its ring of sections nontrivial.

## What is and is not proved

What is proved is the list above, unconditionally.  The rank statements ask `p ≠ 0`, which is the
source's hypothesis — it takes `p` to be a prime; for `p = 0` the local model is `C[z]/(1 - c)`,
which is not free of rank `0`, so they are false without it.  The two affineness statements need
no hypothesis on `p`.

**No tag attribute is placed.**  The remark these results formalise carries no tag of its own in
the source; the enclosing [Stacks, Tag 07PZ] is a section.

The one step between this module and the use [Stacks, Tag 07Q9] makes of the remark — that the
power of `p` found around a point agrees with a *given* constant degree `q` — is
`AlgebraicGeometry.eq_of_hasConstantDegree_of_hasFiniteBasis` of
`Crystalline/AlphaPCoverLocalChain07Q9.lean`.  `HasConstantDegree f q` produces an affine open `V`
containing the point on which the rank is `q`, a chain of `α_p`-extensions produces a possibly
different open `U` on which the rank is `p ^ n`, and the two ranks are compared on a common
smaller affine open.  `AlgebraicGeometry.exists_alphaPChain_and_eq_pow_of_hasConstantDegree`
there is the resulting local normal form: around every point an affine open over which `f` is a
chain of `n` successive `α_p`-extensions, with `q = p ^ n`.

## Where [Stacks, Tag 07Q9] is proved

[Stacks, Tag 07Q9] has a single conclusion: for an iterated `α_p`-cover `f : X' ⟶ X` of constant
degree `q` over `S₀` and a crystal `ℱ` in quasi-coherent modules on `Cris(X/S)`, the third term
`E` of the distinguished triangle

`Ru_{X/S, *}ℱ ⟶ f_*Ru_{X'/S, *}ℱ' ⟶ E ⟶ Ru_{X/S, *}ℱ[1]`,  `ℱ' = f_cris^*ℱ`,

has cohomology sheaves annihilated by `q`.  It is
`Crystalline.GlobalCrystallineSituation.SmallSite.annihilation07Q9_of_isIteratedAlphaPCover` of
`SmallSite/AlphaPCover07Q9Main.lean`, which carries the tag, under the source's hypotheses.  Its
proof uses the following.

1. *The terms and the comparison map.*  `Ru_{X/S, *}` is
   `...SmallSite.derivedZariskiDirectImageFunctor`, `f_{Zar, *}` is
   `...SmallSite.zariskiPushforward`, `f_cris^{-1}` is `...SmallSite.crisInverseImage`, the
   comparison is `...SmallSite.derivedZariskiComparison`, and the commutation of the square of
   topoi it needs is the proved `...SmallSite.crisZariskiSquare`.
2. *The reduction to chain opens.*  The local normal form above makes the affine opens over which
   `f` is a chain of `n` successive `α_p`-extensions with `q = p ^ n` a basis of `X`
   (`...SmallSite.isBasis_isChainOpen07Q9` of `SmallSite/AlphaPCoverBasis07Q9.lean`), and over a
   basis the conclusion is local (`...SmallSite.annihilation07Q9_of_chainConeAnnihilation`).  The
   library also has the triangulated route through the chain one stage at a time:
   `...SmallSite.annihilation07Q9_chainComp` of `SmallSite/AlphaPCoverTowerAnnihilation.lean`
   turns a cone whose cohomology sheaves are annihilated by `p` at every stage into one whose
   cohomology sheaves are annihilated by `p ^ n` for the composite, and the derived composition
   functoriality of the comparison map it needs is `...SmallSite.derivedZariskiComparison_comp'`
   of `SmallSite/DerivedCrisZariskiComposition.lean`, with no hypotheses.  The degree bookkeeping
   `p ^ n` with the same `n` as the number of stages is `hasConstantDegree_alphaPTowerComp` below.
3. *The local step over a chain open.*  `...SmallSite.chainConeAnnihilation_isChainOpen07Q9` of
   `SmallSite/AlphaPCover07Q9Main.lean` computes both crystalline cohomologies over a chain open
   by the de Rham complexes of the divided power envelopes, by [Stacks, Proposition 60.21.3,
   Tag 07LG] — `...SmallSite.crystalPairDeRhamComplex_computesCohomology` of
   `SmallSite/CrystalDeRhamComputesCohomology.lean` — and kills the cone of the row-zero map by
   `p ^ n`, the row-zero map being the composite of the `n` maps of [Stacks, Tag 07N1], each split
   up to `p` (`...SmallSite.smul_id_homology_chainRowZero07Q9` of
   `SmallSite/ChainRowZero07Q9.lean`).  [Stacks, Tag 07N1] for the completed envelope `D ⟶ D'`
   in Situation 07MD is
   `Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension_situation` of
   `Differentials/PthRootCompletedSituation.lean`.
declaration.

## References

* [Stacks Project, Section 60.25, Tag 07PZ](https://stacks.math.columbia.edu/tag/07PZ)
* [Stacks Project, Lemma 60.25.4, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Lemma 60.25.6, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- **The local model of an `α_p`-cover is free of rank `p`**, read on global sections: the ring
map `C ⟶ Γ(Spec(C[z]/(z ^ p - c)), ⊤)` admits a basis of `p` elements, the powers of the adjoined
root.  For `p = 0` the polynomial `z ^ 0 - c = 1 - c` is not monic of degree `0` in the relevant
sense and the statement fails, so `p ≠ 0` is asked for. -/
theorem hasFiniteBasis_alphaPCoverMap (p : ℕ) (hp : p ≠ 0) (C : Type u) [CommRing C] (c : C) :
    HasFiniteBasis (alphaPCoverMap p C c).appTop.hom p :=
  hasFiniteBasis_spec_appTop _ p (hasFiniteBasis_adjoinRoot_X_pow_sub_C C p hp c)

/-- **An `α_p`-cover is free of rank `p` on global sections.**  By definition it is identified
with `Spec(C[z]/(z ^ p - c)) ⟶ Spec(C)` by isomorphisms of its source and of its target, and a
basis of finite rank transports along such a square. -/
theorem hasFiniteBasis_of_isAlphaPCover (p : ℕ) (hp : p ≠ 0) {X' X : Scheme.{u}} {f : X' ⟶ X}
    (hf : IsAlphaPCover p f) : HasFiniteBasis f.appTop.hom p := by
  obtain ⟨C, hC, -, c, e, e', he⟩ := hf
  let := hC
  exact hasFiniteBasis_appTop_of_iso f (alphaPCoverMap p C c) e' e he p
    (hasFiniteBasis_alphaPCoverMap p hp C c)

/-- An isomorphism of schemes is free of rank `1` on global sections. -/
private theorem hasFiniteBasis_appTop_one_of_isIso {X' X : Scheme.{u}} (f : X' ⟶ X) [IsIso f] :
    HasFiniteBasis f.appTop.hom 1 :=
  have : IsIso f.appTop := inferInstanceAs (IsIso (Scheme.Γ.map f.op))
  hasFiniteBasis_of_bijective f.appTop.hom (ConcreteCategory.bijective_of_isIso f.appTop)

/-- Ranks on global sections multiply along a composite of morphisms of schemes. -/
private theorem hasFiniteBasis_appTop_comp {X'' X' X : Scheme.{u}} {g : X'' ⟶ X'} {h : X' ⟶ X}
    {m n : ℕ} (hh : HasFiniteBasis h.appTop.hom m) (hg : HasFiniteBasis g.appTop.hom n) :
    HasFiniteBasis (g ≫ h).appTop.hom (m * n) := by
  rw [Scheme.Hom.comp_appTop]
  exact hasFiniteBasis_comp _ _ m n hh hg

/-- Free of rank `n` on global sections over an affine target gives constant degree `n`. -/
private theorem hasConstantDegree_of_hasFiniteBasis_appTop {X' X : Scheme.{u}} [IsAffine X]
    {f : X' ⟶ X} {n : ℕ} (hn : HasFiniteBasis f.appTop.hom n) : HasConstantDegree f n := by
  intro x
  refine ⟨⊤, isAffineOpen_top X, trivial, ?_⟩
  have : Nonempty (↑(⊤ : X.Opens) : Type u) := ⟨⟨x, trivial⟩⟩
  have hn' : HasFiniteBasis (f.app ⊤).hom n := hn
  let _ := (f.app ⊤).hom.toAlgebra
  obtain ⟨b⟩ := hn'
  exact ⟨Module.Free.of_basis b, by simpa using rank_eq_card_basis b⟩

/-- **A composition of `α_p`-covers is free of rank `p ^ n` on global sections**, one factor of
`p` for each stage of the composition.  The base case of `IsAlphaPCoverComposite` is an
isomorphism, whose exponent is `n = 0`; each further stage multiplies the rank by `p` through
`hasFiniteBasis_comp`. -/
theorem exists_hasFiniteBasis_of_isAlphaPCoverComposite (p : ℕ) (hp : p ≠ 0)
    {X' X : Scheme.{u}} {f : X' ⟶ X} (hf : IsAlphaPCoverComposite p f) :
    ∃ n : ℕ, HasFiniteBasis f.appTop.hom (p ^ n) := by
  induction hf with
  | of_isIso e he =>
    refine ⟨0, ?_⟩
    let := he
    simpa using hasFiniteBasis_appTop_one_of_isIso e
  | @comp X'' X' X g h hg hh ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [pow_succ]
    exact hasFiniteBasis_appTop_comp hn (hasFiniteBasis_of_isAlphaPCover p hp hg)

/-- **The target of an `α_p`-cover is affine**: it is isomorphic to the spectrum of `C`.  The
companion of `AlgebraicGeometry.isAffine_source_of_isAlphaPCover`. -/
theorem isAffine_target_of_isAlphaPCover {X' X : Scheme.{u}} {f : X' ⟶ X} (p : ℕ)
    (hf : IsAlphaPCover p f) : IsAffine X := by
  obtain ⟨C, hC, -, c, e, -, -⟩ := hf
  let := hC
  exact IsAffine.of_isIso e.hom

/-- **The target of a composition of `α_p`-covers with affine source is affine.**  The companion
of `AlgebraicGeometry.isAffine_source_of_isAlphaPCoverComposite`, and the reason the
affineness hypothesis of `exists_hasConstantDegree_of_isAlphaPCoverComposite` costs nothing in
the situation of [Stacks, Tag 07Q9]: the target of an `α_p`-cover is the spectrum of `C`, so
every intermediate scheme of a chain with at least one stage is affine, and the chain's base case
is an isomorphism onto the target. -/
theorem isAffine_target_of_isAlphaPCoverComposite (p : ℕ) {X' X : Scheme.{u}} {f : X' ⟶ X}
    (hf : IsAlphaPCoverComposite p f) : IsAffine X' → IsAffine X := by
  induction hf with
  | of_isIso e he =>
    intro h'
    let := he
    let := h'
    exact IsAffine.of_isIso (inv e)
  | @comp X'' X' X g h hg hh ih =>
    intro _
    exact ih (isAffine_target_of_isAlphaPCover p hg)

/-- **Over an affine target a composition of `α_p`-covers has constant degree `p ^ n`.**  The
basis of `exists_hasFiniteBasis_of_isAlphaPCoverComposite` lives over the whole of the affine
target, which is the affine open `HasConstantDegree` asks for at every point, and the rank of a
free module on a basis indexed by `Fin (p ^ n)` is `p ^ n` because a point of the target makes
the ring of sections nontrivial. -/
theorem exists_hasConstantDegree_of_isAlphaPCoverComposite (p : ℕ) (hp : p ≠ 0)
    {X' X : Scheme.{u}} [IsAffine X] {f : X' ⟶ X} (hf : IsAlphaPCoverComposite p f) :
    ∃ n : ℕ, HasConstantDegree f (p ^ n) := by
  obtain ⟨n, hn⟩ := exists_hasFiniteBasis_of_isAlphaPCoverComposite p hp hf
  exact ⟨n, hasConstantDegree_of_hasFiniteBasis_appTop hn⟩

/-- **An iterated `α_p`-cover is free of rank a power of `p` around every point of the target.**
By definition `f` is, on some open neighbourhood `U` of the given point, a composition of
`α_p`-covers; the rank of the composition is `p ^ n` by
`exists_hasFiniteBasis_of_isAlphaPCoverComposite`, and a basis over the whole of a restriction is
a basis over the open it restricts to.

This is the remark of [Stacks, Section 60.25] in the form [Stacks, Tag 07Q9] uses it: the exponent
`p ^ n` that the chain `X' = X_n ⟶ ⋯ ⟶ X_0 = X` contributes to the (TR 4) step is a degree of
`f` over `U`.  Matching it with a *given* constant degree `q` is the local constancy of the
degree, `AlgebraicGeometry.eq_of_hasConstantDegree_of_hasFiniteBasis` of
`Crystalline/AlphaPCoverLocalChain07Q9.lean`; see the module documentation. -/
theorem exists_hasFiniteBasis_app_of_isIteratedAlphaPCover (p : ℕ) (hp : p ≠ 0)
    {X' X : Scheme.{u}} {f : X' ⟶ X} (hf : IsIteratedAlphaPCover p f) (x : X) :
    ∃ (U : X.Opens) (n : ℕ), x ∈ U ∧ HasFiniteBasis (f.app U).hom (p ^ n) := by
  obtain ⟨U, hx, hU⟩ := hf.2 x
  obtain ⟨n, hn⟩ := exists_hasFiniteBasis_of_isAlphaPCoverComposite p hp hU
  exact ⟨U, n, hx, hasFiniteBasis_app_of_morphismRestrict f U (p ^ n) hn⟩

/-! ### The tower presented explicitly -/

/-- **The composite `X_n ⟶ X_0` of the first `n` stages of a tower `⋯ ⟶ X_1 ⟶ X_0`.**  At `n = 0`
it is the identity of `X_0`.

`IsAlphaPCoverComposite` is a `Prop`-valued inductive predicate, so the number of stages in a
derivation of it cannot be read off as a natural number; the degree statements above therefore
assert only that *some* power of `p` is the degree.  A tower given as a family carries its length
as data, which is what lets `hasFiniteBasis_alphaPTowerComp` below state the degree with the same
`n` that [Stacks, Tag 07Q9]'s (TR 4) step uses as its exponent — the `n` of
`Crystalline.GlobalCrystallineSituation.SmallSite.annihilation07Q9_chainComp`.  The arrows run
down the tower, `X_{i + 1} ⟶ X_i`, as the source writes them. -/
def alphaPTowerComp (Z : ℕ → Scheme.{u}) (g : ∀ i : ℕ, Z (i + 1) ⟶ Z i) : ∀ n : ℕ, Z n ⟶ Z 0
  | 0 => 𝟙 (Z 0)
  | n + 1 => g n ≫ alphaPTowerComp Z g n

/-- The empty tower composes to the identity. -/
@[simp]
theorem alphaPTowerComp_zero (Z : ℕ → Scheme.{u}) (g : ∀ i : ℕ, Z (i + 1) ⟶ Z i) :
    alphaPTowerComp Z g 0 = 𝟙 (Z 0) :=
  rfl

/-- One more stage of a tower is one more composition, on the left. -/
@[simp]
theorem alphaPTowerComp_succ (Z : ℕ → Scheme.{u}) (g : ∀ i : ℕ, Z (i + 1) ⟶ Z i) (n : ℕ) :
    alphaPTowerComp Z g (n + 1) = g n ≫ alphaPTowerComp Z g n :=
  rfl

/-- **The composite of `n` stages of a tower of `α_p`-covers is free of rank `p ^ n` on global
sections**, one factor of `p` for each stage.  This is
`exists_hasFiniteBasis_of_isAlphaPCoverComposite` with the exponent pinned to the length of the
tower instead of being produced existentially. -/
theorem hasFiniteBasis_alphaPTowerComp (p : ℕ) (hp : p ≠ 0) (Z : ℕ → Scheme.{u})
    (g : ∀ i : ℕ, Z (i + 1) ⟶ Z i) (hg : ∀ i : ℕ, IsAlphaPCover p (g i)) (n : ℕ) :
    HasFiniteBasis (alphaPTowerComp Z g n).appTop.hom (p ^ n) := by
  induction n with
  | zero =>
    have : IsIso (alphaPTowerComp Z g 0) := by rw [alphaPTowerComp_zero]; infer_instance
    simpa using hasFiniteBasis_appTop_one_of_isIso (alphaPTowerComp Z g 0)
  | succ n ih =>
    rw [alphaPTowerComp_succ, pow_succ]
    exact hasFiniteBasis_appTop_comp ih (hasFiniteBasis_of_isAlphaPCover p hp (hg n))

/-- **The composite of `n` stages of a tower of `α_p`-covers is a composition of `α_p`-covers**,
so every statement about `IsAlphaPCoverComposite` applies to it. -/
theorem isAlphaPCoverComposite_alphaPTowerComp (p : ℕ) (Z : ℕ → Scheme.{u})
    (g : ∀ i : ℕ, Z (i + 1) ⟶ Z i) (hg : ∀ i : ℕ, IsAlphaPCover p (g i)) (n : ℕ) :
    IsAlphaPCoverComposite p (alphaPTowerComp Z g n) := by
  induction n with
  | zero => exact .of_isIso _ (by rw [alphaPTowerComp_zero]; infer_instance)
  | succ n ih => exact .comp (hg n) ih

/-- **Over an affine base the composite of `n` stages of a tower of `α_p`-covers has constant
degree `p ^ n`.**  The basis of `hasFiniteBasis_alphaPTowerComp` lives over the whole of the
affine target, which is the affine open `HasConstantDegree` asks for at every point, and the rank
of a free module on a basis indexed by `Fin (p ^ n)` is `p ^ n` because a point of the target
makes the ring of sections nontrivial.

This is the degree `q` that [Stacks, Tag 07Q9] states its conclusion with, for a tower whose
length is the `n` of the (TR 4) exponent `p ^ n`; matching it with a degree given independently
is the local constancy discussed in the module documentation,
`AlgebraicGeometry.eq_of_hasConstantDegree_of_hasFiniteBasis`. -/
theorem hasConstantDegree_alphaPTowerComp (p : ℕ) (hp : p ≠ 0) (Z : ℕ → Scheme.{u})
    [IsAffine (Z 0)] (g : ∀ i : ℕ, Z (i + 1) ⟶ Z i) (hg : ∀ i : ℕ, IsAlphaPCover p (g i))
    (n : ℕ) :
    HasConstantDegree (alphaPTowerComp Z g n) (p ^ n) := by
  exact hasConstantDegree_of_hasFiniteBasis_appTop (hasFiniteBasis_alphaPTowerComp p hp Z g hg n)

end AlgebraicGeometry

end
