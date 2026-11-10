module

public import StacksFrontier.AlgebraicGeometry.StalkBridge.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The higher-rank dévissage criterion of [Stacks, Tag 01YM], over library names

[Stacks, Tag 01YM] says: on a Noetherian scheme `X`, a property `P` of coherent modules holds
for every coherent module as soon as it is closed under extensions, descends from a nonempty
finite direct sum, and for every integral closed subscheme `Z ⊆ X` with generic point `ξ` there
is a coherent `G` with `Supp G = Z`, with `G_ξ` annihilated by `𝔪_ξ`, and such that every
quasi-coherent ideal `J` with `J_ξ = 𝒪_{X,ξ}` admits a quasi-coherent `G' ⊆ J·G` with
`G'_ξ = G_ξ` for which `P` holds.

The source proves it from [Stacks, Tag 01YL] — the same criterion over one irreducible closed
subset — "in exactly the same way that Lemma 01YI follows from Lemma 01YH", i.e. by Noetherian
induction on the closed support together with the reduction of [Stacks, Tag 01YG]. This file is
that derivation, written over library names.

## What this file assumes and why

Two inputs are carried as hypotheses, and both are genuinely open in this repository:

* `Stacks.AlgebraicGeometry.Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X` — the
  conclusion of [Stacks, Tag 01YE]. It enters only through
  `Stacks.AlgebraicGeometry.Tag01YEStalkBridge.property_of_hasGenericStalkIdealCoproductSub`,
  which is [Stacks, Tag 01YG] with 01YE as its one added hypothesis.
* `HasIrreducibleHigherRankCriterion X` — [Stacks, Tag 01YL] as a predicate on `X`, restated
  here over library names. Nothing in this repository proves it, and its own proof in the source
  again needs [Stacks, Tag 01YE].

So the content added here is exactly the *global* half of the dévissage: the Noetherian
induction on closed supports, and the identification of the inductive hypothesis with 01YL's
`hproper`. The two named inputs are untouched.

## Main definitions

* `HasIrreducibleHigherRankCriterion`: [Stacks, Tag 01YL] as a predicate on `X`.

## Main results

* `isZero_stalk_pushforward_of_notMem_range`: the stalk of a direct image along a closed
  immersion vanishes off the range of that immersion.
* `supp_pushforward_subset_range`: hence the support of such a direct image is contained in the
  range, in the form the induction consumes.
* `property_higher_rank_of_criteria`: **[Stacks, Tag 01YM] verbatim, with [Stacks, Tag 01YE] and
  [Stacks, Tag 01YL] as its two added hypotheses.**

## Implementation notes

**The annihilation hypothesis is taken at the stalk, which is the source's own statement and is
weaker than the section-wise spelling.** The section-wise form of Stacks 01YM states 01YM's
condition (3)(b) section-wise — for every open `U`, every `r ∈ Γ(X,U)` whose germ at `ξ` lies in
`𝔪_ξ` and every `s ∈ Γ(G,U)`, the germ of `r • s` vanishes — and its first step is to upgrade
that to the stalk statement `G_ξ` is annihilated by `𝔪_ξ`. The stalk statement is what the
source asserts, and it is implied by the section statement, so taking it as the hypothesis makes
the theorem below stronger than the section-wise one. The upgrade itself is not lost: it is
`Stacks.AlgebraicGeometry.Tag01YEStalkBridge.germ_smul`, so a consumer holding
only the section form can still apply this theorem.

**Coherence of `i_* H` costs one lemma, not four.** A direct proof assembles it from four
inputs — the coherence criteria of [Stacks, Tag 01XZ], quasi-coherence of the direct image
along an affine morphism [Stacks, Tag 01LC], the submodule case of [Stacks, Tag 01Y1], and the
finite-type transfer [Stacks, Tag 05B3]. All four are already composed in
`AlgebraicGeometry.ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit`, which is
exactly the statement needed, so [Stacks, Tag 05B3] — which has no library form — is not needed
at all.

**The well-founded induction runs on `TopologicalSpace.Closeds X` under `<`.** A Noetherian
scheme has a Noetherian topological space, so the strict order on closed sets is well-founded;
the motive is the statement that `P` holds for every direct image of a quasi-coherent ideal
sheaf off an integral closed subscheme whose range is that closed set.

**No `stacks` attribute is attached.** Tag 01YM is a single unlabelled assertion, and the theorem
below carries two hypotheses the tag does not grant. Tags 01YE, 01YL and 01YM all remain
unformalized.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01YL](https://stacks.math.columbia.edu/tag/01YL)
* [Stacks Project, Tag 01YM](https://stacks.math.columbia.edu/tag/01YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag01YMHigherRank

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The support of a direct image along a closed immersion -/

/-- **The stalk of a direct image along a closed immersion vanishes off the range.** The
underlying sheaf of abelian groups of `i_* H` is the topological pushforward of that of `H`, and
a topological pushforward along a closed embedding has vanishing stalks outside the image. -/
@[ega "0 4.2.5" "partial"]
theorem isZero_stalk_pushforward_of_notMem_range {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (H : Z.Modules) (x : X) (hx : x ∉ Set.range i.base) :
    IsZero (TopCat.Presheaf.stalk (C := Ab.{u})
      ((Scheme.Modules.pushforward i).obj H).val.presheaf x) := by
  change IsZero (TopCat.Presheaf.stalk
    ((closedInclusionPushforward (TopCat.of Z) (TopCat.of X) i.base).obj
      ((SheafOfModules.toSheaf Z.ringCatSheaf).obj H)).1 x)
  exact closedInclusion_pushforward_stalk_isZero_of_not_mem_range
    (TopCat.of Z) (TopCat.of X) i.base i.isClosedEmbedding
    ((SheafOfModules.toSheaf Z.ringCatSheaf).obj H) x hx

/-- **Every point at which a direct image along a closed immersion has a nontrivial stalk lies in
the range of that immersion.** This is the form the Noetherian induction below consumes: 01YL's
conclusion is stated for modules whose nontrivial stalks all lie in the given closed set. -/
theorem supp_pushforward_subset_range {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (H : Z.Modules) (x : X)
    (hx : Nontrivial (((Scheme.Modules.pushforward i).obj H).presheaf.stalk x)) :
    x ∈ Set.range i.base := by
  by_contra hxout
  exact (not_nontrivial_iff_subsingleton.mpr (AddCommGrpCat.subsingleton_of_isZero
    (isZero_stalk_pushforward_of_notMem_range i H x hxout))) hx

/-! ### [Stacks, Tag 01YL] as a predicate -/

/-- **[Stacks, Tag 01YL], restated over library names.** For every irreducible closed subset `Z₀`
of `X` with generic point `ξ`, a property `P` of coherent modules holds for every coherent module
whose nontrivial stalks all lie in `Z₀`, provided `P` holds for the zero module, is closed under
extensions of coherent modules, descends from a nonempty finite direct sum, holds for the direct
image of every quasi-coherent ideal sheaf off an integral closed subscheme strictly inside `Z₀`,
and holds for one coherent `G` supported exactly on `Z₀` with `G_ξ` annihilated by `𝔪_ξ` in the
generic-subsheaf sense of the source's condition (4)(c).

This is the statement of Tag 01YL with its one auxiliary notion, annihilation by the maximal
ideal in the sense of Tag 01YE, replaced by the character-for-character library copy
`Stacks.AlgebraicGeometry.Tag01YEStalkBridge.IsMaximalIdealAnnihilated`; everything else in that
statement is already written in Mathlib's vocabulary, and nothing is added, removed or
weakened. -/
def HasIrreducibleHigherRankCriterion (X : Scheme.{u}) : Prop :=
  ∀ (Z₀ : Set X), IsClosed Z₀ → ∀ ξ : X, IsGenericPoint ξ Z₀ →
    ∀ P : X.Modules → Prop, P (⊤_ X.Modules) →
      (∀ S : ShortComplex X.Modules, S.ShortExact →
        S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂) →
      (∀ F : X.Modules, F.IsCoherent →
        (∃ n : ℕ, P (∏ᶜ fun _ : Fin (n + 1) => F)) → P F) →
      (∀ (I : X.IdealSheafData) [IsIntegral I.subscheme],
        (I.support : Set X) ⊆ Z₀ → (I.support : Set X) ≠ Z₀ →
        ∀ (H : (SheafOfModules.unit I.subscheme.ringCatSheaf).Submodule)
          [H.toSheafOfModules.IsQuasicoherent],
          P ((Scheme.Modules.pushforward I.subschemeι).obj H.toSheafOfModules)) →
      (∃ G : X.Modules, G.IsCoherent ∧
        (∀ x : X, x ∈ Z₀ ↔ Nontrivial (G.presheaf.stalk x)) ∧
        Tag01YEStalkBridge.IsMaximalIdealAnnihilated G ξ ∧
        (∀ J : X.IdealSheafData, ξ ∉ J.support →
          ∃ G' : G.Submodule,
            G'.toSheafOfModules.IsCoherent ∧
            (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
              (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
                J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
            Function.Surjective
              (((TopCat.Presheaf.stalkFunctor Ab ξ).map
                (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
            P G'.toSheafOfModules)) →
      ∀ F : X.Modules, F.IsCoherent →
        (∀ x : X, Nontrivial (F.presheaf.stalk x) → x ∈ Z₀) → P F

/-! ### [Stacks, Tag 01YM] -/

/-- **[Stacks, Tag 01YM] verbatim, with [Stacks, Tag 01YE] and [Stacks, Tag 01YL] as its two
added hypotheses.** On a Noetherian scheme a property of coherent modules that holds for zero,
is closed under extensions, descends from a nonempty finite direct sum, and for every integral
closed subscheme admits a coherent module supported exactly there with annihilated generic stalk
and a generic-equality subsheaf inside every ideal multiple, holds for every coherent module.

The proof is the source's: the reduction of [Stacks, Tag 01YG] brings the goal down to the direct
images of quasi-coherent ideal sheaves off integral closed subschemes, and those are handled by
well-founded induction on their closed ranges, each step being [Stacks, Tag 01YL] applied to that
range with the inductive hypothesis supplying 01YL's `hproper`. -/
theorem property_higher_rank_of_criteria (X : Scheme.{u}) [IsNoetherian X]
    (h01YE : Tag01YEStalkBridge.HasGenericStalkIdealCoproductSub X)
    (h01YL : HasIrreducibleHigherRankCriterion X)
    (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hsum : ∀ F : X.Modules, F.IsCoherent →
      (∃ n : ℕ, P (∏ᶜ fun _ : Fin (n + 1) => F)) → P F)
    (hgeneric : ∀ (I : X.IdealSheafData) [IsIntegral I.subscheme],
      ∃ G : X.Modules, G.IsCoherent ∧
        (∀ x : X, x ∈ I.support ↔ Nontrivial (G.presheaf.stalk x)) ∧
        Tag01YEStalkBridge.IsMaximalIdealAnnihilated G
          (I.subschemeι (genericPoint I.subscheme)) ∧
        (∀ J : X.IdealSheafData,
          I.subschemeι (genericPoint I.subscheme) ∉ J.support →
          ∃ G' : G.Submodule,
            G'.toSheafOfModules.IsCoherent ∧
            (∀ (U : X.affineOpens) (s : Γ(G'.toSheafOfModules, U.1)),
              (Scheme.Modules.Hom.app G'.ι U.1 s : Γ(G, U.1)) ∈
                J.ideal U • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) ∧
            Function.Surjective
              (((TopCat.Presheaf.stalkFunctor Ab
                (I.subschemeι (genericPoint I.subscheme))).map
                  (Scheme.Modules.Hom.mapPresheaf G'.ι)).hom) ∧
            P G'.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F := by
  classical
  -- The statement of the Noetherian induction: `P` for the direct images of quasi-coherent
  -- ideal sheaves off the integral closed subschemes whose range is `C`.
  let motive : Closeds X → Prop := fun C =>
    ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z],
      (Scheme.Hom.ker i).support = C →
      ∀ H : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
        H.toSheafOfModules.IsQuasicoherent →
        P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules)
  have hmotive : ∀ C : Closeds X, motive C := by
    intro C
    refine (wellFounded_lt : WellFounded (fun A B : Closeds X => A < B)).induction
      (C := motive) C ?_
    intro C ih Z i hi hZ hirange H hH
    let I : X.IdealSheafData := Scheme.Hom.ker i
    have : IsIntegral I.subscheme := IsIntegral.of_isIso i.toImage
    have hIC : I.support = C := hirange
    have hrange : Set.range i.base = C := by
      rw [← hirange, Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]
    let ξ := I.subschemeι (genericPoint I.subscheme)
    have hξ : IsGenericPoint ξ (C : Set X) := by
      have hξ' := (genericPoint_spec I.subscheme).image I.subschemeι.continuous
      rw [Set.image_univ, I.subschemeι.isClosedEmbedding.isClosed_range.closure_eq,
        Scheme.IdealSheafData.range_subschemeι] at hξ'
      simpa [hIC] using hξ'
    -- 01YL's `hproper`, from the inductive hypothesis.
    have hproper : ∀ (J : X.IdealSheafData) [IsIntegral J.subscheme],
        (J.support : Set X) ⊆ (C : Set X) → (J.support : Set X) ≠ (C : Set X) →
        ∀ (H' : (SheafOfModules.unit J.subscheme.ringCatSheaf).Submodule)
          [H'.toSheafOfModules.IsQuasicoherent],
          P ((Scheme.Modules.pushforward J.subschemeι).obj H'.toSheafOfModules) := by
      intro J hJintegral hJsub hJne H' hH'
      exact ih J.support (lt_of_le_of_ne hJsub (fun h =>
        hJne (congrArg SetLike.coe h))) J.subschemeι
        (by simp) H' hH'
    obtain ⟨G, hGc, hGsupport, hGann, hGJ⟩ := hgeneric I
    exact h01YL (C : Set X) C.isClosed ξ hξ P hzero hext hsum hproper
      ⟨G, hGc, by rw [← hIC]; exact hGsupport, hGann, hGJ⟩ _
      (ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit i H hH)
      fun x hx => hrange ▸ supp_pushforward_subset_range i H.toSheafOfModules x hx
  have hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (H : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      H.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj H.toSheafOfModules) := by
    intro Z i hi hZ H hH
    exact hmotive _ i rfl H hH
  exact Tag01YEStalkBridge.property_of_hasGenericStalkIdealCoproductSub X h01YE P hzero hext
    hideal

end Stacks.AlgebraicGeometry.Tag01YMHigherRank

end
