module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairStructureSheaf
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairs
public import StacksFrontier.Homology.PseudoCoherent.Relative.BaseLocalization
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative pseudo-coherence of the structure sheaf on every compatible pair of affine opens

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `m` be an integer. The
local condition of Stacks 09UI for `𝒪_X` at a compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V` is
equivalent, by `AlgebraicGeometry.affinePairStructureSheafComparison`, to `Γ(X, U)`
being `m`-pseudo-coherent as a module over itself relative to `Γ(S, V)`. This module proves that
*that* condition holds at **every** compatible pair as soon as it holds on **some** pair of affine
open covers — the implication (1) ⟹ (2) of Stacks 09UJ at the structure sheaf — and with it
discharges `AlgebraicGeometry.RelativeStructureSheafComparison`, so that Stacks 067Y holds
unconditionally.

## Main definitions

* `AlgebraicGeometry.SectionsRelativelyPseudoCoherentFrom`: at a compatible pair of affine opens
  `U ⊆ f ⁻¹ᵁ V`, the condition that `Γ(X, U)` is `m`-pseudo-coherent as a module over itself
  relative to `Γ(S, V)` for the algebra structure given by `f.appLE V U e`.

## Main results

* `AlgebraicGeometry.affinePairComparison_structureSheaf`: **Stacks 09UJ at the structure
  sheaf**, i.e. `AlgebraicGeometry.AffinePairComparison` for the object of the derived category
  concentrated in degree zero on `𝒪_X`.
* `AlgebraicGeometry.relativeStructureSheafComparison`:
  `AlgebraicGeometry.RelativeStructureSheafComparison`, with no hypotheses.
* `AlgebraicGeometry.pseudoCoherent_tfae_three`: **Stacks 067Y**, the full three-condition
  equivalence, unconditionally.
* `AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent`: the equivalence of conditions
  (2) and (3) of Stacks 067Y, unconditionally.

## Implementation notes

**The argument is entirely algebraic.** Neither Stacks 09VD nor Stacks 09VE is used, and no
closed immersion into an affine space appears: once
`AlgebraicGeometry.affinePairStructureSheafComparison` has replaced the local condition of
Stacks 09UI by a statement about the rings of sections, both sides of Stacks 09UJ are conditions
on rings, and the passage from some covers to all pairs is the locality of relative
pseudo-coherence in the base and in the source. Concretely, for a point `u` of an affine open
`U ⊆ f ⁻¹ᵁ V` with the condition known at a pair `(U₀, V₀)` of the given covers with `u ∈ U₀` and
`f u ∈ V₀`:

1. a standard open `V'` of **both** `V` and `V₀` containing `f u`
   (`AlgebraicGeometry.exists_basicOpen_le_affine_inter`);
2. `W := U₀ ⊓ f ⁻¹ᵁ V'`, which is the standard open of `U₀` cut out by the image of the equation
   of `V'` in `Γ(S, V₀)` (`AlgebraicGeometry.Scheme.basicOpen_appLE`), so tag 0679 with a trivial
   localization of the base moves the condition from `(U₀, V₀)` to `(W, V₀)`;
3. tag 067D, in the form
   `PseudoCoherence.moduleRelativelyPseudoCoherent_iff_baseLocalizationAway`, moves it from
   `(W, V₀)` to `(W, V')`;
4. a standard open `U'` of **both** `W` and `U` containing `u`, and tag 0679 again — this time
   with the base localization `Γ(S, V) → Γ(S, V')` and the source localization
   `Γ(X, W) → Γ(X, U')` — moves it to `(U', V)`;
5. the `U'` so produced cover `U`, finitely many of them suffice, and tag 067E in the form
   `PseudoCoherence.moduleRelativelyPseudoCoherentFrom_of_span_eq_top` assembles the condition at
   `(U, V)` from the conditions at the `(U', V)`.

Step 5 is stated at the concrete localization `Localization.Away a` while what is available is
the abstract one `Γ(X, X.basicOpen a)`; the two are crossed by
`PseudoCoherence.isModuleRelativelyPseudoCoherentFrom_of_algEquiv`, which is why that lemma is
needed in a single fixed degree rather than in all degrees at once.

**Why the opens are taken together with equations.** Each of the three transport lemmas below
takes the new open as an implicit variable together with an equation identifying it with a
standard open, rather than as the standard open itself. This is what lets the two descriptions of
`V'` — as `S.basicOpen b` with `b : Γ(S, V)` and as `S.basicOpen c` with `c : Γ(S, V₀)` — be used
interchangeably, and likewise for `U'`; the equation is discharged by `subst` inside the proof,
so no transport of a module along an isomorphism of rings ever takes place.

**What this does not prove.** Stacks 09UJ is stated for an arbitrary object `E` of `D(𝒪_X)` and
has a final assertion about restriction to open subschemes; only the case `E = 𝒪_X` in degree
zero is proved here, so no declaration in this module carries a `stacks 09UJ` attribute — the tag
sits on `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_forall_affinePair` in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffinePairLocality.lean`. The same
applies to Stacks 09VF, which is about `RΓ(U, E)` for an arbitrary object of `D_QCoh(𝒪_X)`.
Stacks 067Y, on the other hand, is about the structure sheaf only, and
`AlgebraicGeometry.pseudoCoherent_tfae_three` is its full statement.

## References

* [The Stacks Project, Lemma 36.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 15.82.8 (0679)](https://stacks.math.columbia.edu/tag/0679)
* [The Stacks Project, Lemma 15.82.11 (067D)](https://stacks.math.columbia.edu/tag/067D)
* [The Stacks Project, Lemma 15.82.9 (067E)](https://stacks.math.columbia.edu/tag/067E)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- At a compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V` of a morphism locally of finite type,
`Γ(X, U)` is `m`-pseudo-coherent as a module over itself relative to `Γ(S, V)`, the algebra
structure being the one given by `f.appLE V U e`.

This is the right-hand side of `AlgebraicGeometry.RelativeStructureSheafComparisonAt` at one pair,
and by `AlgebraicGeometry.affinePairStructureSheafComparison` it is equivalent to the local
condition `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair` of Stacks 09UI for
`𝒪_X` at that pair. -/
public abbrev SectionsRelativelyPseudoCoherentFrom [LocallyOfFiniteType f] (m : ℤ)
    (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) : Prop :=
  letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  PseudoCoherence.IsModuleRelativelyPseudoCoherentFrom (R := Γ(S, V)) (A := Γ(X, U)) Γ(X, U) m

/-! ### Transport along an equality of opens

The affineness hypothesis and the compatibility of the pair are propositions, so replacing one of
the two opens by an equal one changes nothing. -/

/-- The condition at a pair depends on the open of the source only through the open itself. -/
public theorem sectionsRelativelyPseudoCoherentFrom_congr_source [LocallyOfFiniteType f] (m : ℤ)
    {U₁ U₂ : X.Opens} (hU : U₁ = U₂) (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    {V : S.Opens} (hV : IsAffineOpen V) (e₁ : U₁ ≤ f ⁻¹ᵁ V) (e₂ : U₂ ≤ f ⁻¹ᵁ V)
    (h : SectionsRelativelyPseudoCoherentFrom f m U₁ hU₁ V hV e₁) :
    SectionsRelativelyPseudoCoherentFrom f m U₂ hU₂ V hV e₂ := by
  subst hU
  exact h

/-- The condition at a pair depends on the open of the target only through the open itself. -/
public theorem sectionsRelativelyPseudoCoherentFrom_congr_target [LocallyOfFiniteType f] (m : ℤ)
    {U : X.Opens} (hU : IsAffineOpen U)
    {V₁ V₂ : S.Opens} (hV : V₁ = V₂) (hV₁ : IsAffineOpen V₁) (hV₂ : IsAffineOpen V₂)
    (e₁ : U ≤ f ⁻¹ᵁ V₁) (e₂ : U ≤ f ⁻¹ᵁ V₂)
    (h : SectionsRelativelyPseudoCoherentFrom f m U hU V₁ hV₁ e₁) :
    SectionsRelativelyPseudoCoherentFrom f m U hU V₂ hV₂ e₂ := by
  subst hV
  exact h

/-! ### Shrinking the source to a standard open, with the target fixed -/

/-- Algebras given by ring maps `g`, `h` and `g ≫ h` form a scalar tower. -/
private theorem isScalarTower_toAlgebra {R A B : CommRingCat} (g : R ⟶ A) (h : A ⟶ B)
    (k : R ⟶ B) (H : g ≫ h = k) :
    letI := g.hom.toAlgebra
    letI := h.hom.toAlgebra
    letI := k.hom.toAlgebra
    IsScalarTower R A B := by
  let := g.hom.toAlgebra
  let := h.hom.toAlgebra
  let := k.hom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq' (by subst H; rfl)

/-- **The condition at a pair passes to a standard open of the source cut out by a section coming
from the target.** The ring of sections on `X_{f^♯c}` is a localization of `Γ(X, U)` away from
`f.appLE V U e c`, so this is tag 0679 with a trivial localization of the base.

Taking the standard open to be cut out by a section of `Γ(S, V)` rather than of `Γ(X, U)` is no
restriction for the use made of it below, where the open in question is `U ⊓ f ⁻¹ᵁ V'` for a
standard open `V'` of `V`. -/
public theorem sectionsRelativelyPseudoCoherentFrom_basicOpen_appLE [LocallyOfFiniteType f]
    (m : ℤ) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (c : Γ(S, V))
    {W : X.Opens} (hWeq : W = X.basicOpen (f.appLE V U e c)) (hW : IsAffineOpen W)
    (eW : W ≤ f ⁻¹ᵁ V)
    (h : SectionsRelativelyPseudoCoherentFrom f m U hU V hV e) :
    SectionsRelativelyPseudoCoherentFrom f m W hW V hV eW := by
  subst hWeq
  let algU : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let hFTU : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  let algW : Algebra Γ(S, V) Γ(X, X.basicOpen (f.appLE V U e c)) :=
    (f.appLE V _ eW).hom.toAlgebra
  let hloc : IsLocalization.Away (f.appLE V U e c) Γ(X, X.basicOpen (f.appLE V U e c)) :=
    hU.isLocalization_basicOpen _
  let hone : IsLocalization.Away (1 : Γ(S, V)) Γ(S, V) :=
    IsLocalization.away_of_isUnit_of_bijective _ isUnit_one Function.bijective_id
  have htow : IsScalarTower Γ(S, V) Γ(X, U) Γ(X, X.basicOpen (f.appLE V U e c)) :=
    isScalarTower_toAlgebra _ _ _ (by simp)
  exact PseudoCoherence.moduleRelativelyPseudoCoherentFrom_localizationAway
    (R := Γ(S, V)) (Rs := Γ(S, V)) (A := Γ(X, U))
    (Aa := Γ(X, X.basicOpen (f.appLE V U e c))) (1 : Γ(S, V)) (f.appLE V U e c) m h

/-! ### Shrinking the target to a standard open -/

/-- **The condition at a pair passes to a standard open of the target.** `Γ(S, S_c)` is a
localization of `Γ(S, V)` away from `c`, and relative pseudo-coherence does not see a principal
localization of the base; this is tag 067D in the form
`PseudoCoherence.moduleRelativelyPseudoCoherent_iff_baseLocalizationAway`. -/
public theorem sectionsRelativelyPseudoCoherentFrom_basicOpen_target [LocallyOfFiniteType f]
    (m : ℤ) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V) (c : Γ(S, V))
    {V' : S.Opens} (hV'eq : V' = S.basicOpen c) (hV' : IsAffineOpen V')
    (e' : U ≤ f ⁻¹ᵁ V')
    (h : SectionsRelativelyPseudoCoherentFrom f m U hU V hV e) :
    SectionsRelativelyPseudoCoherentFrom f m U hU V' hV' e' := by
  subst hV'eq
  let algU : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let algU' : Algebra Γ(S, S.basicOpen c) Γ(X, U) := (f.appLE _ U e').hom.toAlgebra
  let hFTU' : Algebra.FiniteType Γ(S, S.basicOpen c) Γ(X, U) :=
    algebraFiniteType_appLE f U hU _ hV' e'
  let hloc : IsLocalization.Away c Γ(S, S.basicOpen c) := hV.isLocalization_basicOpen c
  have htow : IsScalarTower Γ(S, V) Γ(S, S.basicOpen c) Γ(X, U) :=
    isScalarTower_toAlgebra _ _ _ (by simp)
  exact (PseudoCoherence.moduleRelativelyPseudoCoherent_iff_baseLocalizationAway
    (R := Γ(S, V)) (Rs := Γ(S, S.basicOpen c)) (B := Γ(X, U)) c Γ(X, U) m).1.mpr h

/-! ### Growing the target back and shrinking the source -/

/-- **Tag 0679 at a pair of affine opens.** If the condition holds at `(W, V')` with `V'` a
standard open of `V`, then it holds at `(U', V)` for every standard open `U'` of `W`. This is the
step that recovers the original target: `Γ(S, V')` is a localization of `Γ(S, V)` away from `b`
and `Γ(X, U')` is a localization of `Γ(X, W)` away from `p`, which is exactly the shape of
tag 0679. -/
public theorem sectionsRelativelyPseudoCoherentFrom_of_basicOpen_target [LocallyOfFiniteType f]
    (m : ℤ) {W : X.Opens} (hW : IsAffineOpen W) {V : S.Opens} (hV : IsAffineOpen V) (b : Γ(S, V))
    {V' : S.Opens} (hV'eq : V' = S.basicOpen b) (hV' : IsAffineOpen V')
    (eW' : W ≤ f ⁻¹ᵁ V') (eW : W ≤ f ⁻¹ᵁ V) (p : Γ(X, W))
    {U' : X.Opens} (hU'eq : U' = X.basicOpen p) (hU' : IsAffineOpen U') (e' : U' ≤ f ⁻¹ᵁ V)
    (h : SectionsRelativelyPseudoCoherentFrom f m W hW V' hV' eW') :
    SectionsRelativelyPseudoCoherentFrom f m U' hU' V hV e' := by
  subst hV'eq
  subst hU'eq
  let algW : Algebra Γ(S, V) Γ(X, W) := (f.appLE V W eW).hom.toAlgebra
  let algW' : Algebra Γ(S, S.basicOpen b) Γ(X, W) := (f.appLE _ W eW').hom.toAlgebra
  let hFTW' : Algebra.FiniteType Γ(S, S.basicOpen b) Γ(X, W) :=
    algebraFiniteType_appLE f W hW _ hV' eW'
  let algU' : Algebra Γ(S, V) Γ(X, X.basicOpen p) := (f.appLE V _ e').hom.toAlgebra
  let hlocb : IsLocalization.Away b Γ(S, S.basicOpen b) := hV.isLocalization_basicOpen b
  let hlocp : IsLocalization.Away p Γ(X, X.basicOpen p) := hW.isLocalization_basicOpen p
  have htowb : IsScalarTower Γ(S, V) Γ(S, S.basicOpen b) Γ(X, W) :=
    isScalarTower_toAlgebra _ _ _ (by simp)
  have htowp : IsScalarTower Γ(S, V) Γ(X, W) Γ(X, X.basicOpen p) :=
    isScalarTower_toAlgebra _ _ _ (by simp)
  exact PseudoCoherence.moduleRelativelyPseudoCoherentFrom_localizationAway
    (R := Γ(S, V)) (Rs := Γ(S, S.basicOpen b)) (A := Γ(X, W))
    (Aa := Γ(X, X.basicOpen p)) b p m h

/-! ### From one pair of the covers to a standard open neighbourhood of a point -/

/-- **The condition at one pair of affine opens of the covers gives it at a standard open
neighbourhood of each point.** Let the condition hold at `(U₀, V₀)` and let `u` be a point of an
affine open `U ⊆ f ⁻¹ᵁ V` which also lies in `U₀`. Then some standard open `X_q` of `U`
containing `u` satisfies the condition against `V`.

This is the composite of the three transport lemmas above: a standard open `V'` of both `V` and
`V₀` containing `f u`, the standard open `W = U₀ ⊓ f ⁻¹ᵁ V'` of `U₀`, and a standard open of both
`W` and `U` containing `u`. The two "standard open of both" steps are
`AlgebraicGeometry.exists_basicOpen_le_affine_inter`. -/
public theorem exists_basicOpen_sectionsRelativelyPseudoCoherentFrom [LocallyOfFiniteType f]
    (m : ℤ) {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (e : U ≤ f ⁻¹ᵁ V)
    {U₀ : X.Opens} (hU₀ : IsAffineOpen U₀) {V₀ : S.Opens} (hV₀ : IsAffineOpen V₀)
    (e₀ : U₀ ≤ f ⁻¹ᵁ V₀)
    (h : SectionsRelativelyPseudoCoherentFrom f m U₀ hU₀ V₀ hV₀ e₀)
    (u : X) (huU : u ∈ U) (huU₀ : u ∈ U₀) :
    ∃ q : Γ(X, U), u ∈ X.basicOpen q ∧
      SectionsRelativelyPseudoCoherentFrom f m (X.basicOpen q) (hU.basicOpen q) V hV
        ((X.basicOpen_le q).trans e) := by
  obtain ⟨b, c, hbc, hub⟩ := exists_basicOpen_le_affine_inter hV hV₀ (f.base u) ⟨e huU, e₀ huU₀⟩
  have hWeq : X.basicOpen (f.appLE V₀ U₀ e₀ c) = U₀ ⊓ f ⁻¹ᵁ (S.basicOpen c) :=
    Scheme.basicOpen_appLE f U₀ V₀ e₀ c
  have hW : IsAffineOpen (X.basicOpen (f.appLE V₀ U₀ e₀ c)) := hU₀.basicOpen _
  have eWV₀ : X.basicOpen (f.appLE V₀ U₀ e₀ c) ≤ f ⁻¹ᵁ V₀ := (X.basicOpen_le _).trans e₀
  have eWc : X.basicOpen (f.appLE V₀ U₀ e₀ c) ≤ f ⁻¹ᵁ (S.basicOpen c) := hWeq ▸ inf_le_right
  have eWb : X.basicOpen (f.appLE V₀ U₀ e₀ c) ≤ f ⁻¹ᵁ (S.basicOpen b) := hbc ▸ eWc
  have eWV : X.basicOpen (f.appLE V₀ U₀ e₀ c) ≤ f ⁻¹ᵁ V :=
    eWb.trans ((Opens.map f.base).map (homOfLE (S.basicOpen_le b))).le
  have hW₀ := sectionsRelativelyPseudoCoherentFrom_basicOpen_appLE f m hU₀ hV₀ e₀ c rfl hW eWV₀ h
  have hWc := sectionsRelativelyPseudoCoherentFrom_basicOpen_target f m hW hV₀ eWV₀ c rfl
    (hV₀.basicOpen c) eWc hW₀
  have hWb := sectionsRelativelyPseudoCoherentFrom_congr_target f m hW hbc.symm
    (hV₀.basicOpen c) (hV.basicOpen b) eWc eWb hWc
  have huW : u ∈ X.basicOpen (f.appLE V₀ U₀ e₀ c) := by
    rw [hWeq]
    exact ⟨huU₀, hbc ▸ hub⟩
  obtain ⟨p, q, hpq, hup⟩ := exists_basicOpen_le_affine_inter hW hU u ⟨huW, huU⟩
  exact ⟨q, hpq ▸ hup, sectionsRelativelyPseudoCoherentFrom_of_basicOpen_target f m hW hV b rfl
    (hV.basicOpen b) eWb eWV p hpq.symm (hU.basicOpen q) ((X.basicOpen_le q).trans e) hWb⟩

/-! ### Gluing along a finite standard cover of the source -/

/-- **The condition at a pair is local on the source.** If every point of the affine open `U` has
a standard open neighbourhood in `U` at which the condition holds against `V`, then it holds at
`(U, V)`.

The sections cutting out those standard opens span the unit ideal of `Γ(X, U)`
(`AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff`), hence finitely many of them do
(`Ideal.span_eq_top_iff_finite`), and tag 067E in the form
`PseudoCoherence.moduleRelativelyPseudoCoherentFrom_of_span_eq_top` assembles the conclusion. That
lemma speaks about `Localization.Away a` while the sections on `X_a` are only an abstract
localization away from `a`; the two are identified by `IsLocalization.algEquiv` and the condition
is carried across by
`PseudoCoherence.isModuleRelativelyPseudoCoherentFrom_of_algEquiv`. -/
public theorem sectionsRelativelyPseudoCoherentFrom_of_forall_mem [LocallyOfFiniteType f] (m : ℤ)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (h : ∀ u ∈ U, ∃ q : Γ(X, U), u ∈ X.basicOpen q ∧
      SectionsRelativelyPseudoCoherentFrom f m (X.basicOpen q) (hU.basicOpen q) V hV
        ((X.basicOpen_le q).trans e)) :
    SectionsRelativelyPseudoCoherentFrom f m U hU V hV e := by
  classical
  let algU : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  let hFTU : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  set s : Set Γ(X, U) := {q | SectionsRelativelyPseudoCoherentFrom f m (X.basicOpen q)
    (hU.basicOpen q) V hV ((X.basicOpen_le q).trans e)}
  have hle : U ≤ ⨆ q : s, X.basicOpen (q : Γ(X, U)) := by
    intro x hx
    obtain ⟨q, hq, hqpc⟩ := h x hx
    exact Opens.mem_iSup.mpr ⟨⟨q, hqpc⟩, hq⟩
  obtain ⟨t, hts, htspan⟩ :=
    (Ideal.span_eq_top_iff_finite s).mp (hU.self_le_iSup_basicOpen_iff.mp hle)
  refine PseudoCoherence.moduleRelativelyPseudoCoherentFrom_of_span_eq_top
    (R := Γ(S, V)) (A := Γ(X, U)) (ι := {x // x ∈ t}) (fun i ↦ (i : Γ(X, U)))
    (by rwa [show Set.range (fun i : {x // x ∈ t} ↦ (i : Γ(X, U))) = (t : Set Γ(X, U)) from
      Subtype.range_coe]) m fun i ↦ ?_
  have hi : SectionsRelativelyPseudoCoherentFrom f m (X.basicOpen (i : Γ(X, U)))
      (hU.basicOpen _) V hV ((X.basicOpen_le _).trans e) := hts i.2
  let algQ : Algebra Γ(S, V) Γ(X, X.basicOpen (i : Γ(X, U))) :=
    (f.appLE V _ ((X.basicOpen_le _).trans e)).hom.toAlgebra
  let hFTQ : Algebra.FiniteType Γ(S, V) Γ(X, X.basicOpen (i : Γ(X, U))) :=
    algebraFiniteType_appLE f _ (hU.basicOpen _) V hV ((X.basicOpen_le _).trans e)
  let hlocQ : IsLocalization.Away (i : Γ(X, U)) Γ(X, X.basicOpen (i : Γ(X, U))) :=
    hU.isLocalization_basicOpen _
  have htowQ : IsScalarTower Γ(S, V) Γ(X, U) Γ(X, X.basicOpen (i : Γ(X, U))) :=
    isScalarTower_toAlgebra _ _ _ (by simp)
  exact PseudoCoherence.isModuleRelativelyPseudoCoherentFrom_of_algEquiv
    ((IsLocalization.algEquiv (Submonoid.powers (i : Γ(X, U)))
      Γ(X, X.basicOpen (i : Γ(X, U)))
      (Localization.Away (i : Γ(X, U)))).restrictScalars Γ(S, V)) m hi

/-! ### From some covers to every compatible pair -/

/-- **From some pair of affine open covers to every compatible pair of affine opens.** If there
are an affine open cover `V` of `S` and, over each of its members, an affine open cover `U` of
its inverse image on which the condition holds, then the condition holds at every compatible pair
of affine opens.

This is the implication (1) ⟹ (2) of Stacks 09UJ, read through
`AlgebraicGeometry.affinePairStructureSheafComparison` so that both sides are conditions on rings
of sections. -/
public theorem forall_sectionsRelativelyPseudoCoherentFrom_of_exists_cover
    [LocallyOfFiniteType f] (m : ℤ)
    (hcov : ∃ (ι : Type u) (Vc : ι → S.affineOpens), (⨆ i, (Vc i : S.Opens)) = ⊤ ∧
      ∀ i, ∃ (κ : Type u) (Uc : κ → X.affineOpens),
        (⨆ j, (Uc j : X.Opens)) = f ⁻¹ᵁ (Vc i).1 ∧
        ∀ j, ∃ hj : (Uc j).1 ≤ f ⁻¹ᵁ (Vc i).1,
          SectionsRelativelyPseudoCoherentFrom f m (Uc j).1 (Uc j).2 (Vc i).1 (Vc i).2 hj) :
    ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V),
      SectionsRelativelyPseudoCoherentFrom f m U hU V hV e := by
  obtain ⟨ι, Vc, hVcov, hinner⟩ := hcov
  intro U hU V hV e
  refine sectionsRelativelyPseudoCoherentFrom_of_forall_mem f m hU hV e fun u hu ↦ ?_
  have hmem : f.base u ∈ (⨆ i, (Vc i : S.Opens)) := by
    rw [hVcov]
    exact Opens.mem_top _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hmem
  obtain ⟨κ, Uc, hUcov, hUloc⟩ := hinner i
  have humem : u ∈ (⨆ j, (Uc j : X.Opens)) := by
    rw [hUcov]
    exact hi
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp humem
  obtain ⟨hle, hpc⟩ := hUloc j
  exact exists_basicOpen_sectionsRelativelyPseudoCoherentFrom f m hU hV e (Uc j).2 (Vc i).2 hle
    hpc u hu hj

/-! ### Stacks 09UJ at the structure sheaf, and Stacks 067Y -/

/-- **Stacks 09UJ at the structure sheaf.** For `f : X ⟶ S` locally of finite type and `m` an
integer, `𝒪_X` is relatively `m`-pseudo-coherent in the sense of Stacks 09UI if and only if the
local condition of Stacks 09UI holds at every compatible pair of affine opens.

The implication (2) ⟹ (1) is
`AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair`
and is the choice of cover. For (1) ⟹ (2), `AlgebraicGeometry.affinePairStructureSheafComparison`
turns the local condition on the given covers into a condition on the rings of sections,
`AlgebraicGeometry.forall_sectionsRelativelyPseudoCoherentFrom_of_exists_cover` propagates it to
every compatible pair, and the same comparison turns it back.

This is only the case `E = 𝒪_X` in degree zero of the source's lemma, which is stated for an
arbitrary object of `D(𝒪_X)`, so it carries no `stacks` attribute. -/
public theorem affinePairComparison_structureSheaf (hft : LocallyOfFiniteType f) (m : ℤ) :
    letI := hft
    AffinePairComparison f ((DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) m := by
  let := hft
  refine ⟨fun h U V hUV ↦ ?_,
    fun h ↦ Scheme.Hom.isPseudoCoherentFrom_of_forall_affinePair f _ m h⟩
  refine (affinePairStructureSheafComparison f hft m U.1 U.2 V.1 V.2 hUV).2 ?_
  refine forall_sectionsRelativelyPseudoCoherentFrom_of_exists_cover f m ?_ U.1 U.2 V.1 V.2 hUV
  obtain ⟨ι, Vc, hVcov, hinner⟩ := h
  refine ⟨ι, Vc, hVcov, fun i ↦ ?_⟩
  obtain ⟨κ, Uc, hUcov, hUloc⟩ := hinner i
  refine ⟨κ, Uc, hUcov, fun j ↦ ?_⟩
  obtain ⟨hle, hpc⟩ := hUloc j
  exact ⟨hle, (affinePairStructureSheafComparison f hft m _ (Uc j).2 _ (Vc i).2 hle).1 hpc⟩

/-- **The comparison of Stacks 09VF and Stacks 09UJ at the structure sheaf, with no
hypotheses.** For `f : X ⟶ S` locally of finite type and `m` an integer, `𝒪_X` is relatively
`m`-pseudo-coherent over `S` exactly when, at every compatible pair of affine opens
`U ⊆ f ⁻¹ᵁ V`, the ring `Γ(X, U)` is `m`-pseudo-coherent as a module over itself relative to
`Γ(S, V)`.

This is `AlgebraicGeometry.relativeStructureSheafComparison_of_affinePair` fed its two arguments:
Stacks 09UJ at the structure sheaf, which is
`AlgebraicGeometry.affinePairComparison_structureSheaf`, and the per-pair content of Stacks 09VF
at the structure sheaf, which is `AlgebraicGeometry.affinePairStructureSheafComparison`. -/
public theorem relativeStructureSheafComparison : RelativeStructureSheafComparison f :=
  relativeStructureSheafComparison_of_affinePair f
    (fun hft m ↦ affinePairComparison_structureSheaf f hft m)
    (affinePairStructureSheafComparison f)

/-- **Stacks 067Y, the equivalence of (2) and (3).** A morphism of schemes is pseudo-coherent if
and only if it is locally of finite type and `𝒪_X` is pseudo-coherent relative to `S`.

This is `AlgebraicGeometry.pseudoCoherent_iff_isModulePseudoCoherent_of_relativeComparison` with
its hypothesis discharged by `AlgebraicGeometry.relativeStructureSheafComparison`. -/
@[sga "6 III 1.2"]
public theorem pseudoCoherent_iff_isModulePseudoCoherent :
    PseudoCoherent f ↔
      ∃ hft : LocallyOfFiniteType f,
        letI := hft
        Scheme.Hom.IsModulePseudoCoherent f (SheafOfModules.unit X.ringCatSheaf) :=
  pseudoCoherent_iff_isModulePseudoCoherent_of_relativeComparison f
    (relativeStructureSheafComparison f)

/-- **Stacks 067Y.** For a morphism of schemes `f : X ⟶ S` the following are equivalent: there
are an affine open covering of `S` and, over each of its members, an affine open covering of its
inverse image on which the maps on sections are pseudo-coherent ring maps; the map on sections is
pseudo-coherent at every compatible pair of affine opens; and `f` is locally of finite type with
`𝒪_X` pseudo-coherent relative to `S`.

The equivalence of the first two conditions is `AlgebraicGeometry.pseudoCoherent_tfae`, and the
third enters through `AlgebraicGeometry.relativeStructureSheafComparison`. This declaration states
the whole of the source's lemma, so it subsumes the two clauses of it tagged in
`StacksFrontier/AlgebraicGeometry/Morphisms/PseudoCoherent.lean`. -/
@[stacks 067Y "the full three-condition equivalence"]
public theorem pseudoCoherent_tfae_three :
    let pseudoCoherentOn := fun (V : S.Opens) (U : X.Opens)
        (h : U ≤ f ⁻¹ᵁ V) ↦
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U h).hom.toAlgebra
      Algebra.PseudoCoherent Γ(S, V) Γ(X, U)
    List.TFAE [
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ (V j)),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i, pseudoCoherentOn (V j) (U i)
                ((le_iSup U i).trans hU.le),
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (V : S.Opens), IsAffineOpen V →
          ∀ (h : U ≤ f ⁻¹ᵁ V), pseudoCoherentOn V U h,
      ∃ hft : LocallyOfFiniteType f,
        letI := hft
        Scheme.Hom.IsModulePseudoCoherent f (SheafOfModules.unit X.ringCatSheaf)] :=
  pseudoCoherent_tfae_of_relativeComparison f (relativeStructureSheafComparison f)

end AlgebraicGeometry

end
