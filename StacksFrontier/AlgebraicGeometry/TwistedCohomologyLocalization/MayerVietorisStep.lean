module

public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic
public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Classes
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.NumeratorCriterion
public import StacksFrontier.AlgebraicGeometry.TwistedCohomologyLocalization.DegreeZeroNumerators
public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.LocalCondition
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiSeparated.LocalizedRestriction

/-!
# The Mayer--Vietoris step for the numerator statements of [Stacks, Tag 09MR]

Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module, `s` a global section of `ℒ`, `ℱ` an
`𝒪_X`-module and `T = X_s` the nonvanishing open of `s`. The two numerator statements of
`StacksFrontier/AlgebraicGeometry/TwistedCohomologyLocalization/NumeratorCriterion.lean`,

* `RestrictKernelTorsion`: a class of `H^p(A, ℱ ⊗ ℒ^{⊗ n})` dying on `A ⊓ T` is killed by a
  power of `s`,
* `RestrictPowerSurjective`: every class of `H^p(A ⊓ T, ℱ)` is `s^{-n}` times a class of
  `H^p(A, ℱ ⊗ ℒ^{⊗ n})`,

are statements about the cohomology groups themselves, so the Mayer--Vietoris long exact
sequence over an ambient open applies to them. This file runs the resulting diagram chase: if
both statements hold in **every** degree over `U`, over `V` and over `U ⊓ V`, they hold in every
degree over `U ⊔ V`.

## Main definitions

* `Stacks.Cohomology.TwistedLocalizationMap.mulPow`: multiplication by `s^n`,
  `H^p(A, ℱ) ⟶ H^p(A, ℱ ⊗ ℒ^{⊗ n})`, over an arbitrary open. Over an open inside `X_s` it is
  the isomorphism inverted by `Stacks.Cohomology.TwistedLocalizationMap.untwistIso`.
* `Stacks.Cohomology.TwistedLocalizationMap.actPow`: multiplication by `s^k`,
  `H^p(A, ℱ ⊗ ℒ^{⊗ n}) ⟶ H^p(A, ℱ ⊗ ℒ^{⊗ (k + n)})`.

## Main results

* `Stacks.Cohomology.TwistedLocalizationMap.restrictKernelTorsion_sup` and
  `Stacks.Cohomology.TwistedLocalizationMap.restrictPowerSurjective_sup`: **the Mayer--Vietoris
  step** for the two numerator statements.
* `Stacks.Cohomology.TwistedLocalizationMap.restrictNumerators_sup`: the two steps together, in
  the shape the induction principle of [Stacks, Tag 08DR] consumes.
* `Stacks.Cohomology.TwistedLocalizationMap.restrictNumerators_of_isAffineOpen`: both statements
  over every affine open, in every degree.
* `Stacks.Cohomology.TwistedLocalizationMap.restrictNumerators_of_isCompact`: both statements
  over every quasi-compact open of a quasi-separated scheme.
* `Stacks.Cohomology.TwistedLocalizationMap.bijective_canonicalMap_of_isCompact` and
  `Stacks.Cohomology.TwistedLocalizationMap.bijective_canonicalMap_top`: **the comparison map of
  [Stacks, Tag 09MR] is bijective over a quasi-compact open of a quasi-separated scheme**, and in
  particular on a quasi-compact quasi-separated scheme.

## The base case

The base case of the induction splits by degree. In **positive** degree it is a vanishing
statement ([Stacks, Tag 01XB] for the source and [Stacks, Tag 01PV] for the target). In degree
zero neither group vanishes and the base case is [Stacks, Tag 01PW] (2) over an affine open; in
that degree the cohomology over an open is its module of sections, and both statements are the
section-level ones of
`StacksFrontier/AlgebraicGeometry/TwistedCohomologyLocalization/DegreeZeroNumerators.lean`. The
surjectivity half is available there only over an affine open on which `ℒ` is trivial, so the
affine case itself is reached by a second induction, over the finite covers of an affine open by
such opens, which is
`Stacks.AlgebraicGeometry.CompactOpenInduction.of_isAffineOpen_of_locally`.

## Implementation notes

Both chases raise cohomology classes of different twists to a common twist by multiplying by a
power of `s`, and the bookkeeping of the exponents is the only delicate point. Two devices keep
it free of transports.

* The target degree of a raised class is **prescribed**: the monotonicity statements take the
  hypothesis in the form `∃ k, N = k + n` and substitute it, after which
  `actPow` lands in the degree `N` literally. The order `k + n` is forced: `actPow` multiplies on
  the left, so the degree of `s^k · ξ` is `k + n` and not `n + k`.
* Equations between the *exponents* are never crossed on a cohomology class. Instead
  `actPow_eq_zero_iff` moves the statement `s^k · ξ = 0` into the graded module
  `H^p_*(A, ℒ, ℱ)`, where multiplication by `s` is the module structure over the graded section
  ring and `pow_add` and `mul_smul` apply with no degrees in sight.

The second friction is that the intersection of the cut cover, `(U ⊓ T) ⊓ (V ⊓ T)`, is not the
cut intersection `(U ⊓ V) ⊓ T` on the nose, although the two opens are equal. Restriction along
that equality is an isomorphism by
`Stacks.Cohomology.TwistedLocalizationMap.isIso_hrestrict_of_eq`, and
`Stacks.Cohomology.AmbientMayerVietoris.hrestrict_comp` identifies its composites with the
restrictions from the uncut opens; `intersectionIso` below packages this.

## References

* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 01EB](https://stacks.math.columbia.edu/tag/01EB)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules
open Stacks.Cohomology.TwistedGradedModule
open Stacks.Cohomology.AmbientMayerVietoris
open scoped DirectSum

universe u

namespace Stacks.Cohomology.TwistedLocalizationMap

attribute [local instance] Stacks.SheafOfModules.sectionDegreeVAdd

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

variable (s : L.sections) (F : X.Modules)

/-! ### Multiplication by a power of `s`, over an arbitrary open -/

/-- **Multiplication by `s^n` as a morphism of sheaves of modules** `ℱ ⟶ ℱ ⊗ ℒ^{⊗ n}`. -/
def twistHom (n : ℕ) : F ⟶ twist X L F (n : ℤ) :=
  sectionPowerAction (sectionSiteRing X) (sectionSiteSheaf X) L F (n : ℤ)
    (sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s n)

/-- **Multiplication by `s^n` on the cohomology of an arbitrary open**,
`H^p(A, ℱ) ⟶ H^p(A, ℱ ⊗ ℒ^{⊗ n})`. -/
def mulPow (p : ℕ) (A : X.Opens) (n : ℕ) (y : (Hgroup X.ringCatSheaf A p F : Type u)) :
    gradedPiece X L F p A (n : ℤ) :=
  (Hfunctor X.ringCatSheaf A p).map (twistHom X L s F n) y

/-- **Multiplication by `s^k` on the cohomology of the `n`-th twist over an arbitrary open**,
`H^p(A, ℱ ⊗ ℒ^{⊗ n}) ⟶ H^p(A, ℱ ⊗ ℒ^{⊗ (k + n)})`. -/
def actPow (p : ℕ) (A : X.Opens) (k n : ℕ) (ξ : gradedPiece X L F p A (n : ℤ)) :
    gradedPiece X L F p A ((k + n : ℕ) : ℤ) :=
  act X L F p A (k : ℤ) (n : ℤ) (Stacks.Cohomology.PowerSection.powerSectionValue X L s k) ξ

/-- Over `U ⊓ X_s` multiplication by `s^n` is the isomorphism `untwistIso` of
`StacksFrontier/AlgebraicGeometry/TwistedCohomologyLocalization/CanonicalMap.lean`. -/
theorem untwistIso_hom_apply (p : ℕ) (U : X.Opens) (n : ℕ)
    (y : (Hgroup X.ringCatSheaf (nonvanishingPart X L s U) p F : Type u)) :
    (ConcreteCategory.hom (untwistIso X L s F p U n).hom) y =
      mulPow X L s F p (nonvanishingPart X L s U) n y := rfl

/-- Multiplication by `s^n` is an isomorphism on the cohomology of an open inside `X_s`. -/
theorem isIso_mulPow (p : ℕ) (A : X.Opens) (hA : A ≤ nonvanishingOpen L s) (n : ℕ) :
    IsIso ((Hfunctor X.ringCatSheaf A p).map (twistHom X L s F n)) :=
  Stacks.Cohomology.Untwisting.isIso_hfunctor_map_sectionPowerAction X L s F n A hA p

/-- **Every twisted class over an open inside `X_s` is `s^n` times an untwisted one.** -/
theorem exists_mulPow_eq (p : ℕ) (A : X.Opens) (hA : A ≤ nonvanishingOpen L s) (n : ℕ)
    (ξ : gradedPiece X L F p A (n : ℤ)) :
    ∃ y : (Hgroup X.ringCatSheaf A p F : Type u), mulPow X L s F p A n y = ξ := by
  have := isIso_mulPow X L s F p A hA n
  exact (ConcreteCategory.bijective_of_isIso ((Hfunctor X.ringCatSheaf A p).map _)).2 ξ

/-! ### The exponent calculus

Multiplying by `s^k` is read inside the graded module `H^p_*(A, ℒ, ℱ)`, where it is the module
structure over the graded section ring; equations between exponents are crossed there and never
on a cohomology class. -/

/-- The homogeneous class `s^k · ξ` is the action of the `k`-th power of the degree-one
homogeneous section on the homogeneous class of `ξ`. -/
theorem of_actPow (p : ℕ) (A : X.Opens) (k n : ℕ) (ξ : gradedPiece X L F p A (n : ℤ)) :
    (DirectSum.of _ ((k + n : ℕ) : ℤ) (actPow X L s F p A k n ξ) :
        twistedCohomologyModule X L F p A) =
      homogeneousSection X L s ^ k • (DirectSum.of _ (n : ℤ) ξ) :=
  (smul_pow_of X L s F p A k n ξ).symm

/-- A homogeneous class vanishes exactly when its component does. -/
theorem of_eq_zero_iff (p : ℕ) (A : X.Opens) (j : ℤ) (ξ : gradedPiece X L F p A j) :
    (DirectSum.of _ j ξ : twistedCohomologyModule X L F p A) = 0 ↔ ξ = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have h' := congrArg (fun z : twistedCohomologyModule X L F p A => z j) h
  simpa [DirectSum.of_eq_same] using h'

/-- **`s^k` kills a class exactly when the `k`-th power of the homogeneous section kills its
homogeneous class.** -/
theorem actPow_eq_zero_iff (p : ℕ) (A : X.Opens) (k n : ℕ)
    (ξ : gradedPiece X L F p A (n : ℤ)) :
    actPow X L s F p A k n ξ = 0 ↔
      homogeneousSection X L s ^ k •
        (DirectSum.of _ (n : ℤ) ξ : twistedCohomologyModule X L F p A) = 0 := by
  rw [← of_actPow, of_eq_zero_iff]

/-- **Raising the power that kills a class.** -/
theorem actPow_eq_zero_of_le (p : ℕ) (A : X.Opens) {k K : ℕ} (n : ℕ)
    (hk : k ≤ K) (ξ : gradedPiece X L F p A (n : ℤ))
    (h : actPow X L s F p A k n ξ = 0) : actPow X L s F p A K n ξ = 0 := by
  rw [actPow_eq_zero_iff] at h ⊢
  obtain ⟨k', rfl⟩ : ∃ k', K = k' + k := ⟨K - k, by omega⟩
  rw [pow_add, mul_smul, h, smul_zero]

/-! ### Multiplication by a power of `s` against the maps of the Mayer--Vietoris sequence

Both `mulPow` and `actPow` are induced by a morphism of sheaves of modules, so each commutes with
the restriction maps and with the Mayer--Vietoris connecting morphism by naturality in the
sheaf. -/

/-- Multiplying by `s^k` is additive. -/
theorem actPow_sub (p : ℕ) (A : X.Opens) (k n : ℕ) (ξ η : gradedPiece X L F p A (n : ℤ)) :
    actPow X L s F p A k n (ξ - η) =
      actPow X L s F p A k n ξ - actPow X L s F p A k n η := by
  dsimp only [actPow, act]
  exact map_sub _ ξ η

/-- Multiplying `0` by `s^k` gives `0`. -/
theorem actPow_zero (p : ℕ) (A : X.Opens) (k n : ℕ) :
    actPow X L s F p A k n 0 = 0 := by
  dsimp only [actPow, act]
  exact map_zero _

/-- **Multiplying by `s^k` commutes with restriction.** -/
theorem hrestrict_actPow (p : ℕ) {A B : X.Opens} (h : A ≤ B) (k n : ℕ)
    (ξ : gradedPiece X L F p B (n : ℤ)) :
    Hrestrict X.ringCatSheaf h p (twist X L F ((k + n : ℕ) : ℤ))
        (actPow X L s F p B k n ξ) =
      actPow X L s F p A k n (Hrestrict X.ringCatSheaf h p (twist X L F (n : ℤ)) ξ) :=
  hrestrict_map X.ringCatSheaf h p
    (TwistAction.actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
      (Stacks.Cohomology.PowerSection.powerSectionValue X L s k)) ξ

/-- **Multiplying by `s^n` commutes with restriction.** -/
theorem hrestrict_mulPow (p : ℕ) {A B : X.Opens} (h : A ≤ B) (n : ℕ)
    (y : (Hgroup X.ringCatSheaf B p F : Type u)) :
    Hrestrict X.ringCatSheaf h p (twist X L F (n : ℤ)) (mulPow X L s F p B n y) =
      mulPow X L s F p A n (Hrestrict X.ringCatSheaf h p F y) :=
  hrestrict_map X.ringCatSheaf h p (twistHom X L s F n) y

/-- **Multiplying by `s^k` the result of multiplying by `s^n` is multiplying by `s^{k + n}`.**
At the level of sheaves this is
`Stacks.Cohomology.TwistedLocalizationMap.sectionPowerAction_comp_actionOf_powerSectionValue`. -/
theorem actPow_mulPow (p : ℕ) (A : X.Opens) (k n : ℕ)
    (y : (Hgroup X.ringCatSheaf A p F : Type u)) :
    actPow X L s F p A k n (mulPow X L s F p A n y) = mulPow X L s F p A (k + n) y := by
  have h : (Hfunctor X.ringCatSheaf A p).map (twistHom X L s F n) ≫
      (Hfunctor X.ringCatSheaf A p).map
        (TwistAction.actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
          (Stacks.Cohomology.PowerSection.powerSectionValue X L s k)) =
      (Hfunctor X.ringCatSheaf A p).map (twistHom X L s F (k + n)) :=
    ((Hfunctor X.ringCatSheaf A p).map_comp _ _).symm.trans
      (congrArg (Hfunctor X.ringCatSheaf A p).map
        (sectionPowerAction_comp_actionOf_powerSectionValue X L s F k n))
  have h' := congrArg (fun m : Hgroup X.ringCatSheaf A p F ⟶
    Hgroup X.ringCatSheaf A p (twist X L F ((k + n : ℕ) : ℤ)) => m y) h
  dsimp only [actPow, act, mulPow]
  simpa [AddCommGrpCat.comp_apply] using h'

/-- **The Mayer--Vietoris connecting morphism commutes with multiplying by `s^k`.** -/
theorem ambientDelta_actPow (W U V : X.Opens) (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W)
    (q k n : ℕ) (θ : gradedPiece X L F q (U ⊓ V) (n : ℤ)) :
    (ambientDelta X.ringCatSheaf W U V hU hV hUV q).app (twist X L F ((k + n : ℕ) : ℤ))
        (actPow X L s F q (U ⊓ V) k n θ) =
      actPow X L s F (q + 1) W k n
        ((ambientDelta X.ringCatSheaf W U V hU hV hUV q).app (twist X L F (n : ℤ)) θ) :=
  ambientDelta_map X.ringCatSheaf U V (twist X L F (n : ℤ)) W hU hV hUV q
    (TwistAction.actionOf (sectionSiteRing X) (sectionSiteSheaf X) L F (k : ℤ) (n : ℤ)
      (Stacks.Cohomology.PowerSection.powerSectionValue X L s k)) θ


/-- **Three successive multiplications by powers of `s` are one.** -/
theorem actPow_eq_zero_of_actPow_actPow (p : ℕ) (A : X.Opens) (j M K n : ℕ)
    (ξ : gradedPiece X L F p A (n : ℤ))
    (h : actPow X L s F p A j (M + (K + n))
      (actPow X L s F p A M (K + n) (actPow X L s F p A K n ξ)) = 0) :
    actPow X L s F p A (j + M + K) n ξ = 0 := by
  rw [actPow_eq_zero_iff] at h ⊢
  rw [of_actPow, of_actPow] at h
  rw [pow_add, pow_add, mul_smul, mul_smul]
  exact h

/-! ### Raising a class to a prescribed twist -/

/-- **A witness for the surjectivity statement can be raised to any larger twist.** If a class of
the `n`-th twist over `A` restricts to `s^n · y` on `A ⊓ X_s`, then for every `N ≥ n` there is a
class of the `N`-th twist restricting to `s^N · y`: multiply by `s^{N - n}`.

The target twist `N` is prescribed, which is what keeps the chases free of transports: the
hypothesis `n ≤ N` is turned into `N = k + n` and substituted, after which `actPow` lands in the
twist `N` on the nose. -/
theorem exists_restrict_eq_mulPow_of_le (p : ℕ) (A : X.Opens) {n N : ℕ} (hn : n ≤ N)
    (y : (Hgroup X.ringCatSheaf (A ⊓ nonvanishingOpen L s) p F : Type u))
    (ξ : gradedPiece X L F p A (n : ℤ))
    (hξ : Hrestrict X.ringCatSheaf (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A) p
      (twist X L F (n : ℤ)) ξ = mulPow X L s F p (A ⊓ nonvanishingOpen L s) n y) :
    ∃ ζ : gradedPiece X L F p A (N : ℤ),
      Hrestrict X.ringCatSheaf (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A) p
        (twist X L F (N : ℤ)) ζ = mulPow X L s F p (A ⊓ nonvanishingOpen L s) N y := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + n := ⟨N - n, by omega⟩
  exact ⟨actPow X L s F p A k n ξ, by rw [hrestrict_actPow, hξ, actPow_mulPow]⟩

/-- **Restricting a lift to a smaller cut open.** If a class of the `N`-th twist over `A`
restricts to `s^N · c` on `A ⊓ X_s`, then over any open `B` inside `A ⊓ X_s` it restricts to
`s^N · (c|_B)`. -/
theorem hrestrict_of_restrict_eq_mulPow (p : ℕ) (N : ℕ) (A B : X.Opens) (hBA : B ≤ A)
    (hBcut : B ≤ A ⊓ nonvanishingOpen L s)
    (c : (Hgroup X.ringCatSheaf (A ⊓ nonvanishingOpen L s) p F : Type u))
    (ξ : gradedPiece X L F p A (N : ℤ))
    (hξ : Hrestrict X.ringCatSheaf (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A) p
      (twist X L F (N : ℤ)) ξ = mulPow X L s F p (A ⊓ nonvanishingOpen L s) N c) :
    Hrestrict X.ringCatSheaf hBA p (twist X L F (N : ℤ)) ξ =
      mulPow X L s F p B N (Hrestrict X.ringCatSheaf hBcut p F c) := by
  rw [← hrestrict_comp_apply X.ringCatSheaf
    (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A) hBcut hBA p (twist X L F (N : ℤ)) ξ,
    hξ, hrestrict_mulPow]

/-! ### Crossing the two spellings of the cut intersection -/

/-- **Cutting two opens by a third and intersecting is intersecting and then cutting.** -/
theorem inf_cut_inf_cut (A B C : X.Opens) : (A ⊓ C) ⊓ (B ⊓ C) = (A ⊓ B) ⊓ C := by
  rw [inf_inf_inf_comm, inf_idem]

/-- **Restriction from `(A ⊓ B) ⊓ X_s` to `(A ⊓ X_s) ⊓ (B ⊓ X_s)` is an isomorphism**: the two
opens are equal, so this is restriction along an equality. -/
def intersectionIso (G : X.Modules) (q : ℕ) (A B : X.Opens) :
    Hgroup X.ringCatSheaf ((A ⊓ B) ⊓ nonvanishingOpen L s) q G ≅
      Hgroup X.ringCatSheaf ((A ⊓ nonvanishingOpen L s) ⊓ (B ⊓ nonvanishingOpen L s)) q G :=
  @asIso _ _ _ _
    (Hrestrict X.ringCatSheaf (le_of_eq (inf_cut_inf_cut X A B (nonvanishingOpen L s))) q G)
    (isIso_hrestrict_of_eq X.ringCatSheaf _ (inf_cut_inf_cut X A B (nonvanishingOpen L s)) q G)

/-- A class on `(A ⊓ B) ⊓ X_s` dying on `(A ⊓ X_s) ⊓ (B ⊓ X_s)` is zero. -/
theorem eq_zero_of_restrict_inf_cut_eq_zero (G : X.Modules) (q : ℕ) (A B : X.Opens)
    (x : (Hgroup X.ringCatSheaf ((A ⊓ B) ⊓ nonvanishingOpen L s) q G : Type u))
    (hx : Hrestrict X.ringCatSheaf
      (le_of_eq (inf_cut_inf_cut X A B (nonvanishingOpen L s))) q G x = 0) : x = 0 := by
  refine (ConcreteCategory.bijective_of_isIso (intersectionIso X L s G q A B).hom).1 ?_
  rw [map_zero]
  exact hx

/-- Every class on `(A ⊓ X_s) ⊓ (B ⊓ X_s)` is restricted from `(A ⊓ B) ⊓ X_s`. -/
theorem exists_restrict_inf_cut_eq (G : X.Modules) (q : ℕ) (A B : X.Opens)
    (x : (Hgroup X.ringCatSheaf ((A ⊓ nonvanishingOpen L s) ⊓ (B ⊓ nonvanishingOpen L s)) q G :
      Type u)) :
    ∃ x₀ : (Hgroup X.ringCatSheaf ((A ⊓ B) ⊓ nonvanishingOpen L s) q G : Type u),
      Hrestrict X.ringCatSheaf
        (le_of_eq (inf_cut_inf_cut X A B (nonvanishingOpen L s))) q G x₀ = x :=
  (ConcreteCategory.bijective_of_isIso (intersectionIso X L s G q A B).hom).2 x

/-! ### The Mayer--Vietoris step -/

section Step

variable (W U V : X.Opens) (hU : U ≤ W) (hV : V ≤ W) (hUV : U ⊔ V = W)

include hUV in
/-- The cut cover: `U ⊓ X_s` and `V ⊓ X_s` cover `W ⊓ X_s`. -/
theorem sup_cut_eq : (U ⊓ nonvanishingOpen L s) ⊔ (V ⊓ nonvanishingOpen L s) =
    W ⊓ nonvanishingOpen L s := by rw [← inf_sup_right, hUV]

/-- The intersection of the cut cover sits inside `U ⊓ V`. -/
theorem cutInter_le_inf :
    (U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s) ≤ U ⊓ V :=
  (le_of_eq (inf_cut_inf_cut X U V (nonvanishingOpen L s))).trans inf_le_left

/-- **A class on `U ⊓ V` dying on the intersection of the cut cover dies on `(U ⊓ V) ⊓ X_s`.**
This is the one place where the two spellings of the cut intersection are crossed. -/
theorem restrict_cut_eq_zero (G : X.Modules) (q : ℕ)
    (ρ : (Hgroup X.ringCatSheaf (U ⊓ V) q G : Type u))
    (hρ : Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) q G ρ = 0) :
    Hrestrict X.ringCatSheaf
      (inf_le_left : (U ⊓ V) ⊓ nonvanishingOpen L s ≤ U ⊓ V) q G ρ = 0 := by
  refine eq_zero_of_restrict_inf_cut_eq_zero X L s G q U V _ ?_
  rw [hrestrict_comp_apply X.ringCatSheaf
    (inf_le_left : (U ⊓ V) ⊓ nonvanishingOpen L s ≤ U ⊓ V)
    (le_of_eq (inf_cut_inf_cut X U V (nonvanishingOpen L s)))
    (cutInter_le_inf X L s U V) q G ρ]
  exact hρ

/-- The connecting morphism of the cut cover commutes with restriction to the cut. -/
private theorem ambientDelta_cut_restrict (G : X.Modules) (r : ℕ)
    (κ : (Hgroup X.ringCatSheaf (U ⊓ V) r G : Type u)) :
    (ambientDelta X.ringCatSheaf (W ⊓ nonvanishingOpen L s) (U ⊓ nonvanishingOpen L s)
        (V ⊓ nonvanishingOpen L s) (inf_le_inf_right (nonvanishingOpen L s) hU)
        (inf_le_inf_right (nonvanishingOpen L s) hV)
        (sup_cut_eq X L s W U V hUV) r).app G
      (Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) r G κ) =
    Hrestrict X.ringCatSheaf (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) (r + 1) G
      ((ambientDelta X.ringCatSheaf W U V hU hV hUV r).app G κ) :=
  ambientDelta_restrict_apply X.ringCatSheaf W U V (W ⊓ nonvanishingOpen L s)
    (U ⊓ nonvanishingOpen L s) (V ⊓ nonvanishingOpen L s) hU hV
    (inf_le_inf_right (nonvanishingOpen L s) hU)
    (inf_le_inf_right (nonvanishingOpen L s) hV) hUV (sup_cut_eq X L s W U V hUV)
    (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) inf_le_left inf_le_left
    (cutInter_le_inf X L s U V) r G κ

/-- **The first half of the kernel chase**: a power of `s` makes a class on `W` dying on
`W ⊓ X_s` die on both members of the cover. -/
theorem exists_actPow_restrict_eq_zero (p : ℕ)
    (hkU : RestrictKernelTorsion X L s F p U) (hkV : RestrictKernelTorsion X L s F p V)
    (n : ℕ) (ξ : gradedPiece X L F p W (n : ℤ))
    (hξ : Hrestrict X.ringCatSheaf (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) p
      (twist X L F (n : ℤ)) ξ = 0) :
    ∃ K : ℕ,
      Hrestrict X.ringCatSheaf hU p (twist X L F ((K + n : ℕ) : ℤ))
          (actPow X L s F p W K n ξ) = 0 ∧
        Hrestrict X.ringCatSheaf hV p (twist X L F ((K + n : ℕ) : ℤ))
          (actPow X L s F p W K n ξ) = 0 := by
  have hdie : ∀ (A : X.Opens) (hA : A ≤ W),
      Hrestrict X.ringCatSheaf (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A) p
        (twist X L F (n : ℤ))
        (Hrestrict X.ringCatSheaf hA p (twist X L F (n : ℤ)) ξ) = 0 := fun A hA =>
    (hrestrict_comp_apply X.ringCatSheaf hA (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A)
        ((inf_le_inf_right (nonvanishingOpen L s) hA).trans
          (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)) p (twist X L F (n : ℤ)) ξ).trans
      (hrestrict_eq_zero_of_restrict_eq_zero X.ringCatSheaf
        (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)
        (inf_le_inf_right (nonvanishingOpen L s) hA) _ p (twist X L F (n : ℤ)) hξ)
  obtain ⟨k₁, hk₁⟩ := hkU n (Hrestrict X.ringCatSheaf hU p (twist X L F (n : ℤ)) ξ) (hdie U hU)
  obtain ⟨k₂, hk₂⟩ := hkV n (Hrestrict X.ringCatSheaf hV p (twist X L F (n : ℤ)) ξ) (hdie V hV)
  refine ⟨max k₁ k₂, ?_, ?_⟩
  · rw [hrestrict_actPow]
    exact actPow_eq_zero_of_le X L s F p U n (le_max_left k₁ k₂) _ hk₁
  · rw [hrestrict_actPow]
    exact actPow_eq_zero_of_le X L s F p V n (le_max_right k₁ k₂) _ hk₂

/-- **The difference of two lifts, restricted to the intersection of the cut cover.** A class on
`U` which is `s^N · a` on `U ⊓ X_s` and a class on `V` which is `s^N · b` on `V ⊓ X_s` differ, on
the intersection of the cut cover, by `s^N` times the difference of the restrictions of `a` and
of `b`. -/
theorem hrestrict_cutInter_sub_lift (q N : ℕ)
    (a : (Hgroup X.ringCatSheaf (U ⊓ nonvanishingOpen L s) q F : Type u))
    (b : (Hgroup X.ringCatSheaf (V ⊓ nonvanishingOpen L s) q F : Type u))
    (α : gradedPiece X L F q U (N : ℤ)) (β : gradedPiece X L F q V (N : ℤ))
    (hα : Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ nonvanishingOpen L s ≤ U) q
      (twist X L F (N : ℤ)) α = mulPow X L s F q (U ⊓ nonvanishingOpen L s) N a)
    (hβ : Hrestrict X.ringCatSheaf (inf_le_left : V ⊓ nonvanishingOpen L s ≤ V) q
      (twist X L F (N : ℤ)) β = mulPow X L s F q (V ⊓ nonvanishingOpen L s) N b) :
    Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) q (twist X L F (N : ℤ))
        (Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ V ≤ U) q (twist X L F (N : ℤ)) α -
          Hrestrict X.ringCatSheaf (inf_le_right : U ⊓ V ≤ V) q (twist X L F (N : ℤ)) β) =
      mulPow X L s F q ((U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s)) N
          (Hrestrict X.ringCatSheaf (inf_le_left : (U ⊓ nonvanishingOpen L s) ⊓
            (V ⊓ nonvanishingOpen L s) ≤ U ⊓ nonvanishingOpen L s) q F a) -
        mulPow X L s F q ((U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s)) N
          (Hrestrict X.ringCatSheaf (inf_le_right : (U ⊓ nonvanishingOpen L s) ⊓
            (V ⊓ nonvanishingOpen L s) ≤ V ⊓ nonvanishingOpen L s) q F b) := by
  rw [map_sub,
    hrestrict_comp_apply X.ringCatSheaf (inf_le_left : U ⊓ V ≤ U)
      (cutInter_le_inf X L s U V) ((cutInter_le_inf X L s U V).trans inf_le_left) q _ α,
    hrestrict_comp_apply X.ringCatSheaf (inf_le_right : U ⊓ V ≤ V)
      (cutInter_le_inf X L s U V) ((cutInter_le_inf X L s U V).trans inf_le_right) q _ β,
    hrestrict_of_restrict_eq_mulPow X L s F q N U
      ((U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s))
      ((cutInter_le_inf X L s U V).trans inf_le_left) inf_le_left a α hα,
    hrestrict_of_restrict_eq_mulPow X L s F q N V
      ((U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s))
      ((cutInter_le_inf X L s U V).trans inf_le_right) inf_le_right b β hβ]

/-- **The restriction of `s^M · θ` to the intersection of the cut cover**, when `θ` is there the
difference of the restrictions of `s^m · a` and of `s^m · b`. -/
theorem hrestrict_cutInter_actPow (q M m : ℕ)
    (θ : gradedPiece X L F q (U ⊓ V) (m : ℤ))
    (a : (Hgroup X.ringCatSheaf (U ⊓ nonvanishingOpen L s) q F : Type u))
    (b : (Hgroup X.ringCatSheaf (V ⊓ nonvanishingOpen L s) q F : Type u))
    (hab : Hrestrict X.ringCatSheaf (inf_le_left : (U ⊓ nonvanishingOpen L s) ⊓
            (V ⊓ nonvanishingOpen L s) ≤ U ⊓ nonvanishingOpen L s) q (twist X L F (m : ℤ))
          (mulPow X L s F q (U ⊓ nonvanishingOpen L s) m a) -
        Hrestrict X.ringCatSheaf (inf_le_right : (U ⊓ nonvanishingOpen L s) ⊓
            (V ⊓ nonvanishingOpen L s) ≤ V ⊓ nonvanishingOpen L s) q (twist X L F (m : ℤ))
          (mulPow X L s F q (V ⊓ nonvanishingOpen L s) m b) =
      Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) q (twist X L F (m : ℤ)) θ) :
    Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) q (twist X L F ((M + m : ℕ) : ℤ))
        (actPow X L s F q (U ⊓ V) M m θ) =
      mulPow X L s F q ((U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s)) (M + m)
          (Hrestrict X.ringCatSheaf (inf_le_left : (U ⊓ nonvanishingOpen L s) ⊓
            (V ⊓ nonvanishingOpen L s) ≤ U ⊓ nonvanishingOpen L s) q F a) -
        mulPow X L s F q ((U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s)) (M + m)
          (Hrestrict X.ringCatSheaf (inf_le_right : (U ⊓ nonvanishingOpen L s) ⊓
            (V ⊓ nonvanishingOpen L s) ≤ V ⊓ nonvanishingOpen L s) q F b) := by
  rw [hrestrict_actPow, ← hab, actPow_sub, hrestrict_mulPow, hrestrict_mulPow,
    actPow_mulPow, actPow_mulPow]

/-- **The correction term of the kernel chase dies on the intersection of the cut cover.** The
two lifts `α` and `β` reproduce there, after multiplication by `s^M`, exactly the difference of
restrictions that `θ` is on the nonvanishing open. -/
theorem restrict_cutInter_correction_eq_zero (q M m : ℕ)
    (θ : gradedPiece X L F q (U ⊓ V) (m : ℤ))
    (a : (Hgroup X.ringCatSheaf (U ⊓ nonvanishingOpen L s) q F : Type u))
    (b : (Hgroup X.ringCatSheaf (V ⊓ nonvanishingOpen L s) q F : Type u))
    (α : gradedPiece X L F q U ((M + m : ℕ) : ℤ))
    (β : gradedPiece X L F q V ((M + m : ℕ) : ℤ))
    (hα : Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ nonvanishingOpen L s ≤ U) q
      (twist X L F ((M + m : ℕ) : ℤ)) α =
        mulPow X L s F q (U ⊓ nonvanishingOpen L s) (M + m) a)
    (hβ : Hrestrict X.ringCatSheaf (inf_le_left : V ⊓ nonvanishingOpen L s ≤ V) q
      (twist X L F ((M + m : ℕ) : ℤ)) β =
        mulPow X L s F q (V ⊓ nonvanishingOpen L s) (M + m) b)
    (hab : Hrestrict X.ringCatSheaf (inf_le_left : (U ⊓ nonvanishingOpen L s) ⊓
            (V ⊓ nonvanishingOpen L s) ≤ U ⊓ nonvanishingOpen L s) q (twist X L F (m : ℤ))
          (mulPow X L s F q (U ⊓ nonvanishingOpen L s) m a) -
        Hrestrict X.ringCatSheaf (inf_le_right : (U ⊓ nonvanishingOpen L s) ⊓
            (V ⊓ nonvanishingOpen L s) ≤ V ⊓ nonvanishingOpen L s) q (twist X L F (m : ℤ))
          (mulPow X L s F q (V ⊓ nonvanishingOpen L s) m b) =
      Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) q (twist X L F (m : ℤ)) θ) :
    Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) q
        (twist X L F ((M + m : ℕ) : ℤ))
        (Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ V ≤ U) q
              (twist X L F ((M + m : ℕ) : ℤ)) α -
            Hrestrict X.ringCatSheaf (inf_le_right : U ⊓ V ≤ V) q
              (twist X L F ((M + m : ℕ) : ℤ)) β -
          actPow X L s F q (U ⊓ V) M m θ) = 0 := by
  rw [map_sub, hrestrict_cutInter_sub_lift X L s F U V q (M + m) a b α β hα hβ,
    hrestrict_cutInter_actPow X L s F U V q M m θ a b hab]
  exact sub_self _

include hU hV hUV in
/-- **The connecting morphism kills the corrected class.** If `s^j` turns the correction of `θ`
into a difference of restrictions from `U` and from `V`, then `s^j · s^M · δθ` vanishes. -/
theorem actPow_ambientDelta_eq_zero (q j M m : ℕ)
    (θ : gradedPiece X L F q (U ⊓ V) (m : ℤ))
    (α : gradedPiece X L F q U ((M + m : ℕ) : ℤ))
    (β : gradedPiece X L F q V ((M + m : ℕ) : ℤ))
    (hsplit : actPow X L s F q (U ⊓ V) j (M + m)
        (Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ V ≤ U) q
              (twist X L F ((M + m : ℕ) : ℤ)) α -
            Hrestrict X.ringCatSheaf (inf_le_right : U ⊓ V ≤ V) q
              (twist X L F ((M + m : ℕ) : ℤ)) β) =
      actPow X L s F q (U ⊓ V) j (M + m) (actPow X L s F q (U ⊓ V) M m θ)) :
    actPow X L s F (q + 1) W j (M + m)
        (actPow X L s F (q + 1) W M m
          ((ambientDelta X.ringCatSheaf W U V hU hV hUV q).app
            (twist X L F (m : ℤ)) θ)) = 0 := by
  rw [← ambientDelta_actPow X L s F W U V hU hV hUV q M m θ,
    ← ambientDelta_actPow X L s F W U V hU hV hUV q j (M + m)
      (actPow X L s F q (U ⊓ V) M m θ),
    ← hsplit, ambientDelta_actPow X L s F W U V hU hV hUV q j (M + m) _,
    ambientDelta_restrict_sub X.ringCatSheaf U V (twist X L F ((M + m : ℕ) : ℤ)) W hU hV hUV
      q α β, actPow_zero]

include hU hV hUV in
/-- **The Mayer--Vietoris step for the kernel statement, in degree zero.** A class on `W` killed
by a power of `s` on both members of the cover is zero, by the leading monomorphism of the
Mayer--Vietoris sequence. -/
theorem restrictKernelTorsion_sup_zero
    (hkU : RestrictKernelTorsion X L s F 0 U) (hkV : RestrictKernelTorsion X L s F 0 V) :
    RestrictKernelTorsion X L s F 0 W := by
  intro n ξ hξ
  replace hξ : Hrestrict X.ringCatSheaf (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) 0
    (twist X L F (n : ℤ)) ξ = 0 := hξ
  obtain ⟨K, h1, h2⟩ := exists_actPow_restrict_eq_zero X L s F W U V hU hV 0 hkU hkV n ξ hξ
  exact ⟨K, eq_zero_of_restrict_eq_zero X.ringCatSheaf U V
    (twist X L F ((K + n : ℕ) : ℤ)) W hU hV hUV (actPow X L s F 0 W K n ξ) h1 h2⟩

include hU hV hUV in
/-- **The Mayer--Vietoris step for the kernel statement, in positive degree.** After
multiplication by a power of `s` the class dies on both members of the cover, so it is a
connecting image `δ θ`. On the nonvanishing open `θ` is a difference of restrictions, by
exactness of the cut Mayer--Vietoris sequence, and each summand is `s^{-n}` times a class coming
from `U`, respectively from `V`. The difference of those two classes corrects `θ` up to a class
dying on the nonvanishing open, which a power of `s` kills; and `δ` kills a difference of
restrictions. -/
theorem restrictKernelTorsion_sup_succ (q : ℕ)
    (hkU : RestrictKernelTorsion X L s F (q + 1) U)
    (hkV : RestrictKernelTorsion X L s F (q + 1) V)
    (hkI : RestrictKernelTorsion X L s F q (U ⊓ V))
    (hsU : RestrictPowerSurjective X L s F q U)
    (hsV : RestrictPowerSurjective X L s F q V) :
    RestrictKernelTorsion X L s F (q + 1) W := by
  intro n ξ hξ
  replace hξ : Hrestrict X.ringCatSheaf (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) (q + 1)
    (twist X L F (n : ℤ)) ξ = 0 := hξ
  obtain ⟨K, h1, h2⟩ :=
    exists_actPow_restrict_eq_zero X L s F W U V hU hV (q + 1) hkU hkV n ξ hξ
  obtain ⟨θ, hθ⟩ := exists_ambientDelta_eq X.ringCatSheaf U V
    (twist X L F ((K + n : ℕ) : ℤ)) W hU hV hUV q (actPow X L s F (q + 1) W K n ξ) h1 h2
  have hδ0 : (ambientDelta X.ringCatSheaf (W ⊓ nonvanishingOpen L s)
        (U ⊓ nonvanishingOpen L s) (V ⊓ nonvanishingOpen L s)
        (inf_le_inf_right (nonvanishingOpen L s) hU)
        (inf_le_inf_right (nonvanishingOpen L s) hV)
        (sup_cut_eq X L s W U V hUV) q).app (twist X L F ((K + n : ℕ) : ℤ))
      (Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) q
        (twist X L F ((K + n : ℕ) : ℤ)) θ) = 0 := by
    rw [ambientDelta_cut_restrict X L s W U V hU hV hUV (twist X L F ((K + n : ℕ) : ℤ)) q θ,
      hθ, hrestrict_actPow, hξ, actPow_zero]
  obtain ⟨a, b, hab⟩ := exists_restrict_sub_eq_of_ambientDelta_eq_zero X.ringCatSheaf
    (U ⊓ nonvanishingOpen L s) (V ⊓ nonvanishingOpen L s) (twist X L F ((K + n : ℕ) : ℤ))
    (W ⊓ nonvanishingOpen L s) (inf_le_inf_right (nonvanishingOpen L s) hU)
    (inf_le_inf_right (nonvanishingOpen L s) hV) (sup_cut_eq X L s W U V hUV) q
    (Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) q
      (twist X L F ((K + n : ℕ) : ℤ)) θ) hδ0
  obtain ⟨a', ha'⟩ := exists_mulPow_eq X L s F q (U ⊓ nonvanishingOpen L s) inf_le_right
    (K + n) a
  obtain ⟨b', hb'⟩ := exists_mulPow_eq X L s F q (V ⊓ nonvanishingOpen L s) inf_le_right
    (K + n) b
  rw [← ha', ← hb'] at hab
  obtain ⟨n₁, α₀, hα₀⟩ := hsU a'
  obtain ⟨n₂, β₀, hβ₀⟩ := hsV b'
  obtain ⟨α, hα⟩ := exists_restrict_eq_mulPow_of_le X L s F q U
    ((le_max_left n₁ n₂).trans (Nat.le_add_right _ (K + n))) a' α₀ hα₀
  obtain ⟨β, hβ⟩ := exists_restrict_eq_mulPow_of_le X L s F q V
    ((le_max_right n₁ n₂).trans (Nat.le_add_right _ (K + n))) b' β₀ hβ₀
  obtain ⟨j, hj⟩ := hkI (max n₁ n₂ + (K + n))
    (Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ V ≤ U) q
          (twist X L F ((max n₁ n₂ + (K + n) : ℕ) : ℤ)) α -
        Hrestrict X.ringCatSheaf (inf_le_right : U ⊓ V ≤ V) q
          (twist X L F ((max n₁ n₂ + (K + n) : ℕ) : ℤ)) β -
      actPow X L s F q (U ⊓ V) (max n₁ n₂) (K + n) θ)
    (restrict_cut_eq_zero X L s U V (twist X L F ((max n₁ n₂ + (K + n) : ℕ) : ℤ)) q _
      (restrict_cutInter_correction_eq_zero X L s F U V q (max n₁ n₂) (K + n) θ a' b'
        α β hα hβ hab))
  replace hj : actPow X L s F q (U ⊓ V) j (max n₁ n₂ + (K + n))
      (Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ V ≤ U) q
            (twist X L F ((max n₁ n₂ + (K + n) : ℕ) : ℤ)) α -
          Hrestrict X.ringCatSheaf (inf_le_right : U ⊓ V ≤ V) q
            (twist X L F ((max n₁ n₂ + (K + n) : ℕ) : ℤ)) β -
        actPow X L s F q (U ⊓ V) (max n₁ n₂) (K + n) θ) = 0 := hj
  rw [actPow_sub] at hj
  refine ⟨j + max n₁ n₂ + K, actPow_eq_zero_of_actPow_actPow X L s F (q + 1) W j
    (max n₁ n₂) K n ξ ?_⟩
  rw [← hθ]
  exact actPow_ambientDelta_eq_zero X L s F W U V hU hV hUV q j (max n₁ n₂) (K + n) θ α β
    (sub_eq_zero.mp hj)

include hU hV hUV in
/-- **The Mayer--Vietoris step for the kernel statement.** If the kernel of restriction to the
nonvanishing open is `s`-power torsion over `U`, over `V` and over `U ⊓ V` in every degree, and
every class over `U` and over `V` is `s^{-n}` times a twisted class in every degree, then the
kernel statement holds over `U ⊔ V`. -/
theorem restrictKernelTorsion_sup
    (hkU : ∀ q, RestrictKernelTorsion X L s F q U)
    (hkV : ∀ q, RestrictKernelTorsion X L s F q V)
    (hkI : ∀ q, RestrictKernelTorsion X L s F q (U ⊓ V))
    (hsU : ∀ q, RestrictPowerSurjective X L s F q U)
    (hsV : ∀ q, RestrictPowerSurjective X L s F q V)
    (p : ℕ) : RestrictKernelTorsion X L s F p W := by
  cases p with
  | zero => exact restrictKernelTorsion_sup_zero X L s F W U V hU hV hUV (hkU 0) (hkV 0)
  | succ q =>
    exact restrictKernelTorsion_sup_succ X L s F W U V hU hV hUV q (hkU (q + 1))
      (hkV (q + 1)) (hkI q) (hsU q) (hsV q)

include hU hV in
/-- **Two lifts of one class on `W ⊓ X_s` agree on the intersection of the cut cover.** -/
theorem restrict_cutInter_sub_eq_zero (q N : ℕ)
    (y : (Hgroup X.ringCatSheaf (W ⊓ nonvanishingOpen L s) q F : Type u))
    (α : gradedPiece X L F q U (N : ℤ)) (β : gradedPiece X L F q V (N : ℤ))
    (hα : Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ nonvanishingOpen L s ≤ U) q
      (twist X L F (N : ℤ)) α = mulPow X L s F q (U ⊓ nonvanishingOpen L s) N
        (Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hU) q F y))
    (hβ : Hrestrict X.ringCatSheaf (inf_le_left : V ⊓ nonvanishingOpen L s ≤ V) q
      (twist X L F (N : ℤ)) β = mulPow X L s F q (V ⊓ nonvanishingOpen L s) N
        (Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hV) q F y)) :
    Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) q (twist X L F (N : ℤ))
        (Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ V ≤ U) q (twist X L F (N : ℤ)) α -
          Hrestrict X.ringCatSheaf (inf_le_right : U ⊓ V ≤ V) q
            (twist X L F (N : ℤ)) β) = 0 := by
  rw [hrestrict_cutInter_sub_lift X L s F U V q N
      (Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hU) q F y)
      (Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hV) q F y) α β hα hβ,
    hrestrict_comp_apply X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hU)
      (inf_le_left : (U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s) ≤
        U ⊓ nonvanishingOpen L s)
      ((inf_le_left : (U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s) ≤
        U ⊓ nonvanishingOpen L s).trans (inf_le_inf_right (nonvanishingOpen L s) hU)) q F y,
    hrestrict_comp_apply X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hV)
      (inf_le_right : (U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s) ≤
        V ⊓ nonvanishingOpen L s)
      ((inf_le_right : (U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s) ≤
        V ⊓ nonvanishingOpen L s).trans (inf_le_inf_right (nonvanishingOpen L s) hV)) q F y]
  exact sub_self _

/-- **The glued class matches `s^{m + M} · y` on each member of the cut cover.** -/
theorem restrict_cut_glued_eq (q m M : ℕ) (A : X.Opens) (hA : A ≤ W)
    (y : (Hgroup X.ringCatSheaf (W ⊓ nonvanishingOpen L s) q F : Type u))
    (α : gradedPiece X L F q A (M : ℤ))
    (hα : Hrestrict X.ringCatSheaf (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A) q
      (twist X L F (M : ℤ)) α = mulPow X L s F q (A ⊓ nonvanishingOpen L s) M
        (Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hA) q F y))
    (ζ : gradedPiece X L F q W ((m + M : ℕ) : ℤ))
    (hζ : Hrestrict X.ringCatSheaf hA q (twist X L F ((m + M : ℕ) : ℤ)) ζ =
      actPow X L s F q A m M α) :
    Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hA) q
        (twist X L F ((m + M : ℕ) : ℤ))
        (Hrestrict X.ringCatSheaf (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) q
            (twist X L F ((m + M : ℕ) : ℤ)) ζ -
          mulPow X L s F q (W ⊓ nonvanishingOpen L s) (m + M) y) = 0 := by
  rw [map_sub, hrestrict_comp_apply X.ringCatSheaf
      (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)
      (inf_le_inf_right (nonvanishingOpen L s) hA)
      ((inf_le_inf_right (nonvanishingOpen L s) hA).trans
        (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)) q _ ζ,
    ← hrestrict_comp_apply X.ringCatSheaf hA
      (inf_le_left : A ⊓ nonvanishingOpen L s ≤ A)
      ((inf_le_inf_right (nonvanishingOpen L s) hA).trans
        (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W)) q _ ζ,
    hζ, hrestrict_actPow, hα, actPow_mulPow, hrestrict_mulPow]
  exact sub_self _

include hUV in
/-- **The first half of the surjectivity chase.** After multiplication by a power of `s`, a class
on `W ⊓ X_s` is matched on both members of the cut cover by the restriction of a class of a twist
on `W`.  The two lifts coming from `U` and from `V` are made to agree on `U ⊓ V` by the kernel
statement there, and are then glued by exactness of the Mayer--Vietoris sequence at the
biproduct. -/
theorem exists_restrict_sub_mulPow_eq_zero (p : ℕ)
    (hsU : RestrictPowerSurjective X L s F p U)
    (hsV : RestrictPowerSurjective X L s F p V)
    (hkI : RestrictKernelTorsion X L s F p (U ⊓ V))
    (y : (Hgroup X.ringCatSheaf (W ⊓ nonvanishingOpen L s) p F : Type u)) :
    ∃ (D : ℕ) (ζ : gradedPiece X L F p W (D : ℤ)),
      Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hU) p
          (twist X L F (D : ℤ))
          (Hrestrict X.ringCatSheaf (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) p
              (twist X L F (D : ℤ)) ζ -
            mulPow X L s F p (W ⊓ nonvanishingOpen L s) D y) = 0 ∧
        Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hV) p
          (twist X L F (D : ℤ))
          (Hrestrict X.ringCatSheaf (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) p
              (twist X L F (D : ℤ)) ζ -
            mulPow X L s F p (W ⊓ nonvanishingOpen L s) D y) = 0 := by
  obtain ⟨n₁, ξ₁, hξ₁⟩ := hsU (Hrestrict X.ringCatSheaf
    (inf_le_inf_right (nonvanishingOpen L s) hU) p F y)
  obtain ⟨n₂, ξ₂, hξ₂⟩ := hsV (Hrestrict X.ringCatSheaf
    (inf_le_inf_right (nonvanishingOpen L s) hV) p F y)
  obtain ⟨α, hα⟩ := exists_restrict_eq_mulPow_of_le X L s F p U (le_max_left n₁ n₂)
    (Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hU) p F y) ξ₁ hξ₁
  obtain ⟨β, hβ⟩ := exists_restrict_eq_mulPow_of_le X L s F p V (le_max_right n₁ n₂)
    (Hrestrict X.ringCatSheaf (inf_le_inf_right (nonvanishingOpen L s) hV) p F y) ξ₂ hξ₂
  obtain ⟨m, hm⟩ := hkI (max n₁ n₂)
    (Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ V ≤ U) p
        (twist X L F ((max n₁ n₂ : ℕ) : ℤ)) α -
      Hrestrict X.ringCatSheaf (inf_le_right : U ⊓ V ≤ V) p
        (twist X L F ((max n₁ n₂ : ℕ) : ℤ)) β)
    (restrict_cut_eq_zero X L s U V (twist X L F ((max n₁ n₂ : ℕ) : ℤ)) p _
      (restrict_cutInter_sub_eq_zero X L s F W U V hU hV p (max n₁ n₂) y α β hα hβ))
  replace hm : actPow X L s F p (U ⊓ V) m (max n₁ n₂)
      (Hrestrict X.ringCatSheaf (inf_le_left : U ⊓ V ≤ U) p
          (twist X L F ((max n₁ n₂ : ℕ) : ℤ)) α -
        Hrestrict X.ringCatSheaf (inf_le_right : U ⊓ V ≤ V) p
          (twist X L F ((max n₁ n₂ : ℕ) : ℤ)) β) = 0 := hm
  rw [actPow_sub, ← hrestrict_actPow, ← hrestrict_actPow] at hm
  obtain ⟨ζ, hζU, hζV⟩ := exists_restrict_eq_of_restrict_inf_eq X.ringCatSheaf U V
    (twist X L F ((m + max n₁ n₂ : ℕ) : ℤ)) W hU hV hUV p
    (actPow X L s F p U m (max n₁ n₂) α) (actPow X L s F p V m (max n₁ n₂) β)
    (sub_eq_zero.mp hm)
  exact ⟨m + max n₁ n₂, ζ,
    restrict_cut_glued_eq X L s F W p m (max n₁ n₂) U hU y α hα ζ hζU,
    restrict_cut_glued_eq X L s F W p m (max n₁ n₂) V hV y β hβ ζ hζV⟩

include hU hV hUV in
/-- **The lift of the defect, read through the connecting morphism.** The class `κ` on `U ⊓ V`
lifting `θ` out of the nonvanishing open has connecting image on `W` restricting to `s^{n₃}`
times the defect `z`. -/
theorem hrestrict_ambientDelta_eq_actPow (r D n₃ : ℕ)
    (z : gradedPiece X L F (r + 1) (W ⊓ nonvanishingOpen L s) (D : ℤ))
    (θ : gradedPiece X L F r
      ((U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s)) (D : ℤ))
    (hθ : (ambientDelta X.ringCatSheaf (W ⊓ nonvanishingOpen L s)
        (U ⊓ nonvanishingOpen L s) (V ⊓ nonvanishingOpen L s)
        (inf_le_inf_right (nonvanishingOpen L s) hU)
        (inf_le_inf_right (nonvanishingOpen L s) hV)
        (sup_cut_eq X L s W U V hUV) r).app (twist X L F (D : ℤ)) θ = z)
    (θ₁ : (Hgroup X.ringCatSheaf ((U ⊓ V) ⊓ nonvanishingOpen L s) r F : Type u))
    (hθ₁ : Hrestrict X.ringCatSheaf
        (le_of_eq (inf_cut_inf_cut X U V (nonvanishingOpen L s))) r (twist X L F (D : ℤ))
        (mulPow X L s F r ((U ⊓ V) ⊓ nonvanishingOpen L s) D θ₁) = θ)
    (κ : gradedPiece X L F r (U ⊓ V) ((n₃ + D : ℕ) : ℤ))
    (hκ : Hrestrict X.ringCatSheaf
        (inf_le_left : (U ⊓ V) ⊓ nonvanishingOpen L s ≤ U ⊓ V) r
        (twist X L F ((n₃ + D : ℕ) : ℤ)) κ =
      mulPow X L s F r ((U ⊓ V) ⊓ nonvanishingOpen L s) (n₃ + D) θ₁) :
    Hrestrict X.ringCatSheaf (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) (r + 1)
        (twist X L F ((n₃ + D : ℕ) : ℤ))
        ((ambientDelta X.ringCatSheaf W U V hU hV hUV r).app
          (twist X L F ((n₃ + D : ℕ) : ℤ)) κ) =
      actPow X L s F (r + 1) (W ⊓ nonvanishingOpen L s) n₃ D z := by
  have hinner : Hrestrict X.ringCatSheaf (cutInter_le_inf X L s U V) r
        (twist X L F ((n₃ + D : ℕ) : ℤ)) κ =
      actPow X L s F r ((U ⊓ nonvanishingOpen L s) ⊓ (V ⊓ nonvanishingOpen L s)) n₃ D θ := by
    rw [← hrestrict_comp_apply X.ringCatSheaf
        (inf_le_left : (U ⊓ V) ⊓ nonvanishingOpen L s ≤ U ⊓ V)
        (le_of_eq (inf_cut_inf_cut X U V (nonvanishingOpen L s)))
        (cutInter_le_inf X L s U V) r (twist X L F ((n₃ + D : ℕ) : ℤ)) κ,
      hκ, hrestrict_mulPow, ← hθ₁, hrestrict_mulPow, actPow_mulPow]
  rw [← ambientDelta_cut_restrict X L s W U V hU hV hUV (twist X L F ((n₃ + D : ℕ) : ℤ)) r κ,
    ← hθ, ← ambientDelta_actPow X L s F (W ⊓ nonvanishingOpen L s)
      (U ⊓ nonvanishingOpen L s) (V ⊓ nonvanishingOpen L s)
      (inf_le_inf_right (nonvanishingOpen L s) hU)
      (inf_le_inf_right (nonvanishingOpen L s) hV) (sup_cut_eq X L s W U V hUV) r n₃ D θ,
    hinner]

include hU hV hUV in
/-- **The Mayer--Vietoris step for the surjectivity statement, in degree zero.** The defect dies
on both members of the cut cover, so it is zero by the leading monomorphism of the cut
Mayer--Vietoris sequence. -/
theorem restrictPowerSurjective_sup_zero
    (hsU : RestrictPowerSurjective X L s F 0 U)
    (hsV : RestrictPowerSurjective X L s F 0 V)
    (hkI : RestrictKernelTorsion X L s F 0 (U ⊓ V)) :
    RestrictPowerSurjective X L s F 0 W := by
  intro y
  obtain ⟨D, ζ, h1, h2⟩ :=
    exists_restrict_sub_mulPow_eq_zero X L s F W U V hU hV hUV 0 hsU hsV hkI y
  exact ⟨D, ζ, sub_eq_zero.mp (eq_zero_of_restrict_eq_zero X.ringCatSheaf
    (U ⊓ nonvanishingOpen L s) (V ⊓ nonvanishingOpen L s) (twist X L F (D : ℤ))
    (W ⊓ nonvanishingOpen L s) (inf_le_inf_right (nonvanishingOpen L s) hU)
    (inf_le_inf_right (nonvanishingOpen L s) hV) (sup_cut_eq X L s W U V hUV) _ h1 h2)⟩

include hU hV hUV in
/-- **The Mayer--Vietoris step for the surjectivity statement, in positive degree.** The defect
dies on both members of the cut cover, so it is the connecting image of a class `θ` on their
intersection; `θ` is `s^D` times an untwisted class there, which the surjectivity statement over
`U ⊓ V` lifts to a class `κ` on `U ⊓ V`. Subtracting the connecting image of `κ` corrects the
glued class, after one more multiplication by a power of `s`. -/
theorem restrictPowerSurjective_sup_succ (r : ℕ)
    (hsU : RestrictPowerSurjective X L s F (r + 1) U)
    (hsV : RestrictPowerSurjective X L s F (r + 1) V)
    (hkI : RestrictKernelTorsion X L s F (r + 1) (U ⊓ V))
    (hsI : RestrictPowerSurjective X L s F r (U ⊓ V)) :
    RestrictPowerSurjective X L s F (r + 1) W := by
  intro y
  obtain ⟨D, ζ, h1, h2⟩ :=
    exists_restrict_sub_mulPow_eq_zero X L s F W U V hU hV hUV (r + 1) hsU hsV hkI y
  obtain ⟨θ, hθ⟩ := exists_ambientDelta_eq X.ringCatSheaf (U ⊓ nonvanishingOpen L s)
    (V ⊓ nonvanishingOpen L s) (twist X L F (D : ℤ)) (W ⊓ nonvanishingOpen L s)
    (inf_le_inf_right (nonvanishingOpen L s) hU)
    (inf_le_inf_right (nonvanishingOpen L s) hV) (sup_cut_eq X L s W U V hUV) r _ h1 h2
  obtain ⟨θ₀, hθ₀⟩ := exists_restrict_inf_cut_eq X L s (twist X L F (D : ℤ)) r U V θ
  obtain ⟨θ₁, hθ₁'⟩ := exists_mulPow_eq X L s F r ((U ⊓ V) ⊓ nonvanishingOpen L s)
    inf_le_right D θ₀
  have hθ₁ : Hrestrict X.ringCatSheaf
      (le_of_eq (inf_cut_inf_cut X U V (nonvanishingOpen L s))) r (twist X L F (D : ℤ))
      (mulPow X L s F r ((U ⊓ V) ⊓ nonvanishingOpen L s) D θ₁) = θ := by
    rw [hθ₁']; exact hθ₀
  obtain ⟨n₃, κ₀, hκ₀⟩ := hsI θ₁
  obtain ⟨κ, hκ⟩ := exists_restrict_eq_mulPow_of_le X L s F r (U ⊓ V)
    (Nat.le_add_right n₃ D) θ₁ κ₀ hκ₀
  have hdel := hrestrict_ambientDelta_eq_actPow X L s F W U V hU hV hUV r D n₃ _ θ hθ θ₁ hθ₁
    κ hκ
  have hfinal : Hrestrict X.ringCatSheaf (inf_le_left : W ⊓ nonvanishingOpen L s ≤ W) (r + 1)
        (twist X L F ((n₃ + D : ℕ) : ℤ))
        (actPow X L s F (r + 1) W n₃ D ζ -
          (ambientDelta X.ringCatSheaf W U V hU hV hUV r).app
            (twist X L F ((n₃ + D : ℕ) : ℤ)) κ) =
      mulPow X L s F (r + 1) (W ⊓ nonvanishingOpen L s) (n₃ + D) y := by
    rw [map_sub, hdel, hrestrict_actPow, actPow_sub, actPow_mulPow]
    exact sub_sub_cancel _ _
  exact ⟨n₃ + D, _, hfinal⟩

include hU hV hUV in
/-- **The Mayer--Vietoris step for the surjectivity statement.** -/
theorem restrictPowerSurjective_sup
    (hsU : ∀ q, RestrictPowerSurjective X L s F q U)
    (hsV : ∀ q, RestrictPowerSurjective X L s F q V)
    (hkI : ∀ q, RestrictKernelTorsion X L s F q (U ⊓ V))
    (hsI : ∀ q, RestrictPowerSurjective X L s F q (U ⊓ V))
    (p : ℕ) : RestrictPowerSurjective X L s F p W := by
  cases p with
  | zero =>
    exact restrictPowerSurjective_sup_zero X L s F W U V hU hV hUV (hsU 0) (hsV 0) (hkI 0)
  | succ r =>
    exact restrictPowerSurjective_sup_succ X L s F W U V hU hV hUV r (hsU (r + 1))
      (hsV (r + 1)) (hkI (r + 1)) (hsI r)

end Step

/-! ### The induction over the quasi-compact opens

With the Mayer--Vietoris step in hand the induction principle of [Stacks, Tag 08DR] propagates
both numerator statements from the affine opens to every quasi-compact open of a quasi-separated
scheme. Over an affine open they hold in every **positive** degree, because there both groups
vanish; in degree zero they are the statement of [Stacks, Tag 01PW] (2) over an affine open, read
through the identification of degree-zero cohomology with sections. -/

section Induction

/-- **Both numerator statements of [Stacks, Tag 09MR], in every degree**: the property of an open
which the induction principle of [Stacks, Tag 08DR] propagates. -/
def RestrictNumerators (A : X.Opens) : Prop :=
  ∀ q, RestrictKernelTorsion X L s F q A ∧ RestrictPowerSurjective X L s F q A

/-- **The Mayer--Vietoris step for both numerator statements**, in the shape the induction
principle of [Stacks, Tag 08DR] consumes. -/
theorem restrictNumerators_sup (U V : X.Opens)
    (hPU : RestrictNumerators X L s F U) (hPV : RestrictNumerators X L s F V)
    (hPI : RestrictNumerators X L s F (U ⊓ V)) : RestrictNumerators X L s F (U ⊔ V) := fun q =>
  ⟨restrictKernelTorsion_sup X L s F (U ⊔ V) U V le_sup_left le_sup_right rfl
      (fun q => (hPU q).1) (fun q => (hPV q).1) (fun q => (hPI q).1)
      (fun q => (hPU q).2) (fun q => (hPV q).2) q,
    restrictPowerSurjective_sup X L s F (U ⊔ V) U V le_sup_left le_sup_right rfl
      (fun q => (hPU q).2) (fun q => (hPV q).2) (fun q => (hPI q).1) (fun q => (hPI q).2) q⟩

variable [F.IsQuasicoherent]

/-- **Both numerator statements hold over an affine open in every positive degree**, because both
cohomology groups involved vanish there. -/
theorem restrictNumerators_of_isAffineOpen_of_pos (A : X.Opens) (hA : IsAffineOpen A) (q : ℕ)
    (hq : 0 < q) :
    RestrictKernelTorsion X L s F q A ∧ RestrictPowerSurjective X L s F q A :=
  ⟨restrictKernelTorsion_of_isAffineOpen X L s F q A hA hq,
    restrictPowerSurjective_of_isAffineOpen X L s F q A hA hq⟩

/-- **The degree-zero cohomology over an open contained in `⊥` is trivial**, because its module
of sections is. -/
theorem subsingleton_hgroup_zero_of_le_bot (G : X.Modules) {V : X.Opens} (hV : V ≤ ⊥) :
    Subsingleton (Hgroup X.ringCatSheaf V 0 G : Type u) := by
  refine ⟨fun a b => ?_⟩
  have h1 : toSection X G V a = 0 :=
    Stacks.AlgebraicGeometry.QcqsLocalizedRestriction.eq_zero_of_le_bot G hV _
  have h2 : toSection X G V b = 0 :=
    Stacks.AlgebraicGeometry.QcqsLocalizedRestriction.eq_zero_of_le_bot G hV _
  exact (bijective_toSection X G V).1 (h1.trans h2.symm)

/-- **Both numerator statements hold over the empty open**, where every cohomology group in sight
is trivial: in positive degree by the affine vanishing, in degree zero because the sections over
`⊥` vanish. -/
theorem restrictNumerators_bot : RestrictNumerators X L s F ⊥ := by
  intro q
  cases q with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro n ξ _
      have : Subsingleton (gradedPiece X L F 0 ⊥ (n : ℤ)) :=
        subsingleton_hgroup_zero_of_le_bot X (twist X L F (n : ℤ)) le_rfl
      refine ⟨0, ?_⟩
      rw [Subsingleton.elim ξ 0]
      exact map_zero _
    · intro y
      have : Subsingleton
          (Hgroup X.ringCatSheaf (nonvanishingPart X L s ⊥) 0 F : Type u) :=
        subsingleton_hgroup_zero_of_le_bot X F inf_le_left
      refine ⟨0, 0, ?_⟩
      rw [Subsingleton.elim y 0, map_zero, map_zero]
  | succ r =>
    exact restrictNumerators_of_isAffineOpen_of_pos X L s F ⊥ (isAffineOpen_bot X) (r + 1)
      (Nat.succ_pos r)

/-- **Both numerator statements of [Stacks, Tag 09MR] over an affine open, in every degree.**

In positive degree this is the vanishing of both groups. In degree zero the kernel statement is
part (1) of [Stacks, Tag 01PW] over a quasi-compact open, available over every affine open; the
surjectivity statement is [Stacks, Tag 01P7] on a chart, available over an affine open carrying a
frame of `ℒ`. The affine opens carrying a frame of `ℒ` are a basis, so the second induction of
[Stacks, Tag 08DR] -- `Stacks.AlgebraicGeometry.CompactOpenInduction.of_isAffineOpen_of_locally`,
whose Mayer--Vietoris step is `restrictNumerators_sup` again -- propagates the conjunction from
them to the affine open itself. Carrying a frame is inherited by smaller opens, which is what
that induction needs of it. -/
theorem restrictNumerators_of_isAffineOpen (A : X.Opens) (hA : IsAffineOpen A) :
    RestrictNumerators X L s F A := by
  refine Stacks.AlgebraicGeometry.CompactOpenInduction.of_isAffineOpen_of_locally
    (T := fun U => Nonempty (GeneratorSections X.toRingedSpace L U))
    (P := RestrictNumerators X L s F)
    (fun U V hUV hV => ⟨generatorRestrict L hUV hV.some⟩)
    (restrictNumerators_bot X L s F)
    (fun U hU hTU q => ?_)
    (fun U V _ _ hPU hPV hPI => restrictNumerators_sup X L s F U V hPU hPV hPI)
    A hA ?_
  · cases q with
    | zero =>
      exact ⟨restrictKernelTorsion_zero_of_isCompact X L s F U hU.isCompact,
        restrictPowerSurjective_zero_of_generator X L s F hTU.some hU le_rfl⟩
    | succ r =>
      exact restrictNumerators_of_isAffineOpen_of_pos X L s F U hU (r + 1) (Nat.succ_pos r)
  · intro x hx
    obtain ⟨W₀, hxW₀, g₀, hg₀⟩ := exists_bijective_smul_of_isInvertible L x
    obtain ⟨f, hfW₀, hxf⟩ := hA.exists_basicOpen_le (V := W₀) ⟨x, hxW₀⟩ hx
    exact ⟨f, hxf, ⟨generatorRestrict L hfW₀
      (⟨g₀, hg₀⟩ : GeneratorSections X.toRingedSpace L W₀)⟩⟩

/-- **Both numerator statements of [Stacks, Tag 09MR] over a quasi-compact open** of a
quasi-separated scheme. The induction is the one of [Stacks, Tag 08DR]: the base case is the
affine open, and the step is the Mayer--Vietoris chase. -/
theorem restrictNumerators_of_isCompact [QuasiSeparatedSpace X]
    (S : X.Opens) (hS : IsCompact (S : Set X)) : RestrictNumerators X L s F S :=
  Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact
    (P := RestrictNumerators X L s F)
    (fun A hA => restrictNumerators_of_isAffineOpen X L s F A hA)
    (fun A B _ _ hPA hPB hPI => restrictNumerators_sup X L s F A B hPA hPB hPI) S hS

/-- **[Stacks, Tag 09MR] over a quasi-compact open of a quasi-separated scheme.** For a
quasi-compact open `S` of a quasi-separated scheme `X`, an invertible `𝒪_X`-module `ℒ`, a global
section `s` of `ℒ`, a quasi-coherent `𝒪_X`-module `ℱ` and any degree `p`, the comparison map

`H^p_*(S, ℒ, ℱ)₍s₎ ⟶ H^p(S ∩ X_s, ℱ)`,  `ξ / sⁿ ↦ s^{-n} ξ`

is bijective. -/
@[stacks 09MR]
theorem bijective_canonicalMap_of_isCompact [QuasiSeparatedSpace X]
    (S : X.Opens) (hS : IsCompact (S : Set X)) (p : ℕ) :
    Function.Bijective (canonicalMap X L s F p S) :=
  bijective_canonicalMap_of_numerators X L s F p S
    (restrictNumerators_of_isCompact X L s F S hS p).1
    (restrictNumerators_of_isCompact X L s F S hS p).2

/-- **[Stacks, Tag 09MR] on a quasi-compact quasi-separated scheme.** -/
@[stacks 09MR]
theorem bijective_canonicalMap_top [QuasiSeparatedSpace X] [CompactSpace X] (p : ℕ) :
    Function.Bijective (canonicalMap X L s F p ⊤) :=
  bijective_canonicalMap_of_isCompact X L s F ⊤
    (by rw [Opens.coe_top]; exact isCompact_univ) p

end Induction

end Stacks.Cohomology.TwistedLocalizationMap

end
