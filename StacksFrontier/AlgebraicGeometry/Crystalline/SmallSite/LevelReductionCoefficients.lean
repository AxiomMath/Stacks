module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CoordinateOperatorsInfinite
public import StacksFrontier.AlgebraicGeometry.Crystalline.ThetaMonomialFamily
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelReductionAssembly

/-!
# Coordinate operators and coefficient inputs of [Stacks, Tag 07JG] over a system of levels

Given a basis of `Ω` indexed by a finite type and a system of levels whose sections are
annihilated as in item (07JB), the connection assembled from the levels has unique coordinate
operators `θ_i`, and they satisfy the coordinate expansion of the connection. This module names
those operators and builds the reduction datum `...SmallSite.LevelReduction07JG` of
[Stacks, Lemma 60.17.3, Tag 07JG] from the composite operators `θ_K = ∏_i θ_i^{k_i}` and the
finiteness of `{K | θ_K(m) ∉ p M}`, or from items (07JD) and (07JE) of that lemma.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `levelCoordinateOperators`: the coordinate operators of the connection assembled from the
  levels, over a system of levels with the annihilation of item (07JB).
* `levelReduction07JGOfThetaPow`: the reduction datum of [Stacks, Tag 07JG] over a system of
  levels, from the composite operators `θ_K` and the finiteness of `{K | θ_K(m) ∉ p M}`.
* `levelReduction07JGOfItems`: the same datum from items (07JD) and (07JE) of the tag.
* `wholeSpaceCoordinateOperators`, `reduction07JGWholeSpaceOfThetaPow` and
  `reduction07JGWholeSpaceOfItems`: the same at the system of levels of
  [Stacks, Proposition 60.21.1, Tag 07JN].

## Main results

* `levelCoordinateOperators_isCoordinateExpansion`: the operators `levelCoordinateOperators` are
  the coordinate operators of the connection.
* `levelCoordinateOperators_map_add`: those operators are additive.
* `nonempty_reduction07JG_of_thetaPow` and `nonempty_reduction07JG_of_items`: the hypothesis
  bundle of [Stacks, Proposition 60.17.4, Tag 07JH] is inhabited from the composite operators and
  the finiteness, and from items (07JD) and (07JE).

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Proposition 60.21.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/


@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### The coordinate operators of the connection of a system of levels -/

section Generic

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {ι : Type uI} [Fintype ι] {p : ℕ} {dx : ι → Omega}
  {L : LevelScalars07JG S D} (R : LevelForms07JG S A D g Omega d L)
  {b : Module.Basis ι (D : Type u) Omega} (E : LevelBaseChangeData R b) (N : ℕ)
  (hdx : ∀ i, dx i = b i)
  (hann : ∀ (F : QuasiCoherentCrystal S) (e : ℕ) (x : L.levelSections F e),
    ((p : (D : Type u)) ^ (N + e)) • x = 0)

/-- **The coordinate operators of the connection assembled from the levels**: the operators `θ_i`
of the coordinate expansion, along the basis `b` of `Ω`, of the completed connection
`M ⟶ M ⊗̂_D Ω` of `...SmallSite.LevelScalars07JG.comparisonOfLevels`. They are unique, by
`Crystalline.eq_of_isCoordinateExpansion`. -/
def levelCoordinateOperators (F : QuasiCoherentCrystal S) :
    ι → (L.sections F → L.sections F) :=
  (Crystalline.exists_isCoordinateExpansion_of_basis p (D : Type u) Omega
    (L.sections F) b hdx
    ((L.comparisonOfLevels F (E.comparison F) (E.comparison_restrict F) b).completedConnection p)
    (L.isPAdicallyComplete_sections p F N (hann F))).choose

/-- **The operators `...SmallSite.levelCoordinateOperators` are the coordinate operators** of the
completed connection assembled from the levels. -/
theorem levelCoordinateOperators_isCoordinateExpansion (F : QuasiCoherentCrystal S) :
    IsCoordinateExpansion p (D : Type u) Omega dx
      ((L.comparisonOfLevels F (E.comparison F) (E.comparison_restrict F) b).completedConnection
        p)
      (levelCoordinateOperators R E N hdx hann F) :=
  (Crystalline.exists_isCoordinateExpansion_of_basis p (D : Type u) Omega
    (L.sections F) b hdx
    ((L.comparisonOfLevels F (E.comparison F) (E.comparison_restrict F) b).completedConnection p)
    (L.isPAdicallyComplete_sections p F N (hann F))).choose_spec

/-- **The reduction datum of [Stacks, Lemma 60.17.3, Tag 07JG] over a system of levels**, from a
family `thetaPow` of composite operators `θ_K` of the operators
`...SmallSite.levelCoordinateOperators` and the finiteness of `{K | θ_K(m) ∉ p M}` for every
section `m`. -/
def levelReduction07JGOfThetaPow
    (thetaPow : ∀ F : QuasiCoherentCrystal S, (ι →₀ ℕ) → (L.sections F → L.sections F))
    (hfam : ∀ F : QuasiCoherentCrystal S, IsThetaMonomialFamily (L.sections F)
      (levelCoordinateOperators R E N hdx hann F) (thetaPow F))
    (hfin : ∀ (F : QuasiCoherentCrystal S) (m : L.sections F),
      {K : ι →₀ ℕ | thetaPow F K m ∉ pSmul p (D : Type u) (L.sections F)}.Finite) :
    LevelReduction07JG S A D g Omega d p dx L :=
  levelReduction07JGOfLevelwise R E N hdx (levelCoordinateOperators R E N hdx hann) thetaPow
    hfam (levelCoordinateOperators_isCoordinateExpansion R E N hdx hann) hfin
    (fun F e x ↦ hann F e x)

/-! ### The two coefficient inputs read as items (07JD) and (07JE) -/

/-- **The coordinate operators of the levels are additive.** -/
theorem levelCoordinateOperators_map_add (F : QuasiCoherentCrystal S) (j : ι)
    (x y : L.sections F) :
    levelCoordinateOperators R E N hdx hann F j (x + y) =
      levelCoordinateOperators R E N hdx hann F j x +
        levelCoordinateOperators R E N hdx hann F j y :=
  _root_.Crystalline.map_add_of_isCoordinateExpansion p (D : Type u) Omega (L.sections F)
    (levelCoordinateOperators_isCoordinateExpansion R E N hdx hann F) b hdx
    (L.isPAdicallyComplete_sections p F N (hann F)).toIsHausdorff j x y

/-- **The reduction datum of [Stacks, Lemma 60.17.3, Tag 07JG] over a system of levels, from
items (07JD) and (07JE) of the tag**: the completed connection assembled from the levels is
integrable (`Crystalline.IsIntegrable`) and topologically quasi-nilpotent
(`Crystalline.IsTopologicallyQuasiNilpotent`). -/
def levelReduction07JGOfItems
    (hint : ∀ F : QuasiCoherentCrystal S, IsIntegrable p (D : Type u) Omega dx
      ((L.comparisonOfLevels F (E.comparison F) (E.comparison_restrict F)
        b).completedConnection p))
    (hqn : ∀ F : QuasiCoherentCrystal S, IsTopologicallyQuasiNilpotent p (D : Type u) Omega dx
      ((L.comparisonOfLevels F (E.comparison F) (E.comparison_restrict F)
        b).completedConnection p)) :
    LevelReduction07JG S A D g Omega d p dx L :=
  levelReduction07JGOfThetaPow R E N hdx hann
    (fun F ↦ (_root_.Crystalline.exists_isThetaMonomialFamily
      (levelCoordinateOperators R E N hdx hann F)
      (hint F _ (levelCoordinateOperators_isCoordinateExpansion R E N hdx hann F))).choose)
    (fun F ↦ (_root_.Crystalline.exists_isThetaMonomialFamily
      (levelCoordinateOperators R E N hdx hann F)
      (hint F _ (levelCoordinateOperators_isCoordinateExpansion R E N hdx hann F))).choose_spec)
    (fun F ↦ _root_.Crystalline.finite_thetaPow_notMem_pSmul_of_isTopologicallyQuasiNilpotent
      p (D : Type u) Omega (L.sections F)
      ((_root_.Crystalline.exists_isThetaMonomialFamily
        (levelCoordinateOperators R E N hdx hann F)
        (hint F _ (levelCoordinateOperators_isCoordinateExpansion R E N hdx hann F))).choose_spec)
      (fun j x y ↦ levelCoordinateOperators_map_add R E N hdx hann F j x y)
      (levelCoordinateOperators_isCoordinateExpansion R E N hdx hann F) b hdx (hqn F))

end Generic

/-! ### At the system of levels of [Stacks, Proposition 60.21.1, Tag 07JN] -/

section WholeSpace

universe uI'

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme] {A : Type u} [CommRing A]
  {g : A →+* (wholeSpaceSystemEnvelope hp 0).ring} {Omega : Type u} [AddCommGroup Omega]
  [Module (wholeSpaceSystemEnvelope hp 0).ring Omega]
  [Module ((wholeSpaceSystemEnvelope hp 0).ring)ᵐᵒᵖ Omega]
  [IsCentralScalar (wholeSpaceSystemEnvelope hp 0).ring Omega]
  {d : DividedPowerDerivation A (wholeSpaceSystemEnvelope hp 0).ring g Omega}
  {ι : Type uI'} [Fintype ι] {dx : ι → Omega}
  (R : LevelForms07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d
    (wholeSpaceLevelScalars hp 0))
  {b : Module.Basis ι ((wholeSpaceSystemEnvelope hp 0).ring : Type u) Omega}
  (E : LevelBaseChangeData R b) (hdx : ∀ i, dx i = b i)

/-- **The coordinate operators of the connection of the system of levels of
[Stacks, Proposition 60.21.1, Tag 07JN].** -/
abbrev wholeSpaceCoordinateOperators (F : QuasiCoherentCrystal S) :
    ι → ((wholeSpaceLevelScalars hp 0).sections F → (wholeSpaceLevelScalars hp 0).sections F) :=
  levelCoordinateOperators R E (_root_.Crystalline.uniformLevel (affineSituation S hp)) hdx
    (fun F e ↦ pow_smul_eq_zero_wholeSpaceLevelSections hp 0 e F) F

/-- **The reduction datum of [Stacks, Lemma 60.17.3, Tag 07JG] at the system of levels of
[Stacks, Proposition 60.21.1, Tag 07JN]**, from a family `thetaPow` of composite operators `θ_K`
of the operators `...SmallSite.wholeSpaceCoordinateOperators` and the finiteness of
`{K | θ_K(m) ∉ p M}` for every section `m`. -/
def reduction07JGWholeSpaceOfThetaPow
    (thetaPow : ∀ F : QuasiCoherentCrystal S, (ι →₀ ℕ) →
      ((wholeSpaceLevelScalars hp 0).sections F → (wholeSpaceLevelScalars hp 0).sections F))
    (hfam : ∀ F : QuasiCoherentCrystal S,
      IsThetaMonomialFamily ((wholeSpaceLevelScalars hp 0).sections F)
        (wholeSpaceCoordinateOperators hp R E hdx F) (thetaPow F))
    (hfin : ∀ (F : QuasiCoherentCrystal S) (m : (wholeSpaceLevelScalars hp 0).sections F),
      {K : ι →₀ ℕ | thetaPow F K m ∉ pSmul S.p
        ((wholeSpaceSystemEnvelope hp 0).ring : Type u)
        ((wholeSpaceLevelScalars hp 0).sections F)}.Finite) :
    Reduction07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d S.p dx hp :=
  (levelReduction07JGOfThetaPow R E (_root_.Crystalline.uniformLevel (affineSituation S hp)) hdx
    (fun F e ↦ pow_smul_eq_zero_wholeSpaceLevelSections hp 0 e F) thetaPow hfam
    hfin).toReduction07JG rfl

/-- **The reduction datum of [Stacks, Lemma 60.17.3, Tag 07JG] at the system of levels of
[Stacks, Proposition 60.21.1, Tag 07JN], from items (07JD) and (07JE) of the tag**: the completed
connection assembled from the levels is integrable (`Crystalline.IsIntegrable`) and topologically
quasi-nilpotent (`Crystalline.IsTopologicallyQuasiNilpotent`). -/
def reduction07JGWholeSpaceOfItems
    (hint : ∀ F : QuasiCoherentCrystal S,
      IsIntegrable S.p ((wholeSpaceSystemEnvelope hp 0).ring : Type u) Omega dx
        (((wholeSpaceLevelScalars hp 0).comparisonOfLevels F (E.comparison F)
          (E.comparison_restrict F) b).completedConnection S.p))
    (hqn : ∀ F : QuasiCoherentCrystal S,
      IsTopologicallyQuasiNilpotent S.p ((wholeSpaceSystemEnvelope hp 0).ring : Type u) Omega dx
        (((wholeSpaceLevelScalars hp 0).comparisonOfLevels F (E.comparison F)
          (E.comparison_restrict F) b).completedConnection S.p)) :
    Reduction07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d S.p dx hp :=
  (levelReduction07JGOfItems R E (_root_.Crystalline.uniformLevel (affineSituation S hp)) hdx
    (fun F e ↦ pow_smul_eq_zero_wholeSpaceLevelSections hp 0 e F) hint hqn).toReduction07JG rfl

include hdx in
/-- **The hypothesis bundle of [Stacks, Proposition 60.17.4, Tag 07JH] is inhabited** from items
(07JD) and (07JE) of [Stacks, Lemma 60.17.3, Tag 07JG]. -/
theorem nonempty_reduction07JG_of_items
    (hint : ∀ F : QuasiCoherentCrystal S,
      IsIntegrable S.p ((wholeSpaceSystemEnvelope hp 0).ring : Type u) Omega dx
        (((wholeSpaceLevelScalars hp 0).comparisonOfLevels F (E.comparison F)
          (E.comparison_restrict F) b).completedConnection S.p))
    (hqn : ∀ F : QuasiCoherentCrystal S,
      IsTopologicallyQuasiNilpotent S.p ((wholeSpaceSystemEnvelope hp 0).ring : Type u) Omega dx
        (((wholeSpaceLevelScalars hp 0).comparisonOfLevels F (E.comparison F)
          (E.comparison_restrict F) b).completedConnection S.p)) :
    Nonempty (Reduction07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d S.p dx hp) :=
  ⟨reduction07JGWholeSpaceOfItems hp R E hdx hint hqn⟩

/-- **The hypothesis bundle of [Stacks, Proposition 60.17.4, Tag 07JH] is inhabited** from a
family `thetaPow` of composite operators of `...SmallSite.wholeSpaceCoordinateOperators` and the
finiteness of `{K | θ_K(m) ∉ p M}` for every section `m`. -/
theorem nonempty_reduction07JG_of_thetaPow
    (thetaPow : ∀ F : QuasiCoherentCrystal S, (ι →₀ ℕ) →
      ((wholeSpaceLevelScalars hp 0).sections F → (wholeSpaceLevelScalars hp 0).sections F))
    (hfam : ∀ F : QuasiCoherentCrystal S,
      IsThetaMonomialFamily ((wholeSpaceLevelScalars hp 0).sections F)
        (wholeSpaceCoordinateOperators hp R E hdx F) (thetaPow F))
    (hfin : ∀ (F : QuasiCoherentCrystal S) (m : (wholeSpaceLevelScalars hp 0).sections F),
      {K : ι →₀ ℕ | thetaPow F K m ∉ pSmul S.p
        ((wholeSpaceSystemEnvelope hp 0).ring : Type u)
        ((wholeSpaceLevelScalars hp 0).sections F)}.Finite) :
    Nonempty (Reduction07JG S A (wholeSpaceSystemEnvelope hp 0).ring g Omega d S.p dx hp) :=
  ⟨reduction07JGWholeSpaceOfThetaPow hp R E hdx thetaPow hfam hfin⟩

end WholeSpace

end Crystalline.GlobalCrystallineSituation.SmallSite

end
