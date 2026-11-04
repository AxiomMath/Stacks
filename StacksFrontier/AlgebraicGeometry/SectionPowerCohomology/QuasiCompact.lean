module

public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.MayerVietorisExtension
public import StacksFrontier.AlgebraicGeometry.SectionPowerCohomology.DegreeZeroChart
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineBase
public import StacksFrontier.AlgebraicGeometry.Cohomology.UniformVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineNonvanishing.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Powers of a section acting on the cohomology of a quasi-compact open

Let `X` be a quasi-separated scheme, `ℒ` an invertible `𝒪_X`-module and `s ∈ Γ(X, ℒ)`. For every
quasi-compact open `W ⊆ X`, every degree `n` and every quasi-coherent `𝒪_X`-module `𝒢`:

* every class `ξ ∈ Hⁿ(W, 𝒢)` restricting to zero on `W ∩ X_s` satisfies `sᵏ ξ = 0` in
  `Hⁿ(W, 𝒢 ⊗ ℒ^{⊗ k})` for some `k`;
* for every class `η ∈ Hⁿ(W ∩ X_s, 𝒢)` some `sᵏ η` is the restriction of a class of
  `Hⁿ(W, 𝒢 ⊗ ℒ^{⊗ k})`.

These are the two halves of the bijectivity of `H^n_*(W, ℒ, 𝒢)₍s₎ ⟶ Hⁿ(W ∩ X_s, 𝒢)` of
[Stacks, Tag 09MR], proved by the induction principle of [Stacks, Tag 08DR] from the affine
opens on which `ℒ` has a frame. When `X` is quasi-compact and `X_s` is affine,
`Hⁿ(X_s, 𝒢) = 0` in positive degree by [Stacks, Tag 01XB], and the first half at `W = X` is
[Stacks, Tag 01XR].

## Main results

* `Stacks.Cohomology.SectionPowerAnnihilation.annihilates_and_extends_of_isCompact`: both
  properties over every quasi-compact open, in every degree.
* `Stacks.SheafOfModules.exists_sectionPowerAction_eq_zero`: **[Stacks, Tag 01XR]**.

## References

* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
* [Stacks Project, Tag 09MR](https://stacks.math.columbia.edu/tag/09MR)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology Stacks.SheafOfModules Stacks.Cohomology.TwistedGradedModule
open Stacks.SheafOfModules.SectionPowerComposition (mul)

universe u

namespace Stacks.Cohomology.SectionPowerAnnihilation

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

variable {X : Scheme.{u}}
  {L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)}
  [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property L] {s : L.sections}

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

local notation "N" => nonvanishingOpen L s

variable (s) in
/-- **Where the cohomology vanishes both properties hold trivially.** -/
theorem annihilates_and_extends_of_isZero (W : X.Opens) (n : ℕ)
    (hW : ∀ G : X.Modules, G.IsQuasicoherent → IsZero (Hgroup X.ringCatSheaf W n G))
    (hWs : ∀ G : X.Modules, G.IsQuasicoherent →
      IsZero (Hgroup X.ringCatSheaf (W ⊓ N : X.Opens) n G)) :
    Annihilates X L s W n ∧ Extends X L s W n := by
  refine ⟨fun T hT hTeq G hG ξ _ => ?_, fun T hT hTeq G hG η => ?_⟩
  · have := AddCommGrpCat.isZero_iff_subsingleton.mp (hW G hG)
    exact ⟨0, by rw [Subsingleton.elim ξ 0, map_zero]⟩
  · subst hTeq
    have := AddCommGrpCat.isZero_iff_subsingleton.mp (hWs G hG)
    exact ⟨0, 0, by rw [Subsingleton.elim η 0, map_zero, map_zero]⟩

variable (s) in
/-- Both properties over the empty open. -/
theorem annihilates_and_extends_bot (n : ℕ) :
    Annihilates X L s ⊥ n ∧ Extends X L s ⊥ n :=
  annihilates_and_extends_of_isZero s ⊥ n (fun G _ => isZero_Hgroup_bot G n)
    (fun G _ => by rw [bot_inf_eq]; exact isZero_Hgroup_bot G n)

variable (s) in
/-- Both properties over an affine open in positive degree, where the cohomology vanishes by
[Stacks, Tag 01XB]. -/
theorem annihilates_and_extends_of_isAffineOpen {A : X.Opens} (hA : IsAffineOpen A) (n : ℕ)
    (hn : 0 < n) : Annihilates X L s A n ∧ Extends X L s A n :=
  annihilates_and_extends_of_isZero s A n
    (fun G hG => have := hG; Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X G A hA n hn)
    (fun G hG => have := hG; Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X G _
      (AlgebraicGeometry.Scheme.Modules.isAffineOpen_inf_nonvanishingOpen L s A hA) n hn)

variable (s) in
/-- **Both properties over every quasi-compact open of a quasi-separated scheme**, in every
degree, by the induction principle of [Stacks, Tag 08DR] from the affine opens on which `ℒ`
has a frame. -/
theorem annihilates_and_extends_of_isCompact [QuasiSeparatedSpace X] (W : X.Opens)
    (hW : IsCompact (W : Set X)) (n : ℕ) : Annihilates X L s W n ∧ Extends X L s W n := by
  refine Stacks.AlgebraicGeometry.CompactOpenInduction.of_isCompact_of_basis
    (P := fun W => ∀ n, Annihilates X L s W n ∧ Extends X L s W n)
    (Q := fun U => U = ⊥ ∨ Nonempty (GeneratorSections X.toRingedSpace L U))
    (Or.inl rfl) (fun V U hVU hU => ?_) (fun x => ?_) (fun U hU hQ n => ?_)
    (fun U V _ _ _ hPU hPV hPUV n => ?_) W hW n
  · rcases hU with rfl | ⟨⟨g⟩⟩
    · exact Or.inl (le_bot_iff.mp hVU)
    · exact Or.inr ⟨generatorRestrict L hVU g⟩
  · obtain ⟨W₀, hxW₀, g₀, hg₀⟩ := exists_bijective_smul_of_isInvertible L x
    obtain ⟨A, hA, hxA, hAW⟩ := exists_isAffineOpen_mem_and_subset (X := X) hxW₀
    exact ⟨A, hA, Or.inr ⟨generatorRestrict L (fun y hy => hAW hy) ⟨g₀, hg₀⟩⟩, hxA⟩
  · rcases hQ with rfl | ⟨⟨g⟩⟩
    · exact annihilates_and_extends_bot s n
    rcases n with _ | n
    · exact ⟨annihilates_zero_of_generator s hU g, extends_zero_of_generator s hU g⟩
    · exact annihilates_and_extends_of_isAffineOpen s hU (n + 1) n.succ_pos
  · rcases n with _ | q
    · exact ⟨annihilates_sup_zero U V (hPU 0).1 (hPV 0).1,
        extends_sup_zero U V (hPU 0).2 (hPV 0).2 (hPUV 0).1⟩
    · exact ⟨annihilates_sup_succ U V q (hPU (q + 1)).1 (hPV (q + 1)).1 (hPU q).2 (hPV q).2
          (hPUV q).1,
        extends_sup_succ U V q (hPU (q + 1)).2 (hPV (q + 1)).2 (hPUV (q + 1)).1 (hPUV q).2⟩

end Stacks.Cohomology.SectionPowerAnnihilation

namespace Stacks.SheafOfModules

attribute [local implicit_reducible] _root_.SheafOfModules.forget
  PresheafOfModules.restrictScalars TensorSheafification.structureSheaf

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

/-- **[Stacks, Tag 01XR].** Let `X` be a scheme, `ℒ` an invertible `𝒪_X`-module and
`s ∈ Γ(X, ℒ)` a global section. If `X` is quasi-compact and quasi-separated and
`X_s` is affine, then for every quasi-coherent `𝒪_X`-module `ℱ`, every `p > 0` and every
`ξ ∈ Hᵖ(X, ℱ)` there is `n ≥ 0` with `sⁿ ξ = 0` in `Hᵖ(X, ℱ ⊗ ℒ^{⊗ n})`.

Multiplication by `sⁿ` is `Stacks.SheafOfModules.sectionPowerAction` along the morphism
`t : 𝒪_X ⟶ ℒ^{⊗ n}` representing `sⁿ` (`Stacks.SheafOfModules.IsSectionPowerHom`; such a `t` is
unique, by `Stacks.SheafOfModules.IsSectionPowerHom.unique`, and exists, by
`Stacks.SheafOfModules.isSectionPowerHom_sectionPowerHom`). -/
@[stacks 01XR]
theorem exists_sectionPowerAction_eq_zero (X : Scheme.{u})
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [IsInvertible X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L]
    [CompactSpace X] [QuasiSeparatedSpace X] (s : L.sections)
    (hU : IsAffineOpen (nonvanishingOpen L s)) (F : X.Modules) [F.IsQuasicoherent] (p : ℕ)
    (hp : 0 < p) (ξ : Hgroup X.ringCatSheaf ⊤ p F) :
    ∃ n : ℕ, ∀ (t : SheafOfModules.unit X.ringCatSheaf ⟶
        TensorPower.tensorPower X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L n),
      IsSectionPowerHom X.toRingedSpace.presheaf
          (structureSheafRing X.toRingedSpace).property L s n t →
        (Hfunctor X.ringCatSheaf ⊤ p).map
          (sectionPowerAction X.toRingedSpace.presheaf
            (structureSheafRing X.toRingedSpace).property L F n t) ξ = 0 := by
  have hA := (Stacks.Cohomology.SectionPowerAnnihilation.annihilates_and_extends_of_isCompact
    s ⊤ (by simpa using isCompact_univ (X := X)) p).1
  have hz : IsZero (Hgroup X.ringCatSheaf (⊤ ⊓ nonvanishingOpen L s : X.Opens) p F) := by
    rw [top_inf_eq]
    exact Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F _ hU p hp
  have := AddCommGrpCat.isZero_iff_subsingleton.mp hz
  obtain ⟨k, hk⟩ := hA _ inf_le_left rfl F inferInstance ξ (Subsingleton.elim _ _)
  refine ⟨k, fun t ht => ?_⟩
  rwa [IsSectionPowerHom.unique (sectionSiteRing X) (sectionSiteSheaf X) L ht
    (isSectionPowerHom_sectionPowerHom (sectionSiteRing X) (sectionSiteSheaf X) L s k)]

end Stacks.SheafOfModules

end
