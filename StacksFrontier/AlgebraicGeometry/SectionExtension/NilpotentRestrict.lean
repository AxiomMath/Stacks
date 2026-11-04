module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Nilpotent
public import StacksFrontier.AlgebraicGeometry.SectionsColimit.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# A section whose nonvanishing locus misses a closed subscheme restricts to zero on a power

Let `X` be a scheme, `L` an invertible `𝒪_X`-module and `i : Z ⟶ X` a quasi-compact morphism —
a closed immersion, in the application.  A global section `s` of `L^{⊗ n}` whose nonvanishing
locus `X_s` misses the image of `i` has a power `s^N` whose **restriction to `Z`** is zero: the
unit of `i^* ⊣ i_*` kills it over every open of `X`.

The restriction is the unit `L^{⊗ nN} ⟶ i_*(i^*L^{⊗ nN})` of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, which is the leg the twisted
square of `StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.TwistedUnit` consumes, so this is
the hypothesis that
`Stacks.AffineClosedUnion.existsUnique_unit_app_eq_zero_of_unitRestrict_eq_zero` asks for.

## The route, and why no tensor-power comparison is needed

The obvious route is to restrict `s` to `Z` and apply the nilpotence of
`StacksDraft.AlgebraicGeometry.F3b.SectionExtension.Nilpotent` on `Z`.  That needs
`i^*(L^{⊗ m}) ≅ (i^*L)^{⊗ m}`, the pullback-tensor-power comparison, which this development does
not have.  **The route here never leaves `X`.**  Over an open `U` of `X` carrying a frame `g` of
`L^{⊗ n}` the section is a unique multiple `s|_U = a · g`, and

* `AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_generator` computes
  `X_a = X_s ⊓ U`, so `X_a` misses the image of `i`;
* hence `Z_{i^♯a} = i^{-1}X_a = ∅` by `AlgebraicGeometry.Scheme.preimage_basicOpen`, and on a
  compact `i^{-1}U` that makes `i^♯a` nilpotent, by Mathlib's
  `AlgebraicGeometry.Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact`.  **Only the preimage
  has to be compact, not `U`** — which is the one place the hypotheses differ from the nilpotence
  statement on `X`;
* `Stacks.SheafOfModules.Invertible.sectionPowOver_smul` gives `s^k|_U = a^k · g^k`, the unit is
  `Γ(X, U)`-linear, and the `Γ(X, U)`-action on the sections of a direct image is the action of
  `Γ(Z, i^{-1}U)` restricted along the comorphism, so `a^k · (-)` acts as `(i^♯a)^k · (-) = 0`.

Finitely many such `U` cover a quasi-compact `X` and the largest of their exponents serves all of
them, after which a global section vanishing on an open cover vanishes.

`AlgebraicGeometry.Scheme.Hom.isCompact_preimage` supplies the compactness of `i^{-1}U` for `U`
affine from quasi-compactness of `i` alone; a closed immersion is affine and so quasi-compact, so
the application needs nothing beyond its standing hypothesis.

## Main results

* `AlgebraicGeometry.Scheme.Modules.smul_pushforward_eq_zero_of_app_eq_zero`: **a scalar killed
  by the comorphism annihilates the sections of a direct image.**
* `AlgebraicGeometry.Scheme.Modules.isNilpotent_app_of_notMem_nonvanishingLocus`: the coefficient
  of the section in a local frame restricts to a nilpotent on `Z`.
* `AlgebraicGeometry.Scheme.Modules.unit_app_eval_sectionPow'_eq_zero_of_smul_eq`: the unit kills
  a power of the section over one open, given that the power of the coefficient is killed by the
  comorphism.
* `AlgebraicGeometry.Scheme.Modules.exists_unit_app_eval_sectionPow'_eq_zero_of_isCompact`: the
  local form, on one open with compact preimage carrying a frame.
* `AlgebraicGeometry.Scheme.Modules.exists_unit_app_eval_sectionPow'_eq_zero`: **the global
  form** — on a quasi-compact `X`, some power of `s` restricts to zero on `Z` over every open.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules X` is `SheafOfModules X.ringCatSheaf` while the tensor powers
of this development are stated over
  `structureSheafRing X.toRingedSpace`.  The two
are definitionally equal and not interchangeable for instance resolution, and the seam is visible
here in exactly one place: `smul_pushforward_eq_zero_of_app_eq_zero` is stated for an
**abstract** `N : Z.Modules`, because with `N` written out as a pullback of a tensor power the
`zero_smul` rewrite dies with *"the target expression is not type-correct under the `implicit`
transparency level"*.  Applied with the tensor power substituted it goes
through, the application being checked against an expected type.  Inside its proof one declared
type is load-bearing for the same reason, and the passage from `Γ(i_*N, U)` to `Γ(N, i^{-1}U)` is
`Stacks.AlgebraicGeometry.SectionsColimit.pushforward_app_smul`, which is already `rfl`.

No `@[stacks]` attribute is attached.  Replacing a section by a power that vanishes on a closed
subscheme is a step inside the proof of [Stacks, Tag 09NX] and is a numbered result nowhere in the
source; 09NX itself is the ampleness criterion, which is not proved here.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

/-- **A scalar killed by the comorphism annihilates the sections of a direct image.**  The
`Γ(X, U)`-action on `Γ(i_*N, U)` is the `Γ(Z, i^{-1}U)`-action restricted along `i.app U`, so a
`c` with `i^♯c = 0` acts as zero.

`N` is abstract on purpose: substituting a pullback of a tensor power of an invertible module
makes the `zero_smul` step below fail on the `AlgebraicGeometry.Scheme.Modules` versus
`structureSheafRing` spelling of the sheaf of rings,
  while the application of this
lemma at that substitution is checked against an expected type and goes through. -/
theorem smul_pushforward_eq_zero_of_app_eq_zero {Z X : Scheme.{u}} (i : Z ⟶ X) (N : Z.Modules)
    (U : X.Opens) (c : Γ(X, U)) (hc : i.app U c = 0)
    (y : Γ((Scheme.Modules.pushforward i).obj N, U)) :
    c • y = 0 := by
  have h : i.app U c • (show Γ(N, i ⁻¹ᵁ U) from y) = (0 : Γ(N, i ⁻¹ᵁ U)) := by
    rw [hc, zero_smul]
  exact (Stacks.AlgebraicGeometry.SectionsColimit.pushforward_app_smul i N U c y).symm.trans h

variable {X : Scheme.{u}} (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

local notation "Lpow[" n "]" => tensorPowerModule' L ((n : ℕ) : ℤ)

/-- The coefficient of a global section of `L^{⊗ n}` in a local frame, together with the
computation of its basic open as the part of the nonvanishing locus inside the frame's open.  This
packages the surjectivity half of the frame with
`basicOpen_eq_inf_nonvanishingOpen_of_generator`. -/
theorem exists_smul_eq_and_basicOpen_eq {n : ℕ} (s : Lpow[n].sections) {U : X.Opens}
    (g : GeneratorSections X.toRingedSpace Lpow[n] U) :
    ∃ a : Γ(X, U), s.eval (op U) = a • g.val ∧
      X.basicOpen a = nonvanishingOpen (X := X.toRingedSpace) Lpow[n] s ⊓ U := by
  have hbij := g.property U le_rfl
  rw [generator_restrict_self Lpow[n] U g] at hbij
  obtain ⟨a, ha⟩ := hbij.surjective (s.eval (op U))
  exact ⟨a, ha.symm, basicOpen_eq_inf_nonvanishingOpen_of_generator L s g a ha.symm⟩

variable {Z : Scheme.{u}} (i : Z ⟶ X)

/-- **The coefficient restricts to a nilpotent on `Z`.**  Its basic open is the part of the
nonvanishing locus inside the frame's open, which misses the image of `i`, so the basic open of
the restricted coefficient is empty; on a compact `i^{-1}U` that forces nilpotence. -/
theorem isNilpotent_app_of_notMem_nonvanishingLocus {n : ℕ} (s : Lpow[n].sections) {U : X.Opens}
    (hU : IsCompact ((i ⁻¹ᵁ U : Z.Opens) : Set Z)) (a : Γ(X, U))
    (hbo : X.basicOpen a = nonvanishingOpen (X := X.toRingedSpace) Lpow[n] s ⊓ U)
    (hs : ∀ z : Z, i.base z ∉ nonvanishingLocus Lpow[n] s) :
    IsNilpotent (i.app U a) := by
  refine (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU _).mpr ?_
  rw [← Scheme.preimage_basicOpen, hbo]
  exact le_antisymm (fun z hz => absurd hz.1 (hs z)) bot_le

/-- **The unit of `i^* ⊣ i_*` kills a power of the section over one open**, given that the
corresponding power of its coefficient in a local frame is killed by the comorphism.  The unit is
`Γ(X, U)`-linear, which turns `s^k|_U = a^k · g^k` into `a^k · (-)` applied to a section of a
direct image. -/
theorem unit_app_eval_sectionPow'_eq_zero_of_smul_eq {n : ℕ} (s : Lpow[n].sections) (U : X.Opens)
    (a : Γ(X, U)) (w : Lpow[n].val.obj (op U)) (ha : s.eval (op U) = a • w) (k : ℕ)
    (hc : i.app U (a ^ k) = 0) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app Lpow[n * k]).app U
      ((sectionPow' L s k).eval (op U)) = 0 := by
  have hev : (sectionPow' L s k).eval (op U) = a ^ k • sectionPowOver L (op U) w k := by
    rw [eval_sectionPow', ha, sectionPowOver_smul]
  refine (congrArg (fun z => ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
    Lpow[n * k]).app U z) hev).trans ?_
  refine Eq.trans ?_ (smul_pushforward_eq_zero_of_app_eq_zero i
    ((Scheme.Modules.pullback i).obj Lpow[n * k]) U (a ^ k) hc
    (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app Lpow[n * k]).app U
      (sectionPowOver L (op U) w k)))
  exact Scheme.Modules.Hom.app_smul _ _ _

/-- **The local form.**  On an open whose preimage in `Z` is compact and which carries a frame of
`L^{⊗ n}`, every sufficiently high power of a section whose nonvanishing locus misses the image of
`i` restricts to zero on `Z`. -/
theorem exists_unit_app_eval_sectionPow'_eq_zero_of_isCompact {n : ℕ} (s : Lpow[n].sections)
    (U : X.Opens) (hU : IsCompact ((i ⁻¹ᵁ U : Z.Opens) : Set Z))
    (g : GeneratorSections X.toRingedSpace Lpow[n] U)
    (hs : ∀ z : Z, i.base z ∉ nonvanishingLocus Lpow[n] s) :
    ∃ N : ℕ, ∀ k, N ≤ k →
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app Lpow[n * k]).app U
        ((sectionPow' L s k).eval (op U)) = 0 := by
  obtain ⟨a, ha, hbo⟩ := exists_smul_eq_and_basicOpen_eq L s g
  obtain ⟨N, hN⟩ := isNilpotent_app_of_notMem_nonvanishingLocus L i s hU a hbo hs
  refine ⟨N, fun k hk => unit_app_eval_sectionPow'_eq_zero_of_smul_eq L i s U a g.val ha k ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [map_pow, pow_add, hN, zero_mul]

/-- **The global form: a section of `L^{⊗ n}` on a quasi-compact scheme whose nonvanishing locus
misses the image of a quasi-compact morphism `i` has a power restricting to zero along `i`**, over
every open of `X` at once.  This is the hypothesis the twisted square of
`StacksDraft.AlgebraicGeometry.F3b.AffineClosedUnion.TwistedUnit` consumes. -/
theorem exists_unit_app_eval_sectionPow'_eq_zero [CompactSpace X] [QuasiCompact i] {n : ℕ}
    (s : Lpow[n].sections) (hs : ∀ z : Z, i.base z ∉ nonvanishingLocus Lpow[n] s) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ V : X.Opens,
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app Lpow[n * N]).app V
        ((sectionPow' L s N).eval (op V)) = 0 := by
  classical
  have hLinv : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L := isInvertible_of_tensorInvertible L
  have hlocal : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ IsCompact ((i ⁻¹ᵁ V : Z.Opens) : Set Z) ∧
      Nonempty (GeneratorSections X.toRingedSpace L V) := by
    intro x
    obtain ⟨W, hxW, a, ha⟩ := exists_bijective_smul_of_isInvertible L x
    obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
    have hVW' : V ≤ W := hVW
    exact ⟨V, hxV, i.isCompact_preimage hVaff.isCompact,
      ⟨generatorRestrict L hVW' ⟨a, fun V' h => ha V' h⟩⟩⟩
  choose V hxV hVc hVgen using hlocal
  have hNex : ∀ x : X, ∃ N : ℕ, ∀ k, N ≤ k →
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app Lpow[n * k]).app (V x)
        ((sectionPow' L s k).eval (op (V x))) = 0 := fun x =>
    exists_unit_app_eval_sectionPow'_eq_zero_of_isCompact L i s (V x) (hVc x)
      (tensorPowerGenerator L (hVgen x).some n) hs
  choose N hNspec using hNex
  obtain ⟨σ, hσ⟩ := (CompactSpace.isCompact_univ (X := X)).elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hxV y⟩)
  refine ⟨max 1 (σ.sup N), le_max_left _ _, fun W => ?_⟩
  refine eval_eq_zero_of_iSup_eq_top (PresheafOfModules.sectionsMap
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      Lpow[n * max 1 (σ.sup N)]).val (sectionPow' L s (max 1 (σ.sup N))))
    (fun j : (σ : Set X) => V j.1) ?_ ?_ W
  · refine le_antisymm le_top (fun y _ => Opens.mem_iSup.2 ?_)
    obtain ⟨x, hxσ, hyx⟩ : ∃ x ∈ σ, y ∈ V x := by
      have h := hσ (Set.mem_univ y)
      simpa using h
    exact ⟨⟨x, hxσ⟩, hyx⟩
  · exact fun j => hNspec j.1 _ (le_trans (Finset.le_sup j.2) (le_max_right _ _))

end AlgebraicGeometry.Scheme.Modules

end
