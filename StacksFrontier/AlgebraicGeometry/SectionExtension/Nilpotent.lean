module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorPowerGenerator
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# A section of an invertible module with empty nonvanishing locus is nilpotent

Let `X` be a scheme and `L` an invertible `𝒪_X`-module.  A global section `s` of `L^{⊗ n}` has a
nonvanishing locus `X_s` ([Stacks, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)), and if
`X_s` is empty then `s` is *nilpotent*: some power `s^N`, a global section of `L^{⊗ nN}`, is zero.
This file proves that, and the local calculus of powers of sections over an open that it needs.

The hypothesis is **quasi-compactness of `X` and nothing else**: no reducedness, no Noetherian
hypothesis and no bound on the dimension.  On a reduced scheme `N = 1` works, by
`AlgebraicGeometry.Scheme.eq_zero_of_basicOpen_eq_bot`; the point of the statement below is
precisely the non-reduced case, where `s` vanishes at every point and is not zero, and where the
*uniformity* of the nilpotence exponent is what quasi-compactness buys.

## The route

Over an open `U` carrying a frame `g` of `L^{⊗ n}` — which exists near every point, `L` being
invertible — the section is a unique multiple `s|_U = a · g` of the frame, and
`Stacks.SheafOfModules.mem_nonvanishingLocus_iff_isUnit_ringGerm` says that `s` is nonvanishing at
a point of `U` exactly when `a` is.  So an empty `X_s` makes the basic open `X_a` empty, and on a
*compact* `U` that forces `a` to be nilpotent
(`AlgebraicGeometry.Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact`).  The power of a section
over an open is the corresponding power of its coefficient times the power of the frame
(`sectionPowOver_smul`), so `s^N|_U = a^N · g^N = 0`.  Finitely many such `U` cover a quasi-compact
`X`, the largest of their exponents works for all of them at once, and a section of a sheaf
vanishing on an open cover is zero.

## Main definitions

* `Stacks.SheafOfModules.Invertible.sectionPowOver`: the `k`-th power of a section of `L^{⊗ n}`
  **over an open**, built from `Stacks.SheafOfModules.Invertible.sectionMulOver`.  The global
  `sectionPow'` is its value on a global section, `eval_sectionPow'`.

## Main results

* `Stacks.SheafOfModules.eval_eq_zero_of_iSup_eq_top`: a global section of a sheaf of modules
  vanishing on an open cover vanishes.
* `Stacks.SheafOfModules.isInvertible_of_tensorInvertible`: the two `IsInvertible` classes of this
  development agree.
* `Stacks.SheafOfModules.Invertible.sectionPowOver_smul`: `(c · x)^k = c^k · x^k` over an open.
* `AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_generator`: **the basic
  open of the coefficient of a section in a local frame is the part of the nonvanishing locus
  inside the frame's open.**
* `AlgebraicGeometry.Scheme.Modules.exists_eval_sectionPow'_eq_zero_of_isCompact`: the local form,
  on one compact open carrying a frame.
* `AlgebraicGeometry.Scheme.Modules.exists_eval_sectionPow'_eq_zero_of_nonvanishingLocus_eq_empty`:
  **a section of `L^{⊗ n}` on a quasi-compact scheme whose nonvanishing locus is empty has a
  vanishing power.**

## Implementation notes

`Stacks.SheafOfModules.IsInvertible` and `AlgebraicGeometry.SheafOfModules.IsInvertible` are the
same definition written twice as two constants, and
`StacksFrontier/AlgebraicGeometry/NonvanishingTrivialization/Basic.lean` records, at its line 76,
that no bridge between them exists.  `isInvertible_of_tensorInvertible` is that bridge, written as
a theorem rather than an instance so that it changes no instance search anywhere else; it is used
once below, to reach the local frames of
`Stacks.SheafOfModules.exists_bijective_smul_of_isInvertible` from the class that
`Stacks.SheafOfModules.Invertible.tensorPowerModule'` binds.

**The two classes' paths are crossed relative to their names**, so pairing them by the order they
are mentioned in gets them the wrong way round: `Stacks.SheafOfModules.IsInvertible` is declared in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorInvertible.lean`, and
`AlgebraicGeometry.SheafOfModules.IsInvertible` in
`StacksFrontier/Topology/Sheaves/Modules/Invertible.lean`.  Neither the path nor the single field name
distinguishes them; only the namespace does.

Powers of sections are taken through `sectionMulOver` rather than through the monoidal
`Stacks.SheafOfModules.Invertible.sectionMul` of
`StacksFrontier/AlgebraicGeometry/GradedSectionRing/Basic.lean`, for the following reason:
only the `sectionMulOver` spelling has an evaluation rule over an open, and the whole argument here
is a computation over an open.  The two products are not identified anywhere in the development.

No `@[stacks]` attribute is attached.  The statement is the nilpotence step that the proof of
[Stacks, Tag 09NX] needs in order to replace a section by a power vanishing on a closed subscheme;
09NX is the ampleness criterion, which is not proved here, and the source states this step nowhere
as a numbered result.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace (ringStalk ringGerm grpGerm)

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}}

/-- **A global section of a sheaf of modules vanishing on an open cover vanishes.** -/
theorem eval_eq_zero_of_iSup_eq_top {M : _root_.SheafOfModules.{u} (structureSheafRing X)}
    (m : M.sections) {ι : Type*} (U : ι → Opens X.carrier) (hcov : (⨆ i, U i) = ⊤)
    (h : ∀ i, m.eval (op (U i)) = 0) (V : Opens X.carrier) : m.eval (op V) = 0 := by
  have hres : ∀ W : Opens X.carrier,
      M.val.map (homOfLE (le_top (a := W))).op (m.eval (op ⊤)) = m.eval (op W) := fun W =>
    PresheafOfModules.sections_property m (homOfLE (le_top (a := W))).op
  have htop : m.eval (op ⊤) = 0 := by
    refine TopCat.Presheaf.section_ext (C := AddCommGrpCat.{u}) ⟨M.val.presheaf, M.isSheaf⟩ ⊤ _ 0
      fun y hy => ?_
    obtain ⟨i, hyi⟩ : ∃ i, y ∈ U i :=
      Opens.mem_iSup.1 (hcov ▸ (Opens.mem_top y : y ∈ (⊤ : Opens X.carrier)))
    show grpGerm X M.val y ⊤ hy (m.eval (op ⊤)) = grpGerm X M.val y ⊤ hy 0
    rw [map_zero]
    have e1 : grpGerm X M.val y (U i) hyi
        (M.val.map (homOfLE (le_top (a := U i))).op (m.eval (op ⊤)))
        = grpGerm X M.val y ⊤ hy (m.eval (op ⊤)) :=
      TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.val.presheaf
        (homOfLE (le_top (a := U i))) y hyi (m.eval (op ⊤))
    rw [← e1, hres, h i, map_zero]
  rw [← hres V, htop]
  exact map_zero _

/-- An invertible sheaf in the sense of `AlgebraicGeometry.SheafOfModules.IsInvertible` is
invertible in the sense of `Stacks.SheafOfModules.IsInvertible`. -/
theorem isInvertible_of_tensorInvertible
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X).property L] :
    IsInvertible X.presheaf (structureSheafRing X).property L := by
  obtain ⟨F, hF, ⟨u⟩⟩ := h.exists_tensorFunctor
  exact ⟨F, hF, ⟨{ ι := u.ι, bijective := u.bijective }⟩⟩

end Stacks.SheafOfModules

namespace Stacks.SheafOfModules.Invertible

variable {X : RingedSpace.{u, u}}
  (L : _root_.SheafOfModules.{u} (structureSheafRing X))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
    (structureSheafRing X).property L]

local notation "Lpow[" n "]" => tensorPowerModule' L ((n : ℕ) : ℤ)

/-- The `k`-th power of a section of `L^{⊗ n}` **over an open**. -/
def sectionPowOver {n : ℕ} (U : (Opens X.carrier)ᵒᵖ) (x : Lpow[n].val.obj U) :
    (k : ℕ) → Lpow[n * k].val.obj U
  | 0 => (sectionOne X.presheaf (structureSheafRing X).property L).eval U
  | k + 1 => sectionMulOver L (n * k) n U (sectionPowOver U x k) x

/-- The `0`-th power of a section over an open is the unit section. -/
theorem sectionPowOver_zero {n : ℕ} (U : (Opens X.carrier)ᵒᵖ) (x : Lpow[n].val.obj U) :
    sectionPowOver L U x 0
      = (sectionOne X.presheaf (structureSheafRing X).property L).eval U := rfl

/-- The `(k + 1)`-th power of a section `x` over an open is the product of its `k`-th power
with `x`. -/
theorem sectionPowOver_succ {n : ℕ} (U : (Opens X.carrier)ᵒᵖ) (x : Lpow[n].val.obj U) (k : ℕ) :
    sectionPowOver L U x (k + 1)
      = sectionMulOver L (n * k) n U (sectionPowOver L U x k) x := rfl

/-- The power of a global section, read over an open, is the power of its value there. -/
theorem eval_sectionPow' {n : ℕ} (s : Lpow[n].sections) (U : (Opens X.carrier)ᵒᵖ) (k : ℕ) :
    (sectionPow' L s k).eval U = sectionPowOver L U (s.eval U) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [sectionPow'_succ, sectionMul'_eval, ih, sectionPowOver_succ]

/-- Powers of a scalar multiple over an open. -/
theorem sectionPowOver_smul {n : ℕ} (U : (Opens X.carrier)ᵒᵖ) (c : X.presheaf.obj U)
    (x : Lpow[n].val.obj U) (k : ℕ) :
    sectionPowOver L U (c • x) k = c ^ k • sectionPowOver L U x k := by
  induction k with
  | zero => rw [sectionPowOver_zero, sectionPowOver_zero, pow_zero, one_smul]
  | succ k ih =>
      rw [sectionPowOver_succ, sectionPowOver_succ, ih, sectionMulOver_smul_left,
        sectionMulOver_smul_right, smul_smul, ← pow_succ]

/-- If a global section of `L^{⊗ n}` is `c • w` over `U` and `c ^ k = 0`, then its `k`-th power
vanishes over `U`. -/
theorem eval_sectionPow'_eq_zero_of_smul_eq {n : ℕ} (s : Lpow[n].sections)
    (U : (Opens X.carrier)ᵒᵖ) (c : X.presheaf.obj U) (w : Lpow[n].val.obj U)
    (hs : s.eval U = c • w) (k : ℕ) (hc : c ^ k = 0) :
    (sectionPow' L s k).eval U = 0 := by
  rw [eval_sectionPow', hs, sectionPowOver_smul, hc, zero_smul]

end Stacks.SheafOfModules.Invertible

namespace AlgebraicGeometry.Scheme.Modules

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

variable {X : Scheme.{u}} (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

local notation "Lpow[" n "]" => tensorPowerModule' L ((n : ℕ) : ℤ)

/-- **The basic open of the coefficient of a section in a local frame** is the part of the
nonvanishing locus lying inside the frame's open.  This is
`AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_smul_eq` with the global
trivializing section replaced by a local frame, which is the only form available when `L` has no
nowhere-vanishing global section. -/
theorem basicOpen_eq_inf_nonvanishingOpen_of_generator {n : ℕ} (s : Lpow[n].sections)
    {U : X.Opens} (g : GeneratorSections X.toRingedSpace Lpow[n] U) (a : Γ(X, U))
    (ha : s.eval (op U) = a • g.val) :
    X.basicOpen a = nonvanishingOpen (X := X.toRingedSpace) Lpow[n] s ⊓ U := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hxU : x ∈ U := X.basicOpen_le a hx
    exact ⟨(mem_nonvanishingLocus_iff_isUnit_ringGerm Lpow[n] s g a ha x hxU).mpr
      ((isUnit_ringGerm_iff_mem_basicOpen a x hxU).mpr hx), hxU⟩
  · exact (isUnit_ringGerm_iff_mem_basicOpen a x hx.2).mp
      ((mem_nonvanishingLocus_iff_isUnit_ringGerm Lpow[n] s g a ha x hx.2).mp hx.1)

/-- **On a compact open carrying a frame of `L`, a section of `L^{⊗ n}` vanishing at every point
of the open has a power vanishing there.** -/
theorem exists_eval_sectionPow'_eq_zero_of_isCompact {n : ℕ} (s : Lpow[n].sections)
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (t : GeneratorSections X.toRingedSpace L U)
    (hs : ∀ x ∈ U, x ∉ nonvanishingLocus Lpow[n] s) :
    ∃ N : ℕ, ∀ k, N ≤ k → (sectionPow' L s k).eval (op U) = 0 := by
  have g : GeneratorSections X.toRingedSpace Lpow[n] U := tensorPowerGenerator L t n
  have hbij := g.property U le_rfl
  rw [generator_restrict_self Lpow[n] U g] at hbij
  obtain ⟨a₀, ha₀⟩ := hbij.surjective (s.eval (op U))
  obtain ⟨a, ha'⟩ : ∃ a : Γ(X, U), s.eval (op U) = a • g.val := ⟨a₀, ha₀.symm⟩
  have hbasic : X.basicOpen a = ⊥ := by
    rw [basicOpen_eq_inf_nonvanishingOpen_of_generator L s g a ha']
    exact le_antisymm (fun x hx => absurd hx.1 (hs x hx.2)) bot_le
  obtain ⟨N, hN⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU a).mpr hbasic
  have hak : ∀ k, N ≤ k → a ^ k = 0 := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, hN, zero_mul]
  exact ⟨N, fun k hk =>
    eval_sectionPow'_eq_zero_of_smul_eq L s (op U) a g.val ha' k (hak k hk)⟩

/-- **A section of `L^{⊗ n}` on a quasi-compact scheme whose nonvanishing locus is empty has a
vanishing power.** -/
theorem exists_eval_sectionPow'_eq_zero_of_nonvanishingLocus_eq_empty [CompactSpace X] {n : ℕ}
    (s : Lpow[n].sections) (hs : nonvanishingLocus Lpow[n] s = ∅) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ V : _root_.TopologicalSpace.Opens X.toRingedSpace.carrier,
      (sectionPow' L s N).eval (op V) = 0 := by
  classical
  have hLinv : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L := isInvertible_of_tensorInvertible L
  have hcov : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ IsCompact (V : Set X) ∧
      Nonempty (GeneratorSections X.toRingedSpace L V) := by
    intro x
    obtain ⟨W, hxW, a, ha⟩ := exists_bijective_smul_of_isInvertible L x
    obtain ⟨V, hVaff, hxV, hVW⟩ := exists_isAffineOpen_mem_and_subset hxW
    have hVW' : V ≤ W := hVW
    exact ⟨V, hxV, hVaff.isCompact,
      ⟨generatorRestrict L hVW' ⟨a, fun V' h => ha V' h⟩⟩⟩
  choose V hxV hVc hVgen using hcov
  have hNex : ∀ x : X, ∃ N : ℕ, ∀ k, N ≤ k → (sectionPow' L s k).eval (op (V x)) = 0 := fun x =>
    exists_eval_sectionPow'_eq_zero_of_isCompact L s (V x) (hVc x) (hVgen x).some
      (fun y _ => by rw [hs]; exact Set.notMem_empty y)
  choose N hNspec using hNex
  obtain ⟨σ, hσ⟩ := (CompactSpace.isCompact_univ (X := X)).elim_finite_subcover
    (fun x : X => (V x : Set X)) (fun x => (V x).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hxV y⟩)
  refine ⟨max 1 (σ.sup N), le_max_left _ _, ?_⟩
  refine eval_eq_zero_of_iSup_eq_top _ (fun i : (σ : Set X) => V i.1) ?_ ?_
  · refine le_antisymm le_top (fun y _ => Opens.mem_iSup.2 ?_)
    obtain ⟨x, hxσ, hyx⟩ : ∃ x ∈ σ, y ∈ V x := by
      have h := hσ (Set.mem_univ y)
      simpa using h
    exact ⟨⟨x, hxσ⟩, hyx⟩
  · exact fun i => hNspec i.1 _ (le_trans (Finset.le_sup i.2) (le_max_right _ _))

end AlgebraicGeometry.Scheme.Modules

end
