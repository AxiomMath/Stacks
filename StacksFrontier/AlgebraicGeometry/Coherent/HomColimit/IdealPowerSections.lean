module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.GabberColimit.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.IdealPowerMultiple

/-!
# Sections of an ideal-power multiple over an affine open

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals on `X` given by its affine-local ideal
data, and `M` a sheaf of modules on `X`. The subsheaf `I ^ n • M` is defined as the least
subsheaf of `M` containing `I(U) ^ n • Γ(M, U)` on every affine open `U`. When `M` is
quasi-coherent this bound is attained: the sections of `I ^ n • M` over an affine open `U` are
exactly `I(U) ^ n • Γ(M, U)`.

This is the computation that makes the subsheaf usable. The defining infimum gives an upper
bound for the sections on an affine open only in terms of some other subsheaf containing the
local products, so without the equality nothing can be deduced about the sections of
`I ^ n • M` themselves.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPower.idealPowSections`: the family of submodules
  `I(U) ^ n • Γ(M, U)` indexed by the affine opens of `X`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPower.isCompatible_idealPowSections`: for quasi-coherent `M`
  the family is compatible, i.e. the submodule attached to a smaller affine open is generated
  by the restrictions of the sections of the submodule attached to the larger one.
* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_affineOpen`: the sections of
  `I ^ n • M` over an affine open `U` are `I(U) ^ n • Γ(M, U)`.
* `Stacks.AlgebraicGeometry.IdealPower.ideal_eq_top_of_disjoint_support`: an affine open
  disjoint from the support of `I` carries the unit ideal.
* `Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple_obj_eq_top_of_disjoint_support`:
  consequently `I ^ n • M` is all of `M` over any open disjoint from the support of `I`; no
  quasi-coherence is needed for this direction.
* `Stacks.AlgebraicGeometry.IdealPower.mem_of_forall_affineOpens`,
  `Stacks.AlgebraicGeometry.IdealPower.eq_zero_of_locally_zero` and
  `Stacks.AlgebraicGeometry.IdealPower.eq_zero_of_restrict_affineOpens_eq_zero`: membership in
  a subsheaf, and vanishing of a section, are both local on the affine opens.

## Implementation notes

The compatibility of the family, which is the only place quasi-coherence enters, is a span
computation: the restrictions of the sections of `M` over the larger affine open generate the
sections over the smaller one (`Stacks.AlgebraicGeometry.GabberColimit.span_range_restrict_eq_top`,
the surjectivity half of Stacks 01I9), and the restriction of the ideal generates the ideal
there (`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`). Given compatibility, the subsheaf
cut out by the family is `Stacks.AlgebraicGeometry.GabberColimit.sheafSubmodule`, whose sections
over an affine open are the family by construction; identifying `I ^ n • M` with it is then a
two-sided comparison of infima, the harder half of which is that membership in a subsheaf is
local on the affine opens because these form a basis.

The statement about an open disjoint from the support of `I` uses only the easy half, the
defining lower bound, so it holds for an arbitrary sheaf of modules.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.GabberColimit
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

universe u

namespace Stacks.AlgebraicGeometry.IdealPower

variable {X : Scheme.{u}}

/-! ### Locality on the affine opens -/

/-- Every point of an open `W` lies in an affine open contained in `W`. -/
private theorem exists_affineOpen_le_of_mem {W : X.Opens} {x : X} (hx : x ∈ W) :
    ∃ (V : X.affineOpens) (_ : V.1 ≤ W), x ∈ V.1 := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
  exact ⟨⟨V, hV⟩, hVW, hxV⟩

/-- Membership in a subsheaf of a sheaf of modules is local on the affine opens: a section whose
restriction to every affine open contained in `W` lies in the subsheaf lies in it over `W`. -/
theorem mem_of_forall_affineOpens {M : X.Modules} (Q : M.Submodule) {W : X.Opens}
    (s : Γ(M, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W),
      M.presheaf.map (homOfLE hV).op s ∈ Q.toSubmodule.obj (op V.1)) :
    s ∈ Q.toSubmodule.obj (op W) := by
  refine Q.isSheaf (X := op W) s ?_
  intro x hx
  obtain ⟨V, hVW, hxV⟩ := exists_affineOpen_le_of_mem hx
  exact ⟨V, homOfLE hVW, h V hVW, hxV⟩

/-- A section of a sheaf of modules which vanishes on an open neighbourhood of each point of its
domain vanishes. -/
theorem eq_zero_of_locally_zero {M : X.Modules} {W : X.Opens} (s : Γ(M, W))
    (h : ∀ x ∈ W, ∃ (V : X.Opens) (hV : V ≤ W),
      x ∈ V ∧ M.presheaf.map (homOfLE hV).op s = 0) :
    s = 0 := by
  have hF : Presieve.IsSheaf (Opens.grothendieckTopology X)
      (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ _ _ (SheafOfModules.isSheaf M))
  let S : Sieve W :=
    { arrows := fun V f ↦ M.presheaf.map f.op s = 0
      downward_closed := by
        intro V V' f hf g
        rw [op_comp, Functor.map_comp]
        show M.presheaf.map g.op (M.presheaf.map f.op s) = 0
        rw [hf, map_zero] }
  have hS : S ∈ Opens.grothendieckTopology X W := by
    intro x hx
    obtain ⟨V, hVW, hxV, hzero⟩ := h x hx
    exact ⟨V, homOfLE hVW, hzero, hxV⟩
  refine (hF S hS).isSeparatedFor.ext fun V f hf ↦ ?_
  show M.presheaf.map f.op s = M.presheaf.map f.op 0
  exact hf.trans (map_zero _).symm

/-- A section of a sheaf of modules vanishing on every affine open contained in its domain
vanishes. -/
theorem eq_zero_of_restrict_affineOpens_eq_zero {M : X.Modules} {W : X.Opens} (s : Γ(M, W))
    (h : ∀ (V : X.affineOpens) (hV : V.1 ≤ W), M.presheaf.map (homOfLE hV).op s = 0) :
    s = 0 :=
  eq_zero_of_locally_zero s fun x hx ↦ by
    obtain ⟨V, hVW, hxV⟩ := exists_affineOpen_le_of_mem hx
    exact ⟨V, hVW, hxV, h V hVW⟩

/-! ### The affine-local family `I(U) ^ n • Γ(M, U)` -/

/-- The submodule `I(U) ^ n • Γ(M, U)` of the sections of `M` over an affine open `U`. -/
noncomputable def idealPowSections (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (U : X.affineOpens) : Submodule Γ(X, U.1) Γ(M, U.1) :=
  I.ideal U ^ n • ⊤

/-- `idealPowSections I n M U` is the submodule `I(U) ^ n • ⊤` of `Γ(M, U)`. -/
@[simp]
theorem idealPowSections_def (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    (U : X.affineOpens) :
    idealPowSections I n M U = I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) :=
  rfl

/-- The restriction of the `n`-th power of the ideal of a larger affine open generates the
`n`-th power of the ideal of a smaller one. -/
theorem map_idealPow (I : X.IdealSheafData) (n : ℕ) {U W : X.affineOpens} (h : W.1 ≤ U.1) :
    Ideal.map (X.presheaf.map (homOfLE h).op).hom (I.ideal U ^ n) = I.ideal W ^ n := by
  rw [Ideal.map_pow]
  exact congrArg (· ^ n) (I.map_ideal (show W ≤ U from h))

/-- Restriction carries the `n`-th power of the ideal of an affine open into the `n`-th power of
the ideal of a smaller affine open. -/
theorem res_mem_idealPow (I : X.IdealSheafData) (n : ℕ) {U W : X.affineOpens} (h : W.1 ≤ U.1)
    {a : Γ(X, U.1)} (ha : a ∈ I.ideal U ^ n) :
    (X.presheaf.map (homOfLE h).op) a ∈ I.ideal W ^ n :=
  map_idealPow I n h ▸ Ideal.mem_map_of_mem _ ha

/-- For a quasi-coherent `M` the family `U ↦ I(U) ^ n • Γ(M, U)` is compatible: on a smaller
affine open it is generated by the restrictions of its sections on a larger one. -/
theorem isCompatible_idealPowSections (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] : IsCompatible M (idealPowSections I n M) := by
  intro U W h
  refine le_antisymm ?_ ?_
  · rw [idealPowSections, Submodule.smul_le]
    intro a ha
    rw [← map_idealPow I n h, Ideal.map] at ha
    induction ha using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨b', hb', rfl⟩ := hb
      intro y hytop
      clear hytop
      have hy : y ∈ Submodule.span Γ(X, W.1)
          (Set.range (M.presheaf.map (homOfLE h).op)) := by
        rw [span_range_restrict_eq_top M U.2 W.2 h]; trivial
      induction hy using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨x, rfl⟩ := hz
        refine Submodule.subset_span ⟨b' • x, ?_, ?_⟩
        · exact Submodule.smul_mem_smul hb' Submodule.mem_top
        · exact M.map_smul (homOfLE h) b' x
      | zero => simp
      | add p q _ _ hp hq => simpa [smul_add] using Submodule.add_mem _ hp hq
      | smul r p _ hp =>
        rw [smul_comm]
        exact Submodule.smul_mem _ _ hp
    | zero => intro y _; simp
    | add p q _ _ hp hq =>
      intro y hy
      simpa [add_smul] using Submodule.add_mem _ (hp y hy) (hq y hy)
    | smul r p _ hp =>
      intro y hy
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ _ (hp y hy)
  · rw [Submodule.span_le]
    rintro y ⟨z, hz, rfl⟩
    refine Submodule.smul_induction_on hz ?_ ?_
    · intro a ha x _
      rw [M.map_smul (homOfLE h) a x]
      exact Submodule.smul_mem_smul (res_mem_idealPow I n h ha) Submodule.mem_top
    · intro p q hp hq
      simpa using Submodule.add_mem _ hp hq

/-! ### The sections of `I ^ n • M` -/

/-- For a quasi-coherent `M` the subsheaf `I ^ n • M` is the subsheaf cut out by the family
`U ↦ I(U) ^ n • Γ(M, U)`. -/
theorem idealPowerMultiple_eq_sheafSubmodule (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] :
    idealPowerMultiple I n M =
      sheafSubmodule M (idealPowSections I n M) (isCompatible_idealPowSections I n M) := by
  refine le_antisymm ?_ ?_
  · rw [idealPowerMultiple_le_iff]
    intro U
    rw [obj_sheafSubmodule]
    exact le_rfl
  · show sheafSubmodule M (idealPowSections I n M) _ ≤ sInf _
    refine le_sInf fun Q hQ W s hs ↦ ?_
    obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, op W' = W := ⟨W.unop, rfl⟩
    exact mem_of_forall_affineOpens Q s fun V hV ↦ hQ V (hs V hV)

/-- **The sections of `I ^ n • M` over an affine open.** For a quasi-coherent sheaf of modules
`M` on a scheme and an affine open `U`, the sections of `I ^ n • M` over `U` are exactly
`I(U) ^ n • Γ(M, U)`. -/
theorem idealPowerMultiple_obj_affineOpen (I : X.IdealSheafData) (n : ℕ) (M : X.Modules)
    [M.IsQuasicoherent] (U : X.affineOpens) :
    (idealPowerMultiple I n M).toSubmodule.obj (op U.1) =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
  rw [idealPowerMultiple_eq_sheafSubmodule I n M, obj_sheafSubmodule]
  rfl

/-! ### Away from the support of the ideal -/

/-- An affine open disjoint from the support of an ideal sheaf carries the unit ideal. -/
theorem ideal_eq_top_of_disjoint_support (I : X.IdealSheafData) {V : X.affineOpens}
    (h : Disjoint (V.1 : Set X) (I.support : Set X)) : I.ideal V = ⊤ := by
  have hempty : X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)) ∩ (V.1 : Set X) = ∅ := by
    rw [← I.coe_support_inter V]
    exact Set.eq_empty_iff_forall_notMem.mpr fun x hx ↦
      Set.disjoint_left.mp h hx.2 hx.1
  have himg : V.2.fromSpec.base ''
      PrimeSpectrum.zeroLocus (I.ideal V : Set Γ(X, V.1)) = ∅ := by
    rw [V.2.fromSpec_image_zeroLocus]
    exact hempty
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp (Set.image_eq_empty.mp himg)

/-- Over an open disjoint from the support of `I` the subsheaf `I ^ n • M` is all of `M`. No
quasi-coherence is required: only the defining lower bound of `I ^ n • M` is used. -/
theorem idealPowerMultiple_obj_eq_top_of_disjoint_support (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) {W : X.Opens} (hW : Disjoint (W : Set X) (I.support : Set X))
    {V : X.Opens} (hV : V ≤ W) :
    (idealPowerMultiple I n M).toSubmodule.obj (op V) = ⊤ := by
  refine eq_top_iff.mpr fun s _ ↦ ?_
  refine mem_of_forall_affineOpens _ s fun V' hV' ↦ ?_
  have hdisj : Disjoint (V'.1 : Set X) (I.support : Set X) :=
    Set.disjoint_of_subset_left (fun _ hx ↦ hV (hV' hx)) hW
  refine le_idealPowerMultiple_obj I n M V' ?_
  have htop : I.ideal V' ^ n • (⊤ : Submodule Γ(X, V'.1) Γ(M, V'.1)) = ⊤ := by
    rw [ideal_eq_top_of_disjoint_support I hdisj, ← Ideal.one_eq_top, one_pow,
      Ideal.one_eq_top, Submodule.top_smul]
  rw [htop]
  exact Submodule.mem_top

end Stacks.AlgebraicGeometry.IdealPower

end
