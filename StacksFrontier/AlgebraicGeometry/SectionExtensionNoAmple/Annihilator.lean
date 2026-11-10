module

public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Localization
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Ample
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The module-valued annihilator over a quasi-compact open

`Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero` says that a section of a quasi-coherent
`𝒪_X`-module over an **affine** open which restricts to zero on `X.basicOpen f` is killed by a
power of `f`. This file removes the affineness: a quasi-compact open suffices, which is the
module-valued form of Mathlib's
`AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`.

The proof is the usual one: cover the quasi-compact open by finitely many affine opens, apply the
affine statement on each, raise the finitely many exponents to a single one, and conclude by the
separatedness half of the sheaf condition.

## Why this is needed

The gluing argument of Stacks Tag 01PW reconciles the local extensions on the *pairwise
intersections* of its cover. In
`Stacks.ModuleSectionExtension.exists_tensorSection_of_affine_cover`
those intersections are affine, because there the cover consists of nonvanishing loci of global
sections *and* every member is affine, so [Stacks, Tag 01PV] applies. Once the members are allowed
to be arbitrary affine opens inside nonvanishing loci — which is what dropping ampleness forces,
see `StacksFrontier/AlgebraicGeometry/SectionExtensionNoAmple/Basic.lean` — the intersections are
only quasi-compact, and that is exactly the hypothesis available: an intersection of two
quasi-compact opens of a quasi-separated scheme is quasi-compact.

## Main results

* `Stacks.SectionExtensionNoAmple.exists_finite_affine_cover`: a quasi-compact open of a scheme is
  covered by finitely many affine opens contained in it.
* `Stacks.SectionExtensionNoAmple.exists_pow_smul_eq_zero_of_isCompact`: **the annihilator over a
  quasi-compact open.**
* `Stacks.SectionExtensionNoAmple.exists_pow_smul_eq_of_res_eq_of_isCompact`: its difference form,
  which is the shape the gluing uses.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.ModuleSectionExtension (res resR)
open Stacks.SectionExtension (map_res_res_module exists_forall_le)

universe u

namespace Stacks.SectionExtensionNoAmple

variable {X : Scheme.{u}}

/-- **A quasi-compact open is a finite union of affine opens contained in it.** Refine along the
basis of affine opens (`AlgebraicGeometry.Scheme.isBasis_affineOpens`) and cut the resulting cover
down with `IsCompact.elim_finite_subcover`. -/
theorem exists_finite_affine_cover {W : X.Opens} (hW : IsCompact (W : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Opens),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, V i ≤ W) ∧ W ≤ ⨆ i, V i := by
  classical
  have hcov : (W : Set X) ⊆ ⋃ V : {V : X.affineOpens // (V.1 : X.Opens) ≤ W},
      ((V.1.1 : X.Opens) : Set X) := by
    intro x hx
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
    exact Set.mem_iUnion.mpr ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩
  obtain ⟨T, hT⟩ := hW.elim_finite_subcover
    (fun V : {V : X.affineOpens // (V.1 : X.Opens) ≤ W} => ((V.1.1 : X.Opens) : Set X))
    (fun V => V.1.1.2) hcov
  refine ⟨{i : {V : X.affineOpens // (V.1 : X.Opens) ≤ W} // i ∈ T}, inferInstance,
    fun i => (i.1.1.1 : X.Opens), fun i => i.1.1.2, fun i => i.1.2, fun x hx => ?_⟩
  obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.mp (hT hx)
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, hiT⟩, hxi⟩

/-- **The annihilator, module-valued, over a quasi-compact open.** For `W` a quasi-compact open of
a scheme, `F` a quasi-coherent `𝒪_X`-module and `f : Γ(X, W)`, a section of `F` over `W` which
restricts to zero on `X.basicOpen f` is killed by a power of `f`.

This is `Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero` with affineness of `W` relaxed to
quasi-compactness, obtained from it over a finite affine cover: the exponents produced on the
members are raised to a single one, and the resulting multiple of the section restricts to zero on
every member, hence is zero by `TopCat.Sheaf.eq_of_locally_eq'`. -/
@[ega "I 1.4.1" "more general"]
theorem exists_pow_smul_eq_zero_of_isCompact (F : X.Modules) [F.IsQuasicoherent] {W : X.Opens}
    (hW : IsCompact (W : Set X)) (f : Γ(X, W)) (c : Γ(F, W))
    (hc : res F (X.basicOpen_le f) c = 0) :
    ∃ e : ℕ, f ^ e • c = 0 := by
  obtain ⟨ι, hι, V, hVaff, hVW, hcover⟩ := exists_finite_affine_cover hW
  have : Finite ι := hι
  have hble : ∀ i, X.basicOpen (resR (hVW i) f) ≤ X.basicOpen f := fun i => by
    rw [Scheme.basicOpen_res]; exact inf_le_right
  have key : ∀ i, ∃ e : ℕ, resR (hVW i) f ^ e • res F (hVW i) c = 0 := by
    intro i
    refine Stacks.ModuleSectionExtension.exists_pow_smul_eq_zero F (hVaff i) (resR (hVW i) f)
      (res F (hVW i) c) ?_
    have hstep : res F (X.basicOpen_le (resR (hVW i) f)) (res F (hVW i) c)
        = res F (hble i) (res F (X.basicOpen_le f) c) :=
      (map_res_res_module _ _ c).trans (map_res_res_module _ _ c).symm
    rw [hstep, hc]
    simp
  choose e he using key
  obtain ⟨k, hk⟩ := exists_forall_le e
  refine ⟨k, TopCat.Sheaf.eq_of_locally_eq' (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab X) V W
    (fun i => homOfLE (hVW i)) hcover _ _ fun i => ?_⟩
  have hz : F.presheaf.map (homOfLE (hVW i)).op (0 : Γ(F, W)) = 0 := by simp
  change F.presheaf.map (homOfLE (hVW i)).op (f ^ k • c)
    = F.presheaf.map (homOfLE (hVW i)).op 0
  rw [hz, Scheme.Modules.map_smul, map_pow,
    show k = k - e i + e i from (Nat.sub_add_cancel (hk i)).symm, pow_add, mul_smul, he i,
    smul_zero]

/-- **The annihilator over a quasi-compact open, in difference form**: two sections of a
quasi-coherent module over a quasi-compact open that agree on `X.basicOpen f` agree after
multiplication by a power of `f`. This is the shape the gluing argument of Stacks Tag 01PW uses it
in, and it is `Stacks.ModuleSectionExtension.exists_pow_smul_eq_of_res_eq` with affineness relaxed
to quasi-compactness. -/
theorem exists_pow_smul_eq_of_res_eq_of_isCompact (F : X.Modules) [F.IsQuasicoherent]
    {W : X.Opens} (hW : IsCompact (W : Set X)) (f : Γ(X, W)) (c c' : Γ(F, W))
    (hc : res F (X.basicOpen_le f) c = res F (X.basicOpen_le f) c') :
    ∃ e : ℕ, f ^ e • c = f ^ e • c' := by
  obtain ⟨e, he⟩ := exists_pow_smul_eq_zero_of_isCompact F hW f (c - c') (by
    simp only [res, map_sub, hc, sub_self])
  exact ⟨e, by rwa [smul_sub, sub_eq_zero] at he⟩

end Stacks.SectionExtensionNoAmple

end
