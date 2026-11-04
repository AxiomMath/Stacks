module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.FormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageFibreDimension.GeneralDimensionAux

/-!
# Tag 02V7 over an affine Noetherian base

Let `A` be a Noetherian ring, let `f : X ⟶ Spec A` be proper with every fibre of dimension at
most `d`, and let `ℱ` be a coherent `𝒪_X`-module. This file proves `Hᵖ(X, ℱ) = 0` for `p > d`,
which is the substance of [Stacks, Tag 02V7]; the reduction of the tag to this statement is in
`StacksFrontier/AlgebraicGeometry/HigherDirectImageFibreDimension/GeneralDimension.lean`, where the
attribute is carried.

The argument is the source's, with the completion replaced by the uniform bound it rests on.
Write `M = Hᵖ(X, ℱ)`, an `A`-module, and let `𝔪` be a maximal ideal of `A`.

* `M` is a finite `A`-module ([Stacks, Tag 02O6], in the form
  `Stacks.Algebraization.moduleFinite_cohomologyOverBase`).
* [Stacks, Tag 02OB] gives a `c` such that for every `n ≥ c` the kernel of the projection
  `M ⟶ Hᵖ(X, ℱ / 𝔪ⁿ ℱ)` lies in `𝔪 ⁿ⁻ᶜ M`. The form used here,
  `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`,
  carries only [Stacks, Tag 02O8], which is proved unconditionally in this development as
  `Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem`.
* `Hᵖ(X, ℱ / 𝔪ⁿ ℱ) = 0` for `p > d`, because that sheaf lives on a closed subscheme whose space
  is contained in the fibre over `𝔪`, which is Noetherian of dimension at most `d`; this is
  `Stacks.AlgebraicGeometry.FibreDimension.isZero_hgroup_idealPowerQuotient_baseIdealSheaf`.
* Taking `n = c + 1` the projection is the zero map, so its kernel is all of `M` and `M = 𝔪 M`.
  As `𝔪` was an arbitrary maximal ideal and `M` is finite, Nakayama forces `M = 0`: a maximal
  ideal containing the annihilator of a nonzero `M` would contain `1`.

This is where the completion of the source's `Hᵖ(X, ℱ)^∧ ≅ lim Hᵖ(X, ℱ / 𝔪ⁿ ℱ)`
([Stacks, Tag 02OC]) is avoided: only the kernel clause of [Stacks, Tag 02OB] is needed, and
only at a single `n`, since the limit is being shown to vanish rather than computed.

## Main results

Both in the namespace `Stacks.AlgebraicGeometry.FibreDimension`.

* `top_le_smul_top_cohomologyOverBase`: `Hᵖ(X, ℱ) = 𝔪 Hᵖ(X, ℱ)` for every maximal ideal `𝔪`,
  in degrees above `d`.
* `isZero_rightDerived_moduleGlobalSections_of_forall_fiber_dim_le`: `Hᵖ(X, ℱ) = 0` for `p > d`.

## Implementation notes

`cohomologyOverBase A f p ℱ` is `Hᵖ(X, ℱ)` read as an `A`-module through
`Stacks.Cohomology.FormalFunctions.baseRingHom`; it is the spelling the 02OB bound is stated in.
Restriction of scalars does not change the carrier, so vanishing transfers to the
`Γ(X, ⊤)`-module `((moduleGlobalSections X).rightDerived p).obj ℱ` by
`ModuleCat.isZero_iff_subsingleton`.

The two coherence predicates of the library, `SheafOfModules.IsCoherent` and
`Stacks.SheafOfModules.IsCoherent`, both occur: the first is the instance, the second is what
the 02OB statement asks for, and
`AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent` converts.

## References

* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase Stacks.Cohomology.FormalFunctions

universe u

namespace Stacks.AlgebraicGeometry.FibreDimension

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of A)) [IsProper f]

/-- **`Hᵖ(X, ℱ) = 𝔪 Hᵖ(X, ℱ)` in degrees above the fibre dimension.** For `f : X ⟶ Spec A`
proper with `A` Noetherian and every fibre of dimension at most `d`, for `ℱ` coherent and for
`p > d`, every maximal ideal `𝔪` of `A` satisfies `Hᵖ(X, ℱ) = 𝔪 · Hᵖ(X, ℱ)`.

The kernel clause of [Stacks, Tag 02OB] bounds the kernel of `Hᵖ(X, ℱ) ⟶ Hᵖ(X, ℱ / 𝔪ⁿ ℱ)` by
`𝔪 ⁿ⁻ᶜ Hᵖ(X, ℱ)` for `n ≥ c`; the target vanishes, so at `n = c + 1` the kernel is everything
and the bound reads `Hᵖ(X, ℱ) ⊆ 𝔪 Hᵖ(X, ℱ)`. -/
theorem top_le_smul_top_cohomologyOverBase {d : ℕ}
    (hfib : ∀ s : Spec (.of A), topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent] {p : ℕ} (hp : d < p)
    (m : Ideal A) [m.IsMaximal] :
    (⊤ : Submodule A (cohomologyOverBase A f p F)) ≤
      m • (⊤ : Submodule A (cohomologyOverBase A f p F)) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { }
  have : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  obtain ⟨c, hker, -, -⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 A f ‹IsProper f› m F
      (_root_.AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent ‹_›) p
      Stacks.FormalFunctions.isReesFinite_cohomologyIdealPowerSystem
  -- The cohomology of `ℱ / 𝔪 ^ (c + 1) ℱ` vanishes, so the projection is the zero map.
  have hzero : IsZero (cohomologyOverBase A f p
      (Stacks.Algebraization.idealPowerQuotient (baseIdealSheaf A m f) (c + 1) F)) := by
    have h1 : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj
        (Stacks.Algebraization.idealPowerQuotient (baseIdealSheaf A m f) (c + 1) F)) :=
      (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
          (R := X.ringCatSheaf) (U := ⊤) p _).mpr
        (isZero_hgroup_idealPowerQuotient_baseIdealSheaf f m
          ⟨m, ‹m.IsMaximal›.isPrime⟩ rfl (c + 1) F (hfib _) hp)
    have hadd : (ModuleCat.restrictScalars (baseRingHom A f)).Additive := ⟨by intros; rfl⟩
    exact Functor.map_isZero (ModuleCat.restrictScalars (baseRingHom A f)) h1
  have hk := hker (c + 1) (Nat.le_succ c)
  have htop : LinearMap.ker (cohomologyOverBaseMap A f p
      (cokernel.π (C := X.Modules)
        (Stacks.Algebraization.idealPowerMultiple (baseIdealSheaf A m f) (c + 1) F).ι)).hom
      = ⊤ := by
    exact LinearMap.ker_eq_top.mpr (congrArg ModuleCat.Hom.hom (hzero.eq_zero_of_tgt _))
  rw [htop, Nat.add_sub_cancel_left, pow_one] at hk
  exact hk

/-- **[Stacks, Tag 02V7] over an affine Noetherian base.** For `f : X ⟶ Spec A` proper with `A`
Noetherian and every fibre of dimension at most `d`, the cohomology `Hᵖ(X, ℱ)` of a coherent
module vanishes for `p > d`.

`Hᵖ(X, ℱ)` is a finite `A`-module by [Stacks, Tag 02O6] and equals `𝔪 Hᵖ(X, ℱ)` for every
maximal ideal `𝔪`. Were it nonzero its annihilator would be a proper ideal, so contained in some
maximal `𝔪`; Nakayama ([Stacks, Tag 00DV]) then produces `r` with `r - 1 ∈ 𝔪` annihilating the
module, whence `r ∈ 𝔪` and `1 ∈ 𝔪`. -/
theorem isZero_rightDerived_moduleGlobalSections_of_forall_fiber_dim_le {d : ℕ}
    (hfib : ∀ s : Spec (.of A), topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsCoherent] {p : ℕ} (hp : d < p) :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived p).obj F) := by
  have : Module.Finite A ↥(cohomologyOverBase A f p F) :=
    Stacks.Algebraization.moduleFinite_cohomologyOverBase A f F p
  refine ModuleCat.isZero_iff_subsingleton.mpr ?_
  show Subsingleton ↥(cohomologyOverBase A f p F)
  by_contra hns
  have hann : Module.annihilator A ↥(cohomologyOverBase A f p F) ≠ ⊤ := fun h =>
    hns (Module.annihilator_eq_top_iff.mp h)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hann
  have : m.IsMaximal := hm
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul
    m ⊤ Module.Finite.fg_top (top_le_smul_top_cohomologyOverBase f hfib F hp m)
  have hrann : r ∈ Module.annihilator A ↥(cohomologyOverBase A f p F) :=
    Module.mem_annihilator.mpr fun x => hr0 x Submodule.mem_top
  have hone : (1 : A) ∈ m := by
    have h2 : r - (r - 1) ∈ m := Ideal.sub_mem m (hle hrann) hr1
    simpa using h2
  exact hm.ne_top (Ideal.eq_top_of_isUnit_mem m hone isUnit_one)

end Stacks.AlgebraicGeometry.FibreDimension

end
