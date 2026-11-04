module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.Reduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.RationalSingularity
public import StacksFrontier.RingTheory.Length.MaximalIdealPower
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `H¹(X, 𝒪_X)` has finite length for a modification of a surface

Let `(A, 𝔪)` be a two-dimensional Noetherian normal local domain and let `f : X ⟶ Spec(A)` be a
modification. Then `H¹(X, 𝒪_X)`, as an `A`-module, has finite length.

Two facts are combined. The module is finite over `A`, because the higher direct images of a
coherent module under a proper morphism are coherent ([Stacks, Tag 02O5]); and it is supported at
the closed point, because `f` is an isomorphism over the punctured spectrum, so that the stalk of
`R¹f_*𝒪_X` at every prime `𝔭 ≠ 𝔪` vanishes. A finite module whose support is contained in `{𝔪}`
is annihilated by a power of `𝔪`, and a finite module annihilated by a power of the maximal ideal
of a Noetherian local ring has finite length ([Stacks, Tag 00J0]).

## Main results

All in the namespace `AlgebraicGeometry`.

* `moduleFinite_firstCohomologyAsBaseModule` — `H¹(X, 𝒪_X)` is a finite `A`-module for a proper
  `f : X ⟶ Spec(A)`. This is `moduleFinite_firstCohomologySheafAsBaseModule` at the structure
  sheaf, with the coherence of the structure sheaf discharged.
* `exists_notMem_forall_smul_firstCohomologyAsBaseModule_eq_zero` — for every prime `𝔭 ≠ 𝔪` a
  single element of `A` outside `𝔭` annihilates all of `H¹(X, 𝒪_X)`.
* `le_radical_annihilator_firstCohomologyAsBaseModule` — `𝔪` lies in the radical of the
  annihilator, which is the ideal-theoretic form of "supported at the closed point".
* `isFiniteLength_firstCohomologyAsBaseModule` — the finite length.

## Implementation notes

Both inputs are already in the tree and are only assembled here.
`AlgebraicGeometry.DualizingDivisor.exists_smul_eq_zero_rightDerived_one` of
`ResolutionOfSurfaces/DualizingDivisor/FirstCohomologyTorsion.lean` is the element-by-element
support statement, for an arbitrary quasi-coherent module and in the spelling
`((globalSectionsOver f).rightDerived 1).obj 𝒢`; it is carried to the spelling
`AlgebraicGeometry.firstCohomologyAsBaseModule` by
`AlgebraicGeometry.DualizingDivisor.rightDerivedOneUnitIso`. The passage from "each element is
killed by something outside `𝔭`" to "one element outside `𝔭` kills everything" is
`AlgebraicGeometry.DualizingDivisor.exists_notMem_forall_smul_eq_zero`, which needs the
finiteness. The combined statement occurs inside the proof of
`AlgebraicGeometry.DualizingDivisor.subsingleton_rightDerived_one_and_nonempty_iso` as a local
`have`; it is stated here instead, since what that proof consumes is the support hypothesis of
`Stacks.PurityRamification.subsingleton_homology_succ_of_forall_eq_smul` and what is needed below
is the finite length.

Finite length from a power of `𝔪` is `Module.finiteLength_quotient_of_contains_maximalIdealPower`
at the zero submodule, and the power exists because the radical of a finitely generated ideal
contains a power of any ideal it contains (`Ideal.exists_pow_le_of_le_radical_of_fg_radical`).

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 00J0](https://stacks.math.columbia.edu/tag/00J0)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A]

/-- **`H¹(X, 𝒪_X)` is a finite `A`-module for a proper morphism `X ⟶ Spec(A)`.** This is
`AlgebraicGeometry.moduleFinite_firstCohomologySheafAsBaseModule` at the structure sheaf, whose
coherence over a Noetherian base holds because `f` is of finite type. -/
@[ega "III 2.5.1" "Finite type of H^1(X"]
theorem moduleFinite_firstCohomologyAsBaseModule [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] :
    Module.Finite A (firstCohomologyAsBaseModule X f) := by
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  exact moduleFinite_firstCohomologySheafAsBaseModule f (SheafOfModules.unit X.ringCatSheaf)

variable [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]

/-- **One element outside a prime `𝔭 ≠ 𝔪` annihilates all of `H¹(X, 𝒪_X)`.** Every element of
`H¹(X, 𝒪_X)` is killed by some element outside `𝔭`
(`AlgebraicGeometry.DualizingDivisor.exists_smul_eq_zero_rightDerived_one`), and the module is
finite, so a finite product of such elements kills it. -/
theorem exists_notMem_forall_smul_firstCohomologyAsBaseModule_eq_zero
    (hdim : ringKrullDim A = 2) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsModification f)
    (p : Ideal A) [p.IsPrime] (hp : p ≠ IsLocalRing.maximalIdeal A) :
    ∃ c : A, c ∉ p ∧ ∀ x : firstCohomologyAsBaseModule X f, c • x = 0 := by
  have : IsProper f := hf.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : Module.Finite A (firstCohomologyAsBaseModule X f) :=
    moduleFinite_firstCohomologyAsBaseModule f
  have e : ↥(((globalSectionsOver f).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf))
      ≃ₗ[A] ↥(firstCohomologyAsBaseModule X f) :=
    (DualizingDivisor.rightDerivedOneUnitIso (Over.mk f)).toLinearEquiv
  refine DualizingDivisor.exists_notMem_forall_smul_eq_zero p fun x => ?_
  obtain ⟨a, ha, hax⟩ := DualizingDivisor.exists_smul_eq_zero_rightDerived_one hdim f hf
    (SheafOfModules.unit X.ringCatSheaf) p hp (e.symm x)
  exact ⟨a, ha, e.symm.map_eq_zero_iff.mp ((map_smul e.symm a x).trans hax)⟩

/-- **`H¹(X, 𝒪_X)` is supported at the closed point**, as a statement about its annihilator: the
maximal ideal lies in the radical of `Ann_A H¹(X, 𝒪_X)`. A prime containing the annihilator
cannot be different from `𝔪`, since outside such a prime there is an element of the
annihilator. -/
theorem le_radical_annihilator_firstCohomologyAsBaseModule (hdim : ringKrullDim A = 2)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsModification f) :
    IsLocalRing.maximalIdeal A ≤
      (Module.annihilator A (firstCohomologyAsBaseModule X f)).radical := by
  rw [Ideal.radical_eq_sInf]
  refine le_sInf ?_
  rintro J ⟨hJ, hJp⟩
  have : J.IsPrime := hJp
  by_cases hJm : J = IsLocalRing.maximalIdeal A
  · exact hJm ▸ le_rfl
  · obtain ⟨c, hc, hc0⟩ :=
      exists_notMem_forall_smul_firstCohomologyAsBaseModule_eq_zero hdim f hf J hJm
    exact absurd (hJ (Module.mem_annihilator.mpr hc0)) hc

/-- **`H¹(X, 𝒪_X)` has finite length for a modification of a two-dimensional Noetherian normal
local domain.** The module is finite and supported at the closed point, so a power of the maximal
ideal annihilates it, and a finite module annihilated by a power of the maximal ideal of a
Noetherian local ring has finite length ([Stacks, Tag 00J0]). -/
theorem isFiniteLength_firstCohomologyAsBaseModule (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) :
    IsFiniteLength A (firstCohomologyAsBaseModule X f) := by
  have : IsProper f := hf.isProper
  have : Module.Finite A (firstCohomologyAsBaseModule X f) :=
    moduleFinite_firstCohomologyAsBaseModule f
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical
    (le_radical_annihilator_firstCohomologyAsBaseModule hdim f hf) (IsNoetherian.noetherian _)
  have hle : IsLocalRing.maximalIdeal A ^ (k + 1) •
      (⊤ : Submodule A (firstCohomologyAsBaseModule X f)) ≤ ⊥ :=
    Submodule.smul_le.mpr fun a ha x _ =>
      (Submodule.mem_bot A).mpr (Module.mem_annihilator.mp
        (hk (Ideal.pow_le_pow_right (Nat.le_succ k) ha)) x)
  exact IsFiniteLength.of_surjective (Module.finiteLength_quotient_of_contains_maximalIdealPower
    A (firstCohomologyAsBaseModule X f) ⊥ k hle) (Submodule.quotEquivOfEqBot _ rfl).surjective

end AlgebraicGeometry

end
