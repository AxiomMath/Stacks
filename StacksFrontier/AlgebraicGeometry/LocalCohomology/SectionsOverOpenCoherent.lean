module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.SubmoduleAscendingChain
public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.ArtinReesSeparation
public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.IdealPowerSections
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.SectionsOverOpen
public import StacksFrontier.AlgebraicGeometry.Modules.IdealSheafDataSubmodule
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk

/-!
# Sections away from `V(I)` as homomorphisms out of an ideal power, for a coherent module

Let `X` be a Noetherian scheme, `I` a quasi-coherent sheaf of ideals whose first power `I • 𝒪_X`
is of finite type, and `F` a **coherent** `𝒪_X`-module. Writing `U` for the open complement
`X ∖ V(I)`, the canonical map
`colim_n Hom(I ^ n • 𝒪_X, F) ⟶ Γ(F, U)`
of `Stacks.LocalCohomology.canonicalMapToSections` is a bijection.

`Stacks.LocalCohomology.canonicalMapToSections_bijective_of_noIdealTorsion` gives this when `F`
has no `I`-torsion. In general, replace `F` by the subsheaf `F' = I ^ m • F` for a large `m`. Over
an open disjoint from `V(I)` the subsheaf `F'` has *all* the sections of `F`, so the target of the
canonical map does not change, while for `m` large `F'` has no `I`-torsion at all. The exponent
comes from Artin–Rees together with the stabilization of the ascending chain of subsheaves of
`I`-power torsion.

## Main results

* `Stacks.LocalCohomology.exists_eventually_constant_idealPowerAnnihilator` — the chain of
  ideal-power annihilator subsheaves of a coherent module on a Noetherian scheme is eventually
  constant on the sections over every affine open.
* `Stacks.LocalCohomology.exists_idealPow_smul_inf_annihilator_eq_bot` — some ideal multiple
  `I ^ m • F` meets every annihilator subsheaf in zero, on every affine open.
* `Stacks.LocalCohomology.exists_noIdealTorsion_idealPowerMultiple` — hence `I ^ m • F` has no
  `I`-torsion for `m` large.
* `Stacks.LocalCohomology.idealPowerMultiple_obj_idealComplement_eq_top` — over the complement of
  `V(I)` the subsheaf `I ^ m • F` has all the sections of `F`.
* `Stacks.LocalCohomology.canonicalMapToSections_surjective_of_isCoherent` and
  `Stacks.LocalCohomology.canonicalMapToSections_bijective_of_isCoherent` — the canonical map is
  surjective, hence bijective, for a coherent module.

## Implementation notes

The annihilator subsheaves `AlgebraicGeometry.idealPowerAnnihilator` and the Artin–Rees
separation of [Stacks, Tag 01YA] are stated for an ideal presented as a submodule of the
structure sheaf, while `idealPowerMultiple` and the canonical map are stated for Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData`. The passage between them is
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule`, whose sections over an affine open are
the ideal of `I` there.

`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` and
`Stacks.Algebraization.idealPowerMultiple` are two definitions with the same body, so
quasi-coherence of the ideal-power subsheaf, proved for the second, applies verbatim to the
first; this is `Stacks.LocalCohomology.isQuasicoherent_idealPowerMultiple`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01Y8](https://stacks.math.columbia.edu/tag/01Y8)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01PG](https://stacks.math.columbia.edu/tag/01PG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.LocalCohomology

open Stacks.Ample (unitModule)

variable {X : Scheme.{u}}

/-! ### The ideal multiple without `I`-torsion -/

/-- A coherent module is quasi-coherent. -/
private instance isQuasicoherent_of_isCoherent (F : X.Modules) [F.IsCoherent] :
    F.IsQuasicoherent :=
  (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1

/-- On a Noetherian scheme the ascending chain of subsheaves of `I`-power torsion of a coherent
module becomes constant: there is an `n` beyond which the sections of the annihilator subsheaf
over every affine open no longer depend on the exponent. This is a form of [Stacks, Tag 01Y8]. -/
theorem exists_eventually_constant_idealPowerAnnihilator [IsNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsCoherent] :
    ∃ n : ℕ, ∀ N : ℕ, n ≤ N → ∀ U : X.affineOpens,
      (idealPowerAnnihilator I.unitSubmodule F N).toSubmodule.obj (op U.1) =
        (idealPowerAnnihilator I.unitSubmodule F n).toSubmodule.obj (op U.1) := by
  obtain ⟨n, hn⟩ := exists_eventually_constant_quasicoherentSubmodules X F
    (fun k => idealPowerAnnihilator I.unitSubmodule F k)
    (fun _ => inferInstance)
    (fun _ _ h => SheafOfModules.Submodule.le_iff.2 (idealPowerAnnihilator_monotone _ F h))
  exact ⟨n, fun N hN U => congrArg (fun P => P.toSubmodule.obj (op U.1)) (hn N hN)⟩

/-- On a Noetherian scheme a sufficiently high ideal multiple of a coherent module meets *every*
subsheaf of `I`-power torsion in zero, tested on the sections over each affine open. -/
theorem exists_idealPow_smul_inf_annihilator_eq_bot [IsNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsCoherent] :
    ∃ m : ℕ, ∀ (N : ℕ) (U : X.affineOpens),
      (I.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1))) ⊓
          (idealPowerAnnihilator I.unitSubmodule F N).toSubmodule.obj (op U.1) =
        ⊥ := by
  obtain ⟨n, hn⟩ := exists_eventually_constant_idealPowerAnnihilator I F
  obtain ⟨m, hm⟩ := exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot_of_stabilizes
    F I.unitSubmodule n hn
  exact ⟨m, fun N U => by simpa only [I.unitSubmodule_obj_affine U] using hm N U⟩

/-- On a Noetherian scheme a coherent module `F` has an ideal multiple `I ^ m • F` with no
`I`-torsion at all. -/
theorem exists_noIdealTorsion_idealPowerMultiple [IsNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsCoherent] :
    ∃ m : ℕ, NoIdealTorsion I (idealPowerMultiple I m F).toModules := by
  obtain ⟨m, hm⟩ := exists_idealPow_smul_inf_annihilator_eq_bot I F
  refine ⟨m, fun U y hy => Subtype.ext <| (Submodule.eq_bot_iff _).1 (hm 1 U) y.1 ⟨?_, ?_⟩⟩
  · rw [← idealPowerMultiple_obj_affine_of_isQuasicoherent I m F U]
    exact y.2
  · refine (mem_idealPowerAnnihilator_affine_iff I.unitSubmodule F 1 U.2 _).2 fun b hb => ?_
    rw [pow_one] at hb
    exact congrArg Subtype.val (hy b (by rw [← I.unitSubmodule_obj_affine U]; exact hb))

/-! ### The canonical map for a coherent module -/

/-- The ideal-power subsheaf `I ^ n • F` of a quasi-coherent module is quasi-coherent. -/
lemma isQuasicoherent_idealPowerMultiple (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] : (idealPowerMultiple I n F).toSheafOfModules.IsQuasicoherent :=
  Stacks.Algebraization.idealPowerMultiple_isQuasicoherent I n F

/-- Over the complement of `V(I)` the subsheaf `I ^ n • F` has all the sections of `F`: the
complement is disjoint from the support of `I`, where `I` is the unit ideal. -/
lemma idealPowerMultiple_obj_idealComplement_eq_top (I : X.IdealSheafData) (n : ℕ)
    (F : X.Modules) :
    (idealPowerMultiple I n F).toSubmodule.obj (op (idealComplement I)) = ⊤ :=
  idealPowerMultiple_obj_eq_top_of_disjoint_support' I n F _ fun _ hx => hx

/-- On a Noetherian scheme, for a sheaf of ideals whose first power is of finite type and a
coherent `𝒪_X`-module `F`, every section of `F` over `X ∖ V(I)` is the value on the unit section
of a morphism `I ^ n • 𝒪_X ⟶ F`. -/
theorem canonicalMapToSections_surjective_of_isCoherent [IsNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsCoherent]
    [((idealPowerMultiple I 1 (unitModule X)).toModules).IsFiniteType] :
    Function.Surjective (canonicalMapToSections I F).1 := by
  rw [canonicalMapToSections_surjective_iff]
  intro s
  obtain ⟨m, hm⟩ := exists_noIdealTorsion_idealPowerMultiple I F
  have : ((idealPowerMultiple I m F).toModules).IsQuasicoherent :=
    isQuasicoherent_idealPowerMultiple I m F
  have hsurj := canonicalMapToSections_surjective_of_noIdealTorsion I
    (idealPowerMultiple I m F).toModules hm
  rw [canonicalMapToSections_surjective_iff] at hsurj
  obtain ⟨n, φ, hφ⟩ :=
    hsurj ⟨s, Submodule.eq_top_iff'.1 (idealPowerMultiple_obj_idealComplement_eq_top I m F) s⟩
  exact ⟨n, φ ≫ (idealPowerMultiple I m F).ιModules, congrArg Subtype.val hφ⟩

/-- On a Noetherian scheme, for a sheaf of ideals whose first power is of finite type and a
coherent `𝒪_X`-module `F`, the canonical map
`colim_n Hom(I ^ n • 𝒪_X, F) → Γ(F, X ∖ V(I))`
is a bijection: the second clause of [Stacks, Tag 01YB] for a coherent module. -/
theorem canonicalMapToSections_bijective_of_isCoherent [IsNoetherian X] (I : X.IdealSheafData)
    (F : X.Modules) [F.IsCoherent]
    [((idealPowerMultiple I 1 (unitModule X)).toModules).IsFiniteType] :
    Function.Bijective (canonicalMapToSections I F).1 :=
  ⟨canonicalMapToSections_injective I F,
    canonicalMapToSections_surjective_of_isCoherent I F⟩

end Stacks.LocalCohomology

end
