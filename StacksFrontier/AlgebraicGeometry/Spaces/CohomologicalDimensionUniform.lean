module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingAboveTheDimensionInduction

/-!
# Uniform vanishing of the cohomology of a quasi-compact quasi-separated algebraic space

Stacks 072C says that on a quasi-compact and quasi-separated algebraic space `X` there is a
single degree beyond which the cohomology of every quasi-coherent `𝒪_X`-module vanishes.

## Main results

All names are in the namespace `AlgebraicGeometry.Space`.

* `exists_forall_isZero_rightDerived_globalSectionsAb_of_isQuasiCompactSpace`: the uniform
  vanishing for the cohomology as abelian groups.
* `exists_forall_isZero_rightDerived_globalSectionsFunctor_of_isQuasiCompactSpace`:
  **Stacks 072C**, a single degree beyond which the cohomology of every quasi-coherent
  `𝒪_X`-module vanishes.
* `exists_forall_isZero_rightDerived_globalSectionsFunctor_of_isCoherent`: the same bound for
  coherent modules.

## Implementation notes

**The cohomology used.** `Hᑫ(X, 𝓕)` is the right derived functor of the global sections functor
of the small étale ringed site of `X`, `Stacks.Cohomology.SiteModules.globalSectionsFunctor`, at
modules in the universe of the schemes.  The quasi-coherence of a module is
`SheafOfModules.IsQuasicoherentOnSite` on that site, which is [Stacks, Tag 03DL], and coherence
is `AlgebraicGeometry.Space.IsCoherent` of [Stacks, Tag 07UA], whose parent projection supplies
quasi-coherence.

**The degree.** The statement asserts that some degree exists; it does not assert that the
source's explicit degree `max (d_p + p)` works.

## References

* [Stacks Project, Tag 072C](https://stacks.math.columbia.edu/tag/072C)
* [Stacks Project, Tag 0728](https://stacks.math.columbia.edu/tag/0728)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 0CRS](https://stacks.math.columbia.edu/tag/0CRS)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07UA](https://stacks.math.columbia.edu/tag/07UA)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules
  etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The uniform vanishing of Stacks 072C for the cohomology as abelian groups: on a
quasi-compact and quasi-separated algebraic space there is a single degree beyond which the
cohomology of every quasi-coherent module vanishes. -/
theorem exists_forall_isZero_rightDerived_globalSectionsAb_of_isQuasiCompactSpace
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ N : ℕ, ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite → ∀ q, N ≤ q →
      IsZero (((globalSectionsAb B S hS X).rightDerived q).obj F) := by
  suffices key : ∃ N : ℕ, ∀ (hY : IsAlgebraicSpace B S hS X.1)
      (F : Modules.{u, u} B S hS X.1 hY), F.IsQuasicoherentOnSite → ∀ q : ℕ, N ≤ q →
        IsZero (((globalSectionsAb B S hS ⟨X.1, hY⟩).rightDerived q).obj F) from
    key.imp fun _ hN => hN X.2
  refine qcqs_induction_on_self B S hS hZ X hqc hqs
    (fun Y _ => ∃ N : ℕ, ∀ (hY : IsAlgebraicSpace B S hS Y)
      (F : Modules.{u, u} B S hS Y hY), F.IsQuasicoherentOnSite → ∀ q : ℕ, N ≤ q →
        IsZero (((globalSectionsAb B S hS ⟨Y, hY⟩).rightDerived q).obj F)) ?_ ?_
  · exact fun V hVaff => ⟨1, fun hY F hF q hq =>
      (isZero_rightDerived_globalSectionsAb_iff B S hS ⟨V.1.left.1, hY⟩ F q).2
        (isZero_rightDerived_globalSectionsFunctor_of_isAffineSpace B S hS ⟨V.1.left.1, hY⟩
          hVaff F hF q (by omega))⟩
  rintro W V U f _ hsq _ _ _ _ ⟨NU, hNU⟩ ⟨NV, hNV⟩ ⟨NP, hNP⟩
  refine ⟨max (max (max NU NV) (NP + 1)) 1, fun hY F hF q hq => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  refine isZero_rightDerived_globalSectionsAb_succ_of_eds B S hS hsq F n ?_ ?_ ?_
  · exact (hNU _ _ (isQuasicoherentOnSite_etaleModulePullback B S hS _
      (isEtale_edsOpenHom B S hS hsq) F hF) (n + 1) (by omega)).of_iso
      (rightDerivedGlobalSectionsAbRestrictPushIso B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq) F (n + 1))
  · exact (hNV _ _ (isQuasicoherentOnSite_etaleModulePullback B S hS _
      (isEtale_edsEtaleHom B S hS hsq) F hF) (n + 1) (by omega)).of_iso
      (rightDerivedGlobalSectionsAbRestrictPushIso B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq) F (n + 1))
  · exact (hNP _ _ (isQuasicoherentOnSite_etaleModulePullback B S hS _
      (isEtale_edsInterHom B S hS hsq) F hF) n (by omega)).of_iso
      (rightDerivedGlobalSectionsAbRestrictPushIso B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq) F n)

/-- **Stacks 072C, the uniform vanishing.**  On a quasi-compact and quasi-separated algebraic
space `X` there is a single degree `N` beyond which the cohomology of every quasi-coherent
`𝒪_X`-module vanishes: `Hᑫ(X, 𝓕) = 0` for `q ≥ N`. -/
@[stacks 072C "the uniform vanishing degree, for every quasi-coherent module; the value \
max (d_p + p) of the degree is not part of this statement"]
theorem exists_forall_isZero_rightDerived_globalSectionsFunctor_of_isQuasiCompactSpace
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ N : ℕ, ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite → ∀ q, N ≤ q →
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived q).obj F) := by
  exact (exists_forall_isZero_rightDerived_globalSectionsAb_of_isQuasiCompactSpace B S hS hZ X hqc
    hqs).imp fun _ hN F hF q hq =>
      (isZero_rightDerived_globalSectionsAb_iff B S hS X F q).1 (hN F hF q hq)

/-- The cohomological dimension bound of Stacks 072C for coherent modules: on a quasi-compact
and quasi-separated algebraic space there is a single degree beyond which the cohomology of every
coherent module vanishes. -/
theorem exists_forall_isZero_rightDerived_globalSectionsFunctor_of_isCoherent
    (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1) :
    ∃ N : ℕ, ∀ F : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 F → ∀ q, N ≤ q →
      IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).rightDerived q).obj F) := by
  exact (exists_forall_isZero_rightDerived_globalSectionsFunctor_of_isQuasiCompactSpace B S hS hZ
    X hqc hqs).imp fun _ hN F hF => hN F hF.toIsQuasicoherentOnSite

end AlgebraicGeometry.Space

end
