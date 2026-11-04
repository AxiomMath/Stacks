module

public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalNonzerodivisor
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.FiniteLocallyFreeComplementAffine
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence

/-!
# Finiteness of `H^p(U, F)` as an `A`-module

Fix an algebraization situation `S`: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine
scheme `X = Spec(A)` and the open complement `U = X ∖ V(𝔞)`, with inclusion `j : U → X`.
`Stacks.Algebraization.openCohomologyFunctor` derives the global sections of `𝒪_U`-modules on the
open subscheme `U` and restricts scalars along `Stacks.Algebraization.scalarMap`, the map
`A → Γ(U, 𝒪_U)`; `Stacks.LocalCohomologySequence.complementCohomologyBase` takes the derived
sections over the open `U` of sheaves of modules on `X`, restricted along the ring isomorphism
`A ≅ Γ(X, 𝒪_X)`. This file relates finiteness of the two as `A`-modules, through coherence of the
higher direct image `R^p j_* F` on `X`.

## Main results

* `Stacks.Algebraization.finite_openCohomology_iff_isCoherent` — `H^p(U, F)` is a finite
  `A`-module exactly when `R^p j_* F` is coherent.
* `Stacks.Algebraization.finite_openCohomology_of_finite_complementCohomologyBase` — for an `F`
  presented as a restriction `M̃|_U`, finiteness of `H^p(U, M̃)` as given by
  `complementCohomologyBase` gives finiteness of `H^p(U, F)` as given by `openCohomologyFunctor`.
* `Stacks.Algebraization.finite_globalSectionsSystem_zero_of_finite_openCohomology` — finiteness
  of `H^0(U, F_1)` gives finiteness of the first term of
  `Stacks.Algebraization.globalSectionsSystem`.

## References

* [Stacks Project, Tag 0DXW](https://stacks.math.columbia.edu/tag/0DXW)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.AffineBase
open Stacks.Cohomology.SchemeOpenSections
open Stacks.LocalCohomologyTilde
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-- For a quasi-coherent `𝒪_U`-module `F` the `A`-module `H^p(U, F)` is finite exactly when the
higher direct image `R^p j_* F` is a coherent `𝒪_X`-module. -/
theorem finite_openCohomology_iff_isCoherent (S : AlgebraizationSituation.{u})
    (F : S.U.toScheme.Modules) [F.IsQuasicoherent] (p : ℕ) :
    Module.Finite S.A ((openCohomologyFunctor S p).obj F) ↔
      (((AlgebraicGeometry.Scheme.Modules.pushforward S.U.ι).rightDerived p).obj
        F).IsCoherent := by
  have key : Module.Finite S.A ((openCohomologyFunctor S p).obj F) ↔
      Module.Finite Γ(S.X, ⊤) ((ModuleCat.restrictScalars S.U.ι.appTop.hom).obj
        (((moduleGlobalSections S.U.toScheme).rightDerived p).obj F)) :=
    Module.finite_restrictScalars_ringEquiv_iff (baseRingEquiv (CommRingCat.of S.A))
      ((ModuleCat.restrictScalars S.U.ι.appTop.hom).obj
        (((moduleGlobalSections S.U.toScheme).rightDerived p).obj F))
  exact key.trans
    (Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_cohomology_iff_isCoherent
      S.U.ι F p)

/-- Let `F` be a quasi-coherent `𝒪_U`-module presented as the restriction `M̃|_U` of the sheaf
attached to an `A`-module `M`. If `H^p(U, M̃)` is a finite `A`-module as given by
`Stacks.LocalCohomologySequence.complementCohomologyBase`, then `H^p(U, F)` is a finite
`A`-module as given by `openCohomologyFunctor`. -/
theorem finite_openCohomology_of_finite_complementCohomologyBase (S : AlgebraizationSituation.{u})
    (F : S.U.toScheme.Modules) [F.IsQuasicoherent] (M : ModuleCat.{u} (CommRingCat.of S.A))
    (e : (AlgebraicGeometry.tilde M).restrict S.U.ι ≅ F) (p : ℕ)
    (h : Module.Finite S.A
      (Stacks.LocalCohomologySequence.complementCohomologyBase (A := CommRingCat.of S.A)
        S.a M p)) :
    Module.Finite S.A ((openCohomologyFunctor S p).obj F) := by
  have : (((AlgebraicGeometry.Scheme.Modules.pushforward S.U.ι).rightDerived p).obj
      ((AlgebraicGeometry.tilde M).restrict S.U.ι)).IsCoherent :=
    (Stacks.LocalCohomologySequence.moduleFinite_complementCohomologyBase_iff_isCoherent
      (A := CommRingCat.of S.A) S.a M p).mp h
  exact (finite_openCohomology_iff_isCoherent S F p).mpr
    (Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso
      (((AlgebraicGeometry.Scheme.Modules.pushforward S.U.ι).rightDerived p).mapIso e.symm))

/-- If the `A`-module `H^0(U, F_1)`, computed as the zeroth right derived functor of sections, is
finite, then so is the first term of the inverse system
`Stacks.Algebraization.globalSectionsSystem`. -/
theorem finite_globalSectionsSystem_zero_of_finite_openCohomology (S : AlgebraizationSituation.{u})
    (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))
    (h : Module.Finite S.A ((openCohomologyFunctor S 0).obj (systemObj S F 0))) :
    Module.Finite S.A ((globalSectionsSystem S F).obj (Opposite.op 0)) :=
  (Module.finite_iff_of_moduleCat_iso
    ((ModuleCat.restrictScalars (scalarMap S)).mapIso
      ((_root_.SheafOfModules.evaluation S.U.toScheme.ringCatSheaf
        (op (⊤ : S.U.toScheme.Opens))).rightDerivedZeroIsoSelf.app
          (systemObj S F 0)))).mp h

end Stacks.Algebraization

end
