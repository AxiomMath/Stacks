module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.FirstCohomologyTorsion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CohomologyUnconditional

/-!
# `RΓ(X, 𝒢)` on a normal modification of a surface

Let `A` be a Noetherian normal local domain of dimension two, `f : X ⟶ Spec(A)` a modification
with `X` normal, and `𝒢` a quasi-coherent `𝒪_X`-module. The object `RΓ(X, 𝒢)` of `D(A)` has its
cohomology in degrees `0` and `1` only, where it is `Hⁿ(X, 𝒢)` ([Stacks, Tag 0B4X], clause (1),
which is [Stacks, Tag 02V7] for fibres of dimension at most one).

## Main definitions

* `AlgebraicGeometry.DualizingDivisor.derivedSections`: `RΓ(X, 𝒢)` in `D(A)`.

## Main results

* `AlgebraicGeometry.DualizingDivisor.homologyDerivedSectionsIso`: `Hⁿ(RΓ(X, 𝒢)) ≅ Hⁿ(X, 𝒢)`.
* `AlgebraicGeometry.DualizingDivisor.isGE_derivedSections`,
  `AlgebraicGeometry.DualizingDivisor.isLE_derivedSections`: `RΓ(X, 𝒢)` lies in degrees `[0, 1]`.

## References

* [Stacks Project, Tag 0B4X](https://stacks.math.columbia.edu/tag/0B4X)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.DualizingDivisor

section General

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- `RΓ(X, 𝒢)` as an object of `D(A)`: the `A`-linear derived global sections of `𝒢` placed in
degree zero. -/
abbrev derivedSections (G : X.Modules) : DerivedCategory (ModuleCat.{u} A) :=
  (derivedGlobalSectionsOver f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj G)

/-- `Hⁿ(RΓ(X, 𝒢)) = Hⁿ(X, 𝒢)`, the `n`-th right derived functor of `A`-linear global sections. -/
def homologyDerivedSectionsIso (G : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)).obj (derivedSections f G) ≅
      ((globalSectionsOver f).rightDerived n).obj G :=
  (Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (globalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
    (Scheme.Modules.exists_quasiIso_isKInjective X) n).app G

/-- `RΓ(X, 𝒢)` has no cohomology in negative degrees. -/
instance isGE_derivedSections (G : X.Modules) : (derivedSections f G).IsGE 0 := by
  rw [DerivedCategory.isGE_iff]
  intro n hn
  exact Stacks.DerivedFunctor.isZero_homologyFunctor_obj_derived_single (globalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
    (Scheme.Modules.exists_quasiIso_isKInjective X) G n hn

end General

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]

/-- **`Hⁿ(X, 𝒢) = 0` for `n ≥ 2`** on a normal modification of a two-dimensional Noetherian normal
local domain, `𝒢` quasi-coherent ([Stacks, Tag 0B4X], clause (1)). -/
theorem isZero_rightDerived_globalSectionsOver_of_one_lt (hdim : ringKrullDim A = 2)
    {X : Scheme.{u}} [IsNormal X] (f : X ⟶ Spec (.of A)) (hf : IsModification f)
    (G : X.Modules) [G.IsQuasicoherent] (n : ℕ) (hn : 1 < n) :
    IsZero (((globalSectionsOver f).rightDerived n).obj G) := by
  let S : SemistableReduction.TwoModifications.{u} :=
    { situation := VanishingSituation.ofModification A hdim f hf
      X' := X
      g := 𝟙 X
      modification' := by
        show IsModification (𝟙 X ≫ f)
        rw [Category.id_comp]
        exact hf
      normal := inferInstanceAs (IsNormal X) }
  have h₀ : IsZero (((moduleGlobalSections X).rightDerived n).obj G) :=
    rightDerived_of_rightDerivedPlus (moduleGlobalSections X) n G IsZero
      (fun e h => h.of_iso e.symm)
      (@SemistableReduction.TwoModifications.isZero_cohomology_one_lt S G ‹_› n (by omega))
  exact ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map_isZero
    h₀).of_iso ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (moduleGlobalSections X)
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom)
      (globalSectionsOver f) (Iso.refl _) n).app G).symm

/-- `RΓ(X, 𝒢)` has no cohomology above degree one, for `𝒢` quasi-coherent on a normal modification
of a two-dimensional Noetherian normal local domain. -/
theorem isLE_derivedSections (hdim : ringKrullDim A = 2) {X : Scheme.{u}} [IsNormal X]
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) (G : X.Modules) [G.IsQuasicoherent] :
    (derivedSections f G).IsLE 1 := by
  rw [DerivedCategory.isLE_iff]
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) := ⟨n.toNat, by omega⟩
  exact (isZero_rightDerived_globalSectionsOver_of_one_lt hdim f hf G m (by omega)).of_iso
    (homologyDerivedSectionsIso f G m)

end AlgebraicGeometry.DualizingDivisor

end
