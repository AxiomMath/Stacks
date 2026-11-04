module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Coherent.IdealSheafFiniteTypeBridge
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionProperty
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafResolution

/-!
# The resolution property and a finite affine covering cut out by ideals

The immediate half of [Stacks, Tag 0F89].  Let `X` be a scheme equipped with

1. a finite affine open covering `X = U 0 ∪ ⋯ ∪ U (m - 1)`, and
2. finite type quasi-coherent ideals `I j ⊆ 𝒪_X` with `V(I j) = X \ U j`.

Then `X` has the resolution property if and only if each `I j` is the quotient of a finite
locally free `𝒪_X`-module.  The direction proved here is that if `X` has the resolution property
then each `I j` is a quotient of a finite locally free module.

## Main definitions

* `AlgebraicGeometry.IsIdealAffineCovering`: hypotheses (1) and (2) of [Stacks, Tag 0F89].

## Main results

* `AlgebraicGeometry.isIdealAffineCovering_of_isLocallyNoetherian`: on a locally Noetherian
  scheme the finite type condition in those hypotheses is automatic.
* `AlgebraicGeometry.isIdealAffineCovering_of_isFiniteType`: the hypotheses hold as soon as each
  sheaf of ideals is of finite type in the sense of
  `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`.
* `AlgebraicGeometry.exists_isFiniteLocallyFree_epi_idealPow_of_isFiniteType`: on a scheme with
  the resolution property, a power of a quasi-coherent sheaf of ideals that is of finite type as
  a module is the quotient of a finite locally free module.
* `AlgebraicGeometry.exists_isFiniteLocallyFree_epi_of_isIdealAffineCovering`: under hypotheses
  (1) and (2) of [Stacks, Tag 0F89], if `X` has the resolution property then each `I j` is the
  quotient of a finite locally free module.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 0F86](https://stacks.math.columbia.edu/tag/0F86)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Hypotheses (1) and (2) of [Stacks, Tag 0F89] on a scheme `X`: the `U j` are a finite affine
open covering of `X`, and the `I j` are quasi-coherent sheaves of ideals, of finite type as
`𝒪_X`-modules, whose vanishing locus is the complement of `U j`. -/
structure IsIdealAffineCovering (X : Scheme.{u}) {m : ℕ} (U : Fin m → X.Opens)
    (I : Fin m → X.IdealSheafData) : Prop where
  /-- Each member of the covering is an affine open. -/
  isAffineOpen (j : Fin m) : IsAffineOpen (U j)
  /-- The `U j` cover `X`. -/
  iSup_eq_top : ⨆ j, U j = ⊤
  /-- Each sheaf of ideals is of finite type as an `𝒪_X`-module. -/
  isFiniteType (j : Fin m) : (idealPow (I j) 1).IsFiniteType
  /-- The vanishing locus of `I j` is the complement of `U j`. -/
  support_eq (j : Fin m) : ((I j).support : Set X) = ((U j : Set X))ᶜ

/-- On a locally Noetherian scheme the finite type condition of `IsIdealAffineCovering` is
automatic. -/
theorem isIdealAffineCovering_of_isLocallyNoetherian [IsLocallyNoetherian X] {m : ℕ}
    (U : Fin m → X.Opens) (I : Fin m → X.IdealSheafData) (hU : ∀ j, IsAffineOpen (U j))
    (hcover : ⨆ j, U j = ⊤) (hsupport : ∀ j, ((I j).support : Set X) = ((U j : Set X))ᶜ) :
    IsIdealAffineCovering X U I :=
  ⟨hU, hcover, fun j =>
    (@Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
      X (idealPow (I j) 1) (isCoherent_idealPow (I j) 1)).2, hsupport⟩

/-- The hypotheses of [Stacks, Tag 0F89] hold as soon as each sheaf of ideals is of finite type
in the sense of `AlgebraicGeometry.Scheme.IdealSheafData.IsFiniteType`, that is, as soon as every
`(I j).ideal V` is finitely generated. -/
theorem isIdealAffineCovering_of_isFiniteType {m : ℕ} (U : Fin m → X.Opens)
    (I : Fin m → X.IdealSheafData) (hU : ∀ j, IsAffineOpen (U j)) (hcover : ⨆ j, U j = ⊤)
    (hft : ∀ (j : Fin m) (V : X.affineOpens), ((I j).ideal V).FG)
    (hsupport : ∀ j, ((I j).support : Set X) = ((U j : Set X))ᶜ) :
    IsIdealAffineCovering X U I :=
  ⟨hU, hcover,
    fun j => Stacks.AlgebraicGeometry.FiniteTypeBridge.isFiniteType_idealPow (I j) 1 (hft j),
    hsupport⟩

/-- On a scheme with the resolution property, a power of a quasi-coherent sheaf of ideals that is
of finite type as a module is the quotient of a finite locally free module. -/
theorem exists_isFiniteLocallyFree_epi_idealPow_of_isFiniteType [HasResolutionProperty X]
    (I : X.IdealSheafData) (n : ℕ) (hI : (idealPow I n).IsFiniteType) :
    ∃ (E : X.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (q : E ⟶ idealPow I n), Epi q :=
  @HasResolutionProperty.exists_finiteLocallyFree_quotient X _ (idealPow I n) inferInstance hI

/-- Let `X` be a scheme with a finite affine open covering `U` and finite type quasi-coherent
sheaves of ideals `I j` whose vanishing loci are the complements of the `U j`.  If `X` has the
resolution property then each `I j` is the quotient of a finite locally free `𝒪_X`-module. -/
@[stacks 0F89 "the direction that is immediate: resolution property implies each ideal is a \
finite-locally-free quotient"]
theorem exists_isFiniteLocallyFree_epi_of_isIdealAffineCovering [HasResolutionProperty X] {m : ℕ}
    {U : Fin m → X.Opens} {I : Fin m → X.IdealSheafData} (h : IsIdealAffineCovering X U I)
    (j : Fin m) :
    ∃ (E : X.Modules)
      (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
      (q : E ⟶ idealPow (I j) 1), Epi q :=
  exists_isFiniteLocallyFree_epi_idealPow_of_isFiniteType (I j) 1 (h.isFiniteType j)

end AlgebraicGeometry

end
