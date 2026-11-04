module

public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeFormsDerivedComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.FormsDerivedComparisonHomology
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedPushforwardAffineBaseHomology
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateBlowupFormsGlobalSections
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic

/-!
# Clause (3) of Stacks 0FUR reduced to a vanishing on the projective bundle

In the standard situation of Section 50.16 of the source — `A = R[x₁, …, x_m, y₁, …, y_n]`
graded by `deg yⱼ = 1`, `X = Spec A`, the projective bundle `P = Proj(A)` and the cone
`L = Proj(⨁_d A_{≥ d})` with projection `π : L ⟶ P`, zero section `0 : P ⟶ L` and structure
morphism `b : L ⟶ X` — clause (3) of [Stacks, Tag 0FUR] asserts that the comparison
`Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}` of
`Stacks.DeRham.CoordinateCone.coneFormsDerivedComparison` is an isomorphism on cohomology sheaves
in degrees `≥ 1`. This file reduces that to a statement on `P`, following the first steps of the
source's proof.

* The comparison is `Rb_*` of the restriction of forms `r : Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}` followed by
  isomorphisms (`0` is a closed immersion), so it suffices that `H^q(Rb_*(r[0]))` is invertible.
* `X` is affine and `b` is quasi-compact and quasi-separated, so that holds once
  `H^q(L, r) : H^q(L, Ω^a_{L/S}) ⟶ H^q(L, 0_*Ω^a_{P/S})` is invertible
  (`Stacks.Cohomology.AffineBase.isIso_homology_derivedPushforward_map_single_of_isIso`).
* `π` is affine, so `H^q(L, r)` is `H^q(P, π_*r)` ([Stacks, Tag 089W]).
* `π_*r` is an epimorphism; if its kernel `K` has no cohomology in positive degrees, the long
  exact cohomology sequence makes `H^q(P, π_*r)` invertible for `q ≥ 1`.

## Main results

* `Stacks.DeRham.CoordinateCone.isIso_homology_coneFormsDerivedComparison_of_isIso`: the
  comparison is invertible on `H^q` as soon as `H^q(L, r)` is.
* `Stacks.DeRham.CoordinateCone.isIso_rightDerived_coneFormsRestriction_iff`:
  `H^q(L, r)` is invertible exactly when `H^q(P, π_*r)` is.
* `Stacks.DeRham.CoordinateCone.isIso_homology_coneFormsDerivedComparison_of_vanishing`: the
  comparison is invertible on `H^q` for every `q ≥ 1` once `π_*r` is an epimorphism whose kernel
  has vanishing cohomology in positive degrees.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.CoordinateCone

variable (R : Type u) [CommRing R] (m n : ℕ)

open Stacks.AlgebraicGeometry.ProjAndSpec
open Stacks.AlgebraicGeometry.ProjAndSpecTruncation (truncationConeData)

/-- The cone projection `π : L ⟶ P`. -/
abbrev coneProjection := pi (truncationConeData (yGrading R m n))

/-- The zero section `0 : P ⟶ L`. -/
abbrev coneZeroSection := zeroSection (truncationConeData (yGrading R m n))

/-- The cone projection `π : L ⟶ P` is affine. -/
instance isAffineHom_coneProjection : IsAffineHom (coneProjection R m n) :=
  isAffineHom_pi _

/-- The zero section `0 : P ⟶ L` is a closed immersion. -/
instance isClosedImmersion_coneZeroSection : IsClosedImmersion (coneZeroSection R m n) :=
  isClosedImmersion_zeroSection _

/-- The structure morphism `b : L ⟶ X` is quasi-compact: it is the blowing-up morphism of the
standard coordinate blowup, up to the isomorphism `coneBlowupIso`. -/
instance quasiCompact_coneToAmbient : QuasiCompact (coneToAmbient R m n) := by
  change QuasiCompact (toSpecA (truncationConeData (yGrading R m n)))
  rw [← coneBlowupIso_hom_comp]; infer_instance

/-- The structure morphism `b : L ⟶ X` is quasi-separated, being separated. -/
instance quasiSeparated_coneToAmbient : QuasiSeparated (coneToAmbient R m n) := by
  change QuasiSeparated (toSpecA (truncationConeData (yGrading R m n)))
  rw [← coneBlowupIso_hom_comp]; infer_instance

/-- `Ω^a_{L/S}` is quasi-coherent. -/
instance isQuasicoherent_coneForms (a : ℕ) :
    (Scheme.Hom.relativeDifferentialForms (coneToBase R m n) (a : ℤ)).IsQuasicoherent :=
  Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a

/-- `0_*Ω^a_{P/S}` is quasi-coherent. -/
instance isQuasicoherent_coneZeroSectionForms (a : ℕ) :
    ((Scheme.Modules.pushforward (coneZeroSection R m n)).obj
      (Scheme.Hom.relativeDifferentialForms (coneBundleToBase R m n) (a : ℤ))).IsQuasicoherent :=
  AlgebraicGeometry.ProperCoherentFiniteType.isQuasicoherent_pushforward _ _
    (Scheme.Hom.isQuasicoherent_relativeDifferentialForms _ a)

section Derived

variable
  [HasDerivedCategory (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneTotal R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneCentre R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneBundle R m n).toRingedSpace)]

/-- The comparison `Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}` is `formsDerivedComparisonOf` applied to
the restriction of forms `r : Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}`. -/
theorem coneFormsDerivedComparison_eq (a : ℤ) :
    coneFormsDerivedComparison R m n a =
      Stacks.DeRham.formsDerivedComparisonOf (coneToAmbient R m n) (coneZeroSection R m n)
        (coneBundleToCentre R m n) (coneCentreToAmbient R m n) (zeroSection_toShHom_comp R m n)
        (Scheme.Hom.relativeDifferentialForms (coneBundleToBase R m n) a)
        (coneFormsRestriction R m n a) :=
  rfl

/-- **The comparison of clause (3) is invertible on `H^q` as soon as `H^q(L, r)` is**, where
`r : Ω^a_{L/S} ⟶ 0_*Ω^a_{P/S}` is the restriction of forms to the zero section. -/
theorem isIso_homology_coneFormsDerivedComparison_of_isIso (a : ℕ) (q : ℕ)
    (h : IsIso (((Stacks.Cohomology.sectionsFunctor _ ⊤).rightDerived q).map
      (coneFormsRestriction R m n (a : ℤ)))) :
    IsIso ((DerivedCategory.homologyFunctor _ (q : ℤ)).map
      (coneFormsDerivedComparison R m n (a : ℤ))) := by
  have := Stacks.DeRham.isIso_homology_formsDerivedComparisonOf_of_isIso_rightDerived
    (coneToAmbient R m n) (coneZeroSection R m n) (coneBundleToCentre R m n)
    (coneCentreToAmbient R m n) (zeroSection_toShHom_comp R m n)
    (Scheme.Hom.relativeDifferentialForms (coneBundleToBase R m n) (a : ℤ))
    (coneFormsRestriction R m n (a : ℤ)) q h
  rw [coneFormsDerivedComparison_eq]
  exact this

end Derived

/-- **`H^q(L, r)` is `H^q(P, π_*r)`**: the cone projection is affine, so cohomology on `L` of
quasi-coherent modules is cohomology on `P` of their direct images ([Stacks, Tag 089W]). -/
theorem isIso_rightDerived_coneFormsRestriction_iff (a : ℕ) (q : ℕ) :
    IsIso (((Stacks.Cohomology.sectionsFunctor _ ⊤).rightDerived q).map
        (coneFormsRestriction R m n (a : ℤ))) ↔
      IsIso (((Stacks.Cohomology.sectionsFunctor (coneBundle R m n) ⊤).rightDerived q).map
        ((Scheme.Modules.pushforward (coneProjection R m n)).map
          (coneFormsRestriction R m n (a : ℤ)))) :=
  Stacks.Cohomology.AffineBase.isIso_rightDerived_sections_map_iff_of_isAffineHom
    (coneProjection R m n) _ q

section Derived

variable
  [HasDerivedCategory (ModuleSheaves (Stacks.DeRham.coordinateAmbient R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneTotal R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneCentre R m n).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (coneBundle R m n).toRingedSpace)]

/-- **Clause (3) of [Stacks, Tag 0FUR] from a vanishing on `P`.** If `π_*r` is an epimorphism and
its kernel has no cohomology on `P` in positive degrees, the comparison
`Rb_*Ω^a_{L/S} ⟶ i_*Rp_*Ω^a_{P/S}` is an isomorphism on cohomology sheaves in every degree
`q ≥ 1`. -/
theorem isIso_homology_coneFormsDerivedComparison_of_vanishing (a : ℕ)
    [Epi ((Scheme.Modules.pushforward (coneProjection R m n)).map
      (coneFormsRestriction R m n (a : ℤ)))]
    (hK : ∀ p : ℕ, 1 ≤ p →
      IsZero (((Stacks.Cohomology.sectionsFunctor (coneBundle R m n) ⊤).rightDerived p).obj
        (kernel ((Scheme.Modules.pushforward (coneProjection R m n)).map
          (coneFormsRestriction R m n (a : ℤ))))))
    (q : ℕ) (hq : 1 ≤ q) :
    IsIso ((DerivedCategory.homologyFunctor _ (q : ℤ)).map
      (coneFormsDerivedComparison R m n (a : ℤ))) :=
  isIso_homology_coneFormsDerivedComparison_of_isIso R m n a q
    ((isIso_rightDerived_coneFormsRestriction_iff R m n a q).2
      (Stacks.Cohomology.AffineBase.isIso_rightDerived_sections_map_of_epi _ q
        (hK q hq) (hK (q + 1) (by omega))))

end Derived

end Stacks.DeRham.CoordinateCone

end
