module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaPullbackGlobal

/-!
# The canonical comparison `Lh^*(Lη_I M) ⟶ Lη_J(Lh^* M)` for an arbitrary morphism

Let `h : Y ⟶ X` be a morphism of schemes and `D ⊆ X` an effective Cartier divisor whose pullback
`E = h^{-1}D` is defined, with ideal sheaves `I = ℐ_D` and `J = ℐ_E`.  For an object `M = [P^•]`
of `D(𝒪_X)` presented by a K-flat complex `P^•` of flat `𝒪_X`-modules — every object has such a
presentation (Stacks 06YF) — this file builds the canonical comparison

`Lh^*(Lη_I M) ⟶ Lη_J(Lh^* M)`

in `D(𝒪_Y)`, with no hypothesis on `h`: `Lη_I M` is the class of the chain-level décalage
`η_I P^•` (the terms of `P^•` are flat, hence `I`-torsion free); the comparison of Stacks 06YJ
maps `Lh^*[η_I P^•]` to `[h^*(η_I P^•)]`; the chain-level comparison maps this to
`[η_J(h^* P^•)]` (the terms of `h^* P^•` are flat, hence `J`-torsion free), which is
`Lη_J [h^* P^•]`; and `[h^* P^•]` is `Lh^* M` because `P^•` is K-flat.

It then records that the comparison is an isomorphism exactly when the derived comparison
`Stacks.Divisors.Eta.divisorPullbackEtaKFlatComparison` is.

## Main definitions

* `Stacks.Divisors.Eta.derivedEtaPullbackComparisonOfFlat`: the canonical comparison.

## Main results

* `Stacks.Divisors.Eta.isIso_derivedEtaPullbackComparisonOfFlat_iff`.
* `Stacks.Divisors.Eta.exists_kFlat_flat_iso`: every object of `D(𝒪_X)` has a presentation by a
  K-flat complex of flat modules.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open Stacks.RingedSpace (pullbackFunctor)
open Stacks.IdealTorsion.Eta (etaObj pullbackComplex pullbackComplexMap pullbackIdealIncl)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace Stacks.Divisors.Eta

attribute [local instance] Stacks.Divisors.Eta.etaHasDerivedCategory

/-- Composing with isomorphisms on both sides does not change being an isomorphism. -/
theorem isIso_comp_comp_comp_iff {C : Type*} [Category C] {A B B' C' D' : C} (a : A ⟶ B)
    (t : B ⟶ B') (b : B' ⟶ C') (c : C' ⟶ D') (ha : IsIso a) (hb : IsIso b) (hc : IsIso c) :
    IsIso (a ≫ t ≫ b ≫ c) ↔ IsIso t := by
  rw [isIso_comp_left_iff, ← Category.assoc, isIso_comp_right_iff, isIso_comp_right_iff]

/-- **Every object of `D(𝒪_Z)` is presented by a K-flat complex of flat modules** (Stacks 06YF):
a K-flat resolution by flat modules of any complex representing it. -/
theorem exists_kFlat_flat_iso (Z : RingedSpace.{u})
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf))) :
    ∃ (P : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.sheaf)) ℤ)
      (_ : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Z.sheaf) (P.X n))
      (_ : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z P),
      Nonempty (DerivedCategory.Q.obj P ≅ M) := by
  obtain ⟨P, p, hPk, hPflat, hp, -⟩ :=
    AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.exists_kFlatResolution Z
      (DerivedCategory.Q.objPreimage M)
  exact ⟨P, hPflat, hPk,
    ⟨asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso M⟩⟩

variable {Y X : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)
  [Stacks.Divisors.IsEffectiveCartierDivisor D] [hD : Stacks.Divisors.IsPullbackDefined h D]
  (P : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSpace.sheaf)) ℤ)
  (hP : ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
    (O := X.toRingedSpace.sheaf) (P.X n))
  (hPk : Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toRingedSpace P)

include hP hPk

/-- **The canonical comparison `Lh^*(Lη_I M) ⟶ Lη_J(Lh^* M)`** at an object `M = [P^•]`
presented by a K-flat complex of flat modules, where `Lη_I` and `Lη_J` are the derived
décalages of Stacks 0F8Q (`Stacks.Divisors.Eta.derivedEtaData`) for the ideal sheaves of `D` and
of `h^{-1}D`, and `Lh^*` is the left derived pullback.

It is the composite of: `Lh^*` of the identification `Lη_I[P^•] ≅ [η_I P^•]`; the comparison
`Stacks.Divisors.Eta.divisorPullbackEtaKFlatComparison`, which is the comparison of Stacks 06YJ
followed by the class of the chain-level comparison of décalages; the identification
`[η_J(h^* P^•)] ≅ Lη_J[h^* P^•]`; and `Lη_J` of the inverse of the comparison
`Lh^*[P^•] ≅ [h^* P^•]` of Stacks 06YJ, invertible because `P^•` is K-flat. -/
def derivedEtaPullbackComparisonOfFlat :
    (Stacks.IdealTorsion.Eta.etaDerivedPullback h.toLRSHom.toShHom).obj
        ((@Stacks.IdealTorsion.Eta.derivedEta X.toRingedSpace (idealSheaf D) (idealSheafι D)
            (mono_idealSheafι D) (isInvertible_idealSheaf D) (hasTorsionFreeResolutions D)).obj
          (DerivedCategory.Q.obj P)) ⟶
      (@Stacks.IdealTorsion.Eta.derivedEta Y.toRingedSpace (idealSheaf (D.comap h))
          (idealSheafι (D.comap h)) (mono_idealSheafι (D.comap h))
          (isInvertible_idealSheaf (D.comap h)) (hasTorsionFreeResolutions (D.comap h))).obj
        ((Stacks.IdealTorsion.Eta.etaDerivedPullback h.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj P)) :=
  (Stacks.IdealTorsion.Eta.etaDerivedPullback h.toLRSHom.toShHom).map
      ((@Stacks.IdealTorsion.Eta.derivedEta_iso X.toRingedSpace (idealSheaf D) (idealSheafι D)
        (mono_idealSheafι D) (isInvertible_idealSheaf D) (hasTorsionFreeResolutions D)).app
        (HomologicalComplex.liftObjectProperty
          (Stacks.IdealTorsion.Eta.torsionFreeProperty X.toRingedSpace (idealSheafι D)) P
          (isIdealTorsionFree_X D P hP))).hom ≫
    divisorPullbackEtaKFlatComparison h D P hP ≫
    ((@Stacks.IdealTorsion.Eta.derivedEta_iso Y.toRingedSpace (idealSheaf (D.comap h))
        (idealSheafι (D.comap h)) (mono_idealSheafι (D.comap h))
        (isInvertible_idealSheaf (D.comap h)) (hasTorsionFreeResolutions (D.comap h))).app
      (HomologicalComplex.liftObjectProperty
        (Stacks.IdealTorsion.Eta.torsionFreeProperty Y.toRingedSpace (idealSheafι (D.comap h)))
        (pullbackComplex h.toLRSHom.toShHom P)
        (isIdealTorsionFree_pullbackComplex_X h D P hP))).inv ≫
    (@Stacks.IdealTorsion.Eta.derivedEta Y.toRingedSpace (idealSheaf (D.comap h))
        (idealSheafι (D.comap h)) (mono_idealSheafι (D.comap h))
        (isInvertible_idealSheaf (D.comap h)) (hasTorsionFreeResolutions (D.comap h))).map
      (@inv _ _ _ _ (Stacks.IdealTorsion.Eta.etaPullbackComparisonOnComplex h.toLRSHom.toShHom P)
        (Stacks.IdealTorsion.Eta.isIso_etaPullbackComparisonOnComplex h.toLRSHom.toShHom P hPk))

/-- The canonical comparison is an isomorphism exactly when the derived comparison of décalages
is: the other three constituents are isomorphisms. -/
theorem isIso_derivedEtaPullbackComparisonOfFlat_iff :
    IsIso (derivedEtaPullbackComparisonOfFlat h D P hP hPk) ↔
      IsIso (divisorPullbackEtaKFlatComparison h D P hP) :=
  isIso_comp_comp_comp_iff _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ _ _ (Iso.isIso_hom _)) (Iso.isIso_inv _)
    (@Functor.map_isIso _ _ _ _ _ _ _ _ (@IsIso.inv_isIso _ _ _ _ _
      (Stacks.IdealTorsion.Eta.isIso_etaPullbackComparisonOnComplex h.toLRSHom.toShHom P hPk)))

end Stacks.Divisors.Eta

end
