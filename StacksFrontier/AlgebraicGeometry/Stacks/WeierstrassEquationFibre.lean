module

public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroSections
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassCubicFromSectionsRelation

/-!
# The sections `zx, y, z³` on the fibre of a pointed family

Let `E` be a separated pointed family over `Spec B`, smooth of relative dimension one, with zero
section `z` of `O(0)`, and let `x`, `y` be global sections of `O(2·0)` and `O(3·0)` such that the
sections `zx, y, z³` of `O(3·0)` satisfy the cubic of a Weierstrass curve `C` and have no common
zero. At a point `p` of `Spec B`, the restrictions of `x` and `y` to the fibre `E_p` give the
sections `zx, y, z³` of `O(3·0)` on `E_p`; they are the pullbacks of the sections on `E`, read
through the identification of the pullback of `O(0)^{⊗3}` with `O(0)^{⊗3}` of the fibre. So they
satisfy the cubic of `C` over `κ(p)` and have no common zero, and the morphism of `E_p` to the
plane cubic they define is the morphism given by the pulled-back sections.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.satisfiesCubic_fibre`: the sections on the
  fibre satisfy the cubic of `C` over the residue field.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isOpenCover_fibre`: the sections on the
  fibre have no common zero.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.isIso_of_isIso_fibre`: the morphism of the
  pulled-back sections is an isomorphism when the morphism of the sections of the fibre is one.

## References

* [Stacks, Tag 072T](https://stacks.math.columbia.edu/tag/072T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.TensorPowers (natTensorPow)
open Stacks.ProjectiveFromSections
open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections)

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

variable {S T : Scheme.{u}} (E : PointedFamily S) [IsSeparated E.map]
  [SmoothOfRelativeDimension 1 E.map]

/-- `O(0)` of a pulled-back family is invertible. -/
instance isInvertibleModule_pullback_zeroSheaf (g : T ⟶ S) :
    Stacks.Ample.IsInvertibleModule (E.pullback g).total (E.pullback g).zeroSheaf :=
  isInvertibleModule_zeroSheaf (E.pullback g)

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

namespace AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

variable {B : Type u} [CommRing B] (E : PointedFamily (Spec (.of B))) [IsSeparated E.map]
  [SmoothOfRelativeDimension 1 E.map] (C : WeierstrassCurve B)
  (x : Γ(natTensorPow E.zeroSheaf 2, ⊤)) (y : Γ(natTensorPow E.zeroSheaf 3, ⊤))
  (p : Spec (.of B))

/-- The sections `zx, y, z³` restricted to the fibre at `p` are the sections `zx, y, z³` of the
fibre, built from the restrictions of `x` and `y`. -/
theorem weierstrassSections_fibre (k : Fin 3) :
    weierstrassSections (E.pullback ((Spec (.of B)).fromSpecResidueField p)).zeroSheaf
        (E.pullback ((Spec (.of B)).fromSpecResidueField p)).zeroSection
        (E.restrictSection ((Spec (.of B)).fromSpecResidueField p) 2 x)
        (E.restrictSection ((Spec (.of B)).fromSpecResidueField p) 3 y) k =
      ((pullbackNatTensorPowIso (Limits.pullback.fst E.map
          ((Spec (.of B)).fromSpecResidueField p)) E.zeroSheaf 3).symm ≪≫
        natTensorPowCongr (E.zeroSheafPullbackIso ((Spec (.of B)).fromSpecResidueField p))
          3).hom.app ⊤ (pullbackFamily (weierstrassSections E.zeroSheaf E.zeroSection x y)
          (Limits.pullback.fst E.map ((Spec (.of B)).fromSpecResidueField p)) k) := by
  have hres (n : ℕ) (t : Γ(natTensorPow E.zeroSheaf n, ⊤)) :
      E.restrictSection ((Spec (.of B)).fromSpecResidueField p) n t =
        ((pullbackNatTensorPowIso (Limits.pullback.fst E.map
            ((Spec (.of B)).fromSpecResidueField p)) E.zeroSheaf n).symm ≪≫
          natTensorPowCongr (E.zeroSheafPullbackIso ((Spec (.of B)).fromSpecResidueField p))
            n).hom.app ⊤
          (pullbackGlobalSections (Limits.pullback.fst E.map
            ((Spec (.of B)).fromSpecResidueField p)) (natTensorPow E.zeroSheaf n) t) :=
    rfl
  rw [← hres]
  fin_cases k
  · change mulSections _ _ _ = E.restrictSection _ (1 + 2) (mulSections _ _ _)
    rw [E.restrictSection_mulSections, E.restrictSection_zeroSection]
  · rfl
  · change PointedFamily.cube _ _ = E.restrictSection _ 3 (PointedFamily.cube _ _)
    rw [E.restrictSection_cube, E.restrictSection_zeroSection]

variable {E C x y}

/-- **The sections on the fibre satisfy the cubic of the fibre.** -/
theorem satisfiesCubic_fibre
    (hrel : SatisfiesCubic C E.map (weierstrassSections E.zeroSheaf E.zeroSection x y)) :
    SatisfiesCubic (C.map (residueMapOf p)) (E.pullback ((Spec (.of B)).fromSpecResidueField p)).map
      (weierstrassSections (E.pullback ((Spec (.of B)).fromSpecResidueField p)).zeroSheaf
        (E.pullback ((Spec (.of B)).fromSpecResidueField p)).zeroSection
        (E.restrictSection ((Spec (.of B)).fromSpecResidueField p) 2 x)
        (E.restrictSection ((Spec (.of B)).fromSpecResidueField p) 3 y)) :=
  satisfiesCubic_iso _ (weierstrassSections_fibre E x y p)
    (satisfiesCubic_map (residueMapOf p) (Limits.pullback.snd E.map
        ((Spec (.of B)).fromSpecResidueField p))
      ((SpecMap_residueMapOf p) ▸ Limits.pullback.condition.symm)
      (satisfiesCubic_pullbackFamily (g := Limits.pullback.fst E.map
        ((Spec (.of B)).fromSpecResidueField p)) hrel))

/-- **The sections on the fibre have no common zero.** -/
theorem isOpenCover_fibre
    (hcov : TopologicalSpace.IsOpenCover
      (nvCover (weierstrassSections E.zeroSheaf E.zeroSection x y))) :
    TopologicalSpace.IsOpenCover
      (nvCover (weierstrassSections (E.pullback ((Spec (.of B)).fromSpecResidueField p)).zeroSheaf
        (E.pullback ((Spec (.of B)).fromSpecResidueField p)).zeroSection
        (E.restrictSection ((Spec (.of B)).fromSpecResidueField p) 2 x)
        (E.restrictSection ((Spec (.of B)).fromSpecResidueField p) 3 y))) :=
  isOpenCover_iso _ (weierstrassSections_fibre E x y p)
    (isOpenCover_pullbackFamily (g := Limits.pullback.fst E.map
      ((Spec (.of B)).fromSpecResidueField p)) hcov)

/-- **The morphism of the pulled-back sections is an isomorphism when the morphism of the
sections of the fibre is one.** -/
theorem isIso_of_isIso_fibre
    (hrel : SatisfiesCubic C E.map (weierstrassSections E.zeroSheaf E.zeroSection x y))
    (hcov : TopologicalSpace.IsOpenCover
      (nvCover (weierstrassSections E.zeroSheaf E.zeroSection x y)))
    (h : IsIso (cubicHomOfSections (satisfiesCubic_fibre p hrel) (isOpenCover_fibre p hcov))) :
    IsIso (cubicHomOfSections
      (satisfiesCubic_map (residueMapOf p) (Limits.pullback.snd E.map
          ((Spec (.of B)).fromSpecResidueField p))
        ((SpecMap_residueMapOf p) ▸ Limits.pullback.condition.symm)
        (satisfiesCubic_pullbackFamily (g := Limits.pullback.fst E.map
          ((Spec (.of B)).fromSpecResidueField p)) hrel))
      (isOpenCover_pullbackFamily (g := Limits.pullback.fst E.map
        ((Spec (.of B)).fromSpecResidueField p)) hcov)) := by
  rwa [← cubicHomOfSections_iso _ (weierstrassSections_fibre E x y p)]

end AlgebraicGeometry.ModuliEllipticCurves.Weierstrass

end
