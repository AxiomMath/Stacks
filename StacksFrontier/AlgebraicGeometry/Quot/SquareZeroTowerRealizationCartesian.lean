module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatEffectiveSystem
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerRealizationHom
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerSolutionConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.Deformations.CartesianOfFlatRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealizationOfCharts

/-!
# The squares `Xₙ ⟶ X'` over `Yₙ ⟶ Y` of a realized solution of the tower problem are cartesian

In the proof of [Stacks Project, Tag 0D3X], let `X₀ ⊂ X'` be a realization over
`Y = Spec(lim Rₙ)` of a solution of the tower problem and `gₙ : Xₙ ⟶ X'` the morphisms of
`AlgebraicGeometry.ProperFlatFibre.exists_towerRealizationHom_compatible`. Once `X₀ ⊂ X'` is
known to be the base change of `X'` along `Y₀ ⊂ Y` (the cartesian clause of Stacks 06BH, from
the invertibility of the conormal map `f^*𝒞_{Y₀/Y} ⟶ 𝒞_{X₀/X'}`), every square

```
Xₙ --gₙ--> X'
|          |
Yₙ ------> Y
```

is cartesian: `Xₙ` is the base change of `X'` along `Yₙ ⟶ Y` for every `n`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.isPullback_towerRealizationHom`: the squares are cartesian.
* `AlgebraicGeometry.ProperFlatFibre.exists_towerRealizationHom_isPullback_compatible`: the
  morphisms `Xₙ ⟶ X'`, cartesian over `Yₙ ⟶ Y` and compatible with the transitions.
* `AlgebraicGeometry.ProperFlatFibre.isEffectiveSystem_of_isIso_towerRealizationConormalMap`:
  the system is effective once the conormal map of `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` is invertible.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

universe u

namespace AlgebraicGeometry.ProperFlatFibre

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (ξ : ℕ ⥤ CartesianProperFlatSpaces B S hS)
  {Λ : Type u} [CommRing Λ] {R : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ}
  (hsurj : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), Function.Surjective (R.map f).hom)
  (hsq : ∀ {i j : ℕᵒᵖ} (f : i ⟶ j), RingHom.ker (R.map f).hom.toRingHom ^ 2 = ⊥)
  (e : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).obj (towerBase ξ n) ≅
    Spec (.of (R.obj (.op n))))
  (he : ∀ {i j : ℕ} (f : i ⟶ j),
    (BigFppfOver.toScheme B S hS).map ((ξ ⋙ cartesianProperFlatProjection B S hS).map f) ≫
      (e j).hom = (e i).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (R.map f.op).hom.toRingHom).op)
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)
  {P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening}
  (Rz : Space.EtaleSquareZeroExtension.Realization
    (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P'))

include he in
/-- **The square `Xₙ ⟶ X'` over `Yₙ ⟶ Y` is cartesian**, for any `g : Xₙ ⟶ X'` over `Y` with
`aₙ ≫ g = i`, once `X₀ ⊂ X'` is the base change of `X'` along `Y₀ ⊂ Y`. -/
theorem isPullback_towerRealizationHom
    (hcart : IsPullback (Space.subspaceInclusion B S hS Rz.ambient Rz.closedSubspace)
      (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc Rz) Rz.toBase
      (Space.subspaceInclusion B S hS (schemeSpace c.pt)
        (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc)))
    (n : ℕ) (g : towerSpace ξ n ⟶ Rz.ambient) (hg₁ : towerInclusion ξ n ≫ g = Rz.immersion)
    (hg₂ : g ≫ Rz.toBase = towerLimitStructureMap ξ c n) :
    IsPullback (towerStructureMap ξ n).hom g.hom (yoneda.map (c.ι.app n)) Rz.toBase.hom := by
  have hj := isClosedImmersion_towerBase_map ξ hsurj hsq e he (homOfLE (Nat.zero_le n))
  have hj₀ := (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
  have hcj : (ξ ⋙ cartesianProperFlatProjection B S hS).map (homOfLE (Nat.zero_le n)) ≫
      c.ι.app n = c.ι.app 0 := (c.ι.naturality _).trans (Category.comp_id _)
  have h₀ := AlgebraicSpaces.isPullback_hom B S hS
    (isPullback_towerTransition ξ (homOfLE (Nat.zero_le n)))
  have hc' := AlgebraicSpaces.isPullback_hom B S hS hcart
  refine Space.isPullback_of_isFlat_of_isPullback_restriction B S hS
    (Space.rangeSubspace B S hS _ hj)
    (Space.isFirstOrderThickening_squareZeroSubspace B S hS _
      (isSquareZeroClosedImmersion_of_squareZeroTower R hsurj hsq _ e he
        (homOfLE (Nat.zero_le n)))).isFiniteOrderThickening
    (towerStructureMap ξ n) (isFlat_towerStructureMap ξ n) (schemeSpaceMap (c.ι.app n))
    Rz.toBase g hg₂ (towerInclusion ξ n).hom Rz.immersion.hom
    ((towerStructureMap ξ 0).hom ≫ (Space.rangeIsoPresheaf B S hS _ hj).hom) ?_ ?_
    (congrArg (fun m => m.hom) hg₁)
  · refine h₀.of_iso (Iso.refl _) (Iso.refl _) (Space.rangeIsoPresheaf B S hS _ hj) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · simp
    · simp
    · simp [Space.rangeIsoPresheaf]
      rfl
  · refine hc'.of_iso ((ObjectProperty.ι _).mapIso Rz.closedSpaceIso.symm) (Iso.refl _)
      ((Space.rangeIsoPresheaf B S hS _ hj₀).symm ≪≫ Space.rangeIsoPresheaf B S hS _ hj)
      (Iso.refl _) ?_ ?_ ?_ ?_
    · have := congrArg (fun m => m.hom) Rz.immersion_eq_closedSpaceIso_hom_comp
      simp only [Iso.refl_hom, Category.comp_id, Functor.mapIso_hom, Iso.symm_hom,
        ObjectProperty.ι_map]
      rw [this]
      simp
    · simp only [towerRealizationClosedMap, limitBaseRangeIso, Space.rangeSpaceIso]
      change (Rz.closedSpaceIso.inv.hom ≫ (towerStructureMap ξ 0).hom ≫
          (Space.rangeIsoPresheaf B S hS _ hj₀).hom) ≫ ((Space.rangeIsoPresheaf B S hS _ hj₀).inv ≫
          (Space.rangeIsoPresheaf B S hS _ hj).hom) =
        Rz.closedSpaceIso.inv.hom ≫ (towerStructureMap ξ 0).hom ≫
          (Space.rangeIsoPresheaf B S hS _ hj).hom
      exact (Category.assoc _ _ _).trans (congrArg (Rz.closedSpaceIso.inv.hom ≫ ·)
        ((Category.assoc _ _ _).trans
          (congrArg ((towerStructureMap ξ 0).hom ≫ ·) (Iso.hom_inv_id_assoc _ _))))
    · simp
    · change (Subfunctor.range (yoneda.map (c.ι.app 0))).ι ≫ 𝟙 _ =
        ((Space.rangeIsoPresheaf B S hS _ hj₀).inv ≫ (Space.rangeIsoPresheaf B S hS _ hj).hom) ≫
          (Subfunctor.range (yoneda.map _)).ι ≫ yoneda.map (c.ι.app n)
      rw [Category.comp_id, Category.assoc, Space.rangeIsoPresheaf_hom,
        ← Category.assoc (Subfunctor.toRange _), Subfunctor.toRange_ι, ← Functor.map_comp, hcj,
        Iso.eq_inv_comp, Space.rangeIsoPresheaf_hom, Subfunctor.toRange_ι]

variable (κ : RingedToposExtensionProblem.KernelChangeHom.{u, u + 1, u, u, u + 1, u}
    (S := towerProblem ξ hsurj hsq e cR hcR c eLimit hc)
    (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc) P'
    (towerLimitSolutionOfKernelMap ξ hsurj hsq e he cR hcR c eLimit hc))

include κ in
/-- **The morphisms `Xₙ ⟶ X'` of a realized tower solution are cartesian and compatible**, once
`X₀ ⊂ X'` is the base change of `X'` along `Y₀ ⊂ Y`: morphisms `aₙ : Xₙ ⟶ X'` with
`Xₙ = X' ×_Y Yₙ` and `t ≫ aₙ = aₘ` for every transition `t : Xₘ ⟶ Xₙ`. -/
theorem exists_towerRealizationHom_isPullback_compatible
    (hcart : IsPullback (Space.subspaceInclusion B S hS Rz.ambient Rz.closedSubspace)
      (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc Rz) Rz.toBase
      (Space.subspaceInclusion B S hS (schemeSpace c.pt)
        (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc))) :
    ∃ a : ∀ n, ((comma B S hS).obj (ξ.obj n)).left.obj ⟶ Rz.ambient.obj,
      (∀ n, IsPullback ((comma B S hS).obj (ξ.obj n)).hom (a n) (yoneda.map (c.ι.app n))
        Rz.toBase.hom) ∧
      ∀ {m n : ℕ} (k : m ⟶ n), ((comma B S hS).map (ξ.map k)).left.hom ≫ a n = a m := by
  obtain ⟨g, hg₁, hg₂, hg₃⟩ :=
    exists_towerRealizationHom_compatible ξ hsurj hsq e he cR hcR c eLimit hc κ Rz
  exact ⟨fun n => (g n).hom, fun n => isPullback_towerRealizationHom ξ hsurj hsq e he cR hcR c
    eLimit hc Rz hcart n (g n) (hg₁ n) (hg₂ n), fun k => congrArg (fun m => m.hom) (hg₃ k)⟩

include κ in
/-- **The system is effective once the conormal map of `(X₀ ⊂ X') ⟶ (Y₀ ⊂ Y)` is invertible.** -/
theorem isEffectiveSystem_of_isIso_towerRealizationConormalMap
    (h : IsIso (Space.conormalMapOfImmersions B S hS
      (Space.subspaceInclusion B S hS Rz.ambient Rz.closedSubspace)
      (Space.subspaceInclusion B S hS (schemeSpace c.pt)
        (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc))
      (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc Rz) Rz.toBase
      (Space.isImmersion_subspaceInclusion B S hS _ _)
      (Space.isImmersion_subspaceInclusion B S hS _ _)
      (towerRealization_sq ξ hsurj hsq e cR hcR c eLimit hc Rz))) :
    Deformation.Artin.IsEffectiveSystem (cartesianProperFlatProjection B S hS) ξ c := by
  have hf := isFlat_isProper_isFinitePresentation_towerRealizationClosedMap ξ hsurj hsq e cR hcR
    c eLimit hc Rz
  obtain ⟨hfl, hpr, hfp, hcart⟩ :=
    Space.isFlat_isProper_isFinitePresentation_of_isIso_conormalMapOfImmersions B S hS
      Rz.closedSubspace (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc) Rz.toBase
      (towerRealizationClosedMap ξ hsurj hsq e cR hcR c eLimit hc Rz)
      (towerRealization_sq ξ hsurj hsq e cR hcR c eLimit hc Rz) Rz.firstOrder
      (Space.isFirstOrderThickening_squareZeroSubspace B S hS _
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc))
      hf.1 hf.2.1 hf.2.2 h
  obtain ⟨a, ha, hcompat⟩ :=
    exists_towerRealizationHom_isPullback_compatible ξ hsurj hsq e he cR hcR c eLimit hc Rz κ
      hcart
  exact isEffectiveSystem_of_spaces ξ c Rz.ambient Rz.toBase.hom ⟨hfp, hfl, hpr⟩ a ha hcompat

end AlgebraicGeometry.ProperFlatFibre

end
