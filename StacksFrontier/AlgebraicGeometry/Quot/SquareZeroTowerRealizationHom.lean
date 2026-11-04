module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitSurjective
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerRealizationRingMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionRealizationOfCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningHomPrecomposition

/-!
# The morphism `Xₙ ⟶ X'` of a realized solution of the tower problem

In the proof of [Stacks Project, Tag 0D3X], the map `φₙ : i⁻¹𝒪_{X'} ⟶ aₙ⁻¹𝒪_{Xₙ}`
(`AlgebraicGeometry.ProperFlatFibre.towerRealizationRingMap`) between the inverse images along
the two thickenings `aₙ : X₀ ⟶ Xₙ` and `i : X₀ ⟶ X'` gives a morphism `gₙ : Xₙ ⟶ X'`
(Stacks 05ZN, through the 05ZS equivalences of small étale sites): on every affine étale chart
`V` of `Xₙ` it is the spectrum of the ring map of partner charts. This file produces `gₙ`, with
`aₙ ≫ gₙ = i` and `gₙ` over `Y = Spec(lim Rₙ)`.

## Main results

* `AlgebraicGeometry.Space.isThickeningHom_of_hom_eq_comp_ι`: a morphism identified with the
  inclusion of a thickening subspace is a thickening.
* `AlgebraicGeometry.ProperFlatFibre.isThickeningHom_towerInclusion`,
  `AlgebraicGeometry.Space.EtaleSquareZeroExtension.Realization.isThickeningHom_immersion`.
* `AlgebraicGeometry.ProperFlatFibre.exists_towerRealizationHom`: `gₙ`.

## References

* [Stacks Project, Tag 05ZN](https://stacks.math.columbia.edu/tag/05ZN)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Deformation.ToposThickening

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism identified with the inclusion of a thickening subspace is a thickening.** -/
theorem isThickeningHom_of_hom_eq_comp_ι {X X' : AlgebraicSpaces B S hS} (Z : Subfunctor X'.1)
    (hZ : IsThickening B S hS X' Z) (i : X ⟶ X') (eZ : X.1 ⟶ Z.toFunctor) [IsIso eZ]
    (hi : i.hom = eZ ≫ Z.ι) : IsThickeningHom B S hS i := by
  have : Mono i.hom := hi ▸ mono_comp _ _
  rw [isThickeningHom_iff_of_mono]
  have hr : Subfunctor.range i.hom = Z := by
    rw [hi, Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top,
      Subfunctor.range_ι]
  rwa [hr]

/-- The immersion of a realization of a 05ZT extension is a thickening. -/
theorem EtaleSquareZeroExtension.Realization.isThickeningHom_immersion
    {X Y : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {E : EtaleSquareZeroExtension f} (Rz : E.Realization) :
    IsThickeningHom B S hS Rz.immersion :=
  isThickeningHom_of_hom_eq_comp_ι Rz.closed
    (IsNthOrderThickening.isThickening B S hS Rz.firstOrder) Rz.immersion Rz.closedIso.hom
    Rz.immersion_eq

end AlgebraicGeometry.Space

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

include hsurj hsq he in
/-- **`aₙ : X₀ ⟶ Xₙ` is a thickening**: it is identified with the inclusion of the first order
thickening `g⁻¹(Y₀) ⊆ Xₙ`. -/
theorem isThickeningHom_towerInclusion (n : ℕ) :
    Space.IsThickeningHom B S hS (towerInclusion ξ n) := by
  have : IsIso (towerFibreIso ξ hsurj hsq e he n).hom.hom :=
    (ObjectProperty.isIso_hom_iff _).2 inferInstance
  exact Space.isThickeningHom_of_hom_eq_comp_ι (towerFibre ξ hsurj hsq e he n).1
    (Space.IsNthOrderThickening.isThickening B S hS
      (isFirstOrderThickening_towerFibre ξ hsurj hsq e he n))
    (towerInclusion ξ n) (towerFibreIso ξ hsurj hsq e he n).hom.hom
    (congrArg (fun g => g.hom) (towerFibreIso_hom_comp_subspaceInclusion ξ hsurj hsq e he n).symm)

variable (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)
  {P' : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).CompatibleFirstOrderThickening}
  (κ : RingedToposExtensionProblem.KernelChangeHom.{u, u + 1, u, u, u + 1, u}
    (S := towerProblem ξ hsurj hsq e cR hcR c eLimit hc)
    (towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc) P'
    (towerLimitSolutionOfKernelMap ξ hsurj hsq e he cR hcR c eLimit hc))
  (Rz : Space.EtaleSquareZeroExtension.Realization
    (towerSolutionSquareZeroExtension ξ hsurj hsq e cR hcR c eLimit hc P'))

/-- **The morphism `gₙ : Xₙ ⟶ X'`** attached to `φₙ` (Stacks 05ZN): `aₙ ≫ gₙ = i`, `gₙ` lies
over `Y = Spec(lim Rₙ)`, and on every affine étale chart `V` of `Xₙ` it is `V ⟶ V' ⟶ X'`
for the partner chart `V'` and the spectrum of the ring map of partner charts. -/
theorem exists_towerRealizationHom (n : ℕ) :
    ∃ g : towerSpace ξ n ⟶ Rz.ambient,
      towerInclusion ξ n ≫ g = Rz.immersion ∧ g ≫ Rz.toBase = towerLimitStructureMap ξ c n ∧
      haveI : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) := IsAffine.of_isIso eLimit.hom
      ∀ (V : Space.SmallEtale B S hS (towerSpace ξ n).1)
        [IsAffine ((BigFppfOver.toScheme B S hS).obj
          ((Space.SmallEtale.toOver B S hS (towerSpace ξ n).1).obj V))],
        V.1.hom ≫ g.hom = yoneda.map (Space.thickeningChartSiteHom B S hS
            (isThickeningHom_towerInclusion ξ hsurj hsq e he n) Rz.isThickeningHom_immersion
            (towerRealizationRingMap ξ hsurj hsq e he cR hcR c eLimit hc κ Rz n)
            (towerLimitStructureMap ξ c n).hom Rz.toBase.hom
            (Space.thickeningChartRingHom_base_of_inverseImageStructureSheafMap B S hS
              (isThickeningHom_towerInclusion ξ hsurj hsq e he n) Rz.isThickeningHom_immersion
              (towerRealizationRingMap ξ hsurj hsq e he cR hcR c eLimit hc κ Rz n)
              (towerLimitStructureMap ξ c n).hom Rz.toBase.hom
              (towerRealization_immersion_comp_toBase ξ hsurj hsq e cR hcR c eLimit hc Rz n)
              (inverseImageStructureSheafMap_comp_towerRealizationRingMap ξ hsurj hsq e he cR hcR
                c eLimit hc κ Rz n)) V) ≫
          ((Space.thickeningChartTransfer B S hS (isThickeningHom_towerInclusion ξ hsurj hsq e he n)
            Rz.isThickeningHom_immersion).obj V).1.hom := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) := IsAffine.of_isIso eLimit.hom
  have hi₁ := isThickeningHom_towerInclusion ξ hsurj hsq e he n
  have hi₂ := Rz.isThickeningHom_immersion
  have hbase := Space.thickeningChartRingHom_base_of_inverseImageStructureSheafMap B S hS hi₁ hi₂
    (towerRealizationRingMap ξ hsurj hsq e he cR hcR c eLimit hc κ Rz n)
    (towerLimitStructureMap ξ c n).hom Rz.toBase.hom
    (towerRealization_immersion_comp_toBase ξ hsurj hsq e cR hcR c eLimit hc Rz n)
    (inverseImageStructureSheafMap_comp_towerRealizationRingMap ξ hsurj hsq e he cR hcR
      c eLimit hc κ Rz n)
  obtain ⟨g, hg⟩ := Space.exists_hom_of_thickeningChartSiteHom B S hS hi₁ hi₂
    (towerRealizationRingMap ξ hsurj hsq e he cR hcR c eLimit hc κ Rz n)
    (towerLimitStructureMap ξ c n).hom Rz.toBase.hom hbase
  refine ⟨g, ?_, ?_, hg⟩
  · exact Space.comp_eq_of_thickeningChartSiteHom B S hS hi₁ hi₂ _ _ _ hbase
      (Space.thickeningChartRingHom_comp_appTop_cartesianProjection B S hS hi₁ hi₂ _
        (towerRealizationRingMap_comp_fSharpInverseImage ξ hsurj hsq e he cR hcR c eLimit hc
          κ Rz n))
      g hg
  · exact ObjectProperty.hom_ext _
      (Space.comp_base_eq_of_thickeningChartSiteHom B S hS hi₁ hi₂ _ _ _ hbase g hg)

/-- **`φₙ` is `φₙ₊₁` followed by the transition map `Aₙ₊₁ ⟶ Aₙ`**: both are projections from
`𝒜 = lim Aₙ`. -/
theorem towerRealizationRingMap_eq_comp_towerRingSystem_map (n : ℕ) :
    towerRealizationRingMap ξ hsurj hsq e he cR hcR c eLimit hc κ Rz n =
      towerRealizationRingMap ξ hsurj hsq e he cR hcR c eLimit hc κ Rz (n + 1) ≫
        (towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op := by
  unfold towerRealizationRingMap
  exact (congrArg (Rz.sheafIso.hom ≫ κ.hom ≫ ·)
    (limit.w (towerRingSystem ξ) (homOfLE (Nat.le_succ n)).op).symm).trans
    ((congrArg (Rz.sheafIso.hom ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm)

include hsurj hsq he κ in
/-- **The morphisms `gₙ : Xₙ ⟶ X'` exist compatibly**: `aₙ ≫ gₙ = i`, `gₙ` lies over
`Y = Spec(lim Rₙ)`, and `t ≫ gₙ = gₘ` for every transition morphism `t : Xₘ ⟶ Xₙ`. -/
theorem exists_towerRealizationHom_compatible :
    ∃ g : ∀ n : ℕ, towerSpace ξ n ⟶ Rz.ambient,
      (∀ n, towerInclusion ξ n ≫ g n = Rz.immersion) ∧
      (∀ n, g n ≫ Rz.toBase = towerLimitStructureMap ξ c n) ∧
      ∀ {m n : ℕ} (k : m ⟶ n), towerTransition ξ k ≫ g n = g m := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) := IsAffine.of_isIso eLimit.hom
  choose g hg₁ hg₂ hg₃ using exists_towerRealizationHom ξ hsurj hsq e he cR hcR c eLimit hc κ Rz
  have hsucc : ∀ n : ℕ, towerTransition ξ (homOfLE (Nat.le_succ n)) ≫ g (n + 1) = g n := fun n =>
    Space.comp_eq_of_thickeningChartSiteHom_of_precomp B S hS
      (isThickeningHom_towerInclusion ξ hsurj hsq e he n)
      (isThickeningHom_towerInclusion ξ hsurj hsq e he (n + 1)) Rz.isThickeningHom_immersion
      (isClosedImmersion_towerTransition ξ hsurj hsq e he _)
      (towerInclusion_comp_towerTransition ξ n) _ _ _ _ _ _ _ (g (n + 1)) (hg₃ (n + 1)) (g n)
      (hg₃ n) ((towerRingSystem ξ).map (homOfLE (Nat.le_succ n)).op) (towerRingSystem_map_succ ξ n)
      (towerRealizationRingMap_eq_comp_towerRingSystem_map ξ hsurj hsq e he cR hcR c eLimit hc κ
        Rz n)
  have hle : ∀ (m n : ℕ) (h : m ≤ n), towerTransition ξ (homOfLE h) ≫ g n = g m := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base =>
      have h1 : towerTransition ξ (homOfLE (le_refl m)) = 𝟙 _ :=
        (congrArg (towerTransition ξ) (Subsingleton.elim _ (𝟙 m))).trans (by
          unfold towerTransition
          rw [ξ.map_id, (comma B S hS).map_id]
          rfl)
      rw [h1, Category.id_comp]
    | succ n hmn ih =>
      rw [← ih, ← hsucc n, ← Category.assoc, towerTransition_comp]
      exact congrArg (towerTransition ξ · ≫ g (n + 1)) (Subsingleton.elim _ _)
  refine ⟨g, hg₁, hg₂, fun {m n} k => ?_⟩
  rw [show k = homOfLE (leOfHom k) from Subsingleton.elim _ _]
  exact hle m n (leOfHom k)

end AlgebraicGeometry.ProperFlatFibre

end
