module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationLinearIdeal
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatEffectiveSystem
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerIdealComparison
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitIdealMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionModulePullback

/-!
# The prescribed module of the tower problem as `𝒪_{X₀} ⊗ lim Iₙ`

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, with
`Y = Spec(lim Rₙ)` affine, the conormal module of `Y₀ ⊆ Y` is `𝒪_{Y₀} ⊗ I` with
`I = Ker(lim Rₙ → R₀) = lim Iₙ` (Stacks 04CN), and its pullback to `X₀` is `𝒪_{X₀} ⊗ lim Iₙ`,
the source of the canonical map `𝒪_{X₀} ⊗ lim Iₙ ⟶ lim 𝒪_{X₀} ⊗ Iₙ` of Stacks 0D3F.

## Main definitions

* `AlgebraicGeometry.ProperFlatFibre.towerLimitΓIso`: `Γ(Y) ≅ lim Rₙ`.
* `AlgebraicGeometry.ProperFlatFibre.towerLimitKernelIso`: `Ker(Γ(Y) → Γ(Y₀)) ≅ lim Iₙ`, as
  `Γ(Y₀)`-modules.
* `AlgebraicGeometry.ProperFlatFibre.towerProblemKernelIso`: `f^*𝒞_{Y₀/Y} ≅ 𝒪_{X₀} ⊗ lim Iₙ`.
* `AlgebraicGeometry.ProperFlatFibre.towerBaseKernelSystemObjIso`: `Iₙ ≅ Ker(Γ(Yₙ) → Γ(Y₀))`.
* `AlgebraicGeometry.ProperFlatFibre.towerIdealSystemObjIso`: `𝒪_{X₀} ⊗ Iₙ` is the ideal of the
  `n`-th extension of the tower.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.surjective_and_ker_sq_eq_bot_limitBase_Γ`: `Γ(Y) ⟶ Γ(Y₀)`
  is surjective with square-zero kernel.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D3F](https://stacks.math.columbia.edu/tag/0D3F)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

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

include hsurj hsq hcR hc in
/-- **`Γ(Y) ⟶ Γ(Y₀)` is surjective with square-zero kernel**, `Y = Spec(lim Rₙ)`: it is
`lim Rₙ ⟶ R₀` up to isomorphisms. -/
theorem surjective_and_ker_sq_eq_bot_limitBase_Γ :
    Function.Surjective (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (c.ι.app 0)).op).hom ∧
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (c.ι.app 0)).op).hom ^ 2 = ⊥ :=
  surjective_and_ker_sq_eq_bot_Γ_map_of_specIso
    (CommRingCat.ofHom (CommAlgCat.towerLimitProjection cR))
    (CommAlgCat.surjective_towerLimit_π_zero hsurj cR hcR)
    (CommAlgCat.ker_towerLimit_π_zero_sq_eq_bot hsq cR hcR) _ (e 0) eLimit (hc 0)

/-- **`Γ(Y) ≅ lim Rₙ`**, through the identification `Y ≅ Spec(lim Rₙ)`. -/
def towerLimitΓIso :
    Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj c.pt)) ≅ CommRingCat.of cR.pt :=
  (Scheme.Γ.mapIso eLimit.op).symm ≪≫ Scheme.ΓSpecIso _

include hc in
/-- Pullback of functions along `Y₀ ⟶ Y` is `lim Rₙ ⟶ R₀` under `Γ(Y) ≅ lim Rₙ`, `Γ(Y₀) ≅ R₀`. -/
theorem towerLimitΓIso_hom_comp_towerLimitProjection :
    (towerLimitΓIso ξ cR c eLimit).hom ≫ CommRingCat.ofHom (CommAlgCat.towerLimitProjection cR) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (c.ι.app 0)).op ≫
        (towerBaseΓIso ξ e 0).hom := by
  have hf : (BigFppfOver.toScheme B S hS).map (c.ι.app 0) =
      (e 0).hom ≫ Spec.map (CommRingCat.ofHom (CommAlgCat.towerLimitProjection cR)) ≫
        eLimit.inv :=
    ((Iso.eq_comp_inv _).2 (hc 0)).trans (Category.assoc _ _ _)
  have hc' : (e 0).hom.appTop ≫ (e 0).inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
    rfl
  change eLimit.inv.appTop ≫ (Scheme.ΓSpecIso _).hom ≫ _ =
    ((BigFppfOver.toScheme B S hS).map (c.ι.app 0)).appTop ≫ (e 0).inv.appTop ≫
      (Scheme.ΓSpecIso _).hom
  simp only [hf, Scheme.Hom.comp_appTop, Category.assoc]
  rw [reassoc_of% hc', Scheme.ΓSpecIso_naturality]

/-- **`Ker(Γ(Y) → Γ(Y₀)) ≅ lim Iₙ`** as `Γ(Y₀)`-modules, `Iₙ = Ker(Rₙ → R₀)`: through
`Γ(Y) ≅ lim Rₙ` the kernel is `Ker(lim Rₙ → R₀)`, which is `lim Iₙ`. -/
def towerLimitKernelIso :
    RingHom.squareZeroKer _ (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c
        eLimit hc).1 (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).2 ≅
      limit (towerBaseKernelSystem ξ hsurj hsq e) :=
  RingHom.squareZeroKerRestrictScalarsIso _ _ _ _
      (CommAlgCat.surjective_towerLimit_π_zero hsurj cR hcR)
      (CommAlgCat.ker_towerLimit_π_zero_sq_eq_bot hsq cR hcR)
      (towerLimitΓIso ξ cR c eLimit).commRingCatIsoToRingEquiv (towerBaseΓIso ξ e 0).hom.hom
      (congrArg CommRingCat.Hom.hom
        (towerLimitΓIso_hom_comp_towerLimitProjection ξ e cR c eLimit hc))
      (ConcreteCategory.bijective_of_isIso (towerBaseΓIso ξ e 0).hom).1 ≪≫
    (ModuleCat.restrictScalars.{u} (towerBaseΓIso ξ e 0).hom.hom).mapIso
      ((CommAlgCat.isLimitTowerKernelCone hsurj hsq cR hcR).conePointUniqueUpToIso
        (limit.isLimit _)) ≪≫
    (preservesLimitIso (ModuleCat.restrictScalars.{u} (towerBaseΓIso ξ e 0).hom.hom)
      (CommAlgCat.towerKernelSystem R hsurj hsq))

/-- **`f^*𝒞_{Y₀/Y} ≅ 𝒪_{X₀} ⊗_{Γ(Y₀)} lim Iₙ`**, the prescribed module of the tower problem:
étale restriction along `Y₀ ≅ (Y₀ ⊆ Y)` is pullback (Stacks 03LW), the conormal module of
`Y₀ ⊆ Y = Spec(lim Rₙ)` is `𝒪_{Y₀} ⊗ (Γ(Y₀) ⊗_{Γ(Y)} I)` (Stacks 04CN), `Γ(Y₀) ⊗_{Γ(Y)} I = I`
since `I² = 0`, and `I = lim Iₙ`. -/
def towerProblemKernelIso :
    (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G ≅
      (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))).obj
        (limit (towerBaseKernelSystem ξ hsurj hsq e)) :=
  (Space.modulePullback B S hS (towerStructureMap ξ 0)).mapIso
      ((Space.modulePullbackIsoEtaleRestrictionModule B S hS
        (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom
        (Space.isEtale_hom_of_iso B S hS _)).app _).symm ≪≫
    (Space.modulePullbackCompIso B S hS (towerStructureMap ξ 0)
      (limitBaseRangeIso ξ hsurj hsq e cR hcR c eLimit hc).hom).app _ ≪≫
    Space.conormalModuleRangePullbackIso B S hS (c.ι.app 0)
      (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
      (IsAffine.of_isIso eLimit.hom) (towerStructureMap ξ 0) ≪≫
    (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))).mapIso
      (Space.rangeConormalBaseModuleIso B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
        (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).1
        (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).2 ≪≫
        towerLimitKernelIso ξ hsurj hsq e cR hcR c eLimit hc)

include he in
/-- **`Iₙ ≅ Ker(Γ(Yₙ) → Γ(Y₀))`** as `Γ(Y₀)`-modules: the `n`-th term of
`AlgebraicGeometry.ProperFlatFibre.towerBaseKernelSystem` is the kernel of pullback of functions
along `Y₀ ⟶ Yₙ`. -/
def towerBaseKernelSystemObjIso (n : ℕ) :
    (towerBaseKernelSystem ξ hsurj hsq e).obj (op n) ≅
      RingHom.squareZeroKer _
        (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n))).1
        (surjective_and_ker_sq_eq_bot_towerBase_map ξ hsurj hsq e he
          (homOfLE (Nat.zero_le n))).2 :=
  (ModuleCat.restrictScalars.{u} (towerBaseΓIso ξ e 0).hom.hom).mapIso
      (towerKernelIso ξ hsurj hsq e he n) ≪≫
    ((ModuleCat.restrictScalarsComp'.{u} (towerBaseΓIso ξ e 0).hom.hom
      (towerBaseΓIso ξ e 0).inv.hom (RingHom.id _)
      (RingHom.ext fun x => ((towerBaseΓIso ξ e 0).hom_inv_id_apply x).symm)).app _).symm ≪≫
    (ModuleCat.restrictScalarsId'.{u} (RingHom.id _) rfl).app _

/-- **`𝒪_{X₀} ⊗_{Γ(Y₀)} Iₙ` is the ideal of the `n`-th extension**: the `n`-th term of the
base-ring tensor tower is the ideal of the extension `0 → 𝒪_{X₀} ⊗ Iₙ → Aₙ → 𝒪_{X₀} → 0`. -/
def towerIdealSystemObjIso (n : ℕ) :
    (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))).obj
        ((towerBaseKernelSystem ξ hsurj hsq e).obj (op n)) ≅
      (towerIdealSystem ξ hsurj hsq e he).obj (op n) :=
  (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))).mapIso
      (towerBaseKernelSystemObjIso ξ hsurj hsq e he n) ≪≫
    (towerExtensionIdealIso ξ hsurj hsq e he n).symm

end AlgebraicGeometry.ProperFlatFibre

end
