module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationIdealSectionsPullback
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatDeformationKernelSections
public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparisonReduction

/-!
# The sections `1 ⊗ m` of `𝒪_{X₀} ⊗ lim Iₙ` in the prescribed module of the tower problem

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the body of the proof of
[Stacks Project, Tag 0D3X] identifies `f^*𝒞_{Y₀/Y}` with `𝒪_{X₀} ⊗_{Γ(Y₀)} lim Iₙ`
(`AlgebraicGeometry.ProperFlatFibre.towerProblemKernelIso`). This file computes the sections
`1 ⊗ m` through that identification: `1 ⊗ m` is the pullback along `f : X₀ ⟶ Y₀` of the class, in
the conormal module of `Y₀ ⊆ Y`, of the function `c` on `Y = Spec(lim Rₙ)` corresponding to `m`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.baseRingTensorSection_towerProblemKernelIso_inv`.

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory

/-- **A section read through the inverse of a composite of four isomorphisms**, one isomorphism at
a time, the composite given as a variable `E` with its defining equation. -/
theorem comp_inv_eq_of_eq_trans_trans_trans {C : Type*} [Category C] {U P Q Q' Q'' Q''' : C}
    (σ : U ⟶ Q''') (a : P ≅ Q) (b : Q ≅ Q') (c : Q' ≅ Q'') (d : Q'' ≅ Q''')
    (x₁ : U ⟶ Q'') (x₂ : U ⟶ Q') (x₃ : U ⟶ Q) (z : U ⟶ P)
    (h₁ : σ ≫ d.inv = x₁) (h₂ : x₁ ≫ c.inv = x₂) (h₃ : x₂ ≫ b.inv = x₃) (h₄ : x₃ ≫ a.inv = z)
    (E : P ≅ Q''') (hE : E = a ≪≫ b ≪≫ c ≪≫ d) : σ ≫ E.inv = z := by
  subst hE h₁ h₂ h₃ h₄
  simp

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {T T' : BigFppfOver B S hS} (j : T ⟶ T')
  (hj : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j))
  (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
  {X : AlgebraicSpaces B S hS} (q : X ⟶ schemeSpace T)

/-- Through `AlgebraicGeometry.Space.conormalModuleRangePullbackIso` and
`AlgebraicGeometry.Space.rangeSpaceIso`, the section `1 ⊗ (1 ⊗ c)` is the pullback along
`q : X ⟶ T ≅ T'|_T` of the class of `c` in the conormal module of `T ⊆ T'`. -/
theorem baseRingTensorSection_rangeConormalBaseElement_conormalModuleRangePullbackIso_inv
    (c : closedSubspaceBaseIdeal B S hS (rangeSubspace B S hS j hj)) :
    baseRingTensorSection B S hS X (baseRingHomOfMap q) (rangeConormalBaseModule B S hS j hj)
        (rangeConormalBaseElement B S hS j hj c) ≫
        (conormalModuleRangePullbackIso B S hS j hj hT' q).inv =
      modulePullbackGlobalSection B S hS (q ≫ (rangeSpaceIso B S hS j hj).hom)
        (rangeConormalSection B S hS j hj c) := by
  have h :=
    baseRingTensorSection_rangeConormalBaseElement_conormalModuleRangeSchemeBasePullbackIso_inv
      B S hS j hj hT' q c
  rw [conormalModuleRangeSchemeBasePullbackIso_eq] at h
  exact h

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
  (cR : Cone R) (hcR : IsLimit cR) (c : Cocone (ξ ⋙ cartesianProperFlatProjection B S hS))
  (eLimit : (BigFppfOver.toScheme B S hS).obj c.pt ≅ Spec (.of cR.pt))
  (hc : ∀ n : ℕ, (BigFppfOver.toScheme B S hS).map (c.ι.app n) ≫ eLimit.hom =
    (e n).hom ≫ Scheme.Spec.map (CommRingCat.ofHom (cR.π.app (.op n)).hom.toRingHom).op)

/-- The function on `Y = Spec(lim Rₙ)` vanishing on `Y₀` that corresponds to `m ∈ lim Iₙ`,
through `Ker(Γ(Y) → Γ(Y₀)) ≅ lim Iₙ` (`AlgebraicGeometry.ProperFlatFibre.towerLimitKernelIso`). -/
def towerLimitKernelFunction (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    Space.closedSubspaceBaseIdeal B S hS (limitBaseSubspace ξ hsurj hsq e cR hcR c eLimit hc) :=
  ⟨((towerLimitKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv.hom m :
      RingHom.ker (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (c.ι.app 0)).op).hom).1, by
    rw [Space.closedSubspaceBaseIdeal_rangeSubspace]
    exact ((towerLimitKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv.hom m).2⟩

/-- `AlgebraicGeometry.ProperFlatFibre.towerProblemKernelIso` as the composite it is defined by,
with `Y₀ ≅ (Y₀ ⊆ Y)` spelled `AlgebraicGeometry.Space.rangeSpaceIso`. -/
theorem towerProblemKernelIso_eq_trans :
    towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc =
      (Space.modulePullback B S hS (towerStructureMap ξ 0)).mapIso
          ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ 0))
            (Space.rangeSpaceIso B S hS (c.ι.app 0)
              (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom
            (Space.isEtale_hom_of_iso B S hS _)).app
            (Space.rangeConormalModule B S hS (c.ι.app 0)
              (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1)).symm ≪≫
        (Space.modulePullbackCompIso B S hS (towerStructureMap ξ 0)
          (Space.rangeSpaceIso B S hS (c.ι.app 0)
            (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom).app
          (Space.rangeConormalModule B S hS (c.ι.app 0)
            (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1) ≪≫
        Space.conormalModuleRangePullbackIso B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
          (IsAffine.of_isIso eLimit.hom) (towerStructureMap ξ 0) ≪≫
        (Space.baseRingTensorModule B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0))).mapIso
          (Space.rangeConormalBaseModuleIso B S hS (c.ι.app 0)
            (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
            (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).1
            (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).2 ≪≫
            towerLimitKernelIso ξ hsurj hsq e cR hcR c eLimit hc) :=
  rfl


/-- **The section `1 ⊗ m` of `𝒪_{X₀} ⊗ lim Iₙ`, read in `f^*𝒞_{Y₀/Y}`**: through
`AlgebraicGeometry.ProperFlatFibre.towerProblemKernelIso` it is the pullback along
`f : X₀ ⟶ Y₀` of the class of the function `c` corresponding to `m`
(`AlgebraicGeometry.ProperFlatFibre.towerLimitKernelFunction`) in the conormal module of
`Y₀ ⊆ Y`, restricted to `Y₀` along `Y₀ ≅ (Y₀ ⊆ Y)`. -/
theorem baseRingTensorSection_towerProblemKernelIso_inv
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    Space.baseRingTensorSection B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))
        (limit (towerBaseKernelSystem ξ hsurj hsq e)) m ≫
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv =
      Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0)
          (Space.modulePullbackGlobalSection B S hS (X := schemeSpace (towerBase ξ 0))
            (Space.rangeSpaceIso B S hS (c.ι.app 0)
              (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom
            (Space.rangeConormalSection B S hS (c.ι.app 0)
              (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
              (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m))) ≫
        (Space.modulePullback B S hS (towerStructureMap ξ 0)).map
          ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ 0))
            (Space.rangeSpaceIso B S hS (c.ι.app 0)
              (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom
            (Space.isEtale_hom_of_iso B S hS _)).app (Space.rangeConormalModule B S hS (c.ι.app 0)
              (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1)).hom := by
  have h1 : Space.baseRingTensorSection B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))
      (limit (towerBaseKernelSystem ξ hsurj hsq e)) m ≫
      ((Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))).mapIso
      (Space.rangeConormalBaseModuleIso B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
        (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).1
        (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).2 ≪≫
        towerLimitKernelIso ξ hsurj hsq e cR hcR c eLimit hc)).inv =
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))
        (Space.rangeConormalBaseModule B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1)
        (Space.rangeConormalBaseElement B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
          (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m)) := by
    have hm := Space.baseRingTensorSection_map B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))
      (Space.rangeConormalBaseModuleIso B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
          (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).1
          (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).2 ≪≫
          towerLimitKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv m
    have hv : (Space.rangeConormalBaseModuleIso B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
          (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).1
          (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).2 ≪≫
          towerLimitKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv.hom m =
        Space.rangeConormalBaseElement B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
          (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m) :=
      Space.rangeConormalBaseModuleIso_inv_apply B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
        (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).1
        (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).2 _
    exact hm.trans (congrArg (Space.baseRingTensorSection B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))
      (Space.rangeConormalBaseModule B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1)) hv)
  have h2 : Space.baseRingTensorSection B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))
        (Space.rangeConormalBaseModule B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1)
        (Space.rangeConormalBaseElement B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
          (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m)) ≫
        (Space.conormalModuleRangePullbackIso B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
          (IsAffine.of_isIso eLimit.hom) (towerStructureMap ξ 0)).inv =
      Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0 ≫
          (Space.rangeSpaceIso B S hS (c.ι.app 0)
            (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom)
        (Space.rangeConormalSection B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
          (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m)) :=
    Space.baseRingTensorSection_rangeConormalBaseElement_conormalModuleRangePullbackIso_inv
      B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
      (IsAffine.of_isIso eLimit.hom) (towerStructureMap ξ 0)
      (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m)
  have h3 := Space.modulePullbackGlobalSection_comp_modulePullbackCompIso_app_inv B S hS
    (towerStructureMap ξ 0) (Space.rangeSpaceIso B S hS (c.ι.app 0)
      (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom
    (Space.rangeConormalSection B S hS (c.ι.app 0)
      (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
      (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m))
  exact CategoryTheory.comp_inv_eq_of_eq_trans_trans_trans _
    ((Space.modulePullback B S hS (towerStructureMap ξ 0)).mapIso
      ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom
        (Space.isEtale_hom_of_iso B S hS _)).app (Space.rangeConormalModule B S hS (c.ι.app 0)
          (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1)).symm)
    ((Space.modulePullbackCompIso B S hS (towerStructureMap ξ 0)
      (Space.rangeSpaceIso B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1).hom).app
      (Space.rangeConormalModule B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1))
    (Space.conormalModuleRangePullbackIso B S hS (c.ι.app 0)
      (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
      (IsAffine.of_isIso eLimit.hom) (towerStructureMap ξ 0))
    ((Space.baseRingTensorModule B S hS (towerSpace ξ 0)
      (Space.baseRingHomOfMap (towerStructureMap ξ 0))).mapIso
      (Space.rangeConormalBaseModuleIso B S hS (c.ι.app 0)
        (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq e cR hcR c eLimit hc).1
        (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).1
        (surjective_and_ker_sq_eq_bot_limitBase_Γ ξ hsurj hsq e cR hcR c eLimit hc).2 ≪≫
        towerLimitKernelIso ξ hsurj hsq e cR hcR c eLimit hc))
    _ _ _ _ h1 h2 h3 rfl _ (towerProblemKernelIso_eq_trans ξ hsurj hsq e cR hcR c eLimit hc)

end AlgebraicGeometry.ProperFlatFibre

end
