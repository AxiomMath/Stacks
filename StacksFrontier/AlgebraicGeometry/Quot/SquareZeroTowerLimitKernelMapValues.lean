module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparisonSections

/-!
# The sections `1 ⊗ m` of the tower problem read in `f^*𝒞_{Y₀/Y}`

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the body of the proof of
[Stacks Project, Tag 0D3X] compares `φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` with the canonical map
`𝒪_{X₀} ⊗ lim Iₙ ⟶ lim 𝒪_{X₀} ⊗ Iₙ` on the sections `1 ⊗ m`, `m ∈ lim Iₙ`. Read in
`f^*𝒞_{Y₀/Y}`, the section `1 ⊗ m` is the pullback `f^*σ_m` of the class `σ_m` of the function
`c_m ∈ Ker(Γ(Y) → Γ(Y₀))` in the conormal module of `Y₀ ⊆ Y`.

## Main results

* In `AlgebraicGeometry.ProperFlatFibre`:
  `baseRingTensorSection_towerProblemKernelIso_inv_eq_modulePullbackGlobalSection`,
  `…_rangeConormalModule`

## References

* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe u

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` leaves a stuck universe
constraint against the `𝒪_X`-modules at the universe of the schemes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

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

/-- **The section `1 ⊗ m` of `𝒪_{X₀} ⊗ lim Iₙ`, read in `f^*𝒞_{Y₀/Y}`, is the pullback `f^*σ_m`**
of the global section `σ_m` of `𝒞_{Y₀/Y}`, spelled with the conormal module of the range of
`Y₀ ⟶ Y`: `σ_m` is the class of `c_m ∈ Ker(Γ(Y) → Γ(Y₀))`
(`AlgebraicGeometry.ProperFlatFibre.towerLimitKernelFunction`) in the conormal module of `Y₀ ⊆ Y`,
restricted along `Y₀ ≅ (Y₀ ⊆ Y)`. -/
theorem
  baseRingTensorSection_towerProblemKernelIso_inv_eq_modulePullbackGlobalSection_rangeConormalModule
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    Space.baseRingTensorSection B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))
        (limit (towerBaseKernelSystem ξ hsurj hsq e)) m ≫
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv =
      Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0)
          ((Space.modulePullbackGlobalSection B S hS (X := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq
            e cR hcR c eLimit hc).1).hom
        (Space.rangeConormalSection B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ
            hsurj hsq e cR hcR c eLimit hc).1
          (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m))) ≫
      ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq
            e cR hcR c eLimit hc).1).hom (Space.isEtale_hom_of_iso B S hS _)).app
          (Space.rangeConormalModule B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ
              hsurj hsq e cR hcR c eLimit hc).1)).hom) :=
  (baseRingTensorSection_towerProblemKernelIso_inv ξ @hsurj @hsq e cR hcR c eLimit hc m).trans
    (Space.modulePullbackGlobalSection_comp B S hS (towerStructureMap ξ 0)
        (Space.modulePullbackGlobalSection B S hS (X := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq
            e cR hcR c eLimit hc).1).hom
        (Space.rangeConormalSection B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ
            hsurj hsq e cR hcR c eLimit hc).1
          (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m)))
      ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq
            e cR hcR c eLimit hc).1).hom (Space.isEtale_hom_of_iso B S hS _)).app
          (Space.rangeConormalModule B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ
              hsurj hsq e cR hcR c eLimit hc).1)).hom).symm

/-- **The section `1 ⊗ m` of `𝒪_{X₀} ⊗ lim Iₙ`, read in `f^*𝒞_{Y₀/Y}`, is the pullback `f^*σ_m`**
of the global section `σ_m` of `𝒞_{Y₀/Y}` (the class of `c_m ∈ Ker(Γ(Y) → Γ(Y₀))` restricted along
`Y₀ ≅ (Y₀ ⊆ Y)`), as a section of the base ideal of the tower problem. -/
theorem baseRingTensorSection_towerProblemKernelIso_inv_eq_modulePullbackGlobalSection
    (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))) :
    Space.baseRingTensorSection B S hS (towerSpace ξ 0)
        (Space.baseRingHomOfMap (towerStructureMap ξ 0))
        (limit (towerBaseKernelSystem ξ hsurj hsq e)) m ≫
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv =
      Space.modulePullbackGlobalSection B S hS (towerStructureMap ξ 0)
        (M := limitBaseConormal ξ hsurj hsq e cR hcR c eLimit hc)
            ((Space.modulePullbackGlobalSection B S hS (X := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq
            e cR hcR c eLimit hc).1).hom
        (Space.rangeConormalSection B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ
            hsurj hsq e cR hcR c eLimit hc).1
          (towerLimitKernelFunction ξ hsurj hsq e cR hcR c eLimit hc m))) ≫
      ((Space.modulePullbackIsoEtaleRestrictionModule B S hS (U := schemeSpace (towerBase ξ 0))
        (Space.rangeSpaceIso B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ hsurj hsq
            e cR hcR c eLimit hc).1).hom (Space.isEtale_hom_of_iso B S hS _)).app
          (Space.rangeConormalModule B S hS (c.ι.app 0) (isSquareZeroClosedImmersion_limitBase ξ
              hsurj hsq e cR hcR c eLimit hc).1)).hom : SheafOfModules.unit ((sheafCompose
              (Space.SmallEtale.topology B S hS
        (schemeSpace (towerBase ξ 0)).1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (Space.smallEtaleRingedTopos B S hS (schemeSpace (towerBase ξ 0))).O) ⟶ limitBaseConormal ξ
            hsurj hsq e cR hcR c eLimit hc) :=
  baseRingTensorSection_towerProblemKernelIso_inv_eq_modulePullbackGlobalSection_rangeConormalModule
    ξ @hsurj @hsq e cR hcR c eLimit hc m

end AlgebraicGeometry.ProperFlatFibre

end
