module

public import StacksFrontier.AlgebraicGeometry.Quot.SquareZeroTowerLimitComparisonReduction

/-!
# The limit comparison data of the tower problem

In the situation of `AlgebraicGeometry.ProperFlatFibre.towerProblem`, the body of the proof of
[Stacks Project, Tag 0D3X] identifies `φ : f^*𝒞_{Y₀/Y} ⟶ lim 𝒪_{X₀} ⊗ Iₙ` with the canonical map
`𝒪_{X₀} ⊗ lim Iₙ ⟶ lim 𝒪_{X₀} ⊗ Iₙ` (Stacks 0D3F) up to isomorphisms `α` and `β`. This file
packages `α`, `β` and the identification in the form consumed by
`AlgebraicGeometry.ProperFlatFibre.exists_towerProblem_kernelChangeHom_of_limitComparison`, from
the values of `φ` on the sections `1 ⊗ m`.

## Main results

* `AlgebraicGeometry.ProperFlatFibre.towerProblem_limitComparison_data`

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

/-- **The data `(α, β, hφ)` of the limit comparison of the tower problem.** If, for every `n` and
`m ∈ lim Iₙ`, the section `1 ⊗ m` of `𝒪_{X₀} ⊗ lim Iₙ`, read in `f^*𝒞_{Y₀/Y}`, is carried by
`φ = towerLimitKernelMap` and the `n`-th projection to the section `1 ⊗ mₙ` of `𝒪_{X₀} ⊗ Iₙ`, then
there are isomorphisms `α : f^*𝒞_{Y₀/Y} ≅ 𝒪_{X₀} ⊗ lim Iₙ` (namely
`AlgebraicGeometry.ProperFlatFibre.towerProblemKernelIso`) and
`β : lim 𝒪_{X₀} ⊗ Iₙ ≅ lim ℳₙ` with `φ = α ≫ (𝒪_{X₀} ⊗ lim Iₙ ⟶ lim 𝒪_{X₀} ⊗ Iₙ) ≫ β`: the
input of `AlgebraicGeometry.ProperFlatFibre.exists_towerProblem_kernelChangeHom_of_limitComparison`
for the system `Iₙ = towerBaseKernelSystem`. -/
theorem towerProblem_limitComparison_data
    [HasLimit (towerBaseKernelSystem ξ hsurj hsq e ⋙ Space.baseRingTensorModule B S hS
      (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0)))]
    (H : ∀ (n : ℕ) (m : ↑(limit (towerBaseKernelSystem ξ hsurj hsq e))),
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _ m ≫
        (towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc).inv ≫
        towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc ≫
        limit.π (towerIdealSystem ξ hsurj hsq e he) (op n) =
      Space.baseRingTensorSection B S hS (towerSpace ξ 0)
          (Space.baseRingHomOfMap (towerStructureMap ξ 0)) _
          (limit.π (towerBaseKernelSystem ξ hsurj hsq e) (op n) m) ≫
        (towerIdealSystemObjIso ξ hsurj hsq e he n).hom) :
    ∃ (α : (towerProblem ξ hsurj hsq e cR hcR c eLimit hc).G ≅ (Space.baseRingTensorModule B S hS
        (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0))).obj (limit
        (towerBaseKernelSystem ξ hsurj hsq e)))
      (β : limit (towerBaseKernelSystem ξ hsurj hsq e ⋙ Space.baseRingTensorModule B S hS
          (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0))) ≅
        ((towerProblem ξ hsurj hsq e cR hcR c eLimit hc).changeKernel (towerLimitKernelMap ξ hsurj
            hsq e he cR hcR c eLimit hc)).G),
      towerLimitKernelMap ξ hsurj hsq e he cR hcR c eLimit hc =
        α.hom ≫ limit.post (towerBaseKernelSystem ξ hsurj hsq e) (Space.baseRingTensorModule B S hS
            (towerSpace ξ 0) (Space.baseRingHomOfMap (towerStructureMap ξ 0))) ≫ β.hom :=
  ⟨towerProblemKernelIso ξ hsurj hsq e cR hcR c eLimit hc,
    exists_towerLimitKernelMap_eq_of_sections ξ @hsurj @hsq e @he cR hcR c eLimit hc H⟩

end AlgebraicGeometry.ProperFlatFibre

end
