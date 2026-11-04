module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.GlobalCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirschAffine

/-!
# The morphism `ξ̃` of the Leray--Hirsch theorem over an affine base, on cohomology

Let `f : X ⟶ Y` be a smooth proper morphism of schemes over `S`, with `Y` and `S` affine, and let
`ξ_i ∈ H^{n_i}_{dR}(X/S)` be classes whose images in the de Rham cohomology of every fibre form a
basis. Then `ξ̃ = ⨁ ξ̃_i[-n_i] : ⨁ Ω^•_{Y/S}[-n_i] ⟶ Rf_*Ω^•_{X/S}` induces bijections on
`H^k(Y, -)` for every `k`: this is the input of the proof of Proposition 0FMR at the members of a
basis of the topology of `Y`, supplied by Lemma 0FUM through the identification of `H^k(Y, ξ̃)`
with `(a_i) ↦ ∑ ξ_i ∪ f^*a_i`.

## Main results

* `AlgebraicGeometry.DeRhamLerayHirsch.bijective_cohomologyFunctor_lerayHirschMorphism`: over an
  affine base, `ξ̃` induces bijections on cohomology.
* `AlgebraicGeometry.Scheme.Hom.isBasis_affine_le_preimage_affine`: the affine opens of `Y` mapping
  into an affine open of `S` form a basis of the topology of `Y`.

## References

* [Stacks Project, Tag 0FMR](https://stacks.math.columbia.edu/tag/0FMR)
* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- **The affine opens of `Y` mapping into an affine open of `S` form a basis of the topology of
`Y`**, for any morphism `g : Y ⟶ S`: this is the basis on which the proof of Proposition 0FMR
checks the isomorphism, reducing it to the case of affine `Y` and `S`. -/
theorem isBasis_affine_le_preimage_affine {Y S : Scheme.{u}} (g : Y ⟶ S) :
    TopologicalSpace.Opens.IsBasis
      {V : Y.Opens | IsAffineOpen V ∧ ∃ W : S.Opens, IsAffineOpen W ∧ V ≤ g ⁻¹ᵁ W} := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro U x hx
  obtain ⟨W, hW, hgx, -⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens S)
      (show g.base x ∈ (⊤ : S.Opens) from trivial)
  obtain ⟨V, hV, hxV, hVU⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)
      (show x ∈ U ⊓ g ⁻¹ᵁ W from ⟨hx, hgx⟩)
  exact ⟨V, ⟨hV, W, hW, hVU.trans inf_le_right⟩, hxV, hVU.trans inf_le_left⟩

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **Over an affine base, `ξ̃` induces bijections on cohomology** (Lemma 0FUM read through
`sum_deRhamCohomologyCup_eq_lerayCohomologyIso`): for `f : X ⟶ Y` smooth proper with `Y` and `S`
affine and classes `ξ_i` restricting to a basis of the de Rham cohomology of every fibre, the map
`H^k(Y, ⨁ Ω^•_{Y/S}[-n_i]) ⟶ H^k(Y, Rf_*Ω^•_{X/S})` induced by `ξ̃` is bijective for every `k`. -/
theorem bijective_cohomologyFunctor_lerayHirschMorphism [Smooth f] [IsProper f] [IsAffine Y]
    [IsAffine S] {r : ℕ} (n : Fin r → ℕ)
    (ξ : ∀ i, SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (n i : ℤ))
    (hb : ∀ y : Y, ∃ b : Module.Basis (Fin r) (Y.residueField y)
        (DirectSum ℤ fun m : ℤ => ↥(fibreDeRhamModule f y m)),
      ∀ i, b i = DirectSum.lof (Y.residueField y) ℤ (fun m : ℤ => ↥(fibreDeRhamModule f y m))
        (n i : ℤ) (fibreClassOverS f g y (n i : ℤ) (ξ i)))
    (k : ℤ) :
    Function.Bijective ((cohomologyFunctor g k).map (lerayHirschMorphism f g n ξ)).hom :=
  (bijective_cohomologyFunctor_lerayHirschMorphism_iff f g n ξ k).2
    (bijective_sum_deRhamCup_pullback f g n ξ hb k)

end AlgebraicGeometry.DeRhamLerayHirsch
