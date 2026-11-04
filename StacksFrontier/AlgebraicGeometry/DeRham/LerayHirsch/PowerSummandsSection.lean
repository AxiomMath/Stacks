module

public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.PowerSummands
public import StacksFrontier.CategoryTheory.Triangulated.RetractionFromBiproductSection

/-!
# The section of `c ⊕ Rf_*θ` from the Leray--Hirsch decomposition

Let `f : X ⟶ Y`, `g : Y ⟶ S` be morphisms of schemes, `ξ ∈ H^d_{dR}(X/S)`, and let
`ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[d]` be the morphism of Remark 0FU7, with untwisted form
`θ = ξ'[-d] : Ω^•_{X/S}[-d] ⟶ Ω^•_{X/S}`. Assume that the morphism

`ξ̃ : ⨁_{t < r} Ω^•_{Y/S}[-dt] ⟶ Rf_*Ω^•_{X/S}`

of Proposition 0FMR for the powers `ξ^0, …, ξ^{r - 1}` is an isomorphism, `r ≥ 1`. This is the
situation of Remark 0FUN, for the projective bundle `f : 𝐏(ℰ) ⟶ Y` of a locally free module of
rank `r` and `ξ = c₁^{dR}(𝒪(1))`, `d = 2`.

The proof of [Stacks, Tag 0FUW] uses two consequences of Remark 0FUN: `c ⊕ ξ̃|_M` is an
isomorphism, for `c : Ω^•_{Y/S} ⟶ Rf_*Ω^•_{X/S}` the canonical map, and the square
`Rf_*ξ' ∘ ξ̃|_K = (ξ̃|_M)[d] ∘ id` commutes. Together they say that `ξ̃|_M` factors through
`Rf_*θ`, and hence that the map `c ⊕ Rf_*θ : Ω^•_{Y/S} ⊕ Rf_*(Ω^•_{X/S}[-d]) ⟶ Rf_*Ω^•_{X/S}`
has a section restricting to the inclusion of `Ω^•_{Y/S}` along `c`. This file proves both.

## Main definitions

* `AlgebraicGeometry.DeRhamLerayHirsch.classUntwisted`: the untwisted map `θ = ξ'[-n]` of a class
  `ξ` of degree `n`.

## Main results

* `CategoryTheory.Functor.exists_comp_map_untwist_eq`: a map `μ` into `G(A)` whose translate is,
  up to an isomorphism, a map composed with `G(ζ)`, factors through `G` of the untwisted `ζ`.
* `AlgebraicGeometry.DeRhamLerayHirsch.exists_comp_map_classUntwisted_eq`: `ξ̃|_M` factors through
  `Rf_*θ`.
* `AlgebraicGeometry.DeRhamLerayHirsch.exists_section_of_isIso_lerayHirschPowerMorphism`: the
  section of `c ⊕ Rf_*θ`.

## References

* [Stacks Project, Tag 0FUW](https://stacks.math.columbia.edu/tag/0FUW)
* [Stacks Project, Tag 0FUN](https://stacks.math.columbia.edu/tag/0FUN)
* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange
open scoped Stacks.StandardDerivedModel

universe u

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
  (G : C ⥤ D) [G.CommShift ℤ]

/-- **Untwisting a factorisation.** Let `ζ : A ⟶ A[n]`, `μ : M ⟶ G(A)`, `N : K ⟶ G(A)` and an
isomorphism `e : K ⟶ M[n]` satisfy `N ≫ G(ζ) = e ≫ μ[n]`, read through the commutation of `G`
with the shift. Then `μ` factors through `G` of the untwisted map `ζ[-n] : A[-n] ⟶ A`. -/
theorem exists_comp_map_untwist_eq {A : C} {K M : D} (n : ℤ) (ζ : A ⟶ A⟦n⟧) (μ : M ⟶ G.obj A)
    (N : K ⟶ G.obj A) (e : K ⟶ M⟦n⟧) [IsIso e]
    (h : N ≫ G.map ζ ≫ (G.commShiftIso n).hom.app A = e ≫ μ⟦n⟧') :
    ∃ l : M ⟶ G.obj (A⟦-n⟧),
      l ≫ G.map (ζ⟦-n⟧' ≫ (shiftFunctorCompIsoId C n (-n) (add_neg_cancel n)).hom.app A) = μ := by
  have h' : μ⟦n⟧' = CategoryTheory.inv e ≫ N ≫ G.map ζ ≫ (G.commShiftIso n).hom.app A := by
    rw [h, IsIso.inv_hom_id_assoc]
  refine ⟨(shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).inv.app M ≫
    (CategoryTheory.inv e ≫ N)⟦-n⟧' ≫ (G.commShiftIso (-n)).inv.app A, ?_⟩
  have hn := (shiftFunctorCompIsoId D n (-n) (add_neg_cancel n)).hom.naturality μ
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [G.map_comp, G.map_shiftFunctorCompIsoId_hom_app]
  simp only [Category.assoc]
  rw [← G.commShiftIso_inv_naturality_assoc, Iso.inv_hom_id_app_assoc,
    ← (shiftFunctor D (-n)).map_comp_assoc, ← (shiftFunctor D (-n)).map_comp_assoc]
  simp only [Category.assoc]
  rw [← h', hn, Iso.inv_hom_id_app_assoc]

end CategoryTheory.Functor

namespace AlgebraicGeometry.DeRhamLerayHirsch

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)

/-- **The untwisted map `θ = ξ'[-n] : Ω^•_{X/S}[-n] ⟶ Ω^•_{X/S}`** of a class
`ξ ∈ H^n_{dR}(X/S)`, for `ξ' : Ω^•_{X/S} ⟶ Ω^•_{X/S}[n]` the morphism of Remark 0FU7. -/
abbrev classUntwisted (p : X ⟶ S) (n : ℤ)
    (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras p)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) n) :
    (deRhamObject p)⟦-n⟧ ⟶ deRhamObject p :=
  (classMorphism p n ξ)⟦-n⟧' ≫ (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app _

variable (d : ℕ)
  (ξ : SheafOfModules.deRhamCohomology (Scheme.Hom.deRhamAlgebras (f ≫ g))
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras (f ≫ g))) (d : ℤ)) (r : ℕ)

/-- The identification `id : K ⟶ M[d]` of Remark 0FUN is an isomorphism. -/
instance isIso_powerSummandsInitIso : IsIso (powerSummandsInitIso g d r) := by
  refine ⟨biproduct.lift fun t =>
      (biproduct.π (fun t : Fin (r - 1) => (deRhamObject g)⟦-((d * ((t : ℕ) + 1) : ℕ) : ℤ)⟧)
        t)⟦(d : ℤ)⟧' ≫
      (shiftFunctorAdd' _ (-((d * ((t : ℕ) + 1) : ℕ) : ℤ)) (d : ℤ) (-((d * (t : ℕ) : ℕ) : ℤ))
        (by push_cast; ring)).inv.app (deRhamObject g), ?_, ?_⟩
  · refine biproduct.hom_ext' _ _ fun s => biproduct.hom_ext _ _ fun t => ?_
    simp only [powerSummandsInitIso, biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π,
      Category.id_comp]
    rw [← Functor.map_comp_assoc]
    by_cases hst : s = t
    · subst hst
      rw [biproduct.ι_π_self, CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app,
        biproduct.ι_π_self]
    · rw [biproduct.ι_π_ne _ hst, Functor.map_zero, Limits.zero_comp, Limits.comp_zero,
        biproduct.ι_π_ne _ hst]
  · rw [powerSummandsInitIso, biproduct.lift_desc]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
    rw [← Functor.map_sum, biproduct.total, CategoryTheory.Functor.map_id]

/-- **`ξ̃|_M` factors through `Rf_*θ`**: by the square of Remark 0FUN,
`(ξ̃|_M)[d] = (Rf_*ξ' ∘ ξ̃|_K) ∘ id⁻¹`, so that `ξ̃|_M = Rf_*θ ∘ λ` for
`λ = (ξ̃|_K ∘ id⁻¹)[-d] : M ⟶ Rf_*(Ω^•_{X/S}[-d])`. -/
theorem exists_comp_map_classUntwisted_eq :
    ∃ l : powerSummandsTail g d r ⟶
        (relativeDirectImage f g).obj ((deRhamObject (f ≫ g))⟦-(d : ℤ)⟧),
      l ≫ (relativeDirectImage f g).map (classUntwisted (f ≫ g) d ξ) =
        powerSummandsTailι g d r ≫ lerayHirschPowerMorphism f g d ξ r :=
  (relativeDirectImage f g).exists_comp_map_untwist_eq (d : ℤ) (classMorphism (f ≫ g) d ξ)
    (powerSummandsTailι g d r ≫ lerayHirschPowerMorphism f g d ξ r)
    (powerSummandsInitι g d r ≫ lerayHirschPowerMorphism f g d ξ r)
    (powerSummandsInitIso g d r)
    ((Category.assoc _ _ _).trans (lerayHirschPowerMorphism_comp_classDirectImageEndo f g d ξ r))

/-- **The section of `c ⊕ Rf_*θ`.** If `ξ̃` is an isomorphism and `r ≥ 1`, there are
`τ : Rf_*Ω^•_{X/S} ⟶ Ω^•_{Y/S}` and `ν : Rf_*Ω^•_{X/S} ⟶ Rf_*(Ω^•_{X/S}[-d])` with `c ≫ τ = 𝟙`,
`c ≫ ν = 0` and `τ ≫ c + ν ≫ Rf_*θ = 𝟙`, for `c` the canonical map and `θ` the untwisted map of
`ξ`. -/
theorem exists_section_of_isIso_lerayHirschPowerMorphism (hr : 0 < r)
    [IsIso (lerayHirschPowerMorphism f g d ξ r)] :
    ∃ (τ : (relativeDirectImage f g).obj (deRhamObject (f ≫ g)) ⟶ deRhamObject g)
      (ν : (relativeDirectImage f g).obj (deRhamObject (f ≫ g)) ⟶
        (relativeDirectImage f g).obj ((deRhamObject (f ≫ g))⟦-(d : ℤ)⟧)),
      deRhamDirectImageMap f g ≫ τ = 𝟙 _ ∧ deRhamDirectImageMap f g ≫ ν = 0 ∧
        τ ≫ deRhamDirectImageMap f g +
          ν ≫ (relativeDirectImage f g).map (classUntwisted (f ≫ g) d ξ) = 𝟙 _ := by
  have := isIso_biprodDesc_of_isIso_lerayHirschPowerMorphism f g d ξ r hr
  obtain ⟨l, hl⟩ := exists_comp_map_classUntwisted_eq f g d ξ r
  exact Limits.exists_retraction_and_section_of_isIso_biprod_desc _ _ _ l hl

end AlgebraicGeometry.DeRhamLerayHirsch

end
