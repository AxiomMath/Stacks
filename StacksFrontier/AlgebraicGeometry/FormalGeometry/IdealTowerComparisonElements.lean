module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerThickenings
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The comparison map of a tower of thickenings, on elements

Let `X` be a scheme, `J₀ ≥ J₁ ≥ ⋯` a decreasing tower of quasi-coherent ideal sheaves with closed
subschemes `Qₙ`, and `ℱ` a quasi-coherent `𝒪_X`-module. The comparison map
`Hⁱ(X, ℱ) ⟶ lim Hⁱ(Qₙ, ℱₙ)` of `Stacks.Algebraization.IdealTower.comparison` is an isomorphism as
soon as the maps `Hⁱ(X, ℱ) ⟶ Hⁱ(X, ιₙ_* ℱₙ)` induced by the restrictions are jointly injective and
every compatible family of elements of the groups `Hⁱ(X, ιₙ_* ℱₙ)` comes from an element of
`Hⁱ(X, ℱ)`.

## Main results

* `Stacks.Algebraization.IdealTower.comparison_eq_ambientComparison_comp`: the comparison map is
  the comparison map on the ambient scheme followed by the identification of the two towers.
* `Stacks.Algebraization.IdealTower.isIso_comparison_of_elements`: the elementwise criterion.
* `Stacks.Algebraization.IdealTower.isIso_comparison_of_elements_mul`: the same, along the
  cofinal subtower of the levels `N k`.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.Algebraization.IdealTower

variable {X : Scheme.{u}} (J : ℕ → X.IdealSheafData) (hJ : ∀ n, J (n + 1) ≤ J n)
  (F : X.Modules) [F.IsQuasicoherent] (i : ℕ)

/-- The comparison map is the comparison map on the ambient scheme followed by the isomorphism of
limits induced by the identification of the two cohomology towers. -/
theorem comparison_eq_ambientComparison_comp :
    comparison J hJ F i =
      ambientComparison J hJ F i ≫ (HasLimit.isoOfNatIso (cohomologyTowerIso J hJ F i)).hom := by
  refine limit.hom_ext fun n => ?_
  rw [comparison_π, Category.assoc, HasLimit.isoOfNatIso_hom_π, ambientComparison_π_assoc]
  rfl

/-- **The elementwise criterion for the comparison map to be an isomorphism.** The comparison
map `Hⁱ(X, ℱ) ⟶ lim Hⁱ(Qₙ, ℱₙ)` is an isomorphism if the maps `Hⁱ(X, ℱ) ⟶ Hⁱ(X, ιₙ_* ℱₙ)` are
jointly injective and every compatible family of elements of the `Hⁱ(X, ιₙ_* ℱₙ)` comes from an
element of `Hⁱ(X, ℱ)`. -/
theorem isIso_comparison_of_elements
    (hinj : ∀ x : Hgroup X.ringCatSheaf ⊤ i F,
      (∀ n : ℕ, (Hfunctor X.ringCatSheaf ⊤ i).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (ι J n)).unit.app F) x = 0) → x = 0)
    (hsurj : ∀ t : ∀ n : ℕ, Hgroup X.ringCatSheaf ⊤ i ((system J hJ F).obj (op n)),
      (∀ (n m : ℕ) (h : n ≤ m),
        (Hfunctor X.ringCatSheaf ⊤ i).map ((system J hJ F).map (homOfLE h).op) (t m) = t n) →
      ∃ x : Hgroup X.ringCatSheaf ⊤ i F, ∀ n : ℕ, (Hfunctor X.ringCatSheaf ⊤ i).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (ι J n)).unit.app F) x = t n) :
    IsIso (comparison J hJ F i) := by
  rw [comparison_eq_ambientComparison_comp]
  suffices IsIso (ambientComparison J hJ F i) from inferInstance
  have hπ : ∀ (n : ℕ) (x : Hgroup X.ringCatSheaf ⊤ i F),
      limit.π (ambientCohomologyTower J hJ F i) (op n) (ambientComparison J hJ F i x) =
        (Hfunctor X.ringCatSheaf ⊤ i).map
          ((Scheme.Modules.pullbackPushforwardAdjunction (ι J n)).unit.app F) x := fun n x => by
    rw [← ConcreteCategory.comp_apply, ambientComparison_π]
    rfl
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨?_, fun t => ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => hinj x fun n => ?_
    rw [← hπ, hx, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := hsurj (fun n => limit.π (ambientCohomologyTower J hJ F i) (op n) t)
      fun n m h => by
        show (limit.π (ambientCohomologyTower J hJ F i) (op m) ≫
          (ambientCohomologyTower J hJ F i).map (homOfLE h).op) t = _
        rw [limit.w]
    refine ⟨x, Concrete.limit_ext _ _ _ fun n => ?_⟩
    obtain ⟨n⟩ := n
    rw [hπ, hx]

/-- **The elementwise criterion along a cofinal subtower**: it suffices that every compatible
family is matched, by an element of `Hⁱ(X, ℱ)`, along the levels `N k`. -/
theorem isIso_comparison_of_elements_mul (N : ℕ) (hN : 1 ≤ N)
    (hinj : ∀ x : Hgroup X.ringCatSheaf ⊤ i F,
      (∀ n : ℕ, (Hfunctor X.ringCatSheaf ⊤ i).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (ι J n)).unit.app F) x = 0) → x = 0)
    (hsurj : ∀ t : ∀ n : ℕ, Hgroup X.ringCatSheaf ⊤ i ((system J hJ F).obj (op n)),
      (∀ (n m : ℕ) (h : n ≤ m),
        (Hfunctor X.ringCatSheaf ⊤ i).map ((system J hJ F).map (homOfLE h).op) (t m) = t n) →
      ∃ x : Hgroup X.ringCatSheaf ⊤ i F, ∀ k : ℕ, (Hfunctor X.ringCatSheaf ⊤ i).map
        ((Scheme.Modules.pullbackPushforwardAdjunction (ι J (N * k))).unit.app F) x = t (N * k)) :
    IsIso (comparison J hJ F i) := by
  refine isIso_comparison_of_elements J hJ F i hinj fun t ht => ?_
  obtain ⟨x, hx⟩ := hsurj t ht
  refine ⟨x, fun m => ?_⟩
  have hm : m ≤ N * m := Nat.le_mul_of_pos_left m hN
  have hw := ConcreteCategory.congr_hom
    (((Hfunctor X.ringCatSheaf ⊤ i).mapCone (cone J hJ F)).w (homOfLE hm).op) x
  rw [← ht _ _ hm, ← hx m]
  exact hw.symm.trans (ConcreteCategory.comp_apply _ _ x)

end Stacks.Algebraization.IdealTower

end
