module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyShiftedSingleCochains

/-!
# Čech classes on a covering whose Čech class map is bijective

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings, `ℱ` a sheaf of
`𝒪_X`-modules and `𝒰` an open covering of `X`. When the comparison of the total Čech complex of
`ℱ[-a]` for `𝒰` with derived global sections is bijective on cohomology — for instance when the
finite intersections of `𝒰` are acyclic for `ℱ`, by [Stacks, Tag 0FLH] — the explicit Čech
cocycles *of the covering `𝒰` itself* compute the cohomology of `ℱ[-a]`: every class is the class
of a Čech cocycle on `𝒰`, and a cocycle on `𝒰` with vanishing class is a Čech coboundary on `𝒰`.
These are the forms of [Stacks, Tag 01XD] used to compute cohomology by a fixed covering, as in
the proof of [Stacks, Tag 0BED]; the corresponding statements in
`HypercohomologyShiftedSingleCochains.lean` pass to a refinement.

## Main results

* `Stacks.Cech.Hypercohomology.exists_cechCocycleClassAt_eq_of_surjective`: every class is the
  class of a Čech cocycle on `𝒰`.
* `Stacks.Cech.Hypercohomology.exists_cechD_eq_of_cechCocycleClassAt_eq_zero`: a cocycle of
  positive degree with vanishing class is a Čech coboundary on `𝒰`.
* `Stacks.Cech.Hypercohomology.eq_zero_of_cechCocycleClassAt_eq_zero`: a `0`-cocycle with
  vanishing class is zero.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 0FLH](https://stacks.math.columbia.edu/tag/0FLH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing abSections)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
attribute [local implicit_reducible] CechCochains.Cochain

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (F : SheafOfModules.{u} (ringSheaf O))
  (a : ℤ)

/-- The cochain attached to an explicit Čech cochain determines it. -/
private theorem cochainOfAt_injective {p : ℕ} {c c' : CechCochains.Cochain U (abSections F) p}
    (h : cochainOfAt U hU F a c = cochainOfAt U hU F a c') : c = c' :=
  cochainOfAtTo_injective U hU F a _ rfl h

/-- Every morphism out of the ring into the total Čech complex of `ℱ[-a]` in degree `p + a` is
the cochain attached to an explicit Čech cochain. -/
private theorem exists_cochainOfAt_eq {p : ℕ}
    (z : unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((cech O U hU).obj (singlePlus O F a).obj).X ((p : ℤ) + a)) :
    ∃ c : CechCochains.Cochain U (abSections F) p, cochainOfAt U hU F a c = z :=
  exists_cochainOfAtTo_eq U hU F a _ rfl z

/-- **Every class of `H^{p+a}(X, ℱ[-a])` is the class of a Čech cocycle on `𝒰`**, when the Čech
class map of `𝒰` is surjective in that degree. -/
theorem exists_cechCocycleClassAt_eq_of_surjective (p : ℕ)
    (hs : Function.Surjective (cechClass O U hU (singlePlus O F a) ((p : ℤ) + a)))
    (x : hypercohomology O (singlePlus O F a) ((p : ℤ) + a)) :
    ∃ (c : CechCochains.Cochain U (abSections F) p)
      (hc : CechCochains.cechD U (abSections F) p c = 0), cechCocycleClassAt U hU F a c hc = x := by
  obtain ⟨z, rfl⟩ := hs x
  obtain ⟨zz, hzz, hz⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O U hU).obj (singlePlus O F a).obj) ((p : ℤ) + a) _
    (CochainComplex.next ℤ _) (toMor z)
  obtain ⟨c, hc'⟩ := exists_cochainOfAt_eq U hU F a zz
  have hcd : CechCochains.cechD U (abSections F) p c = 0 := by
    refine cochainOfAt_injective U hU F a ?_
    rw [cochainOfAt_zero, ← cochainOfAt_d]
    rw [hc']
    have e : (((p + 1 : ℕ) : ℤ) + a) = (p : ℤ) + a + 1 := by push_cast; ring
    rw [e]
    exact hzz
  refine ⟨c, hcd, ?_⟩
  have e : cocycleClass ((p : ℤ) + a) (cochainOfAt U hU F a c)
      (cochainOfAt_d_eq_zero U hU F a c hcd) = toMor z :=
    (cocycleClass_congr _ hc' _ _).trans hz
  have e' : (cocycleClass ((p : ℤ) + a) (cochainOfAt U hU F a c)
      (cochainOfAt_d_eq_zero U hU F a c hcd)) (1 : SectionRing (ringSheaf O) ⊤) = z := by
    rw [e]
    exact toMor_apply_one z
  exact congrArg (cechClass O U hU (singlePlus O F a) ((p : ℤ) + a)) e'

/-- The cocycle class of an explicit cocycle vanishes as soon as its class in hypercohomology
does, when the Čech class map is injective. -/
theorem cocycleClass_eq_zero_of_cechCocycleClassAt_eq_zero {p : ℕ}
    (hi : Function.Injective (cechClass O U hU (singlePlus O F a) ((p : ℤ) + a)))
    (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0)
    (h0 : cechCocycleClassAt U hU F a c hc = 0) :
    cocycleClass ((p : ℤ) + a) (cochainOfAt U hU F a c) (cochainOfAt_d_eq_zero U hU F a c hc) =
      0 := by
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  refine hi (h0.trans ?_)
  exact (map_zero _).symm

/-- **A Čech cocycle of positive degree on `𝒰` with vanishing class is a Čech coboundary on
`𝒰`**, when the Čech class map of `𝒰` is injective in that degree. -/
theorem exists_cechD_eq_of_cechCocycleClassAt_eq_zero {q : ℕ}
    (hi : Function.Injective (cechClass O U hU (singlePlus O F a) (((q + 1 : ℕ) : ℤ) + a)))
    (c : CechCochains.Cochain U (abSections F) (q + 1))
    (hc : CechCochains.cechD U (abSections F) (q + 1) c = 0)
    (h0 : cechCocycleClassAt U hU F a c hc = 0) :
    ∃ t : CechCochains.Cochain U (abSections F) q, CechCochains.cechD U (abSections F) q t = c := by
  have hcl := cocycleClass_eq_zero_of_cechCocycleClassAt_eq_zero U hU F a hi c hc h0
  have hi' : (up ℤ).prev (((q + 1 : ℕ) : ℤ) + a) = (q : ℤ) + a := by
    rw [CochainComplex.prev]; push_cast; ring
  obtain ⟨A', π, hπ, x₁, hx₁⟩ :=
    (HomologicalComplex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _ _ _ hi'
      (CochainComplex.next ℤ _) _ _).1 hcl
  obtain ⟨t, ht'⟩ := exists_cochainOfAt_eq U hU F a (Projective.factorThru (𝟙 _) π ≫ x₁)
  refine ⟨t, cochainOfAt_injective U hU F a ?_⟩
  rw [← cochainOfAt_d, ht', Category.assoc, ← hx₁, ← Category.assoc,
    Projective.factorThru_comp, Category.id_comp]

/-- **A Čech `0`-cocycle on `𝒰` with vanishing class is zero**, when the Čech class map of `𝒰` is
injective in degree `a`. -/
theorem eq_zero_of_cechCocycleClassAt_eq_zero
    (hi : Function.Injective (cechClass O U hU (singlePlus O F a) (((0 : ℕ) : ℤ) + a)))
    (c : CechCochains.Cochain U (abSections F) 0)
    (hc : CechCochains.cechD U (abSections F) 0 c = 0)
    (h0 : cechCocycleClassAt U hU F a c hc = 0) : c = 0 := by
  have hcl := cocycleClass_eq_zero_of_cechCocycleClassAt_eq_zero U hU F a hi c hc h0
  have hi' : (up ℤ).prev (((0 : ℕ) : ℤ) + a) = a - 1 := by
    rw [CochainComplex.prev]; push_cast; ring
  obtain ⟨A', π, hπ, x₁, hx₁⟩ :=
    (HomologicalComplex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _ _ _ hi'
      (CochainComplex.next ℤ _) _ _).1 hcl
  have hz : x₁ = 0 := (isZero_cech_X O U hU (singlePlus O F a).obj a (a - 1)
    (by omega)).eq_of_tgt _ _
  rw [hz, Limits.zero_comp] at hx₁
  have hπ0 : cochainOfAt U hU F a c = 0 := (cancel_epi π).1 (hx₁.trans (comp_zero).symm)
  exact cochainOfAt_injective U hU F a (hπ0.trans (cochainOfAt_zero U hU F a).symm)

end Stacks.Cech.Hypercohomology

end
