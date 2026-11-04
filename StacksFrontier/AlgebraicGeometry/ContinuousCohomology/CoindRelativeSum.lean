module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafCoindCounit

/-!
# The relative sum map `Coind_{H'} M ⟶ Coind_H M` for open subgroups `H' ≤ H`

Let `G` be a compact group, `H' ≤ H` open subgroups and `M` a finite `R`-module with a continuous
`G`-action. Summing over the fibres of `G ⧸ H' → G ⧸ H` gives a map of modules
`Σ_{H'/H} : Coind_{H'} M ⟶ Coind_H M`, `(Σ_{H'/H} f)(x) = Σ_{y ↦ x} f(y)`. It is `G`-equivariant,
surjective, and followed by the sum map `Σ_H : Coind_H M ⟶ M` it is the sum map `Σ_{H'}`.

This factorization `Σ_{H'} = Σ_H ∘ Σ_{H'/H}` is how the coeffaceability of the functors
`H_c^{2-i}(X_k̄, ℱ_ρ)` (Stacks 03VM) is reduced to modules coinduced from a subgroup acting
trivially: a functor kills `Σ_{H'}` as soon as it kills `Σ_{H'/H}`.

## Main definitions

* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoindRelSum`: the relative sum map.

## Main results

* `Stacks.GroupCohomology.finiteTypeContinuousModuleCoindRelSum_comp_coindSum`:
  `Σ_{H'/H} ≫ Σ_H = Σ_{H'}`.
* `Stacks.GroupCohomology.epi_finiteTypeContinuousModuleCoindRelSum`: it is an epimorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace Stacks.ContinuousCohomology

variable (R : Type u) [Ring R] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {H' H : OpenSubgroup G} (h : H' ≤ H)

/-- The projection `G ⧸ H' → G ⧸ H` for open subgroups `H' ≤ H`. -/
abbrev coindRelProj : G ⧸ (H' : Subgroup G) → G ⧸ (H : Subgroup G) :=
  Subgroup.quotientMapOfLE (show (H' : Subgroup G) ≤ H from h)

omit [IsTopologicalGroup G] [CompactSpace G] in
/-- The projection `G ⧸ H' → G ⧸ H` is `G`-equivariant. -/
theorem coindRelProj_smul (g : G) (y : G ⧸ (H' : Subgroup G)) :
    coindRelProj h (g • y) = g • coindRelProj h y := by
  induction y using QuotientGroup.induction_on with
  | H z => rfl

/-- The sum over the fibres of `G ⧸ H' → G ⧸ H`, `f ↦ Σ_y Pi.single (y H) (f y)`, as a linear
map. -/
def coindRelSumLinearMap (A : Type*) [AddCommGroup A] [Module R A] :
    (G ⧸ (H' : Subgroup G) → A) →ₗ[R] (G ⧸ (H : Subgroup G) → A) :=
  letI : Fintype (G ⧸ (H' : Subgroup G)) := Fintype.ofFinite _
  letI : DecidableEq (G ⧸ (H : Subgroup G)) := Classical.decEq _
  ∑ y, (LinearMap.single R (fun _ ↦ A) (coindRelProj h y)).comp (LinearMap.proj y)

/-- The relative sum of `f` is `Σ_y Pi.single (y H) (f y)`. -/
theorem coindRelSumLinearMap_apply (A : Type*) [AddCommGroup A] [Module R A]
    (f : G ⧸ (H' : Subgroup G) → A) :
    letI : Fintype (G ⧸ (H' : Subgroup G)) := Fintype.ofFinite _
    letI : DecidableEq (G ⧸ (H : Subgroup G)) := Classical.decEq _
    coindRelSumLinearMap R h A f = ∑ y, Pi.single (coindRelProj h y) (f y) := by
  unfold coindRelSumLinearMap
  rw [LinearMap.sum_apply]
  rfl

/-- The value of the relative sum of `f` at `x` is the sum of `f` over the fibre over `x`. -/
theorem coindRelSumLinearMap_apply_apply (A : Type*) [AddCommGroup A] [Module R A]
    (f : G ⧸ (H' : Subgroup G) → A) (x : G ⧸ (H : Subgroup G)) :
    letI : Fintype (G ⧸ (H' : Subgroup G)) := Fintype.ofFinite _
    letI : DecidableEq (G ⧸ (H : Subgroup G)) := Classical.decEq _
    coindRelSumLinearMap R h A f x =
      ∑ y ∈ Finset.univ.filter (fun y ↦ coindRelProj h y = x), f y := by
  let : DecidableEq (G ⧸ (H : Subgroup G)) := Classical.decEq _
  let : Fintype (G ⧸ (H' : Subgroup G)) := Fintype.ofFinite _
  rw [coindRelSumLinearMap_apply, Finset.sum_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  by_cases hy : coindRelProj h y = x
  · subst hy
    rw [ite_eq_left rfl]
    exact Pi.single_eq_same _ _
  · rw [ite_eq_right hy]
    exact Pi.single_eq_of_ne (fun e ↦ hy e.symm) _

/-- Summing the relative sum over `G ⧸ H` is summing over `G ⧸ H'`. -/
theorem finsum_coindRelSumLinearMap (A : Type*) [AddCommGroup A] [Module R A]
    (f : G ⧸ (H' : Subgroup G) → A) :
    ∑ᶠ x, coindRelSumLinearMap R h A f x = ∑ᶠ y, f y := by
  let : DecidableEq (G ⧸ (H : Subgroup G)) := Classical.decEq _
  let : Fintype (G ⧸ (H' : Subgroup G)) := Fintype.ofFinite _
  let : Fintype (G ⧸ (H : Subgroup G)) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [coindRelSumLinearMap_apply_apply]
  exact Finset.sum_fiberwise _ _ _

/-- The relative sum commutes with translating functions by `g` and applying an additive map. -/
theorem coindRelSumLinearMap_translate (A : Type*) [AddCommGroup A] [Module R A] (g : G)
    (φ : A →ₗ[R] A) (f : G ⧸ (H' : Subgroup G) → A) (x : G ⧸ (H : Subgroup G)) :
    coindRelSumLinearMap R h A (fun y ↦ φ (f (g⁻¹ • y))) x =
      φ (coindRelSumLinearMap R h A f (g⁻¹ • x)) := by
  let : DecidableEq (G ⧸ (H : Subgroup G)) := Classical.decEq _
  let : Fintype (G ⧸ (H' : Subgroup G)) := Fintype.ofFinite _
  rw [coindRelSumLinearMap_apply_apply, coindRelSumLinearMap_apply_apply, map_sum]
  refine Finset.sum_equiv (MulAction.toPerm g⁻¹) (fun y ↦ ?_) fun _ _ ↦ rfl
  simp [coindRelProj_smul]

/-- **The relative sum map `Coind_{H'} M ⟶ Coind_H M`**, `(Σ_{H'/H} f)(x) = Σ_{y ↦ x} f(y)`. -/
def coindRelSum (M : Stacks.Injectives.ContinuousModule.{u, v, max u v} R G) :
    (coind.{u, v, 0} R H').obj M ⟶ (coind.{u, v, 0} R H).obj M :=
  (Stacks.GroupCohomology.homEquiv R G ((coind.{u, v, 0} R H').obj M)
      ((coind.{u, v, 0} R H).obj M)).symm
    ⟨coindRelSumLinearMap R h M.obj.obj.V, fun g f ↦ by
      change coindRelSumLinearMap R h M.obj.obj.V (fun y ↦ (M.obj.obj.ρ g).hom (f (g⁻¹ • y))) =
        fun x ↦ (M.obj.obj.ρ g).hom (coindRelSumLinearMap R h M.obj.obj.V f (g⁻¹ • x))
      funext x
      exact coindRelSumLinearMap_translate R h _ g (M.obj.obj.ρ g).hom f x⟩

/-- The underlying map of `coindRelSum` is `coindRelSumLinearMap`. -/
theorem coindRelSum_apply (M : Stacks.Injectives.ContinuousModule.{u, v, max u v} R G)
    (f : G ⧸ (H' : Subgroup G) → M.obj.obj.V) :
    (coindRelSum R h M).hom.hom.hom.hom f = coindRelSumLinearMap R h M.obj.obj.V f :=
  rfl

/-- **`Σ_{H'/H} ≫ Σ_H = Σ_{H'}`**: summing over the fibres and then over `G ⧸ H` is summing over
`G ⧸ H'`. -/
theorem coindRelSum_comp_coindSum (M : Stacks.Injectives.ContinuousModule.{u, v, max u v} R G) :
    coindRelSum R h M ≫ coindSum.{u, v, 0} R H M = coindSum.{u, v, 0} R H' M := by
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  apply Action.hom_ext
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun f ↦ ?_
  change (coindSum.{u, v, 0} R H M).hom.hom.hom.hom (coindRelSumLinearMap R h M.obj.obj.V f) =
    (coindSum.{u, v, 0} R H' M).hom.hom.hom.hom f
  exact (coindSum_apply.{u, v, 0} R H M _).trans ((finsum_coindRelSumLinearMap R h _ f).trans
    (coindSum_apply.{u, v, 0} R H' M f).symm)

/-- The relative sum map is surjective: a function on `G ⧸ H` is the relative sum of its
transport along a section of `G ⧸ H' → G ⧸ H`. -/
theorem surjective_coindRelSumLinearMap (A : Type*) [AddCommGroup A] [Module R A] :
    Function.Surjective (coindRelSumLinearMap R h A) := by
  let : DecidableEq (G ⧸ (H : Subgroup G)) := Classical.decEq _
  let : DecidableEq (G ⧸ (H' : Subgroup G)) := Classical.decEq _
  let : Fintype (G ⧸ (H : Subgroup G)) := Fintype.ofFinite _
  intro F
  let s : G ⧸ (H : Subgroup G) → G ⧸ (H' : Subgroup G) := fun x ↦ (x.out : G)
  have hs : ∀ x, coindRelProj h (s x) = x := fun x ↦ Quotient.out_eq' x
  refine ⟨∑ x, Pi.single (s x) (F x), ?_⟩
  rw [map_sum]
  have h1 : ∀ x, coindRelSumLinearMap R h A (Pi.single (s x) (F x)) = Pi.single x (F x) := by
    intro x
    let : Fintype (G ⧸ (H' : Subgroup G)) := Fintype.ofFinite _
    rw [coindRelSumLinearMap_apply, Finset.sum_eq_single (s x)]
    · rw [Pi.single_eq_same, hs]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, Pi.single_zero]
    · exact fun hx ↦ (hx (Finset.mem_univ _)).elim
  simpa only [h1] using Finset.univ_sum_single F

/-- **The relative sum map is an epimorphism.** -/
instance epi_coindRelSum (M : Stacks.Injectives.ContinuousModule.{u, v, max u v} R G) :
    Epi (coindRelSum R h M) :=
  (epi_iff_surjective R _).2 (surjective_coindRelSumLinearMap R h _)

end Stacks.ContinuousCohomology

namespace Stacks.GroupCohomology

open Stacks.ContinuousCohomology

variable (R : Type u) [Ring R] {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {H' H : OpenSubgroup G} (h : H' ≤ H)

/-- **The relative sum map `Coind_{H'} M ⟶ Coind_H M`** of finite `R`-modules with a continuous
`G`-action, `(Σ_{H'/H} f)(x) = Σ_{y ↦ x} f(y)`. -/
def finiteTypeContinuousModuleCoindRelSum (M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    (finiteTypeContinuousModuleCoind R H').obj M ⟶ (finiteTypeContinuousModuleCoind R H).obj M :=
  ObjectProperty.homMk (coindRelSum R h M.obj)

/-- **`Σ_{H'/H} ≫ Σ_H = Σ_{H'}`.** -/
theorem finiteTypeContinuousModuleCoindRelSum_comp_coindSum
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    finiteTypeContinuousModuleCoindRelSum R h M ≫ finiteTypeContinuousModuleCoindSum R H M =
      finiteTypeContinuousModuleCoindSum R H' M :=
  ObjectProperty.hom_ext _ (coindRelSum_comp_coindSum R h M.obj)

/-- **The relative sum map is an epimorphism.** -/
instance epi_finiteTypeContinuousModuleCoindRelSum
    (M : FiniteTypeContinuousModule.{u, v, max u v} R G) :
    Epi (finiteTypeContinuousModuleCoindRelSum R h M) :=
  (finiteTypeContinuousModuleι.{u, v, max u v} R G).epi_of_epi_map
    (inferInstanceAs (Epi (coindRelSum R h M.obj)))

end Stacks.GroupCohomology
