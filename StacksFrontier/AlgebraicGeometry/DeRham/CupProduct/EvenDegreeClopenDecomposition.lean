module

public import StacksFrontier.AlgebraicGeometry.DeRham.ClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.PullbackEvenDegreeRing

/-!
# Even-degree de Rham cohomology along a decomposition into open and closed pieces

Let `p : X ⟶ B` be a morphism of schemes and let `X` be the disjoint union of finitely many open
and closed subschemes `U i`. The pullbacks along the inclusions identify

`⨁_{n ≥ 0} H^{2n}_{dR}(X/B) = ∏ᵢ ⨁_{n ≥ 0} H^{2n}_{dR}(U i/B)`

as graded rings: the map is bijective, and a class whose restrictions to all the pieces are
homogeneous of degree `n` is homogeneous of degree `n`. This is condition (2) of Weil Cohomology
Theories, Section 45.12 for the functor `A(X) = ⨁_i H^{2i}_{dR}(X/B)` of the proof of Lemma 0FW9,
in the two forms `Stacks.WeilCohomology.SourceChernSetup` asks for
(`bijective_pull_clopenSubobject`, `mem_grade_of_pull_clopenSubobject`). It follows degreewise from
`Stacks.DeRhamClopen.bijective_deRhamCohomologyPullback`.

## Main results

* `Stacks.DeRhamClopen.bijective_deRhamPullbackSquare`: the degreewise bijection, in the
  realization by modules carrying the cup product.
* `Stacks.DeRhamClopen.bijective_evenDeRhamPullback`: the bijection of even-degree rings.
* `Stacks.DeRhamClopen.mem_evenDeRhamGrade_of_evenDeRhamPullback`: the splitting is graded.

## References

* [Stacks Project, Tag 0FW9](https://stacks.math.columbia.edu/tag/0FW9)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.DeRhamBaseChange

universe u

namespace DirectSum

variable {κ : Type*} [DecidableEq κ] {M : κ → Type*} [∀ k, AddCommGroup (M k)] {J : Type*}
  {N : J → κ → Type*} [∀ j k, AddCommGroup (N j k)]
  (F : ∀ j, (⨁ k, M k) →+ ⨁ k, N j k) (φ : ∀ j k, M k →+ N j k)
  (hF : ∀ j x k, F j x k = φ j k (x k))

include hF in
/-- **A finite family of maps of direct sums acting componentwise is jointly bijective once it is
so in every component**: if `F j` acts on the `k`-th summand by `φ j k` and every
`z ↦ (φ j k z)_j` is bijective, then so is `x ↦ (F j x)_j`. -/
theorem bijective_pi_of_bijective_apply [Finite J]
    (hφ : ∀ k, Function.Bijective fun z : M k => fun j => φ j k z) :
    Function.Bijective fun x : ⨁ k, M k => fun j => F j x := by
  classical
  have := Fintype.ofFinite J
  refine ⟨fun x y hxy => DirectSum.ext fun k => (hφ k).1 (funext fun j => ?_), fun y => ?_⟩
  · show φ j k (x k) = φ j k (y k)
    rw [← hF, ← hF]
    exact congrArg (fun z : ⨁ k, N j k => z k) (congrFun hxy j)
  · let T : Finset κ := (Finset.univ : Finset J).biUnion fun j => DFinsupp.support (y j)
    let g : ∀ k, M k := fun k => ((hφ k).2 fun j => y j k).choose
    refine ⟨(DFinsupp.mk T fun k => g k : ⨁ k, M k), funext fun j => DirectSum.ext fun k => ?_⟩
    rw [hF]
    show φ j k (DFinsupp.mk T (fun k => g k) k) = y j k
    rw [DFinsupp.mk_apply]
    by_cases hk : k ∈ T
    · rw [dif_pos hk]
      exact congrFun ((hφ k).2 fun j => y j k).choose_spec j
    · rw [dif_neg hk, map_zero]
      exact (DFinsupp.notMem_support_iff.mp fun h =>
        hk (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, h⟩)).symm

include hF in
/-- **A family of maps of direct sums acting componentwise and jointly injectively in every
component reflects homogeneity**: if every `F j x` lies in the `n`-th summand, so does `x`. -/
theorem mem_range_of_of_apply
    (hφ : ∀ k, Function.Injective fun z : M k => fun j => φ j k z) (x : ⨁ k, M k) (n : κ)
    (h : ∀ j, F j x ∈ (DirectSum.of (N j) n).range) :
    x ∈ (DirectSum.of M n).range := by
  refine ⟨x n, DirectSum.ext fun k => ?_⟩
  by_cases hk : k = n
  · subst hk
    exact DirectSum.of_eq_same _ _
  · rw [DirectSum.of_eq_of_ne _ _ _ hk]
    refine hφ k (funext fun j => ?_)
    obtain ⟨z, hz⟩ := h j
    show φ j k 0 = φ j k (x k)
    rw [map_zero, ← hF, ← hz, DirectSum.of_eq_of_ne _ _ _ hk]

end DirectSum

namespace Stacks.DeRhamClopen

/-! ### The components of the even-degree pullback -/

section Components

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- **The pullback of even-degree rings acts componentwise**: its `k`-th component is the pullback
of the `k`-th component, in degree `2k`. -/
theorem evenDeRhamPullback_apply_component (x : evenDeRhamRing f) (k : ℕ) :
    evenDeRhamPullback g' f' f g w x k = deRhamPullbackSquare g' f' f g w _ (x k) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => rw [map_zero, DirectSum.zero_apply, DirectSum.zero_apply, map_zero]
  | add x x' hx hx' => rw [map_add, DirectSum.add_apply, hx, hx', DirectSum.add_apply, map_add]
  | of j z =>
    rw [evenDeRhamPullback_of]
    by_cases hj : k = j
    · subst hj
      rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ hj, DirectSum.of_eq_of_ne _ _ _ hj, map_zero]

end Components

/-! ### The decomposition -/

variable {X B : Scheme.{u}} (p : X ⟶ B) {ι : Type} [Finite ι] (U : ι → X.Opens)
  (hU : ∀ i, IsClopen (U i : Set X)) (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
  (hcov : (⨆ i, U i) = ⊤)

include hU hdisj hcov in
/-- **De Rham cohomology along a decomposition into open and closed pieces**, in the realization
by modules carrying the cup product: the pullbacks along the inclusions identify
`H^m_{dR}(X/B)` with `∏ᵢ H^m_{dR}(U i/B)`. -/
theorem bijective_deRhamPullbackSquare (m : ℤ) :
    Function.Bijective fun z : AlgebraicGeometry.SheafOfModules.deRhamCohomology
        (Scheme.Hom.deRhamAlgebras p)
        (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) m =>
      fun i => deRhamPullbackSquare (U i).ι ((U i).ι ≫ p) p (𝟙 B)
        (Category.comp_id _).symm m z := by
  have hX := ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras p)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)) m).inv
  have hP := Function.Bijective.piMap fun i => ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.SheafOfModules.deRhamCohomologyAbelianIsoDeRhamCohomology
      (Scheme.Hom.deRhamAlgebras ((U i).ι ≫ p))
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential
        (Scheme.Hom.deRhamAlgebras ((U i).ι ≫ p))) m).hom
  exact (hP.comp (bijective_deRhamCohomologyPullback p U hU hdisj hcov m)).comp hX

include hU hdisj hcov in
/-- **Even-degree de Rham cohomology along a decomposition into open and closed pieces**
(condition (2) of Weil Cohomology Theories, Section 45.12, for the functor `A` of the proof of
Lemma 0FW9): the pullbacks along the inclusions identify `⨁_n H^{2n}_{dR}(X/B)` with
`∏ᵢ ⨁_n H^{2n}_{dR}(U i/B)`. -/
theorem bijective_evenDeRhamPullback :
    Function.Bijective fun a : evenDeRhamRing p => fun i =>
      evenDeRhamPullback (U i).ι ((U i).ι ≫ p) p (𝟙 B) (Category.comp_id _).symm a :=
  DirectSum.bijective_pi_of_bijective_apply
    (fun i => (evenDeRhamPullback (U i).ι ((U i).ι ≫ p) p (𝟙 B)
      (Category.comp_id _).symm).toAddMonoidHom)
    (fun i k => deRhamPullbackSquare (U i).ι ((U i).ι ≫ p) p (𝟙 B) (Category.comp_id _).symm _)
    (fun i x k => evenDeRhamPullback_apply_component _ _ _ _ _ x k)
    (fun k => bijective_deRhamPullbackSquare p U hU hdisj hcov _)

include hU hdisj hcov in
/-- **The decomposition of even-degree de Rham cohomology along open and closed pieces is
graded**: a class whose restrictions to all the pieces lie in `H^{2n}_{dR}` lies in
`H^{2n}_{dR}`. -/
theorem mem_evenDeRhamGrade_of_evenDeRhamPullback (a : evenDeRhamRing p) (n : ℕ)
    (h : ∀ i, evenDeRhamPullback (U i).ι ((U i).ι ≫ p) p (𝟙 B) (Category.comp_id _).symm a ∈
      AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ n) :
    a ∈ AlgebraicGeometry.SheafOfModules.evenDeRhamGrade _ _ n :=
  DirectSum.mem_range_of_of_apply
    (fun i => (evenDeRhamPullback (U i).ι ((U i).ι ≫ p) p (𝟙 B)
      (Category.comp_id _).symm).toAddMonoidHom)
    (fun i k => deRhamPullbackSquare (U i).ι ((U i).ι ≫ p) p (𝟙 B) (Category.comp_id _).symm _)
    (fun i x k => evenDeRhamPullback_apply_component _ _ _ _ _ x k)
    (fun k => (bijective_deRhamPullbackSquare p U hU hdisj hcov _).1) a n h

end Stacks.DeRhamClopen

end
