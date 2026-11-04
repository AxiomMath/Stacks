module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.ComponentDegreeHom
public import StacksFrontier.AlgebraicGeometry.Curves.Models.AssociatedNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequenceExact
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.PicardGroup.Defs
import StacksCore.Tactic.StacksAttribute

/-!
# The Picard group of a model and the Picard group of its numerical type

In the situation of [Stacks, Tag 0C61] let `T` be the numerical type associated to `X`
([Stacks, Tag 0CA5]), built in
`StacksFrontier/AlgebraicGeometry/Curves/Models/AssociatedNumericalType.lean`.
[Stacks, Tag 0CAC] asserts that there is a canonical map

`Pic(C) ⟶ Pic(T)`

whose kernel is exactly the invertible modules on `C` that are restrictions of invertible modules
`ℒ` on `X` with `deg_{Cᵢ}(ℒ|_{Cᵢ}) = 0` for every `i`.

## Main definitions

* `Stacks.Models.RegularProperModelSituation.specialFiberNormalizedDegree` — the normalized degree
  vector `Pic(X) ⟶ ℤ^{⊕n}`, `ℒ ↦ (deg(ℒ|_{C₁})/w₁, …, deg(ℒ|_{Cₙ})/wₙ)`.
* `Stacks.Models.RegularProperModelSituation.picardNumericalTypeHom` — the canonical map
  `Pic(C) ⟶ Pic(T)`.

## Main results

* `Stacks.Models.RegularProperModelSituation.specialFiberNormalizedDegree_componentPicardHom` —
  the computation of the source's proof: the normalized degree vector of `𝒪_X(Σ aⱼCⱼ)` is the
  image of `a` under the relation map `(aᵢⱼ/wᵢ)` defining `Pic(T)`.
* `Stacks.Models.RegularProperModelSituation.picardNumericalTypeHom_spec` — **[Stacks, Tag 0CAC]**:
  the value of the canonical map on restrictions and its kernel.

## The argument

The source's diagram: the top row `ℤ^{⊕n} ⟶ Pic(X) ⟶ Pic(C) ⟶ 0` is exact by
[Stacks, Tag 0C63] (`Stacks.Models.surjective_genericFiberPicardRestriction`,
`Stacks.Models.genericFiberPicardRestriction_componentPicardHom` and
`Stacks.Models.exact_componentPicardHom_genericFiberPicardRestriction`), the
bottom row `ℤ^{⊕n} ⟶ ℤ^{⊕n} ⟶ Pic(T) ⟶ 0` is the definition of `Pic(T)` ([Stacks, Tag 0C7H]),
and the normalized degree, a homomorphism by [Stacks, Tag 0AYX] and [Stacks, Tag 0C6P], makes the
left square commute because `(Cⱼ · Cᵢ) = (Cᵢ · Cⱼ)`. The induced map on cokernels is the
canonical map. A class `y ∈ Pic(C)` lies in its kernel when a lift `x` has normalized degree in
the image of the relation map, `(aᵢⱼ/wᵢ) b` say; then `x - Σ bⱼ[𝒪_X(Cⱼ)]` is another lift, of
normalized degree, hence degree, zero.

## References

* [Stacks Project, Tag 0CAC](https://stacks.math.columbia.edu/tag/0CAC)
* [Stacks Project, Tag 0C7H](https://stacks.math.columbia.edu/tag/0C7H)
* [Stacks Project, Tag 0CA5](https://stacks.math.columbia.edu/tag/0CA5)
* [Stacks Project, Tag 0C63](https://stacks.math.columbia.edu/tag/0C63)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.NumericalType (picardRelationMap picardRelationMatrix picardGroup)

universe u

namespace Stacks.Models

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-! ### The canonical map `Pic(C) ⟶ Pic(T)` -/

section CanonicalMap

open Stacks.Picard (ofScheme)

/-- `[κ_Z : k]` divides the degree on `C_Z` of every Picard class of the model. -/
theorem specialFiberComponentWeight_dvd_specialFiberComponentDegreeHom
    (Z : irreducibleComponents S.specialFiber) (x : ofScheme S.X) :
    (S.specialFiberComponentWeight Z : ℤ) ∣ S.specialFiberComponentDegreeHom Z x := by
  change (S.specialFiberComponentWeight Z : ℤ) ∣ S.specialFiberComponentDegree Z
    (Stacks.Picard.picardRepresentative S.X.toRingedSpace x).obj
    (Stacks.Picard.picardRepresentative S.X.toRingedSpace x).property
  exact S.specialFiberComponentWeight_dvd_componentDegree Z _ _

/-- **The normalized degree vector** `Pic(X) ⟶ ℤ^{⊕n}`,
`ℒ ↦ (deg(ℒ|_{C₁})/w₁, …, deg(ℒ|_{Cₙ})/wₙ)` for an enumeration `e` of the components. It is a
homomorphism because the degree is additive (Tag 0AYX) and each `wᵢ` divides every degree on
`Cᵢ` (Tag 0C6P). -/
def specialFiberNormalizedDegree (n : ℕ) (e : Fin n ≃ irreducibleComponents S.specialFiber) :
    ofScheme S.X →+ (Fin n → ℤ) where
  toFun x i := S.specialFiberComponentDegreeHom (e i) x / (S.specialFiberComponentWeight (e i) : ℤ)
  map_zero' := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp only [map_add, Pi.add_apply]
    exact Int.add_ediv_of_dvd_left
      (S.specialFiberComponentWeight_dvd_specialFiberComponentDegreeHom (e i) x)

/-- The `i`-th entry of the normalized degree vector of `x` is `deg(x|_{C_{e i}}) / w_{e i}`. -/
@[simp] theorem specialFiberNormalizedDegree_apply (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber) (x : ofScheme S.X) (i : Fin n) :
    S.specialFiberNormalizedDegree n e x i =
      S.specialFiberComponentDegreeHom (e i) x / (S.specialFiberComponentWeight (e i) : ℤ) :=
  rfl

/-- The normalized degree vector vanishes exactly when every degree does, the weights being
positive and dividing the degrees. -/
theorem specialFiberNormalizedDegree_eq_zero_iff (n : ℕ)
    (e : Fin n ≃ irreducibleComponents S.specialFiber) (x : ofScheme S.X) :
    S.specialFiberNormalizedDegree n e x = 0 ↔
      ∀ Z, S.specialFiberComponentDegreeHom Z x = 0 := by
  constructor
  · intro h Z
    have hq := congrFun h (e.symm Z)
    rw [specialFiberNormalizedDegree_apply, Equiv.apply_symm_apply, Pi.zero_apply] at hq
    rw [← Int.ediv_mul_cancel
      (S.specialFiberComponentWeight_dvd_specialFiberComponentDegreeHom Z x), hq, zero_mul]
  · intro h
    funext i
    rw [specialFiberNormalizedDegree_apply, h, Int.zero_ediv, Pi.zero_apply]

variable [DecidableEq (irreducibleComponents S.specialFiber)] (T : AlgebraicGeometry.NumericalType)
  (e : Fin T.componentCount ≃ irreducibleComponents S.specialFiber)
  (hw : ∀ i, T.weight i = S.specialFiberComponentWeight (e i))
  (hint : ∀ i j, T.intersection i j = S.specialFiberIntersectionMatrix (e i) (e j))

include hw hint in
/-- **The computation of the source's proof**: the normalized degree vector of `𝒪_X(Σ aⱼCⱼ)` is
the image of `a` under the relation map `(aᵢⱼ/wᵢ)` defining `Pic(T)`. -/
theorem specialFiberNormalizedDegree_componentPicardHom
    (a : irreducibleComponents S.specialFiber → ℤ) :
    S.specialFiberNormalizedDegree T.componentCount e
        (componentPicardHom S S.specialFiberComponentIdeal a) =
      picardRelationMap T (a ∘ e) := by
  have hO : ∀ (Z W : irreducibleComponents S.specialFiber),
      S.specialFiberComponentDegreeHom Z
          (Stacks.Divisors.picardClass (S.specialFiberComponentIdeal W)) =
        S.specialFiberIntersectionMatrix Z W := fun Z W =>
    (S.specialFiberComponentDegreeHom_picardClass Z
      (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal W))
      (Stacks.Divisors.isInvertible_invertibleSheaf_picard _)).trans
      (S.specialFiberIntersectionMatrix_eq_componentDegree Z W).symm
  funext j
  rw [componentPicardHom_apply, map_sum, Finset.sum_apply]
  change _ = (Matrix.toLin' (picardRelationMatrix T) (a ∘ e)) j
  rw [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, ← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, Pi.smul_apply, specialFiberNormalizedDegree_apply, hO, smul_eq_mul,
    Function.comp_apply, picardRelationMatrix, hint, hw,
    S.specialFiberIntersectionMatrix_comm (e i) (e j),
    mul_comm]

include hw hint in
/-- The normalized degree vector carries the kernel of `Pic(X) ⟶ Pic(C)` into the relations of
`Pic(T)`. -/
theorem specialFiberNormalizedDegree_mem_range_of_genericFiberPicardRestriction_eq_zero
    {x : ofScheme S.X} (hx : genericFiberPicardRestriction S x = 0) :
    S.specialFiberNormalizedDegree T.componentCount e x ∈
      LinearMap.range (picardRelationMap T) := by
  obtain ⟨a, rfl⟩ := (exact_componentPicardHom_genericFiberPicardRestriction S x).1 hx
  rw [S.specialFiberNormalizedDegree_componentPicardHom T e hw hint]
  exact ⟨a ∘ e, rfl⟩

/-- **The canonical map `Pic(C) ⟶ Pic(T)`**, for a numerical type `T` whose weights and
intersection numbers are those of the components enumerated by `e`: `Pic(C)` is `Pic(X)` modulo
the classes of the components (Tag 0C63), and the normalized degree vector carries those classes
into the relations defining `Pic(T)`. -/
def picardNumericalTypeHomOf : ofScheme S.C →+ picardGroup T :=
  (QuotientAddGroup.lift (genericFiberPicardRestriction S).ker
      (((LinearMap.range (picardRelationMap T)).mkQ.toAddMonoidHom).comp
        (S.specialFiberNormalizedDegree T.componentCount e))
      (fun _ hx => (Submodule.Quotient.mk_eq_zero _).2
        (S.specialFiberNormalizedDegree_mem_range_of_genericFiberPicardRestriction_eq_zero T e hw
          hint hx))).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_genericFiberPicardRestriction S)).symm.toAddMonoidHom

/-- The map `Pic(C) ⟶ Pic(T)` sends the restriction of `x ∈ Pic(X)` to the class of its normalized
degree vector. -/
theorem picardNumericalTypeHomOf_genericFiberPicardRestriction (x : ofScheme S.X) :
    S.picardNumericalTypeHomOf T e hw hint (genericFiberPicardRestriction S x) =
      Submodule.Quotient.mk (S.specialFiberNormalizedDegree T.componentCount e x) := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (surjective_genericFiberPicardRestriction S)).symm (genericFiberPicardRestriction S x) =
        (QuotientAddGroup.mk x : ofScheme S.X ⧸ (genericFiberPicardRestriction S).ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [picardNumericalTypeHomOf, AddMonoidHom.coe_comp, Function.comp_apply,
    AddEquiv.coe_toAddMonoidHom, h]
  rfl

/-- A class `y ∈ Pic(C)` lies in the kernel of `Pic(C) ⟶ Pic(T)` if and only if it is the
restriction of a class in `Pic(X)` of degree zero on every component of the special fiber. -/
theorem picardNumericalTypeHomOf_eq_zero_iff (y : ofScheme S.C) :
    S.picardNumericalTypeHomOf T e hw hint y = 0 ↔
      ∃ x : ofScheme S.X, (∀ Z, S.specialFiberComponentDegreeHom Z x = 0) ∧
        genericFiberPicardRestriction S x = y := by
  obtain ⟨x₀, rfl⟩ := surjective_genericFiberPicardRestriction S y
  rw [picardNumericalTypeHomOf_genericFiberPicardRestriction, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨x₀ - componentPicardHom S S.specialFiberComponentIdeal (b ∘ e.symm), ?_, ?_⟩
    · rw [← S.specialFiberNormalizedDegree_eq_zero_iff T.componentCount e, map_sub,
        S.specialFiberNormalizedDegree_componentPicardHom T e hw hint, ← hb]
      simp [Function.comp_assoc]
    · rw [map_sub, genericFiberPicardRestriction_componentPicardHom, sub_zero]
  · rintro ⟨x, hx, hxy⟩
    have hker : genericFiberPicardRestriction S (x₀ - x) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h := S.specialFiberNormalizedDegree_mem_range_of_genericFiberPicardRestriction_eq_zero T e
      hw hint hker
    rwa [map_sub, (S.specialFiberNormalizedDegree_eq_zero_iff T.componentCount e x).2 hx,
      sub_zero] at h

end CanonicalMap

/-! ### Stacks Project, Tag 0CAC -/

section AssociatedNumericalType

open Stacks.Picard (ofScheme)

variable [DecidableEq (irreducibleComponents S.specialFiber)] (n : ℕ)
  (e : Fin n ≃ irreducibleComponents S.specialFiber)

/-- The enumeration of the components, read as indexing the components of the numerical type
associated to `X`. -/
abbrev associatedEnumeration :
    Fin (S.associatedNumericalType n e).componentCount ≃ irreducibleComponents S.specialFiber :=
  e

/-- The weights of the numerical type associated to `X` are the weights of the components. -/
theorem associatedNumericalType_weight_eq (i : Fin (S.associatedNumericalType n e).componentCount) :
    (S.associatedNumericalType n e).weight i =
      S.specialFiberComponentWeight (S.associatedEnumeration n e i) := rfl

/-- The intersection numbers of the numerical type associated to `X` are the intersection numbers
`(Cᵢ · Cⱼ)` of the components. -/
theorem associatedNumericalType_intersection_eq_specialFiberIntersectionMatrix
    (i j : Fin (S.associatedNumericalType n e).componentCount) :
    (S.associatedNumericalType n e).intersection i j =
      S.specialFiberIntersectionMatrix (S.associatedEnumeration n e i)
        (S.associatedEnumeration n e j) :=
  rfl

/-- **The canonical map `Pic(C) ⟶ Pic(T)`** to the Picard group of the numerical type `T`
associated to `X`: `Pic(C)` is `Pic(X)` modulo the classes of the components (Tag 0C63), and the
normalized degree vector `Pic(X) ⟶ ℤ^{⊕n}`, `ℒ ↦ (deg(ℒ|_{Cᵢ})/wᵢ)`, carries those classes into
the relations `(aᵢⱼ/wᵢ)` defining `Pic(T)` (Tag 0C7H). -/
def picardNumericalTypeHom : ofScheme S.C →+ picardGroup (S.associatedNumericalType n e) :=
  S.picardNumericalTypeHomOf (S.associatedNumericalType n e) (S.associatedEnumeration n e)
    (S.associatedNumericalType_weight_eq n e)
    (S.associatedNumericalType_intersection_eq_specialFiberIntersectionMatrix n e)

/-- The canonical map on the restriction of a Picard class of the model is the class of its
normalized degree vector `(deg(ℒ|_{Cᵢ})/wᵢ)`. -/
theorem picardNumericalTypeHom_genericFiberPicardRestriction (x : ofScheme S.X) :
    S.picardNumericalTypeHom n e (genericFiberPicardRestriction S x) =
      Submodule.Quotient.mk (S.specialFiberNormalizedDegree _ (S.associatedEnumeration n e) x) :=
  S.picardNumericalTypeHomOf_genericFiberPicardRestriction _ _ _ _ x

/-- **The kernel of the canonical map, on Picard classes**: a class on `C` maps to zero exactly
when it is the restriction of a class on `X` of degree zero on every component. -/
theorem picardNumericalTypeHom_eq_zero_iff' (y : ofScheme S.C) :
    S.picardNumericalTypeHom n e y = 0 ↔
      ∃ x : ofScheme S.X, (∀ Z, S.specialFiberComponentDegreeHom Z x = 0) ∧
        genericFiberPicardRestriction S x = y :=
  S.picardNumericalTypeHomOf_eq_zero_iff _ _ _ _ y

/-- **Stacks Project, Tag 0CAC.** In the situation of [Stacks, Tag 0C61] let `T` be the
numerical type associated to `X` ([Stacks, Tag 0CA5]). The canonical map
`Stacks.Models.RegularProperModelSituation.picardNumericalTypeHom : Pic(C) ⟶ Pic(T)` sends the
restriction of the class of an invertible module `ℒ` on `X` to the class of
`(deg(ℒ|_{C₁})/w₁, …, deg(ℒ|_{Cₙ})/wₙ)`, and its kernel is exactly the classes of the invertible
modules on `C` that are restrictions of invertible modules `ℒ` on `X` with
`deg_{Cᵢ}(ℒ|_{Cᵢ}) = 0` for every `i`. -/
@[stacks 0CAC "the canonical map Pic(C) -> Pic(T) and its kernel"]
theorem picardNumericalTypeHom_spec :
    (∀ (L : S.X.Modules) (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
        (structureSheafRing S.X.toRingedSpace).property L),
      S.picardNumericalTypeHom n e (genericFiberPicardRestriction S
          (Stacks.SheafOfModules.picardClass S.X.presheaf
            (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace) L hL)) =
        Submodule.Quotient.mk (fun i =>
          S.specialFiberComponentDegree (S.associatedEnumeration n e i) L hL /
            (S.specialFiberComponentWeight (S.associatedEnumeration n e i) : ℤ))) ∧
    ∀ y : ofScheme S.C, S.picardNumericalTypeHom n e y = 0 ↔
      ∃ (L : S.X.Modules) (hL : Stacks.SheafOfModules.IsInvertible S.X.presheaf
          (structureSheafRing S.X.toRingedSpace).property L),
        genericFiberPicardRestriction S
            (Stacks.SheafOfModules.picardClass S.X.presheaf
              (Stacks.RingedSpace.structureIsSheaf S.X.toRingedSpace) L hL) = y ∧
          ∀ Z, S.specialFiberComponentDegree Z L hL = 0 := by
  refine ⟨fun L hL => ?_, fun y => ?_⟩
  · refine (S.picardNumericalTypeHom_genericFiberPicardRestriction n e _).trans ?_
    congr 1
    funext i
    exact congrArg (· / (S.specialFiberComponentWeight (S.associatedEnumeration n e i) : ℤ))
      (S.specialFiberComponentDegreeHom_picardClass (S.associatedEnumeration n e i) L hL)
  · rw [picardNumericalTypeHom_eq_zero_iff']
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(Stacks.Picard.picardRepresentative S.X.toRingedSpace x).obj,
        (Stacks.Picard.picardRepresentative S.X.toRingedSpace x).property, ?_, hx⟩
      rw [Stacks.Picard.classOf_picardRepresentative]
    · rintro ⟨L, hL, hy, hdeg⟩
      exact ⟨_, fun Z => (S.specialFiberComponentDegreeHom_picardClass Z L hL).trans (hdeg Z), hy⟩

end AssociatedNumericalType

end RegularProperModelSituation

end Stacks.Models

end
