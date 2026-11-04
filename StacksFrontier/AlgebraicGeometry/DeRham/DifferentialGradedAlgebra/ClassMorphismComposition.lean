module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedForgetCommShift
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.GlobalCohomology
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.CupProductOnCohomology
public import StacksFrontier.CategoryTheory.Shift.ShiftedHomIterate
import StacksCore.Tactic.StacksAttribute

/-!
# Composing the morphisms `ξ' : Ω^• ⟶ Ω^•[n]` of Remark 0FU7

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X` and let
`Ω^•` be the relative de Rham complex. Remark 0FU7 attaches to `ξ ∈ H^n_{dR}` a morphism
`ξ' : Ω^• ⟶ Ω^•[n]` of `D(A)`, characterized by lifting to the derived category of right
differential graded `Ω^•`-modules and by `ξ'(1) = ξ`. This file shows that the construction is
multiplicative:

* `1' = id` for the unit `1 ∈ H^0_{dR}`;
* `η'[n] ∘ ξ' = (η ∪ ξ)'` for `ξ ∈ H^n_{dR}` and `η ∈ H^m_{dR}`, the composite read as a morphism
  `Ω^• ⟶ Ω^•[m][n] = Ω^•[n + m]` (`CategoryTheory.ShiftedHom.comp`);

so that, for `ξ ∈ H^d_{dR}`, the `t`-fold composite `ξ'[d(t - 1)] ∘ ⋯ ∘ ξ'[d] ∘ ξ'` is the
morphism attached to the cup power `ξ^t`. This is the first assertion of Remark 0FUN beyond
Proposition 0FMR, for `ξ = c₁^{dR}(𝒪_P(1))` and `d = 2`.

Both properties of `ξ'` are checked on the characterization: forgetting the differential graded
structure commutes with the translations
(`SheafOfModules.DifferentialGradedModule.derivedForget_commShift`), so a composite of lifts is a
lift of the composite; and the value at `1` of a composite is computed by property (3) of
Remark 0FU7 (`AlgebraicGeometry.SheafOfModules.deRhamCohomologyCup_eq_deRhamClassMorphism`).

## Main definitions

* `AlgebraicGeometry.SheafOfModules.deRhamCohomologyPow`: the cup power `ξ^t ∈ H^{dt}_{dR}` of
  `ξ ∈ H^d_{dR}`, `ξ^0 = 1` and `ξ^{t + 1} = ξ ∪ ξ^t`.

## Main results

* `AlgebraicGeometry.SheafOfModules.deRhamClassMorphism_one`: `1' = id`.
* `AlgebraicGeometry.SheafOfModules.deRhamClassMorphism_comp`: `η'[n] ∘ ξ' = (η ∪ ξ)'`.
* `AlgebraicGeometry.SheafOfModules.iterate_deRhamClassMorphism`:
  `ξ'[d(t - 1)] ∘ ⋯ ∘ ξ'[d] ∘ ξ' = (ξ^t)'`.

## References

* [Stacks Project, Tag 0FU7](https://stacks.math.columbia.edu/tag/0FU7)
* [Stacks Project, Tag 0FUN](https://stacks.math.columbia.edu/tag/0FUN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.Cohomology.RealizationShift (shiftHomologyIsoU)
open scoped Stacks.StandardDerivedModel

universe u

/-! ### Shifted morphisms on cohomology -/

namespace Stacks.Cohomology.RealizationShift

variable {C : Type*} [Category* C] [HasShift C ℤ] {B : Type*} [Category* B] [Abelian B]
  [HasDerivedCategory B] (F : C ⥤ DerivedCategory B) [hF : F.CommShift ℤ]

/-- **A composite of shifted morphisms on cohomology.** For `f₁ : X ⟶ X[n]` and
`f₂ : X ⟶ X[m]` with `m + n = k`, the map induced on `H⁰(F(-))` by `f₂[n] ∘ f₁ : X ⟶ X[k]`, read
through `H⁰(F(X[k])) = Hᵏ(F X)`, is the map induced by `f₁`, read through
`H⁰(F(X[n])) = Hⁿ(F X)`, followed by the map induced by `f₂` on `Hⁿ(F(-))` and
`Hⁿ(F(X[m])) = Hᵏ(F X)`. -/
theorem homologyMap_comp_shiftHomologyIsoU {X : C} {n m k : ℤ} (f₁ : X ⟶ X⟦n⟧)
    (f₂ : X ⟶ X⟦m⟧) (h : m + n = k) :
    (DerivedCategory.homologyFunctor B 0).map (F.map (ShiftedHom.comp f₁ f₂ h)) ≫
        (shiftHomologyIsoU F X k 0 k (add_zero k)).hom =
      (DerivedCategory.homologyFunctor B 0).map (F.map f₁) ≫
        (shiftHomologyIsoU F X n 0 n (add_zero n)).hom ≫
        (DerivedCategory.homologyFunctor B n).map (F.map f₂) ≫
        (shiftHomologyIsoU F X m n k h).hom := by
  have hnat := Stacks.DeRham.GysinCupHodge.shiftHomologyIsoU_naturality F f₂ n 0 n (add_zero n)
  have hadd := shiftHomologyIsoU_add F X n m k h 0 n k (add_zero n) (by rw [← h, add_comm])
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← hadd, reassoc_of% hnat]

/-- **The identity in degree zero on cohomology**: the map induced on `H⁰(F(-))` by the
identity `X ⟶ X[0]`, read through `H⁰(F(X[0])) = H⁰(F X)`, is the identity. -/
theorem homologyMap_mk₀_id_shiftHomologyIsoU (X : C) :
    (DerivedCategory.homologyFunctor B 0).map (F.map (ShiftedHom.mk₀ (0 : ℤ) rfl (𝟙 X))) ≫
        (shiftHomologyIsoU F X 0 0 0 (add_zero 0)).hom = 𝟙 _ := by
  rw [shiftHomologyIsoU_zero_hom, ← Functor.map_comp, ← Functor.map_comp]
  simp [ShiftedHom.mk₀, shiftFunctorZero']

end Stacks.Cohomology.RealizationShift

/-! ### Forgetting the action commutes with composition of shifted morphisms -/

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  (A : DifferentialGradedAlgebra.{u, u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  (M : DifferentialGradedModule.{u, u, u} A)

/-- **Forgetting the action on a morphism `M ⟶ M[n]` of `D(A, d)` is applying the forgetful
functor and its commutation with the translation.** -/
theorem derivedForgetShiftedHom_eq (n : ℤ)
    (g : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M) ⟶
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M))⟦n⟧) :
    derivedForgetShiftedHom A M n g =
      (derivedForget.{u + 1, u, u, u} A).map g ≫
        ((derivedForget.{u + 1, u, u, u} A).commShiftIso n).hom.app
          ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M)) := by
  rw [derivedForget_commShiftIso_hom_app_quotient]
  exact (congrArg (· ≫ _) ((derivedForget.{u + 1, u, u, u} A).map_comp _ _)).trans
    (Category.assoc _ _ _)

/-- **Forgetting the action is compatible with the composition of shifted morphisms.** -/
theorem derivedForgetShiftedHom_comp {n m k : ℤ}
    (g₁ : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M) ⟶
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M))⟦n⟧)
    (g₂ : (toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M) ⟶
        ((toDerivedCategory.{u, u, u} A).obj ((HomotopyCategory.quotient A).obj M))⟦m⟧)
    (h : m + n = k) :
    derivedForgetShiftedHom A M k (ShiftedHom.comp g₁ g₂ h) =
      ShiftedHom.comp (derivedForgetShiftedHom A M n g₁) (derivedForgetShiftedHom A M m g₂) h := by
  rw [derivedForgetShiftedHom_eq, derivedForgetShiftedHom_eq, derivedForgetShiftedHom_eq]
  exact ShiftedHom.map_comp g₁ g₂ h (derivedForget.{u + 1, u, u, u} A)

/-- **Forgetting the action of the identity in degree zero gives the identity.** -/
theorem derivedForgetShiftedHom_mk₀_id (m₀ : ℤ) (hm₀ : m₀ = 0) :
    derivedForgetShiftedHom A M m₀ (ShiftedHom.mk₀ m₀ hm₀ (𝟙 _)) =
      ShiftedHom.mk₀ m₀ hm₀ (𝟙 _) := by
  rw [derivedForgetShiftedHom_eq]
  exact (ShiftedHom.map_mk₀ m₀ hm₀ (𝟙 _) (derivedForget.{u + 1, u, u, u} A)).trans
    (congrArg (ShiftedHom.mk₀ m₀ hm₀) ((derivedForget.{u + 1, u, u, u} A).map_id _))

end SheafOfModules.DifferentialGradedModule

/-! ### Composing the morphisms attached to classes -/

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier}

section Algebra

variable (𝒜 : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (underlyingRingSheaf A))

/-- **Forgetting the action is compatible with composition**, for the regular module. -/
theorem dgaForgetHom_comp {n m k : ℤ} (g₁ : dgaDerivedRegular 𝒜 ⟶ (dgaDerivedRegular 𝒜)⟦n⟧)
    (g₂ : dgaDerivedRegular 𝒜 ⟶ (dgaDerivedRegular 𝒜)⟦m⟧) (h : m + n = k) :
    dgaForgetHom 𝒜 k (ShiftedHom.comp g₁ g₂ h) =
      ShiftedHom.comp (dgaForgetHom 𝒜 n g₁) (dgaForgetHom 𝒜 m g₂) h :=
  _root_.SheafOfModules.DifferentialGradedModule.derivedForgetShiftedHom_comp (X := baseSite A)
    𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) g₁ g₂ h

/-- Forgetting the action of the identity of the regular module gives the identity. -/
theorem dgaForgetHom_mk₀_id (m₀ : ℤ) (hm₀ : m₀ = 0) :
    dgaForgetHom 𝒜 m₀ (ShiftedHom.mk₀ m₀ hm₀ (𝟙 _)) = ShiftedHom.mk₀ m₀ hm₀ (𝟙 _) :=
  _root_.SheafOfModules.DifferentialGradedModule.derivedForgetShiftedHom_mk₀_id (X := baseSite A)
    𝒜 (_root_.SheafOfModules.DifferentialGradedModule.regularModule 𝒜) m₀ hm₀

/-- **The value at the unit of a composite** `f₂[n] ∘ f₁ : 𝒜 ⟶ 𝒜[m][n] = 𝒜[k]`, for
`f₁ : 𝒜 ⟶ 𝒜[n]` and `f₂ : 𝒜 ⟶ 𝒜[m]` with `m + n = k`: the map `f₂` induces on `H^n(X, -)`,
applied to `f₁(1) ∈ H^n(X, 𝒜)` and read in `H^n(X, 𝒜[m]) = H^k(X, 𝒜)`. -/
theorem dgaEvalOne_comp {n m k : ℤ} (f₁ : dgaDerivedObject 𝒜 ⟶ (dgaDerivedObject 𝒜)⟦n⟧)
    (f₂ : dgaDerivedObject 𝒜 ⟶ (dgaDerivedObject 𝒜)⟦m⟧) (h : m + n = k) :
    dgaEvalOne 𝒜 k (ShiftedHom.comp f₁ f₂ h) =
      (dgaShiftHomologyIso 𝒜 m n k h).hom
        ((DerivedCategory.homologyFunctor _ n).map ((derivedSectionsBase A).map f₂)
          (dgaEvalOne 𝒜 n f₁)) := by
  have key := Stacks.Cohomology.RealizationShift.homologyMap_comp_shiftHomologyIsoU
    (hF := (inferInstance : (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen
      (baseRingedSpace A) ⊤).CommShift ℤ))
    (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤) f₁ f₂ h
  exact ConcreteCategory.congr_hom key (dgaOneClass 𝒜)

/-- **The value at the unit of the identity is the unit** `1 ∈ H^0(X, 𝒜)`. -/
theorem dgaEvalOne_mk₀_id : dgaEvalOne 𝒜 0 (ShiftedHom.mk₀ 0 rfl (𝟙 _)) = dgaOneClass 𝒜 := by
  have key := Stacks.Cohomology.RealizationShift.homologyMap_mk₀_id_shiftHomologyIsoU
    (Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen (baseRingedSpace A) ⊤)
    (dgaDerivedObject 𝒜)
  exact ConcreteCategory.congr_hom key (dgaOneClass 𝒜)

end Algebra

section DeRham

variable {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **Stacks Project, Tag 0FU7: the morphism attached to the unit `1 ∈ H^0_{dR}` is the
identity** of `Ω^•`, read as a morphism `Ω^• ⟶ Ω^•[0]`. -/
theorem deRhamClassMorphism_one :
    deRhamClassMorphism B D 0 (deRhamOneClass B D) = ShiftedHom.mk₀ 0 rfl (𝟙 _) := by
  refine (eq_deRhamClassMorphism B D 0 (deRhamOneClass B D)
    ⟨ShiftedHom.mk₀ 0 rfl (𝟙 _), dgaForgetHom_mk₀_id _ 0 rfl⟩ ?_).symm
  exact dgaEvalOne_mk₀_id _

/-- **Stacks Project, Tag 0FU7: the construction is multiplicative.** For `ξ ∈ H^n_{dR}` and
`η ∈ H^m_{dR}`, the composite `η'[n] ∘ ξ' : Ω^• ⟶ Ω^•[m][n] = Ω^•[k]`, `m + n = k`, is the morphism
attached to `η ∪ ξ ∈ H^k_{dR}`. -/
theorem deRhamClassMorphism_comp {n m k : ℤ} (ξ : deRhamCohomology B D n)
    (η : deRhamCohomology B D m) (h : m + n = k) :
    ShiftedHom.comp (deRhamClassMorphism B D n ξ) (deRhamClassMorphism B D m η) h =
      deRhamClassMorphism B D k
        (reindexDeRhamCohomology B D h (deRhamCohomologyCup B D m n η ξ)) := by
  obtain ⟨g₁, hg₁⟩ := exists_lift_deRhamClassMorphism B D n ξ
  obtain ⟨g₂, hg₂⟩ := exists_lift_deRhamClassMorphism B D m η
  refine eq_deRhamClassMorphism B D k _ ⟨ShiftedHom.comp g₁ g₂ h, ?_⟩ ?_
  · rw [deRhamForgetHom, dgaForgetHom_comp, ← deRhamForgetHom, ← deRhamForgetHom, hg₁, hg₂]
    rfl
  · subst h
    refine (dgaEvalOne_comp _ _ _ rfl).trans ?_
    have hξ : dgaEvalOne (deRhamDifferentialGradedAlgebra B D) n (deRhamClassMorphism B D n ξ) =
        ξ := deRhamEvalOne_deRhamClassMorphism B D n ξ
    rw [hξ]
    exact (deRhamCohomologyCup_eq_deRhamClassMorphism B D m n η ξ).symm

/-- **The cup power** `ξ^t ∈ H^{dt}_{dR}` of `ξ ∈ H^d_{dR}`: `ξ^0 = 1`, `ξ^{t + 1} = ξ ∪ ξ^t`. -/
def deRhamCohomologyPow (d : ℕ) (ξ : deRhamCohomology B D (d : ℤ)) :
    (t : ℕ) → deRhamCohomology B D ((d * t : ℕ) : ℤ)
  | 0 => deRhamOneClass B D
  | t + 1 => reindexDeRhamCohomology B D (by push_cast; ring)
      (deRhamCohomologyCup B D d (d * t : ℕ) ξ (deRhamCohomologyPow d ξ t))

/-- The zeroth cup power of a de Rham class is the unit class: `ξ^0 = 1`. -/
theorem deRhamCohomologyPow_zero (d : ℕ) (ξ : deRhamCohomology B D (d : ℤ)) :
    deRhamCohomologyPow B D d ξ 0 = deRhamOneClass B D :=
  rfl

/-- The `(t + 1)`-st cup power of a de Rham class is `ξ^{t + 1} = ξ ∪ ξ^t`, reindexed to degree
`d(t + 1)`. -/
theorem deRhamCohomologyPow_succ (d : ℕ) (ξ : deRhamCohomology B D (d : ℤ)) (t : ℕ) :
    deRhamCohomologyPow B D d ξ (t + 1) = reindexDeRhamCohomology B D (by push_cast; ring)
      (deRhamCohomologyCup B D d (d * t : ℕ) ξ (deRhamCohomologyPow B D d ξ t)) :=
  rfl

/-- **Stacks Project, Tag 0FUN: the composite `ξ'[d(t - 1)] ∘ ⋯ ∘ ξ'[d] ∘ ξ' : Ω^• ⟶ Ω^•[dt]` is
the morphism of Remark 0FU7 attached to `ξ^t`**, for `ξ ∈ H^d_{dR}`; Remark 0FUN states it for
`ξ = c₁^{dR}(𝒪_P(1))` and `d = 2`. -/
@[stacks 0FUN "xi'[2(t-1)] o ... o xi'[2] o xi' is the morphism of Remark 0FU7 attached to xi^t; \
stated for every class xi of every degree d, the remark's case being xi = c_1^dR(O_P(1)), d = 2"]
theorem iterate_deRhamClassMorphism (d : ℕ) (ξ : deRhamCohomology B D (d : ℤ)) (t : ℕ) :
    ShiftedHom.iterate d (deRhamClassMorphism B D d ξ) t =
      deRhamClassMorphism B D ((d * t : ℕ) : ℤ) (deRhamCohomologyPow B D d ξ t) := by
  induction t with
  | zero => exact (deRhamClassMorphism_one B D).symm
  | succ t ih =>
    rw [ShiftedHom.iterate_succ, ih, deRhamClassMorphism_comp]
    rfl

end DeRham

end AlgebraicGeometry.SheafOfModules

end
