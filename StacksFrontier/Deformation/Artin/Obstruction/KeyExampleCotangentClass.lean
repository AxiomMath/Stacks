module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.CotangentClass
public import StacksFrontier.Deformation.Artin.Obstruction.KeyExampleBaseChange
public import StacksFrontier.Homology.TwoTermComplex.Ext

/-!
# The obstruction element of the key example as a map of cotangent complexes

Stacks 07YI gives a second, invariant description of the obstruction element `o_x(A')` of the
key example: it is the composite
```
NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ} ⟶ NL_{A/A'} = I[1]
```
in the derived category of `A`-modules, the first map being functoriality of the naive
cotangent complex for `R → A`, the second the base-change map of the tower `Λ → A' → A`, and
the last identification the one of Stacks 00S1 for the square-zero surjection `A' → A`.

This file builds the first map and proves that description.

## Main definitions

* `Deformation.Artin.doubleToSingleNegOne` — the chain map `[U → V] ⟶ W[1]` determined by a
  functional `U ⟶ W` on the degree `-1` term, and `Deformation.Artin.doubleExtClass` its class
  in the derived category.
* `Deformation.Artin.doubleCokernelExtEquiv` — the resulting identification of
  `Hom_{D(A)}([U → V], W[1])` with the cokernel of the dual of `U → V`, for `V` projective.
* `Deformation.Artin.nlBaseChangeToNaive` — the morphism `NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ}`.
* `Deformation.Artin.compositeObsFunctional` — the conormal functional `A ⊗_R J/J² → I`
  representing the composite, and `Deformation.Artin.canonicalLift` the lifts `a'_i ∈ A'` of
  the coordinates of `x` it evaluates relations at.

## Main results

* `Deformation.Artin.doubleCokernelExtEquiv_doubleExtLinearClass`: the identification sends
  the class of a functional to its residue class, so it is characterised rather than chosen.
* `Deformation.Artin.cotangentExtensionClass_eq`: the extension class `NL_{A/Λ} ⟶ I[1]` of a
  square-zero thickening is the class of an explicit conormal functional.
* `Deformation.Artin.cotangentComposition_eq` and
  `Deformation.Artin.doubleCokernelExtEquiv_cotangentComposition`: the composite
  `NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ} ⟶ NL_{A/A'} = I[1]` is the class of
  `Deformation.Artin.compositeObsFunctional`.
* `Deformation.Artin.coe_compositeObsFunctional_one_tmul_mk`: that functional sends
  `1 ⊗ (class of f)` to `f(a'_1, …, a'_n)`, so the composite is the obstruction element
  `o_x(A')` of `Deformation.Artin.KeyExample.Situation.obsClass`, which by
  `Deformation.Artin.KeyExample.Situation.obsClass_eq` does not depend on the lifts chosen.

## Implementation notes

A two-term complex is placed in cohomological degrees `-1` and `0` by
`HomologicalComplex.double`, the placement
`Deformation.Artin.derivedNaiveCotangentComplex` uses, and `W[1]` is `W` placed in degree
`-1`. With that model a chain map `[U → V] ⟶ W[1]` is exactly a map `U ⟶ W`, and
`Deformation.Artin.doubleCokernelExtEquiv` is Stacks 0ALN applied to that pair: every class
comes from a chain map because `V` is projective, and two functionals have the same class
exactly when they differ by one factoring through `U → V`.

All the morphisms entering the composite are images under `DerivedCategory.Q` of explicit
chain maps, so the composite is the image of the composite chain map; that chain map lands in
a complex concentrated in degree `-1` and is therefore determined by its degree `-1`
component, which is computed by functoriality of the conormal module. The deformation
situation is written here with `Algebra` instances — a square-zero surjection `A' → A` of
`Λ`-algebras together with the `R`-algebra structure on `A` given by the object `x` — rather
than through the bundled `Deformation.Artin.KeyExample.Situation`.

## References

* [Stacks Project, Tag 07YI](https://stacks.math.columbia.edu/tag/07YI)
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 0ALN](https://stacks.math.columbia.edu/tag/0ALN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ComplexShape (upIntRelNegOneZero)
open scoped TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Deformation.Artin

/-! ### Morphisms from a two-term complex to a module in degree `-1` -/

section DoubleModel

variable {A : Type u} [CommRing A]

/-- A complex concentrated in a single degree has vanishing differentials. -/
theorem single_obj_d_eq_zero (W : ModuleCat.{u} A) (j i i' : ℤ) :
    ((single (ModuleCat.{u} A) (ComplexShape.up ℤ) j).obj W).d i i' = 0 := by
  by_cases hi : i = j
  · by_cases hi' : i' = j
    · exact HomologicalComplex.shape _ i i' (by simp only [ComplexShape.up_Rel]; omega)
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) j W i' hi').eq_of_tgt _ _
  · exact (isZero_single_obj_X (ComplexShape.up ℤ) j W i hi).eq_of_src _ _

variable {U V W : ModuleCat.{u} A}

/-- The chain map `[U → V] ⟶ W[1]` determined by a functional `g : U ⟶ W` on the degree `-1`
term of the two-term complex. -/
def doubleToSingleNegOne (d : U ⟶ V) (g : U ⟶ W) :
    double d upIntRelNegOneZero ⟶
      (single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj W :=
  mkHomToSingle ((doubleXIso₀ d upIntRelNegOneZero).hom ≫ g)
    (fun i _ => by
      rw [double_d_eq_zero₁ d upIntRelNegOneZero i (-1) NaiveCotangent.TwoTerm.negOne_ne_zero,
        zero_comp])

/-- In degree `-1`, the chain map `doubleToSingleNegOne d g` is `g`, up to the identifications of
the degree `-1` terms of source and target with `U` and `W`. -/
@[simp] theorem doubleToSingleNegOne_f_neg_one (d : U ⟶ V) (g : U ⟶ W) :
    (doubleToSingleNegOne d g).f (-1) =
      (doubleXIso₀ d upIntRelNegOneZero).hom ≫ g ≫
        (singleObjXSelf (ComplexShape.up ℤ) (-1) W).inv := by
  rw [doubleToSingleNegOne, mkHomToSingle_f, Category.assoc]

/-- Away from degree `-1` the target vanishes, so the chain map is zero there. -/
theorem doubleToSingleNegOne_f_of_ne (d : U ⟶ V) (g : U ⟶ W) (i : ℤ) (hi : i ≠ -1) :
    (doubleToSingleNegOne d g).f i = 0 :=
  (isZero_single_obj_X (ComplexShape.up ℤ) (-1) W i hi).eq_of_tgt _ _

/-- Every chain map `[U → V] ⟶ W[1]` is of this form. -/
theorem doubleToSingleNegOne_eq (d : U ⟶ V)
    (τ : double d upIntRelNegOneZero ⟶
      (single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj W) :
    doubleToSingleNegOne d ((doubleXIso₀ d upIntRelNegOneZero).inv ≫ τ.f (-1) ≫
      (singleObjXSelf (ComplexShape.up ℤ) (-1) W).hom) = τ := by
  apply from_double_hom_ext
  · rw [doubleToSingleNegOne_f_neg_one]
    simp
  · rw [doubleToSingleNegOne_f_of_ne d _ 0 (by omega)]
    exact ((isZero_single_obj_X (ComplexShape.up ℤ) (-1) W 0 (by omega)).eq_of_tgt _ _).symm

/-- The chain map depends additively on the functional. -/
def doubleToSingleNegOneAddHom (d : U ⟶ V) (W : ModuleCat.{u} A) :
    (U ⟶ W) →+ (double d upIntRelNegOneZero ⟶
      (single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj W) where
  toFun := doubleToSingleNegOne d
  map_zero' := by
    apply from_double_hom_ext
    · rw [doubleToSingleNegOne_f_neg_one]
      simp
    · rw [doubleToSingleNegOne_f_of_ne d _ 0 (by omega)]
      simp
  map_add' g h := by
    apply from_double_hom_ext
    · rw [doubleToSingleNegOne_f_neg_one]
      simp [Preadditive.comp_add, Preadditive.add_comp]
    · rw [doubleToSingleNegOne_f_of_ne d _ 0 (by omega)]
      simp [doubleToSingleNegOne_f_of_ne d _ 0 (by omega)]

/-- A functional factoring through the differential gives a null-homotopic chain map. -/
theorem nonempty_homotopy_doubleToSingleNegOne (d : U ⟶ V) (h : V ⟶ W) :
    Nonempty (Homotopy (doubleToSingleNegOne d (d ≫ h)) 0) := by
  refine ⟨{
    hom i j := if hij : i = 0 ∧ j = -1 then
      eqToHom (congrArg (double d upIntRelNegOneZero).X hij.1) ≫
        (doubleXIso₁ d upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).hom ≫ h ≫
        (singleObjXSelf (ComplexShape.up ℤ) (-1) W).inv ≫
        eqToHom (congrArg
          ((single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj W).X hij.2.symm)
      else 0
    zero i j hij := by
      split_ifs with hh
      · exact absurd (by rcases hh with ⟨rfl, rfl⟩; rfl) hij
      · rfl
    comm i := by
      by_cases hi : i = -1
      · subst hi
        rw [dNext_eq _ (i' := 0) (by rfl), prevD_eq _ (j' := -2) (by rfl),
          single_obj_d_eq_zero, comp_zero, HomologicalComplex.zero_f, add_zero,
          doubleToSingleNegOne_f_neg_one,
          double_d d upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero]
        simp
      · rw [dNext_eq _ (i' := i + 1) (by simp [ComplexShape.up_Rel]),
          prevD_eq _ (j' := i - 1) (by simp [ComplexShape.up_Rel]),
          single_obj_d_eq_zero, comp_zero, HomologicalComplex.zero_f, add_zero,
          doubleToSingleNegOne_f_of_ne d _ i hi,
          double_d_eq_zero₀ d upIntRelNegOneZero i (i + 1) (by omega), zero_comp]
        exact ((isZero_single_obj_X (ComplexShape.up ℤ) (-1) W i hi).eq_of_tgt _ _).symm }⟩

/-- **The extension class of a functional on the degree `-1` term of a two-term complex**: the
class in `D(A)` of the chain map `doubleToSingleNegOne`. -/
def doubleExtClass (d : U ⟶ V) (W : ModuleCat.{u} A) :
    (U ⟶ W) →+ TwoTermComplexExt.HomD (double d upIntRelNegOneZero)
      ((single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj W) :=
  DerivedCategory.Q.mapAddHom.comp (doubleToSingleNegOneAddHom d W)

/-- The extension class `doubleExtClass d W g` is the image in `D(A)` of the chain map
`doubleToSingleNegOne d g`. -/
@[simp] theorem doubleExtClass_apply (d : U ⟶ V) (W : ModuleCat.{u} A) (g : U ⟶ W) :
    doubleExtClass d W g = DerivedCategory.Q.map (doubleToSingleNegOne d g) :=
  rfl

variable [Projective V]

/-- For `V` projective, passing from the homotopy category to the derived category is bijective
on morphisms `[U → V] ⟶ W[1]`. -/
private theorem bijective_toHomD_double (d : U ⟶ V) (W : ModuleCat.{u} A) :
    Function.Bijective (fun f : TwoTermComplexExt.HomK (double d upIntRelNegOneZero)
      ((single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj W) =>
        (TwoTermComplexExt.toHomD f : TwoTermComplexExt.HomD (double d upIntRelNegOneZero)
      ((single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj W))) :=
  TwoTermComplexExt.toHomD_bijective (R := A)
    (double d upIntRelNegOneZero) ((single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj W)
    (fun i hi => isZero_double_X d upIntRelNegOneZero i (by omega) (by omega))
    (Projective.of_iso
      (doubleXIso₁ d upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).symm inferInstance)
    (fun i hi => isZero_single_obj_X (ComplexShape.up ℤ) (-1) W i (by omega))

/-- Every class in `Hom_{D(A)}([U → V], W[1])` is the class of a functional, `V` being
projective. This is Stacks 0ALN(1). -/
theorem surjective_doubleExtClass (d : U ⟶ V) (W : ModuleCat.{u} A) :
    Function.Surjective (doubleExtClass d W) := by
  intro f
  obtain ⟨g, hg⟩ := (bijective_toHomD_double d W).surjective f
  obtain ⟨τ, hτ⟩ :=
    (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map_surjective g
  refine ⟨(doubleXIso₀ d upIntRelNegOneZero).inv ≫ τ.f (-1) ≫
    (singleObjXSelf (ComplexShape.up ℤ) (-1) W).hom, ?_⟩
  rw [doubleExtClass_apply, doubleToSingleNegOne_eq, ← TwoTermComplexExt.toHomD_quotient_map,
    hτ]
  exact hg

/-- A functional has zero class exactly when it factors through the differential. -/
theorem doubleExtClass_eq_zero_iff (d : U ⟶ V) (W : ModuleCat.{u} A) (g : U ⟶ W) :
    doubleExtClass d W g = 0 ↔ ∃ h : V ⟶ W, d ≫ h = g := by
  constructor
  · intro hg
    have hz : (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).map
        (doubleToSingleNegOne d g) = 0 := by
      apply (bijective_toHomD_double d W).injective
      dsimp only
      rw [TwoTermComplexExt.toHomD_quotient_map, TwoTermComplexExt.toHomD_zero]
      exact hg
    obtain ⟨H⟩ := (HomotopyCategory.quotient_map_eq_zero_iff _).mp hz
    refine ⟨(doubleXIso₁ d upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).inv ≫
      H.hom 0 (-1) ≫ (singleObjXSelf (ComplexShape.up ℤ) (-1) W).hom, ?_⟩
    have he := H.comm (-1)
    rw [dNext_eq _ (i' := 0) (by rfl), prevD_eq _ (j' := -2) (by rfl),
      single_obj_d_eq_zero, comp_zero, HomologicalComplex.zero_f, add_zero, add_zero,
      doubleToSingleNegOne_f_neg_one,
      double_d d upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero] at he
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using
      congrArg (fun z => (doubleXIso₀ d upIntRelNegOneZero).inv ≫ z ≫
        (singleObjXSelf (ComplexShape.up ℤ) (-1) W).hom) he.symm
  · rintro ⟨h, rfl⟩
    obtain ⟨H⟩ := nonempty_homotopy_doubleToSingleNegOne d h
    rw [doubleExtClass_apply, ← TwoTermComplexExt.toHomD_quotient_map,
      (HomotopyCategory.quotient_map_eq_zero_iff _).mpr ⟨H⟩, TwoTermComplexExt.toHomD_zero]

end DoubleModel

/-! ### The cokernel description of the morphisms out of a two-term complex -/

section Cokernel

variable {A : Type u} [CommRing A] {M₁ M₀ N : Type u} [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₀] [Module A M₀] [AddCommGroup N] [Module A N]

/-- **The extension class of a linear functional on the degree `-1` term**, as a homomorphism
in the functional. -/
def doubleExtLinearClass (dl : M₁ →ₗ[A] M₀) (N : Type u) [AddCommGroup N] [Module A N] :
    (M₁ →ₗ[A] N) →+ TwoTermComplexExt.HomD
      (double (ModuleCat.ofHom dl) upIntRelNegOneZero)
      ((single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj (ModuleCat.of A N)) where
  toFun g :=
    doubleExtClass (ModuleCat.ofHom dl) (ModuleCat.of A N) (ModuleCat.ofHom g)
  map_zero' := by rw [ModuleCat.ofHom_zero, map_zero]
  map_add' g h := by rw [ModuleCat.ofHom_add, map_add]

/-- The extension class `doubleExtLinearClass dl N g` is the image in `D(A)` of the chain map
`doubleToSingleNegOne` of `ModuleCat.ofHom dl` and `ModuleCat.ofHom g`. -/
@[simp] theorem doubleExtLinearClass_apply (dl : M₁ →ₗ[A] M₀) (g : M₁ →ₗ[A] N) :
    doubleExtLinearClass dl N g =
      DerivedCategory.Q.map (doubleToSingleNegOne (ModuleCat.ofHom dl) (ModuleCat.ofHom g)) :=
  rfl

variable [Module.Free A M₀]

/-- Every morphism `[M₁ → M₀] ⟶ N[1]` in `D(A)` is the class of a functional. -/
theorem surjective_doubleExtLinearClass (dl : M₁ →ₗ[A] M₀) :
    Function.Surjective (doubleExtLinearClass dl N) := by
  have : Projective (ModuleCat.of A M₀) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis A M₀)
  intro f
  obtain ⟨g, hg⟩ := surjective_doubleExtClass (ModuleCat.ofHom dl) (ModuleCat.of A N) f
  exact ⟨g.hom, hg⟩

/-- The functionals with vanishing class are exactly those factoring through `dl`. -/
theorem ker_doubleExtLinearClass (dl : M₁ →ₗ[A] M₀) :
    (doubleExtLinearClass dl N).toIntLinearMap.ker =
      (LinearMap.range (LinearMap.lcomp A N dl)).restrictScalars ℤ := by
  have : Projective (ModuleCat.of A M₀) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis A M₀)
  ext g
  rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
  change doubleExtClass (ModuleCat.ofHom dl) (ModuleCat.of A N) (ModuleCat.ofHom g) = 0 ↔ _
  rw [doubleExtClass_eq_zero_iff]
  exact ⟨fun ⟨h, hh⟩ => ⟨h.hom, congrArg ModuleCat.Hom.hom hh⟩,
    fun ⟨h, hh⟩ => ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩⟩

/-- **The morphisms out of a two-term complex, as a cokernel.** For `dl : M₁ → M₀` with `M₀`
free, the group of morphisms `[M₁ → M₀] ⟶ N[1]` in `D(A)` is the cokernel of precomposition
with `dl` on the dual modules. This is Stacks 0ALN read at `N[1]`. -/
def doubleCokernelExtEquiv (dl : M₁ →ₗ[A] M₀) (N : Type u) [AddCommGroup N] [Module A N] :
    TwoTermComplexExt.HomD (double (ModuleCat.ofHom dl) upIntRelNegOneZero)
        ((single (ModuleCat.{u} A) (ComplexShape.up ℤ) (-1)).obj (ModuleCat.of A N)) ≃+
      ((M₁ →ₗ[A] N) ⧸ LinearMap.range (LinearMap.lcomp A N dl)) :=
  ((LinearMap.quotKerEquivOfSurjective (doubleExtLinearClass dl N).toIntLinearMap
      (surjective_doubleExtLinearClass dl)).symm.trans
    (Submodule.quotEquivOfEq _ _ (ker_doubleExtLinearClass dl))).toAddEquiv

/-- **The cokernel description, on an explicit class.** The class of a functional `g` goes to
the residue class of `g`; this characterises `doubleCokernelExtEquiv`. -/
theorem doubleCokernelExtEquiv_doubleExtLinearClass (dl : M₁ →ₗ[A] M₀) (g : M₁ →ₗ[A] N) :
    doubleCokernelExtEquiv dl N (doubleExtLinearClass dl N g) = Submodule.Quotient.mk g := by
  change (Submodule.quotEquivOfEq _ _ (ker_doubleExtLinearClass dl))
      ((LinearMap.quotKerEquivOfSurjective (doubleExtLinearClass dl N).toIntLinearMap
        (surjective_doubleExtLinearClass dl)).symm
          ((doubleExtLinearClass dl N).toIntLinearMap g)) = Submodule.Quotient.mk g
  exact congrArg (Submodule.quotEquivOfEq _ _ (ker_doubleExtLinearClass dl))
    (LinearMap.quotKerEquivOfSurjective_symm_apply
      (doubleExtLinearClass dl N).toIntLinearMap
      (surjective_doubleExtLinearClass dl) g)

/-- The cokernel description read on the chain map of a functional. -/
theorem doubleCokernelExtEquiv_Q_map (dl : M₁ →ₗ[A] M₀) (g : M₁ →ₗ[A] N) :
    doubleCokernelExtEquiv dl N
        (DerivedCategory.Q.map (doubleToSingleNegOne (ModuleCat.ofHom dl)
          (ModuleCat.ofHom g))) =
      Submodule.Quotient.mk g :=
  doubleCokernelExtEquiv_doubleExtLinearClass dl g

end Cokernel

/-! ### Composing a map of two-term complexes with a functional -/

section Compose

variable {A : Type u} [CommRing A] {U V U' V' W : ModuleCat.{u} A}

/-- Composing a morphism of two-term complexes with the chain map of a functional `g` is the
chain map of `g` precomposed with the degree `-1` component. -/
theorem comp_doubleToSingleNegOne {d : U ⟶ V} {d' : U' ⟶ V'}
    (φ : double d upIntRelNegOneZero ⟶ double d' upIntRelNegOneZero) {f₁ : U ⟶ U'}
    (hφ : φ.f (-1) = (doubleXIso₀ d upIntRelNegOneZero).hom ≫ f₁ ≫
      (doubleXIso₀ d' upIntRelNegOneZero).inv) (g : U' ⟶ W) :
    φ ≫ doubleToSingleNegOne d' g = doubleToSingleNegOne d (f₁ ≫ g) := by
  apply from_double_hom_ext
  · rw [HomologicalComplex.comp_f, hφ, doubleToSingleNegOne_f_neg_one,
      doubleToSingleNegOne_f_neg_one]
    simp
  · rw [doubleToSingleNegOne_f_of_ne d _ 0 (by omega)]
    exact (isZero_single_obj_X (ComplexShape.up ℤ) (-1) W 0 (by omega)).eq_of_tgt _ _

/-- The image in `D(A)` of a composite of a chain map of two-term complexes with the chain map of
a functional. -/
private theorem Q_map_comp_doubleToSingleNegOne {d : U ⟶ V} {d' : U' ⟶ V'}
    (φ : double d upIntRelNegOneZero ⟶ double d' upIntRelNegOneZero) {f₁ : U ⟶ U'}
    (hφ : φ.f (-1) = (doubleXIso₀ d upIntRelNegOneZero).hom ≫ f₁ ≫
      (doubleXIso₀ d' upIntRelNegOneZero).inv) (g : U' ⟶ W) :
    DerivedCategory.Q.map φ ≫ DerivedCategory.Q.map (doubleToSingleNegOne d' g) =
      DerivedCategory.Q.map (doubleToSingleNegOne d (f₁ ≫ g)) := by
  rw [← DerivedCategory.Q.map_comp, comp_doubleToSingleNegOne φ hφ]

end Compose

/-! ### The scalar tower on the conormal module -/

section Tower

variable {Λ S : Type*} [CommRing Λ] [CommRing S] [Algebra Λ S] (P : Algebra.Extension Λ S)
  {R : Type*} [CommRing R] [Algebra R S]

/-- The action of a ring `R` on the conormal module of an extension of `S`, obtained by
restricting the action of `S`, is compatible with the action of `S`. -/
instance isScalarTower_cotangent : IsScalarTower R S P.Cotangent :=
  IsScalarTower.of_algebraMap_smul fun r x =>
    Algebra.Extension.Cotangent.ext (by
      rw [Algebra.Extension.Cotangent.val_smul,
        Algebra.Extension.Cotangent.val_smul'''])

end Tower

/-! ### The extension class of a square-zero thickening, chain-level -/

section CotangentClassChain

variable (Λ A' A : Type u) [CommRing Λ] [CommRing A'] [CommRing A]
  [Algebra Λ A'] [Algebra Λ A] [Algebra A' A] [IsScalarTower Λ A' A]
  (hq : Function.Surjective (algebraMap A' A))

/-- The presentation of `A` over `A'` given by the surjection `A' → A` itself. -/
abbrev squareZeroExtension : Algebra.Extension A' A :=
  Algebra.Extension.ofSurjective (Algebra.ofId A' A) hq

/-- The comparison of the canonical presentation of `A` over `A'` with the presentation given
by the surjection `A' → A` itself. -/
abbrev squareZeroCompareHom :
    (Algebra.Generators.self A' A).toExtension.Hom (squareZeroExtension A' A hq) :=
  Algebra.Extension.defaultHom A' A (squareZeroExtension A' A hq)

/-- The comparison of the canonical presentation of `A` over `Λ` with the canonical
presentation of `A` over `A'`. -/
abbrev towerCompareHom :
    (Algebra.Generators.self Λ A).toExtension.Hom (Algebra.Generators.self A' A).toExtension :=
  ((Algebra.Generators.self Λ A).defaultHom (Algebra.Generators.self A' A)).toExtensionHom

/-- The chain map comparing the canonical presentation of `A` over `A'` with the presentation
given by `A' → A` itself. -/
def squareZeroCompareChainMap :
    double (ModuleCat.ofHom (Algebra.Generators.self A' A).toExtension.cotangentComplex)
        upIntRelNegOneZero ⟶
      double (ModuleCat.ofHom (squareZeroExtension A' A hq).cotangentComplex)
        upIntRelNegOneZero :=
  mkHomFromDouble upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero
    (ModuleCat.ofHom (Algebra.Extension.Cotangent.map (squareZeroCompareHom A' A hq)) ≫
      (doubleXIso₀ (ModuleCat.ofHom (squareZeroExtension A' A hq).cotangentComplex)
        upIntRelNegOneZero).inv)
    (ModuleCat.ofHom (Algebra.Extension.CotangentSpace.map (squareZeroCompareHom A' A hq)) ≫
      (doubleXIso₁ (ModuleCat.ofHom (squareZeroExtension A' A hq).cotangentComplex)
        upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero).inv)
    (by
      rw [double_d _ _ NaiveCotangent.TwoTerm.negOne_ne_zero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hmap :
          ModuleCat.ofHom (Algebra.Extension.Cotangent.map (squareZeroCompareHom A' A hq)) ≫
            ModuleCat.ofHom (squareZeroExtension A' A hq).cotangentComplex =
          ModuleCat.ofHom (Algebra.Generators.self A' A).toExtension.cotangentComplex ≫
            ModuleCat.ofHom
              (Algebra.Extension.CotangentSpace.map (squareZeroCompareHom A' A hq)) :=
        ModuleCat.hom_ext <| LinearMap.ext fun x =>
          (Algebra.Extension.CotangentSpace.map_cotangentComplex _ x).symm
      rw [← Category.assoc, hmap, Category.assoc])
    (fun k hk => by
      rw [double_d_eq_zero₀ _ _ _ _ (by omega : (0 : ℤ) ≠ -1)]
      simp)

/-- In degree `-1`, the chain map `squareZeroCompareChainMap` is the map on conormal modules
induced by `squareZeroCompareHom`. -/
theorem squareZeroCompareChainMap_f_neg_one :
    (squareZeroCompareChainMap A' A hq).f (-1) =
      (doubleXIso₀ (ModuleCat.ofHom
          (Algebra.Generators.self A' A).toExtension.cotangentComplex)
        upIntRelNegOneZero).hom ≫
        ModuleCat.ofHom (Algebra.Extension.Cotangent.map (squareZeroCompareHom A' A hq)) ≫
          (doubleXIso₀ (ModuleCat.ofHom (squareZeroExtension A' A hq).cotangentComplex)
            upIntRelNegOneZero).inv := by
  rw [squareZeroCompareChainMap, mkHomFromDouble_f₀]

/-- The morphism `relativeNaiveCotangentSurjectionMap A' A hq` is the image in the derived
category of the chain map `squareZeroCompareChainMap A' A hq`. -/
theorem relativeNaiveCotangentSurjectionMap_eq_Q_map :
    relativeNaiveCotangentSurjectionMap A' A hq =
      DerivedCategory.Q.map (squareZeroCompareChainMap A' A hq) :=
  rfl

/-- The chain map comparing the canonical presentation of `A` over `Λ` with the canonical
presentation of `A` over `A'`. -/
def towerCompareChainMap :
    double (ModuleCat.ofHom (Algebra.Generators.self Λ A).toExtension.cotangentComplex)
        upIntRelNegOneZero ⟶
      double (ModuleCat.ofHom (Algebra.Generators.self A' A).toExtension.cotangentComplex)
        upIntRelNegOneZero :=
  mkHomFromDouble upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero
    (ModuleCat.ofHom ((Algebra.Extension.Cotangent.map
        (towerCompareHom Λ A' A)).restrictScalars A) ≫
      (doubleXIso₀ (ModuleCat.ofHom
        (Algebra.Generators.self A' A).toExtension.cotangentComplex) upIntRelNegOneZero).inv)
    (ModuleCat.ofHom ((Algebra.Extension.CotangentSpace.map
        (towerCompareHom Λ A' A)).restrictScalars A) ≫
      (doubleXIso₁ (ModuleCat.ofHom
        (Algebra.Generators.self A' A).toExtension.cotangentComplex) upIntRelNegOneZero
        NaiveCotangent.TwoTerm.negOne_ne_zero).inv)
    (by
      rw [double_d _ _ NaiveCotangent.TwoTerm.negOne_ne_zero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      have hmap : ModuleCat.ofHom ((Algebra.Extension.Cotangent.map
            (towerCompareHom Λ A' A)).restrictScalars A) ≫
            ModuleCat.ofHom (Algebra.Generators.self A' A).toExtension.cotangentComplex =
          ModuleCat.ofHom (Algebra.Generators.self Λ A).toExtension.cotangentComplex ≫
            ModuleCat.ofHom ((Algebra.Extension.CotangentSpace.map
              (towerCompareHom Λ A' A)).restrictScalars A) :=
        ModuleCat.hom_ext <| LinearMap.ext fun x =>
          (Algebra.Extension.CotangentSpace.map_cotangentComplex _ x).symm
      rw [← Category.assoc, hmap, Category.assoc])
    (fun k hk => by
      rw [double_d_eq_zero₀ _ _ _ _ (by omega : (0 : ℤ) ≠ -1)]
      simp)

/-- In degree `-1`, the chain map `towerCompareChainMap` is the map on conormal modules induced
by `towerCompareHom`. -/
theorem towerCompareChainMap_f_neg_one :
    (towerCompareChainMap Λ A' A).f (-1) =
      (doubleXIso₀ (ModuleCat.ofHom
          (Algebra.Generators.self Λ A).toExtension.cotangentComplex)
        upIntRelNegOneZero).hom ≫
        ModuleCat.ofHom ((Algebra.Extension.Cotangent.map
            (towerCompareHom Λ A' A)).restrictScalars A) ≫
          (doubleXIso₀ (ModuleCat.ofHom
            (Algebra.Generators.self A' A).toExtension.cotangentComplex)
            upIntRelNegOneZero).inv := by
  rw [towerCompareChainMap, mkHomFromDouble_f₀]

/-- The morphism `naiveCotangentBaseMap Λ A' A` is the image in the derived category of the
chain map `towerCompareChainMap Λ A' A`. -/
theorem naiveCotangentBaseMap_eq_Q_map :
    naiveCotangentBaseMap Λ A' A = DerivedCategory.Q.map (towerCompareChainMap Λ A' A) :=
  rfl

variable (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)

/-- **The morphism `NL_{A/A'} = I[1]` of a square-zero surjection, chain-level**: the
comparison of Stacks 00S1 followed by the conormal identification `I/I² = I` is the class of
the functional on the conormal module of the canonical presentation of `A` over `A'` given by
that identification. -/
theorem squareZeroCotangentClass_eq :
    letI := Stacks.Smooth.kerModule hq hsq
    squareZeroCotangentClass A' A hq hsq =
      DerivedCategory.Q.map (doubleToSingleNegOne
        (ModuleCat.ofHom (Algebra.Generators.self A' A).toExtension.cotangentComplex)
        (ModuleCat.ofHom (Algebra.Extension.Cotangent.map (squareZeroCompareHom A' A hq)) ≫
          ModuleCat.ofHom
            (squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap)) := by
  let := Stacks.Smooth.kerModule hq hsq
  exact Q_map_comp_doubleToSingleNegOne _ (squareZeroCompareChainMap_f_neg_one A' A hq)
    (ModuleCat.ofHom (squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap)

/-- **The extension class `NL_{A/Λ} ⟶ I[1]` of a square-zero thickening, chain-level.** -/
theorem cotangentExtensionClass_eq :
    letI := Stacks.Smooth.kerModule hq hsq
    cotangentExtensionClass Λ A' A hq hsq =
      DerivedCategory.Q.map (doubleToSingleNegOne
        (ModuleCat.ofHom (Algebra.Generators.self Λ A).toExtension.cotangentComplex)
        (ModuleCat.ofHom ((Algebra.Extension.Cotangent.map
            (towerCompareHom Λ A' A)).restrictScalars A) ≫
          ModuleCat.ofHom (Algebra.Extension.Cotangent.map (squareZeroCompareHom A' A hq)) ≫
            ModuleCat.ofHom
              (squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap)) := by
  let := Stacks.Smooth.kerModule hq hsq
  rw [cotangentExtensionClass, squareZeroCotangentClass_eq, naiveCotangentBaseMap_eq_Q_map]
  exact Q_map_comp_doubleToSingleNegOne _ (towerCompareChainMap_f_neg_one Λ A' A) _

end CotangentClassChain

/-! ### The morphism `NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ}` -/

section BaseChangeMap

variable (Λ R A : Type u) [CommRing Λ] [CommRing R] [CommRing A]
  [Algebra Λ R] [Algebra R A] [Algebra Λ A] [IsScalarTower Λ R A]
  {n : ℕ} (P : Algebra.Generators Λ R (Fin n))

/-- The morphism of extensions from the presentation `Λ[x_1, …, x_n] → R` of `R` to the
canonical presentation `Λ[A] → A` of `A`, determined by the `Λ`-algebra map `R → A`. -/
def toSelfHom : P.toExtension.Hom (Algebra.Generators.self Λ A).toExtension :=
  (P.defaultHom (Algebra.Generators.self Λ A)).toExtensionHom

/-- The conormal component `A ⊗_R J/J² ⟶ J_A/J_A²` of the morphism
`NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ}`. -/
def nlBaseChangeCotangent :
    A ⊗[R] P.toExtension.Cotangent →ₗ[A]
      (Algebra.Generators.self Λ A).toExtension.Cotangent :=
  LinearMap.liftBaseChange A (Algebra.Extension.Cotangent.map (toSelfHom Λ R A P))

/-- On a pure tensor `a ⊗ x`, `nlBaseChangeCotangent` is `a` times the image of `x` under the
map on conormal modules induced by `toSelfHom`. -/
@[simp] theorem nlBaseChangeCotangent_tmul (a : A) (x : P.toExtension.Cotangent) :
    nlBaseChangeCotangent Λ R A P (a ⊗ₜ[R] x) =
      a • Algebra.Extension.Cotangent.map (toSelfHom Λ R A P) x :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The degree-`0` component `A ⊗_R (⊕_i R dx_i) ⟶ ⊕_{a ∈ A} A da` of the morphism
`NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ}`. -/
def nlBaseChangeCotangentSpace :
    A ⊗[R] P.toExtension.CotangentSpace →ₗ[A]
      (Algebra.Generators.self Λ A).toExtension.CotangentSpace :=
  LinearMap.liftBaseChange A (Algebra.Extension.CotangentSpace.map (toSelfHom Λ R A P))

/-- On a pure tensor `a ⊗ x`, `nlBaseChangeCotangentSpace` is `a` times the image of `x` under
the map on cotangent spaces induced by `toSelfHom`. -/
@[simp] theorem nlBaseChangeCotangentSpace_tmul (a : A) (x : P.toExtension.CotangentSpace) :
    nlBaseChangeCotangentSpace Λ R A P (a ⊗ₜ[R] x) =
      a • Algebra.Extension.CotangentSpace.map (toSelfHom Λ R A P) x :=
  LinearMap.liftBaseChange_tmul _ _ _ _

/-- The two components commute with the differentials. -/
theorem nlBaseChange_comm :
    ModuleCat.ofHom (nlBaseChangeCotangent Λ R A P) ≫
        ModuleCat.ofHom (Algebra.Generators.self Λ A).toExtension.cotangentComplex =
      ModuleCat.ofHom (P.toExtension.cotangentComplex.baseChange A) ≫
        ModuleCat.ofHom (nlBaseChangeCotangentSpace Λ R A P) := by
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun x => ?_
  induction x using TensorProduct.inductionOn with
  | tmul a y =>
      change (Algebra.Generators.self Λ A).toExtension.cotangentComplex
          (nlBaseChangeCotangent Λ R A P (a ⊗ₜ[R] y)) =
        nlBaseChangeCotangentSpace Λ R A P
          (P.toExtension.cotangentComplex.baseChange A (a ⊗ₜ[R] y))
      rw [nlBaseChangeCotangent_tmul, map_smul, LinearMap.baseChange_tmul,
        nlBaseChangeCotangentSpace_tmul,
        Algebra.Extension.CotangentSpace.map_cotangentComplex]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The chain map `[A ⊗_R J/J² → A ⊗_R ⊕_i R dx_i] ⟶ [J_A/J_A² → ⊕_a A da]` realizing
`NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ}`. -/
def nlBaseChangeChainMap :
    double (ModuleCat.ofHom (P.toExtension.cotangentComplex.baseChange A))
        upIntRelNegOneZero ⟶
      double (ModuleCat.ofHom (Algebra.Generators.self Λ A).toExtension.cotangentComplex)
        upIntRelNegOneZero :=
  mkHomFromDouble upIntRelNegOneZero NaiveCotangent.TwoTerm.negOne_ne_zero
    (ModuleCat.ofHom (nlBaseChangeCotangent Λ R A P) ≫
      (doubleXIso₀ (ModuleCat.ofHom
        (Algebra.Generators.self Λ A).toExtension.cotangentComplex) upIntRelNegOneZero).inv)
    (ModuleCat.ofHom (nlBaseChangeCotangentSpace Λ R A P) ≫
      (doubleXIso₁ (ModuleCat.ofHom
        (Algebra.Generators.self Λ A).toExtension.cotangentComplex) upIntRelNegOneZero
        NaiveCotangent.TwoTerm.negOne_ne_zero).inv)
    (by
      rw [double_d _ _ NaiveCotangent.TwoTerm.negOne_ne_zero]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [← Category.assoc, nlBaseChange_comm, Category.assoc])
    (fun k hk => by
      rw [double_d_eq_zero₀ _ _ _ _ (by omega : (0 : ℤ) ≠ -1)]
      simp)

/-- In degree `-1`, the chain map `nlBaseChangeChainMap` is `nlBaseChangeCotangent`. -/
theorem nlBaseChangeChainMap_f_neg_one :
    (nlBaseChangeChainMap Λ R A P).f (-1) =
      (doubleXIso₀ (ModuleCat.ofHom (P.toExtension.cotangentComplex.baseChange A))
        upIntRelNegOneZero).hom ≫ ModuleCat.ofHom (nlBaseChangeCotangent Λ R A P) ≫
          (doubleXIso₀ (ModuleCat.ofHom
            (Algebra.Generators.self Λ A).toExtension.cotangentComplex)
            upIntRelNegOneZero).inv := by
  rw [nlBaseChangeChainMap, mkHomFromDouble_f₀]

/-- **The morphism `NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ}`** in the derived category of `A`-modules:
functoriality of the naive cotangent complex for the `Λ`-algebra map `R → A`, with the source
written as the termwise base change of the two-term complex of the presentation
`Λ[x_1, …, x_n] → R`. -/
@[stacks 07YI "the map NL_{R/Λ} ⊗_R A → NL_{A/Λ}"]
def nlBaseChangeToNaive :
    DerivedCategory.Q.obj (double
        (ModuleCat.ofHom (P.toExtension.cotangentComplex.baseChange A))
        upIntRelNegOneZero) ⟶
      derivedNaiveCotangentComplex Λ A :=
  DerivedCategory.Q.map (nlBaseChangeChainMap Λ R A P)

/-- Composing `NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ}` with the class of a functional on the conormal
module of the canonical presentation gives the class of the functional precomposed with the
conormal component. -/
theorem nlBaseChangeToNaive_comp_doubleToSingleNegOne (W : ModuleCat.{u} A)
    (g : ModuleCat.of A (Algebra.Generators.self Λ A).toExtension.Cotangent ⟶ W) :
    nlBaseChangeToNaive Λ R A P ≫
        DerivedCategory.Q.map (doubleToSingleNegOne (ModuleCat.ofHom
          (Algebra.Generators.self Λ A).toExtension.cotangentComplex) g) =
      DerivedCategory.Q.map (doubleToSingleNegOne
        (ModuleCat.ofHom (P.toExtension.cotangentComplex.baseChange A))
        (ModuleCat.ofHom (nlBaseChangeCotangent Λ R A P) ≫ g)) := by
  exact Q_map_comp_doubleToSingleNegOne _ (nlBaseChangeChainMap_f_neg_one Λ R A P) g

end BaseChangeMap

/-! ### The composite `NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ} ⟶ NL_{A/A'} = I[1]` -/

section Composition

variable (Λ R A A' : Type u) [CommRing Λ] [CommRing R] [CommRing A] [CommRing A']
  [Algebra Λ R] [Algebra R A] [Algebra Λ A] [IsScalarTower Λ R A]
  [Algebra Λ A'] [Algebra A' A] [IsScalarTower Λ A' A]
  {n : ℕ} (P : Algebra.Generators Λ R (Fin n))
  (hq : Function.Surjective (algebraMap A' A))
  (hsq : RingHom.ker (algebraMap A' A) ^ 2 = ⊥)

/-- **The functional computing the composite**: the `A`-linear map `A ⊗_R J/J² → I` obtained
from the conormal maps of the two comparisons of presentations, followed by the identification
`I/I² = I` of the square-zero surjection. -/
def compositeObsFunctional :
    letI := Stacks.Smooth.kerModule hq hsq
    A ⊗[R] P.toExtension.Cotangent →ₗ[A] RingHom.ker (algebraMap A' A) :=
  letI := Stacks.Smooth.kerModule hq hsq
  ((squareZeroKernelCotangentEquiv A' A hq hsq).symm.toLinearMap ∘ₗ
      Algebra.Extension.Cotangent.map (squareZeroCompareHom A' A hq) ∘ₗ
      ((Algebra.Extension.Cotangent.map (towerCompareHom Λ A' A)).restrictScalars A)) ∘ₗ
    nlBaseChangeCotangent Λ R A P

/-- **Stacks 07YI: the invariant description of the obstruction element.** The composite
`NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ} ⟶ NL_{A/A'} = I[1]` in the derived category of `A`-modules is the
class of the conormal functional `compositeObsFunctional`. -/
@[stacks 07YI "the composite NL_{R/Λ} ⊗_R A → NL_{A/Λ} → NL_{A/A'} = I[1]"]
theorem cotangentComposition_eq :
    letI := Stacks.Smooth.kerModule hq hsq
    nlBaseChangeToNaive Λ R A P ≫ cotangentExtensionClass Λ A' A hq hsq =
      DerivedCategory.Q.map (doubleToSingleNegOne
        (ModuleCat.ofHom (P.toExtension.cotangentComplex.baseChange A))
        (ModuleCat.ofHom (compositeObsFunctional Λ R A A' P hq hsq))) := by
  let := Stacks.Smooth.kerModule hq hsq
  rw [cotangentExtensionClass_eq, nlBaseChangeToNaive_comp_doubleToSingleNegOne]
  rfl

/-- The comparison of the presentation `Λ[x_1, …, x_n] → R` with the square-zero thickening
`A' → A`, as a `Λ`-algebra map `Λ[x_1, …, x_n] → A'`. -/
def canonicalLiftAlgHom : P.toExtension.Ring →ₐ[Λ] A' where
  __ := (squareZeroCompareHom A' A hq).toRingHom.comp
    ((towerCompareHom Λ A' A).toRingHom.comp (toSelfHom Λ R A P).toRingHom)
  commutes' x := by
    change (squareZeroCompareHom A' A hq).toRingHom
        ((towerCompareHom Λ A' A).toRingHom
          ((toSelfHom Λ R A P).toRingHom
            (algebraMap Λ P.toExtension.Ring x))) = algebraMap Λ A' x
    rw [(toSelfHom Λ R A P).toRingHom_algebraMap,
      (towerCompareHom Λ A' A).toRingHom_algebraMap,
      (squareZeroCompareHom A' A hq).toRingHom_algebraMap]
    change (algebraMap A' A') ((algebraMap Λ A') x) = (algebraMap Λ A') x
    simp

/-- Reducing the comparison `Λ[x_1, …, x_n] → A'` modulo `I` is the map `Λ[x_1, …, x_n] → A`
of the presentation of `R` followed by `R → A`. -/
theorem algebraMap_canonicalLiftAlgHom (x : P.toExtension.Ring) :
    algebraMap A' A (canonicalLiftAlgHom Λ R A A' P hq x) =
      algebraMap R A (algebraMap P.toExtension.Ring R x) := by
  change algebraMap (squareZeroExtension A' A hq).Ring A
      ((squareZeroCompareHom A' A hq).toRingHom
        ((towerCompareHom Λ A' A).toRingHom ((toSelfHom Λ R A P).toRingHom x))) =
    algebraMap R A (algebraMap P.toExtension.Ring R x)
  rw [(squareZeroCompareHom A' A hq).algebraMap_toRingHom
      ((towerCompareHom Λ A' A).toRingHom ((toSelfHom Λ R A P).toRingHom x)),
    (towerCompareHom Λ A' A).algebraMap_toRingHom ((toSelfHom Λ R A P).toRingHom x),
    (toSelfHom Λ R A P).algebraMap_toRingHom x]
  simp

/-- The lift in `A'` of the `i`-th coordinate of the object `x`, determined by the comparison
of the presentation `Λ[x_1, …, x_n] → R` with the square-zero thickening `A' → A`. -/
def canonicalLift (i : Fin n) : A' :=
  canonicalLiftAlgHom Λ R A A' P hq (MvPolynomial.X i)

/-- The elements `canonicalLift i` are lifts of the coordinates `a_i = x(x_i)` of the
object. -/
theorem algebraMap_canonicalLift (i : Fin n) :
    algebraMap A' A (canonicalLift Λ R A A' P hq i) = algebraMap R A (P.val i) := by
  refine (algebraMap_canonicalLiftAlgHom Λ R A A' P hq (MvPolynomial.X i)).trans ?_
  congr 1
  exact (Deformation.Artin.KeyExample.Situation.algebraMap_extensionRing
    (P := P) (MvPolynomial.X i)).trans (MvPolynomial.aeval_X _ _)

/-- The comparison map is evaluation at the lifts `canonicalLift i`. -/
theorem canonicalLiftAlgHom_eq_aeval :
    canonicalLiftAlgHom Λ R A A' P hq =
      (MvPolynomial.aeval (canonicalLift Λ R A A' P hq) :
        P.toExtension.Ring →ₐ[Λ] A') :=
  MvPolynomial.algHom_ext fun i => (MvPolynomial.aeval_X (canonicalLift Λ R A A' P hq) i).symm

/-- The value of a relation at the lifts lies in `I = Ker(A' → A)`. -/
theorem canonicalLiftAlgHom_mem_ker (f : P.toExtension.ker) :
    canonicalLiftAlgHom Λ R A A' P hq f.1 ∈ RingHom.ker (algebraMap A' A) := by
  rw [RingHom.mem_ker, algebraMap_canonicalLiftAlgHom, RingHom.mem_ker.1 f.2, map_zero]

/-- **The functional computing the composite is evaluation of relations at the lifts.** On
`1 ⊗ (class of f)` it is `f(a'_1, …, a'_n)`, the value of `f ∈ J` at the lifts. -/
theorem compositeObsFunctional_one_tmul_mk (f : P.toExtension.ker) :
    letI := Stacks.Smooth.kerModule hq hsq
    compositeObsFunctional Λ R A A' P hq hsq
        (1 ⊗ₜ[R] Algebra.Extension.Cotangent.mk f) =
      ⟨canonicalLiftAlgHom Λ R A A' P hq f.1,
        canonicalLiftAlgHom_mem_ker Λ R A A' P hq f⟩ := by
  let := Stacks.Smooth.kerModule hq hsq
  have hmk : nlBaseChangeCotangent Λ R A P (1 ⊗ₜ[R] Algebra.Extension.Cotangent.mk f) =
      Algebra.Extension.Cotangent.map (toSelfHom Λ R A P)
        (Algebra.Extension.Cotangent.mk f) := by
    rw [nlBaseChangeCotangent_tmul, one_smul]
  change (squareZeroKernelCotangentEquiv A' A hq hsq).symm
      (Algebra.Extension.Cotangent.map (squareZeroCompareHom A' A hq)
        (Algebra.Extension.Cotangent.map (towerCompareHom Λ A' A)
          (nlBaseChangeCotangent Λ R A P
            (1 ⊗ₜ[R] Algebra.Extension.Cotangent.mk f)))) = _
  rw [hmk, LinearEquiv.symm_apply_eq]
  change Algebra.Extension.Cotangent.map (squareZeroCompareHom A' A hq)
      (Algebra.Extension.Cotangent.map (towerCompareHom Λ A' A)
        (Algebra.Extension.Cotangent.map (toSelfHom Λ R A P)
          (Algebra.Extension.Cotangent.mk f))) =
    Algebra.Extension.Cotangent.mk
      (⟨canonicalLiftAlgHom Λ R A A' P hq f.1,
        canonicalLiftAlgHom_mem_ker Λ R A A' P hq f⟩ : RingHom.ker (algebraMap A' A))
  rw [Algebra.Extension.Cotangent.map_mk, Algebra.Extension.Cotangent.map_mk,
    Algebra.Extension.Cotangent.map_mk]
  exact DFunLike.congr_arg Algebra.Extension.Cotangent.mk (Subtype.ext rfl)

/-- **The conormal functional of the composite, in coordinates**: on `1 ⊗ (class of f)` it is
`f(a'_1, …, a'_n)`, where `a'_i` are the lifts `canonicalLift i`. This is the map `J/J² → I`
of Stacks 07YI. -/
@[stacks 07YI "the composite is represented by the map f ↦ f(a'_1, …, a'_n)"]
theorem coe_compositeObsFunctional_one_tmul_mk (f : P.toExtension.ker) :
    letI := Stacks.Smooth.kerModule hq hsq
    ((compositeObsFunctional Λ R A A' P hq hsq
          (1 ⊗ₜ[R] Algebra.Extension.Cotangent.mk f)).1 : A') =
      (MvPolynomial.aeval (canonicalLift Λ R A A' P hq) :
        P.toExtension.Ring →ₐ[Λ] A') f.1 := by
  let := Stacks.Smooth.kerModule hq hsq
  rw [compositeObsFunctional_one_tmul_mk, ← canonicalLiftAlgHom_eq_aeval]
  rfl

/-- **Stacks 07YI: the obstruction element is the composite of cotangent complexes.** Under
the identification of `Hom_{D(A)}(NL_{R/Λ} ⊗_R A, I[1]) = Ext¹_A(NL_{R/Λ} ⊗_R A, I)` with the
cokernel `Hom_A(A ⊗_R J/J², I)/Hom_A(A ⊗_R R^{⊕n}, I)`, the composite
`NL_{R/Λ} ⊗_R A ⟶ NL_{A/Λ} ⟶ NL_{A/A'} = I[1]` is the class of the functional whose value on
`1 ⊗ (class of f)` is `f(a'_1, …, a'_n)`, for the lifts `a'_i = canonicalLift i` of the
coordinates of `x`. That class is the obstruction element `o_x(A')` of
`Deformation.Artin.KeyExample.Situation.obsClass`, which by
`Deformation.Artin.KeyExample.Situation.obsClass_eq` does not depend on the chosen lifts. -/
@[stacks 07YI "o_x(A') equals the composite NL_{R/Λ} → NL_{A/Λ} → NL_{A/A'} = I[1]"]
theorem doubleCokernelExtEquiv_cotangentComposition :
    letI := Stacks.Smooth.kerModule hq hsq
    doubleCokernelExtEquiv (P.toExtension.cotangentComplex.baseChange A)
        (RingHom.ker (algebraMap A' A))
        (nlBaseChangeToNaive Λ R A P ≫ cotangentExtensionClass Λ A' A hq hsq) =
      Submodule.Quotient.mk (compositeObsFunctional Λ R A A' P hq hsq) := by
  let := Stacks.Smooth.kerModule hq hsq
  rw [cotangentComposition_eq, doubleCokernelExtEquiv_Q_map]

end Composition

end Deformation.Artin

end
