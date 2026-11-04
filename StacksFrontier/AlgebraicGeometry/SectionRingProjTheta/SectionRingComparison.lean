module

public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Basic
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.GlobalSections
public import StacksFrontier.Topology.Sheaves.Modules.InvertibleAndOperators.SectionRing
public import StacksFrontier.Algebra.DirectSum.ExternalGrading
public import StacksFrontier.AlgebraicGeometry.AmpleFiniteAvoidance.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.NonvanishingSections
public import StacksCore.Tactic.StacksAttribute

/-!
# The two section rings of an invertible sheaf of modules have the same graded carrier

For an invertible sheaf of modules `L`, the graded ring `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})` of
[Stacks, Tag 01CV] has two realisations:

* `Stacks.GradedSections.sectionRing L = ⨁_{n ≥ 0} (𝟙_ C ⟶ L^{⊗ n})`, on morphisms out of the
  monoidal unit and the iterated tensor products `Stacks.TensorPowers.natTensorPow`;
* `Stacks.SheafOfModules.sectionRing O hO L = ⨁_{n ≥ 0} Γ(L^{⊗ n}, ⊤_C)`, on sections over the
  terminal object of the site and the tensor powers
  `Stacks.SheafOfModules.TensorPower.tensorPower` of [Stacks, Tag 01CU].

This file constructs an isomorphism of graded additive groups between them.

## Main definitions

* `Stacks.SectionRingProjTheta.powIso`: the degreewise comparison of the two tensor-power
  families in nonnegative degree, `L^{⊗ n}` in the `natTensorPow` spelling against `L^{⊗ n}` in
  the `tensorPower` spelling.
* `Stacks.SectionRingProjTheta.powSectionsAddEquiv`: the degreewise comparison of the carriers.
* `Stacks.SectionRingProjTheta.sectionRingAddEquiv`: the comparison of the two section rings, as
  an additive isomorphism.
* `Stacks.SectionRingProjTheta.schemeSectionRingAddEquiv` and
  `Stacks.SectionRingProjTheta.sectionSiteSectionRingAddEquiv`: the same for an invertible
  `𝒪_X`-module on a scheme, the second with the structure sheaf spelled as
  `Stacks.SheafOfModules.sectionSiteRing`.

## Main results

* `Stacks.SectionRingProjTheta.sectionRingAddEquiv_of` and
  `Stacks.SectionRingProjTheta.sectionRingAddEquiv_symm_of`: the comparison on a homogeneous
  element, in both directions.
* `Stacks.SectionRingProjTheta.map_summand_eq_sectionRingGrading`: the comparison carries the
  `n`-th homogeneous piece of one ring onto the `n`-th homogeneous piece of the other.
* `Stacks.SectionRingProjTheta.map_grading_eq_sectionRingGrading`: the same for the grading
  `Stacks.AmpleFiniteAvoidance.grading` of a scheme.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open CategoryTheory Category MonoidalCategory Limits Opposite
open Stacks.SheafOfModules.TensorSheafification

open scoped DirectSum

universe v u w

namespace Stacks.SectionRingProjTheta

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} [HasTerminal C]
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.braidedCategory

variable (L : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  [AlgebraicGeometry.SheafOfModules.IsInvertible 𝒪 h𝒪 L]

/-- Post-composition with an isomorphism, as an additive isomorphism of the groups of morphisms
out of the monoidal unit. -/
def postcompAddEquiv {A B : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)} (e : A ≅ B) :
    (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ A) ≃+
      (𝟙_ (SheafOfModules.{w} (structureSheaf 𝒪 h𝒪)) ⟶ B) where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by simp
  right_inv g := by simp
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- The degreewise comparison of the two tensor-power families, in the nonnegative degree the
section ring is graded over. -/
def powIso (n : ℕ) :
    Stacks.TensorPowers.natTensorPow L n ≅
      Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L (n : ℤ) :=
  eqToIso (AlgebraicGeometry.SheafOfModules.tensorPow_natCast 𝒪 h𝒪 L n).symm ≪≫
    (Stacks.PowerFamilyBridge.natIso 𝒪 h𝒪 L n).symm

/-- The degreewise comparison of the two carriers. -/
def powSectionsAddEquiv (n : ℕ) :
    Stacks.GradedSections.powSections L n ≃+
      (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L (n : ℤ)).val.obj (op (⊤_ C)) :=
  (postcompAddEquiv 𝒪 h𝒪 (powIso 𝒪 h𝒪 L n)).trans
    (Stacks.SectionRingGeometric.tensorUnitHomAddEquiv 𝒪 h𝒪 terminalIsTerminal _)

/-- The comparison of the two section rings, in the forward direction. -/
def sectionRingHom :
    Stacks.GradedSections.sectionRing L →+ Stacks.SheafOfModules.sectionRing 𝒪 h𝒪 L :=
  DirectSum.map fun n ↦ (powSectionsAddEquiv 𝒪 h𝒪 L n).toAddMonoidHom

/-- The comparison of the two section rings, in the backward direction. -/
def sectionRingHomInv :
    Stacks.SheafOfModules.sectionRing 𝒪 h𝒪 L →+ Stacks.GradedSections.sectionRing L :=
  DirectSum.map fun n ↦ (powSectionsAddEquiv 𝒪 h𝒪 L n).symm.toAddMonoidHom

/-- `sectionRingHom` on a homogeneous element of degree `n` is `powSectionsAddEquiv` in degree
`n`. -/
@[simp]
theorem sectionRingHom_of (n : ℕ) (s : Stacks.GradedSections.powSections L n) :
    sectionRingHom 𝒪 h𝒪 L (DirectSum.of _ n s) =
      DirectSum.of _ n (powSectionsAddEquiv 𝒪 h𝒪 L n s) :=
  DirectSum.map_of _ n s

/-- `sectionRingHomInv` on a homogeneous element of degree `n` is the inverse of
`powSectionsAddEquiv` in degree `n`. -/
@[simp]
theorem sectionRingHomInv_of (n : ℕ)
    (s : (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L (n : ℤ)).val.obj (op (⊤_ C))) :
    sectionRingHomInv 𝒪 h𝒪 L (DirectSum.of _ n s) =
      DirectSum.of _ n ((powSectionsAddEquiv 𝒪 h𝒪 L n).symm s) :=
  DirectSum.map_of (fun n ↦ (powSectionsAddEquiv 𝒪 h𝒪 L n).symm.toAddMonoidHom) n s

/-- **The two section rings of an invertible sheaf of modules have the same carrier.**

Degree by degree this is `powSectionsAddEquiv`: a morphism out of the monoidal unit into the
`natTensorPow` spelling of `L^{⊗ n}` against an honest section over `⊤_ C` of the `tensorPower`
spelling. -/
@[stacks 01CV "the repository's two realisations of the graded ring `Γ_*(X, L)` — the
`Stacks.GradedSections.sectionRing` one on morphisms out of the monoidal unit and the
`Stacks.SheafOfModules.sectionRing` one on honest global sections — have the same carrier,
ADDITIVELY and degree by degree, and the grading corresponds
(`map_summand_eq_sectionRingGrading`). The two MULTIPLICATIONS are not identified BY THIS
DECLARATION, which is an `AddEquiv` and nothing more; they ARE identified, by
`Stacks.SectionRingProjTheta.sectionRingEquiv` in
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/SectionRingMultiplicative.lean`, which is
this map with its multiplicativity supplied"]
def sectionRingAddEquiv :
    Stacks.GradedSections.sectionRing L ≃+ Stacks.SheafOfModules.sectionRing 𝒪 h𝒪 L where
  toFun := sectionRingHom 𝒪 h𝒪 L
  invFun := sectionRingHomInv 𝒪 h𝒪 L
  map_add' := (sectionRingHom 𝒪 h𝒪 L).map_add
  left_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of n s => rw [sectionRingHom_of, sectionRingHomInv_of, AddEquiv.symm_apply_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  right_inv x := by
    induction x using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of n s => rw [sectionRingHomInv_of, sectionRingHom_of, AddEquiv.apply_symm_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The comparison of the two section rings on a homogeneous element of degree `n` is
`powSectionsAddEquiv` in degree `n`. -/
@[simp]
theorem sectionRingAddEquiv_of (n : ℕ) (s : Stacks.GradedSections.powSections L n) :
    sectionRingAddEquiv 𝒪 h𝒪 L (DirectSum.of _ n s) =
      DirectSum.of _ n (powSectionsAddEquiv 𝒪 h𝒪 L n s) :=
  sectionRingHom_of 𝒪 h𝒪 L n s

/-- The inverse comparison of the two section rings on a homogeneous element of degree `n` is the
inverse of `powSectionsAddEquiv` in degree `n`. -/
@[simp]
theorem sectionRingAddEquiv_symm_of (n : ℕ)
    (s : (Stacks.SheafOfModules.TensorPower.tensorPower 𝒪 h𝒪 L (n : ℤ)).val.obj (op (⊤_ C))) :
    (sectionRingAddEquiv 𝒪 h𝒪 L).symm (DirectSum.of _ n s) =
      DirectSum.of _ n ((powSectionsAddEquiv 𝒪 h𝒪 L n).symm s) :=
  sectionRingHomInv_of 𝒪 h𝒪 L n s

/-! ### The comparison is graded -/

/-- **The carrier comparison carries the `n`-th homogeneous piece onto the `n`-th homogeneous
piece.** -/
theorem map_summand_eq_sectionRingGrading (n : ℕ) :
    (Stacks.ExternalGrading.summand (Stacks.GradedSections.powSections L) n).map
        (sectionRingAddEquiv 𝒪 h𝒪 L).toAddMonoidHom
      = Stacks.SheafOfModules.sectionRingGrading 𝒪 h𝒪 L n := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, ⟨s, rfl⟩, rfl⟩
    exact ⟨powSectionsAddEquiv 𝒪 h𝒪 L n s, (sectionRingAddEquiv_of 𝒪 h𝒪 L n s).symm⟩
  · rintro x ⟨t, rfl⟩
    refine ⟨DirectSum.of _ n ((powSectionsAddEquiv 𝒪 h𝒪 L n).symm t),
      ⟨(powSectionsAddEquiv 𝒪 h𝒪 L n).symm t, rfl⟩, ?_⟩
    rw [AddEquiv.coe_toAddMonoidHom, sectionRingAddEquiv_of, AddEquiv.apply_symm_apply]

/-- The comparison sends a homogeneous element of degree `n` to a homogeneous element of degree
`n`. -/
theorem mem_sectionRingGrading_of_mem_summand {n : ℕ} {x : Stacks.GradedSections.sectionRing L}
    (hx : x ∈ Stacks.ExternalGrading.summand (Stacks.GradedSections.powSections L) n) :
    sectionRingAddEquiv 𝒪 h𝒪 L x ∈ Stacks.SheafOfModules.sectionRingGrading 𝒪 h𝒪 L n :=
  map_summand_eq_sectionRingGrading 𝒪 h𝒪 L n ▸ AddSubgroup.mem_map_of_mem _ hx

/-! ### Schemes -/

section Scheme

open AlgebraicGeometry

attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

variable {X : Scheme.{u}} (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]

/-- An invertible `𝒪_X`-module is invertible in the sense of [Stacks, Tag 01CU], by
`Stacks.PowerFamilyBridge.instIsInvertible`. -/
local instance schemeStacksIsInvertible :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M :=
  Stacks.PowerFamilyBridge.instIsInvertible X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M

/-- **The two section rings of an invertible `𝒪_X`-module on a scheme have the same carrier,
degree by degree.** -/
def schemeSectionRingAddEquiv :
    Stacks.GradedSections.sectionRing M ≃+
      Stacks.SheafOfModules.sectionRing X.presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M :=
  sectionRingAddEquiv X.presheaf (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M

/-- The comparison carries the `n`-th piece of the grading `Stacks.AmpleFiniteAvoidance.grading`
onto the `n`-th piece of `Stacks.SheafOfModules.sectionRingGrading`. -/
theorem map_grading_eq_sectionRingGrading (n : ℕ) :
    (Stacks.AmpleFiniteAvoidance.grading M n).map
        (schemeSectionRingAddEquiv M).toAddMonoidHom
      = Stacks.SheafOfModules.sectionRingGrading X.presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M n :=
  map_summand_eq_sectionRingGrading X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) M n

/-- The comparison `schemeSectionRingAddEquiv`, with the structure sheaf spelled as
`Stacks.SheafOfModules.sectionSiteRing` and `Stacks.SheafOfModules.sectionSiteSheaf`. -/
def sectionSiteSectionRingAddEquiv :
    Stacks.GradedSections.sectionRing M ≃+
      Stacks.SheafOfModules.sectionRing (Stacks.SheafOfModules.sectionSiteRing X)
        (Stacks.SheafOfModules.sectionSiteSheaf X) M :=
  schemeSectionRingAddEquiv M

end Scheme

end Stacks.SectionRingProjTheta

end
