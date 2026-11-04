module

public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.ZeroTwist
public import StacksFrontier.AlgebraicGeometry.TwistTensor.MultiplicationAssociativity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafBraidingSections

/-!
# The canonical twist multiplication on `Proj S` is commutative and unital

Let `S` be a graded ring and `X = Proj S`. The canonical multiplication maps

`𝒪_X(a) ⊗_{𝒪_X} 𝒪_X(b) ⟶ 𝒪_X(a + b)`

of `Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap` are associative, by
`Stacks.AlgebraicGeometry.TwistTensor.twistMul_assoc`. This file proves the two remaining laws
of a commutative graded algebra for them, as equalities of morphisms of sheaves of modules:
they are *commutative* with respect to the symmetry constraint of Stacks Tag 01CA, and the
inverse of the identification `𝒪_X ≅ 𝒪_X(0)` of
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit` is a two-sided *unit* for
them with respect to the two unitors.

So the family `a ↦ 𝒪_X(a)` carries, at module level, all three laws in arbitrary integer
degrees, over an arbitrary graded ring, and with no hypothesis in the style of Stacks Tag 01MU.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistTensor.braidedCategoryProj`: the symmetry constraint of Stacks
  Tag 01CA on sheaves of modules on `Proj S`, named at the `projStructureRing` spelling of the
  structure sheaf of rings so that instance search finds it beside
  `Stacks.AlgebraicGeometry.TwistTensor.monoidalCategoryProj`.
* `Stacks.AlgebraicGeometry.TwistTensor.twistUnit`: the unit `𝒪_X ⟶ 𝒪_X(0)`, as a morphism out
  of the monoidal unit of Stacks Tag 01CA.

## Main results

* `Stacks.AlgebraicGeometry.TwistTensor.mulSection_comm`: the product of two local sections of
  twists is commutative, modulo the transport along `b + a = a + b`.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMul_comm`: **commutativity.**
  `twistMul a b` is the symmetry constraint followed by `twistMul b a`, followed by the
  `eqToHom` of `b + a = a + b`.
* `Stacks.AlgebraicGeometry.TwistTensor.twistUnit_val_app_apply`: the unit carries a local
  section of `𝒪_X` to the family of its values, which holds by `rfl`.
* `Stacks.AlgebraicGeometry.TwistTensor.twistMul_one` and
  `Stacks.AlgebraicGeometry.TwistTensor.one_twistMul`: **the two unit laws.** Whiskering the
  unit onto `𝒪_X(a)` on either side and multiplying is the corresponding unitor, followed by
  the `eqToHom` of `a + 0 = a`, respectively `0 + a = a`.

## Implementation notes

**The braiding is registered at the spelling the twists use.**
`Stacks.SheafOfModules.Strict.braidedCategory` takes the presheaf of commutative rings and a
proof of the sheaf condition, exactly as `Stacks.SheafOfModules.Strict.monoidalCategory` does,
and `monoidalCategoryProj` is that monoidal structure at the arguments
`(ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj` and `isSheaf_structureRingPresheaf 𝒮`. So
`braidedCategoryProj` is the braided structure at the same two arguments, and the section
formula `Stacks.SheafOfModules.braiding_tensorSectionsAt` applies to a goal written with
`PresheafOfModules.tensorSheafUnit`: the sheafification unit of the tensor product has one
spelling per world and they are equal by `rfl`
(`Stacks.SheafOfModules.tensorSheafificationUnit_app_eq_tensorSectionsAt`).

**Which `𝒪(0) ≅ 𝒪` the unit laws are about.** It is
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit`, whose inverse
`𝒪_X ⟶ 𝒪_X(0)` is `HomogeneousLocalization.val` at every point and hence has a formula on
local sections — `twistUnit_val_app_apply` below is `rfl`. The monoidal unit of
`monoidalCategoryProj` is `SheafOfModules.unit` of the structure sheaf of rings, and the two
spellings of that ring sheaf agree by `rfl`, so the inverse of that isomorphism already *is* a
morphism out of the monoidal unit; the ascription in `twistUnit` is the whole content of the
definition. No second identification of `𝒪_X(0)` with `𝒪_X` is introduced.

**The computation is the same as for associativity.** Each of the three
laws is proved by evaluating both composites on the image of a local pure tensor and quoting
the corresponding law of the homogeneous localizations at a point: `mul_comm` for
commutativity, `mul_comm` again together with the scalar action for the unit laws — the
scalar action of a local section `r` of `𝒪_X` on a local section `s` of `𝒪_X(a)` has value
`val (r x) * s x` at `x`, by `rfl`, which is why the unitors meet the multiplication maps at
all. The section-level handle is
`Stacks.AlgebraicGeometry.TwistTensor.mulSection_apply`, and the extensionality principle is
`PresheafOfModules.tensorSheaf_hom_ext` in the one-level form; no twice-iterated tensor product
occurs, so `PresheafOfModules.tensorSheaf_hom_ext₂` is not needed here.

## References

* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO) — the twists of the
  structure sheaf on `Proj S` and the canonical maps between them.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules, with its associator, unitors and symmetry constraint.
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN) — the zeroth twist is
  the structure sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open PresheafOfModules
open Stacks.AlgebraicGeometry.ProjInvertibleLocus
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistTensor

universe u w

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

attribute [local instance_reducible] ProjectiveSpectrum.top

attribute [local instance] monoidalCategoryProj

/-! ### The symmetry constraint, named at the spelling the twists use -/

/-- **The symmetry constraint of Stacks Tag 01CA on sheaves of modules on `Proj S`**, named at
the `projStructureRing` spelling of the structure sheaf of rings, so that it sits beside
`Stacks.AlgebraicGeometry.TwistTensor.monoidalCategoryProj` and is found by instance search at
the same key. Its braiding is the sheafification of the braiding of the underlying presheaves of
modules, which exchanges the two factors of a local pure tensor. -/
@[instance_reducible]
def braidedCategoryProj : BraidedCategory (SheafOfModules.{u} (projStructureRing 𝒮)) :=
  Stacks.SheafOfModules.Strict.braidedCategory
    (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj (isSheaf_structureRingPresheaf 𝒮)

attribute [local instance] braidedCategoryProj

/-- **The symmetry constraint on a local pure tensor of sections of two twists**: it exchanges
the two factors. -/
theorem braiding_val_app_tensorSheafUnit (a b : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (s : (twist 𝒮 a).val.obj U) (t : (twist 𝒮 b).val.obj U) :
    (β_ (twist 𝒮 a) (twist 𝒮 b)).hom.val.app U
        ((tensorSheafUnit (twist 𝒮 a) (twist 𝒮 b)).app U (s ⊗ₜ t)) =
      (tensorSheafUnit (twist 𝒮 b) (twist 𝒮 a)).app U (t ⊗ₜ s) :=
  Stacks.SheafOfModules.braiding_tensorSectionsAt (ProjectiveSpectrum.Proj.structureSheaf 𝒮).obj
    (isSheaf_structureRingPresheaf 𝒮) U (twist 𝒮 a) (twist 𝒮 b) s t

/-! ### Commutativity -/

/-- **The product of two local sections of twists is commutative**, modulo the transport along
`b + a = a + b`. Both sides are sections of `𝒪(a + b)` over `U`, so this is a pointwise
statement, and pointwise it is `mul_comm` in the homogeneous localization. -/
theorem mulSection_comm (a b : ℤ) (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (p : (twist 𝒮 a).val.obj U) (q : (twist 𝒮 b).val.obj U) :
    mulSection 𝒮 a b U p q =
      (eqToHom (congrArg (twist 𝒮) (add_comm b a))).val.app U (mulSection 𝒮 b a U q p) := by
  refine twist_section_ext 𝒮 U _ _ fun x ↦ ?_
  refine Eq.trans ?_ (eqToHom_twist_val_app_apply 𝒮 (add_comm b a) U _ x).symm
  simp only [mulSection_apply]
  exact mul_comm _ _

/-- **Commutativity of the canonical twist multiplication on `Proj S`, at module level.**
Multiplying `𝒪(a) ⊗ 𝒪(b)` down to `𝒪(a + b)` is the same as exchanging the two factors by the
symmetry constraint of Stacks Tag 01CA and multiplying the other way round; the `eqToHom` is the
transport along `b + a = a + b`, which is the only reason the two targets are not literally the
same object.

The degrees are arbitrary integers and `S` is an arbitrary graded ring: nothing here needs the
multiplication maps to be isomorphisms, so no hypothesis in the style of Stacks Tag 01MU
appears. -/
theorem twistMul_comm (a b : ℤ) :
    twistMul 𝒮 a b =
      (β_ (twist 𝒮 a) (twist 𝒮 b)).hom ≫ twistMul 𝒮 b a ≫
        eqToHom (congrArg (twist 𝒮) (add_comm b a)) := by
  refine PresheafOfModules.tensorSheaf_hom_ext
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮)
    (F := twist 𝒮 a) (G := twist 𝒮 b) (Q := twist 𝒮 (a + b)) fun U p q ↦ ?_
  refine Eq.trans ?_ (comp_val_app_apply 𝒮 _ _ U _).symm
  refine Eq.trans (mulSection_comm 𝒮 a b U p q) (congrArg _ ?_)
  exact (congrArg ((twistMul 𝒮 b a).val.app U)
    (braiding_val_app_tensorSheafUnit 𝒮 a b U p q)).symm

/-! ### The unit -/

/-- **The unit `𝒪_X ⟶ 𝒪_X(0)` of the twists**, as a morphism out of the monoidal unit of Stacks
Tag 01CA. The body is the inverse of
`Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit`, the identification of the
zeroth twist with the structure sheaf that is `HomogeneousLocalization.val` at every point; the
ascription of its source at `𝟙_` is the whole content. -/
def twistUnit : 𝟙_ (SheafOfModules.{u} (projStructureRing 𝒮)) ⟶ twist 𝒮 0 :=
  (ProjEulerSequence.twistingSheafZeroIsoUnit 𝒮).inv

/-- **The unit on a local section**: it carries a section of `𝒪_X` to the family of the values
of its homogeneous fractions, which is a section of `𝒪_X(0)` because numerator and denominator
have equal degree. -/
theorem twistUnit_val_app_apply (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ)
    (r : (𝟙_ (SheafOfModules.{u} (projStructureRing 𝒮))).val.obj U) (x : U.unop) :
    ((twistUnit 𝒮).val.app U r).1 x = HomogeneousLocalization.val (r.1 x) := rfl

/-- A section of `𝒪(c)` whose values agree with those of the image of `w` under `f : F ⟶ 𝒪(a)` is
the image of `w` under `f` followed by the transport along `a = c`. -/
private theorem eq_comp_eqToHom_apply {a c : ℤ} (h : a = c)
    {F : SheafOfModules.{u} (projStructureRing 𝒮)} (f : F ⟶ twist 𝒮 a)
    (U : (Opens (ProjectiveSpectrum.top 𝒮))ᵒᵖ) (w : F.val.obj U) (z : (twist 𝒮 c).val.obj U)
    (hz : ∀ x : U.unop, z.1 x = (f.val.app U w).1 x) :
    z = (f ≫ eqToHom (congrArg (twist 𝒮) h)).val.app U w :=
  twist_section_ext 𝒮 U _ _ fun x ↦
    (hz x).trans (eqToHom_twist_val_app_apply 𝒮 h U _ x).symm

/-- **The right unit law**, as an equality of morphisms out of `𝒪(a) ⊗ 𝟙`: whiskering the unit
onto `𝒪(a)` on the right and multiplying is the right unitor of Stacks Tag 01CA, followed by the
transport along `a + 0 = a`. Pointwise it is the identity `s x * val (r x) = val (r x) * s x`
between the value of the product section and the value of the scalar multiple. -/
theorem twistMul_one (a : ℤ) :
    twist 𝒮 a ◁ twistUnit 𝒮 ≫ twistMul 𝒮 a 0 =
      (ρ_ (twist 𝒮 a)).hom ≫ eqToHom (congrArg (twist 𝒮) (add_zero a).symm) := by
  refine PresheafOfModules.tensorSheaf_hom_ext
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮)
    (F := twist 𝒮 a) (G := 𝟙_ (SheafOfModules.{u} (projStructureRing 𝒮)))
    (Q := twist 𝒮 (a + 0)) fun U s r ↦ ?_
  have hL : (twist 𝒮 a ◁ twistUnit 𝒮 ≫ twistMul 𝒮 a 0).val.app U
        ((tensorSheafUnit (twist 𝒮 a) (𝟙_ (SheafOfModules.{u} (projStructureRing 𝒮)))).app U
          (s ⊗ₜ r)) =
      mulSection 𝒮 a 0 U s ((twistUnit 𝒮).val.app U r) :=
    (comp_val_app_apply 𝒮 _ _ U _).trans
      (congrArg ((twistMul 𝒮 a 0).val.app U)
        (Stacks.TensorSheafWorld.whiskerLeft_val_app_tensorSheafUnit
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮) (isSheaf_structureRingPresheaf 𝒮) U
          (twist 𝒮 a) (twistUnit 𝒮) s r))
  refine hL.trans (eq_comp_eqToHom_apply 𝒮 (add_zero a).symm _ U _ _ fun x ↦ ?_)
  refine Eq.trans ?_ (congrArg (fun y : (twist 𝒮 a).val.obj U => Subtype.val y x)
    (Stacks.TensorSheafWorld.rightUnitor_hom_val_app_tensorSheafUnit
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮) (isSheaf_structureRingPresheaf 𝒮)
      (twist 𝒮 a) U s r)).symm
  rw [mulSection_apply, twistUnit_val_app_apply]
  exact mul_comm _ _

/-- **The left unit law**, as an equality of morphisms out of `𝟙 ⊗ 𝒪(a)`: whiskering the unit
onto `𝒪(a)` on the left and multiplying is the left unitor of Stacks Tag 01CA, followed by the
transport along `0 + a = a`. Pointwise both sides have value `val (r x) * s x`. -/
theorem one_twistMul (a : ℤ) :
    twistUnit 𝒮 ▷ twist 𝒮 a ≫ twistMul 𝒮 0 a =
      (λ_ (twist 𝒮 a)).hom ≫ eqToHom (congrArg (twist 𝒮) (zero_add a).symm) := by
  refine PresheafOfModules.tensorSheaf_hom_ext
    (Osharp := ProjectiveSpectrum.Proj.structureSheaf 𝒮)
    (F := 𝟙_ (SheafOfModules.{u} (projStructureRing 𝒮))) (G := twist 𝒮 a)
    (Q := twist 𝒮 (0 + a)) fun U r s ↦ ?_
  have hL : (twistUnit 𝒮 ▷ twist 𝒮 a ≫ twistMul 𝒮 0 a).val.app U
        ((tensorSheafUnit (𝟙_ (SheafOfModules.{u} (projStructureRing 𝒮))) (twist 𝒮 a)).app U
          (r ⊗ₜ s)) =
      mulSection 𝒮 0 a U ((twistUnit 𝒮).val.app U r) s :=
    (comp_val_app_apply 𝒮 _ _ U _).trans
      (congrArg ((twistMul 𝒮 0 a).val.app U)
        (Stacks.TensorSheafWorld.whiskerRight_val_app_tensorSheafUnit
          (ProjectiveSpectrum.Proj.structureSheaf 𝒮) (isSheaf_structureRingPresheaf 𝒮) U
          (twistUnit 𝒮) (twist 𝒮 a) r s))
  refine hL.trans (eq_comp_eqToHom_apply 𝒮 (zero_add a).symm _ U _ _ fun x ↦ ?_)
  refine Eq.trans ?_ (congrArg (fun y : (twist 𝒮 a).val.obj U => Subtype.val y x)
    (Stacks.TensorSheafWorld.leftUnitor_hom_val_app_tensorSheafUnit
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮) (isSheaf_structureRingPresheaf 𝒮)
      (twist 𝒮 a) U r s)).symm
  rw [mulSection_apply, twistUnit_val_app_apply]
  rfl

end Stacks.AlgebraicGeometry.TwistTensor

end
