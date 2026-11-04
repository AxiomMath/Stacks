module

public import StacksFrontier.AlgebraicGeometry.Constructions.CoherentMulSections
public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.UnitShiftSectionTensor
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaMultiplicativity

/-!
# The addition law of the tensor powers is the product of the graded section ring

Let `X` be a scheme and `L` an invertible `𝒪_X`-module. The tensor powers of `L` carry two
multiplications:

* `Stacks.Ample.tensorPowModuleAddIso`, the addition law `L^{⊗ n} ⊗ L^{⊗ m} ≅ L^{⊗ (n+m)}` on the
  integer powers of [Stacks, Tag 01CU], whose source is the tensor product sheaf of
  [Stacks, Tag 01CA];
* `Stacks.GradedSections.powAdd`, the addition law on the iterated tensor products
  `Stacks.TensorPowers.natTensorPow`, read in the localized monoidal structure
  `Stacks.SheafInternalHom.monoidalCategory`, which is the multiplication of the graded section
  ring of [Stacks, Tag 01CV].

In nonnegative degree they agree, up to the comparison `Stacks.SheafOfModules.tensorObjIso` of the
localized tensor product with the tensor product sheaf.

## Main results

* `Stacks.AlgebraicGeometry.ThetaMul.tensorPowModuleAddIso_hom_natCast`: the addition law of the
  integer tensor powers in nonnegative degree is the addition law of the iterated tensor products,
  conjugated by the comparison of the two tensor products.
* `Stacks.AlgebraicGeometry.ThetaMul.mulSections_eq_tensorPowModuleAddIso`: the product
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections` of two global sections of nonnegative
  tensor powers is the addition law of Tag 01CU applied to their pure tensor.
* `Stacks.AlgebraicGeometry.ThetaMul.thetaStepNat_hom_eq_powAdd`: the same identity of morphisms
  at `𝒪_{U_d}(d)^{⊗ n} ⊗ 𝒪_{U_d}(d)^{⊗ m} ≅ 𝒪_{U_d}(d)^{⊗ (n+m)}`.

## Implementation notes

Both proofs are composites of `Eq.trans` and `congrArg` rather than rewrites: a goal naming the two
addition laws at once mixes the localized tensor product and the tensor product sheaf, and is
type-correct only at default transparency, so the rewriting tactics refuse it. For the same reason
the two objects of `Stacks.SheafOfModules.tensorObjIso` are left to unification: writing them as
`Stacks.TensorPowers.natTensorPow` makes the elaborator look for a monoidal structure at the
`SheafOfModules` spelling of the ring sheaf, where it is not an instance.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite MonoidalCategory
open AlgebraicGeometry
open Stacks.Ample
open Stacks.AlgebraicGeometry.CommonDegreeTwist
open Stacks.AlgebraicGeometry.ProjTwistTensorPowDegreeOpen
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powAdd powAddIso)

universe u w

namespace Stacks.AlgebraicGeometry.ThetaMul

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- The sheaf condition on the structure presheaf of rings of a scheme. -/
abbrev hStr (X : Scheme.{u}) : Presheaf.IsSheaf (Opens.grothendieckTopology ↥X)
    (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf X.presheaf) :=
  Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X

section Scheme

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]

/-- The addition law of the integer tensor powers of [Stacks, Tag 01CU], in nonnegative degree, is
the addition law `Stacks.GradedSections.powAdd` of the iterated tensor products, conjugated by the
comparison `Stacks.SheafOfModules.tensorObjIso` of the localized tensor product with the tensor
product sheaf of [Stacks, Tag 01CA]. -/
theorem tensorPowModuleAddIso_hom_natCast (n m : ℕ) :
    (tensorPowModuleAddIso X L (n : ℤ) (m : ℤ)).hom
      = (Stacks.SheafOfModules.tensorObjIso X.presheaf (hStr X) _ _).inv ≫ powAdd L n m :=
  have h : (AlgebraicGeometry.SheafOfModules.tensorPowAddIso X.presheaf (hStr X) L
        (n : ℤ) (m : ℤ)).hom = powAdd L n m :=
    (congrArg Iso.hom
      (AlgebraicGeometry.SheafOfModules.tensorPowAddIso_natCast X.presheaf (hStr X) L n m)).trans
      (Stacks.GradedSections.powAddIso_hom L n m)
  (addIsoSheaf_hom X.presheaf (hStr X) L (n : ℤ) (m : ℤ)).trans
    (congrArg (fun φ => (Stacks.SheafOfModules.tensorObjIso X.presheaf (hStr X) _ _).inv ≫ φ) h)

/-- The product of the graded section ring of [Stacks, Tag 01CV] on global sections is the
addition law of the tensor powers of [Stacks, Tag 01CU], applied to the pure tensor of the two
sections. -/
theorem mulSections_eq_tensorPowModuleAddIso (n m : ℕ)
    (u : Γ(natTensorPow L n, ⊤)) (v : Γ(natTensorPow L m, ⊤)) :
    Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections L u v
      = (tensorPowModuleAddIso X L (n : ℤ) (m : ℤ)).hom.val.app (op (⊤ : X.Opens))
          (Stacks.SheafOfModules.tensorSectionsAt X.presheaf (hStr X) (op (⊤ : X.Opens))
            (natTensorPow L n) (natTensorPow L m) u v) := by
  have hpow : powAdd L n m
      = (Stacks.SheafOfModules.tensorObjIso X.presheaf (hStr X)
          (natTensorPow L n) (natTensorPow L m)).hom ≫
        (tensorPowModuleAddIso X L (n : ℤ) (m : ℤ)).hom :=
    (Iso.inv_comp_eq _).mp (tensorPowModuleAddIso_hom_natCast X L n m).symm
  have hsplit : Stacks.GradedSections.mulMap
        (Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf L u) m
      = ((λ_ (natTensorPow L m)).inv ≫
          ((Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf L u) ▷ natTensorPow L m) ≫
            (Stacks.SheafOfModules.tensorObjIso X.presheaf (hStr X)
              (natTensorPow L n) (natTensorPow L m)).hom) ≫
        (tensorPowModuleAddIso X L (n : ℤ) (m : ℤ)).hom :=
    (Stacks.GradedSections.mulMap_eq
        (Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf L u) m).trans
      ((congrArg (fun φ => (λ_ (natTensorPow L m)).inv ≫
            ((Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf L u) ▷ natTensorPow L m) ≫ φ)
          hpow).trans
        ((congrArg (fun φ => (λ_ (natTensorPow L m)).inv ≫ φ)
            (Category.assoc _ _ _).symm).trans
          (Category.assoc _ _ _).symm))
  have hu : ((AlgebraicGeometry.SheafOfModules.unitIso X.presheaf (hStr X)).inv ≫
        Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf L u).val.app (op (⊤ : X.Opens))
          (1 : X.presheaf.obj (op (⊤ : X.Opens))) = u :=
    Stacks.AlgebraicGeometry.ProjChartFromRatios.globalSection_secOf L u
  exact (congrArg (fun φ => SheafOfModules.Hom.val φ |>.app (op (⊤ : X.Opens)) v) hsplit).trans
    ((SheafOfModules.comp_val_app_apply _ _ (op (⊤ : X.Opens)) v).trans
      (congrArg
        ((tensorPowModuleAddIso X L (n : ℤ) (m : ℤ)).hom.val.app (op (⊤ : X.Opens)))
        ((Stacks.SheafOfModules.tensorObjIso_hom_val_app_whiskerRight X.presheaf (hStr X)
            (natTensorPow L n) (natTensorPow L m)
            (Stacks.AlgebraicGeometry.ProjChartFromRatios.secOf L u)
            (op (⊤ : X.Opens)) v).trans
          (congrArg (fun w => Stacks.SheafOfModules.tensorSectionsAt X.presheaf (hStr X)
            (op (⊤ : X.Opens)) (natTensorPow L n) (natTensorPow L m) w v) hu))))

end Scheme

section DegreeOpen

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-- The addition law `thetaStepNat` of the tensor powers of `𝒪_{U_d}(d)` is the product
`Stacks.GradedSections.powAdd` of the graded section ring of `𝒪_{U_d}(d)`, up to the comparison of
the two tensor products. -/
theorem thetaStepNat_hom_eq_powAdd (n m : ℕ) :
    (thetaStepNat 𝒮 d n m).hom
      = (Stacks.SheafOfModules.tensorObjIso
            (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme.presheaf
            (hStr (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme) _ _).inv ≫
          powAdd (twist 𝒮 d (d : ℤ)) n m :=
  tensorPowModuleAddIso_hom_natCast (AlgebraicGeometry.Proj.degreeOpen 𝒮 d).toScheme
    (twist 𝒮 d (d : ℤ)) n m

end DegreeOpen

end Stacks.AlgebraicGeometry.ThetaMul

end
