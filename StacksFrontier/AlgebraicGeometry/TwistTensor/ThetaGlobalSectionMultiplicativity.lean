module

public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaGlobalSectionModule
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaGlobalMultiplicativity
public import StacksFrontier.AlgebraicGeometry.SectionRingProjTheta.PowerCompareAgreement
public import StacksFrontier.AlgebraicGeometry.TwistTensor.ThetaSectionMul

/-!
# Multiplicativity of the twist comparison at the spelling the section ring is graded by

Let `S = ⨁_{k ≥ 0} 𝒮 k` be a graded ring covered in degree one, `X = Proj S`, and let `d` be a
degree with `𝒪_X(d)` invertible. `Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower` is the
comparison `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` with the tensor power taken at
`Stacks.SheafOfModules.TensorPower.tensorPower`, the spelling the graded section ring of [Stacks,
Tag 01CV] is graded by. This file proves that it is **multiplicative on global sections**: it
carries the multiplication of the Laurent algebra of [Stacks, Tag 01CU] to the canonical
multiplication of the twists of Equation 01MO.

## The three steps the comparison is multiplicative through

`thetaSectionPower` is `Stacks.PowerFamilyBridge.tensorPowerModuleIso` followed by
`Stacks.AlgebraicGeometry.ThetaGlobal.thetaInt`, so its multiplicativity is the composite of a
statement about each factor, and in nonnegative degree both are available.

* The first factor is the comparison of the two constructions of the tensor powers. In
  nonnegative degree it is `Stacks.AlgebraicGeometry.CoherentMulSections.powCompare` read
  backwards — that is `thetaSectionPower_natCast` below, by
  `Stacks.SectionRingProjTheta.powIso_eq_tensorPowerCompare` — and
  `Stacks.AlgebraicGeometry.CoherentMulSections.mulSections_mulBilinear` says that comparison
  carries the Laurent multiplication to
  `Stacks.AlgebraicGeometry.ProjChartFromRatios.mulSections`, the product of the iterated tensor
  products on honest global sections.
* That product is the addition law `Stacks.Ample.tensorPowModuleAddIso` of Tag 01CU's powers
  applied to the pure tensor of the two sections, by
  `Stacks.AlgebraicGeometry.ThetaMul.mulSections_eq_tensorPowModuleAddIso`.
* The second factor is multiplicative against that addition law in an arbitrary bidegree, by
  `Stacks.AlgebraicGeometry.ThetaGlobalMul.theta_mul`.

In a nonnegative degree the integer extension plays no part: `thetaInt` at `Int.ofNat m` is the
comparison built by recursion.

## Main results

* `Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower_natCast`: **in nonnegative degree the
  comparison is the comparison of the two tensor-power constructions followed by the recursive
  comparison with the twists.**
* `Stacks.AlgebraicGeometry.ThetaGlobal.theta_mul_modules`: the multiplicativity square of
  `Stacks.AlgebraicGeometry.ThetaGlobal.theta`, restated with no monoidal structure named.
* `Stacks.AlgebraicGeometry.ThetaGlobal.thetaSectionPower_mulBilinear`: **the comparison carries
  the multiplication of the Laurent algebra of [Stacks, Tag 01CU] on global sections to the
  canonical multiplication of the twists**, in an arbitrary pair of nonnegative degrees.

## Implementation notes

The statements are written with no monoidal structure in scope: the tensor product is named
`Stacks.RelativeVeryAmple.tensorModules`, the functorial action
`Stacks.RelativeVeryAmple.tensorModulesMapIso`, and the canonical multiplication of the twists is
retyped as `Stacks.AlgebraicGeometry.ThetaGlobal.twistMulModules`. Two monoidal structures on
`(Proj S).Modules` are in play — `Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal`, which the
multiplicativity square of `theta` is stated against, and
`Stacks.SheafInternalHom.schemeMonoidalCategory`, which the iterated tensor products and so
`powCompare` are formed in — and a goal naming both is not type-correct at the transparency the
rewriting tactics check their motives at. Each half is therefore stated in the section where only
its own structure is installed, and the two are composed where neither is.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
* [Stacks Project, Tag 03GM](https://stacks.math.columbia.edu/tag/03GM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite Limits
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.Ample
open Stacks.RelativeVeryAmple (tensorModules tensorModulesMapIso)

universe u w

namespace Stacks.AlgebraicGeometry.ThetaGlobal

open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover (DegreeOneCover)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (hcover : DegreeOneCover 𝒮) (d : ℕ)
  [IsInvertibleModule (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ))]

/-! ### The canonical multiplication of the twists, with no monoidal structure named -/

section Monoidal

attribute [local instance] Stacks.AlgebraicGeometry.ThetaMul.schemeMonoidal
  Stacks.AlgebraicGeometry.ThetaMul.strictSchemeMonoidal

/-- **The canonical multiplication isomorphism of the `d`-divisible twists in a pair of
natural-number degrees**, `𝒪_X(dn) ⊗ 𝒪_X(dm) ≅ 𝒪_X(d(n+m))`, with its source ascribed at
`Stacks.RelativeVeryAmple.tensorModules` — the tensor product sheaf of [Stacks, Tag 01CA], which
names no monoidal structure. The body is
`Stacks.AlgebraicGeometry.ThetaGlobalMul.twistMulIsoNat`; the ascription is the whole content. -/
def twistMulModules (n m : ℕ) :
    tensorModules (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 ((d : ℤ) * (n : ℤ)))
        (twist 𝒮 ((d : ℤ) * (m : ℤ))) ≅
      twist 𝒮 ((d : ℤ) * ((n + m : ℕ) : ℤ)) :=
  Stacks.AlgebraicGeometry.ThetaGlobalMul.twistMulIsoNat 𝒮 hcover d n m

/-- **The multiplicativity square of the comparison family `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` on all of
`Proj S`, with no monoidal structure named**: the addition law of the tensor powers of [Stacks,
Tag 01CU] followed by the comparison in degree `n + m` is the two comparisons on the two factors
followed by the canonical multiplication at `(dn, dm)`.

This is `Stacks.AlgebraicGeometry.ThetaGlobalMul.theta_mul` with the tensor product of the two
comparisons read as the functorial action of the tensor product sheaf
(`Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom`) and the addition law spelled as
`Stacks.Ample.tensorPowModuleAddIso`, which is what
`Stacks.AlgebraicGeometry.ThetaGlobalMul.thetaStepNat` is. -/
theorem theta_mul_modules (n m : ℕ) :
    (tensorPowModuleAddIso (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) (n : ℤ) (m : ℤ)).hom ≫
        (theta 𝒮 hcover d (n + m)).hom =
      (tensorModulesMapIso (AlgebraicGeometry.Proj 𝒮) (theta 𝒮 hcover d n)
          (theta 𝒮 hcover d m)).hom ≫
        (twistMulModules 𝒮 hcover d n m).hom := by
  rw [Stacks.AlgebraicGeometry.ThetaMul.tensorModulesMapIso_hom]
  exact Stacks.AlgebraicGeometry.ThetaGlobalMul.theta_mul 𝒮 hcover d n m

end Monoidal

/-! ### The comparison in nonnegative degree, and its multiplicativity on global sections -/

/-- **In a nonnegative degree the comparison at the section-ring spelling of the tensor powers is
the comparison of the two constructions of the tensor powers followed by the recursive comparison
with the twists.** The first factor of `thetaSectionPower` is
`Stacks.PowerFamilyBridge.tensorPowerModuleIso`, which in nonnegative degree is
`Stacks.SectionRingProjTheta.powIso` read backwards; and that is
`Stacks.AlgebraicGeometry.CoherentMulSections.powCompare` by
`Stacks.SectionRingProjTheta.powIso_eq_tensorPowerCompare`. The second factor is `thetaInt`,
which at `Int.ofNat n` is `Stacks.AlgebraicGeometry.ThetaGlobal.theta`. -/
theorem thetaSectionPower_natCast (n : ℕ) :
    (thetaSectionPower 𝒮 hcover d (n : ℤ)).hom =
      (powCompare (twist 𝒮 (d : ℤ)) n).inv ≫ (theta 𝒮 hcover d n).hom := by
  have h : powCompare (twist 𝒮 (d : ℤ)) n
      = Stacks.SectionRingProjTheta.powIso (AlgebraicGeometry.Proj 𝒮).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
        (twist 𝒮 (d : ℤ)) n :=
    (Stacks.SectionRingProjTheta.powIso_eq_tensorPowerCompare _ _ _ n).symm
  rw [h]
  rfl

/-- `thetaSectionPower_natCast` read on a global section. -/
theorem thetaSectionPower_app_natCast (n : ℕ)
    (x : (Stacks.SheafOfModules.TensorPower.tensorPower (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
      (twist 𝒮 (d : ℤ)) (n : ℤ)).val.obj (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))) :
    ((thetaSectionPower 𝒮 hcover d (n : ℤ)).hom.val.app
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))) x =
      ((theta 𝒮 hcover d n).hom.val.app (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)))
        ((powCompare (twist 𝒮 (d : ℤ)) n).inv.app (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) x) := by
  rw [thetaSectionPower_natCast]
  rfl

/-- The functorial action of the tensor product sheaf on a pair of isomorphisms, read on a pure
tensor of local sections. This is
`Stacks.SheafOfModules.tensorSections_tensorMapAt` at the spelling
`Stacks.RelativeVeryAmple.tensorModulesMapIso`, which names no monoidal structure.

`tensorModulesMapIso` is the two legs of the curried bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` composed, while
`tensorSections_tensorMapAt` is stated at the map of the uncurried bifunctor on the pair; the two
differ by one `Functor.map_comp`, which is
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`. -/
private theorem tensorSections_tensorModulesMapIso
    {A A' B B' : (AlgebraicGeometry.Proj 𝒮).Modules} (e : A ≅ A') (g : B ≅ B')
    (U : (Opens ↥(AlgebraicGeometry.Proj 𝒮))ᵒᵖ) (s : A.val.obj U) (t : B.val.obj U) :
    (((tensorModulesMapIso (AlgebraicGeometry.Proj 𝒮) e g).hom.val.app U))
        (Stacks.SheafOfModules.tensorSectionsAt (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
          U A B s t) =
      Stacks.SheafOfModules.tensorSectionsAt (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮)) U A' B'
        ((e.hom.val.app U) s) ((g.hom.val.app U) t) :=
  (congrArg
      (fun φ : tensorModules (AlgebraicGeometry.Proj 𝒮) A B ⟶
          tensorModules (AlgebraicGeometry.Proj 𝒮) A' B' =>
        (φ.val.app U) (Stacks.SheafOfModules.tensorSectionsAt (AlgebraicGeometry.Proj 𝒮).presheaf
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
            U A B s t))
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        (AlgebraicGeometry.Proj 𝒮).sheaf e.hom g.hom)).trans
    (Stacks.SheafOfModules.tensorSections_tensorMapAt (AlgebraicGeometry.Proj 𝒮).presheaf
        (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
      U A A' B B' e.hom g.hom s t)

/-- Two equal composites of morphisms of `𝒪_X`-modules agree on a local section, read one factor
at a time. Stated with all four morphisms free: the composite's value on a section is its two
factors' values by definition, and this is the form in which an equation of composites applies to
a goal about sections. -/
private theorem eval_of_comp_eq {A B B' E : (AlgebraicGeometry.Proj 𝒮).Modules}
    (f : A ⟶ B) (g : B ⟶ E) (f' : A ⟶ B') (g' : B' ⟶ E) (h : f ≫ g = f' ≫ g')
    (U : (Opens ↥(AlgebraicGeometry.Proj 𝒮))ᵒᵖ) (z : A.val.obj U) :
    (g.val.app U) ((f.val.app U) z) = (g'.val.app U) ((f'.val.app U) z) :=
  congrArg (fun φ : A ⟶ E => (φ.val.app U) z) h

/-- **The multiplicativity of the comparison on global sections, in the `theta`/`powCompare`
vocabulary.** The three steps are the comparison of the two tensor-power constructions
(`Stacks.AlgebraicGeometry.CoherentMulSections.mulSections_mulBilinear`), the identification of
the product of the iterated powers with the addition law of [Stacks, Tag 01CU]
(`Stacks.AlgebraicGeometry.ThetaMul.mulSections_eq_tensorPowModuleAddIso`), and the
multiplicativity square `theta_mul_modules`. -/
private theorem theta_mulBilinear (a b : ℕ)
    (x : (Stacks.SheafOfModules.TensorPower.tensorPower (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
      (twist 𝒮 (d : ℤ)) (a : ℤ)).val.obj (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)))
    (y : (Stacks.SheafOfModules.TensorPower.tensorPower (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
      (twist 𝒮 (d : ℤ)) (b : ℤ)).val.obj (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))) :
    ((theta 𝒮 hcover d (a + b)).hom.val.app (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)))
        ((powCompare (twist 𝒮 (d : ℤ)) (a + b)).inv.app (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)
          ((Stacks.SheafOfModules.TensorPower.mulBilinear (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
            (twist 𝒮 (d : ℤ)) (a : ℤ) (b : ℤ)).app
              (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)) x y)) =
      ((twistMulModules 𝒮 hcover d a b).hom.val.app
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)))
        (Stacks.SheafOfModules.tensorSectionsAt (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))
          (twist 𝒮 ((d : ℤ) * (a : ℤ))) (twist 𝒮 ((d : ℤ) * (b : ℤ)))
          (((theta 𝒮 hcover d a).hom.val.app (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)))
            ((powCompare (twist 𝒮 (d : ℤ)) a).inv.app
              (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) x))
          (((theta 𝒮 hcover d b).hom.val.app (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)))
            ((powCompare (twist 𝒮 (d : ℤ)) b).inv.app
              (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) y))) := by
  rw [← Stacks.AlgebraicGeometry.CoherentMulSections.mulSections_mulBilinear
      (twist 𝒮 (d : ℤ)) a b x y,
    Stacks.AlgebraicGeometry.ThetaMul.mulSections_eq_tensorPowModuleAddIso
      (AlgebraicGeometry.Proj 𝒮) (twist 𝒮 (d : ℤ)) a b
      ((powCompare (twist 𝒮 (d : ℤ)) a).inv.app (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) x)
      ((powCompare (twist 𝒮 (d : ℤ)) b).inv.app (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens) y)]
  exact (eval_of_comp_eq 𝒮 _ _ _ _ (theta_mul_modules 𝒮 hcover d a b)
      (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)) _).trans
    (congrArg (fun w => ((twistMulModules 𝒮 hcover d a b).hom.val.app
        (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))) w)
      (tensorSections_tensorModulesMapIso 𝒮 (theta 𝒮 hcover d a) (theta 𝒮 hcover d b)
        (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)) _ _))

/-- A pure tensor of local sections is unchanged by rewriting either factor. -/
private theorem tensorSectionsAt_congr {A B : (AlgebraicGeometry.Proj 𝒮).Modules}
    (U : (Opens ↥(AlgebraicGeometry.Proj 𝒮))ᵒᵖ) {s s' : A.val.obj U} {t t' : B.val.obj U}
    (hs : s = s') (ht : t = t') :
    Stacks.SheafOfModules.tensorSectionsAt (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
        U A B s t =
      Stacks.SheafOfModules.tensorSectionsAt (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
        U A B s' t' := by
  rw [hs, ht]

/-- **The comparison `𝒪_X(d)^{⊗ n} ≅ 𝒪_X(dn)` at the spelling the graded section ring of [Stacks,
Tag 01CV] is graded by carries the multiplication of the Laurent algebra of [Stacks, Tag 01CU] on
global sections to the canonical multiplication of the twists of Equation 01MO**, in an arbitrary
pair of nonnegative degrees.

The product on the left is `Stacks.SheafOfModules.TensorPower.mulBilinear`, the multiplication
the graded section ring of Tag 01CV is built from; the product on the right is the canonical
multiplication of Equation 01MO applied to the pure tensor of the two images. This is
`theta_mulBilinear` with both factors of `thetaSectionPower` folded back in by
`thetaSectionPower_app_natCast`. -/
theorem thetaSectionPower_mulBilinear (a b : ℕ)
    (x : (Stacks.SheafOfModules.TensorPower.tensorPower (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
      (twist 𝒮 (d : ℤ)) (a : ℤ)).val.obj (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)))
    (y : (Stacks.SheafOfModules.TensorPower.tensorPower (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
      (twist 𝒮 (d : ℤ)) (b : ℤ)).val.obj (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))) :
    ((thetaSectionPower 𝒮 hcover d ((a + b : ℕ) : ℤ)).hom.val.app
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)))
        ((Stacks.SheafOfModules.TensorPower.mulBilinear (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
          (twist 𝒮 (d : ℤ)) (a : ℤ) (b : ℤ)).app
            (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)) x y) =
      ((twistMulModules 𝒮 hcover d a b).hom.val.app
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens)))
        (Stacks.SheafOfModules.tensorSectionsAt (AlgebraicGeometry.Proj 𝒮).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (AlgebraicGeometry.Proj 𝒮))
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))
          (twist 𝒮 ((d : ℤ) * (a : ℤ))) (twist 𝒮 ((d : ℤ) * (b : ℤ)))
          (((thetaSectionPower 𝒮 hcover d (a : ℤ)).hom.val.app
            (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))) x)
          (((thetaSectionPower 𝒮 hcover d (b : ℤ)).hom.val.app
            (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))) y)) :=
  (thetaSectionPower_app_natCast 𝒮 hcover d (a + b) _).trans
    ((theta_mulBilinear 𝒮 hcover d a b x y).trans
      (congrArg (fun w => ((twistMulModules 𝒮 hcover d a b).hom.val.app
          (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))) w)
        (tensorSectionsAt_congr 𝒮 (op (⊤ : (AlgebraicGeometry.Proj 𝒮).Opens))
          (thetaSectionPower_app_natCast 𝒮 hcover d a x).symm
          (thetaSectionPower_app_natCast 𝒮 hcover d b y).symm)))

end Stacks.AlgebraicGeometry.ThetaGlobal

end
