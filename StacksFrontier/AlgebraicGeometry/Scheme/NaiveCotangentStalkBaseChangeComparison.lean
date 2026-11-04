module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeMap

/-!
# The stalk of the canonical map of Stacks 0E1Y

Let `a : A ⟶ B` and `b : B ⟶ C` be morphisms of sheaves of commutative rings on a topological
space `T` and let `z` be a point of `T`.  Stacks 0E1Y attaches to the tower the canonical map
`c₁ : NL_{B/A} ⊗_B C ⟶ NL_{C/A}` of complexes of sheaves of `C`-modules
(`Stacks.SheafOfModules.baseChangeNaiveCotangentMap`).  This file identifies its stalk at `z`,
degreewise, with the ring-level comparison map
`NaiveCotangent.nlExtensionBaseChangeMap h` of

`NL_{B_z/A_z} ⊗_{B_z} C_z ⟶ NL_{C_z/A_z}`,

for `h` the morphism of canonical presentations of the stalks attached to the square with
vertical morphisms `𝟙 A` and `b`
(`Stacks.NaiveCotangentAffineStalkLegs.generatorsSelfStalkHomOfSquare`).  The two sides are
compared through the two identifications of
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeMap`, that is
`Stacks.NaiveCotangentStalkBaseChange.stalkBaseChangeAddEquivNegOne` and
`stalkBaseChangeAddEquivZero` on the source, and the two legs of Stacks 0D09
(`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` and `stalkLegZeroLinear`) on the
target.

This is the stalkwise content of Stacks 0FJZ: the canonical map is a quasi-isomorphism as soon
as each of its stalks is, and each of its stalks is the ring-level comparison map, whose
quasi-isomorphy is `NaiveCotangent.isQuasiIso_nlExtensionBaseChangeMap_of_flat_base` and its
localized relatives.

## The proof

`baseChangeNaiveCotangentMap` is by definition the composite of the termwise base change of the
square map of Stacks 08TX with the counit of extension and restriction of scalars, so its stalk
splits into two legs (`stalkFunctor_map_baseChangeNaiveCotangentMap_apply`).  On the pure tensor
`c ⊗ ω`:

* the first leg is `c ⊗ (stalk of the square map) ω`, by the functoriality
  `Opens.stalkTowerExtendScalars_map_apply` of the interchange of extension of scalars with
  taking topological stalks (`stalkFunctor_map_towerExtendScalarsComplexes_inv_tmul`);
* the second leg multiplies out, `c ⊗ m ↦ c • m`, by
  `Opens.stalkFunctor_map_towerCounit_apply` together with
  `Opens.restrictScalarsStalkFunctorIso_hom_app_apply` and
  `ModuleCat.extendRestrictScalarsAdj_counit_app_apply_tmul`;
* the scalar moves across the leg of Stacks 0D09 by
  `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_smul_fiber`, and the leg carries
  the stalk of the square map to `Algebra.Extension.Cotangent.map h` by the naturality of that
  leg in the square, which is
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_zero`
  in degree `0` and its degree `-1` companion;
* the result is the value of `NaiveCotangent.nlExtensionBaseChangeMap h` on `c ⊗ ω`, since
  that map is degreewise `LinearMap.liftBaseChange` of the functorial map.

Both sides are additive in the argument, so `tmul_ext` reduces the statement to pure tensors.

## Main results

* `Stacks.NaiveCotangentStalkBaseChange.stalkLegNegOneLinear_baseChangeNaiveCotangentMap` and
  `stalkLegZeroLinear_baseChangeNaiveCotangentMap`: **the stalk of the canonical map of
  Stacks 0E1Y, in degrees `-1` and `0`.**
* `Stacks.NaiveCotangentStalkBaseChange.baseChangeSquareMap_eq`: the square whose adjoint the
  canonical map is, read at the site of opens of a space.  This is what lets the naturality of
  the legs of Stacks 0D09 in a square, which is stated for sheaves of rings on a space, apply
  to the square of the tower, which is defined on an arbitrary site.

## Implementation notes

**The scalar rings.**  As in
`StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkBaseChangeMap`, the interchange and the
counit are over the `CommRingCat`-valued *fibre* of `C` at the point of the site of opens
attached to `z`, while the two legs of Stacks 0D09 are over the `RingCat`-valued *stalk*; the
reconciliation is the built-in `ModuleCat.restrictScalars`, and no new `Module` instance is
declared.  The `Algebra` and `IsScalarTower` structures the statements need are supplied by
`letI`, in the order in which the ring-level comparison map consumes them: the `A_z`-algebra
structure on `C_z` that `NaiveCotangent.nlExtensionBaseChangeMap` and
`Algebra.Extension.Cotangent.map` see is the one read off the composite `𝟙 A ≫ (a ≫ b)`, which
is what the two towers
`Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase` and `stalkIsScalarTowerSquareTarget` are
stated for.

**Term-mode proofs.**  As elsewhere in this area, `rw` cannot match across the two spellings of
a direct image along a composite, and the pure tensors of an extension of scalars of modules are
spelled with `ModuleCat.ExtendScalars`'s own `Module.compHom` instance, which `rw` rejects as
type-incorrect at `implicit` transparency.  The proofs below are therefore `Eq.trans`/`congrArg`
chains throughout.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the canonical map.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), the canonical map
  attached to a square of sheaves of rings.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension and
  restriction of scalars for sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open scoped ChangeOfRings

universe u

noncomputable section

namespace Stacks.NaiveCotangentStalkBaseChange

open Stacks.SheafOfModules Stacks.NaiveCotangentAffineStalkLegs
open Stacks.RelativeDifferentialStalk (algebraStalk)

/-! ### Additive maps out of a tensor product -/

/-- Two additive maps out of a tensor product which agree on pure tensors agree. -/
theorem tmul_ext {R N M P : Type*} [CommSemiring R] [AddCommMonoid N] [AddCommMonoid M]
    [AddCommMonoid P] [Module R N] [Module R M] (F G : TensorProduct R N M →+ P)
    (h : ∀ (n : N) (m : M), F (n ⊗ₜ[R] m) = G (n ⊗ₜ[R] m)) (x : TensorProduct R N M) :
    F x = G x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul n m => exact h n m
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C) (z : T)

/-! ### The two legs of the canonical map -/

/-- The square of Stacks 08TX whose adjoint is the canonical map of Stacks 0E1Y, in the spelling
of `Stacks.SheafOfModules.spaceNaiveCotangentComplexMapOfSquare`. -/
theorem baseChangeSquareMap_eq :
    baseChangeSquareMap.{u, u, u} (Opens.grothendieckTopology T) A B C a b =
      spaceNaiveCotangentComplexMapOfSquare A A B C a (a ≫ b) (𝟙 A) b
        (Category.id_comp (a ≫ b)).symm :=
  rfl

/-- The canonical map of Stacks 0E1Y, on stalks, split into its two legs. -/
theorem stalkFunctor_map_baseChangeNaiveCotangentMap_apply (i : ℤ)
    (ζ : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
          (Opens.grothendieckTopology T) B C b).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).X i))) :
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        ((baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
          A B C a b).f i)).hom ζ =
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((Stacks.SheafOfModules.towerCounit.{u, u, u} (Opens.grothendieckTopology T) B C b
            (naiveCotangentComplex.{u, u, u, u}
              (Opens.grothendieckTopology T) A C (a ≫ b))).f i)).hom
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
                (Opens.grothendieckTopology T) B C b).map
              (spaceNaiveCotangentComplexMapOfSquare A A B C a (a ≫ b) (𝟙 A) b
                (Category.id_comp (a ≫ b)).symm)).f i)).hom ζ) := by
  refine Eq.trans (congrArg (fun ψ => ((AlgebraicGeometry.SheafOfModules.stalkFunctor
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map ψ).hom ζ)
    (show (baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
          A B C a b).f i =
        ((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
            (Opens.grothendieckTopology T) B C b).map
          (spaceNaiveCotangentComplexMapOfSquare A A B C a (a ≫ b) (𝟙 A) b
            (Category.id_comp (a ≫ b)).symm)).f i ≫
          (Stacks.SheafOfModules.towerCounit.{u, u, u} (Opens.grothendieckTopology T) B C b
            (naiveCotangentComplex.{u, u, u, u}
              (Opens.grothendieckTopology T) A C (a ≫ b))).f i from rfl)) ?_
  rw [CategoryTheory.Functor.map_comp]
  exact ConcreteCategory.comp_apply _ _ ζ

/-- **The first leg on a pure tensor.**  The stalk of the termwise base change of the square map
of Stacks 08TX carries the image under `Opens.stalkTowerExtendScalarsXIso` of `c ⊗ ω` to the
image of `c ⊗ (stalk of the square map) ω`. -/
theorem stalkFunctor_map_towerExtendScalarsComplexes_inv_tmul (i : ℤ)
    (c : ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) C.obj))
    (ω : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z ⋙
        ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z B).hom).obj
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X i))) :
    ((AlgebraicGeometry.SheafOfModules.stalkFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
        (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
            (Opens.grothendieckTopology T) B C b).map
          (spaceNaiveCotangentComplexMapOfSquare A A B C a (a ≫ b) (𝟙 A) b
            (Category.id_comp (a ≫ b)).symm)).f i)).hom
        ((Opens.stalkTowerExtendScalarsXIso z B C b
          (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) i).inv
            (c ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
              Stacks.SitePointBaseChange.stalkRingHom b.hom
                (Opens.pointGrothendieckTopology z)] ω)) =
      (Opens.stalkTowerExtendScalarsXIso z B C b
          ((Stacks.SheafOfModules.towerRestrictScalarsComplexes.{u, u, u}
              (Opens.grothendieckTopology T) B C b).obj
            (naiveCotangentComplex.{u, u, u, u}
              (Opens.grothendieckTopology T) A C (a ≫ b))) i).inv
        (c ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
            Stacks.SitePointBaseChange.stalkRingHom b.hom
              (Opens.pointGrothendieckTopology z)]
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z ⋙
              ModuleCat.restrictScalars.{u} (Opens.commRingFiberStalkHom z B).hom).map
            ((spaceNaiveCotangentComplexMapOfSquare A A B C a (a ≫ b) (𝟙 A) b
              (Category.id_comp (a ≫ b)).symm).f i)).hom ω)) := by
  refine Eq.trans (Iso.hom_inv_id_apply (Opens.stalkTowerExtendScalarsXIso z B C b
    ((Stacks.SheafOfModules.towerRestrictScalarsComplexes.{u, u, u}
        (Opens.grothendieckTopology T) B C b).obj
      (naiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology T) A C (a ≫ b))) i) _).symm ?_
  refine congrArg (fun y => (Opens.stalkTowerExtendScalarsXIso z B C b
    ((Stacks.SheafOfModules.towerRestrictScalarsComplexes.{u, u, u}
        (Opens.grothendieckTopology T) B C b).obj
      (naiveCotangentComplex.{u, u, u, u}
        (Opens.grothendieckTopology T) A C (a ≫ b))) i).inv y) ?_
  refine Eq.trans (Opens.stalkTowerExtendScalars_map_apply z B C b
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)
    ((Stacks.SheafOfModules.towerRestrictScalarsComplexes.{u, u, u}
        (Opens.grothendieckTopology T) B C b).obj
      (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A C (a ≫ b)))
    (spaceNaiveCotangentComplexMapOfSquare A A B C a (a ≫ b) (𝟙 A) b
      (Category.id_comp (a ≫ b)).symm) i _) ?_
  exact congrArg _ (Iso.inv_hom_id_apply (Opens.stalkTowerExtendScalarsXIso z B C b
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) i) _)

/-- The value of the inverse of `stalkBaseChangeAddEquivNegOne` on a pure tensor. -/
theorem stalkBaseChangeAddEquivNegOne_symm_tmul
    (t : ToType (TopCat.Presheaf.stalk C.obj z))
    (κ : letI := algebraStalk a.hom z
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.Cotangent) :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    letI := moduleRingStalkCotangent A B a z
    (stalkBaseChangeAddEquivNegOne A B C a b z).symm
        (t ⊗ₜ[ToType (TopCat.Presheaf.stalk B.obj z)] κ) =
      (Opens.stalkTowerExtendScalarsXIso z B C b
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) (-1)).inv
          ((fiberStalkRingEquiv C z).symm t
            ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
              Stacks.SitePointBaseChange.stalkRingHom b.hom
                (Opens.pointGrothendieckTopology z)]
            (stalkLegNegOneLinear A B a z).symm κ) :=
  rfl

/-! ### The stalk of the canonical map of Stacks 0E1Y -/

/-- **The stalk of the canonical map of Stacks 0E1Y in degree `-1`.** -/
theorem stalkLegNegOneLinear_baseChangeNaiveCotangentMap
    (ξ : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
          (Opens.grothendieckTopology T) B C b).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).X (-1)))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z
    letI := algebraStalk b.hom z
    letI := algebraStalk (𝟙 A ≫ (a ≫ b)).hom z
    letI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A A C (a ≫ b)
      (𝟙 A ≫ (a ≫ b)) (𝟙 A) z rfl
    letI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareTarget A B C a
      (𝟙 A ≫ (a ≫ b)) b z (Category.id_comp (a ≫ b)).symm
    stalkLegNegOneLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
            A B C a b).f (-1))).hom ξ) =
      (NaiveCotangent.nlExtensionBaseChangeMap
          (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
            (Category.id_comp (a ≫ b)).symm)).f₁
        (stalkBaseChangeAddEquivNegOne A B C a b z ξ) := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z
  let := algebraStalk b.hom z
  let := algebraStalk (𝟙 A ≫ (a ≫ b)).hom z
  let := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A A C (a ≫ b)
    (𝟙 A ≫ (a ≫ b)) (𝟙 A) z rfl
  let := Stacks.Sites.Conormal.stalkIsScalarTowerSquareTarget A B C a
    (𝟙 A ≫ (a ≫ b)) b z (Category.id_comp (a ≫ b)).symm
  let := moduleRingStalkCotangent A B a z
  let := moduleRingStalkCotangent A C (a ≫ b) z
  refine Eq.trans ?_ (tmul_ext
    ((stalkLegNegOneLinear A C (a ≫ b) z).toLinearMap.toAddMonoidHom.comp
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
            A B C a b).f (-1))).hom.toAddMonoidHom.comp
        (stalkBaseChangeAddEquivNegOne A B C a b z).symm.toAddMonoidHom))
    (NaiveCotangent.nlExtensionBaseChangeMap
      (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
        (Category.id_comp (a ≫ b)).symm)).f₁.toAddMonoidHom
    (fun t κ => ?_) (stalkBaseChangeAddEquivNegOne A B C a b z ξ))
  · exact congrArg (fun ζ => stalkLegNegOneLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
            A B C a b).f (-1))).hom ζ))
      ((stalkBaseChangeAddEquivNegOne A B C a b z).symm_apply_apply ξ).symm
  · refine Eq.trans (congrArg (fun ζ => stalkLegNegOneLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
            A B C a b).f (-1))).hom ζ))
      (stalkBaseChangeAddEquivNegOne_symm_tmul A B C a b z t κ)) ?_
    refine Eq.trans (congrArg (stalkLegNegOneLinear A C (a ≫ b) z)
      (stalkFunctor_map_baseChangeNaiveCotangentMap_apply A B C a b z (-1) _)) ?_
    refine Eq.trans (congrArg (fun ζ => stalkLegNegOneLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((Stacks.SheafOfModules.towerCounit.{u, u, u}
              (Opens.grothendieckTopology T) B C b
              (naiveCotangentComplex.{u, u, u, u}
                (Opens.grothendieckTopology T) A C (a ≫ b))).f (-1))).hom ζ))
      (stalkFunctor_map_towerExtendScalarsComplexes_inv_tmul A B C a b z (-1)
        ((fiberStalkRingEquiv C z).symm t) ((stalkLegNegOneLinear A B a z).symm κ))) ?_
    refine Eq.trans (congrArg (stalkLegNegOneLinear A C (a ≫ b) z)
      (Opens.stalkFunctor_map_towerCounit_apply z B C b
        ((naiveCotangentComplex.{u, u, u, u}
          (Opens.grothendieckTopology T) A C (a ≫ b)).X (-1)) _)) ?_
    refine Eq.trans (congrArg (stalkLegNegOneLinear A C (a ≫ b) z)
      (ModuleCat.extendRestrictScalarsAdj_counit_app_apply_tmul
        (Stacks.SitePointBaseChange.stalkRingHom b.hom
          (Opens.pointGrothendieckTopology z)) _ ((fiberStalkRingEquiv C z).symm t)
        ((Opens.restrictScalarsStalkFunctorIso z B C b).hom.app _
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
            ((spaceNaiveCotangentComplexMapOfSquare A A B C a (a ≫ b) (𝟙 A) b
              (Category.id_comp (a ≫ b)).symm).f (-1))).hom
            ((stalkLegNegOneLinear A B a z).symm κ))))) ?_
    refine Eq.trans (congrArg (fun m => stalkLegNegOneLinear A C (a ≫ b) z
        (@SMul.smul (ToType (TopCat.Presheaf.stalk (Tensor.ringSheaf C).obj z)) _ inferInstance
          ((Opens.commRingFiberStalkHom z C).hom ((fiberStalkRingEquiv C z).symm t)) m))
      (Opens.restrictScalarsStalkFunctorIso_hom_app_apply z B C b _ _)) ?_
    refine Eq.trans (stalkLegNegOneLinear_smul_fiber A C (a ≫ b) z
      ((fiberStalkRingEquiv C z).symm t) _) ?_
    refine Eq.trans (congrArg (fun y => fiberStalkRingEquiv C z
        ((fiberStalkRingEquiv C z).symm t) • y)
      (stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_negOne A A B C a (a ≫ b) (𝟙 A) b z
        (Category.id_comp (a ≫ b)).symm (𝟙 A ≫ (a ≫ b)) rfl
        ((stalkLegNegOneLinear A B a z).symm κ))) ?_
    refine Eq.trans (congrArg (fun s : ToType (TopCat.Presheaf.stalk C.obj z) =>
        s • Algebra.Extension.Cotangent.map
          (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
            (Category.id_comp (a ≫ b)).symm)
          (stalkLegNegOneLinear A B a z ((stalkLegNegOneLinear A B a z).symm κ)))
      ((fiberStalkRingEquiv C z).apply_symm_apply t)) ?_
    exact congrArg (fun y => t • Algebra.Extension.Cotangent.map
        (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
          (Category.id_comp (a ≫ b)).symm) y)
      ((stalkLegNegOneLinear A B a z).apply_symm_apply κ)

/-! ### Degree `0` -/

/-- The value of the inverse of `stalkBaseChangeAddEquivZero` on a pure tensor. -/
theorem stalkBaseChangeAddEquivZero_symm_tmul
    (t : ToType (TopCat.Presheaf.stalk C.obj z))
    (κ : letI := algebraStalk a.hom z
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.CotangentSpace) :
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    letI := moduleRingStalkCotangentSpace A B a z
    (stalkBaseChangeAddEquivZero A B C a b z).symm
        (t ⊗ₜ[ToType (TopCat.Presheaf.stalk B.obj z)] κ) =
      (Opens.stalkTowerExtendScalarsXIso z B C b
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a) 0).inv
          ((fiberStalkRingEquiv C z).symm t
            ⊗ₜ[ToType (Stacks.ringFiber (Opens.pointGrothendieckTopology z) B.obj),
              Stacks.SitePointBaseChange.stalkRingHom b.hom
                (Opens.pointGrothendieckTopology z)]
            (stalkLegZeroLinear A B a z).symm κ) :=
  rfl

/-- **The stalk of the canonical map of Stacks 0E1Y in degree `0`.** -/
theorem stalkLegZeroLinear_baseChangeNaiveCotangentMap
    (ξ : ToType ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).obj
      (((Stacks.SheafOfModules.towerExtendScalarsComplexes.{u, u, u}
          (Opens.grothendieckTopology T) B C b).obj
        (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a)).X 0))) :
    letI := algebraStalk a.hom z
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z
    letI := algebraStalk b.hom z
    letI := algebraStalk (𝟙 A ≫ (a ≫ b)).hom z
    letI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A A C (a ≫ b)
      (𝟙 A ≫ (a ≫ b)) (𝟙 A) z rfl
    letI := Stacks.Sites.Conormal.stalkIsScalarTowerSquareTarget A B C a
      (𝟙 A ≫ (a ≫ b)) b z (Category.id_comp (a ≫ b)).symm
    stalkLegZeroLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
            A B C a b).f 0)).hom ξ) =
      (NaiveCotangent.nlExtensionBaseChangeMap
          (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
            (Category.id_comp (a ≫ b)).symm)).f₀
        (stalkBaseChangeAddEquivZero A B C a b z ξ) := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 A)) z
  let := algebraStalk b.hom z
  let := algebraStalk (𝟙 A ≫ (a ≫ b)).hom z
  let := Stacks.Sites.Conormal.stalkIsScalarTowerSquareBase A A C (a ≫ b)
    (𝟙 A ≫ (a ≫ b)) (𝟙 A) z rfl
  let := Stacks.Sites.Conormal.stalkIsScalarTowerSquareTarget A B C a
    (𝟙 A ≫ (a ≫ b)) b z (Category.id_comp (a ≫ b)).symm
  let := moduleRingStalkCotangentSpace A B a z
  let := moduleRingStalkCotangentSpace A C (a ≫ b) z
  refine Eq.trans ?_ (tmul_ext
    ((stalkLegZeroLinear A C (a ≫ b) z).toLinearMap.toAddMonoidHom.comp
      (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
            A B C a b).f 0)).hom.toAddMonoidHom.comp
        (stalkBaseChangeAddEquivZero A B C a b z).symm.toAddMonoidHom))
    (NaiveCotangent.nlExtensionBaseChangeMap
      (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
        (Category.id_comp (a ≫ b)).symm)).f₀.toAddMonoidHom
    (fun t κ => ?_) (stalkBaseChangeAddEquivZero A B C a b z ξ))
  · exact congrArg (fun ζ => stalkLegZeroLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
            A B C a b).f 0)).hom ζ))
      ((stalkBaseChangeAddEquivZero A B C a b z).symm_apply_apply ξ).symm
  · refine Eq.trans (congrArg (fun ζ => stalkLegZeroLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
          ((baseChangeNaiveCotangentMap.{u, u, u} (Opens.grothendieckTopology T)
            A B C a b).f 0)).hom ζ))
      (stalkBaseChangeAddEquivZero_symm_tmul A B C a b z t κ)) ?_
    refine Eq.trans (congrArg (stalkLegZeroLinear A C (a ≫ b) z)
      (stalkFunctor_map_baseChangeNaiveCotangentMap_apply A B C a b z 0 _)) ?_
    refine Eq.trans (congrArg (fun ζ => stalkLegZeroLinear A C (a ≫ b) z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
              (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
            ((Stacks.SheafOfModules.towerCounit.{u, u, u}
              (Opens.grothendieckTopology T) B C b
              (naiveCotangentComplex.{u, u, u, u}
                (Opens.grothendieckTopology T) A C (a ≫ b))).f 0)).hom ζ))
      (stalkFunctor_map_towerExtendScalarsComplexes_inv_tmul A B C a b z 0
        ((fiberStalkRingEquiv C z).symm t) ((stalkLegZeroLinear A B a z).symm κ))) ?_
    refine Eq.trans (congrArg (stalkLegZeroLinear A C (a ≫ b) z)
      (Opens.stalkFunctor_map_towerCounit_apply z B C b
        ((naiveCotangentComplex.{u, u, u, u}
          (Opens.grothendieckTopology T) A C (a ≫ b)).X 0) _)) ?_
    refine Eq.trans (congrArg (stalkLegZeroLinear A C (a ≫ b) z)
      (ModuleCat.extendRestrictScalarsAdj_counit_app_apply_tmul
        (Stacks.SitePointBaseChange.stalkRingHom b.hom
          (Opens.pointGrothendieckTopology z)) _ ((fiberStalkRingEquiv C z).symm t)
        ((Opens.restrictScalarsStalkFunctorIso z B C b).hom.app _
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor
                (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
            ((spaceNaiveCotangentComplexMapOfSquare A A B C a (a ≫ b) (𝟙 A) b
              (Category.id_comp (a ≫ b)).symm).f 0)).hom
            ((stalkLegZeroLinear A B a z).symm κ))))) ?_
    refine Eq.trans (congrArg (fun m => stalkLegZeroLinear A C (a ≫ b) z
        (@SMul.smul (ToType (TopCat.Presheaf.stalk (Tensor.ringSheaf C).obj z)) _ inferInstance
          ((Opens.commRingFiberStalkHom z C).hom ((fiberStalkRingEquiv C z).symm t)) m))
      (Opens.restrictScalarsStalkFunctorIso_hom_app_apply z B C b _ _)) ?_
    refine Eq.trans (stalkLegZeroLinear_smul_fiber A C (a ≫ b) z
      ((fiberStalkRingEquiv C z).symm t) _) ?_
    refine Eq.trans (congrArg (fun y => fiberStalkRingEquiv C z
        ((fiberStalkRingEquiv C z).symm t) • y)
      (stalkLegLinear_spaceNaiveCotangentComplexMapOfSquare_zero A A B C a (a ≫ b) (𝟙 A) b z
        (Category.id_comp (a ≫ b)).symm (𝟙 A ≫ (a ≫ b)) rfl
        ((stalkLegZeroLinear A B a z).symm κ))) ?_
    refine Eq.trans (congrArg (fun s : ToType (TopCat.Presheaf.stalk C.obj z) =>
        s • Algebra.Extension.CotangentSpace.map
          (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
            (Category.id_comp (a ≫ b)).symm)
          (stalkLegZeroLinear A B a z ((stalkLegZeroLinear A B a z).symm κ)))
      ((fiberStalkRingEquiv C z).apply_symm_apply t)) ?_
    exact congrArg (fun y => t • Algebra.Extension.CotangentSpace.map
        (generatorsSelfStalkHomOfSquare A A B C a (a ≫ b) (𝟙 A) b z
          (Category.id_comp (a ≫ b)).symm) y)
      ((stalkLegZeroLinear A B a z).apply_symm_apply κ)

end Stacks.NaiveCotangentStalkBaseChange

end

end
