module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import StacksFrontier.Homology.ExtendScalars.AlongARingIsomorphism
public import StacksFrontier.Homology.Tor.BaseChangeTensorMonoidalIso
public import StacksFrontier.Homology.Tor.BaseChangeTensorScalarLift

/-!
# Extension of scalars commutes with the scalar lift of [stacks 0E1W]

The scalar-lift world of [stacks 0E1W] replaces `R` and `A` by `ULift R` and `ULift A`, which
live in one universe, and the ring map `f : R → A` by its lift
`f' : ULift R → ULift A`.  Degreewise extension of scalars is then available on both sides of
the lift, and the two composites

`lift scalars over R, then extend along f'` and `extend along f, then lift scalars over A`

carry an `R`-module to two spellings of the same base change.  Nothing in the library compared
them: `ModuleCat.restrictExtendScalarsCompIso` is the right statement but is confined to a single
universe, and `Stacks.DerivedHom.BaseChange.exists_scalarLiftExtendComparison` produces a chain map
between them without claiming it is invertible or evaluating it.

This file supplies the comparison as an isomorphism, and evaluates it.  Both composites are left
adjoint to one and the same functor: restricting a module over `ULift A` to `R` through `ULift R`
and restricting it through `A` give definitionally equal module structures, because
`ULift.ringEquiv` is inverse to its own inverse definitionally.  So uniqueness of left adjoints
supplies the isomorphism with no element-level work, and the triangle identity characterizing it
evaluates it: it carries `1 ⊗ m` to `1 ⊗ m`, both units of the two composite adjunctions being
the degreewise unit of extension of scalars.

**What is not done here.**  Nothing is registered and no caveat is lifted.  Both hypotheses of
`Dualizing.tensorComparisonCompatibility_of_tensorBaseChangeMor` remain open; in particular the
comparison identity `h` is untouched, and its frontier remains
`Dualizing.tensorComparisonCompatibility_of_kFlat_tail`.

## Main definitions

* `CochainComplex.DerivedTensor.extendScalarsLiftNatIso` -- the comparison of the two composites
  on modules, from uniqueness of left adjoints.
* `CochainComplex.DerivedTensor.extendScalarsLiftChainIso` -- the same at a cochain complex,
  degreewise.

## Main results

* `CochainComplex.DerivedTensor.extendScalarsLiftNatIso_hom_app_one_tmul` and
  `CochainComplex.DerivedTensor.extendScalarsLiftNatIso_hom_app_tmul` -- the value of the
  comparison at a pure tensor.
* `CochainComplex.DerivedTensor.extendScalarsLiftNatIso_monoidal_key` -- the monoidality square in
  the oplax direction.
* `CochainComplex.DerivedTensor.extendScalarsLiftNatIso_monoidal` -- **the monoidality square**:
  the comparison carries the monoidality isomorphism of extension of scalars along the lifted
  ring map to the module comparison of [stacks 068I] along `f`.

## References

* [Stacks Project, Tag 068I](https://stacks.math.columbia.edu/tag/068I)
* [Stacks Project, Tag 0E1W](https://stacks.math.columbia.edu/tag/0E1W)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

universe uR uA v

namespace CochainComplex.DerivedTensor

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)

/-- The lift of a ring map to the universe-lifted rings. -/
public abbrev liftRingHom : ULift.{max uR uA v} R →+* ULift.{max uR uA v} A :=
  (ULift.ringEquiv.symm.toRingHom.comp f).comp ULift.ringEquiv.toRingHom

/-- The scalar lift of modules over a ring, as a functor. -/
public abbrev scalarLiftFunctor (B : Type uR) [CommRing B] :
    ModuleCat.{max uR v} B ⥤ ModuleCat.{max uR v} (ULift.{max uR v} B) :=
  ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{max uR v} B ≃+* B).toRingHom

/-- The adjunction "lift scalars over `R`, then extend along the lifted ring map". -/
public abbrev liftExtendAdj :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max uR uA v}
      (ULift.ringEquiv : ULift.{max uR uA v} R ≃+* R)).toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj.{max uR uA v, max uR uA v, max uR uA v}
      (liftRingHom.{uR, uA, v} f))

/-- The adjunction "extend along `f`, then lift scalars over `A`". -/
public abbrev extendLiftAdj :=
  (ModuleCat.extendRestrictScalarsAdj.{max uR uA v, uR, uA} f).comp
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{max uR uA v}
      (ULift.ringEquiv : ULift.{max uR uA v} A ≃+* A)).toAdjunction

/-- **The comparison of "lift, then extend" with "extend, then lift", on modules.**

Restriction of scalars along `ULift.ringEquiv` over `R` followed by extension of scalars along
the lifted ring map, against extension of scalars along `f` followed by restriction of scalars
along `ULift.ringEquiv` over `A`.  Both composites are left adjoint to one and the same functor,
so uniqueness of left adjoints supplies the isomorphism. -/
public def extendScalarsLiftNatIso :
    scalarLiftFunctor.{uR, max uA v} R ⋙
        ModuleCat.extendScalars.{max uR uA v, max uR uA v, max uR uA v}
          (liftRingHom.{uR, uA, v} f) ≅
      ModuleCat.extendScalars.{uR, uA, max uR uA v} f ⋙ scalarLiftFunctor.{uA, max uR v} A :=
  Adjunction.leftAdjointUniq (liftExtendAdj.{uR, uA, v} f) (extendLiftAdj.{uR, uA, v} f)

/-- **The value of the comparison at `1 ⊗ m`.**  By the triangle identity characterizing the
isomorphism of two left adjoints, the comparison carries the image of one unit to the other;
both units send `m` to `1 ⊗ m`. -/
public theorem extendScalarsLiftNatIso_hom_app_one_tmul
    (M : ModuleCat.{max uR uA v} R) (m : M) :
    (extendScalarsLiftNatIso.{uR, uA, v} f).hom.app M
        ((1 : ULift.{max uR uA v} A) ⊗ₜ[ULift.{max uR uA v} R, liftRingHom.{uR, uA, v} f] m) =
      ((1 : A) ⊗ₜ[R, f] m) := by
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ m)
    (Adjunction.unit_leftAdjointUniq_hom_app (liftExtendAdj.{uR, uA, v} f)
      (extendLiftAdj.{uR, uA, v} f) M)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- **The value of the comparison at a general pure tensor.**  A pure tensor is the scalar
acting on `1 ⊗ m`, the comparison is linear over the lifted ring, and the action on the target
is through `ULift.ringEquiv`. -/
public theorem extendScalarsLiftNatIso_hom_app_tmul (M : ModuleCat.{max uR uA v} R)
    (a : ULift.{max uR uA v} A) (m : M) :
    (extendScalarsLiftNatIso.{uR, uA, v} f).hom.app M
        (a ⊗ₜ[ULift.{max uR uA v} R, liftRingHom.{uR, uA, v} f] m) =
      (a.down ⊗ₜ[R, f] m) := by
  have hmap := ((extendScalarsLiftNatIso.{uR, uA, v} f).hom.app M).hom.map_smul a
      ((1 : ULift.{max uR uA v} A) ⊗ₜ[ULift.{max uR uA v} R, liftRingHom.{uR, uA, v} f] m)
  have h1 := extendScalarsLiftNatIso_hom_app_one_tmul.{uR, uA, v} f M m
  conv_lhs => rw [← mul_one a]
  refine Eq.trans hmap ?_
  refine Eq.trans (congrArg (a • ·) h1) ?_
  exact congrArg (· ⊗ₜ[R, f] m) (mul_one a.down)

/-- Two maps out of an extension of scalars of a tensor product agree if they agree on the
generators `1 ⊗ (x ⊗ y)`. -/
private theorem ext_tensor_hom_ext (X Y : ModuleCat.{max uR uA v} R)
    {T : ModuleCat.{max uR uA v} (ULift.{max uR uA v} A)}
    (F G : (ModuleCat.extendScalars.{max uR uA v, max uR uA v, max uR uA v}
          (liftRingHom.{uR, uA, v} f)).obj
        (MonoidalCategory.tensorObj ((scalarLiftFunctor.{uR, max uA v} R).obj X)
          ((scalarLiftFunctor.{uR, max uA v} R).obj Y)) ⟶ T)
    (h : ∀ (x : (scalarLiftFunctor.{uR, max uA v} R).obj X)
      (y : (scalarLiftFunctor.{uR, max uA v} R).obj Y),
      F.hom ((1 : ULift.{max uR uA v} A) ⊗ₜ[ULift.{max uR uA v} R,liftRingHom.{uR, uA, v} f]
        (x ⊗ₜ[ULift.{max uR uA v} R] y)) =
      G.hom ((1 : ULift.{max uR uA v} A) ⊗ₜ[ULift.{max uR uA v} R,liftRingHom.{uR, uA, v} f]
        (x ⊗ₜ[ULift.{max uR uA v} R] y))) :
    F = G :=
  ((ModuleCat.extendRestrictScalarsAdj.{max uR uA v, max uR uA v, max uR uA v}
      (liftRingHom.{uR, uA, v} f)).homEquiv _ _).injective
    (ModuleCat.MonoidalCategory.tensor_ext (fun x y => h x y))

/-- Congruence for a pure tensor over `A` in both factors. -/
private theorem tmulA_congr (M N : ModuleCat.{max uR uA v} A)
    {u u' : M} {w w' : N} (hu : u = u') (hw : w = w') :
    (u ⊗ₜ[A] w) = (u' ⊗ₜ[A] w') := by
  rw [hu, hw]

/-- **The monoidality square for the comparison, in the oplax direction.**

Both sides are maps out of a single extension of scalars, so they agree as soon as they agree on
the generators `1 ⊗ (x ⊗ y)`, where everything is the identity on elements except the module
comparison of [stacks 068I], which is
`TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul` there. -/
public theorem extendScalarsLiftNatIso_monoidal_key (X Y : ModuleCat.{max uR uA v} R) :
    (ModuleCat.extendScalars.{max uR uA v, max uR uA v, max uR uA v}
          (liftRingHom.{uR, uA, v} f)).map
        (restrictScalarsTensorIso
          (ULift.ringEquiv : ULift.{max uR uA v} R ≃+* R) X Y).hom ≫
      (extendScalarsLiftNatIso.{uR, uA, v} f).hom.app
        (((moduleTensor.{uR, max uA v} R).obj X).obj Y) =
    Functor.OplaxMonoidal.δ
        (ModuleCat.extendScalars.{max uR uA v, max uR uA v, max uR uA v}
          (liftRingHom.{uR, uA, v} f))
        ((scalarLiftFunctor.{uR, max uA v} R).obj X)
        ((scalarLiftFunctor.{uR, max uA v} R).obj Y) ≫
      ((extendScalarsLiftNatIso.{uR, uA, v} f).hom.app X ⊗ₘ
          (extendScalarsLiftNatIso.{uR, uA, v} f).hom.app Y) ≫
        (restrictScalarsTensorIso
            (ULift.ringEquiv : ULift.{max uR uA v} A ≃+* A)
            ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj X)
            ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj Y)).hom ≫
          (scalarLiftFunctor.{uA, max uR v} A).map
            (letI := f.toAlgebra
             (TensorProduct.AlgebraTensorModule.distribBaseChange R A X Y).symm.toModuleIso.hom) :=
    by
  apply ext_tensor_hom_ext
  intro x y
  have hcXY := extendScalarsLiftNatIso_hom_app_one_tmul.{uR, uA, v} f
    (((moduleTensor.{uR, max uA v} R).obj X).obj Y) (x ⊗ₜ[R] y)
  have hcX := extendScalarsLiftNatIso_hom_app_one_tmul.{uR, uA, v} f X x
  have hcY := extendScalarsLiftNatIso_hom_app_one_tmul.{uR, uA, v} f Y y
  let := f.toAlgebra
  have hstep := tmulA_congr.{uR, uA, v} ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj X)
    ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj Y) hcX hcY
  have hdbc := TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul
    R A (N := X) (Q := Y) x y 1 1
  refine Eq.trans hcXY (Eq.symm ?_)
  refine Eq.trans ?_ (congrArg (· ⊗ₜ[R, f] (x ⊗ₜ[R] y)) (mul_one (1 : A)))
  exact Eq.trans (congrArg
    (fun z => (TensorProduct.AlgebraTensorModule.distribBaseChange R A X Y).symm z) hstep) hdbc

/-- **The monoidality square for the comparison.**

The comparison of "lift, then extend" with "extend, then lift" is monoidal: the lax comparison
of extension of scalars along the lifted ring map, followed by the extension of the comparison
of restriction of scalars with the tensor product and by the comparison at the tensor product,
is the tensor of two comparisons followed by the comparison of restriction of scalars with the
tensor product over `A` and the lift of the module comparison of [stacks 068I].

This is the module-level content of the identification of the two monoidality isomorphisms of
degreewise extension of scalars across the scalar lift of [stacks 0E1W]. -/
public theorem extendScalarsLiftNatIso_monoidal (X Y : ModuleCat.{max uR uA v} R) :
    (Functor.LaxMonoidal.μ
          (ModuleCat.extendScalars.{max uR uA v, max uR uA v, max uR uA v}
            (liftRingHom.{uR, uA, v} f))
          ((scalarLiftFunctor.{uR, max uA v} R).obj X)
          ((scalarLiftFunctor.{uR, max uA v} R).obj Y)) ≫
        (ModuleCat.extendScalars.{max uR uA v, max uR uA v, max uR uA v}
            (liftRingHom.{uR, uA, v} f)).map
          (restrictScalarsTensorIso
            (ULift.ringEquiv : ULift.{max uR uA v} R ≃+* R) X Y).hom ≫
          (extendScalarsLiftNatIso.{uR, uA, v} f).hom.app
            (((moduleTensor.{uR, max uA v} R).obj X).obj Y) =
      ((extendScalarsLiftNatIso.{uR, uA, v} f).hom.app X ⊗ₘ
          (extendScalarsLiftNatIso.{uR, uA, v} f).hom.app Y) ≫
        (restrictScalarsTensorIso
            (ULift.ringEquiv : ULift.{max uR uA v} A ≃+* A)
            ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj X)
            ((ModuleCat.extendScalars.{uR, uA, max uR uA v} f).obj Y)).hom ≫
          (scalarLiftFunctor.{uA, max uR v} A).map
            (letI := f.toAlgebra
             (TensorProduct.AlgebraTensorModule.distribBaseChange R A X Y).symm.toModuleIso.hom) :=
    by
  rw [extendScalarsLiftNatIso_monoidal_key.{uR, uA, v} f X Y]
  exact Functor.Monoidal.μ_δ_assoc _ _ _ _

/-- **The comparison of "lift, then extend" with "extend, then lift", on cochain complexes.**
Degreewise `CochainComplex.DerivedTensor.extendScalarsLiftNatIso`; it commutes with the
differentials because that isomorphism is natural. -/
public def extendScalarsLiftChainIso (K : CochainComplex (ModuleCat.{max uR uA v} R) ℤ) :
    ((ModuleCat.extendScalars.{max uR uA v, max uR uA v, max uR uA v}
          (liftRingHom.{uR, uA, v} f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((scalarLiftFunctor.{uR, max uA v} R).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      ((scalarLiftFunctor.{uA, max uR v} A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((extensionOfScalarsCochain.{uR, uA, v} f).obj K) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (extendScalarsLiftNatIso.{uR, uA, v} f).app (K.X n))
    (fun i j _ => ((extendScalarsLiftNatIso.{uR, uA, v} f).hom.naturality (K.d i j)).symm)

end CochainComplex.DerivedTensor

end
