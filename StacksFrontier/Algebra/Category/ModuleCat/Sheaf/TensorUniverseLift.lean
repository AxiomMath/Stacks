module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLift
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UliftTensorPresheaf

/-!
# The universe lift of a ringed site commutes with the tensor product

`Stacks.SheafOfModules.CoherentLift.liftModule` raises the universe of the sections of a sheaf of
modules together with the universe of the sections of the structure sheaf, and
`Stacks.SheafOfModules.CoherentLift.isCoherentOnSite_liftModule_iff` shows that coherence is
unaffected.  This file shows that the operation also commutes with the tensor product.

## Main definitions

* `Stacks.SheafOfModules.CoherentLift.uliftDownSemilinearEquiv`: a `ULift` of a module is
  semilinearly equivalent to the module, over `ULift.ringEquiv`.
* `Stacks.SheafOfModules.CoherentLift.tensorLiftEquiv`: the sections of the objectwise tensor
  product of two lifted sheaves of modules are semilinearly equivalent to the sections of the
  objectwise tensor product of the originals.
* `Stacks.SheafOfModules.CoherentLift.liftedTensorUnit`: the morphism of presheaves of modules
  from the objectwise tensor product of two lifted sheaves of modules to the lift of their tensor
  product sheaf.
* `Stacks.SheafOfModules.CoherentLift.tensorLiftIso`: **the tensor product of two universe lifts
  is the universe lift of their tensor product.**

## Implementation notes

The tensor product of sheaves of modules is the sheafification of the objectwise tensor product
of the underlying presheaves, so the comparison is obtained from the extension principle
`Stacks.SheafOfModules.UliftTensor.isoOfLocallyBijective`: both sides receive a locally bijective
morphism from the objectwise tensor product of the two lifted presheaves.  One of the two is the
sheafification unit `Stacks.SheafOfModules.UliftTensor.sheafifyUnit`; the other is
`liftedTensorUnit`, the sheafification unit of the unlifted tensor product read through
`tensorLiftEquiv`.

`tensorLiftEquiv` is a *semilinear* equivalence over `ULift.ringEquiv`, since the ring of scalars
is lifted along with the module.  `TensorProduct.congr` is already semilinear, so the equivalence
is a single application of it; it is stated for bare modules rather than for the sections of a
presheaf of modules, because unifying the carrier of
`PresheafOfModules.tensorObj` with `_ ⊗[_] _` is a problem the unifier does not solve, while the
type ascription on `tensorLiftEquiv` performs the same identification in one step.

`LinearEquiv` has a `FunLike` instance only in the presence of `RingHomInvPair` in *both*
directions, and the second of the two is not syntactically an instance of the first, so both
`ringEquivInvPair` and `ringEquivInvPair'` are supplied as local instances.

The ring of scalars of the lifted sections is written as the `ULift` of `X.O.obj.obj V`, the
sections of the structure sheaf itself, rather than of the sections of `Tensor.ringSheaf X.O`:
`Tensor.ringSheaf` is an ordinary definition, so instance resolution does not unfold it, and the
former spelling is the one against which the `Module` instance of the objectwise tensor product of
the two lifts resolves.  Each component of `liftedTensorUnit` names its ring and both of its
modules for the same reason: the source is the tensor product of the lifted sections, whose module
structure is found at that spelling, while the target is a `ULift` of the sections of the unlifted
tensor product sheaf, whose module structure is found by lifting the one over
`Tensor.ringSheaf X.O`.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

open scoped TensorProduct

namespace Stacks.SheafOfModules.CoherentLift

universe u v w

attribute [local implicit_reducible] liftRingedSite CategoryTheory.sheafCompose
  PresheafOfModules.tensorObj liftModule

/-- A ring equivalence and its inverse form an inverse pair of ring homomorphisms. -/
theorem ringEquivInvPair {A : Type*} {B : Type*} [Semiring A] [Semiring B] (e : A ≃+* B) :
    RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e

/-- A ring equivalence and its inverse form an inverse pair of ring homomorphisms, in the other
order. -/
theorem ringEquivInvPair' {A : Type*} {B : Type*} [Semiring A] [Semiring B] (e : A ≃+* B) :
    RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv e.symm

attribute [local instance] ringEquivInvPair ringEquivInvPair'

/-- A `ULift` of a module is semilinearly equivalent to the module, over `ULift.ringEquiv`. -/
noncomputable def uliftDownSemilinearEquiv (A : Type w) [Semiring A] (M : Type*)
    [AddCommMonoid M] [Module A M] :
    ULift.{u} M ≃ₛₗ[(ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom] M :=
  { AddEquiv.ulift with map_smul' := fun _ _ ↦ rfl }

/-- A `ULift` of a tensor product of modules is semilinearly equivalent to the tensor product. -/
noncomputable def uliftTensorDownSemilinearEquiv (A : Type w) [CommRing A] (M N : Type*)
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] :
    (ULift.{u} M ⊗[ULift.{u} A] ULift.{u} N) ≃ₛₗ[
      (ULift.ringEquiv : ULift.{u} A ≃+* A).toRingHom] (M ⊗[A] N) :=
  TensorProduct.congr (uliftDownSemilinearEquiv.{u} A M) (uliftDownSemilinearEquiv.{u} A N)

/-- The sections of the objectwise tensor product of two lifted sheaves of modules are
semilinearly equivalent to the sections of the objectwise tensor product of the originals. -/
noncomputable def tensorLiftEquiv (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (V : X.Cᵒᵖ) :
    (PresheafOfModules.tensorObj (liftModule.{u, v, w} X F).val
        (liftModule.{u, v, w} X G).val).obj V ≃ₛₗ[
      (ULift.ringEquiv : ULift.{max u v} (X.O.obj.obj V) ≃+* X.O.obj.obj V).toRingHom]
      (PresheafOfModules.tensorObj F.val G.val).obj V :=
  uliftTensorDownSemilinearEquiv.{max u v} (X.O.obj.obj V) (F.val.obj V) (G.val.obj V)

/-- The semilinear comparison `tensorLiftEquiv` of the sections is natural in the object of the
site. -/
theorem tensorLiftEquiv_naturality (X : AlgebraicGeometry.RingedSite.{u, v, w})
    (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {V W : X.Cᵒᵖ}
    (f : V ⟶ W)
    (a : (PresheafOfModules.tensorObj (liftModule.{u, v, w} X F).val
      (liftModule.{u, v, w} X G).val).obj V) :
    tensorLiftEquiv X F G W
        ((PresheafOfModules.tensorObj (liftModule.{u, v, w} X F).val
          (liftModule.{u, v, w} X G).val).map f a) =
      (PresheafOfModules.tensorObj F.val G.val).map f (tensorLiftEquiv X F G V a) := by
  induction a using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    exact map_zero _
  | tmul x y => rfl
  | add x y hx hy =>
    simp only [map_add]
    exact (map_add (tensorLiftEquiv X F G W) _ _).trans (by rw [hx, hy]; rfl)

section Unit

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (F G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- The sheafification unit of the objectwise tensor product of two sheaves of modules. -/
noncomputable abbrev baseUnit :
    PresheafOfModules.tensorObj F.val G.val ⟶
      ((PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj
        (PresheafOfModules.tensorObj F.val G.val)).val :=
  Stacks.SheafOfModules.UliftTensor.sheafifyUnit (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (PresheafOfModules.tensorObj F.val G.val)

/-- The tensor product of two sheaves of modules on a ringed site. -/
noncomputable abbrev baseTensor : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj F).obj G

/-- The lifted sheafification unit: the objectwise tensor product of the lifts of two sheaves of
modules maps to the lift of their tensor product sheaf. -/
noncomputable def liftedTensorUnit :
    PresheafOfModules.tensorObj (liftModule.{u, v, w} X F).val
        (liftModule.{u, v, w} X G).val ⟶
      (liftModule.{u, v, w} X (baseTensor X F G)).val where
  app V := ModuleCat.ofHom
    (R := ULift.{max u v} (X.O.obj.obj V))
    (X := (PresheafOfModules.tensorObj (liftModule.{u, v, w} X F).val
      (liftModule.{u, v, w} X G).val).obj V)
    (Y := ULift.{max u v} ((baseTensor X F G).val.obj V))
    { toFun a := ULift.up ((baseUnit X F G).app V (tensorLiftEquiv X F G V a))
      map_add' a b := by
        change ULift.up ((baseUnit X F G).app V (tensorLiftEquiv X F G V (a + b))) =
          ULift.up ((baseUnit X F G).app V (tensorLiftEquiv X F G V a) +
            (baseUnit X F G).app V (tensorLiftEquiv X F G V b))
        rw [map_add (tensorLiftEquiv X F G V), map_add]
      map_smul' a b := by
        change ULift.up ((baseUnit X F G).app V (tensorLiftEquiv X F G V (a • b))) =
          ULift.up (a.down • (baseUnit X F G).app V (tensorLiftEquiv X F G V b))
        rw [map_smulₛₗ, map_smul]
        rfl }
  naturality f := by
    ext a
    exact ULift.ext
      ((congrArg ((baseUnit X F G).app _) (tensorLiftEquiv_naturality X F G f a)).trans
        (PresheafOfModules.naturality_apply (baseUnit X F G) f _))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The lifted sheafification unit is locally injective. -/
theorem liftedTensorUnit_isLocallyInjective :
    PresheafOfModules.IsLocallyInjective X.J (liftedTensorUnit X F G) := by
  have : Presheaf.IsLocallyInjective X.J
      ((PresheafOfModules.toPresheaf _).map (baseUnit X F G)) :=
    Stacks.SheafOfModules.UliftTensor.isLocallyInjective_sheafifyUnit
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (PresheafOfModules.tensorObj F.val G.val)
  constructor
  intro V x y h
  have h' : (baseUnit X F G).app V (tensorLiftEquiv X F G V x) =
      (baseUnit X F G).app V (tensorLiftEquiv X F G V y) := congrArg ULift.down h
  apply X.J.superset_covering _
    (Presheaf.equalizerSieve_mem X.J
      ((PresheafOfModules.toPresheaf _).map (baseUnit X F G)) _ _ h')
  intro W f hf
  exact (tensorLiftEquiv X F G (op W)).injective
    ((tensorLiftEquiv_naturality X F G f.op x).trans
      (hf.trans (tensorLiftEquiv_naturality X F G f.op y).symm))

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The lifted sheafification unit is locally surjective. -/
theorem liftedTensorUnit_isLocallySurjective :
    PresheafOfModules.IsLocallySurjective X.J (liftedTensorUnit X F G) := by
  have : Presheaf.IsLocallySurjective X.J
      ((PresheafOfModules.toPresheaf _).map (baseUnit X F G)) :=
    Stacks.SheafOfModules.UliftTensor.isLocallySurjective_sheafifyUnit
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (PresheafOfModules.tensorObj F.val G.val)
  constructor
  intro V t
  apply X.J.superset_covering _
    (Presheaf.imageSieve_mem X.J
      ((PresheafOfModules.toPresheaf _).map (baseUnit X F G)) t.down)
  rintro W f ⟨a, ha⟩
  refine ⟨(tensorLiftEquiv X F G (op W)).symm a, ?_⟩
  exact ULift.ext ((congrArg (fun z ↦ (baseUnit X F G).app (op W) z)
    (LinearEquiv.apply_symm_apply (tensorLiftEquiv X F G (op W)) a)).trans ha)

/-- **The universe lift commutes with the tensor product.**  The tensor product of the lifts of
two sheaves of modules is the lift of their tensor product. -/
noncomputable def tensorLiftIso
    [HasWeakSheafify (liftRingedSite.{u, v, w} X).J AddCommGrpCat.{max u v w}]
    [(liftRingedSite.{u, v, w} X).J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] :
    ((Stacks.SheafOfModules.Tensor.sheafTensor (liftRingedSite.{u, v, w} X).O).obj (liftModule.{u,
        v, w} X F)).obj (liftModule.{u, v, w} X G) ≅
      liftModule.{u, v, w} X (baseTensor X F G) :=
  Stacks.SheafOfModules.UliftTensor.isoOfLocallyBijective
    (Stacks.SheafOfModules.UliftTensor.sheafifyUnit
      (R := (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O))
      (PresheafOfModules.tensorObj (liftModule.{u, v, w} X F).val
        (liftModule.{u, v, w} X G).val))
    (liftedTensorUnit X F G)
    (Stacks.SheafOfModules.UliftTensor.isLocallyInjective_sheafifyUnit _)
    (Stacks.SheafOfModules.UliftTensor.isLocallySurjective_sheafifyUnit _)
    (liftedTensorUnit_isLocallyInjective X F G)
    (liftedTensorUnit_isLocallySurjective X F G)
    (Iso.refl _)

end Unit

end Stacks.SheafOfModules.CoherentLift

end
