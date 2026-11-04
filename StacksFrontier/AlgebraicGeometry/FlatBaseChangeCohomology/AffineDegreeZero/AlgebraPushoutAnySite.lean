module

public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.ColimitSheafifyComparison

/-!
# The module underlying a pushout of sheaves of commutative rings, on a site of any size

`StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.AlgebraPushout`
identifies the module underlying a pushout `B ⊗_R R'` of sheaves of commutative rings with the
extension of scalars along `φ : R ⟶ R'` of the module underlying `B`, for a site whose objects
and morphisms lie in the universe of the sections.  This file states and proves the same
identification with the three universes free: objects in `Type u₁`, morphisms in `Type v₁` and
sections in `CommRingCat.{u}`.

The widening is needed because the small étale site of an algebraic space is not of that
restricted shape: `AlgebraicGeometry.Space.smallEtaleRingedSite` is a `RingedSite.{u + 1, u, u}`,
with objects in `Type (u + 1)` and both morphisms and structure sheaf in `u`, so none of the
results of the small-site file can be instantiated at it.

## Main definitions

* `Stacks.SheafOfModules.AlgebraPushout.underlyingModule_anySite`: the `R`-module underlying a
  sheaf of commutative `R`-algebras.
* `Stacks.SheafOfModules.AlgebraPushout.moduleMapOver_anySite`: the morphism of underlying
  modules, semilinear over `φ`, attached to a morphism of the underlying sheaves of rings
  commuting with the two structure morphisms.
* `Stacks.SheafOfModules.AlgebraPushout.tensorSectionsIso_anySite`: at each `U` the tensor
  product `R'(U) ⊗_{R(U)} B(U)` *is* the sections over `U` of the colimit of the underlying
  presheaves of commutative rings.
* `Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparison_anySite`: the canonical
  comparison `R' ⊗_R B ⟶ B ⊗_R R'` of underlying modules, the adjoint transpose of the
  inclusion of the first factor of the pushout.
* `Stacks.SheafOfModules.AlgebraPushout.underlyingModulePushoutIso_anySite`: the resulting
  identification of the module underlying `B ⊗_R R'` with the extension of scalars along `φ` of
  the module underlying `B`.

## Main results

* `Stacks.SheafOfModules.AlgebraPushout.isIso_extendScalarsComparison_anySite`: **the canonical
  comparison is invertible**, on a site of any size.

## Implementation notes

Every declaration here carries the suffix `_anySite` and every statement is new: the
corresponding small-site declaration is left exactly as it stands, because widening the
universes of a declaration that already exists is a change of its statement.  The small-site
file's `variable` line is untouched for the same reason — widening it would silently retype
every declaration beneath it.

Two things besides the universes have to change, and neither is new mathematics.

*The extension of scalars is taken from a different source.*
`Stacks.Sheaves.ModuleAdjunction.extendScalars`, which the small-site file uses, is stated for
`[SmallCategory C]` with every universe collapsed to one, because the left adjoint it is built
from is only known to exist through Mathlib's
`PresheafOfModules.pullbackObjIsDefined_eq_top`, itself restricted to small sites.  This file
uses `Stacks.FlatChangeOfRings.extendScalars` instead, which is unconditional at free universes
because it is built objectwise from `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings`; its
`Stacks.FlatChangeOfRings.ringSheafMap` is the same term as the small-site file's `ringSheafMap`,
and `Stacks.SheafOfModules.Tensor.ringSheaf` the same sheaf of rings as its `ringSheaf`, so the
two statements are about the same objects.

*Instances that smallness supplied are now hypotheses.*  `GrothendieckTopology.HasSheafCompose`
for `forget₂ CommRingCat RingCat` holds on any site and in any universe of sections
(`Stacks.hasSheafCompose_forget₂_commRingCat`), but deliberately is not a global instance, so it
is carried here as a hypothesis, as elsewhere in the development.  Sheafification of sheaves of
commutative rings, pushouts of them, and the identification of local equivalences with locally
bijective morphisms are likewise hypotheses rather than consequences of the site's shape.  All
of them are available on the small étale site of an algebraic space.

## References

* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe v₁ u₁ u

namespace Stacks.SheafOfModules.AlgebraPushout

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R R' : Sheaf J CommRingCat.{u}}

/-- The `R`-module underlying a sheaf of commutative `R`-algebras, on a site of any size: its
underlying sheaf of rings, viewed as a module over itself and then restricted along the
structure morphism. -/
public noncomputable def underlyingModule_anySite (B : Under R) :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R) :=
  (_root_.SheafOfModules.restrictScalars.{u} (Stacks.FlatChangeOfRings.ringSheafMap B.hom)).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf B.right))

/-! ### Semilinear morphisms of underlying modules -/

/-- The morphism of abelian presheaves underlying a morphism `ψ` of the sheaves of rings
underlying two algebra sheaves over different base ring sheaves, on a site of any size.
Restriction of scalars does not change the underlying presheaf of abelian groups, so this is
literally the map on sections of `ψ`. -/
public noncomputable def presheafMapOver_anySite (φ : R ⟶ R') {B : Under R} {B' : Under R'}
    (ψ : B.right ⟶ B'.right) :
    (underlyingModule_anySite B).val.presheaf ⟶
      ((_root_.SheafOfModules.restrictScalars.{u}
          (Stacks.FlatChangeOfRings.ringSheafMap φ)).obj
        (underlyingModule_anySite B')).val.presheaf where
  app U := AddCommGrpCat.ofHom (ψ.hom.app U).hom.toAddMonoidHom
  naturality _ _ f :=
    congrArg (fun t ↦ AddCommGrpCat.ofHom (RingHom.toAddMonoidHom (CommRingCat.Hom.hom t)))
      (ψ.hom.naturality f)

/-- **The morphism of underlying modules, semilinear over `φ`, on a site of any size.**  Let
`ψ : B.right ⟶ B'.right` be a morphism of the sheaves of rings underlying a sheaf of
`R`-algebras `B` and a sheaf of `R'`-algebras `B'`, commuting with the two structure morphisms
over `φ : R ⟶ R'`.  Then `ψ` is a morphism from the `R`-module underlying `B` to the `R`-module
obtained from the `R'`-module underlying `B'` by restriction of scalars along `φ`:  on sections
it is the map on sections of `ψ`, and its `R`-linearity is the commuting square, because the
action of a section `r` of `R` is multiplication by its image under the structure morphism. -/
public noncomputable def moduleMapOver_anySite (φ : R ⟶ R') {B : Under R} {B' : Under R'}
    (ψ : B.right ⟶ B'.right) (w : B.hom ≫ ψ = φ ≫ B'.hom) :
    underlyingModule_anySite B ⟶
      (_root_.SheafOfModules.restrictScalars.{u}
        (Stacks.FlatChangeOfRings.ringSheafMap φ)).obj (underlyingModule_anySite B') :=
  ⟨PresheafOfModules.homMk (presheafMapOver_anySite φ ψ) (by
    intro U r y
    have hsq : (ψ.hom.app U).hom ((B.hom.hom.app U).hom r) =
        (B'.hom.hom.app U).hom ((φ.hom.app U).hom r) := by
      have h : ((B.hom ≫ ψ).hom.app U).hom r = ((φ ≫ B'.hom).hom.app U).hom r := by rw [w]
      exact h
    have h : ∀ y' : B.right.obj.obj U,
        (ψ.hom.app U).hom ((B.hom.hom.app U).hom r * y')
          = (B'.hom.hom.app U).hom ((φ.hom.app U).hom r) * (ψ.hom.app U).hom y' := fun y' ↦ by
      rw [map_mul, hsq]
    exact h y)⟩

/-! ### The pushout of the underlying presheaves, objectwise -/

section Pushout

variable [HasPushouts (Sheaf J CommRingCat.{u})]

/-- **The pushout of the underlying presheaves of commutative rings is computed objectwise**, on
a site of any size.  Evaluating at `U` the colimit of the span of underlying presheaves gives
the pushout of the *sections* over `U`, i.e. the pushout of the two structure maps
`R(U) ⟶ B(U)` and `R(U) ⟶ R'(U)` in `CommRingCat`. -/
public noncomputable def presheafPushoutObjIso_anySite (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ) :
    (colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).obj U ≅
      pushout (B.hom.hom.app U) (φ.hom.app U) :=
  colimitObjIsoColimitCompEvaluation (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u}) U ≪≫
    HasColimit.isoOfNatIso (diagramIsoSpan _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasPushouts (Sheaf J CommRingCat.{u})] in
/-- The objectwise identification of the presheaf pushout carries the first leg of the colimit
cocone to the inclusion `pushout.inl` of the first factor, on a site of any size. -/
@[simp]
public theorem colimit_ι_app_comp_presheafPushoutObjIso_hom_anySite (φ : R ⟶ R') (B : Under R)
    (U : Cᵒᵖ) :
    (colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u}) WalkingSpan.left).app U ≫
        (presheafPushoutObjIso_anySite φ B U).hom =
      pushout.inl (B.hom.hom.app U) (φ.hom.app U) := by
  simp [presheafPushoutObjIso_anySite]

section TensorSections

open Stacks.PresheafOfModules.ChangeOfRings

/-- **The tensor product of the sections is the presheaf pushout at `U`**, on a site of any
size.  The two structure maps make `R'(U)` and `B(U)` algebras over `R(U)`, and
`CommRingCat.pushoutCoconeIsColimit` exhibits `R'(U) ⊗_{R(U)} B(U)` as a pushout of the two — of
the span in the other order, whence the flip. -/
public noncomputable def tensorSectionsIso_anySite (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    CommRingCat.of (R'.obj.obj U ⊗[R.obj.obj U] B.right.obj.obj U) ≅
      (colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).obj U :=
  letI := (φ.hom.app U).hom.toAlgebra
  letI := (B.hom.hom.app U).hom.toAlgebra
  IsColimit.coconePointUniqueUpToIso
      (PushoutCocone.flipIsColimit (CommRingCat.pushoutCoconeIsColimit
        (R.obj.obj U) (R'.obj.obj U) (B.right.obj.obj U)))
      (colimit.isColimit (span (B.hom.hom.app U) (φ.hom.app U))) ≪≫
    (presheafPushoutObjIso_anySite φ B U).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasPushouts (Sheaf J CommRingCat.{u})] in
/-- `tensorSectionsIso_anySite` as the composite of its two factors.  The ascribed source of the
isomorphism is the tensor product, whereas the colimit comparison it is built from has the
cocone point of `CommRingCat.pushoutCocone` for source; the two are the same object, but only
after unfolding that cocone. -/
public theorem tensorSectionsIso_hom_anySite (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    (tensorSectionsIso_anySite φ B U).hom =
      (IsColimit.coconePointUniqueUpToIso
          (PushoutCocone.flipIsColimit (CommRingCat.pushoutCoconeIsColimit
            (R.obj.obj U) (R'.obj.obj U) (B.right.obj.obj U)))
          (colimit.isColimit (span (B.hom.hom.app U) (φ.hom.app U)))).hom ≫
        (presheafPushoutObjIso_anySite φ B U).inv :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasPushouts (Sheaf J CommRingCat.{u})] in
/-- On the pure tensor `1 ⊗ b` the objectwise identification is the first leg of the colimit
cocone, on a site of any size. -/
public theorem tensorSectionsIso_hom_one_tmul_anySite (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ)
    (b : B.right.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    (tensorSectionsIso_anySite φ B U).hom.hom ((1 : R'.obj.obj U) ⊗ₜ[R.obj.obj U] b) =
      ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
        WalkingSpan.left).app U).hom b := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (B.hom.hom.app U).hom.toAlgebra
  have hleg : (CommRingCat.pushoutCocone (R.obj.obj U) (R'.obj.obj U)
          (B.right.obj.obj U)).flip.ι.app WalkingSpan.left ≫
        (tensorSectionsIso_anySite φ B U).hom =
      (colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u}) WalkingSpan.left).app U := by
    rw [tensorSectionsIso_hom_anySite, ← Category.assoc,
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι, Iso.comp_inv_eq,
      colimit_ι_app_comp_presheafPushoutObjIso_hom_anySite]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hleg) b

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasPushouts (Sheaf J CommRingCat.{u})] in
/-- On the pure tensor `a ⊗ 1` the objectwise identification is the second leg of the colimit
cocone, on a site of any size. -/
public theorem tensorSectionsIso_hom_tmul_one_anySite (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ)
    (a : R'.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    (tensorSectionsIso_anySite φ B U).hom.hom (a ⊗ₜ[R.obj.obj U] (1 : B.right.obj.obj U)) =
      ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
        WalkingSpan.right).app U).hom a := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (B.hom.hom.app U).hom.toAlgebra
  have hleg : (CommRingCat.pushoutCocone (R.obj.obj U) (R'.obj.obj U)
          (B.right.obj.obj U)).flip.ι.app WalkingSpan.right ≫
        (tensorSectionsIso_anySite φ B U).hom =
      (colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
        WalkingSpan.right).app U := by
    rw [tensorSectionsIso_hom_anySite, ← Category.assoc,
      IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι, Iso.comp_inv_eq]
    show pushout.inr (B.hom.hom.app U) (φ.hom.app U) = _
    simp [presheafPushoutObjIso_anySite]
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hleg) a

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasPushouts (Sheaf J CommRingCat.{u})] in
/-- **The objectwise identification on a pure tensor**, on a site of any size.  It carries
`a ⊗ b` to the product of the images of `a` and `b` under the two legs of the colimit cocone,
because it is a ring homomorphism and `a ⊗ b = (a ⊗ 1)(1 ⊗ b)`. -/
public theorem tensorSectionsIso_hom_tmul_anySite (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ)
    (a : R'.obj.obj U) (b : B.right.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    (tensorSectionsIso_anySite φ B U).hom.hom (a ⊗ₜ[R.obj.obj U] b) =
      ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
            WalkingSpan.right).app U).hom a *
        ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
            WalkingSpan.left).app U).hom b := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (B.hom.hom.app U).hom.toAlgebra
  rw [show (a ⊗ₜ[R.obj.obj U] b) =
      (a ⊗ₜ[R.obj.obj U] (1 : B.right.obj.obj U)) *
        ((1 : R'.obj.obj U) ⊗ₜ[R.obj.obj U] b) from by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul,
    tensorSectionsIso_hom_tmul_one_anySite, tensorSectionsIso_hom_one_tmul_anySite]

omit [HasPushouts (Sheaf J CommRingCat.{u})] in
/-- **The objectwise identification is natural in `U`**, on a site of any size.  On a pure
tensor both sides are the product of the images of `a` and `b` under the two legs of the colimit
cocone over the smaller object, by multiplicativity of the restriction map of the colimit
presheaf together with the naturality of the two legs; the general case follows because every
map in sight is additive. -/
public theorem tensorSectionsIso_hom_naturality_anySite (φ : R ⟶ R') (B : Under R) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    ∀ x : R'.obj.obj U ⊗[R.obj.obj U] B.right.obj.obj U,
    ((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom
        ((tensorSectionsIso_anySite φ B U).hom.hom x) =
      (tensorSectionsIso_anySite φ B V).hom.hom
        ((cofMap φ.hom (underlyingModule_anySite B).val f).hom x) := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (φ.hom.app V).hom.toAlgebra
  let := (B.hom.hom.app U).hom.toAlgebra
  let := (B.hom.hom.app V).hom.toAlgebra
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
    simp only [map_zero]
    exact ((congrArg (CommRingCat.Hom.hom (tensorSectionsIso_anySite φ B V).hom)
      (map_zero (ModuleCat.Hom.hom (cofMap φ.hom (underlyingModule_anySite B).val f)))).trans
      (map_zero _)).symm
  | add u v hu hv =>
    simp only [map_add, hu, hv]
    exact ((congrArg (CommRingCat.Hom.hom (tensorSectionsIso_anySite φ B V).hom)
      (map_add (ModuleCat.Hom.hom (cofMap φ.hom (underlyingModule_anySite B).val f)) u v)).trans
      (map_add _ _ _)).symm
  | tmul a b =>
    have hl : ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
            WalkingSpan.left).app V).hom ((B.right.obj.map f).hom b) =
        ((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom
          (((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
            WalkingSpan.left).app U).hom b) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
          WalkingSpan.left).naturality f)) b
    have hr : ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
            WalkingSpan.right).app V).hom ((R'.obj.map f).hom a) =
        ((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom
          (((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
            WalkingSpan.right).app U).hom a) :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
          WalkingSpan.right).naturality f)) a
    have hc : (ModuleCat.Hom.hom (cofMap φ.hom (underlyingModule_anySite B).val f))
          (a ⊗ₜ[R.obj.obj U] b) =
        ((R'.obj.map f).hom a) ⊗ₜ[R.obj.obj V] ((B.right.obj.map f).hom b) :=
      cofMap_tmul φ.hom (underlyingModule_anySite B).val f a b
    calc ((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom
          ((tensorSectionsIso_anySite φ B U).hom.hom (a ⊗ₜ[R.obj.obj U] b))
        = ((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom
            (((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
                WalkingSpan.right).app U).hom a *
              ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
                WalkingSpan.left).app U).hom b) :=
          congrArg _ (tensorSectionsIso_hom_tmul_anySite φ B U a b)
      _ = ((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom
            (((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
              WalkingSpan.right).app U).hom a) *
          ((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom
            (((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
              WalkingSpan.left).app U).hom b) := map_mul _ _ _
      _ = ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
              WalkingSpan.right).app V).hom ((R'.obj.map f).hom a) *
          ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
              WalkingSpan.left).app V).hom ((B.right.obj.map f).hom b) := by
          rw [hl, hr]
      _ = (tensorSectionsIso_anySite φ B V).hom.hom
            (((R'.obj.map f).hom a) ⊗ₜ[R.obj.obj V] ((B.right.obj.map f).hom b)) :=
          (tensorSectionsIso_hom_tmul_anySite φ B V _ _).symm
      _ = (tensorSectionsIso_anySite φ B V).hom.hom
            ((cofMap φ.hom (underlyingModule_anySite B).val f).hom (a ⊗ₜ[R.obj.obj U] b)) :=
          congrArg _ hc.symm

end TensorSections

/-! ### The comparison with extension of scalars -/

section Comparison

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.PresheafOfModules.ChangeOfRings
open Stacks.FlatChangeOfRings (extendScalars extendScalarsAdjunction ringSheafMap)

/-- The `R`-module morphism from the module underlying `B` to the module underlying the pushout
`B ⊗_R R'`, read over `R` by restriction of scalars along `φ`, on a site of any size.  It is the
inclusion `pushout.inl` of the first factor, whose compatibility with the structure morphisms is
the pushout square itself. -/
public noncomputable def pushoutInlModuleMap_anySite (φ : R ⟶ R') (B : Under R) :
    underlyingModule_anySite B ⟶
      (_root_.SheafOfModules.restrictScalars.{u} (ringSheafMap φ)).obj
        (underlyingModule_anySite ((Under.pushout φ).obj B)) :=
  moduleMapOver_anySite φ (pushout.inl B.hom φ) pushout.condition

/-- **The canonical comparison of the extension of scalars with the module underlying the
pushout, on a site of any size.**  For a morphism `φ : R ⟶ R'` of sheaves of commutative rings
and a sheaf of commutative `R`-algebras `B`, this is the morphism

`R' ⊗_R (module underlying B) ⟶ module underlying (B ⊗_R R')`

adjoint to the inclusion of the first factor of the pushout. -/
public noncomputable def extendScalarsComparison_anySite (φ : R ⟶ R') (B : Under R) :
    (extendScalars φ).obj (underlyingModule_anySite B) ⟶
      underlyingModule_anySite ((Under.pushout φ).obj B) :=
  ((extendScalarsAdjunction φ).homEquiv _ _).symm (pushoutInlModuleMap_anySite φ B)

/-- The adjoint transpose of the comparison is the inclusion of the first factor of the pushout,
on a site of any size. -/
public theorem homEquiv_extendScalarsComparison_anySite (φ : R ⟶ R') (B : Under R) :
    ((extendScalarsAdjunction φ).homEquiv _ _) (extendScalarsComparison_anySite φ B) =
      pushoutInlModuleMap_anySite φ B :=
  Equiv.apply_symm_apply _ _

/-! #### Invertibility of the comparison -/

/-- **The comparison, at the level of presheaves of modules**, on a site of any size.  The
adjoint transpose of `pushoutInlModuleMap_anySite` under the *presheaf*-level change-of-rings
adjunction of [Stacks, Tag 03CU]: a morphism from the objectwise tensor product
`U ↦ R'(U) ⊗_{R(U)} B(U)` to the presheaf of modules underlying `B ⊗_R R'`. -/
public noncomputable def changeOfRingsComparison_anySite (φ : R ⟶ R') (B : Under R) :
    (changeOfRings φ.hom).obj (underlyingModule_anySite B).val ⟶
      (underlyingModule_anySite ((Under.pushout φ).obj B)).val :=
  counitHom φ.hom ((pushoutInlModuleMap_anySite φ B).val)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On the pure tensor `a ⊗ b` the presheaf-level comparison is the product of the images of `a`
and `b` under the two inclusions of the pushout, on a site of any size. -/
public theorem changeOfRingsComparison_app_tmul_anySite (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ)
    (a : R'.obj.obj U) (b : B.right.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    ((changeOfRingsComparison_anySite φ B).app U).hom (a ⊗ₜ[R.obj.obj U] b) =
      ((pushout.inr B.hom φ).hom.app U).hom a * ((pushout.inl B.hom φ).hom.app U).hom b :=
  counitApp_tmul φ.hom ((pushoutInlModuleMap_anySite φ B).val) U a b

variable [HasWeakSheafify J CommRingCat.{u}] [J.WEqualsLocallyBijective CommRingCat.{u}]

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}] [J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- **The presheaf-level comparison factors through the colimit of the underlying presheaves**,
on a site of any size.  It is the objectwise identification `tensorSectionsIso_anySite` followed
by `CategoryTheory.Sheaf.colimitToColimitObj`, the comparison of the colimit of the underlying
presheaves with the underlying presheaf of the colimit. -/
public theorem changeOfRingsComparison_app_anySite (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    ∀ x : R'.obj.obj U ⊗[R.obj.obj U] B.right.obj.obj U,
    ((changeOfRingsComparison_anySite φ B).app U).hom x =
      ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U).hom
        ((tensorSectionsIso_anySite φ B U).hom.hom x) := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (B.hom.hom.app U).hom.toAlgebra
  have hil : ∀ y : B.right.obj.obj U,
      ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U).hom
          (((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
            WalkingSpan.left).app U).hom y) =
        ((pushout.inl B.hom φ).hom.app U).hom y := fun y =>
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (NatTrans.congr_app
      (Sheaf.ι_colimitToColimitObj J (span B.hom φ) WalkingSpan.left) U)) y
  have hir : ∀ y : R'.obj.obj U,
      ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U).hom
          (((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
            WalkingSpan.right).app U).hom y) =
        ((pushout.inr B.hom φ).hom.app U).hom y := fun y =>
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (NatTrans.congr_app
      (Sheaf.ι_colimitToColimitObj J (span B.hom φ) WalkingSpan.right) U)) y
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
    refine (map_zero (ModuleCat.Hom.hom ((changeOfRingsComparison_anySite φ B).app U))).trans ?_
    exact ((congrArg (CommRingCat.Hom.hom
      ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U))
      (map_zero (CommRingCat.Hom.hom (tensorSectionsIso_anySite φ B U).hom))).trans
      (map_zero _)).symm
  | add u v hu hv =>
    refine (map_add (ModuleCat.Hom.hom ((changeOfRingsComparison_anySite φ B).app U)) u v).trans ?_
    refine (congrArg (fun z => z + ((changeOfRingsComparison_anySite φ B).app U).hom v) hu).trans
      ((congrArg (fun z => ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U).hom
        ((tensorSectionsIso_anySite φ B U).hom.hom u) + z) hv).trans ?_)
    exact ((congrArg (CommRingCat.Hom.hom
      ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U))
      (map_add (CommRingCat.Hom.hom (tensorSectionsIso_anySite φ B U).hom) u v)).trans
      (map_add _ _ _)).symm
  | tmul a b =>
    have hmul : ((pushout.inr B.hom φ).hom.app U).hom a *
          ((pushout.inl B.hom φ).hom.app U).hom b =
        ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U).hom
            (((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
              WalkingSpan.right).app U).hom a) *
          ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U).hom
            (((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
              WalkingSpan.left).app U).hom b) := by
      rw [hil b, hir a]
    exact (changeOfRingsComparison_app_tmul_anySite φ B U a b).trans (hmul.trans
      ((map_mul (CommRingCat.Hom.hom ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U))
          _ _).symm.trans
        (congrArg _ (tensorSectionsIso_hom_tmul_anySite φ B U a b).symm)))

/-- **The presheaf-level comparison is locally injective**, on a site of any size.  Two sections
with the same image have the same image under `CategoryTheory.Sheaf.colimitToColimitObj` composed
with the objectwise isomorphism, so they agree locally there; the objectwise isomorphism is
natural and injective, so they agree locally to begin with. -/
public instance isLocallyInjective_changeOfRingsComparison_anySite (φ : R ⟶ R') (B : Under R) :
    PresheafOfModules.IsLocallyInjective J (changeOfRingsComparison_anySite φ B) where
  equalizerSieve_mem {X} x y h := by
    have h' : ((Sheaf.colimitToColimitObj J (span B.hom φ)).app X).hom
          ((tensorSectionsIso_anySite φ B X).hom.hom x) =
        ((Sheaf.colimitToColimitObj J (span B.hom φ)).app X).hom
          ((tensorSectionsIso_anySite φ B X).hom.hom y) :=
      (changeOfRingsComparison_app_anySite φ B X x).symm.trans
        (h.trans (changeOfRingsComparison_app_anySite φ B X y))
    refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J
      (Sheaf.colimitToColimitObj J (span B.hom φ)) _ _ h')
    intro Y p hp
    exact (ConcreteCategory.bijective_of_isIso
        (tensorSectionsIso_anySite φ B (op Y)).hom).injective
      ((tensorSectionsIso_hom_naturality_anySite φ B p.op x).symm.trans
        (hp.trans (tensorSectionsIso_hom_naturality_anySite φ B p.op y)))

/-- **The presheaf-level comparison is locally surjective**, on a site of any size.  A section
of the target is locally in the image of `CategoryTheory.Sheaf.colimitToColimitObj`, and the
objectwise isomorphism lifts each such preimage to the tensor product. -/
public instance isLocallySurjective_changeOfRingsComparison_anySite (φ : R ⟶ R') (B : Under R) :
    PresheafOfModules.IsLocallySurjective J (changeOfRingsComparison_anySite φ B) where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J
      (Sheaf.colimitToColimitObj J (span B.hom φ)) s)
    rintro Y p ⟨t, ht⟩
    refine ⟨(tensorSectionsIso_anySite φ B (op Y)).inv.hom t, ?_⟩
    have e : (tensorSectionsIso_anySite φ B (op Y)).hom.hom
          ((tensorSectionsIso_anySite φ B (op Y)).inv.hom t) = t :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (tensorSectionsIso_anySite φ B (op Y)).inv_hom_id) t
    exact (changeOfRingsComparison_app_anySite φ B (op Y) _).trans ((congrArg _ e).trans ht)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify J CommRingCat.{u}] [J.WEqualsLocallyBijective CommRingCat.{u}] in
/-- The adjoint transpose of the presheaf-level comparison is the inclusion of the first factor
of the pushout, read on underlying presheaves of modules, on a site of any size. -/
public theorem homEquiv_changeOfRingsComparison_anySite (φ : R ⟶ R') (B : Under R) :
    ((changeOfRingsAdjunction φ.hom).homEquiv _ _) (changeOfRingsComparison_anySite φ B) =
      (pushoutInlModuleMap_anySite φ B).val := by
  simp only [changeOfRingsAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact (homEquivCore φ.hom _ _).apply_symm_apply _

/-- **The canonical comparison is invertible, on a site of any size.**  For every sheaf of
`R'`-modules `Z`, precomposition with the comparison is a bijection on morphisms into `Z`: the
change-of-rings adjunction turns it into precomposition with the presheaf-level comparison
`changeOfRingsComparison_anySite`, by `homEquiv_changeOfRingsComparison_anySite` together with
`CategoryTheory.Adjunction.homEquiv_naturality_right` on both sides, and that is a bijection into
a sheaf because the presheaf-level comparison is locally bijective
(`PresheafOfModules.homEquivOfIsLocallyBijective`).  So
`CategoryTheory.isIso_of_coyoneda_map_bijective` applies.

This is the invertibility that [Stacks, Tag 01SA] and the degree-zero case of [Stacks, Tag
02KH] ask for, now available on the small étale site of an algebraic space. -/
public theorem isIso_extendScalarsComparison_anySite (φ : R ⟶ R') (B : Under R) :
    IsIso (extendScalarsComparison_anySite φ B) := by
  refine isIso_of_coyoneda_map_bijective _ fun Z => ?_
  have key : ∀ y : underlyingModule_anySite ((Under.pushout φ).obj B) ⟶ Z,
      extendScalarsComparison_anySite φ B ≫ y =
        ((extendScalarsAdjunction φ).homEquiv (underlyingModule_anySite B) Z).symm
          ((_root_.SheafOfModules.fullyFaithfulForget
              (Stacks.SheafOfModules.Tensor.ringSheaf R)).homEquiv.symm
            (((changeOfRingsAdjunction φ.hom).homEquiv _ _)
              ((PresheafOfModules.homEquivOfIsLocallyBijective
                (changeOfRingsComparison_anySite φ B) Z.isSheaf)
                ((_root_.SheafOfModules.fullyFaithfulForget
                  (Stacks.SheafOfModules.Tensor.ringSheaf R')).homEquiv y)))) := by
    intro y
    refine ((extendScalarsAdjunction φ).homEquiv
      (underlyingModule_anySite B) Z).injective ?_
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
      homEquiv_extendScalarsComparison_anySite]
    refine _root_.SheafOfModules.hom_ext ?_
    show (pushoutInlModuleMap_anySite φ B).val ≫ (restrictScalars φ.hom).map y.val =
      ((changeOfRingsAdjunction φ.hom).homEquiv (underlyingModule_anySite B).val Z.val)
        (changeOfRingsComparison_anySite φ B ≫ y.val)
    exact (congrArg (fun z => z ≫ (restrictScalars φ.hom).map y.val)
        (homEquiv_changeOfRingsComparison_anySite φ B).symm).trans
      ((changeOfRingsAdjunction φ.hom).homEquiv_naturality_right
        (changeOfRingsComparison_anySite φ B) y.val).symm
  rw [show (fun (y : underlyingModule_anySite ((Under.pushout φ).obj B) ⟶ Z) =>
      extendScalarsComparison_anySite φ B ≫ y) = _ from funext key]
  exact ((extendScalarsAdjunction φ).homEquiv
      (underlyingModule_anySite B) Z).symm.bijective.comp
    (((_root_.SheafOfModules.fullyFaithfulForget
        (Stacks.SheafOfModules.Tensor.ringSheaf R)).homEquiv.symm.bijective).comp
      ((((changeOfRingsAdjunction φ.hom).homEquiv _ _).bijective).comp
        (((PresheafOfModules.homEquivOfIsLocallyBijective
            (changeOfRingsComparison_anySite φ B) Z.isSheaf).bijective).comp
          ((_root_.SheafOfModules.fullyFaithfulForget
            (Stacks.SheafOfModules.Tensor.ringSheaf R')).homEquiv.bijective))))

/-- **The module underlying a pushout of algebra sheaves is an extension of scalars, on a site of
any size.**  This is the identification that the `algebraPullback_isQuasicoherent` clause of
[Stacks, Tag 081V] needs for the small étale site of an algebraic space, whose objects lie one
universe above its morphisms and its structure sheaf. -/
public noncomputable def underlyingModulePushoutIso_anySite (φ : R ⟶ R') (B : Under R) :
    underlyingModule_anySite ((Under.pushout φ).obj B) ≅
      (extendScalars φ).obj (underlyingModule_anySite B) :=
  (@asIso _ _ _ _ (extendScalarsComparison_anySite φ B)
    (isIso_extendScalarsComparison_anySite φ B)).symm

end Comparison

end Pushout

end Stacks.SheafOfModules.AlgebraPushout

end
