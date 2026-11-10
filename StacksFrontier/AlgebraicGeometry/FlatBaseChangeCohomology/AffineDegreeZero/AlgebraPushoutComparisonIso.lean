module

public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ChangeOfRingsAdjunction
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.AlgebraPushout
public import StacksFrontier.CategoryTheory.Sites.ColimitSheafifyComparison

/-!
# The module underlying a pushout of sheaves of commutative rings is an extension of scalars

Let `(C, J)` be a site, let `φ : R ⟶ R'` be a morphism of sheaves of commutative rings on it
and let `B` be a sheaf of commutative `R`-algebras, i.e. an object of `Under R`.  Pushing `B`
out along `φ` produces the sheaf of commutative `R'`-algebras `B ⊗_R R'`, and the mathematics
that several developments in this repository are waiting on is the identification of the
`R'`-module *underlying* that pushout with the extension of scalars along `φ` of the
`R`-module underlying `B`.

`StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.AlgebraPushout`
constructs the canonical comparison morphism

`(R' ⊗_R -) (underlying module of B) ⟶ underlying module of (B ⊗_R R')`,

in the only direction the change-of-rings adjunction supplies it.  This file proves that it is
an isomorphism.

## Main definitions

* `Stacks.SheafOfModules.AlgebraPushout.tensorSectionsIso`: at each `U` the tensor product
  `R'(U) ⊗_{R(U)} B(U)` *is* the sections over `U` of the colimit of the underlying presheaves
  of commutative rings.
* `Stacks.SheafOfModules.AlgebraPushout.changeOfRingsComparison`: the comparison at the level
  of presheaves of modules, i.e. the adjoint transpose of `pushoutInlModuleMap` under the
  presheaf-level change-of-rings adjunction of [Stacks, Tag 03CU].
* `Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparisonIso`: the identification of the
  module underlying `B ⊗_R R'` with the extension of scalars of the module underlying `B`,
  with no hypothesis, the invertibility being supplied by `isIso_extendScalarsComparison`.

## Main results

* `Stacks.SheafOfModules.AlgebraPushout.unit_comp_restrictScalars_map_extendScalarsComparison`
  and `extendScalarsComparison_app_unit`: the adjoint transpose read as a composite with the
  unit of the change-of-rings adjunction, and the resulting value of the comparison on the
  image of a section of `B` under that unit, which is the pure tensor `1 ⊗ b`.  This is the
  computation that pins an objectwise identification of the two sides to *this* morphism.
* `Stacks.SheafOfModules.AlgebraPushout.isIso_extendScalarsComparison`: **the comparison is an
  isomorphism.**  This is the invertibility that [Stacks, Tag 01SA] and the degree-zero case of
  [Stacks, Tag 02KH] ask for; `extendScalarsComparisonIso` reads it as an isomorphism, and
  `underlyingModulePushoutIso` is the inverse under the same invertibility taken as a
  hypothesis.
* `Stacks.SheafOfModules.AlgebraPushout.presheafPushoutObjIso` and
  `colimit_ι_app_comp_presheafPushoutObjIso_hom`: the pushout of the underlying presheaves of
  commutative rings is computed objectwise — at `U` it is the pushout of the sections — and the
  identification carries the first leg of the colimit cocone to `pushout.inl`.
* `Stacks.SheafOfModules.AlgebraPushout.tensorSectionsIso_hom_tmul` and
  `tensorSectionsIso_hom_naturality`: the objectwise identification sends `a ⊗ b` to the
  product of the images of `a` and `b` under the two legs of the colimit cocone, and it is
  natural in `U`.
* `Stacks.SheafOfModules.AlgebraPushout.changeOfRingsComparison_app`,
  `isLocallyInjective_changeOfRingsComparison` and
  `isLocallySurjective_changeOfRingsComparison`: the presheaf-level comparison is the
  objectwise identification followed by `CategoryTheory.Sheaf.colimitToColimitObj`, and is
  therefore locally bijective.

## Implementation notes

**Why only a morphism.**  Extension of scalars for sheaves of modules
(`Stacks.Sheaves.ModuleAdjunction.extendScalars`) is defined by its universal property, as
the left adjoint of restriction of scalars, so a morphism *out of* it is the same thing as a
morphism into a restriction of scalars.  The map `pushout.inl : B.right ⟶ B.right ⊗_R R'` of
sheaves of rings is such a morphism, once its source and target are read as modules over `R`;
transposing it gives the comparison.  Nothing in the adjunction produces a morphism in the
other direction, because that would need a description of the sections of an abstract left
adjoint.  The same asymmetry, for the tensor product rather than for a pushout of algebras,
is recorded in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean`.

**How invertibility is proved.**  Not through the sheaf-level left adjoint at all — nothing
in this proof describes the sections of `Stacks.Sheaves.ModuleAdjunction.extendScalars`, and
neither `Stacks.Sheaves.ModuleAdjunction.extendScalarsIso` nor
`Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoTensor` is used (the latter is a
`CategoryTheory.Adjunction.leftAdjointUniq`, hence opaque on sections).  The whole argument is
run by `CategoryTheory.isIso_of_coyoneda_map_bijective` against the *presheaf*-level
change-of-rings adjunction of [Stacks, Tag 03CU], in three steps.

1. *The objectwise identification.*  `presheafPushoutObjIso` computes the colimit of the
   underlying presheaves of commutative rings at `U` as the pushout of the sections, and
   `CommRingCat.pushoutCoconeIsColimit` computes that pushout as a tensor product.  The cocone
   Mathlib supplies is indexed by the span in the other order, so
   `CategoryTheory.Limits.PushoutCocone.flipIsColimit` is applied to it; that also removes any
   need for `Algebra.TensorProduct.comm`.
   The result is `tensorSectionsIso`.  Its source is *the same object* as the value at `U` of
   `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings φ.hom` on `(underlyingModule B).val`,
   not merely an isomorphic one: `ModuleCat.restrictScalars` along `B.hom` and
   `RingHom.toAlgebra` of `B.hom` put the same `R(U)`-module structure on `B(U)`, so the two
   tensor products are definitionally equal.  `tensorSectionsIso_hom_tmul` evaluates it on
   pure tensors and `tensorSectionsIso_hom_naturality` is its naturality in `U`, proved on
   pure tensors from the naturality of the two colimit legs and the multiplicativity of the
   restriction maps of the colimit presheaf.
2. *Local bijectivity of the presheaf-level comparison.*  `changeOfRingsComparison` is the
   presheaf-level transpose of `pushoutInlModuleMap`, and `changeOfRingsComparison_app`
   factors it as `tensorSectionsIso` followed by `CategoryTheory.Sheaf.colimitToColimitObj`.
   That comparison is locally bijective:
   `CategoryTheory.Sheaf.isLocallyInjective_colimitToColimitObj` and
   `CategoryTheory.Sheaf.isLocallySurjective_colimitToColimitObj` are *instances*, and they
   fire by `inferInstance` at `CategoryTheory.Limits.span B.hom φ`.  The two sieve conditions
   are then transported by hand across the objectwise isomorphism —
   `isLocallyInjective_changeOfRingsComparison` uses its naturality and injectivity,
   `isLocallySurjective_changeOfRingsComparison` only its surjectivity — which avoids having to
   compare a morphism of presheaves of `AddCommGrpCat` with one of presheaves of `CommRingCat`.
   Going instead through `CategoryTheory.Sheaf.sheafifyCocone` and `isColimitSheafifyCocone`,
   as this note once advised, reproves a weaker statement;
   `StacksFrontier/CategoryTheory/Sites/ColimitSheafifyComparison.lean`
   says in its own notes that it deliberately avoids that cocone.
3. *Transport to the sheaf level.*  For a sheaf of `R'`-modules `Z`, precomposition with
   `extendScalarsComparison` is, under the sheaf-level change-of-rings adjunction and then the
   presheaf-level one, precomposition with `changeOfRingsComparison`: both transposes are
   computed by `CategoryTheory.Adjunction.homEquiv_naturality_right` from
   `homEquiv_extendScalarsComparison` and `homEquiv_changeOfRingsComparison`.  Precomposition
   with a locally bijective morphism is a bijection into a sheaf by Mathlib's
   `PresheafOfModules.homEquivOfIsLocallyBijective`, and `SheafOfModules.forget` is fully
   faithful, so the composite of five bijections is precomposition with
   `extendScalarsComparison`.  No `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso` and no
   second spelling of extension of scalars appear.

**What `rw` cannot do here.**  `underlyingModule` is a sheaf of modules over `ringSheaf R`,
whose underlying presheaf of rings is `(ringSheaf R).obj`; the presheaf-level change-of-rings
machinery is indexed by `Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf R.obj`.  The two
are equal by `rfl`, but only after unfolding `CategoryTheory.sheafCompose`, which is
semireducible, so a term mentioning both is not type-correct at the transparency `rw` uses to
build its motive.  Every step of the proofs below that crosses that fork is therefore written
as a term — `Eq.trans`, `congrArg`, a `have` with the goal's own spelling — rather than as a
`rewrite`.  The same applies to the source of `tensorSectionsIso`, which is ascribed as
`CommRingCat.of` of a tensor product while the colimit comparison it is built from has the
cocone point of `CommRingCat.pushoutCocone` for source; `tensorSectionsIso_hom` names the
factorisation so that the leg computations can rewrite with it.

**Which spelling of the underlying sheaf of rings.**  `ringSheaf` is
`CategoryTheory.sheafCompose` applied to `CategoryTheory.forget₂ CommRingCat RingCat`, which is
the spelling of `AlgebraicGeometry.Scheme.ringCatSheaf` and of
`Stacks.RelativeSpec.AlgebraSheaf.ringSheaf`, and that is why
`underlyingModule_eq_algebraSheaf_underlyingModule` holds by `rfl`.  The tree also carries the
reducible abbreviation `CategoryTheory.Sheaf.toRingCat`, whose underlying presheaf is
syntactically `R.obj ⋙ forget₂ _ _` rather than a `sheafCompose`; the two are definitionally
equal but not interchangeable for instance search, as the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean` record.  Anything
stated over `toRingCat` has to cross that fork explicitly.

This material serves [Stacks, Tag 01SA] and the degree-zero case of [Stacks, Tag 02KH];
[Stacks, Tag 02KH] in full is
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_baseChangeMap_of_flat`,
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.isIso_higherBaseChangeMap` and
`Stacks.AlgebraicGeometry.FlatBaseChangeDerived.cohomologyBaseChangeIso`, in
`StacksFrontier/AlgebraicGeometry/FlatBaseChangeCohomology/Derived/FlatBaseChange.lean`.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules.AlgebraPushout

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

variable {R R' : Sheaf J CommRingCat.{u}}

/-! ### The pushout of the underlying presheaves, objectwise -/

/-- **The pushout of the underlying presheaves of commutative rings is computed objectwise.**
Evaluating at `U` the colimit of the span of underlying presheaves gives the pushout of the
*sections* over `U`, i.e. the pushout of the two structure maps `R(U) ⟶ B(U)` and
`R(U) ⟶ R'(U)` in `CommRingCat`.  Composing with `CommRingCat.pushoutCoconeIsColimit`
identifies that with the tensor product `B(U) ⊗_{R(U)} R'(U)`, and `Algebra.TensorProduct.comm`
flips it to the `R'(U) ⊗_{R(U)} B(U)` that a change of rings produces.

This is the objectwise half of the identification that `extendScalarsComparison` is invertible.
The other half is that the colimit of the underlying presheaves maps to the underlying presheaf
of the pushout *sheaf* by a locally bijective morphism, which the tree already has as
`CategoryTheory.Sheaf.colimitToColimitObj` together with
`CategoryTheory.Sheaf.isLocallyInjective_colimitToColimitObj` and
`CategoryTheory.Sheaf.isLocallySurjective_colimitToColimitObj`. -/
public noncomputable def presheafPushoutObjIso (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ) :
    (colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).obj U ≅
      pushout (B.hom.hom.app U) (φ.hom.app U) :=
  colimitObjIsoColimitCompEvaluation _ U ≪≫ HasColimit.isoOfNatIso (diagramIsoSpan _)

/-- The objectwise identification of the presheaf pushout carries the first leg of the colimit
cocone to the inclusion `pushout.inl` of the first factor.  This is what pins
`presheafPushoutObjIso` to the inclusion that `pushoutInlModuleMap` is built from, rather than
to some other isomorphism between the two sides. -/
@[simp]
public theorem colimit_ι_app_comp_presheafPushoutObjIso_hom (φ : R ⟶ R') (B : Under R)
    (U : Cᵒᵖ) :
    (colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u}) WalkingSpan.left).app U ≫
        (presheafPushoutObjIso φ B U).hom =
      pushout.inl (B.hom.hom.app U) (φ.hom.app U) := by
  simp [presheafPushoutObjIso]

section TensorSections

open Stacks.PresheafOfModules.ChangeOfRings

/-- **The tensor product of the sections is the presheaf pushout at `U`.**  The two structure
maps make `R'(U)` and `B(U)` algebras over `R(U)`, and `CommRingCat.pushoutCoconeIsColimit`
exhibits `R'(U) ⊗_{R(U)} B(U)` as a pushout of the two — of the span in the other order, whence
the flip.  Composing with `presheafPushoutObjIso` lands on the sections over `U` of the colimit
of the underlying presheaves.

The source is the value at `U` of `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings φ.hom`
on the module underlying `B`: the `R(U)`-module structure that restriction of scalars along
`B.hom` puts on `B(U)` is the one `(B.hom.hom.app U).hom.toAlgebra` gives, so the two tensor
products are the same object, not merely isomorphic ones. -/
public noncomputable def tensorSectionsIso (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ) :
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
    (presheafPushoutObjIso φ B U).symm

/-- `tensorSectionsIso` as the composite of its two factors.  The ascribed source of the
isomorphism is the tensor product, whereas the colimit comparison it is built from has the
cocone point of `CommRingCat.pushoutCocone` for source; the two are the same object, but only
after unfolding that cocone, which is why rewriting with the definition itself is not
enough. -/
public theorem tensorSectionsIso_hom (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    (tensorSectionsIso φ B U).hom =
      (IsColimit.coconePointUniqueUpToIso
          (PushoutCocone.flipIsColimit (CommRingCat.pushoutCoconeIsColimit
            (R.obj.obj U) (R'.obj.obj U) (B.right.obj.obj U)))
          (colimit.isColimit (span (B.hom.hom.app U) (φ.hom.app U)))).hom ≫
        (presheafPushoutObjIso φ B U).inv :=
  rfl

/-- The two legs of the flipped tensor product cocone are carried by `tensorSectionsIso` to the
two legs of the colimit cocone. -/
private theorem pushoutCocone_flip_ι_comp_tensorSectionsIso_hom (φ : R ⟶ R') (B : Under R)
    (U : Cᵒᵖ) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    (CommRingCat.pushoutCocone (R.obj.obj U) (R'.obj.obj U)
          (B.right.obj.obj U)).flip.ι.app WalkingSpan.left ≫ (tensorSectionsIso φ B U).hom =
        (colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u}) WalkingSpan.left).app U ∧
      (CommRingCat.pushoutCocone (R.obj.obj U) (R'.obj.obj U)
          (B.right.obj.obj U)).flip.ι.app WalkingSpan.right ≫ (tensorSectionsIso φ B U).hom =
        (colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u}) WalkingSpan.right).app U := by
  constructor <;> rw [tensorSectionsIso_hom, ← Category.assoc,
    IsColimit.comp_coconePointUniqueUpToIso_hom, colimit.cocone_ι, Iso.comp_inv_eq]
  · rw [colimit_ι_app_comp_presheafPushoutObjIso_hom]
  · change pushout.inr (B.hom.hom.app U) (φ.hom.app U) = _
    simp [presheafPushoutObjIso]

/-- On the pure tensor `1 ⊗ b` the objectwise identification is the first leg of the colimit
cocone: this is `colimit_ι_app_comp_presheafPushoutObjIso_hom` read through
`CommRingCat.pushoutCocone`, whose flipped first inclusion is `b ↦ 1 ⊗ b`. -/
public theorem tensorSectionsIso_hom_one_tmul (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ)
    (b : B.right.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    (tensorSectionsIso φ B U).hom.hom ((1 : R'.obj.obj U) ⊗ₜ[R.obj.obj U] b) =
      ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
        WalkingSpan.left).app U).hom b :=
  ConcreteCategory.congr_hom (pushoutCocone_flip_ι_comp_tensorSectionsIso_hom φ B U).1 b

/-- On the pure tensor `a ⊗ 1` the objectwise identification is the second leg of the colimit
cocone. -/
public theorem tensorSectionsIso_hom_tmul_one (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ)
    (a : R'.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    (tensorSectionsIso φ B U).hom.hom (a ⊗ₜ[R.obj.obj U] (1 : B.right.obj.obj U)) =
      ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
        WalkingSpan.right).app U).hom a :=
  ConcreteCategory.congr_hom (pushoutCocone_flip_ι_comp_tensorSectionsIso_hom φ B U).2 a

/-- **The objectwise identification on a pure tensor.**  It carries `a ⊗ b` to the product of
the images of `a` and `b` under the two legs of the colimit cocone, because it is a ring
homomorphism and `a ⊗ b = (a ⊗ 1)(1 ⊗ b)`. -/
public theorem tensorSectionsIso_hom_tmul (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ)
    (a : R'.obj.obj U) (b : B.right.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    (tensorSectionsIso φ B U).hom.hom (a ⊗ₜ[R.obj.obj U] b) =
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
    tensorSectionsIso_hom_tmul_one, tensorSectionsIso_hom_one_tmul]

/-- Two additive maps out of a tensor product that agree on pure tensors agree everywhere. -/
private theorem tensorProduct_apply_eq_of_tmul {S M N P : Type*} [CommSemiring S]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [Module S M] [Module S N]
    (F G : M ⊗[S] N →+ P) (h : ∀ a b, F (a ⊗ₜ b) = G (a ⊗ₜ b)) (x : M ⊗[S] N) : F x = G x := by
  induction x using TensorProduct.inductionOn with
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a b => exact h a b

/-- **The objectwise identification is natural in `U`.**  This is the one statement the
invertibility of `extendScalarsComparison` was missing.  On a pure tensor both sides are the
product of the images of `a` and `b` under the two legs of the colimit cocone over the smaller
object, by multiplicativity of the restriction map of the colimit presheaf together with the
naturality of the two legs; the general case follows because every map in sight is additive. -/
public theorem tensorSectionsIso_hom_naturality (φ : R ⟶ R') (B : Under R) {U V : Cᵒᵖ}
    (f : U ⟶ V) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    ∀ x : R'.obj.obj U ⊗[R.obj.obj U] B.right.obj.obj U,
    ((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom
        ((tensorSectionsIso φ B U).hom.hom x) =
      (tensorSectionsIso φ B V).hom.hom
        ((cofMap φ.hom (underlyingModule B).val f).hom x) := by
  let := (φ.hom.app U).hom.toAlgebra
  let := (φ.hom.app V).hom.toAlgebra
  let := (B.hom.hom.app U).hom.toAlgebra
  let := (B.hom.hom.app V).hom.toAlgebra
  refine tensorProduct_apply_eq_of_tmul
    (((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom.toAddMonoidHom.comp
      (tensorSectionsIso φ B U).hom.hom.toAddMonoidHom)
    ((tensorSectionsIso φ B V).hom.hom.toAddMonoidHom.comp
      (cofMap φ.hom (underlyingModule B).val f).hom.toAddMonoidHom) fun a b => ?_
  change ((colimit (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})).map f).hom
      ((tensorSectionsIso φ B U).hom.hom (a ⊗ₜ[R.obj.obj U] b)) =
    (tensorSectionsIso φ B V).hom.hom
      ((cofMap φ.hom (underlyingModule B).val f).hom (a ⊗ₜ[R.obj.obj U] b))
  rw [tensorSectionsIso_hom_tmul, map_mul]
  refine Eq.trans (congrArg₂ _
    (ConcreteCategory.congr_hom ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
      WalkingSpan.right).naturality f) a).symm
    (ConcreteCategory.congr_hom ((colimit.ι (span B.hom φ ⋙ sheafToPresheaf J CommRingCat.{u})
      WalkingSpan.left).naturality f) b).symm)
    ((tensorSectionsIso_hom_tmul φ B V _ _).symm.trans
      (congrArg _ (cofMap_tmul φ.hom (underlyingModule B).val f a b).symm))

end TensorSections

/-! ### The comparison with extension of scalars -/

section Comparison

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.Sheaves.ModuleAdjunction Stacks.PresheafOfModules.ChangeOfRings

/-- The adjoint transpose read as a composite: the unit of the change-of-rings adjunction
followed by the comparison is the inclusion of the first factor of the pushout.  This is
`homEquiv_extendScalarsComparison` with `Adjunction.homEquiv_unit` unfolded, and it is the form
in which the comparison can be evaluated on sections. -/
public theorem unit_comp_restrictScalars_map_extendScalarsComparison (φ : R ⟶ R')
    (B : Under R) :
    ((extendRestrictScalarsAdjunction (ringSheafMap φ)).unit.app (underlyingModule B)) ≫
        (_root_.SheafOfModules.restrictScalars.{u} (ringSheafMap φ)).map
          (extendScalarsComparison φ B) =
      pushoutInlModuleMap φ B := by
  have h := homEquiv_extendScalarsComparison φ B
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- **The comparison on the image of a pure tensor `1 ⊗ b`.**  The unit of the change-of-rings
adjunction carries a section `b` of `B` to the pure tensor `1 ⊗ b` of the extension of scalars
(up to the sheafification unit, cf.
`Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction_unit_app_val_app_apply`),
and the comparison carries that to the image of `b` under the inclusion `pushout.inl` of the
first factor.  This is the computation that pins the objectwise identification of the two sides
to *this* morphism rather than to some other isomorphism between them. -/
public theorem extendScalarsComparison_app_unit (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ)
    (b : B.right.obj.obj U) :
    ((extendScalarsComparison φ B).val.app U).hom
        ((((extendRestrictScalarsAdjunction (ringSheafMap φ)).unit.app
          (underlyingModule B)).val.app U).hom b) =
      ((pushout.inl B.hom φ).hom.app U).hom b :=
  congrArg
    (fun t : underlyingModule B ⟶
        (_root_.SheafOfModules.restrictScalars.{u} (ringSheafMap φ)).obj
          (underlyingModule ((Under.pushout φ).obj B)) => ((t.val.app U).hom b))
    (unit_comp_restrictScalars_map_extendScalarsComparison φ B)

/-! #### Invertibility of the comparison -/

/-- **The comparison, at the level of presheaves of modules.**  The adjoint transpose of
`pushoutInlModuleMap` under the *presheaf*-level change-of-rings adjunction of [Stacks, Tag
03CU]: a morphism from the objectwise tensor product `U ↦ R'(U) ⊗_{R(U)} B(U)` to the presheaf
of modules underlying `B ⊗_R R'`.  On sections it is `a ⊗ b ↦ inr(a) · inl(b)`
(`changeOfRingsComparison_app_tmul`), and it is locally bijective
(`isLocallyInjective_changeOfRingsComparison`, `isLocallySurjective_changeOfRingsComparison`),
which is what makes `extendScalarsComparison` invertible. -/
public noncomputable def changeOfRingsComparison (φ : R ⟶ R') (B : Under R) :
    (changeOfRings φ.hom).obj (underlyingModule B).val ⟶
      (underlyingModule ((Under.pushout φ).obj B)).val :=
  counitHom φ.hom ((pushoutInlModuleMap φ B).val)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- On the pure tensor `a ⊗ b` the presheaf-level comparison is the product of the images of
`a` and `b` under the two inclusions of the pushout: the counit of the change-of-rings
adjunction is `a ⊗ x ↦ a • x`, and the action of `a` on the module underlying the pushout is
multiplication by `inr(a)`. -/
public theorem changeOfRingsComparison_app_tmul (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ)
    (a : R'.obj.obj U) (b : B.right.obj.obj U) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    ((changeOfRingsComparison φ B).app U).hom (a ⊗ₜ[R.obj.obj U] b) =
      ((pushout.inr B.hom φ).hom.app U).hom a * ((pushout.inl B.hom φ).hom.app U).hom b :=
  counitApp_tmul φ.hom ((pushoutInlModuleMap φ B).val) U a b

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The presheaf-level comparison factors through the colimit of the underlying
presheaves.**  It is the objectwise identification `tensorSectionsIso` followed by
`CategoryTheory.Sheaf.colimitToColimitObj`, the comparison of the colimit of the underlying
presheaves with the underlying presheaf of the colimit.  On a pure tensor both sides are
`inr(a) · inl(b)`, because `colimitToColimitObj` carries each leg of the presheaf colimit
cocone to the corresponding inclusion of the pushout sheaf. -/
public theorem changeOfRingsComparison_app (φ : R ⟶ R') (B : Under R) (U : Cᵒᵖ) :
    letI := (φ.hom.app U).hom.toAlgebra
    letI := (B.hom.hom.app U).hom.toAlgebra
    ∀ x : R'.obj.obj U ⊗[R.obj.obj U] B.right.obj.obj U,
    ((changeOfRingsComparison φ B).app U).hom x =
      ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U).hom
        ((tensorSectionsIso φ B U).hom.hom x) := by
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
  induction x using TensorProduct.inductionOn with
  | add u v hu hv =>
    refine (map_add (ModuleCat.Hom.hom ((changeOfRingsComparison φ B).app U)) u v).trans ?_
    refine (congrArg (fun z => z + ((changeOfRingsComparison φ B).app U).hom v) hu).trans
      ((congrArg (fun z => ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U).hom
        ((tensorSectionsIso φ B U).hom.hom u) + z) hv).trans ?_)
    exact ((congrArg (CommRingCat.Hom.hom
      ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U))
      (map_add (CommRingCat.Hom.hom (tensorSectionsIso φ B U).hom) u v)).trans
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
    exact (changeOfRingsComparison_app_tmul φ B U a b).trans (hmul.trans
      ((map_mul (CommRingCat.Hom.hom ((Sheaf.colimitToColimitObj J (span B.hom φ)).app U))
          _ _).symm.trans
        (congrArg _ (tensorSectionsIso_hom_tmul φ B U a b).symm)))

/-- **The presheaf-level comparison is locally injective.**  Two sections with the same image
have the same image under `CategoryTheory.Sheaf.colimitToColimitObj` composed with the
objectwise isomorphism, so they agree locally there; the objectwise isomorphism is natural and
injective, so they agree locally to begin with. -/
public instance isLocallyInjective_changeOfRingsComparison (φ : R ⟶ R') (B : Under R) :
    PresheafOfModules.IsLocallyInjective J (changeOfRingsComparison φ B) where
  equalizerSieve_mem {X} x y h := by
    have h' : ((Sheaf.colimitToColimitObj J (span B.hom φ)).app X).hom
          ((tensorSectionsIso φ B X).hom.hom x) =
        ((Sheaf.colimitToColimitObj J (span B.hom φ)).app X).hom
          ((tensorSectionsIso φ B X).hom.hom y) :=
      (changeOfRingsComparison_app φ B X x).symm.trans
        (h.trans (changeOfRingsComparison_app φ B X y))
    refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J
      (Sheaf.colimitToColimitObj J (span B.hom φ)) _ _ h')
    intro Y p hp
    exact (ConcreteCategory.bijective_of_isIso
        (tensorSectionsIso φ B (op Y)).hom).injective
      ((tensorSectionsIso_hom_naturality φ B p.op x).symm.trans
        (hp.trans (tensorSectionsIso_hom_naturality φ B p.op y)))

/-- **The presheaf-level comparison is locally surjective.**  A section of the target is
locally in the image of `CategoryTheory.Sheaf.colimitToColimitObj`, and the objectwise
isomorphism lifts each such preimage to the tensor product. -/
public instance isLocallySurjective_changeOfRingsComparison (φ : R ⟶ R') (B : Under R) :
    PresheafOfModules.IsLocallySurjective J (changeOfRingsComparison φ B) where
  imageSieve_mem {U} s := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J
      (Sheaf.colimitToColimitObj J (span B.hom φ)) s)
    rintro Y p ⟨t, ht⟩
    refine ⟨(tensorSectionsIso φ B (op Y)).inv.hom t, ?_⟩
    have e : (tensorSectionsIso φ B (op Y)).hom.hom
          ((tensorSectionsIso φ B (op Y)).inv.hom t) = t :=
      DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
        (tensorSectionsIso φ B (op Y)).inv_hom_id) t
    exact (changeOfRingsComparison_app φ B (op Y) _).trans ((congrArg _ e).trans ht)

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The adjoint transpose of the presheaf-level comparison is the inclusion of the first factor
of the pushout, read on underlying presheaves of modules.  This is the presheaf-level analogue
of `homEquiv_extendScalarsComparison`, and it is what identifies the two comparisons. -/
public theorem homEquiv_changeOfRingsComparison (φ : R ⟶ R') (B : Under R) :
    ((changeOfRingsAdjunction φ.hom).homEquiv _ _) (changeOfRingsComparison φ B) =
      (pushoutInlModuleMap φ B).val := by
  simp only [changeOfRingsAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  exact (homEquivCore φ.hom _ _).apply_symm_apply _

/-- **The canonical comparison is invertible.**  For every sheaf of `R'`-modules `Z`,
precomposition with the comparison is a bijection on morphisms into `Z`: the change-of-rings
adjunction turns it into precomposition with the presheaf-level comparison
`changeOfRingsComparison`, by `homEquiv_changeOfRingsComparison` together with
`CategoryTheory.Adjunction.homEquiv_naturality_right` on both sides, and that is a bijection
into a sheaf because the presheaf-level comparison is locally bijective
(`PresheafOfModules.homEquivOfIsLocallyBijective`).  So
`CategoryTheory.isIso_of_coyoneda_map_bijective` applies.

This is the invertibility that [Stacks, Tag 01SA] and the degree-zero case of [Stacks, Tag
02KH] ask for. -/
public theorem isIso_extendScalarsComparison (φ : R ⟶ R') (B : Under R) :
    IsIso (extendScalarsComparison φ B) := by
  refine isIso_of_coyoneda_map_bijective _ fun Z => ?_
  have key : ∀ y : underlyingModule ((Under.pushout φ).obj B) ⟶ Z,
      extendScalarsComparison φ B ≫ y =
        ((extendRestrictScalarsAdjunction (ringSheafMap φ)).homEquiv
            (underlyingModule B) Z).symm
          ((_root_.SheafOfModules.fullyFaithfulForget (ringSheaf R)).homEquiv.symm
            (((changeOfRingsAdjunction φ.hom).homEquiv _ _)
              ((PresheafOfModules.homEquivOfIsLocallyBijective (changeOfRingsComparison φ B)
                Z.isSheaf)
                ((_root_.SheafOfModules.fullyFaithfulForget (ringSheaf R')).homEquiv y)))) := by
    intro y
    refine ((extendRestrictScalarsAdjunction (ringSheafMap φ)).homEquiv
      (underlyingModule B) Z).injective ?_
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
      homEquiv_extendScalarsComparison]
    refine _root_.SheafOfModules.hom_ext ?_
    change (pushoutInlModuleMap φ B).val ≫ (restrictScalars φ.hom).map y.val =
      ((changeOfRingsAdjunction φ.hom).homEquiv (underlyingModule B).val Z.val)
        (changeOfRingsComparison φ B ≫ y.val)
    exact (congrArg (fun z => z ≫ (restrictScalars φ.hom).map y.val)
        (homEquiv_changeOfRingsComparison φ B).symm).trans
      ((changeOfRingsAdjunction φ.hom).homEquiv_naturality_right
        (changeOfRingsComparison φ B) y.val).symm
  rw [show (fun (y : underlyingModule ((Under.pushout φ).obj B) ⟶ Z) =>
      extendScalarsComparison φ B ≫ y) = _ from funext key]
  exact ((extendRestrictScalarsAdjunction (ringSheafMap φ)).homEquiv
      (underlyingModule B) Z).symm.bijective.comp
    (((_root_.SheafOfModules.fullyFaithfulForget (ringSheaf R)).homEquiv.symm.bijective).comp
      ((((changeOfRingsAdjunction φ.hom).homEquiv _ _).bijective).comp
        (((PresheafOfModules.homEquivOfIsLocallyBijective (changeOfRingsComparison φ B)
            Z.isSheaf).bijective).comp
          ((_root_.SheafOfModules.fullyFaithfulForget (ringSheaf R')).homEquiv.bijective))))

/-- **The canonical comparison, as an isomorphism.**  `isIso_extendScalarsComparison` discharges
the invertibility that `underlyingModulePushoutIso` takes as a hypothesis, so the extension of
scalars along `φ` of the module underlying `B` *is* the module underlying `B ⊗_R R'`, with no
hypothesis at all; `(extendScalarsComparisonIso φ B).symm` is that identification in the
direction `underlyingModulePushoutIso` states it. -/
public noncomputable def extendScalarsComparisonIso (φ : R ⟶ R') (B : Under R) :
    (extendScalars (ringSheafMap φ)).obj (underlyingModule B) ≅
      underlyingModule ((Under.pushout φ).obj B) :=
  (underlyingModulePushoutIso φ B (isIso_extendScalarsComparison φ B)).symm

end Comparison

end Stacks.SheafOfModules.AlgebraPushout

end
