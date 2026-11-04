module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Basic

/-!
# The module underlying a pushout of sheaves of commutative rings

Let `(C, J)` be a site, let `φ : R ⟶ R'` be a morphism of sheaves of commutative rings on it
and let `B` be a sheaf of commutative `R`-algebras, i.e. an object of `Under R`.  Pushing `B`
out along `φ` produces the sheaf of commutative `R'`-algebras `B ⊗_R R'`, and the mathematics
that several developments in this repository are waiting on is the identification of the
`R'`-module *underlying* that pushout with the extension of scalars along `φ` of the
`R`-module underlying `B`.

This file constructs the canonical comparison morphism

`(R' ⊗_R -) (underlying module of B) ⟶ underlying module of (B ⊗_R R')`,

in the only direction the change-of-rings adjunction supplies it, and reduces the
identification to invertibility of that one morphism.  It also records the semilinear
morphism of underlying modules attached to any commuting square of algebra sheaves over a
morphism of base ring sheaves, of which the comparison's adjoint transpose is the instance at
`pushout.inl`.

## Main definitions

* `Stacks.SheafOfModules.AlgebraPushout.ringSheaf` and `ringSheafMap`: a sheaf of commutative
  rings, respectively a morphism of such, read as a sheaf of (not necessarily commutative)
  rings.
* `Stacks.SheafOfModules.AlgebraPushout.underlyingModule`: the `R`-module underlying a sheaf
  of commutative `R`-algebras, for an arbitrary sheaf of commutative rings `R` on an
  arbitrary site.  At `R` the structure sheaf of a scheme this is literally
  `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule`
  (`underlyingModule_eq_algebraSheaf_underlyingModule`).
* `Stacks.SheafOfModules.AlgebraPushout.moduleMapOver`: the morphism of underlying modules,
  semilinear over `φ`, attached to a morphism `ψ : B.right ⟶ B'.right` of the underlying
  sheaves of rings which commutes with the two structure morphisms over `φ`.
* `Stacks.SheafOfModules.AlgebraPushout.pushoutInlModuleMap`: that morphism at
  `ψ = pushout.inl`, i.e. the `R`-module morphism from the module underlying `B` to the
  module underlying `B ⊗_R R'`, read over `R`.
* `Stacks.SheafOfModules.AlgebraPushout.extendScalarsComparison`: the adjoint transpose of
  the preceding morphism, which is the canonical comparison
  `R' ⊗_R B ⟶ B ⊗_R R'` of underlying modules.

## Main results

* `Stacks.SheafOfModules.AlgebraPushout.homEquiv_extendScalarsComparison` and
  `extendScalarsComparison_unique`: the comparison is the unique morphism whose adjoint
  transpose is `pushoutInlModuleMap`.
* `Stacks.SheafOfModules.AlgebraPushout.underlyingModulePushoutIso`: granting that the
  comparison is invertible, the module underlying `B ⊗_R R'` is the extension of scalars
  along `φ` of the module underlying `B`.
* `Stacks.SheafOfModules.AlgebraPushout.algebraPullbackComparison`: the comparison at the
  pushout half of `Stacks.AffineAlgebraEquivalence.algebraPullback`, which is the shape in
  which [Stacks, Tag 01SA] and [Stacks, Tag 02KH] need it.

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

**Invertibility, and what it would take.**  Invertibility of `extendScalarsComparison` is not
proved here, and it is not formal: both sides are sheafifications of presheaves which agree
objectwise, and identifying them needs the three steps below, in this order.

1. The pushout in `CategoryTheory.Sheaf J CommRingCat` is the sheafification of the pushout of
   the underlying presheaves of commutative rings
   (`CategoryTheory.Sheaf.sheafifyCocone` and `CategoryTheory.Sheaf.isColimitSheafifyCocone`),
   and the pushout of presheaves is computed objectwise, where it is
   `CategoryTheory.Limits.PushoutCocone`-presented as a tensor product by
   `CommRingCat.pushoutCoconeIsColimit`.
2. Extension of scalars is the sheafification of the objectwise tensor product: this is
   `Stacks.Sheaves.ModuleAdjunction.extendScalarsIso` together with
   `Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoTensor`, which identifies the abstract
   left adjoint with `Stacks.Sheaves.RingedToposModules.extendScalars`, itself built from the
   objectwise `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` of [Stacks, Tag 03CU].
3. The objectwise comparison `B(U) ⊗_{R(U)} R'(U) ≅ R'(U) ⊗_{R(U)} B(U)` of
   `Algebra.TensorProduct.comm` then has to be transported across the two sheafifications.
   The route to take is *local bijectivity*, not a sheafification-commutation isomorphism:
   invertibility of a morphism of sheaves of modules is reflected by the underlying morphism
   of sheaves of abelian groups (`SheafOfModules.forget` and
   `PresheafOfModules.toPresheaf` both reflect isomorphisms), and there invertibility is
   local injectivity together with local surjectivity
   (`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`, whose two hypotheses
   `(forget AddCommGrpCat).ReflectsIsomorphisms` and
   `J.HasSheafCompose (forget AddCommGrpCat)` are both available at this pin), which is a
   property of the underlying map of type-valued presheaves and so is insensitive to which
   concrete category the sheafification was taken in.  The alternative route through
   `CategoryTheory.sheafifyComposeIso` is a dead end as the pin stands:
   `J.HasSheafCompose (forget₂ CommRingCat RingCat)` is found at once, but
   `J.PreservesSheafification (forget₂ CommRingCat RingCat)` does not resolve — it times out
   in `whnf` at ten times the default heartbeat budget, and there is no
   `HasForget₂ CommRingCat AddCommGrpCat` instance at all, so the one-step form of that
   isomorphism is not even statable.
   Either way the last step needs the computation of `homEquiv_extendScalarsComparison` on
   the image of a pure tensor, which is what pins the objectwise isomorphism to *this*
   morphism rather than to some other.

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

universe u

namespace Stacks.SheafOfModules.AlgebraPushout

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}

/-- The sheaf of (not necessarily commutative) rings underlying a sheaf of commutative
rings. -/
public noncomputable abbrev ringSheaf (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R

variable {R R' : Sheaf J CommRingCat.{u}}

/-- A morphism of sheaves of commutative rings, read as a morphism of the underlying sheaves
of rings. -/
public noncomputable def ringSheafMap (φ : R ⟶ R') : ringSheaf R ⟶ ringSheaf R' :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).map φ

/-- The `R`-module underlying a sheaf of commutative `R`-algebras: its underlying sheaf of
rings, viewed as a module over itself and then restricted along the structure morphism. -/
public noncomputable def underlyingModule (B : Under R) :
    _root_.SheafOfModules.{u} (ringSheaf R) :=
  (_root_.SheafOfModules.restrictScalars.{u} (ringSheafMap B.hom)).obj
    (_root_.SheafOfModules.unit (ringSheaf B.right))

/-- On a scheme this is the underlying module of an algebra sheaf as already defined in
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule`; the two are the same term. -/
public theorem underlyingModule_eq_algebraSheaf_underlyingModule {X : Scheme.{u}}
    (A : Stacks.RelativeSpec.AlgebraSheaf X) :
    underlyingModule A = Stacks.RelativeSpec.AlgebraSheaf.underlyingModule A :=
  rfl

/-! ### Semilinear morphisms of underlying modules -/

/-- The morphism of abelian presheaves underlying a morphism `ψ` of the sheaves of rings
underlying two algebra sheaves over different base ring sheaves.  Restriction of scalars does
not change the underlying presheaf of abelian groups, so this is literally the map on sections
of `ψ`. -/
public noncomputable def presheafMapOver (φ : R ⟶ R') {B : Under R} {B' : Under R'}
    (ψ : B.right ⟶ B'.right) :
    (underlyingModule B).val.presheaf ⟶
      ((_root_.SheafOfModules.restrictScalars.{u} (ringSheafMap φ)).obj
        (underlyingModule B')).val.presheaf where
  app U := AddCommGrpCat.ofHom (ψ.hom.app U).hom.toAddMonoidHom
  naturality _ _ f :=
    congrArg (fun t ↦ AddCommGrpCat.ofHom (RingHom.toAddMonoidHom (CommRingCat.Hom.hom t)))
      (ψ.hom.naturality f)

/-- A morphism of algebra sheaves over a morphism `φ` of base ring sheaves carries the image
of a section of `R` to the image of its image under `φ`: this is commutativity of the square
of structure morphisms, read on sections. -/
public theorem apply_structureMapOver (φ : R ⟶ R') {B : Under R} {B' : Under R'}
    (ψ : B.right ⟶ B'.right) (w : B.hom ≫ ψ = φ ≫ B'.hom) (U : Cᵒᵖ) (r : R.obj.obj U) :
    (ψ.hom.app U).hom ((B.hom.hom.app U).hom r) =
      (B'.hom.hom.app U).hom ((φ.hom.app U).hom r) := by
  have h : ((B.hom ≫ ψ).hom.app U).hom r = ((φ ≫ B'.hom).hom.app U).hom r := by rw [w]
  exact h

/-- **The morphism of underlying modules, semilinear over `φ`.**  Let `ψ : B.right ⟶ B'.right`
be a morphism of the sheaves of rings underlying a sheaf of `R`-algebras `B` and a sheaf of
`R'`-algebras `B'`, commuting with the two structure morphisms over `φ : R ⟶ R'`.  Then `ψ` is
a morphism from the `R`-module underlying `B` to the `R`-module obtained from the `R'`-module
underlying `B'` by restriction of scalars along `φ`:  on sections it is the map on sections of
`ψ`, and its `R`-linearity is the commuting square, because the action of a section `r` of `R`
is multiplication by its image under the structure morphism. -/
public noncomputable def moduleMapOver (φ : R ⟶ R') {B : Under R} {B' : Under R'}
    (ψ : B.right ⟶ B'.right) (w : B.hom ≫ ψ = φ ≫ B'.hom) :
    underlyingModule B ⟶
      (_root_.SheafOfModules.restrictScalars.{u} (ringSheafMap φ)).obj (underlyingModule B') :=
  ⟨PresheafOfModules.homMk (presheafMapOver φ ψ) (by
    intro U r y
    have h : ∀ y' : B.right.obj.obj U,
        (ψ.hom.app U).hom ((B.hom.hom.app U).hom r * y')
          = (B'.hom.hom.app U).hom ((φ.hom.app U).hom r) * (ψ.hom.app U).hom y' := fun y' ↦ by
      rw [map_mul, apply_structureMapOver φ ψ w U r]
    exact h y)⟩

/-- On sections, the semilinear morphism of underlying modules is the map on sections of the
given morphism of sheaves of rings. -/
public theorem moduleMapOver_app (φ : R ⟶ R') {B : Under R} {B' : Under R'}
    (ψ : B.right ⟶ B'.right) (w : B.hom ≫ ψ = φ ≫ B'.hom) (U : Cᵒᵖ)
    (y : B.right.obj.obj U) :
    ((moduleMapOver φ ψ w).val.app U).hom y = (ψ.hom.app U).hom y :=
  rfl

/-! ### The comparison with extension of scalars -/

section Comparison

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

open Stacks.Sheaves.ModuleAdjunction

/-- The `R`-module morphism from the module underlying `B` to the module underlying the
pushout `B ⊗_R R'`, read over `R` by restriction of scalars along `φ`.  It is the inclusion
`pushout.inl` of the first factor, whose compatibility with the structure morphisms is the
pushout square itself. -/
public noncomputable def pushoutInlModuleMap (φ : R ⟶ R') (B : Under R) :
    underlyingModule B ⟶ (_root_.SheafOfModules.restrictScalars.{u} (ringSheafMap φ)).obj
      (underlyingModule ((Under.pushout φ).obj B)) :=
  moduleMapOver φ (pushout.inl B.hom φ) pushout.condition

/-- **The canonical comparison of the extension of scalars with the module underlying the
pushout.**  For a morphism `φ : R ⟶ R'` of sheaves of commutative rings on a site and a sheaf
of commutative `R`-algebras `B`, this is the morphism

`R' ⊗_R (module underlying B) ⟶ module underlying (B ⊗_R R')`

adjoint to the inclusion of the first factor of the pushout.  Stacks Tag 01SA and the
degree-zero case of Stacks Tag 02KH ask that it be an isomorphism. -/
public noncomputable def extendScalarsComparison (φ : R ⟶ R') (B : Under R) :
    (extendScalars (ringSheafMap φ)).obj (underlyingModule B) ⟶
      underlyingModule ((Under.pushout φ).obj B) :=
  ((extendRestrictScalarsAdjunction (ringSheafMap φ)).homEquiv _ _).symm
    (pushoutInlModuleMap φ B)

/-- The adjoint transpose of the comparison is the inclusion of the first factor of the
pushout. -/
public theorem homEquiv_extendScalarsComparison (φ : R ⟶ R') (B : Under R) :
    ((extendRestrictScalarsAdjunction (ringSheafMap φ)).homEquiv _ _)
        (extendScalarsComparison φ B) =
      pushoutInlModuleMap φ B :=
  Equiv.apply_symm_apply _ _

/-- The comparison is the unique morphism whose adjoint transpose is the inclusion of the
first factor of the pushout. -/
public theorem extendScalarsComparison_unique (φ : R ⟶ R') (B : Under R)
    (c : (extendScalars (ringSheafMap φ)).obj (underlyingModule B) ⟶
      underlyingModule ((Under.pushout φ).obj B))
    (h : ((extendRestrictScalarsAdjunction (ringSheafMap φ)).homEquiv _ _) c =
      pushoutInlModuleMap φ B) :
    c = extendScalarsComparison φ B :=
  ((extendRestrictScalarsAdjunction (ringSheafMap φ)).homEquiv _ _).injective
    (h.trans (homEquiv_extendScalarsComparison φ B).symm)

/-- **The module underlying a pushout of algebra sheaves is an extension of scalars, granting
that the canonical comparison is invertible.**  This is the identification that
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso` and
the degree-zero case of [Stacks, Tag 02KH] consume. -/
public noncomputable def underlyingModulePushoutIso (φ : R ⟶ R') (B : Under R)
    (h : IsIso (extendScalarsComparison φ B)) :
    underlyingModule ((Under.pushout φ).obj B) ≅
      (extendScalars (ringSheafMap φ)).obj (underlyingModule B) :=
  (@asIso _ _ _ _ (extendScalarsComparison φ B) h).symm

end Comparison

/-! ### The instance the base-change square of a scheme morphism needs -/

section Scheme

variable {S T : Scheme.{u}} (g : T ⟶ S)

open Stacks.Sheaves.ModuleAdjunction Stacks.AffineAlgebraEquivalence

/-- The comparison at the pushout half of `Stacks.AffineAlgebraEquivalence.algebraPullback`:
for `A` a sheaf of commutative `𝒪_S`-algebras, the canonical morphism from the extension of
scalars along `g⁻¹𝒪_S ⟶ 𝒪_T` of the module underlying `g⁻¹A` to the module underlying
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`.  This is the shape in which the `algebraPullback_isQuasicoherent`
clause of [Stacks, Tag 01SA] needs the identification; the remaining input, which this file
does not address, is the identification of the module underlying `g⁻¹A` with the inverse image
of the module underlying `A`. -/
public noncomputable def algebraPullbackComparison (A : Stacks.RelativeSpec.AlgebraSheaf S) :
    (extendScalars (ringSheafMap (inverseImageStructureMap g))).obj
        (underlyingModule ((Under.post (TopCat.Sheaf.pullback CommRingCat g.base)).obj A)) ⟶
      underlyingModule ((algebraPullback g).obj A) :=
  extendScalarsComparison (inverseImageStructureMap g)
    ((Under.post (TopCat.Sheaf.pullback CommRingCat g.base)).obj A)

end Scheme

end Stacks.SheafOfModules.AlgebraPushout

end
