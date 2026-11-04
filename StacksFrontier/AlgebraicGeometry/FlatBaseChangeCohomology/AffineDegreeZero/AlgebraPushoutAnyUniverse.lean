module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.AlgebraicGeometry.AlgebraPullbackQcoh.Basic

/-!
# The module underlying a pushout of sheaves of commutative rings, at any site and universe

Let `(C, J)` be a site, let `φ : R ⟶ R'` be a morphism of sheaves of commutative rings on it
and let `B` be a sheaf of commutative `R`-algebras, i.e. an object of `Under R`.  Pushing `B`
out along `φ` produces the sheaf of commutative `R'`-algebras `B ⊗_R R'`, and the question at
issue is the identification of the `R'`-module *underlying* that pushout with the extension of
scalars along `φ` of the `R`-module underlying `B`.

This file constructs the canonical comparison morphism

`(R' ⊗_R -) (underlying module of B) ⟶ underlying module of (B ⊗_R R')`,

in the only direction the change-of-rings adjunction supplies it, and reduces the
identification to invertibility of that one morphism.  It also records the semilinear
morphism of underlying modules attached to any commuting square of algebra sheaves over a
morphism of base ring sheaves, of which the comparison's adjoint transpose is the instance at
`pushout.inl`.

## Main definitions

* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.ringSheafMap`: a morphism of sheaves of
  commutative rings, respectively a morphism of such, read as a sheaf of (not necessarily
  commutative) rings.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.underlyingModule`: the `R`-module underlying
  a sheaf of commutative `R`-algebras, for an arbitrary sheaf of commutative rings `R` on an
  arbitrary site.  At `R` the structure sheaf of a scheme this is literally
  `Stacks.RelativeSpec.AlgebraSheaf.underlyingModule`
  (`Stacks.SheafOfModules.AlgebraPushout.underlyingModule_eq_algebraSheaf_underlyingModule`,
  the same term here).
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.moduleMapOver`: the morphism of underlying
  modules, semilinear over `φ`, attached to a morphism `ψ : B.right ⟶ B'.right` of the
  underlying sheaves of rings which commutes with the two structure morphisms over `φ`.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.pushoutInlModuleMap`: that morphism at
  `ψ = pushout.inl`, i.e. the `R`-module morphism from the module underlying `B` to the
  module underlying `B ⊗_R R'`, read over `R`.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.extendScalarsComparison`: the adjoint
  transpose of the preceding morphism, which is the canonical comparison
  `R' ⊗_R B ⟶ B ⊗_R R'` of underlying modules.

## Main results

* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.homEquiv_extendScalarsComparison` and
  `extendScalarsComparison_unique`: the comparison is the unique morphism whose adjoint
  transpose is `pushoutInlModuleMap`.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.underlyingModulePushoutIso`: granting that the
  comparison is invertible, the module underlying `B ⊗_R R'` is the extension of scalars
  along `φ` of the module underlying `B`.
* `Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.algebraPullbackComparison`: the comparison at
  the pushout half of `Stacks.AffineAlgebraEquivalence.algebraPullback`, which is the shape in
  which [Stacks, Tag 01SA] and [Stacks, Tag 02KH] need it.

## Implementation notes

**Why only a morphism.**  Extension of scalars for sheaves of modules
(`Stacks.FlatChangeOfRings.extendScalars`) is used here through its universal property, as
the left adjoint of restriction of scalars, so a morphism *out of* it is the same thing as a
morphism into a restriction of scalars.  The map `pushout.inl : B.right ⟶ B.right ⊗_R R'` of
sheaves of rings is such a morphism, once its source and target are read as modules over `R`;
transposing it gives the comparison.  Nothing in the adjunction produces a morphism in the
other direction, because that would need a description of the sections of an abstract left
adjoint.  The same asymmetry, for the tensor product rather than for a pushout of algebras,
is recorded in the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean`.

**Invertibility.**  Invertibility of `extendScalarsComparison`, for an arbitrary site, is
`Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.isIso_extendScalarsComparison` of
`AlgebraPushoutAnyUniverseInvertible.lean`.  It is not formal: both sides are sheafifications of
presheaves which agree objectwise, and identifying them needs the three steps below, in this
order.

1. The pushout in `CategoryTheory.Sheaf J CommRingCat` is the sheafification of the pushout of
   the underlying presheaves of commutative rings
   (`CategoryTheory.Sheaf.sheafifyCocone` and `CategoryTheory.Sheaf.isColimitSheafifyCocone`),
   and the pushout of presheaves is computed objectwise, where it is
   `CategoryTheory.Limits.PushoutCocone`-presented as a tensor product by
   `CommRingCat.pushoutCoconeIsColimit`.
2. Extension of scalars is the sheafification of the objectwise tensor product, and here
   that is true *by definition* rather than by a theorem:
   `Stacks.FlatChangeOfRings.extendScalars` is the objectwise
   `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings` of [Stacks, Tag 03CU] followed by
   `Stacks.moduleSheafification`.  The abstract left-adjoint spelling
   `Stacks.Sheaves.ModuleAdjunction.extendScalars`, for which the identification is the
   theorem `Stacks.SheafOfModules.ChangeOfRings.extendScalarsIsoTensor`, is not
   the one transposed against: both it and that theorem are stated at `SmallCategory` with
   every universe collapsed, and so do not reach a site as large as the small étale site of an
   algebraic space.
3. The objectwise comparison `B(U) ⊗_{R(U)} R'(U) ≅ R'(U) ⊗_{R(U)} B(U)` of
   `Algebra.TensorProduct.comm` then has to be transported across the two sheafifications.
   The route is *local bijectivity*, not a sheafification-commutation isomorphism:
   invertibility of a morphism of sheaves of modules is reflected by the underlying morphism
   of sheaves of abelian groups (`SheafOfModules.forget` and
   `PresheafOfModules.toPresheaf` both reflect isomorphisms), and there invertibility is
   local injectivity together with local surjectivity
   (`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`, under its hypotheses
   `(forget AddCommGrpCat).ReflectsIsomorphisms` and
   `J.HasSheafCompose (forget AddCommGrpCat)`), which is a property of the underlying map of
   type-valued presheaves and so is insensitive to which concrete category the sheafification
   was taken in.  The last step needs the computation of
   `homEquiv_extendScalarsComparison` on the image of a pure tensor, which is what pins the
   objectwise isomorphism to *this* morphism rather than to some other.

**Universes, and the pushout hypothesis.**  The site is `C : Type u` with `Category.{v} C`
and the sections live in an independent universe `w`.  In particular the small étale site of
an algebraic space, which is `Category.{u, u + 1}` and is *not* a `SmallCategory`, is covered,
and so everything here applies to `AlgebraicGeometry.Space.algebraPullback`.  What makes that
possible is the choice of adjunction to transpose against:
`Stacks.FlatChangeOfRings.extendScalarsAdjunction` is stated for an arbitrary `Category.{v} C`
*and* at the `sheafCompose` spelling of the underlying sheaf of rings
(`Stacks.commRingSheafToRingSheaf`), which is the spelling used throughout below, so
no bridge between spellings is needed.

At a general site `HasPushout` in `Sheaf J CommRingCat` is not found by instance search, so
`Under.pushout`'s side condition `CategoryTheory.Limits.HasPushoutsAlong φ` is carried as an
instance argument.  It is satisfied wherever the pushout is actually formed, in particular on
the small étale site, where `AlgebraicGeometry.Space.algebraPullback` already takes that
pushout.

**Which spelling of the underlying sheaf of rings.**  Everything below uses
`Stacks.commRingSheafToRingSheaf`, i.e. `CategoryTheory.sheafCompose` applied to
`CategoryTheory.forget₂ CommRingCat RingCat`, which is
the spelling of `AlgebraicGeometry.Scheme.ringCatSheaf` and of
`Stacks.RelativeSpec.AlgebraSheaf.ringSheaf`, and that is why
the identification of the two spellings holds by `rfl`.  There is also the
reducible abbreviation `CategoryTheory.Sheaf.toRingCat`, whose underlying presheaf is
syntactically `R.obj ⋙ forget₂ _ _` rather than a `sheafCompose`; the two are definitionally
equal but not interchangeable for instance search, as the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorComparison.lean` record.  Anything
stated over `toRingCat` has to cross that fork explicitly.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe w v u

namespace Stacks.SheafOfModules.AlgebraPushoutAnyUniverse

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

variable {R R' : Sheaf J CommRingCat.{w}}

/-- A morphism of sheaves of commutative rings, read as a morphism of the underlying sheaves
of rings. -/
public noncomputable abbrev ringSheafMap (φ : R ⟶ R') :
    Stacks.commRingSheafToRingSheaf R ⟶ Stacks.commRingSheafToRingSheaf R' :=
  Stacks.FlatChangeOfRings.ringSheafMap φ

/-- The `R`-module underlying a sheaf of commutative `R`-algebras: its underlying sheaf of
rings, viewed as a module over itself and then restricted along the structure morphism. -/
public noncomputable def underlyingModule (B : Under R) :
    _root_.SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf R) :=
  (_root_.SheafOfModules.restrictScalars.{w} (ringSheafMap B.hom)).obj
    (_root_.SheafOfModules.unit (Stacks.commRingSheafToRingSheaf B.right))

/-! ### Semilinear morphisms of underlying modules -/

/-- The morphism of abelian presheaves underlying a morphism `ψ` of the sheaves of rings
underlying two algebra sheaves over different base ring sheaves.  Restriction of scalars does
not change the underlying presheaf of abelian groups, so this is literally the map on sections
of `ψ`. -/
public noncomputable def presheafMapOver (φ : R ⟶ R') {B : Under R} {B' : Under R'}
    (ψ : B.right ⟶ B'.right) :
    (underlyingModule B).val.presheaf ⟶
      ((_root_.SheafOfModules.restrictScalars.{w} (ringSheafMap φ)).obj
        (underlyingModule B')).val.presheaf where
  app U := AddCommGrpCat.ofHom (ψ.hom.app U).hom.toAddMonoidHom
  naturality _ _ f :=
    congrArg (fun t ↦ AddCommGrpCat.ofHom (RingHom.toAddMonoidHom (CommRingCat.Hom.hom t)))
      (ψ.hom.naturality f)

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
      (_root_.SheafOfModules.restrictScalars.{w} (ringSheafMap φ)).obj (underlyingModule B') :=
  ⟨PresheafOfModules.homMk (presheafMapOver φ ψ) (by
    intro U r y
    have hstruct : (ψ.hom.app U).hom ((B.hom.hom.app U).hom r) =
        (B'.hom.hom.app U).hom ((φ.hom.app U).hom r) := by
      have h : ((B.hom ≫ ψ).hom.app U).hom r = ((φ ≫ B'.hom).hom.app U).hom r := by rw [w]
      exact h
    have h : ∀ y' : B.right.obj.obj U,
        (ψ.hom.app U).hom ((B.hom.hom.app U).hom r * y')
          = (B'.hom.hom.app U).hom ((φ.hom.app U).hom r) * (ψ.hom.app U).hom y' := fun y' ↦ by
      rw [map_mul, hstruct]
    exact h y)⟩

/-! ### The comparison with extension of scalars -/

section Comparison

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

open Stacks.FlatChangeOfRings

variable (φ : R ⟶ R') [HasPushoutsAlong φ]

/-- The `R`-module morphism from the module underlying `B` to the module underlying the
pushout `B ⊗_R R'`, read over `R` by restriction of scalars along `φ`.  It is the inclusion
`pushout.inl` of the first factor, whose compatibility with the structure morphisms is the
pushout square itself. -/
public noncomputable def pushoutInlModuleMap (B : Under R) :
    underlyingModule B ⟶ (_root_.SheafOfModules.restrictScalars.{w} (ringSheafMap φ)).obj
      (underlyingModule ((Under.pushout φ).obj B)) :=
  moduleMapOver φ (pushout.inl B.hom φ) pushout.condition

/-- **The canonical comparison of the extension of scalars with the module underlying the
pushout.**  For a morphism `φ : R ⟶ R'` of sheaves of commutative rings on a site and a sheaf
of commutative `R`-algebras `B`, this is the morphism

`R' ⊗_R (module underlying B) ⟶ module underlying (B ⊗_R R')`

adjoint to the inclusion of the first factor of the pushout.  Stacks Tag 01SA and the
degree-zero case of Stacks Tag 02KH ask that it be an isomorphism; that it is one is
`Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.isIso_extendScalarsComparison`. -/
public noncomputable def extendScalarsComparison (B : Under R) :
    (extendScalars φ).obj (underlyingModule B) ⟶
      underlyingModule ((Under.pushout φ).obj B) :=
  ((extendScalarsAdjunction φ).homEquiv _ _).symm
    (pushoutInlModuleMap φ B)

/-- The adjoint transpose of the comparison is the inclusion of the first factor of the
pushout. -/
public theorem homEquiv_extendScalarsComparison (B : Under R) :
    ((extendScalarsAdjunction φ).homEquiv _ _)
        (extendScalarsComparison φ B) =
      pushoutInlModuleMap φ B :=
  Equiv.apply_symm_apply _ _

/-- The comparison is the unique morphism whose adjoint transpose is the inclusion of the
first factor of the pushout. -/
public theorem extendScalarsComparison_unique (B : Under R)
    (c : (extendScalars φ).obj (underlyingModule B) ⟶
      underlyingModule ((Under.pushout φ).obj B))
    (h : ((extendScalarsAdjunction φ).homEquiv _ _) c =
      pushoutInlModuleMap φ B) :
    c = extendScalarsComparison φ B :=
  ((extendScalarsAdjunction φ).homEquiv _ _).injective
    (h.trans (homEquiv_extendScalarsComparison φ B).symm)

/-- **The module underlying a pushout of algebra sheaves is an extension of scalars, given that
the canonical comparison is invertible** — which it always is, by
`Stacks.SheafOfModules.AlgebraPushoutAnyUniverse.isIso_extendScalarsComparison`.  This is the
identification that
`Stacks.AffineAlgebraEquivalence.isQuasicoherent_algebraPullback_of_underlyingModuleIso` and
the degree-zero case of [Stacks, Tag 02KH] consume. -/
public noncomputable def underlyingModulePushoutIso (B : Under R)
    (h : IsIso (extendScalarsComparison φ B)) :
    underlyingModule ((Under.pushout φ).obj B) ≅
      (extendScalars φ).obj (underlyingModule B) :=
  (@asIso _ _ _ _ (extendScalarsComparison φ B) h).symm

end Comparison

/-! ### The instance the base-change square of a scheme morphism needs -/

section Scheme

variable {S T : Scheme.{u}} (g : T ⟶ S)

open Stacks.FlatChangeOfRings Stacks.AffineAlgebraEquivalence

/-- The comparison at the pushout half of `Stacks.AffineAlgebraEquivalence.algebraPullback`:
for `A` a sheaf of commutative `𝒪_S`-algebras, the canonical morphism from the extension of
scalars along `g⁻¹𝒪_S ⟶ 𝒪_T` of the module underlying `g⁻¹A` to the module underlying
`g⁻¹A ⊗_{g⁻¹𝒪_S} 𝒪_T`.  This is the shape in which the `algebraPullback_isQuasicoherent`
clause of [Stacks, Tag 01SA] needs the identification; the other input is the identification of
the module underlying `g⁻¹A` with the inverse image of the module underlying `A`. -/
public noncomputable def algebraPullbackComparison (A : Stacks.RelativeSpec.AlgebraSheaf S) :
    (extendScalars (inverseImageStructureMap g)).obj
        (underlyingModule ((Under.post (TopCat.Sheaf.pullback CommRingCat g.base)).obj A)) ⟶
      underlyingModule ((algebraPullback g).obj A) :=
  extendScalarsComparison (inverseImageStructureMap g)
    ((Under.post (TopCat.Sheaf.pullback CommRingCat g.base)).obj A)

end Scheme

end Stacks.SheafOfModules.AlgebraPushoutAnyUniverse

end
