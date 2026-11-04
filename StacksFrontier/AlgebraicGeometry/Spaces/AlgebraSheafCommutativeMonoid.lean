module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAlgebraColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Internal.Module

/-!
# An algebra sheaf is a commutative monoid object in the `𝒪_F`-modules

Let `F` be an algebraic space.  `AlgebraicGeometry.Space.AlgebraSheaf` presents a sheaf of
commutative `𝒪_F`-algebras as a sheaf of commutative rings together with a sectionwise ring
homomorphism out of the structure sheaf, not as an object carrying a multiplication
`𝒜 ⊗_{𝒪_F} 𝒜 ⟶ 𝒜` for the tensor product of `AlgebraicGeometry.Space.modulesMonoidalCategory`.
This file produces that multiplication and its unit, and proves the monoid and commutativity
axioms: **the `𝒪_F`-module underlying an algebra sheaf is a commutative monoid object in
`AlgebraicGeometry.Space.Modules`.**

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.underlyingPresheaf` is the presheaf of `𝒪_F`-modules
  underlying an algebra sheaf, spelled over the ring presheaf which Mathlib's monoidal structure
  on presheaves of modules is indexed by; see the implementation notes.
* `AlgebraicGeometry.Space.AlgebraSheaf.sectionAlgebra` is the sectionwise algebra structure, and
  `AlgebraicGeometry.Space.AlgebraSheaf.sectionMonObj` the resulting monoid object in the
  `𝒪_F(U)`-modules for a single étale chart `U`.
* `AlgebraicGeometry.Space.AlgebraSheaf.presheafMultiplication` and
  `AlgebraicGeometry.Space.AlgebraSheaf.presheafUnit` are the multiplication
  `𝒜 ⊗_p 𝒜 ⟶ 𝒜` and the unit `𝒪_F ⟶ 𝒜` for the objectwise tensor product of *presheaves* of
  modules, and `AlgebraicGeometry.Space.AlgebraSheaf.presheafMonObj`,
  `AlgebraicGeometry.Space.AlgebraSheaf.presheafIsCommMonObj` and
  `AlgebraicGeometry.Space.AlgebraSheaf.presheafCommMon` the commutative monoid object they
  make of it.
* `AlgebraicGeometry.Space.AlgebraSheaf.monObj`,
  `AlgebraicGeometry.Space.AlgebraSheaf.isCommMonObj` and
  `AlgebraicGeometry.Space.AlgebraSheaf.commMon` are **the commutative monoid object structure on
  the `𝒪_F`-module underlying an algebra sheaf**, for the tensor product of
  `AlgebraicGeometry.Space.modulesMonoidalCategory`.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.presheafMultiplication_app_tmul` and
  `AlgebraicGeometry.Space.AlgebraSheaf.presheafUnit_app`: the multiplication sends a pure tensor
  of two local sections to their product, and the unit sends a section of the structure sheaf to
  its image under the structure-algebra map.  These are what identify the two morphisms.
* `AlgebraicGeometry.Space.AlgebraSheaf.commMon_X`: the underlying object of the commutative
  monoid object is `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule` itself, on the nose.

## Implementation notes

**What this is for.** Stacks 081V asks for an anti-equivalence between the algebraic spaces
affine over `X` and the quasi-coherent sheaves of commutative `𝒪_X`-algebras, and the source
constructs it by transporting algebra sheaves through the description of quasi-coherent modules
on an étale presentation, Stacks 03M3.  That description is formalized for an algebraic-space target
(`AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase`), but it is an equivalence of
categories of *modules*, and an algebra sheaf as `AlgebraicGeometry.Space.AlgebraSheaf` presents
it carries no morphism of modules along which an equivalence of modules could carry its
multiplication.  This file supplies that morphism, with its monoid axioms, which is what makes
the algebra structure a structure *in* the monoidal category `AlgebraicGeometry.Space.Modules`.
It does not construct any equivalence; see "what is not here".

**The three spellings of the sections, and why each lemma is stated where it is.** A section of
`AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule` over `U` has the same carrier as a
section of the sheaf of rings `A.right` over `U`, but the two are spelled differently: the first
is a `ModuleCat` object built by `PresheafOfModules.ofPresheaf`, the second a `CommRingCat`
object.  Instance resolution does not connect the spellings, so `x * y` and `1` are not found at
the module spelling at all.  Every proof below therefore states its ring-level content with a
`show` at the ring spelling and discharges it with a ring lemma, the two statements being
definitionally equal.  This is the device of
`StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafMultiplication`, which does the same for
a sheaf of algebras on a scheme.

**Why the monoid axioms are not proved here.** They are Mathlib's, one étale chart at a time:
`AlgebraicGeometry.Space.AlgebraSheaf.sectionMonObj` is
`ModuleCat.MonModuleEquivalenceAlgebra.inverseObj` of the algebra of sections, whose monoid
object laws are exactly the associativity and unit laws of a commutative ring over a base.  The
module of sections of `underlyingModule` is definitionally `ModuleCat.of 𝒪_F(U) A(U)` for the
algebra structure `sectionAlgebra`, so that monoid object is a monoid object on it with nothing
transported.  All three laws, and commutativity, are equations between morphisms of presheaves of
modules whose structural morphisms are objectwise, so each one reduces to its chartwise form by
`PresheafOfModules.hom_ext` and nothing else.

**Why the passage to sheaves is a transport along a monoidal functor.** The monoidal structure of
`AlgebraicGeometry.Space.modulesMonoidalCategory` is the localization of the objectwise monoidal
structure on presheaves of modules along sheafification, so sheafification is a braided monoidal
functor for them and carries commutative monoid objects to commutative monoid objects —
`CategoryTheory.Functor.mapCommMon`.  Its value on the presheaf underlying a sheaf is that sheaf
again, `Stacks.SheafOfModules.sheafifyValIso`, and `CategoryTheory.MonObj.ofIso` moves the
structure across that isomorphism.  No associator or unitor of the sheaf monoidal structure is
written out: the localization has no formulas for them, and this route needs none.

The sheaf-level definitions are stated with their `CategoryTheory.MonoidalCategory` and
`CategoryTheory.BraidedCategory` instances given explicitly as
`AlgebraicGeometry.Space.modulesMonoidalCategory` and
`AlgebraicGeometry.Space.modulesBraidedCategory`, and are built from terms living at the
`CategoryTheory.LocalizedMonoidal` spelling of the same structures.  The two are the same term —
`AlgebraicGeometry.Space.modulesMonoidalCategory` unfolds to
`inferInstanceAs (MonoidalCategory (LocalizedMonoidal ..))` — but
`CategoryTheory.LocalizedMonoidal` is a plain definition, which instance resolution does not
unfold, so Mathlib's instance that the localization functor is braided is not found at the
`AlgebraicGeometry.Space.Modules` spelling. Giving the instances explicitly is what lets the
construction be stated at the spelling its consumers use while being built where the instances
fire. For the same reason the monoidality of the localizing class is supplied by name, as
`AlgebraicGeometry.Space.AlgebraSheaf.isMonoidalLocalIso`; see its docstring.

**What is not here.** No equivalence and no clause of Stacks 081V.  What a commutative monoid
object buys for 081V is that an algebra structure is now a structure in a monoidal category, so
it is transportable along any braided monoidal equivalence of `𝒪`-modules; the equivalence of
Stacks 03M3 is not known to be monoidal, and neither
`AlgebraicGeometry.Space.QuasicoherentSheaves` nor
`AlgebraicGeometry.Space.QuasicoherentModule` carries a monoidal structure at all.  The
declaration that would close the gap is a `CategoryTheory.Functor.Braided` instance for
`AlgebraicGeometry.Space.quasicoherentFromSpaceBase`; with it,
`CategoryTheory.Equivalence.mapCommMon` turns Stacks 03M3 into the descent statement for
algebras that the `equivalence` field of Stacks 081V consumes.  The converse direction — reading
a commutative monoid object in `AlgebraicGeometry.Space.Modules` back as an
`AlgebraicGeometry.Space.AlgebraSheaf` — is also absent: it needs the multiplication's sections,
and a section of a tensor product sheaf is only locally a pure tensor.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonObj

universe u

namespace CategoryTheory.IsCommMonObj

/-- Commutativity of a monoid object transports along an isomorphism, as the monoid object
structure itself does by `CategoryTheory.MonObj.ofIso`.

Mathlib carries `CategoryTheory.MonObj.ofIso` without this companion.  The proof is naturality of
the braiding in the two conjugating isomorphisms, followed by commutativity of the original
multiplication. -/
theorem ofIso {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] {M X : C}
    [MonObj M] [IsCommMonObj M] (e : M ≅ X) :
    letI := MonObj.ofIso e
    IsCommMonObj X := by
  let := MonObj.ofIso e
  refine ⟨?_⟩
  rw [MonObj.ofIso_mul, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm_assoc]

end CategoryTheory.IsCommMonObj

namespace AlgebraicGeometry.Space.AlgebraSheaf

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The presheaf of `𝒪_F`-modules underlying an algebra sheaf, with its ring presheaf spelled as
`Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf` of the structure sheaf rather
than as the ring sheaf of the small étale ringed site.

The two are definitionally equal — that is
`AlgebraicGeometry.Space.ringSheaf_eq_structureSheaf` — but Mathlib's monoidal structure on
presheaves of modules is indexed by a ring presheaf of the shape `𝒪 ⋙ forget₂ CommRingCat RingCat`
and instance resolution does not unfold the ring sheaf of a ringed site to see that shape.  This
is the same respelling as `Stacks.SheafOfModules.sheafifyFunctor`. -/
noncomputable abbrev underlyingPresheaf (A : AlgebraSheaf.{u, u} B S hS F hF) :
    PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (structureSheaf B S hS F hF).obj) :=
  A.underlyingModule.val

variable (A : AlgebraSheaf.{u, u} B S hS F hF)

/-! ### One étale chart -/

/-- The sections of an algebra sheaf over an étale chart form an algebra over the sections of the
structure sheaf there: the structure-algebra map of the chart, read as an algebra structure. -/
@[instance_reducible]
def sectionAlgebra (U : (SmallEtale B S hS F)ᵒᵖ) :
    Algebra ((structureSheaf B S hS F hF).obj.obj U) (A.right.obj.obj U) :=
  RingHom.toAlgebra (A.algebraMap U)

attribute [local instance] sectionAlgebra

/-- **The sections of an algebra sheaf over an étale chart are a monoid object in the
`𝒪_F(U)`-modules.**  This is `ModuleCat.MonModuleEquivalenceAlgebra.inverseObj` of
`AlgebraicGeometry.Space.AlgebraSheaf.sectionAlgebra`; the point is the type it is accepted at,
the module of sections of `AlgebraicGeometry.Space.AlgebraSheaf.underlyingModule`, which is
definitionally `ModuleCat.of 𝒪_F(U) A(U)` for that algebra structure. -/
@[instance_reducible]
noncomputable def sectionMonObj (U : (SmallEtale B S hS F)ᵒᵖ) :
    MonObj (A.underlyingPresheaf.obj U) :=
  ModuleCat.MonModuleEquivalenceAlgebra.inverseObj
    (AlgCat.of ((structureSheaf B S hS F hF).obj.obj U) (A.right.obj.obj U))

attribute [local instance] sectionMonObj

/-- The multiplication of `AlgebraicGeometry.Space.AlgebraSheaf.sectionMonObj` on a pure tensor
of sections is their product in the ring of sections. -/
theorem sectionMonObj_mul_tmul (U : (SmallEtale B S hS F)ᵒᵖ) (x y : A.right.obj.obj U) :
    μ[A.underlyingPresheaf.obj U] (x ⊗ₜ y) = (x * y : A.right.obj.obj U) :=
  rfl

/-- The unit of `AlgebraicGeometry.Space.AlgebraSheaf.sectionMonObj` is the structure-algebra map
of the chart. -/
theorem sectionMonObj_one_apply (U : (SmallEtale B S hS F)ᵒᵖ)
    (r : (structureSheaf B S hS F hF).obj.obj U) :
    η[A.underlyingPresheaf.obj U] r = (A.algebraMap U r : A.right.obj.obj U) :=
  rfl

/-- The sections of an algebra sheaf over an étale chart are a *commutative* monoid object: the
multiplication of the monoid object is the product of the ring of sections, and that ring is
commutative. -/
theorem sectionIsCommMonObj (U : (SmallEtale B S hS F)ᵒᵖ) :
    IsCommMonObj (A.underlyingPresheaf.obj U) where
  mul_comm := ModuleCat.hom_ext <| TensorProduct.ext <| LinearMap.ext₂
    fun (x y : A.right.obj.obj U) => by
      change (y * x : A.right.obj.obj U) = (x * y : A.right.obj.obj U)
      exact mul_comm y x

attribute [local instance] sectionIsCommMonObj

/-! ### The presheaf of modules -/

/-- **The multiplication of an algebra sheaf, as a morphism of presheaves of `𝒪_F`-modules**
`𝒜 ⊗_p 𝒜 ⟶ 𝒜` out of the objectwise tensor product.  On each étale chart it is the
multiplication of the ring of sections; naturality is multiplicativity of the restriction
maps. -/
noncomputable def presheafMultiplication :
    A.underlyingPresheaf ⊗ A.underlyingPresheaf ⟶ A.underlyingPresheaf where
  app U := μ[A.underlyingPresheaf.obj U]
  naturality {U V} f := ModuleCat.MonoidalCategory.tensor_ext
    (fun (x y : A.right.obj.obj U) => by
      change ((A.right.obj.map f x) * (A.right.obj.map f y) : A.right.obj.obj V) =
        (A.right.obj.map f (x * y) : A.right.obj.obj V)
      exact (map_mul ((A.right.obj.map f).hom) x y).symm)

/-- On an étale chart `U`, `AlgebraicGeometry.Space.AlgebraSheaf.presheafMultiplication` sends
`x ⊗ₜ y` to the product `x * y` in the ring of sections over `U`. -/
@[simp]
theorem presheafMultiplication_app_tmul (U : (SmallEtale B S hS F)ᵒᵖ)
    (x y : A.right.obj.obj U) :
    PresheafOfModules.Hom.app A.presheafMultiplication U (x ⊗ₜ y) =
      (x * y : A.right.obj.obj U) :=
  rfl

/-- **The unit of an algebra sheaf, as a morphism of presheaves of `𝒪_F`-modules**
`𝒪_F ⟶ 𝒜` out of the tensor unit.  On each étale chart it is the structure-algebra map;
naturality is `AlgebraicGeometry.Space.AlgebraSheaf.algebraMap_natural`. -/
noncomputable def presheafUnit :
    𝟙_ (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (structureSheaf B S hS F hF).obj)) ⟶ A.underlyingPresheaf where
  app U := η[A.underlyingPresheaf.obj U]
  naturality {_ _} f :=
    ModuleCat.hom_ext (LinearMap.ext fun r => (A.algebraMap_natural f r).symm)

/-- On an étale chart `U`, `AlgebraicGeometry.Space.AlgebraSheaf.presheafUnit` sends a section
`r` of `𝒪_F` to its image under the structure-algebra map `A.algebraMap U`. -/
@[simp]
theorem presheafUnit_app (U : (SmallEtale B S hS F)ᵒᵖ)
    (r : (structureSheaf B S hS F hF).obj.obj U) :
    PresheafOfModules.Hom.app A.presheafUnit U r = (A.algebraMap U r : A.right.obj.obj U) :=
  rfl

/-- **The presheaf of modules underlying an algebra sheaf is a monoid object** for the objectwise
tensor product of presheaves of `𝒪_F`-modules.

Each law is an equation between morphisms of presheaves of modules all of whose structural
morphisms are objectwise, so it holds as soon as it holds on every étale chart, where it is the
corresponding law of `AlgebraicGeometry.Space.AlgebraSheaf.sectionMonObj`. -/
@[instance_reducible]
noncomputable def presheafMonObj : MonObj A.underlyingPresheaf where
  one := A.presheafUnit
  mul := A.presheafMultiplication
  one_mul := PresheafOfModules.hom_ext fun U => MonObj.one_mul (A.underlyingPresheaf.obj U)
  mul_one := PresheafOfModules.hom_ext fun U => MonObj.mul_one (A.underlyingPresheaf.obj U)
  mul_assoc := PresheafOfModules.hom_ext fun U => MonObj.mul_assoc (A.underlyingPresheaf.obj U)

attribute [local instance] presheafMonObj

/-- The monoid object of `AlgebraicGeometry.Space.AlgebraSheaf.presheafMonObj` is commutative,
the ring of sections on each étale chart being commutative. -/
theorem presheafIsCommMonObj : IsCommMonObj A.underlyingPresheaf where
  mul_comm := PresheafOfModules.hom_ext fun U =>
    IsCommMonObj.mul_comm (A.underlyingPresheaf.obj U)

attribute [local instance] presheafIsCommMonObj

/-- **The presheaf of modules underlying an algebra sheaf, as a commutative monoid object** in the
presheaves of `𝒪_F`-modules. -/
noncomputable def presheafCommMon :
    CommMon (PresheafOfModules.{u}
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf
        (structureSheaf B S hS F hF).obj)) where
  X := A.underlyingPresheaf

/-! ### The sheaf of modules -/

/-- **The local isomorphisms of presheaves of `𝒪_F`-modules are a monoidal class of
morphisms**, at the universes of the small étale site of an algebraic space: this is
`Stacks.SheafOfModules.isMonoidal_localIso`, the content of Tag 05NA, applied with its site and
its ring presheaf given, so that its one universe `w` is `u`.

Instance resolution does not find it at this site.  `Stacks.SheafOfModules.localIso` carries a
single universe `w` for the ring presheaf, the modules and the abelian groups at once, and the
goal here determines `w = u`; but matching the conclusion of
`Stacks.SheafOfModules.isMonoidal_localIso`, whose `w` is a metavariable, only *postpones* that
universe constraint.  Its own `CategoryTheory.HasWeakSheafify` argument is synthesized first, at
`AddCommGrpCat.{max (u + 1) ?w}` because Mathlib has sheafification of abelian groups only at a
universe dominating the two site universes, and the postponed `max (u + 1) ?w = u` is then
unsatisfiable: the small étale site has objects in `Type (u + 1)` while the structure sheaf is
in `CommRingCat.{u}`.  Applying the instance with `𝒪` and `J` given pins `w = u` before any
of that, which is why it is supplied here rather than inferred. -/
theorem isMonoidalLocalIso :
    (Stacks.SheafOfModules.localIso (J := SmallEtale.topology B S hS F)
      (structureSheaf B S hS F hF).obj).IsMonoidal :=
  Stacks.SheafOfModules.isMonoidal_localIso (J := SmallEtale.topology B S hS F)
    (structureSheaf B S hS F hF).obj

attribute [local instance] isMonoidalLocalIso

/-- Sheafification of presheaves of `𝒪_F`-modules, read as the localization functor at the local
isomorphisms that it is, so that Mathlib's monoidal and braided structures on it are available.

Its codomain is `CategoryTheory.LocalizedMonoidal`, which is definitionally
`AlgebraicGeometry.Space.Modules`; the monoidal structure of
`AlgebraicGeometry.Space.modulesMonoidalCategory` is Mathlib's on that type. -/
noncomputable abbrev sheafifyBraided :=
  Localization.Monoidal.toMonoidalCategory
    (Stacks.SheafOfModules.sheafifyFunctor (structureSheaf B S hS F hF).obj
      (structureRingPresheaf_isSheaf B S hS F hF))
    (Stacks.SheafOfModules.localIso (J := SmallEtale.topology B S hS F)
      (structureSheaf B S hS F hF).obj)
    (Stacks.SheafOfModules.sheafifyUnitIso (structureSheaf B S hS F hF).obj
      (structureRingPresheaf_isSheaf B S hS F hF))

/-- The sheafification of the presheaf of modules underlying an algebra sheaf, as a commutative
monoid object: the image of `AlgebraicGeometry.Space.AlgebraSheaf.presheafCommMon` under
`CategoryTheory.Functor.mapCommMon` of sheafification. -/
noncomputable def sheafifyCommMon :
    CommMon (LocalizedMonoidal
      (L := Stacks.SheafOfModules.sheafifyFunctor (structureSheaf B S hS F hF).obj
        (structureRingPresheaf_isSheaf B S hS F hF))
      (W := Stacks.SheafOfModules.localIso (J := SmallEtale.topology B S hS F)
        (structureSheaf B S hS F hF).obj)
      (Stacks.SheafOfModules.sheafifyUnitIso (structureSheaf B S hS F hF).obj
        (structureRingPresheaf_isSheaf B S hS F hF))) :=
  (Functor.mapCommMon (sheafifyBraided (B := B) (S := S) (hS := hS) (F := F) (hF := hF))).obj
    A.presheafCommMon

/-- **The `𝒪_F`-module underlying an algebra sheaf is a monoid object** in
`AlgebraicGeometry.Space.Modules` for the tensor product of
`AlgebraicGeometry.Space.modulesMonoidalCategory`: the monoid object structure on the
sheafification of its presheaf of modules, carried across
`Stacks.SheafOfModules.sheafifyValIso`.

The monoidal structure is given explicitly rather than by instance resolution; see the
implementation notes for why. -/
@[instance_reducible]
noncomputable def monObj :
    @MonObj (Modules.{u, u} B S hS F hF) _ (modulesMonoidalCategory B S hS F hF)
      A.underlyingModule :=
  @MonObj.ofIso (Modules.{u, u} B S hS F hF) _ (modulesMonoidalCategory B S hS F hF) _ _
    A.sheafifyCommMon.mon
    (Stacks.SheafOfModules.sheafifyValIso (structureSheaf B S hS F hF).obj
      (structureRingPresheaf_isSheaf B S hS F hF) A.underlyingModule)

/-- The monoid object of `AlgebraicGeometry.Space.AlgebraSheaf.monObj` is commutative. -/
theorem isCommMonObj :
    @IsCommMonObj (Modules.{u, u} B S hS F hF) _ (modulesMonoidalCategory B S hS F hF)
      (modulesBraidedCategory B S hS F hF) A.underlyingModule A.monObj :=
  @IsCommMonObj.ofIso (Modules.{u, u} B S hS F hF) _ (modulesMonoidalCategory B S hS F hF)
    (modulesBraidedCategory B S hS F hF) _ _ A.sheafifyCommMon.mon A.sheafifyCommMon.comm
    (Stacks.SheafOfModules.sheafifyValIso (structureSheaf B S hS F hF).obj
      (structureRingPresheaf_isSheaf B S hS F hF) A.underlyingModule)

/-- **An algebra sheaf on an algebraic space is a commutative monoid object in the
`𝒪_F`-modules.**  The commutative monoid object in `AlgebraicGeometry.Space.Modules`, for the
tensor product of `AlgebraicGeometry.Space.modulesMonoidalCategory`, whose underlying object is
the `𝒪_F`-module underlying the algebra sheaf. -/
noncomputable def commMon :
    @CommMon (Modules.{u, u} B S hS F hF) _ (modulesMonoidalCategory B S hS F hF)
      (modulesBraidedCategory B S hS F hF) :=
  @CommMon.mk (Modules.{u, u} B S hS F hF) _ (modulesMonoidalCategory B S hS F hF)
    (modulesBraidedCategory B S hS F hF) A.underlyingModule A.monObj A.isCommMonObj

/-- The underlying object of `AlgebraicGeometry.Space.AlgebraSheaf.commMon` is the `𝒪_F`-module
underlying the algebra sheaf, on the nose. -/
theorem commMon_X :
    @CommMon.X (Modules.{u, u} B S hS F hF) _ (modulesMonoidalCategory B S hS F hF)
        (modulesBraidedCategory B S hS F hF) (commMon A) =
      A.underlyingModule :=
  rfl

end AlgebraicGeometry.Space.AlgebraSheaf

end
