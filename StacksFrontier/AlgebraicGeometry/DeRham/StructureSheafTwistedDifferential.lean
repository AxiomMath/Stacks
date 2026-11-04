module

public import StacksFrontier.AlgebraicGeometry.DeRham.StructureSheafConnection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.LocalizedLeibniz

/-!
# The twisted de Rham differential of the canonical connection on the structure sheaf

Let `f : Y ⟶ S` be a morphism of schemes.  The structure sheaf `𝒪_Y`, read as a sheaf of
`𝒪_Y`-modules of rank one, carries the canonical relative connection `∇(b) = 1 ⊗ d b` of
`AlgebraicGeometry.Scheme.Hom.structureModuleConnection`.  This file constructs its **twisted de
Rham differential**, that is, a term of
`AlgebraicGeometry.Scheme.Hom.TwistedDeRhamDifferential (structureModuleConnection f)`, shows
that consecutive twisted differentials compose to zero, and concludes that the canonical
connection is integrable.

The construction is the left unitor.  The degree-`q` term of the twisted complex of `𝒪_Y` is
`𝒪_Y ⊗_{𝒪_Y} Ω^q_{Y/S}`, which the left unit constraint of the sheafified tensor product
identifies with `Ω^q_{Y/S}`; under that identification the twisted differential is the relative
de Rham differential of `AlgebraicGeometry.Scheme.Hom.deRhamComplex` and the wedge pairing is the
exterior product `AlgebraicGeometry.Scheme.Hom.relativeExteriorProduct`.  The Leibniz rule
`d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` then comes down, after moving the coefficient across the tensor
sign, to the Leibniz rule `d(b · ω) = d b ∧ ω + b · d ω` for the relative de Rham differential,
which is `AlgebraicGeometry.SheafOfModules.d_smul`.

This exhibits `AlgebraicGeometry.Scheme.Hom.TwistedDeRhamDifferential` as an inhabited structure.
Together with `AlgebraicGeometry.Scheme.Hom.structureModuleConnection` it supplies every field
but coherence of
`...Crystalline.SmallSite.GlobalCrystallineSituation.Situation07MZ.CoherentModuleWithConnection`,
the bundle clause (2) of [Stacks, Tag 07MZ] quantifies over; see the "What is and is not proved"
note below.

## Main definitions

Everything lives in the namespace `AlgebraicGeometry.Scheme.Hom`.

* `structureFormsUnitor` and `structureConnectionUnitor` — **the left unit constraints
  `𝒪_Y ⊗_{𝒪_Y} Ω^q_{Y/S} ≅ Ω^q_{Y/S}` and `𝒪_Y ⊗_{𝒪_Y} Ω_{Y/S} ≅ Ω_{Y/S}`**, the left unitors
  of `Stacks.SheafOfModules.OnSpace.monoidal`.
* `structureTwistedWedge` — the wedge pairing of the twisted differential: a value of the
  connection, read through the left unit constraint as a relative differential, wedged with a
  relative `q`-form.
* `structureTwistedDifferential` — **the twisted de Rham differential in degree `q`** as a
  morphism of sheaves of `f^{-1}𝒪_S`-modules, the relative de Rham differential conjugated by
  the left unit constraints.
* `structureTwistedDeRhamDifferential` — **the twisted de Rham differential of the canonical
  connection on `𝒪_Y`**, the resulting `TwistedDeRhamDifferential`.
* `relativeDifferentialsOnSpace`, `relativeDifferentialFormsOnSpace`,
  `structureConnectionTargetOnSpace`, `structureTwistedFormsOnSpace`,
  `relativeExteriorProductOnSpace`, `relativeDeRhamSectionOnSpace` and `structureRingSection` —
  the sheaves, the two section-level operations and a local function, each produced at the
  ringed-space spelling of the structure sheaf of rings.  These carry no mathematics; see the
  implementation notes for why they are needed.

## Main results

* `relativeDeRhamDifferentialSection_smul` — **the Leibniz rule for the relative de Rham
  differential of a morphism of schemes** on local sections, `d(b · ω) = d b ∧ ω + b · d ω`.
* `nonempty_structureTwistedDeRhamDifferential` — **`TwistedDeRhamDifferential` is inhabited.**
* `structureTwistedDeRhamDifferential_isComplex` — **the twisted de Rham sequence of the
  canonical connection on `𝒪_Y` is a complex**, and
  `isIntegrable_structureModuleConnection` — **the canonical connection on `𝒪_Y` is
  integrable.**
* `structureTwistedDifferential_twistedTmul` — the Leibniz rule
  `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`, which is what makes the differential constructed here *the*
  twisted de Rham differential and not an arbitrary morphism between the right sheaves.
* `relativeExteriorProduct_add_left`, `relativeExteriorProduct_smul_left` and
  `relativeExteriorProduct_restrict` — the exterior product of a relative differential with a
  relative `q`-form is additive and linear in the differential and commutes with restriction.

## What is and is not proved

What is proved is that a twisted de Rham differential exists for the canonical connection on the
structure sheaf, that it squares to zero, and hence that that connection is integrable.  So
neither `AlgebraicGeometry.Scheme.Hom.TwistedDeRhamDifferential` nor
`AlgebraicGeometry.Scheme.Hom.ModuleConnection.IsIntegrable` is a vacuous notion, and the twisted
de Rham complex `AlgebraicGeometry.Scheme.Hom.twistedDeRhamComplex` is a complex that exists.

**Nothing here constructs a twisted de Rham differential for an arbitrary connection on an
arbitrary sheaf of modules.**  The module documentation of
`StacksFrontier.AlgebraicGeometry.DeRham.ModuleConnection` records what that needs — the balanced
presheaf-level pairing pushed through the sheafification that defines the tensor product — and
that step is still not taken.  The construction below is special to the structure sheaf: it uses
that `𝒪_Y ⊗_{𝒪_Y} Ω^q_{Y/S}` is *isomorphic* to `Ω^q_{Y/S}`, which is what makes the wedge
pairing and the differential definable without that step.

Uniqueness of the twisted differential is likewise not proved, and is open for the same reason as
before: it needs an extensionality principle for a morphism out of the restriction of scalars of
a sheafified tensor product.  What the Leibniz rule
`structureTwistedDifferential_twistedTmul` does give is that the differential constructed here is
*a* twisted de Rham differential of the canonical connection in the sense of
`TwistedDeRhamDifferential`, which is the contract every statement quantified over that structure
is about.

**No `CoherentModuleWithConnection` is produced here.**  That bundle additionally asks for
`SheafOfModules.IsCoherent` of the module, and the structure sheaf of a scheme is coherent only
under a hypothesis — local Noetherianness, by
`Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit` — which is a property of the scheme `Y`
of [Stacks, Tag 07MZ] and not of anything constructed here.  Deriving it from that remark's
hypotheses (`S = Spec A` affine with `A` Noetherian and `Y ⟶ S` proper, hence of finite type) is
a statement about those hypotheses and belongs with them; it is
`StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.StructureSheafModuleWithConnection`, which
assembles the bundle out of the connection, the differential and the square-zero property proved
here.

## Implementation notes

The left unitor is the one of `Stacks.SheafOfModules.OnSpace.monoidal`, whose tensor product is
the bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` on the nose, so the source of
`structureFormsUnitor` is the degree-`q` term `AlgebraicGeometry.Scheme.Hom.twistedForms` of the
twisted complex and not a second spelling of it.  That monoidal structure lives on
`SheafOfModules (structureSheafRing Y.toRingedSpace)`, while the sheaves of this tree are typed
as `Y.Modules`; the two are the same type but `AlgebraicGeometry.Scheme.Modules` is a `def`, so
the elaborator of `≅` does not see through it and picks the wrong category instance.  Every
object entering a unitor is therefore produced by an abbreviation whose *declared* codomain is
the ringed-space spelling — `relativeDifferentialFormsOnSpace` and friends — and the resulting
morphisms are matched against the `Y.Modules` spellings by unification at the application site.

The scalar action of a local function on the sections of a sheaf of modules has the same two
spellings, and only one of them is found by instance search in each: the ring of scalars of a
`Y.Modules` is `Y.ringCatSheaf.obj.obj U`, which `AlgebraicGeometry.Scheme.structureSectionScalar`
produces, while the unitor formulas of `Stacks.SheafOfModules.OnSpace` are phrased with
`Y.presheaf.obj U`, the spelling that is reducibly the ring of scalars of a sheaf of modules over
`structureSheafRing`.  Each statement below is therefore phrased at the spelling instance search
finds for it, and the two are joined only inside proofs, by `Eq.trans` and `congrArg` chains
whose application sites tolerate the difference.  For the same reason there is no `rw` or
`simp only` in a proof that mentions a section of a `Y.Modules`: `rw` type-checks its rewrites at
a transparency at which `Y.ringCatSheaf.obj` is opaque, and reports the pattern as absent.

The degree transport `1 + q = q + 1` inside
`AlgebraicGeometry.Scheme.Hom.relativeExteriorProduct` and the one inside
`AlgebraicGeometry.SheafOfModules.reindexForm` are two spellings of one transport; they are
compared through heterogeneous equality rather than rewritten into one another, which is the
cheapest route and the one used throughout the de Rham files of this tree.

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 0FKG](https://stacks.math.columbia.edu/tag/0FKG)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 05NA](https://stacks.math.columbia.edu/tag/05NA)
* [Stacks Project, Tag 07MZ](https://stacks.math.columbia.edu/tag/07MZ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace MonoidalCategory Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {Y S : Scheme.{u}} (f : Y ⟶ S)

/-! ### Transporting a relative differential form along an equality of degrees -/

/-- A transported relative differential form is heterogeneously equal to the form itself:
`AlgebraicGeometry.Scheme.Hom.transportDifferentialForm` renames a degree and does not change the
section. -/
theorem transportDifferentialForm_heq {i j : ℤ} (h : i = j) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms f i).val.obj U) :
    HEq (transportDifferentialForm f h U ω) ω := by
  subst h; rfl

/-- Transporting a relative differential form along an equality of degrees is additive. -/
theorem transportDifferentialForm_add {i j : ℤ} (h : i = j) (U : (Y.Opens)ᵒᵖ)
    (ω ω' : (relativeDifferentialForms f i).val.obj U) :
    transportDifferentialForm f h U (ω + ω') =
      transportDifferentialForm f h U ω + transportDifferentialForm f h U ω' := by
  subst h; rfl

/-- Transporting a relative differential form along an equality of degrees commutes with the
action of a local function. -/
theorem transportDifferentialForm_smul {i j : ℤ} (h : i = j) (U : (Y.Opens)ᵒᵖ)
    (r : Y.ringCatSheaf.obj.obj U) (ω : (relativeDifferentialForms f i).val.obj U) :
    transportDifferentialForm f h U (r • ω) = r • transportDifferentialForm f h U ω := by
  subst h; rfl

/-- Transporting a relative differential form along an equality of degrees commutes with
restriction to a smaller open. -/
theorem transportDifferentialForm_restrict {i j : ℤ} (h : i = j) {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V)
    (ω : (relativeDifferentialForms f i).val.obj U) :
    (relativeDifferentialForms f j).val.map k (transportDifferentialForm f h U ω) =
      transportDifferentialForm f h V ((relativeDifferentialForms f i).val.map k ω) := by
  subst h; rfl

/-! ### The Leibniz rule for the relative de Rham differential -/

/-- The reindexed wedge of the exact differential of a local function with a relative `q`-form,
as the de Rham files of this tree spell it, is the relative exterior product
`AlgebraicGeometry.Scheme.Hom.relativeExteriorProduct`: the two degree transports `1 + q = q + 1`
are transports of one and the same section. -/
theorem reindexForm_eq_relativeExteriorProduct (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (b : Y.ringCatSheaf.obj.obj U) (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    AlgebraicGeometry.SheafOfModules.reindexForm (deRhamAlgebras f) (Nat.add_comm 1 q) U
        (AlgebraicGeometry.SheafOfModules.formProduct (deRhamAlgebras f) 1 q U
          (AlgebraicGeometry.SheafOfModules.exactOne (deRhamAlgebras f) U b) ω) =
      relativeExteriorProduct f q U ((universalRelativeDerivation f).d (X := U) b) ω :=
  eq_of_heq
    ((AlgebraicGeometry.SheafOfModules.reindexForm_heq (deRhamAlgebras f)
        (Nat.add_comm 1 q) U _).trans
      (transportDifferentialForm_heq f _ U _).symm)

/-- **The Leibniz rule for the relative de Rham differential of a morphism of schemes**, on local
sections: `d(b · ω) = d b ∧ ω + b · d ω` for a local function `b` on `Y` and a local relative
`q`-form `ω`.  This is `AlgebraicGeometry.SheafOfModules.d_smul` read at the chosen package of
algebras and the unique relative de Rham differential. -/
theorem relativeDeRhamDifferentialSection_smul (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (b : Y.ringCatSheaf.obj.obj U) (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    relativeDeRhamDifferentialSection f q U (b • ω) =
      relativeExteriorProduct f q U ((universalRelativeDerivation f).d (X := U) b) ω +
        b • relativeDeRhamDifferentialSection f q U ω :=
  (AlgebraicGeometry.SheafOfModules.d_smul (deRhamAlgebras f)
      (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras f)) q U b ω
      (relativeDeRhamDifferentialSection f q U ω) rfl).trans
    (congrArg (fun z => z + b • relativeDeRhamDifferentialSection f q U ω)
      (reindexForm_eq_relativeExteriorProduct f q U b ω))

/-! ### Linearity of the relative exterior product in the differential -/

/-- Multiplication of homogeneous local sections in the algebra `Ω^•_{Y/S}` of relative
differential forms is additive in its first argument. -/
theorem relativeDifferentialFormsAlgebra_mul_add_left (i j : ℤ) (U : (Y.Opens)ᵒᵖ)
    (x x' : ((relativeDifferentialFormsAlgebra f).piece i).val.obj U)
    (y : ((relativeDifferentialFormsAlgebra f).piece j).val.obj U) :
    ((relativeDifferentialFormsAlgebra f).mul i j).app U (x + x') y =
      ((relativeDifferentialFormsAlgebra f).mul i j).app U x y +
        ((relativeDifferentialFormsAlgebra f).mul i j).app U x' y :=
  congrArg (fun k : ((relativeDifferentialFormsAlgebra f).piece j).val.obj U →+
      ((relativeDifferentialFormsAlgebra f).piece (i + j)).val.obj U => k y)
    ((((relativeDifferentialFormsAlgebra f).mul i j).app U).map_add x x')

/-- The relative exterior product is additive in the relative differential. -/
theorem relativeExteriorProduct_add_left (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (α α' : (relativeDifferentials f).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    relativeExteriorProduct f q U (α + α') ω =
      relativeExteriorProduct f q U α ω + relativeExteriorProduct f q U α' ω :=
  (congrArg (transportDifferentialForm f _ U)
      ((congrArg (fun z => ((relativeDifferentialFormsAlgebra f).mul 1 (q : ℤ)).app U z ω)
          (map_add
            ((Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U).hom
            α α')).trans
        (relativeDifferentialFormsAlgebra_mul_add_left f 1 (q : ℤ) U _ _ ω))).trans
    (transportDifferentialForm_add f _ U _ _)

/-- The relative exterior product is linear in the relative differential. -/
theorem relativeExteriorProduct_smul_left (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (r : Y.ringCatSheaf.obj.obj U) (α : (relativeDifferentials f).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    relativeExteriorProduct f q U (r • α) ω = r • relativeExteriorProduct f q U α ω :=
  (congrArg (transportDifferentialForm f _ U)
      ((congrArg (fun z => ((relativeDifferentialFormsAlgebra f).mul 1 (q : ℤ)).app U z ω)
          (map_smul
            ((Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U).hom
            r α)).trans
        (((relativeDifferentialFormsAlgebra f).mul 1 (q : ℤ)).map_smul_left U r _ ω))).trans
    (transportDifferentialForm_smul f _ U r _)

/-- The relative exterior product commutes with restriction to a smaller open. -/
theorem relativeExteriorProduct_restrict (q : ℕ) {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V)
    (α : (relativeDifferentials f).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).val.map k
        (relativeExteriorProduct f q U α ω) =
      relativeExteriorProduct f q V ((relativeDifferentials f).val.map k α)
        ((relativeDifferentialForms f (q : ℤ)).val.map k ω) :=
  (transportDifferentialForm_restrict f _ k _).trans
    (congrArg (transportDifferentialForm f _ V)
      ((((relativeDifferentialFormsAlgebra f).mul 1 (q : ℤ)).naturality k _ ω).trans
        (congrArg
          (fun z => ((relativeDifferentialFormsAlgebra f).mul 1 (q : ℤ)).app V z
            ((relativeDifferentialForms f (q : ℤ)).val.map k ω))
          (PresheafOfModules.naturality_apply
            (Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val k α).symm)))

/-! ### The left unit constraints -/

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

/-- `Ω_{Y/S}`, at the spelling of sheaves of modules over the structure sheaf of the underlying
ringed space of `Y`, which is where the monoidal structure of the sheafified tensor product
lives. -/
abbrev relativeDifferentialsOnSpace :
    _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) :=
  relativeDifferentials f

/-- `Ω^q_{Y/S}`, at the ringed-space spelling. -/
abbrev relativeDifferentialFormsOnSpace (q : ℕ) :
    _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) :=
  relativeDifferentialForms f (q : ℤ)

/-- `𝒪_Y ⊗_{𝒪_Y} Ω_{Y/S}`, the target of the canonical connection, at the ringed-space
spelling. -/
abbrev structureConnectionTargetOnSpace :
    _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) :=
  moduleConnectionTarget f (_root_.SheafOfModules.unit Y.ringCatSheaf)

/-- `𝒪_Y ⊗_{𝒪_Y} Ω^q_{Y/S}`, the degree-`q` term of the twisted complex of the structure sheaf,
at the ringed-space spelling. -/
abbrev structureTwistedFormsOnSpace (q : ℕ) :
    _root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) :=
  twistedForms f (_root_.SheafOfModules.unit Y.ringCatSheaf) q

/-- **The left unit constraint `𝒪_Y ⊗_{𝒪_Y} Ω^q_{Y/S} ≅ Ω^q_{Y/S}`** of [Stacks, Tag 05NA]: the
left unitor of the monoidal structure `Stacks.SheafOfModules.OnSpace.monoidal`, whose tensor
product is the sheafified tensor product of [Stacks, Tag 01CA] and whose unit is the structure
sheaf. -/
def structureFormsUnitor (q : ℕ) :
    structureTwistedFormsOnSpace f q ≅ relativeDifferentialFormsOnSpace f q :=
  λ_ (relativeDifferentialFormsOnSpace f q)

/-- **The left unit constraint `𝒪_Y ⊗_{𝒪_Y} Ω_{Y/S} ≅ Ω_{Y/S}`** on the target of a connection
on the structure sheaf. -/
def structureConnectionUnitor :
    structureConnectionTargetOnSpace f ≅ relativeDifferentialsOnSpace f :=
  λ_ (relativeDifferentialsOnSpace f)

/-- On a local pure tensor the left unit constraint of `𝒪_Y ⊗ Ω^q_{Y/S}` is scalar
multiplication. -/
theorem structureFormsUnitor_hom_app_twistedTmul (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (s : (_root_.SheafOfModules.unit Y.ringCatSheaf).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (structureFormsUnitor f q).hom.val.app U
        (twistedTmul f (_root_.SheafOfModules.unit Y.ringCatSheaf) q U s ω) =
      Y.structureSectionScalar U s • ω :=
  Stacks.SheafOfModules.OnSpace.leftUnitor_tmul Y.toRingedSpace
    (relativeDifferentialFormsOnSpace f q) U (Y.structureSectionScalar U s) ω

/-- The inverse of the left unit constraint of `𝒪_Y ⊗ Ω^q_{Y/S}` tensors with the unit
section. -/
theorem structureFormsUnitor_inv_app (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (structureFormsUnitor f q).inv.val.app U ω =
      twistedTmul f (_root_.SheafOfModules.unit Y.ringCatSheaf) q U
        (Y.structureUnitSection U) ω :=
  Stacks.SheafOfModules.OnSpace.leftUnitor_inv_apply Y.toRingedSpace
    (relativeDifferentialFormsOnSpace f q) U ω

/-- On a local pure tensor the left unit constraint of `𝒪_Y ⊗ Ω_{Y/S}` is scalar
multiplication. -/
theorem structureConnectionUnitor_hom_app_connectionTmul (U : (Y.Opens)ᵒᵖ)
    (s : (_root_.SheafOfModules.unit Y.ringCatSheaf).val.obj U)
    (α : (relativeDifferentials f).val.obj U) :
    (structureConnectionUnitor f).hom.val.app U
        (connectionTmul f (_root_.SheafOfModules.unit Y.ringCatSheaf) U s α) =
      Y.structureSectionScalar U s • α :=
  Stacks.SheafOfModules.OnSpace.leftUnitor_tmul Y.toRingedSpace
    (relativeDifferentialsOnSpace f) U (Y.structureSectionScalar U s) α

/-- A local section of the structure sheaf of `Y`, read back as a local function at the type
`Y.presheaf.obj U` of sections of the structure sheaf of the underlying ringed space.  It is the
identity map; the point of the declaration is that this is the spelling of the ring of sections
at which the scalar action on the sections of a sheaf of modules over
`Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing` is found by instance search,
and a type ascription on a free variable does not reach it. -/
abbrev structureRingSection (U : (Y.Opens)ᵒᵖ)
    (s : (_root_.SheafOfModules.unit Y.ringCatSheaf).val.obj U) : Y.presheaf.obj U := s

/-- The local function coming from the unit section of the structure sheaf acts on a relative
differential as the identity. -/
theorem structureSectionScalar_structureUnitSection_smul (U : (Y.Opens)ᵒᵖ)
    (α : (relativeDifferentials f).val.obj U) :
    Y.structureSectionScalar U (Y.structureUnitSection U) • α = α :=
  one_smul (Y.ringCatSheaf.obj.obj U) α

/-- The relative de Rham differential on local sections, with its source and target at the
ringed-space spelling, which is where the left unit constraints act on them. -/
abbrev relativeDeRhamSectionOnSpace (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialFormsOnSpace f q).val.obj U) :
    (relativeDifferentialFormsOnSpace f (q + 1)).val.obj U :=
  relativeDeRhamDifferentialSection f q U ω

/-- The relative exterior product of a relative differential with a relative `q`-form, with its
source and target at the ringed-space spelling. -/
abbrev relativeExteriorProductOnSpace (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (α : (relativeDifferentialsOnSpace f).val.obj U)
    (ω : (relativeDifferentialFormsOnSpace f q).val.obj U) :
    (relativeDifferentialFormsOnSpace f (q + 1)).val.obj U :=
  relativeExteriorProduct f q U α ω

/-- The inverse of the left unit constraint sends a scalar multiple of a form to the pure tensor of
the scalar with the form. -/
private theorem structureFormsUnitor_inv_app_smul (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (s : (_root_.SheafOfModules.unit Y.ringCatSheaf).val.obj U)
    (ω : (relativeDifferentialFormsOnSpace f q).val.obj U) :
    (structureFormsUnitor f q).inv.val.app U (structureRingSection U s • ω) =
      twistedTmul f (_root_.SheafOfModules.unit Y.ringCatSheaf) q U s ω := by
  refine (map_smul ((structureFormsUnitor f q).inv.val.app U).hom
    (structureRingSection U s) ω).trans ?_
  refine Eq.trans (congrArg (fun z => structureRingSection U s • z)
    (structureFormsUnitor_inv_app f q U ω)) ?_
  refine (toTensorSheafSection_smul_tmul Y.toRingedSpace
    (_root_.SheafOfModules.unit Y.ringCatSheaf)
    (relativeDifferentialFormsOnSpace f q) U (structureRingSection U s)
    (Y.structureUnitSection U) ω).symm.trans ?_
  exact congrArg (fun z => twistedTmul f (_root_.SheafOfModules.unit Y.ringCatSheaf) q U z ω)
    (Y.structureSectionScalar_smul_structureUnitSection U s)

/-! ### The wedge pairing -/

/-- **The wedge pairing of the twisted de Rham differential of the canonical connection on
`𝒪_Y`**: a local section of `𝒪_Y ⊗_{𝒪_Y} Ω_{Y/S}` is a relative differential through the left
unit constraint, and its exterior product with a relative `q`-form is a relative `(q+1)`-form,
read back in `𝒪_Y ⊗_{𝒪_Y} Ω^{q+1}_{Y/S}` through the left unit constraint there. -/
def structureTwistedWedge (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (η : (moduleConnectionTarget f (_root_.SheafOfModules.unit Y.ringCatSheaf)).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (twistedForms f (_root_.SheafOfModules.unit Y.ringCatSheaf) (q + 1)).val.obj U :=
  (structureFormsUnitor f (q + 1)).inv.val.app U
    (relativeExteriorProduct f q U ((structureConnectionUnitor f).hom.val.app U η) ω)

/-- The wedge pairing is additive in the value of the connection. -/
theorem structureTwistedWedge_add (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (η η' : (moduleConnectionTarget f (_root_.SheafOfModules.unit Y.ringCatSheaf)).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    structureTwistedWedge f q U (η + η') ω =
      structureTwistedWedge f q U η ω + structureTwistedWedge f q U η' ω :=
  (congrArg ((structureFormsUnitor f (q + 1)).inv.val.app U)
        ((congrArg (fun z => relativeExteriorProduct f q U z ω)
            (map_add ((structureConnectionUnitor f).hom.val.app U).hom η η')).trans
          (relativeExteriorProduct_add_left f q U _ _ ω))).trans
    (map_add ((structureFormsUnitor f (q + 1)).inv.val.app U).hom _ _)

/-- The wedge pairing commutes with restriction to a smaller open. -/
theorem structureTwistedWedge_restrict (q : ℕ) {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V)
    (η : (moduleConnectionTarget f (_root_.SheafOfModules.unit Y.ringCatSheaf)).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (twistedForms f (_root_.SheafOfModules.unit Y.ringCatSheaf) (q + 1)).val.map k
        (structureTwistedWedge f q U η ω) =
      structureTwistedWedge f q V
        ((moduleConnectionTarget f (_root_.SheafOfModules.unit Y.ringCatSheaf)).val.map k η)
        ((relativeDifferentialForms f (q : ℤ)).val.map k ω) :=
  (PresheafOfModules.naturality_apply (structureFormsUnitor f (q + 1)).inv.val k _).symm.trans
    (congrArg ((structureFormsUnitor f (q + 1)).inv.val.app V)
      ((relativeExteriorProduct_restrict f q k _ ω).trans
        (congrArg
          (fun z => relativeExteriorProduct f q V z
            ((relativeDifferentialForms f (q : ℤ)).val.map k ω))
          (PresheafOfModules.naturality_apply
            (structureConnectionUnitor f).hom.val k η).symm)))

/-- **On a local pure tensor the wedge pairing is the exterior product of relative differential
forms**, which is the clause that pins it. -/
theorem structureTwistedWedge_connectionTmul (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (s : (_root_.SheafOfModules.unit Y.ringCatSheaf).val.obj U)
    (α : (relativeDifferentials f).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    structureTwistedWedge f q U
        (connectionTmul f (_root_.SheafOfModules.unit Y.ringCatSheaf) U s α) ω =
      twistedTmul f (_root_.SheafOfModules.unit Y.ringCatSheaf) (q + 1) U s
        (relativeExteriorProduct f q U α ω) := by
  refine Eq.trans (congrArg ((structureFormsUnitor f (q + 1)).inv.val.app U)
    ((congrArg (fun z => relativeExteriorProduct f q U z ω)
        (structureConnectionUnitor_hom_app_connectionTmul f U s α)).trans
      (relativeExteriorProduct_smul_left f q U (Y.structureSectionScalar U s) α ω))) ?_
  exact structureFormsUnitor_inv_app_smul f (q + 1) U s
    (relativeExteriorProductOnSpace f q U α ω)

/-! ### The twisted de Rham differential -/

/-- Restriction of scalars along the structural map `f^{-1}𝒪_S ⟶ 𝒪_Y`, the change of rings the
terms of the twisted complex are read through. -/
abbrev twistedRestrictScalars :=
  _root_.SheafOfModules.restrictScalars
    (AlgebraicGeometry.SheafOfModules.underlyingRingHom (φ := inverseImageStructureMap f))

/-- **The twisted de Rham differential of the canonical connection on `𝒪_Y` in degree `q`**: the
relative de Rham differential `Ω^q_{Y/S} ⟶ Ω^{q+1}_{Y/S}` conjugated by the left unit
constraints, as a morphism of sheaves of `f^{-1}𝒪_S`-modules. -/
def structureTwistedDifferential (q : ℕ) :
    twistedTerm f (_root_.SheafOfModules.unit Y.ringCatSheaf) q ⟶
      twistedTerm f (_root_.SheafOfModules.unit Y.ringCatSheaf) (q + 1) :=
  (twistedRestrictScalars f).map (structureFormsUnitor f q).hom ≫
    (deRhamComplex f).d q (q + 1) ≫
      (twistedRestrictScalars f).map (structureFormsUnitor f (q + 1)).inv

/-- The twisted de Rham differential of the canonical connection acts on a local section by the
relative de Rham differential, read through the left unit constraints. -/
theorem structureTwistedDifferential_app (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (x : (twistedForms f (_root_.SheafOfModules.unit Y.ringCatSheaf) q).val.obj U) :
    (structureTwistedDifferential f q).val.app U x =
      (structureFormsUnitor f (q + 1)).inv.val.app U
        (relativeDeRhamDifferentialSection f q U
          ((structureFormsUnitor f q).hom.val.app U x)) := rfl

/-- **The Leibniz rule `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`** for the twisted de Rham differential of
the canonical connection on `𝒪_Y`.  On a pure tensor the left unit constraint is scalar
multiplication, so the statement is the Leibniz rule
`AlgebraicGeometry.Scheme.Hom.relativeDeRhamDifferentialSection_smul` for the relative de Rham
differential, pushed back through the constraint. -/
theorem structureTwistedDifferential_twistedTmul (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (s : (_root_.SheafOfModules.unit Y.ringCatSheaf).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (structureTwistedDifferential f q).val.app U
        (twistedTmul f (_root_.SheafOfModules.unit Y.ringCatSheaf) q U s ω) =
      structureTwistedWedge f q U ((structureModuleConnection f).d U s) ω +
        twistedTmul f (_root_.SheafOfModules.unit Y.ringCatSheaf) (q + 1) U s
          (relativeDeRhamDifferentialSection f q U ω) := by
  have hwedge : structureTwistedWedge f q U ((structureModuleConnection f).d U s) ω =
      (structureFormsUnitor f (q + 1)).inv.val.app U
        (relativeExteriorProduct f q U ((universalRelativeDerivation f).d (X := U) s) ω) := by
    refine congrArg ((structureFormsUnitor f (q + 1)).inv.val.app U) ?_
    refine congrArg (fun z => relativeExteriorProduct f q U z ω) ?_
    refine (structureConnectionUnitor_hom_app_connectionTmul f U (Y.structureUnitSection U)
      ((universalRelativeDerivation f).d (X := U) s)).trans ?_
    exact structureSectionScalar_structureUnitSection_smul f U
      ((universalRelativeDerivation f).d (X := U) s)
  have hsecond := structureFormsUnitor_inv_app_smul f (q + 1) U s
    (relativeDeRhamSectionOnSpace f q U ω)
  refine Eq.trans ?_ (congrArg₂ (· + ·) hwedge.symm hsecond)
  refine (structureTwistedDifferential_app f q U _).trans ?_
  refine Eq.trans (congrArg ((structureFormsUnitor f (q + 1)).inv.val.app U)
    ((congrArg (relativeDeRhamDifferentialSection f q U)
        (structureFormsUnitor_hom_app_twistedTmul f q U s ω)).trans
      (relativeDeRhamDifferentialSection_smul f q U (Y.structureSectionScalar U s) ω))) ?_
  exact map_add ((structureFormsUnitor f (q + 1)).inv.val.app U).hom _ _

/-- **The twisted de Rham differential of the canonical connection on the structure sheaf.**  The
wedge pairing is the exterior product of relative differential forms read through the left unit
constraints, and the differential is the relative de Rham differential of [Stacks, Tag 0FKQ]
conjugated by them.  This is a witness that
`AlgebraicGeometry.Scheme.Hom.TwistedDeRhamDifferential` is inhabited. -/
def structureTwistedDeRhamDifferential :
    TwistedDeRhamDifferential (structureModuleConnection f) where
  wedge q U η ω := structureTwistedWedge f q U η ω
  wedge_add q U η η' ω := structureTwistedWedge_add f q U η η' ω
  wedge_restrict q {_ _} k η ω := structureTwistedWedge_restrict f q k η ω
  wedge_tmul q U s α ω := structureTwistedWedge_connectionTmul f q U s α ω
  d q := structureTwistedDifferential f q
  d_tmul q U s ω := structureTwistedDifferential_twistedTmul f q U s ω

/-- **A twisted de Rham differential exists**: the canonical connection on the structure sheaf of
`Y` relative to any `f : Y ⟶ S` carries one.  So
`AlgebraicGeometry.Scheme.Hom.TwistedDeRhamDifferential` is not a vacuous notion, and neither is
any statement quantified over a sheaf of modules with connection and a twisted de Rham
differential for it. -/
theorem nonempty_structureTwistedDeRhamDifferential :
    Nonempty (TwistedDeRhamDifferential (structureModuleConnection f)) :=
  ⟨structureTwistedDeRhamDifferential f⟩

/-! ### Square-zero and integrability -/

/-- **A composite of conjugates vanishes when the composite of the conjugated morphisms does.**
Stated in an arbitrary category with zero morphisms, which is what lets it be proved by `rw`:
the goal of `structureTwistedDeRhamDifferential_isComplex` mentions the sheaves of
`f^{-1}𝒪_S`-modules of the twisted complex and is for that reason not type-correct at the
transparency `rw` type-checks its rewrites at. -/
theorem comp_eq_zero_of_conjugate {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A A' B B' D D' : C} (a : A ≅ A') (b : B ≅ B') (c : D ≅ D') (u : A' ⟶ B') (v : B' ⟶ D')
    (h : u ≫ v = 0) :
    (a.hom ≫ u ≫ b.inv) ≫ (b.hom ≫ v ≫ c.inv) = 0 := by
  rw [Category.assoc, Category.assoc, ← Category.assoc b.inv, Iso.inv_hom_id,
    Category.id_comp, ← Category.assoc u, h, Limits.zero_comp, Limits.comp_zero]

/-- **The twisted de Rham sequence of the canonical connection on `𝒪_Y` is a complex**:
consecutive twisted differentials compose to zero.  The two left unit constraints in the middle
cancel and what is left is the square-zero property of the relative de Rham complex. -/
theorem structureTwistedDeRhamDifferential_isComplex :
    (structureTwistedDeRhamDifferential f).IsComplex := fun q =>
  comp_eq_zero_of_conjugate ((twistedRestrictScalars f).mapIso (structureFormsUnitor f q))
    ((twistedRestrictScalars f).mapIso (structureFormsUnitor f (q + 1)))
    ((twistedRestrictScalars f).mapIso (structureFormsUnitor f (q + 1 + 1)))
    ((deRhamComplex f).d q (q + 1)) ((deRhamComplex f).d (q + 1) (q + 1 + 1))
    ((deRhamComplex f).d_comp_d q (q + 1) (q + 1 + 1))

/-- **The canonical connection on the structure sheaf is integrable**, [Stacks, Tag 07I0]: its
curvature vanishes.  So `AlgebraicGeometry.Scheme.Hom.ModuleConnection.IsIntegrable` is not a
vacuous notion. -/
theorem isIntegrable_structureModuleConnection :
    (structureModuleConnection f).IsIntegrable (structureTwistedDeRhamDifferential f) :=
  (structureTwistedDeRhamDifferential_isComplex f).isIntegrable

end AlgebraicGeometry.Scheme.Hom

end

end
