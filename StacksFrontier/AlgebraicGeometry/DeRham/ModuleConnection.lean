module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# Connections on a sheaf of modules over a scheme, and the twisted de Rham complex

Let `f : Y ⟶ S` be a morphism of schemes and let `ℱ` be a sheaf of `𝒪_Y`-modules.  A
*connection on `ℱ` relative to `f`* is an additive, restriction-compatible map

`∇ : ℱ ⟶ ℱ ⊗_{𝒪_Y} Ω_{Y/S}`

obeying the Leibniz rule `∇(b · s) = b · ∇(s) + s ⊗ d b`, where `d` is the universal relative
derivation `𝒪_Y ⟶ Ω_{Y/S}`.  This is the sheaf-theoretic form of [Stacks, Tag 07I0], whose
ring-level form `Crystalline.Connection` the crystalline tree already has; it is the notion in
which the module-with-connection of [Stacks, Tag 07MW] and of [Stacks, Tag 07MZ] is stated, and
the notion the twisted de Rham complex `ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}` is built from.

The twisted de Rham complex is the complex

`ℱ ⟶ ℱ ⊗ Ω^1_{Y/S} ⟶ ℱ ⊗ Ω^2_{Y/S} ⟶ ⋯`

whose differential is the unique extension of `∇` to all degrees satisfying the Leibniz rule
`d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`.  That differential, and not merely the shape of the terms, is
what the complex *is*: `TwistedDeRhamDifferential` carries it together with exactly that rule, so
every statement made about `twistedDeRhamComplex` is a statement about the genuine twisted
complex and not about an arbitrary complex whose terms happen to be `ℱ ⊗ Ω^q_{Y/S}`.

## Main definitions

Everything lives in the namespace `AlgebraicGeometry.Scheme.Hom`.

* `moduleConnectionTarget` — `ℱ ⊗_{𝒪_Y} Ω_{Y/S}`, the target of a connection, and
  `connectionTmul` the image of a pure tensor of local sections in it.
* `twistedForms` — `ℱ ⊗_{𝒪_Y} Ω^q_{Y/S}` as a sheaf of `𝒪_Y`-modules, `twistedTmul` the image
  of a pure tensor of local sections in it, and `twistedTerm` the same sheaf read as a sheaf of
  `f^{-1}𝒪_S`-modules, which is where the twisted differential is linear.
* `relativeDeRhamDifferentialSection` — the relative de Rham differential
  `Ω^q_{Y/S} ⟶ Ω^{q+1}_{Y/S}` of [Stacks, Tag 0FKQ] on local sections.
* `relativeExteriorProduct` — the exterior product `α ∧ ω` of a relative differential with a
  relative `q`-form, taken through the degree-one generator `Ω_{Y/S} ⟶ Ω^1_{Y/S}`.
* `ModuleConnection` — **a connection on a sheaf of modules over a scheme**,
  [Stacks, Tag 07I0] at the sheaf level.
* `TwistedDeRhamDifferential` — **the twisted de Rham differential of `(ℱ, ∇)`**: the
  differential of `ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}` in every degree, pinned by the Leibniz rule
  `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`, together with the wedge pairing that rule refers to.
* `TwistedDeRhamDifferential.IsComplex` — the condition that consecutive twisted differentials
  compose to zero.
* `ModuleConnection.IsIntegrable` — **integrability of a connection**, the vanishing of its
  curvature, [Stacks, Tag 07I0].
* `twistedDeRhamComplex` — **the twisted de Rham complex `ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}`**, as a
  `CochainComplex` of sheaves of `f^{-1}𝒪_S`-modules on `Y`.

## Main results

* `ModuleConnection.ext` — a connection is determined by its values on local sections.
* `TwistedDeRhamDifferential.IsComplex.isIntegrable` — a twisted differential whose consecutive
  composites vanish is in particular the differential of an integrable connection.
* `twistedDeRhamComplex_X`, `twistedDeRhamComplex_d` and `twistedDeRhamComplex_d_tmul` — the
  specification of the twisted complex: its degree-`q` term is `ℱ ⊗ Ω^q_{Y/S}`, its arrow out of
  degree `q` is the given twisted differential, and that arrow obeys the Leibniz rule.

## What is and is not proved

**Nothing here asserts that a twisted de Rham differential exists, or that there is only one.**
Both are true and both are open in this library:

* *Existence.*  The candidate rule `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω` is balanced over `𝒪_Y` —
  moving a scalar across the tensor sign costs `s ⊗ d b ∧ ω` on the left by the Leibniz rule for
  `∇` and the same on the right by the Leibniz rule for the de Rham differential, and the two
  cancel.  That is the computation carried out at the level of a single ring by
  `Crystalline.connectionFormPair_balance`, and running it over a scheme needs the balanced
  presheaf-level pairing to be pushed through the sheafification that defines
  `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`.  That step is not taken here.
* *Uniqueness.*  Local sections of `ℱ ⊗_{𝒪_Y} Ω^q_{Y/S}` are locally sums of pure tensors, so
  two twisted differentials agree locally, hence agree.  The ingredient is the analogue of
  `Stacks.SheafOfModules.OnSpace.tensor_hom_ext` for a morphism out of the *restriction of
  scalars* of a tensor product, which the library does not have: that lemma is stated for a
  morphism of sheaves of `𝒪_Y`-modules, and the twisted differential is only
  `f^{-1}𝒪_S`-linear.

Because of this the constructions below take a `TwistedDeRhamDifferential` as an argument rather
than producing one, and `twistedDeRhamComplex` additionally takes the square-zero condition
`TwistedDeRhamDifferential.IsComplex`, which in the source follows from integrability of `∇` and
is not derived here.  This is the honest shape: a statement quantified over every twisted
differential is a statement about *the* twisted differential, since the Leibniz rule pins it.

Nor is the notion shown to be inhabited for any particular `ℱ`.  The crystalline tree's
`Crystalline.GlobalCrystallineSituation.structureSheafConnection` is the ring-level connection of
[Stacks, Tag 07J6] on sections over one object of a crystalline site, and transporting it or the
universal derivation of `Y` into a `ModuleConnection` is not done here.

## Implementation notes

The tensor product is `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, the sheafified
tensor product of [Stacks, Tag 01CA], used directly rather than through the monoidal structure
`Stacks.SheafOfModules.OnSpace.monoidal` that it is the tensor product of, so that no monoidal
instance has to be in scope for a statement about a connection to be read.  Local sections of a
tensor product are named by `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`,
the canonical map `ℱ(U) ⊗_{𝒪_Y(U)} 𝒢(U) → (ℱ ⊗ 𝒢)(U)`; a general local section of the
sheafified tensor product is only *locally* a sum of such, which is why the Leibniz rule for the
twisted differential is stated on them and the wedge pairing is carried as data.

A connection is additive and restriction-compatible but *not* `𝒪_Y`-linear — already the Leibniz
rule in degree zero forbids that — so it is given as a family of additive maps on sections
together with its compatibility with restriction, rather than as a morphism in a category of
sheaves of `𝒪_Y`-modules.  The twisted differential, by contrast, *is* linear over
`f^{-1}𝒪_S`, exactly as the untwisted de Rham differential of
`AlgebraicGeometry.Scheme.Hom.deRhamComplex` is, and so is given as a morphism of sheaves of
`f^{-1}𝒪_S`-modules between the `twistedTerm`s.

The connection takes values in `ℱ ⊗ Ω_{Y/S}`, as the source writes it, whereas the degree-one
term of the de Rham complex is the first exterior power `Ω^1_{Y/S}`.  The degree-one generator
`Ω_{Y/S} ⟶ Ω^1_{Y/S}` of the exterior algebra therefore appears in the Leibniz rule, inside
`relativeExteriorProduct`; this is the same arrangement as in the crystalline tree.

Degrees of differential forms are integers, while the de Rham complex is indexed by `ℕ`, so a
transport along `1 + q = q + 1` in `ℤ` is part of the exterior product.  It is
`transportDifferentialForm`, which renames a degree and does not touch the section.

## References

* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01US](https://stacks.math.columbia.edu/tag/01US)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {Y S : Scheme.{u}} (f : Y ⟶ S) (F : Y.Modules)

/-! ### The sheaves the connection and the twisted complex live on -/

/-- `ℱ ⊗_{𝒪_Y} Ω_{Y/S}`, the target of a connection on `ℱ` relative to `f : Y ⟶ S`. -/
abbrev moduleConnectionTarget : Y.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩).obj (F)).obj
    ((relativeDifferentials f)))

/-- The image in `(ℱ ⊗_{𝒪_Y} Ω_{Y/S})(U)` of a pure tensor `s ⊗ α` of a local section of `ℱ`
with a local relative differential. -/
abbrev connectionTmul (U : (Y.Opens)ᵒᵖ) (s : F.val.obj U)
    (α : (relativeDifferentials f).val.obj U) : (moduleConnectionTarget f F).val.obj U :=
  toTensorSheafSection Y.toRingedSpace F (relativeDifferentials f) U
    (s ⊗ₜ[Y.presheaf.obj U] α)

/-- `ℱ ⊗_{𝒪_Y} Ω^q_{Y/S}`, the degree-`q` term of the twisted de Rham complex, as a sheaf of
`𝒪_Y`-modules. -/
abbrev twistedForms (q : ℕ) : Y.Modules :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩).obj (F)).obj
    ((relativeDifferentialForms f (q : ℤ))))

/-- The image in `(ℱ ⊗_{𝒪_Y} Ω^q_{Y/S})(U)` of a pure tensor `s ⊗ ω` of a local section of `ℱ`
with a local relative `q`-form. -/
abbrev twistedTmul (q : ℕ) (U : (Y.Opens)ᵒᵖ) (s : F.val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (twistedForms f F q).val.obj U :=
  toTensorSheafSection Y.toRingedSpace F (relativeDifferentialForms f (q : ℤ)) U
    (s ⊗ₜ[Y.presheaf.obj U] ω)

/-- `ℱ ⊗_{𝒪_Y} Ω^q_{Y/S}` read as a sheaf of `f^{-1}𝒪_S`-modules, which is where the twisted de
Rham differential is linear: already in degree zero the Leibniz rule forbids `𝒪_Y`-linearity.
This is the same change of rings that the untwisted
`AlgebraicGeometry.Scheme.Hom.deRhamComplex` makes on its terms. -/
abbrev twistedTerm (q : ℕ) :
    _root_.SheafOfModules.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf)) :=
  (_root_.SheafOfModules.restrictScalars
    (AlgebraicGeometry.SheafOfModules.underlyingRingHom
      (φ := inverseImageStructureMap f))).obj (twistedForms f F q)

/-! ### The de Rham differential and the exterior product on local sections -/

/-- Transport a local relative differential form along an equality of degrees.  This renames the
degree and does not change the section. -/
def transportDifferentialForm {i j : ℤ} (h : i = j) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms f i).val.obj U) :
    (relativeDifferentialForms f j).val.obj U :=
  h ▸ ω

/-- The relative de Rham differential `Ω^q_{Y/S} ⟶ Ω^{q+1}_{Y/S}` of [Stacks, Tag 0FKQ], read on
local sections. -/
def relativeDeRhamDifferentialSection (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).val.obj U :=
  ((deRhamComplex f).d q (q + 1)).val.app U ω

/-- The exterior product `α ∧ ω` of a local relative differential with a local relative
`q`-form: the image of `α` under the degree-one generator `Ω_{Y/S} ⟶ Ω^1_{Y/S}` of the exterior
algebra, multiplied with `ω` in the algebra `Ω^•_{Y/S}` of relative differential forms. -/
def relativeExteriorProduct (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (α : (relativeDifferentials f).val.obj U)
    (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (relativeDifferentialForms f ((q + 1 : ℕ) : ℤ)).val.obj U :=
  transportDifferentialForm f (show (1 : ℤ) + (q : ℤ) = ((q + 1 : ℕ) : ℤ) by push_cast; ring) U
    (((relativeDifferentialFormsAlgebra f).mul 1 (q : ℤ)).app U
      ((Scheme.Modules.exteriorGenerator (relativeDifferentials f)).val.app U α) ω)

/-! ### Connections -/

/-- **A connection on a sheaf of modules over a scheme**, the sheaf-theoretic form of
[Stacks, Tag 07I0].  For `f : Y ⟶ S` a morphism of schemes and `ℱ` a sheaf of `𝒪_Y`-modules it
is a map

`∇ : ℱ ⟶ ℱ ⊗_{𝒪_Y} Ω_{Y/S}`

given by additive maps on local sections, compatible with restriction, and satisfying the
Leibniz rule `∇(b · s) = b · ∇(s) + s ⊗ d b` for every local function `b` on `Y`, where `d` is
the universal relative derivation `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation`.

The Leibniz rule is the reason the data is a family of additive maps rather than a morphism of
sheaves of `𝒪_Y`-modules: a connection is not `𝒪_Y`-linear.  It *is* linear over `f^{-1}𝒪_S`,
since the universal relative derivation kills the image of `f^{-1}𝒪_S`, but that consequence is
not recorded here.

This is a bundle of data, not an assertion, and carries no tag attribute. -/
structure ModuleConnection where
  /-- The connection on local sections, an additive map `ℱ(U) ⟶ (ℱ ⊗ Ω_{Y/S})(U)`. -/
  d (U : (Y.Opens)ᵒᵖ) : F.val.obj U →+ (moduleConnectionTarget f F).val.obj U
  /-- The connection commutes with restriction to a smaller open. -/
  d_restrict {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V) (s : F.val.obj U) :
    (moduleConnectionTarget f F).val.map k (d U s) = d V (F.val.map k s)
  /-- **The Leibniz rule** `∇(b · s) = b · ∇(s) + s ⊗ d b`. -/
  leibniz (U : (Y.Opens)ᵒᵖ) (b : Y.ringCatSheaf.obj.obj U) (s : F.val.obj U) :
    d U (b • s) =
      b • d U s + connectionTmul f F U s ((universalRelativeDerivation f).d (X := U) b)

namespace ModuleConnection

variable {f F}

/-- A connection carries zero to zero. -/
@[simp] theorem map_zero (nabla : ModuleConnection f F) (U : (Y.Opens)ᵒᵖ) :
    nabla.d U 0 = 0 :=
  (nabla.d U).map_zero

/-- A connection is additive on local sections. -/
@[simp] theorem map_add (nabla : ModuleConnection f F) (U : (Y.Opens)ᵒᵖ)
    (s t : F.val.obj U) : nabla.d U (s + t) = nabla.d U s + nabla.d U t :=
  (nabla.d U).map_add s t

/-- **A connection is determined by its values on local sections.** -/
@[ext] theorem ext {nabla nabla' : ModuleConnection f F}
    (h : ∀ (U : (Y.Opens)ᵒᵖ) (s : F.val.obj U), nabla.d U s = nabla'.d U s) :
    nabla = nabla' := by
  obtain ⟨d₁, hr₁, hl₁⟩ := nabla
  obtain ⟨d₂, hr₂, hl₂⟩ := nabla'
  have hd : d₁ = d₂ := funext fun U => AddMonoidHom.ext (h U)
  subst hd
  rfl

end ModuleConnection

section Twisted

variable {f F}

/-! ### The twisted de Rham differential -/

/-- **The twisted de Rham differential of a sheaf of modules with connection.**  For
`∇ : ℱ ⟶ ℱ ⊗_{𝒪_Y} Ω_{Y/S}` a connection, this is the differential of the twisted de Rham
complex `ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}` in every degree, characterised by the Leibniz rule

`d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`

on local pure tensors, where the first term is the wedge of the value of the connection with the
form and the second the coefficient tensored with the relative de Rham differential of the form.

The wedge pairing that the rule refers to is carried as data, because the value `∇(s)` of the
connection is a local section of the *sheafified* tensor product `ℱ ⊗ Ω_{Y/S}` and need not be a
pure tensor: there is no formula for `∇(s) ∧ ω` in terms of sections alone.  The pairing is
nevertheless pinned, not chosen — it is additive in the value of the connection, commutes with
restriction, and on a pure tensor `s ⊗ α` is `s ⊗ (α ∧ ω)` — and local sections of a sheafified
tensor product are locally sums of pure tensors, so those three clauses determine it.  The
Leibniz rule then determines the differential by the same argument.

Square-zero is deliberately *not* a field: it is `IsComplex` below, and in the source it is a
consequence of integrability of `∇` rather than part of the definition of the differential.

This is a bundle of data, not an assertion, and carries no tag attribute. -/
structure TwistedDeRhamDifferential (nabla : ModuleConnection f F) where
  /-- Wedging a value of the connection with a local relative `q`-form. -/
  wedge (q : ℕ) (U : (Y.Opens)ᵒᵖ) : (moduleConnectionTarget f F).val.obj U →
    (relativeDifferentialForms f (q : ℤ)).val.obj U → (twistedForms f F (q + 1)).val.obj U
  /-- The wedge is additive in the value of the connection. -/
  wedge_add (q : ℕ) (U : (Y.Opens)ᵒᵖ) (η η' : (moduleConnectionTarget f F).val.obj U)
      (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    wedge q U (η + η') ω = wedge q U η ω + wedge q U η' ω
  /-- The wedge commutes with restriction to a smaller open. -/
  wedge_restrict (q : ℕ) {U V : (Y.Opens)ᵒᵖ} (k : U ⟶ V)
      (η : (moduleConnectionTarget f F).val.obj U)
      (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (twistedForms f F (q + 1)).val.map k (wedge q U η ω) =
      wedge q V ((moduleConnectionTarget f F).val.map k η)
        ((relativeDifferentialForms f (q : ℤ)).val.map k ω)
  /-- On a pure tensor the wedge is the exterior product of relative differential forms. -/
  wedge_tmul (q : ℕ) (U : (Y.Opens)ᵒᵖ) (s : F.val.obj U)
      (α : (relativeDifferentials f).val.obj U)
      (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    wedge q U (connectionTmul f F U s α) ω =
      twistedTmul f F (q + 1) U s (relativeExteriorProduct f q U α ω)
  /-- The differential `ℱ ⊗ Ω^q_{Y/S} ⟶ ℱ ⊗ Ω^{q+1}_{Y/S}`, a morphism of sheaves of
  `f^{-1}𝒪_S`-modules. -/
  d (q : ℕ) : twistedTerm f F q ⟶ twistedTerm f F (q + 1)
  /-- **The Leibniz rule** `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`. -/
  d_tmul (q : ℕ) (U : (Y.Opens)ᵒᵖ) (s : F.val.obj U)
      (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    (d q).val.app U (twistedTmul f F q U s ω) =
      wedge q U (nabla.d U s) ω +
        twistedTmul f F (q + 1) U s (relativeDeRhamDifferentialSection f q U ω)

namespace TwistedDeRhamDifferential

variable {nabla : ModuleConnection f F}

/-- **Consecutive twisted de Rham differentials compose to zero**, so that the twisted de Rham
sequence is a complex.  In the source this is a consequence of integrability of `∇`; see the
module documentation for why it is a hypothesis here. -/
def IsComplex (D : TwistedDeRhamDifferential nabla) : Prop :=
  ∀ q : ℕ, D.d q ≫ D.d (q + 1) = 0

end TwistedDeRhamDifferential

/-! ### Integrability -/

namespace ModuleConnection

/-- **Integrability of a connection on a sheaf of modules**, [Stacks, Tag 07I0]: the curvature
`∇¹ ∘ ∇` of `∇` vanishes.

The curvature is read off a twisted de Rham differential `D` of `∇`.  In degree zero the Leibniz
rule of `D` reads `D.d 0 (s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`, and the degree-zero forms are the
multiples of the unit of the exterior algebra, whose relative de Rham differential vanishes; so
`D.d 0` is `∇` itself read through the degree-zero identification `ℱ ⊗ Ω^0_{Y/S} ≅ ℱ` of
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsZeroIso`, and `D.d 0 ≫ D.d 1 = 0` is the
vanishing of `∇¹ ∘ ∇`.  That identification is not proved here, so the condition is stated on
`D` and not transported back to `∇`.

This is a `Prop`-valued definition and carries no tag attribute. -/
def IsIntegrable (nabla : ModuleConnection f F)
    (D : TwistedDeRhamDifferential nabla) : Prop :=
  D.d 0 ≫ D.d 1 = 0

end ModuleConnection

/-- A twisted de Rham differential whose consecutive composites all vanish is in particular the
differential of an integrable connection: integrability is the degree-zero composite. -/
theorem TwistedDeRhamDifferential.IsComplex.isIntegrable {nabla : ModuleConnection f F}
    {D : TwistedDeRhamDifferential nabla} (h : D.IsComplex) : nabla.IsIntegrable D :=
  h 0

/-! ### The twisted de Rham complex -/

/-- **The twisted de Rham complex `ℱ ⊗_{𝒪_Y} Ω^•_{Y/S}`** of a sheaf of modules with connection
on a scheme over `S`:

`ℱ ⟶ ℱ ⊗ Ω^1_{Y/S} ⟶ ℱ ⊗ Ω^2_{Y/S} ⟶ ⋯`,

a cochain complex of sheaves of `f^{-1}𝒪_S`-modules on `Y` whose degree-`q` term is
`ℱ ⊗_{𝒪_Y} Ω^q_{Y/S}` and whose differential is the twisted de Rham differential of `∇`,
pinned by the Leibniz rule `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`.

The terms are sheaves of `f^{-1}𝒪_S`-modules and not of `𝒪_Y`-modules for the same reason as in
the untwisted complex `AlgebraicGeometry.Scheme.Hom.deRhamComplex`: the differential is only
`f^{-1}𝒪_S`-linear.

The square-zero hypothesis is `TwistedDeRhamDifferential.IsComplex`; see the module
documentation. -/
def twistedDeRhamComplex (nabla : ModuleConnection f F)
    (D : TwistedDeRhamDifferential nabla) (hD : D.IsComplex) :
    CochainComplex (_root_.SheafOfModules.{u}
      (AlgebraicGeometry.SheafOfModules.underlyingRingSheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf))) ℕ :=
  CochainComplex.of (twistedTerm f F) D.d hD

/-- The degree-`q` term of the twisted de Rham complex is `ℱ ⊗_{𝒪_Y} Ω^q_{Y/S}`. -/
@[simp] theorem twistedDeRhamComplex_X (nabla : ModuleConnection f F)
    (D : TwistedDeRhamDifferential nabla) (hD : D.IsComplex) (q : ℕ) :
    (twistedDeRhamComplex nabla D hD).X q = twistedTerm f F q := rfl

/-- The arrow of the twisted de Rham complex out of degree `q` is the twisted de Rham
differential of `∇`. -/
@[simp] theorem twistedDeRhamComplex_d (nabla : ModuleConnection f F)
    (D : TwistedDeRhamDifferential nabla) (hD : D.IsComplex) (q : ℕ) :
    (twistedDeRhamComplex nabla D hD).d q (q + 1) = D.d q :=
  CochainComplex.of_d (twistedTerm f F) D.d q

/-- **The Leibniz rule for the twisted de Rham complex**: on a local pure tensor the arrow out of
degree `q` is `d(s ⊗ ω) = ∇(s) ∧ ω + s ⊗ d ω`.  This is what makes the complex above the twisted
de Rham complex of `(ℱ, ∇)` and not an arbitrary complex with the same terms. -/
theorem twistedDeRhamComplex_d_tmul (nabla : ModuleConnection f F)
    (D : TwistedDeRhamDifferential nabla) (hD : D.IsComplex) (q : ℕ) (U : (Y.Opens)ᵒᵖ)
    (s : F.val.obj U) (ω : (relativeDifferentialForms f (q : ℤ)).val.obj U) :
    ((twistedDeRhamComplex nabla D hD).d q (q + 1)).val.app U (twistedTmul f F q U s ω) =
      D.wedge q U (nabla.d U s) ω +
        twistedTmul f F (q + 1) U s (relativeDeRhamDifferentialSection f q U ω) := by
  rw [twistedDeRhamComplex_d]
  exact D.d_tmul q U s ω

end Twisted

end AlgebraicGeometry.Scheme.Hom

end

end
