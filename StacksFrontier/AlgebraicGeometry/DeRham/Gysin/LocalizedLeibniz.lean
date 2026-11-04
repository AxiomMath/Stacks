module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.LogarithmicDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.WedgeDifferential
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.WedgeRepeatedFactor

/-!
# Differentiating a form divided by an invertible function

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X`, let `Ω = Ω_{𝒪_X/A}` be the sheaf of relative
differentials and let `B` also denote a package of the three algebras of Stacks Section 17.21 for
`Ω`. This file proves, on local sections, the Leibniz rule for the de Rham differential against a
*scalar* factor,

`d (a · ω) = d a ∧ ω + a · d ω`,

the form it takes when the scalar is the inverse of an invertible local section,

`d (g⁻¹ · α) = -(g⁻² · (d g ∧ α)) + g⁻¹ · d α`,

and the consequence that differentiating the Gysin fraction of [Stacks, Tag 0G83] differentiates
its numerator alone:

`d ( (ω ∧ d f₁ ∧ ⋯ ∧ d f_c) / (f₁ ⋯ f_c) ) = ( d ω ∧ d f₁ ∧ ⋯ ∧ d f_c ) / (f₁ ⋯ f_c)`

over an open set on which the product `f₁ ⋯ f_c` is invertible — in particular over the principal
open `X.basicOpen (f₁ ⋯ f_c)`. This is step (ii-b) of the proof of [Stacks, Tag 0G85]: the error
term `d(g⁻¹) ∧ (ω ∧ d f₁ ∧ ⋯ ∧ d f_c)` produced by the Leibniz rule vanishes, because
`d(g⁻¹)` is a multiple of `d g` and `d g` is, for `g = f₁ ⋯ f_c`, a sum of multiples of the
`d f_j`, each of which already occurs in the wedge.

## Main definitions

* `AlgebraicGeometry.Scheme.equationsProductInv`: `(f₁ ⋯ f_c)⁻¹`, as a local section of `𝒪_X`
  over the principal open `X.basicOpen (f₁ ⋯ f_c)` on which the product of the equations is
  invertible. This is the denominator of the Gysin fraction, inverted on the largest open set on
  which that makes sense.

## Main results

* `AlgebraicGeometry.SheafOfModules.exactOne_of_mul_eq_one` and
  `AlgebraicGeometry.SheafOfModules.exactOne_inv`: **the exact differential of an inverse**,
  `d (g⁻¹) = -g⁻² · d g`, stated both for a one-sided inverse and for a unit.
* `AlgebraicGeometry.SheafOfModules.d_smul`: **the Leibniz rule against a scalar**,
  `d (a · ω) = d a ∧ ω + a · d ω`.
* `AlgebraicGeometry.SheafOfModules.d_inv_smul`: the same rule for the inverse of a unit,
  `d (g⁻¹ · α) = -(g⁻² · (d g ∧ α)) + g⁻¹ · d α`.
* `AlgebraicGeometry.SheafOfModules.d_smul_of_formProduct_exactOne_eq_zero` and
  `AlgebraicGeometry.SheafOfModules.d_smul_of_mul_eq_one`: **`d` commutes with dividing by `g`
  as soon as `d g` kills the form**, the second being the form in which the error term is
  discharged through an inverse.
* `AlgebraicGeometry.SheafOfModules.d_smul_formProduct_prodDegOne_of_mul_eq_one`: **the
  differential of the Gysin fraction**, `d (v · (ω ∧ d b₁ ∧ ⋯ ∧ d b_c)) =
  v · (d ω ∧ d b₁ ∧ ⋯ ∧ d b_c)` whenever `v` is an inverse of `b₁ ⋯ b_c`.
* `AlgebraicGeometry.Scheme.Hom.d_smul_equationsWedge_of_mul_eq_one` and
  `AlgebraicGeometry.Scheme.Hom.d_smul_equationsWedge_basicOpen`: the same statement for a
  morphism of schemes and global equations, phrased with
  `AlgebraicGeometry.Scheme.Hom.equationsWedge`, over an arbitrary open set on which the product
  of the equations is invertible and over the principal open of that product.

## Implementation notes

**What the Leibniz rule against a scalar is read off.** A de Rham differential is only required
to obey `d (b · d b₁ ∧ ⋯ ∧ d bₚ) = d b ∧ d b₁ ∧ ⋯ ∧ d bₚ` on multiples of *exact wedges*
(`AlgebraicGeometry.SheafOfModules.DeRhamDifferential.generator`), so for an arbitrary local
`p`-form the scalar rule is not part of that data. It is instead the `q = 0` case of the graded
Leibniz rule `AlgebraicGeometry.SheafOfModules.d_formProduct`, which is unconditional: writing
`a · ω = ω ∧ (a · 1)` with the unit of the exterior algebra in degree zero gives
`d (a · ω) = d ω ∧ (a · 1) + (-1)^p ω ∧ d (a · 1)`, the second factor of the first summand is
again a scalar by the unit law, and `d (a · 1) = d a` is
`AlgebraicGeometry.SheafOfModules.deRhamComplex_degreeZero`. That produces the *right-handed*
rule `d (a · ω) = a · d ω + (-1)^p (ω ∧ d a)`, and graded commutativity
`AlgebraicGeometry.SheafOfModules.formProduct_comm` turns `(-1)^p (ω ∧ d a)` into `d a ∧ ω`, the
two signs cancelling. The degree `q = 0` is chosen rather than `p = 0` because `p + 0`, `p + 1 + 0`
and `p + (0 + 1)` all reduce to `p` and `p + 1` definitionally in `ℕ`, so no transport along
`Nat.zero_add` is needed and the reindexing isomorphisms of the complex act trivially.

**The value of the differential is passed as an argument.** Each statement below takes a local
section `dω` of `⋀^{p+1} Ω` together with the hypothesis `d ω = dω` rather than writing
`d ω` inside the conclusion. The reason is bookkeeping, not generality: the terms of the de Rham
complex are the exterior powers with their scalars restricted along `φ`, so
`d.val.app U ω` is a section of a sheaf of `A`-modules, and the `𝒪_X`-action by a local section
`a` of the structure sheaf is not found on it by instance resolution even though the two modules
have the same underlying abelian group. Instantiating `dω := d ω` and `hdω := rfl` recovers the
expected reading of every statement, and that is how the scheme-level results below are proved.
The `reindexForm` of
`StacksFrontier/AlgebraicGeometry/DeRham/CupProduct/GradedCommutativity.lean` is used in place of
`HomologicalComplex.XIsoOfEq` for the same reason, the two agreeing by
`AlgebraicGeometry.SheafOfModules.reindexForm_heq`.

**Invertibility, and how the principal open enters.** The hypothesis carried by every statement
about a fraction is a *one-sided inverse in the ring of local sections*: a local section `v` of
`𝒪_X` over `U` with `g · v = 1`, equivalently the invertibility of `g` in `Γ(U, 𝒪_X)`. No
localization of a module appears, because none is needed: over an open set on which `g` is a
unit, dividing by `g` *is* multiplication by `v`, and the localized module of the Gysin formula
is the module of sections itself. The principal open is the instance of this that the Gysin map
is used over: for `g = f₁ ⋯ f_c` a global function, `g` is invertible on
`X.basicOpen (f₁ ⋯ f_c)` by `AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`, which is what
`AlgebraicGeometry.Scheme.equationsProductInv` packages and
`AlgebraicGeometry.Scheme.Hom.d_smul_equationsWedge_basicOpen` consumes. Stating the results with
`g · v = 1` rather than with `X.basicOpen` is strictly more general and is what makes them usable
on a member of an arbitrary trivializing cover.

**Carried hypotheses.** Beyond the inverse, none. Every statement in the first section holds for
an arbitrary package `B` of the three algebras for the sheaf of relative differentials of an
arbitrary `φ : A ⟶ 𝒪_X` and an arbitrary de Rham differential `D` on it, and at the scheme level
for an arbitrary morphism `π : X ⟶ S` and an arbitrary family of global equations. In particular
nothing here needs the equations to cut out a closed subscheme of the expected codimension, or
to be a regular sequence.

**What is not reached.** Only the identity between local sections is proved. The Gysin map itself
is valued in a local cohomology sheaf, and the comparison carrying this identity into that sheaf
is part (2) of [Stacks, Tag 0G74], recorded as missing in the implementation notes of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/WedgeDifferential.lean`; nothing about it is proved
here.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G83](https://stacks.math.columbia.edu/tag/0G83)
* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
* [Stacks Project, Tag 0G74](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### Bookkeeping

The wedge product is `𝒪_X`-bilinear and has the unit of the exterior algebra as a two-sided unit;
the five helpers below are the instances of those facts that the Leibniz rule needs, in the
degree-normalized spelling `AlgebraicGeometry.SheafOfModules.formProduct`. -/

/-- The wedge product negates with its left factor: the case `a = -1` of
`AlgebraicGeometry.SheafOfModules.formProduct_smul_left`. -/
private theorem formProduct_neg_left (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower q).val.obj U) :
    formProduct B p q U (-ω) η = -formProduct B p q U ω η := by
  simpa only [neg_one_smul] using formProduct_smul_left B p q U (-1 : X.sheaf.obj.obj U) ω η

/-- The unit of the exterior algebra is a unit on the right, in the degree-normalized spelling:
the degree `p + 0` is `p` definitionally, so no transport is left over. -/
private theorem formProduct_one_right (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) :
    formProduct B p 0 U ω (B.exterior.one.eval U) = ω :=
  eq_of_heq (B.exterior.mul_one (p : ℤ) U ω)

/-- Wedging a `p`-form with the degree-zero form `a · 1` is scaling it by `a`. -/
private theorem formProduct_scalar_right (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (a : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U) :
    formProduct B p 0 U ω (a • B.exterior.one.eval U) = a • ω :=
  ((B.exterior.mul (p : ℤ) ((0 : ℕ) : ℤ)).map_smul_right U a ω (B.exterior.one.eval U)).trans
    (congrArg (fun z => a • z) (formProduct_one_right B p U ω))

/-- Reindexing a form commutes with negation. -/
private theorem reindexForm_neg {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower m).val.obj U) :
    reindexForm B h U (-x) = -reindexForm B h U x := by
  subst h
  rfl

/-- **Moving a degree-one factor from the right of a `p`-form to its left** costs the sign
`(-1)^p`, which therefore cancels against a factor `(-1)^p` already present. This is graded
commutativity `AlgebraicGeometry.SheafOfModules.formProduct_comm` in the case `q = 1`, together
with `(-1)^p (-1)^p = 1`. -/
private theorem neg_one_pow_smul_formProduct_comm (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (B.exteriorPower p).val.obj U) (η : (B.exteriorPower 1).val.obj U) :
    (-1 : ℤ) ^ p • formProduct B p 1 U ω η =
      reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U η ω) := by
  rw [formProduct_comm B p 1 U ω η, smul_smul, mul_one, ← pow_add,
    Even.neg_one_pow ⟨p, rfl⟩, one_smul]

/-! ### The exact differential of an inverse -/

/-- **The exact differential of an inverse:** `d v = -v² · d g` for local sections `g` and `v` of
the structure sheaf with `g v = 1`.

Differentiating `g v = 1` gives `g · d v + v · d g = 0` by the Leibniz rule
`AlgebraicGeometry.SheafOfModules.exactOne_mul` and `d 1 = 0`; multiplying by `v` and using
`v g = 1` again isolates `d v`. -/
theorem exactOne_of_mul_eq_one (U : (Opens X.carrier)ᵒᵖ) {g v : X.sheaf.obj.obj U}
    (hgv : g * v = 1) : exactOne B U v = -((v * v) • exactOne B U g) := by
  have hmul := exactOne_mul B U g v
  rw [hgv, exactOne_one] at hmul
  calc exactOne B U v
      = (v * g) • exactOne B U v := by
        rw [show v * g = 1 from (mul_comm v g).trans hgv, one_smul]
    _ = v • (g • exactOne B U v) := mul_smul _ _ _
    _ = -((v * v) • exactOne B U g) := by
        rw [eq_neg_iff_add_eq_zero.mpr hmul.symm, smul_neg, smul_smul]

/-- **The exact differential of the inverse of a unit:** `d (u⁻¹) = -u⁻² · d u`. -/
theorem exactOne_inv (U : (Opens X.carrier)ᵒᵖ) (u : (X.sheaf.obj.obj U)ˣ) :
    exactOne B U (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val =
      -(((u⁻¹ : (X.sheaf.obj.obj U)ˣ).val * (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val) •
        exactOne B U u.val) :=
  exactOne_of_mul_eq_one B U u.mul_inv

variable (D : DeRhamDifferential B)

/-- The canonical isomorphism between two terms of the de Rham complex of equal degree acts
trivially on local sections: a section of the source and one of the target which are
heterogeneously equal correspond. -/
private theorem XIsoOfEq_app_eq {m n : ℕ} (h : m = n) (U : (Opens X.carrier)ᵒᵖ)
    (x : (B.exteriorPower m).val.obj U) (y : (B.exteriorPower n).val.obj U) (hxy : HEq x y) :
    ((deRhamComplex B D).XIsoOfEq h).hom.val.app U x = y := by
  subst h
  cases eq_of_heq hxy
  rw [HomologicalComplex.XIsoOfEq_rfl]
  rfl

/-- **The right-handed Leibniz rule against a scalar:** `d (a · ω) = a · d ω + (-1)^p (ω ∧ d a)`.

This is the graded Leibniz rule `AlgebraicGeometry.SheafOfModules.d_formProduct` in the case
`q = 0`, applied to `ω` and the degree-zero form `a · 1`: the product `ω ∧ (a · 1)` is `a · ω` by
the unit law, and `d (a · 1) = d a` by the de Rham rule in degree zero. Every degree occurring is
definitionally `p` or `p + 1`, so the reindexing isomorphisms of the complex act trivially. -/
private theorem d_smul_right (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (a : X.sheaf.obj.obj U)
    (ω : (B.exteriorPower p).val.obj U) (dω : (B.exteriorPower (p + 1)).val.obj U)
    (hdω : ((deRhamComplex B D).d p (p + 1)).val.app U ω = dω) :
    ((deRhamComplex B D).d p (p + 1)).val.app U (a • ω) =
      (-1 : ℤ) ^ p • formProduct B p 1 U ω (exactOne B U a) + a • dω := by
  refine ((congrArg (fun z => ((deRhamComplex B D).d p (p + 1)).val.app U z)
      (formProduct_scalar_right B p U a ω).symm).trans
    (d_formProduct B D p 0 U ω (a • B.exterior.one.eval U))).trans ?_
  refine (congrArg₂ (· + ·) ?_ ?_).trans (add_comm _ _)
  · exact XIsoOfEq_app_eq B D _ U _ (a • dω)
      (heq_of_eq ((congrArg
        (fun z : (B.exteriorPower (p + 1)).val.obj U =>
          formProduct B (p + 1) 0 U z (a • B.exterior.one.eval U)) hdω).trans
        (formProduct_scalar_right B (p + 1) U a dω)))
  · exact congrArg (fun z => (-1 : ℤ) ^ p • z)
      (XIsoOfEq_app_eq B D _ U _ (formProduct B p 1 U ω (exactOne B U a))
        (heq_of_eq (congrArg (fun z : (B.exteriorPower 1).val.obj U => formProduct B p 1 U ω z)
          (eq_of_heq (deRhamComplex_degreeZero B D U a)))))

/-! ### The Leibniz rule against a scalar -/

/-- The exact differential of an inverse wedged with a form: if `g v = 1` then
`d v ∧ ω = -(v² · (d g ∧ ω))`. -/
private theorem formProduct_exactOne_of_mul_eq_one (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    {g v : X.sheaf.obj.obj U} (hgv : g * v = 1) (ω : (B.exteriorPower p).val.obj U) :
    formProduct B 1 p U (exactOne B U v) ω =
      -((v * v) • formProduct B 1 p U (exactOne B U g) ω) := by
  rw [exactOne_of_mul_eq_one B U hgv, formProduct_neg_left, formProduct_smul_left]

/-- **The Leibniz rule against a scalar:** `d (a · ω) = d a ∧ ω + a · d ω`, for a local section
`a` of the structure sheaf and an arbitrary local `p`-form `ω`.

The exact one-form `d a` is `AlgebraicGeometry.SheafOfModules.exactOne`, and `d a ∧ ω` lives in
exterior degree `1 + p`, which is reindexed to the degree `p + 1` of the complex. The section
`dω` together with `hdω` is the value `d ω`; see the implementation notes. -/
theorem d_smul (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (a : X.sheaf.obj.obj U)
    (ω : (B.exteriorPower p).val.obj U) (dω : (B.exteriorPower (p + 1)).val.obj U)
    (hdω : ((deRhamComplex B D).d p (p + 1)).val.app U ω = dω) :
    ((deRhamComplex B D).d p (p + 1)).val.app U (a • ω) =
      reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U a) ω) + a • dω := by
  rw [d_smul_right B D p U a ω dω hdω,
    neg_one_pow_smul_formProduct_comm B p U ω (exactOne B U a)]

/-- **The Leibniz rule for the inverse of a unit:** `d (u⁻¹ · α) = -(u⁻² · (d u ∧ α)) + u⁻¹ · dα`.

This is `AlgebraicGeometry.SheafOfModules.d_smul` with the scalar `u⁻¹`, whose exact differential
is computed by `AlgebraicGeometry.SheafOfModules.exactOne_inv`. It is the form the rule takes on
the Gysin fraction, whose denominator is a product of equations: the whole error term is a
multiple of `d u ∧ α`, so it suffices to know that *that* vanishes. -/
theorem d_inv_smul (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (u : (X.sheaf.obj.obj U)ˣ)
    (α : (B.exteriorPower p).val.obj U) (dα : (B.exteriorPower (p + 1)).val.obj U)
    (hdα : ((deRhamComplex B D).d p (p + 1)).val.app U α = dα) :
    ((deRhamComplex B D).d p (p + 1)).val.app U ((u⁻¹ : (X.sheaf.obj.obj U)ˣ).val • α) =
      -(((u⁻¹ : (X.sheaf.obj.obj U)ˣ).val * (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val) •
          reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U u.val) α)) +
        (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val • dα := by
  have hinner : reindexForm B (Nat.add_comm 1 p) U
        (formProduct B 1 p U (exactOne B U (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val) α) =
      -(((u⁻¹ : (X.sheaf.obj.obj U)ˣ).val * (u⁻¹ : (X.sheaf.obj.obj U)ˣ).val) •
        reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U u.val) α)) := by
    rw [formProduct_exactOne_of_mul_eq_one B p U u.mul_inv α,
      reindexForm_neg B (Nat.add_comm 1 p) U, reindexForm_smul B (Nat.add_comm 1 p) U]
  rw [d_smul B D p U _ α dα hdα, hinner]

/-- **`d` commutes with scaling by `a` as soon as `d a` kills the form:** if `d a ∧ ω = 0` then
`d (a · ω) = a · d ω`. The Leibniz rule's error term is exactly `d a ∧ ω`. -/
theorem d_smul_of_formProduct_exactOne_eq_zero (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (a : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U)
    (dω : (B.exteriorPower (p + 1)).val.obj U)
    (hdω : ((deRhamComplex B D).d p (p + 1)).val.app U ω = dω)
    (h : formProduct B 1 p U (exactOne B U a) ω = 0) :
    ((deRhamComplex B D).d p (p + 1)).val.app U (a • ω) = a • dω := by
  rw [d_smul B D p U a ω dω hdω, h, reindexForm_zero B (Nat.add_comm 1 p) U, zero_add]

/-- **`d` commutes with dividing by `g` as soon as `d g` kills the form.** For local sections `g`
and `v` of the structure sheaf with `g v = 1` — that is, over an open set on which `g` is
invertible, `v` being its inverse — and a local `p`-form `ω` with `d g ∧ ω = 0`,

`d (ω / g) = (d ω) / g`.

The error term of the Leibniz rule is `d v ∧ ω`, and `d v = -v² · d g` by
`AlgebraicGeometry.SheafOfModules.exactOne_of_mul_eq_one`, so it is a multiple of `d g ∧ ω`. -/
theorem d_smul_of_mul_eq_one (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (g v : X.sheaf.obj.obj U)
    (hgv : g * v = 1) (ω : (B.exteriorPower p).val.obj U)
    (dω : (B.exteriorPower (p + 1)).val.obj U)
    (hdω : ((deRhamComplex B D).d p (p + 1)).val.app U ω = dω)
    (h : formProduct B 1 p U (exactOne B U g) ω = 0) :
    ((deRhamComplex B D).d p (p + 1)).val.app U (v • ω) = v • dω := by
  refine d_smul_of_formProduct_exactOne_eq_zero B D p U v ω dω hdω ?_
  rw [formProduct_exactOne_of_mul_eq_one B p U hgv, h, smul_zero, neg_zero]

/-! ### The differential of the Gysin fraction -/

/-- **Differentiating the Gysin fraction differentiates its numerator alone.** For local sections
`b₁, …, b_c` of the structure sheaf, a local section `v` inverse to their product `b₁ ⋯ b_c`, and
an arbitrary local `p`-form `ω`,

`d ( (ω ∧ d b₁ ∧ ⋯ ∧ d b_c) / (b₁ ⋯ b_c) ) = ( d ω ∧ d b₁ ∧ ⋯ ∧ d b_c ) / (b₁ ⋯ b_c)`.

Two inputs are combined. The numerator is differentiated by
`AlgebraicGeometry.SheafOfModules.d_formProduct_of_closed_right`, the equation wedge being closed
by `AlgebraicGeometry.SheafOfModules.d_prodDegOne_exactOne_eq_zero`. The error term coming from
the denominator is discharged by
`AlgebraicGeometry.SheafOfModules.d_smul_of_mul_eq_one`, whose hypothesis
`d (b₁ ⋯ b_c) ∧ (ω ∧ d b₁ ∧ ⋯ ∧ d b_c) = 0` is
`AlgebraicGeometry.SheafOfModules.formProduct_exactOne_prod_prodDegOne_eq_zero`: the Leibniz rule
expands `d (b₁ ⋯ b_c)` into a sum of multiples of the `d b_j`, each of which repeats a degree-one
factor already present in the wedge.

This is step (ii-b) of the proof of [Stacks, Tag 0G85], as an identity between local sections. -/
theorem d_smul_formProduct_prodDegOne_of_mul_eq_one (p c : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (b : Fin c → X.sheaf.obj.obj U) (v : X.sheaf.obj.obj U) (hv : (∏ j, b j) * v = 1)
    (ω : (B.exteriorPower p).val.obj U) :
    ((deRhamComplex B D).d (p + c) (p + c + 1)).val.app U
        (v • formProduct B p c U ω (B.exterior.prodDegOne U c fun i => exactOne B U (b i))) =
      v • reindexForm B (show p + 1 + c = p + c + 1 by omega) U
        (formProduct B (p + 1) c U (((deRhamComplex B D).d p (p + 1)).val.app U ω)
          (B.exterior.prodDegOne U c fun i => exactOne B U (b i))) := by
  refine d_smul_of_mul_eq_one B D (p + c) U (∏ j, b j) v hv
    (formProduct B p c U ω (B.exterior.prodDegOne U c fun i => exactOne B U (b i))) _ ?_
    (formProduct_exactOne_prod_prodDegOne_eq_zero B p c U ω b)
  exact (d_formProduct_of_closed_right B D p c U ω _
    (d_prodDegOne_exactOne_eq_zero B D c U b)).trans
    (XIsoOfEq_app_eq B D _ U _ _ (reindexForm_heq B _ U _).symm)

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme

/-- **`(f₁ ⋯ f_c)⁻¹`, over the principal open on which the product of the equations is
invertible.** For global functions `f₁, …, f_c` on a scheme `X`, the restriction of `f₁ ⋯ f_c` to
`X.basicOpen (f₁ ⋯ f_c)` is a unit by
`AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen`, and this is its inverse. It is the
denominator of the Gysin fraction of [Stacks, Tag 0G83], inverted on the largest open set on
which that is possible. -/
def equationsProductInv {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤)) :
    X.toRingedSpace.sheaf.obj.obj (op (X.basicOpen (∏ j, f j))) :=
  (X.toRingedSpace.isUnit_res_basicOpen (∏ j, f j)).unit⁻¹.val

/-- `AlgebraicGeometry.Scheme.equationsProductInv` is an inverse of the restriction of
`f₁ ⋯ f_c` to the principal open of that product. -/
theorem mul_equationsProductInv {X : Scheme.{u}} {c : ℕ} (f : Fin c → Γ(X, ⊤))
    (g : X.toRingedSpace.sheaf.obj.obj (op (X.basicOpen (∏ j, f j))))
    (hg : g = X.presheaf.map (homOfLE (le_top : X.basicOpen (∏ j, f j) ≤ ⊤)).op (∏ j, f j)) :
    g * equationsProductInv f = 1 := by
  subst hg
  exact (X.toRingedSpace.isUnit_res_basicOpen (∏ j, f j)).mul_val_inv

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- **Differentiating the Gysin fraction of a morphism of schemes differentiates its numerator
alone.** For `π : X ⟶ S`, global functions `f₁, …, f_c` on `X`, an open set `U` on which the
restriction `g` of the product `f₁ ⋯ f_c` is invertible with inverse `v`, and a local `p`-form
`ω`,

`d ( (ω ∧ d f₁ ∧ ⋯ ∧ d f_c) / (f₁ ⋯ f_c) ) = ( d ω ∧ d f₁ ∧ ⋯ ∧ d f_c ) / (f₁ ⋯ f_c)`,

the wedge being the numerator of the Gysin formula of [Stacks, Tag 0G83] in the spelling
`AlgebraicGeometry.Scheme.Hom.equationsWedge`. This is
`AlgebraicGeometry.SheafOfModules.d_smul_formProduct_prodDegOne_of_mul_eq_one` for the de Rham
algebras of `π`, the restriction of the product being the product of the restrictions. -/
theorem d_smul_equationsWedge_of_mul_eq_one (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℕ)
    (U : X.Opensᵒᵖ) (g v : X.toRingedSpace.sheaf.obj.obj U)
    (hg : g = X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (∏ j, f j)) (hgv : g * v = 1)
    (ω : ((deRhamAlgebras π).exteriorPower p).val.obj U) :
    ((deRhamComplex π).d (p + c) (p + c + 1)).val.app U
        (v • AlgebraicGeometry.SheafOfModules.formProduct (deRhamAlgebras π) p c U ω
          ((equationsWedge π f).eval U)) =
      v • AlgebraicGeometry.SheafOfModules.reindexForm (deRhamAlgebras π)
        (show p + 1 + c = p + c + 1 by omega) U
        (AlgebraicGeometry.SheafOfModules.formProduct (deRhamAlgebras π) (p + 1) c U
          (((deRhamComplex π).d p (p + 1)).val.app U ω) ((equationsWedge π f).eval U)) := by
  have hres : X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (∏ j, f j) =
      ∏ j, X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f j) :=
    map_prod (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op).hom f Finset.univ
  rw [hg, hres] at hgv
  exact AlgebraicGeometry.SheafOfModules.d_smul_formProduct_prodDegOne_of_mul_eq_one
    (deRhamAlgebras π)
    (AlgebraicGeometry.SheafOfModules.deRhamDifferential (deRhamAlgebras π)) p c U
    (fun j => X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op (f j)) v hgv ω

/-- **Differentiating the Gysin fraction over the principal open of the product of the
equations.** The instance of
`AlgebraicGeometry.Scheme.Hom.d_smul_equationsWedge_of_mul_eq_one` the Gysin map of
[Stacks, Tag 0G83] is used over: on `X.basicOpen (f₁ ⋯ f_c)` the denominator is invertible with
inverse `AlgebraicGeometry.Scheme.equationsProductInv`, so

`d ( (ω ∧ d f₁ ∧ ⋯ ∧ d f_c) / (f₁ ⋯ f_c) ) = ( d ω ∧ d f₁ ∧ ⋯ ∧ d f_c ) / (f₁ ⋯ f_c)`

there, with no hypothesis at all. -/
theorem d_smul_equationsWedge_basicOpen (π : X ⟶ S) {c : ℕ} (f : Fin c → Γ(X, ⊤)) (p : ℕ)
    (ω : ((deRhamAlgebras π).exteriorPower p).val.obj (op (X.basicOpen (∏ j, f j)))) :
    ((deRhamComplex π).d (p + c) (p + c + 1)).val.app (op (X.basicOpen (∏ j, f j)))
        (equationsProductInv f •
          AlgebraicGeometry.SheafOfModules.formProduct (deRhamAlgebras π) p c
            (op (X.basicOpen (∏ j, f j))) ω
            ((equationsWedge π f).eval (op (X.basicOpen (∏ j, f j))))) =
      equationsProductInv f •
        AlgebraicGeometry.SheafOfModules.reindexForm (deRhamAlgebras π)
          (show p + 1 + c = p + c + 1 by omega) (op (X.basicOpen (∏ j, f j)))
          (AlgebraicGeometry.SheafOfModules.formProduct (deRhamAlgebras π) (p + 1) c
            (op (X.basicOpen (∏ j, f j)))
            (((deRhamComplex π).d p (p + 1)).val.app (op (X.basicOpen (∏ j, f j))) ω)
            ((equationsWedge π f).eval (op (X.basicOpen (∏ j, f j))))) :=
  d_smul_equationsWedge_of_mul_eq_one π f p (op (X.basicOpen (∏ j, f j)))
    (X.presheaf.map (homOfLE (le_top : X.basicOpen (∏ j, f j) ≤ ⊤)).op (∏ j, f j))
    (equationsProductInv f) rfl (mul_equationsProductInv f _ rfl) ω

end AlgebraicGeometry.Scheme.Hom

end
