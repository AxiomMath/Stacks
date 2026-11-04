module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.WedgeDifferentialLeft

/-!
# The Leibniz form of a linear map into the local differential forms

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a topological space, with
`𝒪_X` the structure sheaf of a ringed space `X`, let `Ω = Ω_{𝒪_X/A}` be the sheaf of relative
differentials, let `B` also denote a package of the three algebras of Stacks Section 17.21 for
`Ω` and let `d` be a de Rham differential on its exterior powers.

Let `N` be an `𝒪_X(U)`-module equipped with an `𝒪_X(U)`-linear map `ι : N ⟶ 𝒪_X(U)` and let
`ψ : N ⟶ Ω^p(U)` be `𝒪_X(U)`-linear. The **Leibniz form** of `ψ` is

`Λ(a, b) = ι a · d(ψ b) − d(ι b) ∧ ψ a`.

This file proves that it is `𝒪_X(U)`-**bilinear**, given `ι a · ψ b = ι b · ψ a`. It is linear
in neither argument on its own: the failure in the second argument is `ι a · (d c ∧ ψ b)` and the
failure in the first is `ι b · (d c ∧ ψ a)`, and that identity is exactly what makes them cancel.

`N` is a module with a map to `𝒪_X(U)` rather than an ideal of it because that is the shape the
consumer has. The ideal sheaf of a closed subscheme is
`Stacks.Divisors.negativeTwist`, defined as a kernel, and a local section of it reaches `𝒪_X` only
through `Stacks.Divisors.idealInclusion`
(`AlgebraicGeometry.Scheme.Hom.negativeTwistSection`); its sections are not an `Ideal`. For `N`
genuinely an ideal, `ι := Submodule.subtype I`, the hypothesis is free — that is
`AlgebraicGeometry.SheafOfModules.smul_apply_comm_of_ideal`, and
`logLeibnizForm_smul_right_of_ideal` and `logLeibnizFormBilinOfIdeal` are the hypothesis-free
forms.

`Stacks.LogPoles.logLeibnizBilin` (`StacksFrontier/RingTheory/DeRham/LogPolesLeibniz.lean`) is the
same statement for the Kähler differentials of a *ring*. It does not imply this one: `Ω^p(U)` is
a section of a sheafification and not `⋀^p Ω_{𝒪_X(U)/A(U)}`, so the two Leibniz rules the
argument runs on — `AlgebraicGeometry.SheafOfModules.d_smul` for the scalar and
`AlgebraicGeometry.SheafOfModules.exactOne_mul` for the derivation — have to be the sheaf-level
ones.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.dForm`: the de Rham differential on local sections, retyped
  so that its value is a section of `Ω^{p+1}` rather than of the restriction of scalars of
  `Ω^{p+1}` along `φ`. This is what makes `a • d ω` elaborate for a local section `a` of `𝒪_X`.
* `AlgebraicGeometry.SheafOfModules.logLeibnizForm` and
  `AlgebraicGeometry.SheafOfModules.logLeibnizFormBilin`: the Leibniz form, and **the Leibniz
  form as a bilinear map.**
* `AlgebraicGeometry.SheafOfModules.logLeibnizFormBilinOfIdeal`: the same for a linear map out of
  an ideal, where the hypothesis is discharged.

## Main results

* `AlgebraicGeometry.SheafOfModules.dForm_smul` and
  `AlgebraicGeometry.SheafOfModules.dForm_exactWedge`: the Leibniz rule against a scalar and the
  anticommutation with `d c ∧ ·`, in the `dForm` spelling — no auxiliary argument naming `d ω`.
* `AlgebraicGeometry.SheafOfModules.exactWedge_add_right`,
  `exactWedge_smul_right`, `exactWedge_add_left` and `exactWedge_mul_left`: the algebra of
  `d c ∧ ·` in the normalized degree `p + 1`.
* `AlgebraicGeometry.SheafOfModules.smul_exactWedge_apply_comm`: `ι a · ψ b = ι b · ψ a` carried
  through the wedge. This is what makes the two failures of linearity cancel.
* `AlgebraicGeometry.SheafOfModules.smul_apply_comm_of_ideal`: that identity holds for free for a
  linear map out of an ideal, both sides being `ψ (a b)`; hence
  `logLeibnizForm_smul_right_of_ideal`, with no hypothesis.
* `AlgebraicGeometry.SheafOfModules.logLeibnizForm_add_left`, `logLeibnizForm_smul_left`,
  `logLeibnizForm_add_right` and `logLeibnizForm_smul_right`: **the four linearity laws.** Only
  the last has content.
* `AlgebraicGeometry.SheafOfModules.dForm_map`, `exactWedge_map`, `map_logLeibnizForm` and
  `logLeibnizForm_map`: **everything commutes with restriction.** This is what makes the Leibniz
  form a natural family, and so a candidate for a section of a sheaf-hom.

## Implementation notes

`AlgebraicGeometry.SheafOfModules.d_smul` takes `d ω` as an explicit argument together with an
equation naming it, because the terms of the de Rham complex are restrictions of scalars along
`φ` and the `𝒪_X`-action by a local section is then not found on `d.val.app U ω` by instance
resolution. `dForm` pays that coercion once, in a definition whose stated result type is the
section of the exterior power; `dForm_smul` is `d_smul` instantiated at `rfl`, and every statement
below is in the `dForm` spelling.

`d c ∧ ω` is spelled
`reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω)` throughout — the
degree of a wedge product of a one-form and a `p`-form is `1 + p`, and the degree of a term of
the complex is `p + 1`. That is the spelling `AlgebraicGeometry.SheafOfModules.d_smul` and
`AlgebraicGeometry.SheafOfModules.d_formProduct_exactOne_left` are stated in, so the two rules
apply to these terms with no bridge. **No new name is introduced for it**: the notion already has
two spellings in the library, this one and
`AlgebraicGeometry.SheafOfModules.prependExact`, and a third would be a duplicate.

The rearrangement of sums that `logLeibnizForm_smul_right` ends in is the separate lemma
`Stacks.DeRham.add_smul_smul_sub_add`, over an abstract module, rather than an `abel` call in
place. Done in place the whole declaration exceeds the heartbeat limit: every atom of the goal is
a section of an exterior power of a sheafification, and `rw`'s abstraction over such an atom is
what the heartbeats go on. Nothing about the mathematics needs the split.

The four restriction lemmas are proved in term mode, not with `rw`, for a related reason. A
restricted section is written `M.val.map i x`, whose type is the `ModuleCat.restrictScalars`
wrapper around `M.val.obj V` rather than `M.val.obj V` itself; the two are definitionally equal
only after unfolding that wrapper, which is below the transparency `rw` builds its motive at, so
`rw [dForm_map]` reports a heartbeat timeout on a pattern that is visibly present. `congrArg`,
`congrArg₂` and `Eq.trans` do the same work and type-check at default transparency. This is the
obstruction `Stacks.restr` was introduced for, and the same one recorded in the implementation
notes of `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BilinearSourceNaturality.lean`.

## References

* [Stacks Project, Tag 0FMW](https://stacks.math.columbia.edu/tag/0FMW)
* [Stacks Project, Tag 0FMV](https://stacks.math.columbia.edu/tag/0FMV)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.DeRham

/-- The rearrangement the Leibniz form's linearity in its second argument comes down to, stated
over an abstract module so that it is elaborated away from the sheaves of differential forms:
there the same computation runs into the heartbeat limit, because every atom is a section of an
exterior power of a sheafification. -/
private theorem add_smul_smul_sub_add {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (c s : R) (w₁ w₂ v z : M) (h : w₁ = w₂) :
    w₁ + c • s • v - (s • z + w₂) = s • (c • v - z) := by
  subst h
  rw [smul_sub, ← mul_smul, ← mul_smul, mul_comm c s]
  abel

end Stacks.DeRham

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! ### The algebra of `d c ∧ ·` in the normalized degree -/

/-- The wedge product with a form of degree `p` is additive in a one-form on the left. -/
private theorem formProduct_one_add_left (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (η η' : (B.exteriorPower 1).val.obj U) (ω : (B.exteriorPower p).val.obj U) :
    formProduct B 1 p U (η + η') ω = formProduct B 1 p U η ω + formProduct B 1 p U η' ω :=
  congrFun (congrArg (fun k : (B.exteriorPower p).val.obj U →+ _ => ⇑k)
    (map_add ((B.exterior.mul ((1 : ℕ) : ℤ) (p : ℤ)).app U) η η')) ω

/-- Wedging an exact one-form on the left is additive in the form. -/
theorem exactWedge_add_right (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (c : X.sheaf.obj.obj U)
    (ω ω' : (B.exteriorPower p).val.obj U) :
    reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) (ω + ω')) =
      reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω) +
        reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω') := by
  rw [show formProduct B 1 p U (exactOne B U c) (ω + ω') =
      formProduct B 1 p U (exactOne B U c) ω + formProduct B 1 p U (exactOne B U c) ω' from
    map_add _ _ _, reindexForm_add]

/-- Wedging an exact one-form on the left commutes with scaling the form. -/
theorem exactWedge_smul_right (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (r c : X.sheaf.obj.obj U)
    (ω : (B.exteriorPower p).val.obj U) :
    reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) (r • ω)) =
      r • reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω) := by
  rw [show formProduct B 1 p U (exactOne B U c) (r • ω) =
      r • formProduct B 1 p U (exactOne B U c) ω from
    (B.exterior.mul ((1 : ℕ) : ℤ) (p : ℤ)).map_smul_right U r _ ω, reindexForm_smul]

/-- Wedging an exact one-form on the left is additive in the section being differentiated. -/
theorem exactWedge_add_left (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (c c' : X.sheaf.obj.obj U)
    (ω : (B.exteriorPower p).val.obj U) :
    reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U (c + c')) ω) =
      reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω) +
        reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c') ω) := by
  rw [exactOne_add, formProduct_one_add_left, reindexForm_add]

/-- **The Leibniz rule inside the wedge:** `d (r c) ∧ ω = r · (d c ∧ ω) + c · (d r ∧ ω)`. This is
`AlgebraicGeometry.SheafOfModules.exactOne_mul` read in the normalized degree. -/
theorem exactWedge_mul_left (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (r c : X.sheaf.obj.obj U)
    (ω : (B.exteriorPower p).val.obj U) :
    reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U (r * c)) ω) =
      r • reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω) +
        c • reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U r) ω) := by
  rw [exactOne_mul, show formProduct B 1 p U (r • exactOne B U c + c • exactOne B U r) ω =
      r • formProduct B 1 p U (exactOne B U c) ω + c • formProduct B 1 p U (exactOne B U r) ω from
    (formProduct_one_add_left B p U _ _ ω).trans
      (congrArg₂ (· + ·) (formProduct_smul_left B 1 p U r _ ω)
        (formProduct_smul_left B 1 p U c _ ω)),
    reindexForm_add, reindexForm_smul, reindexForm_smul]

variable (D : DeRhamDifferential B)

/-! ### The differential on sections, retyped -/

/-- **The de Rham differential on local sections**, with its value typed as a section of
`Ω^{p+1}` rather than of the restriction of scalars of `Ω^{p+1}` along `φ`. The two types have
the same carrier, but only the former carries the `𝒪_X(U)`-action, so this is the spelling in
which `a • d ω` elaborates for a local section `a` of the structure sheaf. -/
def dForm (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (ω : (B.exteriorPower p).val.obj U) :
    (B.exteriorPower (p + 1)).val.obj U :=
  ((deRhamComplex B D).d p (p + 1)).val.app U ω

/-- The differential on sections is additive. -/
theorem dForm_add (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω ω' : (B.exteriorPower p).val.obj U) :
    dForm B D p U (ω + ω') = dForm B D p U ω + dForm B D p U ω' :=
  map_add _ _ _

/-- **The Leibniz rule against a scalar**, `d (a · ω) = d a ∧ ω + a · d ω`, in the `dForm`
spelling: this is `AlgebraicGeometry.SheafOfModules.d_smul` with its auxiliary argument
instantiated at `rfl`. -/
theorem dForm_smul (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (a : X.sheaf.obj.obj U)
    (ω : (B.exteriorPower p).val.obj U) :
    dForm B D p U (a • ω) =
      reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U a) ω) +
        a • dForm B D p U ω :=
  d_smul B D p U a ω _ rfl

/-- **The differential anticommutes with wedging an exact one-form on the left**, in the `dForm`
spelling: this is `AlgebraicGeometry.SheafOfModules.d_formProduct_exactOne_left`. -/
theorem dForm_exactWedge (p : ℕ) (U : (Opens X.carrier)ᵒᵖ) (c : X.sheaf.obj.obj U)
    (ω : (B.exteriorPower p).val.obj U) :
    dForm B D (p + 1) U
        (reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω)) =
      -reindexForm B (Nat.add_comm 1 (p + 1)) U
        (formProduct B 1 (p + 1) U (exactOne B U c) (dForm B D p U ω)) :=
  d_formProduct_exactOne_left B D p U c ω

/-! ### Restriction -/

/-- **The differential on sections commutes with restriction.** This is the naturality of
`D.differential p`, read through the `dForm` spelling. -/
theorem dForm_map {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (ω : (B.exteriorPower p).val.obj U) :
    (B.exteriorPower (p + 1)).val.map i (dForm B D p U ω) =
      dForm B D p V ((B.exteriorPower p).val.map i ω) := by
  simp only [dForm, deRhamComplex_d]
  exact (PresheafOfModules.naturality_apply (D.differential p).val i ω).symm

/-- **Wedging an exact one-form on the left commutes with restriction.** The wedge product is
natural and `AlgebraicGeometry.SheafOfModules.exactOne_map` carries `d c` to `d (c|_V)`. -/
theorem exactWedge_map {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    (c : X.sheaf.obj.obj U) (ω : (B.exteriorPower p).val.obj U) :
    (B.exteriorPower (p + 1)).val.map i
        (reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U c) ω)) =
      reindexForm B (Nat.add_comm 1 p) V
        (formProduct B 1 p V (exactOne B V (X.sheaf.obj.map i c))
          ((B.exteriorPower p).val.map i ω)) := by
  rw [reindexForm_map,
    show (B.exteriorPower (1 + p)).val.map i (formProduct B 1 p U (exactOne B U c) ω) =
        formProduct B 1 p V ((B.exteriorPower 1).val.map i (exactOne B U c))
          ((B.exteriorPower p).val.map i ω) from
      (B.exterior.mul ((1 : ℕ) : ℤ) (p : ℤ)).naturality i _ ω,
    exactOne_map]

/-! ### The Leibniz form -/

variable (p : ℕ) (U : (Opens X.carrier)ᵒᵖ)

section LeibnizForm

variable {N : Type u} [AddCommGroup N] [Module (X.sheaf.obj.obj U) N]
  (ι : N →ₗ[X.sheaf.obj.obj U] X.sheaf.obj.obj U)

/-- **The Leibniz form** `Λ(a, b) = ι a · d(ψ b) − d(ι b) ∧ ψ a` of an `𝒪_X(U)`-linear map `ψ`
out of a module `N` equipped with an `𝒪_X(U)`-linear map `ι : N ⟶ 𝒪_X(U)`.

`N` is not asked to be an ideal of `𝒪_X(U)`, and `ι` is not asked to be injective, because the
sheaf of modules this is applied to is not presented as a subsheaf of the structure sheaf: the
ideal sheaf of a closed subscheme is `Stacks.Divisors.negativeTwist`, a kernel, and a local
section of it is pushed into `𝒪_X` by `Stacks.Divisors.idealInclusion`. For `N` an ideal take
`ι := Submodule.subtype I`. -/
def logLeibnizForm (ψ : N →ₗ[X.sheaf.obj.obj U] (B.exteriorPower p).val.obj U) (a b : N) :
    (B.exteriorPower (p + 1)).val.obj U :=
  ι a • dForm B D p U (ψ b) -
    reindexForm B (Nat.add_comm 1 p) U (formProduct B 1 p U (exactOne B U (ι b)) (ψ a))

variable (ψ : N →ₗ[X.sheaf.obj.obj U] (B.exteriorPower p).val.obj U)

/-- The Leibniz form is additive in its first argument. -/
theorem logLeibnizForm_add_left (a a' b : N) :
    logLeibnizForm B D p U ι ψ (a + a') b =
      logLeibnizForm B D p U ι ψ a b + logLeibnizForm B D p U ι ψ a' b := by
  rw [logLeibnizForm, logLeibnizForm, logLeibnizForm, map_add ι a a', map_add ψ a a', add_smul,
    exactWedge_add_right]
  exact (sub_add_sub_comm _ _ _ _).symm

/-- The Leibniz form commutes with scaling its first argument. -/
theorem logLeibnizForm_smul_left (r : X.sheaf.obj.obj U) (a b : N) :
    logLeibnizForm B D p U ι ψ (r • a) b = r • logLeibnizForm B D p U ι ψ a b := by
  rw [logLeibnizForm, logLeibnizForm, map_smul ι r a, map_smul ψ r a, exactWedge_smul_right,
    smul_eq_mul, mul_smul, smul_sub]

/-- The Leibniz form is additive in its second argument. -/
theorem logLeibnizForm_add_right (a b b' : N) :
    logLeibnizForm B D p U ι ψ a (b + b') =
      logLeibnizForm B D p U ι ψ a b + logLeibnizForm B D p U ι ψ a b' := by
  rw [logLeibnizForm, logLeibnizForm, logLeibnizForm, map_add ψ b b', dForm_add, smul_add,
    map_add ι b b', exactWedge_add_left]
  exact (sub_add_sub_comm _ _ _ _).symm

/-- `ι a · (d c ∧ ψ b) = ι b · (d c ∧ ψ a)` whenever `ι a · ψ b = ι b · ψ a`: the identity is
carried through the wedge, whose right factor it is linear in. -/
theorem smul_exactWedge_apply_comm
    (hcomm : ∀ a b : N, ι a • ψ b = ι b • ψ a) (c : X.sheaf.obj.obj U) (a b : N) :
    ι a • reindexForm B (Nat.add_comm 1 p) U
        (formProduct B 1 p U (exactOne B U c) (ψ b)) =
      ι b • reindexForm B (Nat.add_comm 1 p) U
        (formProduct B 1 p U (exactOne B U c) (ψ a)) := by
  rw [← exactWedge_smul_right, ← exactWedge_smul_right, hcomm a b]

/-- **The Leibniz form commutes with scaling its second argument.** This is the one of the four
linearity laws with content: `d (r · ι b) = r · d(ι b) + ι b · d r` produces the error term
`ι a · (d r ∧ ψ b)`, the failure of linearity in the second argument, and
`AlgebraicGeometry.SheafOfModules.smul_exactWedge_apply_comm` identifies it with
`ι b · (d r ∧ ψ a)`, the failure in the first, against which it cancels. The hypothesis
`ι a · ψ b = ι b · ψ a` is what an ideal supplies for free
(`AlgebraicGeometry.SheafOfModules.smul_apply_comm_of_ideal`). -/
theorem logLeibnizForm_smul_right (hcomm : ∀ a b : N, ι a • ψ b = ι b • ψ a)
    (r : X.sheaf.obj.obj U) (a b : N) :
    logLeibnizForm B D p U ι ψ a (r • b) = r • logLeibnizForm B D p U ι ψ a b := by
  rw [logLeibnizForm, logLeibnizForm, map_smul ψ r b, map_smul ι r b, smul_eq_mul, dForm_smul,
    exactWedge_mul_left, smul_add]
  exact Stacks.DeRham.add_smul_smul_sub_add _ _ _ _ _ _
    (smul_exactWedge_apply_comm B p U ι ψ hcomm r a b)

/-- **The Leibniz form is `𝒪_X(U)`-bilinear.** It is linear in neither argument on its own: the
failure of linearity in the second argument is `ι a · (d c ∧ ψ b)` and the failure in the first
is `ι b · (d c ∧ ψ a)`, and the two cancel by the hypothesis. -/
def logLeibnizFormBilin (hcomm : ∀ a b : N, ι a • ψ b = ι b • ψ a) :
    N →ₗ[X.sheaf.obj.obj U] N →ₗ[X.sheaf.obj.obj U] (B.exteriorPower (p + 1)).val.obj U :=
  LinearMap.mk₂ (X.sheaf.obj.obj U) (logLeibnizForm B D p U ι ψ)
    (logLeibnizForm_add_left B D p U ι ψ) (logLeibnizForm_smul_left B D p U ι ψ)
    (logLeibnizForm_add_right B D p U ι ψ) (logLeibnizForm_smul_right B D p U ι ψ hcomm)

/-- The bilinear map `logLeibnizFormBilin` evaluates to the Leibniz form. -/
@[simp]
theorem logLeibnizFormBilin_apply (hcomm : ∀ a b : N, ι a • ψ b = ι b • ψ a) (a b : N) :
    logLeibnizFormBilin B D p U ι ψ hcomm a b = logLeibnizForm B D p U ι ψ a b := rfl

end LeibnizForm

/-! ### The case of an ideal -/

/-- A linear map out of an ideal satisfies `a · ψ b = b · ψ a`: both sides are `ψ (a b)`. This is
the hypothesis of `AlgebraicGeometry.SheafOfModules.logLeibnizForm_smul_right` for
`ι = Submodule.subtype I`, so for an ideal the Leibniz form is bilinear with no hypothesis. -/
theorem smul_apply_comm_of_ideal {I : Ideal (X.sheaf.obj.obj U)}
    (ψ : ↥I →ₗ[X.sheaf.obj.obj U] (B.exteriorPower p).val.obj U) (a b : ↥I) :
    Submodule.subtype I a • ψ b = Submodule.subtype I b • ψ a := by
  have h : ((Submodule.subtype I a) • b : ↥I) = ((Submodule.subtype I b) • a : ↥I) :=
    Subtype.ext (mul_comm _ _)
  rw [← ψ.map_smul, ← ψ.map_smul, h]

/-- **The Leibniz form of a linear map out of an ideal commutes with scaling its second
argument**, with no hypothesis. -/
theorem logLeibnizForm_smul_right_of_ideal {I : Ideal (X.sheaf.obj.obj U)}
    (ψ : ↥I →ₗ[X.sheaf.obj.obj U] (B.exteriorPower p).val.obj U) (r : X.sheaf.obj.obj U)
    (a b : ↥I) :
    logLeibnizForm B D p U (Submodule.subtype I) ψ a (r • b) =
      r • logLeibnizForm B D p U (Submodule.subtype I) ψ a b :=
  logLeibnizForm_smul_right B D p U (Submodule.subtype I) ψ
    (smul_apply_comm_of_ideal B p U ψ) r a b

/-- **The Leibniz form of a linear map out of an ideal is bilinear**, with no hypothesis. -/
def logLeibnizFormBilinOfIdeal {I : Ideal (X.sheaf.obj.obj U)}
    (ψ : ↥I →ₗ[X.sheaf.obj.obj U] (B.exteriorPower p).val.obj U) :
    ↥I →ₗ[X.sheaf.obj.obj U] ↥I →ₗ[X.sheaf.obj.obj U] (B.exteriorPower (p + 1)).val.obj U :=
  logLeibnizFormBilin B D p U (Submodule.subtype I) ψ (smul_apply_comm_of_ideal B p U ψ)

/-! ### Restriction of the Leibniz form -/

/-- **The restriction of the Leibniz form, computed.** Every ingredient is natural, so the
restriction of `ι a · d(ψ b) − d(ι b) ∧ ψ a` is the same expression in the restrictions of
`ι a`, `ι b` and of the two values of `ψ`. -/
theorem map_logLeibnizForm {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (p : ℕ) {N : Type u}
    [AddCommGroup N] [Module (X.sheaf.obj.obj U) N]
    (ι : N →ₗ[X.sheaf.obj.obj U] X.sheaf.obj.obj U)
    (ψ : N →ₗ[X.sheaf.obj.obj U] (B.exteriorPower p).val.obj U) (a b : N) :
    (B.exteriorPower (p + 1)).val.map i (logLeibnizForm B D p U ι ψ a b) =
      X.sheaf.obj.map i (ι a) • dForm B D p V ((B.exteriorPower p).val.map i (ψ b)) -
        reindexForm B (Nat.add_comm 1 p) V
          (formProduct B 1 p V (exactOne B V (X.sheaf.obj.map i (ι b)))
            ((B.exteriorPower p).val.map i (ψ a))) := by
  refine Eq.trans (map_sub _ _ _) (congrArg₂ (· - ·) ?_ (exactWedge_map B i p _ (ψ a)))
  exact ((B.exteriorPower (p + 1)).val.map_smul i (ι a) _).trans
    (congrArg (fun z => X.sheaf.obj.map i (ι a) • z) (dForm_map B D i p (ψ b)))

/-- **The Leibniz form commutes with restriction.** The restricted data is taken as variables
together with the equations naming it, so that a caller can supply its own spelling of the
restriction of `N` and of the two linear maps: `a'`, `b'` restrict `a`, `b` compatibly with `ι`,
and `ψ'` agrees with `ψ` after restriction. This is what makes the Leibniz form a *natural*
family, and so a candidate for a section of a sheaf-hom. -/
theorem logLeibnizForm_map {U V : (Opens X.carrier)ᵒᵖ} (i : U ⟶ V) (p : ℕ)
    {N : Type u} [AddCommGroup N] [Module (X.sheaf.obj.obj U) N]
    {N' : Type u} [AddCommGroup N'] [Module (X.sheaf.obj.obj V) N']
    (ι : N →ₗ[X.sheaf.obj.obj U] X.sheaf.obj.obj U)
    (ι' : N' →ₗ[X.sheaf.obj.obj V] X.sheaf.obj.obj V)
    (ψ : N →ₗ[X.sheaf.obj.obj U] (B.exteriorPower p).val.obj U)
    (ψ' : N' →ₗ[X.sheaf.obj.obj V] (B.exteriorPower p).val.obj V)
    (a b : N) (a' b' : N')
    (ha : ι' a' = X.sheaf.obj.map i (ι a)) (hb : ι' b' = X.sheaf.obj.map i (ι b))
    (hψa : ψ' a' = (B.exteriorPower p).val.map i (ψ a))
    (hψb : ψ' b' = (B.exteriorPower p).val.map i (ψ b)) :
    (B.exteriorPower (p + 1)).val.map i (logLeibnizForm B D p U ι ψ a b) =
      logLeibnizForm B D p V ι' ψ' a' b' := by
  refine (map_logLeibnizForm B D i p ι ψ a b).trans ?_
  have h₁ : X.sheaf.obj.map i (ι a) •
        dForm B D p V ((B.exteriorPower p).val.map i (ψ b)) =
      ι' a' • dForm B D p V (ψ' b') :=
    congrArg₂ (· • ·) ha.symm (congrArg (dForm B D p V) hψb.symm)
  have h₂ : reindexForm B (Nat.add_comm 1 p) V
        (formProduct B 1 p V (exactOne B V (X.sheaf.obj.map i (ι b)))
          ((B.exteriorPower p).val.map i (ψ a))) =
      reindexForm B (Nat.add_comm 1 p) V
        (formProduct B 1 p V (exactOne B V (ι' b')) (ψ' a')) :=
    congrArg₂ (fun c z => reindexForm B (Nat.add_comm 1 p) V
      (formProduct B 1 p V (exactOne B V c) z)) hb.symm hψa.symm
  exact congrArg₂ (· - ·) h₁ h₂

end AlgebraicGeometry.SheafOfModules
