module

public import StacksFrontier.AlgebraicGeometry.TensorSectionProduct.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingOpen.Basic

/-!
# Tensor powers of a section built with `tensorSection`, and the power law for a *local* generator

The gluing argument of [Stacks, Tag 01PW] runs on a cover by opens trivializing the invertible
module `M`, and on each member it needs the identity

> `s ^ (k+1)|_W = f ^ (k+1) · b ^ (k+1)`,  where `s|_W = f · b` and `b` generates `M` over `W`,

relating the restriction of a power of a *global* section `s` to the corresponding power of the
*local* generator `b`. `Stacks.TensorPowerTrivialize.resTop_sectionPow` is that identity when `b`
is itself the restriction of a global section, and that hypothesis is exactly
`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing` — strictly stronger than anything Tag
01PW assumes. For a local generator nothing stated it.

## Why the power is taken with `tensorSection` and not with `Stacks.GradedSections.mul`

`Stacks.GradedSections.mul` multiplies two **global** sections, as a composite of morphisms of
modules; `Stacks.TensorPowerTrivialize.sectionPow` iterates it, and
`Stacks.TensorPowerTrivialize.resTop_sectionPow` is its power law. A local generator is not a
morphism out of the monoidal unit, so that product cannot be formed on it, and relating the global
product to the only product that *is* available on local sections —
`Stacks.SectionTensorFormula.tensorSection` — is an identification that neither tree has: there is
no lemma anywhere mentioning both `Stacks.GradedSections.mulMap` (or
`Stacks.TensorSectionNonvanishing.unitMul`) and `tensorSection`, and
`StacksFrontier/AlgebraicGeometry/TensorSectionProduct/Basic.lean` records the identification as
open. Proving it means computing the associator of the localized monoidal structure of
`Stacks.SheafInternalHom.monoidalCategory` on sections, which is a project of its own.

The way round it is to take **both** powers with `tensorSection`: the powers of the global section
`s` below are honest global sections, formed by the same operation as the powers of the local
generator, and then the two are related by `Stacks.SectionTensorFormula.map_tensorSection` — the
restriction compatibility of `tensorSection`, which is one application of
`PresheafOfModules.naturality_apply`. So the power law becomes
`Stacks.TensorSectionPower.map_secPow` followed by `Stacks.TensorSectionPower.secPow_smul`, and no
comparison of the two products is needed anywhere.

What is bought with this is Tag 01PW's hypotheses: the generator may be the basis section of an
arbitrary trivialization, which every invertible module has around every point by clause 2 of
[Stacks, Tag 0B8M], with no global section in sight.

## Main definitions

* `Stacks.TensorSectionPower.powObj`: the object `M ^⊗ (k+1)`, by the recursion
  `powObj M 0 = M`, `powObj M (k+1) = powObj M k ⊗ M`. Characterized by
  `Stacks.TensorSectionPower.powObj_zero` and `Stacks.TensorSectionPower.powObj_succ`, both `rfl`.
  Indexing from the first power rather than the zeroth is what keeps the recursion transport-free:
  a zeroth entry would be the monoidal unit, the first power would be `𝟙_X.Modules ⊗ M` rather
  than `M`, and every statement below would carry a unitor. (The same choice, for the same reason,
  as `Stacks.TensorPowerTrivialize.sectionPow`.)
* `Stacks.TensorSectionPower.secPow`: the `(k+1)`-st power `u ^ (k+1) : Γ(M ^⊗ (k+1), U)` of a
  section `u : Γ(M, U)` over **any** open `U`, formed with `tensorSection`. For `U = ⊤` this is a
  global section; for `U` a trivializing open and `u` a basis section it is the local generator the
  gluing needs, and the two cases are the same definition, which is the point.

## Main results

* `Stacks.TensorSectionPower.map_secPow`: **powers commute with restriction**,
  `(u ^ (k+1))|_V = (u|_V) ^ (k+1)`. This is what makes the power of the global section and the
  power of the local generator comparable at all.
* `Stacks.TensorSectionPower.secPow_smul`: **the power law**,
  `(a · u) ^ (k+1) = a ^ (k+1) · u ^ (k+1)` for a scalar `a : Γ(X, U)`. Together with `map_secPow`
  this is the identity displayed above, for an arbitrary local generator.
* `Stacks.TensorSectionPower.nonvanishingLocus_secPow` and `nonvanishingOpen_secPow`:
  `X_{s ^ (k+1)} = X_s`, so a power of a global section cuts out the same open. Induction from
  `Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection`.
* `Stacks.TensorSectionPower.smul_res_basis_injective`: multiplication by the restricted basis
  section of a trivialization is injective on scalars — the uniqueness half of the division the
  gluing performs in degree one.

## What is not done, and no Stacks attribute is attached

**No `@[stacks]` attribute is attached here.** Nothing below is an assertion of a Stacks tag: Tag
01CU's tensor powers are `Stacks.Ample.tensorPowModule` and Tag 01CY's clauses are proved
elsewhere; `powObj` is a bracketing of iterated tensor products chosen to make a recursion
transport-free, not a new mathematical object.

**`powObj M k` is not identified with `Stacks.TensorPowers.natTensorPow M (k+1)` or with
`Stacks.Ample.tensorPowModule X M (k+1)`.** They are isomorphic — `natTensorPow` differs by the
unit factor in its zeroth entry and `tensorPowModule` by the general addition law
`Stacks.TensorPowerAssoc.powAdd` — but they are different terms, and transporting a statement
whose conclusion contains `tensorSection` along such an isomorphism needs the naturality of
`tensorSection` in its module arguments, i.e. a formula for `(F ◁ φ).app U` on a product of
sections. That formula is absent (see the discussion above) and is the one thing standing between
the gluing of the sibling file and the `Stacks.Ample.tensorPowModule` vocabulary the consumers of
the ample cluster are stated over.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample
open Stacks.SectionTensorFormula (tensorSection tensorSection_smul_left tensorSection_smul_right
  map_tensorSection)

universe u

namespace Stacks.TensorSectionPower

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.TensorSectionNonvanishing.isInvertibleModule_tensorObj

variable {X : Scheme.{u}}

/-! ### The powers of an object -/

/-- **The `(k+1)`-st tensor power of an `𝒪_X`-module**, left-bracketed, indexed from the first
power so that no monoidal unit and no unitor occurs: `powObj M 0` is `M` on the nose. -/
def powObj (M : X.Modules) : ℕ → X.Modules
  | 0 => M
  | k + 1 => powObj M k ⊗ M

/-- The zeroth power `powObj M 0` is `M`. -/
theorem powObj_zero (M : X.Modules) : powObj M 0 = M := rfl

/-- The `(k+2)`-nd power is the `(k+1)`-st power tensored on the right with `M`. -/
theorem powObj_succ (M : X.Modules) (k : ℕ) : powObj M (k + 1) = powObj M k ⊗ M := rfl

/-- Every power of an invertible module is invertible. -/
instance isInvertibleModule_powObj (M : X.Modules) [IsInvertibleModule X M] (k : ℕ) :
    IsInvertibleModule X (powObj M k) := by
  induction k with
  | zero => exact ‹IsInvertibleModule X M›
  | succ k ih =>
      rw [powObj_succ]
      have : IsInvertibleModule X (powObj M k) := ih
      infer_instance

/-! ### The powers of a section -/

/-- **The `(k+1)`-st power of a section over an arbitrary open**, formed with
`Stacks.SectionTensorFormula.tensorSection`. For `U = ⊤` this is a power of a global section and
for `U` a trivializing open it is a power of a local generator. -/
def secPow (M : X.Modules) {U : X.Opens} (u : Γ(M, U)) : (k : ℕ) → Γ(powObj M k, U)
  | 0 => u
  | k + 1 => tensorSection (powObj M k) M (secPow M u k) u

/-- The zeroth power `secPow M u 0` of a section is `u`. -/
@[simp] theorem secPow_zero (M : X.Modules) {U : X.Opens} (u : Γ(M, U)) : secPow M u 0 = u := rfl

/-- The `(k+2)`-nd power of a section is the tensor section of its `(k+1)`-st power with `u`. -/
theorem secPow_succ (M : X.Modules) {U : X.Opens} (u : Γ(M, U)) (k : ℕ) :
    secPow M u (k + 1) = tensorSection (powObj M k) M (secPow M u k) u := rfl

/-- **Powers commute with restriction.** The restriction of the `(k+1)`-st power of a section is
the `(k+1)`-st power of its restriction. -/
theorem map_secPow (M : X.Modules) {U V : X.Opens} (h : V ⟶ U) (u : Γ(M, U)) (k : ℕ) :
    (powObj M k).presheaf.map h.op (secPow M u k) = secPow M (M.presheaf.map h.op u) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [secPow_succ, secPow_succ]
      exact (map_tensorSection ..).trans (by rw [ih])

/-- **The power law.** Scaling a section by `a : Γ(X, U)` scales its `(k+1)`-st power by
`a ^ (k+1)`, by bilinearity of `Stacks.SectionTensorFormula.tensorSection`.

With `Stacks.TensorSectionPower.map_secPow` this is the identity
`s ^ (k+1)|_W = f ^ (k+1) · b ^ (k+1)` that the gluing argument of [Stacks, Tag 01PW] runs on,
for `b` an **arbitrary** local generator:
restrict the power of `s` to `W`, rewrite `s|_W = f · b`, and apply this. -/
theorem secPow_smul (M : X.Modules) {U : X.Opens} (a : Γ(X, U)) (u : Γ(M, U)) (k : ℕ) :
    secPow M (a • u) k = a ^ (k + 1) • secPow M u k := by
  induction k with
  | zero => rw [secPow_zero, secPow_zero, pow_one]; rfl
  | succ k ih =>
      rw [secPow_succ, secPow_succ, ih, tensorSection_smul_left, tensorSection_smul_right,
        smul_smul, ← pow_succ]
      rfl

/-! ### The nonvanishing locus of a power -/

/-- **`X_{s ^ (k+1)} = X_s`.** A power of a global section of an invertible module vanishes exactly
where the section does: induction from
`Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection`, whose intersection collapses
because both factors are powers of the same section. -/
theorem nonvanishingLocus_secPow (M : X.Modules) [IsInvertibleModule X M] (s : Γ(M, ⊤))
    (k : ℕ) :
    nonvanishingLocus (powObj M k) (secPow M s k) = nonvanishingLocus M s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [secPow_succ]
      exact (Stacks.TensorSectionProduct.nonvanishingLocus_tensorSection _ _).trans
        (by rw [ih, Set.inter_self])

/-- `X_{s ^ (k+1)} = X_s` as an equality of opens. -/
theorem nonvanishingOpen_secPow (M : X.Modules) [IsInvertibleModule X M] (s : Γ(M, ⊤))
    (k : ℕ) :
    Stacks.NonvanishingOpen.nonvanishingOpen X (powObj M k) (secPow M s k)
      = Stacks.NonvanishingOpen.nonvanishingOpen X M s :=
  TopologicalSpace.Opens.ext (by
    rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen,
      Stacks.NonvanishingOpen.coe_nonvanishingOpen, nonvanishingLocus_secPow])

/-! ### Division by a local generator -/

/-- **Multiplication by the restricted basis section of a trivialization is injective on
scalars.** Apply the trivializing map: it is `Γ(X, W)`-linear and sends the restricted basis
section to `1`. This is the uniqueness half of the division by a local generator; the existence
half is `Stacks.SectionProduct.eq_triv_smul_res_basis`. -/
theorem smul_res_basis_injective {M : X.Modules} {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) {W : X.Opens} (h : W ⟶ V)
    {a a' : Γ(X, W)}
    (haa : a • M.presheaf.map h.op (Stacks.NonvanishingOpen.basis t)
      = a' • M.presheaf.map h.op (Stacks.NonvanishingOpen.basis t)) : a = a' := by
  have hcongr := congrArg (Stacks.NonvanishingOpen.triv t h) haa
  rwa [Stacks.NonvanishingOpen.triv_smul, Stacks.NonvanishingOpen.triv_smul,
    Stacks.NonvanishingOpen.triv_res_basis, mul_one, mul_one] at hcongr

end Stacks.TensorSectionPower

end
