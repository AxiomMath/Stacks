module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.Basic

/-!
# Powers of a homogeneous section, and the ratio of two of them

The proof of the surjectivity half of Stacks Tag 01PW —
`Stacks.SectionExtension.IsSectionRatio`, the one open declaration of the ample cluster — runs
over a finite cover of `X` by affine nonvanishing opens `X_a` and needs, on each of them, the
identity

`(s^k)|_{X_a} = f^k • (a^k)|_{X_a)`,   where   `s|_{X_a} = f • a|_{X_a}`,

for `s` and `a` global sections of one and the same tensor power of `L`. This file supplies both
ingredients: a **power operation on homogeneous sections** of the graded section ring of Stacks
Tag 01CV, which `Stacks.GradedSections` does not define (it has `mul` and the `GradedMonoid`
instances only, and `Stacks.AmpleAffineAvoidance.exists_pow_succ` produces a power only up to its
nonvanishing locus), and that identity.

## Main definitions

* `Stacks.SectionExtension.powSec`: the `k`-th power of a homogeneous section of degree `d`, as a
  homogeneous section of degree `d * k`. The degree needs **no transport**: `Nat.mul` recurses on
  its second argument, so `d * (k + 1)` and `d * k + d` are the same numeral by `rfl`, and
  `Stacks.GradedSections.mul (powSec a k) a` lands in the declared type on the nose.

## Main results

* `Stacks.SectionExtension.resTop_app`: the naturality of a morphism of `𝒪_X`-modules, read on a
  global section and its restriction.
* `Stacks.SectionExtension.resTop_app_of_res_eq`: **the shape in which naturality is used.** A
  ratio relation `x|_U = c • y|_U` between global sections is preserved by every morphism of
  `𝒪_X`-modules, because `φ.app U` is `Γ(X, U)`-linear.
* `Stacks.SectionExtension.resTop_globalSection_powSec`: **the identity above.** Proved by
  induction on `k`, with the only two non-formal inputs being
  `Stacks.SectionProduct.globalSection_mul` (the product is multiplication by the first factor,
  applied to the second) and `Stacks.GradedSections.mul_comm'` (commutativity, which is what lets
  the inductive hypothesis be applied to the *second* factor of the product, where multiplication
  is linear).
* `Stacks.SectionExtension.nvLocus_powSec`: `X_{a^k} = X_a` for `k ≥ 1`, for the actual power
  rather than for some section with the same locus, **given the case `k = 1`**. This is the
  hypothesis `X_s ≤ X_σ` of `Stacks.SectionExtension.IsSectionRatio` at `σ = s^k`.

## No Stacks attribute is attached

Nothing here is a statement of the Stacks Project; it is the arithmetic the proof of Tag 01PW
needs. The label 01PW remains open — see the "What is not done" section of
`Stacks.SectionExtension.Basic` for the three steps that remain after this one.

## The hypothesis of `nvLocus_powSec` is discharged elsewhere

`Stacks.SectionExtension.nvLocus_powSec` carries its own first case as a hypothesis. The induction
step is `X_{st} = X_s ⊓ X_t`, so everything above `k = 1` is free; at `k = 1` the product is `a`
times the zeroth power, which is the *unit* `𝟙 (𝟙_ X.Modules)` of the section ring. The obvious
route is to say that the unit's nonvanishing locus is all of `X`, and that is not available: no
declaration identifies `Stacks.SectionProduct.globalSection X (𝟙_ X.Modules) (𝟙 (𝟙_ X.Modules))`
with the section `1` of `Stacks.Ample.unitModule`.

It is not needed. `Stacks.GradedSections.mulMap_id` expresses `powSec L a 1` as `a` composed with
the degree transport `d = 0 + d`, and
`Stacks.AmpleAffineAvoidance.nvLocus_comp_eqToHom` says a transport leaves the nonvanishing locus
alone — the unit section is gone before any locus is computed. That is
`Stacks.SectionExtension.nvLocus_powSec_one` in
`StacksFrontier/AlgebraicGeometry/SectionExtension/Ample.lean`, and with it
`Stacks.SectionExtension.nvLocus_powSec_of_one_le` is `X_{a^k} = X_a` for `k ≥ 1` with no
hypothesis. The two live there rather than here because
`Stacks.AmpleAffineAvoidance.nvLocus_comp_eqToHom` is not in this file's import closure.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.Ample Stacks.NonvanishingOpen
open Stacks.AmpleFiniteAvoidance
open Stacks.GradedSections Stacks.SectionProduct

universe u

namespace Stacks.SectionExtension

/-! ### Naturality, in the shape a ratio relation needs -/

section Naturality

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **Naturality of a morphism of `𝒪_X`-modules on a global section.** Applying `φ` and then
restricting to `U` is restricting and then applying `φ`. -/
theorem resTop_app (φ : M ⟶ N) (U : X.Opens) (x : Γ(M, ⊤)) :
    resTop U (φ.app ⊤ x) = φ.app U (resTop U x) :=
  (PresheafOfModules.naturality_apply φ.val (homOfLE (le_top : U ≤ ⊤)).op x).symm

/-- **A ratio relation between global sections is preserved by every morphism of
`𝒪_X`-modules.** If `x|_U = c • y|_U` then `(φ x)|_U = c • (φ y)|_U`: naturality moves `φ` past
the restriction and `Γ(X, U)`-linearity moves it past the scalar. This is the only way the
induction below uses that the multiplication of the section ring is given by a *morphism* of
modules. -/
theorem resTop_app_of_res_eq (φ : M ⟶ N) {U : X.Opens} (c : Γ(X, U)) (x y : Γ(M, ⊤))
    (h : resTop U x = c • resTop U y) :
    resTop U (φ.app ⊤ x) = c • resTop U (φ.app ⊤ y) := by
  rw [resTop_app, h, Scheme.Modules.Hom.app_smul, resTop_app]

end Naturality

/-! ### Powers of a homogeneous section -/

section Powers

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

attribute [local implicit_reducible] Stacks.TensorPowers.natTensorPow

variable {X : Scheme.{u}} (L : X.Modules)

/-- **The `k`-th power of a homogeneous section of degree `d`**, a homogeneous section of degree
`d * k`. The zeroth power is the identity of the monoidal unit, which is the `1` of the section
ring, and the successor multiplies on the right by `a`.

No degree transport appears: `d * (k + 1)` reduces to `d * k + d`, which is the degree
`Stacks.GradedSections.mul` produces. -/
def powSec {d : ℕ} (a : powSections L d) : (k : ℕ) → powSections L (d * k)
  | 0 => 𝟙 (𝟙_ X.Modules)
  | (k + 1) => mul (powSec a k) a

/-- The zeroth power of a homogeneous section is the identity of the monoidal unit. -/
@[simp] theorem powSec_zero {d : ℕ} (a : powSections L d) :
    powSec L a 0 = 𝟙 (𝟙_ X.Modules) := rfl

/-- The `(k + 1)`-th power of a homogeneous section `a` is the product of its `k`-th power with
`a`. -/
theorem powSec_succ {d : ℕ} (a : powSections L d) (k : ℕ) :
    powSec L a (k + 1) = mul (powSec L a k) a := rfl

variable [IsInvertibleModule X L]

/-- **`X_{a^(k+1)} = X_{a^k} ⊓ X_a`**, which is `X_{st} = X_s ⊓ X_t` at a power. The step of the
induction that gives `X_{a^k} = X_a` for `k ≥ 1`; its base case `k = 1` needs the nonvanishing
locus of the unit of the section ring, for which see "What is not done". -/
theorem nvLocus_powSec_succ {d : ℕ} (a : powSections L d) (k : ℕ) :
    nvLocus L (powSec L a (k + 1)) = nvLocus L (powSec L a k) ∩ nvLocus L a :=
  nvLocus_mul L (powSec L a k) a

/-- **`X_{a^k} = X_a` for `k ≥ 1`**, given it in the first degree. Stated for
`Stacks.SectionExtension.powSec`, the actual power, rather than for some section that happens to
have the same nonvanishing locus, which is what
`Stacks.AmpleAffineAvoidance.exists_pow_succ` provides. -/
theorem nvLocus_powSec {d : ℕ} (a : powSections L d)
    (h1 : nvLocus L (powSec L a 1) = nvLocus L a) (k : ℕ) (hk : 1 ≤ k) :
    nvLocus L (powSec L a k) = nvLocus L a := by
  induction k with
  | zero => omega
  | succ k ih =>
      match k with
      | 0 => exact h1
      | j + 1 => rw [nvLocus_powSec_succ, ih (by omega), Set.inter_self]

/-- **The identity the gluing argument of Stacks Tag 01PW turns on.** Let `a` and `s` be global
sections of the same tensor power of `L`, and suppose that on an open `U` the section `s` is `f`
times `a`. Then on `U` the `k`-th power of `s` is `f^k` times the `k`-th power of `a`.

The induction step is three applications of `resTop_app_of_res_eq`. For the outer factor the
relation applied is the hypothesis `hf` itself; for the inner one it is the inductive hypothesis,
and reaching it needs `Stacks.GradedSections.mul_comm'`, because the product
`Stacks.GradedSections.mul x y` is linear in `y` and the inductive hypothesis is about the power,
which sits in the *first* position of `powSec L s (k + 1) = mul (powSec L s k) s`.

No hypothesis relating `U` to a nonvanishing locus is used: the statement is an identity between
restrictions, and the geometry enters only through the existence of `f`, which is where
`Stacks.NonvanishingSpelling.bijective_smul` is applied by the caller. -/
theorem resTop_globalSection_powSec {d : ℕ} (a s : powSections L d) {U : X.Opens} (f : Γ(X, U))
    (hf : resTop U (globalSection X _ s) = f • resTop U (globalSection X _ a)) (k : ℕ) :
    resTop U (globalSection X _ (powSec L s k))
      = f ^ k • resTop U (globalSection X _ (powSec L a k)) := by
  induction k with
  | zero => rw [powSec_zero, powSec_zero, pow_zero, one_smul]
  | succ k ih =>
      -- `powSec L _ (k + 1)` is `mul (powSec L _ k) _` by definition, and the degree
      -- `d * (k + 1)` is the numeral `d * k + d`; restate the goal in that spelling so that the
      -- three identities below, which `Stacks.GradedSections.mul` states at `d * k + d`, rewrite.
      show resTop U (globalSection X (Stacks.TensorPowers.natTensorPow L (d * k + d))
              (mul (powSec L s k) s))
            = f ^ (k + 1) • resTop U
              (globalSection X (Stacks.TensorPowers.natTensorPow L (d * k + d))
                (mul (powSec L a k) a))
      -- the inner factor, reached through commutativity so that the power is the second argument
      have hcomm : ∀ t : powSections L d,
          globalSection X _ (mul (powSec L t k) a) =
            (mulMap a (d * k) ≫ powCongr L (Nat.add_comm d (d * k))).app ⊤
              (globalSection X _ (powSec L t k)) := by
        intro t
        rw [← mul_comm' a (powSec L t k), globalSection_comp, Scheme.Modules.Hom.comp_app]
        rfl
      have hinner : resTop U (globalSection X _ (mul (powSec L s k) a))
          = f ^ k • resTop U (globalSection X _ (mul (powSec L a k) a)) := by
        rw [hcomm s, hcomm a]
        exact resTop_app_of_res_eq _ _ _ _ ih
      -- the outer factor, reached through the hypothesis on `s` itself
      have houter : resTop U (globalSection X _ (mul (powSec L s k) s))
          = f • resTop U (globalSection X _ (mul (powSec L s k) a)) := by
        rw [globalSection_mul, globalSection_mul]
        exact resTop_app_of_res_eq _ _ _ _ hf
      rw [houter, hinner, smul_smul, ← pow_succ']

end Powers

end Stacks.SectionExtension

end
