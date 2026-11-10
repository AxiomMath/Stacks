module

public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.Basic

/-!
# The multiplicative family: powers of one global section trivializing every tensor power

`StacksFrontier/AlgebraicGeometry/TensorPowerTrivialize/Basic.lean` builds, for a global section
`u` of an invertible `𝒪_X`-module and any open `V` inside `X_u`, a sectionwise trivialization of
that module over `V` whose basis section is `u|_V`. This file applies that to the powers of one
global section of a tensor power of `L`, which is what the gluing argument of Stacks Tag 01PW
needs: **one** open `V`, and on it a generator of `L ^⊗ n`, of `L ^⊗ 2n`, of `L ^⊗ 3n`, … all of
which are the successive powers of a single section.

The two facts that make this work are both already available. `Stacks.GradedSections.mul` multiplies
two global sections of tensor powers, and `Stacks.SectionProduct.nonvanishingOpen_mul` says
`X_{st} = X_s ⊓ X_t`; so the nonvanishing open of a power of `u` is the nonvanishing open of `u`
itself, in every positive exponent, and one and the same `V ≤ X_u` serves every degree.

## Main definitions

* `Stacks.TensorPowerTrivialize.powDeg` and `Stacks.TensorPowerTrivialize.sectionPow`: the
  degree `n * (k + 1)` and the `(k+1)`-st power of a global section of `L ^⊗ n`, both by their
  own recursion so that **no transport appears anywhere**. Indexing from the first power rather
  than the zeroth is what buys this: `sectionPow L u 0` is `u` itself, where a zeroth entry would
  force the degree `n * 1`, which is `0 + n` and not `n`.
* `Stacks.TensorPowerTrivialize.trivializationPow`: **the compatible family.** For every
  `k`, a `Stacks.SheafDescent.Trivialization` of `L ^⊗ (n * (k + 1))` over the same open
  `V ≤ X_u`, with basis section the restriction of `u ^ (k + 1)`.

## Main results

* `Stacks.TensorPowerTrivialize.nonvanishingLocus_sectionPow` and
  `nonvanishingOpen_sectionPow`: `X_{u^(k+1)} = X_u`, so one open `V ≤ X_u` is inside the
  nonvanishing locus of every positive power at once. Induction on `k` from
  `Stacks.SectionProduct.nonvanishingLocus_mul`, with an identity for the base case. **This is
  unconditional**, and the indexing is why: the sibling statement
  `Stacks.SectionExtension.nvLocus_powSec`, whose power is indexed from the zeroth, has to carry
  its own first case as a hypothesis `h1`, and its "What is not done" records that discharging
  it needs a lemma saying that the nonvanishing locus of the unit of the section ring is all of
  `X` — a lemma nobody has written. Starting the recursion at the first power removes the need
  for it: the unit section never occurs.
* `Stacks.TensorPowerTrivialize.basis_trivializationPow`: the basis section of the `k`-th member
  of the family is `u ^ (k + 1)|_V`.
* `Stacks.TensorPowerTrivialize.resTop_sectionPow`: **the multiplicativity of the ratio.** If
  `s|_V = f · u|_V` for two global sections of the same tensor power, then
  `s ^ (k+1)|_V = f ^ (k+1) · u ^ (k+1)|_V`. This is the identity
  "`s^e|_{U_j} = f_j^e · q_j^e`" that Stacks Tag 01PW's gluing argument runs on, and the one
  thing a trivialization with an unnamed local generator cannot supply.
* `Stacks.TensorPowerTrivialize.resTop_sectionPow_trivTop`: the same with `f` produced rather
  than assumed, as the trivializing function of `s` against the generator `u|_V`.
* `Stacks.TensorPowerTrivialize.resTop_globalSection_mul`: **multiplication of a local section by
  a global one.** The restriction to `V` of the global section of a product `s · t` is
  multiplication by `s` — a morphism of sheaves of modules, hence available over every open —
  applied to the restriction of `t`. This is the handle that lets the Stacks argument multiply
  the *local* generator of `L ^⊗ n` over `V` by a global section and stay over `V`.
* `Stacks.TensorPowerTrivialize.exists_isAffineOpen_trivialization_natTensorPow`: an affine
  trivializing open through every point for the nonnegative power family, the statement that
  could not be made in the sibling file for want of the monoidal instances.

## The degree bookkeeping, and why there is almost none

`Stacks.TensorPowerTrivialize.powDeg` is defined by recursion rather than as `n * (k + 1)`, which
makes the definition of `sectionPow` and both of its recursion equations transport-free. The only
transport anywhere is the single `Stacks.GradedSections.powCongr` inside the proof of
`resTop_sectionPow`, inserted by `Stacks.GradedSections.mul_comm'` and cancelled on both sides of
the equation; it is needed because the induction hypothesis has to be substituted *under* a
multiplication map, and only multiplication by the left factor is a morphism independent of the
section being multiplied.

## Implementation notes

**The monoidal structure on `X.Modules` is a local instance.** `Stacks.GradedSections.powSections`
and `Stacks.TensorPowers.natTensorPow` are stated in a monoidal category, and `X.Modules` carries
no global monoidal instance; the eight local instances reintroduced below are exactly the list
that `StacksFrontier/AlgebraicGeometry/SectionProduct/Basic.lean` uses.
`Stacks.SectionRingGeometric.schemeSectionCommRing` is deliberately **not** among them: with it
in scope `GradedRing (summand (powSections L))` becomes unsynthesizable, and nothing here needs
the ring structure on the direct sum — only the product of two homogeneous sections.

**`Stacks.SectionProduct.globalSection` is the bridge to honest sections.** A
`Stacks.GradedSections.powSections L n` is a morphism `𝟙_ X.Modules ⟶ L ^⊗ n`, not an element of
`Γ(L ^⊗ n, ⊤)`; the two are identified by that function, which is compatible with composition by
`Stacks.SectionProduct.globalSection_comp`.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)

## What is not done

**Stacks Tag 01PW is not proved**, and no Stacks attribute is attached to anything here. What is
supplied is the local input of its proof on one member of a cover; the two steps still owed are
global. First, the cover: for `X` quasi-compact a *finite* family of affine opens of the shape
`V ≤ X_u` must be extracted, which needs a supply of global sections of positive powers through
every point — that is ampleness, so nothing here applies to an arbitrary invertible module on a
quasi-compact scheme, which is the hypothesis of the source statement. Second, the gluing: the
sections produced on the members must be shown to agree on the overlaps after multiplying by a
further power of `s`, and glued by the sheaf condition. Nor is anything proved about a general
quasi-coherent `F`; everything here is about the structure sheaf and the powers of `L`, which is
the case `F = 𝒪_X` of the source lemma.

The exponents are also only nonnegative: `Stacks.TensorPowerTrivialize.sectionPow` is indexed by
`ℕ`, and nothing is said about the inverse sections of degree `-n` that the full statement of
`Γ_*(X, L)_{(s)}` involves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.SheafOfModules.TensorSheafification
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul)
open Stacks.SectionProduct (globalSection)

universe u

namespace Stacks.TensorPowerTrivialize

/-! ### Restriction along a morphism of modules -/

variable {X : Scheme.{u}}

/-- **Restriction commutes with a morphism of `𝒪_X`-modules.** The restriction to `V` of the
image of a global section under `φ` is `φ` over `V` applied to the restriction. This is the
naturality of `AlgebraicGeometry.Scheme.Modules.Hom.mapPresheaf`, read on an element. -/
theorem resTop_app {M N : X.Modules} (φ : M ⟶ N) (t : Γ(M, ⊤)) (V : X.Opens) :
    resTop N (φ.app ⊤ t) V = φ.app V (resTop M t V) := by
  have h := ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality (homOfLE (le_top : V ≤ ⊤)).op) t
  simpa using h.symm

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Powers of a global section of a tensor power -/

/-- The degree of the `(k+1)`-st power of a global section of `L ^⊗ n`. Defined by its own
recursion rather than as `n * (k + 1)` so that **no transport appears anywhere**: the zeroth
entry is `n` on the nose, so the first power is the section itself, and the step adds `n` on the
right, which is exactly the degree `Stacks.GradedSections.mul` returns.
`Stacks.TensorPowerTrivialize.powDeg_eq` identifies it with `n * (k + 1)`. -/
def powDeg (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => powDeg n k + n

/-- The zeroth entry of `powDeg n` is `n`, by definition. -/
theorem powDeg_zero (n : ℕ) : powDeg n 0 = n := rfl

/-- Each step of `powDeg n` adds `n` on the right, by definition. -/
theorem powDeg_succ (n k : ℕ) : powDeg n (k + 1) = powDeg n k + n := rfl

/-- `powDeg n k` is `n * (k + 1)`, the degree of the `(k+1)`-st power of a section of degree
`n`. -/
theorem powDeg_eq (n k : ℕ) : powDeg n k = n * (k + 1) := by
  induction k with
  | zero => rw [powDeg_zero, Nat.mul_one]
  | succ k ih => rw [powDeg_succ, ih]; ring

variable (L : X.Modules)

/-- **The `(k+1)`-st power of a global section of `L ^⊗ n`**, as a global section of
`L ^⊗ (powDeg n k)`, that is of `L ^⊗ (n * (k + 1))`. Indexed from the first power rather than
from the zeroth, because `sectionPow L u 0` is then `u` itself with no transport: the degree of
the zeroth power would be `n * 0`, and `n * 1` is `0 + n` rather than `n`, so an index starting
at the unit section costs a `Stacks.GradedSections.powCongr` in every statement below. -/
noncomputable def sectionPow {n : ℕ} (u : powSections L n) :
    (k : ℕ) → powSections L (powDeg n k)
  | 0 => u
  | k + 1 => mul (sectionPow u k) u

/-- The first power of a section is the section itself, with no transport. -/
@[simp] theorem sectionPow_zero {n : ℕ} (u : powSections L n) : sectionPow L u 0 = u := rfl

/-- The `(k+2)`-nd power of `u` is the `(k+1)`-st power multiplied by `u` on the right. -/
theorem sectionPow_succ {n : ℕ} (u : powSections L n) (k : ℕ) :
    sectionPow L u (k + 1) = mul (sectionPow L u k) u := rfl

/-! ### Multiplying a local section by a global one -/

/-- **Restriction of the global section of a composite.** For `t` a morphism out of the monoidal
unit and `φ` a morphism of modules, the restriction to `V` of the global section of `t ≫ φ` is
`φ` over `V` applied to the restriction of the global section of `t`. -/
theorem resTop_globalSection_comp {M N : X.Modules} (t : 𝟙_ X.Modules ⟶ M) (φ : M ⟶ N)
    (V : X.Opens) :
    resTop N (globalSection X N (t ≫ φ)) V = φ.app V (resTop M (globalSection X M t) V) := by
  rw [Stacks.SectionProduct.globalSection_comp, resTop_app]

/-- **Multiplication by a global section of a tensor power, on sections over an open.** The
restriction to `V` of the global section of a product `s · t` is multiplication by `s` — the
morphism of sheaves of modules `Stacks.GradedSections.mulMap s m`, hence defined on sections over
*every* open — applied to the restriction of `t`.

This is the handle Stacks Tag 01PW's gluing argument needs: the generators of the compatible
family below are restrictions of global sections, so products of them never leave `V`, and the
scalar in `a · t|_V` passes through by
`AlgebraicGeometry.Scheme.Modules.Hom.app_smul`. -/
theorem resTop_globalSection_mul {n m : ℕ} (s : powSections L n) (t : powSections L m)
    (V : X.Opens) :
    resTop (natTensorPow L (n + m)) (globalSection X _ (mul s t)) V
      = (Stacks.GradedSections.mulMap s m).app V
          (resTop (natTensorPow L m) (globalSection X _ t) V) := by
  rw [Stacks.SectionProduct.globalSection_mul, resTop_app]

/-- `resTop_globalSection_mul` at a power: the restriction of `u ^ (k + 2)` is multiplication by
`u ^ (k + 1)` applied to the restriction of `u`. -/
theorem resTop_sectionPow_succ {n : ℕ} (u : powSections L n) (k : ℕ) (V : X.Opens) :
    resTop (natTensorPow L (powDeg n (k + 1))) (globalSection X _ (sectionPow L u (k + 1))) V
      = (Stacks.GradedSections.mulMap (sectionPow L u k) n).app V
          (resTop (natTensorPow L n) (globalSection X _ u) V) :=
  resTop_globalSection_mul L (sectionPow L u k) u V

variable [Stacks.Ample.IsInvertibleModule X L]

/-- **`X_{u^(k+1)} = X_u`.** A positive power of a global section of a tensor power vanishes
exactly where the section does, so one open `V ≤ X_u` is inside the nonvanishing locus of every
positive power at once. Induction from `Stacks.SectionProduct.nonvanishingLocus_mul`; the base
case is an identity, which is what the indexing of
`Stacks.TensorPowerTrivialize.sectionPow` buys. -/
theorem nonvanishingLocus_sectionPow {n : ℕ} (u : powSections L n) (k : ℕ) :
    Stacks.Ample.nonvanishingLocus (natTensorPow L (powDeg n k))
        (globalSection X _ (sectionPow L u k))
      = Stacks.Ample.nonvanishingLocus (natTensorPow L n) (globalSection X _ u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have h := Stacks.SectionProduct.nonvanishingLocus_mul L (powDeg n k) n
        (sectionPow L u k) u
      rw [ih, Set.inter_self] at h
      exact h

/-- `X_{u^(k+1)} = X_u` as an equality of open subsets. -/
theorem nonvanishingOpen_sectionPow {n : ℕ} (u : powSections L n) (k : ℕ) :
    Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L (powDeg n k))
        (globalSection X _ (sectionPow L u k))
      = Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L n)
          (globalSection X _ u) :=
  Opens.ext (nonvanishingLocus_sectionPow L u k)

/-! ### The compatible family of trivializations -/

/-- **One open, a generator in every positive multiple of the degree, and the generators are the
powers of one global section.** For `u` a global section of `L ^⊗ n` and `V` any open inside
`X_u`, this is a sectionwise trivialization of `L ^⊗ (n * (k + 1))` over `V` for every `k`,
with basis section `u ^ (k + 1)|_V` (`basis_trivializationPow`).

This is the data that the finite-affine-cover argument of Stacks Tag 01PW uses on each member of
its cover. -/
noncomputable def trivializationPow {n : ℕ} (u : powSections L n) (k : ℕ) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L n)
            (globalSection X _ u)) :
    Stacks.SheafDescent.Trivialization X.presheaf (natTensorPow L (powDeg n k)).val V :=
  trivializationOfSection _ (globalSection X _ (sectionPow L u k))
    (hV.trans_eq (nonvanishingOpen_sectionPow L u k).symm)

/-- The basis section of the `k`-th member of the family is the restriction of `u ^ (k + 1)`. -/
theorem basis_trivializationPow {n : ℕ} (u : powSections L n) (k : ℕ) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L n)
            (globalSection X _ u)) :
    Stacks.NonvanishingOpen.basis (trivializationPow L u k hV)
      = resTop _ (globalSection X _ (sectionPow L u k)) V :=
  basis_trivializationOfSection _ _ _

/-- **`X_s ∩ V` is the basic open of the ratio `s / u^(k+1)`**, for `V ≤ X_u` and `s` any global
section of `L ^⊗ (n * (k + 1))`. The step "`X_s ∩ U_j = D(f_j)`" of Stacks Tag 01PW's proof, at
the member of the compatible family of the right degree. -/
theorem nonvanishingLocus_inter_eq_basicOpen_pow {n : ℕ} (u : powSections L n) (k : ℕ)
    {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L n)
            (globalSection X _ u))
    (s : Γ(natTensorPow L (powDeg n k), ⊤)) :
    Stacks.Ample.nonvanishingLocus (natTensorPow L (powDeg n k)) s ∩ (V : Set X)
      = (X.basicOpen (Stacks.NonvanishingOpen.trivTop
          (trivializationPow L u k hV) s) : Set X) :=
  Stacks.NonvanishingOpen.nonvanishingLocus_inter (trivializationPow L u k hV) s

/-! ### Multiplicativity of the ratio -/

/-- **The ratio of two global sections of one tensor power is multiplicative in the powers.** If a
global section `s` of `L ^⊗ n` is `f` times a global section `u` of the same power on an open `V`,
then `s ^ (k+1)` is `f ^ (k+1)` times `u ^ (k+1)` there.

This is the identity "`s^e|_{U_j} = f_j^e · q_j^e`" that the gluing argument of Stacks Tag 01PW
runs on, and it is exactly what a trivialization whose generator is an *unnamed* local choice
cannot give: the proof multiplies by the global sections `s` and `u` through the sheaf morphisms
`Stacks.GradedSections.mulMap s n` and `Stacks.GradedSections.mulMap u (powDeg n k)`, which act on
sections over every open, and carries the scalar through them with
`AlgebraicGeometry.Scheme.Modules.Hom.app_smul`. The only degree bookkeeping is the single
commutation `Stacks.GradedSections.mul_comm'` needed to move `u` from the right of the product to
the left, so that multiplication is by a morphism depending on `u` alone and the induction
hypothesis can be substituted under it. -/
theorem resTop_sectionPow {n : ℕ} (u s : powSections L n) {V : X.Opens} (f : Γ(X, V))
    (hf : resTop (natTensorPow L n) (globalSection X _ s) V
            = f • resTop (natTensorPow L n) (globalSection X _ u) V) (k : ℕ) :
    resTop (natTensorPow L (powDeg n k)) (globalSection X _ (sectionPow L s k)) V
      = f ^ (k + 1) • resTop (natTensorPow L (powDeg n k))
          (globalSection X _ (sectionPow L u k)) V := by
  induction k with
  | zero =>
      simp only [zero_add, pow_one]
      exact hf
  | succ k ih =>
      have hmix : resTop (natTensorPow L (powDeg n k + n))
            (globalSection X _ (mul (sectionPow L s k) u)) V
          = f ^ (k + 1) • resTop (natTensorPow L (powDeg n k + n))
              (globalSection X _ (mul (sectionPow L u k) u)) V := by
        rw [← Stacks.GradedSections.mul_comm' u (sectionPow L s k),
          ← Stacks.GradedSections.mul_comm' u (sectionPow L u k),
          resTop_globalSection_comp, resTop_globalSection_comp,
          resTop_globalSection_mul, resTop_globalSection_mul, ih,
          Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
      change resTop (natTensorPow L (powDeg n k + n))
            (globalSection X _ (mul (sectionPow L s k) s)) V
          = f ^ (k + 1 + 1) • resTop (natTensorPow L (powDeg n k + n))
              (globalSection X _ (mul (sectionPow L u k) u)) V
      rw [resTop_globalSection_mul, hf, Scheme.Modules.Hom.app_smul,
        ← resTop_globalSection_mul, hmix, smul_smul, ← pow_succ' f (k + 1)]

/-- **The package Stacks Tag 01PW's gluing argument opens with, on one open.** Let `u` and `s` be
global sections of `L ^⊗ n` and let `V` be any open inside `X_u`. Write `f` for the ratio `s/u`
on `V`, the trivializing function of `s` against the generator `u|_V`. Then for every `k`,

`s ^ (k+1)|_V = f ^ (k+1) · u ^ (k+1)|_V`,

where `u ^ (k+1)|_V` generates `L ^⊗ (n * (k+1))` freely over `V`
(`Stacks.TensorPowerTrivialize.trivializationPow`,
`Stacks.TensorPowerTrivialize.basis_trivializationPow`) and
`X_s ∩ V = D(f)` (`Stacks.TensorPowerTrivialize.nonvanishingLocus_inter_eq_basicOpen`). -/
theorem resTop_sectionPow_trivTop {n : ℕ} (u s : powSections L n) {V : X.Opens}
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (natTensorPow L n)
            (globalSection X _ u)) (k : ℕ) :
    resTop (natTensorPow L (powDeg n k)) (globalSection X _ (sectionPow L s k)) V
      = Stacks.NonvanishingOpen.trivTop
            (trivializationOfSection _ (globalSection X _ u) hV) (globalSection X _ s) ^ (k + 1)
          • resTop (natTensorPow L (powDeg n k)) (globalSection X _ (sectionPow L u k)) V :=
  resTop_sectionPow L u s _
    (resTop_eq_ratio_smul (natTensorPow L n) (globalSection X _ u) (globalSection X _ s) hV) k

/-! ### Affine trivializing opens for the nonnegative power family -/

/-- **Every nonnegative tensor power of an invertible `𝒪_X`-module is sectionwise trivial on an
affine open through every point.** The statement of
`Stacks.TensorPowerTrivialize.exists_isAffineOpen_trivialization_tensorPowModule` at the power
family the graded ring of sections of Stacks Tag 01CV is built from; it needs the monoidal
instances of this section to be stated at all. -/
theorem exists_isAffineOpen_trivialization_natTensorPow (n : ℕ) (x : X) :
    ∃ V : X.Opens, x ∈ V ∧ IsAffineOpen V ∧
      Nonempty (Stacks.SheafDescent.Trivialization X.presheaf (natTensorPow L n).val V) :=
  exists_isAffineOpen_trivialization (natTensorPow L n) x

end Monoidal

end Stacks.TensorPowerTrivialize

end
