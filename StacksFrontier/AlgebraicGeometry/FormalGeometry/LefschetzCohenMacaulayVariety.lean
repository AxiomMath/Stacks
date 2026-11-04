module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SerreCondition
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.LefschetzZeroSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.CohenMacaulayDepthDimensionBound
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Lefschetz comparison on Cohen–Macaulay proper varieties

Let `k` be a field, `X` a proper variety over `k`, `L` an ample invertible `𝒪_X`-module, `s` a
global section of `L` with zero scheme `Y = Z(s)` and `n`-th infinitesimal neighbourhood
`Yₙ = Z(sⁿ)`, and let `𝓔` be a finite locally free `𝒪_X`-module. [Stacks, Tag 0EL3] lists what
[Stacks, Tag 0EL1] gives for the comparison maps `Hⁱ(X, 𝓔) ⟶ lim Hⁱ(Yₙ, 𝓔ₙ)` when `X` has small
dimension:

1. on a curve, nothing;
2. on a Cohen–Macaulay (for example normal) surface, `H⁰(X, 𝓔) ⟶ lim H⁰(Yₙ, 𝓔ₙ)` is an
   isomorphism;
3. on a Cohen–Macaulay threefold, `H⁰(X, 𝓔) ⟶ lim H⁰(Yₙ, 𝓔ₙ)` and
   `H¹(X, 𝓔) ⟶ lim H¹(Yₙ, 𝓔ₙ)` are isomorphisms;

and closes with the remark that on a normal threefold one still gets the statement for `H⁰`.
Clause (1) records the absence of a conclusion (the range `0 ≤ i < σ = 0` is empty) and is not a
statement; so is the half of the closing remark saying that `H¹` is not obtained.

## The argument

Let `X` have dimension at least `d` and satisfy Serre's condition `(S_d)`; a Cohen–Macaulay
scheme satisfies `(S_d)` for every `d` and a normal one satisfies `(S₂)`. At a point `x` the stalk
`𝓔_x` is finite free over `𝒪_{X,x}`, so `depth(𝓔_x) ≥ depth(𝒪_{X,x}) ≥ min(d, dim(𝒪_{X,x}))`,
and the dimension formula on a variety gives `dim(𝒪_{X,x}) + dim({x}‾) = dim(X) ≥ d`. Hence

`depth(𝓔_x) + dim({x}‾) ≥ d > d - 1`

everywhere, which is the hypothesis of [Stacks, Tag 0EL1]
(`Stacks.Algebraization.isIso_zeroSchemeComparison_of_isProper`) at `σ = d - 1`; it gives every
degree `i < d - 1`. A Cohen–Macaulay surface is `d = 2`, a Cohen–Macaulay threefold `d = 3`, and
a normal surface or threefold is `d = 2` through `(S₂)`.

The source's effective Cartier divisor `Y` with `𝒪_X(Y)` ample is the zero scheme of the
canonical section of the ample invertible module `𝒪_X(Y)`, its `n`-th infinitesimal
neighbourhood being the zero scheme of the `n`-th power of that section. The statements below
are for the zero scheme of an arbitrary global section of an ample invertible module, which
contains that case.

## Main results

* `Stacks.Algebraization.intCast_le_sheafDepthAt_add_dimClosureAt_of_hasPropertySk` — the bound
  `depth(𝓔_x) + dim({x}‾) ≥ d` under `(S_d)` and `dim(X) ≥ d`.
* `Stacks.Algebraization.isIso_zeroSchemeComparison_of_hasPropertySk` — the general pattern:
  every degree `i` with `i + 1 < d`.
* `Stacks.Algebraization.isIso_zeroSchemeComparison_zero_of_isCohenMacaulay_surface` —
  **[Stacks, Tag 0EL3], clause (2)**.
* `Stacks.Algebraization.isIso_zeroSchemeComparison_of_isCohenMacaulay_threefold` —
  **[Stacks, Tag 0EL3], clause (3)**.
* `Stacks.Algebraization.isIso_zeroSchemeComparison_zero_of_isNormal` — **[Stacks, Tag 0EL3],
  the normal case**: the "for example normal" of clause (2) and the closing remark on normal
  threefolds, for a normal proper variety of any dimension at least two.

## Implementation notes

The comparison map `Stacks.Algebraization.zeroSchemeComparison` is stated for a quasi-coherent
module, and the quasi-coherence of `𝓔` is supplied inside each statement by
`Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree`, so that it
is not an extra hypothesis. Being a proposition, that instance agrees with any other.

## References

* [Stacks Project, Tag 0EL3](https://stacks.math.columbia.edu/tag/0EL3)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 033Q](https://stacks.math.columbia.edu/tag/033Q)
* [Stacks Project, Tag 0342](https://stacks.math.columbia.edu/tag/0342)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### The depth–dimension bound under Serre's condition -/

/-- A lower bound `d ≤ a + c` in `WithBot ℕ∞`, together with a bound `min(d, a) ≤ e` on the
truncation of `a`, gives `d ≤ e + c` in the extended integers. -/
lemma intCast_le_enatToEInt_add_krullDimToEInt_of_min_le {d : ℕ} {a c : WithBot ℕ∞} {e : ℕ∞}
    (hsum : ((d : ℕ) : WithBot ℕ∞) ≤ a + c) (he : min ((d : ℕ) : WithBot ℕ∞) a ≤ e) :
    ((d : ℤ) : EInt) ≤ enatToEInt e + krullDimToEInt c := by
  induction a using WithBot.recBotCoe with
  | bot => simp at hsum
  | coe a =>
  induction c using WithBot.recBotCoe with
  | bot => simp at hsum
  | coe c =>
  induction c using ENat.recTopCoe with
  | top =>
    induction e using ENat.recTopCoe with
    | top => exact le_top
    | coe e => exact le_top
  | coe c =>
  induction e using ENat.recTopCoe with
  | top => exact le_top
  | coe e =>
  show ((d : ℤ) : EInt) ≤ ((e : ℤ) : EInt) + ((c : ℤ) : EInt)
  have hadd : ((e : ℤ) : EInt) + ((c : ℤ) : EInt) = (((e + c : ℕ) : ℤ) : EInt) := by
    push_cast
    rfl
  rw [hadd]
  refine WithBotTop.coe_le_coe.mpr (Int.ofNat_le.mpr ?_)
  have hsum' : (d : ℕ∞) ≤ a + c := by exact_mod_cast hsum
  have he' : min (d : ℕ∞) a ≤ e := by exact_mod_cast he
  induction a using ENat.recTopCoe with
  | top =>
    rw [min_eq_left le_top] at he'
    have : d ≤ e := by exact_mod_cast he'
    omega
  | coe a =>
    have h1 : d ≤ a + c := by exact_mod_cast hsum'
    rcases le_total d a with hda | hda
    · rw [min_eq_left (by exact_mod_cast hda)] at he'
      have : d ≤ e := by exact_mod_cast he'
      omega
    · rw [min_eq_right (by exact_mod_cast hda)] at he'
      have : a ≤ e := by exact_mod_cast he'
      omega

/-- **The depth–dimension bound under Serre's condition `(S_d)`.** Let `X` be an irreducible
scheme locally of finite type over a field `k`, of dimension at least `d` and satisfying Serre's
condition `(S_d)`, and let `𝓔` be a finite locally free `𝒪_X`-module. Then
`depth(𝓔_x) + dim({x}‾) ≥ d` at every point `x` of `X`, in the extended integers in which
[Stacks, Tag 0EL1] states its hypothesis.

The stalk `𝓔_x` is finite free, so its depth is at least `depth(𝒪_{X,x})`, which `(S_d)` bounds
below by `min(d, dim(𝒪_{X,x}))`; and `dim(𝒪_{X,x}) + dim({x}‾) = dim(X) ≥ d` by the dimension
formula. -/
theorem intCast_le_sheafDepthAt_add_dimClosureAt_of_hasPropertySk
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [IrreducibleSpace X] [IsLocallyNoetherian X] (E : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (d : ℕ)
    (hSk : HasPropertySk X d) (hdim : ((d : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) (x : X) :
    ((d : ℤ) : EInt) ≤ enatToEInt (sheafDepthAt E x) + krullDimToEInt (dimClosureAt X x) :=
  intCast_le_enatToEInt_add_krullDimToEInt_of_min_le
    (hdim.trans (ringKrullDim_stalk_add_dimClosureAt k X f x).ge)
    ((hSk x).trans (WithBot.coe_le_coe.mpr (depth_stalk_le_sheafDepthAt E x)))

/-! ### The general pattern -/

/-- **The pattern of [Stacks, Tag 0EL3].** Let `X` be a proper variety over a field `k`, `L` an
ample invertible `𝒪_X`-module, `s` a global section of `L` with zero scheme `Y` and `n`-th
infinitesimal neighbourhood `Yₙ`, and `𝓔` a finite locally free `𝒪_X`-module. If `X` has
dimension at least `d` and satisfies Serre's condition `(S_d)`, then
`Hⁱ(X, 𝓔) ⟶ lim Hⁱ(Yₙ, 𝓔ₙ)` is an isomorphism for every `i` with `i + 1 < d`.

This is [Stacks, Tag 0EL1] at `σ = d - 1`, its hypothesis being
`Stacks.Algebraization.intCast_le_sheafDepthAt_add_dimClosureAt_of_hasPropertySk`. -/
@[sga "2 X 2.2" "(i)"]
theorem isIso_zeroSchemeComparison_of_hasPropertySk
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProperVariety k fX]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (s : Γ(L, ⊤)) (E : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (d : ℕ)
    (hSk : haveI := LocallyOfFiniteType.isLocallyNoetherian fX; HasPropertySk X d)
    (hdim : ((d : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) (i : ℕ) (hi : i + 1 < d) :
    haveI := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    IsIso (zeroSchemeComparison X L s E i) := by
  have := LocallyOfFiniteType.isLocallyNoetherian fX
  have := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X E
  refine isIso_zeroSchemeComparison_of_isProper k fX L hL s E ((d : ℤ) - 1) (fun x _ => ?_) i
    (by omega)
  refine lt_of_lt_of_le ?_
    (intCast_le_sheafDepthAt_add_dimClosureAt_of_hasPropertySk k fX E d hSk hdim x)
  exact WithBotTop.coe_lt_coe.mpr (by omega)

/-! ### Stacks 0EL3 -/

/-- **Stacks Project, Tag 0EL3 (Example 52.28.3), clause (2).** Let `k` be a field, `X` a proper
variety over `k`, `L` an ample invertible `𝒪_X`-module (the source's `𝒪_X(Y)`), `s` a global
section of `L` with zero scheme `Y` and `n`-th infinitesimal neighbourhood `Yₙ`, and `𝓔` a finite
locally free `𝒪_X`-module. If `X` is a Cohen–Macaulay surface, then

`H⁰(X, 𝓔) ⟶ lim H⁰(Yₙ, 𝓔ₙ)`

is an isomorphism. -/
@[stacks 0EL3 "clause (2): on a Cohen-Macaulay proper surface over k, H^0(X,E) -> \
lim H^0(Y_n,E_n) is an isomorphism, for E finite locally free and Y the zero scheme of a \
section of an ample invertible module"]
theorem isIso_zeroSchemeComparison_zero_of_isCohenMacaulay_surface
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProperVariety k fX]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (s : Γ(L, ⊤)) (E : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hCM : IsCohenMacaulay X) (hdim : topologicalKrullDim X = 2) :
    haveI := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    IsIso (zeroSchemeComparison X L s E 0) :=
  have := LocallyOfFiniteType.isLocallyNoetherian fX
  isIso_zeroSchemeComparison_of_hasPropertySk fX hL s E 2
    ((isCohenMacaulay_iff_forall_hasPropertySk X).mp hCM 2) (by rw [hdim]; rfl) 0 (by omega)

/-- **Stacks Project, Tag 0EL3 (Example 52.28.3), clause (3).** In the situation of clause (2),
if `X` is a Cohen–Macaulay threefold then both

`H⁰(X, 𝓔) ⟶ lim H⁰(Yₙ, 𝓔ₙ)` and `H¹(X, 𝓔) ⟶ lim H¹(Yₙ, 𝓔ₙ)`

are isomorphisms. -/
@[stacks 0EL3 "clause (3): on a Cohen-Macaulay proper threefold over k, H^0(X,E) -> \
lim H^0(Y_n,E_n) and H^1(X,E) -> lim H^1(Y_n,E_n) are isomorphisms, for E finite locally free \
and Y the zero scheme of a section of an ample invertible module"]
theorem isIso_zeroSchemeComparison_of_isCohenMacaulay_threefold
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProperVariety k fX]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (s : Γ(L, ⊤)) (E : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hCM : IsCohenMacaulay X) (hdim : topologicalKrullDim X = 3) :
    haveI := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    IsIso (zeroSchemeComparison X L s E 0) ∧ IsIso (zeroSchemeComparison X L s E 1) := by
  have := LocallyOfFiniteType.isLocallyNoetherian fX
  have hSk := (isCohenMacaulay_iff_forall_hasPropertySk X).mp hCM 3
  have hd : ((3 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X := by rw [hdim]; rfl
  constructor <;> exact isIso_zeroSchemeComparison_of_hasPropertySk fX hL s E 3 hSk hd _ (by omega)

/-- **Stacks Project, Tag 0EL3 (Example 52.28.3), the normal case.** In the situation of
clause (2), if `X` is normal of dimension at least two, then

`H⁰(X, 𝓔) ⟶ lim H⁰(Yₙ, 𝓔ₙ)`

is an isomorphism. At dimension two this is the source's "for example normal" in clause (2); at
dimension three it is the closing remark that on a normal threefold the result holds for `H⁰`.
A normal scheme satisfies `(S₂)` (Serre's criterion, [Stacks, Tag 031S]), which is the pattern at
`d = 2`. -/
@[stacks 0EL3 "the normal case: on a normal proper variety over k of dimension at least two \
(the normal surface of clause (2), the normal threefold of the closing remark), \
H^0(X,E) -> lim H^0(Y_n,E_n) is an isomorphism"]
theorem isIso_zeroSchemeComparison_zero_of_isNormal
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProperVariety k fX]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    (s : Γ(L, ⊤)) (E : X.Modules)
    [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    [IsNormal X] (hdim : ((2 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    haveI := Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
    IsIso (zeroSchemeComparison X L s E 0) :=
  have := LocallyOfFiniteType.isLocallyNoetherian fX
  isIso_zeroSchemeComparison_of_hasPropertySk fX hL s E 2 (hasPropertySk_two_of_isNormal X)
    hdim 0 (by omega)

end Stacks.Algebraization

end
