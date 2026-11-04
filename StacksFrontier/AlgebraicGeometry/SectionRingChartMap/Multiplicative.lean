module

public import StacksFrontier.AlgebraicGeometry.SectionRingChartMap.Normalization

/-!
# The ratio `t / g` at an arbitrary homogeneous generator, and its multiplicativity

For `L` an invertible module on `X`, a homogeneous section `g` of `L ^⊗ j` and an open
`V ≤ X_g`, a global section `s` of the same tensor power divided by `g` is a function on `V`. This
file defines that ratio, reads it on the section ring `Γ_*(X, L)` by dividing the degree-`j`
component, and proves that it is multiplicative. At the generator `aⁿ` the ratio is
`Stacks.SectionRingChartMap.numMap`, and on the ring the multiplicativity of `numMap` is stated at
the exponent `m + n`.

## Main definitions

* `Stacks.SectionRingChartMap.ratio`: the ratio `s / g` on `V`, for `s` and `g` homogeneous of the
  same degree `j` and `V ≤ X_g`.
* `Stacks.SectionRingChartMap.ratioR`: the additive map `Γ_*(X, L) →+ Γ(X, V)` dividing the
  degree-`j` component by `g`.
* `Stacks.SectionRingChartMap.numMapR`: `ratioR` at the generator `aⁿ`.

## Main results

* `Stacks.SectionRingChartMap.of_mul_of_powSec`: `aᵐ · aⁿ = a^(m+n)` in the ring `Γ_*(X, L)`.
* `Stacks.SectionRingChartMap.ratio_mul`: the ratio of a product is the product of the ratios.
* `Stacks.SectionRingChartMap.numMap_eq_ratio`: `numMap` is `ratio` at the generator `aⁿ`.
* `Stacks.SectionRingChartMap.ratioR_congr`: two generators of equal degree with the same image
  under `DirectSum.of` give the same ratio map.
* `Stacks.SectionRingChartMap.numMapR_mul`: `numMapR` is multiplicative, at the exponent `m + n`,
  on elements homogeneous of degree `d m` and `d n`.
* `Stacks.SectionRingChartMap.numMapR_pow_mul`: multiplying numerator and denominator by a power
  of `a` does not change the ratio.

## References

* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PZ](https://stacks.math.columbia.edu/tag/01PZ)

No `@[stacks]` attribute is attached: these are ring-theoretic identities used in the chart map of
Stacks Tag 01PZ, not the statement of the tag, which is about the glued morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powSections mul sectionRing mulMap powCongr mul_comm')
open Stacks.SectionProduct (globalSection globalSection_comp)
open Stacks.SectionExtension (powSec powSec_zero powSec_succ)
open Stacks.AmpleFiniteAvoidance (nvOpen nvLocus coe_nvOpen nvLocus_mul grading)
open Stacks.TensorPowerTrivialize (resTop trivEquiv resTop_app resTop_globalSection_mul)

universe u

namespace Stacks.SectionRingChartMap

section Monoidal

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] {V : X.Opens}

/-! ### One open inside the nonvanishing open of a product -/

/-- **`X_{gg'} = X_g ⊓ X_{g'}`**, as an equality of opens. -/
public theorem nvOpen_mul {j j' : ℕ} (g : powSections L j) (g' : powSections L j') :
    nvOpen L (mul g g') = nvOpen L g ⊓ nvOpen L g' := by
  refine Opens.ext ?_
  rw [coe_nvOpen, Opens.coe_inf, coe_nvOpen, coe_nvOpen]
  exact nvLocus_mul L g g'

/-- An open inside the nonvanishing opens of two homogeneous sections lies inside the
nonvanishing open of their product. -/
public theorem le_nvOpen_mul {j j' : ℕ} {g : powSections L j} {g' : powSections L j'}
    (hg : V ≤ nvOpen L g) (hg' : V ≤ nvOpen L g') : V ≤ nvOpen L (mul g g') := by
  rw [nvOpen_mul]
  exact le_inf hg hg'

/-! ### The ratio by an arbitrary homogeneous generator -/

/-- **The ratio `s / g`**, for `s` and `g` global sections of one and the same tensor power of `L`
and `V` an open inside the nonvanishing open of `g`: the unique function on `V` whose product with
`g|_V` is `s|_V`. -/
public noncomputable def ratio {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g)
    (s : powSections L j) : Γ(X, V) :=
  (trivEquiv (natTensorPow L j) (globalSection X _ g) hg).symm
    (resTop (natTensorPow L j) (globalSection X _ s) V)

/-- **The defining identity of the ratio:** `s|_V = (s/g) · g|_V`. -/
public theorem ratio_smul_resTop {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g)
    (s : powSections L j) :
    ratio L g hg s • resTop (natTensorPow L j) (globalSection X _ g) V
      = resTop (natTensorPow L j) (globalSection X _ s) V :=
  (trivEquiv (natTensorPow L j) (globalSection X _ g) hg).apply_symm_apply _

/-- **The ratio is the unique function with the defining property:** if `s|_V = c · g|_V`, then
`s / g = c`. -/
public theorem ratio_unique {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g)
    (s : powSections L j) (c : Γ(X, V))
    (hc : resTop (natTensorPow L j) (globalSection X _ s) V
      = c • resTop (natTensorPow L j) (globalSection X _ g) V) :
    ratio L g hg s = c :=
  (trivEquiv (natTensorPow L j) (globalSection X _ g) hg).injective
    ((ratio_smul_resTop L g hg s).trans hc)

/-- The ratio of the zero section is zero. -/
public theorem ratio_zero {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g) :
    ratio L g hg 0 = 0 := by
  refine ratio_unique L g hg 0 0 ?_
  rw [show globalSection X (natTensorPow L j) (0 : powSections L j) = 0 from map_zero _,
    show resTop (natTensorPow L j) 0 V = 0 from map_zero _, zero_smul]

/-- The ratio is additive in the numerator. -/
public theorem ratio_add {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g)
    (s t : powSections L j) :
    ratio L g hg (s + t) = ratio L g hg s + ratio L g hg t := by
  refine ratio_unique L g hg (s + t) _ ?_
  rw [show globalSection X (natTensorPow L j) (s + t)
        = globalSection X _ s + globalSection X _ t from map_add _ s t,
    show resTop (natTensorPow L j) (globalSection X _ s + globalSection X _ t) V
      = resTop (natTensorPow L j) (globalSection X _ s) V
        + resTop (natTensorPow L j) (globalSection X _ t) V from map_add _ _ _,
    add_smul, ratio_smul_resTop, ratio_smul_resTop]

/-- **The generator divided by itself is `1`.** -/
public theorem ratio_self {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g) :
    ratio L g hg g = 1 :=
  ratio_unique L g hg g 1 (one_smul (Γ(X, V)) _).symm

/-- **The ratio of a product is the product of the ratios:** `(s t) / (g g') = (s / g) (t / g')`
on `V`. -/
public theorem ratio_mul {j j' : ℕ} (g : powSections L j) (g' : powSections L j')
    (hg : V ≤ nvOpen L g) (hg' : V ≤ nvOpen L g') (hgg : V ≤ nvOpen L (mul g g'))
    (s : powSections L j) (t : powSections L j') :
    ratio L (mul g g') hgg (mul s t) = ratio L g hg s * ratio L g' hg' t := by
  refine ratio_unique L (mul g g') hgg (mul s t) _ ?_
  have hinner : resTop (natTensorPow L (j + j')) (globalSection X _ (mul s t)) V
      = ratio L g' hg' t • resTop (natTensorPow L (j + j')) (globalSection X _ (mul s g')) V := by
    rw [resTop_globalSection_mul L s t V, ← ratio_smul_resTop L g' hg' t,
      Scheme.Modules.Hom.app_smul, resTop_globalSection_mul L s g' V]
  have hcomm : ∀ u : powSections L j,
      globalSection X (natTensorPow L (j + j')) (mul u g')
        = (mulMap g' j ≫ powCongr L (Nat.add_comm j' j)).app ⊤
          (globalSection X _ u) := by
    intro u
    rw [← mul_comm' g' u, globalSection_comp, Scheme.Modules.Hom.comp_app]
    rfl
  have houter : resTop (natTensorPow L (j + j')) (globalSection X _ (mul s g')) V
      = ratio L g hg s • resTop (natTensorPow L (j + j')) (globalSection X _ (mul g g')) V := by
    rw [hcomm s, hcomm g, resTop_app, resTop_app, ← ratio_smul_resTop L g hg s,
      Scheme.Modules.Hom.app_smul]
  rw [hinner, houter, smul_smul, mul_comm]

/-- **`numMap` is the ratio by the generator `aⁿ`.** -/
public theorem numMap_eq_ratio {d : ℕ} (a : powSections L d) (hV : V ≤ nvOpen L a) (n : ℕ)
    (hn : 1 ≤ n) (t : powSections L (d * n)) :
    numMap L a hV n hn (globalSection X _ t)
      = ratio L (powSec L a n) (le_nvOpen_powSec L a hV n hn) t :=
  rfl

/-! ### The ratio read on the section ring -/

/-- **The ratio by `g`, read on the ring `Γ_*(X, L)`**: divide the degree-`j` component by `g`. -/
public noncomputable def ratioR {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g) :
    sectionRing L →+ Γ(X, V) :=
  AddMonoidHom.mk' (fun z ↦ ratio L g hg (z j)) fun z w ↦ by
    rw [show (z + w) j = z j + w j from DFinsupp.add_apply z w j, ratio_add]

/-- `ratioR` divides the degree-`j` component by `g`. -/
public theorem ratioR_apply {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g)
    (z : sectionRing L) : ratioR L g hg z = ratio L g hg (z j) := rfl

/-- `ratioR` on a homogeneous element named by `DirectSum.of`. -/
public theorem ratioR_of {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g)
    (s : powSections L j) :
    ratioR L g hg (DirectSum.of (powSections L) j s) = ratio L g hg s := by
  rw [ratioR_apply, DirectSum.of_eq_same]

/-- **The generator divided by itself is `1`**, on the ring. -/
public theorem ratioR_of_self {j : ℕ} (g : powSections L j) (hg : V ≤ nvOpen L g) :
    ratioR L g hg (DirectSum.of (powSections L) j g) = 1 := by
  rw [ratioR_of, ratio_self]

/-- **The ratio depends only on the ring elements, not on the spelling of their degree.** Two
generators of equal — not necessarily identical — degree with the same image in `Γ_*(X, L)` divide
alike. -/
public theorem ratioR_congr {j j' : ℕ} (hjj : j = j') (g : powSections L j)
    (g' : powSections L j') (hg : V ≤ nvOpen L g) (hg' : V ≤ nvOpen L g')
    (hgg : DirectSum.of (powSections L) j g = DirectSum.of (powSections L) j' g')
    (z : sectionRing L) :
    ratioR L g hg z = ratioR L g' hg' z := by
  subst hjj
  obtain rfl : g = g' := by
    have h := DirectSum.of_eq_same (β := fun i ↦ powSections L i) j g
    rw [hgg, DirectSum.of_eq_same] at h
    exact h.symm
  rfl

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- **The product of two homogeneous elements, named by `DirectSum.of`:** the product in
`Γ_*(X, L)` of `s` and `t` is `Stacks.GradedSections.mul s t` in degree `j + j'`. -/
public theorem of_mul_eq {j j' : ℕ} (s : powSections L j) (t : powSections L j') :
    DirectSum.of (powSections L) (j + j') (mul s t)
      = DirectSum.of (powSections L) j s * DirectSum.of (powSections L) j' t :=
  (DirectSum.of_mul_of s t).symm

/-- **The ratio of a product is the product of the ratios**, on the ring. -/
public theorem ratioR_mul {j j' : ℕ} (g : powSections L j) (g' : powSections L j')
    (hg : V ≤ nvOpen L g) (hg' : V ≤ nvOpen L g') (hgg : V ≤ nvOpen L (mul g g'))
    {z w : sectionRing L} (hz : z ∈ grading L j) (hw : w ∈ grading L j') :
    ratioR L (mul g g') hgg (z * w) = ratioR L g hg z * ratioR L g' hg' w := by
  obtain ⟨s, rfl⟩ := Stacks.ExternalGrading.mem_summand_iff.mp hz
  obtain ⟨t, rfl⟩ := Stacks.ExternalGrading.mem_summand_iff.mp hw
  rw [← of_mul_eq, ratioR_of, ratioR_of, ratioR_of, ratio_mul]

/-! ### The powers of one homogeneous element -/

variable {d : ℕ} (a : powSections L d)

/-- **The addition law for the powers of a homogeneous section**, `aᵐ · aⁿ = a^(m+n)`, stated in
the ring `Γ_*(X, L)`. -/
public theorem of_mul_of_powSec (m n : ℕ) :
    DirectSum.of (powSections L) (d * m) (powSec L a m)
        * DirectSum.of (powSections L) (d * n) (powSec L a n)
      = DirectSum.of (powSections L) (d * (m + n)) (powSec L a (m + n)) := by
  induction n with
  | zero =>
      rw [powSec_zero,
        show DirectSum.of (powSections L) (d * 0) (𝟙 (𝟙_ X.Modules)) = 1 from
          DirectSum.of_zero_one (powSections L),
        mul_one]
      rfl
  | succ n ih =>
      show DirectSum.of (powSections L) (d * m) (powSec L a m)
            * DirectSum.of (powSections L) (d * n + d) (mul (powSec L a n) a)
          = DirectSum.of (powSections L) (d * (m + n) + d) (mul (powSec L a (m + n)) a)
      rw [of_mul_eq, of_mul_eq, ← mul_assoc, ih]

omit [Stacks.Ample.IsInvertibleModule X L] in
/-- The ring power of `DirectSum.of _ d a`, in the degree `Stacks.SectionExtension.powSec` gives
it: `aᵏ` in degree `d k` is the `k`-th power of `a` in `Γ_*(X, L)`. -/
public theorem of_powSec_eq_pow (k : ℕ) :
    DirectSum.of (powSections L) (d * k) (powSec L a k)
      = DirectSum.of (powSections L) d a ^ k :=
  (Stacks.SectionRingProjOverlap.of_pow_eq_of_powSec L a k).symm

/-! ### Multiplicativity of `numMap`, at the level of sections -/

/-- **The ratio of a product of two numerators is the product of the ratios.** The denominator is
`aᵐ · aⁿ`, of degree `d m + d n`; `Stacks.SectionRingChartMap.numMapR_mul` is the statement at
the denominator `a^(m+n)`, on the ring. -/
public theorem numMap_mul (hV : V ≤ nvOpen L a) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (s : powSections L (d * m)) (t : powSections L (d * n)) :
    ratio L (mul (powSec L a m) (powSec L a n))
        (le_nvOpen_mul L (le_nvOpen_powSec L a hV m hm) (le_nvOpen_powSec L a hV n hn))
        (mul s t)
      = numMap L a hV m hm (globalSection X _ s) * numMap L a hV n hn (globalSection X _ t) := by
  rw [ratio_mul L (powSec L a m) (powSec L a n) (le_nvOpen_powSec L a hV m hm)
    (le_nvOpen_powSec L a hV n hn), numMap_eq_ratio, numMap_eq_ratio]

/-- **Multiplying numerator and denominator by a positive power of `a` leaves the ratio
unchanged**, at the level of sections: `(aᵏ · t) / (aᵏ · aⁿ) = t / aⁿ`. The exponent `k` has to be
positive; the ring-level `Stacks.SectionRingChartMap.numMapR_pow_mul` allows `k = 0`. -/
public theorem numMap_powSec_mul (hV : V ≤ nvOpen L a) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (t : powSections L (d * n)) :
    ratio L (mul (powSec L a k) (powSec L a n))
        (le_nvOpen_mul L (le_nvOpen_powSec L a hV k hk) (le_nvOpen_powSec L a hV n hn))
        (mul (powSec L a k) t)
      = numMap L a hV n hn (globalSection X _ t) := by
  rw [ratio_mul L (powSec L a k) (powSec L a n) (le_nvOpen_powSec L a hV k hk)
    (le_nvOpen_powSec L a hV n hn), ratio_self, one_mul, numMap_eq_ratio]

/-! ### `numMap` read on the section ring -/

/-- **`numMap` read on the ring `Γ_*(X, L)`**: divide the degree-`d n` component by `aⁿ`. -/
public noncomputable def numMapR (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n) :
    sectionRing L →+ Γ(X, V) :=
  ratioR L (powSec L a n) (le_nvOpen_powSec L a hV n hn)

/-- `numMapR` is `ratioR` at the generator `aⁿ`. -/
public theorem numMapR_def (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n) :
    numMapR L a hV n hn = ratioR L (powSec L a n) (le_nvOpen_powSec L a hV n hn) := rfl

/-- `numMapR` on a homogeneous element is `numMap` on its component. -/
public theorem numMapR_of (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n)
    (t : powSections L (d * n)) :
    numMapR L a hV n hn (DirectSum.of (powSections L) (d * n) t)
      = numMap L a hV n hn (globalSection X _ t) := by
  rw [numMapR_def, ratioR_of, numMap_eq_ratio]

/-- **Two equal exponents give the same map.** -/
public theorem numMapR_exp_congr (hV : V ≤ nvOpen L a) {p q : ℕ} (hpq : p = q) (hp : 1 ≤ p)
    (hq : 1 ≤ q) (z : sectionRing L) :
    numMapR L a hV p hp z = numMapR L a hV q hq z := by
  subst hpq
  rfl

/-- **`numMap` is multiplicative.** For `z` and `w` homogeneous of degrees `d m` and `d n`, the
ratio of `z w` by `a^(m+n)` is the product of the ratios of `z` by `aᵐ` and of `w` by `aⁿ`. -/
public theorem numMapR_mul (hV : V ≤ nvOpen L a) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmn : 1 ≤ m + n) {z w : sectionRing L}
    (hz : z ∈ grading L (d * m)) (hw : w ∈ grading L (d * n)) :
    numMapR L a hV (m + n) hmn (z * w)
      = numMapR L a hV m hm z * numMapR L a hV n hn w := by
  have hgen : DirectSum.of (powSections L) (d * (m + n)) (powSec L a (m + n))
      = DirectSum.of (powSections L) (d * m + d * n) (mul (powSec L a m) (powSec L a n)) :=
    (of_mul_of_powSec L a m n).symm.trans (of_mul_eq L (powSec L a m) (powSec L a n)).symm
  have hgg : V ≤ nvOpen L (mul (powSec L a m) (powSec L a n)) :=
    le_nvOpen_mul L (le_nvOpen_powSec L a hV m hm) (le_nvOpen_powSec L a hV n hn)
  rw [numMapR_def, numMapR_def, numMapR_def,
    ratioR_congr L (by ring) (powSec L a (m + n)) (mul (powSec L a m) (powSec L a n))
      (le_nvOpen_powSec L a hV (m + n) hmn) hgg hgen (z * w),
    ratioR_mul L (powSec L a m) (powSec L a n) (le_nvOpen_powSec L a hV m hm)
      (le_nvOpen_powSec L a hV n hn) hgg hz hw]

/-- **Multiplying numerator and denominator by a power of `a` does not change the ratio:** for `z`
homogeneous of degree `d n`, the ratio of `aᵏ z` by `a^(k+n)` is the ratio of `z` by `aⁿ`. -/
public theorem numMapR_pow_mul (hV : V ≤ nvOpen L a) (n k : ℕ) (hn : 1 ≤ n) (hkn : 1 ≤ k + n)
    {z : sectionRing L} (hz : z ∈ grading L (d * n)) :
    numMapR L a hV (k + n) hkn (DirectSum.of (powSections L) d a ^ k * z)
      = numMapR L a hV n hn z := by
  match k with
  | 0 =>
      rw [pow_zero, one_mul]
      exact numMapR_exp_congr L a hV (Nat.zero_add n) hkn hn z
  | k + 1 =>
      have hz' : DirectSum.of (powSections L) d a ^ (k + 1)
          ∈ grading L (d * (k + 1)) := by
        rw [← of_powSec_eq_pow]
        exact Stacks.ExternalGrading.of_mem_summand _ _
      rw [numMapR_mul L a hV (k + 1) n (Nat.le_add_left 1 k) hn hkn hz' hz, numMapR_def,
        ← of_powSec_eq_pow, ratioR_of_self, one_mul]

/-- `numMapR_mul` with the exponent of the denominator given by an equation rather than as a
literal sum. -/
public theorem numMapR_mul' (hV : V ≤ nvOpen L a) (m n p : ℕ) (hp : m + n = p) (hm : 1 ≤ m)
    (hn : 1 ≤ n) (hp1 : 1 ≤ p) {z w : sectionRing L}
    (hz : z ∈ grading L (d * m)) (hw : w ∈ grading L (d * n)) :
    numMapR L a hV p hp1 (z * w) = numMapR L a hV m hm z * numMapR L a hV n hn w := by
  subst hp
  exact numMapR_mul L a hV m n hm hn hp1 hz hw

/-- `numMapR_pow_mul` with the exponent of the denominator given by an equation rather than as a
literal sum. -/
public theorem numMapR_pow_mul' (hV : V ≤ nvOpen L a) (n k p : ℕ) (hp : k + n = p) (hn : 1 ≤ n)
    (hp1 : 1 ≤ p) {z : sectionRing L} (hz : z ∈ grading L (d * n)) :
    numMapR L a hV p hp1 (DirectSum.of (powSections L) d a ^ k * z) = numMapR L a hV n hn z := by
  subst hp
  exact numMapR_pow_mul L a hV n k hn hp1 hz

/-- **`a / a = 1`**, on the ring. -/
public theorem numMapR_of_self (hV : V ≤ nvOpen L a) (h1 : 1 ≤ 1) :
    numMapR L a hV 1 h1 (DirectSum.of (powSections L) d a) = 1 := by
  have h : DirectSum.of (powSections L) (d * 1) (powSec L a 1)
      = DirectSum.of (powSections L) d a := by
    rw [of_powSec_eq_pow, pow_one]
  rw [numMapR_def, ← h, ratioR_of_self]

/-- **Multiplying numerator and denominator by `a` once leaves the ratio unchanged:** the ratio of
`a z` by `a^(n+1)` is the ratio of `z` by `aⁿ`. -/
public theorem numMapR_of_mul (hV : V ≤ nvOpen L a) (n : ℕ) (hn : 1 ≤ n) (hn1 : 1 ≤ n + 1)
    {z : sectionRing L} (hz : z ∈ grading L (d * n)) :
    numMapR L a hV (n + 1) hn1 (DirectSum.of (powSections L) d a * z)
      = numMapR L a hV n hn z := by
  simpa only [pow_one] using
    numMapR_pow_mul' L a hV n 1 (n + 1) (Nat.add_comm 1 n) hn hn1 hz

end Monoidal

end Stacks.SectionRingChartMap

end
