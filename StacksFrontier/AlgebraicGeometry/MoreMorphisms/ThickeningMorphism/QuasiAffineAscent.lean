module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Affine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFiniteType
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningRestrict
public import Mathlib.AlgebraicGeometry.Noetherian
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The ascent of quasi-affineness along a thickening

Let `k : Y ⟶ Y'` be a thickening — a closed immersion that is surjective on points — with `Y`
quasi-affine. Quasi-affineness of `Y'` is a statement about the *global functions* of `Y'`: by
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen` it is enough that every
point lie in an affine nonvanishing locus of one. The affine opens of `Y` and `Y'` correspond
(`Stacks.Thickenings.isAffineOpen_iff_isAffineOpen_preimage`, [Stacks Project, Tag 06AD] read over
an open), so what has to be produced is, for an affine basic open `Y_r` of `Y`, a global function
on `Y'` whose nonvanishing locus pulls back to `Y_r` — the property
`Stacks.Thickenings.AffineBasicOpenLifts` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/Affine.lean`.

This file proves that property for a **first-order** thickening, with no Noetherian hypothesis,
and draws the consequences: along the filtration by the powers of the ideal sheaf it gives the
property for a thickening of finite order, hence the ascent of quasi-affineness along one; and
over a Noetherian scheme every thickening is of finite order, which closes
[Stacks Project, Tag 0B7K].

## The proof of the first-order case

It is the Čech argument of the source's proof of [Stacks Project, Tag 09MS] at `L = 𝒪`, carried
out by hand, with no cohomology group formed anywhere. A quasi-affine scheme has a finite cover by
affine basic opens of global functions whose pairwise intersections are again affine
(`Stacks.Thickenings.exists_finite_affine_basicOpen_cover` — the intersection of two basic opens
is the basic open of the product). Over each member `U i` of the matching cover of `Y'` the
function `r` lifts to `b i`, because the map on sections of a closed immersion over an affine open
is surjective, and over the open matching `Y_r` it lifts to `c`. The difference `b i - c` lies in
the kernel over the nonvanishing locus of `b i`, which is that open; a power of `b i` times it is
therefore the restriction of a section of `𝒪_{Y'}` over `U i`
(`AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen`), and a further power of `b i` puts that
section into the kernel, by the same localization statement read on the closed subscheme. Finitely
many members make the exponent `M` uniform. The two descriptions of the cocycle `b i - b j` over
an overlap then force a power of `b i` to annihilate `b i ^ M (b i - b j) - (G i - G j)`
(`Stacks.Thickenings.exists_pow_mul_sub_eq_zero`), uniformly in the pair; and with `K` that
exponent and `N = K + M + 1`, the corrected sections `b i ^ N - N b i ^ K G i` agree on the
overlaps (`Stacks.Thickenings.corrected_lift_eq`). They glue to a global function on `Y'` whose
image downstairs is `r ^ N`, and `Y_{r ^ N} = Y_r`.

Square-zeroness of the kernel enters exactly twice, through
`Stacks.Thickenings.mul_eq_zero_of_isFirstOrderThickening`: multiplication by the two local lifts
agrees on the kernel (`Stacks.Thickenings.pow_mul_left_eq_of_sub_mem`), and the `N`th power obeys
the derivation rule `Stacks.Thickenings.pow_sub_pow_of_sub_mem`. This is why no analogue of
[Stacks Project, Tag 01XR] in degree one, and so none of [Stacks Project, Tag 09MR], is needed:
the cohomology class obstructing the lift of `r` is never formed, only the Čech cocycle
representing it, and the cocycle is handled by the two localization statements above.

## Main results

* `Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening_of_isQuasiAffine`: the
  first-order case of `Stacks.Thickenings.AffineBasicOpenLifts`, unconditionally.
* `Stacks.Thickenings.affineBasicOpenLifts_of_isFiniteOrderThickening` and
  `Stacks.Thickenings.isQuasiAffine_of_isFiniteOrderThickening`: the finite-order case, and the
  ascent of quasi-affineness along a finite-order thickening — the implication *closed subscheme
  quasi-affine `⟹` ambient quasi-affine* of [Stacks Project, Tag 0B7L] for such a thickening.
* `Stacks.Thickenings.isFiniteOrderThickening_of_isThickening`: a thickening of a quasi-compact
  locally Noetherian scheme is of finite order.
* `Stacks.Thickenings.isQuasiAffine_iff_of_isNoetherian`: **[Stacks Project, Tag 0B7K]**, both
  implications, with no hypothesis beyond the source's.
* `Stacks.Thickenings.isQuasiAffineHom_left_iff_right_of_isLocallyNoetherian`: part (9) of
  [Stacks Project, Tag 09ZV] for a morphism of thickenings whose ambient closed subscheme is
  locally Noetherian. The unconditional part (9) is
  `Stacks.Thickenings.isQuasiAffineHom_left_iff_right` of
  `StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`.

## Where the general case of part (9) of [Stacks Project, Tag 09ZV] is proved

Part (9) is stated for arbitrary thickenings, and a thickening need not be of finite order: the
kernel ideal sheaf of a surjective closed immersion consists of nilpotents, but with no bound on
their order when the ambient scheme is not locally Noetherian. The results in *this* file
therefore give part (9) only over a locally Noetherian ambient scheme, and the filtration argument
cannot do better: if an ideal sheaf `𝒥 ⊆ ℐ` and the quotient `ℐ / 𝒥` are both nilpotent then so
is `ℐ`, so no finite chain of first-order steps joins `Y` to `Y'`.

The general case is the limit argument of [Stacks Project, Tag 09MW] — write `Y'` as a limit of
schemes of finite type over `ℤ` with affine transition morphisms, where the ideal sheaf *is* of
finite order, and descend — and it is carried out in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`, using the
finite-order results below at the stages. That file holds the unconditional statements:
`Stacks.Thickenings.isQuasiAffine_of_isThickening`,
`Stacks.Thickenings.isQuasiAffine_iff_of_isThickening` ([Stacks Project, Tag 0B7L]) and
`Stacks.Thickenings.isQuasiAffineHom_left_iff_right` (part (9)).

## References

* [Stacks Project, Tag 09ZV](https://stacks.math.columbia.edu/tag/09ZV)
* [Stacks Project, Tag 0B7K](https://stacks.math.columbia.edu/tag/0B7K)
* [Stacks Project, Tag 0B7L](https://stacks.math.columbia.edu/tag/0B7L)
* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
* [Stacks Project, Tag 09MW](https://stacks.math.columbia.edu/tag/09MW)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 01XR](https://stacks.math.columbia.edu/tag/01XR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Stacks.Thickenings

universe u

/-! ### Square-zero ideals -/

/-- Multiplication by two elements congruent modulo a square-zero ideal agrees on that ideal. -/
theorem mul_left_eq_of_sub_mem {R : Type*} [CommRing R] {I : Ideal R}
    (hI : ∀ x ∈ I, ∀ y ∈ I, x * y = 0) {a b x : R} (hab : a - b ∈ I) (hx : x ∈ I) :
    a * x = b * x :=
  sub_eq_zero.mp ((sub_mul a b x).symm.trans (hI _ hab _ hx))

/-- Powers of two elements congruent modulo a square-zero ideal agree on that ideal. -/
theorem pow_mul_left_eq_of_sub_mem {R : Type*} [CommRing R] {I : Ideal R}
    (hI : ∀ x ∈ I, ∀ y ∈ I, x * y = 0) {a b : R} (hab : a - b ∈ I) :
    ∀ (n : ℕ) {x : R}, x ∈ I → a ^ n * x = b ^ n * x := by
  intro n
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    rw [pow_succ, pow_succ, mul_assoc, mul_assoc, mul_left_eq_of_sub_mem hI hab hx]
    exact ih (I.mul_mem_left b hx)

/-- The derivation rule for a power modulo a square-zero ideal: if `a - b` lies in a square-zero
ideal then `aⁿ⁺¹ - bⁿ⁺¹ = (n + 1) aⁿ (a - b)`. -/
theorem pow_sub_pow_of_sub_mem {R : Type*} [CommRing R] {I : Ideal R}
    (hI : ∀ x ∈ I, ∀ y ∈ I, x * y = 0) {a b : R} (hab : a - b ∈ I) :
    ∀ n : ℕ, a ^ (n + 1) - b ^ (n + 1) = ((n : R) + 1) * a ^ n * (a - b) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    linear_combination (norm := (push_cast; ring))
      a * ih - pow_mul_left_eq_of_sub_mem hI hab (n + 1) hab

/-! ### The kernel of a first-order thickening over an affine open -/

/-- **The kernel ideal of a first-order thickening is square-zero over every affine open.** -/
theorem mul_eq_zero_of_isFirstOrderThickening {Y Y' : Scheme.{u}} {k : Y ⟶ Y'}
    (hk : IsFirstOrderThickening k) {U : Y'.Opens} (hU : IsAffineOpen U) {x y : Γ(Y', U)}
    (hx : (k.app U) x = 0) (hy : (k.app U) y = 0) : x * y = 0 := by
  have : IsClosedImmersion k := hk.1
  have hker : k.ker.ideal ⟨U, hU⟩ = RingHom.ker (k.app U).hom := Scheme.Hom.ker_apply k ⟨U, hU⟩
  have hx' : x ∈ k.ker.ideal ⟨U, hU⟩ := hker ▸ RingHom.mem_ker.mpr hx
  have hy' : y ∈ k.ker.ideal ⟨U, hU⟩ := hker ▸ RingHom.mem_ker.mpr hy
  have hsq : k.ker * k.ker = ⊥ := by rw [← sq]; exact hk.2
  have h2 : x * y ∈ (k.ker * k.ker).ideal ⟨U, hU⟩ := Ideal.mul_mem_mul hx' hy'
  rw [hsq] at h2
  simpa using h2

/-- The kernel of the map on sections over an affine open, as an ideal that
`Stacks.Thickenings.mul_eq_zero_of_isFirstOrderThickening` makes square-zero. -/
theorem forall_mul_eq_zero_of_isFirstOrderThickening {Y Y' : Scheme.{u}} {k : Y ⟶ Y'}
    (hk : IsFirstOrderThickening k) {U : Y'.Opens} (hU : IsAffineOpen U) :
    ∀ x ∈ RingHom.ker (k.app U).hom, ∀ y ∈ RingHom.ker (k.app U).hom, x * y = 0 :=
  fun _ hx _ hy => mul_eq_zero_of_isFirstOrderThickening hk hU
    (RingHom.mem_ker.mp hx) (RingHom.mem_ker.mp hy)

/-! ### Naturality of the map on sections -/

/-- The map on sections of a morphism commutes with restriction to a smaller open. -/
theorem app_restrict {Y Y' : Scheme.{u}} (k : Y ⟶ Y') {U V : Y'.Opens} (h : V ≤ U)
    (h' : k ⁻¹ᵁ V ≤ k ⁻¹ᵁ U) (s : Γ(Y', U)) :
    (k.app V) (s |_ V) = (k.app U s) |_ (k ⁻¹ᵁ V) := by
  simp [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict]

/-! ### Restriction of sections is a ring homomorphism

The restriction notation `|_` hides the map of the presheaf behind a definition, so the generic
`map_mul`, `map_sub` and `map_pow` do not rewrite through it; these are the four instances needed
below. -/

/-- Restriction of sections respects subtraction. -/
theorem restrict_sub {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (x y : Γ(X, U)) :
    (x - y) |_ V = x |_ V - y |_ V :=
  map_sub (X.presheaf.map (homOfLE h).op).hom x y

/-- Restriction of sections respects multiplication. -/
theorem restrict_mul {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (x y : Γ(X, U)) :
    (x * y) |_ V = x |_ V * y |_ V :=
  map_mul (X.presheaf.map (homOfLE h).op).hom x y

/-- Restriction of sections respects powers. -/
theorem restrict_pow {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) (n : ℕ) :
    (x ^ n) |_ V = (x |_ V) ^ n :=
  map_pow (X.presheaf.map (homOfLE h).op).hom x n

/-- Restriction of sections respects the natural numbers. -/
theorem restrict_natCast {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (n : ℕ) :
    ((n : Γ(X, U))) |_ V = (n : Γ(X, V)) :=
  map_natCast (X.presheaf.map (homOfLE h).op).hom n

/-- Restriction of sections respects zero. -/
theorem restrict_zero {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) :
    ((0 : Γ(X, U))) |_ V = 0 :=
  map_zero (X.presheaf.map (homOfLE h).op).hom

/-- The nonvanishing locus of a restricted section, in the restriction notation. -/
theorem basicOpen_restrict_eq {X : Scheme.{u}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) :
    X.basicOpen (f |_ V) = V ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE h).op

/-- Raising the exponent of an annihilating power. -/
theorem pow_mul_eq_zero_of_le {R : Type*} [CommRing R] {a z : R} {p K : ℕ} (h : p ≤ K)
    (hz : a ^ p * z = 0) : a ^ K * z = 0 := by
  rw [← Nat.sub_add_cancel h, pow_add, mul_assoc, hz, mul_zero]

/-! ### A finite affine cover with affine pairwise intersections -/

/-- **A quasi-affine scheme has a finite cover by affine basic opens of global functions**, and any
two members of that cover meet in an affine open. -/
theorem exists_finite_affine_basicOpen_cover (Y : Scheme.{u}) [Scheme.IsQuasiAffine Y] :
    ∃ (ι : Type u) (_ : Fintype ι) (A : ι → Y.Opens), (∀ i, IsAffineOpen (A i)) ∧
      (∀ i j, IsAffineOpen (A i ⊓ A j)) ∧ ⨆ i, A i = ⊤ := by
  classical
  have hcov : (Set.univ : Set Y) ⊆
      ⋃ j : {f : Γ(Y, ⊤) // IsAffineOpen (Y.basicOpen f)}, (Y.basicOpen j.1 : Set Y) := by
    intro y _
    obtain ⟨f, hf, hyf⟩ := exists_isAffineOpen_basicOpen_mem Y y
    exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hyf⟩
  obtain ⟨S, hS⟩ := (isCompact_univ (X := Y)).elim_finite_subcover
    (fun j : {f : Γ(Y, ⊤) // IsAffineOpen (Y.basicOpen f)} => (Y.basicOpen j.1 : Set Y))
    (fun j => (Y.basicOpen j.1).isOpen) hcov
  refine ⟨{j : {f : Γ(Y, ⊤) // IsAffineOpen (Y.basicOpen f)} // j ∈ S}, inferInstance,
    fun j => Y.basicOpen j.1.1, fun j => j.1.2, ?_, ?_⟩
  · intro i j
    have h1 : Y.basicOpen i.1.1 ⊓ Y.basicOpen j.1.1
        = Y.basicOpen ((j.1.1 : Γ(Y, ⊤)) |_ (Y.basicOpen i.1.1)) := by
      rw [TopCat.Presheaf.restrictOpen, TopCat.Presheaf.restrict, Scheme.basicOpen_res]
    rw [h1]
    exact i.1.2.basicOpen _
  · refine TopologicalSpace.Opens.ext (Set.eq_univ_of_univ_subset ?_)
    refine hS.trans ?_
    simp only [TopologicalSpace.Opens.coe_iSup]
    exact Set.iUnion₂_subset fun j hj => Set.subset_iUnion_of_subset ⟨j, hj⟩ le_rfl

/-! ### Variants of the two localization statements over an affine open -/

/-- `AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact` with the
nonvanishing locus presented by an equation, so that no open has to be rewritten inside a type. -/
theorem exists_pow_mul_eq_zero_of_res_eq_zero {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsCompact U.1) (x f : Γ(X, U)) (hVU : V ≤ U) (hV : V = X.basicOpen f)
    (H : x |_ V = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  subst hV
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU x f H

/-- `AlgebraicGeometry.exists_eq_pow_mul_of_isAffineOpen` with the nonvanishing locus presented by
an equation, so that no open has to be rewritten inside a type. -/
theorem exists_eq_pow_mul_of_isAffineOpen' {X : Scheme.{u}} {U V : X.Opens}
    (hU : IsAffineOpen U) (f : Γ(X, U)) (hVU : V ≤ U) (hV : V = X.basicOpen f) (x : Γ(X, V)) :
    ∃ (n : ℕ) (y : Γ(X, U)), y |_ V = (f |_ V) ^ n * x := by
  subst hV
  exact exists_eq_pow_mul_of_isAffineOpen X U hU f x

/-! ### The two steps of the cocycle computation -/

variable {Y Y' : Scheme.{u}} {k : Y ⟶ Y'}

/-- **Two local lifts of one global function agree downstairs.** If `s₁` and `s₂` are sections of
the ambient scheme over `U₁` and `U₂` both restricting to the global function `r` of the closed
subscheme, then their difference over `W ≤ U₁ ⊓ U₂` lies in the kernel. -/
theorem app_sub_eq_zero (k : Y ⟶ Y') {U₁ U₂ W : Y'.Opens} (r : Γ(Y, ⊤))
    (s₁ : Γ(Y', U₁)) (s₂ : Γ(Y', U₂)) (h₁ : W ≤ U₁) (h₂ : W ≤ U₂)
    (hs₁ : (k.app U₁) s₁ = r |_ (k ⁻¹ᵁ U₁)) (hs₂ : (k.app U₂) s₂ = r |_ (k ⁻¹ᵁ U₂)) :
    (k.app W) (s₁ |_ W - s₂ |_ W) = 0 := by
  rw [map_sub, app_restrict k h₁ (k.preimage_mono h₁) s₁,
    app_restrict k h₂ (k.preimage_mono h₂) s₂, hs₁, hs₂,
    TopCat.Presheaf.restrict_restrict (k.preimage_mono h₁) le_top,
    TopCat.Presheaf.restrict_restrict (k.preimage_mono h₂) le_top, sub_self]

/-- **A power of a local lift kills the cocycle.** Over an affine open `P` of the ambient scheme,
let `x` and `y` be two sections agreeing modulo the kernel, let `gx` and `gy` be sections of the
kernel, and let `z` be a section over the nonvanishing locus `P_x` with `x - z` and `y - z` in the
kernel there. If `gx` and `gy` are, over `P_x`, the `m`th powers of `x` and `y` times `x - z` and
`y - z`, then some power of `x` annihilates `xᵐ(x - y) - (gx - gy)`.

This is the Čech computation of the proof of [Stacks Project, Tag 09MS] in the square-zero case,
carried out on one member of the cover: the two local lifts differ by a section of the kernel,
which is a module over the structure sheaf of the closed subscheme because the kernel is
square-zero, so multiplication by `x` and by `y` agree on it. -/
theorem exists_pow_mul_sub_eq_zero (hk : IsFirstOrderThickening k) {P Q : Y'.Opens}
    (hP : IsAffineOpen P) (hQP : Q ≤ P) (x y gx gy : Γ(Y', P)) (z : Γ(Y', Q)) (m : ℕ)
    (hQ : Q = Y'.basicOpen x)
    (hxy : (k.app P) (x - y) = 0)
    (hεy : (k.app Q) (y |_ Q - z) = 0)
    (hgx : gx |_ Q = (x |_ Q) ^ m * (x |_ Q - z))
    (hgy : gy |_ Q = (y |_ Q) ^ m * (y |_ Q - z)) :
    ∃ q : ℕ, x ^ q * (x ^ m * (x - y) - (gx - gy)) = 0 := by
  refine exists_pow_mul_eq_zero_of_res_eq_zero hP.isCompact _ x hQP hQ ?_
  have hQaff : IsAffineOpen Q := by rw [hQ]; exact hP.basicOpen x
  have hsq := forall_mul_eq_zero_of_isFirstOrderThickening hk hQaff
  have hd : x |_ Q - y |_ Q ∈ RingHom.ker (k.app Q).hom := by
    refine RingHom.mem_ker.mpr ?_
    rw [← restrict_sub hQP, app_restrict k hQP (k.preimage_mono hQP) (x - y), hxy,
      restrict_zero]
  have key : (y |_ Q) ^ m * (y |_ Q - z) = (x |_ Q) ^ m * (y |_ Q - z) :=
    (pow_mul_left_eq_of_sub_mem hsq hd m (RingHom.mem_ker.mpr hεy)).symm
  simp only [restrict_sub hQP, restrict_mul hQP, restrict_pow hQP]
  rw [hgx, hgy, key]
  ring

/-- **The corrected local lifts agree on an overlap.** With the notation of
`Stacks.Thickenings.exists_pow_mul_sub_eq_zero`, if a `K`th power of `x` annihilates
`xᵐ(x - y) - (gx - gy)` then the two corrected sections `x^N - N x^K gx` and `y^N - N y^K gy`
agree, where `N = K + m + 1`.

This is where the power of the function is spent: the difference of the `N`th powers of the two
local lifts is `N` times `x^{N-1}` times their difference, by
`Stacks.Thickenings.pow_sub_pow_of_sub_mem`, and that is exactly `N` times the difference of the
corrections. -/
theorem corrected_lift_eq (hk : IsFirstOrderThickening k) {P : Y'.Opens}
    (hP : IsAffineOpen P) (x y gx gy : Γ(Y', P)) (K m : ℕ)
    (hxy : (k.app P) (x - y) = 0) (hgy0 : (k.app P) gy = 0)
    (hkill : x ^ K * (x ^ m * (x - y) - (gx - gy)) = 0) :
    x ^ (K + m + 1) - ((K + m + 1 : ℕ) : Γ(Y', P)) * (x ^ K * gx)
      = y ^ (K + m + 1) - ((K + m + 1 : ℕ) : Γ(Y', P)) * (y ^ K * gy) := by
  have hsq := forall_mul_eq_zero_of_isFirstOrderThickening hk hP
  have hd : x - y ∈ RingHom.ker (k.app P).hom := RingHom.mem_ker.mpr hxy
  linear_combination (norm := (push_cast; ring)) pow_sub_pow_of_sub_mem hsq hd (K + m) -
    ((K + m + 1 : ℕ) : Γ(Y', P)) * pow_mul_left_eq_of_sub_mem hsq hd K (RingHom.mem_ker.mpr hgy0) +
    ((K + m + 1 : ℕ) : Γ(Y', P)) * hkill

/-! ### The lift of an affine basic open along a first-order thickening -/

/-- **An affine basic open of the closed subscheme of a first-order thickening with quasi-affine
closed subscheme is the inverse image of a basic open upstairs.** This is
`Stacks.Thickenings.AffineBasicOpenLifts` for a first-order thickening, with no Noetherian
hypothesis.

The proof is the Čech argument of the proof of [Stacks Project, Tag 09MS], carried out by hand on
a finite cover by affine basic opens with affine pairwise intersections
(`Stacks.Thickenings.exists_finite_affine_basicOpen_cover`). On each member `U i` of the cover the
function `r` lifts to `b i`, because the map on sections of a closed immersion over an affine open
is surjective, and over the affine open matching `Y_r` it lifts to `c`. The difference `b i - c`
is a section of the kernel over the nonvanishing locus of `b i`, so a power of `b i` times it is
the restriction of a section `G i` of the kernel over `U i`
(`Stacks.Thickenings.exists_eq_pow_mul_of_isAffineOpen'`, and a further power to put `G i` into the
kernel); the exponent is made uniform by taking a maximum over the finite cover. The sections
`b i ^ N - N b i ^ K G i` then agree on overlaps — this is
`Stacks.Thickenings.exists_pow_mul_sub_eq_zero` followed by
`Stacks.Thickenings.corrected_lift_eq` — and glue to a global function on `Y'` whose image is
`r ^ N`, which has the same nonvanishing locus as `r`.

The square-zero hypothesis enters exactly twice, through
`Stacks.Thickenings.mul_eq_zero_of_isFirstOrderThickening`: it makes the kernel a module over the
structure sheaf of the closed subscheme, so that multiplication by the two local lifts agrees on
it, and it gives the derivation rule `Stacks.Thickenings.pow_sub_pow_of_sub_mem` for the `N`th
power. No cohomology group is formed anywhere, so neither [Stacks Project, Tag 01XR] in degree one
nor [Stacks Project, Tag 09MR] is needed. -/
theorem affineBasicOpenLifts_of_isFirstOrderThickening_of_isQuasiAffine
    (hk : IsFirstOrderThickening k)
    [Scheme.IsQuasiAffine Y] : AffineBasicOpenLifts k := by
  classical
  have : IsClosedImmersion k := hk.1
  have hT : IsThickening k := hk.isThickening
  have hinj : ∀ {V₁ V₂ : Y'.Opens}, k ⁻¹ᵁ V₁ = k ⁻¹ᵁ V₂ → V₁ = V₂ := by
    intro V₁ V₂ h
    rw [← hT.opensCongr_preimage V₁, ← hT.opensCongr_preimage V₂, h]
  intro r hr
  obtain ⟨ι, hfin, A, hAaff, hAinter, hAcover⟩ := exists_finite_affine_basicOpen_cover Y
  obtain ⟨U, hUpre⟩ : ∃ U : ι → Y'.Opens, ∀ i, k ⁻¹ᵁ U i = A i :=
    ⟨fun i => hT.opensCongr (A i), fun i => hT.preimage_opensCongr (A i)⟩
  obtain ⟨V, hVpre⟩ : ∃ V : Y'.Opens, k ⁻¹ᵁ V = Y.basicOpen r :=
    ⟨hT.opensCongr (Y.basicOpen r), hT.preimage_opensCongr _⟩
  have hUaff : ∀ i, IsAffineOpen (U i) := fun i =>
    (isAffineOpen_iff_isAffineOpen_preimage hT (U i)).mpr (by rw [hUpre i]; exact hAaff i)
  have hPaff : ∀ i j, IsAffineOpen (U i ⊓ U j) := fun i j =>
    (isAffineOpen_iff_isAffineOpen_preimage hT _).mpr (by
      change IsAffineOpen (k ⁻¹ᵁ U i ⊓ k ⁻¹ᵁ U j)
      rw [hUpre i, hUpre j]
      exact hAinter i j)
  have hVaff : IsAffineOpen V :=
    (isAffineOpen_iff_isAffineOpen_preimage hT V).mpr (by rw [hVpre]; exact hr)
  have hUcover : (⨆ i, U i) = ⊤ := by
    refine hinj ?_
    rw [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_top]
    simp only [hUpre]
    exact hAcover
  -- the local lifts of `r`, over the members of the cover and over the open matching `Y_r`
  obtain ⟨c, hc⟩ := Scheme.Hom.app_surjective k V hVaff (r |_ (k ⁻¹ᵁ V))
  choose b hb using fun i => Scheme.Hom.app_surjective k (U i) (hUaff i) (r |_ (k ⁻¹ᵁ U i))
  have hWpre : ∀ i, k ⁻¹ᵁ (V ⊓ U i) = Y.basicOpen (r |_ (k ⁻¹ᵁ U i)) := by
    intro i
    rw [basicOpen_restrict_eq]
    change k ⁻¹ᵁ V ⊓ k ⁻¹ᵁ U i = _
    rw [hVpre]
    exact inf_comm _ _
  have hWeq : ∀ i, V ⊓ U i = Y'.basicOpen (b i) := fun i =>
    hinj (by rw [Scheme.preimage_basicOpen, hb i]; exact hWpre i)
  -- the correction over each member of the cover, with a uniform exponent
  have hstep : ∀ i, ∃ (n : ℕ) (F : Γ(Y', U i)), (k.app (U i)) F = 0 ∧
      F |_ (V ⊓ U i)
        = (b i |_ (V ⊓ U i)) ^ n * (b i |_ (V ⊓ U i) - c |_ (V ⊓ U i)) := by
    intro i
    obtain ⟨n, y, hy⟩ := exists_eq_pow_mul_of_isAffineOpen' (hUaff i) (b i) inf_le_right
      (hWeq i) (b i |_ (V ⊓ U i) - c |_ (V ⊓ U i))
    have hezero : (k.app (V ⊓ U i)) (b i |_ (V ⊓ U i) - c |_ (V ⊓ U i)) = 0 :=
      app_sub_eq_zero k r (b i) c inf_le_right inf_le_left (hb i) hc
    have hle : k ⁻¹ᵁ (V ⊓ U i) ≤ k ⁻¹ᵁ U i := k.preimage_mono inf_le_right
    have hy0 : ((k.app (U i)) y) |_ (k ⁻¹ᵁ (V ⊓ U i)) = 0 := by
      rw [← app_restrict k inf_le_right (k.preimage_mono inf_le_right) y, hy, map_mul, map_pow,
        hezero, mul_zero]
    obtain ⟨p, hp⟩ := exists_pow_mul_eq_zero_of_res_eq_zero ((hUaff i).preimage k).isCompact
      ((k.app (U i)) y) (r |_ (k ⁻¹ᵁ U i)) (k.preimage_mono inf_le_right) (hWpre i) hy0
    refine ⟨p + n, b i ^ p * y, ?_, ?_⟩
    · rw [map_mul, map_pow, hb i]
      exact hp
    · rw [restrict_mul inf_le_right, restrict_pow inf_le_right, hy, ← mul_assoc, ← pow_add]
  choose n F hF0 hFe using hstep
  obtain ⟨M, hM⟩ : ∃ M, ∀ i, n i ≤ M :=
    ⟨Finset.univ.sup n, fun i => Finset.le_sup (Finset.mem_univ i)⟩
  have hGstep : ∀ i, ∃ G : Γ(Y', U i), (k.app (U i)) G = 0 ∧
      G |_ (V ⊓ U i)
        = (b i |_ (V ⊓ U i)) ^ M * (b i |_ (V ⊓ U i) - c |_ (V ⊓ U i)) := by
    intro i
    refine ⟨b i ^ (M - n i) * F i, ?_, ?_⟩
    · rw [map_mul, map_pow, hF0 i, mul_zero]
    · rw [restrict_mul inf_le_right, restrict_pow inf_le_right, hFe i, ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel (hM i)]
  choose G hG0 hGe using hGstep
  -- a power of the local lift kills the cocycle, with an exponent uniform over the pairs
  have hpairstep : ∀ i j, ∃ q : ℕ, (b i |_ (U i ⊓ U j)) ^ q *
      ((b i |_ (U i ⊓ U j)) ^ M * (b i |_ (U i ⊓ U j) - b j |_ (U i ⊓ U j))
        - (G i |_ (U i ⊓ U j) - G j |_ (U i ⊓ U j))) = 0 := by
    intro i j
    have hQPi : V ⊓ (U i ⊓ U j) ≤ V ⊓ U i := inf_le_inf le_rfl inf_le_left
    have hQPj : V ⊓ (U i ⊓ U j) ≤ V ⊓ U j := inf_le_inf le_rfl inf_le_right
    have hQ : V ⊓ (U i ⊓ U j) = Y'.basicOpen (b i |_ (U i ⊓ U j)) := by
      rw [basicOpen_restrict_eq, ← hWeq i]
      exact le_antisymm (le_inf inf_le_right (le_inf inf_le_left (inf_le_right.trans inf_le_left)))
        (le_inf (inf_le_right.trans inf_le_left) inf_le_left)
    refine exists_pow_mul_sub_eq_zero hk (hPaff i j) inf_le_right _ _ _ _
      (c |_ (V ⊓ (U i ⊓ U j))) M hQ
      (app_sub_eq_zero k r (b i) (b j) inf_le_left inf_le_right (hb i) (hb j)) ?_ ?_ ?_
    · rw [TopCat.Presheaf.restrict_restrict inf_le_right inf_le_right]
      exact app_sub_eq_zero k r (b j) c (le_trans inf_le_right inf_le_right) inf_le_left (hb j) hc
    · have h2 := congrArg (fun t : Γ(Y', V ⊓ U i) => t |_ (V ⊓ (U i ⊓ U j))) (hGe i)
      simpa only [TopCat.Presheaf.restrict_restrict, restrict_mul, restrict_pow, restrict_sub]
        using h2
    · have h2 := congrArg (fun t : Γ(Y', V ⊓ U j) => t |_ (V ⊓ (U i ⊓ U j))) (hGe j)
      simpa only [TopCat.Presheaf.restrict_restrict, restrict_mul, restrict_pow, restrict_sub]
        using h2
  choose q hq using hpairstep
  obtain ⟨K, hK⟩ : ∃ K, ∀ i j, q i j ≤ K :=
    ⟨Finset.univ.sup fun p : ι × ι => q p.1 p.2,
      fun i j => Finset.le_sup (f := fun p : ι × ι => q p.1 p.2) (Finset.mem_univ (i, j))⟩
  -- the corrected local lifts agree on the overlaps, hence glue
  have hcompat : ∀ i j,
      (b i ^ (K + M + 1) - ((K + M + 1 : ℕ) : Γ(Y', U i)) * (b i ^ K * G i)) |_ (U i ⊓ U j)
        = (b j ^ (K + M + 1) - ((K + M + 1 : ℕ) : Γ(Y', U j)) * (b j ^ K * G j))
            |_ (U i ⊓ U j) := by
    intro i j
    have hgy0 : (k.app (U i ⊓ U j)) (G j |_ (U i ⊓ U j)) = 0 := by
      rw [app_restrict k inf_le_right (k.preimage_mono inf_le_right) (G j), hG0 j, restrict_zero]
    have key := corrected_lift_eq hk (hPaff i j) (b i |_ (U i ⊓ U j)) (b j |_ (U i ⊓ U j))
      (G i |_ (U i ⊓ U j)) (G j |_ (U i ⊓ U j)) K M
      (app_sub_eq_zero k r (b i) (b j) inf_le_left inf_le_right (hb i) (hb j)) hgy0
      (pow_mul_eq_zero_of_le (hK i j) (hq i j))
    simpa only [restrict_sub, restrict_mul, restrict_pow, restrict_natCast] using key
  obtain ⟨r', hr'⟩ : ∃ r' : Γ(Y', ⊤), ∀ i,
      r' |_ U i = b i ^ (K + M + 1) - ((K + M + 1 : ℕ) : Γ(Y', U i)) * (b i ^ K * G i) :=
    (Y'.sheaf.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hUcover.ge
      (fun i => b i ^ (K + M + 1) - ((K + M + 1 : ℕ) : Γ(Y', U i)) * (b i ^ K * G i))
      hcompat).exists
  -- its image downstairs is a power of `r`
  have himg : (k.app ⊤) r' = r ^ (K + M + 1) := by
    refine Y.sheaf.eq_of_locally_eq' (fun i => k ⁻¹ᵁ U i) ⊤ (fun _ => homOfLE le_top)
      (Scheme.Hom.iSup_preimage_eq_top k hUcover).ge _ _ fun i => ?_
    change ((k.app ⊤) r') |_ (k ⁻¹ᵁ U i) = (r ^ (K + M + 1)) |_ (k ⁻¹ᵁ U i)
    rw [← app_restrict k le_top (k.preimage_mono le_top) r', hr' i]
    simp only [map_sub, map_mul, map_pow, map_natCast]
    rw [hG0 i, mul_zero, mul_zero, sub_zero, hb i, restrict_pow le_top]
  refine ⟨r', ?_⟩
  have hpre : k ⁻¹ᵁ Y'.basicOpen r' = Y.basicOpen ((k.app ⊤) r') := Scheme.preimage_basicOpen k r'
  rw [hpre, himg]
  exact Y.basicOpen_pow r (Nat.succ_pos _)

/-! ### The finite-order case, and the ascent of quasi-affineness -/

/-- **An affine basic open lifts along a finite-order thickening with quasi-affine closed
subscheme.** The first-order case
`Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening_of_isQuasiAffine` fed into the
filtration argument `Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening`. -/
theorem affineBasicOpenLifts_of_isFiniteOrderThickening {t : Y ⟶ Y'}
    (ht : IsFiniteOrderThickening t) [Scheme.IsQuasiAffine Y] : AffineBasicOpenLifts t :=
  affineBasicOpenLifts_of_isFirstOrderThickening
    (fun _ _ _ hm hZ => have := hZ
      affineBasicOpenLifts_of_isFirstOrderThickening_of_isQuasiAffine hm) ht

/-- **Quasi-affineness ascends along a finite-order thickening**, with no further hypothesis:
the implication *closed subscheme quasi-affine `⟹` ambient quasi-affine* of
[Stacks Project, Tag 0B7L] for a thickening some power of whose ideal sheaf vanishes. -/
theorem isQuasiAffine_of_isFiniteOrderThickening {t : Y ⟶ Y'}
    (ht : IsFiniteOrderThickening t) [Scheme.IsQuasiAffine Y] : Scheme.IsQuasiAffine Y' :=
  isQuasiAffine_of_affineBasicOpenLifts ht.isThickening
    (affineBasicOpenLifts_of_isFiniteOrderThickening ht)

/-- **A thickening of a quasi-compact locally Noetherian scheme is of finite order.** The kernel
ideal sheaf of a thickening has full support, hence lies in the nilradical, and on a locally
Noetherian scheme it is finitely generated over each affine open, so a power of it vanishes over
each; quasi-compactness makes the exponent uniform.

This is `Stacks.Thickenings.isFiniteOrderThickening_of_isThickening_of_isNoetherianRing` with the
affineness of the ambient scheme relaxed to quasi-compactness, which is all its proof uses. -/
theorem isFiniteOrderThickening_of_isThickening {X X' : Scheme.{u}} {i : X ⟶ X'}
    (hi : IsThickening i) [CompactSpace X'] [IsLocallyNoetherian X'] :
    IsFiniteOrderThickening i := by
  have hfg : ∀ U : X'.affineOpens, (i.ker.ideal U).FG := by
    intro U
    have _ : IsNoetherianRing Γ(X', U.1) := IsLocallyNoetherian.component_noetherian U
    exact IsNoetherian.noetherian _
  exact ⟨hi.1, exists_pow_eq_bot_of_fg_of_support_eq_top hfg hi.support_ker_eq_top⟩

/-- **Quasi-affineness ascends along a thickening of a locally Noetherian scheme.** The thickening
is of finite order by `Stacks.Thickenings.isFiniteOrderThickening_of_isThickening` — the ambient
scheme is quasi-compact because the closed subscheme is and the two are homeomorphic — and then
`Stacks.Thickenings.isQuasiAffine_of_isFiniteOrderThickening` applies. -/
theorem isQuasiAffine_of_isThickening_of_isLocallyNoetherian {k : Y ⟶ Y'} (hk : IsThickening k)
    [Scheme.IsQuasiAffine Y] [IsLocallyNoetherian Y'] : Scheme.IsQuasiAffine Y' :=
  have : CompactSpace Y' := hk.homeomorph.compactSpace
  isQuasiAffine_of_isFiniteOrderThickening (isFiniteOrderThickening_of_isThickening hk)

/-- **[Stacks Project, Tag 0B7K].** For a closed immersion `i : Z ⟶ X` of Noetherian schemes
inducing a homeomorphism of underlying spaces — equivalently, a surjective closed immersion — the
ambient scheme is quasi-affine if and only if the closed subscheme is.

Both implications are unconditional. *Ambient `⟹` closed subscheme* is the elementary one, a
closed immersion being affine (`Stacks.Thickenings.isQuasiAffine_of_isQuasiAffine_ambient`).
*Closed subscheme `⟹` ambient* is
`Stacks.Thickenings.isQuasiAffine_of_isThickening_of_isLocallyNoetherian`: over a Noetherian
scheme a thickening is of finite order, and along a finite-order thickening an affine basic open
lifts, by the square-zero computation of
`Stacks.Thickenings.affineBasicOpenLifts_of_isFirstOrderThickening_of_isQuasiAffine` along the
filtration by the powers of the ideal sheaf. Neither the ampleness criterion
[Stacks Project, Tag 01QE] nor [Stacks Project, Tag 09MS] nor any cohomology group enters, so the
hypothesis `Stacks.AmpleClosedImmersion.SectionsLiftAfterPower` carried by
`Stacks.AmpleSurjectiveThickening.isQuasiAffine_iff_of_sectionsLiftAfterPower` is discharged.

Noetherianness of the closed subscheme is not used, and of the ambient scheme only local
Noetherianness together with quasi-compactness; both are carried because the source assumes
them. -/
@[stacks 0B7K, ega "II 5.1.10" "(vi), special case"]
theorem isQuasiAffine_iff_of_isNoetherian {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    [Surjective i] [IsNoetherian Z] [IsNoetherian X] :
    X.IsQuasiAffine ↔ Z.IsQuasiAffine :=
  have hi : IsThickening i := ⟨inferInstance, Surjective.surj⟩
  ⟨fun hX => isQuasiAffine_of_isQuasiAffine_ambient hi hX,
    fun _ => isQuasiAffine_of_isThickening_of_isLocallyNoetherian hi⟩

/-! ### Part (9) of [Stacks Project, Tag 09ZV] over a locally Noetherian ambient scheme -/

/-- **The implication `φ.left` quasi-affine `⟹` `φ.right` quasi-affine of part (9) of
[Stacks Project, Tag 09ZV], for a morphism of thickenings whose ambient closed subscheme is
locally Noetherian.**

The reduction is the source's: over an affine open `U'` of `S'` the inverse image in `S` is
affine, so `φ.left ⁻¹ᵁ (j ⁻¹ᵁ U')` is quasi-affine; that open is `i ⁻¹ᵁ (φ.right ⁻¹ᵁ U')`, and `i`
restricts over `φ.right ⁻¹ᵁ U'` to a thickening of it whose ambient scheme is an open of `X'`, so
again locally Noetherian, and
`Stacks.Thickenings.isQuasiAffine_of_isThickening_of_isLocallyNoetherian` applies.

No tag attribute: part (9) of the source assumes nothing about the schemes, and local
Noetherianness is what makes the thickening of finite order. The hypothesis is removed, by the
limit argument of [Stacks Project, Tag 09MW], in
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`, and it is
`Stacks.Thickenings.isQuasiAffineHom_left_iff_right` there that carries the tag. -/
theorem isQuasiAffineHom_right_of_left_of_isLocallyNoetherian {X X' S S' : Scheme.{u}}
    {i : X ⟶ X'} {j : S ⟶ S'} (hi : IsThickening i) (hj : IsThickening j)
    (φ : Arrow.mk i ⟶ Arrow.mk j) [hX' : IsLocallyNoetherian X']
    (h : IsQuasiAffineHom φ.left) : IsQuasiAffineHom φ.right := by
  have : IsLocallyNoetherian (Arrow.mk i).right := hX'
  refine ⟨fun U' hU' ↦ ?_⟩
  have hQA : Scheme.IsQuasiAffine (φ.left ⁻¹ᵁ (j ⁻¹ᵁ U')) :=
    h.isQuasiAffine_preimage _ ((isAffineOpen_iff_isAffineOpen_preimage hj U').mp hU')
  rw [preimage_left_preimage_eq_preimage_preimage_right φ U'] at hQA
  have := hQA
  have : IsLocallyNoetherian (φ.right ⁻¹ᵁ U').toScheme :=
    isLocallyNoetherian_of_isOpenImmersion (φ.right ⁻¹ᵁ U').ι
  exact isQuasiAffine_of_isThickening_of_isLocallyNoetherian (hi.morphismRestrict _)

/-- **Part (9) of [Stacks Project, Tag 09ZV] for a morphism of thickenings whose ambient closed
subscheme is locally Noetherian**: the morphism of closed subschemes is quasi-affine if and only
if the morphism of ambient schemes is.

The `mpr` half is unconditional and is `Stacks.Thickenings.isQuasiAffineHom_left_of_right`; the
`mp` half is `Stacks.Thickenings.isQuasiAffineHom_right_of_left_of_isLocallyNoetherian`.

No tag attribute: part (9) assumes nothing about the schemes, so this is not the source
statement. The source statement is
`Stacks.Thickenings.isQuasiAffineHom_left_iff_right` of
`StacksFrontier/AlgebraicGeometry/MoreMorphisms/ThickeningMorphism/QuasiAffineLimit.lean`. -/
theorem isQuasiAffineHom_left_iff_right_of_isLocallyNoetherian {X X' S S' : Scheme.{u}}
    {i : X ⟶ X'} {j : S ⟶ S'} (hi : IsThickening i) (hj : IsThickening j)
    (φ : Arrow.mk i ⟶ Arrow.mk j) [IsLocallyNoetherian X'] :
    IsQuasiAffineHom φ.left ↔ IsQuasiAffineHom φ.right :=
  ⟨isQuasiAffineHom_right_of_left_of_isLocallyNoetherian hi hj φ,
    isQuasiAffineHom_left_of_right hi hj φ⟩

end Stacks.Thickenings

end
