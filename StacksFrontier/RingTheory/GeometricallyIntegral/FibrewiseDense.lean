module

public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.Algebra.Category.Ring.Epi.GenericFlatness
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.GeometricallyIntegral.ReducedLocus

/-!
# Fibrewise scheme-theoretic density spreads out, and the geometrically reduced fibre locus

Stacks 0573 says: for `f : X → Y` of finite type with `Y` irreducible with generic point `η`, and
`U ⊆ X` an open subscheme whose generic fibre `U_η` is scheme theoretically dense in `X_η`, the
fibre `U_y` is scheme theoretically dense in `X_y` for every `y` in a nonempty open of `Y`. This
file proves the affine case, which is the only case the proof of Stacks 0578 needs, and uses it to
reduce the *good half* of the generic-fibre dichotomy for geometric reducedness — the affine case
of Stacks 0578 at the generic point, one of the two statements to which
`StacksFrontier.RingTheory.GeometricallyIntegral.ConstructibleFibreLocus05FT` reduces
constructibility of the geometrically integral fibre locus — to a statement about a *single*
fibre, with no spreading out left in it.

## The affine translation

Let `A` be a domain with fraction field `F` and `B` a finite type `A`-algebra. A quasi-compact
open `U ⊆ Spec B` is a finite union of basic opens `D(g 1), …, D(g m)`, and `U` is scheme
theoretically dense in `Spec B` exactly when `B → ⨁ⱼ B_{g j}` is injective
(Stacks 056C), which by Stacks 0565 is the same as injectivity of the multiplication tuple
`b ↦ (g 1 * b, …, g m * b)`; that is `Algebra.mulTuple`. Spreading out is then the statement that
injectivity of `mulTuple g` after base change to `F` forces injectivity after base change to the
residue field at every prime of a nonempty basic open of `Spec A`, which is
`Algebra.exists_ne_zero_forall_mulTuple_eq_zero_imp_eq_zero`.

The proof is the one in the source, with the two shrinkings of the base merged into one element.
Write `I` for the kernel and `Q` for the cokernel of `mulTuple g` as a map of `B`-modules. The
generic injectivity says that `F ⊗[A] I = 0`, so each element of `I` is killed by a nonzero
element of `A`; `I` is finitely generated because `A` is Noetherian, hence so is `B`, so a single
nonzero `a : A` kills `I`. Generic freeness (Stacks 051T,
`Algebra.exists_ne_zero_isFinitePresentationFreeAway`) supplies a nonzero `b : A` making `Q`
free, hence flat, over `A_b`; moving the condition from `b` to `a * b` is
`Algebra.IsFinitePresentationFreeAway.of_dvd`. Over `A_{a b}` the sequence
`0 → A_{ab} ⊗ B → A_{ab} ⊗ Bᵐ → A_{ab} ⊗ Q → 0` is therefore short exact with flat quotient, so
Stacks 00HL (`flat_tor_zero`) keeps it exact after tensoring with *any* `A_{ab}`-module — in
particular with any `A`-algebra `K` in which `a * b` is invertible, which includes every residue
field at a prime of the basic open `D(a b)`.

## Main definitions

* `Algebra.mulTuple g`: the `B`-linear map `b ↦ fun j => g j * b` from `B` to `Fin m → B`, whose
  injectivity after base change expresses scheme theoretic density of `⋃ⱼ D(g j)` in the relevant
  fibre.

## Main results

* `Algebra.eq_zero_of_forall_exists_pow_mul_eq_zero`: the affine case of Stacks 0565. If no
  nonzero element of a ring is annihilated by all of `g 1, …, g m`, then no nonzero element is
  annihilated by a power of each of them; equivalently `R → ⨁ⱼ R_{g j}` is injective as soon as
  the multiplication tuple is.
* `Algebra.isReduced_of_mulTuple_injective_of_isReduced_away`: the affine case of Stacks 056E for
  reducedness. A ring with a scheme theoretically dense open union of basic opens, each of which
  is reduced, is reduced.
* `Algebra.exists_ne_zero_forall_injective_lTensor_of_smul_ker_eq_zero` and
  `Algebra.exists_ne_zero_smul_ker_eq_zero`: the two halves of the affine case of Stacks 0573 for
  an arbitrary map of finite modules over a finite type algebra.
* `Algebra.exists_ne_zero_smul_eq_zero_of_mem_ker` and
  `Algebra.exists_ne_zero_forall_injective_lTensor_of_forall_exists_smul_eq_zero`: the same two
  halves over a base which is only a domain. Each element of the kernel is separately `A`-torsion,
  and generic freeness is applied to the source module as well as to the cokernel, so that the
  kernel is killed by a power of the inverted element instead of by one element of the base.
* `Algebra.exists_ne_zero_forall_mulTuple_eq_zero_imp_eq_zero`: **the affine case of Stacks
  0573.** Fibrewise scheme theoretic density of `⋃ⱼ D(g j)` spreads from the generic fibre to the
  fibres over a nonempty basic open of the base.
* `Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_of_mulTuple`: **the affine case
  of Stacks 0578 at the generic point, reduced to one fibre.** If some finite union of basic opens
  of `Spec T` is scheme theoretically dense in the generic fibre and has geometrically reduced
  fibres over the base, then a nonempty basic open of `Spec D` lies in the geometrically reduced
  fibre locus.

## What this does and does not discharge

`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_of_mulTuple` has no quantifier
over the base left in it: both hypotheses are about the single algebra `T` over the single base
`D`, one of them about the generic fibre alone. What remains in order to supply the hypothesis
`hred` of `Algebra.isConstructible_geometricallyIntegralFibreLocus_of_free_halves`, and hence the
hypothesis `hConstr` of
`AlgebraicGeometry.exists_elementaryEtaleNeighborhood_projective_sections`, is to *produce* the
tuple `g` from geometric reducedness of the generic fibre: by Stacks 056V
(`AlgebraicGeometry.geometricallyReduced_iff_exists_dense_open_smooth`) the generic fibre of a
geometrically reduced finite type algebra has a dense open which is smooth over the base field,
and by Stacks 02V4 a point of the generic fibre at which the fibre is smooth is a point at which
the morphism is smooth, the generic fibre of a flat algebra being its own smooth locus. Supplying
`g` therefore needs Stacks 02V4 and the fact that a smooth morphism has geometrically reduced
fibres (`AlgebraicGeometry.geometricallyReduced_of_smooth`), neither of which is proved
here. Nothing below is conditional on them: the statements are unconditional, and it is the
*application* that is not yet available.

Nothing here carries a `@[stacks 0573]`, `@[stacks 0565]`, `@[stacks 056E]` or `@[stacks 0578]`
attribute. Stacks 0573, 056E and 0578 are statements about schemes and only their affine cases are
proved; 0565 is proved only in the form the affine case of 056C needs. The `@[stacks 05FT]` and
`@[stacks 0579]` tags stay absent for the reason given in
`StacksFrontier.RingTheory.GeometricallyIntegral.ReducedLocus`: the statements reached are still
conditional.

## References

* [Stacks Project, Tag 0573](https://stacks.math.columbia.edu/tag/0573)
* [Stacks Project, Tag 0578](https://stacks.math.columbia.edu/tag/0578)
* [Stacks Project, Tag 0579](https://stacks.math.columbia.edu/tag/0579)
* [Stacks Project, Tag 056C](https://stacks.math.columbia.edu/tag/056C)
* [Stacks Project, Tag 056E](https://stacks.math.columbia.edu/tag/056E)
* [Stacks Project, Tag 0565](https://stacks.math.columbia.edu/tag/0565)
* [Stacks Project, Tag 051T](https://stacks.math.columbia.edu/tag/051T)
* [Stacks Project, Tag 00HL](https://stacks.math.columbia.edu/tag/00HL)
* [Stacks Project, Tag 05FT](https://stacks.math.columbia.edu/tag/05FT)
-/

@[expose] public section

open TensorProduct

universe u

namespace Algebra

section Annihilator

variable {R : Type*} [CommRing R] {m : ℕ}

/-- **The affine case of Stacks 0565.** Let `g 1, …, g m` be elements of a commutative ring `R`
such that the only element annihilated by all of them is `0`. Then the only element annihilated by
*some power* of each of them is `0`; that is, the kernel of `R → ⨁ⱼ R_{g j}` is zero.

The induction is on `∑ⱼ n j`. If some `n j` is zero the element is zero outright. Otherwise each
`g j * b` is annihilated by a tuple of smaller total degree, hence vanishes, and then the
hypothesis applies to `b` itself. -/
theorem eq_zero_of_forall_exists_pow_mul_eq_zero (g : Fin m → R)
    (hann : ∀ b : R, (∀ j, g j * b = 0) → b = 0) (b : R)
    (hb : ∀ j, ∃ n : ℕ, g j ^ n * b = 0) : b = 0 := by
  classical
  choose n hn using hb
  suffices H : ∀ N : ℕ, ∀ (n : Fin m → ℕ) (b : R), ∑ j, n j = N →
      (∀ j, g j ^ n j * b = 0) → b = 0 from H _ n b rfl hn
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro n b hsum hzero
    by_cases h0 : ∃ j, n j = 0
    · obtain ⟨j, hj⟩ := h0
      simpa [hj] using hzero j
    · have hpos : ∀ j, 1 ≤ n j := fun j => Nat.one_le_iff_ne_zero.mpr fun h => h0 ⟨j, h⟩
      refine hann b fun j => ?_
      have hlt : ∑ i, (if i = j then n i - 1 else n i) < N := by
        rw [← hsum]
        refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ j, ?_⟩
        · by_cases hij : i = j
          · simp only [hij, ite_true]; omega
          · simp only [hij, ite_false]; exact le_refl _
        · simp only [ite_true]
          have := hpos j; omega
      refine ih _ hlt (fun i => if i = j then n i - 1 else n i) (g j * b) rfl fun i => ?_
      by_cases hij : i = j
      · subst hij
        have h1 : g i ^ (n i - 1) * (g i * b) = g i ^ (n i - 1 + 1) * b := by
          rw [pow_succ]; ring
        have h2 : n i - 1 + 1 = n i := by have := hpos i; omega
        simp only [ite_true]
        rw [h1, h2]
        exact hzero i
      · simp only [hij, ite_false]
        have h3 : g i ^ n i * (g j * b) = g j * (g i ^ n i * b) := by ring
        rw [h3, hzero i, mul_zero]

/-- **The affine case of Stacks 056E for reducedness.** If the only element of `R` annihilated by
all of `g 1, …, g m` is `0` — that is, if `⋃ⱼ D(g j)` is scheme theoretically dense in `Spec R` —
and each localization `R_{g j}` is reduced, then `R` is reduced.

A nilpotent element of `R` becomes nilpotent, hence zero, in each `R_{g j}`, so some power of each
`g j` annihilates it; `Algebra.eq_zero_of_forall_exists_pow_mul_eq_zero` then makes it zero. -/
theorem isReduced_of_mulTuple_injective_of_isReduced_away (g : Fin m → R)
    (hann : ∀ b : R, (∀ j, g j * b = 0) → b = 0)
    (hred : ∀ j, IsReduced (Localization.Away (g j))) : IsReduced R := by
  refine ⟨fun x hx => ?_⟩
  refine eq_zero_of_forall_exists_pow_mul_eq_zero g hann x fun j => ?_
  have h0 : algebraMap R (Localization.Away (g j)) x = 0 :=
    (hred j).eq_zero _ (hx.map (algebraMap R (Localization.Away (g j))))
  obtain ⟨⟨s, n, rfl⟩, hs⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers (g j))
      (Localization.Away (g j)) x).mp h0
  exact ⟨n, hs⟩

end Annihilator

section MulTuple

/-- The tuple of multiplication operators attached to `g 1, …, g m` in a ring `B`, as a `B`-linear
map `B →ₗ[B] (Fin m → B)`. Injectivity of its base change to an `A`-algebra `K` says that
`⋃ⱼ D(g j)` is scheme theoretically dense in `Spec (K ⊗[A] B)`, by Stacks 056C and Stacks 0565. -/
def mulTuple {B : Type u} [CommRing B] {m : ℕ} (g : Fin m → B) : B →ₗ[B] (Fin m → B) :=
  LinearMap.pi fun j => LinearMap.mulLeft B (g j)

/-- The `j`-th component of `mulTuple g t` is `g j * t`. -/
@[simp]
theorem mulTuple_apply {B : Type u} [CommRing B] {m : ℕ} (g : Fin m → B) (t : B) (j : Fin m) :
    mulTuple g t j = g j * t := rfl

variable {A B K : Type u} [CommRing A] [CommRing B] [Algebra A B] [CommRing K] [Algebra A K]

/-- Base changing multiplication by `b` is multiplication by `1 ⊗ₜ b`. -/
theorem lTensor_mulLeft_apply (b : B) (z : K ⊗[A] B) :
    LinearMap.lTensor K ((LinearMap.mulLeft B b).restrictScalars A) z = ((1 : K) ⊗ₜ b) * z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul k t => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => rw [map_add, hx, hy, mul_add]

/-- An element of a fibre annihilated by every `1 ⊗ₜ g j` is in the kernel of the base change of
`Algebra.mulTuple g`. -/
theorem lTensor_mulTuple_eq_zero {m : ℕ} (g : Fin m → B) (z : K ⊗[A] B)
    (hz : ∀ j, ((1 : K) ⊗ₜ g j) * z = 0) :
    LinearMap.lTensor K ((mulTuple g).restrictScalars A) z = 0 := by
  classical
  have hdec : (mulTuple g).restrictScalars A
      = ∑ j, (LinearMap.single A (fun _ : Fin m => B) j).comp
          ((LinearMap.mulLeft B (g j)).restrictScalars A) := by
    refine LinearMap.ext fun t => funext fun i => ?_
    rw [LinearMap.sum_apply]
    simp [Finset.sum_apply, Pi.single_apply]
  have h0 : AlgebraTensorModule.lTensor A K ((mulTuple g).restrictScalars A) z = 0 := by
    rw [hdec, map_sum, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [AlgebraTensorModule.lTensor_comp]
    show (AlgebraTensorModule.lTensor A K (LinearMap.single A (fun _ : Fin m => B) j))
      ((AlgebraTensorModule.lTensor A K ((LinearMap.mulLeft B (g j)).restrictScalars A)) z) = 0
    rw [show (AlgebraTensorModule.lTensor A K
          ((LinearMap.mulLeft B (g j)).restrictScalars A)) z
        = ((1 : K) ⊗ₜ g j) * z from lTensor_mulLeft_apply _ _, hz j, map_zero]
  exact h0

/-- Conversely, an element of the kernel of the base change of `Algebra.mulTuple g` is annihilated
by every `1 ⊗ₜ g j`. -/
theorem mul_eq_zero_of_lTensor_mulTuple_eq_zero {m : ℕ} (g : Fin m → B) (z : K ⊗[A] B)
    (hz : LinearMap.lTensor K ((mulTuple g).restrictScalars A) z = 0) (j : Fin m) :
    ((1 : K) ⊗ₜ g j) * z = 0 := by
  have hproj : ((LinearMap.proj j : (Fin m → B) →ₗ[A] B)).comp
      ((mulTuple g).restrictScalars A) = (LinearMap.mulLeft B (g j)).restrictScalars A := rfl
  have h2 : AlgebraTensorModule.lTensor A K (LinearMap.proj j : (Fin m → B) →ₗ[A] B)
      ((AlgebraTensorModule.lTensor A K ((mulTuple g).restrictScalars A)) z) = 0 := by
    rw [show (AlgebraTensorModule.lTensor A K ((mulTuple g).restrictScalars A)) z = 0 from hz,
      map_zero]
  rw [← LinearMap.comp_apply, ← AlgebraTensorModule.lTensor_comp, hproj] at h2
  rw [← lTensor_mulLeft_apply (A := A) (K := K) (g j) z]
  exact h2

end MulTuple

section SpreadOut

/-- Generic freeness in base-change form: if the condition of Stacks 051U holds for `f`, then the
base change of `Q` to `A_f` is flat. The condition is stated for the localization of `Q` at the
image of the powers of `f` in `B`; that localization is also the localization of `Q` at the powers
of `f` as an `A`-module (`IsLocalizedModule.restrictScalars_powers`), hence is the base change
`A_f ⊗[A] Q` by `isLocalizedModule_iff_isBaseChange`. -/
theorem flat_baseChange_of_isFinitePresentationFreeAway
    {A B Q : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup Q] [Module B Q] [Module A Q] [IsScalarTower A B Q] (f : A)
    (h : Algebra.IsFinitePresentationFreeAway A B Q f) :
    Module.Flat (Localization.Away f) (Localization.Away f ⊗[A] Q) := by
  have hfree : Module.Free (Localization.Away f)
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) ⊗[B] Q) := h.2.2.2
  let l : Q →ₗ[B] Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) ⊗[B] Q :=
    TensorProduct.mk B _ Q 1
  have h1 : IsLocalizedModule (Submonoid.powers (algebraMap A B f)) l := by
    rw [← Algebra.algebraMapSubmonoid_powers]
    exact inferInstance
  have h3 := (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) (Localization.Away f)
    (l.restrictScalars A)).mp (IsLocalizedModule.restrictScalars_powers f l)
  have : Module.Flat (Localization.Away f)
      (Localization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) ⊗[B] Q) :=
    Module.Flat.of_free
  exact Module.Flat.of_linearEquiv h3.equiv

/-- A module killed by an element which acts invertibly on the base of a base change has zero base
change. -/
theorem subsingleton_tensorProduct_of_smul_eq_zero {A E X : Type u} [CommRing A] [CommRing E]
    [Algebra A E] [AddCommGroup X] [Module A X] (a : A) (ha : IsUnit (algebraMap A E a))
    (hX : ∀ x : X, a • x = 0) : Subsingleton (E ⊗[A] X) := by
  have h1 : ∀ z : E ⊗[A] X, a • z = 0 := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hX x, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  refine subsingleton_of_forall_eq 0 fun z => ?_
  have h2 : (algebraMap A E a) • z = 0 := by rw [algebraMap_smul, h1 z]
  obtain ⟨u, hu⟩ := ha
  simpa [smul_smul, ← hu] using congrArg (fun y : E ⊗[A] X => (↑u⁻¹ : E) • y) h2

/-- Base change along `A → K` factors through an intermediate `A`-algebra `E`, so injectivity of
the base change to `K` of the base change to `E` gives injectivity of the base change to `K`. -/
theorem injective_lTensor_of_injective_lTensor_baseChange
    {A E K M N : Type u} [CommRing A] [CommRing E] [Algebra A E] [CommRing K] [Algebra A K]
    [Algebra E K] [IsScalarTower A E K]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (φ : M →ₗ[A] N)
    (h : Function.Injective (LinearMap.lTensor K (LinearMap.baseChange E φ))) :
    Function.Injective (LinearMap.lTensor K φ) := by
  have hcomm := AlgebraTensorModule.lTensor_comp_cancelBaseChange A E K
    (M := K) (N := M) (Q := N) φ
  have hT : Function.Injective
      (AlgebraTensorModule.lTensor K K (AlgebraTensorModule.lTensor E E φ)) := h
  intro x y hxy
  obtain ⟨u, rfl⟩ := (AlgebraTensorModule.cancelBaseChange A E K K M).surjective x
  obtain ⟨v, rfl⟩ := (AlgebraTensorModule.cancelBaseChange A E K K M).surjective y
  have h1 := LinearMap.congr_fun hcomm u
  have h2 := LinearMap.congr_fun hcomm v
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe] at h1 h2
  have hxy' : (AlgebraTensorModule.cancelBaseChange A E K K N)
      ((AlgebraTensorModule.lTensor K K (AlgebraTensorModule.lTensor E E φ)) u) =
      (AlgebraTensorModule.cancelBaseChange A E K K N)
      ((AlgebraTensorModule.lTensor K K (AlgebraTensorModule.lTensor E E φ)) v) := by
    rw [← h1, ← h2]; exact hxy
  exact congrArg _ (hT ((AlgebraTensorModule.cancelBaseChange A E K K N).injective hxy'))

/-- Injectivity of `φ` after base change to `E = A_f` spreads to every `A`-algebra `K` in which `f`
is invertible, once the base change of the cokernel to `E` is flat and that of `ker φ` vanishes. -/
private theorem injective_lTensor_of_flat_quotient_of_subsingleton_ker
    {A B M N : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (φ : M →ₗ[B] N) {f : A}
    (hflatQ : Module.Flat (Localization.Away f) (Localization.Away f ⊗[A] (N ⧸ LinearMap.range φ)))
    (hsub : Subsingleton (Localization.Away f ⊗[A] (LinearMap.ker (φ.restrictScalars A))))
    (K : Type u) [CommRing K] [Algebra A K] (hunit : IsUnit (algebraMap A K f)) :
    Function.Injective (LinearMap.lTensor K (φ.restrictScalars A)) := by
  have hinjRf : Function.Injective
      (LinearMap.lTensor (Localization.Away f) (φ.restrictScalars A)) := by
    have hex := Module.Flat.lTensor_exact (Localization.Away f)
      (LinearMap.exact_subtype_ker_map (φ.restrictScalars A))
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨w, hw⟩ := (hex z).mp hz
    rw [← hw, Subsingleton.elim w 0, map_zero]
  have hexφψ : Function.Exact (φ.restrictScalars A)
      (((LinearMap.range φ).mkQ).restrictScalars A) := LinearMap.exact_map_mkQ_range φ
  have hexRf := Module.Flat.lTensor_exact (Localization.Away f) hexφψ
  have hsurjRf : Function.Surjective (LinearMap.lTensor (Localization.Away f)
      (((LinearMap.range φ).mkQ).restrictScalars A)) :=
    LinearMap.lTensor_surjective (Localization.Away f)
      (g := ((LinearMap.range φ).mkQ).restrictScalars A)
      (Submodule.mkQ_surjective (LinearMap.range φ))
  let algRfK : Algebra (Localization.Away f) K :=
    (IsLocalization.lift (M := Submonoid.powers f) (S := Localization.Away f)
      (g := algebraMap A K)
      (fun y => by obtain ⟨n, hn⟩ := y.2; rw [← hn]; simpa [map_pow] using hunit.pow n)).toAlgebra
  have : IsScalarTower A (Localization.Away f) K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq _ x).symm
  refine injective_lTensor_of_injective_lTensor_baseChange
    (E := Localization.Away f) (φ.restrictScalars A) ?_
  exact (flat_tor_zero (R := Localization.Away f) (N := K)
      (M'' := Localization.Away f ⊗[A] M) (M' := Localization.Away f ⊗[A] N)
      (M := Localization.Away f ⊗[A] (N ⧸ LinearMap.range φ))
      (LinearMap.baseChange (Localization.Away f) (φ.restrictScalars A))
      (LinearMap.baseChange (Localization.Away f)
        (((LinearMap.range φ).mkQ).restrictScalars A))
      (by rw [LinearMap.baseChange_eq_ltensor]; exact hinjRf)
      (by rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]; exact hexRf)
      (by rw [LinearMap.baseChange_eq_ltensor]; exact hsurjRf)).1

/-- If a map `φ` is injective after base change to the fraction field of a domain `A`, each element
of its kernel is killed by a nonzero element of `A`. -/
private theorem exists_ne_zero_smul_eq_zero_of_injective_lTensor_fractionRing
    {A M N : Type u} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (φ : M →ₗ[A] N)
    (hgen : Function.Injective (LinearMap.lTensor (FractionRing A) φ))
    (x : M) (hx : φ x = 0) : ∃ c : A, c ≠ 0 ∧ c • x = 0 := by
  have h0 : (TensorProduct.mk A (FractionRing A) M 1) x = 0 := by
    refine hgen ?_
    show LinearMap.lTensor (FractionRing A) φ ((1 : FractionRing A) ⊗ₜ x) =
      LinearMap.lTensor (FractionRing A) φ 0
    simp [hx]
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := nonZeroDivisors A) (f := TensorProduct.mk A (FractionRing A) M 1)
    (x₁ := x) (x₂ := 0) (by rw [h0, map_zero])
  exact ⟨(c : A), nonZeroDivisors.ne_zero c.2, by simpa [Submonoid.smul_def] using hc⟩

variable {A B M N : Type u} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
  [Algebra.FiniteType A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

/-- **The kernel of a generically injective map of finite modules is killed by one element of the
base.** If `φ : M →ₗ[B] N` becomes injective after base change to the fraction field of a
Noetherian domain `A`, then a single nonzero `a : A` annihilates its kernel.

Each element of the kernel goes to zero in `F ⊗[A] M`, which is the localization of `M` at the
nonzero elements of `A`, so each is killed by some nonzero element of `A`; the kernel is a
finitely generated `B`-module because `B` is Noetherian, so the product of the finitely many
elements obtained from a generating set works. -/
theorem exists_ne_zero_smul_ker_eq_zero [IsNoetherianRing A] [Module.Finite B M] (φ : M →ₗ[B] N)
    (hgen : Function.Injective (LinearMap.lTensor (FractionRing A) (φ.restrictScalars A))) :
    ∃ a : A, a ≠ 0 ∧ ∀ x : M, φ x = 0 → a • x = 0 := by
  classical
  have hBN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hMN : IsNoetherian B M := inferInstance
  have key := exists_ne_zero_smul_eq_zero_of_injective_lTensor_fractionRing (φ.restrictScalars A)
    hgen
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (LinearMap.ker φ) : (LinearMap.ker φ).FG)
  have hmem : ∀ x : {y // y ∈ s}, φ (x : M) = 0 := by
    intro x
    have hx : (x : M) ∈ LinearMap.ker φ := hs ▸ Submodule.subset_span x.2
    exact hx
  have hchoice : ∀ x : {y // y ∈ s}, ∃ c : A, c ≠ 0 ∧ c • (x : M) = 0 :=
    fun x => key x (hmem x)
  choose c hc0 hcz using hchoice
  refine ⟨∏ x ∈ s.attach, c x, Finset.prod_ne_zero_iff.mpr fun x _ => hc0 x, ?_⟩
  intro x hx
  have hx' : x ∈ Submodule.span B (s : Set M) := hs ▸ (hx : x ∈ LinearMap.ker φ)
  clear hx
  induction hx' using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem c (Finset.mem_attach s ⟨y, hy⟩)
      rw [hd, mul_comm, mul_smul, hcz ⟨y, hy⟩, smul_zero]
  | zero => simp
  | add y z hy hz ihy ihz => rw [smul_add, ihy, ihz, add_zero]
  | smul b y hy ih => rw [smul_comm, ih, smul_zero]

/-- **The affine case of Stacks 0573, for an arbitrary map of finite modules.** Let `A` be a
domain, `B` a finite type `A`-algebra and `φ : M →ₗ[B] N` a map of finite `B`-modules whose kernel
is annihilated by a nonzero `a : A`. Then there is a nonzero `f : A`, a multiple of `a`, such that
`φ` stays injective after base change to *every* `A`-algebra in which `f` is invertible.

Generic freeness makes the cokernel of `φ` free, hence flat, over `A_f` for a suitable multiple
`f` of `a`; over `A_f` the kernel of `φ` has vanishing base change, so `φ` base changes to a short
exact sequence with flat quotient, and Stacks 00HL keeps that exact after any further base
change. -/
theorem exists_ne_zero_forall_injective_lTensor_of_smul_ker_eq_zero [Module.Finite B N]
    (φ : M →ₗ[B] N) {a : A} (ha0 : a ≠ 0) (hakill : ∀ x : M, φ x = 0 → a • x = 0) :
    ∃ f : A, f ≠ 0 ∧ ∀ (K : Type u) [CommRing K] [Algebra A K], IsUnit (algebraMap A K f) →
      Function.Injective (LinearMap.lTensor K (φ.restrictScalars A)) := by
  classical
  obtain ⟨b, hb0, hbfree⟩ := Algebra.exists_ne_zero_isFinitePresentationFreeAway
    (R := A) (S := B) (M := N ⧸ LinearMap.range φ)
  refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
  have hfree : Algebra.IsFinitePresentationFreeAway A B (N ⧸ LinearMap.range φ) (a * b) :=
    hbfree.of_dvd ⟨a, mul_comm a b⟩
  have hflatQ : Module.Flat (Localization.Away (a * b))
      (Localization.Away (a * b) ⊗[A] (N ⧸ LinearMap.range φ)) :=
    flat_baseChange_of_isFinitePresentationFreeAway (a * b) hfree
  have hRfunit : IsUnit (algebraMap A (Localization.Away (a * b)) (a * b)) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (a * b)) (a * b)
  have haRf : IsUnit (algebraMap A (Localization.Away (a * b)) a) := by
    have h : IsUnit (algebraMap A (Localization.Away (a * b)) a *
        algebraMap A (Localization.Away (a * b)) b) := by
      simpa [map_mul] using hRfunit
    exact (IsUnit.mul_iff.mp h).1
  have hsub : Subsingleton
      (Localization.Away (a * b) ⊗[A] (LinearMap.ker (φ.restrictScalars A))) :=
    subsingleton_tensorProduct_of_smul_eq_zero a haRf
      fun x => Subtype.ext (hakill (x : M) x.2)
  intro K _ _ hunit
  exact injective_lTensor_of_flat_quotient_of_subsingleton_ker φ hflatQ hsub K hunit

/-- **The affine case of Stacks 0573.** Let `A` be a Noetherian domain and `B` a finite type
`A`-algebra, and let `g 1, …, g m` be elements of `B` whose basic opens cover a scheme
theoretically dense open of the generic fibre — that is, the only element of
`F ⊗[A] B` annihilated by all the `1 ⊗ₜ g j` is zero, `F` the fraction field of `A`. Then there is
a nonzero `f : A` with the same property in `K ⊗[A] B` for every `A`-algebra `K` in which `f` is
invertible, in particular in the fibre at every prime of the basic open `D(f)`. -/
theorem exists_ne_zero_forall_mulTuple_eq_zero_imp_eq_zero [IsNoetherianRing A] {m : ℕ}
    (g : Fin m → B)
    (hgen : ∀ z : FractionRing A ⊗[A] B,
      (∀ j, ((1 : FractionRing A) ⊗ₜ g j) * z = 0) → z = 0) :
    ∃ f : A, f ≠ 0 ∧ ∀ (K : Type u) [CommRing K] [Algebra A K], IsUnit (algebraMap A K f) →
      ∀ z : K ⊗[A] B, (∀ j, ((1 : K) ⊗ₜ g j) * z = 0) → z = 0 := by
  have hgen' : Function.Injective
      (LinearMap.lTensor (FractionRing A) ((mulTuple g).restrictScalars A)) := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    exact hgen z fun j => mul_eq_zero_of_lTensor_mulTuple_eq_zero g z hz j
  obtain ⟨a, ha0, hakill⟩ := exists_ne_zero_smul_ker_eq_zero (mulTuple g) hgen'
  obtain ⟨f, hf0, hf⟩ :=
    exists_ne_zero_forall_injective_lTensor_of_smul_ker_eq_zero (mulTuple g) ha0 hakill
  refine ⟨f, hf0, fun K _ _ hunit z hz => ?_⟩
  have := hf K hunit
  rw [injective_iff_map_eq_zero] at this
  exact this z (lTensor_mulTuple_eq_zero g z hz)

end SpreadOut

/-- **The affine case of Stacks 0578 at the generic point, reduced to a single fibre.** Let `D` be
a Noetherian domain and `T` a finite type `D`-algebra. Suppose `g 1, …, g m` are elements of `T`
such that

* `⋃ⱼ D(g j)` is scheme theoretically dense in the generic fibre, i.e. no nonzero element of
  `F ⊗[D] T` is annihilated by all the `1 ⊗ₜ g j`, and
* each `D(g j)` has geometrically reduced fibres, i.e. `(K ⊗[D] T)_{g j}` is reduced for every
  field `K` over `D`.

Then a nonempty basic open of `Spec D` is contained in the geometrically reduced fibre locus of
`T`.

This is the good half of the generic-fibre dichotomy of Stacks 0577/0578 for geometric
reducedness, which — by
`Algebra.exists_basicOpen_subset_geometricallyReducedFibreLocus_iff_isConstructible` — is
equivalent to the affine case of Stacks 0579, and is one of the two inputs of
`Algebra.isConstructible_geometricallyIntegralFibreLocus_of_free_halves`. The spreading out is
`Algebra.exists_ne_zero_forall_mulTuple_eq_zero_imp_eq_zero` (Stacks 0573) and the passage from a
dense open with reduced fibres to a reduced fibre is
`Algebra.isReduced_of_mulTuple_injective_of_isReduced_away` (Stacks 056E). -/
theorem exists_basicOpen_subset_geometricallyReducedFibreLocus_of_mulTuple
    {D T : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [CommRing T] [Algebra D T]
    [Algebra.FiniteType D T] {m : ℕ} (g : Fin m → T)
    (hgen : ∀ z : FractionRing D ⊗[D] T,
      (∀ j, ((1 : FractionRing D) ⊗ₜ g j) * z = 0) → z = 0)
    (hgood : ∀ (K : Type u) [Field K] [Algebra D K] (j : Fin m),
      IsReduced (Localization.Away (((1 : K) ⊗ₜ g j : K ⊗[D] T)))) :
    ∃ f : D, f ≠ 0 ∧ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum D)) ⊆
      geometricallyReducedFibreLocus D T := by
  obtain ⟨f, hf0, hf⟩ := exists_ne_zero_forall_mulTuple_eq_zero_imp_eq_zero g hgen
  refine ⟨f, hf0, fun p hp => ?_⟩
  intro K _ _ hker
  have hfK : IsUnit (algebraMap D K f) := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    exact (PrimeSpectrum.mem_basicOpen f p).mp hp (hker ▸ RingHom.mem_ker.mpr h0)
  have hred : IsReduced (K ⊗[D] T) :=
    isReduced_of_mulTuple_injective_of_isReduced_away (fun j => (1 : K) ⊗ₜ g j)
      (fun z hz => hf K hfK z hz) (hgood K)
  exact (isReduced_congr (Algebra.TensorProduct.comm D K T).toRingEquiv).mp hred

section TorsionSpreadOut

/-- A base change on which every element is killed by a scalar becoming invertible downstairs is
zero: if each `x : X` has some `a : A` with `a • x = 0` and `a` a unit in `E`, then `E ⊗[A] X`
is trivial. Unlike `Algebra.subsingleton_tensorProduct_of_smul_eq_zero` the scalar may depend on
the element, which is what removes the need for a finiteness hypothesis on `X`. -/
theorem subsingleton_tensorProduct_of_forall_exists_smul_eq_zero {A E X : Type u} [CommRing A]
    [CommRing E] [Algebra A E] [AddCommGroup X] [Module A X]
    (hX : ∀ x : X, ∃ a : A, IsUnit (algebraMap A E a) ∧ a • x = 0) :
    Subsingleton (E ⊗[A] X) := by
  refine subsingleton_of_forall_eq 0 fun z => ?_
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul r x =>
      obtain ⟨a, ha, hax⟩ := hX x
      have h1 : a • (r ⊗ₜ[A] x) = 0 := by
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hax, TensorProduct.tmul_zero]
      have h2 : (algebraMap A E a) • (r ⊗ₜ[A] x) = 0 := by rw [algebraMap_smul]; exact h1
      obtain ⟨u, hu⟩ := ha
      have h3 := congrArg (fun y : E ⊗[A] X => ((↑u⁻¹ : E)) • y) h2
      simpa [smul_smul, ← hu] using h3
  | add z w hz hw => rw [hz, hw, add_zero]

/-- **A torsion element of a generically flat module is killed by a power of the inverted
element.** Let `A` be a domain, `f : A` nonzero and `M` an `A`-module whose base change to `A_f`
is flat. Then an element of `M` annihilated by some nonzero element of `A` is annihilated by a
power of `f`.

The base change is flat, hence torsion free, over the domain `A_f`, so the element dies in
`A_f ⊗[A] M`; that base change is the localization of `M` at the powers of `f`, so dying in it
means being killed by a power of `f`. -/
theorem exists_pow_smul_eq_zero_of_flat_baseChange {A M : Type u} [CommRing A] [IsDomain A]
    [AddCommGroup M] [Module A M] {f : A} (hf0 : f ≠ 0)
    (hflat : Module.Flat (Localization.Away f) (Localization.Away f ⊗[A] M))
    {x : M} {c : A} (hc0 : c ≠ 0) (hcx : c • x = 0) :
    ∃ n : ℕ, f ^ n • x = 0 := by
  have hdom : IsDomain (Localization.Away f) :=
    IsLocalization.Away.isDomain (S := Localization.Away f) hf0
  have := hflat
  have hinj : Function.Injective (algebraMap A (Localization.Away f)) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  have hc : algebraMap A (Localization.Away f) c ≠ 0 :=
    fun h => hc0 (hinj (by rw [h, map_zero]))
  have hreg : IsSMulRegular (Localization.Away f ⊗[A] M)
      (algebraMap A (Localization.Away f) c) :=
    Module.IsTorsionFree.isSMulRegular (IsRegular.of_ne_zero hc)
  have hz : (TensorProduct.mk A (Localization.Away f) M 1) x = 0 := by
    refine hreg ?_
    show algebraMap A (Localization.Away f) c •
        ((TensorProduct.mk A (Localization.Away f) M 1) x)
      = algebraMap A (Localization.Away f) c • (0 : Localization.Away f ⊗[A] M)
    rw [smul_zero, algebraMap_smul]
    show c • ((1 : Localization.Away f) ⊗ₜ[A] x) = 0
    rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, hcx, TensorProduct.tmul_zero]
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers f) (f := TensorProduct.mk A (Localization.Away f) M 1)
    (x₁ := x) (x₂ := 0) (by rw [hz, map_zero])
  obtain ⟨n, hn⟩ := s.2
  refine ⟨n, ?_⟩
  have hsn : (f : A) ^ n = (s : A) := hn
  rw [hsn]
  simpa [Submonoid.smul_def] using hs

variable {A B M N : Type u} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
  [Algebra.FiniteType A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

omit [Algebra.FiniteType A B] in
/-- **Every element of the kernel of a generically injective map is torsion.** If `φ : M →ₗ[B] N`
becomes injective after base change to the fraction field of a domain `A`, then each element of
its kernel is annihilated by some nonzero element of `A`.

This is the elementwise half of `Algebra.exists_ne_zero_smul_ker_eq_zero`, and unlike that
statement it needs no Noetherian hypothesis: `F ⊗[A] M` is the localization of `M` at the nonzero
elements of `A`, so an element dying there is killed by one of them. -/
theorem exists_ne_zero_smul_eq_zero_of_mem_ker (φ : M →ₗ[B] N)
    (hgen : Function.Injective (LinearMap.lTensor (FractionRing A) (φ.restrictScalars A)))
    (x : M) (hx : φ x = 0) : ∃ c : A, c ≠ 0 ∧ c • x = 0 := by
  exact exists_ne_zero_smul_eq_zero_of_injective_lTensor_fractionRing (φ.restrictScalars A)
    hgen x hx

/-- **The affine case of Stacks 0573 for an arbitrary map of finite modules, with no Noetherian
hypothesis on the base.** Let `A` be a domain, `B` a finite type `A`-algebra and `φ : M →ₗ[B] N` a
map of finite `B`-modules each element of whose kernel is `A`-torsion. Then there is a nonzero
`f : A` such that `φ` stays injective after base change to *every* `A`-algebra in which `f` is
invertible.

This is `Algebra.exists_ne_zero_forall_injective_lTensor_of_smul_ker_eq_zero` with the hypothesis
that a single element of `A` annihilate the whole kernel — which over a Noetherian domain is
`Algebra.exists_ne_zero_smul_ker_eq_zero` — weakened to the elementwise one, which generic
injectivity supplies over any domain. Generic freeness is applied to `M` as well as to the
cokernel of `φ`: over `A_f` the module `M` is flat, hence torsion free, so every element of the
kernel is killed by a power of `f` and the kernel still has vanishing base change to `A_f`. -/
theorem exists_ne_zero_forall_injective_lTensor_of_forall_exists_smul_eq_zero
    [Module.Finite B M] [Module.Finite B N] (φ : M →ₗ[B] N)
    (htors : ∀ x : M, φ x = 0 → ∃ c : A, c ≠ 0 ∧ c • x = 0) :
    ∃ f : A, f ≠ 0 ∧ ∀ (K : Type u) [CommRing K] [Algebra A K], IsUnit (algebraMap A K f) →
      Function.Injective (LinearMap.lTensor K (φ.restrictScalars A)) := by
  classical
  obtain ⟨b, hb0, hbfree⟩ := Algebra.exists_ne_zero_isFinitePresentationFreeAway
    (R := A) (S := B) (M := N ⧸ LinearMap.range φ)
  obtain ⟨c, hc0, hcfree⟩ := Algebra.exists_ne_zero_isFinitePresentationFreeAway
    (R := A) (S := B) (M := M)
  refine ⟨b * c, mul_ne_zero hb0 hc0, ?_⟩
  have hfreeQ : Algebra.IsFinitePresentationFreeAway A B (N ⧸ LinearMap.range φ) (b * c) :=
    hbfree.of_dvd ⟨c, rfl⟩
  have hfreeM : Algebra.IsFinitePresentationFreeAway A B M (b * c) :=
    hcfree.of_dvd ⟨b, mul_comm b c⟩
  have hflatQ : Module.Flat (Localization.Away (b * c))
      (Localization.Away (b * c) ⊗[A] (N ⧸ LinearMap.range φ)) :=
    flat_baseChange_of_isFinitePresentationFreeAway (b * c) hfreeQ
  have hflatM : Module.Flat (Localization.Away (b * c))
      (Localization.Away (b * c) ⊗[A] M) :=
    flat_baseChange_of_isFinitePresentationFreeAway (b * c) hfreeM
  have hRfunit : IsUnit (algebraMap A (Localization.Away (b * c)) (b * c)) :=
    IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (b * c)) (b * c)
  have hsub : Subsingleton
      (Localization.Away (b * c) ⊗[A] (LinearMap.ker (φ.restrictScalars A))) := by
    refine subsingleton_tensorProduct_of_forall_exists_smul_eq_zero fun x => ?_
    obtain ⟨d, hd0, hdx⟩ := htors (x : M) x.2
    obtain ⟨n, hn⟩ := exists_pow_smul_eq_zero_of_flat_baseChange (M := M)
      (mul_ne_zero hb0 hc0) hflatM hd0 hdx
    exact ⟨(b * c) ^ n, by simpa [map_pow] using hRfunit.pow n, Subtype.ext hn⟩
  intro K _ _ hunit
  exact injective_lTensor_of_flat_quotient_of_subsingleton_ker φ hflatQ hsub K hunit

end TorsionSpreadOut

end Algebra

end
