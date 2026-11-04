module

public import StacksFrontier.RingTheory.DifferentialOperator.Defs

@[expose] public section

/-!
# Localization of a differential operator of finite order

Let `R → S` be a ring map, let `M` and `N` be `S`-modules, let `T ⊆ S` be a multiplicative subset
and let `k : ℕ`. This file proves that a differential operator `D : M → N` of order at most `k`
relative to `R → S` extends uniquely to a differential operator `T⁻¹M → T⁻¹N` of order at most `k`
relative to `R → T⁻¹S`.

Both halves are proved by induction on `k`, in the following form, for a fixed `S'`-module `N'`
(the target `T⁻¹N` of the extension, or any other `S'`-module):

* an operator `F : T⁻¹M → N'` of order at most `k` relative to `R → S'` which vanishes on the image
  of `M` is zero. Indeed for `s ∈ T` the commutator of `F` with `s` again vanishes on the image of
  `M`, hence is zero by induction, so `F` is `s`-homogeneous; and `s • x` lies in the image of `M`
  for a suitable `s`, while `s` acts invertibly on `N'`. This is the uniqueness, which the source
  omits.
* an operator `D : M → N'` of order at most `k` relative to `R → S` extends to an operator
  `T⁻¹M → N'` of order at most `k` relative to `R → S'`. For `k = 0` this is the universal property
  of the localization of a module. For `k + 1` the commutators `L_b : m ↦ D (b • m) - b • D m`,
  `b ∈ S`, have order at most `k`, so extend to operators `E_b` of order at most `k`, uniquely by
  the previous item; the extension `E` of `D` is then defined by `s • E x = D m - E_s x` for any
  `m ∈ M` and `s ∈ T` with `s • x` the image of `m`.

## Main results

* `Stacks.DifferentialOperator.LocalExtension.solution`: the statement of Lemma 0G36, that a
  differential operator of order at most `k` has a unique extension of order at most `k` to the
  localizations.

## Implementation notes

The existence half is proved with an arbitrary `S'`-module `N'` in place of `T⁻¹N`; the operator
that is extended is then `g ∘ D` for the localization map `g : N → T⁻¹N`. This is what makes the
induction go through: the commutators of `D` are extended one at a time with the same target.

The mathematical content of the inductive step is
`Stacks.DifferentialOperator.LocalExtension.smul_sub_smul_comm`: the value `(1/s) • (D m - E_s x)`
intended for the extension at `x` does not depend on the chosen pair `(m, s)` with `s • x = f m`.
It is the source's computation, arranged so that no representative is privileged, and it rests on
the two identities the source records for the extended commutators, `E_{bc} = E_b ∘ c + b • E_c`
(`Stacks.DifferentialOperator.LocalExtension.extension_mul_apply`) and `[E_b, c] = [E_c, b]`
(`Stacks.DifferentialOperator.LocalExtension.commSMul_extension_comm`), both consequences of the
uniqueness half, together with the fact that an operator of finite order kills the kernel of
`M → T⁻¹M` (`Stacks.DifferentialOperator.LocalExtension.apply_eq_of_map_eq`, proved by induction on
the order).

That the extension has order at most `k + 1` is
`Stacks.DifferentialOperator.LocalExtension.order_succ_of_commSMul_algebraMap`: the order of an
operator between modules over `T⁻¹S` may be tested on the image of `S`, because every `t : T⁻¹S`
satisfies `t * u = b` for some `b ∈ S` and `u ∈ T` with `u` acting invertibly. The source instead
appeals to Lemma 0G35 to reduce to the generators `b` and `1 / u` of `T⁻¹S` over `R`; the
computation for a general `t = b / u` is the same one, so Lemma 0G35 is not needed here.

The generalities on the order of a differential operator that the source leaves to the reader are
proved here as private lemmas: the zero operator has every order, operators of order at most `k`
are closed under differences (hence under negation and sums), order at most `k` implies order at
most `k + 1`, the commutator of an operator of order at most `k` has order at most `k`, and pre- or
postcomposing with a linear map preserves the order. The last two are instances of
`Stacks.DifferentialOperator.LocalExtension.order_map`: a construction on operators which commutes
with taking commutators and preserves order at most `0` preserves every order.

## References

* [Stacks 0G36](https://stacks.math.columbia.edu/tag/0G36), Lemma 10.133.12, in the section
  "Finite order differential operators" (Tag 09CH).
-/

@[expose] public section

namespace Stacks.DifferentialOperator.LocalExtension

open LinearMap (commSMul commSMul_apply commSMul_zero_left commSMul_sub_left commSMul_mul_apply
  commSMul_mul commSMul_comm isDifferentialOperatorOfOrderLE_zero_iff
  isDifferentialOperatorOfOrderLE_zero_iff_commSMul_eq_zero
  isDifferentialOperatorOfOrderLE_succ_iff zero_isDifferentialOperatorOfOrderLE
  isDifferentialOperatorOfOrderLE_add isDifferentialOperatorOfOrderLE_sub
  isDifferentialOperatorOfOrderLE_succ isDifferentialOperatorOfOrderLE_commSMul
  isDifferentialOperatorOfOrderLE_postcomp)

/-! ### Generalities on differential operators of finite order -/

section Order

variable {R S M M₂ N N₂ : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommMonoid M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂]
  [AddCommGroup N₂] [Module R N₂] [Module S N₂] [IsScalarTower R S N₂]

/-- A construction on operators which commutes with taking commutators and preserves order at most
`0` preserves order at most `k` for every `k`. This is the shape of every functoriality of the
order below. -/
private lemma order_map {Φ : (M →ₗ[R] N) → (M₂ →ₗ[R] N₂)}
    (h0 : ∀ D : M →ₗ[R] N, D.IsDifferentialOperatorOfOrderLE S 0 →
      (Φ D).IsDifferentialOperatorOfOrderLE S 0)
    (hcomm : ∀ (D : M →ₗ[R] N) (g : S), Φ (commSMul D g) = commSMul (Φ D) g) {k : ℕ}
    {D : M →ₗ[R] N} (hD : D.IsDifferentialOperatorOfOrderLE S k) :
    (Φ D).IsDifferentialOperatorOfOrderLE S k := by
  induction k generalizing D with
  | zero => exact h0 D hD
  | succ k ih =>
    refine isDifferentialOperatorOfOrderLE_succ_iff.mpr fun g => ?_
    rw [← hcomm]
    exact ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hD g)

/-- Postcomposition with the multiplication by `c : S` preserves the order of a differential
operator. -/
private lemma order_postcomp_smul {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) (c : S) :
    (Algebra.lsmul R R N c ∘ₗ D).IsDifferentialOperatorOfOrderLE S k :=
  isDifferentialOperatorOfOrderLE_postcomp (Algebra.lsmul S S N c) hD

/-- Precomposition with the multiplication by `c : S` preserves the order of a differential
operator. -/
private lemma order_precomp_smul {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) (c : S) :
    (D ∘ₗ Algebra.lsmul R R M c).IsDifferentialOperatorOfOrderLE S k :=
  order_map (Φ := fun D => D ∘ₗ Algebra.lsmul R R M c)
    (fun D hD g m => by
      show D (c • g • m) = g • D (c • m)
      rw [smul_comm c g m, isDifferentialOperatorOfOrderLE_zero_iff.mp hD g (c • m)])
    (fun D g => by
      ext m
      show D (g • c • m) - g • D (c • m) = D (c • g • m) - g • D (c • m)
      rw [smul_comm c g m]) hD

end Order

/-! ### Extending an operator along a localization -/

section Localization

variable {R S S' M M' N' : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommMonoid M'] [Module R M'] [Module S M'] [Module S' M']
  [IsScalarTower R S M'] [IsScalarTower S S' M'] [IsScalarTower R S' M']
  [AddCommGroup N'] [Module R N'] [Module S N'] [Module S' N']
  [IsScalarTower R S N'] [IsScalarTower S S' N'] [IsScalarTower R S' N']
  (T : Submonoid S) [IsLocalization T S']

/-! #### An element of `T` acts invertibly on a module over the localization -/

/-- Multiplication by an element of `T` is bijective on a module over the localization `S'`. -/
private lemma smul_bijective {P : Type*} [AddCommMonoid P] [Module S P] [Module S' P]
    [IsScalarTower S S' P] (s : T) : Function.Bijective (fun y : P => (s : S) • y) := by
  have h : (fun y : P => (s : S) • y) = fun y : P => (algebraMap S S' (s : S)) • y := by
    funext y
    rw [IsScalarTower.algebraMap_smul]
  rw [h]
  exact (IsLocalization.map_units S' s).smul_bijective

include S' in
/-- An element of `T` acts surjectively on a module over the localization `S'`. -/
private lemma exists_smul_eq (s : T) (z : N') : ∃ y : N', (s : S) • y = z :=
  (smul_bijective (S' := S') T s).surjective z

include S' in
/-- An element of `T` acts injectively on a module over the localization `S'`. -/
private lemma smul_injective (s : T) : Function.Injective (fun y : N' => (s : S) • y) :=
  (smul_bijective (S' := S') T s).injective

include S' in
/-- An element of `T` acts invertibly on a module over the localization `S'`. -/
private lemma isUnit_algebraMap_end (s : T) :
    IsUnit ((algebraMap S (Module.End S N')) (s : S)) := by
  have h : ⇑((algebraMap S (Module.End S N')) (s : S)) = fun y : N' => (s : S) • y := by
    funext y
    simp [Module.algebraMap_end_apply]
  rw [Module.End.isUnit_iff, h]
  exact smul_bijective (S' := S') T s

/-! #### The order of an operator over the localization -/

omit [Algebra R S] [IsScalarTower R S S'] [IsScalarTower R S M'] [IsScalarTower R S N'] in
/-- The commutator over `S'` with the image of `b : S`, computed with the `S`-action. -/
private lemma commSMul_algebraMap_apply (F : M' →ₗ[R] N') (b : S) (x : M') :
    commSMul F (algebraMap S S' b) x = F (b • x) - b • F x := by
  rw [commSMul_apply, IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul]

omit [IsScalarTower R S S'] in
/-- Multiplication by the image of `c : S` in `S'` is multiplication by `c`. -/
private lemma lsmul_algebraMap_source (c : S) :
    Algebra.lsmul R R M' (algebraMap S S' c) = Algebra.lsmul R R M' c :=
  LinearMap.ext fun x => IsScalarTower.algebraMap_smul S' c x

omit [IsScalarTower R S S'] in
/-- Multiplication by the image of `c : S` in `S'` is multiplication by `c`. -/
private lemma lsmul_algebraMap_target (c : S) :
    Algebra.lsmul R R N' (algebraMap S S' c) = Algebra.lsmul R R N' c :=
  LinearMap.ext fun x => IsScalarTower.algebraMap_smul S' c x

omit [Algebra R S] [IsScalarTower R S S'] [IsScalarTower R S M'] [IsScalarTower R S N'] in
include T in
/-- An `S`-linear map between modules over the localization `S'` is `S'`-linear, i.e. it is a
differential operator of order at most `0` relative to `R → S'`. -/
private lemma order_zero_of_smul {E : M' →ₗ[R] N'}
    (h : ∀ (s : S) (x : M'), E (s • x) = s • E x) :
    E.IsDifferentialOperatorOfOrderLE S' 0 := fun t x =>
  (({ toFun := E, map_add' := map_add E, map_smul' := h } :
    M' →ₗ[S] N').extendScalarsOfIsLocalization T S').map_smul t x

omit [Algebra R S] [IsScalarTower R S S'] [Module S M'] [IsScalarTower R S M'] [Module S N']
  [IsScalarTower S S' N'] [IsScalarTower R S N'] in
include T in
/-- Multiplication by an element of `T` may be cancelled from the right: an operator whose
composition with it has order at most `k` has order at most `k`. -/
private lemma order_of_comp_smul {k : ℕ} {G : M' →ₗ[R] N'} (u : T)
    (h : (G ∘ₗ Algebra.lsmul R R M' (algebraMap S S' (u : S))).IsDifferentialOperatorOfOrderLE
      S' k) :
    G.IsDifferentialOperatorOfOrderLE S' k := by
  obtain ⟨w, hw⟩ := IsLocalization.map_units S' u
  have hG : G = (G ∘ₗ Algebra.lsmul R R M' (algebraMap S S' (u : S)))
      ∘ₗ Algebra.lsmul R R M' ((w⁻¹ : S'ˣ) : S') := by
    ext x
    show G x = G ((algebraMap S S' (u : S)) • (((w⁻¹ : S'ˣ) : S') • x))
    rw [smul_smul, ← hw, w.mul_inv, one_smul]
  rw [hG]
  exact order_precomp_smul h _

omit [Algebra R S] [IsScalarTower R S S'] [Module S M'] [IsScalarTower R S M']
  [IsScalarTower S S' M'] [IsScalarTower R S N'] in
include T in
omit [Module S N'] [IsScalarTower S S' N'] in
/-- **The order may be tested on `S`.** An operator between modules over the localization `S'` all
of whose commutators with elements of the image of `S` have order at most `k` has order at most
`k + 1`: every `t : S'` satisfies `t * u = b` with `b : S` and `u ∈ T`, and multiplication by `u`
is invertible. This replaces the appeal to Lemma 0G35 in the source. -/
private lemma order_succ_of_commSMul_algebraMap {k : ℕ} {F : M' →ₗ[R] N'}
    (h : ∀ b : S, (commSMul F (algebraMap S S' b)).IsDifferentialOperatorOfOrderLE S' k) :
    F.IsDifferentialOperatorOfOrderLE S' (k + 1) := by
  refine isDifferentialOperatorOfOrderLE_succ_iff.mpr fun t => ?_
  obtain ⟨⟨b, u⟩, hbu⟩ := IsLocalization.surj T t
  refine order_of_comp_smul T u ?_
  have hmul := commSMul_mul F t (algebraMap S S' (u : S))
  rw [hbu] at hmul
  have hcomp : commSMul F t ∘ₗ Algebra.lsmul R R M' (algebraMap S S' (u : S))
      = commSMul F (algebraMap S S' b)
        - Algebra.lsmul R R N' t ∘ₗ commSMul F (algebraMap S S' (u : S)) := by
    rw [hmul]
    abel
  rw [hcomp]
  exact isDifferentialOperatorOfOrderLE_sub (h b) (order_postcomp_smul (h (u : S)) t)

/-! #### An operator of finite order kills the kernel of the localization map -/

omit [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R S' N'] in
include S' in
/-- An operator of finite order kills the kernel of the localization map: if `c • p = c • q` for
some `c ∈ T`, then `D p = D q`. -/
private lemma apply_eq_of_smul_eq {k : ℕ} {D : M →ₗ[R] N'}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) (c : T) {p q : M} (h : (c : S) • p = (c : S) • q) :
    D p = D q := by
  induction k generalizing D with
  | zero =>
    refine smul_injective (S' := S') T c ?_
    show (c : S) • D p = (c : S) • D q
    rw [← isDifferentialOperatorOfOrderLE_zero_iff.mp hD,
      ← isDifferentialOperatorOfOrderLE_zero_iff.mp hD, h]
  | succ k ih =>
    have h1 : commSMul D (c : S) p = commSMul D (c : S) q :=
      ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hD _)
    rw [commSMul_apply, commSMul_apply, h] at h1
    exact smul_injective (S' := S') T c (sub_right_injective h1)

omit [Algebra R S'] [IsScalarTower R S S'] [Module R M'] [Module S' M']
  [IsScalarTower R S M'] [IsScalarTower S S' M'] [IsScalarTower R S' M'] in
include S' in
/-- An operator of finite order kills the kernel of the localization map. -/
private lemma apply_eq_of_map_eq (f : M →ₗ[S] M') [IsLocalizedModule T f] {k : ℕ}
    {D : M →ₗ[R] N'} (hD : D.IsDifferentialOperatorOfOrderLE S k) {p q : M} (h : f p = f q) :
    D p = D q := by
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := T) (f := f) h
  exact apply_eq_of_smul_eq (S' := S') T hD c (by simpa [Submonoid.smul_def] using hc)

/-! #### Uniqueness of the extension -/

/-- Every element of the localization is `m` divided by some `s ∈ T`: `s • x = f m`. -/
private lemma exists_smul_eq_map {A P Q : Type*} [CommSemiring A] [AddCommMonoid P] [Module A P]
    [AddCommMonoid Q] [Module A Q] (U : Submonoid A) (f : P →ₗ[A] Q) [IsLocalizedModule U f]
    (x : Q) : ∃ (m : P) (s : U), (s : A) • x = f m := by
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj U f x
  exact ⟨m, s, hs⟩

omit [Algebra R S] [IsScalarTower R S S'] [Module R M] [IsScalarTower R S M]
  [IsScalarTower R S M'] [IsScalarTower R S N'] in
/-- An operator of order at most `k` on the localization which vanishes on the image of `M` is
zero: this is the uniqueness half of Lemma 0G36. -/
private lemma eq_zero_of_comp_eq_zero (f : M →ₗ[S] M') [IsLocalizedModule T f] {k : ℕ}
    {F : M' →ₗ[R] N'} (hF : F.IsDifferentialOperatorOfOrderLE S' k) (hf : ∀ m : M, F (f m) = 0)
    (x : M') : F x = 0 := by
  obtain ⟨m, s, hs⟩ := exists_smul_eq_map T f x
  induction k generalizing F with
  | zero =>
    refine smul_injective (S' := S') T s ?_
    show (s : S) • F x = (s : S) • 0
    rw [smul_zero, ← IsScalarTower.algebraMap_smul S' (s : S) (F x),
      ← isDifferentialOperatorOfOrderLE_zero_iff.mp hF, IsScalarTower.algebraMap_smul, hs, hf m]
  | succ k ih =>
    have h0 : commSMul F (algebraMap S S' (s : S)) x = 0 :=
      ih (isDifferentialOperatorOfOrderLE_succ_iff.mp hF _) fun n => by
        rw [commSMul_algebraMap_apply, ← map_smul f (s : S) n, hf, hf, smul_zero, sub_zero]
    rw [commSMul_algebraMap_apply, hs, hf m, zero_sub, neg_eq_zero] at h0
    exact smul_injective (S' := S') T s (h0.trans (smul_zero _).symm)

omit [Algebra R S] [IsScalarTower R S S'] [Module R M] [IsScalarTower R S M]
  [IsScalarTower R S M'] [IsScalarTower R S N'] in
/-- Two operators of order at most `k` on the localization which agree on the image of `M` are
equal. -/
private lemma ext_of_comp_eq (f : M →ₗ[S] M') [IsLocalizedModule T f] {k : ℕ}
    {F₁ F₂ : M' →ₗ[R] N'} (h₁ : F₁.IsDifferentialOperatorOfOrderLE S' k)
    (h₂ : F₂.IsDifferentialOperatorOfOrderLE S' k) (h : ∀ m : M, F₁ (f m) = F₂ (f m)) :
    F₁ = F₂ := by
  refine LinearMap.ext fun x => sub_eq_zero.mp ?_
  have hx := eq_zero_of_comp_eq_zero T f (isDifferentialOperatorOfOrderLE_sub h₁ h₂)
    (fun m => by rw [LinearMap.sub_apply, h m, sub_self]) x
  rwa [LinearMap.sub_apply] at hx

/-! #### Existence of the extension: the inductive step

Throughout, `D` is an operator of order at most `k + 1`, and `E b` is, for `b : S`, an extension of
the commutator `[D, b]` of order at most `k`; the extension of `D` is built out of the `E b`. Its
value at `x` is characterised by `s • F x = D m - E_s x` for every pair `(m, s)` with
`s • x = f m`, which is the hypothesis `hF` below. -/

section Extension

omit [IsScalarTower R S S'] in
/-- The Leibniz rule passes to the extended commutators: `E_{bc} = E_b ∘ c + b • E_c`, by
uniqueness of extensions. -/
private lemma extension_mul_apply (f : M →ₗ[S] M') [IsLocalizedModule T f] {k : ℕ}
    {D : M →ₗ[R] N'} {E : S → M' →ₗ[R] N'}
    (hEord : ∀ b : S, (E b).IsDifferentialOperatorOfOrderLE S' k)
    (hEext : ∀ (b : S) (m : M), E b (f m) = commSMul D b m) (b c : S) (x : M') :
    E (b * c) x = E b (c • x) + b • E c x := by
  have key : E (b * c) = E b ∘ₗ Algebra.lsmul R R M' c + Algebra.lsmul R R N' b ∘ₗ E c := by
    refine ext_of_comp_eq T f (hEord _) ?_ fun m => ?_
    · rw [← lsmul_algebraMap_source (S' := S') c, ← lsmul_algebraMap_target (S' := S') b]
      exact isDifferentialOperatorOfOrderLE_add (order_precomp_smul (hEord b) _)
        (order_postcomp_smul (hEord c) _)
    · show E (b * c) (f m) = E b (c • f m) + b • E c (f m)
      rw [← map_smul f c m, hEext b (c • m), hEext c m, hEext (b * c) m]
      exact commSMul_mul_apply D b c m
  exact LinearMap.congr_fun key x

omit [IsScalarTower R S S'] [IsScalarTower R S M'] in
/-- The extended commutators commute with each other: `[E_b, c] = [E_c, b]`, by uniqueness of
extensions, since `[[D, b], c] = [[D, c], b]`. -/
private lemma commSMul_extension_comm (f : M →ₗ[S] M') [IsLocalizedModule T f] {k : ℕ}
    {D : M →ₗ[R] N'} {E : S → M' →ₗ[R] N'}
    (hEord : ∀ b : S, (E b).IsDifferentialOperatorOfOrderLE S' k)
    (hEext : ∀ (b : S) (m : M), E b (f m) = commSMul D b m) (b c : S) :
    commSMul (E b) (algebraMap S S' c) = commSMul (E c) (algebraMap S S' b) := by
  refine ext_of_comp_eq T f (isDifferentialOperatorOfOrderLE_commSMul (hEord _) _)
    (isDifferentialOperatorOfOrderLE_commSMul (hEord _) _) fun m => ?_
  rw [commSMul_algebraMap_apply, commSMul_algebraMap_apply, ← map_smul f c m, ← map_smul f b m,
    hEext b (c • m), hEext c (b • m), hEext b m, hEext c m]
  exact LinearMap.congr_fun (commSMul_comm D b c) m

omit [IsScalarTower R S S'] in
/-- **The heart of Lemma 0G36.** The value `(1/s) • (D m - E_s x)` intended for the extension at
`x` does not depend on the representative: for two pairs `(m, s)` and `(n, u)` with
`s • x = f m` and `u • x = f n` one has `u • (D m - E_s x) = s • (D n - E_u x)`. -/
private lemma smul_sub_smul_comm (f : M →ₗ[S] M') [IsLocalizedModule T f] {k : ℕ}
    {D : M →ₗ[R] N'} (hD : D.IsDifferentialOperatorOfOrderLE S (k + 1)) {E : S → M' →ₗ[R] N'}
    (hEord : ∀ b : S, (E b).IsDifferentialOperatorOfOrderLE S' k)
    (hEext : ∀ (b : S) (m : M), E b (f m) = commSMul D b m) {x : M'} {m n : M} {s u : T}
    (hs : (s : S) • x = f m) (hu : (u : S) • x = f n) :
    (u : S) • (D m - E (s : S) x) = (s : S) • (D n - E (u : S) x) := by
  have h3 : D ((u : S) • m) = D ((s : S) • n) :=
    apply_eq_of_map_eq (S' := S') T f hD (by rw [map_smul, map_smul, ← hs, ← hu, smul_comm])
  have key : ∀ (s u : T) (m : M), (u : S) • x = f m →
      (s : S) • (D m - E (u : S) x) = D ((s : S) • m) - E ((s : S) * (u : S)) x := by
    intro s u m hu
    have h : E ((s : S) * (u : S)) x = commSMul D (s : S) m + (s : S) • E (u : S) x := by
      rw [extension_mul_apply T f hEord hEext, hu, hEext (s : S) m]
    rw [h, commSMul_apply, smul_sub]
    abel
  rw [key s u n hu, mul_comm, key u s m hs, h3]

omit [IsScalarTower R S S'] in
/-- The extension has a value at every `x`, characterised by every representative of `x`. -/
private lemma exists_smul_eq_sub (f : M →ₗ[S] M') [IsLocalizedModule T f] {k : ℕ}
    {D : M →ₗ[R] N'} (hD : D.IsDifferentialOperatorOfOrderLE S (k + 1)) {E : S → M' →ₗ[R] N'}
    (hEord : ∀ b : S, (E b).IsDifferentialOperatorOfOrderLE S' k)
    (hEext : ∀ (b : S) (m : M), E b (f m) = commSMul D b m) (x : M') :
    ∃ y : N', ∀ (m : M) (s : T), (s : S) • x = f m → (s : S) • y = D m - E (s : S) x := by
  obtain ⟨n, u, hu⟩ := exists_smul_eq_map T f x
  obtain ⟨y, hy⟩ := exists_smul_eq (S' := S') T u (D n - E (u : S) x)
  refine ⟨y, fun m s hs => smul_injective (S' := S') T u ?_⟩
  show (u : S) • ((s : S) • y) = (u : S) • (D m - E (s : S) x)
  rw [smul_comm (u : S) (s : S) y, hy]
  exact (smul_sub_smul_comm T f hD hEord hEext hs hu).symm

omit [Algebra R S] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R S M] [Module S' M']
  [IsScalarTower R S M'] [IsScalarTower S S' M'] [IsScalarTower R S' M'] [IsScalarTower R S N']
  [IsScalarTower R S' N'] in
include S' in
/-- A function with the defining property of the extension is additive. -/
private lemma map_add_of_spec (f : M →ₗ[S] M') [IsLocalizedModule T f] {D : M →ₗ[R] N'}
    {E : S → M' →ₗ[R] N'} {F : M' → N'}
    (hF : ∀ (x : M') (m : M) (s : T), (s : S) • x = f m → (s : S) • F x = D m - E (s : S) x)
    (x y : M') : F (x + y) = F x + F y := by
  obtain ⟨m, s, hs⟩ := exists_smul_eq_map T f x
  obtain ⟨n, u, hu⟩ := exists_smul_eq_map T f y
  have hx : ((s * u : T) : S) • x = f ((u : S) • m) := by
    rw [Submonoid.coe_mul, mul_comm, mul_smul, hs, map_smul]
  have hy : ((s * u : T) : S) • y = f ((s : S) • n) := by
    rw [Submonoid.coe_mul, mul_smul, hu, map_smul]
  refine smul_injective (S' := S') T (s * u) ?_
  show ((s * u : T) : S) • F (x + y) = ((s * u : T) : S) • (F x + F y)
  rw [hF (x + y) _ (s * u) (by rw [smul_add, hx, hy, map_add]), smul_add, hF x _ (s * u) hx,
    hF y _ (s * u) hy]
  simp only [map_add]
  abel

omit [Algebra R S'] [IsScalarTower R S S'] [Module S' M'] [IsScalarTower S S' M']
  [IsScalarTower R S' M'] [IsScalarTower R S' N'] in
include S' in
/-- A function with the defining property of the extension is `R`-homogeneous. -/
private lemma map_smul_of_spec (f : M →ₗ[S] M') [IsLocalizedModule T f] {D : M →ₗ[R] N'}
    {E : S → M' →ₗ[R] N'} {F : M' → N'}
    (hF : ∀ (x : M') (m : M) (s : T), (s : S) • x = f m → (s : S) • F x = D m - E (s : S) x)
    (r : R) (x : M') : F (r • x) = r • F x := by
  obtain ⟨m, s, hs⟩ := exists_smul_eq_map T f x
  have hrx : (s : S) • (r • x) = f (r • m) := by rw [smul_comm, hs, f.map_smul_of_tower]
  refine smul_injective (S' := S') T s ?_
  show (s : S) • F (r • x) = (s : S) • (r • F x)
  rw [hF (r • x) (r • m) s hrx, smul_comm (s : S) r (F x), hF x m s hs, map_smul, map_smul,
    smul_sub]

omit [CommSemiring S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S'] [Module S' M']
  [IsScalarTower R S M'] [IsScalarTower S S' M'] [IsScalarTower R S' M'] [Module S' N']
  [IsScalarTower S S' N'] [IsScalarTower R S' N'] in
/-- A function with the defining property of the extension extends `D`, since `E 1 = 0`. -/
private lemma apply_map_of_spec (f : M →ₗ[S] M') [IsLocalizedModule T f] {D : M →ₗ[R] N'}
    {E : S → M' →ₗ[R] N'} (hEext : ∀ (b : S) (m : M), E b (f m) = commSMul D b m) {F : M' → N'}
    (hF : ∀ (x : M') (m : M) (s : T), (s : S) • x = f m → (s : S) • F x = D m - E (s : S) x)
    (m : M) : F (f m) = D m := by
  have h := hF (f m) m 1 (by rw [OneMemClass.coe_one, one_smul])
  rwa [OneMemClass.coe_one, one_smul, hEext (1 : S) m, commSMul_apply, one_smul, one_smul,
    sub_self, sub_zero] at h

omit [IsScalarTower R S S'] [IsScalarTower R S M'] in
/-- The commutator of the extension with `b : S` is the chosen extension `E b` of the commutator of
`D` with `b`. This is the second half of the source's computation. -/
private lemma sub_smul_eq_of_spec (f : M →ₗ[S] M') [IsLocalizedModule T f] {k : ℕ}
    {D : M →ₗ[R] N'} {E : S → M' →ₗ[R] N'}
    (hEord : ∀ b : S, (E b).IsDifferentialOperatorOfOrderLE S' k)
    (hEext : ∀ (b : S) (m : M), E b (f m) = commSMul D b m) {F : M' → N'}
    (hF : ∀ (x : M') (m : M) (s : T), (s : S) • x = f m → (s : S) • F x = D m - E (s : S) x)
    (b : S) (x : M') : F (b • x) - b • F x = E b x := by
  obtain ⟨m, s, hs⟩ := exists_smul_eq_map T f x
  have e1 : (s : S) • F (b • x) = D (b • m) - E (s : S) (b • x) :=
    hF _ _ s (by rw [smul_comm, hs, map_smul])
  have e2 : (s : S) • F x = D m - E (s : S) x := hF _ _ s hs
  have e3 : E (s : S) (b • x) - b • E (s : S) x = E b ((s : S) • x) - (s : S) • E b x := by
    have h := LinearMap.congr_fun (commSMul_extension_comm T f hEord hEext (s : S) b) x
    rwa [commSMul_algebraMap_apply, commSMul_algebraMap_apply] at h
  have e4 : E b ((s : S) • x) = D (b • m) - b • D m := by
    rw [hs, hEext b m, commSMul_apply]
  refine smul_injective (S' := S') T s ?_
  show (s : S) • (F (b • x) - b • F x) = (s : S) • E b x
  rw [smul_sub, e1, smul_comm (s : S) b (F x), e2, smul_sub,
    show D (b • m) - E (s : S) (b • x) - (b • D m - b • E (s : S) x)
      = D (b • m) - b • D m - (E (s : S) (b • x) - b • E (s : S) x) by abel, e3, e4]
  abel

end Extension

omit [IsScalarTower R S S'] in
/-- **Existence in Lemma 0G36.** An operator `D : M → N'` of order at most `k` relative to `R → S`,
with values in a module over the localization `S'`, extends to an operator `T⁻¹M → N'` of order at
most `k` relative to `R → S'`. -/
private lemma exists_extension (f : M →ₗ[S] M') [IsLocalizedModule T f] :
    ∀ (k : ℕ) (D : M →ₗ[R] N'), D.IsDifferentialOperatorOfOrderLE S k →
      ∃ E : M' →ₗ[R] N', E.IsDifferentialOperatorOfOrderLE S' k ∧ ∀ m : M, E (f m) = D m := by
  intro k
  induction k with
  | zero =>
    intro D hD
    let DS : M →ₗ[S] N' :=
      { toFun := D, map_add' := map_add D,
        map_smul' := isDifferentialOperatorOfOrderLE_zero_iff.mp hD }
    exact ⟨(IsLocalizedModule.lift T f DS (isUnit_algebraMap_end (S' := S') T)).restrictScalars R,
      order_zero_of_smul T (fun s x => LinearMap.map_smul _ s x),
      fun m => LinearMap.congr_fun (IsLocalizedModule.lift_comp T f DS _) m⟩
  | succ k ih =>
    intro D hD
    choose E hEord hEext using fun b : S =>
      ih (commSMul D b) (isDifferentialOperatorOfOrderLE_succ_iff.mp hD b)
    choose F hF using exists_smul_eq_sub T f hD hEord hEext
    let G : M' →ₗ[R] N' :=
      { toFun := F, map_add' := map_add_of_spec (S' := S') T f hF,
        map_smul' := map_smul_of_spec (S' := S') T f hF }
    have hG : ∀ b : S, commSMul G (algebraMap S S' b) = E b := fun b =>
      LinearMap.ext fun x => (commSMul_algebraMap_apply (S' := S') G b x).trans
        (sub_smul_eq_of_spec T f hEord hEext hF b x)
    exact ⟨G, order_succ_of_commSMul_algebraMap T fun b => hG b ▸ hEord b,
      apply_map_of_spec T f hEext hF⟩

end Localization

/-! ### Lemma 0G36 -/

variable {R S S' M N M' N' : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommMonoid M'] [Module R M'] [Module S M'] [Module S' M']
  [IsScalarTower R S M'] [IsScalarTower S S' M'] [IsScalarTower R S' M']
  [AddCommGroup N'] [Module R N'] [Module S N'] [Module S' N']
  [IsScalarTower R S N'] [IsScalarTower S S' N'] [IsScalarTower R S' N']

omit [IsScalarTower R S S'] in
/-- **Lemma 0G36.** A differential operator `D : M → N` of order at most `k` relative to `R → S`
has a unique extension `E : T⁻¹M → T⁻¹N` of order at most `k` relative to `R → T⁻¹S`, that is,
a unique such `E` with `E ∘ f = g ∘ D` for the localization maps `f : M → T⁻¹M` and
`g : N → T⁻¹N`. -/
public theorem solution {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) (T : Submonoid S) [IsLocalization T S']
    (f : M →ₗ[S] M') (g : N →ₗ[S] N') [IsLocalizedModule T f] [IsLocalizedModule T g] :
    ∃! E : M' →ₗ[R] N', E.IsDifferentialOperatorOfOrderLE S' k ∧
      E ∘ₗ f.restrictScalars R = g.restrictScalars R ∘ₗ D := by
  obtain ⟨E, hEord, hEext⟩ :=
    exists_extension (S' := S') T f k (g.restrictScalars R ∘ₗ D)
      (isDifferentialOperatorOfOrderLE_postcomp g hD)
  refine ⟨E, ⟨hEord, LinearMap.ext hEext⟩, ?_⟩
  rintro F ⟨hFord, hFext⟩
  exact ext_of_comp_eq T f hFord hEord fun m =>
    (LinearMap.congr_fun hFext m).trans (hEext m).symm

end Stacks.DifferentialOperator.LocalExtension

end

/-!
# Localization of a differential operator of finite order

Let `R → S` be a ring map, let `M` and `N` be `S`-modules, let `T ⊆ S` be a multiplicative
subset and let `k : ℕ`. A differential operator `D : M → N` of order at most `k` relative to
`R → S` extends uniquely to a differential operator `T⁻¹M → T⁻¹N` of order at most `k` relative
to `R → T⁻¹S`: there is exactly one `R`-linear `E : T⁻¹M → T⁻¹N` which is a differential
operator of order at most `k` and satisfies `E ∘ f = g ∘ D`, where `f : M → T⁻¹M` and
`g : N → T⁻¹N` are the localization maps.

At `k = 0` this is the functoriality of localization for `S`-linear maps, and the general case is
proved from it by induction on `k`, extending the commutators `m ↦ D (g • m) - g • D m` first
and building `E (m / g) = (1 / g) (D m - E_g (m / g))` out of them.

## Main results

* `LinearMap.IsDifferentialOperatorOfOrderLE.existsUnique_extension`: a differential operator of
  order at most `k` has a unique extension to the localizations which is again a differential
  operator of order at most `k`.

## Implementation notes

The localizations are abstract rather than constructed: `T⁻¹S` is any `S`-algebra `S'` with
`IsLocalization T S'`, and `T⁻¹M`, `T⁻¹N` are any `S`-modules `M'`, `N'` together with maps
`f : M →ₗ[S] M'`, `g : N →ₗ[S] N'` satisfying `IsLocalizedModule T f`, `IsLocalizedModule T g`.
Applying the lemma to `Localization T` and `LocalizedModule T M` recovers the source's statement,
and the abstract form is what a dependent needs when the localizations arrive as sections of a
sheaf on a standard affine open (Morphisms, Lemma 0G44).

The order of the extension is measured relative to `R → S'`, not relative to `R → S`, as in the
source: its proof verifies the order of `E` by checking, via Lemma 0G35, the commutators of `E`
with the algebra generators `b` and `1 / g'` of `S'` over `R`. Accordingly `M'` and `N'` carry
`S'`-module structures compatible with their `S`-module structures. The scalar towers
`IsScalarTower R S M'` and `IsScalarTower R S' M'` are both assumed, although either can be
deduced from the other together with `IsScalarTower R S S'` and `IsScalarTower S S' M'`; both
spellings of the `R`-action occur in the statement, the first in `f.restrictScalars R` and the
second in the order-`0` clause of the differential operator predicate.

Uniqueness is asserted inside the class of differential operators of order at most `k`, which is
what the source claims: an `R`-linear map on `T⁻¹M` need not be determined by its restriction
along `f` in general. Only `N` and `N'` are required to be groups, since only values of the
operators are subtracted, and only `CommSemiring` is required of `R`, `S` and `S'`.

Faithfulness. (1) No dead hypothesis: `hD` gives the operator that is extended, the localization
hypotheses pin `S'`, `M'`, `N'` as `T⁻¹S`, `T⁻¹M`, `T⁻¹N` (without them the statement is false:
for `M' = N' = N ≠ 0` and `f = g = 0` every operator of order at most `k` satisfies the equation,
so uniqueness fails), the towers pin the `R`-actions to the ones along `R → S`, and `k` occurs in
both `hD` and the conclusion. (2) The scalars and base are the source's: `D` is a differential
operator relative to the source's ring map `R → S` and `E` one relative to `R → T⁻¹S`, both
`R`-linear for the same `R`, with the actions tied together by the scalar towers. (3) The
canonical maps are pinned, not merely asserted to exist: the extension is characterised by
`E ∘ₗ f.restrictScalars R = g.restrictScalars R ∘ₗ D` for the localization maps `f` and `g`
themselves, which is the sense in which `E` extends `D`. (4) The instantiation is not degenerate:
every instance and localization hypothesis is satisfied by `S' = Localization T`,
`M' = LocalizedModule T M`, `N' = LocalizedModule T N` for an arbitrary ring map `R → S` and
submonoid `T`, and the operators in question are not all `S`-linear — for `R = ℚ` and
`S = M = N = ℚ[X]` the derivative `d/dX` has order at most `1` and not `0`.

## References

* [Stacks 0G36](https://stacks.math.columbia.edu/tag/0G36), Lemma 10.133.7, in the section
  "Finite order differential operators" (Tag 09CH).
-/

@[expose] public section

namespace LinearMap.IsDifferentialOperatorOfOrderLE

variable {R S S' M N M' N' : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [CommSemiring S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommMonoid M'] [Module R M'] [Module S M'] [Module S' M']
  [IsScalarTower R S M'] [IsScalarTower S S' M'] [IsScalarTower R S' M']
  [AddCommGroup N'] [Module R N'] [Module S N'] [Module S' N']
  [IsScalarTower R S N'] [IsScalarTower S S' N'] [IsScalarTower R S' N']

omit [IsScalarTower R S S'] in
/-- **Stacks 0G36.** Let `R → S` be a ring map, let `M` and `N` be `S`-modules and let `T ⊆ S` be
a multiplicative subset. A differential operator `D : M → N` of order at most `k` relative to
`R → S` extends uniquely to a differential operator of order at most `k` relative to
`R → T⁻¹S` on the localizations: there is a unique `R`-linear map `E : T⁻¹M → T⁻¹N` which is a
differential operator of order at most `k` and satisfies `E ∘ f = g ∘ D` for the localization
maps `f : M → T⁻¹M` and `g : N → T⁻¹N`. -/
@[stacks 0G36 "Stated for abstract localizations `IsLocalization T S'`, `IsLocalizedModule T f`,
`IsLocalizedModule T g` rather than for `Localization T` and `LocalizedModule T`. The order of
the extension is relative to `R → S'`, as in the source's proof. `extends` is spelled as the
equation `E ∘ₗ f.restrictScalars R = g.restrictScalars R ∘ₗ D`, so the source's canonical maps
are pinned; the case `k = 0` is `IsLocalizedModule.lift`. See the module docstring."]
public theorem existsUnique_extension {k : ℕ} {D : M →ₗ[R] N}
    (hD : D.IsDifferentialOperatorOfOrderLE S k) (T : Submonoid S) [IsLocalization T S']
    (f : M →ₗ[S] M') (g : N →ₗ[S] N') [IsLocalizedModule T f] [IsLocalizedModule T g] :
    ∃! E : M' →ₗ[R] N', E.IsDifferentialOperatorOfOrderLE S' k ∧
      E ∘ₗ f.restrictScalars R = g.restrictScalars R ∘ₗ D :=
  Stacks.DifferentialOperator.LocalExtension.solution hD T f g

end LinearMap.IsDifferentialOperatorOfOrderLE

end
