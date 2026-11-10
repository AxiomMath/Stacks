module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.TwoTermExtBoundCanDual

/-!
# Tag 0GAD at the source's levels: the dotted arrow through `H¹` of `(p^*M)^∨`

[Stacks, Tag 0GAD](https://stacks.math.columbia.edu/tag/0GAD) asserts that for a two-term
object `K` of `D(A/Iⁿ)` whose `Ext¹` into finite modules is killed by `I^c`, the map
`Ext¹(K, Iⁿ/I^{2n}) → Ext¹(K, I^{n-(1+d)c}/I^{2n-2(1+d)c})` vanishes. The source's argument
for `d > 0` (through Tag 0GAC) does not reach this target: it reaches only
`I^{n-(2+d)c}/I^{2n-(2+d)c}`, which maps neither to nor from the printed module when `d ≥ 1`;
see `CanDualSituation.ext_one_powQuot_map_eq_zero`. Its argument for `d = 0` does reach it,
and this file runs that argument for every `d`.

Represent `K` by `K⁻¹ --u--> K⁰` with `K⁰` finite free and `a·id = h_a ∘ u` for `a ∈ I^c`, and
let `M₀ = coker(u)`, again an `(A, n, c)`-module (`isANCModule_cokernel`). A class of
`Ext¹(K, Iⁿ/I^{2n})` is a homomorphism `φ : K⁻¹ → Iⁿ/I^{2n}`, and it dies in
`Ext¹(K, I^f/I^{f+n})` once `φ` twisted down to level `f` extends along `u`. On the blowup this
is a lifting problem along the dual `D = (p^*u)^∨ : (p^*K⁰)^∨ → (p^*K⁻¹)^∨`, whose kernel is
`(p^*M₀)^∨` and whose cokernel is killed by `I^c` (since `D ∘ (p^*h_a)^∨ = a`):

* the section `σ ∈ Γ((p^*K⁻¹)^∨(n))` attached to `φ`, twisted down by `c`, lies in the
  sections of the image of `D`, because the cokernel is supported on `Y_c` (Tag 0GA9);
* its obstruction to lifting to `Γ((p^*K⁰)^∨(n - c))` lies in `H¹(X, (p^*M₀)^∨(n - c))`;
* the canonical map `H¹(X, (p^*M₀)^∨(q)) → H¹(X, (p^*M₀)^∨(q - dc))` is zero for `q - dc ≥ q₀`
  (`DottedArrowSituation.Hdual₁tr_eq_zero`). For `d = 0` its source vanishes, which is the
  source's own `d = 0` argument; for `d ≥ 1` this is Tag 0GAA for `p^*(M₀^∨)` transported
  along `can : p^*(M₀^∨) → (p^*M₀)^∨`, whose kernel and cokernel are supported on `Y_c`
  (Remark 0GAB): twisting `(p^*M₀)^∨` down by `c` factors through the image of `can`, twisting
  the image down by `c` factors through `p^*(M₀^∨)`, and for `d = 1` the image already has no
  `H¹` because `H²` of the kernel vanishes.

So the twist of `σ` to level `f = n - (1 + d)c` lifts, the lift is a homomorphism
`ψ : K⁰ → I^f/I^{f+n}` with `ψ ∘ u = φ` at level `f`, and the class dies in
`Ext¹(K, I^f/I^{f+n})`, hence in its quotient `Ext¹(K, I^f/I^{2f})`, the printed target.

## Main definitions

* `Stacks.LocalCohomology.UniformityIII.DottedArrowSituation`: a `CanDualSituation` together
  with the first cohomology of the twists of `(p^*M)^∨` and of the image of `can`, the second
  cohomology of the kernel of `can`, and the image and cokernel of the dual of a map of
  `(A, n, c)`-modules with its connecting map.
* `Stacks.LocalCohomology.UniformityIII.powQuotObjOfLe`: `I^q/I^{q+m}` as an `A/Iⁿ`-module for
  `m ≤ n`, the coefficient module `I^{n-(1+d)c}/I^{2n-2(1+d)c}` of the tag.

## Main results

* `DottedArrowSituation.Hdual₁tr_eq_zero`: `H¹((p^*M)^∨(q)) → H¹((p^*M)^∨(q - dc))` is zero.
* `DottedArrowSituation.exists_comp_resMap_eq`: the dotted arrow at level `n - (1 + d)c`.
* `DottedArrowSituation.ext_one_powQuot_map_eq_zero`: the conclusion of Tag 0GAD at the
  printed target, over a `DottedArrowSituation`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Stacks.LocalCohomology.UniformityIII

section Coefficients

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- `Iⁿ` annihilates `I^q/I^{q+m}` when `m ≤ n`. -/
theorem isTorsionBySet_powQuot_of_le (q : ℕ) {m n : ℕ} (hm : m ≤ n) :
    Module.IsTorsionBySet A (powQuot I q m) ((I ^ n : Ideal A) : Set A) := by
  intro x a
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    change (Submodule.Quotient.mk ((a : A) • y) : powQuot I q m) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype, SetLike.val_smul,
      smul_eq_mul]
    have h : (a : A) * (y : A) ∈ I ^ n * I ^ q := Ideal.mul_mem_mul a.2 y.2
    rw [← pow_add] at h
    exact Ideal.pow_le_pow_right (by omega) h

/-- The subquotient `I^q/I^{q+m}` of `A` as an object of the category of `A/Iⁿ`-modules, for
`m ≤ n`. For `q = n - (1 + d)c` and `m = q` this is the module `I^{n-(1+d)c}/I^{2n-2(1+d)c}`
of Tag 0GAD. -/
noncomputable def powQuotObjOfLe (q : ℕ) {m n : ℕ} (hm : m ≤ n) : ModuleCat.{u} (A ⧸ I ^ n) :=
  letI := (isTorsionBySet_powQuot_of_le I q hm).module
  ModuleCat.of (A ⧸ I ^ n) (powQuot I q m)

/-- The canonical map `I^q/I^{q+m} → I^{q'}/I^{q'+m'}` for `q' ≤ q` and `q' + m' ≤ q + m`,
induced by the inclusion `I^q ⊆ I^{q'}`. -/
def powQuotMap {q m q' m' : ℕ} (h : q' ≤ q) (h' : q' + m' ≤ q + m) :
    powQuot I q m →ₗ[A] powQuot I q' m' :=
  Submodule.mapQ _ _ (Submodule.inclusion (Ideal.pow_le_pow_right h))
    (by
      rintro ⟨x, hx⟩ hmem
      simp only [powSub, Submodule.mem_comap, Submodule.coe_subtype] at hmem ⊢
      exact Ideal.pow_le_pow_right h' hmem)

/-- `powQuotMap` sends the class of `x ∈ I^q` to the class of `x` in `I^{q'}/I^{q'+m'}`. -/
@[simp] theorem powQuotMap_mk {q m q' m' : ℕ} (h : q' ≤ q) (h' : q' + m' ≤ q + m)
    (x : (I ^ q : Ideal A)) :
    powQuotMap I h h' (Submodule.Quotient.mk x : powQuot I q m) =
      Submodule.Quotient.mk (Submodule.inclusion (Ideal.pow_le_pow_right h) x) := rfl

/-- The canonical map `I^q/I^{q+n} ⟶ I^{q'}/I^{q'+m'}` of `A/Iⁿ`-modules, for `q' ≤ q`,
`q' + m' ≤ q + n` and `m' ≤ n`. -/
noncomputable def powQuotToOfLe {q n q' m' : ℕ} (h : q' ≤ q) (h' : q' + m' ≤ q + n)
    (hm' : m' ≤ n) : powQuotObj I q n ⟶ powQuotObjOfLe I q' hm' :=
  letI := (isTorsionBySet_powQuot_of_le I q' hm').module
  ModuleCat.ofHom
    { toFun := powQuotMap I h h'
      map_add' := (powQuotMap I h h').map_add
      map_smul' := fun r x => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact (powQuotMap I h h').map_smul a x }

/-- The underlying linear map of `powQuotToOfLe` is `powQuotMap`. -/
@[simp] theorem powQuotToOfLe_apply {q n q' m' : ℕ} (h : q' ≤ q) (h' : q' + m' ≤ q + n)
    (hm' : m' ≤ n) (x : powQuot I q n) :
    (powQuotToOfLe I h h' hm').hom x = powQuotMap I h h' x := rfl

end Coefficients

section ANC

variable {A : Type u} [CommRing A] {I : Ideal A} {n c : ℕ}

/-- A finite projective `A/Iⁿ`-module is an `(A, n, c)`-module: multiplication by any element
factors through the module itself. -/
theorem isANCModule_of_projective (P : ModuleCat.{u} (A ⧸ I ^ n))
    [Module.Finite (A ⧸ I ^ n) P] [Module.Projective (A ⧸ I ^ n) P] : IsANCModule I n c P :=
  ⟨inferInstance, fun a _ =>
    ⟨P, inferInstance, inferInstance, inferInstance, LinearMap.lsmul _ P a, LinearMap.id,
      rfl⟩⟩

/-- The cokernel of a map `u : M ⟶ P` of `A/Iⁿ`-modules with `P` finite projective, such that
multiplication by every element of `I^c/Iⁿ` on `M` factors as `h ∘ u`, is an
`(A, n, c)`-module: multiplication by `a` on `P` minus `u ∘ h_a` kills the image of `u`, so it
descends to the cokernel, and composed with the projection it is multiplication by `a`. -/
theorem isANCModule_cokernel {M P : ModuleCat.{u} (A ⧸ I ^ n)} (u : M ⟶ P)
    [Module.Finite (A ⧸ I ^ n) P] [Module.Projective (A ⧸ I ^ n) P]
    (hfac : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∃ h : P ⟶ M, u ≫ h = a • 𝟙 M) :
    IsANCModule I n c (ModuleCat.of (A ⧸ I ^ n) (P ⧸ LinearMap.range u.hom)) := by
  refine ⟨inferInstance, fun a ha => ?_⟩
  obtain ⟨h, hh⟩ := hfac a ha
  have hpt : ∀ z : M, h.hom (u.hom z) = a • z := fun z => by
    have hz : (u ≫ h).hom z = (a • 𝟙 M).hom z := by rw [hh]
    simpa using hz
  let β : P →ₗ[A ⧸ I ^ n] P := a • LinearMap.id - u.hom ∘ₗ h.hom
  have hβ : LinearMap.range u.hom ≤ LinearMap.ker β := by
    rintro _ ⟨z, rfl⟩
    simp [β, hpt]
  refine ⟨P, inferInstance, inferInstance, inferInstance,
    (LinearMap.range u.hom).liftQ β hβ, (LinearMap.range u.hom).mkQ, ?_⟩
  ext y
  simp only [LinearMap.lsmul_apply, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, Submodule.liftQ_apply, β, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
  rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self u.hom (h.hom y)), sub_zero]

end ANC

/-- The data and the standing hypotheses of the dotted-arrow argument of Stacks Tag 0GAD: a
`CanDualSituation` together with

* `Hdual₁ M q = H¹(X, (p^*M)^∨(q))`, `Himg₁ M q = H¹(X, im(can)(q))` and
  `Hker₂ M q = H²(X, ker(can)(q))` for the `can : p^*(M^∨) → (p^*M)^∨` of Remark 0GAB, with
  the maps induced by the canonical twisting maps and by the factorizations Tag 0GA9 gives for
  them: `(p^*M)^∨(q) → (p^*M)^∨(q - c)` factors through `im(can)(q - c)` since `coker(can)` is
  supported on `Y_c`, and `im(can)(q) → im(can)(q - c)` factors through `p^*(M^∨)(q - c)` since
  `ker(can)` is;
* for a map `u : M ⟶ M'` of `(A, n, c)`-modules, the sections of the twists of the image and of
  the cokernel of the dual `D_u = (p^*u)^∨ : (p^*M')^∨ → (p^*M)^∨`, and, when
  `M → M' → M'' → 0` is exact, the connecting map into `H¹(X, (p^*M'')^∨(q))` of the short exact
  sequence `0 → (p^*M'')^∨ → (p^*M')^∨ → im(D_u) → 0`;
* the vanishing of `Hⁱ(X, ℱ)` for `i > d` at `ℱ = (p^*M)^∨(q)` and `ℱ = ker(can)(q)`, and the
  vanishing of the twisting map on the cokernel of `D_u` when multiplication by every `a ∈ I^c`
  factors through `u` (Tag 0GA9, the cokernel then being killed by `I^c`).

Like every Situation in this section the cohomology enters as data; the structure carries no
statement of Tag 0GAA or of Tag 0GAD. -/
structure DottedArrowSituation (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (n c : ℕ) extends CanDualSituation A I n c where
  /-- `Hdual₁ M q` is `H¹(X, (p^*M)^∨(q))`. -/
  Hdual₁ : ANCModule I n c → ℕ → ModuleCat.{u} A
  /-- The map `H¹(X, (p^*M)^∨(q)) → H¹(X, (p^*M)^∨(q'))` for `q' ≤ q`. -/
  Hdual₁tr : ∀ (M : ANCModule I n c) (q q' : ℕ), q' ≤ q → Hdual₁ M q →ₗ[A] Hdual₁ M q'
  /-- The twisting maps on `H¹(X, (p^*M)^∨(-))` compose. -/
  Hdual₁tr_trans : ∀ (M : ANCModule I n c) (q q' q'' : ℕ) (h : q' ≤ q) (h' : q'' ≤ q')
      (x : Hdual₁ M q), Hdual₁tr M q' q'' h' (Hdual₁tr M q q' h x) = Hdual₁tr M q q'' (h'.trans h) x
  /-- `Himg₁ M q` is `H¹(X, im(can)(q))`. -/
  Himg₁ : ANCModule I n c → ℕ → ModuleCat.{u} A
  /-- The map `H¹(X, im(can)(q)) → H¹(X, im(can)(q'))` for `q' ≤ q`. -/
  Himg₁tr : ∀ (M : ANCModule I n c) (q q' : ℕ), q' ≤ q → Himg₁ M q →ₗ[A] Himg₁ M q'
  /-- The twisting maps on `H¹(X, im(can)(-))` compose. -/
  Himg₁tr_trans : ∀ (M : ANCModule I n c) (q q' q'' : ℕ) (h : q' ≤ q) (h' : q'' ≤ q')
      (x : Himg₁ M q), Himg₁tr M q' q'' h' (Himg₁tr M q q' h x) = Himg₁tr M q q'' (h'.trans h) x
  /-- `Hker₂ M q` is `H²(X, ker(can)(q))`. -/
  Hker₂ : ANCModule I n c → ℕ → ModuleCat.{u} A
  /-- `H¹(X, im(can)(q)) → H¹(X, (p^*M)^∨(q))`, induced by the inclusion of the image. -/
  img₁ToDual₁ : ∀ (M : ANCModule I n c) (q : ℕ), Himg₁ M q →ₗ[A] Hdual₁ M q
  /-- The inclusion of the image is natural in the twist. -/
  img₁ToDual₁_Himg₁tr : ∀ (M : ANCModule I n c) (q q' : ℕ) (h : q' ≤ q) (x : Himg₁ M q),
    img₁ToDual₁ M q' (Himg₁tr M q q' h x) = Hdual₁tr M q q' h (img₁ToDual₁ M q x)
  /-- `H¹(X, (p^*M)^∨(q)) → H¹(X, im(can)(q - c))`, induced by the factorization of
  `(p^*M)^∨(q) → (p^*M)^∨(q - c)` through `im(can)(q - c)`. -/
  dual₁ToImg₁ : ∀ (M : ANCModule I n c) (q e : ℕ), e + c = q → Hdual₁ M q →ₗ[A] Himg₁ M e
  /-- The factorization does factor the twisting map. -/
  img₁ToDual₁_dual₁ToImg₁ : ∀ (M : ANCModule I n c) (q e : ℕ) (he : e + c = q)
      (x : Hdual₁ M q),
    img₁ToDual₁ M e (dual₁ToImg₁ M q e he x) = Hdual₁tr M q e (Nat.le.intro he) x
  /-- `H¹(X, p^*(M^∨)(q)) → H¹(X, im(can)(q))`, induced by `can` onto its image. -/
  canToImg₁ : ∀ (M : ANCModule I n c) (q : ℕ),
    toModuleSituation.H M.dual 1 (q : ℤ) →ₗ[A] Himg₁ M q
  /-- `can` onto its image is natural in the twist. -/
  canToImg₁_Htr : ∀ (M : ANCModule I n c) (q q' : ℕ) (h : q' ≤ q) (h' : (q' : ℤ) ≤ (q : ℤ))
      (x : toModuleSituation.H M.dual 1 (q : ℤ)),
    Himg₁tr M q q' h (canToImg₁ M q x) =
      canToImg₁ M q' (toTwistedModuleSituation.Htr M.dual 1 (q : ℤ) (q' : ℤ) h' x)
  /-- `H¹(X, im(can)(q)) → H¹(X, p^*(M^∨)(q - c))`, induced by the factorization of
  `im(can)(q) → im(can)(q - c)` through `p^*(M^∨)(q - c)`. -/
  img₁ToPullback₁ : ∀ (M : ANCModule I n c) (q e : ℕ), e + c = q →
    Himg₁ M q →ₗ[A] toModuleSituation.H M.dual 1 (e : ℤ)
  /-- The factorization does factor the twisting map. -/
  canToImg₁_img₁ToPullback₁ : ∀ (M : ANCModule I n c) (q e : ℕ) (he : e + c = q)
      (x : Himg₁ M q),
    canToImg₁ M e (img₁ToPullback₁ M q e he x) = Himg₁tr M q e (Nat.le.intro he) x
  /-- The connecting map `H¹(X, im(can)(q)) → H²(X, ker(can)(q))` of
  `0 → ker(can) → p^*(M^∨) → im(can) → 0`. -/
  canToImg₁δ : ∀ (M : ANCModule I n c) (q : ℕ), Himg₁ M q →ₗ[A] Hker₂ M q
  /-- Exactness of that long exact sequence at `H¹(X, im(can)(q))`. -/
  exact_canToImg₁ : ∀ (M : ANCModule I n c) (q : ℕ),
    Function.Exact (canToImg₁ M q) (canToImg₁δ M q)
  /-- `Hⁱ(X, ℱ) = 0` for coherent `ℱ` and `i > d`, at `ℱ = (p^*M)^∨(q)` and `i = 1`. -/
  vanishing_Hdual₁ : ∀ (M : ANCModule I n c) (q : ℕ), toSituation.d < 1 →
    Subsingleton (Hdual₁ M q)
  /-- `Hⁱ(X, ℱ) = 0` for coherent `ℱ` and `i > d`, at `ℱ = ker(can)(q)` and `i = 2`. -/
  vanishing_Hker₂ : ∀ (M : ANCModule I n c) (q : ℕ), toSituation.d < 2 →
    Subsingleton (Hker₂ M q)
  /-- `HimgD u q` is `Γ(X, im(D_u)(q))` for the dual `D_u = (p^*u)^∨ : (p^*M')^∨ → (p^*M)^∨`. -/
  HimgD : ∀ {M M' : ANCModule I n c}, (M.1 ⟶ M'.1) → ℕ → ModuleCat.{u} A
  /-- The canonical map `Γ(X, im(D_u)(q)) → Γ(X, im(D_u)(q'))` for `q' ≤ q`. -/
  HimgDtr : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1) (q q' : ℕ), q' ≤ q →
    HimgD u q →ₗ[A] HimgD u q'
  /-- `HcokerD u q` is `Γ(X, coker(D_u)(q))`. -/
  HcokerD : ∀ {M M' : ANCModule I n c}, (M.1 ⟶ M'.1) → ℕ → ModuleCat.{u} A
  /-- The canonical map `Γ(X, coker(D_u)(q)) → Γ(X, coker(D_u)(q'))` for `q' ≤ q`. -/
  HcokerDtr : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1) (q q' : ℕ), q' ≤ q →
    HcokerD u q →ₗ[A] HcokerD u q'
  /-- `Γ(X, (p^*M')^∨(q)) → Γ(X, im(D_u)(q))`, `D_u` onto its image. -/
  dualToImgD : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1) (q : ℕ),
    Hdual M' q →ₗ[A] HimgD u q
  /-- The inclusion `Γ(X, im(D_u)(q)) → Γ(X, (p^*M)^∨(q))`. -/
  imgDToDual : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1) (q : ℕ),
    HimgD u q →ₗ[A] Hdual M q
  /-- The map `Γ(X, (p^*M)^∨(q)) → Γ(X, coker(D_u)(q))`. -/
  dualToCokerD : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1) (q : ℕ),
    Hdual M q →ₗ[A] HcokerD u q
  /-- The inclusion of the image of `D_u` is natural in the twist. -/
  imgDToDual_HimgDtr : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1) (q q' : ℕ) (h : q' ≤ q)
      (t : HimgD u q), imgDToDual u q' (HimgDtr u q q' h t) = Hdualtr M q q' h (imgDToDual u q t)
  /-- The map to the cokernel of `D_u` is natural in the twist. -/
  dualToCokerD_Hdualtr : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1) (q q' : ℕ) (h : q' ≤ q)
      (σ : Hdual M q),
    dualToCokerD u q' (Hdualtr M q q' h σ) = HcokerDtr u q q' h (dualToCokerD u q σ)
  /-- Left exactness of `Γ(X, -)` on `0 → im(D_u) → (p^*M)^∨ → coker(D_u) → 0`. -/
  exact_imgDToDual : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1) (q : ℕ),
    Function.Exact (imgDToDual u q) (dualToCokerD u q)
  /-- Tag 0GA9 for the cokernel of `D_u`: when multiplication by every `a ∈ I^c` on `M` factors
  as `h_a ∘ u`, the cokernel is killed by `I^c` (`D_u ∘ D_{h_a} = a`), so the canonical map
  `coker(D_u)(q) → coker(D_u)(q - c)` is zero. -/
  HcokerDtr_eq_zero : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1),
    (∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∃ h : M'.1 ⟶ M.1, u ≫ h = a • 𝟙 M.1) →
    ∀ (q e : ℕ) (h : e ≤ q), e + c = q → HcokerDtr u q e h = 0
  /-- Evaluating `D_u(τ)` against `z ∈ M` is evaluating `τ` against `u(z)`. -/
  evDual_imgDToDual_dualToImgD : ∀ {M M' : ANCModule I n c} (u : M.1 ⟶ M'.1) (q : ℕ)
      (hq : toSituation.q₀ ≤ q) (τ : Hdual M' q),
    evDual M q hq (imgDToDual u q (dualToImgD u q τ)) = (evDual M' q hq τ).comp (resMap I n u)
  /-- The connecting map `Γ(X, im(D_u)(q)) → H¹(X, (p^*M'')^∨(q))` of
  `0 → (p^*M'')^∨ → (p^*M')^∨ → im(D_u) → 0`, for `M → M' → M'' → 0` exact: `p^*` is right exact
  and `(-)^∨` left exact, so the kernel of `D_u` is `(p^*M'')^∨`. -/
  imgDδ : ∀ {M M' M'' : ANCModule I n c} (u : M.1 ⟶ M'.1) (v : M'.1 ⟶ M''.1),
    Function.Exact u.hom v.hom → Function.Surjective v.hom → ∀ q : ℕ,
    HimgD u q →ₗ[A] Hdual₁ M'' q
  /-- The connecting map is natural in the twist. -/
  imgDδ_HimgDtr : ∀ {M M' M'' : ANCModule I n c} (u : M.1 ⟶ M'.1) (v : M'.1 ⟶ M''.1)
      (hex : Function.Exact u.hom v.hom) (hv : Function.Surjective v.hom)
      (q q' : ℕ) (h : q' ≤ q) (t : HimgD u q),
    imgDδ u v hex hv q' (HimgDtr u q q' h t) = Hdual₁tr M'' q q' h (imgDδ u v hex hv q t)
  /-- Exactness of the long exact sequence of `0 → (p^*M'')^∨ → (p^*M')^∨ → im(D_u) → 0` at
  `Γ(X, im(D_u)(q))`. -/
  exact_imgDδ : ∀ {M M' M'' : ANCModule I n c} (u : M.1 ⟶ M'.1) (v : M'.1 ⟶ M''.1)
    (hex : Function.Exact u.hom v.hom) (hv : Function.Surjective v.hom) (q : ℕ),
    Function.Exact (dualToImgD u q) (imgDδ u v hex hv q)

namespace DottedArrowSituation

/-- Peel one copy of `c` off `r + d * c = q` when `d` is positive. -/
private theorem exists_add_eq_of_add_mul_eq {r q c d : ℕ} (hd : 0 < d) (h : r + d * c = q) :
    ∃ e, e + c = q ∧ r + (d - 1) * c = e := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  exact ⟨r + d * c, by rw [← h]; ring, by simp⟩

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}
  (S : DottedArrowSituation A I n c)

/-- **The twisting map on `H¹(X, (p^*M)^∨)` vanishes after `dc` steps**: for an
`(A, n, c)`-module `M` and `r + dc = q` with `r ≥ q₀`, the map
`H¹(X, (p^*M)^∨(q)) → H¹(X, (p^*M)^∨(r))` is zero.

For `d = 0` its source vanishes. For `d ≥ 1` the first `c` steps factor it through
`H¹(X, im(can)(q - c))`. For `d = 1` that group vanishes: it sits between
`H¹(X, p^*(M^∨)(q - c))`, zero by Tag 0GAA(1), and `H²(X, ker(can)(q - c))`, zero as `2 > d`.
For `d ≥ 2` the next `c` steps factor `H¹(im(can)(q - c)) → H¹(im(can)(q - 2c))` through
`H¹(X, p^*(M^∨)(q - 2c))`, and the remaining `(d - 2)c` steps on it vanish, by Tag 0GAA(2) when
`d = 2` and by Tag 0GAA(3) at `i = 1` when `d ≥ 3`. -/
theorem Hdual₁tr_eq_zero (M : ANCModule I n c) {q r : ℕ} (h : r ≤ q) (hr : r + S.d * c = q)
    (hq : S.q₀ ≤ r) (x : S.Hdual₁ M q) : S.Hdual₁tr M q r h x = 0 := by
  rcases Nat.lt_or_ge S.d 1 with hd | hd
  · have := S.vanishing_Hdual₁ M q hd
    rw [Subsingleton.elim x 0, map_zero]
  obtain ⟨e, he, hrd⟩ := exists_add_eq_of_add_mul_eq hd hr
  have hre : r ≤ e := by omega
  set y := S.dual₁ToImg₁ M q e he x with hy
  have hx : S.Hdual₁tr M q r h x = S.img₁ToDual₁ M r (S.Himg₁tr M e r hre y) := by
    rw [S.img₁ToDual₁_Himg₁tr, hy, S.img₁ToDual₁_dual₁ToImg₁, S.Hdual₁tr_trans]
  rw [hx]
  suffices hz : S.Himg₁tr M e r hre y = 0 by rw [hz, map_zero]
  rcases Nat.lt_or_ge S.d 2 with hd2 | hd2
  · -- `d = 1`: `H¹(X, im(can)(q - c)) = 0`.
    have hd1 : S.d = 1 := by omega
    have hre' : r = e := by simpa [hd1] using hrd
    subst hre'
    have : Subsingleton (S.Hker₂ M r) := S.vanishing_Hker₂ M r hd2
    obtain ⟨z, hz⟩ := (S.exact_canToImg₁ M r y).1 (Subsingleton.elim _ _)
    have hsub : Subsingleton (S.H M.dual 1 (r : ℤ)) := by
      have h1 := S.subsingleton_H_top M.dual (q := (r : ℤ)) hd (by exact_mod_cast hq)
      rwa [hd1] at h1
    rw [← hz, Subsingleton.elim z 0, map_zero, map_zero]
  · -- `d ≥ 2`: factor through `H¹(X, p^*(M^∨)(q - 2c))`.
    obtain ⟨k, hk⟩ : ∃ k, S.d = k + 2 := ⟨S.d - 2, by omega⟩
    obtain ⟨e', he', hre'⟩ := exists_add_eq_of_add_mul_eq (by omega : 0 < S.d - 1) hrd
    rw [show S.d - 1 - 1 = k by omega] at hre'
    have hre'' : r ≤ e' := by omega
    set z := S.img₁ToPullback₁ M e e' he' y with hzdef
    have hstep : S.Himg₁tr M e r hre y =
        S.canToImg₁ M r (S.Htr M.dual 1 (e' : ℤ) (r : ℤ) (by exact_mod_cast hre'') z) := by
      rw [← S.canToImg₁_Htr M e' r hre'', hzdef, S.canToImg₁_img₁ToPullback₁,
        S.Himg₁tr_trans]
    rw [hstep]
    suffices hw : S.Htr M.dual 1 (e' : ℤ) (r : ℤ) (by exact_mod_cast hre'') z = 0 by
      rw [hw, map_zero]
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · have hsub : Subsingleton (S.H M.dual 1 (r : ℤ)) :=
        S.subsingleton_H_next M.dual (i := 1) le_rfl (by omega) (by exact_mod_cast hq)
      exact Subsingleton.elim _ _
    · rw [S.Htr_eq_zero M.dual (i := 1) (k := k) _ le_rfl hk0 (by omega)
        (by exact_mod_cast hre') (by exact_mod_cast (by omega : S.q₀ + k * c ≤ e'))]
      rfl

/-- **The dotted arrow of Tag 0GAD.** Let `M → M' → M'' → 0` be exact, with maps `u` and `v`,
such that multiplication by every `a ∈ I^c` on `M` factors as `h_a ∘ u`, and let
`φ : M → Iⁿ/I^{2n}` be `A`-linear. With `f + dc + c = n` and `f ≥ q₀`, there is an `A`-linear
`ψ : M' → I^f/I^{f+n}` with `ψ ∘ u` equal to `φ` twisted down to level `f`.

The section of `(p^*M)^∨(n)` attached to `φ`, twisted down by `c`, comes from the image of
`D_u` (`HcokerDtr_eq_zero`); its obstruction to lifting is in `H¹(X, (p^*M'')^∨(n - c))`, and
dies after twisting down by `dc` more (`Hdual₁tr_eq_zero`); a lift at level `f` evaluates to
`ψ`. -/
theorem exists_comp_resMap_eq {M M' M'' : ANCModule I n c} (u : M.1 ⟶ M'.1)
    (v : M'.1 ⟶ M''.1) (hex : Function.Exact u.hom v.hom) (hv : Function.Surjective v.hom)
    (hfac : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∃ h : M'.1 ⟶ M.1, u ≫ h = a • 𝟙 M.1)
    (φ : resModule I n M.1 →ₗ[A] powQuot I n n) {f e₁ : ℕ} (he₁ : e₁ + c = n)
    (hf : f + S.d * c = e₁) (hq : S.q₀ ≤ f) :
    ∃ ψ : resModule I n M'.1 →ₗ[A] powQuot I f n,
      ψ.comp (resMap I n u) = (powQuotLe I (by omega : f ≤ n)).comp φ := by
  have hfe : f ≤ e₁ := Nat.le.intro hf
  have hen : e₁ ≤ n := Nat.le.intro he₁
  obtain ⟨t, ht⟩ : ∃ t : S.HimgD u e₁,
      S.imgDToDual u e₁ t = S.Hdualtr M n e₁ hen (S.secDual M n φ) := by
    refine (S.exact_imgDToDual u e₁ _).1 ?_
    rw [S.dualToCokerD_Hdualtr, S.HcokerDtr_eq_zero u hfac n e₁ hen he₁, LinearMap.zero_apply]
  have hδ : S.imgDδ u v hex hv f (S.HimgDtr u e₁ f hfe t) = 0 := by
    rw [S.imgDδ_HimgDtr, S.Hdual₁tr_eq_zero M'' hfe hf hq]
  obtain ⟨τ, hτ⟩ := (S.exact_imgDδ u v hex hv f _).1 hδ
  refine ⟨S.evDual M' f hq τ, ?_⟩
  rw [← S.evDual_imgDToDual_dualToImgD u f hq τ, hτ, S.imgDToDual_HimgDtr, ht,
    S.evDual_Hdualtr M e₁ f (hq.trans hfe) hq hfe,
    S.evDual_Hdualtr M n e₁ ((hq.trans hfe).trans hen) (hq.trans hfe) hen,
    S.evDual_secDual M n ((hq.trans hfe).trans hen) φ]
  exact LinearMap.ext fun z => powQuotLe_powQuotLe I n hen hfe (φ z)

attribute [local instance] HasDerivedCategory.standard

/-- **The conclusion of Stacks Tag 0GAD at the printed target, over a `DottedArrowSituation`.**
Let `f + (1 + d)c = n` and `q₀ ≤ f`, so `f = n - (1 + d)c` and `2f = 2n - 2(1 + d)c`. Let `K` be
an object of `D(A/Iⁿ)` with `Hⁱ(K) = 0` for `i ≠ -1, 0`, `H⁻¹(K)` and `H⁰(K)` finite, and
`Ext¹_{A/Iⁿ}(K, N)` annihilated by `I^c/Iⁿ` for every finite `A/Iⁿ`-module `N`. Then
`Ext¹_{A/Iⁿ}(K, Iⁿ/I^{2n}) → Ext¹_{A/Iⁿ}(K, I^f/I^{2f})` is zero.

A finite two-term representative `L⁻¹ --u--> L⁰` with `L⁰` finite free and `a = h_a ∘ u` for
`a ∈ I^c` exists by Tag 0G9F; `L⁻¹` and `coker(u)` are `(A, n, c)`-modules; a class is a map
`φ : L⁻¹ → Iⁿ/I^{2n}` (Tag 0ALN(1)); `exists_comp_resMap_eq` extends `φ` twisted down to
`I^f/I^{f+n}` along `u`, so the class dies there, and a fortiori in the quotient
`I^f/I^{2f}`. -/
theorem ext_one_powQuot_map_eq_zero {f : ℕ} (hf : f + (1 + S.d) * c = n) (hq : S.q₀ ≤ f)
    (K : DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n)))
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) i).obj K))
    (hfin₁ : Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) (-1)).obj K))
    (hfin₀ : Module.Finite (A ⧸ I ^ n)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj K))
    (hann : ∀ (N : ModuleCat.{u} (A ⧸ I ^ n)), Module.Finite (A ⧸ I ^ n) N →
      ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∀ ξ : DerivedCategory.Ext K
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj N) 1, a • ξ = 0)
    (ξ : DerivedCategory.Ext K
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).obj (powQuotObj I n n)) 1) :
    ξ ≫ (CategoryTheory.shiftFunctor (DerivedCategory (ModuleCat.{u} (A ⧸ I ^ n))) (1 : ℤ)).map
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I ^ n)) 0).map
          (powQuotToOfLe I (Nat.le.intro hf) (by omega) (Nat.le.intro hf))) = 0 := by
  classical
  have hfn : f ≤ n := Nat.le.intro hf
  obtain ⟨L, hLge, hLle, hLfin₁, hLfin₀, hLfree, ⟨e₀⟩, hLfac⟩ :=
    ((TwoTermComplex.ext_one_annihilated_iff_twoTerm_factorization
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) K hK).2.2
        inferInstance hfin₁ hfin₀).2.mp hann
  have : L.IsStrictlyGE (-1) := hLge
  have : L.IsStrictlyLE 0 := hLle
  have : Module.Free (A ⧸ I ^ n) (L.X 0) := hLfree
  have : Module.Finite (A ⧸ I ^ n) (L.X 0) := hLfin₀
  have : Projective (L.X 0) :=
    (IsProjective.iff_projective (R := A ⧸ I ^ n) (L.X 0)).mp inferInstance
  let K₁ : ANCModule I n c := ⟨L.X (-1), isANCModule_X_neg_one L hLfin₁ hLfree hLfac⟩
  let K₀ : ANCModule I n c := ⟨L.X 0, isANCModule_of_projective (L.X 0)⟩
  let M₀ : ANCModule I n c :=
    ⟨ModuleCat.of (A ⧸ I ^ n) (L.X 0 ⧸ LinearMap.range (L.d (-1) 0).hom),
      isANCModule_cokernel (L.d (-1) 0) hLfac⟩
  let v : K₀.1 ⟶ M₀.1 := ModuleCat.ofHom (LinearMap.range (L.d (-1) 0).hom).mkQ
  have hex : Function.Exact (L.d (-1) 0).hom v.hom := by
    intro y
    change (LinearMap.range (L.d (-1) 0).hom).mkQ y = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  have hv : Function.Surjective v.hom := Submodule.mkQ_surjective _
  obtain ⟨e₁, he₁, hfe₁⟩ := exists_add_eq_of_add_mul_eq (by omega : 0 < 1 + S.d) hf
  rw [Nat.add_sub_cancel_left] at hfe₁
  refine TwoTermComplex.ext_one_map_eq_zero_of_forall_factorization L e₀ _ ?_ ξ
  intro φcat
  obtain ⟨ψ, hψ⟩ := S.exists_comp_resMap_eq (M := K₁) (M' := K₀) (M'' := M₀) (L.d (-1) 0) v
    hex hv hLfac (toResHom I n n φcat) he₁ hfe₁ hq
  refine ⟨ofResHom I f n ψ ≫ powQuotToOfLe I le_rfl (by omega) hfn, ?_⟩
  ext z
  have h1 : ψ (resMap I n (L.d (-1) 0) z) = powQuotLe I hfn ((toResHom I n n φcat) z) :=
    LinearMap.congr_fun hψ z
  change powQuotMap I (le_refl f) (by omega : f + f ≤ f + n) (ψ (resMap I n (L.d (-1) 0) z)) =
    powQuotMap I hfn (by omega : f + f ≤ n + n) ((toResHom I n n φcat) z)
  rw [h1]
  induction (toResHom I n n φcat) z using Submodule.Quotient.induction_on with
  | H y => rfl

end DottedArrowSituation

end Stacks.LocalCohomology.UniformityIII

end
