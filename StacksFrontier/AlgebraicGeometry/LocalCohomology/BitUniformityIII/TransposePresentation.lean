module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.PullbackCohomology
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DottedArrow
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.DualPullback
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The transpose of a presentation of an `(A, n, c)`-module

Let `R^{⊕r₁} --d--> R^{⊕r₀} --π--> M → 0` be a finite free presentation of an `(A, n, c)`-module
`M`, `R = A/Iⁿ`. Dualizing gives the exact sequence

`0 → M^∨ → R^{⊕r₀} --d^∨--> R^{⊕r₁} → C → 0`,

and this file shows that its two pieces `0 → M^∨ → R^{⊕r₀} → L → 0` and `0 → L → R^{⊕r₁} → C → 0`,
`L = im(d^∨)`, are presentations of `(A, n, c)`-modules. The point is that the cokernel `C` of the
transpose is again `I^c/Iⁿ`-projective (`isIProjective_cokernel_dualMap`): this is what lets the
section of [Stacks, Tag 0GAC] that the source obtains by dualizing a sheaf be constructed instead
inside the twisted pullbacks of `A`-modules, with [Stacks, Tag 0GA8] applied to the two
presentations.

## Main results

* `Stacks.LocalCohomology.UniformityIII.isIProjective_cokernel_dualMap`: the cokernel of the
  transpose of a presentation of a `J`-projective module is `J`-projective.
* `Stacks.LocalCohomology.UniformityIII.TwoStepPresentation.presL` and `…presC`: the two
  presentations above, as `ANCPresentation`s.
-/

@[expose] public noncomputable section

universe u

namespace Stacks.LocalCohomology.UniformityIII

section Transpose

variable {R : Type u} [CommRing R] {F₀ F₁ M : Type u}
  [AddCommGroup F₀] [Module R F₀] [AddCommGroup F₁] [Module R F₁] [AddCommGroup M] [Module R M]

/-- A map `g` into `F₀` with `π ∘ g = 0` factors through `d` when `range d = ker π` and the source
is projective. -/
private theorem exists_comp_eq_of_map_eq_zero {F : Type u} [AddCommGroup F] [Module R F]
    [Module.Projective R F] (d : F₁ →ₗ[R] F₀) (π : F₀ →ₗ[R] M)
    (hex : LinearMap.range d = LinearMap.ker π) (g : F →ₗ[R] F₀) (hg : ∀ x, π (g x) = 0) :
    ∃ h : F →ₗ[R] F₁, d ∘ₗ h = g := by
  obtain ⟨h, hh⟩ := Module.projective_lifting_property d.rangeRestrict
    (LinearMap.codRestrict (LinearMap.range d) g fun x => hex ▸ hg x) d.surjective_rangeRestrict
  exact ⟨h, LinearMap.ext fun x => congrArg Subtype.val (LinearMap.congr_fun hh x)⟩

/-- **The transpose of a presentation of a relatively projective module is relatively
projective.** Let `F₁ --d--> F₀ --π--> M → 0` be exact with `F₀` projective and `M`
`J`-projective. Then the cokernel of the transpose `d^∨ : F₀^∨ → F₁^∨` is `J`-projective, as soon
as `F₁^∨` is projective.

For `a ∈ J` write `a = β ∘ α` through a projective `P`, lift `β` to `β₀ : P → F₀`, and `a - β₀απ`
(which lands in `ker π = im d`) to `h : F₀ → F₁` with `d h = a - β₀απ`. Then `k = a - hd` has
`dk = 0`, so `λ ↦ λ ∘ k` descends to the cokernel of `d^∨`, and composing it with the projection
is multiplication by `a`, because `λ ∘ k = aλ - d^∨(λ ∘ h)`. -/
theorem isIProjective_cokernel_dualMap (J : Ideal R) [Module.Projective R F₀]
    [Module.Projective R (Module.Dual R F₁)] (d : F₁ →ₗ[R] F₀) (π : F₀ →ₗ[R] M)
    (hπ : Function.Surjective π) (hex : LinearMap.range d = LinearMap.ker π)
    (hM : Module.IsIProjective R J M) :
    Module.IsIProjective R J (Module.Dual R F₁ ⧸ LinearMap.range d.dualMap) := by
  intro a ha
  obtain ⟨P, _, _, _, α, β, hαβ⟩ := hM a ha
  obtain ⟨β₀, hβ₀⟩ := Module.projective_lifting_property π β hπ
  set g : F₀ →ₗ[R] F₀ := a • LinearMap.id - β₀ ∘ₗ α ∘ₗ π with hg
  obtain ⟨h, hh⟩ := exists_comp_eq_of_map_eq_zero d π hex g fun x => by
    have h₁ : π (β₀ (α (π x))) = a • π x := by
      rw [← LinearMap.comp_apply π β₀, hβ₀, ← LinearMap.comp_apply β α, ← hαβ]
      rfl
    simp [hg, h₁]
  have hdh : ∀ x, d (h x) = g x := LinearMap.congr_fun hh
  set k : F₁ →ₗ[R] F₁ := a • LinearMap.id - h ∘ₗ d with hk
  have hdk : ∀ y, d (k y) = 0 := by
    intro y
    have h₂ : π (d y) = 0 := by
      rw [← LinearMap.mem_ker, ← hex]
      exact ⟨y, rfl⟩
    simp [hk, hdh, hg, h₂]
  let s : (Module.Dual R F₁ ⧸ LinearMap.range d.dualMap) →ₗ[R] Module.Dual R F₁ :=
    (LinearMap.range d.dualMap).liftQ k.dualMap (by
      rintro _ ⟨μ, rfl⟩
      rw [LinearMap.mem_ker]
      ext y
      simp [hdk])
  refine FactorsThroughProj.mk' s (LinearMap.range d.dualMap).mkQ ?_
  ext lam
  simp only [LinearMap.lsmul_apply, LinearMap.coe_comp, Function.comp_apply,
    Submodule.mkQ_apply, s, Submodule.liftQ_apply]
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
  refine ⟨lam ∘ₗ h, ?_⟩
  ext y
  simp [hk]

end Transpose

section Transport

variable {R : Type u} [CommRing R]

/-- Relative projectivity transports along a linear equivalence. -/
theorem isIProjective_of_linearEquiv {J : Ideal R} {M N : Type*} [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (hM : Module.IsIProjective R J M)
    (e : M ≃ₗ[R] N) : Module.IsIProjective R J N := by
  intro a ha
  convert (hM a ha).comp_comp (e.symm : N →ₗ[R] M) (e : M →ₗ[R] N) using 1
  ext x
  simp

/-- The dual of the standard free module `R^{⊕r}`, identified with `R^{⊕r}` by evaluation on the
standard basis. -/
def finDualEquiv (r : ℕ) : Module.Dual R (Fin r → R) ≃ₗ[R] (Fin r → R) :=
  LinearEquiv.ofLinearMap
    { toFun := fun μ j => μ (Pi.single j 1)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    { toFun := fun v => ∑ j, v j • LinearMap.proj j
      map_add' := fun v w => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a v => by simp [Finset.smul_sum, smul_smul] }
    (by
      refine LinearMap.ext fun v => funext fun j => ?_
      simp [Pi.single_apply, eq_comm])
    (by
      refine LinearMap.ext fun μ => LinearMap.ext fun w => ?_
      change (∑ j, μ (Pi.single j 1) • LinearMap.proj (R := R) (φ := fun _ : Fin r => R) j) w
        = μ w
      rw [LinearMap.pi_apply_eq_sum_univ μ w, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [LinearMap.smul_apply, LinearMap.coe_proj, Function.eval, smul_eq_mul]
      rw [mul_comm]
      congr 2
      ext k
      simp [Pi.single_apply, eq_comm])

/-- The functional attached to `v ∈ R^{⊕r}` sends `w` to `∑ⱼ vⱼ wⱼ`. -/
@[simp] theorem finDualEquiv_symm_apply (r : ℕ) (v w : Fin r → R) :
    (finDualEquiv r).symm v w = ∑ j, v j * w j := by
  change (∑ j, v j • LinearMap.proj (R := R) (φ := fun _ : Fin r => R) j) w = _
  rw [LinearMap.sum_apply]
  rfl

/-- The `j`-th coordinate of a functional `μ` is its value `μ(eⱼ)` on the `j`-th standard basis
vector. -/
@[simp] theorem finDualEquiv_apply (r : ℕ) (μ : Module.Dual R (Fin r → R)) (j : Fin r) :
    finDualEquiv r μ j = μ (Pi.single j 1) := rfl

end Transport

section Presentation

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}

/-- **A finite free presentation `R^{⊕r₁} --d--> R^{⊕r₀} --π--> M → 0`** of an
`(A, n, c)`-module, `R = A/Iⁿ`. -/
structure TwoStepPresentation (M : ANCModule I n c) where
  /-- The rank of the generators. -/
  r₀ : ℕ
  /-- The rank of the relations. -/
  r₁ : ℕ
  /-- The surjection onto `M`. -/
  π : (Fin r₀ → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] M.1
  /-- The relations. -/
  d : (Fin r₁ → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin r₀ → A ⧸ I ^ n)
  surjective_π : Function.Surjective π
  range_d : LinearMap.range d = LinearMap.ker π

/-- Every `(A, n, c)`-module has a finite free presentation: it is finite over the Noetherian ring
`A/Iⁿ`, so is the kernel of any finite free surjection onto it. -/
theorem nonempty_twoStepPresentation (M : ANCModule I n c) :
    Nonempty (TwoStepPresentation M) := by
  have : Module.Finite (A ⧸ I ^ n) M.1 := M.2.1
  obtain ⟨r₀, π, hπ⟩ := Module.Finite.exists_fin' (A ⧸ I ^ n) M.1
  have : Module.Finite (A ⧸ I ^ n) (LinearMap.ker π) := Module.IsNoetherian.finite _ _
  obtain ⟨r₁, g, hg⟩ := Module.Finite.exists_fin' (A ⧸ I ^ n) (LinearMap.ker π)
  refine ⟨⟨r₀, r₁, π, (LinearMap.ker π).subtype ∘ₗ g, hπ, ?_⟩⟩
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hg, Submodule.map_top,
    Submodule.range_subtype]

namespace TwoStepPresentation

variable {M : ANCModule I n c} (P : TwoStepPresentation M)

/-- **The transpose `R^{⊕r₀} → R^{⊕r₁}` of the relation matrix**, i.e. `d^∨` read through
`finDualEquiv`. -/
def transD : (Fin P.r₀ → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin P.r₁ → A ⧸ I ^ n) :=
  (finDualEquiv (R := A ⧸ I ^ n) P.r₁).toLinearMap ∘ₗ P.d.dualMap ∘ₗ
    (finDualEquiv (R := A ⧸ I ^ n) P.r₀).symm.toLinearMap

/-- **`M^∨ → R^{⊕r₀}`, `λ ↦ (λ(π eⱼ))ⱼ`**, the transpose of `π`. -/
def dualIncl : Module.Dual (A ⧸ I ^ n) M.1 →ₗ[A ⧸ I ^ n] (Fin P.r₀ → A ⧸ I ^ n) :=
  (finDualEquiv (R := A ⧸ I ^ n) P.r₀).toLinearMap ∘ₗ P.π.dualMap

omit [IsNoetherianRing A] in
/-- The `j`-th coordinate of `dualIncl λ` is `λ(π eⱼ)`. -/
@[simp] theorem dualIncl_apply (lam : Module.Dual (A ⧸ I ^ n) M.1) (j : Fin P.r₀) :
    P.dualIncl lam j = lam (P.π (Pi.single j 1)) := rfl

omit [IsNoetherianRing A] in
/-- The coordinates of the transposed relation matrix: `(d^∨ eⱼ)ₖ = (d eₖ)ⱼ`. -/
theorem transD_single (j : Fin P.r₀) (k : Fin P.r₁) :
    P.transD (Pi.single j 1) k = P.d (Pi.single k 1) j := by
  simp [transD, Pi.single_apply]

omit [IsNoetherianRing A] in
/-- `dualIncl` is injective, `π` being surjective. -/
theorem injective_dualIncl : Function.Injective P.dualIncl :=
  (finDualEquiv P.r₀).injective.comp (LinearMap.dualMap_injective_of_surjective P.surjective_π)

omit [IsNoetherianRing A] in
/-- The image of `dualIncl` is the kernel of the transposed relation matrix, so
`0 → M^∨ → R^{⊕r₀} → R^{⊕r₁}` is exact. -/
theorem range_dualIncl : LinearMap.range P.dualIncl = LinearMap.ker P.transD := by
  have hker : LinearMap.ker P.d.dualMap = LinearMap.range P.π.dualMap := by
    rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, P.range_d,
      LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _ P.surjective_π]
  ext v
  constructor
  · rintro ⟨lam, rfl⟩
    have : P.π.dualMap lam ∈ LinearMap.ker P.d.dualMap := hker ▸ ⟨lam, rfl⟩
    simp only [LinearMap.mem_ker, transD, dualIncl, LinearMap.coe_comp, Function.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this ⊢
    rw [this, map_zero]
  · intro hv
    obtain ⟨lam, hlam⟩ : (finDualEquiv P.r₀).symm v ∈ LinearMap.range P.π.dualMap := by
      rw [← hker]
      simp only [LinearMap.mem_ker, transD, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe] at hv ⊢
      exact (finDualEquiv P.r₁).map_eq_zero_iff.mp hv
    exact ⟨lam, by simp [dualIncl, hlam]⟩

/-- The image `L` of the transposed relation matrix. -/
abbrev imageL : Submodule (A ⧸ I ^ n) (Fin P.r₁ → A ⧸ I ^ n) := LinearMap.range P.transD

/-- The cokernel `C` of the transposed relation matrix. -/
abbrev cokerC : Type u := (Fin P.r₁ → A ⧸ I ^ n) ⧸ P.imageL

omit [IsNoetherianRing A] in
/-- The cokernel `C` of the transposed relation matrix is an `(A, n, c)`-module. -/
theorem isANCModule_cokerC : IsANCModule I n c (ModuleCat.of (A ⧸ I ^ n) P.cokerC) := by
  refine ⟨Module.Finite.of_surjective _ (Submodule.mkQ_surjective _), ?_⟩
  refine isIProjective_of_linearEquiv
    (isIProjective_cokernel_dualMap (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) P.d P.π
      P.surjective_π P.range_d M.2.2)
    (Submodule.Quotient.equiv _ _ (finDualEquiv P.r₁) ?_)
  change _ = LinearMap.range ((finDualEquiv (R := A ⧸ I ^ n) P.r₁).toLinearMap ∘ₗ P.d.dualMap ∘ₗ
    (finDualEquiv (R := A ⧸ I ^ n) P.r₀).symm.toLinearMap)
  rw [LinearMap.range_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr (finDualEquiv (R := A ⧸ I ^ n) P.r₀).symm.surjective,
    Submodule.map_top]

/-- The image `L` of the transposed relation matrix is an `(A, n, c)`-module. -/
theorem isANCModule_imageL : IsANCModule I n c (ModuleCat.of (A ⧸ I ^ n) P.imageL) :=
  isANCModule_kernel (M := ModuleCat.of (A ⧸ I ^ n) P.cokerC) P.imageL.subtype P.imageL.mkQ
    Subtype.coe_injective (Submodule.mkQ_surjective _)
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) P.isANCModule_cokerC

/-- `C` as an `(A, n, c)`-module. -/
def cokerANC : ANCModule I n c := ⟨ModuleCat.of (A ⧸ I ^ n) P.cokerC, P.isANCModule_cokerC⟩

/-- `L` as an `(A, n, c)`-module. -/
def imageANC : ANCModule I n c := ⟨ModuleCat.of (A ⧸ I ^ n) P.imageL, P.isANCModule_imageL⟩

/-- **`0 → L → R^{⊕r₁} → C → 0`**, a presentation of `C` with kernel `L`. -/
def presC : ANCPresentation I n c P.cokerANC where
  rank := P.r₁
  kernel := ModuleCat.of (A ⧸ I ^ n) P.imageL
  incl := P.imageL.subtype
  proj := P.imageL.mkQ
  incl_injective := Subtype.coe_injective
  proj_surjective := Submodule.mkQ_surjective _
  range_incl_eq_ker_proj := by rw [Submodule.range_subtype]; exact (Submodule.ker_mkQ _).symm

/-- **`0 → M^∨ → R^{⊕r₀} → L → 0`**, a presentation of `L` with kernel `M^∨`. -/
def presL : ANCPresentation I n c P.imageANC where
  rank := P.r₀
  kernel := (M.dual).1
  incl := P.dualIncl
  proj := P.transD.rangeRestrict
  incl_injective := P.injective_dualIncl
  proj_surjective := P.transD.surjective_rangeRestrict
  range_incl_eq_ker_proj := P.range_dualIncl.trans (LinearMap.ker_rangeRestrict _).symm

end TwoStepPresentation

end Presentation

section FinTranspose

variable {R : Type u} [CommRing R]

/-- **The transpose of a map between standard free modules**, `g^∨` read through
`finDualEquiv`. -/
def finTranspose {r s : ℕ} (g : (Fin r → R) →ₗ[R] (Fin s → R)) :
    (Fin s → R) →ₗ[R] (Fin r → R) :=
  (finDualEquiv (R := R) r).toLinearMap ∘ₗ g.dualMap ∘ₗ (finDualEquiv (R := R) s).symm.toLinearMap

/-- The `j`-th coordinate of `g^∨ w` is `∑ₖ wₖ · (g eⱼ)ₖ`. -/
theorem finTranspose_apply {r s : ℕ} (g : (Fin r → R) →ₗ[R] (Fin s → R)) (w : Fin s → R)
    (j : Fin r) : finTranspose g w j = ∑ k, w k * g (Pi.single j 1) k := by
  simp [finTranspose]

/-- The transpose of a composite is the composite of the transposes in the opposite order. -/
theorem finTranspose_comp {r s t : ℕ} (g : (Fin s → R) →ₗ[R] (Fin t → R))
    (g' : (Fin r → R) →ₗ[R] (Fin s → R)) :
    finTranspose (g ∘ₗ g') = finTranspose g' ∘ₗ finTranspose g := by
  refine LinearMap.ext fun w => ?_
  simp only [finTranspose, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

/-- The transpose is additive. -/
theorem finTranspose_add {r s : ℕ} (g g' : (Fin r → R) →ₗ[R] (Fin s → R)) :
    finTranspose (g + g') = finTranspose g + finTranspose g' := by
  refine LinearMap.ext fun w => funext fun j => ?_
  simp [finTranspose_apply, mul_add, Finset.sum_add_distrib]

/-- The transpose of `a • id` is `a • id`. -/
theorem finTranspose_smul_id {r : ℕ} (a : R) :
    finTranspose (a • LinearMap.id : (Fin r → R) →ₗ[R] (Fin r → R)) = a • LinearMap.id := by
  refine LinearMap.ext fun w => funext fun j => ?_
  simp [finTranspose_apply, Pi.single_apply, mul_comm]

end FinTranspose

section Cokernel

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A} {n c : ℕ}

/-- **The cokernel of a map `D : M → R^{⊕r}` that splits multiplication by `I^c`, as an
`(A, n, c)`-module.** That it is one is `isANCModule_cokernel` of
`BitUniformityIII/DottedArrow.lean` at the finite free module `R^{⊕r}`: if for every
`a ∈ I^c/Iⁿ` there is `h` with `h ∘ D = a`, then `a - D h` kills the image of `D` and so
descends to `coker D → R^{⊕r}`, which composed with the projection is multiplication by `a`. -/
def cokernelANC {M : ModuleCat.{u} (A ⧸ I ^ n)} {r : ℕ}
    (D : M →ₗ[A ⧸ I ^ n] (Fin r → A ⧸ I ^ n))
    (hD : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∃ h : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] M, ∀ z, h (D z) = a • z) : ANCModule I n c :=
  ⟨ModuleCat.of (A ⧸ I ^ n) ((Fin r → A ⧸ I ^ n) ⧸ LinearMap.range D),
    isANCModule_cokernel (P := ModuleCat.of (A ⧸ I ^ n) (Fin r → A ⧸ I ^ n)) (ModuleCat.ofHom D)
      fun a ha => (hD a ha).elim fun h hh =>
        ⟨ModuleCat.ofHom h, ModuleCat.hom_ext (LinearMap.ext fun z => by simpa using hh z)⟩⟩

/-- **The presentation `R^{⊕r₀} --D∘π--> R^{⊕r} → coker D → 0`** of the cokernel, built from a
presentation of `M`. -/
def TwoStepPresentation.cokernelPres {M : ANCModule I n c} (P : TwoStepPresentation M) {r : ℕ}
    (D : M.1 →ₗ[A ⧸ I ^ n] (Fin r → A ⧸ I ^ n))
    (hD : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∃ h : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] M.1, ∀ z, h (D z) = a • z) :
    TwoStepPresentation (cokernelANC D hD) where
  r₀ := r
  r₁ := P.r₀
  π := (LinearMap.range D).mkQ
  d := D ∘ₗ P.π
  surjective_π := Submodule.mkQ_surjective _
  range_d := by
    refine Eq.trans ?_ (Submodule.ker_mkQ (LinearMap.range D)).symm
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr P.surjective_π, Submodule.map_top]

omit [IsNoetherianRing A] in
/-- **The key identity of the local lift.** For `a ∈ I^c/Iⁿ` and `h` with `h ∘ D = a`, a lift
`h̃ : R^{⊕r} → R^{⊕r₀}` of `h` satisfies `(D π)^∨ ∘ h̃^∨ = a + ℓ^∨ ∘ d^∨` for some `ℓ`, so on the
kernel of the transposed relation matrix `d^∨` it is multiplication by `a`. -/
theorem TwoStepPresentation.exists_transpose_comp {M : ANCModule I n c} (P : TwoStepPresentation M)
    {r : ℕ} (D : M.1 →ₗ[A ⧸ I ^ n] (Fin r → A ⧸ I ^ n)) (a : A ⧸ I ^ n)
    (h : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] M.1) (hh : ∀ z, h (D z) = a • z) :
    ∃ (ht : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin P.r₀ → A ⧸ I ^ n))
      (ℓ : (Fin P.r₀ → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin P.r₁ → A ⧸ I ^ n)),
      finTranspose (D ∘ₗ P.π) ∘ₗ finTranspose ht =
        a • LinearMap.id + finTranspose ℓ ∘ₗ P.transD := by
  obtain ⟨ht, hht⟩ := Module.projective_lifting_property P.π h P.surjective_π
  let G : (Fin P.r₀ → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin P.r₀ → A ⧸ I ^ n) :=
    ht ∘ₗ D ∘ₗ P.π - a • LinearMap.id
  obtain ⟨ℓ, hdℓ⟩ := exists_comp_eq_of_map_eq_zero P.d P.π P.range_d G fun v => by
    have h₁ : P.π (ht (D (P.π v))) = a • P.π v := by
      rw [← LinearMap.comp_apply P.π ht, hht, hh]
    simp [G, h₁]
  refine ⟨ht, ℓ, ?_⟩
  rw [← finTranspose_comp, show ht ∘ₗ D ∘ₗ P.π = a • LinearMap.id + P.d ∘ₗ ℓ by
      rw [hdℓ]; simp [G], finTranspose_add, finTranspose_smul_id, finTranspose_comp]
  rfl

end Cokernel

end Stacks.LocalCohomology.UniformityIII

end
