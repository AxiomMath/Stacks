module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.Annihilator
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientDerivedLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Kernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Product
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated
public import StacksCore.Tactic.StacksAttribute

/-!
# The remark of Tag 0888 over sheaves of modules

Let `X` be a scheme, let `𝒦, 𝒥 ⊆ 𝒪_X` be quasi-coherent sheaves of ideals and let `a : M ⟶ N` be
a morphism of quasi-coherent `𝒪_X`-modules whose kernel and cokernel are annihilated by `𝒦 ᵗ`.
Reducing `a` modulo `𝒥 ᵐ` gives `ā : M / 𝒥 ᵐ M ⟶ N / 𝒥 ᵐ N`, and this file shows that `𝒦 ᵗ`
annihilates the cokernel of `ā` and `𝒦 ²ᵗ` annihilates its kernel. That is the commutative-algebra
fact of the remark of [Stacks, Tag 0888], transported from modules to sheaves of modules.

The module-level statements are already available: `Ideal.pow_le_annihilator_ker_mapQ_of_exact`
proves the kernel half for a five-term exact sequence of modules over a commutative ring. What is
added here is the passage to sheaves. Annihilation of a sheaf of modules by a power of an ideal
sheaf is tested on the sections over the affine opens
(`Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_sections_annihilated`), and over an
affine open the sections of the three sheaves involved are the corresponding modules:

* the sections of a categorical kernel are the kernel of the map on sections, which is
  `Stacks.Algebraization.exists_kernel_section` together with monicity of `kernel.ι`;
* the sections of a categorical cokernel receive the sections of the target surjectively and the
  resulting sequence is exact, which is
  `Stacks.Algebraization.affine_sections_cokernel_exact` and needs quasi-coherence;
* the sections of `M / 𝒥 ᵐ M` are `Γ(M, U) / 𝒥(U) ᵐ Γ(M, U)`, which is surjectivity of the
  projection on sections together with
  `Stacks.Algebraization.cokernel_π_idealPowerMultiple_app_eq_zero_iff` for its kernel.

## Main results

* `Stacks.Algebraization.smul_mem_range_app_of_idealPowerMultiple_cokernel_eq_bot` — over an
  affine open, a power of `𝒦` annihilating the cokernel of `a` carries every section of the target
  into the range of `a` on sections.
* `Stacks.Algebraization.idealPowerMultiple_cokernel_idealPowerQuotientMap_eq_bot` — **the
  cokernel half**: `𝒦 ᵗ` annihilates the cokernel of the reduction of `a` modulo `𝒥 ᵐ`.
* `Stacks.Algebraization.idealPowerMultiple_kernel_idealPowerQuotientMap_eq_bot` — **the kernel
  half**: `𝒦 ²ᵗ` annihilates the kernel of the reduction of `a` modulo `𝒥 ᵐ`.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_whiskerRight_idealPowerQuotientFunctor`
  — the two halves together, for the levelwise reduction of a morphism of inverse systems; this is
  the form in which the proof of Tag 088A uses the remark.
* `Stacks.Algebraization.idealPowerMultiple_kernel_eq_bot_of_reductions` and
  `Stacks.Algebraization.idealPowerMultiple_cokernel_eq_bot_of_reductions` — the converse passage,
  from the annihilation of the kernels and cokernels of all the reductions of a morphism modulo
  the powers of `ℐ` back to the annihilation of its own kernel and cokernel, for a morphism whose
  source, respectively whose cokernel, is `ℐ`-adically separated on affine sections. That
  hypothesis is *not* what Tag 088A has available; see the docstring of the first of the two.

## Implementation notes

The exponent for the cokernel is `t` rather than `2 * t`, because the cokernel of `ā` is a
quotient of the cokernel of `a`; the source states the single exponent `2 t` for both halves,
which is the weaker statement obtained by raising the exponent with
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_le`.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and the two
presentations carry separately declared instances, so every categorical construction below names
its category explicitly as `(C := X.Modules)`.

**No `@[stacks]` attribute is attached here.** The remark of Tag 0888 over sheaves of modules is
registered on `Stacks.Algebraization.idealPowerMultiple_kernel_cokernel_idealPowerQuotientMap`
(`Cohomology/Coherent/AnnihilatorSheaf.lean`); the statements below are the two halves with the
sharper cokernel exponent, and the levelwise form for a morphism of systems.

## References

* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-! ### Annihilation of a cokernel, read on the sections over an affine open -/

/-- **A power of `𝒦` annihilating the cokernel of `a` carries sections into the range of `a`.**
Over an affine open `U`, if `𝒦 ᵗ Coker(a) = 0` and `r ∈ 𝒦(U) ᵗ`, then `r • y` is in the range of
`a` on sections for every section `y` of the target.

The projection onto the cokernel kills `r • y`, and over an affine open the sections of a
quasi-coherent module are exact at the target, which is
`Stacks.Algebraization.affine_sections_cokernel_exact`. -/
public theorem smul_mem_range_app_of_idealPowerMultiple_cokernel_eq_bot
    {K : X.IdealSheafData} {t : ℕ} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {a : M ⟶ N}
    (hcok : idealPowerMultiple K t (cokernel (C := X.Modules) a) = ⊥)
    (U : X.affineOpens) {r : Γ(X, U)} (hr : r ∈ K.ideal U ^ t) (y : Γ(N, U)) :
    ∃ x : Γ(M, U), a.app U.1 x = r • y := by
  have hz : (cokernel.π (C := X.Modules) a).app U.1 (r • y) = 0 := by
    rw [Scheme.Modules.Hom.app_smul]
    exact affine_sections_annihilated_of_idealPowerMultiple_eq_bot hcok U hr _
  exact (affine_sections_cokernel_exact a U (r • y)).mp hz

/-! ### The commutative-algebra fact of Tag 0888, over sheaves -/

/-- **The remark of Tag 0888, cokernel half.** If `𝒦 ᵗ` annihilates the cokernel of a morphism
`a : M ⟶ N` of quasi-coherent modules, then it annihilates the cokernel of the reduction
`M / 𝒥 ᵐ M ⟶ N / 𝒥 ᵐ N` of `a` modulo any power of any quasi-coherent ideal sheaf.

The cokernel of the reduction is a quotient of the cokernel of `a`; concretely, every section of
it over an affine open comes from a section of `N`, and a power of `𝒦` carries that section into
the range of `a`, which the projection to the cokernel of the reduction kills. -/
public theorem idealPowerMultiple_cokernel_idealPowerQuotientMap_eq_bot
    (K J : X.IdealSheafData) (m : ℕ) {t : ℕ} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    (hcok : idealPowerMultiple K t (cokernel (C := X.Modules) a) = ⊥) :
    idealPowerMultiple K t (cokernel (C := X.Modules)
      (idealPowerQuotientMap J J m m le_rfl a)) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U r hr w => ?_
  let abar := idealPowerQuotientMap J J m m le_rfl a
  let πM := cokernel.π (C := X.Modules) (idealPowerMultiple J m M).ι
  let πN := cokernel.π (C := X.Modules) (idealPowerMultiple J m N).ι
  change r • w = 0
  obtain ⟨v, hv⟩ : ∃ v : Γ(idealPowerQuotient J m N, U.1),
      (cokernel.π (C := X.Modules) abar).app U.1 v = w :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
      (cokernel.π (C := X.Modules) abar) U.1 U.2 w
  obtain ⟨y, hy⟩ : ∃ y : Γ(N, U.1), πN.app U.1 y = v :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X πN U.1 U.2 v
  obtain ⟨x, hx⟩ := smul_mem_range_app_of_idealPowerMultiple_cokernel_eq_bot hcok U hr y
  have key : (cokernel.π (C := X.Modules) abar).app U.1 (πN.app U.1 (a.app U.1 x)) = 0 := by
    have h1 : πN.app U.1 (a.app U.1 x) = abar.app U.1 (πM.app U.1 x) :=
      (congrArg (fun k : M ⟶ idealPowerQuotient J m N => k.app U.1 x)
        (idealPowerQuotientMap_π J J m m le_rfl a)).symm
    rw [h1]
    exact congrArg (fun k : idealPowerQuotient J m M ⟶ cokernel (C := X.Modules) abar =>
      k.app U.1 (πM.app U.1 x)) (cokernel.condition (C := X.Modules) abar)
  calc r • w = r • (cokernel.π (C := X.Modules) abar).app U.1 (πN.app U.1 y) := by
        rw [hy, hv]
    _ = (cokernel.π (C := X.Modules) abar).app U.1 (πN.app U.1 (r • y)) := by
        rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul]
    _ = (cokernel.π (C := X.Modules) abar).app U.1 (πN.app U.1 (a.app U.1 x)) := by rw [hx]
    _ = 0 := key

/-- Over an affine open, a power of `𝒦` annihilating the kernel of `a` kills every section of the
source which `a` sends to zero. -/
public theorem smul_eq_zero_of_idealPowerMultiple_kernel_eq_bot
    {K : X.IdealSheafData} {t : ℕ} {M N : X.Modules} {a : M ⟶ N}
    (hker : idealPowerMultiple K t (kernel (C := X.Modules) a) = ⊥)
    (U : X.affineOpens) {r : Γ(X, U)} (hr : r ∈ K.ideal U ^ t) {x : Γ(M, U)}
    (hx : a.app U.1 x = 0) : r • x = 0 := by
  obtain ⟨y, hy⟩ := exists_kernel_section a U.1 x hx
  calc r • x = r • (kernel.ι (C := X.Modules) a).app U.1 y := by rw [hy]
    _ = (kernel.ι (C := X.Modules) a).app U.1 (r • y) :=
        (Scheme.Modules.Hom.app_smul _ r y).symm
    _ = 0 := by
        rw [affine_sections_annihilated_of_idealPowerMultiple_eq_bot hker U hr y, map_zero]

/-- **The commutative-algebra fact of Tag 0888, on the sections over an affine open.** If `𝒦 ᵗ`
annihilates the kernel and the cokernel of `a : M ⟶ N`, then a section of `M / 𝒥 ᵐ M` over an
affine open which the reduction of `a` kills is killed by `𝒦 ²ᵗ`.

Over an affine open the sections of `M / 𝒥 ᵐ M` are `Γ(M, U) / 𝒥(U) ᵐ Γ(M, U)`: the projection is
surjective there, and a section of `M` dies in the quotient exactly when it lies in
`𝒥(U) ᵐ Γ(M, U)`, which is
`Stacks.Algebraization.cokernel_π_idealPowerMultiple_app_eq_zero_iff`. The statement is then the
module-level `Ideal.pow_le_annihilator_ker_mapQ_of_exact`, applied to the five-term exact sequence
built from the kernel and the cokernel of `a` on sections. -/
public theorem smul_eq_zero_of_app_idealPowerQuotientMap_eq_zero
    (K J : X.IdealSheafData) (m : ℕ) {t : ℕ} (ht : 0 < t) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] {a : M ⟶ N}
    (hker : idealPowerMultiple K t (kernel (C := X.Modules) a) = ⊥)
    (hcok : idealPowerMultiple K t (cokernel (C := X.Modules) a) = ⊥)
    (U : X.affineOpens) {r : Γ(X, U)} (hr : r ∈ K.ideal U ^ (2 * t))
    {w : Γ(idealPowerQuotient J m M, U)}
    (hw : (idealPowerQuotientMap J J m m le_rfl a).app U.1 w = 0) :
    r • w = 0 := by
  obtain ⟨x, hx⟩ : ∃ x : Γ(M, U.1),
      (cokernel.π (C := X.Modules) (idealPowerMultiple J m M).ι).app U.1 x = w :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
      (cokernel.π (C := X.Modules) (idealPowerMultiple J m M).ι) U.1 U.2 w
  let au : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1) := (a.val.app (op U.1)).hom
  have hau : ∀ y : Γ(M, U.1), au y = a.app U.1 y := fun _ => rfl
  have hT : K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1) ↥(LinearMap.ker au) := by
    intro s hs
    rw [Module.mem_annihilator]
    intro v
    refine Subtype.ext ?_
    exact smul_eq_zero_of_idealPowerMultiple_kernel_eq_bot hker U hs
      ((hau _).symm.trans (LinearMap.mem_ker.mp v.property))
  have hQ : K.ideal U ^ t ≤ Module.annihilator Γ(X, U.1)
      (Γ(N, U.1) ⧸ LinearMap.range au) := by
    intro s hs
    rw [Module.mem_annihilator]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨v, hv⟩ := smul_mem_range_app_of_idealPowerMultiple_cokernel_eq_bot hcok U hs y
    rw [← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (LinearMap.mem_range.mpr ⟨v, (hau v).trans hv⟩)
  have hmain := Ideal.pow_le_annihilator_ker_mapQ_of_exact
    (LinearMap.ker au).subtype au (LinearMap.range au).mkQ (Submodule.injective_subtype _)
    (LinearMap.exact_subtype_ker_map _) (LinearMap.exact_map_mkQ_range _)
    (Submodule.mkQ_surjective _) (K.ideal U) t ht hT hQ (J.ideal U ^ m)
  have hax : au x ∈ J.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(N, U.1)) := by
    rw [hau x]
    refine (cokernel_π_idealPowerMultiple_app_eq_zero_iff J m N U _).mp ?_
    have h1 := congrArg (fun k : M ⟶ idealPowerQuotient J m N => k.app U.1 x)
      (idealPowerQuotientMap_π J J m m le_rfl a)
    have h2 : (idealPowerQuotientMap J J m m le_rfl a).app U.1
        ((cokernel.π (C := X.Modules) (idealPowerMultiple J m M).ι).app U.1 x) = 0 := by
      rwa [hx]
    exact h1.symm.trans h2
  have hmem : (Submodule.Quotient.mk x :
      Γ(M, U.1) ⧸ (J.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)))) ∈
      LinearMap.ker (Submodule.mapQ
        (J.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)))
        (J.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(N, U.1))) au
        (Submodule.smul_top_le_comap_smul_top _ _)) := by
    rw [LinearMap.mem_ker, Submodule.mapQ_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hax
  have hzero := congrArg Subtype.val (Module.mem_annihilator.mp (hmain hr) ⟨_, hmem⟩)
  have hrx : r • x ∈ J.ideal U ^ m • (⊤ : Submodule Γ(X, U.1) Γ(M, U.1)) := by
    refine (Submodule.Quotient.mk_eq_zero _).mp ?_
    rw [Submodule.Quotient.mk_smul]
    simpa using hzero
  rw [← hx, ← Scheme.Modules.Hom.app_smul]
  exact (cokernel_π_idealPowerMultiple_app_eq_zero_iff J m M U _).mpr hrx

/-- **The remark of Tag 0888, kernel half.** If `𝒦 ᵗ` annihilates the kernel and the cokernel of a
morphism `a : M ⟶ N` of quasi-coherent modules, then `𝒦 ²ᵗ` annihilates the kernel of the
reduction `M / 𝒥 ᵐ M ⟶ N / 𝒥 ᵐ N` of `a` modulo any power of any quasi-coherent ideal sheaf.

The inclusion of the kernel is injective on the sections over an affine open
(`Stacks.SheafOfModules.injective_app_kernel_ι`), so the statement reduces to
`Stacks.Algebraization.smul_eq_zero_of_app_idealPowerQuotientMap_eq_zero` for the image of a
section of the kernel. -/
public theorem idealPowerMultiple_kernel_idealPowerQuotientMap_eq_bot
    (K J : X.IdealSheafData) (m : ℕ) {t : ℕ} (ht : 0 < t) {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (a : M ⟶ N)
    (hker : idealPowerMultiple K t (kernel (C := X.Modules) a) = ⊥)
    (hcok : idealPowerMultiple K t (cokernel (C := X.Modules) a) = ⊥) :
    idealPowerMultiple K (2 * t) (kernel (C := X.Modules)
      (idealPowerQuotientMap J J m m le_rfl a)) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U r hr z => ?_
  have hw : (idealPowerQuotientMap J J m m le_rfl a).app U.1
      ((kernel.ι (C := X.Modules) (idealPowerQuotientMap J J m m le_rfl a)).app U.1 z) = 0 :=
    congrArg (fun k : kernel (C := X.Modules)
        (idealPowerQuotientMap J J m m le_rfl a) ⟶ idealPowerQuotient J m N => k.app U.1 z)
      (kernel.condition (C := X.Modules) (idealPowerQuotientMap J J m m le_rfl a))
  refine Stacks.AlgebraicGeometry.QcohLimits.injective_app_kernel_ι _ U.1 ?_
  rw [Scheme.Modules.Hom.app_smul, map_zero]
  exact smul_eq_zero_of_app_idealPowerQuotientMap_eq_zero K J m ht hker hcok U hr hw

/-! ### The reduction of a morphism of systems modulo a power of a second ideal -/

/-- **The first application of the remark of Tag 0888 in the proof of Tag 088A.** Let
`α : (F_n) ⟶ (G_n)` be a morphism of inverse systems of quasi-coherent modules whose levelwise
kernels and cokernels are annihilated by `𝒦 ᵗ`. Then the levelwise kernels and cokernels of the
reduction `(F_n / 𝒥 ᵉ F_n) ⟶ (G_n / 𝒥 ᵉ G_n)` are annihilated by `𝒦 ²ᵗ`.

This is the source's step from `𝒦 ᵗ` annihilating the kernel and cokernel of `F_n ⟶ 𝓗 / ℐ ⁿ 𝓗` to
`𝒦 ²ᵗ` annihilating those of `F_n / 𝒦 ᵉ F_n ⟶ 𝓗 / (ℐ ⁿ + 𝒦 ᵉ) 𝓗`, applied one level at a time:
the reduction of the system is the composite of the system with
`Stacks.Algebraization.idealPowerQuotientFunctor`, so its component at `n` is the reduction of
`α_n`. -/
public theorem isKernelCokernelAnnihilatedByPower_whiskerRight_idealPowerQuotientFunctor
    (K J : X.IdealSheafData) (e : ℕ) {F G : ℕᵒᵖ ⥤ X.Modules}
    (hF : ∀ n : ℕ, (F.obj (op n)).IsQuasicoherent)
    (hG : ∀ n : ℕ, (G.obj (op n)).IsQuasicoherent)
    {α : F ⟶ G} (hα : IsKernelCokernelAnnihilatedByPower K α) :
    IsKernelCokernelAnnihilatedByPower K
      (Functor.whiskerRight α (idealPowerQuotientFunctor J e)) := by
  obtain ⟨t, ht, h⟩ := hα
  refine ⟨2 * t, by omega, fun k => ?_⟩
  have _ := hF k
  have _ := hG k
  exact ⟨idealPowerMultiple_kernel_idealPowerQuotientMap_eq_bot K J e ht (α.app (op k))
      (h k).1 (h k).2,
    idealPowerMultiple_eq_bot_of_le
      (idealPowerMultiple_cokernel_idealPowerQuotientMap_eq_bot K J e (α.app (op k)) (h k).2)
      (by omega)⟩

/-! ### Descending annihilation from the completion to the map itself -/

/-- The image of `ℐ(U) ⁿ Γ(M, U)` under a morphism lies in `ℐ(U) ⁿ Γ(N, U)`. -/
public theorem app_mem_pow_smul_top {I : X.IdealSheafData} {n : ℕ} {M N : X.Modules}
    (f : M ⟶ N) (U : X.affineOpens) {x : Γ(M, U)}
    (hx : x ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U))) :
    f.app U.1 x ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(N, U)) := by
  refine Submodule.smul_induction_on hx (fun c hc y _ => ?_) (fun y y' hy hy' => ?_)
  · rw [Scheme.Modules.Hom.app_smul]
    exact Submodule.smul_mem_smul hc Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hy hy'

/-- **The kernel of a map of quasi-coherent modules, from the kernels of its reductions.** Let
`a : G ⟶ P` be a morphism of quasi-coherent modules and suppose `𝒦 ˢ` annihilates the kernel of
every reduction `G / ℐ ⁿ G ⟶ P / ℐ ⁿ P`. If `G` is `ℐ`-adically separated on the sections over
every affine open, then `𝒦 ˢ` annihilates the kernel of `a` itself.

This is the shape of the step the proof of Tag 088A takes when it passes from the annihilation of
the kernels of the maps `𝒢_e / ℐ ⁿ 𝒢_e ⟶ 𝓗 / (ℐ ⁿ + 𝒦 ᵉ) 𝓗` to the annihilation of the kernel of
`𝒢_e ⟶ 𝓗 / 𝒦 ᵉ 𝓗`, with affine-local separatedness as the hypothesis that makes it legitimate.

Separatedness in that form is **not** available in the situation of Tag 088A, and hypothesis (1)
of that tag does not supply it: for `X = Spec k[[t]]`, `ℐ = (t)`, `𝒦 = 0` and `G = 𝒪_X` the
functor of hypothesis (1) is an equivalence, while over the affine open `D(t)` the ideal of `ℐ` is
the unit ideal, so the sections of `ℐ ⁿ G` over `D(t)` are all of `k((t))` and no nonzero section
there is separated away. What hypothesis (1) does give is a *global* vanishing criterion: a
morphism of coherent modules annihilated by a power of `𝒦` which dies in every term of the
`ℐ`-adic completion of its target is zero. -/
public theorem idealPowerMultiple_kernel_eq_bot_of_reductions
    (K I : X.IdealSheafData) {s : ℕ} {G P : X.Modules}
    [G.IsQuasicoherent] [P.IsQuasicoherent] (a : G ⟶ P)
    (hsep : ∀ (U : X.affineOpens) (x : Γ(G, U)),
      (∀ n : ℕ, x ∈ I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(G, U))) → x = 0)
    (hker : ∀ n : ℕ, idealPowerMultiple K s
      (kernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a)) = ⊥) :
    idealPowerMultiple K s (kernel (C := X.Modules) a) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U r hr z => ?_
  refine Stacks.AlgebraicGeometry.QcohLimits.injective_app_kernel_ι _ U.1 ?_
  rw [Scheme.Modules.Hom.app_smul, map_zero]
  set v := (kernel.ι (C := X.Modules) a).app U.1 z
  have hav : a.app U.1 v = 0 :=
    congrArg (fun k : kernel (C := X.Modules) a ⟶ P => k.app U.1 z)
      (kernel.condition (C := X.Modules) a)
  refine hsep U (r • v) fun n => ?_
  refine (cokernel_π_idealPowerMultiple_app_eq_zero_iff I n G U _).mp ?_
  rw [Scheme.Modules.Hom.app_smul]
  have hmem : (idealPowerQuotientMap I I n n le_rfl a).app U.1
      ((cokernel.π (C := X.Modules) (idealPowerMultiple I n G).ι).app U.1 v) = 0 := by
    have h1 := congrArg (fun k : G ⟶ idealPowerQuotient I n P => k.app U.1 v)
      (idealPowerQuotientMap_π I I n n le_rfl a)
    have h2 : (cokernel.π (C := X.Modules) (idealPowerMultiple I n P).ι).app U.1
        (a.app U.1 v) = 0 := by rw [hav, map_zero]
    exact h1.trans h2
  obtain ⟨y, hy⟩ := exists_kernel_section (idealPowerQuotientMap I I n n le_rfl a) U.1
    ((cokernel.π (C := X.Modules) (idealPowerMultiple I n G).ι).app U.1 v) hmem
  calc r • (cokernel.π (C := X.Modules) (idealPowerMultiple I n G).ι).app U.1 v
      = r • (kernel.ι (C := X.Modules)
          (idealPowerQuotientMap I I n n le_rfl a)).app U.1 y := by rw [hy]
    _ = (kernel.ι (C := X.Modules)
          (idealPowerQuotientMap I I n n le_rfl a)).app U.1 (r • y) :=
        (Scheme.Modules.Hom.app_smul _ r y).symm
    _ = 0 := by
        rw [affine_sections_annihilated_of_idealPowerMultiple_eq_bot (hker n) U hr y, map_zero]

/-- **The cokernel of a map of quasi-coherent modules, from the cokernels of its reductions.** Let
`a : G ⟶ P` be a morphism of quasi-coherent modules and suppose `𝒦 ˢ` annihilates the cokernel of
every reduction `G / ℐ ⁿ G ⟶ P / ℐ ⁿ P`. If `Coker(a)` is `ℐ`-adically separated on the sections
over every affine open, then `𝒦 ˢ` annihilates `Coker(a)`.

The companion of `Stacks.Algebraization.idealPowerMultiple_kernel_eq_bot_of_reductions`; the same
step of the proof of Tag 088A, for the cokernel. -/
public theorem idealPowerMultiple_cokernel_eq_bot_of_reductions
    (K I : X.IdealSheafData) {s : ℕ} {G P : X.Modules}
    [G.IsQuasicoherent] [P.IsQuasicoherent] (a : G ⟶ P)
    (hsep : ∀ (U : X.affineOpens) (x : Γ(cokernel (C := X.Modules) a, U)),
      (∀ n : ℕ, x ∈ I.ideal U ^ n •
        (⊤ : Submodule Γ(X, U) Γ(cokernel (C := X.Modules) a, U))) → x = 0)
    (hcok : ∀ n : ℕ, idealPowerMultiple K s
      (cokernel (C := X.Modules) (idealPowerQuotientMap I I n n le_rfl a)) = ⊥) :
    idealPowerMultiple K s (cokernel (C := X.Modules) a) = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U r hr y => ?_
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Γ(P, U.1), (cokernel.π (C := X.Modules) a).app U.1 y₀ = y :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
      (cokernel.π (C := X.Modules) a) U.1 U.2 y
  refine hsep U (r • y) fun n => ?_
  obtain ⟨z, hz⟩ := smul_mem_range_app_of_idealPowerMultiple_cokernel_eq_bot (hcok n) U hr
    ((cokernel.π (C := X.Modules) (idealPowerMultiple I n P).ι).app U.1 y₀)
  obtain ⟨w, hw⟩ : ∃ w : Γ(G, U.1),
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n G).ι).app U.1 w = z :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X
      (cokernel.π (C := X.Modules) (idealPowerMultiple I n G).ι) U.1 U.2 z
  have hdiff : r • y₀ - a.app U.1 w ∈
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(P, U.1)) := by
    refine (cokernel_π_idealPowerMultiple_app_eq_zero_iff I n P U _).mp ?_
    rw [map_sub, Scheme.Modules.Hom.app_smul, sub_eq_zero]
    have h1 := congrArg (fun k : G ⟶ idealPowerQuotient I n P => k.app U.1 w)
      (idealPowerQuotientMap_π I I n n le_rfl a)
    refine Eq.symm (h1.symm.trans ?_)
    change (idealPowerQuotientMap I I n n le_rfl a).app U.1
      ((cokernel.π (C := X.Modules) (idealPowerMultiple I n G).ι).app U.1 w) = _
    rw [hw]
    exact hz
  have himg := app_mem_pow_smul_top (I := I) (n := n) (cokernel.π (C := X.Modules) a) U hdiff
  have hzero : (cokernel.π (C := X.Modules) a).app U.1 (a.app U.1 w) = 0 :=
    congrArg (fun k : G ⟶ cokernel (C := X.Modules) a => k.app U.1 w)
      (cokernel.condition (C := X.Modules) a)
  rwa [map_sub, hzero, sub_zero, Scheme.Modules.Hom.app_smul, hy₀] at himg

end Stacks.Algebraization

end
