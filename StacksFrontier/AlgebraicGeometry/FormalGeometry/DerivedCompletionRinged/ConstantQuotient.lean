module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Annihilator
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafCompletion
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.ConstantCoefficients
import StacksCore.Tactic.StacksAttribute

/-!
# The quotient of a constant sheaf of rings by a constant ideal

Let `(𝒞, Λ̲)` be the constant ringed site of a commutative ring `Λ` and let `I ⊂ Λ` be an
ideal, with `IΛ̲ ⊂ Λ̲` the sheaf of ideals it generates. This file proves two facts relating
`IΛ̲` to constant sheaves of modules.

* Every section of `IΛ̲` kills the constant sheaf `M̲` of a `Λ`-module `M` killed by `I`. The
  global sections `a̲`, `a ∈ I`, generating `IΛ̲` act on `M̲` as the constant sheaf of the
  multiplication by `a`, which is zero; and the sections of `Λ̲` annihilating `M̲` form a sheaf
  of ideals, `SheafOfModules.annihilator`, so it contains all of `IΛ̲`.
* When `I` is finitely generated, `Λ̲/IΛ̲ = (Λ/I)̲`: the cokernel of the inclusion `IΛ̲ ⟶ Λ̲`
  is the constant sheaf of `Λ/I`, compatibly with the projections from `Λ̲`. With generators
  `g_1, …, g_r` of `I`, the sequence `Λʳ ⟶ Λ ⟶ Λ/I ⟶ 0` is exact and the constant sheaf of
  modules functor is right exact, so `(Λ/I)̲` is the cokernel of `⊕ Λ̲ ⟶ Λ̲`, whose components
  are the multiplications by the `g̲_k`; these land in `IΛ̲`, and `IΛ̲` dies in `(Λ/I)̲` by the
  first point.

## Main definitions

* `Stacks.ConstantSheaf.adicQuotientSystemShortComplex`: the short exact sequence
  `0 → Iⁿ/Iⁿ⁺¹ → Λ/Iⁿ⁺¹ → Λ/Iⁿ → 0` of `Λ`-modules.
* `AlgebraicGeometry.RingedSite.constantReduction`: the reduction `Λ̲ ⟶ (Λ/I)̲`.
* `AlgebraicGeometry.RingedSite.constantQuotientIso`: `Λ̲/IΛ̲ ≅ (Λ/I)̲`.

## Main results

* `AlgebraicGeometry.RingedSite.constantIdealSheaf_le_annihilator`: `IΛ̲` annihilates the
  constant sheaf of every `Λ`-module killed by `I`.
* `AlgebraicGeometry.RingedSite.pow_mem_annihilator_of_mem_constantIdealSheaf`: the `m`-th power
  of a local section of `IΛ̲` annihilates the constant sheaf of every module killed by `Iᵐ`.
* `AlgebraicGeometry.RingedSite.idealGeneratorsMap_val_app_mem`: the image of `⊕ Λ̲ ⟶ Λ̲`, for
  generators `g_k` of `I`, consists sectionwise of combinations of the `g̲_k`.
* `AlgebraicGeometry.RingedSite.cokernelπ_comp_constantQuotientIso_hom`: the isomorphism carries
  the projection `Λ̲ ⟶ Λ̲/IΛ̲` to the reduction.

## Implementation notes

The universes are diagonal, as for `AlgebraicGeometry.RingedSite.constant`.

## References

* [Stacks Project, Tag 093M](https://stacks.math.columbia.edu/tag/093M)
* [Stacks Project, Tag 099Q](https://stacks.math.columbia.edu/tag/099Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

universe u

namespace Stacks.ConstantSheaf

variable {Λ : Type u} [CommRing Λ] (I : Ideal Λ) (n : ℕ)

/-- The short exact sequence `0 ⟶ Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ ⟶ 0` of `Λ`-modules, the graded
piece being the kernel of the transition map of the tower
`Stacks.ConstantSheaf.adicQuotientSystem`. -/
def adicQuotientSystemShortComplex : ShortComplex (ModuleCat.{u} Λ) :=
  ShortComplex.mk
    (ModuleCat.ofHom (LinearMap.ker ((adicQuotientSystem I).map
      (homOfLE (Nat.le_succ n)).op).hom).subtype)
    ((adicQuotientSystem I).map (homOfLE (Nat.le_succ n)).op) (by ext x; exact x.2)

/-- The sequence `0 ⟶ Iⁿ/Iⁿ⁺¹ ⟶ Λ/Iⁿ⁺¹ ⟶ Λ/Iⁿ ⟶ 0` is short exact. -/
theorem adicQuotientSystemShortComplex_shortExact :
    (adicQuotientSystemShortComplex I n).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).2 (Submodule.range_subtype _)
  mono_f := (ModuleCat.mono_iff_injective _).2 Subtype.val_injective
  epi_g := (ModuleCat.epi_iff_surjective _).2 fun y => by
    induction y using Submodule.Quotient.induction_on with
    | H y => exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- **The graded piece `Iⁿ/Iⁿ⁺¹` is killed by `I`.** -/
theorem smul_adicQuotientSystemShortComplex_X₁ {a : Λ} (ha : a ∈ I)
    (m : (adicQuotientSystemShortComplex I n).X₁) : a • m = 0 := by
  obtain ⟨m, hm⟩ := m
  induction m using Submodule.Quotient.induction_on with
  | H y =>
    have hy : y ∈ I ^ n := by
      change Submodule.Quotient.mk (p := I ^ n) y = 0 at hm
      exact (Submodule.Quotient.mk_eq_zero _).1 hm
    apply Subtype.ext
    show a • Submodule.Quotient.mk (p := I ^ (n + 1)) y = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, pow_succ']
    exact Ideal.mul_mem_mul ha hy

/-- The first term `Λ/I⁰` of the tower is zero. -/
theorem isZero_adicQuotientSystem_obj_zero :
    IsZero ((adicQuotientSystem I).obj (op 0)) := by
  have : Subsingleton (Λ ⧸ I ^ 0) := by
    rw [pow_zero, Ideal.one_eq_top]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton (ModuleCat.of Λ (Λ ⧸ I ^ 0))

/-- The term `Λ/Iⁿ` of the tower is killed by `Iⁿ`. -/
theorem smul_adicQuotientSystem_obj {a : Λ} (ha : a ∈ I ^ n)
    (m : (adicQuotientSystem I).obj (op n)) : a • m = 0 := by
  change Λ ⧸ I ^ n at m
  induction m using Submodule.Quotient.induction_on with
  | H y =>
    show a • Submodule.Quotient.mk (p := I ^ n) y = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Ideal.mul_mem_right y _ ha

end Stacks.ConstantSheaf

namespace AlgebraicGeometry.RingedSite

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (Λ : Type u) [CommRing Λ]

section Annihilation

/-- **`IΛ̲` annihilates the constant sheaf of a module killed by `I`.** Each generator `a̲`,
`a ∈ I`, acts on `M̲` as the constant sheaf of multiplication by `a`, which is zero, and the
sections of `Λ̲` annihilating `M̲` form a sheaf of ideals. -/
theorem constantIdealSheaf_le_annihilator {I : Ideal Λ} (M : ModuleCat.{u} Λ)
    (hM : ∀ a ∈ I, ∀ m : M, a • m = 0) :
    constantIdealSheaf J Λ I ≤
      SheafOfModules.annihilator ((constantModuleFunctor J Λ).obj M) := by
  refine SheafOfModules.Submodule.generatedBy_le _ _ fun p W g y => ?_
  have h1 : (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.map g
      (constantSectionRingHom J Λ p.2 p.1) = constantSectionRingHom J Λ W p.1 :=
    (constantSection J Λ p.1).property g
  have h0 : ((p.1 : Λ) • 𝟙 M) = 0 := by
    ext m
    exact hM _ p.1.2 m
  have h2 := constantModuleFunctor_map_smul J Λ M p.1
  rw [h0, Functor.map_zero] at h2
  have h3 := congr_arg (fun f => f.val.app W y) h2
  change (0 : _) = constantSectionRingHom J Λ W p.1 • y at h3
  show (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.map g
      (constantSectionRingHom J Λ p.2 p.1) • y = 0
  rw [h1, ← h3]

/-- A section of `IΛ̲` kills every section of the constant sheaf of a module killed by `I`. -/
theorem smul_eq_zero_of_mem_constantIdealSheaf {I : Ideal Λ} (M : ModuleCat.{u} Λ)
    (hM : ∀ a ∈ I, ∀ m : M, a • m = 0) {U : Cᵒᵖ}
    {c : (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj U}
    (hc : c ∈ (constantIdealSheaf J Λ I).obj U)
    (y : ((constantModuleFunctor J Λ).obj M).val.obj U) : c • y = 0 :=
  SheafOfModules.smul_eq_zero_of_mem_annihilator _
    (constantIdealSheaf_le_annihilator J Λ M hM U hc) y

/-- The rings of sections of the structure sheaf `Λ̲` are commutative. -/
private theorem isMulCommutative_ringSheaf_obj (U : Cᵒᵖ) :
    IsMulCommutative ((Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj U) := by
  change IsMulCommutative ((constant J Λ).O.obj.obj U)
  infer_instance

/-- The image of an element `a ∈ I` in the sections of `Λ̲` over `U` lies in `IΛ̲`. -/
private theorem constantSectionRingHom_mem_constantIdealSheaf {I : Ideal Λ} {a : Λ} (ha : a ∈ I)
    (U : Cᵒᵖ) : constantSectionRingHom J Λ U a ∈ (constantIdealSheaf J Λ I).obj U :=
  SheafOfModules.Submodule.mem_generatedBy
    (F := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O))
    (fun p : I × Cᵒᵖ => p.2) (fun p => constantSectionRingHom J Λ p.2 p.1) (⟨a, ha⟩, U)

/-- **A local section of `IΛ̲` has its `m`-th power in the annihilator of `M̲`** whenever `Iᵐ`
kills `M`, for a finitely generated `I`. Locally the section is a combination of the generators
`g̲_k` of `IΛ̲`, so its `m`-th power is locally a section of `IᵐΛ̲`, which annihilates `M̲`; and
the annihilator is a sheaf of ideals. -/
theorem pow_mem_annihilator_of_mem_constantIdealSheaf {I : Ideal Λ} (hI : I.FG)
    (M : ModuleCat.{u} Λ) (m : ℕ) (hM : ∀ a ∈ I ^ m, ∀ x : M, a • x = 0) {U : Cᵒᵖ}
    {f : (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj U}
    (hf : f ∈ (constantIdealSheaf J Λ I).obj U) :
    f ^ m ∈ (SheafOfModules.annihilator ((constantModuleFunctor J Λ).obj M)).obj U := by
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hI
  have hf' : f ∈ (idealOfGlobalSections (constant J Λ)
      (fun i => constantGlobalSection J Λ (g i))).toSubmodule.obj U := by
    rwa [← constantIdealSheaf_eq_idealOfGlobalSections J Λ I g hg]
  obtain ⟨S, hS, hloc⟩ := (mem_idealOfGlobalSections_iff (constant J Λ)
    (fun i => constantGlobalSection J Λ (g i)) U).1 hf'
  let N := (constantModuleFunctor J Λ).obj M
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O
  refine SheafOfModules.mem_annihilatorObj_of_locally (R := R) N (f ^ m) hS fun Y h hh => ?_
  have := isMulCommutative_ringSheaf_obj J Λ (op Y)
  let φ := constantSectionRingHom J Λ (op Y)
  have hspan : Ideal.span (Set.range (restrictGlobalSections (constant J Λ)
      (fun i => constantGlobalSection J Λ (g i)) (op Y))) = Ideal.map φ I := by
    rw [← hg, Ideal.map_span, ← Set.range_comp]
    congr 2
  have h2 : (R.obj.map h.op f) ^ m ∈ Ideal.map φ (I ^ m) := by
    rw [Ideal.map_pow]
    exact Ideal.pow_mem_pow (by rw [← hspan]; exact hloc h hh) m
  rw [map_pow]
  refine (Ideal.map_le_iff_le_comap.2 fun a ha => ?_) h2
  exact constantIdealSheaf_le_annihilator J Λ M hM (op Y)
    (constantSectionRingHom_mem_constantIdealSheaf J Λ ha (op Y))

end Annihilation

section Quotient

/-- **The reduction `Λ̲ ⟶ (Λ/I)̲`**, the constant sheaf of the quotient map, read through the
identification of `Λ̲` with the constant sheaf of modules on `Λ`. -/
def constantReduction (I : Ideal Λ) :
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O) ⟶
      (constantModuleFunctor J Λ).obj (ModuleCat.of Λ (Λ ⧸ I)) :=
  (constantModuleFunctorUnitIso J Λ).inv ≫
    (constantModuleFunctor J Λ).map (ModuleCat.ofHom (Submodule.mkQ I))

/-- **`IΛ̲` dies in `(Λ/I)̲`.** A section `c` of `IΛ̲` is sent to `c` times the image of `1`,
and `c` annihilates `(Λ/I)̲`. -/
theorem constantIdealSheaf_ι_comp_constantReduction (I : Ideal Λ) :
    (constantIdealSheaf J Λ I).ι ≫ constantReduction J Λ I = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj U
  have hQ : ∀ a ∈ I, ∀ m : ModuleCat.of Λ (Λ ⧸ I), a • m = 0 := fun a ha m => by
    induction m using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact I.mul_mem_right m ha
  have key : ∀ y : R, y ∈ (constantIdealSheaf J Λ I).obj U →
      (constantReduction J Λ I).val.app U y = 0 := fun y hy => by
    have h := ((constantReduction J Λ I).val.app U).hom.map_smul y (1 : R)
    refine Eq.trans ?_ (h.trans (smul_eq_zero_of_mem_constantIdealSheaf J Λ _ hQ hy _))
    exact congrArg ((constantReduction J Λ I).val.app U).hom (mul_one y).symm
  exact key x.1 x.2

/-- Multiplication by `a̲`, for `a ∈ I`, followed by the projection `Λ̲ ⟶ Λ̲/IΛ̲`, vanishes:
`a̲` and its multiples are sections of `IΛ̲`. -/
theorem globalSectionToEnd_comp_cokernelπ {I : Ideal Λ} {a : Λ} (ha : a ∈ I) :
    (Stacks.SheafOfModules.globalSectionToEnd _ (constantSection J Λ a)).asHom.app
        (SheafOfModules.unit _) ≫ cokernel.π (constantIdealSheaf J Λ I).ι = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  let R := (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj U
  have := isMulCommutative_ringSheaf_obj J Λ U
  have hmem := constantSectionRingHom_mem_constantIdealSheaf J Λ ha U
  have key : ∀ x : R, constantSectionRingHom J Λ U a * x ∈ (constantIdealSheaf J Λ I).obj U :=
    fun x => by
      have := (constantIdealSheaf J Λ I).obj U |>.smul_mem x hmem
      have e : x • constantSectionRingHom J Λ U a = constantSectionRingHom J Λ U a * x :=
        (smul_eq_mul (α := R) _ _).trans (mul_comm _ _)
      exact e ▸ this
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show (cokernel.π (constantIdealSheaf J Λ I).ι).val.app U
    ((constantIdealSheaf J Λ I).ι.val.app U ⟨_, key x⟩) = 0
  exact Stacks.SheafOfModules.val_app_apply_eq_zero _ _ (cokernel.condition _) U _

/-- The map `Λʳ ⟶ Λ` of a finite family of elements `g_1, …, g_r` of `Λ`. -/
abbrev idealGeneratorsMap {r : ℕ} (g : Fin r → Λ) :
    (⨁ fun _ : Fin r => ModuleCat.of Λ Λ) ⟶ ModuleCat.of Λ Λ :=
  biproduct.desc fun k => g k • 𝟙 (ModuleCat.of Λ Λ)

/-- For generators `g_1, …, g_r` of `I`, the composite of `Λʳ ⟶ Λ` with the quotient map
`Λ ⟶ Λ/I` is zero. -/
theorem idealGeneratorsMap_comp_mkQ {r : ℕ} (g : Fin r → Λ) (I : Ideal Λ)
    (hg : Ideal.span (Set.range g) = I) :
    idealGeneratorsMap Λ g ≫ ModuleCat.ofHom (Submodule.mkQ I) = 0 := by
  refine biproduct.hom_ext' _ _ fun k => ?_
  rw [biproduct.ι_desc_assoc, comp_zero]
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show Submodule.mkQ I (g k • x) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact I.mul_mem_right x (hg ▸ Ideal.subset_span ⟨k, rfl⟩)

/-- For generators `g_1, …, g_r` of `I`, the quotient map `Λ ⟶ Λ/I` is a cokernel of `Λʳ ⟶ Λ`. -/
def isColimitIdealGeneratorsMapCokernelCofork {r : ℕ} (g : Fin r → Λ) (I : Ideal Λ)
    (hg : Ideal.span (Set.range g) = I) :
    IsColimit (CokernelCofork.ofπ (f := idealGeneratorsMap Λ g) (ModuleCat.ofHom (Submodule.mkQ I))
      (idealGeneratorsMap_comp_mkQ Λ g I hg)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun h hh => ModuleCat.ofHom (Submodule.liftQ I h.hom (by
      rw [← hg, Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      have h1 := congrArg (fun φ => φ.hom (1 : Λ)) (biproduct.ι _ k ≫= hh)
      rw [biproduct.ι_desc_assoc, comp_zero] at h1
      change h.hom (g k • (1 : Λ)) = 0 at h1
      rwa [smul_eq_mul, mul_one] at h1)))
    (fun h hh => ModuleCat.hom_ext (Submodule.liftQ_mkQ _ _ _))
    (fun h hh m hm => by
      have : Epi (ModuleCat.ofHom (Submodule.mkQ I)) :=
        (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective I)
      rw [← cancel_epi (ModuleCat.ofHom (Submodule.mkQ I)), hm]
      exact ModuleCat.hom_ext (Submodule.liftQ_mkQ _ _ _).symm)

/-- The constant sheaf of `Λʳ ⟶ Λ`, followed by the projection `Λ̲ ⟶ Λ̲/IΛ̲`, vanishes when the
`g_k` lie in `I`. -/
theorem constantModuleFunctor_map_idealGeneratorsMap_comp {r : ℕ} (g : Fin r → Λ)
    (I : Ideal Λ) (hg : Ideal.span (Set.range g) = I) :
    (constantModuleFunctor J Λ).map (idealGeneratorsMap Λ g) ≫
      (constantModuleFunctorUnitIso J Λ).hom ≫
      cokernel.π (constantIdealSheaf J Λ I).ι = 0 := by
  let F := constantModuleFunctor J Λ
  rw [← cancel_epi (F.mapBiproduct fun _ : Fin r => ModuleCat.of Λ Λ).inv, comp_zero]
  refine biproduct.hom_ext' _ _ fun k => ?_
  rw [comp_zero, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc, ← Functor.map_comp_assoc,
    biproduct.ι_desc, ← Category.assoc, constantModuleFunctor_map_smul_unitIso, Category.assoc,
    globalSectionToEnd_comp_cokernelπ J Λ (hg ▸ Ideal.subset_span ⟨k, rfl⟩), comp_zero]

/-- The constant sheaf of the quotient map `Λ ⟶ Λ/I` is a cokernel of the constant sheaf of
`Λʳ ⟶ Λ`, for generators `g_1, …, g_r` of `I`: the constant sheaf of modules functor is right
exact. -/
def isColimitConstantModuleFunctorMapMkQ {I : Ideal Λ} {r : ℕ} (g : Fin r → Λ)
    (hg : Ideal.span (Set.range g) = I) :
    IsColimit (CokernelCofork.ofπ (f := (constantModuleFunctor J Λ).map (idealGeneratorsMap Λ g))
      ((constantModuleFunctor J Λ).map (ModuleCat.ofHom (Submodule.mkQ I)))
      (by rw [← Functor.map_comp, idealGeneratorsMap_comp_mkQ Λ g I hg, Functor.map_zero])) :=
  isColimitCoforkMapOfIsColimit' (constantModuleFunctor J Λ)
    (idealGeneratorsMap_comp_mkQ Λ g I hg) (isColimitIdealGeneratorsMapCokernelCofork Λ g I hg)

private theorem constantModuleFunctor_map_mkQ_comp_desc {I : Ideal Λ} {r : ℕ} (g : Fin r → Λ)
    (hg : Ideal.span (Set.range g) = I) :
    (constantModuleFunctor J Λ).map (ModuleCat.ofHom (Submodule.mkQ I)) ≫
      (isColimitConstantModuleFunctorMapMkQ J Λ g hg).desc
        (CokernelCofork.ofπ ((constantModuleFunctorUnitIso J Λ).hom ≫
          cokernel.π (constantIdealSheaf J Λ I).ι)
          (constantModuleFunctor_map_idealGeneratorsMap_comp J Λ g I hg)) =
      (constantModuleFunctorUnitIso J Λ).hom ≫ cokernel.π (constantIdealSheaf J Λ I).ι := by
  have := Cofork.IsColimit.π_desc (isColimitConstantModuleFunctorMapMkQ J Λ g hg)
    (t := CokernelCofork.ofπ
      ((constantModuleFunctorUnitIso J Λ).hom ≫ cokernel.π (constantIdealSheaf J Λ I).ι)
      (constantModuleFunctor_map_idealGeneratorsMap_comp J Λ g I hg))
  simpa only [Cofork.π_ofπ] using this

/-- **`Λ̲/IΛ̲ = (Λ/I)̲`**, for generators `g_1, …, g_r` of `I`: the cokernel of the inclusion of
the sheaf of ideals `IΛ̲` into `Λ̲` is the constant sheaf of `Λ/I`. -/
def constantQuotientIsoOfGenerators {I : Ideal Λ} {r : ℕ} (g : Fin r → Λ)
    (hg : Ideal.span (Set.range g) = I) :
    cokernel (constantIdealSheaf J Λ I).ι ≅
      (constantModuleFunctor J Λ).obj (ModuleCat.of Λ (Λ ⧸ I)) where
  hom := cokernel.desc _ (constantReduction J Λ I)
    (constantIdealSheaf_ι_comp_constantReduction J Λ I)
  inv := (isColimitConstantModuleFunctorMapMkQ J Λ g hg).desc
      (CokernelCofork.ofπ ((constantModuleFunctorUnitIso J Λ).hom ≫
        cokernel.π (constantIdealSheaf J Λ I).ι)
        (constantModuleFunctor_map_idealGeneratorsMap_comp J Λ g I hg))
  hom_inv_id := by
    have := constantModuleFunctor_map_mkQ_comp_desc J Λ g hg
    refine coequalizer.hom_ext ?_
    rw [coequalizer.π, cokernel.π_desc_assoc, Category.comp_id, constantReduction,
      Category.assoc, this, Iso.inv_hom_id_assoc]
  inv_hom_id := by
    have := constantModuleFunctor_map_mkQ_comp_desc J Λ g hg
    refine Cofork.IsColimit.hom_ext (isColimitConstantModuleFunctorMapMkQ J Λ g hg) ?_
    simp only [Cofork.π_ofπ]
    rw [reassoc_of% this, cokernel.π_desc, constantReduction, Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm

/-- **`Λ̲/IΛ̲ = (Λ/I)̲`** for a finitely generated ideal `I ⊂ Λ`: the cokernel of the inclusion of
the sheaf of ideals `IΛ̲` into `Λ̲` is the constant sheaf of `Λ/I`. -/
def constantQuotientIso {I : Ideal Λ} (hI : I.FG) :
    cokernel (constantIdealSheaf J Λ I).ι ≅
      (constantModuleFunctor J Λ).obj (ModuleCat.of Λ (Λ ⧸ I)) :=
  constantQuotientIsoOfGenerators J Λ
    (Submodule.fg_iff_exists_fin_generating_family.1 hI).choose_spec.choose
    (Submodule.fg_iff_exists_fin_generating_family.1 hI).choose_spec.choose_spec

/-- **`Λ̲/IΛ̲ = (Λ/I)̲` carries the projection from `Λ̲` to the reduction.** -/
@[reassoc (attr := simp)]
theorem cokernelπ_comp_constantQuotientIso_hom {I : Ideal Λ} (hI : I.FG) :
    cokernel.π (constantIdealSheaf J Λ I).ι ≫ (constantQuotientIso J Λ hI).hom =
      constantReduction J Λ I := by
  unfold constantQuotientIso constantQuotientIsoOfGenerators
  exact cokernel.π_desc _ _ _

/-- Evaluation of a finite sum of morphisms of sheaves of modules on a section. -/
private theorem sum_val_app_apply {D : Type*} [Category D] {K : GrothendieckTopology D}
    {R : Sheaf K RingCat.{u}} {ι : Type*} (s : Finset ι) {M N : SheafOfModules.{u} R}
    (f : ι → (M ⟶ N)) (X : Dᵒᵖ) (x : M.val.obj X) :
    (∑ i ∈ s, f i).val.app X x = ∑ i ∈ s, (f i).val.app X x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

/-- The constant sheaf of `Λʳ ⟶ Λ` is the sum of the multiplications by the `g̲_k` on the
components. -/
theorem constantModuleFunctor_map_idealGeneratorsMap_comp_unitIso {r : ℕ} (g : Fin r → Λ) :
    (constantModuleFunctor J Λ).map (idealGeneratorsMap Λ g) ≫
        (constantModuleFunctorUnitIso J Λ).hom =
      ∑ k, (constantModuleFunctor J Λ).map (biproduct.π _ k) ≫
        (constantModuleFunctorUnitIso J Λ).hom ≫
          (Stacks.SheafOfModules.globalSectionToEnd _ (constantSection J Λ (g k))).asHom.app
            (SheafOfModules.unit _) := by
  rw [idealGeneratorsMap, biproduct.desc_eq, Functor.map_sum, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Functor.map_comp, Category.assoc, constantModuleFunctor_map_smul_unitIso]

/-- A multiple of `g̲_k` over `U` lies in the ideal of `Γ(U, Λ̲)` generated by the `g̲_k`. -/
theorem globalSectionToEnd_val_app_mem_span {r : ℕ} (g : Fin r → Λ) (U : Cᵒᵖ) (k : Fin r)
    (w : (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)).val.obj U) :
    ((Stacks.SheafOfModules.globalSectionToEnd _ (constantSection J Λ (g k))).asHom.app
          (SheafOfModules.unit _)).val.app U w ∈
      Submodule.span ((Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj U)
        (Set.range fun k => (show (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)).val.obj U from
            constantSectionRingHom J Λ U (g k))) := by
  rw [Stacks.SheafOfModules.globalSectionToEnd_apply, constantSection_val]
  have hcomm := isMulCommutative_ringSheaf_obj J Λ U
  have e : constantSectionRingHom J Λ U (g k) • w =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj U from w) •
        (show (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)).val.obj U from
        constantSectionRingHom J Λ U (g k)) :=
    hcomm.is_comm.comm _ _
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- **The sections of `Λ̲` in the image of `⊕ Λ̲ ⟶ Λ̲` are combinations of the `g̲_k`**, over
every object. -/
theorem idealGeneratorsMap_val_app_mem {r : ℕ} (g : Fin r → Λ) (U : Cᵒᵖ)
    (z : ((constantModuleFunctor J Λ).obj (⨁ fun _ : Fin r => ModuleCat.of Λ Λ)).val.obj U) :
    ((constantModuleFunctor J Λ).map (idealGeneratorsMap Λ g) ≫
      (constantModuleFunctorUnitIso J Λ).hom).val.app U z ∈
      Submodule.span ((Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O).obj.obj U)
        (Set.range fun k => (show (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf (constant J Λ).O)).val.obj U from
            constantSectionRingHom J Λ U (g k))) := by
  rw [constantModuleFunctor_map_idealGeneratorsMap_comp_unitIso, sum_val_app_apply]
  exact Submodule.sum_mem _ fun k _ => globalSectionToEnd_val_app_mem_span J Λ g U k _

end Quotient

end AlgebraicGeometry.RingedSite

end
