module

public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSurjectivityFromDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineDirectImageCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisorSumEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardExactSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallBaseChangeGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.RingTheory.UniversallyExact

/-!
# Right exactness of global sections on quasi-coherent modules

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  Global
sections on the small étale site of `X` are left exact; they are *right exact on quasi-coherent
modules* when every epimorphism of quasi-coherent `𝒪_X`-modules is surjective on global
sections.  This holds as soon as the first cohomology of every quasi-coherent module vanishes,
which is the hypothesis of Stacks 07UY.

This file shows that the property passes to every algebraic space affine over `X`, and that it
computes the global functions of a base change: if `p : X ⟶ Spec A` induces a surjection from
`A` onto the global functions of a quasi-compact `X` with the property, and `A ⟶ A'` is a ring
map, then every global function on `X' = X ×_{Spec A} Spec A'` comes from `A'`, and if `p`
induces a bijection then `A' ⟶ Γ(X', 𝒪_{X'})` is a bijection (Stacks 07V0).

## Main results

* `AlgebraicGeometry.Space.epi_of_surjective_val_app_of_isAffine`: a morphism of modules which
  is surjective on sections over every affine étale chart is an epimorphism.
* `AlgebraicGeometry.Space.surjective_sectionsMap_of_isAffineHom`: right exactness of global
  sections on quasi-coherent modules passes along an affine morphism `X' ⟶ X`.
* `AlgebraicGeometry.Space.exists_eq_sum_smul_of_surjective_sectionsMap`: where global sections
  are right exact on quasi-coherent modules, a global section of a quasi-coherent module which
  lies, on a covering chart, in the span of finitely many global sections is a combination of
  them with global coefficients.
* `AlgebraicGeometry.Space.exists_eq_sum_mul_of_surjective_sectionsMap`: a finite linear system
  in global functions which is solvable on a covering chart is solvable in global functions.
* `CommRingCat.injective_inr_of_isPushout`: in a pushout of commutative rings along a map which
  solves linear systems over its source, the opposite leg is injective.
* `AlgebraicGeometry.Space.surjective_pullbackToGlobalFunctions_of_isPullback`: **the
  surjectivity half of clause (2) of Stacks 07V0** — the global functions of
  `X ×_{Spec A} Spec A'` come from `A'`.
* `AlgebraicGeometry.Space.injective_pullbackToGlobalFunctions_of_isPullback`: **the injectivity
  half of clause (2) of Stacks 07V0** when `A ⟶ Γ(X, 𝒪_X)` is bijective.

## Implementation notes

The hypothesis is surjectivity on global sections rather than vanishing of first cohomology:
the first cohomology of Stacks 07UY is taken at a module universe containing the universe of the
objects of the small étale site, whereas the direct image of modules along a morphism of algebraic
spaces exists only at the universe of the structure rings.

## References

* [Stacks Project, Tag 07UY](https://stacks.math.columbia.edu/tag/07UY)
* [Stacks Project, Tag 07UZ](https://stacks.math.columbia.edu/tag/07UZ)
* [Stacks Project, Tag 07V0](https://stacks.math.columbia.edu/tag/07V0)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
* [Stacks Project, Tag 058K](https://stacks.math.columbia.edu/tag/058K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u m

/-- In a pushout square of commutative rings every element of the corner is a finite sum of
products of an element coming from one side and an element coming from the other. -/
theorem CommRingCat.exists_eq_sum_mul_of_isPushout {A B C D : CommRingCat.{u}} {f : A ⟶ B}
    {g : A ⟶ C} {inl : B ⟶ D} {inr : C ⟶ D} (h : IsPushout f g inl inr) (d : D) :
    ∃ (n : ℕ) (b : Fin n → B) (c : Fin n → C), d = ∑ i, inl (b i) * inr (c i) := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := inl.hom.toAlgebra
  let := inr.hom.toAlgebra
  let : Algebra A D := (f ≫ inl).hom.toAlgebra
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun x =>
    (ConcreteCategory.congr_hom h.w x)
  have : Algebra.IsPushout A B C D := CommRingCat.isPushout_iff_isPushout.1 h
  obtain ⟨z, rfl⟩ := (Algebra.IsPushout.equiv A B C D).surjective d
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    refine ⟨1, fun _ => x, fun _ => y, ?_⟩
    rw [Algebra.IsPushout.equiv_tmul, Fin.sum_univ_one]
    rfl
  | add z w hz hw =>
    obtain ⟨n, b, c, hn⟩ := hz
    obtain ⟨m, b', c', hm⟩ := hw
    refine ⟨n + m, Fin.append b b', Fin.append c c', ?_⟩
    rw [map_add, hn, hm, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

/-- **In a pushout of commutative rings, the second leg is injective as soon as the first map
solves linear systems over its source.**  Let `f : A ⟶ B` be such that every finite system of
linear equations `x i = ∑ j, a i j * y j` with `x i, a i j ∈ A` which has a solution `y` in `B`
already has one in `A`.  Then for every pushout square `B ⟶ D ⟵ C` of `f` along `g : A ⟶ C`
the map `C ⟶ D` is injective. -/
theorem CommRingCat.injective_inr_of_isPushout {A B C D : CommRingCat.{u}} {f : A ⟶ B}
    {g : A ⟶ C} {inl : B ⟶ D} {inr : C ⟶ D} (h : IsPushout f g inl inr)
    (hf : ∀ (n m : ℕ) (x : Fin n → A) (y : Fin m → B) (a : Fin n → Fin m → A),
      (∀ i, f (x i) = ∑ j, f (a i j) * y j) → ∃ z : Fin m → A, ∀ i, x i = ∑ j, a i j * z j) :
    Function.Injective inr := by
  let := f.hom.toAlgebra
  let := g.hom.toAlgebra
  let := inl.hom.toAlgebra
  let := inr.hom.toAlgebra
  let : Algebra A D := (f ≫ inl).hom.toAlgebra
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq fun x =>
    (ConcreteCategory.congr_hom h.w x)
  have : Algebra.IsPushout A B C D := CommRingCat.isPushout_iff_isPushout.1 h
  let f₁ : A →ₗ[A] B := Algebra.linearMap A B
  have h₁ : Function.Injective f₁ := by
    refine (injective_iff_map_eq_zero f₁).2 fun x hx => ?_
    obtain ⟨z, hz⟩ := hf 1 0 (fun _ => x) Fin.elim0 (fun _ => Fin.elim0) fun _ => by
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact hx
    simpa using hz 0
  have hex : Function.Exact f₁ (LinearMap.range f₁).mkQ := LinearMap.exact_map_mkQ_range f₁
  have hrT : Function.Injective (f₁.rTensor C) := by
    have e := (hex.universallyExact_tfae h₁ (Submodule.mkQ_surjective _)).out 3 1
    refine e.mp (fun n m x y a hxy => ?_) C
    obtain ⟨z, hz⟩ := hf n m x y a fun i => by
      rw [show f (x i) = f₁ (x i) from rfl, hxy i]
      exact Finset.sum_congr rfl fun j _ => Algebra.smul_def _ _
    exact ⟨z, fun i => (hz i).trans (Finset.sum_congr rfl fun j _ => (smul_eq_mul _ _).symm)⟩
  intro c c' hcc'
  have key : ∀ c₀ : C, inr c₀ =
      Algebra.IsPushout.equiv A B C D (f₁.rTensor C ((TensorProduct.lid A C).symm c₀)) := by
    intro c₀
    rw [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.IsPushout.equiv_tmul]
    change inr c₀ = inl (f 1) * inr c₀
    rw [map_one, map_one, one_mul]
  rw [key c, key c'] at hcc'
  exact (TensorProduct.lid A C).symm.injective (hrT ((Algebra.IsPushout.equiv A B C D).injective
    hcc'))

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance 5000] SheafOfModules.instAbelian

/-- **A morphism of `𝒪_X`-modules surjective on every affine étale chart is an epimorphism.** -/
theorem epi_of_surjective_val_app_of_isAffine {X : AlgebraicSpaces B S hS}
    {P Q : Modules.{u, m} B S hS X.1 X.2} (g : P ⟶ Q)
    (h : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W)) →
        Function.Surjective (g.val.app (op W))) : Epi g := by
  obtain ⟨Uc, hUc⟩ := exists_isSurjective_chart B S hS X
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective g ⟨fun {U} s => ?_⟩
  refine sieve_mem_of_forall_isAffine_hom B S hS X Uc hUc U _ (fun A hA _ k => ?_)
  exact h A hA (Q.val.map k.op s)

/-- **Right exactness of global sections passes along an affine morphism.** If global sections
are right exact on quasi-coherent `𝒪_X`-modules and `f : X' ⟶ X` is affine, then global sections
are right exact on quasi-coherent `𝒪_{X'}`-modules. -/
theorem surjective_sectionsMap_of_isAffineHom {X X' : AlgebraicSpaces B S hS} (f : X' ⟶ X)
    (hf : IsAffineHom B S hS f.hom)
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g)) :
    ∀ ⦃M N : Modules.{u, u} B S hS X'.1 X'.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g) := by
  intro M N g hg hM hN t
  have hrep := relativelyRepresentable_of_isAffineHom B S hS f hf
  have hepi : Epi ((smallBaseChangeModulePushforward B S hS f hrep).map g) :=
    epi_of_surjective_val_app_of_isAffine B S hS _ fun W hW =>
      surjective_val_app_of_epi_of_isQuasicoherentOnSite g hg hM hN
        ((smallBaseChange B S hS f hrep).obj W)
        (isAffine_smallBaseChange_obj B S hS f hrep hf W hW)
  obtain ⟨s', hs'⟩ := hX _ hepi
    (isQuasicoherentOnSite_smallBaseChangeModulePushforward_of_isAffineHom f hrep hf hM)
    (isQuasicoherentOnSite_smallBaseChangeModulePushforward_of_isAffineHom f hrep hf hN)
    (sectionsSmallBaseChange B S hS f hrep N t)
  obtain ⟨s, rfl⟩ := (bijective_sectionsSmallBaseChange B S hS f hrep M).2 s'
  refine ⟨s, (bijective_sectionsSmallBaseChange B S hS f hrep N).1 ?_⟩
  rwa [← sectionsMap_sectionsSmallBaseChange]


/-- The section `s` of `M` over `V` is the image of `1` under the morphism `𝒪_X ⟶ M` attached
to `s`. -/
private theorem sections_eval_eq_val_app_one {X : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2} (s : M.sections) (V : (SmallEtale B S hS X.1)ᵒᵖ) :
    PresheafOfModules.sections.eval s V = (M.unitHomEquiv.symm s).val.app V
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
          V) := by
  conv_lhs => rw [← M.unitHomEquiv.apply_symm_apply s]
  rfl

/-- The morphism `𝒪_X ⟶ M` attached to a global section `s` sends a function `r` over a chart to
`r • s`. -/
theorem unitHomEquiv_symm_val_app {X : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS X.1 X.2} (s : M.sections) (V : (SmallEtale B S hS X.1)ᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj V)
        :
    (M.unitHomEquiv.symm s).val.app V r = r • PresheafOfModules.sections.eval s V := by
  rw [sections_eval_eq_val_app_one B S hS s V, ← (((M.unitHomEquiv.symm s).val.app V).hom.map_smul r
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj.obj
        V))]
  congr 1
  exact (mul_one r).symm

/-- A finite biproduct of copies of the unit module is quasi-coherent. -/
private theorem isQuasicoherentOnSite_biproduct_unit (X : AlgebraicSpaces B S hS) (n : ℕ) :
    (⨁ fun _ : Fin n => SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
      ).IsQuasicoherentOnSite :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_of_iso
    (biproduct.isoProduct _).symm
    ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_product
      fun _ => SheafOfModules.isQuasicoherentOnSite_unit _)

/-- **Global coefficients for a local linear combination.** Let global sections be right exact on
quasi-coherent `𝒪_X`-modules, let `M` be quasi-coherent, and let `s₁, …, sₙ, t` be global
sections of `M`.  If on a chart `U₀` covering `X` the section `t` is a combination
`∑ rᵢ sᵢ` with coefficients `rᵢ ∈ 𝒪(U₀)`, then `t = ∑ cᵢ sᵢ` for global functions `cᵢ`. -/
theorem exists_eq_sum_smul_of_surjective_sectionsMap {X : AlgebraicSpaces B S hS}
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    {M : Modules.{u, u} B S hS X.1 X.2}
    (hM : M.IsQuasicoherentOnSite) {n : ℕ} (s : Fin n → M.sections) (t : M.sections)
    (U₀ : SmallEtale B S hS X.1)
    (hU₀ : (SmallEtale.topology B S hS X.1).CoversTop fun _ : PUnit.{u + 2} => U₀)
    (r : Fin n → chartRing B S hS X.1 X.2 U₀)
    (ht : PresheafOfModules.sections.eval t (op U₀) =
      ∑ i, r i • PresheafOfModules.sections.eval (s i) (op U₀)) :
    ∃ c : Fin n → (SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).sections,
      ∀ V, PresheafOfModules.sections.eval t V =
        ∑ i, (@id ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1
            X.2).O).obj.obj V)
          (PresheafOfModules.sections.eval (c i) V)) •
          PresheafOfModules.sections.eval (s i) V := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  let ψ : (⨁ fun _ : Fin n => SheafOfModules.unit R) ⟶ M :=
    biproduct.desc fun i => M.unitHomEquiv.symm (s i)
  let g : SheafOfModules.unit R ⟶ M := M.unitHomEquiv.symm t
  have hι : ∀ i, biproduct.ι _ i ≫ ψ = M.unitHomEquiv.symm (s i) := fun i =>
    biproduct.ι_desc _ _
  have hg : g ≫ cokernel.π ψ = 0 := by
    apply (cokernel ψ).unitHomEquiv.injective
    refine hU₀.sections_ext (moduleSetSheaf B S hS X (cokernel ψ)) (fun _ => ?_)
    change (cokernel.π ψ).val.app (op U₀) (g.val.app (op U₀) (1 : R.obj.obj (op U₀))) = 0
    rw [show g.val.app (op U₀) (1 : R.obj.obj (op U₀)) = _ from
      (sections_eval_eq_val_app_one B S hS t _).symm, ht]
    have hx : (∑ i, r i • PresheafOfModules.sections.eval (s i) (op U₀)) =
        ψ.val.app (op U₀) (∑ i, (biproduct.ι (fun _ : Fin n => SheafOfModules.unit R) i).val.app
          (op U₀) (r i)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      refine (unitHomEquiv_symm_val_app B S hS (s i) (op U₀) (r i)).symm.trans ?_
      rw [← hι i]
      rfl
    rw [hx]
    change (ψ ≫ cokernel.π ψ).val.app (op U₀) _ = 0
    rw [cokernel.condition]
    rfl
  have hP := isQuasicoherentOnSite_biproduct_unit B S hS X n
  have hC : (cokernel ψ).IsQuasicoherentOnSite :=
    @isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 _ _ hP hM ψ
  have hK : (Abelian.image ψ).IsQuasicoherentOnSite := by
    have := isClosedUnderKernels_quasicoherentSheaves_smallEtale B S hS X.1 X.2
    exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} R).prop_kernel _ hM hC
  let g' : SheafOfModules.unit R ⟶ Abelian.image ψ := kernel.lift _ g hg
  obtain ⟨σ, hσ⟩ := hX (Abelian.factorThruImage ψ) inferInstance hP hK
    ((Abelian.image ψ).unitHomEquiv g')
  obtain ⟨h, rfl⟩ := (⨁ fun _ : Fin n => SheafOfModules.unit R).unitHomEquiv.surjective σ
  have hh : h ≫ Abelian.factorThruImage ψ = g' :=
    (Abelian.image ψ).unitHomEquiv.injective
      ((SheafOfModules.unitHomEquiv_comp_apply _ _).trans hσ)
  have hgh : g = h ≫ ψ := by
    rw [← Abelian.image.fac ψ, ← Category.assoc, hh]
    exact (kernel.lift_ι _ _ _).symm
  have hdec : h ≫ ψ = ∑ i, (h ≫ biproduct.π _ i) ≫ M.unitHomEquiv.symm (s i) := by
    have hl : h = biproduct.lift fun i => h ≫ biproduct.π _ i :=
      biproduct.hom_ext _ _ fun j => by simp
    conv_lhs => rw [hl]
    exact biproduct.lift_desc
  refine ⟨fun i => (SheafOfModules.unit R).unitHomEquiv (h ≫ biproduct.π _ i), fun V => ?_⟩
  rw [show PresheafOfModules.sections.eval t V = g.val.app V (1 : R.obj.obj V) from
    sections_eval_eq_val_app_one B S hS t V, hgh, hdec]
  refine (_root_.SheafOfModules.sum_val_app_apply _ _ V _).trans
    (Finset.sum_congr rfl fun i _ => ?_)
  exact unitHomEquiv_symm_val_app B S hS (s i) V _


/-- **Linear systems solvable on a covering chart are solvable globally.** Let global sections be
right exact on quasi-coherent `𝒪_X`-modules, and let `x i, a i j` be global functions on `X`.  If
on a chart `U₀` covering `X` the system `x i = ∑ j, a i j * y j` has a solution `y` with
`y j ∈ 𝒪(U₀)`, then it has a solution `z` in global functions. -/
theorem exists_eq_sum_mul_of_surjective_sectionsMap {X : AlgebraicSpaces B S hS}
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    (U₀ : SmallEtale B S hS X.1)
    (hU₀ : (SmallEtale.topology B S hS X.1).CoversTop fun _ : PUnit.{u + 2} => U₀)
    {n m : ℕ} (x : Fin n → globalFunctions B S hS X.1)
    (a : Fin n → Fin m → globalFunctions B S hS X.1)
    (y : Fin m → Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U₀), ⊤))
    (h : ∀ i, globalFunctionsChartRestriction B S hS X U₀ (x i) =
      ∑ j, globalFunctionsChartRestriction B S hS X U₀ (a i j) * y j) :
    ∃ z : Fin m → globalFunctions B S hS X.1, ∀ i, x i = ∑ j, a i j * z j := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  let M := ⨁ fun _ : Fin n => SheafOfModules.unit R
  let vec : (Fin n → (SheafOfModules.unit R).sections) → M.sections := fun v =>
    M.unitHomEquiv (biproduct.lift fun i => (SheafOfModules.unit R).unitHomEquiv.symm (v i))
  have hcomp : ∀ (v : Fin n → (SheafOfModules.unit R).sections) (i : Fin n)
      (V : (SmallEtale B S hS X.1)ᵒᵖ),
      (biproduct.π (fun _ : Fin n => SheafOfModules.unit R) i).val.app V
          (PresheafOfModules.sections.eval (vec v) V) =
        PresheafOfModules.sections.eval (v i) V := by
    intro v i V
    change ((biproduct.lift fun i => (SheafOfModules.unit R).unitHomEquiv.symm (v i)) ≫
      biproduct.π (fun _ : Fin n => SheafOfModules.unit R) i).val.app V (1 : R.obj.obj V) = _
    rw [biproduct.lift_π, unitHomEquiv_symm_val_app B S hS (v i) V 1, one_smul]
  have hext : ∀ (V : (SmallEtale B S hS X.1)ᵒᵖ) (μ ν : M.val.obj V),
      (∀ i, (biproduct.π (fun _ : Fin n => SheafOfModules.unit R) i).val.app V μ =
        (biproduct.π (fun _ : Fin n => SheafOfModules.unit R) i).val.app V ν) → μ = ν := by
    intro V μ ν hμν
    have htot : ∀ ξ : M.val.obj V, ξ = ∑ i,
        (biproduct.ι (fun _ : Fin n => SheafOfModules.unit R) i).val.app V
          ((biproduct.π (fun _ : Fin n => SheafOfModules.unit R) i).val.app V ξ) := by
      intro ξ
      conv_lhs => rw [← show (𝟙 M : M ⟶ M).val.app V ξ = ξ from rfl, ← biproduct.total]
      exact _root_.SheafOfModules.sum_val_app_apply _ _ V ξ
    rw [htot μ, htot ν]
    exact Finset.sum_congr rfl fun i _ => by rw [hμν i]
  let s : Fin m → M.sections := fun j => vec fun i => a i j
  obtain ⟨c, hc⟩ := exists_eq_sum_smul_of_surjective_sectionsMap B S hS hX
    (isQuasicoherentOnSite_biproduct_unit B S hS X n)
    s (vec x) U₀ hU₀ y (by
      refine hext _ _ _ fun i => ?_
      refine (hcomp x i _).trans ?_
      rw [map_sum]
      refine (h i).trans (Finset.sum_congr rfl fun j _ => ?_)
      refine Eq.trans ?_ (((biproduct.π (fun _ : Fin n => SheafOfModules.unit R) i).val.app
        (op U₀)).hom.map_smul (y j) _).symm
      refine Eq.trans ?_ (congrArg (fun r : (SheafOfModules.unit R).val.obj (op U₀) =>
        (show R.obj.obj (op U₀) from y j) • r) (hcomp (fun i => a i j) i (op U₀))).symm
      exact mul_comm _ _)
  refine ⟨fun j => c j, fun i => ?_⟩
  refine Subtype.ext (funext fun V => ?_)
  have hV := congrArg (fun μ => (biproduct.π (fun _ : Fin n => SheafOfModules.unit R) i).val.app
    V μ) (hc V)
  simp only at hV
  rw [map_sum] at hV
  refine (hcomp x i V).symm.trans (hV.trans ?_)
  change _ = globalFunctionsChartRestriction B S hS X V.unop
    (∑ j, a i j * (show globalFunctions B S hS X.1 from c j))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (((biproduct.π (fun _ : Fin n => SheafOfModules.unit R) i).val.app
    V).hom.map_smul _ _).trans ?_
  refine (congrArg (fun r : (SheafOfModules.unit R).val.obj V =>
    (show R.obj.obj V from PresheafOfModules.sections.eval (c j) V) • r)
    (hcomp (fun i => a i j) i V)).trans ?_
  rw [map_mul]
  exact mul_comm (G := Γ((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X.1).obj V.unop), ⊤)) _ _


/-- **Pulling back along a composite with a morphism of the site.** For `f : X ⟶ W` and a
morphism `q : W ⟶ V` of the site, pulling a function on `V` back along `f ≫ q` is pulling back
its pullback to `W` along `f`. -/
theorem pullbackToGlobalFunctions_comp_schemeSpaceMap (X : AlgebraicSpaces B S hS)
    {V W : BigFppfOver B S hS} (f : X ⟶ schemeSpace W) (q : W ⟶ V)
    (x : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) :
    pullbackToGlobalFunctions B S hS X V (f ≫ schemeSpaceMap q) x =
      pullbackToGlobalFunctions B S hS X W f
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map q).op x) := by
  refine Subtype.ext (funext fun j => ?_)
  change Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (j.unop.1.hom ≫ (f ≫ schemeSpaceMap q).hom))).op x =
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (j.unop.1.hom ≫ f.hom))).op
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map q).op x)
  have h : yoneda.preimage (j.unop.1.hom ≫ (f ≫ schemeSpaceMap q).hom) =
      yoneda.preimage (j.unop.1.hom ≫ f.hom) ≫ q :=
    yoneda.map_injective (by
      rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
      rfl)
  rw [h, Functor.map_comp, op_comp, Functor.map_comp]
  rfl

/-- **Global coefficients for a local combination of functions on a space affine over `X`.**
Let global sections be right exact on quasi-coherent `𝒪_X`-modules, let `p : X ⟶ V` be a
morphism to an affine object of the site inducing a surjection on global functions, let
`pr : X' ⟶ X` be affine and let `U₀` be a chart covering `X`.  If a global function `a` on `X'`
is, on the chart `U₀ ×_X X'`, a combination `∑ rᵢ μᵢ` of global functions `μᵢ` on `X'` with
coefficients `rᵢ ∈ 𝒪(U₀)`, then `a = ∑ dᵢ μᵢ` with `dᵢ` pulled back from `V`. -/
theorem exists_eq_sum_mul_of_isAffineHom {X X' : AlgebraicSpaces B S hS}
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    {V : BigFppfOver B S hS} (p : X ⟶ schemeSpace V)
    (hp : Function.Surjective (pullbackToGlobalFunctions B S hS X V p))
    (pr : X' ⟶ X) (hf : IsAffineHom B S hS pr.hom) (U₀ : SmallEtale B S hS X.1)
    (hU₀ : (SmallEtale.topology B S hS X.1).CoversTop fun _ : PUnit.{u + 2} => U₀)
    {n : ℕ} (μ : Fin n → globalFunctions B S hS X'.1) (r : Fin n → chartRing B S hS X.1 X.2 U₀)
    (a : globalFunctions B S hS X'.1)
    (ha : globalFunctionsChartRestriction B S hS X' ((smallBaseChange B S hS pr
        (relativelyRepresentable_of_isAffineHom B S hS pr hf)).obj U₀) a =
      ∑ i, globalFunctionsChartRestriction B S hS X' ((smallBaseChange B S hS pr
          (relativelyRepresentable_of_isAffineHom B S hS pr hf)).obj U₀) (μ i) *
        (show Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X'.1).obj
            ((smallBaseChange B S hS pr
              (relativelyRepresentable_of_isAffineHom B S hS pr hf)).obj U₀)), ⊤) from
          Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            ((relativelyRepresentable_of_isAffineHom B S hS pr hf).snd U₀.1.hom)).op (r i))) :
    ∃ d : Fin n → Γ((BigFppfOver.toScheme B S hS).obj V, ⊤),
      a = ∑ i, pullbackToGlobalFunctions B S hS X' V (pr ≫ p) (d i) * μ i := by
  set hrep := relativelyRepresentable_of_isAffineHom B S hS pr hf
  let O' := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
      X'.1 X'.2).O)
  have hF : ((smallBaseChangeModulePushforward B S hS pr hrep).obj O').IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_smallBaseChangeModulePushforward_of_isAffineHom pr hrep hf
      (SheafOfModules.isQuasicoherentOnSite_unit _)
  let s : Fin n → ((smallBaseChangeModulePushforward B S hS pr hrep).obj O').sections :=
    fun i => sectionsSmallBaseChange B S hS pr hrep O' (μ i)
  obtain ⟨c, hc⟩ := exists_eq_sum_smul_of_surjective_sectionsMap B S hS hX hF s
    (sectionsSmallBaseChange B S hS pr hrep O' a) U₀ hU₀ r (by
      refine Eq.trans ha (Finset.sum_congr rfl fun i _ => ?_)
      exact (mul_comm (G := Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X'.1).obj
        ((smallBaseChange B S hS pr hrep).obj U₀)), ⊤)) _ _).trans rfl)
  have hcomp : ∀ (U : SmallEtale B S hS X.1) (x : Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)),
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (hrep.snd U.1.hom)).op
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            (yoneda.preimage (U.1.hom ≫ p.hom))).op x) =
        Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
            (yoneda.preimage (hrep.fst U.1.hom ≫ (pr ≫ p).hom))).op x := by
    intro U x
    have hw : (hrep.fst U.1.hom ≫ pr.hom) ≫ p.hom =
        (yoneda.map (hrep.snd U.1.hom) ≫ U.1.hom) ≫ p.hom := by
      rw [(hrep.isPullback U.1.hom).w]
    have h : hrep.snd U.1.hom ≫ yoneda.preimage (U.1.hom ≫ p.hom) =
        yoneda.preimage (hrep.fst U.1.hom ≫ (pr ≫ p).hom) := by
      refine yoneda.map_injective ?_
      rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
      simp only [Category.assoc] at hw
      exact hw.symm
    rw [← h, Functor.map_comp, op_comp, Functor.map_comp]
    rfl
  choose d hd using fun i => hp (c i)
  refine ⟨d, ?_⟩
  apply (bijective_sectionsSmallBaseChange B S hS pr hrep O').1
  apply Subtype.ext
  funext Y
  refine (hc Y).trans (Eq.symm ?_)
  change globalFunctionsChartRestriction B S hS X' ((smallBaseChange B S hS pr hrep).obj Y.unop)
    (∑ i, pullbackToGlobalFunctions B S hS X' V (pr ≫ p) (d i) * μ i) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  change Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (yoneda.preimage (hrep.fst Y.unop.1.hom ≫ (pr ≫ p).hom))).op (d i) * _ = _
  rw [← hcomp, ← hd i]
  rfl


section BaseChange

variable {X X' : AlgebraicSpaces B S hS} {V W : BigFppfOver B S hS}
  (p : X ⟶ schemeSpace V) (q : W ⟶ V) {pr' : X' ⟶ schemeSpace W} {pr : X' ⟶ X}
  (sq : IsPullback pr' pr (schemeSpaceMap q) p)
  (hrep : yoneda.relativelyRepresentable pr.hom)

include sq in
/-- **The base change of an étale chart is a fibre product of schemes.** For a cartesian square
`X' = W ×_V X` of algebraic spaces with `V` and `W` objects of the site, and a chart `U` of `X`,
the base-changed chart `U ×_X X'` is `U ×_V W`. -/
theorem isPullback_smallBaseChange_of_isPullback (U : SmallEtale B S hS X.1) :
    IsPullback (yoneda.preimage (hrep.fst U.1.hom ≫ pr'.hom))
      (hrep.snd U.1.hom) q (yoneda.preimage (U.1.hom ≫ p.hom)) := by
  refine IsPullback.of_map_of_faithful yoneda ?_
  rw [Functor.map_preimage, Functor.map_preimage]
  exact IsPullback.paste_horiz (hrep.isPullback U.1.hom) (AlgebraicSpaces.isPullback_hom B S hS sq)

include sq in
/-- The two maps from a base-changed chart `U ×_X X'` to `V`, through `W` and through `U`,
agree. -/
theorem preimage_comp_eq_of_isPullback (U : SmallEtale B S hS X.1) :
    hrep.snd U.1.hom ≫ yoneda.preimage (U.1.hom ≫ p.hom) =
      yoneda.preimage (hrep.fst U.1.hom ≫ pr'.hom) ≫ q :=
  (isPullback_smallBaseChange_of_isPullback B S hS p q sq hrep U).w.symm

end BaseChange

/-- The base change of a morphism of the site is affine. -/
private theorem isAffineHom_of_isPullback_schemeSpaceMap {X X' : AlgebraicSpaces B S hS}
    {V W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] {p : X ⟶ schemeSpace V} (q : W ⟶ V)
    {pr' : X' ⟶ schemeSpace W} {pr : X' ⟶ X} (sq : IsPullback pr' pr (schemeSpaceMap q) p) :
    IsAffineHom B S hS pr.hom :=
  IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom _ _ _ sq)
    (isAffineHom_yoneda_map B S hS q)

/-- Over a quasi-compact `X`, some chart `U₀` covering `X` has global functions on its base
change forming a pushout of those of `V` and `U₀` along those of `W`. -/
private theorem exists_chart_isPushout_of_isPullback {X X' : AlgebraicSpaces B S hS}
    (hqc : IsQuasiCompactSpace B S hS X.1)
    {V W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (p : X ⟶ schemeSpace V) (q : W ⟶ V) {pr' : X' ⟶ schemeSpace W} {pr : X' ⟶ X}
    (sq : IsPullback pr' pr (schemeSpaceMap q) p) (hf : IsAffineHom B S hS pr.hom)
    (hrep : yoneda.relativelyRepresentable pr.hom) :
    ∃ U₀ : SmallEtale B S hS X.1,
      (SmallEtale.topology B S hS X.1).CoversTop (fun _ : PUnit.{u + 2} => U₀) ∧
      IsPushout (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map q))
        (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (U₀.1.hom ≫ p.hom))))
        (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (hrep.fst U₀.1.hom ≫ pr'.hom))))
        (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map (hrep.snd U₀.1.hom))) := by
  obtain ⟨U₀, hU₀aff, hU₀⟩ := SmallEtale.exists_affineObject_coversTop B S hS X.1 X.2 hqc
  have hU₀aff' : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀.1.left) := hU₀aff
  have hGU₀aff : IsAffine ((BigFppfOver.toScheme B S hS).obj (hrep.pullback U₀.1.hom)) :=
    isAffine_smallBaseChange_obj B S hS pr hrep hf U₀ hU₀aff
  exact ⟨U₀, hU₀, isPushout_appTop_of_isPullback
    ((isPullback_smallBaseChange_of_isPullback B S hS p q sq hrep U₀).map
      (BigFppfOver.toScheme B S hS))⟩

/-- **The surjectivity half of clause (2) of Stacks 07V0.** Let `X` be quasi-compact with global
sections right exact on quasi-coherent modules, let `p : X ⟶ V` be a morphism to an affine
object of the site inducing a surjection `Γ(V, 𝒪) ⟶ Γ(X, 𝒪)` on global functions, and let
`q : W ⟶ V` be a morphism of affine objects.  Then on the base change `X' = W ×_V X` every
global function is the pullback of a global function on `W`.

In Stacks 07V0 (2) `p` is the canonical morphism `X ⟶ Spec A` and `q` is `Spec A' ⟶ Spec A`; the
conclusion is that `A' ⟶ Γ(X', 𝒪_{X'})` is surjective. -/
theorem surjective_pullbackToGlobalFunctions_of_isPullback {X X' : AlgebraicSpaces B S hS}
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    (hqc : IsQuasiCompactSpace B S hS X.1)
    {V W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (p : X ⟶ schemeSpace V) (hp : Function.Surjective (pullbackToGlobalFunctions B S hS X V p))
    (q : W ⟶ V) {pr' : X' ⟶ schemeSpace W} {pr : X' ⟶ X}
    (sq : IsPullback pr' pr (schemeSpaceMap q) p) :
    Function.Surjective (pullbackToGlobalFunctions B S hS X' W pr') := by
  have hf := isAffineHom_of_isPullback_schemeSpaceMap B S hS q sq
  have hrep := relativelyRepresentable_of_isAffineHom B S hS pr hf
  obtain ⟨U₀, hU₀, hpo⟩ := exists_chart_isPushout_of_isPullback B S hS hqc p q sq hf hrep
  intro a
  obtain ⟨n, μ, r, hz⟩ := CommRingCat.exists_eq_sum_mul_of_isPushout hpo
    (a.val (op ((smallBaseChange B S hS pr hrep).obj U₀)))
  obtain ⟨d, hd⟩ := exists_eq_sum_mul_of_isAffineHom B S hS hX p hp pr hf U₀ hU₀
    (fun i => pullbackToGlobalFunctions B S hS X' W pr' (μ i)) r a (hz.trans
      (Finset.sum_congr rfl fun i _ => rfl))
  refine ⟨∑ i, ((BigFppfOver.toScheme B S hS).map q).appTop (d i) * μ i, ?_⟩
  rw [hd, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← sq.w]
  exact congrArg (· * _) (pullbackToGlobalFunctions_comp_schemeSpaceMap B S hS X' pr' q (d i)).symm

/-- **The injectivity half of clause (2) of Stacks 07V0.** Let `X` be quasi-compact with global
sections right exact on quasi-coherent modules, let `p : X ⟶ V` be a morphism to an affine object
of the site inducing a bijection `Γ(V, 𝒪) ≅ Γ(X, 𝒪)` on global functions, and let `q : W ⟶ V` be a
morphism of affine objects.  Then on the base change `X' = W ×_V X` no nonzero global function on
`W` pulls back to zero.

In Stacks 07V0 (2) `p` is the canonical morphism `X ⟶ Spec A` and `q` is `Spec A' ⟶ Spec A`; the
conclusion is that `A' ⟶ Γ(X', 𝒪_{X'})` is injective. -/
theorem injective_pullbackToGlobalFunctions_of_isPullback {X X' : AlgebraicSpaces B S hS}
    (hX : ∀ ⦃M N : Modules.{u, u} B S hS X.1 X.2⦄ (g : M ⟶ N), Epi g →
      M.IsQuasicoherentOnSite → N.IsQuasicoherentOnSite →
        Function.Surjective (SheafOfModules.sectionsMap g))
    (hqc : IsQuasiCompactSpace B S hS X.1)
    {V W : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (p : X ⟶ schemeSpace V) (hp : Function.Bijective (pullbackToGlobalFunctions B S hS X V p))
    (q : W ⟶ V) {pr' : X' ⟶ schemeSpace W} {pr : X' ⟶ X}
    (sq : IsPullback pr' pr (schemeSpaceMap q) p) :
    Function.Injective (pullbackToGlobalFunctions B S hS X' W pr') := by
  have hf := isAffineHom_of_isPullback_schemeSpaceMap B S hS q sq
  have hrep := relativelyRepresentable_of_isAffineHom B S hS pr hf
  obtain ⟨U₀, hU₀, hpo⟩ := exists_chart_isPushout_of_isPullback B S hS hqc p q sq hf hrep
  have hinl := CommRingCat.injective_inr_of_isPushout hpo.flip (by
    intro n m x y a hxy
    obtain ⟨z', hz'⟩ := exists_eq_sum_mul_of_surjective_sectionsMap B S hS hX U₀ hU₀
      (fun i => pullbackToGlobalFunctions B S hS X V p (x i))
      (fun i j => pullbackToGlobalFunctions B S hS X V p (a i j)) y hxy
    choose z hz using fun j => hp.2 (z' j)
    refine ⟨z, fun i => hp.1 ?_⟩
    rw [hz' i, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul, hz j])
  intro a b hab
  exact hinl (congrArg (fun φ : globalFunctions B S hS X'.1 =>
    globalFunctionsChartRestriction B S hS X' ((smallBaseChange B S hS pr hrep).obj U₀) φ) hab)

end AlgebraicGeometry.Space

end
