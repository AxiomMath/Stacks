module

public import StacksFrontier.AlgebraicGeometry.BaseAdicFiltration.GradedPiece
public import StacksFrontier.AlgebraicGeometry.CohomologyGlobalSectionScalar.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusColimitStalk
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicInverseSystem.IdealPowers
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.PrincipalShortExactStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.StalkTorsion
public import StacksFrontier.AlgebraicGeometry.Modules.SubobjectSubmodule

/-!
# Multiplication by a power of a uniformizer between the steps of the adic filtration

Let `p : X ⟶ Spec A` be a morphism of schemes, `π ∈ A`, and `ϖ` the image of `π` in
`Γ(X, 𝒪_X)`. For a sheaf of modules `F` on `X`, multiplication by `ϖ ^ e` carries the subsheaf
`πʲ F` of the `π`-adic filtration into `πʲ⁺ᵉ F`.

## Main definitions

The elided prefix is `Stacks.AlgebraicGeometry.FreenessOverDVR`.

* `adicMul`: multiplication by `ϖ ^ e`, as a morphism `πʲ F ⟶ πʲ⁺ᵉ F`.
* `adicIncl`: the inclusion `πᵐ F ⊆ πʲ F` for `j ≤ m`.
* `StalkTorsionBounded`: the `ϖ`-torsion of every stalk of `F` is killed by `ϖᵏ`.
* `adicReductionComplex`: the short complex `πᵏ F --ϖᵐ--> πᵏ F --> πᵏ (F / πᵏ⁺ᵐ F)`.
* `adicLift`: multiplication by `ϖⁿ`, as a morphism `F ⟶ πⁿ F`.

## Main results

* `stalk_globalSmul`: on stalks, multiplication by a global function is multiplication by its
  germ.
* `mem_range_stalk_adicFiltration_ι_iff`, `mem_ker_stalk_adicProj_iff`: the stalk of `πʲ F` is
  `ϖ_xʲ F_x`, and it is the kernel of the stalk of `F ⟶ F / πʲ F`.
* `adicMul_comp_ι`, `adicMul_comp_adicIncl`, `adicIncl_comp_adicMul`: the defining property
  of `adicMul` and its composites with the inclusions of the filtration, which are
  multiplication by `ϖ ^ e`.
* `isIso_adicMul`: **beyond the torsion exponent, multiplication by `ϖᵉ` is an isomorphism
  `πʲ F ≅ πʲ⁺ᵉ F`.**
* `adicReductionComplex_shortExact`: **the reduction of `πᵏ F` modulo `πᵐ` is short exact**
  beyond the torsion exponent.
* `adicLift_comp_ι`, `ι_comp_adicLift`: `adicLift` composed with the inclusion, either way, is
  multiplication by `ϖⁿ`.

## Implementation notes

`X.Modules` and `SheafOfModules X.ringCatSheaf` carry separately declared category instances, and
a composite mixing the two is not type-correct at the transparency `rw` uses to build its motive.
The identities between morphisms below are therefore proved in term mode, as chains of
`Category.assoc` and the defining identities.

## References

* [Stacks Project, Tag 0EXF](https://stacks.math.columbia.edu/tag/0EXF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.BaseAdicFiltration Stacks.Algebraization Stacks.ModuleSkyscraper

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.AlgebraicGeometry.FreenessOverDVR

variable {X : Scheme.{u}}

/-- The two spellings of multiplication by a global function agree. -/
theorem globalSmul_eq_mulSection (a : Γ(X, ⊤)) (M : X.Modules) :
    globalSmul a M = Stacks.Coherent.mulSection a M := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext x
  rw [globalSmul_app, Stacks.Coherent.mulSection_app]
  rfl

/-- **On stalks, multiplication by a global function is multiplication by its germ.** -/
theorem stalk_globalSmul (a : Γ(X, ⊤)) (M : X.Modules) (x : X)
    (m : (modulesStalkFunctor X x).obj M) :
    ((modulesStalkFunctor X x).map (globalSmul a M)).hom m = (X.presheaf.Γgerm x).hom a • m := by
  rw [globalSmul_eq_mulSection]
  exact Stacks.Coherent.modulesStalkFunctor_map_mulSection a M x m

variable {A : Type u} [CommRing A] (p : X ⟶ Spec (.of A)) (π : A)

/-- **The stalk of `πʲ F` is `ϖ_xʲ F_x`**, for `F` quasi-coherent: an element of the stalk of
`F` comes from the stalk of `πʲ F` exactly when it is a multiple of the `j`-th power of the germ
of `ϖ`. -/
theorem mem_range_stalk_adicFiltration_ι_iff (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (j : ℕ) (z : (modulesStalkFunctor X x).obj F) :
    z ∈ LinearMap.range ((modulesStalkFunctor X x).map
        (adicFiltration p (Ideal.span {π}) j F).ι).hom ↔
      ∃ v, (X.presheaf.Γgerm x).hom (baseScalarMap p π) ^ j • v = z := by
  let := stalkAlgebra p x
  rw [range_stalk_adicFiltration_ι, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]
  rfl

/-- **Multiplication by `ϖ ^ e` carries `πʲ F` into `πʲ⁺ᵉ F`.** -/
theorem adicFiltration_le_comap_globalSmul (F : X.Modules) (j e : ℕ) :
    adicFiltration p (Ideal.span {π}) j F ≤
      sheafSubmoduleComap (globalSmul (baseScalarMap p π ^ e) F)
        (adicFiltration p (Ideal.span {π}) (j + e) F) := by
  refine (idealPowerMultiple_le_iff _ j F _).2 fun U => ?_
  intro x hx
  show (globalSmul (baseScalarMap p π ^ e) F).app U.1 x ∈
    (adicFiltration p (Ideal.span {π}) (j + e) F).toSubmodule.obj (op U.1)
  rw [globalSmul_app]
  have hmem := restrictMemIdealPow_baseScalarMap p e
    (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) e) U
  rw [map_pow] at hmem
  refine (idealPowerMultiple_le_iff _ (j + e) F _).1 le_rfl U ?_
  rw [pow_add, mul_comm, Submodule.mul_smul]
  exact Submodule.smul_mem_smul hmem hx

/-- **Multiplication by `ϖ ^ e`, as a morphism `πʲ F ⟶ πʲ⁺ᵉ F`.** -/
def adicMul (F : X.Modules) (j e : ℕ) :
    ((adicFiltration p (Ideal.span {π}) j F).toSheafOfModules : X.Modules) ⟶
      ((adicFiltration p (Ideal.span {π}) (j + e) F).toSheafOfModules : X.Modules) :=
  sheafSubmoduleMap (globalSmul (baseScalarMap p π ^ e) F) _ _
    (adicFiltration_le_comap_globalSmul p π F j e)

/-- The inclusion `πᵐ F ⊆ πʲ F` for `j ≤ m`, as a morphism of `X.Modules`. -/
def adicIncl (F : X.Modules) {j m : ℕ} (h : j ≤ m) :
    ((adicFiltration p (Ideal.span {π}) m F).toSheafOfModules : X.Modules) ⟶
      ((adicFiltration p (Ideal.span {π}) j F).toSheafOfModules : X.Modules) :=
  SheafOfModules.Submodule.homOfLE (adicFiltration_antitone p (Ideal.span {π}) F h)

/-- `adicMul` is multiplication by `ϖ ^ e`, read inside `F`. -/
theorem adicMul_comp_ι (F : X.Modules) (j e : ℕ) :
    adicMul p π F j e ≫ ((adicFiltration p (Ideal.span {π}) (j + e) F).ι :
        ((adicFiltration p (Ideal.span {π}) (j + e) F).toSheafOfModules : X.Modules) ⟶ F) =
      ((adicFiltration p (Ideal.span {π}) j F).ι :
        ((adicFiltration p (Ideal.span {π}) j F).toSheafOfModules : X.Modules) ⟶ F) ≫
        globalSmul (baseScalarMap p π ^ e) F :=
  sheafSubmoduleMap_comp_ι _ _ _ _

/-- The inclusion `πᵐ F ⊆ πʲ F` is compatible with the inclusions into `F`. -/
theorem adicIncl_comp_ι (F : X.Modules) {j m : ℕ} (h : j ≤ m) :
    adicIncl p π F h ≫ ((adicFiltration p (Ideal.span {π}) j F).ι :
        ((adicFiltration p (Ideal.span {π}) j F).toSheafOfModules : X.Modules) ⟶ F) =
      ((adicFiltration p (Ideal.span {π}) m F).ι :
        ((adicFiltration p (Ideal.span {π}) m F).toSheafOfModules : X.Modules) ⟶ F) :=
  SheafOfModules.Submodule.homOfLE_ι _

/-- Multiplication by `ϖ ^ e` on `πʲ F`, followed by the inclusion `πʲ⁺ᵉ F ⊆ πʲ F`, is
multiplication by `ϖ ^ e` on `πʲ F`. -/
theorem adicMul_comp_adicIncl (F : X.Modules) (j e : ℕ) :
    adicMul p π F j e ≫ adicIncl p π F (Nat.le_add_right j e) =
      globalSmul (baseScalarMap p π ^ e)
        ((adicFiltration p (Ideal.span {π}) j F).toSheafOfModules : X.Modules) := by
  refine (Scheme.Modules.mono_submodule_ι
    (adicFiltration p (Ideal.span {π}) j F)).right_cancellation _ _ ?_
  exact (Category.assoc _ _ _).trans ((congrArg (adicMul p π F j e ≫ ·)
    (adicIncl_comp_ι p π F (Nat.le_add_right j e))).trans
      ((adicMul_comp_ι p π F j e).trans (comp_globalSmul _ _)))

/-- The inclusion `πʲ⁺ᵉ F ⊆ πʲ F` followed by multiplication by `ϖ ^ e` is multiplication by
`ϖ ^ e` on `πʲ⁺ᵉ F`. -/
theorem adicIncl_comp_adicMul (F : X.Modules) (j e : ℕ) :
    adicIncl p π F (Nat.le_add_right j e) ≫ adicMul p π F j e =
      globalSmul (baseScalarMap p π ^ e)
        ((adicFiltration p (Ideal.span {π}) (j + e) F).toSheafOfModules : X.Modules) := by
  refine (Scheme.Modules.mono_submodule_ι
    (adicFiltration p (Ideal.span {π}) (j + e) F)).right_cancellation _ _ ?_
  exact (Category.assoc _ _ _).trans ((congrArg (adicIncl p π F (Nat.le_add_right j e) ≫ ·)
    (adicMul_comp_ι p π F j e)).trans (((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ globalSmul (baseScalarMap p π ^ e) F)
        (adicIncl_comp_ι p π F (Nat.le_add_right j e)))).trans (comp_globalSmul _ _)))

/-! ### Stalks -/

/-- A sheaf of modules has **stalks of bounded `t`-torsion exponent `k`** when, at every point,
an element of the stalk killed by a power of the germ of `t` is killed by its `k`-th power. -/
def StalkTorsionBounded (F : X.Modules) (t : Γ(X, ⊤)) (k : ℕ) : Prop :=
  ∀ (x : X) (v : (modulesStalkFunctor X x).obj F) (j : ℕ),
    (X.presheaf.Γgerm x).hom t ^ j • v = 0 → (X.presheaf.Γgerm x).hom t ^ k • v = 0

/-- Stalkwise form of a commuting square `f ≫ g = f' ≫ g'` of modules. -/
private theorem stalk_map_comp_eq {M N P Q : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (f' : M ⟶ Q)
    (g' : Q ⟶ P) (h : f ≫ g = f' ≫ g') (x : X) (y : (modulesStalkFunctor X x).obj M) :
    ((modulesStalkFunctor X x).map g).hom (((modulesStalkFunctor X x).map f).hom y) =
      ((modulesStalkFunctor X x).map g').hom (((modulesStalkFunctor X x).map f').hom y) := by
  have := congrArg (fun φ => ((modulesStalkFunctor X x).map φ).hom y) h
  simpa using this

/-- Over the torsion exponent, an element of the stalk of `πʲ F` whose image in `F_x` is killed by
`ϖ ^ e` has zero image in `F_x`. -/
private theorem stalk_adicFiltration_ι_eq_zero_of_smul_eq_zero (F : X.Modules)
    [F.IsQuasicoherent] {k j : ℕ} (hk : StalkTorsionBounded F (baseScalarMap p π) k) (hj : k ≤ j)
    (e : ℕ) (x : X) (y : (modulesStalkFunctor X x).obj
      ((adicFiltration p (Ideal.span {π}) j F).toSheafOfModules : X.Modules))
    (h : (X.presheaf.Γgerm x).hom (baseScalarMap p π) ^ e •
      ((modulesStalkFunctor X x).map (adicFiltration p (Ideal.span {π}) j F).ι).hom y = 0) :
    ((modulesStalkFunctor X x).map (adicFiltration p (Ideal.span {π}) j F).ι).hom y = 0 := by
  obtain ⟨v, hv⟩ := (mem_range_stalk_adicFiltration_ι_iff p π F x j _).1
    (LinearMap.mem_range_self _ y)
  rw [← hv, smul_smul, ← pow_add] at h
  rw [← hv, ← Nat.sub_add_cancel hj, pow_add, mul_smul, hk x v _ h, smul_zero]

/-- On stalks, `adicMul` is multiplication by the `e`-th power of the germ of `ϖ`. -/
theorem stalk_ι_adicMul (F : X.Modules) (j e : ℕ) (x : X)
    (y : (modulesStalkFunctor X x).obj
      ((adicFiltration p (Ideal.span {π}) j F).toSheafOfModules : X.Modules)) :
    ((modulesStalkFunctor X x).map (adicFiltration p (Ideal.span {π}) (j + e) F).ι).hom
        (((modulesStalkFunctor X x).map (adicMul p π F j e)).hom y) =
      (X.presheaf.Γgerm x).hom (baseScalarMap p π) ^ e •
        ((modulesStalkFunctor X x).map (adicFiltration p (Ideal.span {π}) j F).ι).hom y := by
  refine (stalk_map_comp_eq _ _ _ _ (adicMul_comp_ι p π F j e) x y).trans ?_
  show ((modulesStalkFunctor X x).map (globalSmul (baseScalarMap p π ^ e) F)).hom _ = _
  rw [stalk_globalSmul, map_pow]

/-- **Multiplication by `ϖ ^ e` is an isomorphism `πʲ F ≅ πʲ⁺ᵉ F` beyond the torsion
exponent.** If the stalks of the quasi-coherent module `F` have `ϖ`-torsion of exponent at most
`k`, then for `j ≥ k` multiplication by `ϖ ^ e` carries `πʲ F` isomorphically onto `πʲ⁺ᵉ F`. -/
theorem isIso_adicMul (F : X.Modules) [F.IsQuasicoherent] {k j : ℕ}
    (hk : StalkTorsionBounded F (baseScalarMap p π) k) (hj : k ≤ j) (e : ℕ) :
    IsIso (adicMul p π F j e) := by
  refine isIso_of_forall_isIso_modulesStalkFunctor_map _ fun x => ?_
  set t := (X.presheaf.Γgerm x).hom (baseScalarMap p π)
  have hι := injective_stalk_adicFiltration_ι p F x (Ideal.span {π}) (j + e)
  have hιj := injective_stalk_adicFiltration_ι p F x (Ideal.span {π}) j
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun y y' hyy' => ?_, fun z => ?_⟩
  · have hyy : ((modulesStalkFunctor X x).map (adicMul p π F j e)).hom y =
        ((modulesStalkFunctor X x).map (adicMul p π F j e)).hom y' := hyy'
    have h0 : ((modulesStalkFunctor X x).map (adicMul p π F j e)).hom (y - y') = 0 := by
      rw [map_sub, hyy, sub_self]
    have h1 : t ^ e • ((modulesStalkFunctor X x).map
        (adicFiltration p (Ideal.span {π}) j F).ι).hom (y - y') = 0 := by
      rw [← stalk_ι_adicMul, h0, map_zero]
    have h3 := stalk_adicFiltration_ι_eq_zero_of_smul_eq_zero p π F hk hj e x _ h1
    exact sub_eq_zero.1 (hιj (h3.trans (map_zero _).symm))
  · obtain ⟨v, hv⟩ := (mem_range_stalk_adicFiltration_ι_iff p π F x (j + e) _).1
      (LinearMap.mem_range_self _ z)
    obtain ⟨y, hy⟩ := (mem_range_stalk_adicFiltration_ι_iff p π F x j (t ^ j • v)).2 ⟨v, rfl⟩
    refine ⟨y, hι ?_⟩
    show ((modulesStalkFunctor X x).map (adicFiltration p (Ideal.span {π}) (j + e) F).ι).hom
        (((modulesStalkFunctor X x).map (adicMul p π F j e)).hom y) = _
    rw [stalk_ι_adicMul, hy, ← hv, smul_smul, ← pow_add, add_comm]

/-- **The kernel of the stalk of `F ⟶ F / πⁿ F` is `ϖ_xⁿ F_x`**, elementwise. -/
theorem mem_ker_stalk_adicProj_iff (F : X.Modules) [F.IsQuasicoherent] (x : X) (n : ℕ)
    (z : (modulesStalkFunctor X x).obj F) :
    ((modulesStalkFunctor X x).map (adicProj p (Ideal.span {π}) n F)).hom z = 0 ↔
      ∃ v, (X.presheaf.Γgerm x).hom (baseScalarMap p π) ^ n • v = z := by
  rw [← LinearMap.mem_ker, ker_stalk_adicProj, ← range_stalk_adicFiltration_ι]
  exact mem_range_stalk_adicFiltration_ι_iff p π F x n z

/-! ### Reduction of `πᵏ F` modulo `πᵐ` -/

/-- The image `πᵏ (F / πᵏ⁺ᵐ F)` of `πᵏ F` in `F / πᵏ⁺ᵐ F`. -/
abbrev adicImage (F : X.Modules) (k m : ℕ) :
    (adicQuotient p (Ideal.span {π}) (k + m) F).Submodule :=
  adicFiltration p (Ideal.span {π}) k (adicQuotient p (Ideal.span {π}) (k + m) F)

/-- The reduction `πᵏ F ⟶ πᵏ (F / πᵏ⁺ᵐ F)`, the restriction of the quotient projection. -/
def adicReduce (F : X.Modules) (k m : ℕ) :
    ((adicFiltration p (Ideal.span {π}) k F).toSheafOfModules : X.Modules) ⟶
      ((adicImage p π F k m).toSheafOfModules : X.Modules) :=
  sheafSubmoduleMap (adicProj p (Ideal.span {π}) (k + m) F) _ _
    (idealPowerMultiple_le_sheafSubmoduleComap _ k _ _ le_rfl)

/-- The reduction is the quotient projection, read inside the ambient sheaves. -/
theorem adicReduce_comp_ι (F : X.Modules) (k m : ℕ) :
    adicReduce p π F k m ≫ ((adicImage p π F k m).ι :
        ((adicImage p π F k m).toSheafOfModules : X.Modules) ⟶ _) =
      ((adicFiltration p (Ideal.span {π}) k F).ι :
        ((adicFiltration p (Ideal.span {π}) k F).toSheafOfModules : X.Modules) ⟶ F) ≫
        adicProj p (Ideal.span {π}) (k + m) F :=
  sheafSubmoduleMap_comp_ι _ _ _ _

/-- On stalks, the reduction is the quotient projection. -/
theorem stalk_ι_adicReduce (F : X.Modules) (k m : ℕ) (x : X)
    (y : (modulesStalkFunctor X x).obj
      ((adicFiltration p (Ideal.span {π}) k F).toSheafOfModules : X.Modules)) :
    ((modulesStalkFunctor X x).map (adicImage p π F k m).ι).hom
        (((modulesStalkFunctor X x).map (adicReduce p π F k m)).hom y) =
      ((modulesStalkFunctor X x).map (adicProj p (Ideal.span {π}) (k + m) F)).hom
        (((modulesStalkFunctor X x).map (adicFiltration p (Ideal.span {π}) k F).ι).hom y) := by
  exact stalk_map_comp_eq _ _ _ _ (adicReduce_comp_ι p π F k m) x y

/-- **The short complex `πᵏ F --ϖᵐ--> πᵏ F --> πᵏ (F / πᵏ⁺ᵐ F)`.** -/
def adicReductionComplex (F : X.Modules) (k m : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (globalSmul (baseScalarMap p π ^ m)
      ((adicFiltration p (Ideal.span {π}) k F).toSheafOfModules : X.Modules))
    (adicReduce p π F k m) (by
      refine (Scheme.Modules.mono_submodule_ι (adicImage p π F k m)).right_cancellation _ _ ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (globalSmul (baseScalarMap p π ^ m) _ ≫ ·)
        (adicReduce_comp_ι p π F k m)).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      refine (congrArg (· ≫ adicProj p (Ideal.span {π}) (k + m) F)
        (comp_globalSmul _ ((adicFiltration p (Ideal.span {π}) k F).ι :
          ((adicFiltration p (Ideal.span {π}) k F).toSheafOfModules : X.Modules) ⟶ F)).symm).trans
        ?_
      refine (congrArg (· ≫ adicProj p (Ideal.span {π}) (k + m) F)
        (adicMul_comp_ι p π F k m).symm).trans ?_
      refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (adicMul p π F k m ≫ ·)
        (cokernel.condition (C := X.Modules) (adicFiltration p (Ideal.span {π}) (k + m) F).ι)).trans
        ?_
      exact comp_zero.trans zero_comp.symm)

/-- **`πᵏ F --ϖᵐ--> πᵏ F --> πᵏ (F / πᵏ⁺ᵐ F)` is short exact** once the stalks of `F` have
`ϖ`-torsion of exponent at most `k`. -/
theorem adicReductionComplex_shortExact (F : X.Modules) [F.IsQuasicoherent] {k : ℕ}
    (hk : StalkTorsionBounded F (baseScalarMap p π) k) (m : ℕ) :
    (adicReductionComplex p π F k m).ShortExact := by
  refine (AlgebraicGeometry.SheafOfModules.shortExact_iff_stalkFunctor_map_shortExact
    (O := X.ringCatSheaf) _).2 fun x => ?_
  set t := (X.presheaf.Γgerm x).hom (baseScalarMap p π)
  have hιk := injective_stalk_adicFiltration_ι p F x (Ideal.span {π}) k
  have hιZ := injective_stalk_adicFiltration_ι p (adicQuotient p (Ideal.span {π}) (k + m) F) x
    (Ideal.span {π}) k
  have hsmul : ∀ y, ((modulesStalkFunctor X x).map (globalSmul (baseScalarMap p π ^ m)
      ((adicFiltration p (Ideal.span {π}) k F).toSheafOfModules : X.Modules))).hom y =
        t ^ m • y := fun y =>
    (stalk_globalSmul _ _ x y).trans (by rw [map_pow])
  have hinj : Function.Injective ((modulesStalkFunctor X x).map (globalSmul
      (baseScalarMap p π ^ m)
      ((adicFiltration p (Ideal.span {π}) k F).toSheafOfModules : X.Modules))).hom := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hsmul] at hy
    have h1 : t ^ m • ((modulesStalkFunctor X x).map
        (adicFiltration p (Ideal.span {π}) k F).ι).hom y = 0 := by
      rw [← map_smul, hy, map_zero]
    have h2 := stalk_adicFiltration_ι_eq_zero_of_smul_eq_zero p π F hk le_rfl m x y h1
    exact hιk (h2.trans (map_zero _).symm)
  have hsurj : Function.Surjective ((modulesStalkFunctor X x).map (adicReduce p π F k m)).hom := by
    intro z
    obtain ⟨q, hq⟩ := (mem_range_stalk_adicFiltration_ι_iff p π
      (adicQuotient p (Ideal.span {π}) (k + m) F) x k _).1 (LinearMap.mem_range_self _ z)
    obtain ⟨w, rfl⟩ := surjective_stalk_adicProj p F x (Ideal.span {π}) (k + m) q
    obtain ⟨y, hy⟩ := (mem_range_stalk_adicFiltration_ι_iff p π F x k (t ^ k • w)).2 ⟨w, rfl⟩
    refine ⟨y, hιZ ?_⟩
    rw [stalk_ι_adicReduce, hy, map_smul, hq]
  have hexact : LinearMap.ker ((modulesStalkFunctor X x).map (adicReduce p π F k m)).hom ≤
      LinearMap.range ((modulesStalkFunctor X x).map (globalSmul (baseScalarMap p π ^ m)
        ((adicFiltration p (Ideal.span {π}) k F).toSheafOfModules : X.Modules))).hom := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    have h0 : ((modulesStalkFunctor X x).map (adicProj p (Ideal.span {π}) (k + m) F)).hom
        (((modulesStalkFunctor X x).map (adicFiltration p (Ideal.span {π}) k F).ι).hom y) = 0 := by
      rw [← stalk_ι_adicReduce, hy, map_zero]
    obtain ⟨v, hv⟩ := (mem_ker_stalk_adicProj_iff p π F x (k + m) _).1 h0
    obtain ⟨y', hy'⟩ := (mem_range_stalk_adicFiltration_ι_iff p π F x k (t ^ k • v)).2 ⟨v, rfl⟩
    refine ⟨y', hιk ?_⟩
    rw [hsmul, map_smul, hy', ← hv, smul_smul, ← pow_add, add_comm]
  refine ShortComplex.ShortExact.mk' ?_ ((ModuleCat.mono_iff_injective _).2 hinj)
    ((ModuleCat.epi_iff_surjective _).2 hsurj)
  exact (ShortComplex.moduleCat_exact_iff_ker_sub_range _).2 hexact

/-! ### Multiplication by `ϖⁿ` into `πⁿ F` -/

/-- Multiplication by `ϖⁿ`, as a morphism `F ⟶ πⁿ F`. -/
def adicLift (F : X.Modules) (n : ℕ) :
    F ⟶ ((adicFiltration p (Ideal.span {π}) n F).toSheafOfModules : X.Modules) :=
  (sheafTopIso F).inv ≫ sheafSubmoduleMap (globalSmul (baseScalarMap p π ^ n) F) ⊤ _ (by
    have h := adicFiltration_le_comap_globalSmul p π F 0 n
    rwa [zero_add, adicFiltration, idealPowerMultiple_zero] at h)

/-- `adicLift` is multiplication by `ϖⁿ`, read inside `F`. -/
theorem adicLift_comp_ι (F : X.Modules) (n : ℕ) :
    adicLift p π F n ≫ ((adicFiltration p (Ideal.span {π}) n F).ι :
        ((adicFiltration p (Ideal.span {π}) n F).toSheafOfModules : X.Modules) ⟶ F) =
      globalSmul (baseScalarMap p π ^ n) F := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg ((sheafTopIso F).inv ≫ ·) (sheafSubmoduleMap_comp_ι _ _ _ _)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact (congrArg (· ≫ globalSmul (baseScalarMap p π ^ n) F) (sheafTopIso F).inv_hom_id).trans
    (Category.id_comp _)

/-- The inclusion `πⁿ F ⊆ F` followed by `adicLift` is multiplication by `ϖⁿ` on `πⁿ F`. -/
theorem ι_comp_adicLift (F : X.Modules) (n : ℕ) :
    ((adicFiltration p (Ideal.span {π}) n F).ι :
        ((adicFiltration p (Ideal.span {π}) n F).toSheafOfModules : X.Modules) ⟶ F) ≫
      adicLift p π F n =
      globalSmul (baseScalarMap p π ^ n)
        ((adicFiltration p (Ideal.span {π}) n F).toSheafOfModules : X.Modules) := by
  refine (Scheme.Modules.mono_submodule_ι
    (adicFiltration p (Ideal.span {π}) n F)).right_cancellation _ _ ?_
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (adicLift_comp_ι p π F n)).trans
    (comp_globalSmul _ _))

end Stacks.AlgebraicGeometry.FreenessOverDVR
