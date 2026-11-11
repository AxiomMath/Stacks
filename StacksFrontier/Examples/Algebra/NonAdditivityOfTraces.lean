module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.Examples.Algebra.DualNumberHomotopyDiagram
public import StacksFrontier.CategoryTheory.Trace.Preliminaries.GroupTrace
public import StacksFrontier.CategoryTheory.FilteredDerived.Perfectness.Trace

/-!
# Nonadditivity of traces

There is a distinguished triangle of perfect complexes in a homotopy category and an endomorphism
of that triangle for which the alternating trace is not additive: the trace of the endomorphism of
the middle term differs from the sum of the traces of the endomorphisms of the outer terms.

The triangle is the one attached to the degreewise split short exact sequence of two-term complexes
over the dual numbers from the previous file, transported to a universe-polymorphic copy of the
dual numbers. The endomorphism is multiplication by `1 + ε` on the left column and the identity on
the other two, which is a morphism of triangles because the left square commutes up to homotopy.
Its traces are `-(1 + ε)`, `1` and `1` in the additive commutator quotient, and `-(1 + ε) + 1 ≠ 1`
there because that quotient of the dual numbers is `ℚ[ε]` itself.

## Main results

* `Stacks.Examples.ulift_dualNumber_distinguished_triangle_trace_nonadditive`: the triangle, its
  endomorphism, and the failure of trace additivity over the dual numbers, traces in `R/[R,R]`.
* `Stacks.Examples.exists_distinguished_triangle_trace_nonadditive`: the same, quantified over
  rings that need not be commutative. Stacks 087L itself, over a commutative ring with traces in
  `R`, is `exists_commRing_distinguished_triangle_trace_nonadditive` in
  `StacksFrontier.Examples.Algebra.NonAdditivityOfTracesCommRing`.

## Implementation notes

The three vertices are presented by bounded complexes of finite projective modules. Their
endomorphisms are presented by cochain maps; the triangle endomorphism is required to have their
images in the homotopy category as its three components. The trace is the alternating trace of a
finite-projective presentation, which is independent of the presentation.

## References

* [Stacks Project, Tag 087L](https://stacks.math.columbia.edu/tag/087L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Pretriangulated

namespace Stacks.Examples

universe u v

private lemma additiveCommutatorQuotientMk_injective (R : Type u) [CommRing R] :
    Function.Injective (CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk
      R) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  rw [CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk,
    QuotientAddGroup.ker_mk']
  apply AddSubgroup.closure_eq_bot_iff.mpr
  rintro x ⟨a, b, rfl⟩
  simp [mul_comm]

private lemma projectiveModuleTrace_conj_regular (R : Type u) [CommRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (e : M ≃ₗ[R] R) (x : R) :
    Stacks.Trace.projectiveModuleTrace R M
      (e.symm.toLinearMap.comp ((LinearMap.mulLeft R x).comp e.toLinearMap)) =
      CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk R x := by
  classical
  let h := Module.Finite.exists_comp_eq_id_of_projective R M
  let n := h.choose
  let p : (Fin n → R) →ₗ[R] M := h.choose_spec.choose
  let i : M →ₗ[R] (Fin n → R) := h.choose_spec.choose_spec.choose
  have hpi : p.comp i = LinearMap.id := h.choose_spec.choose_spec.choose_spec.2.2
  have hpix (y : M) : p (i y) = y := by
    simpa using congrArg (fun f : Module.End R M => f y) hpi
  let e1 : (Fin 1 → R) ≃ₗ[R] R :=
    { toFun := fun z => z 0
      invFun := fun z _ => z
      left_inv z := by funext j; fin_cases j; rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let U : (Fin n → R) →ₗ[R] (Fin 1 → R) :=
    e1.symm.toLinearMap.comp (e.toLinearMap.comp p)
  let V : (Fin 1 → R) →ₗ[R] (Fin n → R) :=
    i.comp (e.symm.toLinearMap.comp ((LinearMap.mulLeft R x).comp e1.toLinearMap))
  have hUV : V.comp U = i.comp
      ((e.symm.toLinearMap.comp ((LinearMap.mulLeft R x).comp e.toLinearMap)).comp p) := by
    ext z j
    simp [U, V, e1, LinearMap.comp_apply]
  have hVU : U.comp V = e1.symm.toLinearMap.comp
      ((LinearMap.mulLeft R x).comp e1.toLinearMap) := by
    ext z j
    simp [U, V, e1, LinearMap.comp_apply, hpix]
  change CategoryTheory.FilteredDerived.freeModuleTrace R (Fin n)
      (i.comp ((e.symm.toLinearMap.comp ((LinearMap.mulLeft R x).comp e.toLinearMap)).comp p)) = _
  rw [← hUV, CategoryTheory.FilteredDerived.freeModuleTrace_cyclic R V U, hVU,
    CategoryTheory.FilteredDerived.freeModuleTrace_apply]
  unfold CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk
  simp only [map_sum]
  simp [CategoryTheory.FilteredDerived.standardBasisVector, e1]

private lemma dualNumber_eps_mul_comp :
    (LinearMap.mulLeft (DualNumber ℚ) (1 + (DualNumber.eps : DualNumber ℚ))).comp
        (LinearMap.mulLeft (DualNumber ℚ) (DualNumber.eps : DualNumber ℚ)) =
      LinearMap.mulLeft (DualNumber ℚ) (DualNumber.eps : DualNumber ℚ) := by
  refine LinearMap.ext fun x => ?_
  change (1 + (DualNumber.eps : DualNumber ℚ)) *
    ((DualNumber.eps : DualNumber ℚ) * x) = (DualNumber.eps : DualNumber ℚ) * x
  rw [← mul_assoc, add_mul, one_mul, DualNumber.eps_mul_eps, add_zero]

private abbrev dualBaseRing := DualNumber ℚ

private abbrev dualRing.{u₁} : Type u₁ := ULift.{u₁} dualBaseRing

private abbrev dualDown : dualRing →+* dualBaseRing where
  toFun := ULift.down
  map_one' := rfl
  map_mul' := by intro x y; cases x; cases y; rfl
  map_zero' := rfl
  map_add' := by intro x y; cases x; cases y; rfl

private abbrev dualModuleFunctor.{u₁, v₁} : ModuleCat dualBaseRing ⥤ ModuleCat.{v₁} dualRing.{u₁} :=
  ModuleCat.restrictScalars.{0} dualDown ⋙ ModuleCat.uliftFunctor.{v₁, 0, u₁} dualRing.{u₁}

private abbrev dualZero.{u₁, v₁} : ModuleCat.{v₁} dualRing.{u₁} :=
  dualModuleFunctor.{u₁, v₁}.obj (dualNumberZeroModule ℚ)

private instance : Subsingleton (dualNumberZeroModule ℚ) :=
  ⟨fun _ _ => funext fun i => Fin.elim0 i⟩

/-- A degree of a complex over the dual numbers equal to the zero module is a zero object. -/
private lemma dualNumber_isZero_X (K : CochainComplex (DualNumberModuleCat.{0, 0} ℚ) ℤ) {n : ℤ}
    (hx : K.X n = dualNumberZeroModule ℚ) : Limits.IsZero (K.X n) := by
  rw [hx]
  exact ModuleCat.isZero_of_subsingleton _

private lemma dualZero_subsingleton.{u₁, v₁} :
    Subsingleton (dualZero.{u₁, v₁}) := by
  change Subsingleton (ULift.{v₁, 0} (Fin 0 → dualBaseRing))
  infer_instance

private def dualZeroEquiv.{u₁, v₁} :
    dualZero.{u₁, v₁} ≃ₗ[dualRing.{u₁}] (Fin 0 → dualRing.{u₁}) where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := dualZero_subsingleton.{u₁, v₁}.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_add' := by intros; simp
  map_smul' := by intros; simp

private abbrev dualRegular.{u₁, v₁} : ModuleCat.{v₁} dualRing.{u₁} :=
  dualModuleFunctor.{u₁, v₁}.obj (ModuleCat.of dualBaseRing dualBaseRing)

private def dualRegularEquiv.{u₁, v₁} : dualRegular.{u₁, v₁} ≃ₗ[dualRing.{u₁}] dualRing.{u₁} where
  toFun x := ULift.up x.down
  invFun x := ULift.up x.down
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private lemma dualRegular_finite.{u₁, v₁} :
    Module.Finite dualRing.{u₁} dualRegular.{u₁, v₁} :=
  Module.Finite.of_surjective dualRegularEquiv.{u₁, v₁}.symm.toLinearMap
    dualRegularEquiv.{u₁, v₁}.symm.surjective

private lemma dualRegular_projective.{u₁, v₁} :
    Module.Projective dualRing.{u₁} dualRegular.{u₁, v₁} :=
  Module.Projective.of_equiv' dualRegularEquiv.{u₁, v₁}.symm

attribute [local instance] dualRegular_finite dualRegular_projective

private lemma dualRegular_map_mul.{u₁, v₁} (x : dualBaseRing) :
    (dualModuleFunctor.{u₁, v₁}).map
      (ModuleCat.ofHom (LinearMap.mulLeft dualBaseRing x)) =
    ModuleCat.ofHom
      (dualRegularEquiv.{u₁, v₁}.symm.toLinearMap.comp
        ((LinearMap.mulLeft dualRing.{u₁} (ULift.up x)).comp
          dualRegularEquiv.{u₁, v₁}.toLinearMap)) :=
  ModuleCat.hom_ext <| LinearMap.ext fun ⟨_⟩ => rfl

private lemma dualRegular_projectiveTrace_map_mul.{u₁, v₁} (x : dualBaseRing) :
    Stacks.Trace.projectiveModuleTrace dualRing.{u₁}
      dualRegular.{u₁, v₁}
      ((dualModuleFunctor.{u₁, v₁}).map
        (ModuleCat.ofHom (LinearMap.mulLeft dualBaseRing x))).hom =
        CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk dualRing.{u₁}
          (ULift.up x) := by
  rw [dualRegular_map_mul]
  exact projectiveModuleTrace_conj_regular dualRing dualRegular
    dualRegularEquiv (ULift.up x)

private lemma dualRegular_projectiveTrace_map_id.{u₁, v₁} :
    Stacks.Trace.projectiveModuleTrace dualRing.{u₁} dualRegular.{u₁, v₁}
      ((dualModuleFunctor.{u₁, v₁}).map (𝟙 (ModuleCat.of dualBaseRing dualBaseRing))).hom =
        CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk dualRing.{u₁}
          (ULift.up (1 : dualBaseRing)) := by
  rw [show 𝟙 (ModuleCat.of dualBaseRing dualBaseRing) =
      ModuleCat.ofHom (LinearMap.mulLeft dualBaseRing 1) by simp [LinearMap.mulLeft_one]]
  exact dualRegular_projectiveTrace_map_mul 1

private lemma dualZero_projective_finite.{u₁, v₁} :
    Module.Projective dualRing.{u₁} dualZero.{u₁, v₁} ∧
      Module.Finite dualRing.{u₁} dualZero.{u₁, v₁} :=
  ⟨Module.Projective.of_equiv' dualZeroEquiv.{u₁, v₁}.symm,
    Module.Finite.of_surjective _ dualZeroEquiv.{u₁, v₁}.symm.surjective⟩

private lemma dualMapped_perfect.{u₁, v₁}
    (K : CochainComplex (DualNumberModuleCat ℚ) ℤ)
    (hzero : ∀ n, n ≠ 0 → n ≠ 1 → K.X n = dualNumberZeroModule ℚ)
    (hcomponents : ∀ n, K.X n = dualNumberZeroModule ℚ ∨
      K.X n = ModuleCat.of dualBaseRing dualBaseRing) :
    CategoryTheory.FilteredDerived.finiteProjectiveComplex dualRing.{u₁}
      (((dualModuleFunctor.{u₁, v₁}).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  classical
  let F := dualModuleFunctor.{u₁, v₁}
  refine ⟨⟨?_, ?_⟩, fun n => ?_⟩
  · rw [CochainComplex.plus_iff]
    refine ⟨-1, ?_⟩
    apply (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff (K := K) F (-1)).2
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    rw [hzero n (by omega) (by omega)]
    exact ModuleCat.isZero_of_subsingleton _
  · rw [CochainComplex.minus_iff]
    refine ⟨1, ?_⟩
    apply (CochainComplex.isStrictlyLE_mapHomologicalComplex_obj_iff (K := K) F 1).2
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    rw [hzero n (by omega) (by omega)]
    exact ModuleCat.isZero_of_subsingleton _
  · rw [Functor.mapHomologicalComplex_obj_X]
    rcases hcomponents n with h | h <;> rw [h]
    exacts [dualZero_projective_finite.{u₁, v₁},
      ⟨dualRegular_projective.{u₁, v₁}, dualRegular_finite.{u₁, v₁}⟩]

private abbrev dualMapped.{u₁, v₁} :
    CochainComplex (DualNumberModuleCat ℚ) ℤ ⥤ CochainComplex (ModuleCat.{v₁} dualRing.{u₁}) ℤ :=
  (dualModuleFunctor.{u₁, v₁}).mapHomologicalComplex (ComplexShape.up ℤ)

private lemma dualMapped_twoTerm_perfect.{u₁, v₁} (P Q : DualNumberModuleCat ℚ) (d : P ⟶ Q)
    (hP : P = dualNumberZeroModule ℚ ∨ P = ModuleCat.of dualBaseRing dualBaseRing)
    (hQ : Q = dualNumberZeroModule ℚ ∨ Q = ModuleCat.of dualBaseRing dualBaseRing) :
    CategoryTheory.FilteredDerived.finiteProjectiveComplex dualRing.{u₁}
      (dualMapped.{u₁, v₁}.obj (dualNumberTwoTermComplex ℚ P Q d)) := by
  apply dualMapped_perfect
  · intro n hn₀ hn₁
    simp [dualNumberTwoTermComplex, hn₀, hn₁]
  · intro n
    simp only [dualNumberTwoTermComplex]
    split_ifs <;> first | exact hP | exact hQ | exact Or.inl rfl

/-- A degree of the transported complex is a subsingleton when the original degree is zero. -/
private lemma dualMapped_subsingleton.{u₁, v₁} (K : CochainComplex (DualNumberModuleCat.{0, 0} ℚ) ℤ)
    {n : ℤ} (hx : K.X n = dualNumberZeroModule ℚ) :
    Subsingleton ((dualMapped.{u₁, v₁}.obj K).X n) :=
  ModuleCat.isZero_iff_subsingleton.mp 
    ((dualModuleFunctor.{u₁, v₁}).map_isZero (dualNumber_isZero_X K hx))

private def dualNumberSplitting (i₀ : dualNumberLeftComplex ℚ ⟶ dualNumberMiddleComplex ℚ)
    (p₀ : dualNumberMiddleComplex ℚ ⟶ dualNumberRightComplex ℚ) (hip : i₀ ≫ p₀ = 0)
    (hi₁ : i₀.f 1 = 𝟙 _) (hp₀ : p₀.f 0 = 𝟙 _) (n : ℤ) :
    ((ShortComplex.mk i₀ p₀ hip).map
      (HomologicalComplex.eval (DualNumberModuleCat ℚ) (ComplexShape.up ℤ) n)).Splitting := by
  classical
  by_cases hn₀ : n = 0
  · subst n
    letI : Subsingleton (((ShortComplex.mk i₀ p₀ hip).map (HomologicalComplex.eval
        (DualNumberModuleCat ℚ) (ComplexShape.up ℤ) 0)).X₁) := by
      change Subsingleton ((dualNumberLeftComplex ℚ).X 0)
      simp only [dualNumberLeftComplex, dualNumberTwoTermComplex, dualNumberZeroModule]
      exact ⟨fun x y => by funext i; exact Fin.elim0 i⟩
    have hiso : IsIso ((ShortComplex.mk i₀ p₀ hip).map (HomologicalComplex.eval
        (DualNumberModuleCat ℚ) (ComplexShape.up ℤ) 0)).g := by
      change IsIso (p₀.f 0)
      rw [hp₀]
      exact IsIso.id _
    exact ShortComplex.Splitting.ofIsZeroOfIsIso _ (ModuleCat.isZero_of_subsingleton _) hiso
  by_cases hn₁ : n = 1
  · subst n
    letI : Subsingleton (((ShortComplex.mk i₀ p₀ hip).map (HomologicalComplex.eval
        (DualNumberModuleCat ℚ) (ComplexShape.up ℤ) 1)).X₃) := by
      change Subsingleton ((dualNumberRightComplex ℚ).X 1)
      simp only [dualNumberRightComplex, dualNumberTwoTermComplex, dualNumberZeroModule]
      exact ⟨fun x y => by funext i; exact Fin.elim0 i⟩
    have hiso : IsIso ((ShortComplex.mk i₀ p₀ hip).map (HomologicalComplex.eval
        (DualNumberModuleCat ℚ) (ComplexShape.up ℤ) 1)).f := by
      change IsIso (i₀.f 1)
      rw [hi₁]
      exact IsIso.id _
    exact ShortComplex.Splitting.ofIsIsoOfIsZero _ hiso (ModuleCat.isZero_of_subsingleton _)
  have hz (K : CochainComplex (DualNumberModuleCat ℚ) ℤ) (hK : K = dualNumberLeftComplex ℚ ∨
      K = dualNumberMiddleComplex ℚ ∨ K = dualNumberRightComplex ℚ) : Limits.IsZero (K.X n) :=
    dualNumber_isZero_X K (by rcases hK with rfl | rfl | rfl <;>
      simp [dualNumberLeftComplex, dualNumberMiddleComplex, dualNumberRightComplex,
        dualNumberTwoTermComplex, hn₀, hn₁])
  exact ShortComplex.Splitting.ofIsZero _ (hz _ (Or.inl rfl)) (hz _ (Or.inr (Or.inl rfl)))
    (hz _ (Or.inr (Or.inr rfl)))

private lemma dualNumberSplitting_homOfDegreewiseSplit_f_zero
    (i₀ : dualNumberLeftComplex ℚ ⟶ dualNumberMiddleComplex ℚ)
    (p₀ : dualNumberMiddleComplex ℚ ⟶ dualNumberRightComplex ℚ) (hip : i₀ ≫ p₀ = 0)
    (hi₁ : i₀.f 1 = 𝟙 _) (hp₀ : p₀.f 0 = 𝟙 _) :
    (CochainComplex.homOfDegreewiseSplit (ShortComplex.mk i₀ p₀ hip)
      (dualNumberSplitting i₀ p₀ hip hi₁ hp₀)).f 0 =
      ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing ℚ) DualNumber.eps) := by
  let S₀ := ShortComplex.mk i₀ p₀ hip
  let σ₀ := dualNumberSplitting i₀ p₀ hip hi₁ hp₀
  have hs₀ : (σ₀ 0).s = 𝟙 ((dualNumberRightComplex ℚ).X 0) := by
    have h := (σ₀ 0).s_g
    rw [show ((ShortComplex.mk i₀ p₀ hip).map (HomologicalComplex.eval (DualNumberModuleCat ℚ)
      (ComplexShape.up ℤ) 0)).g = 𝟙 _ from hp₀] at h
    exact (Category.comp_id ((σ₀ 0).s)).symm.trans h
  have hr₁ : (σ₀ 1).r = 𝟙 ((dualNumberLeftComplex ℚ).X 1) := by
    have h := (σ₀ 1).f_r
    rw [show ((ShortComplex.mk i₀ p₀ hip).map (HomologicalComplex.eval (DualNumberModuleCat ℚ)
      (ComplexShape.up ℤ) 1)).f = 𝟙 _ from hi₁] at h
    exact (Category.id_comp ((σ₀ 1).r)).symm.trans h
  have hd : (dualNumberMiddleComplex ℚ).d 0 1 =
      ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing ℚ) (DualNumber.eps)) := by
    simp [dualNumberMiddleComplex, dualNumberTwoTermComplex, CochainComplex.of.d,
      dualNumberRing]
  simp only [CochainComplex.homOfDegreewiseSplit_f]
  change (σ₀ 0).s ≫ S₀.X₂.d 0 1 ≫ (σ₀ 1).r = _
  rw [hs₀, hr₁, hd]
  change 𝟙 (ModuleCat.of (dualNumberRing ℚ) (dualNumberRing ℚ)) ≫
    ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing ℚ) DualNumber.eps) ≫
    𝟙 (ModuleCat.of (dualNumberRing ℚ) (dualNumberRing ℚ)) = _
  simp

private lemma dualNumberSplitting_homOfDegreewiseSplit_comp_shift_map
    (i₀ : dualNumberLeftComplex ℚ ⟶ dualNumberMiddleComplex ℚ)
    (p₀ : dualNumberMiddleComplex ℚ ⟶ dualNumberRightComplex ℚ) (hip : i₀ ≫ p₀ = 0)
    (hi₁ : i₀.f 1 = 𝟙 _) (hp₀ : p₀.f 0 = 𝟙 _)
    (a₀ : dualNumberLeftComplex ℚ ⟶ dualNumberLeftComplex ℚ)
    (ha₁ : a₀.f 1 = ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing ℚ)
      (1 + (DualNumber.eps : dualNumberRing ℚ)))) :
    CochainComplex.homOfDegreewiseSplit (ShortComplex.mk i₀ p₀ hip)
        (dualNumberSplitting i₀ p₀ hip hi₁ hp₀) ≫
        (shiftFunctor (CochainComplex (DualNumberModuleCat ℚ) ℤ) (1 : ℤ)).map a₀ =
      CochainComplex.homOfDegreewiseSplit (ShortComplex.mk i₀ p₀ hip)
        (dualNumberSplitting i₀ p₀ hip hi₁ hp₀) := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
    change (CochainComplex.homOfDegreewiseSplit (ShortComplex.mk i₀ p₀ hip)
      (dualNumberSplitting i₀ p₀ hip hi₁ hp₀)).f 0 ≫ a₀.f 1 = _
    rw [dualNumberSplitting_homOfDegreewiseSplit_f_zero, ha₁]
    exact ModuleCat.hom_ext dualNumber_eps_mul_comp
  · refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    have hz : Subsingleton ((dualNumberRightComplex ℚ).X n) := by
      have hx : (dualNumberRightComplex ℚ).X n = dualNumberZeroModule ℚ := by
        simp [dualNumberRightComplex, dualNumberTwoTermComplex, hn]
      rw [hx]
      infer_instance
    obtain rfl : x = 0 := hz.elim x 0
    simp

private lemma alternatingTrace_dualLeft.{u₁, v₁}
    (a₀ : dualNumberLeftComplex ℚ ⟶ dualNumberLeftComplex ℚ)
    (ha₁ : a₀.f 1 = ModuleCat.ofHom (LinearMap.mulLeft (dualNumberRing ℚ)
      (1 + (DualNumber.eps : dualNumberRing ℚ))))
    (ha_other : ∀ n : ℤ, n ≠ 1 → a₀.f n = 0)
    (hP : CategoryTheory.FilteredDerived.finiteProjectiveComplex dualRing.{u₁}
      (dualMapped.{u₁, v₁}.obj (dualNumberLeftComplex ℚ))) :
    CategoryTheory.FilteredDerived.alternatingTrace dualRing.{u₁} _ hP
      (dualMapped.{u₁, v₁}.map a₀) =
      -CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk dualRing.{u₁}
        (ULift.up (1 + (DualNumber.eps : DualNumber ℚ))) := by
  unfold CategoryTheory.FilteredDerived.alternatingTrace
  rw [finsum_eq_single _ (1 : ℤ)]
  · let : Module.Projective dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberLeftComplex ℚ)).X 1) := (hP.2 1).1
    let : Module.Finite dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberLeftComplex ℚ)).X 1) := (hP.2 1).2
    have hterm : Stacks.Trace.projectiveModuleTrace dualRing.{u₁}
        ((dualMapped.{u₁, v₁}.obj (dualNumberLeftComplex ℚ)).X 1)
        ((dualMapped.{u₁, v₁}.map a₀).f 1).hom =
        CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk dualRing
          (ULift.up (1 + (DualNumber.eps : DualNumber ℚ))) := by
      have hf : (dualMapped.{u₁, v₁}.map a₀).f 1 = (dualModuleFunctor.{u₁, v₁}).map
          (ModuleCat.ofHom
            (LinearMap.mulLeft dualBaseRing (1 + (DualNumber.eps : DualNumber ℚ)))) := by
        change (dualModuleFunctor.{u₁, v₁}).map (a₀.f 1) = _
        rw [ha₁]
        rfl
      rw [hf]
      exact dualRegular_projectiveTrace_map_mul.{u₁, v₁}
        (1 + (DualNumber.eps : DualNumber ℚ))
    rw [hterm]
    simp
  · intro n hn
    let : Module.Projective dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberLeftComplex ℚ)).X n) := (hP.2 n).1
    let : Module.Finite dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberLeftComplex ℚ)).X n) := (hP.2 n).2
    have hz : (dualMapped.{u₁, v₁}.map a₀).f n = 0 := by
      change (dualModuleFunctor.{u₁, v₁}).map (a₀.f n) = 0
      rw [ha_other n hn]
      exact Functor.map_zero _ _ _
    rw [hz]
    simp [Stacks.Trace.projectiveModuleTrace]

private lemma alternatingTrace_dualRight.{u₁, v₁}
    (hS : CategoryTheory.FilteredDerived.finiteProjectiveComplex dualRing.{u₁}
      (dualMapped.{u₁, v₁}.obj (dualNumberRightComplex ℚ))) :
    CategoryTheory.FilteredDerived.alternatingTrace dualRing.{u₁} _ hS
      (dualMapped.{u₁, v₁}.map (𝟙 (dualNumberRightComplex ℚ))) =
      CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk dualRing.{u₁}
        (ULift.up (1 : dualBaseRing)) := by
  unfold CategoryTheory.FilteredDerived.alternatingTrace
  rw [finsum_eq_single _ (0 : ℤ)]
  · let : Module.Projective dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberRightComplex ℚ)).X 0) := (hS.2 0).1
    let : Module.Finite dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberRightComplex ℚ)).X 0) := (hS.2 0).2
    have hterm : Stacks.Trace.projectiveModuleTrace dualRing
        ((dualMapped.{u₁, v₁}.obj (dualNumberRightComplex ℚ)).X 0)
        ((dualMapped.{u₁, v₁}.map (𝟙 (dualNumberRightComplex ℚ))).f 0).hom =
        CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk dualRing
          (ULift.up (1 : dualBaseRing)) := by
      change Stacks.Trace.projectiveModuleTrace dualRing.{u₁} dualRegular.{u₁, v₁}
        ((dualModuleFunctor.{u₁, v₁}).map (𝟙 (ModuleCat.of dualBaseRing dualBaseRing))).hom = _
      exact dualRegular_projectiveTrace_map_id
    rw [hterm]
    simp
  · intro n hn
    let : Module.Projective dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberRightComplex ℚ)).X n) := (hS.2 n).1
    let : Module.Finite dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberRightComplex ℚ)).X n) := (hS.2 n).2
    have hz := dualMapped_subsingleton.{u₁, v₁} (dualNumberRightComplex ℚ) (n := n)
      (by simp [dualNumberRightComplex, dualNumberTwoTermComplex, hn])
    rw [CategoryTheory.FilteredDerived.projectiveModuleTrace_eq_zero_of_subsingleton
      dualRing ((dualMapped.{u₁, v₁}.obj (dualNumberRightComplex ℚ)).X n)]
    split_ifs <;> simp

private lemma alternatingTrace_dualMiddle.{u₁, v₁}
    (hQ : CategoryTheory.FilteredDerived.finiteProjectiveComplex dualRing.{u₁}
      (dualMapped.{u₁, v₁}.obj (dualNumberMiddleComplex ℚ))) :
    CategoryTheory.FilteredDerived.alternatingTrace dualRing.{u₁} _ hQ
      (dualMapped.{u₁, v₁}.map (𝟙 (dualNumberMiddleComplex ℚ))) = 0 := by
  unfold CategoryTheory.FilteredDerived.alternatingTrace
  rw [finsum_eq_sum_of_support_subset (s := {0, 1})]
  · have hterm (n : ℤ) (hn : n = 0 ∨ n = 1) :
        let : Module.Projective dualRing
          ((dualMapped.{u₁, v₁}.obj (dualNumberMiddleComplex ℚ)).X n) := (hQ.2 n).1
        let : Module.Finite dualRing
          ((dualMapped.{u₁, v₁}.obj (dualNumberMiddleComplex ℚ)).X n) := (hQ.2 n).2
        Stacks.Trace.projectiveModuleTrace dualRing
          ((dualMapped.{u₁, v₁}.obj (dualNumberMiddleComplex ℚ)).X n)
          ((dualMapped.{u₁, v₁}.map (𝟙 (dualNumberMiddleComplex ℚ))).f n).hom =
          CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk dualRing
            (ULift.up (1 : dualBaseRing)) := by
      rcases hn with rfl | rfl <;>
        change Stacks.Trace.projectiveModuleTrace dualRing.{u₁} dualRegular.{u₁, v₁}
          ((dualModuleFunctor.{u₁, v₁}).map (𝟙 (ModuleCat.of dualBaseRing dualBaseRing))).hom = _
      all_goals exact dualRegular_projectiveTrace_map_id
    simp only [Finset.sum_pair zero_ne_one, hterm 0 (Or.inl rfl), hterm 1 (Or.inr rfl)]
    simp
  · intro n hn
    by_contra hmem
    obtain ⟨hn₀, hn₁⟩ : n ≠ 0 ∧ n ≠ 1 := by simpa using hmem
    let : Module.Projective dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberMiddleComplex ℚ)).X n) := (hQ.2 n).1
    let : Module.Finite dualRing
      ((dualMapped.{u₁, v₁}.obj (dualNumberMiddleComplex ℚ)).X n) := (hQ.2 n).2
    have hz := dualMapped_subsingleton.{u₁, v₁} (dualNumberMiddleComplex ℚ) (n := n)
      (by simp [dualNumberMiddleComplex, dualNumberTwoTermComplex, hn₀, hn₁])
    apply hn
    dsimp only
    rw [CategoryTheory.FilteredDerived.projectiveModuleTrace_eq_zero_of_subsingleton
      dualRing ((dualMapped.{u₁, v₁}.obj (dualNumberMiddleComplex ℚ)).X n)]
    split_ifs <;> simp

private lemma dualTrace_add_ne.{u₁}
    {x y z : CategoryTheory.FilteredDerived.AdditiveCommutatorQuotient dualRing.{u₁}}
    (hx : x = -CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk dualRing.{u₁}
      (ULift.up (1 + (DualNumber.eps : DualNumber ℚ))))
    (hy : y = CategoryTheory.FilteredDerived.additiveCommutatorQuotientMk dualRing.{u₁}
      (ULift.up (1 : dualBaseRing)))
    (hz : z = 0) : x + y ≠ z := by
  subst hx hy hz
  intro heq
  have hh := congrArg (fun x : dualRing.{u₁} => x.down.snd)
    (additiveCommutatorQuotientMk_injective dualRing (neg_add_eq_zero.mp heq))
  norm_num at hh

/-- Over `ULift (DualNumber ℚ)` there are a distinguished triangle of perfect complexes in the
homotopy category and an endomorphism of it whose alternating traces in `R/[R,R]` are not
additive. This is the witness of Stacks 087L; see
`exists_commRing_distinguished_triangle_trace_nonadditive`. -/
public theorem ulift_dualNumber_distinguished_triangle_trace_nonadditive.{u₁, v₁} :
    let R := ULift.{u₁} (DualNumber ℚ)
      ∃ (P Q S : CochainComplex (ModuleCat.{v₁} R) ℤ)
        (hP : CategoryTheory.FilteredDerived.finiteProjectiveComplex R P)
        (hQ : CategoryTheory.FilteredDerived.finiteProjectiveComplex R Q)
        (hS : CategoryTheory.FilteredDerived.finiteProjectiveComplex R S),
        let q := HomotopyCategory.quotient (ModuleCat.{v₁} R) (ComplexShape.up ℤ)
        ∃ (f : q.obj P ⟶ q.obj Q) (g : q.obj Q ⟶ q.obj S)
          (h : q.obj S ⟶ (q.obj P)⟦(1 : ℤ)⟧)
          (a : P ⟶ P) (b : Q ⟶ Q) (c : S ⟶ S),
          (Triangle.mk f g h ∈ distTriang _) ∧
          (∃ t : Triangle.mk f g h ⟶ Triangle.mk f g h,
            t.hom₁ = q.map a ∧ t.hom₂ = q.map b ∧ t.hom₃ = q.map c) ∧
          CategoryTheory.FilteredDerived.alternatingTrace R P hP a +
            CategoryTheory.FilteredDerived.alternatingTrace R S hS c ≠
            CategoryTheory.FilteredDerived.alternatingTrace R Q hQ b := by
  classical
  let F : (DualNumberModuleCat ℚ) ⥤ ModuleCat.{v₁} dualRing.{u₁} := dualModuleFunctor.{u₁, v₁}
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let H := F.mapHomotopyCategory (ComplexShape.up ℤ)
  let q₀ := HomotopyCategory.quotient.{0, 1, 0} (DualNumberModuleCat.{0, 0} ℚ) (ComplexShape.up ℤ)
  let q₁ := HomotopyCategory.quotient (ModuleCat.{v₁} dualRing.{u₁}) (ComplexShape.up ℤ)
  obtain ⟨i₀, p₀, a₀, hi₁, -, hp₀, -, ha₁, ha_other, hsq, hip⟩ :=
    dualNumber_diagram_commutes_up_to_homotopy ℚ
  let S₀ : ShortComplex (CochainComplex (DualNumberModuleCat ℚ) ℤ) := ShortComplex.mk i₀ p₀ hip
  let σ₀ := dualNumberSplitting i₀ p₀ hip hi₁ hp₀
  let T₀ := q₀.mapTriangle.obj (CochainComplex.triangleOfDegreewiseSplit S₀ σ₀)
  let δ₀ := CochainComplex.homOfDegreewiseSplit S₀ σ₀
  have hδ₀a : δ₀ ≫ (shiftFunctor (CochainComplex (DualNumberModuleCat ℚ) ℤ) (1 : ℤ)).map a₀ = δ₀ :=
    dualNumberSplitting_homOfDegreewiseSplit_comp_shift_map i₀ p₀ hip hi₁ hp₀ a₀ ha₁
  let t₀ : T₀ ⟶ T₀ :=
    { hom₁ := q₀.map a₀
      hom₂ := 𝟙 _
      hom₃ := 𝟙 _
      comm₁ := by
        change q₀.map i₀ = q₀.map a₀ ≫ q₀.map i₀
        exact hsq.symm
      comm₂ := by simp [T₀, S₀]
      comm₃ := by
        change (q₀.map δ₀ ≫ (q₀.commShiftIso (1 : ℤ)).hom.app S₀.X₁) ≫
            (shiftFunctor (HomotopyCategory (DualNumberModuleCat ℚ) (ComplexShape.up ℤ))
              (1 : ℤ)).map (q₀.map a₀) =
          𝟙 _ ≫ (q₀.map δ₀ ≫ (q₀.commShiftIso (1 : ℤ)).hom.app S₀.X₁)
        rw [Category.assoc, ← q₀.commShiftIso_hom_naturality a₀ (1 : ℤ), ← Category.assoc,
          ← q₀.map_comp, hδ₀a]
        simp [S₀] }
  let T := H.mapTriangle.obj T₀
  refine ⟨G.obj (dualNumberLeftComplex ℚ), G.obj (dualNumberMiddleComplex ℚ),
    G.obj (dualNumberRightComplex ℚ), dualMapped_twoTerm_perfect _ _ _ (Or.inl rfl) (Or.inr rfl),
    dualMapped_twoTerm_perfect _ _ _ (Or.inr rfl) (Or.inr rfl),
    dualMapped_twoTerm_perfect _ _ _ (Or.inr rfl) (Or.inl rfl), ?_⟩
  refine ⟨T.mor₁, T.mor₂, T.mor₃, G.map a₀, G.map (𝟙 _), G.map (𝟙 _), ?_,
    ⟨H.mapTriangle.map t₀, ?_, ?_, ?_⟩, ?_⟩
  · change T ∈ distTriang _
    exact H.map_distinguished T₀ (CochainComplex.trianglehOfDegreewiseSplit_distinguished S₀ σ₀)
  · change H.map (q₀.map a₀) = q₁.map (G.map a₀)
    exact Functor.mapHomotopyCategory_map F a₀
  · change H.map (𝟙 (q₀.obj (dualNumberMiddleComplex ℚ))) = q₁.map (G.map (𝟙 _))
    rw [← q₀.map_id]
    exact Functor.mapHomotopyCategory_map F _
  · change H.map (𝟙 (q₀.obj (dualNumberRightComplex ℚ))) = q₁.map (G.map (𝟙 _))
    rw [← q₀.map_id]
    exact Functor.mapHomotopyCategory_map F _
  · exact dualTrace_add_ne (alternatingTrace_dualLeft a₀ ha₁ ha_other _)
      (alternatingTrace_dualRight _) (alternatingTrace_dualMiddle _)

/-- Trace need not be additive on an endomorphism of a distinguished triangle of perfect
complexes in the homotopy category, for a ring `R` that is not required to be commutative and
traces in the additive commutator quotient `R/[R,R]`. This is weaker than Stacks 087L, whose rings
are commutative: see `exists_commRing_distinguished_triangle_trace_nonadditive` in
`StacksFrontier.Examples.Algebra.NonAdditivityOfTracesCommRing`. -/
public theorem exists_distinguished_triangle_trace_nonadditive :
    ∃ (R : Type u) (hR : Ring R),
      letI : Ring R := hR
      ∃ (P Q S : CochainComplex (ModuleCat.{v} R) ℤ)
        (hP : CategoryTheory.FilteredDerived.finiteProjectiveComplex R P)
        (hQ : CategoryTheory.FilteredDerived.finiteProjectiveComplex R Q)
        (hS : CategoryTheory.FilteredDerived.finiteProjectiveComplex R S),
        let q := HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)
        ∃ (f : q.obj P ⟶ q.obj Q) (g : q.obj Q ⟶ q.obj S)
          (h : q.obj S ⟶ (q.obj P)⟦(1 : ℤ)⟧)
          (a : P ⟶ P) (b : Q ⟶ Q) (c : S ⟶ S),
          (Triangle.mk f g h ∈ distTriang _) ∧
          (∃ t : Triangle.mk f g h ⟶ Triangle.mk f g h,
            t.hom₁ = q.map a ∧ t.hom₂ = q.map b ∧ t.hom₃ = q.map c) ∧
          CategoryTheory.FilteredDerived.alternatingTrace R P hP a +
            CategoryTheory.FilteredDerived.alternatingTrace R S hS c ≠
            CategoryTheory.FilteredDerived.alternatingTrace R Q hQ b :=
  ⟨dualRing.{u}, inferInstance, ulift_dualNumber_distinguished_triangle_trace_nonadditive.{u, v}⟩

end Stacks.Examples

end
