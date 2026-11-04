module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageSectionsGlobalFunctionsEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerAffineChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperChartVanishingIdealBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingOverOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairSpec
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingTowerEssentiallyConstant
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSectionsKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardAlgebraQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueingTowerRange

/-!
# The adic bound for `f : X' ⟶ X`, from Stacks 08AX and Stacks 08AR

In the situation of Stacks 0AGH with `X` quasi-compact this file proves
`AlgebraicGeometry.Space.CoequalizerGlueSituation.AdicKernelBound`, the one input of the last
step of the proof of Stacks 0AGK, and hence that step itself up to Stacks 0AGG.

Let `U = Spec R` be an affine étale chart of `X`, `I ⊆ R` the ideal of `Z` and
`B = Γ(X' ×_X U, 𝒪) = (f_* 𝒪_{X'})(U)`.

1. **Stacks 08AY (1) at `p = 0`.** There is a `c₁` with
   `Ker(B ⟶ Γ(X' ×_X Z_{k+1} ×_X U, 𝒪)) ⊆ Iᵏ⁺¹⁻ᶜ¹ B` for all `k`
   (`exists_mem_map_algebraMap_of_crossToModification_eq_zero`): a function in the kernel
   vanishes at every point of `X' ×_X U` over `Z_{k+1}`, so
   `AlgebraicGeometry.Space.exists_mem_map_pow_of_forall_eq_zero` applies, the defining ideal of
   `Z_{k+1}` at `U` being `Iᵏ⁺¹`.
2. **The cokernel of `R ⟶ B`.** There is a `t` with `Iᵗ B ⊆ im(R ⟶ B)`
   (`exists_pow_smul_mem_range_algebraMap`): `B` is finite over `R` (Stacks 08AR, through
   `AlgebraicGeometry.Space.isCoherent_pushforwardAlgebra`), and `R ⟶ B` becomes an
   isomorphism after inverting any element of `I`, since `f` is an isomorphism over `X ∖ Z`.
3. **Uniformity.** Both are proved on one surjective Noetherian affine chart `U`; the
   combined statement `Ker ⊆ im(Iᵏ⁺¹⁻ᶜ)`, `c = c₁ + t`, transfers to every affine chart over
   `U` because `f_* 𝒪_{X'}` and `(X' ×_X Z_{k+1} ⟶ X)_* 𝒪` are quasi-coherent and the rings of
   functions of affine charts are flat over each other, and every chart is covered by affine
   charts over `U`.

## Main results

* `AlgebraicGeometry.Space.CoequalizerGlueSituation.adicKernelBound`: the adic bound.
* `CoequalizerGlueSituation.exists_factorsThroughSection_of_properKernelPairCoequalizers`:
  Stacks 0AGK for the tower, from the conclusion of Stacks 0AGG alone, and
  `CoequalizerGlueSituation.exists_isEssentiallyConstantWith_of_properKernelPairCoequalizers`,
  Stacks 0AGL from it.

## References

* [Stacks Project, Tag 0AGK](https://stacks.math.columbia.edu/tag/0AGK)
* [Stacks Project, Tag 08AY](https://stacks.math.columbia.edu/tag/08AY)
* [Stacks Project, Tag 08AX](https://stacks.math.columbia.edu/tag/08AX)
* [Stacks Project, Tag 08AR](https://stacks.math.columbia.edu/tag/08AR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Two lemmas of commutative algebra -/

/-- If every element of an ideal `I` of a Noetherian ring has a power carrying a finite module
`B` into a submodule `N`, then some power of `I` carries `B` into `N`. -/
theorem _root_.Submodule.exists_pow_smul_mem_of_forall {R B : Type*} [CommRing R]
    [IsNoetherianRing R] [AddCommGroup B] [Module R B] [Module.Finite R B] (N : Submodule R B)
    (I : Ideal R) (h : ∀ g ∈ I, ∀ b : B, ∃ n : ℕ, g ^ n • b ∈ N) :
    ∃ t : ℕ, ∀ s ∈ I ^ t, ∀ b : B, s • b ∈ N := by
  have hrad : I ≤ (Module.annihilator R (B ⧸ N)).radical := by
    intro g hg
    obtain ⟨r, x, hx⟩ := Module.Finite.exists_fin (R := R) (M := B)
    choose n hn using fun i : Fin r => h g hg (x i)
    refine Ideal.mem_radical_iff.2 ⟨Finset.univ.sup n, Module.mem_annihilator.2 fun q => ?_⟩
    obtain ⟨b, rfl⟩ := Submodule.mkQ_surjective N q
    have hb : b ∈ Submodule.span R (Set.range x) := hx ▸ Submodule.mem_top
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.span_induction (p := fun b _ => g ^ Finset.univ.sup n • b ∈ N) ?_ ?_ ?_ ?_ hb
    · rintro _ ⟨i, rfl⟩
      have hle : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
      exact N.smul_mem _ (hn i)
    · simp
    · intro a b _ _ ha hb; rw [smul_add]; exact N.add_mem ha hb
    · intro c a _ ha; rw [smul_comm]; exact N.smul_mem c ha
  obtain ⟨t, ht⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian I)
  refine ⟨t, fun s hs b => ?_⟩
  have := Module.mem_annihilator.1 (ht hs) (Submodule.Quotient.mk b)
  rwa [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this

/-- If `Iᵗ A ⊆ im(R ⟶ A)` for a ring map `R ⟶ A`, then the ideal of `A` generated by the image
of `Iʲ` lies in the image of `Iʲ⁻ᵗ`. -/
theorem _root_.Ideal.exists_mem_pow_eq_of_mem_map_pow {R A : Type*} [CommRing R] [CommRing A]
    (alg : R →+* A) (I : Ideal R) {t j : ℕ} (htj : t ≤ j)
    (hcok : ∀ s ∈ I ^ t, ∀ b : A, ∃ r, alg r = alg s * b) {a : A}
    (ha : a ∈ Ideal.map alg (I ^ j)) : ∃ s ∈ I ^ (j - t), alg s = a := by
  let := alg.toAlgebra
  let N : Submodule R A := Submodule.map (Algebra.linearMap R A) (I ^ (j - t))
  have key : ∀ s ∈ I ^ j, ∀ b : A, b * alg s ∈ N := by
    intro s hs
    rw [show j = (j - t) + t by omega, pow_add] at hs
    refine Submodule.mul_induction_on hs (fun u hu v hv b => ?_) (fun x y hx hy b => ?_)
    · obtain ⟨r, hr⟩ := hcok v hv b
      exact ⟨u * r, Ideal.mul_mem_right _ _ hu, by
        change alg (u * r) = _
        rw [map_mul, map_mul, hr]; ring⟩
    · rw [map_add, mul_add]
      exact N.add_mem (hx b) (hy b)
  have : ∀ b : A, b * a ∈ N := by
    refine Submodule.span_induction (p := fun a _ => ∀ b : A, b * a ∈ N) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨s, hs, rfl⟩ b
      exact key s hs b
    · simp
    · intro x y _ _ hx hy b
      rw [mul_add]
      exact N.add_mem (hx b) (hy b)
    · intro c x _ hx b
      rw [smul_eq_mul, ← mul_assoc]
      exact hx _
  obtain ⟨s, hs, h⟩ := one_mul a ▸ this 1
  exact ⟨s, hs, h⟩

/-- A ring-level identity in an algebra sheaf: restriction of `c a - r`. -/
theorem AlgebraSheaf.map_algebraMap_mul_sub_algebraMap {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    (A : AlgebraSheaf.{u, u} B S hS F hF) {U V : (SmallEtale B S hS F)ᵒᵖ} (f : U ⟶ V)
    (c r : (structureSheaf B S hS F hF).obj.obj U) (b : A.right.obj.obj U) :
    A.right.obj.map f (A.algebraMap U c * b - A.algebraMap U r * 1) =
      A.algebraMap V ((structureSheaf B S hS F hF).obj.map f c) * A.right.obj.map f b -
        A.algebraMap V ((structureSheaf B S hS F hF).obj.map f r) := by
  rw [map_sub, map_mul, map_mul, map_one, mul_one, A.algebraMap_natural, A.algebraMap_natural]

namespace CoequalizerGlueSituation

variable (T : CoequalizerGlueSituation.{u})

/-! ### The defining ideal of `Z_{k+1}` on an affine chart -/

/-- On an affine chart `U`, the defining ideal of `Z_{k+1}` lies in `I(U)ᵏ⁺¹`. -/
theorem definingIdealAt_neighbourhood_le (k : ℕ) (U : SmallEtale T.B T.S T.hS T.X)
    (hU : IsAffine
      ((SmallEtale.toOver T.B T.S T.hS T.X ⋙ BigFppfOver.toScheme T.B T.S T.hS).obj U)) :
    definingIdealAt T.B T.S T.hS T.targetSpace (T.neighbourhood k) (op U) ≤
      chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U ^ (k + 1) := by
  have h1 : definingIdealAt T.B T.S T.hS T.targetSpace (T.neighbourhood k) (op U) =
      chartSubmodule T.B T.S T.hS T.X T.hX (idealPowSubmodule T.closedIdeal (k + 1)
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O))) U := by
    rw [T.idealPowSubmodule_closedIdeal_unit (k + 1)]
    exact congrArg (fun J => J.obj (op U)) (T.definingIdealSheaf_neighbourhood k)
  rw [h1, chartSubmodule_idealPowSubmodule_eq_of_isQuasicoherentOnSite T.B T.S T.hS T.X T.hX
    T.closedIdeal (k + 1) _ (SheafOfModules.isQuasicoherentOnSite_unit _)
    T.isQuasicoherentOnSite_closedIdeal U hU]
  refine Submodule.smul_le.2 fun r hr n _ => ?_
  exact Ideal.mul_mem_right (show chartRing T.B T.S T.hS T.X T.hX U from n) _ hr

/-! ### Functions in the kernel vanish over `Z_{k+1}` -/

/-- `f : X' ⟶ X` as a morphism of algebraic spaces. -/
abbrev modificationHom : T.modificationSpace ⟶ T.targetSpace := ObjectProperty.homMk T.f

omit T in
/-- The value of a regular function at two equal points. -/
theorem chartFunctions_val_congr {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (s : chartFunctions B S hS F)
    {b : BigFppfOver B S hS} {w w' : yoneda.obj b ⟶ F} (h : w = w') :
    s.val (op (CostructuredArrow.mk w)) = s.val (op (CostructuredArrow.mk w')) := by
  subst h
  rfl

/-- A point of an algebraic space, as a morphism from the represented algebraic space. -/
abbrev pointHom {b : BigFppfOver T.B T.S T.hS} {Q : AlgebraicSpaces T.B T.S T.hS}
    (y : yoneda.obj b ⟶ Q.1) : schemeSpace b ⟶ Q :=
  ObjectProperty.homMk y

/-- A point of `X' ×_X U` over `Z_{k+1}`, as a point of `X' ×_X Z_{k+1}`. -/
def crossChartLiftCross (k : ℕ) (U : SmallEtale T.B T.S T.hS T.X) {b : BigFppfOver T.B T.S T.hS}
    (y : yoneda.obj b ⟶ (chartBaseChangeSpace T.B T.S T.hS T.modificationHom U).1)
    (z : yoneda.obj b ⟶ (T.neighbourhood k).1.toFunctor)
    (hz : z ≫ (T.neighbourhood k).1.ι =
      y ≫ (chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U).hom ≫ T.f) :
    schemeSpace b ⟶ T.crossSpace k :=
  ObjectProperty.homMk (pullback.lift
    (y ≫ (chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U).hom) z
    ((Category.assoc _ _ _).trans hz.symm))

/-- The lift `crossChartLiftCross` followed by the projection to `X'` is the given point of
`X' ×_X U` followed by its inclusion into `X'`. -/
theorem crossChartLiftCross_comp (k : ℕ) (U : SmallEtale T.B T.S T.hS T.X)
    {b : BigFppfOver T.B T.S T.hS}
    (y : yoneda.obj b ⟶ (chartBaseChangeSpace T.B T.S T.hS T.modificationHom U).1)
    (z : yoneda.obj b ⟶ (T.neighbourhood k).1.toFunctor)
    (hz : z ≫ (T.neighbourhood k).1.ι =
      y ≫ (chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U).hom ≫ T.f) :
    T.crossChartLiftCross k U y z hz ≫ T.crossFst k =
      T.pointHom y ≫ chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U :=
  ObjectProperty.hom_ext _ (pullback.lift_fst _ _ _)

/-- The lift `crossChartLiftCross` followed by `X' ×_X Z_{k+1} ⟶ X` agrees with the given point
of `X' ×_X U` followed by the projection to `U` and the chart `U ⟶ X`. -/
theorem crossChartLiftCross_w (k : ℕ) (U : SmallEtale T.B T.S T.hS T.X)
    {b : BigFppfOver T.B T.S T.hS}
    (y : yoneda.obj b ⟶ (chartBaseChangeSpace T.B T.S T.hS T.modificationHom U).1)
    (z : yoneda.obj b ⟶ (T.neighbourhood k).1.toFunctor)
    (hz : z ≫ (T.neighbourhood k).1.ι =
      y ≫ (chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U).hom ≫ T.f) :
    T.crossChartLiftCross k U y z hz ≫ (T.crossOver k).hom =
      (T.pointHom y ≫ chartBaseChangeProjection T.B T.S T.hS T.modificationHom U) ≫
        chartToSpace T.B T.S T.hS T.targetSpace U := by
  change T.crossChartLiftCross k U y z hz ≫ T.crossFst k ≫ T.modificationHom = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ T.modificationHom) (T.crossChartLiftCross_comp k U y z hz)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun q => T.pointHom y ≫ q)
    (isPullback_chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U).w).trans ?_
  exact (Category.assoc _ _ _).symm

/-- A point of `X' ×_X U` over `Z_{k+1}` lifts to `(X' ×_X Z_{k+1}) ×_X U`. -/
def crossChartLift (k : ℕ) (U : SmallEtale T.B T.S T.hS T.X) {b : BigFppfOver T.B T.S T.hS}
    (y : yoneda.obj b ⟶ (chartBaseChangeSpace T.B T.S T.hS T.modificationHom U).1)
    (z : yoneda.obj b ⟶ (T.neighbourhood k).1.toFunctor)
    (hz : z ≫ (T.neighbourhood k).1.ι =
      y ≫ (chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U).hom ≫ T.f) :
    schemeSpace b ⟶ chartBaseChangeSpace T.B T.S T.hS (T.crossOver k).hom U :=
  (isPullback_chartBaseChangeInclusion T.B T.S T.hS (T.crossOver k).hom U).lift
    (T.crossChartLiftCross k U y z hz)
    (T.pointHom y ≫ chartBaseChangeProjection T.B T.S T.hS T.modificationHom U)
    (T.crossChartLiftCross_w k U y z hz)

/-- The lift `crossChartLift` followed by the map `(X' ×_X Z_{k+1}) ×_X U ⟶ X' ×_X U` is the
given point of `X' ×_X U`. -/
theorem crossChartLift_comp (k : ℕ) (U : SmallEtale T.B T.S T.hS T.X)
    {b : BigFppfOver T.B T.S T.hS}
    (y : yoneda.obj b ⟶ (chartBaseChangeSpace T.B T.S T.hS T.modificationHom U).1)
    (z : yoneda.obj b ⟶ (T.neighbourhood k).1.toFunctor)
    (hz : z ≫ (T.neighbourhood k).1.ι =
      y ≫ (chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U).hom ≫ T.f) :
    T.crossChartLift k U y z hz ≫
        chartBaseChangeSpaceMap T.B T.S T.hS (T.crossToModification k).left
          (Over.w (T.crossToModification k)) U =
      T.pointHom y := by
  refine (isPullback_chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U).hom_ext ?_ ?_
  · have h1 := chartBaseChangeSpaceMap_inclusion T.B T.S T.hS (T.crossToModification k).left
      (Over.w (T.crossToModification k)) U
    exact (Category.assoc _ _ _).trans ((congrArg (T.crossChartLift k U y z hz ≫ ·) h1).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ T.crossFst k)
        (IsPullback.lift_fst _ _ _ _)).trans (T.crossChartLiftCross_comp k U y z hz))))
  · have h1 := chartBaseChangeSpaceMap_projection T.B T.S T.hS (T.crossToModification k).left
      (Over.w (T.crossToModification k)) U
    exact (Category.assoc _ _ _).trans ((congrArg (T.crossChartLift k U y z hz ≫ ·) h1).trans
      (IsPullback.lift_snd _ _ _ _))

/-- **A function in the kernel of restriction to `X' ×_X Z_{k+1}` vanishes at every point of
`X' ×_X U` over `Z_{k+1}`.** -/
theorem globalFunctionsChartEquiv_eq_zero_of_crossToModification (k : ℕ)
    (U : SmallEtale T.B T.S T.hS T.X)
    (a : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op U))
    (ha : (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op U) a = 0)
    {b : BigFppfOver T.B T.S T.hS}
    (y : yoneda.obj b ⟶ (chartBaseChangeSpace T.B T.S T.hS T.modificationHom U).1)
    (z : yoneda.obj b ⟶ (T.neighbourhood k).1.toFunctor)
    (hz : z ≫ (T.neighbourhood k).1.ι =
      y ≫ (chartBaseChangeInclusion T.B T.S T.hS T.modificationHom U).hom ≫ T.f) :
    ((globalFunctionsChartEquiv T.B T.S T.hS
        (chartBaseChangeSpace T.B T.S T.hS T.modificationHom U)).val
      (directImageSectionsToGlobalFunctions T.B T.S T.hS T.modificationHom U a)).val
        (op (CostructuredArrow.mk y)) = 0 := by
  have hnat := directImageSectionsToGlobalFunctions_pushforwardAlgebraMap T.B T.S T.hS
    (T.crossToModification k) U a
  have h0 : ((pushforwardAlgebraMap T.B T.S T.hS (T.crossToModification k)).right.hom.app
      (op U)).hom a = 0 := ha
  rw [h0, map_zero] at hnat
  have hc := globalFunctionsMap_chart T.B T.S T.hS
    (chartBaseChangeSpaceMap T.B T.S T.hS (T.crossToModification k).left
      (Over.w (T.crossToModification k)) U)
    (directImageSectionsToGlobalFunctions T.B T.S T.hS T.modificationHom U a)
  rw [← hnat, map_zero] at hc
  have hy : ((T.crossChartLift k U y z hz).hom ≫
      (chartBaseChangeSpaceMap T.B T.S T.hS (T.crossToModification k).left
        (Over.w (T.crossToModification k)) U).hom : yoneda.obj b ⟶ _) = y :=
    congrArg (fun q => q.hom) (T.crossChartLift_comp k U y z hz)
  have hv := congrArg (fun s => s.val (op (CostructuredArrow.mk
    ((T.crossChartLift k U y z hz).hom : yoneda.obj b ⟶ _)))) hc
  refine (chartFunctions_val_congr _ hy.symm).trans ?_
  exact hv.symm

/-- The identification of the sections of `f_* 𝒪_{X'}` over `U` with the global functions of
`X' ×_X U` carries the structure map to pullback of functions along `X' ×_X U ⟶ U`. -/
theorem directImageSectionsToGlobalFunctions_comp_algebraMap (U : SmallEtale T.B T.S T.hS T.X) :
    (directImageSectionsToGlobalFunctions T.B T.S T.hS T.modificationHom U).comp
        ((pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op U)) =
      pullbackToGlobalFunctions T.B T.S T.hS (chartBaseChangeSpace T.B T.S T.hS T.modificationHom U)
        U.1.left (chartBaseChangeToScheme T.modificationHom U) := by
  refine RingHom.ext fun r => Subtype.ext (funext fun c => ?_)
  exact (directImageSectionsToGlobalFunctions_algebraMap T.B T.S T.hS T.modificationHom U c.unop
    r).trans (pullbackToGlobalFunctions_chartBaseChange_val T.modificationHom U c.unop r).symm

/-- **Stacks 08AY (1) at `p = 0`, on a Noetherian affine chart.** On a Noetherian affine étale
chart `U` of `X` there is a `c₁` such that for every `k` with `c₁ ≤ k + 1`, a section of
`f_* 𝒪_{X'}` over `U` killed by restriction to `X' ×_X Z_{k+1}` lies in
`I(U)ᵏ⁺¹⁻ᶜ¹ · (f_* 𝒪_{X'})(U)`. -/
theorem exists_mem_map_algebraMap_of_crossToModification_eq_zero (U : SmallEtale T.B T.S T.hS T.X)
    (hU : IsNoetherianAffineChart T.B T.S T.hS T.X U) :
    ∃ c₁ : ℕ, ∀ k : ℕ, c₁ ≤ k + 1 →
      ∀ a : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op U),
        (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op U) a = 0 →
        a ∈ Ideal.map ((pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op U))
          (chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U ^ (k + 1 - c₁)) := by
  have : IsAffine ((BigFppfOver.toScheme T.B T.S T.hS).obj U.1.left) := hU.1
  have : IsLocallyNoetherian ((BigFppfOver.toScheme T.B T.S T.hS).obj U.1.left) :=
    isLocallyNoetherian_chart T.B T.S T.hS (Y := T.targetSpace) T.locallyNoetherian U
  obtain ⟨c, hc⟩ := exists_mem_map_pow_of_forall_eq_zero T.modificationHom U T.hf
    (chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U)
  refine ⟨c, fun k hk a ha => ?_⟩
  have hx := hc (k + 1) hk (T.neighbourhood k) (T.definingIdealAt_neighbourhood_le k U hU.1)
    (directImageSectionsToGlobalFunctions T.B T.S T.hS T.modificationHom U a)
    (fun b y z hz => T.globalFunctionsChartEquiv_eq_zero_of_crossToModification k U a ha y z hz)
  let e := directImageSectionsGlobalFunctionsEquiv T.B T.S T.hS T.modificationHom U
  rw [← T.directImageSectionsToGlobalFunctions_comp_algebraMap U] at hx
  have hle : Ideal.map ((directImageSectionsToGlobalFunctions T.B T.S T.hS T.modificationHom U).comp
      ((pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op U)))
        (chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U ^ (k + 1 - c)) ≤
      Ideal.map e (Ideal.map ((pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap
        (op U)) (chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U ^ (k + 1 - c))) :=
    Ideal.map_le_iff_le_comap.2 fun r hr =>
      Ideal.mem_map_of_mem e (Ideal.mem_map_of_mem _ hr)
  obtain ⟨a', ha', hea⟩ := (Ideal.mem_map_of_equiv e _).1 (hle hx)
  rwa [e.injective hea] at ha'

/-! ### The structure map is surjective away from `Z` -/

/-- **`f` is a monomorphism over `U`**: two morphisms to `X'` with the same composite to `X`,
landing in `U`, agree. -/
theorem eq_of_comp_f_eq_comp_ι {P : (BigFppfOver T.B T.S T.hS)ᵒᵖ ⥤ Type u} (a a' : P ⟶ T.X')
    (t : P ⟶ T.U.toFunctor) (ha : a ≫ T.f = t ≫ T.U.ι) (ha' : a' ≫ T.f = t ≫ T.U.ι) :
    a = a' := by
  have := T.f_iso_over_U
  have h : pullback.lift a t ha = pullback.lift a' t ha' :=
    (cancel_mono (pullback.snd T.f T.U.ι)).1 (by rw [pullback.lift_snd, pullback.lift_snd])
  have h' := congrArg (· ≫ pullback.fst T.f T.U.ι) h
  simpa only [pullback.lift_fst] using h'

/-- **On a chart on which `𝓘` is the unit ideal, `𝒪_X ⟶ f_* 𝒪_{X'}` is surjective**: the chart
factors through `U`, over which `f` has a section, and that section identifies `X' ×_X V` with
`V`. -/
theorem surjective_algebraMap_of_closedIdeal_obj_eq_top (V : SmallEtale T.B T.S T.hS T.X)
    (hV : T.closedIdeal.obj (op V) = ⊤) :
    Function.Surjective
      ((pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op V)) := by
  obtain ⟨g, hg⟩ := (factorsThrough_openSubspace_iff_points T.B T.S T.hS T.hX
    (isAlgebraicSpace_yoneda T.B T.S T.hS _) T.U T.hU V.1.hom).2
      (T.range_subset_open_of_closedIdeal_obj_eq_top V hV)
  let σ : yoneda.obj V.1.left ⟶ T.X' := g ≫ T.sectionOverU
  have hσ : σ ≫ T.f = V.1.hom := by
    change (g ≫ T.sectionOverU) ≫ T.f = V.1.hom
    rw [Category.assoc, T.sectionOverU_comp_f, hg]
  let s : schemeSpace V.1.left ⟶ chartBaseChangeSpace T.B T.S T.hS T.modificationHom V :=
    (isPullback_chartBaseChangeInclusion T.B T.S T.hS T.modificationHom V).lift (T.pointHom σ)
      (𝟙 (schemeSpace V.1.left)) (ObjectProperty.hom_ext _ (hσ.trans (Category.id_comp _).symm))
  have hsp : s ≫ chartBaseChangeProjection T.B T.S T.hS T.modificationHom V =
      𝟙 (schemeSpace V.1.left) := IsPullback.lift_snd _ _ _ _
  have hsi : s ≫ chartBaseChangeInclusion T.B T.S T.hS T.modificationHom V = T.pointHom σ :=
    IsPullback.lift_fst _ _ _ _
  have hw : (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom ≫ V.1.hom =
      (chartBaseChangeInclusion T.B T.S T.hS T.modificationHom V).hom ≫ T.f :=
    congrArg (fun k => k.hom)
      (isPullback_chartBaseChangeInclusion T.B T.S T.hS T.modificationHom V).w.symm
  have hsec : ∀ {b : BigFppfOver T.B T.S T.hS}
      (y : yoneda.obj b ⟶ (chartBaseChangeSpace T.B T.S T.hS T.modificationHom V).1),
      (y ≫ (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom) ≫ s.hom = y := by
    intro b y
    have hsp' : s.hom ≫ (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom =
        𝟙 _ := congrArg (fun k => k.hom) hsp
    have hsi' : s.hom ≫ (chartBaseChangeInclusion T.B T.S T.hS T.modificationHom V).hom = σ :=
      congrArg (fun k => k.hom) hsi
    refine (isPullback_chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (fun q => (y ≫
        (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom) ≫ q) hsp').trans
          (Category.comp_id _))
    · refine (Category.assoc _ _ _).trans ((congrArg (fun q => (y ≫
        (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom) ≫ q) hsi').trans ?_)
      refine T.eq_of_comp_f_eq_comp_ι _ _
        (y ≫ (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom ≫ g) ?_ ?_
      · exact (Category.assoc _ _ _).trans ((congrArg (fun q => (y ≫
          (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom) ≫ q)
            (hσ.trans hg.symm)).trans ((Category.assoc _ _ _).trans
              (congrArg (fun q => y ≫ q) (Category.assoc _ _ _).symm)))
      · exact (Category.assoc _ _ _).trans (congrArg (fun q => y ≫ q)
          (hw.symm.trans ((congrArg (fun q =>
            (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom ≫ q) hg.symm).trans
              (Category.assoc _ _ _).symm)))
  intro b
  let x := (globalFunctionsChartEquiv T.B T.S T.hS
    (chartBaseChangeSpace T.B T.S T.hS T.modificationHom V)).val
      (directImageSectionsToGlobalFunctions T.B T.S T.hS T.modificationHom V b)
  refine ⟨x.val (op (CostructuredArrow.mk s.hom)),
    injective_directImageSectionsToGlobalFunctions T.B T.S T.hS T.modificationHom V
      (Subtype.ext (funext fun c => ?_))⟩
  obtain ⟨c⟩ := c
  refine (directImageSectionsToGlobalFunctions_algebraMap T.B T.S T.hS T.modificationHom V c
    _).trans ?_
  have hval : x.val (op (CostructuredArrow.mk c.1.hom)) =
      (directImageSectionsToGlobalFunctions T.B T.S T.hS T.modificationHom V b).1 (op c) :=
    congrArg (fun z => z.1 (op c)) ((globalFunctionsChartEquiv T.B T.S T.hS
      (chartBaseChangeSpace T.B T.S T.hS T.modificationHom V)).property
        (directImageSectionsToGlobalFunctions T.B T.S T.hS T.modificationHom V b))
  refine Eq.trans ?_ hval
  let k := smallEtaleChartMapToBase T.B T.S T.hS
    (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom c
  have hk : yoneda.map k ≫ s.hom = c.1.hom := by
    rw [show yoneda.map k = c.1.hom ≫
      (chartBaseChangeProjection T.B T.S T.hS T.modificationHom V).hom from
        yoneda_map_smallEtaleChartMapToBase T.B T.S T.hS _ c]
    exact hsec c.1.hom
  refine Eq.trans ?_ (chartFunctions_val_congr x hk)
  exact x.property (CostructuredArrow.homMk k rfl :
    CostructuredArrow.mk (yoneda.map k ≫ s.hom) ⟶ CostructuredArrow.mk s.hom).op

/-! ### The cokernel of `𝒪_X ⟶ f_* 𝒪_{X'}` is killed by a power of `𝓘` -/

/-- `f_* 𝒪_{X'}` as an `𝒪_X`-module. -/
abbrev modificationModule : Modules.{u, u} T.B T.S T.hS T.X T.hX :=
  (pushforwardAlgebra T.B T.S T.hS T.modificationOver).underlyingModule

/-- The unit section of `f_* 𝒪_{X'}` over a chart. -/
abbrev modificationModuleOne (U : SmallEtale T.B T.S T.hS T.X) :
    T.modificationModule.val.obj (op U) :=
  (1 : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op U))

/-- `f_* 𝒪_{X'}` is a coherent `𝒪_X`-module. -/
theorem isCoherent_modificationModule :
    IsCoherent T.B T.S T.hS T.X T.hX T.modificationModule :=
  isCoherent_pushforwardAlgebra T.modificationHom T.hf T.locallyNoetherian

/-- `f_* 𝒪_{X'}` is cartesian on affine charts. -/
theorem isCartesianOnAffineCharts_modificationModule :
    IsCartesianOnAffineCharts T.modificationModule :=
  isCartesianOnAffineCharts_of_isQuasicoherentOnSite T.B T.S T.hS T.X T.hX _
    T.isCoherent_modificationModule.toIsQuasicoherentOnSite

/-- **Away from `Z`, a power of a function of `𝓘` carries every section into the image of
`𝒪_X`.** On a Noetherian affine chart `U` and for `g ∈ 𝓘(U)`, every section `b` of
`f_* 𝒪_{X'}` over `U` has `gⁿ b` in the image of `𝒪_X(U)` for some `n`: over the chart `D(g)`
the structure map is surjective, and the sections there are the localization of those over `U`.
-/
theorem exists_pow_smul_mem_span_one (U : SmallEtale T.B T.S T.hS T.X)
    (hU : IsNoetherianAffineChart T.B T.S T.hS T.X U) (g : chartRing T.B T.S T.hS T.X T.hX U)
    (hg : g ∈ chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U)
    (b : T.modificationModule.val.obj (op U)) :
    ∃ n : ℕ, g ^ n • b ∈ Submodule.span (chartRing T.B T.S T.hS T.X T.hX U)
      {T.modificationModuleOne U} := by
  have hUaff : IsAffine (chartScheme U) := hU.1
  let V := openChart T.B T.S T.hS T.X U ((chartScheme U).basicOpen g)
  let j := openChartInclusion T.B T.S T.hS T.X U ((chartScheme U).basicOpen g)
  let := chartAlgebra (hF := T.hX) j
  have hloc := isLocalization_away_chartRing_basicOpen (hF := T.hX) hUaff g
  have hunit : IsUnit (chartRestrict (hF := T.hX) j g) :=
    IsLocalization.map_units (M := Submonoid.powers g)
      (chartRing T.B T.S T.hS T.X T.hX V) ⟨g, Submonoid.mem_powers g⟩
  have htop : T.closedIdeal.obj (op V) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (Stacks.Sites.map_mem_sectionIdeal T.closedIdeal j.op hg) hunit
  have hVaff : IsAffine (chartScheme V) := (isAffineOpen_top (chartScheme U)).basicOpen g
  obtain ⟨ρ, hρ⟩ := T.surjective_algebraMap_of_closedIdeal_obj_eq_top V htop
    (chartRestrictLinear T.modificationModule j b)
  obtain ⟨⟨r, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.mk'_surjective
    (S := chartRing T.B T.S T.hS T.X T.hX V) (Submonoid.powers g)
    (ρ : chartRing T.B T.S T.hS T.X T.hX V)
  have hr' : IsLocalization.mk' (chartRing T.B T.S T.hS T.X T.hX V) r
      (⟨g ^ n, n, rfl⟩ : Submonoid.powers g) = ρ := hr
  have hspec := IsLocalization.mk'_spec (chartRing T.B T.S T.hS T.X T.hX V) r
    (⟨g ^ n, n, rfl⟩ : Submonoid.powers g)
  rw [hr'] at hspec
  let A := pushforwardAlgebra T.B T.S T.hS T.modificationOver
  let x : T.modificationModule.val.obj (op U) := g ^ n • b - r • T.modificationModuleOne U
  have hx : chartRestrictLinear T.modificationModule j x = 0 := by
    refine (AlgebraSheaf.map_algebraMap_mul_sub_algebraMap A j.op (g ^ n) r b).trans ?_
    have hb : A.right.obj.map j.op b = A.algebraMap (op V) ρ := hρ.symm
    rw [hb, ← map_mul, ← map_sub]
    have h0 : ((structureSheaf T.B T.S T.hS T.X T.hX).obj.map j.op (g ^ n)) * ρ -
        (structureSheaf T.B T.S T.hS T.X T.hX).obj.map j.op r = 0 :=
      sub_eq_zero.2 ((mul_comm _ _).trans hspec)
    rw [h0, map_zero]
    rfl
  have htens : TensorProduct.mk (chartRing T.B T.S T.hS T.X T.hX U)
      (chartRing T.B T.S T.hS T.X T.hX V) (T.modificationModule.val.obj (op U)) 1 x = 0 := by
    refine (T.isCartesianOnAffineCharts_modificationModule U V hUaff hVaff j).1 ?_
    rw [map_zero]
    exact (chartBaseChange_one_tmul T.modificationModule j x).trans hx
  have : IsLocalizedModule (Submonoid.powers g) (TensorProduct.mk
      (chartRing T.B T.S T.hS T.X T.hX U) (chartRing T.B T.S T.hS T.X T.hX V)
        (T.modificationModule.val.obj (op U)) 1) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g) _ _).2
      (TensorProduct.isBaseChange _ _ _)
  obtain ⟨⟨c, ⟨m, rfl⟩⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers g)
    (f := TensorProduct.mk (chartRing T.B T.S T.hS T.X T.hX U)
      (chartRing T.B T.S T.hS T.X T.hX V) (T.modificationModule.val.obj (op U)) 1)
    (htens.trans (map_zero _).symm)
  refine ⟨m + n, ?_⟩
  have : g ^ (m + n) • b = (g ^ m * r) • T.modificationModuleOne U := by
    rw [pow_add, mul_smul, mul_smul, ← sub_eq_zero, ← smul_sub]
    rwa [Submonoid.smul_def, Submonoid.smul_def, smul_zero] at hc
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **The cokernel of `R ⟶ B` is killed by a power of `I`**, on a Noetherian affine chart. -/
theorem exists_pow_mul_mem_range_algebraMap (U : SmallEtale T.B T.S T.hS T.X)
    (hU : IsNoetherianAffineChart T.B T.S T.hS T.X U) :
    ∃ t : ℕ, ∀ s ∈ chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U ^ t,
      ∀ b : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op U),
        ∃ r, (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op U) r =
          (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op U) s * b := by
  have : IsNoetherianRing (chartRing T.B T.S T.hS T.X T.hX U) := hU.2
  have : Module.Finite (chartRing T.B T.S T.hS T.X T.hX U)
      (T.modificationModule.val.obj (op U)) :=
    moduleFinite_sections_of_isNoetherianAffineChart T.B T.S T.hS T.X T.hX _
      T.isCoherent_modificationModule hU
  obtain ⟨t, ht⟩ := Submodule.exists_pow_smul_mem_of_forall
    (Submodule.span (chartRing T.B T.S T.hS T.X T.hX U) {T.modificationModuleOne U})
    (chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U)
    (fun g hg b => T.exists_pow_smul_mem_span_one U hU g hg b)
  refine ⟨t, fun s hs b => ?_⟩
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (ht s hs b)
  exact ⟨r, (mul_one _).symm.trans hr⟩

/-- **Stacks 08AY (1) at `p = 0` and the cokernel bound, on a Noetherian affine chart.** There is
a `c` such that for `k ≥ c` a section of `f_* 𝒪_{X'}` over `U` killed by restriction to
`X' ×_X Z_{k+1}` is the image of a section of `I(U)ᵏ⁺¹⁻ᶜ`. -/
theorem exists_eq_algebraMap_of_crossToModification_eq_zero (U : SmallEtale T.B T.S T.hS T.X)
    (hU : IsNoetherianAffineChart T.B T.S T.hS T.X U) :
    ∃ c : ℕ, ∀ k : ℕ, c ≤ k →
      ∀ a : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op U),
        (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op U) a = 0 →
        ∃ s ∈ chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U ^ (k + 1 - c),
          (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op U) s = a := by
  obtain ⟨c₁, hc₁⟩ := T.exists_mem_map_algebraMap_of_crossToModification_eq_zero U hU
  obtain ⟨t, ht⟩ := T.exists_pow_mul_mem_range_algebraMap U hU
  refine ⟨c₁ + t, fun k hk a ha => ?_⟩
  obtain ⟨s, hs, e⟩ := Ideal.exists_mem_pow_eq_of_mem_map_pow _ _ (t := t) (j := k + 1 - c₁)
    (by omega) ht (hc₁ k (by omega) a ha)
  exact ⟨s, by rwa [show k + 1 - c₁ - t = k + 1 - (c₁ + t) by omega] at hs, e⟩

/-! ### Uniformity -/

/-- `(X' ×_X Z_{k+1} ⟶ X)_* 𝒪` as an `𝒪_X`-module. -/
abbrev crossModule (k : ℕ) : Modules.{u, u} T.B T.S T.hS T.X T.hX :=
  (pushforwardAlgebra T.B T.S T.hS (T.crossOver k)).underlyingModule

/-- Restriction `f_* 𝒪_{X'} ⟶ (X' ×_X Z_{k+1} ⟶ X)_* 𝒪`, as a morphism of `𝒪_X`-modules. -/
abbrev crossRestriction (k : ℕ) : T.modificationModule ⟶ T.crossModule k :=
  AlgebraSheaf.underlyingModuleMap (pushforwardAlgebraMap T.B T.S T.hS (T.crossToModification k))

/-- The morphism `X' ×_X Z_{k+1} ⟶ X` is proper. -/
theorem isProper_crossOver_hom (k : ℕ) : IsProper T.B T.S T.hS (T.crossOver k).hom.hom := by
  have h1 : IsProper T.B T.S T.hS (T.crossFst k).hom :=
    isProper_of_isPullback T.B T.S T.hS (T.crossSpace k).2 (T.neighbourhoodSystem.space k).2
      T.hX' T.hX (IsPullback.of_hasPullback T.f (T.neighbourhoodSystem.toTarget k).hom).flip
      (isProper_of_isClosedImmersion T.B T.S T.hS (T.neighbourhoodSystem.space k).2 T.hX _
        (T.neighbourhoodSystem.isClosedImmersion_toTarget k))
  exact isProper_comp T.B T.S T.hS (T.crossSpace k).2 T.hX' T.hX _ _ h1 T.hf

/-- `(X' ×_X Z_{k+1} ⟶ X)_* 𝒪` is cartesian on affine charts. -/
theorem isCartesianOnAffineCharts_crossModule (k : ℕ) :
    IsCartesianOnAffineCharts (T.crossModule k) :=
  isCartesianOnAffineCharts_of_isQuasicoherentOnSite T.B T.S T.hS T.X T.hX _
    (isQuasicoherent_pushforwardAlgebra_of_qcqs T.B T.S T.hS (T.crossOver k).hom
      (T.isProper_crossOver_hom k).2.1.2
      (isQuasiSeparated_of_isSeparated T.B T.S T.hS (T.isProper_crossOver_hom k).1))

/-- **Transfer to an affine chart over `U`.** The image statement on `U` holds, with the same
exponent, on every affine chart `A` over `U`: the sections of the kernel of restriction to
`X' ×_X Z_{k+1}` over `A` are the base change of those over `U`. -/
theorem exists_eq_algebraMap_of_chartHom (k j : ℕ) {U A : SmallEtale T.B T.S T.hS T.X}
    (e : A ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver T.B T.S T.hS T.X ⋙ BigFppfOver.toScheme T.B T.S T.hS).obj U))
    (hA : IsAffine ((SmallEtale.toOver T.B T.S T.hS T.X ⋙ BigFppfOver.toScheme T.B T.S T.hS).obj A))
    (hUk : ∀ a : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op U),
      (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op U) a = 0 →
      ∃ s ∈ chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal U ^ j,
        (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op U) s = a)
    (a : (pushforwardAlgebra T.B T.S T.hS T.modificationOver).right.obj.obj (op A))
    (ha : (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op A) a = 0) :
    ∃ s ∈ chartSectionIdeal T.B T.S T.hS T.X T.hX T.closedIdeal A ^ j,
      (pushforwardAlgebra T.B T.S T.hS T.modificationOver).algebraMap (op A) s = a := by
  let φ := T.crossRestriction k
  let F := pushforwardAlgebra T.B T.S T.hS T.modificationOver
  have hK := isCartesianOnAffineCharts_kernel φ T.isCartesianOnAffineCharts_modificationModule
    (T.isCartesianOnAffineCharts_crossModule k) U A hU hA e
  obtain ⟨κ, rfl⟩ := (SheafOfModules.exact_kernel_ι_val_app φ (op A) a).1 ha
  obtain ⟨t, rfl⟩ := hK.2 κ
  clear ha
  let := chartAlgebra (hF := T.hX) e
  induction t using TensorProduct.induction_on with
  | zero =>
    refine ⟨0, Ideal.zero_mem _, ?_⟩
    rw [map_zero, map_zero]
    exact map_zero _
  | tmul c κ' =>
    have h1 : φ.val.app (op U) ((kernel.ι φ).val.app (op U) κ') = 0 :=
      congrArg (fun m => (m.val.app (op U)) κ') (kernel.condition φ)
    obtain ⟨s₀, hs₀, hs₀e⟩ := hUk _ h1
    refine ⟨c * chartRestrict (hF := T.hX) e s₀,
      Ideal.mul_mem_left _ c (chartRestrict_mem_pow_chartSectionIdeal T.B T.S T.hS T.X T.hX
        T.closedIdeal e j hs₀), ?_⟩
    have hR : (kernel.ι φ).val.app (op A) (sectionsBaseChange (kernel φ) e (c ⊗ₜ κ')) =
        F.algebraMap (op A) c * F.right.obj.map e.op (F.algebraMap (op U) s₀) := by
      rw [chartBaseChange_tmul, map_smul]
      exact congrArg (fun z => c • z)
        ((PresheafOfModules.naturality_apply (kernel.ι φ).val e.op κ').trans
          (congrArg (fun z => T.modificationModule.val.map e.op z) hs₀e.symm))
    exact (((F.algebraMap (op A)).map_mul c (chartRestrict (hF := T.hX) e s₀)).trans
      (congrArg (F.algebraMap (op A) c * ·) (F.algebraMap_natural e.op s₀).symm)).trans hR.symm
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, e₂⟩ := h₂
    refine ⟨s₁ + s₂, Ideal.add_mem _ hs₁ hs₂, ?_⟩
    refine ((F.algebraMap (op A)).map_add s₁ s₂).trans ((congrArg₂ (· + ·) e₁ e₂).trans ?_)
    exact ((congrArg (fun z => (kernel.ι φ).val.app (op A) z)
      (map_add (sectionsBaseChange (kernel φ) e) t₁ t₂)).trans
        (map_add ((kernel.ι φ).val.app (op A)).hom _ _)).symm

/-- **The adic bound** (`AdicKernelBound`), for `X` quasi-compact: Stacks 08AY (1) at `p = 0`
and the finiteness of Stacks 08AR, made uniform over `X`. -/
theorem adicKernelBound (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X) : T.AdicKernelBound := by
  obtain ⟨U, hUN, hUsurj, -⟩ := exists_surjective_isNoetherianAffineChart_of_isQuasiCompactSpace
    T.B T.S T.hS T.targetSpace hqc T.locallyNoetherian
  obtain ⟨c, hc⟩ := T.exists_eq_algebraMap_of_crossToModification_eq_zero U hUN
  refine ⟨c, fun k hk V a ha => ?_⟩
  obtain ⟨Sv, hSv, hfac⟩ := exists_covering_through_affine_over T.B T.S T.hS T.X U hUsurj V
  refine ⟨Sv, hSv, fun W h hh => ?_⟩
  obtain ⟨A, l, m, e, hA, rfl⟩ := hfac h hh
  let F := pushforwardAlgebra T.B T.S T.hS T.modificationOver
  have haA : (pushforwardRingMap T.B T.S T.hS (T.crossToModification k)).hom.app (op A)
      (F.right.obj.map m.op a) = 0 := by
    rw [sheafHom_app_map, ha, map_zero]
  obtain ⟨s, hs, hsa⟩ := T.exists_eq_algebraMap_of_chartHom k (k + 1 - c) e hUN.1 hA (hc k hk)
    _ haA
  refine ⟨(structureSheaf T.B T.S T.hS T.X T.hX).obj.map l.op s,
    (Stacks.Sites.idealPow (O := (smallEtaleRingedSite T.B T.S T.hS T.X T.hX).O)
      T.closedIdeal (k + 1 - c)).map_mem l.op
        (pow_chartSectionIdeal_le_chartIdealPow T.B T.S T.hS T.X T.hX T.closedIdeal _ A hs), ?_⟩
  rw [op_comp, Functor.map_comp, CommRingCat.comp_apply, ← hsa]
  exact F.algebraMap_natural l.op s

/-- **Stacks 0AGK for the tower, from the conclusion of Stacks 0AGG.** For `X` quasi-compact and
any choice of coequalizers `X_n` along the infinitesimal neighbourhoods `Z_n` of `Z`, for all `n`
large enough there is an `m` such that `X_n ⟶ X_{n+m}` factors through a closed immersion
`X ⟶ X_{n+m}`, a section of `X_{n+m} ⟶ X`. -/
theorem exists_factorsThroughSection_of_properKernelPairCoequalizers
    (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)
    (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X)
    (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n)) :
    ∃ n₀, ∀ n, n₀ ≤ n → ∃ m, T.neighbourhoodSystem.FactorsThroughSection D n m :=
  T.exists_factorsThroughSection_of_adicKernelBound hAGG D hqc (T.adicKernelBound hqc)

/-- **Stacks 0AGL for the tower, from the conclusion of Stacks 0AGG.** For `X` quasi-compact the
system `X_1 ⟶ X_2 ⟶ X_3 ⟶ …` of coequalizers along the infinitesimal neighbourhoods of `Z` is
essentially constant with value `X` (Stacks 05PU(1)) with respect to the cocone of the morphisms
`X_n ⟶ X`. -/
theorem exists_isEssentiallyConstantWith_of_properKernelPairCoequalizers
    (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS)
    (hqc : IsQuasiCompactSpace T.B T.S T.hS T.X)
    (D : ∀ n, KernelPairCoequalizer T.B T.S T.hS (T.neighbourhoodSystem.glueMapAt n)) :
    ∃ (i : ℕ) (r : T.targetSpace ⟶ (D i).space),
      CategoryTheory.EssentiallyConstantInd.IsEssentiallyConstantWith
        (T.neighbourhoodSystem.towerDiagram D)
        (T.neighbourhoodSystem.towerCocone D) i r :=
  T.neighbourhoodSystem.exists_isEssentiallyConstantWith_towerCocone D
    (T.exists_factorsThroughSection_of_properKernelPairCoequalizers hAGG hqc D)

end CoequalizerGlueSituation

end AlgebraicGeometry.Space

end
