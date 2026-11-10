module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RetractionStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.NilpotentApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.TensorByBaseModuleAffineChartComparison
public import StacksFrontier.AlgebraicGeometry.Quot.TwistedEulerCharacteristic
public import StacksFrontier.Deformation.ToposThickening.SplitSquareZeroExtension
public import StacksFrontier.Deformation.ToposThickening.CoefficientSquareZeroReduction

/-!
# The ideal of a thickening with a retraction, base changed from a split thickening of schemes

Let `i : X ⟶ X'` be a thickening of algebraic spaces with a retraction `q : X' ⟶ X`, and suppose
the pair is the base change of a pair of morphisms `β : T₀ ⟶ T`, `τ : T ⟶ T₀` of affine schemes of
the site with `β ≫ τ = 𝟙`: `q` is the base change of `τ` along `p : X ⟶ T₀` and `i ≫ p' = p ≫ β`.
On the small étale site of `X` the structure sheaf of `X'` is the sheaf of rings
`A = q_* 𝒪_{X'}` (`AlgebraicGeometry.Space.thickeningRetractionRing`) with the section
`s : 𝒪_X ⟶ A` and the restriction `r : A ⟶ 𝒪_X`. Let `R ≅ Γ(T₀)` and let `j : M ⟶ Γ(T)` be an
`R`-linear isomorphism of an `R`-module onto the kernel of `Γ(T) ⟶ Γ(T₀)`. Then

* the kernel of `r` is `𝒪_X ⊗_R M`, by `a ⊗ m ↦ s(a) · j(m)`
  (`AlgebraicGeometry.Space.retractionIdealIso`), `𝒪_X` being an `R`-algebra through
  `X ⟶ T₀` (`AlgebraicGeometry.Space.retractionCoefficientMap`);
* the kernel of `r` has square zero when that of `Γ(T) ⟶ Γ(T₀)` has
  (`AlgebraicGeometry.Space.thickeningRetraction_mul_eq_zero`);
* hence `A ≅ 𝒪_X[𝒪_X ⊗_R M]`, the trivial square-zero extension, compatibly with `r` and the
  projection (`AlgebraicGeometry.Space.thickeningRetractionRingIso`,
  `AlgebraicGeometry.Space.thickeningRetractionRingIso_hom_comp`).

The affine-chart computation is `Γ(W ×_X X') = Γ(W) ⊗_R Γ(T)`
(`AlgebraicGeometry.Space.retractionChartTensorIso`), followed by base change of the split exact
sequence `0 ⟶ M ⟶ Γ(T) ⟶ R ⟶ 0` (`Stacks.SplitKernel.exact_lTensor`,
`Stacks.SplitKernel.injective_lTensor`); the comparison is glued over the affine charts by
`Stacks.TensorByBaseModule.tensorByBaseModuleIsoOfComparisonOfHom`.

## References

* [Stacks Project, Tag 0DLL](https://stacks.math.columbia.edu/tag/0DLL)
* [Stacks Project, Tag 08RR](https://stacks.math.columbia.edu/tag/08RR)
-/

@[expose] public noncomputable section

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe u

namespace Stacks.SplitKernel

variable {R P M : Type*} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]
  (Q : Type*) [AddCommGroup Q] [Module R Q]
  {j : M →ₗ[R] P} {β : P →ₗ[R] R} (hj : Function.Injective j) (hjβ : Function.Exact j β)
  {e : R →ₗ[R] P} (he : ∀ c, β (e c) = c)

include hjβ he in
/-- **Base change of a split exact sequence `0 ⟶ M ⟶ P ⟶ R ⟶ 0` is exact in the middle.** -/
theorem exact_lTensor : Function.Exact (j.lTensor Q) (β.lTensor Q) :=
  lTensor_exact Q hjβ (fun c => ⟨e c, he c⟩)

include hj hjβ he in
/-- The retraction `P ⟶ M`, `x ↦ j⁻¹(x - e(β x))`, of the kernel inclusion. -/
def splitKernelRetraction : P →ₗ[R] M :=
  (LinearEquiv.ofInjective j hj).symm.toLinearMap ∘ₗ
    (LinearMap.id - e ∘ₗ β).codRestrict (LinearMap.range j) (fun x =>
      LinearMap.mem_range.2 ((hjβ _).1 (by simp [he])))

/-- The retraction `splitKernelRetraction` is a left inverse of `j`. -/
theorem splitKernelRetraction_apply_j (m : M) : splitKernelRetraction hj hjβ he (j m) = m := by
  apply hj
  simp only [splitKernelRetraction, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.ofInjective_symm_apply]
  rw [LinearMap.codRestrict_apply]
  simp [hjβ.apply_apply_eq_zero m]

include hj hjβ he in
/-- **Base change of a split injection is injective.** -/
theorem injective_lTensor : Function.Injective (j.lTensor Q) := by
  have hret : (splitKernelRetraction hj hjβ he).lTensor Q ∘ₗ j.lTensor Q = LinearMap.id := by
    rw [← LinearMap.lTensor_comp]
    have : splitKernelRetraction hj hjβ he ∘ₗ j = LinearMap.id :=
      LinearMap.ext fun m => splitKernelRetraction_apply_j hj hjβ he m
    rw [this, LinearMap.lTensor_id]
  exact Function.LeftInverse.injective (g := (splitKernelRetraction hj hjβ he).lTensor Q)
    (fun x => congrArg (fun φ : Q ⊗[R] M →ₗ[R] Q ⊗[R] M => φ x) hret)

end Stacks.SplitKernel


namespace Deformation.ComplexLift

open CategoryTheory.Limits PresheafOfModules

variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O₀ A : Sheaf J CommRingCat.{u}} (s : O₀ ⟶ A) (r : A ⟶ O₀)

/-- **Multiplication by a compatible family of sections of the kernel**, as a morphism from the
unit to the kernel: `a ↦ a • ε_U`. -/
def splitIdealSectionHom (ε : ∀ U : Cᵒᵖ, (splitIdeal s r).val.obj U)
    (hε : ∀ {U V : Cᵒᵖ} (g : U ⟶ V), (splitIdeal s r).val.map g (ε U) = ε V) :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O₀)).val ⟶
      (SheafOfModules.forget _).obj (splitIdeal s r) :=
  PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun a => (show (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj.obj U from a) • ε U)
        (fun a b => add_smul _ _ _))
      naturality {U V} g := by
        ext a
        change (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj.map g a • ε V =
          (splitIdeal s r).val.map g
            ((show (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj.obj U from a) • ε U)
        rw [PresheafOfModules.map_smul, hε]
        rfl }
    (fun U b a => mul_smul _ _ _)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The section `splitIdealSectionHom` sends `a` to `s(a) · ε U` over `U`. -/
theorem splitIdealSectionHom_app_val (ε : ∀ U : Cᵒᵖ, (splitIdeal s r).val.obj U)
    (hε : ∀ {U V : Cᵒᵖ} (g : U ⟶ V), (splitIdeal s r).val.map g (ε U) = ε V) (U : Cᵒᵖ)
    (a : O₀.obj.obj U) :
    splitIdealVal s r ((splitIdealSectionHom s r ε hε).app U a) =
      s.hom.app U a * splitIdealVal s r (ε U) := rfl

/-- An isomorphism of sheaves of modules induces an isomorphism of trivial square-zero
extensions over `O₀`. -/
def sqZeroExtSheafAnySiteMapIso
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    (e : M ≅ N) : sqZeroExtSheafAnySite O₀ M ≅ sqZeroExtSheafAnySite O₀ N where
  hom := sqZeroExtSheafAnySiteMap e.hom
  inv := sqZeroExtSheafAnySiteMap e.inv
  hom_inv_id := by rw [← sqZeroExtSheafAnySiteMap_comp, e.hom_inv_id, sqZeroExtSheafAnySiteMap_id]
  inv_hom_id := by rw [← sqZeroExtSheafAnySiteMap_comp, e.inv_hom_id, sqZeroExtSheafAnySiteMap_id]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The isomorphism `sqZeroExtSheafAnySiteMapIso e` commutes with the projections. -/
theorem sqZeroExtSheafAnySiteMapIso_hom_comp_proj
    {M N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)} (e : M ≅ N) :
    (sqZeroExtSheafAnySiteMapIso e).hom ≫ sqZeroExtSheafAnySiteProj N =
      sqZeroExtSheafAnySiteProj M :=
  rfl

end Deformation.ComplexLift

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' : AlgebraicSpaces B S hS} {i : X ⟶ X'} (hi : IsThickeningHom B S hS i)
  {q : X' ⟶ X} (h : i ≫ q = 𝟙 X) (hq : yoneda.relativelyRepresentable q.hom)
  {T T₀ : BigFppfOver B S hS} {τ : T ⟶ T₀} {β : T₀ ⟶ T}
  {p : X.1 ⟶ yoneda.obj T₀} {p' : X'.1 ⟶ yoneda.obj T}

/-- The map of a base-changed chart `W ×_X X' ⟶ T`. -/
abbrev retractionChartToBase (W : SmallEtale B S hS X.1) :
    hq.pullback W.1.hom ⟶ T :=
  chartToScheme B S hS X'.1 p' ((smallBaseChange B S hS q hq).obj W)

/-- **The functions of `T` on the base-changed charts**: a function on `T` pulled back along
`W ×_X X' ⟶ X' ⟶ T`. -/
abbrev retractionBaseFunction (W : SmallEtale B S hS X.1) :
    Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)) ⟶
      (thickeningRetractionRing B S hS hq).obj.obj (op W) :=
  Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (retractionChartToBase B S hS hq (p' := p') W)).op

/-- The functions of `T` restrict along the base change of a morphism of charts. -/
theorem retractionBaseFunction_naturality {W W' : SmallEtale B S hS X.1} (g : W ⟶ W')
    (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :
    (thickeningRetractionRing B S hS hq).obj.map g.op
        (retractionBaseFunction B S hS hq (p' := p') W' t) =
      retractionBaseFunction B S hS hq (p' := p') W t :=
  (Γ_map_toScheme_comp_apply B S hS
      ((SmallEtale.toOver B S hS X'.1).map ((smallBaseChange B S hS q hq).map g))
      (retractionChartToBase B S hS hq (p' := p') W') t).symm.trans (by
    rw [chartToScheme_naturality]; rfl)

variable {B S hS hq} in
/-- The square of the base change: `W ×_X X' ⟶ W ⟶ T₀` is `W ×_X X' ⟶ T ⟶ T₀`. -/
theorem retractionChartToBase_comp (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (W : SmallEtale B S hS X.1) :
    retractionChartToBase B S hS hq (p' := p') W ≫ τ =
      hq.snd W.1.hom ≫ chartToScheme B S hS X.1 p W := by
  apply Yoneda.fullyFaithful.map_injective
  rw [Functor.map_comp, Functor.map_comp]
  change yoneda.map (Yoneda.fullyFaithful.preimage (hq.fst W.1.hom ≫ p')) ≫ yoneda.map τ =
    yoneda.map (hq.snd W.1.hom) ≫ yoneda.map (Yoneda.fullyFaithful.preimage (W.1.hom ≫ p))
  rw [Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage, Category.assoc,
    ← hpb.w, ← Category.assoc, hq.w, Category.assoc]

variable {B S hS hq} in
/-- A chart map `W ⟶ (W ×_X X') ×_{X'} X` over `W`, followed by the projections to `W ×_X X'`
and to `T`, is `W ⟶ T₀ ⟶ T`. -/
theorem comp_snd_comp_chartToBase (hir : yoneda.relativelyRepresentable i.hom)
    (hip : i.hom ≫ p' = p ≫ yoneda.map β) (W : SmallEtale B S hS X.1)
    (a : W.1.left ⟶ hir.pullback (hq.fst W.1.hom))
    (ha : yoneda.map a ≫ hir.fst (hq.fst W.1.hom) = W.1.hom) :
    a ≫ hir.snd (hq.fst W.1.hom) ≫ retractionChartToBase B S hS hq (p' := p') W =
      chartToScheme B S hS X.1 p W ≫ β := by
  apply Yoneda.fullyFaithful.map_injective
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  change yoneda.map a ≫ yoneda.map (hir.snd (hq.fst W.1.hom)) ≫
      yoneda.map (Yoneda.fullyFaithful.preimage (hq.fst W.1.hom ≫ p')) =
    yoneda.map (Yoneda.fullyFaithful.preimage (W.1.hom ≫ p)) ≫ yoneda.map β
  rw [Functor.FullyFaithful.map_preimage, Functor.FullyFaithful.map_preimage,
    ← Category.assoc (yoneda.map (hir.snd _)), ← hir.w]
  simp only [Category.assoc]
  rw [hip, reassoc_of% ha]

variable {B S hS hq} in
/-- **The section `X ⟶ X'` read on the charts**: `W ≅ (W ×_X X') ×_{X'} X ⟶ W ×_X X' ⟶ T` is
`W ⟶ T₀ ⟶ T`. -/
theorem retractionInv_comp_chartToBase (hir : yoneda.relativelyRepresentable i.hom)
    (hip : i.hom ≫ p' = p ≫ yoneda.map β) (W : SmallEtale B S hS X.1) :
    ((smallBaseChangeRetractionIso B S hS i q h hir hq).inv.app W).hom.left ≫
        hir.snd (hq.fst W.1.hom) ≫ retractionChartToBase B S hS hq (p' := p') W =
      chartToScheme B S hS X.1 p W ≫ β :=
  comp_snd_comp_chartToBase hir hip W _
    (CostructuredArrow.w ((smallBaseChangeRetractionIso B S hS i q h hir hq).inv.app W).hom)

/-- **Restriction to `X` of a function of `T`** on a base-changed chart is its pullback along
`W ⟶ T₀ ⟶ T`. -/
theorem thickeningRetractionRestriction_baseFunction (hip : i.hom ≫ p' = p ≫ yoneda.map β)
    (W : SmallEtale B S hS X.1) (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :
    (thickeningRetractionRestriction B S hS hi h hq).hom.app (op W)
        (retractionBaseFunction B S hS hq (p' := p') W t) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToScheme B S hS X.1 p W)).op
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t) :=
  ((congrArg (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      ((smallBaseChangeRetractionIso B S hS i q h hi.isClosedImmersion.rep hq).inv.app
        W).hom.left).op)
      (Γ_map_toScheme_comp_apply B S hS (hi.isClosedImmersion.rep.snd (hq.fst W.1.hom))
        (retractionChartToBase B S hS hq (p' := p') W) t).symm).trans
    (Γ_map_toScheme_comp_apply B S hS _ _ t).symm).trans
  ((congrArg (fun m => Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op t)
      (retractionInv_comp_chartToBase h hi.isClosedImmersion.rep hip W)).trans
    (Γ_map_toScheme_comp_apply B S hS _ _ t))

/-! ### The ideal sections pulled back from `T` -/

section IdealSection

open Deformation.ComplexLift

variable (hip : i.hom ≫ p' = p ≫ yoneda.map β)

/-- A function `t` on `T` vanishing on `T₀`, pulled back to the base-changed chart `W ×_X X'`, is
a section of the ideal of `X` over `W`. -/
def retractionIdealElem (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (ht : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0)
    (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    (splitIdeal (thickeningRetractionSection B S hS hq)
      (thickeningRetractionRestriction B S hS hi h hq)).val.obj W :=
  splitIdealMk _ _ (retractionBaseFunction B S hS hq (p' := p') W.unop t) (by
    rw [thickeningRetractionRestriction_baseFunction B S hS hi h hq hip W.unop t, ht, map_zero]
    rfl)

/-- The value of `retractionIdealElem` on a chart `W` is the pullback of `t` to `W ×_X X'`. -/
theorem retractionIdealElem_val (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (ht : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0)
    (W : (SmallEtale B S hS X.1)ᵒᵖ) :
    splitIdealVal _ _ (retractionIdealElem B S hS hi h hq hip t ht W) =
      retractionBaseFunction B S hS hq (p' := p') W.unop t := rfl

/-- The sections `retractionIdealElem` are compatible with restriction along chart morphisms. -/
theorem retractionIdealElem_restrict (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (ht : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0)
    {W W' : (SmallEtale B S hS X.1)ᵒᵖ} (g : W ⟶ W') :
    (splitIdeal (thickeningRetractionSection B S hS hq)
      (thickeningRetractionRestriction B S hS hi h hq)).val.map g
        (retractionIdealElem B S hS hi h hq hip t ht W) =
      retractionIdealElem B S hS hi h hq hip t ht W' :=
  splitIdealVal_injective _ _ ((splitIdealVal_restrict _ _ _ _).trans
    (retractionBaseFunction_naturality B S hS hq g.unop t))

/-- **Multiplication by a function of `T` vanishing on `T₀`**, as a morphism from `𝒪_X` to the
ideal of `X`: `a ↦ s(a) · t`. -/
def retractionIdealSection (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (ht : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0) :
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (structureSheaf B S hS X.1 X.2))).val ⟶
    (SheafOfModules.forget _).obj (splitIdeal (thickeningRetractionSection B S hS hq)
        (thickeningRetractionRestriction B S hS hi h hq)) :=
  splitIdealSectionHom (thickeningRetractionSection B S hS hq)
    (thickeningRetractionRestriction B S hS hi h hq)
    (retractionIdealElem B S hS hi h hq hip t ht)
    (retractionIdealElem_restrict B S hS hi h hq hip t ht)

/-- The section `retractionIdealSection` sends `a` to `s(a) · t` on the chart `W`. -/
theorem retractionIdealSection_app_val (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (ht : Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0)
    (W : (SmallEtale B S hS X.1)ᵒᵖ) (a : (structureSheaf B S hS X.1 X.2).obj.obj W) :
    splitIdealVal _ _ ((retractionIdealSection B S hS hi h hq hip t ht).app W a) =
      (thickeningRetractionSection B S hS hq).hom.app W a *
        retractionBaseFunction B S hS hq (p' := p') W.unop t := rfl

end IdealSection

/-! ### The coefficient map of `X ⟶ T₀` -/

section Coefficient

variable (R : Type u) [CommRing R]
  (φ₀ : CommRingCat.of R ⟶ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T₀)))

/-- **The coefficient map of `p : X ⟶ T₀`**, through a ring map `φ₀ : R ⟶ Γ(T₀)`: over a chart
`W` of `X` a scalar is sent to its pullback along `W ⟶ X ⟶ T₀`. -/
def retractionCoefficientMap :
    Stacks.TensorByBaseModule.constantRingPresheaf (C := SmallEtale B S hS X.1) R ⟶
      (structureSheaf B S hS X.1 X.2).obj where
  app W := φ₀ ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
    (chartToScheme B S hS X.1 p W.unop)).op
  naturality {W W'} g := by
    ext c
    exact (Γ_map_toScheme_comp_apply B S hS ((SmallEtale.toOver B S hS X.1).map g.unop)
      (chartToScheme B S hS X.1 p W.unop) (φ₀ c)).symm.trans
        (by rw [chartToScheme_naturality]; rfl) |>.symm

/-- Over a chart `W`, the coefficient map sends `c` to the pullback of `φ₀ c` along the chart. -/
theorem retractionCoefficientMap_app_apply (W : (SmallEtale B S hS X.1)ᵒᵖ) (c : R) :
    ((retractionCoefficientMap B S hS (p := p) R φ₀).app W).hom c =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToScheme B S hS X.1 p W.unop)).op
        (φ₀ c) := rfl

end Coefficient

variable {B S hS hq} in
/-- **Pulling back a function of `T₀` to a base-changed chart through `T` or through `W`.** -/
theorem retractionBaseFunction_comp (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (W : SmallEtale B S hS X.1) (y : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T₀))) :
    retractionBaseFunction B S hS hq (p' := p') W
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op y) =
      (thickeningRetractionSection B S hS hq).hom.app (op W)
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToScheme B S hS X.1 p W)).op y) :=
  (Γ_map_toScheme_comp_apply B S hS _ _ y).symm.trans
    ((congrArg (fun m => Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op y)
      (retractionChartToBase_comp hpb W)).trans (Γ_map_toScheme_comp_apply B S hS _ _ y))

/-! ### The comparison `𝒪_X ⊗_R M ⟶ I` -/

section Comparison

open Deformation.ComplexLift Stacks.TensorByBaseModule

variable (hip : i.hom ≫ p' = p ≫ yoneda.map β) (R : Type u) [CommRing R]
  (φ₀ : CommRingCat.of R ⟶ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T₀)))
  {M : Type u} [AddCommGroup M] [Module R M]
  (j : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
  (hjβ : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op (j m) = 0)

/-- The family `m ↦ (a ↦ s(a) · j(m))` of morphisms from `𝒪_X` to the ideal of `X`. -/
def retractionComparisonFamily (m : ModuleCat.of R M) :
    (SheafOfModules.unit (ringSheaf (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2))).val ⟶
    (PresheafOfModules.restrictScalars (𝟙 (ringSheaf (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2)).obj)).obj
      ((SheafOfModules.forget (ringSheaf (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2))).obj
        (splitIdeal (thickeningRetractionSection B S hS hq)
          (thickeningRetractionRestriction B S hS hi h hq))) :=
  retractionIdealSection B S hS hi h hq hip (j m) (hjβ m)

/-- The underlying section of `A` of `retractionComparisonFamily m` at `x` is `s(x) · j(m)`. -/
private theorem splitIdealVal_retractionComparisonFamily (m : ModuleCat.of R M)
    (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (SheafOfModules.unit (ringSheaf (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2))).val.obj W) :
    splitIdealVal (thickeningRetractionSection B S hS hq)
        (thickeningRetractionRestriction B S hS hi h hq)
        (((retractionComparisonFamily B S hS hi h hq hip R j hjβ m).app W).hom x) =
      (thickeningRetractionSection B S hS hq).hom.app W
        (show (structureSheaf B S hS X.1 X.2).obj.obj W from x) *
          retractionBaseFunction B S hS hq (p' := p') W.unop (j m) := rfl

/-- The comparison family is additive in `m`. -/
theorem retractionComparisonFamily_add (m₁ m₂ : ModuleCat.of R M) (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (SheafOfModules.unit (ringSheaf (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2))).val.obj W) :
    ((retractionComparisonFamily B S hS hi h hq hip R j hjβ (m₁ + m₂)).app W).hom x =
      ((retractionComparisonFamily B S hS hi h hq hip R j hjβ m₁).app W).hom x +
        ((retractionComparisonFamily B S hS hi h hq hip R j hjβ m₂).app W).hom x := by
  apply splitIdealVal_injective (thickeningRetractionSection B S hS hq)
    (thickeningRetractionRestriction B S hS hi h hq)
  refine (splitIdealVal_retractionComparisonFamily B S hS hi h hq hip R j hjβ _ _ _).trans
    (Eq.trans ?_ (splitIdealVal_add _ _ _ _).symm)
  rw [splitIdealVal_retractionComparisonFamily B S hS hi h hq hip R j hjβ,
    splitIdealVal_retractionComparisonFamily B S hS hi h hq hip R j hjβ, map_add, map_add, mul_add]

variable {R φ₀} in
/-- The comparison family is `R`-linear: `c • m` acts as multiplication by the image of `c`. -/
theorem retractionComparisonFamily_smul (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀ c) * j m)
    (c : R) (m : ModuleCat.of R M) (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (SheafOfModules.unit (ringSheaf (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2))).val.obj W) :
    ((retractionComparisonFamily B S hS hi h hq hip R j hjβ (c • m)).app W).hom x =
      ((retractionCoefficientMap B S hS (p := p) R φ₀).app W).hom c •
        ((retractionComparisonFamily B S hS hi h hq hip R j hjβ m).app W).hom x := by
  apply splitIdealVal_injective (thickeningRetractionSection B S hS hq)
    (thickeningRetractionRestriction B S hS hi h hq)
  refine (splitIdealVal_retractionComparisonFamily B S hS hi h hq hip R j hjβ _ _ _).trans
    (Eq.trans ?_ (splitIdealVal_smul _ _ _ _).symm)
  rw [splitIdealVal_retractionComparisonFamily B S hS hi h hq hip R j hjβ,
    retractionCoefficientMap_app_apply]
  rw [hjs, map_mul, retractionBaseFunction_comp hpb W.unop]
  ring

variable {R φ₀} in
/-- **The ideal of `X` in `X'` is `𝒪_X ⊗_R M`**, given that the comparison
`a ⊗ m ↦ s(a) · j(m)` is bijective over the affine charts. -/
def retractionIdealIsoOfBijective (hpb : IsPullback q.hom p' p (yoneda.map τ))
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀ c) * j m)
    (hbij : ∀ W : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        Function.Bijective (comparisonCancelled R (SmallEtale.topology B S hS X.1)
          (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
          (retractionCoefficientMap B S hS (p := p) R φ₀) (ModuleCat.of R M) _
          (retractionComparisonFamily B S hS hi h hq hip R j hjβ)
          (retractionComparisonFamily_add B S hS hi h hq hip R j hjβ)
          (retractionComparisonFamily_smul B S hS hi h hq hip j hjβ hpb hjs) (op W))) :
    (tensorByBaseModuleOfHom R (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
        (SheafOfModules.unit _) (retractionCoefficientMap B S hS (p := p) R φ₀)).obj
        (ModuleCat.of R M) ≅
      splitIdeal (thickeningRetractionSection B S hS hq)
        (thickeningRetractionRestriction B S hS hi h hq) :=
  tensorByBaseModuleIsoOfComparisonOfHom R (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
    (retractionCoefficientMap B S hS (p := p) R φ₀) (ModuleCat.of R M)
    (splitIdeal (thickeningRetractionSection B S hS hq)
      (thickeningRetractionRestriction B S hS hi h hq))
    (retractionComparisonFamily B S hS hi h hq hip R j hjβ)
    (retractionComparisonFamily_add B S hS hi h hq hip R j hjβ)
    (retractionComparisonFamily_smul B S hS hi h hq hip j hjβ hpb hjs)
    (fun W => IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W))
    (generate_isAffine_chart_mem B S hS X)
    (fun W hW => (bijective_comparisonApp_iff R (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (retractionCoefficientMap B S hS (p := p) R φ₀) (ModuleCat.of R M) _ _ _ _ (op W)).mpr
      (hbij W hW))

end Comparison

/-! ### The affine charts -/

section AffineChart

open Deformation.ComplexLift Stacks.TensorByBaseModule

variable {B S hS hq} in
/-- **On an affine chart the base-changed chart is a pushout of rings**:
`Γ(W ×_X X') = Γ(W) ⊗_{Γ(T₀)} Γ(T)`, through `s` and the functions of `T`. -/
theorem isPushout_retractionChart (hpb : IsPullback q.hom p' p (yoneda.map τ))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    IsPushout (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op)
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (chartToScheme B S hS X.1 p W)).op)
      (retractionBaseFunction B S hS hq (p' := p') W)
      ((thickeningRetractionSection B S hS hq).hom.app (op W)) :=
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj W)) := hW
  isPushout_appTop_of_isPullback (isPullback_toScheme_smallBaseChange_of_isPullback B S hS hq hpb W
    (Functor.FullyFaithful.map_preimage _ _) (Functor.FullyFaithful.map_preimage _ _))

variable (R : Type u) [CommRing R]
  (φ₀ : CommRingCat.of R ≅ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T₀)))

variable {B S hS hq R φ₀} in
/-- The pushout square of an affine chart, with `Γ(T₀)` replaced by `R` along `φ₀`. -/
theorem isPushout_retractionChart' (hpb : IsPullback q.hom p' p (yoneda.map τ))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    IsPushout ((retractionCoefficientMap B S hS (p := p) R φ₀.hom).app (op W))
      (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op)
      ((thickeningRetractionSection B S hS hq).hom.app (op W))
      (retractionBaseFunction B S hS hq (p' := p') W) :=
  (isPushout_retractionChart hpb W hW).flip.of_iso φ₀.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (φ₀.inv_hom_id_assoc _).symm)
    ((Category.comp_id _).trans (φ₀.inv_hom_id_assoc _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

variable {B S hS hq R φ₀} in
/-- **`Γ(W ×_X X') = Γ(W) ⊗_R Γ(T)` on an affine chart `W`**, `g ⊗ t ↦ s(g) · t`. -/
def retractionChartTensorIso (hpb : IsPullback q.hom p' p (yoneda.map τ))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    letI := coefficientAlgebraOfHom R (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (op W)
    letI : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
      (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
    CommRingCat.of ((structureSheaf B S hS X.1 X.2).obj.obj (op W) ⊗[R]
        Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) ≅
      (thickeningRetractionRing B S hS hq).obj.obj (op W) :=
  letI := coefficientAlgebraOfHom R (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (op W)
  letI : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
    (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
  (CommRingCat.isPushout_tensorProduct R _ _).isoIsPushout _ _
    (isPushout_retractionChart' hpb W hW)

variable {B S hS hq R φ₀} in
/-- `retractionChartTensorIso` sends `g ⊗ t` to `s(g) · t`. -/
theorem retractionChartTensorIso_tmul (hpb : IsPullback q.hom p' p (yoneda.map τ))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W))
    (g : (structureSheaf B S hS X.1 X.2).obj.obj (op W))
    (t : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :
    letI := coefficientAlgebraOfHom R (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (op W)
    letI : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
      (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
    (retractionChartTensorIso hpb W hW).hom (g ⊗ₜ[R] t) =
      (thickeningRetractionSection B S hS hq).hom.app (op W) g *
        retractionBaseFunction B S hS hq (p' := p') W t := by
  let := coefficientAlgebraOfHom R (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (op W)
  let : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
    (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
  have hl := congrArg (fun φ => CommRingCat.Hom.hom φ g) (IsPushout.inl_isoIsPushout_hom _ _
    (CommRingCat.isPushout_tensorProduct R _ _) (isPushout_retractionChart' (hq := hq) hpb W hW))
  have hr := congrArg (fun φ => CommRingCat.Hom.hom φ t) (IsPushout.inr_isoIsPushout_hom _ _
    (CommRingCat.isPushout_tensorProduct R _ _) (isPushout_retractionChart' (hq := hq) hpb W hW))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at hl hr
  rw [← hl, ← hr, ← map_mul]
  congr 1
  change g ⊗ₜ[R] t = (g ⊗ₜ[R] (1 : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))) *
    ((1 : (structureSheaf B S hS X.1 X.2).obj.obj (op W)) ⊗ₜ[R] t)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

variable {B S hS} in
/-- `T₀ ⟶ T ⟶ T₀` is the identity on functions. -/
theorem Γ_map_section_retraction (hβτ : β ≫ τ = 𝟙 T₀)
    (y : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T₀))) :
    Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op y) = y := by
  refine (Γ_map_toScheme_comp_apply B S hS β τ y).symm.trans ?_
  rw [hβτ, CategoryTheory.Functor.map_id, op_id, Scheme.Γ.map_id]
  rfl

variable {B S hS R φ₀} in
/-- The map `j : M ⟶ Γ(T)`, `R`-linear for the `R`-algebra structure of `Γ(T)` through
`R ≅ Γ(T₀) ⟶ Γ(T)`. -/
def retractionKernelLinearMap {M : Type u} [AddCommGroup M] [Module R M]
    (j : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c) * j m) :
    letI : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
      (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
    M →ₗ[R] Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)) :=
  letI : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
    (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
  { toFun := j, map_add' := j.map_add, map_smul' := fun c m => hjs c m }

variable {B S hS hq R φ₀} in
/-- **The kernel of `Γ(W ×_X X') ⟶ Γ(W)` is `Γ(W) ⊗_R M` on an affine chart `W`**: the map
`g ⊗ m ↦ s(g) · j(m)` is injective, with image the kernel of the restriction `r`. -/
theorem retractionChartTensor_kernel (hip : i.hom ≫ p' = p ≫ yoneda.map β)
    (hpb : IsPullback q.hom p' p (yoneda.map τ)) (hβτ : β ≫ τ = 𝟙 T₀)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {M : Type u} [AddCommGroup M] [Module R M]
    (j : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (hjβ : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op (j m) = 0)
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c) * j m)
    (hjinj : Function.Injective j)
    (hjker : ∀ t, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0 → ∃ m, j m = t)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    letI := coefficientAlgebraOfHom R (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (op W)
    letI : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
      (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
    Function.Injective (fun x => (retractionChartTensorIso (hq := hq) (φ₀ := φ₀) hpb W hW).hom
        ((retractionKernelLinearMap (φ₀ := φ₀) j hjs).lTensor _ x)) ∧
      ∀ v, (thickeningRetractionRestriction B S hS hi h hq).hom.app (op W) v = 0 →
        ∃ x, (retractionChartTensorIso (hq := hq) (φ₀ := φ₀) hpb W hW).hom
          ((retractionKernelLinearMap (φ₀ := φ₀) j hjs).lTensor _ x) = v := by
  let := coefficientAlgebraOfHom R (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (op W)
  let : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
    (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
  let jl := retractionKernelLinearMap (φ₀ := φ₀) j hjs
  let βl : Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)) →ₗ[R] R :=
    { toFun := fun t => φ₀.inv (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t)
      map_add' := fun t t' => by rw [map_add, map_add]
      map_smul' := fun c t => by
        change φ₀.inv (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op
          (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c) * t)) =
            c * φ₀.inv (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t)
        rw [map_mul, Γ_map_section_retraction hβτ, map_mul, Iso.hom_inv_id_apply] }
  have he : ∀ c, βl (Algebra.linearMap R _ c) = c := fun c => by
    change φ₀.inv (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c))) = c
    rw [Γ_map_section_retraction hβτ, Iso.hom_inv_id_apply]
  have hexact : Function.Exact jl βl := by
    intro t
    constructor
    · intro ht
      have h0 : φ₀.hom (φ₀.inv (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t)) = 0 := by
        rw [show φ₀.inv (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t) = 0 from ht,
          map_zero]
      rw [Iso.inv_hom_id_apply] at h0
      exact hjker t h0
    · rintro ⟨m, rfl⟩
      change φ₀.inv (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op (j m)) = 0
      rw [hjβ, map_zero]
  have hinjT := Stacks.SplitKernel.injective_lTensor (R := R)
    ((structureSheaf B S hS X.1 X.2).obj.obj (op W)) (j := jl) (β := βl)
    (e := Algebra.linearMap R _) hjinj hexact he
  have hexT := Stacks.SplitKernel.exact_lTensor (R := R)
    ((structureSheaf B S hS X.1 X.2).obj.obj (op W)) (j := jl) (β := βl)
    (e := Algebra.linearMap R _) hexact he
  have hFinv : ∀ a, (retractionChartTensorIso (hq := hq) (φ₀ := φ₀) hpb W hW).inv
      ((retractionChartTensorIso (hq := hq) (φ₀ := φ₀) hpb W hW).hom a) = a :=
    fun a => Iso.hom_inv_id_apply _ _
  have hFinv' : ∀ v, (retractionChartTensorIso (hq := hq) (φ₀ := φ₀) hpb W hW).hom
      ((retractionChartTensorIso (hq := hq) (φ₀ := φ₀) hpb W hW).inv v) = v :=
    fun v => Iso.inv_hom_id_apply _ _
  refine ⟨fun x₁ x₂ h12 => hinjT ?_, fun v hv => ?_⟩
  · change jl.lTensor _ x₁ = jl.lTensor _ x₂
    rw [← hFinv (jl.lTensor _ x₁)]
    exact (congrArg _ h12).trans (hFinv _)
  · have hrid : ∀ u, (thickeningRetractionRestriction B S hS hi h hq).hom.app (op W)
        ((retractionChartTensorIso (hq := hq) (φ₀ := φ₀) hpb W hW).hom u) =
        TensorProduct.rid R ((structureSheaf B S hS X.1 X.2).obj.obj (op W))
          (βl.lTensor ((structureSheaf B S hS X.1 X.2).obj.obj (op W)) u) := by
      intro u
      induction u using TensorProduct.inductionOn with
      | tmul g t =>
        rw [retractionChartTensorIso_tmul (hq := hq) (φ₀ := φ₀) hpb W hW g t, map_mul,
          split_app_apply _ _ (thickeningRetractionSection_comp_restriction B S hS hi h hq),
          thickeningRetractionRestriction_baseFunction B S hS hi h hq hip W t,
          LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
        congr 1
        change _ = Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
          (chartToScheme B S hS X.1 p W)).op (φ₀.hom (φ₀.inv
            (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t)))
        rw [Iso.inv_hom_id_apply]
      | add a b ha hb => rw [map_add, map_add, map_add, map_add, ha, hb]
    have hu : βl.lTensor ((structureSheaf B S hS X.1 X.2).obj.obj (op W))
        ((retractionChartTensorIso (hq := hq) (φ₀ := φ₀) hpb W hW).inv v) = 0 := by
      apply (TensorProduct.rid R ((structureSheaf B S hS X.1 X.2).obj.obj (op W))).injective
      rwa [map_zero, ← hrid, hFinv']
    obtain ⟨x, hx⟩ := (hexT _).1 hu
    exact ⟨x, (congrArg _ hx).trans (hFinv' v)⟩

variable {B S hS hq R φ₀} in
/-- **The comparison `𝒪_X(W) ⊗_R M ⟶ I(W)` is bijective on an affine chart `W`**, when `T` and
`T₀` are affine, `T₀ ⟶ T ⟶ T₀` is the identity and `j` identifies `M` with the kernel of
`Γ(T) ⟶ Γ(T₀)`. -/
theorem bijective_retractionComparison (hip : i.hom ≫ p' = p ≫ yoneda.map β)
    (hpb : IsPullback q.hom p' p (yoneda.map τ)) (hβτ : β ≫ τ = 𝟙 T₀)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {M : Type u} [AddCommGroup M] [Module R M]
    (j : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (hjβ : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op (j m) = 0)
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c) * j m)
    (hjinj : Function.Injective j)
    (hjker : ∀ t, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0 → ∃ m, j m = t)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W)) :
    Function.Bijective (comparisonCancelled R (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
      (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (ModuleCat.of R M) _
      (retractionComparisonFamily B S hS hi h hq hip R j hjβ)
      (retractionComparisonFamily_add B S hS hi h hq hip R j hjβ)
      (retractionComparisonFamily_smul B S hS hi h hq hip j hjβ hpb hjs) (op W)) := by
  obtain ⟨hinj, hsurj⟩ := retractionChartTensor_kernel hi h hip hpb hβτ j hjβ hjs hjinj hjker W hW
  let := coefficientAlgebraOfHom R (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (op W)
  let : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
    (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
  let := sectionsModuleOfHom R (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
    (retractionCoefficientMap B S hS (p := p) R φ₀.hom)
    (SheafOfModules.unit (ringSheaf (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2))).val (op W)
  let eQ : (SheafOfModules.unit (ringSheaf (SmallEtale.topology B S hS X.1)
      (structureSheaf B S hS X.1 X.2))).val.obj (op W) ≃ₗ[R]
        (structureSheaf B S hS X.1 X.2).obj.obj (op W) :=
    { toFun := fun x => x, invFun := fun x => x, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  let castL := TensorProduct.congr eQ (LinearEquiv.refl R M)
  have key : ∀ t, splitIdealVal (thickeningRetractionSection B S hS hq)
      (thickeningRetractionRestriction B S hS hi h hq)
      (comparisonCancelled R (SmallEtale.topology B S hS X.1)
        (structureSheaf B S hS X.1 X.2) (SheafOfModules.unit _)
        (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (ModuleCat.of R M) _
        (retractionComparisonFamily B S hS hi h hq hip R j hjβ)
        (retractionComparisonFamily_add B S hS hi h hq hip R j hjβ)
        (retractionComparisonFamily_smul B S hS hi h hq hip j hjβ hpb hjs) (op W) t) =
      (retractionChartTensorIso (hq := hq) (φ₀ := φ₀) hpb W hW).hom
        ((retractionKernelLinearMap (φ₀ := φ₀) j hjs).lTensor _ (castL t)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul x m => exact (retractionChartTensorIso_tmul (hq := hq) (φ₀ := φ₀) hpb W hW x (j m)).symm
    | add a b ha hb =>
      rw [map_add, map_add, map_add, map_add, ← ha, ← hb]
      rfl
  refine ⟨fun t₁ t₂ h12 => castL.injective (hinj ?_), fun y => ?_⟩
  · have h' := congrArg (splitIdealVal (thickeningRetractionSection B S hS hq)
      (thickeningRetractionRestriction B S hS hi h hq)) h12
    rwa [key, key] at h'
  · obtain ⟨x, hx⟩ := hsurj _ (splitIdealVal_mem (thickeningRetractionSection B S hS hq)
      (thickeningRetractionRestriction B S hS hi h hq)
      (show (splitIdeal (thickeningRetractionSection B S hS hq)
        (thickeningRetractionRestriction B S hS hi h hq)).val.obj (op W) from y))
    refine ⟨castL.symm x, splitIdealVal_injective (thickeningRetractionSection B S hS hq)
      (thickeningRetractionRestriction B S hS hi h hq) ?_⟩
    rwa [key, LinearEquiv.apply_symm_apply]

variable {B S hS hq R φ₀} in
/-- **The ideal of `X` in `X'` is `𝒪_X ⊗_R M`** (Stacks 0DLL, the identification of the ideal of
`X₀ ⊂ X_V` with `𝒪_{X₀} ⊗_k V`): for `X ⟶ X' ⟶ X` the base change of `T₀ ⟶ T ⟶ T₀` with `T`,
`T₀` affine, and `j : M ⟶ Γ(T)` an `R`-linear isomorphism onto the kernel of `Γ(T) ⟶ Γ(T₀)`. -/
def retractionIdealIso (hip : i.hom ≫ p' = p ≫ yoneda.map β)
    (hpb : IsPullback q.hom p' p (yoneda.map τ)) (hβτ : β ≫ τ = 𝟙 T₀)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {M : Type u} [AddCommGroup M] [Module R M]
    (j : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (hjβ : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op (j m) = 0)
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c) * j m)
    (hjinj : Function.Injective j)
    (hjker : ∀ t, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0 → ∃ m, j m = t) :
    (tensorByBaseModuleOfHom R (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
        (SheafOfModules.unit _) (retractionCoefficientMap B S hS (p := p) R φ₀.hom)).obj
        (ModuleCat.of R M) ≅
      splitIdeal (thickeningRetractionSection B S hS hq)
        (thickeningRetractionRestriction B S hS hi h hq) :=
  retractionIdealIsoOfBijective B S hS hi h hq hip j hjβ hpb hjs
    (fun W hW => bijective_retractionComparison hi h hip hpb hβτ j hjβ hjs hjinj hjker W hW)

variable {B S hS hq R φ₀} in
/-- **The ideal of `X` in `X'` has square zero on an affine chart** when the kernel of
`Γ(T) ⟶ Γ(T₀)` has. -/
theorem retractionChart_mul_eq_zero (hip : i.hom ≫ p' = p ≫ yoneda.map β)
    (hpb : IsPullback q.hom p' p (yoneda.map τ)) (hβτ : β ≫ τ = 𝟙 T₀)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {M : Type u} [AddCommGroup M] [Module R M]
    (j : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (hjβ : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op (j m) = 0)
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c) * j m)
    (hjinj : Function.Injective j)
    (hjker : ∀ t, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0 → ∃ m, j m = t)
    (hjsq : ∀ m m', j m * j m' = 0)
    (W : SmallEtale B S hS X.1)
    (hW : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W))
    (a b : (thickeningRetractionRing B S hS hq).obj.obj (op W))
    (ha : (thickeningRetractionRestriction B S hS hi h hq).hom.app (op W) a = 0)
    (hb : (thickeningRetractionRestriction B S hS hi h hq).hom.app (op W) b = 0) :
    a * b = 0 := by
  obtain ⟨-, hsurj⟩ := retractionChartTensor_kernel hi h hip hpb hβτ j hjβ hjs hjinj hjker W hW
  let := coefficientAlgebraOfHom R (SmallEtale.topology B S hS X.1)
    (structureSheaf B S hS X.1 X.2) (retractionCoefficientMap B S hS (p := p) R φ₀.hom) (op W)
  let : Algebra R (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T))) :=
    (φ₀.hom ≫ Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op).hom.toAlgebra
  obtain ⟨x, rfl⟩ := hsurj a ha
  obtain ⟨y, rfl⟩ := hsurj b hb
  rw [← map_mul]
  suffices h0 : ∀ x y : (structureSheaf B S hS X.1 X.2).obj.obj (op W) ⊗[R] M,
      (retractionKernelLinearMap (φ₀ := φ₀) j hjs).lTensor _ x *
        (retractionKernelLinearMap (φ₀ := φ₀) j hjs).lTensor _ y = 0 by
    rw [h0, map_zero]
  intro x y
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [map_add, add_mul, hx, hx', add_zero]
  | tmul g m =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => rw [map_add, mul_add, hy, hy', add_zero]
    | tmul g' m' =>
      rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul]
      change (g * g') ⊗ₜ[R] (j m * j m') = 0
      rw [hjsq, TensorProduct.tmul_zero]

/-- **A section of a sheaf of rings on the small étale site vanishing on every affine chart is
zero.** -/
theorem eq_zero_of_isAffine_restrict
    (A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (z : A.obj.obj U)
    (hz : ∀ (W : SmallEtale B S hS X.1) (e : W ⟶ U.unop),
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj W) →
        A.obj.map e.op z = 0) :
    z = 0 := by
  have hsh : Presieve.IsSheaf (SmallEtale.topology B S hS X.1)
      (A.obj ⋙ CategoryTheory.forget CommRingCat.{u}) :=
    (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose _ (CategoryTheory.forget CommRingCat.{u})).obj A).property
  refine hsh.isSeparated _ (generate_isAffine_chart_mem B S hS X U.unop) (fun _ _ _ => 0) z 0 ?_ ?_
  · rintro V f ⟨W, g, e, hW, rfl⟩
    change A.obj.map (g ≫ e).op z = 0
    rw [op_comp, Functor.map_comp, CommRingCat.comp_apply, hz W e hW, map_zero]
  · intro V f _
    exact map_zero (A.obj.map f.op).hom

variable {B S hS hq R φ₀} in
/-- **The ideal of `X` in `X'` has square zero** when the kernel of `Γ(T) ⟶ Γ(T₀)` has. -/
theorem thickeningRetraction_mul_eq_zero (hip : i.hom ≫ p' = p ≫ yoneda.map β)
    (hpb : IsPullback q.hom p' p (yoneda.map τ)) (hβτ : β ≫ τ = 𝟙 T₀)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {M : Type u} [AddCommGroup M] [Module R M]
    (j : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (hjβ : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op (j m) = 0)
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c) * j m)
    (hjinj : Function.Injective j)
    (hjker : ∀ t, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0 → ∃ m, j m = t)
    (hjsq : ∀ m m', j m * j m' = 0)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (a b : (thickeningRetractionRing B S hS hq).obj.obj U)
    (ha : (thickeningRetractionRestriction B S hS hi h hq).hom.app U a = 0)
    (hb : (thickeningRetractionRestriction B S hS hi h hq).hom.app U b = 0) :
    a * b = 0 := by
  have hres : ∀ (W : SmallEtale B S hS X.1) (e : W ⟶ U.unop)
      (c : (thickeningRetractionRing B S hS hq).obj.obj U),
      (thickeningRetractionRestriction B S hS hi h hq).hom.app U c = 0 →
        (thickeningRetractionRestriction B S hS hi h hq).hom.app (op W)
          ((thickeningRetractionRing B S hS hq).obj.map e.op c) = 0 := by
    intro W e c hc
    change ((thickeningRetractionRing B S hS hq).obj.map e.op ≫
      (thickeningRetractionRestriction B S hS hi h hq).hom.app (op W)) c = 0
    rw [(thickeningRetractionRestriction B S hS hi h hq).hom.naturality, CommRingCat.comp_apply,
      hc, map_zero]
  refine eq_zero_of_isAffine_restrict B S hS (thickeningRetractionRing B S hS hq) U _
    (fun W e hW => ?_)
  rw [map_mul]
  exact retractionChart_mul_eq_zero hi h hip hpb hβτ j hjβ hjs hjinj hjker hjsq W hW _ _
    (hres W e a ha) (hres W e b hb)

variable {B S hS hq R φ₀} in
/-- **The structure sheaf of `X'` on the site of `X` is the trivial square-zero extension
`𝒪_X[𝒪_X ⊗_R M]`**, compatibly with restriction to `X`
(`AlgebraicGeometry.Space.thickeningRetractionRingIso_hom_comp`). -/
def thickeningRetractionRingIso (hip : i.hom ≫ p' = p ≫ yoneda.map β)
    (hpb : IsPullback q.hom p' p (yoneda.map τ)) (hβτ : β ≫ τ = 𝟙 T₀)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {M : Type u} [AddCommGroup M] [Module R M]
    (j : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (hjβ : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op (j m) = 0)
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c) * j m)
    (hjinj : Function.Injective j)
    (hjker : ∀ t, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0 → ∃ m, j m = t)
    (hjsq : ∀ m m', j m * j m' = 0) :
    thickeningRetractionRing B S hS hq ≅ sqZeroExtSheafAnySite (structureSheaf B S hS X.1 X.2)
      ((tensorByBaseModuleOfHom R (SmallEtale.topology B S hS X.1) (structureSheaf B S hS X.1 X.2)
        (SheafOfModules.unit _) (retractionCoefficientMap B S hS (p := p) R φ₀.hom)).obj
        (ModuleCat.of R M)) :=
  (splitSqZeroExtIso (thickeningRetractionSection B S hS hq)
      (thickeningRetractionRestriction B S hS hi h hq)
      (thickeningRetractionSection_comp_restriction B S hS hi h hq)
      (thickeningRetraction_mul_eq_zero hi h hip hpb hβτ j hjβ hjs hjinj hjker hjsq)).symm ≪≫
    sqZeroExtSheafAnySiteMapIso (retractionIdealIso hi h hip hpb hβτ j hjβ hjs hjinj hjker).symm

variable {B S hS hq R φ₀} in
/-- The isomorphism `q_*𝒪_{X'} ≅ 𝒪_X[𝒪_X ⊗_R M]` carries restriction to `X` to the projection. -/
theorem thickeningRetractionRingIso_hom_comp (hip : i.hom ≫ p' = p ≫ yoneda.map β)
    (hpb : IsPullback q.hom p' p (yoneda.map τ)) (hβτ : β ≫ τ = 𝟙 T₀)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T₀)]
    {M : Type u} [AddCommGroup M] [Module R M]
    (j : M →+ Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T)))
    (hjβ : ∀ m, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op (j m) = 0)
    (hjs : ∀ (c : R) (m : M), j (c • m) =
      Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map τ).op (φ₀.hom c) * j m)
    (hjinj : Function.Injective j)
    (hjker : ∀ t, Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map β).op t = 0 → ∃ m, j m = t)
    (hjsq : ∀ m m', j m * j m' = 0) :
    (thickeningRetractionRingIso hi h hip hpb hβτ j hjβ hjs hjinj hjker hjsq).hom ≫
        sqZeroExtSheafAnySiteProj _ =
      thickeningRetractionRestriction B S hS hi h hq :=
  (Iso.inv_comp_eq _).2 (splitSqZeroExtIso_hom_comp (thickeningRetractionSection B S hS hq)
      (thickeningRetractionRestriction B S hS hi h hq)
      (thickeningRetractionSection_comp_restriction B S hS hi h hq)
      (thickeningRetraction_mul_eq_zero hi h hip hpb hβτ j hjβ hjs hjinj hjker hjsq)).symm

end AffineChart

/-! ### Back on the site of `X'` -/

section Transpose

/-- Transposing an isomorphism under an equivalence gives an isomorphism. -/
theorem equivalence_isIso_homEquiv {C D : Type*} [Category* C] [Category* D] (E : C ≌ D) {P : C}
    {R : D} (f : E.functor.obj P ⟶ R) (hf : IsIso f) : IsIso (E.toAdjunction.homEquiv P R f) := by
  rw [Adjunction.homEquiv_unit]
  infer_instance

/-- A transpose followed by `G.map π` is `s` as soon as `y ≫ π` is the transpose of `s`. -/
theorem adjunction_homEquiv_comp_map_eq {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {P : C} {R Q : D} (y : F.obj P ⟶ R) (π : R ⟶ Q)
    (s : P ⟶ G.obj Q) (hy : y ≫ π = (adj.homEquiv P Q).symm s) :
    adj.homEquiv P R y ≫ G.map π = s := by
  rw [← Adjunction.homEquiv_naturality_right, hy, Equiv.apply_symm_apply]

variable {Rr : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}

/-- **The structure sheaf of `X'` on its own site from its restriction to the charts of `X`**:
an isomorphism `y : q_* 𝒪_{X'} ≅ Rr` on the site of `X` transposes, under the Comparison Lemma
equivalence `AlgebraicGeometry.Space.thickeningRetractionEquivalence`, to an isomorphism
`𝒪_{X'} ≅ i^* Rr` on the site of `X'` (`i^*` restriction along chart base change along `i`). -/
def thickeningRetractionTranspose (y : thickeningRetractionRing B S hS hq ≅ Rr) :
    structureSheaf B S hS X'.1 X'.2 ≅
      (thickeningRetractionEquivalence B S hS hi h hq CommRingCat.{u}).functor.obj Rr :=
  haveI := equivalence_isIso_homEquiv
    (thickeningRetractionEquivalence B S hS hi h hq CommRingCat.{u}).symm
    (P := structureSheaf B S hS X'.1 X'.2) (R := Rr) y.hom (Iso.isIso_hom y)
  asIso
    (((thickeningRetractionEquivalence B S hS hi h hq CommRingCat.{u}).symm.toAdjunction.homEquiv
      (structureSheaf B S hS X'.1 X'.2) Rr) y.hom)

/-- **The transpose is compatible with the structure maps**: if `y` carries the restriction
`q_* 𝒪_{X'} ⟶ 𝒪_X` to `π : Rr ⟶ 𝒪_X`, then its transpose followed by `i^* π` is the structure map
`𝒪_{X'} ⟶ i^* 𝒪_X` of chart base change along `i`. -/
theorem thickeningRetractionTranspose_hom_comp (y : thickeningRetractionRing B S hS hq ≅ Rr)
    (π : Rr ⟶ structureSheaf B S hS X.1 X.2)
    (hπ : y.hom ≫ π = thickeningRetractionRestriction B S hS hi h hq) :
    (thickeningRetractionTranspose B S hS hi h hq y).hom ≫
        (thickeningRetractionEquivalence B S hS hi h hq CommRingCat.{u}).functor.map π =
      smallBaseChangeSharpCommRingCat B S hS i hi.isClosedImmersion.rep :=
  adjunction_homEquiv_comp_map_eq
    (thickeningRetractionEquivalence B S hS hi h hq CommRingCat.{u}).symm.toAdjunction y.hom π
    (smallBaseChangeSharpCommRingCat B S hS i hi.isClosedImmersion.rep)
    (hπ.trans (thickeningRetractionEquivalence_homEquiv_symm B S hS hi h hq CommRingCat.{u}
      (structureSheaf B S hS X'.1 X'.2) (structureSheaf B S hS X.1 X.2)
      (smallBaseChangeSharpCommRingCat B S hS i hi.isClosedImmersion.rep)).symm)

end Transpose

end AlgebraicGeometry.Space

end
