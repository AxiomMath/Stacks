module

public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupDualSection
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupFibreDimension

/-!
# Extending a map along a two-term complex on the blowup (the corrected Tag 0GAD)

[Stacks, Tag 0GAD] says that for a two-term complex `K = [K⁻¹ → K⁰]` over `R = A/Iⁿ` whose
`Ext¹` is annihilated by `I^c`, the class of a map `K⁻¹ → Iⁿ/I^{2n}` dies in
`Ext¹(K, I^{n-(1+d)c}/I^{2n-2(1+d)c})`. Its proof for `d > 0` goes through Tag 0GAC and reaches
only the level `n - (2+d)c` (the identity `φ' = ψ ∘ d` it concludes with compares maps at two
different levels). Its proof for `d = 0` is different and reaches the stated level: lift locally
on the blowup, where `I` is principal, and kill the global obstruction by the vanishing of `H¹`.

This file carries out that second argument for every `d`, at the source's level, for the
complexes `[M → R^{⊕r}]` with `M` an `(A, n, c)`-module and multiplication by `I^c` on `M`
factoring through the differential — which is what the obstruction complex of Stacks 0GAQ is,
by the obstruction relation of Stacks 0GAP. No dual sheaf is formed: the obstruction is tracked
through the transposed presentations of `BitUniformityIII/TransposePresentation.lean`.

* `blowupHmodMap_cokerπ_twistDown_eq_zero`, the local step: on `D₊(b)` multiplication by `b^c`
  is invertible and `b^c` splits through the differential, so the twist by `c` of the section
  attached to `φ` lies in `H⁰(𝒢)` of the presentation of the cokernel of the transpose
  (`comp_twistDown_eq_zero_of_smul_eq_zero`).
* `exists_lift_transD`, the global step: the dotted arrow of [Stacks, Tag 0GAA] and its
  clauses (4) and (5) lift that section through the transpose after a further twist by `dc`;
  for `d = 0`, `H¹(ℱ) = 0` instead.
* `exists_extension_of_split`: **the corrected Tag 0GAD**, the extension `Λ : R^{⊕r} → I^f/I^{f+n}`
  of `φ` twisted down to level `f = n - (1+d)c`.

## References

* [Stacks Project, Tag 0GAD](https://stacks.math.columbia.edu/tag/0GAD)
* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 0GA8](https://stacks.math.columbia.edu/tag/0GA8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace
open AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.LocalCohomology.UniformityIII

attribute [local instance] modulesMonoidal modulesMonoidal' modulesEnoughInjectives
attribute [local instance] sheafSectionsPreservesFiniteLimits secFPreservesFiniteLimits
attribute [local instance] HasDerivedCategory.standard
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- **A morphism into a twisted pullback that every `b^c`, `b ∈ I`, annihilates dies on twisting
down by `c`.** This is `kernelι_comp_twistDown_eq_zero` for an arbitrary morphism in place of
the inclusion of `ℱ(q)`: twisting down followed by multiplication by `(b⁽¹⁾)^c` is `b^c • 𝟙`,
which kills the morphism, and that multiplication is injective on the sections over every open
inside `D₊(b⁽¹⁾)`; those opens cover the blowup. -/
theorem comp_twistDown_eq_zero_of_smul_eq_zero {c : ℕ} (q q' : ℤ) (hq : (c : ℤ) + q' = q)
    (hle : q' ≤ q) {Z : _root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf}
    {N : ModuleCat.{u} A} (ρ : Z ⟶ (twistedPullbackFunctor I q).obj N)
    (hzero :
      letI : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
        Stacks.Blowup.blowUpModulesLinear I
      ∀ b ∈ I, (b ^ c) • ρ = 0) :
    ρ ≫ (twistedPullbackTwistDown I q q' hle).app N = 0 := by
  let : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
    Stacks.Blowup.blowUpModulesLinear I
  have hloc : ∀ (r : I) (W : (blowupScheme I).Opens),
      W ≤ Proj.basicOpen (Stacks.Blowup.reesGrading I) (Stacks.Blowup.reesDegOne I r.2) →
      (ρ ≫ (twistedPullbackTwistDown I q q' hle).app N).val.app (op W) = 0 := by
    intro r W hW
    have hstep :
        (twistedPullbackTwistDown I q q' hle).app N ≫
            (twistedPullbackTwistScalar I c q' q hq
                ⟨(Stacks.Blowup.reesDegOne I r.2 : reesAlgebra I) ^ c,
                  Stacks.Blowup.reesDegOnePow_mem_reesGrading I r.2 c⟩).app N =
          ((r : A) ^ c) • 𝟙 ((twistedPullbackFunctor I q).obj N) :=
      (NatTrans.comp_app _ _ _).symm.trans
        ((NatTrans.congr_app
              (Stacks.Blowup.twistDownFactorMap_comp_twistScalarFactorMap_reesDegOnePow
                I c q q' hq hle r.2)
              N).trans
          (twistScalarFactorMap_reesConst_app_eq_smul_id I q ((r : A) ^ c) N))
    refine val_app_eq_zero_of_comp_eq_zero _ _ _
      (bijective_twistedPullbackTwistScalar_app I c q' q hq r.2 N hW).1 ?_
    rw [Category.assoc, hstep, Linear.comp_smul, Category.comp_id]
    exact hzero r r.2
  refine _root_.SheafOfModules.hom_ext (TopCat.Sheaf.eq_hom_of_restrict
    (U := fun r : I => Proj.basicOpen (Stacks.Blowup.reesGrading I)
      (Stacks.Blowup.reesDegOne I r.2))
    (Stacks.Blowup.iSup_basicOpen_reesDegOne_eq_top I)
    ((twistedPullbackFunctor I q').obj N).isSheaf (fun _ _ _ => 0) (fun r V hV => ?_)
    (fun _ _ _ => rfl))
  exact hloc r V hV

/-- **`H⁰(X, -)` is left exact, on elements**: an element of `H⁰(X, F)` killed by `H⁰(f)` comes
from `H⁰(X, ker f)`. The kernel sequence `0 → ker f → F → im f → 0` is short exact and
`H⁰(im f) → H⁰(G)` is injective. -/
theorem exists_blowupHmodMap_kernelι_eq
    {F G : _root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf}
    (f : F ⟶ G) (x : blowupHmod I 0 F) (hx : blowupHmodMap I 0 f x = 0) :
    ∃ x' : blowupHmod I 0 (kernel f), blowupHmodMap I 0 (kernel.ι f) x' = x := by
  -- global sections preserve the kernel
  have hex : (ShortComplex.mk ((blowupΓmod I).map (kernel.ι f)) ((blowupΓmod I).map f)
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])).Exact :=
    ShortComplex.exact_of_f_is_kernel _
      (KernelFork.mapIsLimit _ (kernelIsKernel f) (blowupΓmod I))
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  obtain ⟨s, rfl⟩ := (bijective_blowupΓmodToH0 I F).2 x
  have hnat : ∀ {P Q : _root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf} (φ : P ⟶ Q)
      (t : (blowupΓmod I).obj P),
      blowupHmodMap I 0 φ (blowupΓmodToH0 I P t) =
        blowupΓmodToH0 I Q ((blowupΓmod I).map φ t) := fun φ t =>
    (ConcreteCategory.congr_hom ((blowupΓmod I).toRightDerivedZero.naturality φ) t).symm
  have h1 : (blowupΓmod I).map f s = 0 := by
    apply injective_blowupΓmodToH0 I G
    rw [← hnat, hx, map_zero]
  obtain ⟨s', hs'⟩ := (hex s).1 h1
  exact ⟨blowupΓmodToH0 I (kernel f) s', (hnat (kernel.ι f) s').trans (congrArg _ hs')⟩

omit [CommRing A] in
/-- In a linear functor's image, a morphism killed by `T(e)` is killed by `r • T(g)` as soon as
`r • g` factors through `e`. Stated for abstract linear categories, where it is three rewrites. -/
theorem smul_comp_map_eq_zero {R : Type*} [CommRing R] {C D : Type*} [Category C] [Preadditive C]
    [Linear R C] [Category D] [Preadditive D] [Linear R D] (T : C ⥤ D) [T.Additive] [T.Linear R]
    {K : D} {X X' Y : C} (ι : K ⟶ T.obj X) (e : X ⟶ X') (g : X ⟶ Y) (k : X' ⟶ Y) (r : R)
    (hk : r • g = e ≫ k) (hι : ι ≫ T.map e = 0) : r • (ι ≫ T.map g) = 0 := by
  rw [← Linear.comp_smul, ← Functor.Linear.map_smul, hk, T.map_comp, ← Category.assoc, hι,
    zero_comp]

/-- `H^i` of the twisted pullback of a composite is the composite of the `H^i`s. -/
private theorem blowupHmodMap_map_comp_apply (i : ℕ) (q : ℤ) {X Y Z : ModuleCat.{u} A}
    (g : X ⟶ Y) (g' : Y ⟶ Z) (x : blowupHmodTwistedPullback I X i q) :
    blowupHmodMap I i ((twistedPullbackFunctor I q).map (g ≫ g')) x =
      blowupHmodMap I i ((twistedPullbackFunctor I q).map g')
        (blowupHmodMap I i ((twistedPullbackFunctor I q).map g) x) :=
  (congrArg (fun φ => blowupHmodMap I i φ x) ((twistedPullbackFunctor I q).map_comp _ _)).trans
    (blowupHmodMap_comp_apply I i _ _ x)

section Lift

variable [IsNoetherianRing A] {n c : ℕ} {M : ANCModule I n c} (P : TwoStepPresentation M)
  {r : ℕ} (D : M.1 →ₗ[A ⧸ I ^ n] (Fin r → A ⧸ I ^ n))
  (hD : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
    ∃ h : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] M.1, ∀ z, h (D z) = a • z)

/-- A map between standard free `A ⧸ Iⁿ`-modules, as a morphism of `A`-modules. -/
abbrev resLin {r s : ℕ} (g : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin s → A ⧸ I ^ n)) :
    ModuleCat.of A (Fin r → A ⧸ I ^ n) ⟶ ModuleCat.of A (Fin s → A ⧸ I ^ n) :=
  ModuleCat.ofHom (g.restrictScalars A)

omit [IsNoetherianRing A] in
/-- `resLin` takes composition of `A ⧸ Iⁿ`-linear maps to composition of morphisms. -/
theorem resLin_comp {r s t : ℕ} (g : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin s → A ⧸ I ^ n))
    (g' : (Fin s → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin t → A ⧸ I ^ n)) :
    resLin I g ≫ resLin I g' = resLin I (g' ∘ₗ g) := rfl

omit [IsNoetherianRing A] in
/-- `resLin I g` acts on a vector `v` as `g` does. -/
theorem resLin_apply {r s : ℕ} (g : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin s → A ⧸ I ^ n))
    (v : Fin r → A ⧸ I ^ n) : (resLin I g).hom v = g v := rfl

/-- **`b^c` on the cokernel `C` of the transpose of `D ∘ π` factors through the transposed
relation matrix of `M`**, by the identity of `TwoStepPresentation.exists_transpose_comp`. -/
theorem exists_smul_cokerπ_eq_comp {b : A} (hb : b ∈ I) :
    ∃ k : ModuleCat.of A (Fin P.r₁ → A ⧸ I ^ n) ⟶
        (P.cokernelPres D hD).presC.resShortComplex.X₃,
      (b ^ c) • (P.cokernelPres D hD).presC.resShortComplex.g = resLin I P.transD ≫ k := by
  obtain ⟨hh, hhh⟩ := hD (Ideal.Quotient.mk (I ^ n) (b ^ c))
    (Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow hb c))
  obtain ⟨ht, ℓ, hid⟩ := P.exists_transpose_comp D _ hh hhh
  refine ⟨-(resLin I (finTranspose ℓ) ≫ (P.cokernelPres D hD).presC.resShortComplex.g), ?_⟩
  refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
  have hv := LinearMap.congr_fun hid v
  simp only [LinearMap.coe_comp] at hv
  let w : Fin P.r₀ → A ⧸ I ^ n := v
  have key : (Submodule.Quotient.mk (Ideal.Quotient.mk (I ^ n) (b ^ c) • w) :
        (Fin P.r₀ → A ⧸ I ^ n) ⧸ (P.cokernelPres D hD).imageL) =
      Submodule.Quotient.mk (-(finTranspose ℓ (P.transD w))) :=
    (Submodule.Quotient.eq _).2 ⟨finTranspose ht w, by rw [sub_neg_eq_add]; exact hv⟩
  exact key

/-- **Every `b^c` kills the image of the kernel of the transposed relation matrix in the
twisted pullback of `C`.** -/
theorem smul_kernelι_comp_cokerπ_eq_zero (q : ℤ) {b : A} (hb : b ∈ I) :
    letI : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
      Stacks.Blowup.blowUpModulesLinear I
    (b ^ c) • (kernel.ι ((twistedPullbackFunctor I q).map (resLin I P.transD)) ≫
      (twistedPullbackFunctor I q).map (P.cokernelPres D hD).presC.resShortComplex.g) = 0 := by
  let : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
    Stacks.Blowup.blowUpModulesLinear I
  let : (twistedPullbackFunctor I q).Linear A := linear_twistedPullbackFunctor I q
  obtain ⟨k, hk⟩ := exists_smul_cokerπ_eq_comp I P D hD hb
  exact smul_comp_map_eq_zero (twistedPullbackFunctor I q) _ (resLin I P.transD) _ k (b ^ c) hk
    (kernel.condition _)

/-- **The local step of the lift.** Let `y` be a section of `𝒪_X(q) ⊗ p^*(R^{⊕r₀})~` killed by the
transposed relation matrix of `M`. Its twist down by `c`, pushed into the twisted pullback of
the cokernel `C` of the transpose of `D ∘ π`, vanishes: the kernel of the transposed relation
matrix maps into that twisted pullback by a morphism every `b^c` kills
(`smul_kernelι_comp_cokerπ_eq_zero`), and twisting down kills any such morphism
(`comp_twistDown_eq_zero_of_smul_eq_zero`). -/
theorem blowupHmodMap_cokerπ_twistDown_eq_zero (q q' : ℤ) (hq : (c : ℤ) + q' = q)
    (hle : q' ≤ q) (y : blowupHmodTwistedPullback I (ModuleCat.of A (Fin P.r₀ → A ⧸ I ^ n)) 0 q)
    (hy : blowupHmodMap I 0 ((twistedPullbackFunctor I q).map (resLin I P.transD)) y = 0) :
    blowupHmodMap I 0 ((twistedPullbackFunctor I q').map
      ((P.cokernelPres D hD).presC.resShortComplex.g))
      (blowupHtr I (ModuleCat.of A (Fin P.r₀ → A ⧸ I ^ n)) 0 q q' hle y) = 0 := by
  have hρ := comp_twistDown_eq_zero_of_smul_eq_zero I q q' hq hle _
    (fun b hb => smul_kernelι_comp_cokerπ_eq_zero I P D hD q hb)
  obtain ⟨y', rfl⟩ := exists_blowupHmodMap_kernelι_eq I _ y hy
  have hnat := (twistedPullbackTwistDown I q q' hle).naturality
    (P.cokernelPres D hD).presC.resShortComplex.g
  have h2 : (kernel.ι ((twistedPullbackFunctor I q).map (resLin I P.transD)) ≫
        (twistedPullbackTwistDown I q q' hle).app _) ≫
        (twistedPullbackFunctor I q').map (P.cokernelPres D hD).presC.resShortComplex.g = 0 := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun φ => kernel.ι ((twistedPullbackFunctor I q).map (resLin I P.transD)) ≫ φ)
      hnat.symm).trans ?_
    exact (Category.assoc _ _ _).symm.trans hρ
  have h3 := blowupHmodMap_comp_apply I 0 (kernel.ι ((twistedPullbackFunctor I q).map
    (resLin I P.transD)) ≫ (twistedPullbackTwistDown I q q' hle).app _)
    ((twistedPullbackFunctor I q').map (P.cokernelPres D hD).presC.resShortComplex.g) y'
  have h4 := blowupHmodMap_comp_apply I 0 (kernel.ι ((twistedPullbackFunctor I q).map
    (resLin I P.transD))) ((twistedPullbackTwistDown I q q' hle).app _) y'
  refine (congrArg (fun t => blowupHmodMap I 0
    ((twistedPullbackFunctor I q').map (P.cokernelPres D hD).presC.resShortComplex.g) t)
    h4.symm).trans ?_
  refine h3.symm.trans ?_
  exact (congrArg (fun φ => blowupHmodMap I 0 φ y') h2).trans
    (ConcreteCategory.congr_hom (((blowupΓmod I).rightDerived 0).map_zero _ _) y')

/-- **The local step, read in `H⁰(𝒢)`.** The twist down by `c` of a section killed by the
transposed relation matrix comes from `H⁰(𝒢)` of the presentation `0 → L → R^{⊕r₀} → C → 0`
of the cokernel of the transpose of `D ∘ π`. -/
theorem exists_twistedPullbackImage_of_transD (q q' : ℤ) (hq : (c : ℤ) + q' = q)
    (hle : q' ≤ q) (y : blowupHmodTwistedPullback I (ModuleCat.of A (Fin P.r₀ → A ⧸ I ^ n)) 0 q)
    (hy : blowupHmodMap I 0 ((twistedPullbackFunctor I q).map (resLin I P.transD)) y = 0) :
    ∃ s : blowupHmod I 0
        (twistedPullbackImage I q' (S := (P.cokernelPres D hD).presC.resShortComplex)),
      blowupHmodMap I 0
          ((P.cokernelPres D hD).presC.resShortComplex.map (twistedPullbackFunctor I q')).iCycles
          s =
        blowupHtr I (ModuleCat.of A (Fin P.r₀ → A ⧸ I ^ n)) 0 q q' hle y :=
  (exact_blowupHmodMap I _ _ _ (shortExact_twistedPullbackFreeSequence I q'
    (P.cokernelPres D hD).presC.shortExact_resShortComplex) 0 _).1
    (blowupHmodMap_cokerπ_twistDown_eq_zero I P D hD q q' hq hle y hy)

end Lift

section SecMLift

variable [IsNoetherianRing A] {n c : ℕ} {N : ANCModule I n c} (PN : TwoStepPresentation N)

/-- `x ↦ x • v`, `A/Iⁿ → R^{⊕r}`, over `A`. -/
def smulVecHom {r : ℕ} (v : Fin r → A ⧸ I ^ n) :
    ModuleCat.of A (A ⧸ I ^ n) ⟶ ModuleCat.of A (Fin r → A ⧸ I ^ n) :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton (A ⧸ I ^ n) _ v).restrictScalars A)

/-- **The canonical sections of the twisted pullback of `L` come from `R^{⊕r₀}`.** Every value of
the canonical map `(I^q/I^{q+n}) ⊗_A L → H⁰(X, 𝒪_X(q) ⊗ p^*L~)` is the image of a section of
`𝒪_X(q) ⊗ p^*(R^{⊕r₀})~` under the surjection `R^{⊕r₀} → L`. -/
theorem exists_presL_g_eq_twistedPullbackSecM (q₀ : ℕ) (h : IsBaseThreshold I q₀) (hcn : c ≤ n)
    (q : ℕ) (t : powTensor I n q PN.imageANC.1) :
    ∃ x : blowupHmodTwistedPullback I (ModuleCat.of A (Fin PN.r₀ → A ⧸ I ^ n)) 0 (q : ℤ),
      blowupHmodMap I 0 ((twistedPullbackFunctor I (q : ℤ)).map PN.presL.resShortComplex.g) x =
        twistedPullbackSecM I q₀ h n c hcn PN.imageANC q t := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, (map_zero (blowupHmodMap I 0 ((twistedPullbackFunctor I (q : ℤ)).map
      PN.presL.resShortComplex.g)).hom).trans (map_zero _).symm⟩
  | tmul a l =>
    obtain ⟨v, hv⟩ := PN.transD.surjective_rangeRestrict l
    refine ⟨blowupHmodMap I 0 ((twistedPullbackFunctor I (q : ℤ)).map (smulVecHom I v))
      ((blowupHmodTwistedPullbackQuotientEquiv I n 0 q).symm
        ((blowupSituationOf I q₀ h).cdiv n q a)), ?_⟩
    rw [twistedPullbackSecM_tmul]
    have hcomp : smulVecHom I v ≫ PN.presL.resShortComplex.g =
        resSmulHom I n PN.imageANC.1 l := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      show PN.transD.rangeRestrict (x • v) = x • (l : PN.imageL)
      rw [map_smul, hv]
      rfl
    rw [← hcomp]
    exact (blowupHmodMap_map_comp_apply I 0 (q : ℤ) _ _ _).symm
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨x₁, hx₁⟩ := h₁
    obtain ⟨x₂, hx₂⟩ := h₂
    exact ⟨x₁ + x₂, ((map_add (blowupHmodMap I 0 ((twistedPullbackFunctor I (q : ℤ)).map
      PN.presL.resShortComplex.g)).hom x₁ x₂).trans (congrArg₂ (· + ·) hx₁ hx₂)).trans
      (map_add _ _ _).symm⟩

end SecMLift

section Cycles

variable [IsNoetherianRing A] {S : ShortComplex (ModuleCat.{u} A)}

/-- `H⁰` of the inclusion `𝒢 ⊆ 𝒪_X(q) ⊗ p^*S₂~` commutes with twisting down. -/
theorem blowupHmodMap_iCycles_blowupHGtr (i : ℕ) (q q' : ℤ) (hq : q' ≤ q)
    (x : blowupHmod I i (twistedPullbackImage I q (S := S))) :
    blowupHmodMap I i (S.map (twistedPullbackFunctor I q')).iCycles
        (blowupHGtr I i q q' hq (S := S) x) =
      blowupHtr I S.X₂ i q q' hq
        (blowupHmodMap I i (S.map (twistedPullbackFunctor I q)).iCycles x) := by
  have hcyc := ShortComplex.cyclesMap_i (twistDownShortComplexMap I q q' hq (S := S))
  have h := ConcreteCategory.congr_hom (congrArg (fun φ => blowupHmodMap I i φ) hcyc) x
  simp only [Functor.map_comp] at h
  exact h

/-- `H⁰` of `𝒪_X(q) ⊗ p^*S.f~` is `H⁰` of `toCycles` followed by `H⁰` of `iCycles`. -/
theorem blowupHmodMap_map_f (i : ℕ) (q : ℤ) (x : blowupHmodTwistedPullback I S.X₁ i q) :
    blowupHmodMap I i ((twistedPullbackFunctor I q).map S.f) x =
      blowupHmodMap I i (S.map (twistedPullbackFunctor I q)).iCycles
        (blowupHmodMap I i (S.map (twistedPullbackFunctor I q)).toCycles x) :=
  (congrArg (fun φ => blowupHmodMap I i φ x)
    (S.map (twistedPullbackFunctor I q)).toCycles_i.symm).trans
    (blowupHmodMap_comp_apply I i _ _ x)

end Cycles

section LiftThroughTranspose

variable [IsNoetherianRing A] {d : ℕ}
  (hfib : ∀ s, topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (d : WithBot ℕ∞))
  (q₀ : ℕ) (h : IsBaseThreshold I q₀) {n c : ℕ} (hcn : c ≤ n) {N : ANCModule I n c}
  (PN : TwoStepPresentation N)

/-- The transposed relation matrix `PN.transD`, as a morphism of `A`-modules, is the composite
`R^{⊕r₀} → L → R^{⊕r₁}` of the two short exact sequences of the presentation. -/
theorem resLin_transD_eq :
    resLin I PN.transD = PN.presL.resShortComplex.g ≫ PN.presC.resShortComplex.f := rfl

/-- `H⁰` of the transposed relation matrix on a lift of `u ∈ H⁰(𝒪_X(q) ⊗ p^*L~)` through
`R^{⊕r₀} → L`. -/
theorem blowupHmodMap_transD_of_presL_g (q : ℤ)
    (x : blowupHmodTwistedPullback I (ModuleCat.of A (Fin PN.r₀ → A ⧸ I ^ n)) 0 q)
    (u : blowupHmodTwistedPullback I PN.presL.resShortComplex.X₃ 0 q)
    (hx : blowupHmodMap I 0 ((twistedPullbackFunctor I q).map PN.presL.resShortComplex.g) x = u) :
    blowupHmodMap I 0 ((twistedPullbackFunctor I q).map (resLin I PN.transD)) x =
      blowupHmodMap I 0 ((twistedPullbackFunctor I q).map PN.presC.resShortComplex.f) u := by
  rw [← hx, resLin_transD_eq]
  exact blowupHmodMap_map_comp_apply I 0 q _ _ x

include h hcn in
/-- **The lift through the transpose when the fibres of the blowup are finite.** Here `H¹(ℱ)`
vanishes, so `s` lifts to the twisted pullback of `L` with no twist at all, and clause (4) of
[Stacks, Tag 0GAA] puts that lift into the image of the canonical sections, which come from
`R^{⊕r₀^N}` (`exists_presL_g_eq_twistedPullbackSecM`). -/
private theorem exists_lift_transD_of_fiber_le_zero
    (hfib₀ : ∀ s, topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ ((0 : ℕ) : WithBot ℕ∞))
    {t : ℕ} (hq : q₀ ≤ t)
    (s : blowupHmod I 0 (twistedPullbackImage I t (S := PN.presC.resShortComplex))) :
    ∃ x : blowupHmodTwistedPullback I (ModuleCat.of A (Fin PN.r₀ → A ⧸ I ^ n)) 0 (t : ℤ),
      blowupHmodMap I 0 ((twistedPullbackFunctor I (t : ℤ)).map (resLin I PN.transD)) x =
        blowupHtr I PN.presC.resShortComplex.X₂ 0 (t : ℤ) (t : ℤ) le_rfl
          (blowupHmodMap I 0
            (PN.presC.resShortComplex.map (twistedPullbackFunctor I (t : ℤ))).iCycles s) := by
  let SW := blowupTwistedModuleSituationOfFiberLE I hfib₀ q₀ h n c hcn
  have hfin : Module.Finite A PN.presC.resShortComplex.X₁ := by
    have : Module.Finite (A ⧸ I ^ n) PN.imageL := PN.isANCModule_imageL.1
    exact finite_resModule I n (ModuleCat.of (A ⧸ I ^ n) PN.imageL)
  have := isCoherent_twistedPullbackSupported I (t : ℤ) (S := PN.presC.resShortComplex)
  have hF : Subsingleton (blowupHmod I 1
      (twistedPullbackSupported I (t : ℤ) (S := PN.presC.resShortComplex))) :=
    subsingleton_blowupHmod_of_fiber_le I hfib₀ _ (by omega)
  obtain ⟨u, hu⟩ := (exact_blowupHmodMap_δ I _ _ (kernel.condition _)
    (shortExact_twistedPullbackKernelSequence I (t : ℤ)
      PN.presC.shortExact_resShortComplex) 0 s).1 (hF.elim _ _)
  obtain ⟨t', ht'⟩ := SW.surjective_secM PN.imageANC (show SW.d ≤ 1 by
    show 0 ≤ 1; omega) (show SW.q₀ ≤ t by change q₀ ≤ t; omega) u
  obtain ⟨x, hx⟩ := exists_presL_g_eq_twistedPullbackSecM I PN q₀ h hcn t t'
  refine ⟨x, ?_⟩
  rw [blowupHmodMap_transD_of_presL_g I PN _ x u (hx.trans ht'), blowupHtr_self,
    blowupHmodMap_map_f, hu]
  rfl

include hfib h hcn in
/-- **The lift through the transpose.** A section `s` of `𝒢` of the presentation
`0 → L → R^{⊕r₀^N} → C → 0`, at level `t`, lifts after twisting down by `d·c` to a section of
`𝒪_X(t - dc) ⊗ p^*(R^{⊕r^N})~` whose image under the transposed relation matrix is the twist of
`s`. For `d ≥ 1`: the dotted arrow of [Stacks, Tag 0GAA] lifts the twist by `c` of `s` to the
twisted pullback of `L`, clause (5) of [Stacks, Tag 0GAA] (clause (4) for `d = 1`) puts a
further twist by `(d-1)c` into the image of the canonical sections, and those come from
`R^{⊕r₀^N}` (`exists_presL_g_eq_twistedPullbackSecM`). For `d = 0`: `H¹(ℱ) = 0`, so `s` lifts to
the twisted pullback of `L` with no twist, and clause (4) applies. -/
theorem exists_lift_transD {t f : ℕ} (hft : f + d * c = t) (hq : q₀ + d * c ≤ t)
    (s : blowupHmod I 0 (twistedPullbackImage I t (S := PN.presC.resShortComplex))) :
    ∃ x : blowupHmodTwistedPullback I (ModuleCat.of A (Fin PN.r₀ → A ⧸ I ^ n)) 0 (f : ℤ),
      blowupHmodMap I 0 ((twistedPullbackFunctor I (f : ℤ)).map (resLin I PN.transD)) x =
        blowupHtr I PN.presC.resShortComplex.X₂ 0 (t : ℤ) (f : ℤ) (by omega)
          (blowupHmodMap I 0
            (PN.presC.resShortComplex.map (twistedPullbackFunctor I (t : ℤ))).iCycles s) := by
  let SW := blowupTwistedModuleSituationOfFiberLE I hfib q₀ h n c hcn
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- `d = 0`: no twist at all
    subst hd0
    obtain rfl : f = t := by simpa using hft
    exact exists_lift_transD_of_fiber_le_zero I q₀ h hcn PN hfib (by omega) s
  · -- `d ≥ 1`: the dotted arrow first
    obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₁ + c = t := ⟨t - c, by
      have : c ≤ d * c := Nat.le_mul_of_pos_left c hdpos
      omega⟩
    have hle₁ : ((t₁ : ℕ) : ℤ) ≤ (t : ℤ) := by omega
    have hct : (c : ℤ) + (t₁ : ℤ) = (t : ℤ) := by omega
    set u := blowupHmodMap I 0 (dottedOfPresentation I PN.presC (t : ℤ) (t₁ : ℤ) hct hle₁) s
      with hu
    have hu' : blowupHmodMap I 0
        (PN.presC.resShortComplex.map (twistedPullbackFunctor I (t₁ : ℤ))).toCycles u =
        blowupHGtr I 0 (t : ℤ) (t₁ : ℤ) hle₁ (S := PN.presC.resShortComplex) s :=
      ConcreteCategory.congr_hom
        (blowupHmodMap_dottedOfPresentation_comp_toCycles I PN.presC 0 (t : ℤ) (t₁ : ℤ) hct hle₁) s
    have hfu : blowupHmodMap I 0
        ((twistedPullbackFunctor I (t₁ : ℤ)).map PN.presC.resShortComplex.f) u =
        blowupHtr I PN.presC.resShortComplex.X₂ 0 (t : ℤ) (t₁ : ℤ) hle₁
          (blowupHmodMap I 0
            (PN.presC.resShortComplex.map (twistedPullbackFunctor I (t : ℤ))).iCycles s) := by
      rw [blowupHmodMap_map_f, hu']
      exact blowupHmodMap_iCycles_blowupHGtr I 0 (t : ℤ) (t₁ : ℤ) hle₁ s
    rcases Nat.lt_or_ge d 2 with hd1 | hd2
    · -- `d = 1`: clause (4)
      obtain rfl : d = 1 := by omega
      obtain rfl : f = t₁ := by omega
      obtain ⟨t', ht'⟩ := SW.surjective_secM PN.imageANC (show SW.d ≤ 1 by
        show 1 ≤ 1; omega) (show SW.q₀ ≤ f by change q₀ ≤ f; omega) u
      obtain ⟨x, hx⟩ := exists_presL_g_eq_twistedPullbackSecM I PN q₀ h hcn f t'
      exact ⟨x, (blowupHmodMap_transD_of_presL_g I PN _ x u (hx.trans ht')).trans hfu⟩
    · -- `d ≥ 2`: clause (5)
      obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
      have hk : 1 ≤ k := by omega
      have hfk : f + k * c = t₁ := by rw [add_mul, one_mul] at hft; omega
      have hle₂ : ((f : ℕ) : ℤ) ≤ (t₁ : ℤ) := by omega
      have hmem := SW.range_Htr_le PN.imageANC (r := f) (q := (t₁ : ℤ)) hle₂ hk
        (show k + 1 = SW.d from rfl) (by rw [← hfk]; push_cast; ring)
        (show (SW.q₀ : ℤ) + k * c ≤ (t₁ : ℤ) by
          show (q₀ : ℤ) + k * c ≤ (t₁ : ℤ)
          rw [add_mul, one_mul] at hq
          omega) ⟨u, rfl⟩
      obtain ⟨t', ht'⟩ := hmem
      obtain ⟨x, hx⟩ := exists_presL_g_eq_twistedPullbackSecM I PN q₀ h hcn f t'
      refine ⟨x, ?_⟩
      rw [blowupHmodMap_transD_of_presL_g I PN _ x _ (hx.trans ht')]
      have hnat := ConcreteCategory.congr_hom
        (blowupHtr_naturality I PN.presC.resShortComplex.f 0 (t₁ : ℤ) (f : ℤ) hle₂) u
      refine hnat.symm.trans ?_
      show blowupHtr I PN.presC.resShortComplex.X₂ 0 (t₁ : ℤ) (f : ℤ) hle₂
        (blowupHmodMap I 0 ((twistedPullbackFunctor I (t₁ : ℤ)).map PN.presC.resShortComplex.f) u)
        = _
      rw [hfu]
      exact ConcreteCategory.congr_hom
        (blowupHtr_comp I PN.presC.resShortComplex.X₂ 0 (t : ℤ) (t₁ : ℤ) (f : ℤ) hle₂ hle₁ _) _

end LiftThroughTranspose

section Extension

variable [IsNoetherianRing A] {n c : ℕ}

omit [IsNoetherianRing A] in
/-- Evaluating against `w` after transposing `E` is evaluating against `E w`. -/
theorem resLin_finTranspose_comp_evalVec {s r : ℕ}
    (E : (Fin s → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] (Fin r → A ⧸ I ^ n)) (w : Fin s → A ⧸ I ^ n) :
    resLin I (finTranspose E) ≫ evalVec I s w = evalVec I r (E w) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun v => ?_)
  show ∑ j, finTranspose E v j * w j = ∑ k, v k * E w k
  have hEw : E w = ∑ j, w j • E (Pi.single j 1) := by
    conv_lhs => rw [pi_eq_sum_univ w, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← map_smul]
    congr 1
    ext i
    simp [Pi.single_apply, eq_comm]
  simp only [finTranspose_apply, hEw, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The readout: an element of `H⁰(X, 𝒪_X(f) ⊗ p^*(R^{⊕r})~)` as an `A`-linear map
`R^{⊕r} → I^f/I^{f+n}`, coordinate by coordinate. -/
def readout (q₀ : ℕ) (h : IsBaseThreshold I q₀) {r f : ℕ} (hf : q₀ ≤ f)
    (x : blowupHmodTwistedPullback I (ModuleCat.of A (Fin r → A ⧸ I ^ n)) 0 (f : ℤ)) :
    (Fin r → A ⧸ I ^ n) →ₗ[A] powQuot I f n where
  toFun v := cdivInv I q₀ h n hf (blowupHmodTwistedPullbackQuotientEquiv I n 0 f
    (blowupHmodMap I 0 ((twistedPullbackFunctor I (f : ℤ)).map (evalVec I r v)) x))
  map_add' v v' := by
    have hadd : evalVec I r (v + v') = evalVec I r v + evalVec I r v' := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change ∑ j, x j * (v + v') j = ∑ j, x j * v j + ∑ j, x j * v' j
      simp [mul_add, Finset.sum_add_distrib]
    have h1 : (twistedPullbackCohomologyFunctor I 0 (f : ℤ)).map (evalVec I r (v + v')) =
        (twistedPullbackCohomologyFunctor I 0 (f : ℤ)).map (evalVec I r v) +
          (twistedPullbackCohomologyFunctor I 0 (f : ℤ)).map (evalVec I r v') := by
      rw [hadd, Functor.map_add]
    have h2 := congrArg (fun ψ => ψ.hom x) h1
    simp only [ModuleCat.hom_add, LinearMap.add_apply] at h2
    change cdivInv I q₀ h n hf (blowupHmodTwistedPullbackQuotientEquiv I n 0 f
      ((twistedPullbackCohomologyFunctor I 0 (f : ℤ)).map (evalVec I r (v + v')) x)) = _
    rw [h2]
    exact (congrArg (cdivInv I q₀ h n hf) (map_add _ _ _)).trans (map_add _ _ _)
  map_smul' a v := by
    let := linear_twistedPullbackCohomologyFunctor I 0 (f : ℤ)
    have hsmul : evalVec I r (a • v) = a • evalVec I r v := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
      change ∑ j, x j * (a • v) j = a • ∑ j, x j * v j
      simp only [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h1 : (twistedPullbackCohomologyFunctor I 0 (f : ℤ)).map (evalVec I r (a • v)) =
        a • (twistedPullbackCohomologyFunctor I 0 (f : ℤ)).map (evalVec I r v) := by
      rw [hsmul, Functor.Linear.map_smul]
    have h2 := congrArg (fun ψ => ψ.hom x) h1
    simp only [ModuleCat.hom_smul, LinearMap.smul_apply] at h2
    change cdivInv I q₀ h n hf (blowupHmodTwistedPullbackQuotientEquiv I n 0 f
      ((twistedPullbackCohomologyFunctor I 0 (f : ℤ)).map (evalVec I r (a • v)) x)) = _
    rw [h2]
    exact (congrArg (cdivInv I q₀ h n hf) (map_smul _ _ _)).trans (map_smul _ _ _)

/-- **The corrected Tag 0GAD, on the blowup.** Let `M` be an `(A, n, c)`-module and
`D : M → R^{⊕r}` a map such that multiplication by every element of `I^c` on `M` factors through
`D`. Let `d` bound the dimensions of the fibres of the blowup and `q₀` have the defining property
of `q(S)`, and let `f + (d + 1)c = n` with `q₀ ≤ f`. Then for every `A`-linear `φ : M → Iⁿ/I^{2n}`
the twist of `φ` down to level `f` extends along `D`: there is `Λ : R^{⊕r} → I^f/I^{f+n}` with
`Λ ∘ D = φ` twisted down.

This is the statement the source's Tag 0GAD reaches for the two-term complex `M → R^{⊕r}`, at the
source's level `n - (1+d)c`. The source's own argument for `d > 0` reaches only
`n - (2+d)c`; the argument here is the one the source gives for `d = 0`, a local lift followed by
the vanishing of a global obstruction, carried out for every `d`: the local step
(`blowupHmodMap_cokerπ_twistDown_eq_zero`) costs `c`, and the lift through the transpose
(`exists_lift_transD`) costs `dc`. -/
theorem exists_extension_of_split {d : ℕ}
    (hfib : ∀ s, topologicalKrullDim ((Stacks.Blowup.toSpec I).fiber s) ≤ (d : WithBot ℕ∞))
    (q₀ : ℕ) (h : IsBaseThreshold I q₀) (hcn : c ≤ n) {M : ANCModule I n c} {r : ℕ}
    (D : M.1 →ₗ[A ⧸ I ^ n] (Fin r → A ⧸ I ^ n))
    (hD : ∀ a ∈ Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c),
      ∃ h : (Fin r → A ⧸ I ^ n) →ₗ[A ⧸ I ^ n] M.1, ∀ z, h (D z) = a • z)
    (φ : resModule I n M.1 →ₗ[A] powQuot I n n) {f : ℕ} (hf : f + (d + 1) * c = n)
    (hq : q₀ ≤ f) :
    ∃ Λ : (Fin r → A ⧸ I ^ n) →ₗ[A] powQuot I f n,
      ∀ z : M.1, Λ (D z) = powQuotLe I (Nat.le.intro hf) (φ z) := by
  classical
  obtain ⟨P⟩ := nonempty_twoStepPresentation M
  set PN := P.cokernelPres D hD
  have hf' : f + d * c + c = n := by rw [add_mul, one_mul] at hf; omega
  obtain ⟨t, ht⟩ : ∃ t, t + c = n := ⟨n - c, by omega⟩
  have hnt : ((t : ℕ) : ℤ) ≤ (n : ℤ) := by omega
  have htf : ((f : ℕ) : ℤ) ≤ (t : ℤ) := by omega
  have hnf : ((f : ℕ) : ℤ) ≤ (n : ℤ) := by omega
  set y := presSection I q₀ h P φ
  have hy : blowupHmodMap I 0 ((twistedPullbackFunctor I (n : ℤ)).map (resLin I P.transD)) y = 0 :=
    blowupHmodMap_transD_presSection I q₀ h P φ
  obtain ⟨s, hs⟩ := exists_twistedPullbackImage_of_transD I P D hD (n : ℤ) (t : ℤ)
    (by omega) hnt y hy
  obtain ⟨x, hx⟩ := exists_lift_transD I hfib q₀ h hcn PN (t := t) (f := f)
    (by omega) (by omega) s
  have hx' : blowupHmodMap I 0 ((twistedPullbackFunctor I (f : ℤ)).map (resLin I PN.transD)) x =
      blowupHtr I (ModuleCat.of A (Fin P.r₀ → A ⧸ I ^ n)) 0 (n : ℤ) (f : ℤ) hnf y := by
    rw [hx]
    show blowupHtr I (ModuleCat.of A (Fin P.r₀ → A ⧸ I ^ n)) 0 (t : ℤ) (f : ℤ) htf
      (blowupHmodMap I 0
        (PN.presC.resShortComplex.map (twistedPullbackFunctor I (t : ℤ))).iCycles s) = _
    rw [hs]
    exact ConcreteCategory.congr_hom
      (blowupHtr_comp I (ModuleCat.of A (Fin P.r₀ → A ⧸ I ^ n)) 0 (n : ℤ) (t : ℤ) (f : ℤ)
        htf hnt hnf) y
  refine ⟨readout I q₀ h hq x, fun z => ?_⟩
  obtain ⟨w, rfl⟩ := P.surjective_π z
  show cdivInv I q₀ h n hq (blowupHmodTwistedPullbackQuotientEquiv I n 0 f
    (blowupHmodMap I 0 ((twistedPullbackFunctor I (f : ℤ)).map (evalVec I r ((D ∘ₗ P.π) w))) x))
      = _
  have he : evalVec I r ((D ∘ₗ P.π) w) = resLin I PN.transD ≫ evalVec I P.r₀ w :=
    (resLin_finTranspose_comp_evalVec I (D ∘ₗ P.π) w).symm
  have h1 : blowupHmodMap I 0 ((twistedPullbackFunctor I (f : ℤ)).map
        (evalVec I r ((D ∘ₗ P.π) w))) x =
      blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (n : ℤ) (f : ℤ) hnf
        ((blowupHmodTwistedPullbackQuotientEquiv I n 0 n).symm
          ((blowupSituationOf I q₀ h).cdiv n n (φ (P.π w)))) := by
    refine ((congrArg (fun g => blowupHmodMap I 0 ((twistedPullbackFunctor I (f : ℤ)).map g) x)
      he).trans (blowupHmodMap_map_comp_apply I 0 (f : ℤ) _ _ x)).trans ?_
    refine (congrArg (fun t => blowupHmodMap I 0
      ((twistedPullbackFunctor I (f : ℤ)).map (evalVec I P.r₀ w)) t) hx').trans ?_
    refine (ConcreteCategory.congr_hom
      (blowupHtr_naturality I (evalVec I P.r₀ w) 0 (n : ℤ) (f : ℤ) hnf) y).symm.trans ?_
    exact congrArg (fun t => blowupHtr I (ModuleCat.of A (A ⧸ I ^ n)) 0 (n : ℤ) (f : ℤ) hnf t)
      (blowupHmodMap_evalVec_presSection I q₀ h P φ w)
  refine (congrArg (fun t => cdivInv I q₀ h n hq (blowupHmodTwistedPullbackQuotientEquiv I n 0 f t))
    h1).trans ?_
  exact cdivInv_blowupHtr_cdiv I q₀ h n n f (by omega) hq (Nat.le.intro hf) hnf (φ (P.π w))

end Extension

end Stacks.LocalCohomology.UniformityIII

end
