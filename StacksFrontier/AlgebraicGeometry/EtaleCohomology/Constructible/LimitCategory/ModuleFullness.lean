module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.ModuleSectionsSurjectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.StageRealization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.ConstantMorphisms
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StageFaithfulnessModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.FlatEtaleStalks
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fullness of the comparison for constructible sheaves of modules on a limit

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms and let `Λ` be a Noetherian ring. For constructible
sheaves of `Λ`-modules `F`, `G` on `(X_i)_étale`, every map `p_i⁻¹F ⟶ p_i⁻¹G` on `X_étale` comes
from a map at a later stage. This is the fullness assertion of Stacks 09YU, clause (3).

The proof is the source's. For `F = j_{U!}Λ` with `U` affine, a map out of `p_i⁻¹F` is a section
of `p_i⁻¹G` over `U ×_{X_i} X`, which comes from a stage by the degree zero case of Stacks 09YQ
(`AlgebraicGeometry.exists_smallEtaleStageLeg_eq_module`). Finite direct sums follow, a
realization persisting to later stages. A general constructible `F` is a quotient of such a sum by
Stacks 095N; the map on the sum is realized at a stage, its restriction to the kernel vanishes on
`X`, hence at a later stage by the faithfulness assertion, and there the map descends to `F`.

## Main results

* `AlgebraicGeometry.exists_smallEtaleStage_realization_moduleShriekConstant` — one generator.
* `AlgebraicGeometry.smallEtaleStagesFull_isConstructibleModuleSheaf` — **Tag 09YU, clause (3),
  the fullness assertion.**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isRightAdjointPushforward_addCommGrpCat

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ]
  {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- The realization relation of the fullness assertion, for sheaves of `Λ`-modules: `b` at the
stage `j` induces `a` on the vertex through the canonical comparison. -/
abbrev SmallEtaleStageRealizes {i j : I} (h : i ≤ j)
    {F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (ModuleCat.{u + 1} Λ)}
    (a : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj G)
    (b : (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg h).obj F ⟶
      (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg h).obj G) : Prop :=
  (smallEtaleStageComparison B (ModuleCat.{u + 1} Λ) Dg c hX h F).inv ≫
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX j).map b ≫
      (smallEtaleStageComparison B (ModuleCat.{u + 1} Λ) Dg c hX h G).hom = a

/-- **Fullness for one generator.** A map on the vertex out of the inverse image of
`j_{U!}Λ`, for `U` quasi-compact and quasi-separated over a stage, comes from a later stage. -/
theorem exists_smallEtaleStage_realization_moduleShriekConstant (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) {i : I}
    (U : SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    [CompactSpace ((SmallEtale.toScheme B _ _).obj U)]
    [QuasiSeparatedSpace ((SmallEtale.toScheme B _ _).obj U)]
    (G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (ModuleCat.{u + 1} Λ))
    (a : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj
        (moduleShriekConstant.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ U) ⟶
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj G) :
    ∃ (j : I) (h : i ≤ j) (b : _), SmallEtaleStageRealizes B Λ Dg c hX h a b := by
  let S := moduleShriekConstant.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ U
  let pi := coneStageHom B Dg c hX i
  let A := ModuleCat.{u + 1} Λ
  let aflat :
      S ⟶ (smallEtaleSheafPushforward B A pi).obj ((smallEtaleSheafPullback B A pi).obj G) :=
    (smallEtaleSheafAdjunction B A pi).unit.app S ≫ (smallEtaleSheafPushforward B A pi).map a
  obtain ⟨j, hij, t, ht⟩ := exists_smallEtaleStageLeg_eq_module B Λ Dg c hX hc haff G U
    (moduleShriekConstantSectionEquiv.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ U _ aflat)
  let g := systemStageHom B Dg hij
  let pj := coneStageHom B Dg c hX j
  let e := coneStageHom_comp B Dg c hX hij
  let τ := (moduleShriekConstantSectionEquiv.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ U _).symm t
  let b := ((smallEtaleSheafAdjunction B A g).homEquiv S _).symm τ
  refine ⟨j, hij, b, ?_⟩
  simp only [SmallEtaleStageRealizes, smallEtaleStageComparison_eq]
  apply ((smallEtaleSheafAdjunction B A pi).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have : Mono ((smallEtalePushforwardCompHom B A pj g pi e).app
      ((smallEtaleSheafPullback B A pi).obj G)) :=
    @IsIso.mono_of_iso _ _ _ _ _ (isIso_smallEtalePushforwardCompHom_app B A pj g pi e _)
  rw [← cancel_mono ((smallEtalePushforwardCompHom B A pj g pi e).app
    ((smallEtaleSheafPullback B A pi).obj G)), Category.assoc,
    unit_comp_map_smallEtaleStageRealization B A pj g pi e b]
  have hb : (smallEtaleSheafAdjunction B A g).unit.app S ≫
      (smallEtaleSheafPushforward B A g).map b = τ :=
    ((smallEtaleSheafAdjunction B A g).homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ τ)
  rw [hb]
  apply (moduleShriekConstantSectionEquiv.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ U _).injective
  rwa [moduleShriekConstantSectionEquiv_naturality, moduleShriekConstantSectionEquiv_naturality,
    Equiv.apply_symm_apply]

/-- Inverse image on small étale sheaves of modules preserves colimits, being a left adjoint. -/
private theorem preservesColimitsOfSize_smallEtaleSheafPullback {X Y : B.Scheme} (f : X ⟶ Y) :
    PreservesColimitsOfSize.{0, 0} (smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ) f) :=
  (smallEtaleSheafAdjunction B (ModuleCat.{u + 1} Λ) f).leftAdjoint_preservesColimits

/-- **Fullness for a finite direct sum of generators.** A map on the vertex out of the inverse
image of `⊕_k j_{U_k!}Λ`, for finitely many affine `U_k` over a stage, comes from a later
stage. -/
theorem exists_smallEtaleStage_realization_sigma (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e))) {i : I}
    {n : ℕ} (U : Fin n → SmallEtale B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
    (hU : ∀ k, SmallEtale.IsAffine B _ _ (U k))
    (G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (ModuleCat.{u + 1} Λ))
    (a : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj
        (∐ fun k => moduleShriekConstant.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ (U k)) ⟶
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj G) :
    ∃ (j : I) (h : i ≤ j) (b : _), SmallEtaleStageRealizes B Λ Dg c hX h a b := by
  classical
  let X := fun k => moduleShriekConstant.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ (U k)
  have hk : ∀ k, ∃ (j : I) (h : i ≤ j) (b : _), SmallEtaleStageRealizes B Λ Dg c hX h
      ((smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).map (Sigma.ι X k) ≫ a) b :=
    fun k => by
    have hA : IsAffine ((SmallEtale.toScheme B _ _).obj (U k)) := hU k
    exact exists_smallEtaleStage_realization_moduleShriekConstant B Λ Dg c hX hc haff (U k) G _
  choose jk hik bk hbk using hk
  have : Nonempty I := ⟨i⟩
  obtain ⟨j, hj⟩ := Finset.exists_le (insert i (Finset.univ.image jk))
  have hij : i ≤ j := hj i (Finset.mem_insert_self _ _)
  have hkj : ∀ k, jk k ≤ j := fun k =>
    hj (jk k) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem jk (Finset.mem_univ k)))
  have hk' : ∀ k, ∃ b', SmallEtaleStageRealizes B Λ Dg c hX hij
      ((smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).map (Sigma.ι X k) ≫ a) b' :=
    fun k =>
    smallEtaleStageRealizes_of_le B (ModuleCat.{u + 1} Λ) Dg c hX (hik k) (hkj k) _ (bk k) (hbk k)
  choose b' hb' using hk'
  let T := smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hij
  have := preservesColimitsOfSize_smallEtaleSheafPullback B Λ (systemStageHom B Dg hij)
  have := preservesColimitsOfSize_smallEtaleSheafPullback B Λ (coneStageHom B Dg c hX i)
  let hT := isColimitOfPreserves T (colimit.isColimit (Discrete.functor X))
  let cc : Cocone (Discrete.functor X ⋙ T) :=
    { pt := T.obj G
      ι := Discrete.natTrans fun k => b' k.as }
  refine ⟨j, hij, hT.desc cc, ?_⟩
  refine (isColimitOfPreserves (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i)
    (colimit.isColimit (Discrete.functor X))).hom_ext fun ⟨k⟩ => ?_
  have hfac := hT.fac cc ⟨k⟩
  simp only [Functor.mapCocone_ι_app, colimit.cocone_ι] at hfac ⊢
  rw [← hb' k]
  refine (smallEtaleStageComparison_inv_naturality_assoc B (ModuleCat.{u + 1} Λ) Dg c hX hij
    (Sigma.ι X k) _).trans ?_
  rw [← Functor.map_comp_assoc]
  exact congrArg
    (fun z => _ ≫ (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX j).map z ≫ _) hfac

omit [IsDirected I (· ≤ ·)] in
/-- **Descent of a realization along an epimorphism.** Let `p : P ⟶ F` be an epimorphism at a
stage and `b0` a realization of `p_i⁻¹p ≫ a` at a later stage `j`. If the restriction of `b0` to
the kernel of `p` vanishes at a stage `k ≥ j`, then `a` is realized at `k`. -/
private theorem exists_smallEtaleStage_realization_of_epi {i j k : I} (hij : i ≤ j) (hjk : j ≤ k)
    {P F G : Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj (Dg.obj (op i)).property)
      (ModuleCat.{u + 1} Λ)} (p : P ⟶ F) [Epi p]
    (a : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj F ⟶
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj G)
    (b0 : (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hij).obj P ⟶
      (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hij).obj G)
    (hb0 : SmallEtaleStageRealizes B Λ Dg c hX hij
      ((smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).map p ≫ a) b0)
    (hk : (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hjk).map
      ((smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hij).map (kernel.ι p) ≫ b0) = 0) :
    ∃ b, SmallEtaleStageRealizes B Λ Dg c hX (hij.trans hjk) a b := by
  have : (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg (hij.trans hjk)).Additive :=
    additive_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B _ Λ
  let ψ := smallEtaleSheafPullbackCompIso' B (ModuleCat.{u + 1} Λ) (systemStageHom B Dg hjk)
    (systemStageHom B Dg hij) (systemStageHom B Dg (hij.trans hjk))
    (systemStageHom_comp B Dg hij hjk)
  let b0' := (ψ.app _).inv ≫ (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hjk).map b0 ≫
    (ψ.app G).hom
  have hι : (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg (hij.trans hjk)).map
      (kernel.ι p) ≫ b0' = 0 := by
    have hn := ψ.inv.naturality (kernel.ι p)
    simp only [b0', Iso.app_inv, Iso.app_hom, Functor.comp_map] at hn ⊢
    rw [reassoc_of% hn, ← Functor.map_comp_assoc, hk, zero_comp, comp_zero]
  have := preservesColimitsOfSize_smallEtaleSheafPullback B Λ (systemStageHom B Dg (hij.trans hjk))
  let hcok := isColimitCoforkMapOfIsColimit
    (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg (hij.trans hjk)) _
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel p))
  let b := Cofork.IsColimit.desc hcok b0'
    (by simpa only [Fork.ι_ofι, Functor.map_zero, zero_comp] using hι)
  have hb :
      (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg (hij.trans hjk)).map p ≫ b = b0' :=
    Cofork.IsColimit.π_desc hcok
  refine ⟨b, ?_⟩
  unfold SmallEtaleStageRealizes
  have : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).IsLeftAdjoint :=
    (smallEtaleSheafAdjunction B (ModuleCat.{u + 1} Λ) (coneStageHom B Dg c hX i)).isLeftAdjoint
  rw [← cancel_epi ((smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).map p),
    smallEtaleStageComparison_inv_naturality_assoc, ← Functor.map_comp_assoc, hb]
  exact smallEtaleStageRealizes_trans B (ModuleCat.{u + 1} Λ) Dg c hX hij hjk _ b0 hb0

/-- **Stacks 09YU, clause (3), the fullness assertion.** Let `X = lim X_i` be the limit of a
directed inverse system of quasi-compact and quasi-separated schemes with affine transition
morphisms and let `Λ` be a Noetherian ring. Every map between the inverse images to `X_étale` of
two constructible sheaves of `Λ`-modules on `(X_i)_étale` is the inverse image of a map at some
later stage, read through the canonical comparison of inverse images.

A constructible sheaf is a quotient of a finite direct sum of sheaves `j_{U!}Λ` with `U` affine by
Stacks 095N; the map on the sum comes from a stage by the degree zero case of Stacks 09YQ, its
restriction to the kernel vanishes on `X` and hence, by the faithfulness assertion, at a later
stage, where the map descends to the quotient. -/
@[stacks 09YU "clause (3), the fullness assertion", sga "4 IX 2.7.4" "partial"]
theorem smallEtaleStagesFull_isConstructibleModuleSheaf [IsNoetherianRing Λ] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesFull B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y => IsConstructibleModuleSheaf B Y Λ) := by
  intro i F G hF hG a
  have := hqc i
  have := hqs i
  obtain ⟨n, U, hU, p, hp⟩ :=
    exists_finite_epi_sigma_moduleShriekConstant_affine_of_isConstructibleModuleSheaf B
      (Dg.obj (op i)) Λ F hF
  have hP0 : IsConstructibleModuleSheaf B (Dg.obj (op i)) Λ
      (∐ fun k => moduleShriekConstant.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ (U k)) :=
    isConstructibleModuleSheaf_sigma_moduleShriekConstant.{u, u + 1} B (Dg.obj (op i)) Λ U hU
  let Q : ObjectProperty (Sheaf (SmallEtale.topology B (Dg.obj (op i)).obj
      (Dg.obj (op i)).property) (ModuleCat.{u + 1} Λ)) :=
    fun H => IsConstructibleModuleSheaf B (Dg.obj (op i)) Λ H
  have : Q.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B _ Λ
  have hK : IsConstructibleModuleSheaf B (Dg.obj (op i)) Λ (kernel p) := Q.prop_kernel p hP0 hF
  obtain ⟨j, hij, b0, hb0⟩ := exists_smallEtaleStage_realization_sigma B Λ Dg c hX hc haff U hU G
    ((smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).map p ≫ a)
  have : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).Additive :=
    additive_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B _ Λ
  have : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX j).Additive :=
    additive_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B _ Λ
  have hzero : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX j).map
      ((smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hij).map (kernel.ι p) ≫ b0) =
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX j).map 0 := by
    have hb0' : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX j).map b0 =
        (smallEtaleStageComparison B (ModuleCat.{u + 1} Λ) Dg c hX hij _).hom ≫
          ((smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).map p ≫ a) ≫
          (smallEtaleStageComparison B (ModuleCat.{u + 1} Λ) Dg c hX hij G).inv := by
      rw [← hb0]
      simp
    rw [Functor.map_comp, hb0', smallEtaleStageComparison_hom_naturality_assoc]
    simp only [Category.assoc]
    rw [← Functor.map_comp_assoc, kernel.condition, Functor.map_zero, zero_comp, comp_zero,
      Functor.map_zero]
  obtain ⟨k, hjk, hk⟩ := smallEtaleStagesFaithful_isConstructibleModuleSheaf B Λ Dg c hX hc haff hqc
    hqs j _ _ (isConstructibleModuleSheaf_pullback B Λ _ _ hK)
    (isConstructibleModuleSheaf_pullback B Λ _ _ hG) _ _ hzero
  have : (smallEtaleStageTransition B (ModuleCat.{u + 1} Λ) Dg hjk).Additive :=
    additive_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B _ Λ
  exact ⟨k, hij.trans hjk, exists_smallEtaleStage_realization_of_epi B Λ Dg c hX hij hjk p a b0 hb0
    (hk.trans (Functor.map_zero _ _ _))⟩

end AlgebraicGeometry
