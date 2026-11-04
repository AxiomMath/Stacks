module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.StageAdjoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.SeparablyClosedNormalCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.GenericPointLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Complete

/-!
# A map out of a finitely presented sheaf which is injective at a point of a finite cover

Let `X` be a quasi-compact and quasi-separated scheme, `Λ` a ring and `ℱ` a sheaf of `Λ`-modules
on `X_étale` which is the cokernel of a map between finite direct sums of the sheaves `j_! Λ` at
affine étale `X`-schemes, and whose inverse images to spectra of separably closed fields have
finite global sections. For every point `x ∈ X` this file produces a finite morphism of finite
presentation `f : Y ⟶ X`, a finite `Λ`-module `M`, a map `ψ : f^{-1} ℱ ⟶ 𝓛_Y(M)` into the sheaf of
locally constant `M`-valued maps, and a morphism `t : Spec Ω ⟶ Y` from the spectrum of a separably
closed field, lying over `x`, along which the kernel of `ψ` pulls back to zero.

This is the main step of the proof of Stacks 09Z6. The construction is the source's. Let
`π : Ỹ ⟶ X` be integral, with `Ỹ` integral and normal with separably closed function field `Ω`,
whose generic point lies over `x`, and let `g : Spec Ω ⟶ Ỹ` be the generic point. On `Spec Ω` the
sheaf `g^{-1}π^{-1}ℱ` is constant on its module of global sections `M`, which is finite; adjunction
gives `π^{-1}ℱ ⟶ g_* 𝓛(M) = 𝓛_Ỹ(M)` (Stacks 09Z5), and adjunction again `ℱ ⟶ π_* 𝓛_Ỹ(M)`. Writing
`Ỹ` as the limit of finite morphisms of finite presentation `Y_i ⟶ X` (Stacks 09YZ), this map
factors through `f_{i,*} 𝓛_{Y_i}(M)`
(`Stacks.EtaleCohomology.IntegralLimitPresentation.exists_comp_stageMap_eq`); its adjoint `ψ`
pulled back along `c : Ỹ ⟶ Y_i` and then along `g` is, up to isomorphisms, a monomorphism
(`Stacks.EtaleCohomology.locallyConstantPushforwardMap_eq` and
`CategoryTheory.Adjunction.homEquiv_symm_comp_map_comp_hom_app`). So `t = g ≫ c` kills the kernel.

Unlike the source, the conclusion records the *component* of the embedding at one point of the
finite cover, `ψ` on `Y`, rather than the map `ℱ ⟶ f_* 𝓛_Y(M)` on `X`: this is what the finite
selection of `AlgebraicGeometry.exists_mono_biproduct_lift_of_forall_isZero_etaleStalk_kernel`
consumes, over a base which need not be Noetherian.

## Main results

* `Stacks.EtaleCohomology.exists_stage_pointEmbedding` — the construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] AlgebraicGeometry.IntegralLimitPresentation.indexPreorder
  AlgebraicGeometry.IntegralLimitPresentation.indexNonempty
  AlgebraicGeometry.IntegralLimitPresentation.indexDirected
  etaleModuleInverseImage_preservesFiniteLimits

/-- The left adjoint sends the adjoint of a monomorphism `L X ⟶ Y` to a monomorphism. -/
lemma _root_.CategoryTheory.Adjunction.mono_map_homEquiv {C D : Type*} [Category C]
    [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {X : C} {Y : D} (f : L.obj X ⟶ Y)
    [Mono f] : Mono (L.map (adj.homEquiv _ _ f)) := by
  have : Mono (L.map (adj.homEquiv _ _ f) ≫ adj.counit.app Y) := by
    rwa [← adj.homEquiv_counit (g := adj.homEquiv _ _ f), Equiv.symm_apply_apply]
  exact mono_of_mono _ (adj.counit.app Y)

/-- A functor sending `ψ` and `kernel.ι ψ` to monomorphisms kills the kernel of `ψ`. -/
lemma _root_.CategoryTheory.Functor.isZero_obj_kernel_of_mono_map {C D : Type*} [Category C]
    [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D] (T : C ⥤ D)
    [T.PreservesZeroMorphisms] {A B : C} (ψ : A ⟶ B) [HasKernel ψ] [Mono (T.map (kernel.ι ψ))]
    [Mono (T.map ψ)] : IsZero (T.obj (kernel ψ)) :=
  IsZero.of_mono_eq_zero (T.map (kernel.ι ψ)) <| by
    rw [← cancel_mono (T.map ψ), ← T.map_comp, kernel.condition, T.map_zero, zero_comp]

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- On an integral normal scheme `Y` with separably closed function field, every sheaf `G` of
`Λ`-modules maps to `𝓛_Y(M)`, for `M` the global sections of the pullback of `G` to the generic
point, by a map which is a monomorphism after pullback to the generic point. -/
private theorem exists_mono_inverseImage_genericPointInclusion (Y : Scheme.{u}) [IsIntegral Y]
    [IsNormal Y] [IsSepClosed Y.functionField] (G : EtaleModules.{u, u + 1} Λ Y) :
    ∃ ψ : G ⟶ smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ Y
        ((etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Y.functionField))).obj
          ((etaleModuleInverseImage.{u, u + 1} Λ (genericPointInclusion Y)).obj G)),
      Mono ((etaleModuleInverseImage.{u, u + 1} Λ (genericPointInclusion Y)).map ψ) := by
  let Ω : Type u := Y.functionField
  let g : Spec (.of Ω) ⟶ Y := genericPointInclusion Y
  let G' := (etaleModuleInverseImage.{u, u + 1} Λ g).obj G
  let M := (etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))).obj G'
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  let α : (constantSheaf _ (ModuleCat.{u + 1} Λ)).obj M ≅ G' :=
    asIso ((constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)).counit.app G')
  let β : smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ (Spec (.of Ω)) M ≅ G' :=
    (smallEtaleConstantSheafIsoLocallyConstantMapsModule.{u, u + 1} Λ _ M).symm ≪≫ α
  let Ag := etaleModuleInverseImageAdj.{u, u + 1} Λ g
  let θ := locallyConstantToDirectImage.{u, u + 1} Λ M g
  have : IsIso θ := isIso_locallyConstantToDirectImage_genericPointInclusion Λ M Y
  have : Mono ((etaleModuleInverseImage.{u, u + 1} Λ g).map (Ag.homEquiv _ _ β.inv)) :=
    Ag.mono_map_homEquiv β.inv
  refine ⟨Ag.homEquiv _ _ β.inv ≫ inv θ, ?_⟩
  rw [Functor.map_comp]
  infer_instance

/-- **The main step of Stacks 09Z6, over a quasi-compact quasi-separated base.** Let `ℱ` be a
finitely presented sheaf of `Λ`-modules on `X_étale` (a quotient `p` of finitely many `j_! Λ` at
affine étale `X`-schemes whose kernel is a quotient `q` of such a sum) whose inverse images to
spectra of separably closed fields have finite global sections. For every `x ∈ X` there are a
finite morphism of finite presentation `f : Y ⟶ X`, a finite `Λ`-module `M`, a map
`ψ : f^{-1} ℱ ⟶ 𝓛_Y(M)` and a morphism `t : Spec Ω ⟶ Y` from the spectrum of a separably closed
field, lying over `x`, with `t^{-1} (ker ψ) = 0`. -/
theorem exists_stage_pointEmbedding {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : EtaleModules.{u, u + 1} Λ X) {n : ℕ}
    {Wd : Fin n → Scheme.{u}} (e : ∀ k, Wd k ⟶ X) [∀ k, Etale (e k)] [∀ k, IsAffine (Wd k)]
    (p : (∐ fun k => extensionByZeroConstant Λ (e k)) ⟶ F) [Epi p] {m : ℕ}
    {Wd' : Fin m → Scheme.{u}} (e' : ∀ l, Wd' l ⟶ X) [∀ l, Etale (e' l)]
    [∀ l, IsAffine (Wd' l)] (q : (∐ fun l => extensionByZeroConstant Λ (e' l)) ⟶ kernel p)
    [Epi q]
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      Module.Finite Λ ((etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))).obj
        ((etaleModuleInverseImage.{u, u + 1} Λ s).obj F)))
    (x : X) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : IsFinite f) (_ : FinitePresentation f)
      (M : ModuleCat.{u + 1} Λ) (_ : Module.Finite Λ M)
      (ψ : (etaleModuleInverseImage.{u, u + 1} Λ f).obj F ⟶
        smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ Y M)
      (Ω : Type u) (_ : Field Ω) (_ : IsSepClosed Ω) (t : Spec (.of Ω) ⟶ Y),
      (∀ y, f (t y) = x) ∧ IsZero ((etaleModuleInverseImage.{u, u + 1} Λ t).obj (kernel ψ)) := by
  obtain ⟨Y', hY', π, hπ, hN, hS, hx, -⟩ :=
    exists_isIntegralHom_isNormal_isSepClosed_functionField x
  let Ω : Type u := Y'.functionField
  let g : Spec (.of Ω) ⟶ Y' := genericPointInclusion Y'
  let G := (etaleModuleInverseImage.{u, u + 1} Λ g).obj
    ((etaleModuleInverseImage.{u, u + 1} Λ π).obj F)
  let M := (etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))).obj G
  have := hfin Ω (g ≫ π)
  have hM : Module.Finite Λ M :=
    .equiv ((etaleModuleGlobalSections.{u, u + 1} Λ (Spec (.of Ω))).mapIso
      ((etaleModuleInverseImageCompIso.{u, u + 1} Λ g π).app F)).toLinearEquiv
  obtain ⟨ψt, hmonot⟩ : ∃ ψt : (etaleModuleInverseImage.{u, u + 1} Λ π).obj F ⟶
      smallEtaleLocallyConstantMapsModuleSheaf.{u, u + 1} Λ Y' M,
      Mono ((etaleModuleInverseImage.{u, u + 1} Λ g).map ψt) :=
    exists_mono_inverseImage_genericPointInclusion Λ Y' _
  let Aπ := etaleModuleInverseImageAdj.{u, u + 1} Λ π
  let φ' := Aπ.homEquiv _ _ ψt
  let P := (Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation π).some
  obtain ⟨i, φ, hφ⟩ := IntegralLimitPresentation.exists_comp_stageMap_eq Λ M P e p e' q φ'
  let c : Y' ⟶ P.diagram.obj i := P.limitCone.app i
  let si := IntegralLimitPresentation.stage P i
  have hcs : c ≫ si = π := (P.compatible i).symm
  let Af := etaleModuleInverseImageAdj.{u, u + 1} Λ si
  let Ac := etaleModuleInverseImageAdj.{u, u + 1} Λ c
  let κ := etaleModuleDirectImageComp.{u, u + 1} Λ c si π hcs.symm
  let ψ := (Af.homEquiv _ _).symm φ
  -- the adjoint of `φ'` along `π` through the stage
  have hψt : ψt = (Aπ.leftAdjointUniq ((Af.comp Ac).ofNatIsoRight κ)).hom.app F ≫
      (etaleModuleInverseImage.{u, u + 1} Λ c).map ψ ≫
        (Ac.homEquiv _ _).symm (locallyConstantToDirectImage.{u, u + 1} Λ M c) := by
    rw [show ψt = (Aπ.homEquiv _ _).symm φ' by simp [φ'], ← hφ, IntegralLimitPresentation.stageMap,
      locallyConstantPushforwardMap_eq, Adjunction.homEquiv_symm_comp_map_comp_hom_app]
  -- after inverse image along `g`, that adjoint is a monomorphism
  let Tg := etaleModuleInverseImage.{u, u + 1} Λ g
  let Tc := etaleModuleInverseImage.{u, u + 1} Λ c
  have hmonoψ : Mono ((Tc ⋙ Tg).map ψ) := by
    rw [hψt, Functor.map_comp, Functor.map_comp, mono_comp_iff_of_isIso] at hmonot
    exact mono_of_mono (Tg.map (Tc.map ψ))
      (Tg.map ((Ac.homEquiv _ _).symm (locallyConstantToDirectImage.{u, u + 1} Λ M c)))
  refine ⟨P.diagram.obj i, si, P.stageFinite i, P.stageFinitePresentation i, M, hM, ψ, Ω,
    inferInstance, hS, g ≫ c, fun y => ?_, ?_⟩
  · have : Subsingleton ↥(Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    rw [← Scheme.Hom.comp_apply, Category.assoc, hcs, Scheme.Hom.comp_apply,
      Subsingleton.elim y (IsLocalRing.closedPoint Y'.functionField),
      genericPointInclusion_closedPoint, hx]
  · exact IsZero.of_iso ((Tc ⋙ Tg).isZero_obj_kernel_of_mono_map ψ)
      ((etaleModuleInverseImageCompIso.{u, u + 1} Λ g c).app (kernel ψ))

end Stacks.EtaleCohomology

end
