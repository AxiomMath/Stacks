module

public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.QuasiSeparatedSourceChange
public import
  StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.KernelOfFunctor
public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.PullbackCover
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.PullbackChartRefine

/-!
# Kernels are determined by their integral transforms

Let `R` be a ring and let `X` and `Y` be schemes over `R` with `X` quasi-compact and with affine
diagonal.  This file proves that sending a quasi-coherent kernel `K` on `X ×_R Y` to its integral
transform `F_K = pr_{2,*}(pr_1^*(-) ⊗ K)` is a **fully faithful** functor
`QCoh(𝒪_{X ×_R Y}) ⥤ (QCoh(𝒪_X) ⥤ QCoh(𝒪_Y))`.  For `X` affine this is part of Tag 0FZD
(`AlgebraicGeometry.full_integralTransformQcohFunctorLift` and
`AlgebraicGeometry.faithful_integralTransformQcohFunctorLift`).

## Main definitions

* `AlgebraicGeometry.chartKernelHom`: for `f : X' ⟶ X` over `R` with `X'` affine, the morphism of
  inverse images of kernels along `f × id_Y` induced by a natural transformation of integral
  transforms.

## Main results

* `AlgebraicGeometry.faithful_integralTransformQcohFunctor`: `K ↦ F_K` is faithful.
* `AlgebraicGeometry.full_integralTransformQcohFunctor`: `K ↦ F_K` is full.

## References

* [Stacks Project, Tag 0FZH](https://stacks.math.columbia.edu/tag/0FZH)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0FZF](https://stacks.math.columbia.edu/tag/0FZF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **On an affine source the integral transform is fully faithful in the kernel** (Tag 0FZD). -/
def fullyFaithfulIntegralTransformQcohFunctorOfIsAffine (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left] :
    (integralTransformQcohFunctor R X Y).FullyFaithful :=
  haveI := full_integralTransformQcohFunctorLift R X Y
  haveI := faithful_integralTransformQcohFunctorLift R X Y
  { preimage := fun φ => (Functor.FullyFaithful.ofFullyFaithful
        (integralTransformQcohFunctorLift R X Y)).preimage (ObjectProperty.homMk φ)
    map_preimage := fun φ => congrArg (fun t => t.hom) ((Functor.FullyFaithful.ofFullyFaithful
        (integralTransformQcohFunctorLift R X Y)).map_preimage (ObjectProperty.homMk φ))
    preimage_map := fun f => (Functor.FullyFaithful.ofFullyFaithful
        (integralTransformQcohFunctorLift R X Y)).preimage_map f }

/-- **Restricting a morphism of inverse images along a composite** is restricting twice. -/
theorem ModuleHomGlue.pullbackRestrictAlong_comp {T Z Z' Z'' : Scheme.{u}} {M N : T.Modules}
    {g : Z ⟶ T} {g' : Z' ⟶ T} {g'' : Z'' ⟶ T} (a : Z'' ⟶ Z') (b : Z' ⟶ Z) (hb : b ≫ g = g')
    (ha : a ≫ g' = g'') (hab : (a ≫ b) ≫ g = g'')
    (ψ : (Scheme.Modules.pullback g).obj M ⟶ (Scheme.Modules.pullback g).obj N) :
    Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong (a ≫ b) hab ψ =
      Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong a ha
        (Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong b hb ψ) := by
  subst hb ha
  obtain rfl : hab = Category.assoc a b g := rfl
  have kM := Scheme.Modules.pullbackComp_assoc_inv_app a b g M
  have kN := Scheme.Modules.pullbackComp_assoc_inv_app a b g N
  have kN' : (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback g).obj N) ≫
      (Scheme.Modules.pullbackComp (a ≫ b) g).hom.app N ≫
      (Scheme.Modules.pullbackCongr (Category.assoc a b g)).hom.app N =
      (Scheme.Modules.pullback a).map ((Scheme.Modules.pullbackComp b g).hom.app N) ≫
        (Scheme.Modules.pullbackComp a (b ≫ g)).hom.app N := by
    haveI : Epi ((Scheme.Modules.pullbackCongr (Category.assoc a b g)).inv.app N ≫
        (Scheme.Modules.pullbackComp (a ≫ b) g).inv.app N ≫
        (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback g).obj N)) :=
      inferInstanceAs (Epi (((Scheme.Modules.pullbackCongr (Category.assoc a b g)).app N).symm ≪≫
        ((Scheme.Modules.pullbackComp (a ≫ b) g).app N).symm ≪≫
        ((Scheme.Modules.pullbackComp a b).app ((Scheme.Modules.pullback g).obj N)).symm).hom)
    rw [← cancel_epi ((Scheme.Modules.pullbackCongr (Category.assoc a b g)).inv.app N ≫
      (Scheme.Modules.pullbackComp (a ≫ b) g).inv.app N ≫
      (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback g).obj N))]
    conv_rhs => rw [kN]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  have nat := (Scheme.Modules.pullbackComp a b).inv.naturality ψ
  simp only [Functor.comp_map] at nat
  have e : (Scheme.Modules.pullback (a ≫ b)).map ψ =
      (Scheme.Modules.pullbackComp a b).inv.app _ ≫
        (Scheme.Modules.pullback a).map ((Scheme.Modules.pullback b).map ψ) ≫
        (Scheme.Modules.pullbackComp a b).hom.app _ := by
    rw [← reassoc_of% nat, Iso.inv_hom_id_app, Category.comp_id]
  have r1 : Scheme.Modules.pullbackCongr (rfl : b ≫ g = b ≫ g) = Iso.refl _ := rfl
  have r2 : Scheme.Modules.pullbackCongr (rfl : a ≫ b ≫ g = a ≫ b ≫ g) = Iso.refl _ := rfl
  simp only [Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong, e, r1, r2,
    CategoryTheory.Functor.map_comp, Category.assoc, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id, kN']
  simp only [← Category.assoc]
  congr 3

/-- Given a functor `G : D ⥤ C`, isomorphisms `eK : Ak ≅ G.obj Bk` and `eL : Al ≅ G.obj Bl`
factored as in `hK` and `hL`, and the commutations `hn`, `hχ`, `h1` and `hφ`, the conjugate
`eK.inv ≫ φ'' ≫ eL.hom` of `φ''` is `G.map (cK.hom ≫ S ≫ cL.inv)`. -/
theorem chartKernelHom_comp_source_chase {C D : Type*} [Category C] [Category D] (G : D ⥤ C)
    {Ak Al Mk Ml Nk Nl : C} {Bk Bl Pk Pl : D} (eK : Ak ≅ G.obj Bk) (eL : Al ≅ G.obj Bl)
    (φ'' : Ak ⟶ Al) (wK : Ak ⟶ Mk) (gK1 : Mk ⟶ Nk) (gK2 : Nk ⟶ G.obj Pk) (cK : Bk ≅ Pk)
    (wL : Al ⟶ Ml) (gL1 : Ml ⟶ Nl) (gL2 : Nl ⟶ G.obj Pl) (cL : Bl ≅ Pl) (S : Pk ⟶ Pl)
    (gχ : Nk ⟶ Nl) (gK1i : Nk ⟶ Mk) (gφ : Mk ⟶ Ml)
    (hK : eK.hom = wK ≫ gK1 ≫ gK2 ≫ G.map cK.inv) (hL : eL.hom = wL ≫ gL1 ≫ gL2 ≫ G.map cL.inv)
    (hn : gK2 ≫ G.map S = gχ ≫ gL2) (hχ : gχ = gK1i ≫ gφ ≫ gL1)
    (h1 : gK1 ≫ gK1i = 𝟙 _) (hφ : φ'' ≫ wL = wK ≫ gφ) :
    eK.inv ≫ φ'' ≫ eL.hom = G.map (cK.hom ≫ S ≫ cL.inv) := by
  rw [Iso.inv_comp_eq, hK, hL, G.map_comp, G.map_comp]
  simp only [Category.assoc]
  rw [← G.map_comp_assoc cK.inv cK.hom, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% hn, hχ]
  simp only [Category.assoc, reassoc_of% h1, reassoc_of% hφ]

section Chart

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]

attribute [local instance] isAffineHom_left_of_isAffine_left

variable {X' : Over (Spec (.of R))} [IsAffine X'.left] (f : X' ⟶ X)
  {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)}

/-- **The morphism of inverse images of kernels induced by a natural transformation of integral
transforms.**  For `f : X' ⟶ X` over `R` with `X'` affine, a natural transformation
`φ : F_K ⟶ F_L` gives `F_K ∘ f_* ⟶ F_L ∘ f_*`, which change of source reads as a natural
transformation between the integral transforms of `(f × id_Y)^*K` and `(f × id_Y)^*L` on the
affine `X'`; by Tag 0FZD it is induced by exactly one morphism of kernels, which is this one. -/
def chartKernelHom
    (φ : quasicoherentIntegralTransform R X Y K ⟶ quasicoherentIntegralTransform R X Y L) :
    sourceChangeKernel R X X' Y f K ⟶ sourceChangeKernel R X X' Y f L :=
  (fullyFaithfulIntegralTransformQcohFunctorOfIsAffine R X' Y).preimage
    ((quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f K).inv ≫
      Functor.whiskerLeft (quasicoherentPushforward f.left) φ ≫
      (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f L).hom)

/-- The integral transform of `AlgebraicGeometry.chartKernelHom` is the transformation it was
built from, read through change of source. -/
theorem map_chartKernelHom
    (φ : quasicoherentIntegralTransform R X Y K ⟶ quasicoherentIntegralTransform R X Y L) :
    (integralTransformQcohFunctor R X' Y).map (chartKernelHom R X Y f φ) =
      (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f K).inv ≫
        Functor.whiskerLeft (quasicoherentPushforward f.left) φ ≫
        (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f L).hom :=
  (fullyFaithfulIntegralTransformQcohFunctorOfIsAffine R X' Y).map_preimage _

/-- **On the transform of a morphism of kernels, `AlgebraicGeometry.chartKernelHom` is its
inverse image**. -/
theorem chartKernelHom_map (ψ : K ⟶ L) :
    chartKernelHom R X Y f ((integralTransformQcohFunctor R X Y).map ψ) =
      (sourceChangeKernelFunctor R X X' Y f).map ψ := by
  have h : (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f K).inv ≫
      Functor.whiskerLeft (quasicoherentPushforward f.left)
        ((integralTransformQcohFunctor R X Y).map ψ) ≫
      (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f L).hom =
      (integralTransformQcohFunctor R X' Y).map ((sourceChangeKernelFunctor R X X' Y f).map ψ) :=
    (Iso.inv_comp_eq _).mpr
      (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_naturality R X X' Y f K ψ)
  exact (congrArg (fullyFaithfulIntegralTransformQcohFunctorOfIsAffine R X' Y).preimage h).trans
    ((fullyFaithfulIntegralTransformQcohFunctorOfIsAffine R X' Y).preimage_map _)

/-- **`AlgebraicGeometry.chartKernelHom` is compatible with a further change of source**:  along
a composite `X'' ⟶ X' ⟶ X` of morphisms with affine sources it is the inverse image of the one
along `X' ⟶ X`, up to the identification of the two iterated inverse images. -/
theorem chartKernelHom_comp_source {X'' : Over (Spec (.of R))} [IsAffine X''.left] (g : X'' ⟶ X')
    (φ : quasicoherentIntegralTransform R X Y K ⟶ quasicoherentIntegralTransform R X Y L) :
    chartKernelHom R X Y (g ≫ f) φ =
      (sourceChangeKernelCompIso R X X' X'' Y f g K).hom ≫
        (sourceChangeKernelFunctor R X' X'' Y g).map (chartKernelHom R X Y f φ) ≫
        (sourceChangeKernelCompIso R X X' X'' Y f g L).inv := by
  have hK := quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_comp R X X' X'' Y f g K
  have hL := quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_comp R X X' X'' Y f g L
  have hn : (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X' X'' Y g
      (sourceChangeKernel R X X' Y f K)).hom ≫ (integralTransformQcohFunctor R X'' Y).map
        ((sourceChangeKernelFunctor R X' X'' Y g).map (chartKernelHom R X Y f φ)) =
      Functor.whiskerLeft (quasicoherentPushforward g.left)
        ((quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f K).inv ≫
          Functor.whiskerLeft (quasicoherentPushforward f.left) φ ≫
          (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f L).hom) ≫
        (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X' X'' Y g
          (sourceChangeKernel R X X' Y f L)).hom := by
    rw [← map_chartKernelHom]
    exact (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_naturality R X' X''
      Y g (sourceChangeKernel R X X' Y f K) (chartKernelHom R X Y f φ)).symm
  have hφ : Functor.whiskerLeft (quasicoherentPushforward (g ≫ f).left) φ ≫
      Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g rfl)).hom
        (quasicoherentIntegralTransform R X Y L) ≫
      ((quasicoherentPushforward g.left).associator (quasicoherentPushforward f.left)
        (quasicoherentIntegralTransform R X Y L)).hom =
      (Functor.whiskerRight (eqToIso (quasicoherentPushforward_eq_comp f g rfl)).hom
          (quasicoherentIntegralTransform R X Y K) ≫
        ((quasicoherentPushforward g.left).associator (quasicoherentPushforward f.left)
          (quasicoherentIntegralTransform R X Y K)).hom) ≫
        Functor.whiskerLeft (quasicoherentPushforward g.left)
          (Functor.whiskerLeft (quasicoherentPushforward f.left) φ) := by
    refine NatTrans.ext (funext fun M => ?_)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id, Category.assoc]
    exact (φ.naturality ((eqToIso (quasicoherentPushforward_eq_comp f g rfl)).hom.app M)).symm
  refine (fullyFaithfulIntegralTransformQcohFunctorOfIsAffine R X'' Y).map_injective ?_
  rw [map_chartKernelHom]
  exact chartKernelHom_comp_source_chase (integralTransformQcohFunctor R X'' Y) _ _ _ _ _ _
    (sourceChangeKernelCompIso R X X' X'' Y f g K) _ _ _
    (sourceChangeKernelCompIso R X X' X'' Y f g L) _ _ _ _
    (hK.trans (Category.assoc _ _ _).symm) (hL.trans (Category.assoc _ _ _).symm) hn
    (Functor.whiskerLeft_comp _ _ _ |>.trans (congrArg (_ ≫ ·) (Functor.whiskerLeft_comp _ _ _)))
    ((Functor.isoWhiskerLeft (quasicoherentPushforward g.left)
      (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X X' Y f K)).hom_inv_id) hφ

/-- **`AlgebraicGeometry.chartKernelHom`, restricted along a change of source**, is
`AlgebraicGeometry.chartKernelHom` along the composite, read as morphisms of inverse images of
sheaves of modules. -/
theorem pullbackRestrictAlong_chartKernelHom {X'' : Over (Spec (.of R))} [IsAffine X''.left]
    (g : X'' ⟶ X') (f'' : X'' ⟶ X) (hf : g ≫ f = f'')
    (hk : sourceChangeMap R X' X'' Y g ≫ sourceChangeMap R X X' Y f = sourceChangeMap R X X'' Y f'')
    (φ : quasicoherentIntegralTransform R X Y K ⟶ quasicoherentIntegralTransform R X Y L) :
    Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong (sourceChangeMap R X' X'' Y g)
        hk (chartKernelHom R X Y f φ).hom =
      (chartKernelHom R X Y f'' φ).hom := by
  subst hf
  rw [chartKernelHom_comp_source]
  rfl

end Chart

/-! ### Full faithfulness -/

section FullyFaithful

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))]

attribute [local instance] isAffineHom_left_of_isAffine_left isAffineHom_ι_affineOpens
  isAffineHom_ι_affineOpens_inf

omit [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))] in
/-- The charts `U ×_R Y` of the affine opens `U` of `X` cover `X ×_R Y`. -/
theorem iSup_image_top_baseChangeOpenTargetMap :
    ⨆ U : X.left.affineOpens, baseChangeOpenTargetMap R X Y (U : X.left.Opens) ''ᵁ ⊤ = ⊤ := by
  simp only [Scheme.Hom.image_top_eq_opensRange]
  exact iSup_opensRange_baseChangeOpenTargetMap R X Y

/-- `AlgebraicGeometry.chartKernelHom` at the chart of an affine open, as a morphism of inverse
images of sheaves of modules. -/
def affineChartHom {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)}
    (φ : quasicoherentIntegralTransform R X Y K ⟶ quasicoherentIntegralTransform R X Y L)
    (U : X.left.affineOpens) :
    (Scheme.Modules.pullback (baseChangeOpenTargetMap R X Y (U : X.left.Opens))).obj K.obj ⟶
      (Scheme.Modules.pullback (baseChangeOpenTargetMap R X Y (U : X.left.Opens))).obj L.obj :=
  haveI : IsAffine (openSubOver R X (U : X.left.Opens)).left := U.2
  (chartKernelHom R X Y (openSubOverHom R X (U : X.left.Opens)) φ).hom

/-- **The morphisms at the charts agree on the overlaps.** -/
theorem affineChartHom_compatible {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)}
    (φ : quasicoherentIntegralTransform R X Y K ⟶ quasicoherentIntegralTransform R X Y L)
    (U₁ U₂ : X.left.affineOpens) (W : (pullback X.hom Y.hom).Opens)
    (k₁ : W.toScheme ⟶ pullback (openSubOver R X (U₁ : X.left.Opens)).hom Y.hom)
    (k₂ : W.toScheme ⟶ pullback (openSubOver R X (U₂ : X.left.Opens)).hom Y.hom)
    (h₁ : k₁ ≫ baseChangeOpenTargetMap R X Y (U₁ : X.left.Opens) = W.ι)
    (h₂ : k₂ ≫ baseChangeOpenTargetMap R X Y (U₂ : X.left.Opens) = W.ι) :
    Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong k₁ h₁ (affineChartHom R X Y φ U₁) =
      Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong k₂ h₂
        (affineChartHom R X Y φ U₂) := by
  have hU : IsAffineOpen ((U₁ : X.left.Opens) ⊓ U₂) := U₁.2.inf U₂.2
  have : IsAffine (openSubOver R X ((U₁ : X.left.Opens) ⊓ U₂)).left := hU
  have hW {V : X.left.Opens} (k : W.toScheme ⟶ pullback (openSubOver R X V).hom Y.hom)
      (hk : k ≫ baseChangeOpenTargetMap R X Y V = W.ι) :
      W ≤ (baseChangeOpenTargetMap R X Y V).opensRange := by
    intro x hx
    obtain ⟨y, rfl⟩ : x ∈ Set.range W.ι.base := by
      rwa [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι]
    rw [← hk]
    exact ⟨k.base y, rfl⟩
  have hr : Set.range W.ι.base ⊆
      Set.range (baseChangeOpenTargetMap R X Y ((U₁ : X.left.Opens) ⊓ U₂)).base := by
    rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι,
      ← opensRange_baseChangeOpenTargetMap_inf]
    exact le_inf (hW k₁ h₁) (hW k₂ h₂)
  let k := IsOpenImmersion.lift (baseChangeOpenTargetMap R X Y ((U₁ : X.left.Opens) ⊓ U₂)) W.ι hr
  have hk : k ≫ baseChangeOpenTargetMap R X Y ((U₁ : X.left.Opens) ⊓ U₂) = W.ι :=
    IsOpenImmersion.lift_fac _ _ _
  have key : ∀ (U : X.left.affineOpens) (le : (U₁ : X.left.Opens) ⊓ U₂ ≤ U)
      (k' : W.toScheme ⟶ pullback (openSubOver R X (U : X.left.Opens)).hom Y.hom)
      (h : k' ≫ baseChangeOpenTargetMap R X Y (U : X.left.Opens) = W.ι),
      Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong k' h (affineChartHom R X Y φ U) =
        Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong k hk
          (chartKernelHom R X Y (openSubOverHom R X ((U₁ : X.left.Opens) ⊓ U₂)) φ).hom := by
    intro U le k' h
    have : IsAffine (openSubOver R X (U : X.left.Opens)).left := U.2
    have hc := openSubChartMap_comp R X Y le
    obtain rfl : k' = k ≫ openSubChartMap R X Y le := by
      rw [← cancel_mono (baseChangeOpenTargetMap R X Y (U : X.left.Opens)), h, Category.assoc, hc,
        hk]
    exact (ModuleHomGlue.pullbackRestrictAlong_comp k _ hc hk h _).trans
      (congrArg _ (pullbackRestrictAlong_chartKernelHom R X Y
        (openSubOverHom R X (U : X.left.Opens)) (openSubInclusionOver R X le) _
        (openSubInclusionOver_comp R X _) hc φ))
  exact (key U₁ inf_le_left k₁ h₁).trans (key U₂ inf_le_right k₂ h₂).symm

omit [CompactSpace X.left] [IsAffineHom (pullback.diagonal (terminal.from X.left))] in
/-- **A morphism of kernels is determined by its inverse images on the charts of the affine
opens.** -/
theorem hom_ext_of_pullback_baseChangeOpenTargetMap
    {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)} {a b : K ⟶ L}
    (h : ∀ U : X.left.affineOpens,
      (Scheme.Modules.pullback (baseChangeOpenTargetMap R X Y (U : X.left.Opens))).map a.hom =
        (Scheme.Modules.pullback (baseChangeOpenTargetMap R X Y (U : X.left.Opens))).map b.hom) :
    a = b :=
  ObjectProperty.hom_ext _
    ((Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_openImmersion_cover
      (fun U : X.left.affineOpens => baseChangeOpenTargetMap R X Y (U : X.left.Opens))
      (iSup_image_top_baseChangeOpenTargetMap R X Y)
      (fun U => (Scheme.Modules.pullback
        (baseChangeOpenTargetMap R X Y (U : X.left.Opens))).map a.hom)
      (fun _ _ _ _ _ h₁ h₂ =>
        (Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong_pullback_map _ _ h₁).trans
          (Stacks.AlgebraicGeometry.ModuleHomGlue.pullbackRestrictAlong_pullback_map _ _
            h₂).symm)).unique
      (fun _ => rfl) (fun U => (h U).symm))

/-- **Morphisms into `F_K(G)` are determined by their composites with the legs at the affine
opens of `X`**. -/
theorem quasicoherentIntegralTransform_hom_ext
    (K : Scheme.QuasicoherentModules (pullback X.hom Y.hom))
    (G : Scheme.QuasicoherentModules X.left) {T : Scheme.QuasicoherentModules Y.left}
    {a b : T ⟶ (quasicoherentIntegralTransform R X Y K).obj G}
    (h : ∀ i : X.left.affineOpens,
      a ≫ (quasicoherentIntegralTransform R X Y K).map ((cechUnit (i : X.left.Opens)).app G) =
        b ≫ (quasicoherentIntegralTransform R X Y K).map ((cechUnit (i : X.left.Opens)).app G)) :
    a = b := by
  refine (isLimitIntegralTransformCechMultifork R X Y K
    (Subtype.val : X.left.affineOpens → X.left.Opens) (iSup_affineOpens_eq_top X.left) G).hom_ext
    ?_
  rintro (i | p)
  · exact h i
  · exact comp_eq_comp_of_comp_eq_comp (h p.1)
      (((quasicoherentIntegralTransform R X Y K).mapCone
        (cechMultifork (Subtype.val : X.left.affineOpens → X.left.Opens) G)).w
          (multicospanFst p))

/-- **Natural transformations of integral transforms are determined by their restrictions to
direct images from the affine opens of `X`.** -/
theorem integralTransform_natTrans_ext {K L : Scheme.QuasicoherentModules (pullback X.hom Y.hom)}
    {φ φ' : quasicoherentIntegralTransform R X Y K ⟶ quasicoherentIntegralTransform R X Y L}
    (h : ∀ U : X.left.affineOpens,
      Functor.whiskerLeft (quasicoherentPushforward (U : X.left.Opens).ι) φ =
        Functor.whiskerLeft (quasicoherentPushforward (U : X.left.Opens).ι) φ') :
    φ = φ' := by
  refine NatTrans.ext (funext fun G => ?_)
  refine quasicoherentIntegralTransform_hom_ext R X Y L G fun i => ?_
  have e := NatTrans.congr_app (h i) ((qcohRestrict (i : X.left.Opens).ι).obj G)
  rw [Functor.whiskerLeft_app, Functor.whiskerLeft_app] at e
  rw [← φ.naturality, ← φ'.naturality]
  exact congrArg (_ ≫ ·) e

/-- **`K ↦ F_K` is faithful** for `X` quasi-compact with affine diagonal. -/
theorem faithful_integralTransformQcohFunctor : (integralTransformQcohFunctor R X Y).Faithful := by
  refine ⟨fun {K L} a b hab => ?_⟩
  refine hom_ext_of_pullback_baseChangeOpenTargetMap R X Y fun U => ?_
  have : IsAffine (openSubOver R X (U : X.left.Opens)).left := U.2
  have ha := chartKernelHom_map R X Y (openSubOverHom R X (U : X.left.Opens)) a
  have hb := chartKernelHom_map R X Y (openSubOverHom R X (U : X.left.Opens)) b
  rw [hab] at ha
  exact congrArg (fun t => t.hom) (ha.symm.trans hb)

/-- **`K ↦ F_K` is full** for `X` quasi-compact with affine diagonal. -/
theorem full_integralTransformQcohFunctor : (integralTransformQcohFunctor R X Y).Full := by
  refine ⟨fun {K L} φ => ?_⟩
  obtain ⟨ψ₀, hψ₀, -⟩ :=
    Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_openImmersion_cover
      (fun U : X.left.affineOpens => baseChangeOpenTargetMap R X Y (U : X.left.Opens))
      (iSup_image_top_baseChangeOpenTargetMap R X Y) (affineChartHom R X Y φ)
      (affineChartHom_compatible R X Y φ)
  refine ⟨ObjectProperty.homMk ψ₀, integralTransform_natTrans_ext R X Y fun U => ?_⟩
  have : IsAffine (openSubOver R X (U : X.left.Opens)).left := U.2
  have hc : (sourceChangeKernelFunctor R X (openSubOver R X (U : X.left.Opens)) Y
      (openSubOverHom R X (U : X.left.Opens))).map (ObjectProperty.homMk ψ₀ : K ⟶ L) =
      chartKernelHom R X Y (openSubOverHom R X (U : X.left.Opens)) φ :=
    ObjectProperty.hom_ext _ (hψ₀ U)
  have hn := quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated_naturality R X
    (openSubOver R X (U : X.left.Opens)) Y (openSubOverHom R X (U : X.left.Opens)) K
    (ObjectProperty.homMk ψ₀ : K ⟶ L)
  have hm := map_chartKernelHom R X Y (openSubOverHom R X (U : X.left.Opens)) φ
  have key : Functor.whiskerLeft (quasicoherentPushforward (openSubOverHom R X
        (U : X.left.Opens)).left) ((integralTransformQcohFunctor R X Y).map
          (ObjectProperty.homMk ψ₀ : K ⟶ L)) ≫
        (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X
          (openSubOver R X (U : X.left.Opens)) Y (openSubOverHom R X (U : X.left.Opens)) L).hom =
      Functor.whiskerLeft (quasicoherentPushforward (openSubOverHom R X
        (U : X.left.Opens)).left) φ ≫
        (quasicoherentIntegralTransformSourceChangeIsoOfQuasiSeparated R X
          (openSubOver R X (U : X.left.Opens)) Y (openSubOverHom R X (U : X.left.Opens)) L).hom :=
    hn.trans ((congrArg (_ ≫ ·) ((congrArg (integralTransformQcohFunctor R
      (openSubOver R X (U : X.left.Opens)) Y).map hc).trans hm)).trans
        (Iso.hom_inv_id_assoc _ _))
  exact (Iso.cancel_iso_hom_right _ _ _).mp key

end FullyFaithful

end AlgebraicGeometry

end
