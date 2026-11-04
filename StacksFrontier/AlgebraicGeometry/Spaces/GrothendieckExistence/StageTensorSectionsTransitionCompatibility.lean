module

public import StacksFrontier.AlgebraicGeometry.Spaces.TensorSingleSectionsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPushforwardUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EtaleStageSectionsMap
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.StageTensorSectionsTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.LimitTensorSectionsBaseChange

/-!
# The identifications `RΓ(X, E ⊗^𝐋 iₙ,* Fₙ) ≅ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` and the transitions

In Situation [Stacks, Tag 0CX4], the maps
`ψₙ : RΓ(X, E ⊗^𝐋 (iₙ,* Fₙ)[0]) ⟶ RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ[0])` carry `RΓ(X, E ⊗^𝐋 -)` of the
transition `iₙ₊₁,* Fₙ₊₁ ⟶ iₙ,* Fₙ` to the transition map `Mₙ₊₁ ⟶ Mₙ` of
`Mₙ = RΓ(Xₙ, Liₙ^*E ⊗^𝐋 Fₙ[0])` read in `D(A)`, which is
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsTransition`. This is
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.StageTensorSectionsTransitionCompatible`,
the hypothesis `htr` of
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.isPerfect_limitTensorSections_and_isIso_of`.

It is the component at `E` of the equation of natural transformations
`AlgebraicGeometry.Space.tensorSingleSectionsNatTrans_comp`, once the map along `tₙ` there is
re-associated and written in the spelling of `stageTensorSectionsTransition`.

## Main results

* `AlgebraicGeometry.Space.tensorSingleSectionsTransition_compatible`: the statement over
  variable spaces.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsTransitionCompatible`:
  the instance in Situation 0CX4.

## Implementation notes

The statement over variable spaces takes every map that is defined in the situation as a variable
with an equation, and the statement in the situation instantiates these variables with the maps of
the situation; then the instance is checked argument by argument. Its proof is the instance of
the lemmas over variable categories `Stacks.TensorSingleSectionsTransition.*`, with every argument
given, so that the kernel compares the arguments rather than unfolding the projections.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.TensorSingleSectionsTransition

open CategoryTheory Functor

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {𝒳 : Type u₁} {𝒳₁ : Type u₂} {𝒳₀ : Type u₃} {𝒜 : Type u₄} {𝒜₁ : Type u₅} {𝒜₀ : Type u₆}
  [Category.{v₁} 𝒳] [Category.{v₂} 𝒳₁] [Category.{v₃} 𝒳₀] [Category.{v₄} 𝒜] [Category.{v₅} 𝒜₁]
  [Category.{v₆} 𝒜₀]

/-- **Re-associating the transition map**: `x` whiskered by `G₁`, then `ι`, then `c`, all inside
the whiskering by `L₁`, is `x` whiskered by `L₁` then `G₁`, then `ι`, then `c` whiskered by
`B ⋙ G₀` and `R'`; both followed by `R₁` and `ρ`. -/
theorem whiskerRight_whiskerLeft_assoc (L₁ : 𝒳 ⥤ 𝒳₁) (Lt : 𝒳₁ ⥤ 𝒳₀) (L₀ : 𝒳 ⥤ 𝒳₀)
    (A : 𝒳₁ ⥤ 𝒳₁) (Bf : 𝒳₀ ⥤ 𝒳₀) (Rt : 𝒳₀ ⥤ 𝒳₁) (G₁ : 𝒳₁ ⥤ 𝒜₁) (G₀ : 𝒳₀ ⥤ 𝒜₀)
    (R' : 𝒜₀ ⥤ 𝒜₁) (R₁ : 𝒜₁ ⥤ 𝒜) (R₀ : 𝒜₀ ⥤ 𝒜) (x : A ⟶ Lt ⋙ Bf ⋙ Rt)
    (ι : Rt ⋙ G₁ ⟶ G₀ ⋙ R') (c : L₁ ⋙ Lt ⟶ L₀) (ρ : R' ⋙ R₁ ⟶ R₀) :
    whiskerRight (whiskerLeft L₁ (whiskerRight x G₁ ≫ whiskerLeft (Lt ⋙ Bf) ι) ≫
        whiskerRight c (Bf ⋙ G₀ ⋙ R')) R₁ ≫ whiskerLeft (L₀ ⋙ Bf ⋙ G₀) ρ =
      whiskerRight (whiskerRight (whiskerLeft L₁ x) G₁ ≫ whiskerLeft (L₁ ⋙ Lt ⋙ Bf) ι ≫
        whiskerRight (whiskerRight c (Bf ⋙ G₀)) R') R₁ ≫ whiskerLeft (L₀ ⋙ Bf ⋙ G₀) ρ := by
  ext E
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.comp_obj,
    Functor.comp_map, Category.assoc]

/-- **The component at `E` of the re-associated transition map**, read through the hooks `pfc`
(`T₁(M, u)` followed by the projection formula `pf`) and `ac` (`G₁(a)` followed by `ι` and
`R'(z)`): it is `R₁` of `ac` at `pfc (L₁ E) u` and `G₀(T₀(c_E, K))`, followed by `ρ`. -/
theorem app_eq_comp (L₁ : 𝒳 ⥤ 𝒳₁) (Lt : 𝒳₁ ⥤ 𝒳₀) (L₀ : 𝒳 ⥤ 𝒳₀)
    (T₁ : 𝒳₁ ⥤ 𝒳₁ ⥤ 𝒳₁) (T₀ : 𝒳₀ ⥤ 𝒳₀ ⥤ 𝒳₀) (Rt : 𝒳₀ ⥤ 𝒳₁) (G₁ : 𝒳₁ ⥤ 𝒜₁) (G₀ : 𝒳₀ ⥤ 𝒜₀)
    (R' : 𝒜₀ ⥤ 𝒜₁) (R₁ : 𝒜₁ ⥤ 𝒜) (R₀ : 𝒜₀ ⥤ 𝒜)
    (pf : ∀ K : 𝒳₀, T₁.flip.obj (Rt.obj K) ⟶ Lt ⋙ T₀.flip.obj K ⋙ Rt)
    (ι : Rt ⋙ G₁ ⟶ G₀ ⋙ R') (c : L₁ ⋙ Lt ⟶ L₀) (ρ : R' ⋙ R₁ ⟶ R₀)
    {K₁ : 𝒳₁} {K : 𝒳₀} (u : K₁ ⟶ Rt.obj K)
    (θ : L₁ ⋙ T₁.flip.obj K₁ ⋙ G₁ ⋙ R₁ ⟶ L₀ ⋙ T₀.flip.obj K ⋙ G₀ ⋙ R₀)
    (hθ : θ = whiskerRight (whiskerRight (whiskerLeft L₁ (T₁.flip.map u ≫ pf K)) G₁ ≫
        whiskerLeft (L₁ ⋙ Lt ⋙ T₀.flip.obj K) ι ≫
        whiskerRight (whiskerRight c (T₀.flip.obj K ⋙ G₀)) R') R₁ ≫
      whiskerLeft (L₀ ⋙ T₀.flip.obj K ⋙ G₀) ρ)
    (pfc : ∀ (M : 𝒳₁) {K₁ : 𝒳₁} {K : 𝒳₀}, (K₁ ⟶ Rt.obj K) →
      ((T₁.obj M).obj K₁ ⟶ Rt.obj ((T₀.obj (Lt.obj M)).obj K)))
    (hpfc : ∀ (M : 𝒳₁) {K₁ : 𝒳₁} {K : 𝒳₀} (u : K₁ ⟶ Rt.obj K),
      pfc M u = (T₁.obj M).map u ≫ (pf K).app M)
    (ac : ∀ {H : 𝒳₁} {Y : 𝒳₀} {W : 𝒜₀}, (H ⟶ Rt.obj Y) → (G₀.obj Y ⟶ W) →
      (G₁.obj H ⟶ R'.obj W))
    (hac : ∀ {H : 𝒳₁} {Y : 𝒳₀} {W : 𝒜₀} (a : H ⟶ Rt.obj Y) (z : G₀.obj Y ⟶ W),
      ac a z = G₁.map a ≫ ι.app Y ≫ R'.map z)
    (E : 𝒳)
    (σ : (T₁.obj (L₁.obj E)).obj K₁ ⟶ Rt.obj ((T₀.obj (Lt.obj (L₁.obj E))).obj K))
    (hσ : σ = pfc (L₁.obj E) u)
    (π : G₀.obj ((T₀.obj (Lt.obj (L₁.obj E))).obj K) ⟶ G₀.obj ((T₀.obj (L₀.obj E)).obj K))
    (hπ : π = G₀.map ((T₀.flip.obj K).map (c.app E)))
    (τ : G₁.obj ((T₁.obj (L₁.obj E)).obj K₁) ⟶ R'.obj (G₀.obj ((T₀.obj (L₀.obj E)).obj K)))
    (hτ : τ = ac σ π) :
    θ.app E = R₁.map τ ≫ ρ.app (G₀.obj ((T₀.obj (L₀.obj E)).obj K)) := by
  subst hθ hτ hσ hπ
  rw [hac, hpfc]
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.flip_map_app,
    Functor.comp_obj, Functor.comp_map, Functor.flip_obj_obj, Functor.map_comp, Category.assoc]

/-- **An equation of natural transformations at one object**, with the components given as
variables with equations. -/
theorem comp_app_eq_of {P₁ P₀ Q₁ Q₀ : 𝒳 ⥤ 𝒜} (W : P₁ ⟶ P₀) (N₀ : P₀ ⟶ Q₀) (N₁ : P₁ ⟶ Q₁)
    (θ : Q₁ ⟶ Q₀) (h7 : W ≫ N₀ = N₁ ≫ θ) (E : 𝒳)
    (Fx : P₁.obj E ⟶ P₀.obj E) (hFx : Fx = W.app E)
    (ψ₀ : P₀.obj E ⟶ Q₀.obj E) (hψ₀ : ψ₀ = N₀.app E)
    (ψ₁ : P₁.obj E ⟶ Q₁.obj E) (hψ₁ : ψ₁ = N₁.app E)
    (Z : Q₁.obj E ⟶ Q₀.obj E) (hZ : θ.app E = Z) :
    Fx ≫ ψ₀ = ψ₁ ≫ Z := by
  subst hFx hψ₀ hψ₁ hZ
  rw [← NatTrans.comp_app, h7, NatTrans.comp_app]

end Stacks.TensorSingleSectionsTransition

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U U₁ U₀ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)]
  {X X₁ X₀ : AlgebraicSpaces B S hS}
  (h : X ⟶ schemeSpace U)
  (h₁ : X₁ ⟶ schemeSpace U₁)
  (h₀ : X₀ ⟶ schemeSpace U₀)
  (g₁ : U₁ ⟶ U) (gt : U₀ ⟶ U₁) (g₀ : U₀ ⟶ U) (hg : gt ≫ g₁ = g₀)
  (i₁ : X₁ ⟶ X) (t : X₀ ⟶ X₁) (i₀ : X₀ ⟶ X) (hi : t ≫ i₁ = i₀)
  (w₁ : i₁ ≫ h = h₁ ≫ representedSpaceMap B S hS g₁)
  (wt : t ≫ h₁ = h₀ ≫ representedSpaceMap B S hS gt)
  (w₀ : i₀ ≫ h = h₀ ≫ representedSpaceMap B S hS g₀)
  (hc : (representedAffineCommRingCatHom B S hS g₀).hom =
    (representedAffineCommRingCatHom B S hS gt).hom.comp
      (representedAffineCommRingCatHom B S hS g₁).hom)
  (hi₁ : IsAffineHom B S hS i₁.hom) (hi₀ : IsAffineHom B S hS i₀.hom)
  (ht : IsAffineHom B S hS t.hom)
  (F : Modules.{u, u} B S hS X₀.1 X₀.2) (hF : F.IsQuasicoherentOnSite)
  (F₁ : Modules.{u, u} B S hS X₁.1 X₁.2) (hF₁ : F₁.IsQuasicoherentOnSite)
  (a : F₁ ⟶ (modulePushforward B S hS t).obj F)
  (E : spaceDerivedCategory B S hS X)

section StandardModel

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

/-- `RΓ(X, E ⊗^𝐋 (i_*F)[0])` over variable spaces: the form of
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsSource`. -/
abbrev tensorSingleSectionsSource :
    StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  (representedAffineDerivedSections B S hS U).obj
    ((derivedModulePushforward B S hS h).obj
      (((smallEtaleDerivedTensor B S hS X).obj E).obj
        ((spaceDerivedSingle B S hS X 0).obj ((modulePushforward B S hS i₀).obj F))))

/-- `Li^*E ⊗^𝐋 F[0]` on `X₀` over variable spaces: the form of
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorObj`. -/
abbrev tensorSingleSectionsObj :
    DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₀)) :=
  ((smallEtaleDerivedTensor B S hS X₀).obj
      ((smallEtaleDerivedModulePullback B S hS i₀).obj E)).obj
    ((DerivedCategory.singleFunctor _ 0).obj F)

/-- `RΓ(X₀, Li^*E ⊗^𝐋 F[0])` in `D(R₀)` over variable spaces: the form of
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.stageTensorSectionsTarget`. -/
abbrev tensorSingleSectionsTarget :
    StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme B S hS).obj U₀, ⊤) :=
  (representedAffineDerivedSections B S hS U₀).obj
    ((derivedModulePushforward B S hS h₀).obj (tensorSingleSectionsObj B S hS i₀ F E))

end StandardModel

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U₁)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U₀)] in
/-- `RΓ(X, E ⊗^𝐋 -)` over a variable space: the form of
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.tensorSectionsFunctor`. -/
abbrev tensorSingleSectionsFunctor :
    spaceDerivedCategory B S hS X ⥤
      StacksDraft.ringDerivedCategory Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  (smallEtaleDerivedTensor B S hS X).obj E ⋙
    (derivedModulePushforward B S hS h ⋙ representedAffineDerivedSections B S hS U)

section Core

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance] HasDerivedCategory.standard

/-- **The map along `t` of `tensorSingleSectionsNatTrans_comp`, re-associated**: for
`u : K₁ ⟶ Rt_* K`, `RΓ(X₁, Li'^* - ⊗^𝐋 u)` followed by the projection formula of `t`, the
identification `RΓ(X₁, Rt_* -) ≅ RΓ(X₀, -)`, `RΓ(X₀, c ⊗^𝐋 K)` for `c : Lt^*Li'^* ⟶ Li^*` and the
comparison of restrictions of scalars, grouped as in
`AlgebraicGeometry.Space.affineBaseDerivedSectionsPushforwardComp`. -/
def tensorSingleSectionsTransitionCompNatTrans
    {K₁ : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₁))}
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X₀))}
    (u : K₁ ⟶ (derivedModulePushforward B S hS t).obj K)
    (c : smallEtaleDerivedModulePullback B S hS i₁ ⋙ smallEtaleDerivedModulePullback B S hS t ⟶
      smallEtaleDerivedModulePullback B S hS i₀) :=
  Functor.whiskerRight
      (Functor.whiskerRight (Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS i₁)
          ((smallEtaleDerivedTensor B S hS X₁).flip.map u ≫
            smallEtaleProjectionFormulaSndNatTrans t K))
          (derivedModulePushforward B S hS h₁ ⋙ representedAffineDerivedSections B S hS U₁) ≫
        Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS i₁ ⋙
            smallEtaleDerivedModulePullback B S hS t ⋙
              (smallEtaleDerivedTensor B S hS X₀).flip.obj K)
          (affineBaseDerivedSectionsPushforwardIso B S hS gt h₁ h₀ t wt).hom ≫
        Functor.whiskerRight (Functor.whiskerRight c
            ((smallEtaleDerivedTensor B S hS X₀).flip.obj K ⋙
              (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀)))
          (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS gt).hom))
      (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₁).hom) ≫
    Functor.whiskerLeft (smallEtaleDerivedModulePullback B S hS i₀ ⋙
        (smallEtaleDerivedTensor B S hS X₀).flip.obj K ⋙
        (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀))
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
        (representedAffineCommRingCatHom B S hS g₁).hom
        (representedAffineCommRingCatHom B S hS gt).hom
        (representedAffineCommRingCatHom B S hS g₀).hom hc).hom

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- `tensorSingleSectionsTransitionCompNatTrans` does not see whether `F[0]` is written with the
single functor of the standard model on the topos or with `spaceDerivedSingle`, nor whether the
comparison `(t_*F)[0] ⟶ Rt_*(F[0])` is written as `modulePushforwardSingleToDerived` or as the
inverse of `derivedModulePushforwardSingleIsoOfIsAffineHom`. -/
theorem tensorSingleSectionsTransitionCompNatTrans_spaceSingle
    (c : smallEtaleDerivedModulePullback B S hS i₁ ⋙ smallEtaleDerivedModulePullback B S hS t ⟶
      smallEtaleDerivedModulePullback B S hS i₀) :
    tensorSingleSectionsTransitionCompNatTrans B S hS h₁ h₀ g₁ gt g₀ i₁ t i₀ wt hc
        ((DerivedCategory.singleFunctor _ 0).map a ≫
          (modulePushforwardSingleToDerived B S hS t).app F) c =
      tensorSingleSectionsTransitionCompNatTrans B S hS h₁ h₀ g₁ gt g₀ i₁ t i₀ wt hc
        ((spaceDerivedSingle B S hS X₁ 0).map a ≫
          (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS t ht F hF).inv :
          _ ⟶ (derivedModulePushforward B S hS t).obj ((spaceDerivedSingle B S hS X₀ 0).obj F)) c :=
  rfl

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] in
/-- `tensorSingleSectionsTransitionNatTrans` is `tensorSingleSectionsTransitionCompNatTrans` at
`a[0] ≫ ((t_*F)[0] ⟶ Rt_*(F[0]))` and `Lt^*Li'^* ≅ Li^*`. -/
theorem tensorSingleSectionsTransitionNatTrans_eq_compNatTrans :
    tensorSingleSectionsTransitionNatTrans B S hS h₁ h₀ g₁ gt g₀ i₁ t i₀ hi wt hc F F₁ a =
      tensorSingleSectionsTransitionCompNatTrans B S hS h₁ h₀ g₁ gt g₀ i₁ t i₀ wt hc
        ((DerivedCategory.singleFunctor _ 0).map a ≫
          (modulePushforwardSingleToDerived B S hS t).app F)
        (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hi).hom :=
  Stacks.TensorSingleSectionsTransition.whiskerRight_whiskerLeft_assoc
    (smallEtaleDerivedModulePullback B S hS i₁) (smallEtaleDerivedModulePullback B S hS t)
    (smallEtaleDerivedModulePullback B S hS i₀)
    ((smallEtaleDerivedTensor B S hS X₁).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F₁))
    ((smallEtaleDerivedTensor B S hS X₀).flip.obj ((DerivedCategory.singleFunctor _ 0).obj F))
    _ (derivedModulePushforward B S hS h₁ ⋙ representedAffineDerivedSections B S hS U₁)
    (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀)
    (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS gt).hom)
    (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₁).hom)
    (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₀).hom)
    ((smallEtaleDerivedTensor B S hS X₁).flip.map
        ((DerivedCategory.singleFunctor _ 0).map a ≫
          (modulePushforwardSingleToDerived B S hS t).app F) ≫
      smallEtaleProjectionFormulaSndNatTrans t ((DerivedCategory.singleFunctor _ 0).obj F))
    (affineBaseDerivedSectionsPushforwardIso B S hS gt h₁ h₀ t wt).hom
    (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS hi).hom
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
      (representedAffineCommRingCatHom B S hS g₁).hom
      (representedAffineCommRingCatHom B S hS gt).hom
      (representedAffineCommRingCatHom B S hS g₀).hom hc).hom

end Core

include hg in
/-- **The identifications `ψ` are compatible with the transition along `t`, at one object**: over
variable spaces, `RΓ(X, E ⊗^𝐋 m[0])` followed by `ψ_i` is `ψ_{i'}` followed by the restriction of
scalars of `affineBaseDerivedSectionsPushforwardComp` of
`E|_{X₁} ⊗^𝐋 (a[0] ≫ (t_*F)[0] ≅ Rt_*(F[0]))` and the projection formula of `t`, and of
`RΓ(X₀, - ⊗^𝐋 F[0])` of `c : Lt^*Li'^* ≅ Li^*`, followed by the comparison of restrictions of
scalars. Every map is a variable `ψ₀, ψ₁, σ, π, τ, c` given together with an equation. -/
theorem tensorSingleSectionsTransition_compatible
    (cI : (modulePushforward B S hS i₁).obj ((modulePushforward B S hS t).obj F) ≅
      (modulePushforward B S hS i₀).obj F)
    (hcI : cI = (modulePushforwardCompIso B S hS t i₁).app F ≪≫
      eqToIso (congrArg (fun φ => (modulePushforward B S hS φ).obj F) hi))
    (m : (modulePushforward B S hS i₁).obj F₁ ⟶ (modulePushforward B S hS i₀).obj F)
    (hm : m = (modulePushforward B S hS i₁).map a ≫ cI.hom)
    (N₀ : _) (hN₀ : N₀ = tensorSingleSectionsNatTrans B S hS h h₀ g₀ i₀ w₀ hi₀ F hF)
    (ψ₀ : tensorSingleSectionsSource B S hS h i₀ F E ⟶
      (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₀).hom).obj
        (tensorSingleSectionsTarget B S hS h₀ i₀ F E))
    (hψ₀ : ψ₀ = N₀.app E)
    (N₁ : _) (hN₁ : N₁ = tensorSingleSectionsNatTrans B S hS h h₁ g₁ i₁ w₁ hi₁ F₁ hF₁)
    (ψ₁ : tensorSingleSectionsSource B S hS h i₁ F₁ E ⟶
      (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₁).hom).obj
        (tensorSingleSectionsTarget B S hS h₁ i₁ F₁ E))
    (hψ₁ : ψ₁ = N₁.app E)
    (c : smallEtaleDerivedModulePullback B S hS i₁ ⋙ smallEtaleDerivedModulePullback B S hS t ≅
      smallEtaleDerivedModulePullback B S hS i₀)
    (hcc : c = smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
      smallEtaleDerivedModulePullbackCongr B S hS hi)
    (σ : ((smallEtaleDerivedTensor B S hS X₁).obj
        ((smallEtaleDerivedModulePullback B S hS i₁).obj E)).obj
      ((spaceDerivedSingle B S hS X₁ 0).obj F₁) ⟶
    (derivedModulePushforward B S hS t).obj
      (((smallEtaleDerivedTensor B S hS X₀).obj
          ((smallEtaleDerivedModulePullback B S hS t).obj
            ((smallEtaleDerivedModulePullback B S hS i₁).obj E))).obj
        ((spaceDerivedSingle B S hS X₀ 0).obj F)))
    (hσ : σ = smallEtaleProjectionFormulaComp t
      ((smallEtaleDerivedModulePullback B S hS i₁).obj E)
      ((spaceDerivedSingle B S hS X₁ 0).map a ≫
        (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS t ht F hF).inv :
        _ ⟶ (derivedModulePushforward B S hS t).obj ((spaceDerivedSingle B S hS X₀ 0).obj F)))
    (π : (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀).obj
      (((smallEtaleDerivedTensor B S hS X₀).obj
          ((smallEtaleDerivedModulePullback B S hS t).obj
            ((smallEtaleDerivedModulePullback B S hS i₁).obj E))).obj
        ((spaceDerivedSingle B S hS X₀ 0).obj F)) ⟶
      tensorSingleSectionsTarget B S hS h₀ i₀ F E)
    (hπ : π = (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀).map
      (((smallEtaleDerivedTensor B S hS X₀).flip.obj ((spaceDerivedSingle B S hS X₀ 0).obj F)).map
        (c.hom.app E)))
    (τ : tensorSingleSectionsTarget B S hS h₁ i₁ F₁ E ⟶
      (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS gt).hom).obj
        (tensorSingleSectionsTarget B S hS h₀ i₀ F E))
    (hτ : τ = affineBaseDerivedSectionsPushforwardComp B S hS gt h₁ h₀ t wt σ π) :
    (tensorSingleSectionsFunctor B S hS h E).map ((spaceDerivedSingle B S hS X 0).map m) ≫ ψ₀ =
    ψ₁ ≫ (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₁).hom).map τ ≫
      (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
        (representedAffineCommRingCatHom B S hS g₁).hom
        (representedAffineCommRingCatHom B S hS gt).hom
        (representedAffineCommRingCatHom B S hS g₀).hom hc).hom.app
        (tensorSingleSectionsTarget B S hS h₀ i₀ F E) := by
  subst hcI hm hcc hN₀ hN₁
  have h7 := tensorSingleSectionsNatTrans_comp B S hS h h₁ h₀ g₁ gt g₀ hg i₁ t i₀ hi w₁ wt w₀ hc
    hi₁ hi₀ F hF F₁ hF₁ a _ rfl _ rfl
    (modulePushforwardSingleToDerived_comp B S hS t i₁ i₀ hi F)
  have hTT := (tensorSingleSectionsTransitionNatTrans_eq_compNatTrans B S hS h₁ h₀ g₁ gt g₀ i₁ t
    i₀ hi wt hc F F₁ a).trans
    (tensorSingleSectionsTransitionCompNatTrans_spaceSingle B S hS h₁ h₀ g₁ gt g₀ i₁ t i₀ wt hc ht
      F hF F₁ a (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
        smallEtaleDerivedModulePullbackCongr B S hS hi).hom)
  exact Stacks.TensorSingleSectionsTransition.comp_app_eq_of _ _ _ _ h7 E _ rfl ψ₀ hψ₀ ψ₁ hψ₁ _
    ((congrArg (fun θ => NatTrans.app θ E) hTT).trans
      (Stacks.TensorSingleSectionsTransition.app_eq_comp
        (smallEtaleDerivedModulePullback B S hS i₁) (smallEtaleDerivedModulePullback B S hS t)
        (smallEtaleDerivedModulePullback B S hS i₀) (smallEtaleDerivedTensor B S hS X₁)
        (smallEtaleDerivedTensor B S hS X₀) _
        (derivedModulePushforward B S hS h₁ ⋙ representedAffineDerivedSections B S hS U₁)
        (derivedModulePushforward B S hS h₀ ⋙ representedAffineDerivedSections B S hS U₀)
        (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS gt).hom)
        (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₁).hom)
        (StacksDraft.ringRestrictScalars (representedAffineCommRingCatHom B S hS g₀).hom)
        (fun W => smallEtaleProjectionFormulaSndNatTrans t W)
        (affineBaseDerivedSectionsPushforwardIso B S hS gt h₁ h₀ t wt).hom
        (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
          smallEtaleDerivedModulePullbackCongr B S hS hi).hom
        (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
          (representedAffineCommRingCatHom B S hS g₁).hom
          (representedAffineCommRingCatHom B S hS gt).hom
          (representedAffineCommRingCatHom B S hS g₀).hom hc).hom
        ((spaceDerivedSingle B S hS X₁ 0).map a ≫
          (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS t ht F hF).inv :
          _ ⟶ (derivedModulePushforward B S hS t).obj ((spaceDerivedSingle B S hS X₀ 0).obj F))
        (tensorSingleSectionsTransitionCompNatTrans B S hS h₁ h₀ g₁ gt g₀ i₁ t i₀ wt hc
          ((spaceDerivedSingle B S hS X₁ 0).map a ≫
            (derivedModulePushforwardSingleIsoOfIsAffineHom B S hS t ht F hF).inv :
            _ ⟶ (derivedModulePushforward B S hS t).obj ((spaceDerivedSingle B S hS X₀ 0).obj F))
          (smallEtaleDerivedModulePullbackCompIso B S hS t i₁ ≪≫
            smallEtaleDerivedModulePullbackCongr B S hS hi).hom)
        rfl (fun M _ _ u => smallEtaleProjectionFormulaComp t M u) (fun _ _ _ _ => rfl)
        (fun a z => affineBaseDerivedSectionsPushforwardComp B S hS gt h₁ h₀ t wt a z)
        (fun _ _ => rfl) E σ hσ π hπ τ hτ))

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u}) (n : ℕ)
  (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)

/-- **The identifications `RΓ(X, E ⊗^𝐋 iₙ,* Fₙ) ≅ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` are compatible with
the transitions** (the hypothesis `htr` of
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.isPerfect_limitTensorSections_and_isIso_of`):
the instance of `AlgebraicGeometry.Space.tensorSingleSectionsTransition_compatible` along
`iₙ = tₙ ≫ iₙ₊₁`. -/
theorem stageTensorSectionsTransitionCompatible : D.StageTensorSectionsTransitionCompatible E n :=
  tensorSingleSectionsTransition_compatible D.B D.S D.containsLimitBase
    (U := limitBaseObject D.system D.B D.containsLimitBase)
    (U₁ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))
    (U₀ := baseObjectAt D.system D.B D.containsLimitBase D.containsBaseAt n)
    (X := D.X.left) (X₁ := D.stage (n + 1)) (X₀ := D.stage n) D.X.hom (D.stageToBase (n + 1))
    (D.stageToBase n)
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt (n + 1))
    (baseObjectTransition D.system D.B D.containsLimitBase D.containsBaseAt n)
    (baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (baseObjectTransition_baseObjectProjection D.system D.B D.containsLimitBase D.containsBaseAt n)
    (D.closedImmersion (n + 1)) (D.transition n) (D.closedImmersion n)
    (D.transition_closedImmersion n) (D.closedImmersion_comp_hom (n + 1))
    (D.transition_comp_stageToBase n) (D.closedImmersion_comp_hom n) (D.stageRingHom_eq_comp n)
    (D.isAffineHom_closedImmersion (n + 1)) (D.isAffineHom_closedImmersion n)
    (D.isAffineHom_transition n)
    (D.F n) (D.isQuasicoherentOnSite_F n) (D.F (n + 1)) (D.isQuasicoherentOnSite_F (n + 1))
    (D.transitionAdjoint n) E (D.pushforwardCompIso n) rfl (D.pushforwardTransition n) rfl
    (D.stageTensorSectionsNatTrans n)
    ((D.stageTensorSectionsNatTrans_eq_natTransOf n).trans
      (D.stageTensorSectionsNatTransOf_eq_tensorSingleSectionsNatTrans n _ _))
    (D.stageTensorSectionsMap n E) (D.stageTensorSectionsMap_eq n E)
    (D.stageTensorSectionsNatTrans (n + 1))
    ((D.stageTensorSectionsNatTrans_eq_natTransOf (n + 1)).trans
      (D.stageTensorSectionsNatTransOf_eq_tensorSingleSectionsNatTrans (n + 1) _ _))
    (D.stageTensorSectionsMap (n + 1) E) (D.stageTensorSectionsMap_eq (n + 1) E)
    (D.stagePullbackCompIso n) rfl
    (D.stageTensorSectionsTransitionStage n E) rfl
    (D.stageTensorSectionsTransitionPullback n E) rfl
    (D.stageTensorSectionsTransition n E) rfl

end AlgebraicGeometry.Space.FlatSheafExistenceSituation

end
