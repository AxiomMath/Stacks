module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.AffineTensorFunctor

/-!
# Quasi-coherent modules on an affine scheme are of the form `M~`

Let `U` be an affine scheme over `S` with ring of global functions `A`.  Every quasi-coherent
module `N` on the fppf site of `U` is `Γ(U, N)~`: the map `Γ(U, N)~ ⟶ N` adjoint to the
restriction maps `Γ(U, N) ⟶ N(T)` is bijective over every affine `T`, where it is the
base-change comparison `𝒪(T) ⊗_A N(U) ⟶ N(T)` of the cartesian module `N`.  So
`Γ(U, -) ⋙ (-)~ ≅ 𝟭` on `QCoh(𝒪_U)`, and `QCoh(𝒪_U)` is read through `Mod_A` by `Γ(U, -)`.

## Main definitions

* `AlgebraicGeometry.Stack.quasicoherentGlobalSections`: `Γ(U, -) : QCoh(𝒪_U) ⥤ Mod_A`.
* `AlgebraicGeometry.Stack.tildeCounitIso`: `Γ(U, -) ⋙ (-)~ ≅ 𝟭`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace CategoryTheory.Functor

/-- A square carried through a functor and pasted with a natural square. -/
lemma map_comp_map_comp_eq_of_comm {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D)
    {P P' Q Q' : C} {Y Y' : D} (a : P ⟶ P') (b : Q ⟶ Q') (l : P ⟶ Q) (l' : P' ⟶ Q')
    (c : L.obj Q ⟶ Y) (c' : L.obj Q' ⟶ Y') (f : Y ⟶ Y') (h₁ : a ≫ l' = l ≫ b)
    (h₂ : c ≫ f = L.map b ≫ c') :
    L.map a ≫ L.map l' ≫ c' = (L.map l ≫ c) ≫ f := by
  rw [Category.assoc, h₂, ← L.map_comp_assoc, ← L.map_comp_assoc, h₁]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

attribute [local instance] FibredSite.hasWeakSheafify_associatedTopology
  FibredSite.wEqualsLocallyBijective_associatedTopology

local notation "𝒪[" Y "]" => AlgebraicStacks.fppfStructureRingSheaf _ _ _ Y
local notation "𝒪c[" Y "]" => AlgebraicStacks.fppfStructureSheaf _ _ _ Y

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (U : BigFppfOver B S hS)

/-- The final object `𝟙 U` of the site of `U`. -/
noncomputable abbrev siteTop : (schemeStack.{u, w} B S hS U).val.val.obj := Over.mk (𝟙 U)

variable {U} in
/-- The arrow `T ⟶ U` to the final object. -/
noncomputable abbrev toSiteTop (T : (schemeStack.{u, w} B S hS U).val.val.obj) :
    T ⟶ siteTop.{u, w} U :=
  Over.homMk (T.hom : T.left ⟶ U)

variable {U} in
/-- Any morphism `T ⟶ T'` followed by `T' ⟶ U` is `T ⟶ U`. -/
lemma comp_toSiteTop {T T' : (schemeStack.{u, w} B S hS U).val.val.obj} (f : T ⟶ T') :
    f ≫ toSiteTop T' = toSiteTop T :=
  Over.OverMorphism.ext (Over.w f)

/-- **`Γ(U, -) : QCoh(𝒪_U) ⥤ Mod_A`**, sections over the final object. -/
noncomputable def quasicoherentGlobalSections :
    AlgebraicStacks.quasicoherentModules B S hS (schemeStack.{u, w} B S hS U) ⥤
      ModuleCat.{u} (schemeGlobalRing U) :=
  ObjectProperty.ι _ ⋙ SheafOfModules.forget _ ⋙
    PresheafOfModules.evaluation _ (op (siteTop.{u, w} U))

variable {U}

/-- `Γ(U, N)`, the sections over the final object, as a module over `A`. -/
noncomputable def globalSectionsModule (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U]) :
    ModuleCat.{u} (schemeGlobalRing U) :=
  (PresheafOfModules.evaluation _ (op (siteTop.{u, w} U))).obj N.val

/-- The restriction map `Γ(U, N) ⟶ N(T)`, as a map of `A`-modules. -/
noncomputable def tildeCounitRestriction (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U])
    (T : (Over U)ᵒᵖ) :
    globalSectionsModule N ⟶ (ModuleCat.restrictScalars (globalRingHomApp U T)).obj (N.val.obj T) :=
  N.val.map (toSiteTop.{u, w} T.unop).op

/-- The component at `T` of `𝒪(T) ⊗_A Γ(U, N) ⟶ N(T)`, adjoint to the restriction map. -/
noncomputable def tildeCounitPresheafApp (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U])
    (T : (Over U)ᵒᵖ) :
    (ModuleCat.extendScalars (globalRingHomApp U T)).obj (globalSectionsModule.{u, w} N) ⟶
      N.val.obj T :=
  ((ModuleCat.extendRestrictScalarsAdj (globalRingHomApp U T)).homEquiv _ _).symm
    (tildeCounitRestriction N T)

/-- The map `𝒪(T) ⊗_A Γ(U, N) ⟶ N(T)` sends `1 ⊗ n` to the restriction of `n` to `T`. -/
lemma tildeCounitPresheafApp_one_tmul (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U])
    (T : (Over U)ᵒᵖ) (n : globalSectionsModule.{u, w} N) :
    (tildeCounitPresheafApp N T).hom (Stacks.PullbackModel.tmul (globalRingHomApp U T) 1 n) =
      (N.val.map (toSiteTop.{u, w} T.unop).op).hom n :=
  @Stacks.PullbackModel.homEquiv_symm_apply_tmul _ _ _ _ (globalRingHomApp U T)
    (globalSectionsModule.{u, w} N) (N.val.obj T) (tildeCounitRestriction N T) n

/-- Naturality of `𝒪(T) ⊗_A Γ(U, N) ⟶ N(T)` in `T`, evaluated on an element `1 ⊗ n`. -/
theorem tildeCounitPresheafApp_naturality_apply
    (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U])
    {T T' : (Over U)ᵒᵖ} (f : T ⟶ T') (n : globalSectionsModule.{u, w} N) :
    (tildeCounitPresheafApp N T').hom (Stacks.PullbackModel.tmul (globalRingHomApp U T')
        (((schemeStructurePresheaf U).map f).hom 1) n) =
      (N.val.map f).hom ((tildeCounitPresheafApp N T).hom
        (Stacks.PullbackModel.tmul (globalRingHomApp U T) 1 n)) := by
  have htop : (toSiteTop.{u, w} T'.unop).op = (toSiteTop.{u, w} T.unop).op ≫ f :=
    congrArg Quiver.Hom.op (comp_toSiteTop.{u, w} f.unop).symm
  rw [map_one, tildeCounitPresheafApp_one_tmul N T' n, tildeCounitPresheafApp_one_tmul N T n, htop]
  exact N.val.map_comp_apply _ _ n

/-- The maps `𝒪(T) ⊗_A Γ(U, N) ⟶ N(T)` are natural in `T`. -/
theorem tildeCounitPresheafApp_naturality (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U])
    {T T' : (Over U)ᵒᵖ} (f : T ⟶ T') :
    ((tildePresheafFunctor.{u, w} U).obj (globalSectionsModule.{u, w} N)).map f ≫
        (ModuleCat.restrictScalars ((𝒪[schemeStack.{u, w} B S hS U]).obj.map f).hom).map
          (tildeCounitPresheafApp N T') =
      tildeCounitPresheafApp N T ≫ N.val.map f :=
  Stacks.PullbackModel.extendScalars_hom_ext _ fun n =>
    tildeCounitPresheafApp_naturality_apply N f n

/-- **`𝒪(T) ⊗_A Γ(U, N) ⟶ N(T)`**, a morphism of presheaves of modules. -/
noncomputable def tildeCounitPresheaf (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U]) :
    (tildePresheafFunctor.{u, w} U).obj (globalSectionsModule.{u, w} N) ⟶ N.val where
  app T := tildeCounitPresheafApp N T
  naturality f := tildeCounitPresheafApp_naturality N f

/-- **The counit `Γ(U, N)~ ⟶ N`**: the sheafification of
`AlgebraicGeometry.Stack.tildeCounitPresheaf`, followed by `N^# ≅ N`. -/
noncomputable def tildeCounit (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U]) :
    (tildeFunctor.{u, w} U).obj (globalSectionsModule.{u, w} N) ⟶ N :=
  (Stacks.SheafOfModules.sheafifyFunctor (𝒪c[schemeStack.{u, w} B S hS U]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))).map
      (tildeCounitPresheaf N) ≫
    (Stacks.SheafOfModules.sheafifyValIso (𝒪c[schemeStack.{u, w} B S hS U]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U)) N).hom

/-- The counit, composed with the sheafification map, is `𝒪(T) ⊗_A Γ(U, N) ⟶ N(T)`. -/
theorem tildeCounit_val_app_tildeUnit (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U])
    (T : (Over U)ᵒᵖ)
    (x : ((tildePresheafFunctor.{u, w} U).obj (globalSectionsModule.{u, w} N)).obj T) :
    ((tildeCounit N).val.app T).hom
        (((tildeUnit.{u, w} U (globalSectionsModule.{u, w} N)).app T).hom x) =
      ((tildeCounitPresheaf N).app T).hom x := by
  let adj := Stacks.SheafOfModules.TensorSheafification.sheafifyAdjunction
    (𝒪c[schemeStack.{u, w} B S hS U]).obj
    (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U))
  have h₁ := congrArg (fun k => (PresheafOfModules.Hom.app k T).hom x)
    (adj.unit.naturality (tildeCounitPresheaf N))
  have h₂ := congrArg
    (fun k => (PresheafOfModules.Hom.app k T).hom (((tildeCounitPresheaf N).app T).hom x))
    (adj.right_triangle_components N)
  exact (congrArg (((Stacks.SheafOfModules.sheafifyValIso (𝒪c[schemeStack.{u, w} B S hS U]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS
        (schemeStack.{u, w} B S hS U)) N).hom.val.app T).hom) h₁.symm).trans h₂

/-- **Over an affine `T`, `𝒪(T) ⊗_A Γ(U, N) ⟶ N(T)` is bijective** for `N` quasi-coherent and `U`
affine: it is the base-change comparison of the restriction along `T ⟶ U`, and `N` is cartesian
on affines. -/
theorem bijective_tildeCounitPresheaf_app (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U])
    (hN : N.IsQuasicoherentOnSite) (hU : IsAffineOver B S hS U)
    {T : (schemeStack.{u, w} B S hS U).val.val.obj}
    (hT : IsAffineOver B S hS ((schemeStack.{u, w} B S hS U).val.val.p.obj T)) :
    Function.Bijective ((tildeCounitPresheaf N).app (op T)) := by
  have hp := (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
  have hcart := FibredSite.isCartesianOnAffines_of_isQuasicoherentOnSite hp N hN
    (toSiteTop.{u, w} T) hU hT
  let := FibredSite.sectionModule hp N.val (siteTop.{u, w} U)
  let := FibredSite.sectionModule hp N.val T
  let := FibredSite.sectionAlgebra hp (toSiteTop.{u, w} T)
  let := FibredSite.sectionModuleAlong hp N.val (toSiteTop.{u, w} T)
  have := FibredSite.sectionIsScalarTower hp N.val (toSiteTop.{u, w} T)
  have heq : (tildeCounitPresheaf N).app (op T) =
      @ModuleCat.ofHom (FibredSite.sectionRing hp T) _
        ((ModuleCat.extendScalars (globalRingHomApp U (op T))).obj
          (globalSectionsModule.{u, w} N)) (N.val.obj (op T)) _
        ((ModuleCat.extendScalars (globalRingHomApp U (op T))).obj
          (globalSectionsModule.{u, w} N)).isModule _ (N.val.obj (op T)).isModule
        (FibredSite.restrictionBaseChangeMap hp N.val (toSiteTop.{u, w} T)) := by
    refine Stacks.PullbackModel.extendScalars_hom_ext _ fun n => ?_
    have h := LinearMap.liftBaseChange_tmul (A := FibredSite.sectionRing hp T)
      (FibredSite.restrictionLinearMap hp N.val (toSiteTop.{u, w} T))
      (1 : FibredSite.sectionRing hp T) n
    exact (tildeCounitPresheafApp_one_tmul N (op T) n).trans (h.trans (one_smul _ _)).symm
  rwa [heq]

/-- **`Γ(U, N)~ ≅ N` for `N` quasi-coherent on an affine `U`.** -/
theorem isIso_tildeCounit (N : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U])
    (hN : N.IsQuasicoherentOnSite) (hU : IsAffineOver B S hS U) : IsIso (tildeCounit N) :=
  FibredSite.isIso_of_bijective_affine (schemeStack.{u, w} B S hS U).val.isFiberedInGroupoids
    (tildeCounit N) fun T hT => by
      have hη := bijective_tildeUnit_app.{u, w} U (globalSectionsModule.{u, w} N) hT
      have hlam := bijective_tildeCounitPresheaf_app N hN hU hT
      have hfac := tildeCounit_val_app_tildeUnit N (op T)
      refine ⟨fun y y' hyy' => ?_, fun z => ?_⟩
      · obtain ⟨x, rfl⟩ := hη.2 y
        obtain ⟨x', rfl⟩ := hη.2 y'
        exact congrArg _ (hlam.1 ((hfac x).symm.trans (hyy'.trans (hfac x'))))
      · obtain ⟨x, hx⟩ := hlam.2 z
        exact ⟨_, (hfac x).trans hx⟩

/-- The map `Γ(U, N) ⟶ Γ(U, N')` of a morphism of sheaves of modules. -/
noncomputable abbrev globalSectionsMap {N N' : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U]}
    (f : N ⟶ N') : globalSectionsModule.{u, w} N ⟶ globalSectionsModule.{u, w} N' :=
  f.val.app (op (siteTop.{u, w} U))

/-- The morphism of presheaves of modules `𝒪(-) ⊗_A Γ(U, N) ⟶ N` is natural in `N`. -/
theorem tildeCounitPresheaf_naturality {N N' : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U]}
    (f : N ⟶ N') :
    (tildePresheafFunctor.{u, w} U).map (globalSectionsMap f) ≫ tildeCounitPresheaf N' =
      tildeCounitPresheaf N ≫ f.val :=
  PresheafOfModules.hom_ext fun T => Stacks.PullbackModel.extendScalars_hom_ext _ fun n =>
    (tildeCounitPresheafApp_one_tmul N' T ((globalSectionsMap f).hom n)).trans
      ((PresheafOfModules.naturality_apply f.val (toSiteTop.{u, w} T.unop).op n).symm.trans
        (congrArg (f.val.app T).hom (tildeCounitPresheafApp_one_tmul N T n).symm))

/-- **Naturality of the counit `Γ(U, N)~ ⟶ N`.** -/
theorem tildeCounit_naturality {N N' : SheafOfModules.{u} 𝒪[schemeStack.{u, w} B S hS U]}
    (f : N ⟶ N') :
    (tildeFunctor.{u, w} U).map (globalSectionsMap f) ≫ tildeCounit N' = tildeCounit N ≫ f :=
  Functor.map_comp_map_comp_eq_of_comm _ _ f.val _ _ _ _ f (tildeCounitPresheaf_naturality f)
    (Stacks.SheafOfModules.sheafifyValIso_hom_naturality (𝒪c[schemeStack.{u, w} B S hS U]).obj
      (AlgebraicStacks.isSheaf_structureRingPresheaf B S hS (schemeStack.{u, w} B S hS U)) f)

variable (U) in
/-- **`Γ(U, -) ⋙ (-)~ ≅ 𝟭` on `QCoh(𝒪_U)` for an affine scheme `U`.** -/
noncomputable def tildeCounitIso (hU : IsAffineOver B S hS U) :
    quasicoherentGlobalSections.{u, w} U ⋙ tildeQuasicoherent.{u, w} U ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun N => (ObjectProperty.fullyFaithfulι _).preimageIso
      (haveI := isIso_tildeCounit N.obj N.property hU
       (asIso (tildeCounit N.obj) :
         (tildeFunctor.{u, w} U).obj (globalSectionsModule.{u, w} N.obj) ≅ N.obj)))
    (fun f => ObjectProperty.hom_ext _ (tildeCounit_naturality f.hom))

section Functor

attribute [local instance] FibredSite.monoidalCategoryQuasicoherentModules
  AlgebraicStacks.quasicoherentSymmetricCategory

variable {𝒳 : AlgebraicStacks.{u, w} B S hS}
  (g : schemeStack.{u, w} B S hS U ⟶ 𝒳) (hg : AlgebraicStacks.IsAffineHom B S hS g)
  {R : Type u} [CommRing R]
  (F : AlgebraicStacks.quasicoherentModules B S hS 𝒳 ⥤ ModuleCat.{u} R) [F.LaxBraided]
  [F.Additive] [PreservesFiniteColimits F] [∀ J : Type u, PreservesColimitsOfShape (Discrete J) F]

/-- **Stacks 0GRK on `QCoh(𝒪_U)` for `U` affine**: `F ∘ g_{QCoh,*}` is
`N ↦ Γ(U, N) ⊗_A C` viewed as an `R`-module. -/
noncomputable def affineTensorFunctorGlobalSectionsIso (hU : IsAffineOver B S hS U) :
    affineQuasicoherentPushforward g hg ⋙ F ≅
      quasicoherentGlobalSections.{u, w} U ⋙ ModuleCat.extendScalars (affineTensorRingHom g hg F) ⋙
        ModuleCat.restrictScalars (algebraMap R (affineTensorAlgebra g hg F)) :=
  (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight (tildeCounitIso U hU).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (quasicoherentGlobalSections.{u, w} U) (affineTensorFunctorIso g hg F)

end Functor

end AlgebraicGeometry.Stack
