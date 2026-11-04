module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalFunctionsOfMapGlobalSectionSets
public import StacksFrontier.AlgebraicGeometry.Spaces.InverseImageStructureSheafMapGlobalSection
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.AlgebraExtensionEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRestrictionModulePullback

/-!
# Inverse images of global functions, restricted along étale morphisms

For a morphism `h : X ⟶ Y` of algebraic spaces and a global section `t` of `𝒪_Y` on underlying
sheaves of sets, write `h^♯t` for the inverse image `h⁻¹t` followed by `h^♯ : h⁻¹𝒪_Y ⟶ 𝒪_X`. This
file records how these global sections behave under composition, how the maps
`(u ≫ h)⁻¹𝒪_Y ⟶ u⁻¹𝒪_X` act on them, and how the restriction of `i⁻¹𝒪_{X'}` along an étale
`a : U ⟶ X` (Stacks 03G8, 03LQ) and the maps of restricted inverse images
`AlgebraicGeometry.Space.etaleRestrictionInverseImageMap` act on inverse images of global
sections. All declarations below are in the namespace `AlgebraicGeometry.Space`.

## Main results

* `globalSectionMap_comp_forget_map_structureSharpInverseImage_comp`: `(u ≫ h)^♯t = u^♯(h^♯t)`.
* `globalSectionMap_unitModuleMul_globalFunctionsOfMap_comp_structureSharpInverseImage`: the
  function `(h ≫ g)^♯a` is `h^♯` of the function `g^♯a`.
* `globalSectionMap_comp_forget_map_etaleRestrictionInverseImageMap`: the map of restricted
  inverse images carries the restricted inverse image of `τ` along `a ≫ i` to that of `φ^♯τ`
  along `a₁ ≫ i₁`.
* `globalSectionMap_comp_forget_map_etaleRestrictionRingComparison_α_hom`: for an étale `a`, the
  inverse image of `τ` along `a ≫ i`, read in `(i⁻¹𝒪_{X'})|_U`, is the restriction along `a` of
  its inverse image along `i`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

attribute [local instance] MorphismOfTopoi.preservesFiniteLimits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {W X Y : AlgebraicSpaces B S hS}

/-- **Inverse images of global sections followed by the structure maps compose**: for
`u : W ⟶ X`, `h : X ⟶ Y` and a global section `t` of `𝒪_Y`, `(u ≫ h)^♯t = u^♯(h^♯t)` on
underlying sheaves of sets. -/
theorem globalSectionMap_comp_forget_map_structureSharpInverseImage_comp (u : W ⟶ X) (h : X ⟶ Y)
    (t : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS Y).O) :
    (smallEtaleRingedToposHom B S hS (u ≫ h)).toToposHom.inverseImage.globalSectionMap t ≫
        (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
          (structureSharpInverseImage B S hS (u ≫ h)) =
      (smallEtaleRingedToposHom B S hS u).toToposHom.inverseImage.globalSectionMap
          ((smallEtaleRingedToposHom B S hS h).toToposHom.inverseImage.globalSectionMap t ≫
            (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
              (structureSharpInverseImage B S hS h)) ≫
        (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
          (structureSharpInverseImage B S hS u) := by
  refine (congrArg (_ ≫ ·) ((congrArg
    (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
      (inverseImageStructureSheafMap_comp_structureSharpInverseImage B S hS u h).symm).trans
    ((sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map_comp _ _))).trans
    ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (globalSectionMap_comp_forget_map_inverseImageStructureSheafMap B S hS
    u h t)

variable {T : BigFppfOver B S hS}

/-- **The global section `g^♯a` on underlying sheaves of sets**, read on the commutative
structure sheaves: for `g : X ⟶ T` and `a ∈ Γ(T, 𝒪_T)`, the unit section followed by
multiplication by `g^♯a` is `g⁻¹a` followed by `g^♯`. -/
theorem ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap_eq (g : X ⟶ schemeSpace T)
    (a : baseRing B S hS T) :
    (ringOneHom (structureRingSheaf B S hS X) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (unitModuleMul B S hS X (globalFunctionsOfMap g a)) :
        ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS X).O) =
      (smallEtaleRingedToposHom B S hS g).toToposHom.inverseImage.globalSectionMap
          (ringOneHom (structureRingSheaf B S hS (schemeSpace T)) ≫
            (moduleSheafFunctor (structureRingSheaf B S hS (schemeSpace T))).map
              (unitModuleMul B S hS (schemeSpace T)
                (globalFunctionsOfMap (𝟙 (schemeSpace T)) a))) ≫
        (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).map
          (structureSharpInverseImage B S hS g) :=
  ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap B S hS g a

/-- **Pulling back a pulled-back function**: for `h : W ⟶ X`, `g : X ⟶ T` and
`a ∈ Γ(T, 𝒪_T)`, `h^♯` of the global section `g^♯a` of `𝒪_X` is the global section
`(h ≫ g)^♯a` of `𝒪_W`, on underlying sheaves of sets. -/
theorem globalSectionMap_unitModuleMul_globalFunctionsOfMap_comp_structureSharpInverseImage
    (h : W ⟶ X) (g : X ⟶ schemeSpace T) (a : baseRing B S hS T) :
    (smallEtaleRingedToposHom B S hS h).toToposHom.inverseImage.globalSectionMap
        (ringOneHom (structureRingSheaf B S hS X) ≫
          (moduleSheafFunctor (structureRingSheaf B S hS X)).map
            (unitModuleMul B S hS X (globalFunctionsOfMap g a)) :
          ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS X.1) (forget CommRingCat.{u})).obj
            (smallEtaleRingedTopos B S hS X).O) ≫
        (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
          (structureSharpInverseImage B S hS h) =
      ringOneHom (structureRingSheaf B S hS W) ≫
        (moduleSheafFunctor (structureRingSheaf B S hS W)).map
          (unitModuleMul B S hS W (globalFunctionsOfMap (h ≫ g) a)) := by
  refine (congrArg (fun t =>
      (smallEtaleRingedToposHom B S hS h).toToposHom.inverseImage.globalSectionMap t ≫
        (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
          (structureSharpInverseImage B S hS h))
    (ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap_eq B S hS g a)).trans ?_
  refine (globalSectionMap_comp_forget_map_structureSharpInverseImage_comp B S hS h g
    _).symm.trans ?_
  exact (ringOneHom_comp_map_unitModuleMul_globalFunctionsOfMap_eq B S hS (h ≫ g) a).symm

/-- The inverse image of a global section along `u₁` is that along `u₂ = u₁`, through the
identification `u₂⁻¹𝒪 = u₁⁻¹𝒪`. -/
theorem globalSectionMap_comp_forget_map_eqToHom_inverseImageStructureSheaf {u₁ u₂ : W ⟶ Y}
    (h : u₁ = u₂)
    (t : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS Y.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS Y).O) :
    (smallEtaleRingedToposHom B S hS u₁).toToposHom.inverseImage.globalSectionMap t ≫
        (sheafCompose (SmallEtale.topology B S hS W.1) (forget CommRingCat.{u})).map
          (eqToHom (congrArg (inverseImageStructureSheaf B S hS) h)) =
      (smallEtaleRingedToposHom B S hS u₂).toToposHom.inverseImage.globalSectionMap t := by
  subst h
  exact (congrArg (_ ≫ ·) ((sheafCompose (SmallEtale.topology B S hS W.1)
    (forget CommRingCat.{u})).map_id _)).trans (Category.comp_id _)

/-- Changing the base map along an equality does not change the inclusion of the ideal, on
sections. -/
theorem castBase_incl {Y : AlgebraicSpaces B S hS} {f f' : W ⟶ Y} (h : f = f')
    {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS W.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS W).O)}
    (P : Deformation.AlgebraExtension (J := SmallEtale.topology B S hS W.1)
      (structureSharpInverseImage B S hS f) M) {V : (SmallEtale B S hS W.1)ᵒᵖ} (m : M.val.obj V) :
    (castBase B S hS h P).incl m = P.incl m := by
  subst h
  rfl

section InverseImageMap

variable {U X' X₁ X'₁ : AlgebraicSpaces B S hS} (a : U ⟶ X) (ha : IsEtale B S hS a.hom)
  (i : X ⟶ X') (a₁ : U ⟶ X₁) (ha₁ : IsEtale B S hS a₁.hom) (i₁ : X₁ ⟶ X'₁) (φ : X'₁ ⟶ X')
  (tri : (a₁ ≫ i₁) ≫ φ = a ≫ i)

/-- **The map of restricted inverse images on inverse images of global sections**: a global
section `τ` of `𝒪_{X'}`, pulled back along `a ≫ i` and read in the restriction of `i⁻¹𝒪_{X'}`
along `a`, is carried by `AlgebraicGeometry.Space.etaleRestrictionInverseImageMap` to the global
section `φ^♯τ` of `𝒪_{X'₁}`, pulled back along `a₁ ≫ i₁` and read in the restriction of
`i₁⁻¹𝒪_{X'₁}` along `a₁`, on underlying sheaves of sets. -/
theorem globalSectionMap_comp_forget_map_etaleRestrictionInverseImageMap
    (τ : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS X'.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X').O) :
    (smallEtaleRingedToposHom B S hS (a ≫ i)).toToposHom.inverseImage.globalSectionMap τ ≫
        (sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).map
          ((etaleRestrictionRingComparison B S hS a ha i).α.hom ≫
            etaleRestrictionInverseImageMap B S hS a ha i a₁ ha₁ i₁ φ tri) =
      (smallEtaleRingedToposHom B S hS (a₁ ≫ i₁)).toToposHom.inverseImage.globalSectionMap
          ((smallEtaleRingedToposHom B S hS φ).toToposHom.inverseImage.globalSectionMap τ ≫
            (sheafCompose (SmallEtale.topology B S hS X'₁.1) (forget CommRingCat.{u})).map
              (structureSharpInverseImage B S hS φ)) ≫
        (sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).map
          (etaleRestrictionRingComparison B S hS a₁ ha₁ i₁).α.hom := by
  have hm : (etaleRestrictionRingComparison B S hS a ha i).α.hom ≫
      etaleRestrictionInverseImageMap B S hS a ha i a₁ ha₁ i₁ φ tri =
      eqToHom (congrArg (inverseImageStructureSheaf B S hS) tri.symm) ≫
        inverseImageStructureSheafMap B S hS (a₁ ≫ i₁) φ ≫
          (etaleRestrictionRingComparison B S hS a₁ ha₁ i₁).α.hom := by
    unfold etaleRestrictionInverseImageMap inverseImageStructureSheafMapOfEq
    simp only [Iso.hom_inv_id_assoc, Category.assoc]
  refine (congrArg (fun m => _ ≫ (sheafCompose (SmallEtale.topology B S hS U.1)
    (forget CommRingCat.{u})).map m) hm).trans ?_
  simp only [Functor.map_comp]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (globalSectionMap_comp_forget_map_eqToHom_inverseImageStructureSheaf
    B S hS tri.symm τ)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (· ≫ _) (globalSectionMap_comp_forget_map_inverseImageStructureSheafMap B S hS
    (a₁ ≫ i₁) φ τ)

end InverseImageMap

/-- An `eqToHom` of sheaves of modules acts on sections by the cast along the equality. -/
theorem eqToHom_val_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {A A' : SheafOfModules.{u} R} (H : A = A') (V : Cᵒᵖ)
    (y : A.val.obj V) :
    (eqToHom H).val.app V y =
      cast (congrArg (fun N : SheafOfModules.{u} R => (N.val.obj V : Type u)) H) y := by
  subst H
  rfl

section Restriction

variable {U X' : AlgebraicSpaces B S hS} (a : U ⟶ X) (ha : IsEtale B S hS a.hom) (i : X ⟶ X')

/-- The inverse image along an étale `a` of a global section of sheaves of sets is its
restriction along `a`, through the comparison of Stacks 03LQ. -/
theorem globalSectionMap_comp_smallToposMorphismTypeU_inverseImageIso_hom_app
    {F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (σ : ⊤_ _ ⟶ F) :
    (smallEtaleRingedToposHom B S hS a).toToposHom.inverseImage.globalSectionMap σ ≫
        (smallToposMorphismTypeU_inverseImageIso B S hS a ha).hom.app F =
      (smallEtaleSetRestriction B S hS a ha).globalSectionMap σ :=
  Functor.globalSectionMap_comp_app _ σ

/-- The comparison `(a ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_U` on underlying sheaves of sets: the
composition law of inverse images followed by the comparison of Stacks 03LQ. -/
theorem forget_map_etaleRestrictionRingComparison_α_hom :
    (sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).map
      (etaleRestrictionRingComparison B S hS a ha i).α.hom =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS a i).inv.app _ ≫
        (smallToposMorphismTypeU_inverseImageIso B S hS a ha).hom.app _ := by
  have hc : (sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).map
      ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS a i).inv.app
        (smallEtaleRingedTopos B S hS X').O) =
      (smallEtaleRingedToposHom_compInverseImageIso B S hS a i).inv.app _ := by
    rw [smallEtaleRingedToposHom_compInverseImageRingIso, Iso.trans_inv, NatTrans.comp_app,
      Functor.map_comp]
    exact (congrArg (_ ≫ ·)
      (Stacks.Sheaves.ToposPushforward.forget_map_inverseImageCommRingComp_inv
        (smallEtaleRingedToposHom B S hS i).toToposHom
        (smallEtaleRingedToposHom B S hS a).toToposHom
        (smallEtaleRingedTopos B S hS X').O)).trans (Category.comp_id _)
  have hr := Stacks.Sheaves.ToposPullback.inverseImageCommRingRestrictionIso_hom_forget
    (SmallEtale.topology B S hS U.1) (SmallEtale.topology B S hS X.1)
    (smallEtalePostcomp B S hS a ha) (smallEtaleRingedToposHom B S hS a).toToposHom
    (smallToposMorphismTypeU_inverseImageIso B S hS a ha) (inverseImageStructureSheaf B S hS i)
  exact ((sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).map_comp
    _ _).trans ((congrArg (· ≫ _) hc).trans (congrArg (_ ≫ ·) hr))

/-- **The restricted inverse image of a global section**: a global section `τ` of `𝒪_{X'}`,
pulled back along `a ≫ i` (`a` étale) and read through `(a ≫ i)⁻¹𝒪_{X'} ≅ (i⁻¹𝒪_{X'})|_U`
(Stacks 03G8, 03LQ), is the restriction along `a` of the inverse image of `τ` along `i`, on
underlying sheaves of sets. -/
theorem globalSectionMap_comp_forget_map_etaleRestrictionRingComparison_α_hom
    (τ : ⊤_ _ ⟶ (sheafCompose (SmallEtale.topology B S hS X'.1) (forget CommRingCat.{u})).obj
      (smallEtaleRingedTopos B S hS X').O) :
    (smallEtaleRingedToposHom B S hS (a ≫ i)).toToposHom.inverseImage.globalSectionMap τ ≫
        (sheafCompose (SmallEtale.topology B S hS U.1) (forget CommRingCat.{u})).map
          (etaleRestrictionRingComparison B S hS a ha i).α.hom =
      (smallEtaleSetRestriction B S hS a ha).globalSectionMap
        ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.globalSectionMap τ) := by
  have hm := forget_map_etaleRestrictionRingComparison_α_hom B S hS a ha i
  have h1 := Functor.globalSectionMap_comp_inv_app
    (F := (smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage)
    (G := (smallEtaleRingedToposHom B S hS a).toToposHom.inverseImage)
    (smallEtaleRingedToposHom_compInverseImageIso B S hS a i) τ
  have h2 := globalSectionMap_comp_smallToposMorphismTypeU_inverseImageIso_hom_app B S hS a ha
    ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.globalSectionMap τ)
  have h12 := (congrArg (· ≫ (smallToposMorphismTypeU_inverseImageIso B S hS a ha).hom.app
      ((smallEtaleRingedToposHom B S hS i).toToposHom.inverseImage.obj
        ((sheafCompose (SmallEtale.topology B S hS X'.1) (forget CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS X').O))) h1).trans h2
  have hY := congrArg
    ((smallEtaleRingedToposHom B S hS (a ≫ i)).toToposHom.inverseImage.globalSectionMap τ ≫ ·) hm
  exact hY.trans ((Category.assoc _ _ _).symm.trans h12)

/-- **The pullback of a global section along an étale morphism is its restriction**: for an
étale `a : U ⟶ X` and a global section `s : 𝒪_X ⟶ M`, the pulled-back section `a^*s`, read in
the étale restriction of `M` through Stacks 03LW, is the restriction of `s`. -/
theorem modulePullbackGlobalSection_comp_modulePullbackIsoEtaleModulePullback_hom_app
    {M : Modules.{u, u} B S hS X.1 X.2}
    (s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ M) :
    modulePullbackGlobalSection B S hS a s ≫
        (modulePullbackIsoEtaleModulePullback B S hS a ha).hom.app M =
      (etaleModulePullback.{u, u} B S hS a ha).map s := by
  have hn := (modulePullbackIsoEtaleModulePullback B S hS a ha).hom.naturality s
  have hu := modulePullbackIsoEtaleModulePullback_hom_app_unit B S hS a ha
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hn).trans ?_
  refine (congrArg (fun m => (modulePullbackUnitIso B S hS a).inv ≫ m ≫
    (etaleModulePullback.{u, u} B S hS a ha).map s) hu).trans ?_
  exact (Iso.inv_hom_id_assoc _ _)

/-- **The pullback of a global section along an étale morphism, on sections**: the value at `1`
over a chart `V` of `U` of the pulled-back section `a^*s`, read in the étale restriction of `M`, is
the value at `1` of `s` over the composite chart `V ⟶ U ⟶ X`. -/
theorem modulePullbackGlobalSection_comp_modulePullbackIsoEtaleRestrictionModule_hom_val_app_one
    {M : Modules.{u, u} B S hS X.1 X.2} (s : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ M)
    (V : (SmallEtale B S hS U.1)ᵒᵖ) :
    (modulePullbackGlobalSection B S hS a s ≫
        (modulePullbackIsoEtaleRestrictionModule B S hS a ha).hom.app M).val.app V
        (1 : (structureRingSheaf B S hS U).obj.obj V) =
      s.val.app ((smallEtalePostcomp B S hS a ha).op.obj V)
        (1 : (structureRingSheaf B S hS X).obj.obj
          ((smallEtalePostcomp B S hS a ha).op.obj V)) := by
  have h :=
    modulePullbackGlobalSection_comp_modulePullbackIsoEtaleModulePullback_hom_app B S hS a ha s
  have h2 : modulePullbackGlobalSection B S hS a s ≫
      (modulePullbackIsoEtaleRestrictionModule B S hS a ha).hom.app M =
      (modulePullbackGlobalSection B S hS a s ≫
        (modulePullbackIsoEtaleModulePullback B S hS a ha).hom.app M) ≫
        eqToHom (Functor.congr_obj
          (etaleRestrictionModule_eq_etaleModulePullback B S hS a ha).symm M) :=
    (congrArg (_ ≫ ·) ((NatTrans.comp_app _ _ M).trans (congrArg (_ ≫ ·)
      (eqToHom_app (etaleRestrictionModule_eq_etaleModulePullback B S hS a ha).symm M)))).trans
      (Category.assoc _ _ _).symm
  refine (congrArg (fun m => m.val.app V (1 : (structureRingSheaf B S hS U).obj.obj V))
    (h2.trans (congrArg (· ≫ _) h))).trans ?_
  refine (SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine (eqToHom_val_app_apply _ _ _).trans ?_
  exact cast_eq _ _

/-- The restriction along an étale `a` of a global section of sheaves of sets, on a section over a
chart `V` of `U`: the value over the composite chart `V ⟶ U ⟶ X`. -/
theorem sectionsFunctor_map_globalSectionMap_smallEtaleSetRestriction
    {F : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (σ : ⊤_ _ ⟶ F)
    (V : (SmallEtale B S hS U.1)ᵒᵖ)
    (p : (sectionsFunctor _ V).obj (⊤_ Sheaf (SmallEtale.topology B S hS U.1) (Type u))) :
    (sectionsFunctor _ V).map ((smallEtaleSetRestriction B S hS a ha).globalSectionMap σ) p =
      (sectionsFunctor _ ((smallEtalePostcomp B S hS a ha).op.obj V)).map σ
        ((sectionsFunctor _ V).map (CategoryTheory.inv (terminalComparison
          (smallEtaleSetRestriction B S hS a ha))) p) :=
  rfl

/-- The inclusion of the ideal of an extension restricted along an étale `a` is the inclusion of
the ideal of the extension over the composite chart, sections being unchanged. -/
theorem etaleRestrictionFunctor_obj_incl {Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {M : SheafOfModules.{u} ((sheafCompose (SmallEtale.topology B S hS X.1)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O)}
    (P : Deformation.AlgebraExtension (J := SmallEtale.topology B S hS X.1)
      (structureSharpInverseImage B S hS f) M) {V : (SmallEtale B S hS U.1)ᵒᵖ}
    (m : ((etaleRestrictionModule B S hS a ha).obj M).val.obj V) :
    ((etaleRestrictionFunctor B S hS a ha f M).obj P).incl m =
      P.incl (U := (smallEtalePostcomp B S hS a ha).op.obj V) m :=
  rfl

end Restriction

end AlgebraicGeometry.Space

end
