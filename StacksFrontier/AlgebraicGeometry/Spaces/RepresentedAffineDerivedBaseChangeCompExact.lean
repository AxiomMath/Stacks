module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitCorepresentable
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsCompCancel

/-!
# Exact composition of affine base change isomorphisms

The affine pullback isomorphisms `g^*(M^~) ≅ (R' ⊗_R M)^~` are normalized at `M = R` by the
identification `g^*𝒪 ≅ 𝒪` of Stacks 03LU. This file proves the ingredients of their exact
composition law: that identification, built by corepresentability, is compatible with the
composition law of inverse images of modules, and a path of normalized edges is normalized. The two
module-level paths around a commutative square of affines are then equal, and the derived base
change isomorphisms compose exactly around the square.

## Main results

* `MorphismOfTopoi.pushforwardTerminalHomEquiv_comp_app`: global sections of a direct image do not
  see a comparison of direct images.
* `MorphismOfTopoi.comp_pushforwardTerminalHomEquiv`: global sections of the direct image along a
  composite are read twice.
* `CategoryTheory.Adjunction.unit_comp_leftAdjointCompIso`: corepresented units compose.
* `AlgebraicGeometry.Space.pullbackModulesObjUnitIso_hom_comp_smallEtaleModulePullbackCompIso`:
  the identification `𝒪_X ≅ f^*𝒪_Y` is compatible with the composition law of pullbacks.
* `Stacks.Homology.pathNatTrans_app_self_comp`: a path of edges normalized at the unit is the
  trivialization at the unit.
* `AlgebraicGeometry.Space.representedAffineToposPullbackIso_hom_app_self`: the affine pullback
  isomorphism at the ring is the trivialization, in the ringed-topos spelling.
* `AlgebraicGeometry.RingedToposHom.pathNatTrans_app_self`: a path of pullback edges of ringed
  topoi normalized at the unit is the trivialization through `1 ≅ h^*1`.
* `AlgebraicGeometry.Space.representedAffinePathLeft_eq_pathRight`: the two module-level paths
  around a commutative square of affines agree.
* `AlgebraicGeometry.Space.representedAffineToposDerivedBaseChange_compat`: the derived affine base
  change isomorphisms compose exactly around a commutative square of affines.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' w'' v u v' u' v'' u''

namespace MorphismOfTopoi

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  {D' : Type u''} [Category.{v''} D'] {K' : GrothendieckTopology D'}

/-- **Global sections of a direct image do not see a comparison of direct images**: for two
morphisms of topoi and any natural transformation `τ` between their direct images,
`pushforwardTerminalHomEquiv` takes `c ≫ τ` to the image of `c`. The terminal sheaf has only one
morphism into the inverse image of the terminal sheaf. -/
theorem pushforwardTerminalHomEquiv_comp_app
    (g₁ g₂ : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (τ : g₁.pushforward ⟶ g₂.pushforward) (E : Sheaf J (Type w))
    (c : ⊤_ (Sheaf K (Type w')) ⟶ g₁.pushforward.obj E) :
    g₂.pushforwardTerminalHomEquiv E (c ≫ τ.app E) = g₁.pushforwardTerminalHomEquiv E c := by
  obtain ⟨σ, rfl⟩ := (conjugateEquiv g₁.adj g₂.adj).surjective τ
  have h : (g₂.adj.homEquiv _ E).symm (c ≫ (conjugateEquiv g₁.adj g₂.adj σ).app E) =
      σ.app _ ≫ (g₁.adj.homEquiv _ E).symm c := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
      Category.assoc, conjugateEquiv_counit, NatTrans.naturality_assoc]
  have hT : IsTerminal (g₁.inverseImage.obj (⊤_ (Sheaf K (Type w')))) :=
    terminalIsTerminal.ofIso (inverseImageTerminalIso g₁).symm
  change (inverseImageTerminalIso g₂).inv ≫ (g₂.adj.homEquiv _ E).symm (c ≫ _) =
    (inverseImageTerminalIso g₁).inv ≫ (g₁.adj.homEquiv _ E).symm c
  rw [h, ← Category.assoc, hT.hom_ext ((inverseImageTerminalIso g₂).inv ≫ σ.app _)
    (inverseImageTerminalIso g₁).inv]

/-- **Global sections of the direct image along a composite of morphisms of topoi** are read in
two steps. -/
theorem comp_pushforwardTerminalHomEquiv
    (g : MorphismOfTopoi (Sheaf K (Type w')) (Sheaf K' (Type w'')))
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w'))) (E : Sheaf J (Type w))
    (c : ⊤_ (Sheaf K' (Type w'')) ⟶ g.pushforward.obj (f.pushforward.obj E)) :
    (g.comp f).pushforwardTerminalHomEquiv E c =
      f.pushforwardTerminalHomEquiv E (g.pushforwardTerminalHomEquiv _ c) := by
  have hT : IsTerminal (f.inverseImage.obj (g.inverseImage.obj (⊤_ (Sheaf K' (Type w''))))) :=
    terminalIsTerminal.ofIso (f.inverseImage.mapIso (inverseImageTerminalIso g) ≪≫
      inverseImageTerminalIso f).symm
  change (inverseImageTerminalIso (g.comp f)).inv ≫ ((g.adj.comp f.adj).homEquiv _ E).symm c =
    (inverseImageTerminalIso f).inv ≫ (f.adj.homEquiv _ E).symm
      ((inverseImageTerminalIso g).inv ≫ (g.adj.homEquiv _ _).symm c)
  rw [Adjunction.comp_homEquiv, Equiv.symm_trans_apply,
    Adjunction.homEquiv_naturality_left_symm, ← Category.assoc]
  congr 1
  exact hT.hom_ext _ _

end MorphismOfTopoi

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R₁) {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁}
  (adj₂ : L₂ ⊣ R₂) {L : C₀ ⥤ C₂} {R : C₂ ⥤ C₀} (adj : L ⊣ R) (e : R₂ ⋙ R₁ ≅ R)

/-- Transposing along `L ⊣ R` is transposing twice, through `leftAdjointCompIso`. -/
theorem homEquiv_eq_leftAdjointCompIso {X : C₀} {Y : C₂} (q : L.obj X ⟶ Y) :
    adj.homEquiv X Y q = adj₁.homEquiv X _ (adj₂.homEquiv _ Y
      ((leftAdjointCompIso adj₁ adj₂ adj e).hom.app X ≫ q)) ≫ e.hom.app Y := by
  rw [← Equiv.eq_symm_apply]
  have h₂ : (leftAdjointCompIso adj₁ adj₂ adj e).inv.app X ≫
      ((adj₁.comp adj₂).homEquiv X Y).symm (adj₁.homEquiv X _ (adj₂.homEquiv _ Y
        ((leftAdjointCompIso adj₁ adj₂ adj e).hom.app X ≫ q))) =
      (adj.homEquiv X Y).symm (adj₁.homEquiv X _ (adj₂.homEquiv _ Y
        ((leftAdjointCompIso adj₁ adj₂ adj e).hom.app X ≫ q)) ≫
        (conjugateEquiv (adj₁.comp adj₂) adj (leftAdjointCompIso adj₁ adj₂ adj e).inv).app Y) := by
    rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_comp,
      Category.assoc, conjugateEquiv_counit]
    exact (NatTrans.naturality_assoc _ _ _).symm
  rw [conjugateEquiv_leftAdjointCompIso_inv] at h₂
  rw [← h₂, comp_homEquiv, Equiv.symm_trans_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply, Iso.inv_hom_id_app_assoc]

/-- **Corepresented units compose.** Let `μ₁ : 1₁ ⟶ L₁ 1₀`, `μ₂ : 1₂ ⟶ L₂ 1₁` and
`μ : 1₂ ⟶ L 1₀` be characterized by their composites through bijections `Θ₁`, `Θ₂`, `Θ` with
morphisms out of the units, and suppose `Θ` is `Θ₂ ∘ Θ₁` through `e`. Then `μ` is the composite of
`μ₂`, `L₂ μ₁` and `leftAdjointCompIso`. -/
theorem unit_comp_leftAdjointCompIso {u₀ : C₀} {u₁ : C₁} {u₂ : C₂}
    (Θ₁ : ∀ N : C₁, (u₀ ⟶ R₁.obj N) ≃ (u₁ ⟶ N)) (Θ₂ : ∀ N : C₂, (u₁ ⟶ R₂.obj N) ≃ (u₂ ⟶ N))
    (Θ : ∀ N : C₂, (u₀ ⟶ R.obj N) ≃ (u₂ ⟶ N))
    (μ₁ : u₁ ⟶ L₁.obj u₀) (μ₂ : u₂ ⟶ L₂.obj u₁) (μ : u₂ ⟶ L.obj u₀)
    (hμ₁ : ∀ {N} (q : L₁.obj u₀ ⟶ N), μ₁ ≫ q = Θ₁ N (adj₁.homEquiv _ _ q))
    (hμ₂ : ∀ {N} (q : L₂.obj u₁ ⟶ N), μ₂ ≫ q = Θ₂ N (adj₂.homEquiv _ _ q))
    (hμ : ∀ {N} (q : L.obj u₀ ⟶ N), μ ≫ q = Θ N (adj.homEquiv _ _ q))
    (htrans : ∀ N (x : u₀ ⟶ R₁.obj (R₂.obj N)),
      Θ N (x ≫ e.hom.app N) = Θ₂ N (Θ₁ (R₂.obj N) x)) :
    μ = μ₂ ≫ L₂.map μ₁ ≫ (leftAdjointCompIso adj₁ adj₂ adj e).hom.app u₀ := by
  have h := homEquiv_eq_leftAdjointCompIso adj₁ adj₂ adj e (𝟙 (L.obj u₀))
  rw [Category.comp_id] at h
  rw [hμ₂, adj₂.homEquiv_naturality_left, hμ₁, ← htrans, ← h, ← hμ, Category.comp_id]

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.RingedToposModules CategoryTheory.Sheaf

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]

/-- Morphisms from `1_{O_D}` into the direct image of an `O_C`-module `N` are morphisms from
`1_{O_C}` into `N`: both are the global sections of the underlying sheaf of sets of `N`. -/
def unitPushforwardHomEquiv (f : RingedToposHom X Y)
    (N : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))) :
    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) ⟶
      (pushforwardModules f).obj N) ≃
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) ⟶ N) :=
  (unitTerminalHomEquiv _ _).trans
    ((f.toToposHom.pushforwardTerminalHomEquiv _).trans (unitTerminalHomEquiv _ N).symm)

/-- `unitPushforwardHomEquiv f N` sends a morphism `x` to the morphism corresponding to the image
of the global section `x` under the identification of global sections of `f_* N` with those of `N`.
-/
theorem unitPushforwardHomEquiv_apply (f : RingedToposHom X Y)
    (N : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (x : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O)) ⟶
      (pushforwardModules f).obj N) :
    unitPushforwardHomEquiv f N x = (unitTerminalHomEquiv _ N).symm
      (f.toToposHom.pushforwardTerminalHomEquiv _ (unitTerminalHomEquiv _ _ x)) :=
  rfl

variable [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The identification `1_{O_C} ≅ f^*1_{O_D}` is characterized by its composites, through
`unitPushforwardHomEquiv` and the adjunction of Stacks 03D7. -/
theorem pullbackModulesObjUnitIso_hom_comp_eq (f : RingedToposHom X Y)
    {N : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))}
    (q : (f.toModulesHom.pullbackModules).obj
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))) ⟶ N) :
    (pullbackModulesObjUnitIso f.toModulesHom).hom ≫ q =
      unitPushforwardHomEquiv f N ((pullbackAdjPushforwardModules f).homEquiv _ _ q) := by
  have h : (pullbackAdjPushforwardModules f).homEquiv _ N q =
      (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules f.toModulesHom).homEquiv
        _ N q ≫ (f.toModulesPushforwardIsoApp N).hom :=
    Adjunction.homEquiv_ofNatIsoRight_apply _ _ _
  refine (pullbackModulesObjUnitIso_hom_comp f.toModulesHom N q).trans ?_
  have h' : (moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J) Y.O))).map
      (f.toModulesPushforwardIsoApp N).hom =
        𝟙 (f.toToposHom.pushforward.obj
          (moduleSheaf ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)) N)) :=
    moduleSheafFunctor_map_ofSheafHom _ _ _
  rw [h, unitPushforwardHomEquiv_apply, unitTerminalHomEquiv_comp, h']
  exact congrArg (fun c => (unitTerminalHomEquiv _ N).symm
    (f.toToposHom.pushforwardTerminalHomEquiv _ c)) (Category.comp_id _).symm

variable [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

omit [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}] in
/-- `unitPushforwardHomEquiv` along `h` is read in two steps along `f` and `g`, for any
comparison `π : f_* ⋙ g_* ≅ h_*` of direct images of modules which is, on underlying sheaves of
sets, a natural transformation between the direct images of the morphisms of topoi. -/
theorem unitPushforwardHomEquiv_comp (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (h : RingedToposHom X Z)
    (π : pushforwardModules f ⋙ pushforwardModules g ≅ pushforwardModules h)
    (τ : (g.toToposHom.comp f.toToposHom).pushforward ⟶ h.toToposHom.pushforward)
    (hπ : ∀ N, (moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
      (π.hom.app N) =
      τ.app ((moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).obj N))
    (N : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O)))
    (x : SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O)) ⟶
      (pushforwardModules g).obj ((pushforwardModules f).obj N)) :
    unitPushforwardHomEquiv h N (x ≫ π.hom.app N) =
      unitPushforwardHomEquiv f N (unitPushforwardHomEquiv g _ x) := by
  rw [unitPushforwardHomEquiv_apply, unitPushforwardHomEquiv_apply, unitPushforwardHomEquiv_apply,
    Equiv.apply_symm_apply, unitTerminalHomEquiv_comp, hπ]
  exact congrArg (unitTerminalHomEquiv _ N).symm
    ((MorphismOfTopoi.pushforwardTerminalHomEquiv_comp_app _ _ τ _ _).trans
      (MorphismOfTopoi.comp_pushforwardTerminalHomEquiv _ _ _ _))

/-- **The identification `1 ≅ f^*1` is compatible with composition**: for a comparison
`π : f_* ⋙ g_* ≅ h_*` of direct images of modules induced on underlying sheaves by a natural
transformation of the direct images of topoi, the identification for `h` is the one for `f`,
then `f^*` of the one for `g`, then the composition law of pullbacks adjoint to `π`. -/
theorem pullbackModulesObjUnitIso_hom_comp_leftAdjointCompIso (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) (h : RingedToposHom X Z)
    (π : pushforwardModules f ⋙ pushforwardModules g ≅ pushforwardModules h)
    (τ : (g.toToposHom.comp f.toToposHom).pushforward ⟶ h.toToposHom.pushforward)
    (hπ : ∀ N, (moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
      (π.hom.app N) =
      τ.app ((moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).obj N)) :
    (pullbackModulesObjUnitIso h.toModulesHom).hom =
      (pullbackModulesObjUnitIso f.toModulesHom).hom ≫
        (f.toModulesHom.pullbackModules).map (pullbackModulesObjUnitIso g.toModulesHom).hom ≫
        (Adjunction.leftAdjointCompIso (pullbackAdjPushforwardModules g)
          (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules h) π).hom.app _ :=
  Adjunction.unit_comp_leftAdjointCompIso _ _ _ π (fun N => unitPushforwardHomEquiv g N)
    (fun N => unitPushforwardHomEquiv f N) (fun N => unitPushforwardHomEquiv h N) _ _ _
    (pullbackModulesObjUnitIso_hom_comp_eq g) (pullbackModulesObjUnitIso_hom_comp_eq f)
    (pullbackModulesObjUnitIso_hom_comp_eq h) (unitPushforwardHomEquiv_comp f g h π τ hπ)

/-- `pullbackModulesObjUnitIso_hom_comp_leftAdjointCompIso` for any composition law `κ` of
pullbacks equal to the one adjoint to `π`. -/
theorem pullbackModulesObjUnitIso_hom_comp_of_eq (f : RingedToposHom X Y)
    (g : RingedToposHom Y Z) (h : RingedToposHom X Z)
    (π : pushforwardModules f ⋙ pushforwardModules g ≅ pushforwardModules h)
    (τ : (g.toToposHom.comp f.toToposHom).pushforward ⟶ h.toToposHom.pushforward)
    (hπ : ∀ N, (moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
      (π.hom.app N) =
      τ.app ((moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).obj N))
    (κ : g.toModulesHom.pullbackModules ⋙ f.toModulesHom.pullbackModules ≅
      h.toModulesHom.pullbackModules)
    (hκ : κ = Adjunction.leftAdjointCompIso (pullbackAdjPushforwardModules g)
          (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules h) π) :
    (pullbackModulesObjUnitIso h.toModulesHom).hom =
      (pullbackModulesObjUnitIso f.toModulesHom).hom ≫
        (f.toModulesHom.pullbackModules).map (pullbackModulesObjUnitIso g.toModulesHom).hom ≫
        κ.hom.app _ := by
  subst hκ
  exact pullbackModulesObjUnitIso_hom_comp_leftAdjointCompIso f g h π τ hπ

end AlgebraicGeometry.RingedToposHom

namespace Stacks.Homology

open scoped ChangeOfRings

section UnitPath

variable {A₀ A₁ A₂ : Type u} [CommRing A₀] [CommRing A₁] [CommRing A₂]

/-- On `A₀`, the composition law of extension of scalars is the identity through
`A₂ ⊗_{A₁} A₁ = A₂` and `A₁ ⊗_{A₀} A₀ = A₁`. -/
theorem objSelfIso_inv_comp_extendScalarsCompInvOfEq (φ₁ : A₀ →+* A₁) (φ₂ : A₁ →+* A₂)
    (φc : A₀ →+* A₂) (h : φ₂.comp φ₁ = φc) :
    (ModuleCat.ExtendScalars.objSelfIso φ₂).inv ≫
        (ModuleCat.extendScalars φ₂).map (ModuleCat.ExtendScalars.objSelfIso φ₁).inv ≫
        (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u} φ₁ φ₂ φc h).app
          (ModuleCat.of A₀ A₀) ≫ (ModuleCat.ExtendScalars.objSelfIso φc).hom = 𝟙 _ := by
  subst h
  have hc :=
    StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp_hom_app_one_tmul.{u, u, u, u}
      φ₁ φ₂ (ModuleCat.of A₀ A₀) (1 : A₀)
  have hinv : (StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
      φ₁ φ₂).inv.app (ModuleCat.of A₀ A₀) ((1 : A₂) ⊗ₜ[A₁, φ₂]
        (show (ModuleCat.extendScalars.{u, u, u} φ₁).obj (ModuleCat.of A₀ A₀) from
          (1 : A₁) ⊗ₜ[A₀, φ₁] (1 : A₀))) = (1 : A₂) ⊗ₜ[A₀, φ₂.comp φ₁] (1 : A₀) :=
    (congrArg ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
      φ₁ φ₂).inv.app (ModuleCat.of A₀ A₀)).hom hc).symm.trans
      (((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
        φ₁ φ₂).app (ModuleCat.of A₀ A₀)).hom_inv_id_apply _)
  ext
  change (ModuleCat.ExtendScalars.objSelfIso (φ₂.comp φ₁)).hom
    ((StacksDraft.DerivedExtensionScalarsModelComp.extendScalarsComp.{u, u, u, u}
      φ₁ φ₂).inv.app (ModuleCat.of A₀ A₀) ((ModuleCat.extendScalars φ₂).map
        (ModuleCat.ExtendScalars.objSelfIso φ₁).inv
        ((ModuleCat.ExtendScalars.objSelfIso φ₂).inv 1))) = 1
  have h₁ : (ModuleCat.extendScalars φ₂).map (ModuleCat.ExtendScalars.objSelfIso φ₁).inv
      ((ModuleCat.ExtendScalars.objSelfIso φ₂).inv 1) = (1 : A₂) ⊗ₜ[A₁, φ₂]
        (show (ModuleCat.extendScalars.{u, u, u} φ₁).obj (ModuleCat.of A₀ A₀) from
          (1 : A₁) ⊗ₜ[A₀, φ₁] (1 : A₀)) := rfl
  rw [h₁]
  refine (congrArg (ModuleCat.ExtendScalars.objSelfIso (φ₂.comp φ₁)).hom.hom hinv).trans ?_
  exact (ModuleCat.ExtendScalars.objSelfIso_hom_tmul (φ₂.comp φ₁) (1 : A₂) (1 : A₀)).trans
    (by rw [map_one, mul_one])

variable (φ₁ : A₀ →+* A₁) (φ₂ : A₁ →+* A₂) (φc : A₀ →+* A₂)
  {N₀ N₁ N₂ : Type*} [Category* N₀] [Category* N₁] [Category* N₂]
  {F₀ : ModuleCat.{u} A₀ ⥤ N₀} {F₁ : ModuleCat.{u} A₁ ⥤ N₁} {F₂ : ModuleCat.{u} A₂ ⥤ N₂}
  {q₁ : N₀ ⥤ N₁} {q₂ : N₁ ⥤ N₂} {H : N₀ ⥤ N₂}

/-- **A path of normalized edges, at the unit.** If the two edges `r₁`, `r₂` are the
trivializations `q(ν) ≫ μ⁻¹ ≫ ν⁻¹` at the rings, the composite comparison `μ` is the composite of
the edge ones through `e`, and the composition law `s` of extension of scalars is trivial on the
rings, then the path is the trivialization for `μ`. -/
theorem pathNatTrans_app_self_comp (e : q₁ ⋙ q₂ ≅ H)
    (r₁ : F₀ ⋙ q₁ ≅ ModuleCat.extendScalars.{u, u, u} φ₁ ⋙ F₁)
    (r₂ : F₁ ⋙ q₂ ≅ ModuleCat.extendScalars.{u, u, u} φ₂ ⋙ F₂)
    (s : ModuleCat.extendScalars.{u, u, u} φ₁ ⋙ ModuleCat.extendScalars.{u, u, u} φ₂ ⟶
      ModuleCat.extendScalars.{u, u, u} φc)
    {o₀ : N₀} {o₁ : N₁} {o₂ : N₂} (ν₀ : F₀.obj (ModuleCat.of A₀ A₀) ≅ o₀)
    (ν₁ : F₁.obj (ModuleCat.of A₁ A₁) ≅ o₁) (ν₂ : F₂.obj (ModuleCat.of A₂ A₂) ≅ o₂)
    (μ₁ : o₁ ≅ q₁.obj o₀) (μ₂ : o₂ ≅ q₂.obj o₁) (μ : o₂ ≅ H.obj o₀)
    (hμ : μ.hom = μ₂.hom ≫ q₂.map μ₁.hom ≫ e.hom.app o₀)
    (hr₁ : r₁.hom.app (ModuleCat.of A₀ A₀) ≫ F₁.map (ModuleCat.ExtendScalars.objSelfIso φ₁).hom =
      q₁.map ν₀.hom ≫ μ₁.inv ≫ ν₁.inv)
    (hr₂ : r₂.hom.app (ModuleCat.of A₁ A₁) ≫ F₂.map (ModuleCat.ExtendScalars.objSelfIso φ₂).hom =
      q₂.map ν₁.hom ≫ μ₂.inv ≫ ν₂.inv)
    (hs : (ModuleCat.ExtendScalars.objSelfIso φ₂).inv ≫
        (ModuleCat.extendScalars φ₂).map (ModuleCat.ExtendScalars.objSelfIso φ₁).inv ≫
        s.app (ModuleCat.of A₀ A₀) ≫ (ModuleCat.ExtendScalars.objSelfIso φc).hom = 𝟙 _) :
    (pathNatTrans e r₁ r₂ s).app (ModuleCat.of A₀ A₀) ≫
        F₂.map (ModuleCat.ExtendScalars.objSelfIso φc).hom = H.map ν₀.hom ≫ μ.inv ≫ ν₂.inv := by
  have hr₁' := (Iso.eq_comp_inv (F₁.mapIso (ModuleCat.ExtendScalars.objSelfIso φ₁))).2 hr₁
  have hr₂' := (Iso.eq_comp_inv (F₂.mapIso (ModuleCat.ExtendScalars.objSelfIso φ₂))).2 hr₂
  rw [Functor.mapIso_inv] at hr₁' hr₂'
  have hnat := r₂.hom.naturality (ModuleCat.ExtendScalars.objSelfIso φ₁).inv
  have hμ' : μ.inv = e.inv.app o₀ ≫ q₂.map μ₁.inv ≫ μ₂.inv := by
    rw [← cancel_epi μ.hom, Iso.hom_inv_id, hμ]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← q₂.map_comp_assoc, Iso.hom_inv_id,
      q₂.map_id, Category.id_comp]
  have hs' := congrArg F₂.map hs
  simp only [F₂.map_comp, F₂.map_id] at hs'
  simp only [Functor.comp_map] at hnat
  rw [pathNatTrans_app, hr₁', hμ']
  simp only [Category.assoc, Functor.map_comp]
  rw [reassoc_of% hnat, hr₂']
  simp only [Category.assoc]
  rw [hs', Category.comp_id, ← q₂.map_comp_assoc ν₁.inv, Iso.inv_hom_id, q₂.map_id,
    Category.id_comp]
  have hn := e.inv.naturality ν₀.hom
  simp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

/-- **Transport of a normalized edge along an equality of indices**: if `Q` is normalized at `m`
through the comparisons `μ t'`, then so is `P = (F₀ ◁ eqToHom) ≫ Q`, through `μ t`. -/
theorem app_comp_eq_of_whiskerLeft_eqToHom {M₀ : Type*} [Category* M₀] {T : Type*}
    {Ψ : T → (N₀ ⥤ N₂)} {t t' : T} (h : t = t') {F : M₀ ⥤ N₀} {G : M₀ ⥤ N₂}
    (Q : F ⋙ Ψ t' ⟶ G) (P : F ⋙ Ψ t ⟶ G)
    (hP : P = Functor.whiskerLeft F (eqToHom (congrArg Ψ h)) ≫ Q) (m : M₀) {o : N₀} {o' d : N₂}
    (γ : G.obj m ⟶ d) (ν : F.obj m ≅ o) (μ : ∀ t, (Ψ t).obj o ⟶ o') (x : o' ⟶ d)
    (hQ : Q.app m ≫ γ = (Ψ t').map ν.hom ≫ μ t' ≫ x) :
    P.app m ≫ γ = (Ψ t).map ν.hom ≫ μ t ≫ x := by
  subst hP h
  simpa using hQ

end UnitPath

end Stacks.Homology

namespace AlgebraicGeometry.RingedToposHom

open Stacks.Sheaves.RingedToposModules CategoryTheory.Sheaf

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  {Z : RingedTopos.{v'', u'', w''}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [Z.J.HasSheafCompose (forget RingCat.{w''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w''})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **A path of normalized pullback edges, at the unit**, for morphisms of ringed topoi
`f : X ⟶ Y`, `g : Y ⟶ Z`, `h : X ⟶ Z` whose pullbacks compose through `κ`: if both edges are the
trivializations through `1 ≅ f^*1` and `1 ≅ g^*1` at the rings, the path is the trivialization
through `1 ≅ h^*1`. -/
theorem pathNatTrans_app_self (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (h : RingedToposHom X Z)
    (π : pushforwardModules f ⋙ pushforwardModules g ≅ pushforwardModules h)
    (τ : (g.toToposHom.comp f.toToposHom).pushforward ⟶ h.toToposHom.pushforward)
    (hπ : ∀ N, (moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Z.J) Z.O))).map
      (π.hom.app N) =
      τ.app ((moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J) X.O))).obj N))
    (κ : g.toModulesHom.pullbackModules ⋙ f.toModulesHom.pullbackModules ≅
      h.toModulesHom.pullbackModules)
    (hκ : κ = Adjunction.leftAdjointCompIso (pullbackAdjPushforwardModules g)
          (pullbackAdjPushforwardModules f) (pullbackAdjPushforwardModules h) π)
    {A₀ A₁ A₂ : Type w''} [CommRing A₀] [CommRing A₁] [CommRing A₂]
    (φ₁ : A₀ →+* A₁) (φ₂ : A₁ →+* A₂) (φc : A₀ →+* A₂)
    {F₀ : ModuleCat.{w''} A₀ ⥤ SheafOfModules.{w''} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)}
    {F₁ : ModuleCat.{w''} A₁ ⥤ SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {F₂ : ModuleCat.{w''} A₂ ⥤ SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (r₁ : F₀ ⋙ g.toModulesHom.pullbackModules ≅ ModuleCat.extendScalars.{w'', w'', w''} φ₁ ⋙ F₁)
    (r₂ : F₁ ⋙ f.toModulesHom.pullbackModules ≅ ModuleCat.extendScalars.{w'', w'', w''} φ₂ ⋙ F₂)
    (s : ModuleCat.extendScalars.{w'', w'', w''} φ₁ ⋙ ModuleCat.extendScalars.{w'', w'', w''} φ₂ ⟶
      ModuleCat.extendScalars.{w'', w'', w''} φc)
    (ν₀ : F₀.obj (ModuleCat.of A₀ A₀) ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
    (ν₁ : F₁.obj (ModuleCat.of A₁ A₁) ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ν₂ : F₂.obj (ModuleCat.of A₂ A₂) ≅ SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hr₁ : r₁.hom.app (ModuleCat.of A₀ A₀) ≫ F₁.map (ModuleCat.ExtendScalars.objSelfIso φ₁).hom =
      (g.toModulesHom.pullbackModules).map ν₀.hom ≫ (pullbackModulesObjUnitIso g.toModulesHom).inv ≫
        ν₁.inv)
    (hr₂ : r₂.hom.app (ModuleCat.of A₁ A₁) ≫ F₂.map (ModuleCat.ExtendScalars.objSelfIso φ₂).hom =
      (f.toModulesHom.pullbackModules).map ν₁.hom ≫ (pullbackModulesObjUnitIso f.toModulesHom).inv ≫
        ν₂.inv)
    (hs : (ModuleCat.ExtendScalars.objSelfIso φ₂).inv ≫
        (ModuleCat.extendScalars φ₂).map (ModuleCat.ExtendScalars.objSelfIso φ₁).inv ≫
        s.app (ModuleCat.of A₀ A₀) ≫ (ModuleCat.ExtendScalars.objSelfIso φc).hom = 𝟙 _) :
    (Stacks.Homology.pathNatTrans κ r₁ r₂ s).app (ModuleCat.of A₀ A₀) ≫
        F₂.map (ModuleCat.ExtendScalars.objSelfIso φc).hom =
      (h.toModulesHom.pullbackModules).map ν₀.hom ≫ (pullbackModulesObjUnitIso h.toModulesHom).inv ≫
        ν₂.inv :=
  Stacks.Homology.pathNatTrans_app_self_comp φ₁ φ₂ φc κ r₁ r₂ s ν₀ ν₁ ν₂
    (pullbackModulesObjUnitIso g.toModulesHom) (pullbackModulesObjUnitIso f.toModulesHom)
    (pullbackModulesObjUnitIso h.toModulesHom)
    (pullbackModulesObjUnitIso_hom_comp_of_eq f g h π τ hπ κ hκ) hr₁ hr₂ hs

end AlgebraicGeometry.RingedToposHom


namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules CategoryTheory.Sheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section UnitComp

variable {X Y Z : AlgebraicSpaces B S hS}

/-- **Stacks 03LU, the identification `𝒪_X ≅ f^*𝒪_Y` is compatible with composition**: for
`f : X ⟶ Y` and `g : Y ⟶ Z`, the identification for `f ≫ g` is the one for `f`, then `f^*` of the
one for `g`, then the composition law of pullbacks of modules. -/
theorem pullbackModulesObjUnitIso_hom_comp_smallEtaleModulePullbackCompIso (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS (f ≫ g)).toModulesHom).hom =
      (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS f).toModulesHom).hom ≫
        ((smallEtaleRingedToposHom B S hS f).toModulesHom.pullbackModules).map
          (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS g).toModulesHom).hom ≫
        (smallEtaleModulePullbackCompIso B S hS f g).hom.app _ :=
  RingedToposHom.pullbackModulesObjUnitIso_hom_comp_of_eq
    (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)
    (smallEtaleRingedToposHom B S hS (f ≫ g)) (pushforwardModulesCompAt B S hS f g)
    (smallToposMorphismTypeU_comp B S hS f g).hom
    (fun N => moduleSheafFunctor_map_pushforwardModulesCompAt_hom_app B S hS f g N)
    (smallEtaleModulePullbackCompIso B S hS f g)
    (smallEtaleModulePullbackCompIso_eq_leftAdjointCompIso B S hS f g)

end UnitComp

section PathUnit

/- The sheafification of the small étale sites, found first, so that the categories of modules
below are formed without a search through the other sheafification instances. -/
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]

/-- The associated module of the ring is the structure sheaf, in the ringed-topos spelling. -/
def representedAffineToposObjUnitIso (W : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)] :
    (representedAffineToposAssociated B S hS W).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)) ≅
      SheafOfModules.unit (ringedToposStructureRingSheaf B S hS
        ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩) :=
  representedAffineAssociatedObjUnitIso B S hS W

/-- `AlgebraicGeometry.Space.representedAffineAssociatedPullbackIso_hom_app_self` in the
ringed-topos spelling. -/
theorem representedAffineToposPullbackIso_hom_app_self (g : U' ⟶ V) :
    (representedAffineToposPullbackIso B S hS g).hom.app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ≫
      (representedAffineToposAssociated B S hS U').map
        (ModuleCat.ExtendScalars.objSelfIso (representedAffineCommRingCatHom B S hS g).hom).hom =
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _)
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom).map
          (representedAffineToposObjUnitIso B S hS V).hom ≫
        (pullbackModulesObjUnitIso
          (smallEtaleRingedToposHom B S hS (representedSpaceMap B S hS g)).toModulesHom).inv ≫
        (representedAffineToposObjUnitIso B S hS U').inv :=
  representedAffineAssociatedPullbackIso_hom_app_self B S hS g

/-- **A path of normalized pullback edges, at the unit**, for morphisms `f : X₂ ⟶ X₁` and
`g : X₁ ⟶ X₀` of algebraic spaces: if both edges are the trivializations through `𝒪 ≅ h^*𝒪` at the
rings, so is the path, through the identification for `f ≫ g`. -/
theorem smallEtalePathNatTrans_app_self {X₀ X₁ X₂ : AlgebraicSpaces B S hS} (g : X₁ ⟶ X₀)
    (f : X₂ ⟶ X₁) {A₀ A₁ A₂ : Type u} [CommRing A₀] [CommRing A₁] [CommRing A₂]
    (φ₁ : A₀ →+* A₁) (φ₂ : A₁ →+* A₂) (φc : A₀ →+* A₂)
    {F₀ : ModuleCat.{u} A₀ ⥤
      SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X₀).O))}
    {F₁ : ModuleCat.{u} A₁ ⥤
      SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X₁).O))}
    {F₂ : ModuleCat.{u} A₂ ⥤
      SheafOfModules.{u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X₂).O))}
    (r₁ : F₀ ⋙ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X₁)
        (Y := smallEtaleRingedTopos B S hS X₀) (smallEtaleRingedToposHom B S hS g).toModulesHom ≅
      ModuleCat.extendScalars.{u, u, u} φ₁ ⋙ F₁)
    (r₂ : F₁ ⋙ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X₂)
        (Y := smallEtaleRingedTopos B S hS X₁) (smallEtaleRingedToposHom B S hS f).toModulesHom ≅
      ModuleCat.extendScalars.{u, u, u} φ₂ ⋙ F₂)
    (s : ModuleCat.extendScalars.{u, u, u} φ₁ ⋙ ModuleCat.extendScalars.{u, u, u} φ₂ ⟶
      ModuleCat.extendScalars.{u, u, u} φc)
    (ν₀ : F₀.obj (ModuleCat.of A₀ A₀) ≅
      SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X₀).O)))
    (ν₁ : F₁.obj (ModuleCat.of A₁ A₁) ≅
      SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X₁).O)))
    (ν₂ : F₂.obj (ModuleCat.of A₂ A₂) ≅
      SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X₂).O)))
    (hr₁ : r₁.hom.app (ModuleCat.of A₀ A₀) ≫ F₁.map (ModuleCat.ExtendScalars.objSelfIso φ₁).hom =
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X₁)
        (Y := smallEtaleRingedTopos B S hS X₀)
        (smallEtaleRingedToposHom B S hS g).toModulesHom).map ν₀.hom ≫
        (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS g).toModulesHom).inv ≫ ν₁.inv)
    (hr₂ : r₂.hom.app (ModuleCat.of A₁ A₁) ≫ F₂.map (ModuleCat.ExtendScalars.objSelfIso φ₂).hom =
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X₂)
        (Y := smallEtaleRingedTopos B S hS X₁)
        (smallEtaleRingedToposHom B S hS f).toModulesHom).map ν₁.hom ≫
        (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS f).toModulesHom).inv ≫ ν₂.inv)
    (hs : (ModuleCat.ExtendScalars.objSelfIso φ₂).inv ≫
        (ModuleCat.extendScalars φ₂).map (ModuleCat.ExtendScalars.objSelfIso φ₁).inv ≫
        s.app (ModuleCat.of A₀ A₀) ≫ (ModuleCat.ExtendScalars.objSelfIso φc).hom = 𝟙 _)
    (P : F₀ ⋙ Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X₂)
        (Y := smallEtaleRingedTopos B S hS X₀)
        (smallEtaleRingedToposHom B S hS (f ≫ g)).toModulesHom ⟶
      ModuleCat.extendScalars.{u, u, u} φc ⋙ F₂)
    (hP : P = Stacks.Homology.pathNatTrans (smallEtaleModulePullbackCompIso B S hS f g) r₁ r₂ s) :
    P.app (ModuleCat.of A₀ A₀) ≫ F₂.map (ModuleCat.ExtendScalars.objSelfIso φc).hom =
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS X₂)
        (Y := smallEtaleRingedTopos B S hS X₀)
        (smallEtaleRingedToposHom B S hS (f ≫ g)).toModulesHom).map ν₀.hom ≫
        (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS (f ≫ g)).toModulesHom).inv ≫
        ν₂.inv := by
  subst hP
  refine RingedToposHom.pathNatTrans_app_self (smallEtaleRingedToposHom B S hS f)
    (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS (f ≫ g))
    (pushforwardModulesCompAt B S hS f g) (smallToposMorphismTypeU_comp B S hS f g).hom
    ?_ (smallEtaleModulePullbackCompIso B S hS f g) ?_
    φ₁ φ₂ φc r₁ r₂ s ν₀ ν₁ ν₂ ?_ ?_ ?_
  · exact fun N => moduleSheafFunctor_map_pushforwardModulesCompAt_hom_app B S hS f g N
  · exact smallEtaleModulePullbackCompIso_eq_leftAdjointCompIso B S hS f g
  · exact hr₁
  · exact hr₂
  · exact hs

/-- **The path through `V'` at the ring of `V` is the trivialization.** -/
theorem representedAffinePathLeft_app_self (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') :
    (representedAffinePathLeft B S hS g₀ f₀').app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ≫
      (representedAffineToposAssociated B S hS U').map
        (ModuleCat.ExtendScalars.objSelfIso
          (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom).hom =
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS f₀' ≫ representedSpaceMap B S hS g₀)).toModulesHom).map
          (representedAffineToposObjUnitIso B S hS V).hom ≫
        (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS f₀' ≫ representedSpaceMap B S hS g₀)).toModulesHom).inv ≫
        (representedAffineToposObjUnitIso B S hS U').inv :=
  smallEtalePathNatTrans_app_self B S hS (representedSpaceMap B S hS g₀)
    (representedSpaceMap B S hS f₀') (representedAffineCommRingCatHom B S hS g₀).hom
    (representedAffineCommRingCatHom B S hS f₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
    (representedAffineToposPullbackIso B S hS g₀) (representedAffineToposPullbackIso B S hS f₀')
    (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
      (representedAffineCommRingCatHom B S hS g₀).hom
        (representedAffineCommRingCatHom B S hS f₀').hom
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineRingHom_comp B S hS f₀' g₀).symm)
    (representedAffineToposObjUnitIso B S hS V) (representedAffineToposObjUnitIso B S hS V')
    (representedAffineToposObjUnitIso B S hS U')
    (representedAffineToposPullbackIso_hom_app_self B S hS g₀)
    (representedAffineToposPullbackIso_hom_app_self B S hS f₀')
    (Stacks.Homology.objSelfIso_inv_comp_extendScalarsCompInvOfEq _ _ _ _)
    (representedAffinePathLeft B S hS g₀ f₀') rfl


end PathUnit

section Square

/- The sheafification of the small étale sites, found first, so that the categories of modules
below are formed without a search through the other sheafification instances. -/
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj V')] in
/-- **The path through `U` at the ring of `V` is the trivialization**, through `𝒪 ≅ h^*𝒪` for
the composite `h` of the path through `V'`. -/
theorem representedAffinePathRight_app_self :
    (representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ≫
      (representedAffineToposAssociated B S hS U').map
        (ModuleCat.ExtendScalars.objSelfIso
          (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom).hom =
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS f₀' ≫ representedSpaceMap B S hS g₀)).toModulesHom).map
          (representedAffineToposObjUnitIso B S hS V).hom ≫
        (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS f₀' ≫ representedSpaceMap B S hS g₀)).toModulesHom).inv ≫
        (representedAffineToposObjUnitIso B S hS U').inv :=
  Stacks.Homology.app_comp_eq_of_whiskerLeft_eqToHom
    (Ψ := smallEtaleModulePullbackFamily B S hS _ _)
    (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀).symm
    (Stacks.Homology.pathNatTrans (smallEtaleModulePullbackCompIso B S hS
      (representedSpaceMap B S hS g₀') (representedSpaceMap B S hS f₀))
      (representedAffineToposPullbackIso B S hS f₀)
      (representedAffineToposPullbackIso B S hS g₀')
      (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
        (representedAffineCommRingCatHom B S hS f₀).hom
          (representedAffineCommRingCatHom B S hS g₀').hom
        (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
        (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀)))
    (representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀) rfl _ _
    (representedAffineToposObjUnitIso B S hS V)
    (fun t => (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS t).toModulesHom).inv)
    (representedAffineToposObjUnitIso B S hS U').inv
    (smallEtalePathNatTrans_app_self B S hS (representedSpaceMap B S hS f₀)
      (representedSpaceMap B S hS g₀') (representedAffineCommRingCatHom B S hS f₀).hom
      (representedAffineCommRingCatHom B S hS g₀').hom
        (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
      (representedAffineToposPullbackIso B S hS f₀) (representedAffineToposPullbackIso B S hS g₀')
      (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
        (representedAffineCommRingCatHom B S hS f₀).hom
          (representedAffineCommRingCatHom B S hS g₀').hom
        (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
        (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀))
      (representedAffineToposObjUnitIso B S hS V) (representedAffineToposObjUnitIso B S hS U)
      (representedAffineToposObjUnitIso B S hS U')
      (representedAffineToposPullbackIso_hom_app_self B S hS f₀)
      (representedAffineToposPullbackIso_hom_app_self B S hS g₀')
      (Stacks.Homology.objSelfIso_inv_comp_extendScalarsCompInvOfEq _ _ _ _) _ rfl)

/-- **The two module-level paths around a square of affines agree**: the unit by which they
differ is `1`, as both are the trivialization at the ring. -/
theorem representedAffinePathLeft_eq_pathRight :
    representedAffinePathLeft B S hS g₀ f₀' =
      representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀ := by
  obtain ⟨c, -, hc⟩ := exists_isUnit_representedAffinePath B S hS f₀ g₀ f₀' g₀' w₀
  have hRi : IsIso ((representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _
      (isIso_representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀)
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))
  have h₁ : (representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ≫
      (representedAffineToposAssociated B S hS U').map (c • 𝟙 _) ≫
        (representedAffineToposAssociated B S hS U').map
          (ModuleCat.ExtendScalars.objSelfIso
            (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom).hom =
      (representedAffinePathRight B S hS f₀ g₀ f₀' g₀' w₀).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)) ≫
        (representedAffineToposAssociated B S hS U').map
          (ModuleCat.ExtendScalars.objSelfIso
            (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom).hom :=
    (Category.assoc _ _ _).symm.trans ((eq_whisker (hc _) _).symm.trans
      ((representedAffinePathLeft_app_self B S hS g₀ f₀').trans
        (representedAffinePathRight_app_self B S hS f₀ g₀ f₀' g₀' w₀).symm))
  have h₂ := (@cancel_epi _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ hRi) _ _).1 h₁
  have h₃ : c • 𝟙 ((ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) = 𝟙 _ := by
    refine (Iso.cancel_iso_hom_right _ _
      (ModuleCat.ExtendScalars.objSelfIso
        (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom)).1 ?_
    apply (representedAffineToposAssociatedFullyFaithful B S hS U').map_injective
    rwa [Functor.map_comp, Functor.map_comp, CategoryTheory.Functor.map_id, Category.id_comp]
  have h₄ := ModuleCat.ExtendScalars.eq_one_of_smul_id_eq_id _ h₃
  subst h₄
  refine NatTrans.ext (funext fun M => (hc M).trans ?_)
  rw [one_smul, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end Square

section DerivedSquare

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/- The filtered colimits used to form the étale sheafification, through Mathlib's instance, so that
the categories of `𝒪`-modules below are spelled as in the files of the derived pullback. -/
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

attribute [local instance 6000] preadditive_smallEtaleModules

variable {U V U' V' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj V')]
  (f₀ : U ⟶ V) (g₀ : V' ⟶ V) (f₀' : U' ⟶ V') (g₀' : U' ⟶ U) (w₀ : g₀' ≫ f₀ = f₀' ≫ g₀)

include w₀ in
/-- **The affine base change isomorphisms compose exactly around a square**: the derived base
change isomorphisms `Lg^* Φ_R ≅ Φ_{R'}(- ⊗ᴸ_R R')` along the two sides of a commutative square of
affines agree, through the composition laws of derived pullbacks and of derived extensions of
scalars. -/
theorem representedAffineToposDerivedBaseChange_compat
    (N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))) :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS f₀')).map
          ((representedAffineToposDerivedBaseChangeIso B S hS g₀).hom.app N) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS f₀').hom.app
          ((representedAffineDerivedExtension B S hS g₀).functor.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS g₀).hom
                (representedAffineCommRingCatHom B S hS f₀').hom
              (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
              (representedAffineRingHom_comp B S hS f₀' g₀).symm).hom.app N) =
      (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀)).hom.app
          ((representedAffineToposDerivedAssociated B S hS V).obj N) ≫
        (smallEtaleDerivedModulePullbackSquareIso B S hS (representedSpaceMap B S hS f₀)
          (representedSpaceMap B S hS g₀) (representedSpaceMap B S hS f₀')
          (representedSpaceMap B S hS g₀')
          (representedSpaceMap_square B S hS f₀ g₀ f₀' g₀' w₀)).inv.app
          ((representedAffineToposDerivedAssociated B S hS V).obj N) ≫
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₀')).map
          ((representedAffineToposDerivedBaseChangeIso B S hS f₀).hom.app N) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS g₀').hom.app
          ((representedAffineDerivedExtension B S hS f₀).functor.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U').map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS f₀).hom
                (representedAffineCommRingCatHom B S hS g₀').hom
              (representedAffineCommRingCatHom B S hS (f₀' ≫ g₀)).hom
              (representedAffineRingHom_square B S hS f₀ g₀ f₀' g₀' w₀)).hom.app N) := by
  have h := representedAffineToposDerivedBaseChange_compat_of_path B S hS f₀ g₀ f₀' g₀' w₀ 1
    isUnit_one ?_ N
  swap
  · rw [one_smul, Functor.whiskerRight_id', Category.comp_id]
    exact representedAffinePathLeft_eq_pathRight B S hS f₀ g₀ f₀' g₀' w₀
  have h₁ : (unitCentralIso (1 : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) isUnit_one).hom.app
      ((representedAffineDerivedExtension B S hS (f₀' ≫ g₀)).functor.obj N) = 𝟙 _ := by
    change (1 : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) • 𝟙 _ = _
    exact one_smul _ _
  have h₂ : (representedAffineToposDerivedAssociated B S hS U').map
      ((unitCentralIso (1 : Γ((BigFppfOver.toScheme B S hS).obj U', ⊤)) isUnit_one).hom.app
        ((representedAffineDerivedExtension B S hS (f₀' ≫ g₀)).functor.obj N)) = 𝟙 _ := by
    rw [h₁, CategoryTheory.Functor.map_id]
  rw [h₂] at h
  exact h.trans (congrArg _ (congrArg _ (congrArg _ (congrArg _ (Category.comp_id _)))))

end DerivedSquare


end AlgebraicGeometry.Space

end
