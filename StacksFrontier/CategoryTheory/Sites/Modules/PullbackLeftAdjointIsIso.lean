module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.Modules.PullbackLeftAdjointFlat
public import StacksFrontier.CategoryTheory.Sites.Modules.PullbackRingULift

/-!
# When is the adjunct of a map into a pushforward an isomorphism?

Let `F : C ⥤ D` be a continuous functor with a left adjoint `L`, let `φ : O₀ ⟶ F_*O` be a
morphism of sheaves of rings and let `κ : M ⟶ F_*N` be a morphism of sheaves of `O₀`-modules
into the pushforward of a sheaf of `O`-modules.  Its adjunct `F^*M ⟶ N` under `F^* ⊣ F_*` is an
isomorphism as soon as the map of presheaves

`V ↦ (O(V) ⊗_{O₀(L V)} M(L V) ⟶ N(V)),  s ⊗ m ↦ s • N(V ⟶ F (L V)) (κ m)`

is locally injective and locally surjective: `F^*M` is the sheafification of the presheaf
`V ↦ O(V) ⊗_{O₀(L V)} M(L V)` (`Stacks.PullbackLeftAdjoint.pullbackIsoSheafifyModel`), and under
this identification the adjunct of `κ` is the sheafification of the displayed map, which is its
adjunct for the concrete adjunction `Stacks.PullbackLeftAdjoint.modelAdjunction`.

When the modules live in a universe above the one of the rings, the same holds after raising the
universe of the rings: the adjunct for `φ` is an isomorphism as soon as the adjunct for the
lifted morphism `Stacks.UniverseLift.liftedRingHom φ` of the transported map is.

## Main results

* `Stacks.PullbackLeftAdjoint.isIso_homEquiv_symm_of_isLocallyBijective`: the criterion.
* `Stacks.UniverseLift.isIso_homEquiv_symm_of_liftedRingHom`: the reduction to the lifted rings.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe m z w r u₁ v₁ u₂ v₂

namespace CategoryTheory.Adjunction

open CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.PreservesZeroMorphisms] {X₁ X₂ : C} {Y₁ Y₂ : D} (d₀ : X₁ ⟶ X₂) (d : Y₁ ⟶ Y₂)
  (α₁ : F.obj X₁ ⟶ Y₁) (α₂ : F.obj X₂ ⟶ Y₂) (w : F.map d₀ ≫ α₂ = α₁ ≫ d)

/-- **The map on kernels induced by a square out of `F` is an adjunct**: if `F` preserves the
kernel of `d₀`, the map `ker (F d₀) ⟶ ker d` induced by `α₁, α₂` is an isomorphism as soon as
the adjunct of any `κ : ker d₀ ⟶ G (ker d)` lifting `ι ≫ α₁♭` is. -/
theorem isIso_kernel_map_of_isIso_homEquiv_symm [HasKernel d₀] [HasKernel (F.map d₀)]
    [HasKernel d] [PreservesLimit (parallelPair d₀ 0) F]
    (κ : kernel d₀ ⟶ G.obj (kernel d))
    (hκ : κ ≫ G.map (kernel.ι d) = kernel.ι d₀ ≫ adj.homEquiv _ _ α₁)
    (h : IsIso ((adj.homEquiv _ _).symm κ)) :
    IsIso (kernel.map (F.map d₀) d α₁ α₂ w) := by
  have := adj.isRightAdjoint
  have : Mono (G.map (kernel.ι d)) := inferInstance
  have e : (adj.homEquiv _ _).symm κ =
      kernelComparison d₀ F ≫ kernel.map (F.map d₀) d α₁ α₂ w := by
    rw [Equiv.symm_apply_eq]
    refine (cancel_mono (G.map (kernel.ι d))).1 ?_
    rw [hκ, ← adj.homEquiv_naturality_right, Category.assoc, kernel.lift_ι,
      ← Category.assoc, kernelComparison_comp_ι, adj.homEquiv_naturality_left]
  have : IsIso (kernelComparison d₀ F) := inferInstance
  rwa [← isIso_comp_left_iff (kernelComparison d₀ F), ← e]

/-- **The map on cokernels induced by a square out of `F` is an adjunct**: the map
`coker (F d₀) ⟶ coker d` induced by `α₁, α₂` is an isomorphism as soon as the adjunct of any
`κ : coker d₀ ⟶ G (coker d)` with `π ≫ κ = α₂♭ ≫ G π` is. -/
theorem isIso_cokernel_map_of_isIso_homEquiv_symm [HasCokernel d₀] [HasCokernel (F.map d₀)]
    [HasCokernel d] (κ : cokernel d₀ ⟶ G.obj (cokernel d))
    (hκ : cokernel.π d₀ ≫ κ = adj.homEquiv _ _ α₂ ≫ G.map (cokernel.π d))
    (h : IsIso ((adj.homEquiv _ _).symm κ)) :
    IsIso (cokernel.map (F.map d₀) d α₁ α₂ w) := by
  have := adj.isLeftAdjoint
  have : Epi (F.map (cokernel.π d₀)) := inferInstance
  have : PreservesColimitsOfSize.{0, 0} F := adj.leftAdjoint_preservesColimits
  have : IsIso (cokernelComparison d₀ F) := inferInstance
  have e : (adj.homEquiv _ _).symm κ = inv (cokernelComparison d₀ F) ≫
      cokernel.map (F.map d₀) d α₁ α₂ w := by
    refine (cancel_epi (F.map (cokernel.π d₀))).1 ?_
    rw [← adj.homEquiv_naturality_left_symm, hκ, adj.homEquiv_naturality_right_symm,
      Equiv.symm_apply_apply, ← π_comp_cokernelComparison, Category.assoc,
      IsIso.hom_inv_id_assoc, cokernel.π_desc]
  rwa [← isIso_comp_left_iff (inv (cokernelComparison d₀ F)), ← e]

end CategoryTheory.Adjunction

/-- Whether an inverse transpose is an isomorphism may be tested in either of two adjunctions
with the same right adjoint. -/
private theorem isIso_homEquiv_symm_of_leftAdjointUniq {C : Type*} [Category C] {D : Type*}
    [Category D] {L L' : C ⥤ D} {R : D ⥤ C} (adj₁ : L ⊣ R) (adj₂ : L' ⊣ R) {X : C} {Y : D}
    (t : X ⟶ R.obj Y) (h : IsIso ((adj₂.homEquiv X Y).symm t)) :
    IsIso ((adj₁.homEquiv X Y).symm t) := by
  rw [← adj₁.leftAdjointUniq_hom_app_comp_homEquiv_symm adj₂ t]
  infer_instance

namespace Stacks.PullbackLeftAdjoint

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {L : D ⥤ C} (adj : L ⊣ F)
  {O₀ : Cᵒᵖ ⥤ CommRingCat.{w}} {O : Dᵒᵖ ⥤ CommRingCat.{w}} (φ : O₀ ⟶ F.op ⋙ O)

/-- **The adjunct of `κ : M ⟶ F_*N` for the concrete adjunction, on pure tensors**:
`s ⊗ m ↦ s • N(V ⟶ F (L V)) (κ m)` for `s ∈ O(V)` and `m ∈ M(L V)`. -/
theorem modelAdjunction_homEquiv_symm_app_tmul
    (φ' : O₀ ⋙ forget₂ CommRingCat RingCat ⟶ F.op ⋙ O ⋙ forget₂ CommRingCat RingCat)
    (h : ringHom φ = φ') {M : _root_.PresheafOfModules.{w} (O₀ ⋙ forget₂ CommRingCat RingCat)}
    {N : _root_.PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
    (κ : M ⟶ (_root_.PresheafOfModules.pushforward.{w} φ').obj N) (V : Dᵒᵖ) (s : O.obj V)
    (m : M.obj (op (L.obj V.unop))) :
    ((((modelAdjunction adj φ φ' h).homEquiv M N).symm κ).app V)
        (Stacks.PullbackModel.tmul ((transposeRingHom adj φ).app V).hom s m) =
      s • N.map (adj.unit.app V.unop).op (κ.app (op (L.obj V.unop)) m) := by
  rw [Adjunction.homEquiv_counit, _root_.PresheafOfModules.comp_app]
  have hκ : (((pullbackModel adj φ).map κ).app V).hom
      (Stacks.PullbackModel.tmul ((transposeRingHom adj φ).app V).hom s m) =
        s • Stacks.PullbackModel.tmul ((transposeRingHom adj φ).app V).hom 1
          (κ.app (op (L.obj V.unop)) m) := by
    rw [Stacks.PullbackModel.smul_tmul, mul_one]
    rfl
  show (((modelAdjunction adj φ φ' h).counit.app N).app V).hom
      ((((pullbackModel adj φ).map κ).app V).hom
        (Stacks.PullbackModel.tmul ((transposeRingHom adj φ).app V).hom s m)) = _
  rw [hκ]
  exact ((((modelAdjunction adj φ φ' h).counit.app N).app V).hom.map_smul s _).trans
    (congrArg (s • ·) (modelAdjunction_counit_app_app_tmul adj φ φ' h N V _))

/-- **The adjunct of `κ : M ⟶ F_*N` on `1 ⊗ m|_{L V}`**: for a morphism `g : V ⟶ F Z` and a
section `m` of `M` over `Z`, the tensor `1 ⊗ m|_{L V}` is sent to `κ(m)|_V`, restriction being
along `g` and along its adjunct `L V ⟶ Z`. -/
theorem modelAdjunction_homEquiv_symm_app_tmul_one_map
    (φ' : O₀ ⋙ forget₂ CommRingCat RingCat ⟶ F.op ⋙ O ⋙ forget₂ CommRingCat RingCat)
    (h : ringHom φ = φ') {M : _root_.PresheafOfModules.{w} (O₀ ⋙ forget₂ CommRingCat RingCat)}
    {N : _root_.PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat RingCat)}
    (κ : M ⟶ (_root_.PresheafOfModules.pushforward.{w} φ').obj N) {V : D} {Z : C}
    (g : V ⟶ F.obj Z) (m : M.obj (op Z)) :
    ((((modelAdjunction adj φ φ' h).homEquiv M N).symm κ).app (op V))
        (Stacks.PullbackModel.tmul ((transposeRingHom adj φ).app (op V)).hom 1
          (M.map ((adj.homEquiv V Z).symm g).op m : M.obj (op (L.obj V)))) =
      N.map g.op (κ.app (op Z) m) := by
  refine (modelAdjunction_homEquiv_symm_app_tmul adj φ φ' h κ (op V) 1 _).trans ?_
  rw [one_smul, _root_.PresheafOfModules.naturality_apply]
  show N.map (adj.unit.app V).op (N.map (F.map ((adj.homEquiv V Z).symm g)).op
    (κ.app (op Z) m)) = _
  have e : adj.unit.app V ≫ F.map ((adj.homEquiv V Z).symm g) = g :=
    (adj.homEquiv_unit V Z _).symm.trans ((adj.homEquiv V Z).apply_symm_apply g)
  conv_rhs => rw [← e]
  exact (_root_.PresheafOfModules.map_comp_apply N (F.map ((adj.homEquiv V Z).symm g)).op
    (adj.unit.app V).op _).symm

end Presheaf

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
  {L : D ⥤ C} (adj : L ⊣ F)
  {O₀ : Sheaf J CommRingCat.{w}} {O : Sheaf K CommRingCat.{w}}
  (φ : Stacks.SheafOfModules.Tensor.ringSheaf O₀ ⟶
    (F.sheafPushforwardContinuous RingCat.{w} J K).obj (Stacks.SheafOfModules.Tensor.ringSheaf O))
  [HasWeakSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(_root_.SheafOfModules.pushforward.{w} φ).IsRightAdjoint]

/-- **The criterion.**  The adjunct `F^*M ⟶ N` of `κ : M ⟶ F_*N` is an isomorphism as soon as
the map of presheaves `V ↦ (O(V) ⊗_{O₀(L V)} M(L V) ⟶ N(V))`, its adjunct for the concrete
adjunction `Stacks.PullbackLeftAdjoint.modelAdjunction`, is locally injective and locally
surjective. -/
theorem isIso_homEquiv_symm_of_isLocallyBijective
    {M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (κ : M ⟶ (_root_.SheafOfModules.pushforward.{w} φ).obj N)
    (hi : _root_.PresheafOfModules.IsLocallyInjective K
      (((modelAdjunction adj (commRingHom φ) φ.hom (ringHom_commRingHom φ)).homEquiv
        M.val N.val).symm κ.val))
    (hs : _root_.PresheafOfModules.IsLocallySurjective K
      (((modelAdjunction adj (commRingHom φ) φ.hom (ringHom_commRingHom φ)).homEquiv
        M.val N.val).symm κ.val)) :
    IsIso (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{w} φ).homEquiv M N).symm κ) := by
  have := isRightAdjoint_presheafPushforward φ adj
  let P := _root_.PresheafOfModules.pullbackPushforwardAdjunction.{w} φ.hom
  let Q := modelAdjunction adj (commRingHom φ) φ.hom (ringHom_commRingHom φ)
  let A := _root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)
  let adjPC := _root_.SheafOfModules.PullbackConstruction.adjunction.{w} φ
  refine isIso_homEquiv_symm_of_leftAdjointUniq _ adjPC κ ?_
  let g₀ := (P.homEquiv M.val N.val).symm κ.val
  have hg₀ : (P.leftAdjointUniq Q).hom.app M.val ≫ (Q.homEquiv M.val N.val).symm κ.val =
      (P.homEquiv M.val N.val).symm κ.val :=
    Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm P Q κ.val
  let h := (A.homEquiv ((_root_.PresheafOfModules.pullback.{w} φ.hom).obj M.val) N).symm g₀
  have hh : (adjPC.homEquiv M N).symm κ = h := by
    simp only [adjPC, _root_.SheafOfModules.PullbackConstruction.adjunction,
      Adjunction.mkOfHomEquiv_homEquiv]
    rfl
  rw [hh]
  have hfac : A.unit.app _ ≫ (_root_.SheafOfModules.forget _ ⋙
      _root_.PresheafOfModules.restrictScalars _).map h = g₀ :=
    (A.homEquiv_unit _ _ h).symm.trans ((A.homEquiv _ N).apply_symm_apply g₀)
  let T := _root_.PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj
  have hc : T.map g₀ = T.map ((P.leftAdjointUniq Q).hom.app M.val) ≫
      T.map ((Q.homEquiv M.val N.val).symm κ.val) :=
    (congrArg T.map hg₀).symm.trans (Functor.map_comp _ _ _)
  have : Presheaf.IsLocallyInjective K (T.map ((Q.homEquiv M.val N.val).symm κ.val)) := hi
  have : Presheaf.IsLocallySurjective K (T.map ((Q.homEquiv M.val N.val).symm κ.val)) := hs
  have : Presheaf.IsLocallyInjective K (T.map g₀) := by
    rw [hc]
    exact Presheaf.isLocallyInjective_comp K (T.mapIso ((P.leftAdjointUniq Q).app M.val)).hom _
  have : Presheaf.IsLocallySurjective K (T.map g₀) := by
    rw [hc]
    exact Presheaf.isLocallySurjective_comp K (T.mapIso ((P.leftAdjointUniq Q).app M.val)).hom _
  have hfac' : CategoryTheory.toSheafify K
      ((_root_.PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).obj
        ((_root_.PresheafOfModules.pullback.{w} φ.hom).obj M.val)) ≫
      (_root_.PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).map
        h.val =
      (_root_.PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).map
        g₀ := by
    rw [← hfac]; rfl
  have u₁ := (K.W_toSheafify
    ((_root_.PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).obj
      ((_root_.PresheafOfModules.pullback.{w} φ.hom).obj M.val))).isLocallyInjective
  have u₂ := (K.W_toSheafify
    ((_root_.PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).obj
      ((_root_.PresheafOfModules.pullback.{w} φ.hom).obj M.val))).isLocallySurjective
  have hi' := ‹Presheaf.IsLocallyInjective K
    ((_root_.PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).map g₀)›
  have hs' := ‹Presheaf.IsLocallySurjective K
    ((_root_.PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).map g₀)›
  rw [← hfac'] at hi' hs'
  have : _root_.PresheafOfModules.IsLocallyInjective K h.val :=
    (@Presheaf.comp_isLocallyInjective_iff _ _ K _ _ _ _ _ _ _ _ _ _ _ u₁ u₂).1 hi'
  have : _root_.PresheafOfModules.IsLocallySurjective K h.val :=
    (@Presheaf.comp_isLocallySurjective_iff _ _ K _ _ _ _ _ _ _ _ _ _ _ u₂).1 hs'
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective h

end Stacks.PullbackLeftAdjoint

namespace Stacks.UniverseLift

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D} [F.IsContinuous J K]
  {O₀ : Sheaf J CommRingCat.{r}} {O : Sheaf K CommRingCat.{r}}
  (φ : Stacks.SheafOfModules.Tensor.ringSheaf O₀ ⟶
    (F.sheafPushforwardContinuous RingCat.{r} J K).obj (Stacks.SheafOfModules.Tensor.ringSheaf O))
  [(_root_.SheafOfModules.pushforward.{max r z m} φ).IsRightAdjoint]

/-- **The transport of a map into a pushforward to the lifted rings**: `κ : M ⟶ F_*N` read as a
map `M ⟶ F_*N` of modules over the universe lifts of the structure rings; on sections it is `κ`
itself. -/
def liftedPushforwardHom
    {M : _root_.SheafOfModules.{max r z m} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {N : _root_.SheafOfModules.{max r z m} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (κ : M ⟶ (_root_.SheafOfModules.pushforward.{max r z m} φ).obj N) :
    (ringTransportEquivalence.{max r z m, z} O₀).functor.obj M ⟶
      (_root_.SheafOfModules.pushforward.{max r z m} (liftedRingHom.{z} φ)).obj
        ((ringTransportEquivalence.{max r z m, z} O).functor.obj N) :=
  (ringTransportEquivalence.{max r z m, z} O₀).functor.map κ ≫
    (pushforwardRingULiftIso.{m, z} φ).hom.app N

/-- **Reduction to the lifted rings.**  The adjunct `φ^*M ⟶ N` of `κ : M ⟶ φ_*N` is an
isomorphism as soon as the adjunct for the lifted morphism `φ↑` of the transported map
`Stacks.UniverseLift.liftedPushforwardHom κ` is. -/
theorem isIso_homEquiv_symm_of_liftedRingHom
    {M : _root_.SheafOfModules.{max r z m} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)}
    {N : _root_.SheafOfModules.{max r z m} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (κ : M ⟶ (_root_.SheafOfModules.pushforward.{max r z m} φ).obj N)
    (h : have := isRightAdjoint_pushforward_liftedRingHom.{m, z} φ
      IsIso (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{max r z m}
        (liftedRingHom.{z} φ)).homEquiv _ _).symm (liftedPushforwardHom.{m, z} φ κ))) :
    IsIso (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{max r z m} φ).homEquiv
      M N).symm κ) := by
  have := isRightAdjoint_pushforward_liftedRingHom.{m, z} φ
  let T₀ := ringTransportEquivalence.{max r z m, z} O₀
  let T := ringTransportEquivalence.{max r z m, z} O
  let adjL := _root_.SheafOfModules.pullbackPushforwardAdjunction.{max r z m}
    (liftedRingHom.{z} φ)
  let ρ : (T.functor ⋙ _root_.SheafOfModules.pushforward.{max r z m} (liftedRingHom.{z} φ)) ⋙
      T₀.inverse ≅ _root_.SheafOfModules.pushforward.{max r z m} φ :=
    Functor.isoWhiskerRight (pushforwardRingULiftIso.{m, z} φ).symm T₀.inverse ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ T₀.unitIso.symm ≪≫
      Functor.rightUnitor _
  let adj₂ := (T₀.toAdjunction.comp (adjL.comp T.symm.toAdjunction)).ofNatIsoRight ρ
  refine isIso_homEquiv_symm_of_leftAdjointUniq _ adj₂ κ ?_
  have hκ : T₀.functor.map (κ ≫ ρ.inv.app N) ≫ T₀.counit.app _ =
      liftedPushforwardHom.{m, z} φ κ := by
    have hρ : ρ.inv.app N = T₀.unit.app _ ≫
        T₀.inverse.map ((pushforwardRingULiftIso.{m, z} φ).hom.app N) := by
      simp [ρ]
    have hn := T₀.counit.naturality ((pushforwardRingULiftIso.{m, z} φ).hom.app N)
    rw [hρ, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    show _ ≫ _ ≫ (T₀.inverse ⋙ T₀.functor).map _ ≫ _ = _
    rw [hn, ← Category.assoc (T₀.functor.map (T₀.unit.app _))]
    have ht := T₀.functor_unit_comp ((_root_.SheafOfModules.pushforward.{max r z m} φ).obj N)
    show _ ≫ (T₀.functor.map (T₀.unit.app _) ≫
      T₀.counit.app (T₀.functor.obj ((_root_.SheafOfModules.pushforward.{max r z m} φ).obj N))) ≫
        _ = _
    rw [ht]
    exact congrArg (T₀.functor.map κ ≫ ·) (Category.id_comp _)
  have e : (adj₂.homEquiv M N).symm κ = T.inverse.map ((adjL.homEquiv _ _).symm
      (liftedPushforwardHom.{m, z} φ κ)) ≫ T.unitInv.app N := by
    rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply, Adjunction.comp_homEquiv,
      Adjunction.comp_homEquiv]
    simp only [Equiv.symm_trans_apply]
    rw [← hκ]
    rfl
  rw [e]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) inferInstance

end Stacks.UniverseLift

end
