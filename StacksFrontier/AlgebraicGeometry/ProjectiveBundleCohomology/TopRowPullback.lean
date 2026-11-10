module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.TopRowPairing
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.PullbackWedge
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.ProjectionFormulaBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.CoherentTensor
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DualBaseChangeCompatibility
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.SpellingBridge
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleCohomology.IsoTrace
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerShortExact

/-!
# The pairing of the top row of Tag 01XX under pullback

For a finite locally free module `A` on a scheme, `L ⊗ A^∨ ≅ SheafHom(A, L)` is adjoint to the
contraction `(L ⊗ A^∨) ⊗ A ⟶ L`, `(l ⊗ λ) ⊗ a ↦ λ(a) l`. The contraction commutes with pullback
along a morphism of schemes, through the dual base-change map `f^*(A^∨) ≅ (f^* A)^∨`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.ReflexiveModules (dualSheaf dualMap)
open scoped TensorProduct

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

section Contract

variable {X : Scheme.{u}} (A L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A]

/-- **The contraction** `(L ⊗ A^∨) ⊗ A ⟶ L`, adjoint to `L ⊗ A^∨ ≅ SheafHom(A, L)`. -/
public def tensorDualContract :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj (L, dualSheaf A), A) ⟶ L :=
  (Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace _ _ _).symm (sheafHomIsoTensorDual A L).inv

/-- The contraction on a pure tensor: `(l ⊗ λ) ⊗ a ↦ λ(a) l`. -/
public theorem tensorDualContract_unit (U : X.Opensᵒᵖ) (l : L.val.obj U)
    (lam : (dualSheaf A).val.obj U) (a : A.val.obj U) (r : X.ringCatSheaf.obj.obj U)
    (hr : (lam.app (op (Over.mk (𝟙 U.unop)))).hom a = r) :
    (tensorDualContract A L).val.app U
        ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf) _ A).app U
          ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf) L
            (dualSheaf A)).app U (l ⊗ₜ lam) ⊗ₜ a)) = r • l := by
  subst hr
  have h1 := Stacks.SheafOfModules.tensorHomEquiv_isTensorCurry X.toRingedSpace
    (tensorDualContract A L) U.unop
    ((PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf) L (dualSheaf A)).app U
      (l ⊗ₜ lam)) a
  have h2 : Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace _ _ _ (tensorDualContract A L) =
      (sheafHomIsoTensorDual A L).inv := Equiv.apply_symm_apply _ _
  have h3 := Stacks.SheafOfModules.tensorDualToSheafHom_toTensorSheafSection X.sheaf.obj
    (Stacks.SheafOfModules.Strict.isSheaf_ringSheaf X.sheaf) A L U l lam
  rw [h2] at h1
  refine h1.symm.trans ?_
  refine (congrArg (fun s => (s.app (op (Over.mk (𝟙 U.unop)))).hom a) h3).trans ?_
  exact (Stacks.SheafOfModules.rankOneHomSection_app _ _ l lam (op (Over.mk (𝟙 U.unop))) a).trans
    (congrArg (_ • ·) (Stacks.SheafOfModules.resSection_self (U := U.unop) l))

end Contract


section ContractPullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (A L : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A] {A' L' : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A']
  (α : (Scheme.Modules.pullback f).obj A ≅ A') (θ : (Scheme.Modules.pullback f).obj L ≅ L')
  (β : (Scheme.Modules.pullback f).obj (dualSheaf A) ≅ dualSheaf A')

/-- **The contraction commutes with pullback**: for `α : f^* A ≅ A'`, `θ : f^* L ≅ L'` and
`β : f^*(A^∨) ≅ A'^∨` compatible with the evaluations, `f^*((L ⊗ A^∨) ⊗ A ⟶ L)` is
`(L' ⊗ A'^∨) ⊗ A' ⟶ L'`. -/
public theorem tensorDualContract_pullback
    (hβ : ∀ (U : (Opens Y.carrier)ᵒᵖ) (lam : (dualSheaf A).val.obj U) (a : A.val.obj U),
      ((β.hom.val.app ((opensMap f.toLRSHom.toShHom).op.obj U)
          (pullbackUnit f.toLRSHom.toShHom (dualSheaf A) U lam)).app
          (op (Over.mk (𝟙 ((opensMap f.toLRSHom.toShHom).op.obj U).unop)))).hom
          (α.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom A U a)) =
        sharp f.toLRSHom.toShHom U ((lam.app (op (Over.mk (𝟙 U.unop)))).hom a)) :
    (tensorPullbackIso f.toLRSHom.toShHom (tensorPullbackIso f.toLRSHom.toShHom θ β) α).hom ≫
        tensorDualContract A' L' =
      (Scheme.Modules.pullback f).map (tensorDualContract A L) ≫ θ.hom := by
  refine pullback_tensorSheaf_hom_ext₂ f.toLRSHom.toShHom fun U l lam a => ?_
  refine (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).trans ?_
  refine Eq.trans ?_ (_root_.SheafOfModules.comp_val_app_apply _ _ _ _).symm
  refine (congrArg ((tensorDualContract A' L').val.app _)
    ((tensorPullbackIso_unit f.toLRSHom.toShHom (tensorPullbackIso f.toLRSHom.toShHom θ β) α U
      _ a).trans (congrArg (fun w =>
        (PresheafOfModules.tensorSheafUnit (Osharp := X.toRingedSpace.sheaf) _ A').app _
          (w ⊗ₜ α.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom A U a)))
        (tensorPullbackIso_unit f.toLRSHom.toShHom θ β U l lam)))).trans ?_
  refine (tensorDualContract_unit A' L' _ _ _ _ _ (hβ U lam a)).trans ?_
  refine Eq.trans ?_ (congrArg (θ.hom.val.app _)
    ((pullbackUnit_naturality f.toLRSHom.toShHom (tensorDualContract A L) U _).trans
      (congrArg (pullbackUnit f.toLRSHom.toShHom L U)
        (tensorDualContract_unit A L U l lam a _ rfl)))).symm
  refine Eq.trans ?_ (congrArg (θ.hom.val.app _)
    (pullbackUnit_smul f.toLRSHom.toShHom L U _ l)).symm
  exact (map_smul (θ.hom.val.app _).hom _ _).symm


/-- The dual base-change isomorphism `f^*(A^∨) ≅ (f^* A)^∨ ≅ A'^∨` along `α : f^* A ≅ A'`. -/
public abbrev pullbackDualIsoOf
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A) :
    (Scheme.Modules.pullback f).obj (dualSheaf A) ≅ dualSheaf A' :=
  Stacks.FundamentalGroup.pullbackDualSheafIso f A hA ≪≫
    ((Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor X).mapIso α.op).symm

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A'] in
/-- `pullbackDualIsoOf` is compatible with the evaluations. -/
public theorem pullbackDualIsoOf_unit
    (hA : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A)
    (U : (Opens Y.carrier)ᵒᵖ) (lam : (dualSheaf A).val.obj U) (a : A.val.obj U) :
    (((pullbackDualIsoOf f A α hA).hom.val.app ((opensMap f.toLRSHom.toShHom).op.obj U)
        (pullbackUnit f.toLRSHom.toShHom (dualSheaf A) U lam)).app
        (op (Over.mk (𝟙 ((opensMap f.toLRSHom.toShHom).op.obj U).unop)))).hom
        (α.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom A U a)) =
      sharp f.toLRSHom.toShHom U ((lam.app (op (Over.mk (𝟙 U.unop)))).hom a) := by
  change (((Stacks.FundamentalGroup.pullbackDualSheafIso f A hA).hom.val.app (op (f ⁻¹ᵁ U.unop))
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (dualSheaf A)).val.app U lam)).app
      (op (Over.mk (𝟙 (f ⁻¹ᵁ U.unop))))).hom (α.inv.val.app (op (f ⁻¹ᵁ U.unop))
        (α.hom.val.app (op (f ⁻¹ᵁ U.unop))
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app A).val.app U a))) = _
  exact (congrArg (fun y => (((Stacks.FundamentalGroup.pullbackDualSheafIso f A hA).hom.val.app
      (op (f ⁻¹ᵁ U.unop)) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (dualSheaf A)).val.app U lam)).app (op (Over.mk (𝟙 (f ⁻¹ᵁ U.unop))))).hom y)
    (Stacks.Chow.iso_inv_val_app_hom_val_app α (f ⁻¹ᵁ U.unop) _)).trans
    (Stacks.FundamentalGroup.pullbackDualSheafIso_unit_apply f A hA U.unop lam a)

end ContractPullback




section TensorPullbackRefl

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {O A M : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
  {O' A' N : _root_.SheafOfModules.{u} (structureRingSheaf X)}
  (α : (pullbackFunctor f).obj A ≅ A')

/-- `tensorPullbackIso` with the identity in the first factor, followed by a morphism there. -/
public theorem tensorPullbackIso_refl_tensorMap (θ : (pullbackFunctor f).obj O ≅ O') :
    (tensorPullbackIso f (Iso.refl _) α).hom ≫ tensorMap θ.hom (𝟙 A') =
      (tensorPullbackIso f θ α).hom := by
  change (Stacks.RingedSpace.comparison f O A ≫ tensorMap (𝟙 _) α.hom) ≫ tensorMap θ.hom (𝟙 A') =
    Stacks.RingedSpace.comparison f O A ≫ tensorMap θ.hom α.hom
  refine (Category.assoc _ _ _).trans (congrArg (Stacks.RingedSpace.comparison f O A ≫ ·) ?_)
  exact (tensorMap_comp _ _ _ _).trans
    (congrArg₂ tensorMap (Category.id_comp _) (Category.comp_id _))

/-- `tensorPullbackIso` with the identity in the first factor, followed by the pullback of a
morphism there. -/
public theorem tensorPullbackIso_refl_tensorMap_map (φ : O ⟶ M)
    (T : (pullbackFunctor f).obj M ⟶ N) :
    (tensorPullbackIso f (Iso.refl _) α).hom ≫ tensorMap ((pullbackFunctor f).map φ ≫ T) (𝟙 A') =
      (pullbackFunctor f).map (tensorMap φ (𝟙 A)) ≫ Stacks.RingedSpace.comparison f M A ≫
        tensorMap T α.hom := by
  change (Stacks.RingedSpace.comparison f O A ≫ tensorMap (𝟙 _) α.hom) ≫
    tensorMap ((pullbackFunctor f).map φ ≫ T) (𝟙 A') = _
  refine Eq.trans ?_ ((comparison_naturality_assoc f φ (𝟙 A) (tensorMap T α.hom)).trans
    (Category.assoc _ _ _)).symm
  refine (Category.assoc _ _ _).trans (congrArg (Stacks.RingedSpace.comparison f O A ≫ ·) ?_)
  refine (tensorMap_comp _ _ _ _).trans (Eq.trans ?_ (tensorMap_comp _ _ _ _).symm)
  exact congrArg₂ tensorMap (Category.id_comp _) ((Category.comp_id _).trans
    ((Category.id_comp _).symm.trans
      (congrArg (· ≫ α.hom) ((pullbackFunctor f).map_id A).symm)))

/-- `tensorPullbackIso` with the identity in the first factor, followed by a composite there. -/
public theorem tensorPullbackIso_refl_tensorMap_comp (θ : (pullbackFunctor f).obj O ⟶ O')
    (v : O' ⟶ N) :
    (tensorPullbackIso f (Iso.refl _) α).hom ≫ tensorMap (θ ≫ v) (𝟙 A') =
      Stacks.RingedSpace.comparison f O A ≫ tensorMap θ α.hom ≫ tensorMap v (𝟙 A') := by
  change (Stacks.RingedSpace.comparison f O A ≫ tensorMap (𝟙 _) α.hom) ≫
    tensorMap (θ ≫ v) (𝟙 A') = _
  refine (Category.assoc _ _ _).trans (congrArg (Stacks.RingedSpace.comparison f O A ≫ ·) ?_)
  refine (tensorMap_comp _ _ _ _).trans (Eq.trans ?_ (tensorMap_comp _ _ _ _).symm)
  exact congrArg₂ tensorMap (Category.id_comp _) (Category.comp_id _)

end TensorPullbackRefl


section DualNaturality

open Stacks.Chow in
/-- The pulled-back evaluation pairing is natural in the module. -/
public theorem pullbackEvaluation_naturality {W Y : Scheme.{u}} (t : W ⟶ Y) {M₁ M₂ : Y.Modules}
    (c : M₁ ⟶ M₂) :
    tensorMap (Z := W.toRingedSpace)
        ((Scheme.Modules.pullback t).map (dualMap c)) (𝟙 _) ≫ pullbackEvaluation t M₁ =
      tensorMap (Z := W.toRingedSpace) (𝟙 _)
        ((Scheme.Modules.pullback t).map c) ≫ pullbackEvaluation t M₂ := by
  refine tensor_hom_ext_of_pullbackUnit t (dualSheaf M₂) M₁ (fun U s m => ?_)
  refine (comp_val_app _ _ _ _).trans ?_
  refine Eq.trans ?_ (comp_val_app _ _ _ _).symm
  refine (val_app_congr _ _ ((tensorSheafMap_tensorSheafPure _ _ _ _ _).trans
    (tensorSheafPure_congr _ _ _ (pullback_map_unit_app t (dualMap c) U s) rfl))).trans ?_
  refine Eq.trans ?_ (val_app_congr _ _ ((tensorSheafMap_tensorSheafPure _ _ _ _ _).trans
    (tensorSheafPure_congr _ _ _ rfl (pullback_map_unit_app t c U m)))).symm
  exact (pullbackEvaluation_unit_tmul t M₁ U _ m).trans
    (pullbackEvaluation_unit_tmul t M₂ U s _).symm

open Stacks.Chow in
/-- **The dual base-change map is natural in the module**: for `c : M₁ ⟶ M₂`,
`t^*(c^∨) : t^*(M₂^∨) ⟶ t^*(M₁^∨)` corresponds to `(t^* c)^∨`. -/
public theorem pullbackDualMap_naturality {W Y : Scheme.{u}} (t : W ⟶ Y) {M₁ M₂ : Y.Modules}
    (c : M₁ ⟶ M₂) :
    (Scheme.Modules.pullback t).map (dualMap c) ≫ pullbackDualMap t M₁ =
      pullbackDualMap t M₂ ≫ dualMap ((Scheme.Modules.pullback t).map c) := by
  refine hom_ext_dualSheaf_of_terminal (fun V a b => ?_)
  have e1 : (tensorMap (Z := W.toRingedSpace)
        ((Scheme.Modules.pullback t).map (dualMap c)) (𝟙 _) ≫ pullbackEvaluation t M₁).val.app
          (op V) (tensorSheafPure W _ _ V (a ⊗ₜ[W.presheaf.obj (op V)] b)) =
      (pullbackEvaluation t M₁).val.app (op V) (tensorSheafPure W _ _ V
        (((Scheme.Modules.pullback t).map (dualMap c)).val.app (op V) a ⊗ₜ[W.presheaf.obj (op V)]
          b)) :=
    (comp_val_app _ _ _ _).trans (val_app_congr _ _ (tensorSheafMap_tensorSheafPure _ _ _ _ _))
  have e2 : (tensorMap (Z := W.toRingedSpace) (𝟙 _)
        ((Scheme.Modules.pullback t).map c) ≫ pullbackEvaluation t M₂).val.app
          (op V) (tensorSheafPure W _ _ V (a ⊗ₜ[W.presheaf.obj (op V)] b)) =
      (pullbackEvaluation t M₂).val.app (op V) (tensorSheafPure W _ _ V
        (a ⊗ₜ[W.presheaf.obj (op V)] ((Scheme.Modules.pullback t).map c).val.app (op V) b)) :=
    (comp_val_app _ _ _ _).trans (val_app_congr _ _ (tensorSheafMap_tensorSheafPure _ _ _ _ _))
  refine (pullbackDualMap_eval t M₁ V _ _).trans ?_
  exact e1.symm.trans ((congrArg (fun φ => φ.val.app (op V)
    (tensorSheafPure W _ _ V (a ⊗ₜ[W.presheaf.obj (op V)] b)))
    (pullbackEvaluation_naturality t c)).trans (e2.trans (pullbackDualMap_eval t M₂ V a _).symm))

end DualNaturality


/-- The diagram chase behind `pullbackDualMap_square`. -/
private theorem dualSquare_chase {C : Type*} [Category C] {X₀ X₁ X₂ X₃ Y₁ Y₂ Z₁ Z₂ : C}
    {a : X₀ ⟶ X₁} {D₁ : X₁ ⟶ Y₁} {dm₁ : Y₁ ⟶ Z₁} {L₁ : X₀ ⟶ Z₁} {c : X₃ ⟶ X₂} {ci : X₂ ⟶ X₃}
    {D₂ : X₂ ⟶ Y₂} {dm₂ : Y₂ ⟶ Z₂} {L₂ : X₃ ⟶ Z₂} {k : X₁ ⟶ X₂} {dmk : Y₂ ⟶ Y₁}
    {dsq : Z₁ ⟶ Z₂} {sq : X₀ ⟶ X₃}
    (h₁ : a ≫ D₁ ≫ dm₁ = L₁) (h₂ : c ≫ D₂ ≫ dm₂ = L₂) (hk : k ≫ D₂ ≫ dmk = D₁)
    (hsq : sq = a ≫ k ≫ ci) (hc : ci ≫ c = 𝟙 _) (hdm : dmk ≫ dm₁ ≫ dsq = dm₂) :
    L₁ ≫ dsq = sq ≫ L₂ := by
  rw [← h₁, ← h₂, hsq, ← hk]
  simp only [Category.assoc, hdm, reassoc_of% hc]

section DualSquare

variable {P P' S S' : Scheme.{u}} (π : P ⟶ S) (g : S' ⟶ S) (π' : P' ⟶ S') (b : P' ⟶ P)
  (w : b ≫ π = π' ≫ g) (N : S.Modules)

/-- **The dual base-change maps of a commutative square agree**: along `b^* π^* ≅ π'^* g^*`,
`b^* π^*(N^∨) ⟶ b^*((π^* N)^∨) ⟶ (b^* π^* N)^∨` is
`π'^* g^*(N^∨) ⟶ π'^*((g^* N)^∨) ⟶ (π'^* g^* N)^∨`. -/
public theorem pullbackDualMap_square :
    (Scheme.Modules.pullback b).map (Stacks.Chow.pullbackDualMap π N) ≫
        Stacks.Chow.pullbackDualMap b ((Scheme.Modules.pullback π).obj N) ≫
        dualMap (squarePullbackIso π g π' b w N).inv =
      (squarePullbackIso π g π' b w (dualSheaf N)).hom ≫
        (Scheme.Modules.pullback π').map (Stacks.Chow.pullbackDualMap g N) ≫
        Stacks.Chow.pullbackDualMap π' ((Scheme.Modules.pullback g).obj N) := by
  have hdm : dualMap ((Scheme.Modules.pullbackCongr w).hom.app N) ≫
      dualMap ((Scheme.Modules.pullbackComp b π).hom.app N) ≫
        dualMap (squarePullbackIso π g π' b w N).inv =
      dualMap ((Scheme.Modules.pullbackComp π' g).hom.app N) := by
    rw [← Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_comp,
      ← Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_comp]
    congr 1
    simp [squarePullbackIso]
  have hsq : (squarePullbackIso π g π' b w (dualSheaf N)).hom =
      (Scheme.Modules.pullbackComp b π).hom.app (dualSheaf N) ≫
        (Scheme.Modules.pullbackCongr w).hom.app (dualSheaf N) ≫
        (Scheme.Modules.pullbackComp π' g).inv.app (dualSheaf N) := rfl
  refine (Category.assoc _ _ _).symm.trans ?_
  exact dualSquare_chase (Stacks.Chow.pullbackDualMap_comp b π N)
    (Stacks.Chow.pullbackDualMap_comp π' g N)
    (Stacks.FundamentalGroup.pullbackDualMap_congr w N) hsq (Iso.inv_hom_id_app _ _) hdm

/-- The diagram chase behind `pullbackDualIsoOf_square`. -/
private theorem dualIsoSquare_chase {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ : C}
    {sq : X₀ ⟶ X₁} {pg : X₁ ⟶ X₂} {dσ : X₂ ⟶ X₃} {pπ' : X₃ ⟶ X₅} {pπ'g : X₂ ⟶ X₄}
    {dσ' : X₄ ⟶ X₅} {bp : X₀ ⟶ Y₁} {pb : Y₁ ⟶ Y₂} {dsq : Y₂ ⟶ X₄} {L : X₁ ⟶ X₃} {R : Y₂ ⟶ X₅}
    (hL : L = pg ≫ dσ) (hR : R = dsq ≫ dσ') (h₁ : bp ≫ pb ≫ dsq = sq ≫ pg ≫ pπ'g)
    (h₂ : dσ ≫ pπ' = pπ'g ≫ dσ') :
    sq ≫ L ≫ pπ' = bp ≫ pb ≫ R := by
  subst hL hR
  rw [reassoc_of% h₁, Category.assoc, h₂]

variable {N' : S'.Modules} (σ : (Scheme.Modules.pullback g).obj N ≅ N')
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N']
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((Scheme.Modules.pullback π).obj N)]
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((Scheme.Modules.pullback π').obj N')]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
    ((Scheme.Modules.pullback π').obj N')] in
/-- **The dual base-change isomorphisms of a commutative square agree**, along `σ : g^* N ≅ N'`:
`b^* π^*(N^∨) ⟶ b^*((π^* N)^∨) ⟶ (π'^* N')^∨` is
`b^* π^*(N^∨) ≅ π'^* g^*(N^∨) ⟶ π'^*(N'^∨) ⟶ (π'^* N')^∨`. -/
public theorem pullbackDualIsoOf_square :
    (squarePullbackIso π g π' b w (dualSheaf N)).hom ≫
        (Scheme.Modules.pullback π').map (pullbackDualIsoOf g N σ inferInstance).hom ≫
        (Stacks.FundamentalGroup.pullbackDualSheafIso π' N' inferInstance).hom =
      (Scheme.Modules.pullback b).map
          (Stacks.FundamentalGroup.pullbackDualSheafIso π N inferInstance).hom ≫
        (pullbackDualIsoOf b ((Scheme.Modules.pullback π).obj N)
          (squarePullbackIso π g π' b w N ≪≫ (Scheme.Modules.pullback π').mapIso σ)
          inferInstance).hom := by
  have hL : (Scheme.Modules.pullback π').map (pullbackDualIsoOf g N σ inferInstance).hom =
      (Scheme.Modules.pullback π').map (Stacks.Chow.pullbackDualMap g N) ≫
        (Scheme.Modules.pullback π').map (dualMap σ.inv) :=
    (Scheme.Modules.pullback π').map_comp _ _
  have hR : ((Stacks.AlgebraicGeometry.ReflexiveModules.dualFunctor P').mapIso
        (squarePullbackIso π g π' b w N ≪≫ (Scheme.Modules.pullback π').mapIso σ).op).symm.hom =
      dualMap (squarePullbackIso π g π' b w N).inv ≫
        dualMap ((Scheme.Modules.pullback π').map σ.inv) :=
    Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_comp _ _
  exact dualIsoSquare_chase hL hR (pullbackDualMap_square π g π' b w N)
    (pullbackDualMap_naturality π' σ.inv)

end DualSquare


section DualCurry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- `dualEvaluation` after a map into the dual, on a local pure tensor. -/
private theorem tensorMap_dualEvaluation_unit {Z N : X.Modules} (v : Z ⟶ dualSheaf N)
    (U : X.Opensᵒᵖ) (x : Z.val.obj U) (y : N.val.obj U) :
    (tensorMap v (𝟙 N) ≫ dualEvaluation N).val.app U
        ((PresheafOfModules.tensorSheafUnit Z N).app U (x ⊗ₜ y)) =
      ((v.val.app U x).app (op (Over.mk (𝟙 U.unop)))).hom y :=
  (congrArg ((dualEvaluation N).val.app U)
    (Stacks.TensorSheafWorld.tensorSheafBifunctor_map_val_app_tensorSheafUnit
      (J := Opens.grothendieckTopology X) (Osharp := X.sheaf) (f := v) (g := 𝟙 N)
      (V := U) (x := x) (y := y))).trans
    (dualEvaluation_tensorSheafUnit N U (v.val.app U x) y)

/-- **A morphism into a dual is determined by its pairing**: `v ↦ (v ⊗ 1) ≫ ev` is injective. -/
public theorem dualEvaluation_cancel {Z N : X.Modules} {v₁ v₂ : Z ⟶ dualSheaf N}
    (h : tensorMap v₁ (𝟙 N) ≫ dualEvaluation N = tensorMap v₂ (𝟙 N) ≫ dualEvaluation N) :
    v₁ = v₂ := by
  refine Stacks.Chow.hom_ext_dualSheaf_of_terminal (fun U x y => ?_)
  exact (tensorMap_dualEvaluation_unit v₁ (op U) x y).symm.trans
    ((congrArg (fun φ => φ.val.app (op U)
    ((PresheafOfModules.tensorSheafUnit Z N).app (op U) (x ⊗ₜ y))) h).trans
    (tensorMap_dualEvaluation_unit v₂ (op U) x y))


/-- **A morphism into a dual, under pullback**: if the pairings `R ⊗ A ⟶ 𝒪` and
`R' ⊗ A' ⟶ 𝒪` of `u : R ⟶ A^∨` and `u' : R' ⟶ A'^∨` correspond under `θ : f^* R ⟶ R'` and
`α : f^* A ≅ A'`, then `f^* u` followed by `f^*(A^∨) ≅ A'^∨` is `θ` followed by `u'`. -/
public theorem pullbackDualIsoOf_curry {R A : Y.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A] {R' A' : X.Modules}
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A']
    (α : (Scheme.Modules.pullback f).obj A ≅ A') (θ : (Scheme.Modules.pullback f).obj R ⟶ R')
    (u : R ⟶ dualSheaf A) (u' : R' ⟶ dualSheaf A')
    (h : (pullbackFunctor f.toLRSHom.toShHom).map (tensorMap u (𝟙 A) ≫ dualEvaluation A) ≫
        (Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom).hom =
      Stacks.RingedSpace.comparison f.toLRSHom.toShHom R A ≫ tensorMap θ α.hom ≫
        tensorMap u' (𝟙 A') ≫ dualEvaluation A') :
    (Scheme.Modules.pullback f).map u ≫ (pullbackDualIsoOf f A α inferInstance).hom = θ ≫ u' := by
  refine dualEvaluation_cancel ?_
  refine (Iso.cancel_iso_hom_left (tensorPullbackIso f.toLRSHom.toShHom
    (Iso.refl ((Scheme.Modules.pullback f).obj R)) α) _ _).mp ?_
  refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_ ((congrArg (· ≫ dualEvaluation A')
    (tensorPullbackIso_refl_tensorMap_comp f.toLRSHom.toShHom α θ u')).trans
    ((Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans h.symm)))).symm)
  refine pullback_tensorSheaf_hom_ext f.toLRSHom.toShHom (fun U r a => ?_)
  have l1 := tensorPullbackIso_unit f.toLRSHom.toShHom
    (Iso.refl ((Scheme.Modules.pullback f).obj R)) α U r a
  have l3 := tensorMap_dualEvaluation_unit
    ((Scheme.Modules.pullback f).map u ≫ (pullbackDualIsoOf f A α inferInstance).hom)
    ((opensMap f.toLRSHom.toShHom).op.obj U) (pullbackUnit f.toLRSHom.toShHom R U r)
    (α.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom A U a))
  have l4 := pullbackUnit_naturality f.toLRSHom.toShHom u U r
  have l5 := pullbackDualIsoOf_unit f A α inferInstance U (u.val.app U r) a
  have r1 := pullbackUnit_naturality f.toLRSHom.toShHom (tensorMap u (𝟙 A) ≫ dualEvaluation A) U
    ((PresheafOfModules.tensorSheafUnit (Osharp := Y.toRingedSpace.sheaf) R A).app U (r ⊗ₜ a))
  have r2 := tensorMap_dualEvaluation_unit u U r a
  have r3 := Stacks.PullbackAlgebra.pullbackUnitIso_hom_pullbackUnit f.toLRSHom.toShHom U
    (((u.val.app U r).app (op (Over.mk (𝟙 U.unop)))).hom a)
  refine (congrArg (fun t => (dualEvaluation A').val.app _ ((tensorMap
    ((Scheme.Modules.pullback f).map u ≫ (pullbackDualIsoOf f A α inferInstance).hom)
    (𝟙 A')).val.app _ t)) l1).trans ?_
  refine l3.trans ?_
  refine (congrArg (fun t => (((pullbackDualIsoOf f A α inferInstance).hom.val.app _ t).app
    (op (Over.mk (𝟙 ((opensMap f.toLRSHom.toShHom).op.obj U).unop)))).hom
      (α.hom.val.app _ (pullbackUnit f.toLRSHom.toShHom A U a))) l4).trans ?_
  refine l5.trans ?_
  refine Eq.trans ?_ (congrArg (fun t =>
    (Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom).hom.val.app _ t) r1).symm
  refine Eq.trans ?_ (congrArg (fun t =>
    (Stacks.PullbackAlgebra.pullbackUnitIso f.toLRSHom.toShHom).hom.val.app _
      (pullbackUnit f.toLRSHom.toShHom _ U t)) r2).symm
  exact r3.symm

end DualCurry


section TensorPullbackT

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M M' L₁ L₂ : Y.Modules} {N N' L₁' L₂' : X.Modules}

/-- `f^*(M ⊗ L) ≅ N ⊗ L'` from `f^* M ≅ N` and `f^* L ≅ L'`, with the tensor products of
`Stacks.SheafOfModules.TensorStalkRingedSpace`. -/
public def tensorPullbackIsoT (a : (Scheme.Modules.pullback f).obj M ≅ N)
    (l : (Scheme.Modules.pullback f).obj L₁ ≅ L₁') :
    (Scheme.Modules.pullback f).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj M).obj L₁) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj N).obj L₁' :=
  tensorPullbackIso f.toLRSHom.toShHom a l

/-- `tensorPullbackIsoT` is natural in both factors. -/
public theorem tensorPullbackIsoT_naturality₂ (a : (Scheme.Modules.pullback f).obj M ≅ N)
    (a' : (Scheme.Modules.pullback f).obj M' ≅ N') (l : (Scheme.Modules.pullback f).obj L₁ ≅ L₁')
    (l' : (Scheme.Modules.pullback f).obj L₂ ≅ L₂') (g : M ⟶ M') (g' : N ⟶ N') (k : L₁ ⟶ L₂)
    (k' : L₁' ⟶ L₂') (hg : (Scheme.Modules.pullback f).map g ≫ a'.hom = a.hom ≫ g')
    (hk : (Scheme.Modules.pullback f).map k ≫ l'.hom = l.hom ≫ k') :
    (Scheme.Modules.pullback f).map (tensorMap (Z := Y.toRingedSpace) g k) ≫
        (tensorPullbackIsoT f a' l').hom =
      (tensorPullbackIsoT f a l).hom ≫ tensorMap (Z := X.toRingedSpace) g' k' :=
  tensorPullbackIso_naturality₂ f.toLRSHom.toShHom a a' l l' g g' k k' hg hk

end TensorPullbackT


section FourfoldExt

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {P Q R T Z : _root_.SheafOfModules.{u} (CategoryTheory.Sheaf.toRingCat J Osharp)}

/-- **Two morphisms out of `(P ⊗ Q) ⊗ (R ⊗ T)` agreeing on the images of the quadruple pure
tensors of local sections are equal.** -/
public theorem tensorSheaf_hom_ext₂₂
    {φ ψ : (Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Osharp)).obj
        ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Osharp)).obj (P, Q),
          (Functor.uncurry.obj
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Osharp)).obj (R, T)) ⟶ Z}
    (h : ∀ (U : Cᵒᵖ) (p : P.val.obj U) (q : Q.val.obj U) (r : R.val.obj U) (t : T.val.obj U),
      φ.val.app U ((PresheafOfModules.tensorSheafUnit _ _).app U
          ((PresheafOfModules.tensorSheafUnit P Q).app U (p ⊗ₜ q) ⊗ₜ
            (PresheafOfModules.tensorSheafUnit R T).app U (r ⊗ₜ t))) =
        ψ.val.app U ((PresheafOfModules.tensorSheafUnit _ _).app U
          ((PresheafOfModules.tensorSheafUnit P Q).app U (p ⊗ₜ q) ⊗ₜ
            (PresheafOfModules.tensorSheafUnit R T).app U (r ⊗ₜ t)))) :
    φ = ψ := by
  have hls₁ : PresheafOfModules.IsLocallySurjective J (PresheafOfModules.tensorSheafUnit P Q) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
      (𝟙 (CategoryTheory.Sheaf.toRingCat J Osharp).obj) (PresheafOfModules.tensorObj P.val Q.val)
  have hls₂ : PresheafOfModules.IsLocallySurjective J (PresheafOfModules.tensorSheafUnit R T) :=
    PresheafOfModules.isLocallySurjective_sheafificationAdjunction_unit_app
      (𝟙 (CategoryTheory.Sheaf.toRingCat J Osharp).obj) (PresheafOfModules.tensorObj R.val T.val)
  refine PresheafOfModules.tensorSheaf_hom_ext fun U s w => ?_
  refine PresheafOfModules.hom_congr_apply'
    (PresheafOfModules.tensorObj_hom_ext_of_isLocallySurjective Z.isSheaf.isSeparated
      (PresheafOfModules.tensorSheafUnit P Q)
      (φ := PresheafOfModules.tensorSheafUnit _ _ ≫ φ.val)
      (ψ := PresheafOfModules.tensorSheafUnit _ _ ≫ ψ.val) fun V x y z => ?_) U (s ⊗ₜ w)
  have key : PresheafOfModules.tensorHom (𝟙 (PresheafOfModules.tensorObj P.val Q.val))
        (PresheafOfModules.tensorSheafUnit R T) ≫
      PresheafOfModules.tensorHom (PresheafOfModules.tensorSheafUnit P Q) (𝟙 _) ≫
        PresheafOfModules.tensorSheafUnit _ _ ≫ φ.val =
      PresheafOfModules.tensorHom (𝟙 (PresheafOfModules.tensorObj P.val Q.val))
        (PresheafOfModules.tensorSheafUnit R T) ≫
      PresheafOfModules.tensorHom (PresheafOfModules.tensorSheafUnit P Q) (𝟙 _) ≫
        PresheafOfModules.tensorSheafUnit _ _ ≫ ψ.val :=
    PresheafOfModules.hom_ext fun W => ModuleCat.hom_ext
      (TensorProduct.ext_fourfold' fun p q r t => h W p q r t)
  exact PresheafOfModules.hom_congr_apply'
    (Stacks.SheafOfModules.TopWedge.tensorObj_hom_ext_of_isLocallySurjective_right
      Z.isSheaf.isSeparated
      (PresheafOfModules.tensorSheafUnit R T)
      (φ := PresheafOfModules.tensorHom (PresheafOfModules.tensorSheafUnit P Q) (𝟙 _) ≫
        PresheafOfModules.tensorSheafUnit _ _ ≫ φ.val)
      (ψ := PresheafOfModules.tensorHom (PresheafOfModules.tensorSheafUnit P Q) (𝟙 _) ≫
        PresheafOfModules.tensorSheafUnit _ _ ≫ ψ.val) fun W a r t =>
        PresheafOfModules.hom_congr_apply' key W (a ⊗ₜ (r ⊗ₜ t))) V ((x ⊗ₜ y) ⊗ₜ z)

end FourfoldExt


section FourfoldPullbackExt

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Two morphisms out of the pullback of `(A ⊗ B) ⊗ (C ⊗ D)` that agree on the pulled-back
quadruple pure tensors are equal.** -/
public theorem pullback_tensorSheaf_hom_ext₂₂
    {A B C D : _root_.SheafOfModules.{u} (structureRingSheaf Y)}
    {N : _root_.SheafOfModules.{u} (structureRingSheaf X)}
    {θ₁ θ₂ : (pullbackFunctor f).obj ((Functor.uncurry.obj
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj
      ((Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj
          (A, B),
        (Functor.uncurry.obj
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} ⟨Y.presheaf, Y.IsSheaf⟩)).obj
          (C, D))) ⟶ N}
    (h : ∀ (U : (Opens Y.carrier)ᵒᵖ) (a : A.val.obj U) (b : B.val.obj U) (c : C.val.obj U)
        (d : D.val.obj U),
      θ₁.val.app ((opensMap f).op.obj U) (pullbackUnit f _ U
          ((PresheafOfModules.tensorSheafUnit (Osharp := Y.sheaf) _ _).app U
            ((PresheafOfModules.tensorSheafUnit (Osharp := Y.sheaf) A B).app U (a ⊗ₜ b) ⊗ₜ
              (PresheafOfModules.tensorSheafUnit (Osharp := Y.sheaf) C D).app U (c ⊗ₜ d)))) =
        θ₂.val.app ((opensMap f).op.obj U) (pullbackUnit f _ U
          ((PresheafOfModules.tensorSheafUnit (Osharp := Y.sheaf) _ _).app U
            ((PresheafOfModules.tensorSheafUnit (Osharp := Y.sheaf) A B).app U (a ⊗ₜ b) ⊗ₜ
              (PresheafOfModules.tensorSheafUnit (Osharp := Y.sheaf) C D).app U (c ⊗ₜ d))))) :
    θ₁ = θ₂ := by
  refine ((pullbackAdjunction f).homEquiv _ N).injective ?_
  refine tensorSheaf_hom_ext₂₂ (J := Opens.grothendieckTopology Y.carrier) (Osharp := Y.sheaf)
    (P := A) (Q := B) (R := C) (T := D) (Z := (pushforwardFunctor f).obj N) fun U a b c d => ?_
  exact (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₁ U _).trans
    ((h U a b c d).trans (SheafOfModules.GradedAlgebra.homEquiv_val_app f θ₂ U _).symm)

end FourfoldPullbackExt

section CurryPullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {O L A : Y.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A] {O' L' A' : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} A']
  (θO : (Scheme.Modules.pullback f).obj O ≅ O') (θL : (Scheme.Modules.pullback f).obj L ≅ L')
  (α : (Scheme.Modules.pullback f).obj A ≅ A')

/-- Uncurrying a composite with a morphism into the sheaf-hom. -/
private theorem tensorHomEquiv_symm_comp {Z : Scheme.{u}} {P Q B H : Z.Modules} (u : P ⟶ Q)
    (c : Q ⟶ Stacks.SheafOfModules.sheafHomSpace Z.toRingedSpace B H) :
    (Stacks.SheafOfModules.tensorHomEquiv Z.toRingedSpace P B H).symm (u ≫ c) =
      tensorMap u (𝟙 B) ≫ (Stacks.SheafOfModules.tensorHomEquiv Z.toRingedSpace Q B H).symm c := by
  refine (Equiv.symm_apply_eq _).mpr ?_
  exact ((AlgebraicGeometry.CoherentReflexive.tensorSheafHomEquiv_natural_left Z.toRingedSpace u
    _).trans (congrArg (u ≫ ·) (Equiv.apply_symm_apply _ _))).symm

/-- A pairing is recovered from its curried form by the contraction. -/
private theorem tensorMap_curry_contract
    (tp : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (O, A) ⟶ L) :
    tensorMap (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
        (sheafHomIsoTensorDual A L).hom) (𝟙 A) ≫ tensorDualContract A L = tp := by
  have h := tensorHomEquiv_symm_comp
    (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
      (sheafHomIsoTensorDual A L).hom) (sheafHomIsoTensorDual A L).inv
  have e : (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
      (sheafHomIsoTensorDual A L).hom) ≫ (sheafHomIsoTensorDual A L).inv =
      Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))
  exact h.symm.trans ((congrArg (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L).symm
    e).trans (Equiv.symm_apply_apply _ _))

/-- The diagram chase behind `curry_sheafHomIsoTensorDual_pullback`. -/
private theorem curry_chase {C : Type*} [Category C] {P₀ P P₁ R S Z Q : C} {r₀ : P₀ ⟶ P}
    {tM : P ⟶ R} {tN : P ⟶ S} {fu : P₀ ⟶ P₁} {t₂ : P₁ ⟶ R} {e' : R ⟶ Z} {fe : P₁ ⟶ Q}
    {θ : Q ⟶ Z} {r' : P₀ ⟶ S} {tp' : S ⟶ Z} {ft : P₀ ⟶ Q}
    (h1 : r₀ ≫ tM = fu ≫ t₂) (h2 : r₀ ≫ tN = r') (hK : t₂ ≫ e' = fe ≫ θ) (hφ : fu ≫ fe = ft)
    (htp : ft ≫ θ = r' ≫ tp') :
    r₀ ≫ tM ≫ e' = r₀ ≫ tN ≫ tp' := by
  rw [← Category.assoc, h1, Category.assoc, hK, ← Category.assoc, hφ, htp, ← h2,
    Category.assoc]

/-- **The curried pairing commutes with pullback.** For a pairing `O ⊗ A ⟶ L` with `A` finite
locally free, the morphism `O ⟶ SheafHom(A, L) ≅ L ⊗ A^∨` pulls back, along `f^* O ≅ O'`,
`f^* L ≅ L'` and `f^* A ≅ A'`, to the morphism of a pairing `O' ⊗ A' ⟶ L'` compatible with it. -/
public theorem curry_sheafHomIsoTensorDual_pullback
    (tp : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (O, A) ⟶ L)
    (tp' : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj (O', A') ⟶ L')
    (htp : (Scheme.Modules.pullback f).map tp ≫ θL.hom =
      (tensorPullbackIso f.toLRSHom.toShHom θO α).hom ≫ tp') :
    (Scheme.Modules.pullback f).map
        (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
          (sheafHomIsoTensorDual A L).hom) ≫
        (tensorPullbackIso f.toLRSHom.toShHom θL (pullbackDualIsoOf f A α inferInstance)).hom =
      θO.hom ≫ Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace O' A' L' tp' ≫
        (sheafHomIsoTensorDual A' L').hom := by
  have hK := tensorDualContract_pullback f A L α θL (pullbackDualIsoOf f A α inferInstance)
    (pullbackDualIsoOf_unit f A α inferInstance)
  have hφ := ((Scheme.Modules.pullback f).map_comp _ _).symm.trans
    (congrArg (Scheme.Modules.pullback f).map (tensorMap_curry_contract tp))
  have h1 : (tensorPullbackIso f.toLRSHom.toShHom (Iso.refl _) α).hom ≫
      tensorMap ((Scheme.Modules.pullback f).map
        (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
          (sheafHomIsoTensorDual A L).hom) ≫
        (tensorPullbackIso f.toLRSHom.toShHom θL (pullbackDualIsoOf f A α inferInstance)).hom)
        (𝟙 A') =
      (Scheme.Modules.pullback f).map (tensorMap
        (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
          (sheafHomIsoTensorDual A L).hom) (𝟙 A)) ≫
        (tensorPullbackIso f.toLRSHom.toShHom
          (tensorPullbackIso f.toLRSHom.toShHom θL
            (pullbackDualIsoOf f A α inferInstance)) α).hom :=
    tensorPullbackIso_refl_tensorMap_map f.toLRSHom.toShHom α _ _
  have h2 := tensorPullbackIso_refl_tensorMap f.toLRSHom.toShHom α θO
  have hE := (Iso.cancel_iso_hom_left (tensorPullbackIso f.toLRSHom.toShHom
    (Iso.refl ((Scheme.Modules.pullback f).obj O)) α) _ _).mp (curry_chase h1 h2 hK hφ htp)
  have E : tensorMap ((Scheme.Modules.pullback f).map
        (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
          (sheafHomIsoTensorDual A L).hom) ≫
        (tensorPullbackIso f.toLRSHom.toShHom θL (pullbackDualIsoOf f A α inferInstance)).hom)
        (𝟙 A') ≫ (Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace _ A' L').symm
          (sheafHomIsoTensorDual A' L').inv =
      tensorMap θO.hom (𝟙 A') ≫ tp' := hE
  have key : ((Scheme.Modules.pullback f).map
      (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
        (sheafHomIsoTensorDual A L).hom) ≫
      (tensorPullbackIso f.toLRSHom.toShHom θL (pullbackDualIsoOf f A α inferInstance)).hom) ≫
      (sheafHomIsoTensorDual A' L').inv =
      θO.hom ≫ Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace O' A' L' tp' := by
    refine (Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace
      ((Scheme.Modules.pullback f).obj O) A' L').symm.injective ?_
    refine (tensorHomEquiv_symm_comp (P := (Scheme.Modules.pullback f).obj O)
      (Q := ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L').obj (dualSheaf A'))
      (B := A') (H := L')
      ((Scheme.Modules.pullback f).map
        (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
          (sheafHomIsoTensorDual A L).hom) ≫
        (tensorPullbackIso f.toLRSHom.toShHom θL (pullbackDualIsoOf f A α inferInstance)).hom)
      (sheafHomIsoTensorDual A' L').inv).trans (E.trans ?_)
    exact ((congrArg (tensorMap θO.hom (𝟙 A') ≫ ·) (Equiv.symm_apply_apply _ tp')).symm).trans
      (tensorHomEquiv_symm_comp (P := (Scheme.Modules.pullback f).obj O) (Q := O') (B := A')
        (H := L') θO.hom _).symm
  exact ((Iso.comp_inv_eq _).mp key).trans (Category.assoc _ _ _)

/-- The diagram chase behind `curry_dual_pullback`. -/
private theorem curryDual_chase {C : Type*} [Category C] {P₁ P₂ Q₀ Q₀' Q₁ Q₂ R : C}
    {top : R ⟶ P₂} {m : R ⟶ P₁} {t : P₁ ⟶ P₂} {T₁ : P₁ ⟶ Q₁} {T₂ : P₂ ⟶ Q₂} {θ : R ⟶ Q₀}
    {c₁ : Q₀ ⟶ Q₀'} {c₂ : Q₀' ⟶ Q₁} {t' : Q₁ ⟶ Q₂}
    (hs : top = m ≫ t) (hc : m ≫ T₁ = θ ≫ c₁ ≫ c₂) (hn : t ≫ T₂ = T₁ ≫ t') :
    top ≫ T₂ = θ ≫ c₁ ≫ c₂ ≫ t' := by
  rw [hs, Category.assoc, hn, ← Category.assoc, hc]
  simp only [Category.assoc]

/-- `curry_sheafHomIsoTensorDual_pullback`, with the tensor products of
`Stacks.SheafOfModules.TensorStalkRingedSpace`. -/
public theorem curry_sheafHomIsoTensorDual_pullbackT
    (tp : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj O).obj A ⟶ L)
    (tp' : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj O').obj A' ⟶ L')
    (htp : (Scheme.Modules.pullback f).map tp ≫ θL.hom = (tensorPullbackIsoT f θO α).hom ≫ tp') :
    (Scheme.Modules.pullback f).map
        (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
          (sheafHomIsoTensorDual A L).hom) ≫
        (tensorPullbackIsoT f θL (pullbackDualIsoOf f A α inferInstance)).hom =
      θO.hom ≫ Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace O' A' L' tp' ≫
        (sheafHomIsoTensorDual A' L').hom :=
  curry_sheafHomIsoTensorDual_pullback f θO θL α tp tp' htp

/-- **The curried pairing followed by an identification of the dual, under pullback**: as
`curry_sheafHomIsoTensorDual_pullback`, followed by `κ : A^∨ ⟶ G` and `κ' : A'^∨ ⟶ G'` compatible
with `γ : f^* G ≅ G'` and the dual base-change isomorphism. -/
public theorem curry_dual_pullback {G : Y.Modules} {G' : X.Modules}
    (γ : (Scheme.Modules.pullback f).obj G ≅ G') (κ : dualSheaf A ⟶ G) (κ' : dualSheaf A' ⟶ G')
    (hκ : (Scheme.Modules.pullback f).map κ ≫ γ.hom =
      (pullbackDualIsoOf f A α inferInstance).hom ≫ κ')
    (tp : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj O).obj A ⟶ L)
    (tp' : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj O').obj A' ⟶ L')
    (htp : (Scheme.Modules.pullback f).map tp ≫ θL.hom = (tensorPullbackIsoT f θO α).hom ≫ tp') :
    (Scheme.Modules.pullback f).map (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
        (sheafHomIsoTensorDual A L).hom ≫
          tensorMap (Z := Y.toRingedSpace) (𝟙 L) κ) ≫
        (tensorPullbackIsoT f θL γ).hom =
      θO.hom ≫ Stacks.SheafOfModules.tensorHomEquiv X.toRingedSpace O' A' L' tp' ≫
        (sheafHomIsoTensorDual A' L').hom ≫
          tensorMap (Z := X.toRingedSpace) (𝟙 L') κ' := by
  have hc := curry_sheafHomIsoTensorDual_pullbackT f θO θL α tp tp' htp
  have hg : (Scheme.Modules.pullback f).map (𝟙 L) ≫ θL.hom = θL.hom ≫ 𝟙 L' :=
    ((congrArg (· ≫ _) ((Scheme.Modules.pullback f).map_id _)).trans
      (Category.id_comp _)).trans (Category.comp_id _).symm
  have hn := tensorPullbackIsoT_naturality₂ f θL θL (pullbackDualIsoOf f A α inferInstance) γ
    (𝟙 L) (𝟙 L') κ κ' hg hκ
  have hs : (Scheme.Modules.pullback f).map
      (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
        (sheafHomIsoTensorDual A L).hom ≫
          tensorMap (Z := Y.toRingedSpace) (𝟙 L) κ) =
      (Scheme.Modules.pullback f).map
        (Stacks.SheafOfModules.tensorHomEquiv Y.toRingedSpace O A L tp ≫
          (sheafHomIsoTensorDual A L).hom) ≫
      (Scheme.Modules.pullback f).map
        (tensorMap (Z := Y.toRingedSpace) (𝟙 L) κ) :=
    (congrArg (Scheme.Modules.pullback f).map (Category.assoc _ _ _).symm).trans
      ((Scheme.Modules.pullback f).map_comp _ _)
  exact curryDual_chase hs hc hn

end CurryPullback


section PairingPullback

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Od Ok Os Oe A : Y.Modules} {Od' Ok' Os' Oe' A' : X.Modules}
  (θd : (Scheme.Modules.pullback f).obj Od ≅ Od') (θk : (Scheme.Modules.pullback f).obj Ok ≅ Ok')
  (θs : (Scheme.Modules.pullback f).obj Os ≅ Os') (θe : (Scheme.Modules.pullback f).obj Oe ≅ Oe')
  (α : (Scheme.Modules.pullback f).obj A ≅ A')

/-- The diagram chase behind `pairing_pullback`. -/
private theorem pairing_chase {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Z : C}
    {top : P₀ ⟶ P₃} {m₁ : P₀ ⟶ P₁} {m₂ : P₁ ⟶ P₂} {m₃ : P₂ ⟶ P₃} {θe : P₃ ⟶ Z}
    {θs : P₂ ⟶ Q₃} {q' : Q₃ ⟶ Z} {c' : P₁ ⟶ P₄} {tθθ : P₄ ⟶ Q₂} {μ' : Q₂ ⟶ Q₃}
    {Q₁' : C} {c : P₀ ⟶ Q₁} {tψ : Q₁ ⟶ P₄} {tθα : Q₁ ⟶ Q₁'} {t₁ψ : Q₁' ⟶ Q₂} {T : P₀ ⟶ Q₁'}
    {R : Q₁' ⟶ Z}
    (hL : top = m₁ ≫ m₂ ≫ m₃) (hE : m₃ ≫ θe = θs ≫ q') (hM : m₂ ≫ θs = c' ≫ tθθ ≫ μ')
    (hC : m₁ ≫ c' = c ≫ tψ) (hT : tψ ≫ tθθ = tθα ≫ t₁ψ) (hP : c ≫ tθα = T)
    (hR : t₁ψ ≫ μ' ≫ q' = R) :
    top ≫ θe = T ≫ R := by
  subst hL hP hR
  simp only [Category.assoc]
  rw [hE, reassoc_of% hM, reassoc_of% hC, reassoc_of% hT]

/-- **A multiplication pairing under pullback**: for `ψ : A ⟶ O_k`, `μ : O_d ⊗ O_k ⟶ O_s` and
`q : O_s ⟶ O_e` compatible with identifications `f^* O ≅ O'` and `f^* A ≅ A'`, the pairing
`O_d ⊗ A ⟶ O_e` pulls back to the corresponding pairing. -/
public theorem pairing_pullback (ψ : A ⟶ Ok) (ψ' : A' ⟶ Ok')
    (μ : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (Od, Ok) ⟶ Os)
    (μ' : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj (Od', Ok') ⟶ Os')
    (q : Os ⟶ Oe) (q' : Os' ⟶ Oe')
    (hψ : (Scheme.Modules.pullback f).map ψ ≫ θk.hom = α.hom ≫ ψ')
    (hμ : (pullbackFunctor f.toLRSHom.toShHom).map μ ≫ θs.hom =
      Stacks.RingedSpace.comparison f.toLRSHom.toShHom Od Ok ≫ tensorMap θd.hom θk.hom ≫ μ')
    (hq : (Scheme.Modules.pullback f).map q ≫ θe.hom = θs.hom ≫ q') :
    (pullbackFunctor f.toLRSHom.toShHom).map (tensorMap (Z := Y.toRingedSpace) (𝟙 Od) ψ ≫ μ ≫ q) ≫
        θe.hom =
      (tensorPullbackIso f.toLRSHom.toShHom θd α).hom ≫
        (tensorMap (Z := X.toRingedSpace) (𝟙 Od') ψ' ≫ μ' ≫ q') := by
  have hL := ((pullbackFunctor f.toLRSHom.toShHom).map_comp (tensorMap (𝟙 Od) ψ)
    (μ ≫ q)).trans (congrArg (_ ≫ ·) ((pullbackFunctor f.toLRSHom.toShHom).map_comp μ q))
  have hC : (pullbackFunctor f.toLRSHom.toShHom).map (tensorMap (𝟙 Od) ψ) ≫
      Stacks.RingedSpace.comparison f.toLRSHom.toShHom Od Ok =
      Stacks.RingedSpace.comparison f.toLRSHom.toShHom Od A ≫
        tensorMap (𝟙 _) ((pullbackFunctor f.toLRSHom.toShHom).map ψ) :=
    (comparison_naturality f.toLRSHom.toShHom (𝟙 Od) ψ).trans
      (congrArg (fun t => _ ≫ tensorMap t _) ((pullbackFunctor f.toLRSHom.toShHom).map_id _))
  have hψ' : (pullbackFunctor f.toLRSHom.toShHom).map ψ ≫ θk.hom = α.hom ≫ ψ' := hψ
  have hT : tensorMap (𝟙 _) ((pullbackFunctor f.toLRSHom.toShHom).map ψ) ≫
        tensorMap θd.hom θk.hom = tensorMap θd.hom α.hom ≫ tensorMap (𝟙 Od') ψ' :=
    (tensorMap_comp _ _ _ _).trans ((congrArg₂ (fun a b => tensorMap a b)
      ((Category.id_comp _).trans (Category.comp_id _).symm) hψ').trans
      (tensorMap_comp _ _ _ _).symm)
  have hq' : (pullbackFunctor f.toLRSHom.toShHom).map q ≫ θe.hom = θs.hom ≫ q' := hq
  have hP : Stacks.RingedSpace.comparison f.toLRSHom.toShHom Od A ≫ tensorMap θd.hom α.hom =
      (tensorPullbackIso f.toLRSHom.toShHom θd α).hom := rfl
  exact pairing_chase hL hq' hμ hC hT hP rfl

/-- `pairing_pullback`, with the tensor products of
`Stacks.SheafOfModules.TensorStalkRingedSpace` and the pullback of schemes. -/
public theorem pairing_pullbackT (ψ : A ⟶ Ok) (ψ' : A' ⟶ Ok')
    (μ : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (Od, Ok) ⟶ Os)
    (μ' : (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj (Od', Ok') ⟶ Os')
    (q : Os ⟶ Oe) (q' : Os' ⟶ Oe')
    (hψ : (Scheme.Modules.pullback f).map ψ ≫ θk.hom = α.hom ≫ ψ')
    (hμ : (pullbackFunctor f.toLRSHom.toShHom).map μ ≫ θs.hom =
      Stacks.RingedSpace.comparison f.toLRSHom.toShHom Od Ok ≫ tensorMap θd.hom θk.hom ≫ μ')
    (hq : (Scheme.Modules.pullback f).map q ≫ θe.hom = θs.hom ≫ q') :
    (Scheme.Modules.pullback f).map (tensorMap (Z := Y.toRingedSpace) (𝟙 Od) ψ ≫ μ ≫ q) ≫ θe.hom =
      (tensorPullbackIsoT f θd α).hom ≫ (tensorMap (Z := X.toRingedSpace) (𝟙 Od') ψ' ≫ μ' ≫ q') :=
  pairing_pullback f θd θk θs θe α ψ ψ' μ μ' q q' hψ hμ hq

end PairingPullback

end Stacks.AlgebraicGeometry.ProjectiveBundleCohomology

end

