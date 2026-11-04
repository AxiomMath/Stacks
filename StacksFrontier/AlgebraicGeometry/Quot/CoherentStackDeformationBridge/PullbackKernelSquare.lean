module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackDeformationBridge.PullbackTrivial
public import StacksFrontier.AlgebraicGeometry.Quot.Helpers.SmallEtaleThickenedModulesRestrictIso
public import StacksFrontier.Deformation.ToposThickening.Helpers.ThickeningTargetKernelMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp

/-!
# The kernel square of the pullback of a lift

Let `ξ = (T, 𝒢)` be an object of `Coh_{X/Y}` (Stacks 08KB), `L` a lift of `ξ` across
`h : T ⟶ T'` and `g : T'₂ ⟶ T'` a morphism under `T`. The unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` is a map of
the extensions attached to `L` and to its pullback (Stacks 08MQ), lying over the comparison
`(X_h)_*𝒢 ≅ (X_g)_*(X_{h₂})_*𝒢` of Stacks 03LU; on the kernels it is the map of square-zero ideals
induced by `X_g` tensored with `𝒢`.

## Main results

* `AlgebraicGeometry.Space.restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_eq`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08MQ](https://stacks.math.columbia.edu/tag/08MQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

-- Typeclass search for `(smallEtaleRingedTopos X).J.HasSheafCompose (forget RingCat)` exceeds
-- 1000 heartbeats below priority 10000.
attribute [local instance 10000]
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget_ringCat
  AlgebraicGeometry.Space.smallEtaleRingedTopos_hasSheafCompose_forget₂_commRingCat

universe e u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y Z : AlgebraicSpaces B S hS}

/-- **`Ψ₀ ∘ f_* ≅ k_*` of the small étale thickened topoi is the comparison
`AlgebraicGeometry.Space.pushforwardModulesCompAt` of Stacks 03LU**, read through `j_*M ≅ Ψ₀M`, for
`f ≫ g = k`. -/
theorem restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_eq (f : X ⟶ Y)
    (g : Y ⟶ Z) {k : X ⟶ Z} (hk : f ≫ g = k)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O)) :
    ((smallEtaleThickeningTargetOfEq f g k hk).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f)).obj M)).hom ≫
      (structureRestrict (smallEtaleRingedToposHom B S hS k)).map
        ((smallEtaleThickenedModulesCompIso f g k hk).hom.app M) =
      (pushforwardModulesCompAt B S hS f g).hom.app M ≫
        eqToHom (congrArg (fun x : X ⟶ Z =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) hk) := by
  subst hk
  refine ((smallEtaleThickeningTargetOfEq f g (f ≫ g) rfl).restrictIso_hom_comp_map_hom_app_eq
    (smallEtaleThickenedModulesCompIso f g (f ≫ g) rfl)
    (smallEtaleThickeningTargetPushforwardIso f g (f ≫ g) rfl)
    (moduleSheafFunctor_map_smallEtaleThickenedModulesCompIso_hom_app f g (f ≫ g) rfl)
    (pushforwardModulesCompAt B S hS f g) M
    (moduleSheafFunctor_map_pushforwardModulesCompAt_hom_app B S hS f g M)).trans ?_
  exact (Category.comp_id _).symm



/-- If `u₁ ≫ u₂ ≫ X = t` and `r ≫ G(e) = X` for an isomorphism `e`, then
`u₁ ≫ u₂ ≫ r = t ≫ G(e⁻¹)`. -/
private theorem comp_comp_eq_comp_map_of_comp_eq {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    (G : C₁ ⥤ C₂) {P Q : C₁} {A₀ A₁ R W : C₂} (u₁ : A₀ ⟶ A₁) (u₂ : A₁ ⟶ R) (eh : P ⟶ Q)
    (ei : Q ⟶ P) (hei : eh ≫ ei = 𝟙 P) (rh : R ⟶ G.obj P) (X₁ : R ⟶ W) (X₂ : W ⟶ G.obj Q)
    (hX : rh ≫ G.map eh = X₁ ≫ X₂) (t : A₀ ⟶ G.obj Q) (hQ : u₁ ≫ u₂ ≫ X₁ ≫ X₂ = t) :
    u₁ ≫ u₂ ≫ rh = t ≫ G.map ei := by
  rw [← hQ, ← hX]
  simp only [Category.assoc, ← G.map_comp, hei, G.map_id, Category.comp_id]

/-- **A map into `g_*f_*M` read through `j_*M ≅ Ψ₀M`**: if `u₁ ≫ u₂` followed by the comparison
`g_*f_* ≅ k_*` of Stacks 03LU is `t`, then `u₁ ≫ u₂` followed by `j_*M ≅ Ψ₀M` is `t` followed by
`k_*M ≅ Ψ₀ f_*M`. -/
theorem comp_comp_restrictIso_hom_eq_comp_map_smallEtaleThickenedModulesCompIso_inv_app
    (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z} (hk : f ≫ g = k)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X).O))
    {A₀ A₁ : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS Z).O)} (u₁ : A₀ ⟶ A₁)
    (u₂ : A₁ ⟶ (smallEtaleRingedToposHom B S hS g).pushforwardModules.obj
      ((smallEtaleRingedToposHom B S hS f).pushforwardModules.obj M))
    (t : A₀ ⟶ (smallEtaleRingedToposHom B S hS k).pushforwardModules.obj M)
    (hQ : u₁ ≫ u₂ ≫ (pushforwardModulesCompAt B S hS f g).hom.app M ≫
        eqToHom (congrArg (fun x : X ⟶ Z =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) hk) = t) :
    u₁ ≫ u₂ ≫ ((smallEtaleThickeningTargetOfEq f g k hk).restrictIso
        ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS f)).obj M)).hom =
      t ≫ (structureRestrict (smallEtaleRingedToposHom B S hS k)).map
        ((smallEtaleThickenedModulesCompIso f g k hk).inv.app M) :=
  comp_comp_eq_comp_map_of_comp_eq (structureRestrict (smallEtaleRingedToposHom B S hS k)) u₁ u₂
    ((smallEtaleThickenedModulesCompIso f g k hk).hom.app M)
    ((smallEtaleThickenedModulesCompIso f g k hk).inv.app M)
    ((smallEtaleThickenedModulesCompIso f g k hk).hom_inv_id_app M) _ _ _
    (restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_eq f g hk M) t hQ

/-- The comparison `b_*a_* ≅ k_*` of Stacks 03LU for `a ≫ b = k`, on an object. -/
theorem pushforwardModulesCompAt_trans_eqToIso_hom_app {X₀ X₁ X₂ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) {k : X₀ ⟶ X₂} (e : a ≫ b = k)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (pushforwardModulesCompAt B S hS a b ≪≫
      eqToIso (congrArg (fun x : X₀ ⟶ X₂ => (smallEtaleRingedToposHom B S hS x).pushforwardModules)
        e)).hom.app M =
      (pushforwardModulesCompAt B S hS a b).hom.app M ≫
        eqToHom (congrArg (fun x : X₀ ⟶ X₂ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) e) := by
  subst e
  simp

/-- The identification `a_* ⋙ c_* ≅ 𝟭` for `a ≫ c = 𝟙`, at the level of functors. -/
theorem pushforwardModulesRetractionIso_hom {X₀ X₁ : AlgebraicSpaces B S hS} (a : X₀ ⟶ X₁)
    (c : X₁ ⟶ X₀) (hac : a ≫ c = 𝟙 X₀) :
    (CoherentSituation.pushforwardModulesRetractionIso a c hac).hom =
      (pushforwardModulesCompAt B S hS a c).hom ≫
        (eqToIso (congrArg (fun x : X₀ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) hac)).hom ≫
        (CoherentSituation.pushforwardModulesIsoIdSmallEtaleTopos X₀).inv :=
  (Iso.trans_hom _ _).trans (congrArg (_ ≫ ·) ((Iso.trans_hom _ _).trans
    (congrArg (_ ≫ ·) (Iso.symm_hom _))))

/-- The component of the identification `a_* ≅ c_*` of direct images of modules along `a = c`. -/
theorem pushforwardModules_eqToIso_hom_app {X₀ X₁ : AlgebraicSpaces B S hS} {a c : X₀ ⟶ X₁}
    (hac : a = c)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (eqToIso (congrArg (fun x : X₀ ⟶ X₁ =>
      (smallEtaleRingedToposHom B S hS x).pushforwardModules) hac)).hom.app M =
      eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) hac) :=
  (congrArg (fun φ => NatTrans.app φ M) (eqToIso.hom (congrArg (fun x : X₀ ⟶ X₁ =>
    (smallEtaleRingedToposHom B S hS x).pushforwardModules) hac))).trans
    ((eqToHom_app (congrArg (fun x : X₀ ⟶ X₁ =>
      (smallEtaleRingedToposHom B S hS x).pushforwardModules) hac) M).trans rfl)

/-- The identification `a_* ⋙ c_* ≅ 𝟭` for `a ≫ c = 𝟙`, on an object. -/
theorem pushforwardModulesRetractionIso_hom_app {X₀ X₁ : AlgebraicSpaces B S hS} (a : X₀ ⟶ X₁)
    (c : X₁ ⟶ X₀) (hac : a ≫ c = 𝟙 X₀)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (CoherentSituation.pushforwardModulesRetractionIso a c hac).hom.app M =
      (pushforwardModulesCompAt B S hS a c).hom.app M ≫
        eqToHom (congrArg (fun x : X₀ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) hac) ≫
        (CoherentSituation.pushforwardModulesIsoIdSmallEtaleTopos X₀).inv.app M :=
  (NatTrans.congr_app (pushforwardModulesRetractionIso_hom a c hac) M).trans
    ((NatTrans.comp_app _ _ M).trans (congrArg (_ ≫ ·) ((NatTrans.comp_app _ _ M).trans
      (congrArg (· ≫ _) (pushforwardModules_eqToIso_hom_app hac M)))))

/-- Reassociation: `m ≫ p ≫ q = u ≫ v ≫ w ≫ y` gives `m ≫ p ≫ q ≫ t = (u ≫ v) ≫ w ≫ y ≫ t`. -/
private theorem comp_comp_comp_eq_of_comp_comp_eq {C : Type*} [Category C]
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ : C} (m : P₀ ⟶ P₁) (p : P₁ ⟶ P₂) (q : P₂ ⟶ P₃) (t : P₃ ⟶ P₄)
    (u : P₀ ⟶ P₅) (v : P₅ ⟶ P₆) (w : P₆ ⟶ P₇) (y : P₇ ⟶ P₃)
    (key : m ≫ p ≫ q = u ≫ v ≫ w ≫ y) :
    m ≫ p ≫ q ≫ t = (u ≫ v) ≫ w ≫ y ≫ t := by
  simp only [← Category.assoc] at key ⊢
  rw [key]

/-- **The identifications `c_* k_* ≅ 𝟭` along a factorization**, for small étale ringed topoi:
for `a ≫ b = k`, `b ≫ c = c₂`, `k ≫ c = 𝟙` and `a ≫ c₂ = 𝟙`, the identification along `k` read
through `b_*a_* ≅ k_*` is `c_*b_* ≅ c₂_*` followed by the identification along `a` (the
associativity coherence of Stacks 03LU). -/
theorem pushforwardModulesRetractionIso_hom_app_coherence {X₀ X₁ X₂ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) (c : X₁ ⟶ X₀) {k : X₀ ⟶ X₁} {c₂ : X₂ ⟶ X₀} (e₁ : a ≫ b = k)
    (e₂ : b ≫ c = c₂) (h₁ : k ≫ c = 𝟙 X₀) (h₂ : a ≫ c₂ = 𝟙 X₀)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((pushforwardModulesCompAt B S hS a b).hom.app M ≫
          eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
            (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M) e₁)) ≫
      (CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M =
    (pushforwardModulesCompAt B S hS b c ≪≫
      eqToIso (congrArg (fun x : X₂ ⟶ X₀ => (smallEtaleRingedToposHom B S hS x).pushforwardModules)
        e₂)).hom.app ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M) ≫
      (CoherentSituation.pushforwardModulesRetractionIso a c₂ h₂).hom.app M := by
  refine (congrArg (_ ≫ ·) (pushforwardModulesRetractionIso_hom_app k c h₁ M)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· ≫ ·)
    (pushforwardModulesCompAt_trans_eqToIso_hom_app b c e₂ _).symm
    (pushforwardModulesRetractionIso_hom_app a c₂ h₂ M).symm)
  exact comp_comp_comp_eq_of_comp_comp_eq _ _ _ _ _ _ _ _
    (CoherentSituation.pushforwardModulesCompAt_retraction_coherence a b c e₁ e₂ h₁ h₂ M)

/-- Cancellation: if `X = r ≫ G(e)` for isomorphisms `e`, `r`, and `F(X) ≫ R₁ = Z ≫ R₂`, then
`F(G(e⁻¹) ≫ r⁻¹) ≫ Z ≫ R₂ = R₁`. -/
private theorem map_comp_comp_eq_of_map_comp_eq {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] (G : C₁ ⥤ C₂) (F : C₂ ⥤ C₃) {P Q : C₁} {R : C₂} (eh : P ⟶ Q) (ei : Q ⟶ P)
    (hei : ei ≫ eh = 𝟙 Q) (rh : R ⟶ G.obj P) (ri : G.obj P ⟶ R) (hri : ri ≫ rh = 𝟙 _)
    (X : R ⟶ G.obj Q) (hX : rh ≫ G.map eh = X) {W V : C₃} (R₁ : F.obj (G.obj Q) ⟶ V)
    (Z : F.obj R ⟶ W) (R₂ : W ⟶ V) (hRC : F.map X ≫ R₁ = Z ≫ R₂) :
    F.map (G.map ei ≫ ri) ≫ Z ≫ R₂ = R₁ := by
  rw [← hRC, ← Category.assoc, ← F.map_comp, ← hX, Category.assoc, ← Category.assoc ri, hri,
    Category.id_comp, ← G.map_comp, hei, G.map_id, F.map_id, Category.id_comp]

/-- **The identifications `c_* k_* ≅ 𝟭` and `c₂_* a_* ≅ 𝟭` through `Ψ₀ ∘ a_* ≅ k_*`**: for
`a ≫ b = k`, `b ≫ c = c₂`, `k ≫ c = 𝟙` and `a ≫ c₂ = 𝟙`, the map
`c_*k_*M ⟶ c_*b_*a_*M` given by `Ψ₀ ∘ a_* ≅ k_*` and `j_*M ≅ Ψ₀M`, followed by
`c_*b_* ≅ c₂_*` and the identification along `a`, is the identification along `k`. -/
theorem pushforwardModulesRetractionIso_hom_app_thickenedModulesCompIso
    {X₀ X₁ X₂ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) (c : X₁ ⟶ X₀) {k : X₀ ⟶ X₁} {c₂ : X₂ ⟶ X₀} (e₁ : a ≫ b = k)
    (e₂ : b ≫ c = c₂) (h₁ : k ≫ c = 𝟙 X₀) (h₂ : a ≫ c₂ = 𝟙 X₀)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS X₀).O)) :
    (smallEtaleRingedToposHom B S hS c).pushforwardModules.map
        ((structureRestrict (smallEtaleRingedToposHom B S hS k)).map
            ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M) ≫
          ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
            ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv) ≫
      (pushforwardModulesCompAt B S hS b c ≪≫
        eqToIso (congrArg (fun x : X₂ ⟶ X₀ =>
          (smallEtaleRingedToposHom B S hS x).pushforwardModules) e₂)).hom.app
        ((smallEtaleRingedToposHom B S hS a).pushforwardModules.obj M) ≫
      (CoherentSituation.pushforwardModulesRetractionIso a c₂ h₂).hom.app M =
    (CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M :=
  map_comp_comp_eq_of_map_comp_eq (structureRestrict (smallEtaleRingedToposHom B S hS k))
    (smallEtaleRingedToposHom B S hS c).pushforwardModules
    ((smallEtaleThickenedModulesCompIso a b k e₁).hom.app M)
    ((smallEtaleThickenedModulesCompIso a b k e₁).inv.app M)
    ((smallEtaleThickenedModulesCompIso a b k e₁).inv_hom_id_app M)
    ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).hom
    ((smallEtaleThickeningTargetOfEq a b k e₁).restrictIso
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj M)).inv
    (Iso.inv_hom_id _) _
    (restrictIso_hom_comp_map_smallEtaleThickenedModulesCompIso_hom_app_eq a b e₁ M)
    ((CoherentSituation.pushforwardModulesRetractionIso k c h₁).hom.app M) _ _
    (pushforwardModulesRetractionIso_hom_app_coherence a b c e₁ e₂ h₁ h₂ M)

/-- A map `F₁ ⟶ b_*N` of modules followed by `b_*` of `Y : N ⟶ a_*F₀` and the comparison of
Stacks 03LU, read through the identification of the two direct images along `k = a ≫ b`. -/
theorem comp_pushforwardModulesIsoModulePushforward_inv_app_comp_map_comp_eq
    {X₀ X₂ X₁ : AlgebraicSpaces B S hS}
    (a : X₀ ⟶ X₂) (b : X₂ ⟶ X₁) {k : X₀ ⟶ X₁} (e : a ≫ b = k)
    {F₁ : Modules.{u, u} B S hS X₁.1 X₁.2} {N : Modules.{u, u} B S hS X₂.1 X₂.2}
    {F₀ : Modules.{u, u} B S hS X₀.1 X₀.2} (v : F₁ ⟶ (modulePushforward B S hS b).obj N)
    (Y : N ⟶ (structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj F₀))
    (Y' : N ⟶ (smallEtaleRingedToposHom B S hS a).pushforwardModules.obj F₀)
    (hY : @Eq (N ⟶ (structureRestrict (smallEtaleRingedToposHom B S hS a)).obj
      ((thickenedModulesFunctor (smallEtaleRingedToposHom B S hS a)).obj F₀)) Y Y') :
    ((v ≫ (pushforwardModulesIsoModulePushforward B S hS b).inv.app N) ≫
      (smallEtaleRingedToposHom B S hS b).pushforwardModules.map Y ≫
      (pushforwardModulesCompAt B S hS a b).hom.app F₀ ≫
      eqToHom (congrArg (fun x : X₀ ⟶ X₁ =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj F₀) e)) ≫
        (pushforwardModulesIsoModulePushforward B S hS k).hom.app F₀ =
      v ≫ (modulePushforward B S hS b).map Y' ≫ (modulePushforward B S hS b).map
          ((pushforwardModulesIsoModulePushforward B S hS a).hom.app F₀) ≫
        (modulePushforwardCompIso B S hS a b ≪≫
          eqToIso (congrArg (modulePushforward B S hS) e)).hom.app F₀ := by
  subst hY
  have hσ := (pushforwardModulesIsoModulePushforward B S hS b).hom.naturality Y
  have key := pushforwardModulesCompAt_hom_app_comp_eqToHom a b e F₀
  refine (Category.assoc _ _ _).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (v ≫ ·) ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((Category.assoc _ _ _).trans key)))).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) hσ).trans (Category.assoc _ _ _)))).trans ?_
  exact Iso.inv_hom_id_app_assoc (pushforwardModulesIsoModulePushforward B S hS b) N _

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} {ξ : CoherentObject D} {T' T'₂ : SchemesOver D.Y}
  {h : ξ.T ⟶ T'} {h₂ : ξ.T ⟶ T'₂}

/-- **The identifications `ρ_* i_* ≅ 𝟭` along a morphism of split thickenings** (the associativity
coherence of Stacks 03LU): for `h₂ ≫ g = h` and retractions `r`, `r₂ = g ≫ r`, the identification
along `h` read through `(X_g)_*(X_{h₂})_* ≅ (X_h)_*` is the comparison
`(X_r)_*(X_g)_* ≅ (X_{r₂})_*` followed by the identification along `h₂`. -/
theorem retractionPushforwardModulesIso_hom_app_pullback (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    {r : T' ⟶ ξ.T} {r₂ : T'₂ ⟶ ξ.T} (hr : h ≫ r = 𝟙 ξ.T) (hr₂ : h₂ ≫ r₂ = 𝟙 ξ.T)
    (hgr : r₂ = g ≫ r)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos B S hS (D.relativeSquareSituation.space ξ.T)).O)) :
    (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap r)).pushforwardModules.map
        ((pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g)).hom.app M ≫
          eqToHom (congrArg (fun x : D.relativeSquareSituation.space ξ.T ⟶
              D.relativeSquareSituation.space T' =>
            (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj M)
            (relativeMap_comp_of_comp_eq g hg))) ≫
      (retractionPushforwardModulesIso h r hr).hom.app M =
    (pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap g)
        (D.relativeSquareSituation.relativeMap r) ≪≫
      eqToIso (congrArg (fun x : D.relativeSquareSituation.space T'₂ ⟶
          D.relativeSquareSituation.space ξ.T =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules)
        (relativeMap_comp_of_eq_comp g hgr))).hom.app
        ((smallEtaleRingedToposHom B S hS
          (D.relativeSquareSituation.relativeMap h₂)).pushforwardModules.obj M) ≫
      (retractionPushforwardModulesIso h₂ r₂ hr₂).hom.app M :=
  pushforwardModulesRetractionIso_hom_app_coherence (D.relativeSquareSituation.relativeMap h₂)
    (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap r)
    (relativeMap_comp_of_comp_eq g hg) (relativeMap_comp_of_eq_comp g hgr)
    (relativeMap_comp_relativeMap_retraction h r hr)
    (relativeMap_comp_relativeMap_retraction h₂ r₂ hr₂) M

/-- **The reduction of a lift through the reduction of its pullback, through `Ψ₀ ∘ i₂_* ≅ i_*`**:
the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'` followed by the direct image of the reduction of the pulled back
lift and `j_*M ≅ Ψ₀M` is the reduction of `L` followed by `i_*𝒢 ≅ Ψ₀ i₂_*𝒢`. -/
theorem ThickeningLift.unit_comp_map_pullback_toThickened_comp_restrictIso_hom (g : T'₂ ⟶ T')
    (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    type_of% (comp_comp_restrictIso_hom_eq_comp_map_smallEtaleThickenedModulesCompIso_inv_app
      (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
      (relativeMap_comp_of_comp_eq g hg) ξ.F _ _ _ (L.unit_comp_map_pullback_toThickened g hg)) :=
  comp_comp_restrictIso_hom_eq_comp_map_smallEtaleThickenedModulesCompIso_inv_app
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (relativeMap_comp_of_comp_eq g hg) ξ.F _ _ _ (L.unit_comp_map_pullback_toThickened g hg)

section Kernel

variable (hh : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
  (hh₂ : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map h₂.left))

/-- The canonical action of the square-zero ideal on the extension attached to a lift is the
identity (`Deformation.ToposThickening.FlatLift.extensionActionMap_fixedActionExtension`). -/
theorem extensionActionMap_thickeningLiftExtension (L : D.ThickeningLift ξ h) :
    (extensionActionMap (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      (thickeningLiftExtension h hh L)).1 = 𝟙 _ :=
  (L.toFlatLift h hh).extensionActionMap_fixedActionExtension
    (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
    (D.relativeSquareSituation.relativeSquareThickening h)
    (D.relativeSquareSituation.relativeSquareLeft h)
    (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
    (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
    (D.relativeSquareSituation.relativeSquare_comm h) (thickenedModule ξ h)
    ((isStrictPullbackIdealMap_iff_isStrict
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
      (D.relativeSquareSituation.relativeSquareThickening h)
      (D.relativeSquareSituation.relativeSquareLeft h)
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquare_comm h)).mpr
      (D.relativeSquareSituation.isStrict_relativeSquare h hh))
    (isFlat_reducedBaseModule_of_isFlatOverBase
      (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.relativeMap h))
      (D.relativeSquareSituation.relativeSquareThickening h)
      (D.relativeSquareSituation.relativeSquareLeft h)
      (relBaseRight (smallEtaleRingedToposHom B S hS (D.relativeSquareSituation.projection T')))
      (D.relativeSquareSituation.relativeMapFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquareThickeningFirstOrderThickening h hh)
      (D.relativeSquareSituation.relativeSquare_comm h) (thickenedModule ξ h)
      (isFlatOverBase_thickenedModule h hh))

/-- The reduction square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`, on the extensions attached to `L`
and to its pullback. -/
theorem unit_comp_map_thickeningLiftExtension_g_comp_restrictIso_hom (g : T'₂ ⟶ T')
    (hg : h₂ ≫ g = h) (L : D.ThickeningLift ξ h) :
    ((smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.relativeMap g)).pullbackAdjPushforwardModulesViaComparison.unit.app
        L.F : (thickeningLiftExtension h hh L).Z.left ⟶
          (smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
            (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
            (relativeMap_comp_of_comp_eq g hg)).j.pushforwardModules.obj
            (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).Z.left) ≫
      (smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
        (relativeMap_comp_of_comp_eq g hg)).j.pushforwardModules.map
        (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).g ≫
      ((smallEtaleThickeningTargetOfEq (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
        (relativeMap_comp_of_comp_eq g hg)).restrictIso (thickenedModule ξ h₂)).hom =
    (thickeningLiftExtension h hh L).g ≫
      (structureRestrict (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h))).map
        ((smallEtaleThickenedModulesCompIso (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) (D.relativeSquareSituation.relativeMap h)
          (relativeMap_comp_of_comp_eq g hg)).inv.app ξ.F) :=
  L.unit_comp_map_pullback_toThickened_comp_restrictIso_hom g hg

/-- The reduction of the extension attached to a lift is the reduction of the lift. -/
theorem thickeningLiftExtension_g_eq (L : D.ThickeningLift ξ h) :
    @Eq ((thickeningLiftExtension h hh L).Z.right ⟶
      (structureRestrict (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap h))).obj
        (thickenedModule ξ h))
      (thickeningLiftExtension h hh L).g (L.toThickened h) :=
  rfl

/-- The reduction square of the unit, step through the reduction of the pulled back lift. -/
theorem unit_comp_map_pullback_toThickened_comp_eq_aux (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    type_of% (congrArg
      (((modulePullbackAdjunction B S hS
        (D.relativeSquareSituation.relativeMap g)).unit.app L.F) ≫ ·)
      ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ (modulePushforwardCompIso B S hS (D.relativeSquareSituation.relativeMap h₂)
            (D.relativeSquareSituation.relativeMap g) ≪≫
          eqToIso (congrArg (modulePushforward B S hS) (relativeMap_comp_of_comp_eq g hg))).hom.app
            ξ.F) (L.modulePushforward_map_pullback_toThickened g hg)))) :=
  (congrArg
    (((modulePullbackAdjunction B S hS
      (D.relativeSquareSituation.relativeMap g)).unit.app L.F) ≫ ·)
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (modulePushforwardCompIso B S hS (D.relativeSquareSituation.relativeMap h₂)
          (D.relativeSquareSituation.relativeMap g) ≪≫
        eqToIso (congrArg (modulePushforward B S hS) (relativeMap_comp_of_comp_eq g hg))).hom.app
          ξ.F) (L.modulePushforward_map_pullback_toThickened g hg))))

/-- **The reduction square of the unit `𝒢' ⟶ (X_g)_*(X_g)^*𝒢'`** (in the spelling of the
extensions attached to `L` and to its pullback). -/
theorem unit_comp_map_thickeningLiftExtension_g (g : T'₂ ⟶ T') (hg : h₂ ≫ g = h)
    (L : D.ThickeningLift ξ h) :
    ((modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap g)).unit.app L.F ≫
        (pushforwardModulesIsoModulePushforward B S hS
          (D.relativeSquareSituation.relativeMap g)).inv.app
          ((modulePullback B S hS (D.relativeSquareSituation.relativeMap g)).obj L.F)) ≫
      (smallEtaleRingedToposHom B S hS
        (D.relativeSquareSituation.relativeMap g)).pushforwardModules.map
        (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).g ≫
      (pushforwardModulesCompAt B S hS (D.relativeSquareSituation.relativeMap h₂)
        (D.relativeSquareSituation.relativeMap g)).hom.app ξ.F ≫
      eqToHom (congrArg (fun x : D.relativeSquareSituation.space ξ.T ⟶
          D.relativeSquareSituation.space T' =>
        (smallEtaleRingedToposHom B S hS x).pushforwardModules.obj ξ.F)
        (relativeMap_comp_of_comp_eq g hg)) = (thickeningLiftExtension h hh L).g := by
  refine (Iso.cancel_iso_hom_right _ _ ((pushforwardModulesIsoModulePushforward B S hS
    (D.relativeSquareSituation.relativeMap h)).app ξ.F)).1 ?_
  refine (comp_pushforwardModulesIsoModulePushforward_inv_app_comp_map_comp_eq
    (D.relativeSquareSituation.relativeMap h₂) (D.relativeSquareSituation.relativeMap g)
    (relativeMap_comp_of_comp_eq g hg) (F₁ := L.F)
    (N := (modulePullback B S hS (D.relativeSquareSituation.relativeMap g)).obj L.F) (F₀ := ξ.F)
    ((modulePullbackAdjunction B S hS (D.relativeSquareSituation.relativeMap g)).unit.app L.F)
    (thickeningLiftExtension h₂ hh₂ (L.pullback g hg)).g ((L.pullback g hg).toThickened h₂)
    (thickeningLiftExtension_g_eq hh₂ (L.pullback g hg))).trans ?_
  refine (unit_comp_map_pullback_toThickened_comp_eq_aux g hg L).trans ?_
  refine (L.reduction_pullback g hg).symm.trans ?_
  refine L.toThickened_comp_pushforwardModulesIsoModulePushforward_hom_app.symm.trans ?_
  exact congrArg (· ≫ _) (thickeningLiftExtension_g_eq hh L).symm

end Kernel

end AlgebraicGeometry.Space.CoherentSituation

end
