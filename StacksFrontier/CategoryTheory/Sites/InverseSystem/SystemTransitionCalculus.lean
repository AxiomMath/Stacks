module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.InjectiveSystemsOfAbelianSheaves
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose

/-!
# The transitions of a system of abelian sheaves: identity and composition laws

For a system `F` of abelian sheaves on an inverse system of sites with finite coverings, the
adjoint-form transition `transition D F a : F_j ⟶ u_a^* F_k` along `a : k ⟶ j` satisfies an
identity law and a composition law. This file states both in `eqToHom` form, against the system's
own equalities of functors `u_{𝟙} = 𝟭` and `u_{a ≫ b} = u_b ⋙ u_a`, so that no comparison
isomorphism of direct images appears; it records the transition as a morphism of sheaves; and it
assembles a system from transition maps written in the direct-image direction.

## Main definitions

* `Stacks.WeakSites.ColimitSiteCohomology.pushforwardTransition` — the transition as a morphism
  of sheaves `F_j ⟶ f_{a,*} F_k`.
* `Stacks.WeakSites.ColimitSiteCohomology.systemOfDirectImageMaps` — a system of abelian sheaves
  from transition maps `F_j ⟶ f_{a,*} F_i` satisfying the identity and composition laws.

## Main results

* `Stacks.WeakSites.ColimitSiteCohomology.transition_id_eq` and `transition_comp_eq` — the two
  laws of the transitions in `eqToHom` form.
* `Stacks.WeakSites.ColimitSiteCohomology.transition_systemOfDirectImageMaps` — the transitions of
  `systemOfDirectImageMaps` are the given maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sites.InverseSystem

universe v u w t

namespace Stacks.WeakSites.ColimitSiteCohomology

open InverseSystemOfFiniteSites

variable (D : InverseSystemOfFiniteSites.{v, u, w})

/-- The identification `𝟭 ≅ f_{𝟙,*}` on sections: transport along `u_{𝟙} = 𝟭`. -/
theorem abelianSheafPushforwardIdIso_hom_app_hom_app (j : D.I)
    (X : Sheaf (D.J j) Ab.{max u v w t}) (U : D.C j) :
    (((abelianSheafPushforwardIdIso.{v, u, w, t} D j).hom.app X).hom.app (op U)) =
      X.obj.map (eqToHom (congrArg op (Functor.congr_obj (D.id_map j).symm U))) := by
  dsimp [abelianSheafPushforwardIdIso, abelianSheafPushforward]
  simp only [Functor.sheafPushforwardContinuousId, Iso.refl_inv, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom, Functor.sheafPushforwardContinuousIso_inv, eqToIso.hom,
    Functor.sheafPushforwardContinuousNatTrans_app_hom, ObjectProperty.ι_obj,
    Functor.whiskerRight_app, Functor.op_obj, Functor.id_obj, NatTrans.op_app, eqToHom_app,
    eqToHom_op]
  exact Category.id_comp _

/-- The comparison `f_{a,*} ⋙ f_{b,*} ≅ f_{a ≫ b,*}` on sections: transport along
`u_{a ≫ b} = u_b ⋙ u_a`. -/
theorem abelianSheafPushforwardCompIso_hom_app_hom_app {j k l : D.I} (a : j ⟶ k) (b : k ⟶ l)
    (X : Sheaf (D.J j) Ab.{max u v w t}) (U : D.C l) :
    (((abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app X).hom.app (op U)) =
      X.obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp a b).symm U))) := by
  let _ := D.continuous a
  let _ := D.continuous b
  let _ := D.continuous (a ≫ b)
  dsimp [abelianSheafPushforwardCompIso, abelianSheafPushforward]
  exact sheafPushforwardContinuousComp'_hom_app_app.{w, max u v w t} (D.comp a b).symm
    (D.J l) (D.J k) (D.J j) X U

/-- The inverse of the comparison `f_{a,*} ⋙ f_{b,*} ≅ f_{a ≫ b,*}` on sections: transport along
`u_{a ≫ b} = u_b ⋙ u_a`, read backwards. -/
theorem abelianSheafPushforwardCompIso_inv_app_hom_app {j k l : D.I} (a : j ⟶ k) (b : k ⟶ l)
    (X : Sheaf (D.J j) Ab.{max u v w t}) (U : D.C l) :
    (((abelianSheafPushforwardCompIso.{v, u, w, t} D a b).inv.app X).hom.app (op U)) =
      X.obj.map (eqToHom (congrArg op (Functor.congr_obj (D.comp a b).symm.symm U))) := by
  let _ := D.continuous a
  let _ := D.continuous b
  let _ := D.continuous (a ≫ b)
  dsimp [abelianSheafPushforwardCompIso, abelianSheafPushforward]
  exact sheafPushforwardContinuousComp'_inv_app_app.{w, max u v w t} (D.comp a b).symm
    (D.J l) (D.J k) (D.J j) X U

variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)

/-- **The transition of a system of abelian sheaves as a morphism of sheaves**, in adjoint
(direct-image) form: the adjunct of `F.map a : f_a⁻¹F_j ⟶ F_i` under `abelianSheafAdjunction`.
`transition` is its underlying map of presheaves (`pushforwardTransition_hom`). -/
def pushforwardTransition {i j : D.I} (a : i ⟶ j) :
    F.obj j ⟶ (abelianSheafPushforward.{v, u, w, t} D a).obj (F.obj i) :=
  (abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _ (F.map a)

/-- The underlying map of presheaves of `pushforwardTransition D F a` is `transition D F a`. -/
theorem pushforwardTransition_hom {i j : D.I} (a : i ⟶ j) :
    (pushforwardTransition D F a).hom = transition D F a :=
  rfl

/-- **The identity law of the transitions, in `eqToHom` form**: the transition at an identity is
the transport along the system's own equality `u_{𝟙 i} = 𝟭`. -/
alias transition_id_eq := transition_id_eqToHom

/-- **The composition law of the transitions, in `eqToHom` form**: the transition along a
composite is the two transitions, whiskered, followed by the transport along the system's own
equality `u_{a ≫ b} = u_b ⋙ u_a`. -/
alias transition_comp_eq := transition_comp_eqToHom

/-- **A system of abelian sheaves from transition maps written in the direct-image direction.**
A sheaf on each level together with maps `F_j ⟶ f_{a,*} F_i` that take the identity transition to
the canonical identification and a composite transition to the composite determines a system, the
two cocycle conditions of the system being the transposes of the two hypotheses. -/
def systemOfDirectImageMaps
    (F : ∀ i, Sheaf (D.J i) (Ab.{max u v w t}))
    (φ : ∀ {i j} (a : i ⟶ j), F j ⟶ (abelianSheafPushforward.{v, u, w, t} D a).obj (F i))
    (hid : ∀ i, φ (𝟙 i) = (abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app (F i))
    (hcomp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k), φ (a ≫ b) = φ b ≫
      (abelianSheafPushforward.{v, u, w, t} D b).map (φ a) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app (F i)) :
    AbelianSheafSystem.{v, u, w, t} D where
  obj := F
  map a := (abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _ |>.symm <| φ a
  map_id i := by
    have hh : (abelianSheafAdjunction.{v, u, w, t} D (𝟙 i)).homEquiv (F i) (F i)
        ((abelianSheafPullbackIdIso.{v, u, w, t} D i).hom.app (F i)) = φ (𝟙 i) := by
      rw [hid]
      exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _
    rw [← hh]
    simpa only [Equiv.symm_apply_apply, Functor.id_obj] using
      (abelianSheafPullbackIdIso.{v, u, w, t} D i).inv_hom_id_app (F i)
  map_comp {i j k} a b := by
    apply (abelianSheafAdjunction.{v, u, w, t} D (a ≫ b)).homEquiv _ _ |>.injective
    dsimp only [abelianSheafPullbackCompIso]
    rw [Adjunction.homEquiv_leftAdjointUniq_inv_app_comp, Adjunction.homEquiv_ofNatIsoRight_apply,
      Adjunction.comp_homEquiv]
    change ((abelianSheafAdjunction.{v, u, w, t} D b).homEquiv _ _)
      (((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _)
        ((abelianSheafPullback.{v, u, w, t} D a).map
          (((abelianSheafAdjunction.{v, u, w, t} D b).homEquiv _ _).symm (φ b)) ≫
          ((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv _ _).symm (φ a))) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app (F i) = _
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
    exact (hcomp a b).symm

/-- The adjoint-form transitions of `systemOfDirectImageMaps` are the given maps. -/
theorem transition_systemOfDirectImageMaps
    (F : ∀ i, Sheaf (D.J i) (Ab.{max u v w t}))
    (φ : ∀ {i j} (a : i ⟶ j), F j ⟶ (abelianSheafPushforward.{v, u, w, t} D a).obj (F i))
    (hid : ∀ i, φ (𝟙 i) = (abelianSheafPushforwardIdIso.{v, u, w, t} D i).hom.app (F i))
    (hcomp : ∀ {i j k} (a : i ⟶ j) (b : j ⟶ k), φ (a ≫ b) = φ b ≫
      (abelianSheafPushforward.{v, u, w, t} D b).map (φ a) ≫
        (abelianSheafPushforwardCompIso.{v, u, w, t} D a b).hom.app (F i))
    {i j : D.I} (a : i ⟶ j) :
    transition.{v, u, w, t} D (systemOfDirectImageMaps.{v, u, w, t} D F φ hid hcomp) a =
      (φ a).hom :=
  congrArg (fun g => g.hom)
    ((abelianSheafAdjunction.{v, u, w, t} D a).homEquiv (F j) (F i) |>.apply_symm_apply (φ a))

end Stacks.WeakSites.ColimitSiteCohomology

end
