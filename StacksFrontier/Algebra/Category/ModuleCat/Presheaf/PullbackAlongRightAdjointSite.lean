module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# The mate of a direct-image comparison along a functor with a left adjoint

Let `F : C ⥤ D` be a functor with a left adjoint `G ⊣ F`, let `φ : S ⟶ F.op ⋙ R` be a morphism
of presheaves of rings and let `η : M ⟶ φ_* P` be a morphism from a presheaf of `S`-modules to
the direct image of a presheaf of `R`-modules. This file gives a sectionwise criterion for the
mate `φ^* M ⟶ P` of `η` under the pullback–direct image adjunction to be an isomorphism: for
every object `X` of `D`,

* the map of rings `S(G X) ⟶ R(F G X) ⟶ R(X)`, the second arrow restriction along the unit
  `X ⟶ F G X`, is surjective, and
* the map of sections `M(G X) ⟶ P(F G X) ⟶ P(X)` is bijective.

The mate is then an isomorphism by the Yoneda lemma: every morphism `M ⟶ φ_* Q` factors uniquely
as `η` followed by the direct image of a morphism `P ⟶ Q`, which is constructed section by section
through the bijections above.

This is the shape of **Stacks 075D** part (2): for an étale morphism, base change of small étale
sites has post-composition as a left adjoint, and both maps above are restrictions along an
isomorphism.

## Main definitions

* `PresheafOfModules.unitSectionsMap`: the map `M(G X) ⟶ P(X)` attached to `η`.
* `PresheafOfModules.unitRingMap`: the map of rings `S(G X) ⟶ R(X)`.

## Main results

* `PresheafOfModules.isIso_pullbackPushforwardAdjunction_homEquiv_symm_of_bijective`: the
  criterion.
-/

@[expose] public section

open CategoryTheory Opposite

universe v v₁ v₂ u₁ u₂ u

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F)
  {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)
  {M : PresheafOfModules.{v} S}

/-- A morphism `η : M ⟶ φ_* P` read as a morphism of abelian presheaves
`M ⟶ P ∘ F^op`. -/
noncomputable def pushforwardPresheafHom {P : PresheafOfModules.{v} R}
    (η : M ⟶ (pushforward.{v} φ).obj P) : M.presheaf ⟶ F.op ⋙ P.presheaf :=
  (toPresheaf S).map η

/-- `pushforwardPresheafHom` does not change sections. -/
theorem pushforwardPresheafHom_app_apply {P : PresheafOfModules.{v} R}
    (η : M ⟶ (pushforward.{v} φ).obj P) (W : Cᵒᵖ) (m : M.obj W) :
    (pushforwardPresheafHom φ η).app W m = η.app W m :=
  rfl

/-- The map of sections `M(G X) ⟶ P(F G X) ⟶ P(X)` attached to a morphism `η : M ⟶ φ_* P` and an
adjunction `G ⊣ F`: the component of `η` at `G X` followed by restriction along the unit
`X ⟶ F G X`, as a morphism of abelian groups. -/
noncomputable def unitSectionsMap {P : PresheafOfModules.{v} R}
    (η : M ⟶ (pushforward.{v} φ).obj P) (X : Dᵒᵖ) :
    M.presheaf.obj (op (G.obj X.unop)) ⟶ P.presheaf.obj X :=
  (pushforwardPresheafHom φ η).app (op (G.obj X.unop)) ≫ P.presheaf.map (adj.unit.app X.unop).op

/-- The ring map `S(G X) ⟶ R(F G X) ⟶ R(X)` along which `unitSectionsMap` is semilinear. -/
noncomputable def unitRingMap (X : Dᵒᵖ) : S.obj (op (G.obj X.unop)) ⟶ R.obj X :=
  φ.app (op (G.obj X.unop)) ≫ R.map (adj.unit.app X.unop).op

variable {adj φ}

/-- `unitSectionsMap` on sections. -/
theorem unitSectionsMap_apply {P : PresheafOfModules.{v} R}
    (η : M ⟶ (pushforward.{v} φ).obj P) (X : Dᵒᵖ) (m : M.obj (op (G.obj X.unop))) :
    unitSectionsMap adj φ η X m =
      P.map (adj.unit.app X.unop).op (η.app (op (G.obj X.unop)) m) :=
  rfl

/-- `unitSectionsMap` is semilinear along `unitRingMap`. -/
theorem unitSectionsMap_smul {P : PresheafOfModules.{v} R}
    (η : M ⟶ (pushforward.{v} φ).obj P) (X : Dᵒᵖ) (s : S.obj (op (G.obj X.unop)))
    (m : M.obj (op (G.obj X.unop))) :
    unitSectionsMap adj φ η X (s • m) = unitRingMap adj φ X s • unitSectionsMap adj φ η X m := by
  let n : P.obj (op (F.obj (G.obj X.unop))) := η.app (op (G.obj X.unop)) m
  have h : η.app (op (G.obj X.unop)) (s • m) = (φ.app (op (G.obj X.unop)) s • n) :=
    (η.app (op (G.obj X.unop))).hom.map_smul s m
  rw [unitSectionsMap_apply, unitSectionsMap_apply, h]
  exact P.map_smul _ _ _

/-- Naturality of `unitSectionsMap`. -/
theorem unitSectionsMap_naturality {P : PresheafOfModules.{v} R}
    (η : M ⟶ (pushforward.{v} φ).obj P) {X Y : Dᵒᵖ} (f : X ⟶ Y) :
    M.presheaf.map (G.map f.unop).op ≫ unitSectionsMap adj φ η Y =
      unitSectionsMap adj φ η X ≫ P.presheaf.map f := by
  have hnat : M.presheaf.map (G.map f.unop).op ≫
      (pushforwardPresheafHom φ η).app (op (G.obj Y.unop)) =
      (pushforwardPresheafHom φ η).app (op (G.obj X.unop)) ≫
        P.presheaf.map (F.map (G.map f.unop)).op :=
    (pushforwardPresheafHom φ η).naturality (G.map f.unop).op
  simp only [unitSectionsMap]
  rw [← Category.assoc, hnat, Category.assoc, Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 2
  exact Quiver.Hom.unop_inj (adj.unit.naturality f.unop).symm

/-- `unitSectionsMap` recovers `η` through the counit. -/
theorem unitSectionsMap_counit {P : PresheafOfModules.{v} R}
    (η : M ⟶ (pushforward.{v} φ).obj P) (W : Cᵒᵖ) :
    M.presheaf.map (adj.counit.app W.unop).op ≫ unitSectionsMap adj φ η (op (F.obj W.unop)) =
      (pushforwardPresheafHom φ η).app W := by
  have hnat : M.presheaf.map (adj.counit.app W.unop).op ≫
      (pushforwardPresheafHom φ η).app (op (G.obj (F.obj W.unop))) =
      (pushforwardPresheafHom φ η).app W ≫ P.presheaf.map (F.map (adj.counit.app W.unop)).op :=
    (pushforwardPresheafHom φ η).naturality (adj.counit.app W.unop).op
  simp only [unitSectionsMap]
  rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp, ← op_comp,
    adj.right_triangle_components W.unop]
  exact (congrArg _ (P.presheaf.map_id (op (F.obj W.unop)))).trans (Category.comp_id _)

/-- `unitSectionsMap` is natural in the target module, on sections. -/
theorem app_unitSectionsMap {P Q : PresheafOfModules.{v} R}
    (η : M ⟶ (pushforward.{v} φ).obj P) (g : P ⟶ Q) (X : Dᵒᵖ) (m : M.obj (op (G.obj X.unop))) :
    g.app X (unitSectionsMap adj φ η X m) =
      unitSectionsMap adj φ (η ≫ (pushforward.{v} φ).map g) X m := by
  rw [unitSectionsMap_apply, unitSectionsMap_apply]
  exact naturality_apply g (adj.unit.app X.unop).op (η.app (op (G.obj X.unop)) m)

variable (adj) in
/-- **The mate of a direct-image comparison along a functor with a left adjoint is an
isomorphism** as soon as, at every object `X` of `D`, the ring map `S(G X) ⟶ R(X)` and the map of
sections `M(G X) ⟶ P(X)` obtained through the unit of `G ⊣ F` are isomorphisms. -/
theorem isIso_pullbackPushforwardAdjunction_homEquiv_symm_of_isIso
    [hφ : (pushforward.{v} φ).IsRightAdjoint] {P : PresheafOfModules.{v} R}
    (η : M ⟶ (pushforward.{v} φ).obj P)
    (hR : ∀ X : Dᵒᵖ, IsIso (unitRingMap adj φ X))
    (hP : ∀ X : Dᵒᵖ, IsIso (unitSectionsMap adj φ η X)) :
    IsIso (((pullbackPushforwardAdjunction.{v} φ).homEquiv M P).symm η) := by
  set A := pullbackPushforwardAdjunction.{v} φ
  set c := (A.homEquiv M P).symm η
  rw [isIso_iff_coyoneda_map_bijective]
  intro Q
  have key : ∀ g : P ⟶ Q, A.homEquiv M Q (c ≫ g) = η ≫ (pushforward.{v} φ).map g := by
    intro g
    rw [A.homEquiv_naturality_right, Equiv.apply_symm_apply]
  have hfun : (fun g : P ⟶ Q => c ≫ g) =
      (A.homEquiv M Q).symm ∘ fun g : P ⟶ Q => η ≫ (pushforward.{v} φ).map g := by
    funext g
    simp only [Function.comp_apply, ← key, Equiv.symm_apply_apply]
  have hsurj : ∀ X p, ∃ m, unitSectionsMap adj φ η X m = p := fun X p =>
    ⟨_, ConcreteCategory.congr_hom (IsIso.inv_hom_id (unitSectionsMap adj φ η X)) p⟩
  show Function.Bijective (fun g : P ⟶ Q => c ≫ g)
  rw [hfun]
  refine (A.homEquiv M Q).symm.bijective.comp ⟨fun g₁ g₂ hg => ?_, fun k => ?_⟩
  · ext X p
    obtain ⟨m, rfl⟩ := hsurj X p
    have hg' : η ≫ (pushforward.{v} φ).map g₁ = η ≫ (pushforward.{v} φ).map g₂ := hg
    exact (app_unitSectionsMap η g₁ X m).trans
      ((congrArg (fun ζ => unitSectionsMap adj φ ζ X m) hg').trans
        (app_unitSectionsMap η g₂ X m).symm)
  · have hinv : ∀ X x, inv (unitSectionsMap adj φ η X) (unitSectionsMap adj φ η X x) = x :=
      fun X x => ConcreteCategory.congr_hom (IsIso.hom_inv_id (unitSectionsMap adj φ η X)) x
    have hrsurj : ∀ X r, ∃ s, unitRingMap adj φ X s = r := fun X r =>
      ⟨_, ConcreteCategory.congr_hom (IsIso.inv_hom_id (unitRingMap adj φ X)) r⟩
    let gab : P.presheaf ⟶ Q.presheaf :=
      { app := fun X => inv (unitSectionsMap adj φ η X) ≫ unitSectionsMap adj φ k X
        naturality := by
          intro X Y f
          rw [← cancel_epi (unitSectionsMap adj φ η X)]
          have h₁ := unitSectionsMap_naturality (adj := adj) η f
          have h₂ := unitSectionsMap_naturality (adj := adj) k f
          rw [← Category.assoc (unitSectionsMap adj φ η X) (P.presheaf.map f), ← h₁,
            Category.assoc, IsIso.hom_inv_id_assoc]
          simp only [Category.assoc, IsIso.hom_inv_id_assoc, h₂] }
    have hgab : ∀ X m, gab.app X (unitSectionsMap adj φ η X m) = unitSectionsMap adj φ k X m :=
      fun X m => by
        show unitSectionsMap adj φ k X
          (inv (unitSectionsMap adj φ η X) (unitSectionsMap adj φ η X m)) = _
        rw [hinv]
    have hlin : ∀ (X : Dᵒᵖ) (r : R.obj X) (p : P.obj X), gab.app X (r • p) = r • gab.app X p := by
      intro X r p
      obtain ⟨s, rfl⟩ := hrsurj X r
      obtain ⟨m, rfl⟩ := hsurj X p
      calc gab.app X (unitRingMap adj φ X s • unitSectionsMap adj φ η X m)
          = gab.app X (unitSectionsMap adj φ η X (s • m)) :=
            congrArg _ (unitSectionsMap_smul (adj := adj) η X s m).symm
        _ = unitRingMap adj φ X s • unitSectionsMap adj φ k X m :=
            (hgab X (s • m)).trans (unitSectionsMap_smul (adj := adj) k X s m)
        _ = unitRingMap adj φ X s • gab.app X (unitSectionsMap adj φ η X m) :=
          congrArg _ (hgab X m).symm
    refine ⟨homMk gab hlin, ?_⟩
    ext W m
    have hc : ∀ (N : PresheafOfModules.{v} R) (ζ : M ⟶ (pushforward.{v} φ).obj N),
        unitSectionsMap adj φ ζ (op (F.obj W.unop)) (M.map (adj.counit.app W.unop).op m) =
          ζ.app W m := fun N ζ => ConcreteCategory.congr_hom (unitSectionsMap_counit ζ W) m
    show gab.app (op (F.obj W.unop)) (η.app W m) = k.app W m
    rw [← hc P η]
    exact (hgab _ _).trans (hc Q k)

end PresheafOfModules
