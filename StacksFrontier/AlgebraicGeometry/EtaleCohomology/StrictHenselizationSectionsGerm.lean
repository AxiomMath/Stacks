module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsPullbackComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsTransitivityOverBase

/-!
# The map from the stalk of a direct image to sections over the strict henselization, on germs

Let `f : X ⟶ S` be a morphism of schemes, `s` a geometric point of `S` and
`p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` the projection. The map
`(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` of
`AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb` is built from a restriction
of sections of `f_*F` along the structure morphism to `S`, the composition isomorphism for
inverse images and the counit of `f⁻¹ ⊣ f_*`. This file shows that on the germ at `s` of a
section of `f_*F` over an étale neighbourhood `W`, which is a section of `F` over `W ×_S X`, it is
simply the restriction of that section of `F` along the morphism
`X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ W ×_S X` over `X`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_pushforward` — restricting a section of
  `f_*F` along `p ≫ f` and then applying the counit is restricting the corresponding section of
  `F` along `p`.
* `AlgebraicGeometry.pushforwardStalkToSectionsAb` — the map `(f_*F)_s ⟶ Γ(T, p⁻¹F)` for a scheme
  `T` over `X` and over the strict henselization, defined by its values on germs, and
  `AlgebraicGeometry.toPresheafFiber_comp_pushforwardStalkToSectionsAb_app` the germ formula.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {X S T : Scheme.{u}} (f : X ⟶ S) (p : T ⟶ X) (W : S.Etale)
  (ρ : T ⟶ ((smallEtaleBaseChange f).obj W).left)

/-- **Restriction of sections of a direct image.** A section of `f_*F` over `W` is a section of
`F` over the base change `f^*W`. Restricting it, as a section of `f_*F`, to a global section of
`(p ≫ f)⁻¹f_*F` over `T`, rewriting `(p ≫ f)⁻¹ = p⁻¹f⁻¹` and applying `p⁻¹` of the counit
`f⁻¹f_*F ⟶ F`, is restricting it, as a section of `F`, along a lift `ρ : T ⟶ f^*W` of `p`. -/
theorem smallEtaleSectionsPullbackAb_pushforward
    (hρ : ρ ≫ ((smallEtaleBaseChange f).obj W).hom = p)
    (hr : (ρ ≫ pullback.fst W.hom f) ≫ W.hom = p ≫ f)
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtaleSectionsPullbackAb (p ≫ f) W (ρ ≫ pullback.fst W.hom f) hr).app
          ((smallEtalePushforwardAb f).obj F) ≫
        (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
          ((smallEtalePullbackAbCompIso p f).inv.app ((smallEtalePushforwardAb f).obj F)) ≫
        (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
          ((smallEtalePullbackAb p).map ((smallEtaleAdjunctionAb f).counit.app F)) =
      (smallEtaleSectionsPullbackAb p ((smallEtaleBaseChange f).obj W) ρ hρ).app F := by
  rw [← smallEtaleSectionsPullbackAb_comp_app p f W ρ hρ hr]
  have hnat : ((sheafSections (smallEtaleTopology X) Ab.{u + 1}).obj
          (op ((smallEtaleBaseChange f).obj W))).map ((smallEtaleAdjunctionAb f).counit.app F) ≫
        (smallEtaleSectionsPullbackAb p ((smallEtaleBaseChange f).obj W) ρ hρ).app F =
      (smallEtaleSectionsPullbackAb p ((smallEtaleBaseChange f).obj W) ρ hρ).app
          ((smallEtalePullbackAb f).obj ((smallEtalePushforwardAb f).obj F)) ≫
        (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
          ((smallEtalePullbackAb p).map ((smallEtaleAdjunctionAb f).counit.app F)) :=
    (smallEtaleSectionsPullbackAb p ((smallEtaleBaseChange f).obj W) ρ hρ).naturality
      ((smallEtaleAdjunctionAb f).counit.app F)
  have htri : ((smallEtaleAdjunctionAb f).unit.app ((smallEtalePushforwardAb f).obj F)).hom.app
        (op W) ≫ ((sheafSections (smallEtaleTopology X) Ab.{u + 1}).obj
          (op ((smallEtaleBaseChange f).obj W))).map
            ((smallEtaleAdjunctionAb f).counit.app F) = 𝟙 _ :=
    congrArg (fun φ => φ.hom.app (op W)) ((smallEtaleAdjunctionAb f).right_triangle_components F)
  let Γ' := Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}
  let A := ((smallEtaleAdjunctionAb f).unit.app ((smallEtalePushforwardAb f).obj F)).hom.app (op W)
  let Bm := (smallEtaleSectionsPullbackAb p ((smallEtaleBaseChange f).obj W) ρ hρ).app
    ((smallEtalePullbackAb f).obj ((smallEtalePushforwardAb f).obj F))
  let h := Γ'.map ((smallEtalePullbackAbCompIso p f).hom.app ((smallEtalePushforwardAb f).obj F))
  let Γi := Γ'.map ((smallEtalePullbackAbCompIso p f).inv.app ((smallEtalePushforwardAb f).obj F))
  let Γc := Γ'.map ((smallEtalePullbackAb p).map ((smallEtaleAdjunctionAb f).counit.app F))
  have hΓ : h ≫ Γi ≫ Γc = Γc := by
    simp only [h, Γi, Γc]
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  show (A ≫ Bm ≫ h) ≫ Γi ≫ Γc = _
  refine ((Category.assoc A _ _).trans ((congrArg (A ≫ ·) (Category.assoc Bm h _)).trans
    (congrArg (fun x => A ≫ Bm ≫ x) hΓ))).trans ?_
  refine (congrArg (fun x => A ≫ x) hnat).symm.trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) htri).trans (Category.id_comp _))

/-- Global sections of the inverse of a composition isomorphism followed by a renaming of the
composite, computed with the renaming first. -/
theorem sheafΓ_map_compIso_trans_eqToIso_inv_app {T Y Z : Scheme.{u}} (a : T ⟶ Y) (b : Y ⟶ Z)
    {m : T ⟶ Z} (h : a ≫ b = m) (G : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
        ((smallEtalePullbackAbCompIso a b ≪≫
          eqToIso (congrArg (fun m : T ⟶ Z => smallEtalePullbackAb m) h)).inv.app G) =
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
          ((eqToIso (congrArg (fun m : T ⟶ Z => smallEtalePullbackAb m) h.symm)).hom.app G) ≫
        (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
          ((smallEtalePullbackAbCompIso a b).inv.app G) := by
  subst h
  simp

/-- Replacing the morphism `p` by an equal morphism `p'` and the lift `r` by an equal lift `r'`
changes the restriction of sections by the transport along `p = p'` of the inverse images.
This is `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_congr_base`, restated so that its
transport is literally the one used in `AlgebraicGeometry.pushforwardStalkToSectionsAb`. -/
theorem smallEtaleSectionsPullbackAb_congr_base' {Z T : Scheme.{u}} {p p' : T ⟶ Z} (W : Z.Etale)
    {r r' : T ⟶ W.left} (hp : p = p') (hr : r = r') (h : r ≫ W.hom = p)
    (h' : r' ≫ W.hom = p') (G : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtaleSectionsPullbackAb p' W r' h').app G =
      (smallEtaleSectionsPullbackAb p W r h).app G ≫
        (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
          ((eqToIso (congrArg (fun m : T ⟶ Z => smallEtalePullbackAb m) hp)).hom.app G) := by
  subst hp
  subst hr
  simp

/-- Renaming a composite and undoing it, on global sections. -/
@[reassoc]
theorem sheafΓ_map_eqToIso_hom_comp_compIso_trans_inv {T Y Z : Scheme.{u}} (a : T ⟶ Y)
    (b : Y ⟶ Z) {m : T ⟶ Z} (h : a ≫ b = m) (G : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
        ((eqToIso (congrArg (fun m : T ⟶ Z => smallEtalePullbackAb m) h)).hom.app G) ≫
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
        ((smallEtalePullbackAbCompIso a b ≪≫
          eqToIso (congrArg (fun m : T ⟶ Z => smallEtalePullbackAb m) h)).inv.app G) =
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
        ((smallEtalePullbackAbCompIso a b).inv.app G) := by
  subst h
  simp

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)

section General

variable {T : Scheme.{u}} (p : T ⟶ X) (q : T ⟶ strictHenselization B S hS s)
  (cond : p ≫ f = q ≫ strictHenselizationToBase B S hS s)

/-- The morphism `T ⟶ X ×_S W` over `X` into the base change of an étale neighbourhood `W` of
`s`, induced by the canonical morphism from the strict henselization to `W`. -/
def sectionsLift (W : S.Etale) (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    T ⟶ ((smallEtaleBaseChange f).obj W).left :=
  pullback.lift (q ≫ strictHenselizationNeighborhoodLift B S hS s W v) p (by
    rw [Category.assoc, strictHenselizationNeighborhoodLift_comp]
    exact cond.symm)

/-- The lift `sectionsLift` composed with the structure morphism `X ×_S W ⟶ X` is `p`. -/
@[reassoc (attr := simp)]
theorem sectionsLift_hom (W : S.Etale) (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    sectionsLift B hS f s p q cond W v ≫ ((smallEtaleBaseChange f).obj W).hom = p :=
  pullback.lift_snd _ _ _

/-- The lift `sectionsLift` composed with the projection `X ×_S W ⟶ W` is the composite of `q`
with the canonical morphism from the strict henselization to `W`. -/
@[reassoc (attr := simp)]
theorem sectionsLift_fst (W : S.Etale) (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    sectionsLift B hS f s p q cond W v ≫ pullback.fst W.hom f =
      q ≫ strictHenselizationNeighborhoodLift B S hS s W v :=
  pullback.lift_fst _ _ _

/-- The lifts into the base changes are compatible with morphisms of étale neighbourhoods. -/
theorem sectionsLift_comp_map {W V : S.Etale} (m : W ⟶ V)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    sectionsLift B hS f s p q cond W v ≫ ((smallEtaleBaseChange f).map m).left =
      sectionsLift B hS f s p q cond V ((Scheme.pointSmallEtale s.hom).fiber.map m v) := by
  have e : ((smallEtaleBaseChange f).map m).left =
      pullback.lift (pullback.fst W.hom f ≫ m.left) (pullback.snd W.hom f) (by
        rw [Category.assoc, MorphismProperty.Over.w m, pullback.condition]) := rfl
  rw [e]
  apply pullback.hom_ext
  · calc _ = sectionsLift B hS f s p q cond W v ≫ (pullback.fst W.hom f ≫ m.left) :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_fst _ _ _))
      _ = (q ≫ strictHenselizationNeighborhoodLift B S hS s W v) ≫ m.left :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ m.left) (sectionsLift_fst B hS f s p q cond W v))
      _ = q ≫ strictHenselizationNeighborhoodLift B S hS s V
            ((Scheme.pointSmallEtale s.hom).fiber.map m v) := by
          rw [Category.assoc, strictHenselizationNeighborhoodLift_comp_left]
      _ = _ := (sectionsLift_fst B hS f s p q cond V _).symm
  · calc _ = sectionsLift B hS f s p q cond W v ≫ pullback.snd W.hom f :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_snd _ _ _))
      _ = p := sectionsLift_hom B hS f s p q cond W v
      _ = _ := (sectionsLift_hom B hS f s p q cond V _).symm

/-- The map from sections of `f_*F` over an étale neighbourhood `W` of `s` to `Γ(T, p⁻¹F)`: a
section of `f_*F` over `W`, which is a section of `F` over `X ×_S W`, is restricted along
`T ⟶ X ×_S W`. These are the germ-level maps of
`AlgebraicGeometry.pushforwardStalkToSectionsAb`. -/
abbrev pushforwardSectionsStage (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    ((smallEtalePushforwardAb f).obj F).obj.obj (op W) ⟶
      (smallEtalePullbackAb p ⋙ Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).obj F :=
  (smallEtaleSectionsPullbackAb p ((smallEtaleBaseChange f).obj W)
    (sectionsLift B hS f s p q cond W v) (sectionsLift_hom B hS f s p q cond W v)).app F

/-- The maps `pushforwardSectionsStage` are compatible with the restriction maps of `f_*F` along
morphisms of étale neighbourhoods of `s`. -/
theorem map_comp_pushforwardSectionsStage (F : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    {W V : S.Etale} (m : W ⟶ V) (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    ((smallEtalePushforwardAb f).obj F).obj.map m.op ≫
        pushforwardSectionsStage B hS f s p q cond F W v =
      pushforwardSectionsStage B hS f s p q cond F V
        ((Scheme.pointSmallEtale s.hom).fiber.map m v) := by
  have h := map_comp_smallEtaleSectionsPullbackAb p ((smallEtaleBaseChange f).obj W)
    (sectionsLift B hS f s p q cond W v) ((smallEtaleBaseChange f).map m)
    (sectionsLift_hom B hS f s p q cond W v)
    (by rw [sectionsLift_comp_map, sectionsLift_hom])
  exact (NatTrans.congr_app h F).trans (NatTrans.congr_app (smallEtaleSectionsPullbackAb_congr p
    _ _ _ _ (sectionsLift_comp_map B hS f s p q cond m v)) F)

/-- **The canonical map `(f_*F)_s ⟶ Γ(T, p⁻¹F)`**, for a scheme `T` over `X` and over the strict
henselization at `s`, compatibly over `S`: on the germ at `s` of a section of `f_*F` over an étale
neighbourhood `W`, which is a section of `F` over `X ×_S W`, it is the restriction of that section
along `T ⟶ X ×_S W`. -/
def pushforwardStalkToSectionsAb :
    smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom ⟶
      smallEtalePullbackAb p ⋙ Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1} where
  app F := (Scheme.pointSmallEtale s.hom).presheafFiberDesc
    (pushforwardSectionsStage B hS f s p q cond F)
    (fun _ _ m v => map_comp_pushforwardSectionsStage B hS f s p q cond F m v)
  naturality F G α := by
    apply (Scheme.pointSmallEtale s.hom).presheafFiber_hom_ext
    intro W v
    change (Scheme.pointSmallEtale s.hom).toPresheafFiber W v _ ≫
        ((Scheme.pointSmallEtale s.hom).presheafFiber.map ((smallEtalePushforwardAb f).map α).hom ≫
          (Scheme.pointSmallEtale s.hom).presheafFiberDesc
            (pushforwardSectionsStage B hS f s p q cond G)
            (fun _ _ m v => map_comp_pushforwardSectionsStage B hS f s p q cond G m v)) =
      (Scheme.pointSmallEtale s.hom).toPresheafFiber W v _ ≫
        ((Scheme.pointSmallEtale s.hom).presheafFiberDesc
            (pushforwardSectionsStage B hS f s p q cond F)
            (fun _ _ m v => map_comp_pushforwardSectionsStage B hS f s p q cond F m v) ≫ _)
    rw [(Scheme.pointSmallEtale s.hom).toPresheafFiber_naturality_assoc,
      (Scheme.pointSmallEtale s.hom).toPresheafFiber_presheafFiberDesc
        (pushforwardSectionsStage B hS f s p q cond G)
        (fun _ _ m v => map_comp_pushforwardSectionsStage B hS f s p q cond G m v),
      (Scheme.pointSmallEtale s.hom).toPresheafFiber_presheafFiberDesc_assoc
        (pushforwardSectionsStage B hS f s p q cond F)
        (fun _ _ m v => map_comp_pushforwardSectionsStage B hS f s p q cond F m v)]
    exact (smallEtaleSectionsPullbackAb p ((smallEtaleBaseChange f).obj W)
      (sectionsLift B hS f s p q cond W v) (sectionsLift_hom B hS f s p q cond W v)).naturality α

/-- **The map `(f_*F)_s ⟶ Γ(T, p⁻¹F)` on germs.** -/
@[reassoc]
theorem toPresheafFiber_comp_pushforwardStalkToSectionsAb_app
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : S.Etale)
    (v : (Scheme.pointSmallEtale s.hom).fiber.obj W) :
    (Scheme.pointSmallEtale s.hom).toPresheafFiber W v ((smallEtalePushforwardAb f).obj F).obj ≫
        (pushforwardStalkToSectionsAb B hS f s p q cond).app F =
      pushforwardSectionsStage B hS f s p q cond F W v :=
  (Scheme.pointSmallEtale s.hom).toPresheafFiber_presheafFiberDesc
    (pushforwardSectionsStage B hS f s p q cond F)
    (fun _ _ m v => map_comp_pushforwardSectionsStage B hS f s p q cond F m v) W v

end General

end AlgebraicGeometry

end
