module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.ExtColimitFirstVariableIso

/-!
# The first variable of a system with a colimit presentation by invertible legs

Let `P` be a system of abelian sheaves on the levels of an inverse system of sites with finite
coverings whose transitions are isomorphisms, and let `𝒫` with legs `κ` be a compatible family on
the colimit site whose transposes `u_j⁻¹ P_j ⟶ 𝒫` are isomorphisms. Then, at every index `i`,
`A ↦ P_{A.left}` with the transitions of `P` and the legs `κ` is a first variable
(`Stacks.WeakSites.ExtColimit.systemFirstVariable`). Its value at the identity arrow is `P_i`, so
it has the `Ext` colimit property as soon as the pullback first variable of a sheaf isomorphic to
`P_i` has (`Stacks.WeakSites.ExtColimit.FirstVariable.nonempty_isColimit_of_topIso`).

This is the shape in which the first variable `π⁻¹ℤ` of the cohomology of the levels arises: the
inverse images of one sheaf along the projections of a cocone.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open CategoryTheory.Sites.InverseSystem

universe v u w

namespace Stacks.WeakSites.ExtColimit

open InverseSystemOfFiniteSites Stacks.Homology Stacks.WeakSites.ColimitSiteCohomology

variable {D : InverseSystemOfFiniteSites.{v, u, max u v w}}
  {C : Type (max u v w)} [SmallCategory C]
  {uC : ∀ i, D.C i ⥤ C} {hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j}
  {K : Precoverage C} [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck]

variable (P : AbelianSheafSystem.{v, u, max u v w, max u v w} D)

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck] in
/-- The pushforward transition of `P` along an identity arrow is the canonical isomorphism
identifying the pushforward along the identity with the identity. -/
theorem pushforwardTransition_id' (j : D.I) :
    pushforwardTransition D P (𝟙 j) =
      (abelianSheafPushforwardIdIso.{v, u, max u v w, max u v w} D j).hom.app (P.obj j) := by
  have h : P.map (𝟙 j) =
      (abelianSheafPullbackIdIso.{v, u, max u v w, max u v w} D j).hom.app (P.obj j) := by
    rw [← cancel_epi ((abelianSheafPullbackIdIso.{v, u, max u v w, max u v w} D j).inv.app
      (P.obj j)), P.map_id, Iso.inv_hom_id_app]
    rfl
  show (abelianSheafAdjunction.{v, u, max u v w, max u v w} D (𝟙 j)).homEquiv _ _ (P.map _) = _
  rw [h]
  exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ _

omit [∀ i, (uC i).IsContinuous (D.J i) K.toGrothendieck] in
/-- The pushforward transition of `P` along `a ≫ b` is the transition along `b`, followed by the
pushforward along `b` of the transition along `a`, followed by the canonical isomorphism
identifying the composite pushforward with the pushforward along `a ≫ b`. -/
theorem pushforwardTransition_comp' {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k) :
    pushforwardTransition D P (a ≫ b) = pushforwardTransition D P b ≫
      (abelianSheafPushforward.{v, u, max u v w, max u v w} D b).map
        (pushforwardTransition D P a) ≫
      (abelianSheafPushforwardCompIso.{v, u, max u v w, max u v w} D a b).hom.app (P.obj i) := by
  show (abelianSheafAdjunction.{v, u, max u v w, max u v w} D (a ≫ b)).homEquiv _ _
    (P.map (a ≫ b)) = _
  rw [← P.map_comp a b]
  dsimp only [abelianSheafPullbackCompIso]
  rw [Adjunction.homEquiv_leftAdjointUniq_inv_app_comp, Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.comp_homEquiv]
  show ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D b).homEquiv _ _)
    (((abelianSheafAdjunction.{v, u, max u v w, max u v w} D a).homEquiv _ _)
      ((abelianSheafPullback.{v, u, max u v w, max u v w} D a).map (P.map b) ≫ P.map a)) ≫
    (abelianSheafPushforwardCompIso.{v, u, max u v w, max u v w} D a b).hom.app (P.obj i) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  rfl

variable {P} (hP : ∀ {j k : D.I} (a : j ⟶ k), IsIso (P.map a))
  (Q : Sheaf K.toGrothendieck Ab.{max u v w}) (κ : ∀ j, (P.obj j).obj ⟶ (uC j).op ⋙ Q.obj)
  (hκ : IsCompatible.{v, u, max u v w, max u v w} D uC hu P Q.obj κ)
  (hκiso : ∀ j, IsIso (systemLeg (K := K) κ j))

include hκ in
/-- For a compatible family `κ`, the leg at `j` is the pushforward transition of `P` along
`a : k ⟶ j`, followed by the pushforward along `a` of the leg at `k`, followed by the canonical
isomorphism identifying the composite pushforwards of `Q`. -/
theorem lg_comp_of_isCompatible {k j : D.I} (a : k ⟶ j) :
    (⟨κ j⟩ : P.obj j ⟶ (colimitPushforward.{v, u, w} D uC K j).obj Q) =
      pushforwardTransition D P a ≫
        (abelianSheafPushforward.{v, u, max u v w, max u v w} D a).map ⟨κ k⟩ ≫
        (colimitPushforwardCompIso.{v, u, w} D uC hu K a).hom.app Q := by
  apply Sheaf.hom_ext
  ext V : 2
  have hc := congrArg (fun q => q.app V) (hκ a)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app] at hc
  let := D.continuous a
  rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.comp_hom,
    NatTrans.comp_app, NatTrans.comp_app]
  show (κ j).app V = _
  rw [hc, colimitPushforwardCompIso, sheafPushforwardContinuousComp'_hom_app_app, eqToHom_map]
  rfl

include hP hκ hκiso in
/-- **The first variable of a system with invertible transitions presented by invertible legs.** -/
def systemFirstVariable (i : D.I) : FirstVariable.{v, u, w} D uC hu K i where
  obj A := P.obj A.left
  φ f := pushforwardTransition D P f.left
  φ_id A := pushforwardTransition_id' P A.left
  φ_comp f g := pushforwardTransition_comp' P f.left g.left
  isIso_φ f := by
    change IsIso (((abelianSheafAdjunction.{v, u, max u v w, max u v w} D f.left).homEquiv _ _).symm
      ((abelianSheafAdjunction.{v, u, max u v w, max u v w} D f.left).homEquiv _ _ (P.map f.left)))
    rw [Equiv.symm_apply_apply]
    exact hP f.left
  top := Q
  lg A := ⟨κ A.left⟩
  lg_comp f := lg_comp_of_isCompatible Q κ hκ f.left
  isIso_lg A := hκiso A.left

end Stacks.WeakSites.ExtColimit

end
