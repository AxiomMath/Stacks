module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.PushforwardCoherence
public import StacksFrontier.CategoryTheory.Sites.Topos.PushPullTransition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The restriction and direct-image compositors of a composable pair of site functors are mates

Let `u : C₂ ⥤ C₁` and `v : C₁ ⥤ C₀` be continuous and cocontinuous for topologies `J₂`, `J₁`,
`J₀`, and let `w : C₂ ⥤ C₀` be likewise, together with an equality `h : u ⋙ v = w`. There are
then two canonical comparisons attached to the pair, one on each side of the adjunction
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`:

* on the restriction side, `v^{-1} ⋙ u^{-1} ≅ w^{-1}` is Mathlib's
  `CategoryTheory.Functor.sheafPushforwardContinuousComp'` applied to `eqToIso h`;
* on the direct-image side, `u_* ⋙ v_* ≅ w_*` is `sheafPushforwardCocontinuousCompIso`
  (Stacks 03L5) followed by the transport
  `CategoryTheory.SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq` along `h`.

This file proves that the two are *mates* of each other: the companion comparison of right
adjoints that the restriction-side compositor determines by uniqueness of right adjoints is the
inverse of the direct-image compositor.

## Main results

* `CategoryTheory.restrictionRightAdjointIso_sheafPushforwardContinuousComp'`: the mate
  identity in the form that uniqueness of right adjoints produces, i.e. an identity of
  `Stacks.CategoryTheory.restrictionRightAdjointIso`. This is the form a push-pull transition
  for the pair `(u, v)` is written with.
* `CategoryTheory.leftAdjointCompIso_sheafPushforwardCocontinuousCompIso`: the same identity
  read in the other direction, as a computation of Mathlib's
  `CategoryTheory.Adjunction.leftAdjointCompIso` of the direct-image compositor.
* `Stacks.CategoryTheory.restrictionRightAdjointIso_eq_symm_of_counit`: the abstract counit
  criterion that identifies `restrictionRightAdjointIso` with a given isomorphism of right
  adjoints, and `Stacks.CategoryTheory.leftAdjointCompIso_eq_of_restrictionRightAdjointIso`,
  which passes between the two forms.

## Implementation notes

The criterion `restrictionRightAdjointIso_eq_symm_of_counit` is what makes the identity
checkable: `restrictionRightAdjointIso` is a `CategoryTheory.Adjunction.rightAdjointUniq`, so a
candidate equals it as soon as the two have the same adjunct, and the adjunct of a candidate is
computed by the counits alone. Taking the criterion with the transported adjunction
`CategoryTheory.Adjunction.ofNatIsoLeft` written out keeps every left adjoint in sight
*syntactically* equal to `w^{-1}`, which matters: `v^{-1} ⋙ u^{-1}` and `(u ⋙ v)^{-1}` are only
definitionally equal — that is exactly the content of Mathlib's
`CategoryTheory.Functor.sheafPushforwardContinuousComp`, which is `Iso.refl` — so a rewrite
against a lemma stated for one of them does not fire at the other.

The verification itself starts with `subst h`. Both compositors then become identities: the
transport along `h` is `Iso.refl` by
`CategoryTheory.SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl`, and the
restriction-side compositor at `eqToIso rfl` is the identity by
`CategoryTheory.Functor.sheafPushforwardContinuousComp'_eqToIso_rfl_inv_app`. What is left is an
identity of morphisms of sheaves, which `CategoryTheory.Sheaf.hom_ext` and the bridges of
`StacksFrontier/CategoryTheory/Sites/Simplicial/PushforwardCoherence.lean` turn into the
corresponding identity for the right Kan extensions. There it is literally the counit
characterisation of `ranOpCompIso`, because the left adjoints of the two right Kan extension
adjunctions — precomposition with `u.op ⋙ v.op` versus precomposition with `v.op` and then with
`u.op` — are the same functor.

## References

* [Stacks Project, Tag 03L5](https://stacks.math.columbia.edu/tag/03L5)
* [Stacks Project, Tag 00XR](https://stacks.math.columbia.edu/tag/00XR)
-/

@[expose] public noncomputable section

open CategoryTheory Functor

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace Stacks.CategoryTheory

variable {A : Type u₁} {B : Type u₂} {D : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} D]
  {P : A ⥤ B} {Q : B ⥤ A} {P' : A ⥤ D} {Q' : D ⥤ A} {R : B ⥤ D} {S : D ⥤ B}

/-- **A counit criterion for the companion comparison of right adjoints.** For a triangle of
adjunctions `adj : P ⊣ Q`, `adj' : P' ⊣ Q'`, `radj : R ⊣ S` with comparison `eL : P ⋙ R ≅ P'` of
left adjoints, an isomorphism `e : S ⋙ Q ≅ Q'` of right adjoints is the inverse of
`Stacks.CategoryTheory.restrictionRightAdjointIso` as soon as `e.inv`, read through `P'` and
followed by the two counits, is the counit of `adj'`. -/
theorem restrictionRightAdjointIso_eq_symm_of_counit (adj : P ⊣ Q) (adj' : P' ⊣ Q')
    (radj : R ⊣ S) (eL : P ⋙ R ≅ P') (e : S ⋙ Q ≅ Q')
    (h : ∀ X : D, P'.map (e.inv.app X) ≫ eL.inv.app (Q.obj (S.obj X)) ≫
      R.map (adj.counit.app (S.obj X)) ≫ radj.counit.app X = adj'.counit.app X) :
    restrictionRightAdjointIso adj adj' radj eL = e.symm := by
  refine Iso.ext (NatTrans.ext (funext fun X => ?_))
  refine (((adj.comp radj).ofNatIsoLeft eL).homEquiv _ _).symm.injective ?_
  rw [restrictionRightAdjointIso, Adjunction.homEquiv_symm_rightAdjointUniq_hom_app,
    Adjunction.homEquiv_counit]
  simp only [Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit_app, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  exact (h X).symm

/-- **Passing from the comparison of right adjoints back to the comparison of left adjoints.**
If the companion comparison of right adjoints of a triangle with compositor `eL` is `e.symm`,
then `eL` is the comparison of left adjoints that Mathlib's
`CategoryTheory.Adjunction.leftAdjointCompIso` builds from `e`. Both statements say that the
conjugate of `eL.inv` is `e.hom`, so each follows from the other by injectivity of
`CategoryTheory.conjugateEquiv`. -/
theorem leftAdjointCompIso_eq_of_restrictionRightAdjointIso (adj : P ⊣ Q) (adj' : P' ⊣ Q')
    (radj : R ⊣ S) (eL : P ⋙ R ≅ P') (e : S ⋙ Q ≅ Q')
    (h : restrictionRightAdjointIso adj adj' radj eL = e.symm) :
    Adjunction.leftAdjointCompIso adj radj adj' e = eL := by
  have h₁ : conjugateEquiv (adj.comp radj) adj' eL.inv = e.hom := by
    have h₂ : (restrictionRightAdjointIso adj adj' radj eL).inv = e.hom := by
      rw [h, Iso.symm_inv]
    rw [restrictionRightAdjointIso, show (Adjunction.rightAdjointUniq adj'
        ((adj.comp radj).ofNatIsoLeft eL)).inv =
      conjugateEquiv ((adj.comp radj).ofNatIsoLeft eL) adj' (𝟙 P') from rfl,
      conjugateEquiv_ofNatIsoLeft_left, Category.id_comp] at h₂
    exact h₂
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp ?_)
  exact (conjugateEquiv (adj.comp radj) adj').injective
    (by rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv, h₁])

end Stacks.CategoryTheory

namespace CategoryTheory

section

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]

/-- Restriction along a continuous site functor acts on underlying presheaves by precomposition
with the opposite functor. -/
theorem Functor.sheafPushforwardContinuous_map_hom (F : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) [F.IsContinuous J K] {X Y : Sheaf K (Type u)} (f : X ⟶ Y) :
    ((F.sheafPushforwardContinuous (Type u) J K).map f).hom =
      Functor.whiskerLeft F.op f.hom := rfl

end

section

variable {C₂ : Type u} [SmallCategory C₂] {C₁ : Type u} [SmallCategory C₁]
  {C₀ : Type u} [SmallCategory C₀]
  (J₂ : GrothendieckTopology C₂) (J₁ : GrothendieckTopology C₁)
  (J₀ : GrothendieckTopology C₀) (u : C₂ ⥤ C₁) (v : C₁ ⥤ C₀) {w : C₂ ⥤ C₀}
  [u.IsContinuous J₂ J₁] [u.IsCocontinuous J₂ J₁]
  [v.IsContinuous J₁ J₀] [v.IsCocontinuous J₁ J₀]
  [w.IsContinuous J₂ J₀] [w.IsCocontinuous J₂ J₀]
  [(u ⋙ v).IsCocontinuous J₂ J₀]

omit [u.IsCocontinuous J₂ J₁] [v.IsCocontinuous J₁ J₀] [(u ⋙ v).IsCocontinuous J₂ J₀] in
/-- The comparison of restrictions attached to a reflexivity proof is the identity: its inverse
is the identity morphism of the restriction along `u ⋙ v`. -/
theorem Functor.sheafPushforwardContinuousComp'_eqToIso_rfl_inv_app
    [(u ⋙ v).IsContinuous J₂ J₀] (M : Sheaf J₀ (Type u)) :
    (Functor.sheafPushforwardContinuousComp' (eqToIso (rfl : u ⋙ v = u ⋙ v))
        (Type u) J₂ J₁ J₀).inv.app M = 𝟙 _ := by
  ext U x
  simp only [eqToIso_refl, Functor.comp_obj, Functor.sheafPushforwardContinuousComp', Iso.trans,
    Functor.sheafPushforwardContinuousComp, Iso.refl_hom, Functor.sheafPushforwardContinuousIso,
    Functor.sheafPushforwardContinuousNatTrans, Iso.refl_inv, NatTrans.op_id,
    ObjectProperty.ι_obj, Functor.whiskerRight_id', ObjectProperty.FullSubcategory.id_hom,
    NatTrans.id_app]
  rfl

omit [(u ⋙ v).IsCocontinuous J₂ J₀] in
/-- **The two compositors of a composable pair of continuous-and-cocontinuous site functors are
mates.** The comparison of right adjoints that the restriction-side compositor
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` determines, by uniqueness of right
adjoints, is the inverse of the direct-image compositor `sheafPushforwardCocontinuousCompIso`
followed by the transport along `h : u ⋙ v = w`. -/
@[sga "4 VI 7.1.3" "c'_{g, special case"]
theorem restrictionRightAdjointIso_sheafPushforwardContinuousComp' (h : u ⋙ v = w) :
    Stacks.CategoryTheory.restrictionRightAdjointIso
        (v.sheafAdjunctionCocontinuous (Type u) J₁ J₀)
        (w.sheafAdjunctionCocontinuous (Type u) J₂ J₀)
        (u.sheafAdjunctionCocontinuous (Type u) J₂ J₁)
        (Functor.sheafPushforwardContinuousComp' (eqToIso h) (Type u) J₂ J₁ J₀) =
      ((sheafPushforwardCocontinuousCompIso J₂ J₁ J₀ u v).symm ≪≫
        SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq J₂ J₀ h).symm := by
  subst h
  refine Stacks.CategoryTheory.restrictionRightAdjointIso_eq_symm_of_counit
    _ _ _ _ _ (fun X => ?_)
  apply Sheaf.hom_ext
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.refl_inv,
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl, Category.id_comp,
    Functor.sheafPushforwardContinuousComp'_eqToIso_rfl_inv_app,
    ObjectProperty.FullSubcategory.comp_hom,
    Functor.sheafAdjunctionCocontinuous_counit_app_hom,
    Functor.sheafPushforwardContinuous_map_hom,
    sheafPushforwardCocontinuousCompIso_hom_app_hom]
  have hp := Adjunction.rightAdjointUniq_hom_app_counit
      ((u.op ⋙ v.op).ranAdjunction (Type u))
      ((v.op.ranAdjunction (Type u)).comp (u.op.ranAdjunction (Type u))) X.obj
  rw [← ranOpCompIso_def, Adjunction.comp_counit_app] at hp
  exact hp

/-- **The mate identity read in the other direction.** The comparison of restrictions that
Mathlib's `CategoryTheory.Adjunction.leftAdjointCompIso` builds from the direct-image compositor
of `u` and `v`, transported along `h : u ⋙ v = w`, is
`CategoryTheory.Functor.sheafPushforwardContinuousComp'` at `eqToIso h`. -/
theorem leftAdjointCompIso_sheafPushforwardCocontinuousCompIso (h : u ⋙ v = w) :
    Adjunction.leftAdjointCompIso (v.sheafAdjunctionCocontinuous (Type u) J₁ J₀)
        (u.sheafAdjunctionCocontinuous (Type u) J₂ J₁)
        (w.sheafAdjunctionCocontinuous (Type u) J₂ J₀)
        ((sheafPushforwardCocontinuousCompIso J₂ J₁ J₀ u v).symm ≪≫
          SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq J₂ J₀ h) =
      Functor.sheafPushforwardContinuousComp' (eqToIso h) (Type u) J₂ J₁ J₀ :=
  Stacks.CategoryTheory.leftAdjointCompIso_eq_of_restrictionRightAdjointIso _ _ _ _ _
    (restrictionRightAdjointIso_sheafPushforwardContinuousComp' J₂ J₁ J₀ u v h)

end

end CategoryTheory

end
