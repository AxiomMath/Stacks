module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.InverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# Commutative squares of schemes as 2-commutative squares of étale ringed topoi

For a morphism of schemes `a : X ⟶ Y` and a commutative ring `Λ`,
`Stacks.EtaleCohomology.etaleRingedToposHom Λ a` is the morphism of ringed topoi
`(X_étale, Λ̲) ⟶ (Y_étale, Λ̲)` on the small models of the small étale sites. This file proves
that these morphisms compose up to a 2-isomorphism: for `a : X ⟶ Y` and `b : Y ⟶ Z` the
composite of the morphisms of ringed topoi of `a` and `b` is 2-isomorphic to the morphism of
ringed topoi of `a ≫ b` (this is the étale case of [Stacks, Tag 03G8] read on ringed topoi).
Consequently a commutative square of schemes gives a 2-commutative square of ringed topoi, which
is the input of the compatibility [Stacks, Tag 0E48] of the projection formula map with base
change,
`Stacks.Cohomology.ProjectionFormulaOfToposHom.projectionFormulaMap_baseChange_square_of_twoIso`.

## Main definitions

* `Stacks.EtaleCohomology.etaleRingedToposHomComp`: the composite of the morphisms of ringed
  topoi of `a` and `b`.
* `Stacks.EtaleCohomology.etaleRingedToposHomCompTwoIso`: the 2-isomorphism between it and the
  morphism of ringed topoi of `a ≫ b`.
* `Stacks.EtaleCohomology.etaleRingedToposHomSquareTwoIso`: the 2-isomorphism attached to a
  commutative square of schemes.

## Main results

* `Stacks.EtaleCohomology.etaleRingedSiteFSharp_comp`: the structure maps `Λ̲ ⟶ a_*Λ̲` compose,
  through the composition isomorphism of base change functors, to the structure map of `a ≫ b`.

## Implementation notes

The underlying isomorphism of direct images is the action on direct images of the composition
isomorphism `(a ≫ b)^* ≅ b^* ⋙ a^*` of base change functors on the small models,
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp`; the direct image along a composite of
continuous functors is the composite of the direct images by definition. The compatibility
with the structure maps is checked on the constant sections, which generate the constant sheaf
of rings under sheafification: every structure map sends a constant to the same constant.

The composites are written with their three ringed topoi named, since otherwise the universe
levels of the middle ringed topos are not determined when the instance arguments of
`AlgebraicGeometry.RingedToposHom.comp` are synthesized.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ]

/-- The composite of the morphisms of étale ringed topoi of `a : X ⟶ Y` and `b : Y ⟶ Z`, as a
morphism of ringed topoi `(X_étale, Λ̲) ⟶ (Z_étale, Λ̲)`. -/
abbrev etaleRingedToposHomComp {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) :=
  RingedToposHom.comp (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
      (etaleRingedSite.{u, r} Λ X)))
    (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
      (etaleRingedSite.{u, r} Λ Y)))
    (Z := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
      (etaleRingedSite.{u, r} Λ Z)))
    (etaleRingedToposHom.{u, r} Λ b) (etaleRingedToposHom.{u, r} Λ a)

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **Base change along a composite, on the small models**: `b^* ⋙ a^* ≅ (a ≫ b)^*`, the
inverse of `Stacks.EtaleCohomology.smallEtaleBaseChangeComp` read on the small models. -/
def etaleSmallModelBaseChangeCompIso :
    etaleSmallModelBaseChange.{u, r} b ⋙ etaleSmallModelBaseChange.{u, r} a ≅
      etaleSmallModelBaseChange.{u, r} (a ≫ b) :=
  Functor.isoWhiskerLeft AsSmall.down
    (Functor.isoWhiskerRight (smallEtaleBaseChangeComp a b).symm AsSmall.up)

/-- **The structure maps compose.** The structure map `Λ̲ ⟶ b_*Λ̲`, followed by `b_*` of the
structure map `Λ̲ ⟶ a_*Λ̲` and by the identification of `b_* a_*` with `(a ≫ b)_*`, is the
structure map of `a ≫ b`. -/
theorem etaleRingedSiteFSharp_comp :
    letI := Functor.isContinuous_comp (etaleSmallModelBaseChange.{u, r} b)
      (etaleSmallModelBaseChange.{u, r} a)
      (etaleSmallModelTopology.{u, r} Z) (etaleSmallModelTopology.{u, r} Y)
      (etaleSmallModelTopology.{u, r} X)
    etaleRingedSiteFSharp.{u, r} Λ b ≫
      ((etaleSmallModelBaseChange.{u, r} b).sheafPushforwardContinuous CommRingCat _ _).map
        (etaleRingedSiteFSharp.{u, r} Λ a) ≫
      (Functor.sheafPushforwardContinuousComp (etaleSmallModelBaseChange.{u, r} b)
        (etaleSmallModelBaseChange.{u, r} a) CommRingCat (etaleSmallModelTopology.{u, r} Z)
        (etaleSmallModelTopology.{u, r} Y) (etaleSmallModelTopology.{u, r} X)).hom.app
          (etaleRingedSite.{u, r} Λ X).O ≫
      (Functor.sheafPushforwardContinuousIso (etaleSmallModelBaseChangeCompIso.{u, r} a b)
        CommRingCat (etaleSmallModelTopology.{u, r} Z) (etaleSmallModelTopology.{u, r} X)).hom.app
          (etaleRingedSite.{u, r} Λ X).O =
      etaleRingedSiteFSharp.{u, r} Λ (a ≫ b) := by
  apply Sheaf.hom_ext
  refine sheafify_hom_ext (J := etaleSmallModelTopology.{u, r} Z)
    (P := (Functor.const (AsSmall.{max (u + 1) r} Z.Etale)ᵒᵖ).obj
      (CommRingCat.of (ULift.{max (u + 1) r} Λ))) _ _ (ObjectProperty.FullSubcategory.property _) ?_
  ext V x
  let := Functor.isContinuous_comp (etaleSmallModelBaseChange.{u, r} b)
    (etaleSmallModelBaseChange.{u, r} a)
    (etaleSmallModelTopology.{u, r} Z) (etaleSmallModelTopology.{u, r} Y)
    (etaleSmallModelTopology.{u, r} X)
  have key {S T : Scheme.{u}} (c : S ⟶ T) (W) :=
    congrArg (fun φ => (φ.app W).hom x) (etaleRingedSiteFSharp_toSheafify.{u, r} Λ c)
  have hb := key b V
  have hab := key (a ≫ b) V
  have ha := key a (Opposite.op ((etaleSmallModelBaseChange.{u, r} b).obj V.unop))
  let D := (((Functor.sheafPushforwardContinuousIso (etaleSmallModelBaseChangeCompIso.{u, r} a b)
    CommRingCat (etaleSmallModelTopology.{u, r} Z) (etaleSmallModelTopology.{u, r} X)).hom.app
      (etaleRingedSite.{u, r} Λ X).O).hom.app V).hom
  let B := ((etaleRingedSiteFSharp.{u, r} Λ a).hom.app
    (Opposite.op ((etaleSmallModelBaseChange.{u, r} b).obj V.unop))).hom
  let A := ((etaleRingedSiteFSharp.{u, r} Λ b).hom.app V).hom
  let T := ((toSheafify (etaleSmallModelTopology.{u, r} Z)
    ((Functor.const (AsSmall.{max (u + 1) r} Z.Etale)ᵒᵖ).obj
      (CommRingCat.of (ULift.{max (u + 1) r} Λ)))).app V).hom
  refine Eq.trans (?_ : _ = D (B (A (T x)))) ?_
  · rfl
  refine (congrArg (fun y => D (B y)) hb).trans ?_
  refine (congrArg (fun y => D y) ha).trans ?_
  refine Eq.trans ?_ hab.symm
  exact (congrArg (fun h => CommRingCat.Hom.hom h x)
    ((toSheafify (etaleSmallModelTopology.{u, r} X)
      ((Functor.const (AsSmall.{max (u + 1) r} X.Etale)ᵒᵖ).obj
        (CommRingCat.of (ULift.{max (u + 1) r} Λ)))).naturality
      ((etaleSmallModelBaseChangeCompIso.{u, r} a b).inv.app V.unop).op)).symm

/-- **The morphisms of étale ringed topoi compose** up to a 2-isomorphism: the composite of the
morphisms of ringed topoi of `a : X ⟶ Y` and `b : Y ⟶ Z` is 2-isomorphic to the morphism of
ringed topoi of `a ≫ b`. -/
def etaleRingedToposHomCompTwoIso :
    RingedToposHom.TwoIso
      (A := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
      (etaleRingedSite.{u, r} Λ X)))
      (B := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
      (etaleRingedSite.{u, r} Λ Z))) (etaleRingedToposHomComp Λ a b)
      (etaleRingedToposHom.{u, r} Λ (a ≫ b)) where
  e := by
    letI := Functor.isContinuous_comp (etaleSmallModelBaseChange.{u, r} b)
      (etaleSmallModelBaseChange.{u, r} a)
      (etaleSmallModelTopology.{u, r} Z) (etaleSmallModelTopology.{u, r} Y)
      (etaleSmallModelTopology.{u, r} X)
    exact Functor.sheafPushforwardContinuousIso (etaleSmallModelBaseChangeCompIso.{u, r} a b) _ _ _
  commutes := by
    have h := RingedToposHom.comp_fSharp_forget (etaleRingedToposHom.{u, r} Λ b)
      (etaleRingedToposHom.{u, r} Λ a)
    refine (congrArg (· ≫ _) h).trans ?_
    have hb := RingedSite.Hom.forgetFSharp_ringedToposHom (etaleRingedSiteHom.{u, r} Λ b)
    have ha := RingedSite.Hom.forgetFSharp_ringedToposHom (etaleRingedSiteHom.{u, r} Λ a)
    have hab := RingedSite.Hom.forgetFSharp_ringedToposHom (etaleRingedSiteHom.{u, r} Λ (a ≫ b))
    unfold RingedToposHom.forgetFSharp at hb ha hab ⊢
    rw [hb, ha, hab]
    exact congrArg (sheafCompose (etaleRingedSite.{u, r} Λ Z).J (forget CommRingCat)).map
      (etaleRingedSiteFSharp_comp.{u, r} Λ a b)

/-- The 2-isomorphism between the morphisms of étale ringed topoi of two equal morphisms of
schemes: the action on direct images of the identification of the two base change functors. -/
def etaleRingedToposHomEqTwoIso {a a' : X ⟶ Y} (h : a = a') :
    RingedToposHom.TwoIso
      (A := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
      (etaleRingedSite.{u, r} Λ X)))
      (B := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
      (etaleRingedSite.{u, r} Λ Y))) (etaleRingedToposHom.{u, r} Λ a)
      (etaleRingedToposHom.{u, r} Λ a') where
  e := Functor.sheafPushforwardContinuousIso
    (eqToIso (congrArg (fun m => etaleSmallModelBaseChange.{u, r} m) h)) (Type (max (u + 1) r))
      (etaleSmallModelTopology.{u, r} Y) (etaleSmallModelTopology.{u, r} X)
  commutes := by
    subst h
    apply Sheaf.hom_ext
    ext V x
    simp [Functor.sheafPushforwardContinuousNatTrans]
    rfl

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- **A commutative square of schemes is a 2-commutative square of étale ringed topoi**: for
`g' ≫ f = f' ≫ g` the composites `g ∘ f'` and `f ∘ g'` of morphisms of ringed topoi are
2-isomorphic, through the morphism of ringed topoi of the common composite. -/
def etaleRingedToposHomSquareTwoIso :
    RingedToposHom.TwoIso
      (A := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
      (etaleRingedSite.{u, r} Λ X')))
      (B := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
      (etaleRingedSite.{u, r} Λ Y))) (etaleRingedToposHomComp Λ f' g)
      (etaleRingedToposHomComp Λ g' f) :=
  (etaleRingedToposHomCompTwoIso Λ f' g).trans ((etaleRingedToposHomEqTwoIso Λ w.symm).trans
    (etaleRingedToposHomCompTwoIso Λ g' f).symm)

end Stacks.EtaleCohomology
