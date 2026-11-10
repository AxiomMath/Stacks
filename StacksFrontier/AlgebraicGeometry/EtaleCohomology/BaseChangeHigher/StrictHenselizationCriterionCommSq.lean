module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StrictHenselizationCriterion
public import
StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StrictHenselizationSquareSiteChange

/-!
# The stalk of the base change map of a commutative square, on strict henselizations

Consider a commutative, not necessarily cartesian, square of schemes
```
X  ←-h-  Y
|f       |e
S  ←-g-  T
```
with `g` and `h` quasi-compact and quasi-separated, and a geometric point `x` of `X`. By
Stacks 03Q9 (`AlgebraicGeometry.higherDirectImageStalkComparison`) the stalk at `f(x)` of
`R^q g_* F` is `H^q(T ×_S Spec(𝒪^{sh}_{S,f(x)}), F)` and the stalk at `x` of `R^q h_* e⁻¹F` is
`H^q(Y ×_X Spec(𝒪^{sh}_{X,x}), e⁻¹F)`. A morphism of strict henselizations
`m : Spec(𝒪^{sh}_{X,x}) ⟶ Spec(𝒪^{sh}_{S,f(x)})` lying over `f` and carrying the canonical
geometric point to the canonical geometric point gives the morphism
`κ : Y ×_X Spec(𝒪^{sh}_{X,x}) ⟶ T ×_S Spec(𝒪^{sh}_{S,f(x)})`, which is `e` on the first factor
and `m` on the second. This file shows that, under the two identifications of Stacks 03Q9, the
stalk at `x` of the base change map `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is the restriction along `κ`.

For a cartesian square this is `AlgebraicGeometry.higherBaseChangeStalkHom_comp_comparison`, where
`κ` factors through the isomorphism `Y ×_X Spec(𝒪^{sh}_{X,x}) ≅ T ×_S Spec(𝒪^{sh}_{X,x})`. Here
no such factorization is available, and the restriction is taken along `κ` directly.

The strict henselizations at `x` and at `f(x)` may be taken in two different big étale sites
`B₁` and `B₂`: the morphism `m` is an argument, subject only to its two compatibilities. When one
site contains both `X` and `S`, `AlgebraicGeometry.strictHenselizationSquareMap` is such a
morphism (`AlgebraicGeometry.higherBaseChangeStalkHom_comp_squareRestriction_squareMap`); in
general `AlgebraicGeometry.strictHenselizationSquareMapVia` is one, formed through any site
containing both schemes (`AlgebraicGeometry.BigEtaleSite.exists_contains_of_small` provides one).

## Main definitions

* `AlgebraicGeometry.strictHenselizationBaseChangeSquareMap` is the morphism `κ`.
* `AlgebraicGeometry.strictHenselizationBaseChangeSquarePullbackHom` is the comparison
  `κ⁻¹ p_S⁻¹ ⟶ p_X⁻¹ e⁻¹` of inverse images along which the restriction is read.

## Main results

* `AlgebraicGeometry.higherBaseChangeStalkHom_comp_squareRestriction` says that the stalk of the
  base change map is the restriction along `κ`, as morphisms of δ-functors in `F`.
* `AlgebraicGeometry.higherBaseChangeStalkHom_comp_squareRestriction_app` is its reading in one
  degree, and `AlgebraicGeometry.higherBaseChangeStalkHom_comp_higherDirectImageStalkIso_hom` the
  same through the isomorphisms `AlgebraicGeometry.higherDirectImageStalkIso` of Stacks 03Q9.
* `AlgebraicGeometry.higherBaseChangeStalkHom_comp_squareRestriction_squareMap` is the special
  case for one big étale site and the canonical morphism of strict henselizations, and
  `AlgebraicGeometry.higherBaseChangeStalkHom_comp_squareRestriction_squareMapVia` the case of
  two sites, through the morphism `AlgebraicGeometry.strictHenselizationSquareMapVia`.

## Implementation notes

As for a cartesian square, the identity is an equality of morphisms of δ-functors out of the
stalks of the higher direct images along `g`, which form a universal δ-functor, so it is checked
in degree zero, on germs of sections. The degree-zero computation uses only the commutativity of
the square.

## References

* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0EZU](https://stacks.math.columbia.edu/tag/0EZU)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B₁ B₂ : BigEtaleSite.{u}) {X Y S T : Scheme.{u}} (hX : B₁.Contains X)
  (hS : B₂.Contains S) {f : X ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T} {g : T ⟶ S}

section Lift

variable (f) (x : GeometricPoint X)
  (m : strictHenselization B₁ X hX x ⟶ strictHenselization B₂ S hS (x.map f))
  (hm : m ≫ strictHenselizationToBase B₂ S hS (x.map f) = strictHenselizationToBase B₁ X hX x ≫ f)
  (hmpt : geometricPointToStrictHenselization B₁ X hX x ≫ m =
    geometricPointToStrictHenselization B₂ S hS (x.map f))

include hm hmpt in
/-- **The morphism from the strict henselization into a base changed étale neighbourhood**, for a
morphism `m` of strict henselizations, possibly taken in two different big étale sites, which lies
over `f` and carries the canonical geometric point to the canonical geometric point. The unique
morphism from `Spec 𝒪^{sh}_{X,x}` into the étale neighbourhood `X ×_S V` of `x`, followed by the
projection to `V`, is `m` followed by the unique morphism from `Spec 𝒪^{sh}_{S,f(x)}` into `V`. -/
theorem strictHenselizationNeighborhoodLift_smallEtaleBaseChange_of_square (V : S.Etale)
    (v : (Scheme.pointSmallEtale (x.map f).hom).fiber.obj V) :
    strictHenselizationNeighborhoodLift B₁ X hX x
          ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
          ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v) ≫
        pullback.fst V.hom f =
      m ≫ strictHenselizationNeighborhoodLift B₂ S hS (x.map f) V v := by
  have hlift := strictHenselizationNeighborhoodLift_comp B₂ S hS (x.map f) V v
  have hpt := geometricPointToStrictHenselization_comp_neighborhoodLift B₂ S hS (x.map f) V v
  generalize strictHenselizationNeighborhoodLift B₂ S hS (x.map f) V v = ℓ at *
  have hcond : (m ≫ ℓ) ≫ V.hom = strictHenselizationToBase B₁ X hX x ≫ f := by
    rw [Category.assoc, hlift, hm]
  have key := strictHenselizationNeighborhoodLift_eq B₁ X hX x
    ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
    ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v)
    (pullback.lift (m ≫ ℓ) (strictHenselizationToBase B₁ X hX x) hcond)
    (pullback.lift_snd _ _ _) (by
      refine pullback.hom_ext ?_ ?_
      · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_fst _ _ hcond)).trans
          ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ℓ) hmpt).trans (hpt.trans
            (pointSmallEtaleComapFiberIso_hom_app_left_fst f x.hom V v).symm))))
      · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pullback.lift_snd _ _ hcond)).trans
          ((geometricPointToStrictHenselization_comp B₁ X hX x).trans
            (Over.w ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v)).symm)))
  exact (congrArg (· ≫ pullback.fst V.hom f) key.symm).trans (pullback.lift_fst _ _ hcond)

end Lift

section Geometry

variable (w : h ≫ f = e ≫ g) (x : GeometricPoint X)
  (m : strictHenselization B₁ X hX x ⟶ strictHenselization B₂ S hS (x.map f))
  (hm : m ≫ strictHenselizationToBase B₂ S hS (x.map f) = strictHenselizationToBase B₁ X hX x ≫ f)

include w hm in
/-- The two composites `Y ×_X Spec(𝒪^{sh}_{X,x}) ⟶ S` through `e` and through `m` agree. -/
theorem strictHenselizationBaseChangeSquareMap_condition :
    (pullback.fst h (strictHenselizationToBase B₁ X hX x) ≫ e) ≫ g =
      (pullback.snd h (strictHenselizationToBase B₁ X hX x) ≫ m) ≫
        strictHenselizationToBase B₂ S hS (x.map f) := by
  rw [Category.assoc, Category.assoc, ← w, pullback.condition_assoc, hm]

/-- **The morphism of strict henselization base changes attached to a commutative square**:
`κ : Y ×_X Spec(𝒪^{sh}_{X,x}) ⟶ T ×_S Spec(𝒪^{sh}_{S,f(x)})`, which is `e` on the first factor
and the morphism `m` of strict henselizations on the second. -/
def strictHenselizationBaseChangeSquareMap :
    strictHenselizationBaseChange B₁ hX h x ⟶ strictHenselizationBaseChange B₂ hS g (x.map f) :=
  pullback.lift (pullback.fst _ _ ≫ e) (pullback.snd _ _ ≫ m)
    (strictHenselizationBaseChangeSquareMap_condition B₁ B₂ hX hS w x m hm)

/-- The morphism `κ` lies over `e`. -/
theorem strictHenselizationBaseChangeSquareMap_fst :
    strictHenselizationBaseChangeToSource B₁ hX h x ≫ e =
      strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm ≫
        strictHenselizationBaseChangeToSource B₂ hS g (x.map f) :=
  (pullback.lift_fst _ _ _).symm

/-- The morphism `κ` lies over the morphism `m` of strict henselizations. -/
theorem strictHenselizationBaseChangeSquareMap_snd :
    strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm ≫
        strictHenselizationBaseChangeToStrictHenselization B₂ hS g (x.map f) =
      strictHenselizationBaseChangeToStrictHenselization B₁ hX h x ≫ m :=
  pullback.lift_snd _ _ _

/-- The comparison `κ⁻¹ p_S⁻¹ ⟶ p_X⁻¹ e⁻¹` of inverse images, for the projections `p_S` and `p_X`
of the strict henselization base changes to `T` and to `Y`: both are inverse image along
`p_X ≫ e = κ ≫ p_S`. -/
abbrev strictHenselizationBaseChangeSquarePullbackHom :
    smallEtalePullbackAb (strictHenselizationBaseChangeToSource B₂ hS g (x.map f)) ⋙
        smallEtalePullbackAb (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm) ⟶
      smallEtalePullbackAb e ⋙
        smallEtalePullbackAb (strictHenselizationBaseChangeToSource B₁ hX h x) :=
  (smallEtalePullbackAbComp' _ _ _
      (strictHenselizationBaseChangeSquareMap_fst B₁ B₂ hX hS w x m hm)).hom ≫
    (smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B₁ hX h x) e _ rfl).inv

end Geometry

section Lifts

variable {C : Type*} [Category* C]

/-- The first components of two morphisms into a fibre product built from the canonical
morphisms of strict henselization base changes of a commutative square agree. -/
theorem fst_eq_of_strictHenselization_squareLifts
    {YX A Q M Vl W Xsh Ssh TS : C} {L : YX ⟶ A} {ql : A ⟶ Q} {fst₁ : Q ⟶ M} {fst₂ : M ⟶ Vl}
    {fsth : A ⟶ W} {fstf : W ⟶ Vl} {qX : YX ⟶ Xsh} {nlX : Xsh ⟶ W} {σ : Xsh ⟶ Ssh}
    {nlS : Ssh ⟶ Vl} {ℓ : TS ⟶ M} {qS : TS ⟶ Ssh} {κ : YX ⟶ TS}
    (h1 : ql ≫ fst₁ ≫ fst₂ = fsth ≫ fstf) (h3 : L ≫ fsth = qX ≫ nlX)
    (h5 : nlX ≫ fstf = σ ≫ nlS) (h6 : ℓ ≫ fst₂ = qS ≫ nlS) (h10 : κ ≫ qS = qX ≫ σ) :
    ((L ≫ ql) ≫ fst₁) ≫ fst₂ = (κ ≫ ℓ) ≫ fst₂ := by
  simp only [Category.assoc, h1, reassoc_of% h3, h5, h6, reassoc_of% h10]

/-- The second components of two morphisms into a fibre product built from the canonical
morphisms of strict henselization base changes of a commutative square agree. -/
theorem snd_eq_of_strictHenselization_squareLifts
    {YX A Q M T Y TS : C} {L : YX ⟶ A} {ql : A ⟶ Q} {fst₁ : Q ⟶ M} {snd₂ : M ⟶ T}
    {snd₁ : Q ⟶ Y} {e : Y ⟶ T} {sndh : A ⟶ Y} {pX : YX ⟶ Y} {ℓ : TS ⟶ M} {pS : TS ⟶ T}
    {κ : YX ⟶ TS}
    (h2 : ql ≫ snd₁ = sndh) (h4 : L ≫ sndh = pX) (h7 : ℓ ≫ snd₂ = pS)
    (h11 : κ ≫ pS = pX ≫ e) (h12 : fst₁ ≫ snd₂ = snd₁ ≫ e) :
    ((L ≫ ql) ≫ fst₁) ≫ snd₂ = (κ ≫ ℓ) ≫ snd₂ := by
  simp only [Category.assoc, h12, reassoc_of% h2, reassoc_of% h4, h7, h11]

end Lifts

section Criterion

variable (w : h ≫ f = e ≫ g) (x : GeometricPoint X)
  (m : strictHenselization B₁ X hX x ⟶ strictHenselization B₂ S hS (x.map f))
  (hm : m ≫ strictHenselizationToBase B₂ S hS (x.map f) = strictHenselizationToBase B₁ X hX x ≫ f)
  (hmpt : geometricPointToStrictHenselization B₁ X hX x ≫ m =
    geometricPointToStrictHenselization B₂ S hS (x.map f))

include hmpt in
/-- The morphism `κ` carries the canonical morphisms into the base changes of an étale
neighbourhood to each other. -/
theorem strictHenselizationBaseChangeSquareMap_lift_eq (V : S.Etale)
    (v : (Scheme.pointSmallEtale (x.map f).hom).fiber.obj V) :
    (strictHenselizationBaseChangeEtaleLift B₁ hX h x
        ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
        ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v) ≫
      (smallEtaleSquareBaseChangeHom f g h e w V).left) ≫
        pullback.fst ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V).hom e =
      strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm ≫
        strictHenselizationBaseChangeEtaleLift B₂ hS g (x.map f) V v := by
  exact pullback.hom_ext
    (fst_eq_of_strictHenselization_squareLifts
      (smallEtaleSquareBaseChangeHom_left_fst_fst f g h e w V) (pullback.lift_fst _ _ _)
      (strictHenselizationNeighborhoodLift_smallEtaleBaseChange_of_square B₁ B₂ hX hS f x m hm
        hmpt V v) (pullback.lift_fst _ _ _)
      (strictHenselizationBaseChangeSquareMap_snd B₁ B₂ hX hS w x m hm))
    (snd_eq_of_strictHenselization_squareLifts
      (MorphismProperty.Over.w (smallEtaleSquareBaseChangeHom f g h e w V))
      (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _)
      (strictHenselizationBaseChangeSquareMap_fst B₁ B₂ hX hS w x m hm).symm pullback.condition)

/-- The canonical morphism into the base change of an étale neighbourhood, followed by the square
isomorphism of base changes, lies over `Y`. -/
theorem strictHenselizationEtaleLift_squareBaseChangeHom_comp (V : S.Etale)
    (v : (Scheme.pointSmallEtale (x.map f).hom).fiber.obj V) :
    (strictHenselizationBaseChangeEtaleLift B₁ hX h x
        ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
        ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v) ≫
      (smallEtaleSquareBaseChangeHom f g h e w V).left) ≫
        ((Stacks.EtaleCohomology.smallEtaleBaseChange e).obj
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)).hom =
      strictHenselizationBaseChangeToSource B₁ hX h x :=
  (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
    (MorphismProperty.Over.w (smallEtaleSquareBaseChangeHom f g h e w V))).trans
      (pullback.lift_snd _ _ _))

end Criterion

/-- Identities are étale, so the identity is the final object of a small étale site. -/
local instance containsIdentities_etale_commSq :
    MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
  ⟨fun _ => inferInstance⟩

section DegreeZero

variable (w : h ≫ f = e ≫ g) (x : GeometricPoint X)
  (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (V : S.Etale)
  (v : (Scheme.pointSmallEtale (x.map f).hom).fiber.obj V)
  (σ : ToType (F.obj.obj (op ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V))))

/-- **The stalk of the base change map of a commutative square in degree zero, on germs.** -/
theorem stalkBaseChange_comparison_zero_germ_of_comm :
    Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B₁ hX h x)).obj
        ((smallEtalePullbackAb e).obj F)) (MorphismProperty.Over.mkIdTerminal _ _)
      (((higherDirectImageStalkComparison B₁ hX h x).app 0).app ((smallEtalePullbackAb e).obj F)
        (((higherBaseChangeStalkHom f g h e w x.hom).app 0).app F
          ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
            ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
              ((smallEtalePushforwardAb g).obj F).obj σ)))) =
      sectionsRestrictionAlong (strictHenselizationBaseChangeToSource B₁ hX h x)
        ((smallEtalePullbackAb e).obj F)
        ((Stacks.EtaleCohomology.smallEtaleBaseChange e).obj
          ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V))
        (strictHenselizationBaseChangeEtaleLift B₁ hX h x
            ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
            ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v) ≫
          (smallEtaleSquareBaseChangeHom f g h e w V).left)
        (strictHenselizationEtaleLift_squareBaseChangeHom_comp B₁ hX w x V v)
        (smallEtalePullbackAbUnitApp e F ((Stacks.EtaleCohomology.smallEtaleBaseChange g).obj V)
          σ) := by
  have hkey := map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero f g h e w F
  have hnat : (smallEtaleStalkPullbackAbIso f x.hom).inv.app
        (((smallEtalePushforwardAb g).rightDerived 0).obj F)
      ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
        ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
          ((smallEtalePushforwardAb g).obj F).obj σ)) =
      (smallEtaleStalkAb x.hom).map ((smallEtalePullbackAb f).map
        ((pushforwardIsoRightDerivedZero g).hom.app F))
        ((smallEtaleStalkPullbackAbIso f x.hom).inv.app ((smallEtalePushforwardAb g).obj F)
          ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
            ((smallEtalePushforwardAb g).obj F).obj σ)) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans ((ConcreteCategory.congr_hom
      (((smallEtaleStalkPullbackAbIso f x.hom).inv.naturality
        ((pushforwardIsoRightDerivedZero g).hom.app F)).trans
          (congrArg (_ ≫ ·) (Functor.comp_map _ _ _))) _).trans
            (ConcreteCategory.comp_apply _ _ _))
  have hgerm : (smallEtaleStalkPullbackAbIso f x.hom).inv.app ((smallEtalePushforwardAb g).obj F)
      ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
        ((smallEtalePushforwardAb g).obj F).obj σ) =
      (Scheme.pointSmallEtale x.hom).toPresheafFiber
        ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
        ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v)
        ((smallEtalePullbackAb f).obj ((smallEtalePushforwardAb g).obj F)).obj
        (smallEtalePullbackAbUnitApp f ((smallEtalePushforwardAb g).obj F) V σ) :=
    (ConcreteCategory.comp_apply _ _ _).symm.trans ((ConcreteCategory.congr_hom
      (toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv f x.hom
        ((smallEtalePushforwardAb g).obj F) V v) σ).trans (ConcreteCategory.comp_apply _ _ _))
  have hstep : ((higherBaseChangeStalkHom f g h e w x.hom).app 0).app F
      ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
        ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
          ((smallEtalePushforwardAb g).obj F).obj σ)) =
      (smallEtaleStalkAb x.hom).map ((pushforwardIsoRightDerivedZero h).hom.app
          ((smallEtalePullbackAb e).obj F))
        ((Scheme.pointSmallEtale x.hom).toPresheafFiber
          ((Stacks.EtaleCohomology.smallEtaleBaseChange f).obj V)
          ((pointSmallEtaleComapFiberIso f x.hom).hom.app V v)
          ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb e).obj F)).obj
          (((smallEtaleBaseChangeAb f g h e w).app F).hom.app _
            (smallEtalePullbackAbUnitApp f ((smallEtalePushforwardAb g).obj F) V σ))) := by
    refine (ConcreteCategory.comp_apply _ _ _).trans ?_
    refine (congrArg ((smallEtaleStalkAb x.hom).map ((higherBaseChangeMapAb f g h e w 0).app
      F)) hnat).trans ?_
    refine (ConcreteCategory.comp_apply _ _ _).symm.trans ?_
    refine (ConcreteCategory.congr_hom (((smallEtaleStalkAb x.hom).map_comp _ _).symm.trans
      ((congrArg (smallEtaleStalkAb x.hom).map hkey).trans
        ((smallEtaleStalkAb x.hom).map_comp _ _))) _).trans ?_
    refine (ConcreteCategory.comp_apply _ _ _).trans (congrArg _ ?_)
    refine (congrArg _ hgerm).trans ?_
    exact (Scheme.pointSmallEtale x.hom).toPresheafFiber_naturality_apply
      ((smallEtaleBaseChangeAb f g h e w).app F).hom _ _ _
  refine (congrArg (Sheaf.H.equiv₀ ((smallEtalePullbackAb
    (strictHenselizationBaseChangeToSource B₁ hX h x)).obj ((smallEtalePullbackAb e).obj F))
    (MorphismProperty.Over.mkIdTerminal _ _)) ((congrArg
      (((higherDirectImageStalkComparison B₁ hX h x).app 0).app ((smallEtalePullbackAb e).obj F))
        hstep).trans (higherDirectImageStalkComparison_zero_apply' B₁ hX x _ _))).trans ?_
  refine (equiv₀_smallEtaleGlobalSectionsIsoExtZero_hom _ _).trans ?_
  refine (pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber_apply B₁ hX
    ((smallEtalePullbackAb e).obj F) _ _ _).trans ?_
  refine (congrArg _ (smallEtaleBaseChangeAb_app_unitApp f g h e w F V σ)).trans ?_
  exact sectionsRestrictionAlong_map _ _ _ _ _ _ _ _

variable (m : strictHenselization B₁ X hX x ⟶ strictHenselization B₂ S hS (x.map f))
  (hm : m ≫ strictHenselizationToBase B₂ S hS (x.map f) = strictHenselizationToBase B₁ X hX x ≫ f)
  (hmpt : geometricPointToStrictHenselization B₁ X hX x ≫ m =
    geometricPointToStrictHenselization B₂ S hS (x.map f))

/-- The restriction along `κ` in degree zero, read on the identity object. -/
theorem equiv₀_squarePullbackHom_zero (z : Sheaf.H.{u + 1} ((smallEtalePullbackAb
      (strictHenselizationBaseChangeToSource B₂ hS g (x.map f))).obj F) 0) :
    Sheaf.H.equiv₀ ((smallEtalePullbackAb e ⋙ smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B₁ hX h x)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _)
      (((etaleCohomologyRestrictionPrecompHom
        (strictHenselizationBaseChangeToSource B₂ hS g (x.map f))
        (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm) (smallEtalePullbackAb e)
        (strictHenselizationBaseChangeToSource B₁ hX h x)
        (strictHenselizationBaseChangeSquarePullbackHom B₁ B₂ hX hS w x m hm)).app 0).app F z) =
    ((smallEtalePullbackAbComp' (strictHenselizationBaseChangeToSource B₁ hX h x) e _
        rfl).inv.app F).hom.app _
      (Sheaf.H.equiv₀ ((smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B₁ hX h x ≫ e)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _)
      (etaleCohomologyPullback (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm)
        ((smallEtalePullbackAbComp' _ _ _
          (strictHenselizationBaseChangeSquareMap_fst B₁ B₂ hX hS w x m hm)).hom.app F) 0 z)) :=
  (congrArg (Sheaf.H.equiv₀ ((smallEtalePullbackAb e ⋙ smallEtalePullbackAb
        (strictHenselizationBaseChangeToSource B₁ hX h x)).obj F)
        (MorphismProperty.Over.mkIdTerminal _ _))
    ((etaleCohomologyRestrictionPrecompHom_app_app_apply _ _ _ _ _ 0 F z).trans
      (congrArg (fun φ => etaleCohomologyPullback
        (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm) φ 0 z)
        (NatTrans.comp_app _ _ F)))).trans
    (equiv₀_etaleCohomologyPullback_comp_zero _ _ _ z)

include hmpt in
/-- **The two degree-zero composites agree on germs**, for a commutative square. -/
theorem stalkBaseChange_square_zero_germ_of_comm :
    Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B₁ hX h x)).obj
        ((smallEtalePullbackAb e).obj F)) (MorphismProperty.Over.mkIdTerminal _ _)
      (((higherDirectImageStalkComparison B₁ hX h x).app 0).app ((smallEtalePullbackAb e).obj F)
        (((higherBaseChangeStalkHom f g h e w x.hom).app 0).app F
          ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
            ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
              ((smallEtalePushforwardAb g).obj F).obj σ)))) =
    Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B₁ hX h x)).obj
        ((smallEtalePullbackAb e).obj F)) (MorphismProperty.Over.mkIdTerminal _ _)
      (((etaleCohomologyRestrictionPrecompHom
        (strictHenselizationBaseChangeToSource B₂ hS g (x.map f))
        (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm) (smallEtalePullbackAb e)
        (strictHenselizationBaseChangeToSource B₁ hX h x)
        (strictHenselizationBaseChangeSquarePullbackHom B₁ B₂ hX hS w x m hm)).app 0).app F
          (((higherDirectImageStalkComparison B₂ hS g (x.map f)).app 0).app F
            ((smallEtaleStalkAb (x.map f).hom).map ((pushforwardIsoRightDerivedZero g).hom.app F)
              ((Scheme.pointSmallEtale (x.map f).hom).toPresheafFiber V v
                ((smallEtalePushforwardAb g).obj F).obj σ)))) := by
  refine (stalkBaseChange_comparison_zero_germ_of_comm B₁ hX w x F V v σ).trans ?_
  have hR := (congrArg (fun z => Sheaf.H.equiv₀ ((smallEtalePullbackAb
      (strictHenselizationBaseChangeToSource B₁ hX h x)).obj ((smallEtalePullbackAb e).obj F))
      (MorphismProperty.Over.mkIdTerminal _ _)
    (((etaleCohomologyRestrictionPrecompHom
        (strictHenselizationBaseChangeToSource B₂ hS g (x.map f))
        (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm) (smallEtalePullbackAb e)
        (strictHenselizationBaseChangeToSource B₁ hX h x)
        (strictHenselizationBaseChangeSquarePullbackHom B₁ B₂ hX hS w x m hm)).app 0).app F z))
      (higherDirectImageStalkComparison_zero_germ B₂ hS x F V v σ)).trans
    ((equiv₀_squarePullbackHom_zero B₁ B₂ hX hS w x F m hm _).trans (congrArg _
      (equiv₀_etaleCohomologyPullback_sectionsRestrictionAlong
        (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm) _ _
        (strictHenselizationBaseChangeSquareMap_fst B₁ B₂ hX hS w x m hm) F _ _ _ σ)))
  refine Eq.trans ?_ hR.symm
  have hinj : Function.Injective (((smallEtalePullbackAbComp'
      (strictHenselizationBaseChangeToSource B₁ hX h x) e _ rfl).hom.app F).hom.app
        (op (Scheme.Etale.mk (𝟙 _)))) :=
    ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  apply hinj
  refine (smallEtalePullbackAbComp'_sectionsRestrictionAlong_unitApp _ e _ rfl F _ _ _ σ).trans ?_
  refine Eq.trans ?_ (ConcreteCategory.congr_hom (congrArg (fun φ => φ.hom.app
    (op (Scheme.Etale.mk (𝟙 _)))) ((smallEtalePullbackAbComp'
      (strictHenselizationBaseChangeToSource B₁ hX h x) e _ rfl).inv_hom_id_app F)) _ |>.trans
        (ConcreteCategory.id_apply _)).symm
  exact ConcreteCategory.congr_hom (sectionsRestrictionAlong_congr _ F _ _ _ _
    (strictHenselizationBaseChangeSquareMap_lift_eq B₁ B₂ hX hS w x m hm hmpt V v)) σ

end DegreeZero

section Main

variable (w : h ≫ f = e ≫ g) (x : GeometricPoint X)
  (m : strictHenselization B₁ X hX x ⟶ strictHenselization B₂ S hS (x.map f))
  (hm : m ≫ strictHenselizationToBase B₂ S hS (x.map f) = strictHenselizationToBase B₁ X hX x ≫ f)
  (hmpt : geometricPointToStrictHenselization B₁ X hX x ≫ m =
    geometricPointToStrictHenselization B₂ S hS (x.map f))

include hmpt in
/-- **The stalk of the base change map of a commutative square is the restriction along `κ`**, as
morphisms of δ-functors. For a commutative square `h ≫ f = e ≫ g`, a geometric point `x` of `X`
and a morphism `m` of strict henselizations at `x` and `f(x)` lying over `f` and compatible with
the canonical geometric points, the stalk at `x` of
`f⁻¹ R^• g_* F ⟶ R^• h_* e⁻¹ F`, read through Stacks 03Q9 on both sides, is the restriction
`H^•(T ×_S Spec(𝒪^{sh}_{S,f(x)}), F) ⟶ H^•(Y ×_X Spec(𝒪^{sh}_{X,x}), e⁻¹F)` along
`κ = AlgebraicGeometry.strictHenselizationBaseChangeSquareMap`. -/
theorem higherBaseChangeStalkHom_comp_squareRestriction :
    (higherBaseChangeStalkHom f g h e w x.hom ≫
        DeltaFunctor.precompHom (smallEtalePullbackAb e)
          (higherDirectImageStalkComparison B₁ hX h x) :
      higherDirectImageStalkDeltaFunctor g (x.map f) ⟶ _) =
      higherDirectImageStalkComparison B₂ hS g (x.map f) ≫
        etaleCohomologyRestrictionPrecompHom
          (strictHenselizationBaseChangeToSource B₂ hS g (x.map f))
          (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm) (smallEtalePullbackAb e)
          (strictHenselizationBaseChangeToSource B₁ hX h x)
          (strictHenselizationBaseChangeSquarePullbackHom B₁ B₂ hX hS w x m hm) := by
  apply DeltaFunctor.IsUniversal.hom_ext_zero
  refine NatTrans.ext (funext fun F => ?_)
  refine (cancel_epi ((smallEtaleStalkAb (x.map f).hom).map
    ((pushforwardIsoRightDerivedZero g).hom.app F))).1 ?_
  refine (Scheme.pointSmallEtale (x.map f).hom).presheafFiber_hom_ext fun V v => ?_
  ext σ
  exact (Sheaf.H.equiv₀ ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B₁ hX h
    x)).obj ((smallEtalePullbackAb e).obj F)) (MorphismProperty.Over.mkIdTerminal _ _)).injective
      (stalkBaseChange_square_zero_germ_of_comm B₁ B₂ hX hS w x F V v σ m hm hmpt)

include hmpt in
/-- **The stalk of the base change map of a commutative square in one degree.** In degree `q`, for
an abelian sheaf `F` on `T`, the stalk at `x` of `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` followed by the
Stacks 03Q9 identification at `x` is the Stacks 03Q9 identification at `f(x)` followed by pull back
along `κ = AlgebraicGeometry.strictHenselizationBaseChangeSquareMap`. -/
theorem higherBaseChangeStalkHom_comp_squareRestriction_app (q : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    ((higherBaseChangeStalkHom f g h e w x.hom).app q).app F ≫
        ((higherDirectImageStalkComparison B₁ hX h x).app q).app ((smallEtalePullbackAb e).obj F) =
      ((higherDirectImageStalkComparison B₂ hS g (x.map f)).app q).app F ≫
        AddCommGrpCat.ofHom (etaleCohomologyPullback
          (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm)
          ((strictHenselizationBaseChangeSquarePullbackHom B₁ B₂ hX hS w x m hm).app F) q) :=
  congrArg (fun η => (DeltaFunctor.Hom.app η q).app F)
    (higherBaseChangeStalkHom_comp_squareRestriction B₁ B₂ hX hS w x m hm hmpt)

end Main

section OneSite

variable (B : BigEtaleSite.{u}) (hXB : B.Contains X) (hSB : B.Contains S)
  (w : h ≫ f = e ≫ g) (x : GeometricPoint X)

/-- **The stalk of the base change map of a commutative square, in one big étale site**: the
special case of `AlgebraicGeometry.higherBaseChangeStalkHom_comp_squareRestriction` for the
canonical morphism of strict henselizations `AlgebraicGeometry.strictHenselizationSquareMap`. -/
theorem higherBaseChangeStalkHom_comp_squareRestriction_squareMap :
    (higherBaseChangeStalkHom f g h e w x.hom ≫
        DeltaFunctor.precompHom (smallEtalePullbackAb e)
          (higherDirectImageStalkComparison B hXB h x) :
      higherDirectImageStalkDeltaFunctor g (x.map f) ⟶ _) =
      higherDirectImageStalkComparison B hSB g (x.map f) ≫
        etaleCohomologyRestrictionPrecompHom
          (strictHenselizationBaseChangeToSource B hSB g (x.map f))
          (strictHenselizationBaseChangeSquareMap B B hXB hSB w x
            (strictHenselizationSquareMap B hXB hSB f x)
            (strictHenselizationSquareMap_comp B hXB hSB f x))
          (smallEtalePullbackAb e) (strictHenselizationBaseChangeToSource B hXB h x)
          (strictHenselizationBaseChangeSquarePullbackHom B B hXB hSB w x
            (strictHenselizationSquareMap B hXB hSB f x)
            (strictHenselizationSquareMap_comp B hXB hSB f x)) :=
  higherBaseChangeStalkHom_comp_squareRestriction B B hXB hSB w x _ _
    (geometricPointToStrictHenselization_strictHenselizationSquareMap B hXB hSB f x)

end OneSite

section TwoSites

variable (B : BigEtaleSite.{u}) (hXB : B.Contains X) (hSB : B.Contains S)
  (w : h ≫ f = e ≫ g) (x : GeometricPoint X)

/-- **The stalk of the base change map of a commutative square, across two big étale sites**: the
special case of `AlgebraicGeometry.higherBaseChangeStalkHom_comp_squareRestriction` for the
morphism of strict henselizations `AlgebraicGeometry.strictHenselizationSquareMapVia`, formed
through any big étale site `B` containing both `X` and `S`. The strict henselization at `x` is
taken in `B₁` and the one at `f(x)` in `B₂`. -/
theorem higherBaseChangeStalkHom_comp_squareRestriction_squareMapVia :
    (higherBaseChangeStalkHom f g h e w x.hom ≫
        DeltaFunctor.precompHom (smallEtalePullbackAb e)
          (higherDirectImageStalkComparison B₁ hX h x) :
      higherDirectImageStalkDeltaFunctor g (x.map f) ⟶ _) =
      higherDirectImageStalkComparison B₂ hS g (x.map f) ≫
        etaleCohomologyRestrictionPrecompHom
          (strictHenselizationBaseChangeToSource B₂ hS g (x.map f))
          (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x
            (strictHenselizationSquareMapVia B₁ B₂ B hX hS hXB hSB f x)
            (strictHenselizationSquareMapVia_comp B₁ B₂ B hX hS hXB hSB f x))
          (smallEtalePullbackAb e) (strictHenselizationBaseChangeToSource B₁ hX h x)
          (strictHenselizationBaseChangeSquarePullbackHom B₁ B₂ hX hS w x
            (strictHenselizationSquareMapVia B₁ B₂ B hX hS hXB hSB f x)
            (strictHenselizationSquareMapVia_comp B₁ B₂ B hX hS hXB hSB f x)) :=
  higherBaseChangeStalkHom_comp_squareRestriction B₁ B₂ hX hS w x _ _
    (geometricPointToStrictHenselization_strictHenselizationSquareMapVia B₁ B₂ B hX hS hXB hSB f
      x)

end TwoSites

section Isomorphism

variable (w : h ≫ f = e ≫ g) [QuasiCompact g] [QuasiSeparated g] [QuasiCompact h]
  [QuasiSeparated h] (x : GeometricPoint X)
  (m : strictHenselization B₁ X hX x ⟶ strictHenselization B₂ S hS (x.map f))
  (hm : m ≫ strictHenselizationToBase B₂ S hS (x.map f) = strictHenselizationToBase B₁ X hX x ≫ f)
  (hmpt : geometricPointToStrictHenselization B₁ X hX x ≫ m =
    geometricPointToStrictHenselization B₂ S hS (x.map f))

include hmpt in
/-- **Stacks 03Q9, compatibility with base change along a commutative square.** Write
`θ = AlgebraicGeometry.higherDirectImageStalkIso` for the isomorphisms
`(R^q g_* F)_{f(x)} ≅ H^q(T ×_S Spec(𝒪^{sh}_{S,f(x)}), F)` and
`(R^q h_* e⁻¹F)_x ≅ H^q(Y ×_X Spec(𝒪^{sh}_{X,x}), e⁻¹F)`. For a commutative square
`h ≫ f = e ≫ g` with `g`, `h` quasi-compact and quasi-separated, `θ` at `x` after the stalk `b` at
`x` of the base change map `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is `θ` at `f(x)` followed by the pull
back `ρ` along `κ = AlgebraicGeometry.strictHenselizationBaseChangeSquareMap`, the morphism
`Y ×_X Spec(𝒪^{sh}_{X,x}) ⟶ T ×_S Spec(𝒪^{sh}_{S,f(x)})` given by `e` and by the morphism `m`
of strict henselizations: `θ ∘ b = ρ ∘ θ`. -/
@[stacks 03Q9 "compatibility of the isomorphisms with the base change map of a commutative square"]
theorem higherBaseChangeStalkHom_comp_higherDirectImageStalkIso_hom (q : ℕ)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    ((higherBaseChangeStalkHom f g h e w x.hom).app q).app F ≫
        (higherDirectImageStalkIso B₁ hX h x q ((smallEtalePullbackAb e).obj F)).hom =
      (higherDirectImageStalkIso B₂ hS g (x.map f) q F).hom ≫
        AddCommGrpCat.ofHom (etaleCohomologyPullback
          (strictHenselizationBaseChangeSquareMap B₁ B₂ hX hS w x m hm)
          ((strictHenselizationBaseChangeSquarePullbackHom B₁ B₂ hX hS w x m hm).app F) q) :=
  higherBaseChangeStalkHom_comp_squareRestriction_app B₁ B₂ hX hS w x m hm hmpt q F

end Isomorphism

end AlgebraicGeometry
