module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeProjectionFormula
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.PhTorsionComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImage
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafCondition
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.PhToEtaleSquares

/-!
# Proper direct image commutes with the comparison of the big ph and small étale topoi

Let `B` be a big ph site and `f : X ⟶ Y` a morphism of it. Stacks 0DDX gives the commutative
square of topoi `a_Y ∘ f_{big,ph} = f_{small} ∘ a_X`, where `a_X = π_X ∘ ε_X` is the composite of
the change of topology `ε_X : Sh((Sch/X)_ph) ⟶ Sh((Sch/X)_étale)` with the projection
`π_X : Sh((Sch/X)_étale) ⟶ Sh(X_étale)`. Its base change map

`a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,ph,*} ∘ a_X⁻¹`

is the mate of the identification of direct images of that square. This file proves that it is
an isomorphism when `f` is proper (Stacks 0DDY).

## Main definitions

* `AlgebraicGeometry.bigPHSmallEtaleDirectImageBaseChange` — the base change map
  `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,ph,*} ∘ a_X⁻¹`, the mate of
  `AlgebraicGeometry.bigPHSmallEtale_pushforwardCommIso` (Stacks 0DDX).
* `AlgebraicGeometry.bigPHSmallEtaleDirectImageIso` — for `f` proper, the resulting isomorphism
  `a_Y⁻¹ ∘ f_{small,*} ≅ f_{big,ph,*} ∘ a_X⁻¹`.

## Main results

* `AlgebraicGeometry.isIso_bigPHSmallEtaleDirectImageBaseChange` — **Stacks 0DDY**.

## Implementation notes

The proof is the source's. The square of Stacks 0DDX is, by its construction, the horizontal
pasting of the big ph–big étale square (for `ε`) and the big–small étale square of Stacks 021I
(for `π`), and the adjunction of `a_X` is the composite of those of `π_X` and `ε_X`. By the
pasting law for mates (`CategoryTheory.mateEquiv_hcomp`) the base change map of `a` is therefore,
at a sheaf `F` on `X_étale`, the composite of `ε_Y⁻¹` applied to the base change map of `π` at `F`
and the base change map of `ε` at `π_X⁻¹F`.

* The base change map of `π` is that of Stacks 0DDJ (1),
  `AlgebraicGeometry.bigSmallEtaleBaseChange` (up to the identification
  `AlgebraicGeometry.bigEtaleMorphismPushforwardIso` of the big étale direct image with restriction
  along base change); it is invertible for `f` proper by proper base change for sheaves of sets,
  Stacks 0A3U, `Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper`.
* The base change map of `ε` is invertible at `π_X⁻¹F`: `ε_{Y,*}` is fully faithful (it forgets
  that a ph sheaf is a ph sheaf), so the counit of `ε_Y⁻¹ ⊣ ε_{Y,*}` is invertible, and the unit of
  `ε_X⁻¹ ⊣ ε_{X,*}` is invertible at `π_X⁻¹F` because `π_X⁻¹F` is a ph sheaf, Stacks 0DDW,
  `AlgebraicGeometry.smallEtaleInverseImage_isSheaf_ph`.

The source phrases the second step as "`ε_{Y,*}` reflects isomorphisms and
`ε_{Y,*} ∘ a_Y⁻¹ = π_Y⁻¹`"; the mate computation above is the same argument.

## References

* [Stacks Project, Tag 0DDY](https://stacks.math.columbia.edu/tag/0DDY)
* [Stacks Project, Tag 0DDX](https://stacks.math.columbia.edu/tag/0DDX)
* [Stacks Project, Tag 0DDJ](https://stacks.math.columbia.edu/tag/0DDJ)
* [Stacks Project, Tag 0DDW](https://stacks.math.columbia.edu/tag/0DDW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare

universe u

namespace AlgebraicGeometry

variable (B : BigPHSite.{u}) {X Y : B.Schemes} (f : X ⟶ Y)

/-- **The base change map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,ph,*} ∘ a_X⁻¹`** of the square of topoi
`a_Y ∘ f_{big,ph} = f_{small} ∘ a_X` of Stacks 0DDX: the mate, along the adjunctions
`a_X⁻¹ ⊣ a_{X,*}` and `a_Y⁻¹ ⊣ a_{Y,*}`, of the identification
`AlgebraicGeometry.bigPHSmallEtale_pushforwardCommIso` of the two composite direct images. Here
`a_X` is `AlgebraicGeometry.phToSmallEtaleMorphism`, `f_{small}` is
`AlgebraicGeometry.phSmallEtaleMorphism` and `f_{big,ph}` is `AlgebraicGeometry.bigPHMorphism`. -/
public def bigPHSmallEtaleDirectImageBaseChange :
    (phSmallEtaleMorphism B f).pushforward ⋙ (phToSmallEtaleMorphism B Y).inverseImage ⟶
      (phToSmallEtaleMorphism B X).inverseImage ⋙ (bigPHMorphism B X Y f).pushforward :=
  ((mateEquiv (phToSmallEtaleMorphism B X).adj (phToSmallEtaleMorphism B Y).adj).symm
    (TwoSquare.mk _ _ _ _ (bigPHSmallEtale_pushforwardCommIso B f).hom)).natTrans

/-- **Stacks 0DDY.** Let `B` be a big ph site and `f : X ⟶ Y` a proper morphism of it. Then
`a_Y⁻¹ ∘ f_{small,*} = f_{big,ph,*} ∘ a_X⁻¹` as functors from sheaves of sets on `X_étale` to
sheaves of sets on `(Sch/Y)_ph`: the base change map
`AlgebraicGeometry.bigPHSmallEtaleDirectImageBaseChange` of the square of topoi of Stacks 0DDX
is an isomorphism. -/
@[stacks 0DDY]
public theorem isIso_bigPHSmallEtaleDirectImageBaseChange [IsProper (B.inclusion.map f)] :
    IsIso (bigPHSmallEtaleDirectImageBaseChange B f) := by
  let E := phAssociatedBigEtaleSite B
  let εX := phToBigEtaleMorphism B X
  let εY := phToBigEtaleMorphism B Y
  let πX := bigEtaleToSmallEtaleMorphism E X.1 X.2
  let πY := bigEtaleToSmallEtaleMorphism E Y.1 Y.2
  let s := phSmallEtaleMorphism B f
  let e := bigEtaleMorphism E X Y f
  let b := bigPHMorphism B X Y f
  -- the two squares of which the square of Stacks 0DDX is the horizontal pasting
  let wε : TwoSquare εX.pushforward b.pushforward e.pushforward εY.pushforward :=
    TwoSquare.mk _ _ _ _ (bigPHBigEtale_pushforwardCommIso B f).hom
  let wπ : TwoSquare πX.pushforward e.pushforward s.pushforward πY.pushforward :=
    TwoSquare.mk _ _ _ _ (bigSmallEtalePushforwardCommIso E X Y f).hom
  -- their base change maps
  let γε := (mateEquiv εX.adj εY.adj).symm wε
  let γπ := (mateEquiv πX.adj πY.adj).symm wπ
  have hpaste : bigPHSmallEtaleDirectImageBaseChange B f = (γπ ≫ᵥ γε).natTrans := by
    have h := mateEquiv_hcomp πX.adj πY.adj εX.adj εY.adj γπ γε
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    show ((mateEquiv (πX.adj.comp εX.adj) (πY.adj.comp εY.adj)).symm (wε ≫ₕ wπ)).natTrans = _
    rw [← h, Equiv.symm_apply_apply]
  -- the base change map of `π` is that of Stacks 0DDJ (1), invertible by Stacks 0A3U
  have hπ (c : Sheaf (SmallEtale.topology E X.1 X.2) (Type (u + 1))) :
      IsIso (γπ.natTrans.app c) := by
    have h0DDJ : IsIso (bigSmallEtaleBaseChange E (Type (u + 1)) f
        (bigEtaleProjectionAdjunction E X) (bigEtaleProjectionAdjunction E Y)) :=
      isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange E f
        fun _ _ g g' f' sq =>
          Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_isProper _ g g' f' sq
    -- `wπ` is the square of Stacks 0DDJ (1) whiskered by `f_{big,*} ≅ (Over.pullback f)_*`
    have hw : wπ = ((bigSmallEtaleDirectImageSquare E (Type (u + 1)) f).whiskerRight
        (𝟙 _)).whiskerLeft (bigEtaleMorphismPushforwardIso E X Y f).inv := by
      refine TwoSquare.ext _ _ fun F => ?_
      rfl
    let β := (mateEquiv (bigEtaleProjectionAdjunction E X)
      (bigEtaleProjectionAdjunction E Y)).symm (bigSmallEtaleDirectImageSquare E (Type (u + 1)) f)
    have hγ : γπ = (β.whiskerTop (𝟙 _)).whiskerBottom
        (bigEtaleMorphismPushforwardIso E X Y f).inv := by
      have h := Stacks.CategoryTheory.BaseChange.mateEquiv_whiskerTop_whiskerBottom
        (bigEtaleProjectionAdjunction E X) (bigEtaleProjectionAdjunction E Y) β (𝟙 _)
        (bigEtaleMorphismPushforwardIso E X Y f).inv
      rw [Equiv.apply_symm_apply] at h
      exact (congrArg (mateEquiv πX.adj πY.adj).symm hw).trans
        ((Equiv.eq_symm_apply _).mpr h).symm
    have hβ : IsIso (β.natTrans.app c) :=
      NatIso.isIso_app_of_isIso (bigSmallEtaleBaseChange E (Type (u + 1)) f
        (bigEtaleProjectionAdjunction E X) (bigEtaleProjectionAdjunction E Y)) c
    have happ : ((β.whiskerTop (𝟙 _)).whiskerBottom
        (bigEtaleMorphismPushforwardIso E X Y f).inv).natTrans.app c =
          β.natTrans.app c ≫ (bigEtaleMorphismPushforwardIso E X Y f).inv.app _ := by
      simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
    rw [hγ, happ]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hβ inferInstance
  -- the base change map of `ε` is invertible at `π_X⁻¹F`, a ph sheaf by Stacks 0DDW
  have hε (c : Sheaf (SmallEtale.topology E X.1 X.2) (Type (u + 1))) :
      IsIso (γε.natTrans.app (πX.inverseImage.obj c)) := by
    -- `ε_{Y,*}` is fully faithful, so the counit of `ε_Y⁻¹ ⊣ ε_{Y,*}` is invertible
    have hcounit : IsIso εY.adj.counit := by
      have := (Stacks.Sites.sheafPushforwardIdFullyFaithful
        (BigEtaleOver.topology E Y.1 Y.2) (B.topology.over Y)).full
      have := (Stacks.Sites.sheafPushforwardIdFullyFaithful
        (BigEtaleOver.topology E Y.1 Y.2) (B.topology.over Y)).faithful
      have : εY.pushforward.Full := ‹_›
      have : εY.pushforward.Faithful := ‹_›
      infer_instance
    have hunit : IsIso (εX.adj.unit.app (πX.inverseImage.obj c)) :=
      (smallEtaleInverseImage_isSheaf_ph B X.1 X.2 c).2
    have hc : γε.natTrans.app (πX.inverseImage.obj c) =
        εY.inverseImage.map (e.pushforward.map (εX.adj.unit.app (πX.inverseImage.obj c))) ≫
          εY.inverseImage.map (wε.natTrans.app _) ≫ εY.adj.counit.app _ := by
      simp [γε]
    have hwε : IsIso wε.natTrans :=
      inferInstanceAs (IsIso (bigPHBigEtale_pushforwardCommIso B f).hom)
    rw [hc]
    infer_instance
  rw [hpaste]
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun c => ?_
  have hvc : (γπ ≫ᵥ γε).natTrans.app c =
      εY.inverseImage.map (γπ.natTrans.app c) ≫ γε.natTrans.app (πX.inverseImage.obj c) := by
    simp [TwoSquare.vComp]
  rw [hvc]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _
    (@Functor.map_isIso _ _ _ _ _ _ εY.inverseImage _ (hπ c)) (hε c)

/-- **Stacks 0DDY**, as an isomorphism: for a proper morphism `f : X ⟶ Y` of a big ph site,
`a_Y⁻¹ ∘ f_{small,*} ≅ f_{big,ph,*} ∘ a_X⁻¹`, the isomorphism being the base change map
`AlgebraicGeometry.bigPHSmallEtaleDirectImageBaseChange`. -/
public def bigPHSmallEtaleDirectImageIso [IsProper (B.inclusion.map f)] :
    (phSmallEtaleMorphism B f).pushforward ⋙ (phToSmallEtaleMorphism B Y).inverseImage ≅
      (phToSmallEtaleMorphism B X).inverseImage ⋙ (bigPHMorphism B X Y f).pushforward :=
  have := isIso_bigPHSmallEtaleDirectImageBaseChange B f
  asIso (bigPHSmallEtaleDirectImageBaseChange B f)

end AlgebraicGeometry

end
