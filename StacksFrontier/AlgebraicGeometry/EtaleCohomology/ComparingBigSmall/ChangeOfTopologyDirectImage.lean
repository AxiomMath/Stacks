module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImage
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafConditionSmallEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopologyEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopologyEtaleComparisonDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.SmallEtalePullbackSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.SmallEtalePullbackSheafDescent

/-!
# Proper direct image and the comparison of a big site with the small étale site

Let `τ` be a topology on schemes finer than the étale topology (fppf, ph or h), and let
`a_X : Sh((Sch/X)_τ) ⟶ Sh(X_étale)` be the composite of the change of topology
`ε_X : Sh((Sch/X)_τ) ⟶ Sh((Sch/X)_étale)` with the projection `π_X` to the small étale topos.
For a morphism `f : X ⟶ Y` of the big site there is a canonical base change map

`a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,τ,*} ∘ a_X⁻¹`,

the mate of the identification of the composite direct images. This file proves that it is an
isomorphism when the base change map of Stacks 0DDJ (1) is, and `π_X⁻¹F` is a `τ` sheaf for
every sheaf `F` on `X_étale`. For the fppf topology the second condition is Stacks 0DDL, so the
fppf case, Stacks 0DDN, rests on proper base change (Stacks 0A3U) alone.

## Main definitions

* `AlgebraicGeometry.changeOfTopologyDirectImageSquare` — for two topologies `J ≤ K` on each of
  two categories and a functor `P` continuous for both, the identification
  `ε_{C,*} ⋙ P_{J,*} = P_{K,*} ⋙ ε_{D,*}` of restrictions.
* `AlgebraicGeometry.bigFppfSmallEtaleBaseChange` — the base change map
  `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_X⁻¹` of the big fppf site.

## Main results

* `AlgebraicGeometry.isIso_mateEquiv_symm_changeOfTopologyDirectImageSquare_app` — the base
  change map `ε_D⁻¹ ∘ P_{J,*} ⟶ P_{K,*} ∘ ε_C⁻¹` is invertible at every `J`-sheaf which is
  already a `K`-sheaf.
* `AlgebraicGeometry.isIso_bigFppfSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange` — the
  fppf base change map is invertible, granted the conclusion of Stacks 0A3U for `f`.
* `AlgebraicGeometry.isIso_bigFppfSmallEtaleBaseChange_of_isFinite` — the fppf base change map
  is invertible for `f` finite, unconditionally.

## Implementation notes

The base change map of `a` is the vertical pasting of those of `π` and of `ε`, by Mathlib's
`CategoryTheory.mateEquiv_hcomp`. At a sheaf `G` the first is invertible by Stacks 0DDJ (1);
the second is evaluated at `π_X⁻¹G`, which is a `τ` sheaf, and there it is invertible because
`ε_{X,*}` is fully faithful: the counits of `ε⁻¹ ⊣ ε_*` are invertible and the identification
of the direct images is.

For the ph and h topologies the base change map is proved invertible granted the conclusion of
Stacks 0A3U for `f` and the proper half of the corresponding descent statement; the forms that
deduce these from proper base change alone, through
`smallEtaleSheafDescentFunctor_isEquivalence_of_surjective_proper_of_properBaseChange`
(namespace `AlgebraicGeometry`), are not stated here.

## References

* [Stacks Project, Tag 0DDM](https://stacks.math.columbia.edu/tag/0DDM)
* [Stacks Project, Tag 0DDN](https://stacks.math.columbia.edu/tag/0DDN)
* [Stacks Project, Tag 0DDL](https://stacks.math.columbia.edu/tag/0DDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open Opposite

universe u

namespace AlgebraicGeometry

/-! ### Change of topology along the identity -/

section ChangeOfTopology

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  (J K : GrothendieckTopology C) (J' K' : GrothendieckTopology D)
  [(𝟭 C).IsContinuous J K] [(𝟭 D).IsContinuous J' K']
  (P : D ⥤ C) [P.IsContinuous J' J] [P.IsContinuous K' K]

/-- **Restriction along `P` commutes with change of topology.** For topologies `J ≤ K` on `C`,
`J' ≤ K'` on `D` and a functor `P : D ⥤ C` continuous for both, regarding a `K`-sheaf as a
`J`-sheaf and then restricting along `P` is restricting along `P` and then regarding the
`K'`-sheaf as a `J'`-sheaf. -/
public def changeOfTopologyDirectImageSquare :
    TwoSquare ((𝟭 C).sheafPushforwardContinuous (Type (u + 1)) J K)
      (P.sheafPushforwardContinuous (Type (u + 1)) K' K)
      (P.sheafPushforwardContinuous (Type (u + 1)) J' J)
      ((𝟭 D).sheafPushforwardContinuous (Type (u + 1)) J' K') :=
  letI : (P ⋙ 𝟭 C).IsContinuous J' K := Functor.isContinuous_comp _ _ _ J _
  letI : (𝟭 D ⋙ P).IsContinuous J' K := Functor.isContinuous_comp _ _ _ K' _
  TwoSquare.mk _ _ _ _
    ((Functor.sheafPushforwardContinuousComp P (𝟭 C) (Type (u + 1)) J' J K).hom ≫
      (Functor.sheafPushforwardContinuousIso (Functor.rightUnitor P ≪≫ (Functor.leftUnitor P).symm)
        (Type (u + 1)) J' K).hom ≫
      (Functor.sheafPushforwardContinuousComp (𝟭 D) P (Type (u + 1)) J' K' K).inv)

/-- The natural transformation of `AlgebraicGeometry.changeOfTopologyDirectImageSquare` is an
isomorphism, as a composite of isomorphisms. -/
public instance isIso_changeOfTopologyDirectImageSquare :
    IsIso (changeOfTopologyDirectImageSquare J K J' K' P).natTrans := by
  dsimp only [changeOfTopologyDirectImageSquare, TwoSquare.mk, TwoSquare.natTrans]
  infer_instance

/-- **The base change map of a change of topology is invertible at the sheaves of the finer
topology.** For any left adjoints `ε_C⁻¹`, `ε_D⁻¹` of the two restrictions, the mate
`ε_D⁻¹ ∘ P_{J,*} ⟶ P_{K,*} ∘ ε_C⁻¹` of `AlgebraicGeometry.changeOfTopologyDirectImageSquare` is
invertible at every `J`-sheaf `G` at which the unit of `ε_C⁻¹ ⊣ ε_{C,*}` is invertible, that is,
at every `J`-sheaf which is a `K`-sheaf. -/
public theorem isIso_mateEquiv_symm_changeOfTopologyDirectImageSquare_app
    {LC : Sheaf J (Type (u + 1)) ⥤ Sheaf K (Type (u + 1))}
    {LD : Sheaf J' (Type (u + 1)) ⥤ Sheaf K' (Type (u + 1))}
    (adjC : LC ⊣ (𝟭 C).sheafPushforwardContinuous (Type (u + 1)) J K)
    (adjD : LD ⊣ (𝟭 D).sheafPushforwardContinuous (Type (u + 1)) J' K')
    (G : Sheaf J (Type (u + 1))) [IsIso (adjC.unit.app G)] :
    IsIso (((mateEquiv adjC adjD).symm
      (changeOfTopologyDirectImageSquare J K J' K' P)).natTrans.app G) := by
  have := (Stacks.Sites.sheafPushforwardIdFullyFaithful J K).full
  have := (Stacks.Sites.sheafPushforwardIdFullyFaithful J K).faithful
  have := (Stacks.Sites.sheafPushforwardIdFullyFaithful J' K').full
  have := (Stacks.Sites.sheafPushforwardIdFullyFaithful J' K').faithful
  have e := mateEquiv_counit_symm adjC adjD (changeOfTopologyDirectImageSquare J K J' K' P)
    (LC.obj G)
  have h₁ : IsIso (LD.map ((changeOfTopologyDirectImageSquare J K J' K' P).natTrans.app
      (LC.obj G)) ≫ adjD.counit.app _) := inferInstance
  rw [e] at h₁
  have h₂ : IsIso (((mateEquiv adjC adjD).symm
      (changeOfTopologyDirectImageSquare J K J' K' P)).natTrans.app
        (((𝟭 C).sheafPushforwardContinuous (Type (u + 1)) J K).obj (LC.obj G))) :=
    IsIso.of_isIso_comp_right _
      ((P.sheafPushforwardContinuous (Type (u + 1)) K' K).map (adjC.counit.app (LC.obj G)))
  exact (NatTrans.isIso_app_iff_of_iso _ (asIso (adjC.unit.app G))).2 h₂

end ChangeOfTopology

/-- The component of a vertical pasting of 2-squares at an object. -/
private theorem vComp_natTrans_app {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂]
    [Category* C₃] [Category* C₄] [Category* C₅] [Category* C₆]
    {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    {L' : C₃ ⥤ C₅} {R'' : C₄ ⥤ C₆} {B'' : C₅ ⥤ C₆}
    (w : TwoSquare T L R B) (w' : TwoSquare B L' R'' B'') (c : C₁) :
    (w ≫ᵥ w').natTrans.app c = R''.map (w.natTrans.app c) ≫ w'.natTrans.app (L.obj c) := by
  simp [TwoSquare.vComp]

/-! ### The comparison of a big site with the small étale site -/

section General

variable (E : BigEtaleSite.{u}) {X Y : E.Scheme} (f : X ⟶ Y)
  (KX : GrothendieckTopology (Over X)) (KY : GrothendieckTopology (Over Y))
  [(𝟭 (Over X)).IsContinuous (BigEtaleOver.topology E X.obj X.property) KX]
  [(𝟭 (Over Y)).IsContinuous (BigEtaleOver.topology E Y.obj Y.property) KY]
  [(Over.pullback f).IsContinuous KY KX]
  {LX : Sheaf (BigEtaleOver.topology E X.obj X.property) (Type (u + 1)) ⥤ Sheaf KX (Type (u + 1))}
  {LY : Sheaf (BigEtaleOver.topology E Y.obj Y.property) (Type (u + 1)) ⥤ Sheaf KY (Type (u + 1))}
  (adjX : LX ⊣ (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
    (BigEtaleOver.topology E X.obj X.property) KX)
  (adjY : LY ⊣ (𝟭 (Over Y)).sheafPushforwardContinuous (Type (u + 1))
    (BigEtaleOver.topology E Y.obj Y.property) KY)

/-- **The base change map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,τ,*} ∘ a_X⁻¹`** for a topology `τ` on
the big étale category finer than the étale topology, `a_X = π_X ∘ ε_X` being the comparison
with the small étale topos and `ε_X⁻¹` any left adjoint of the change of topology `ε_{X,*}`:
the mate of the vertical pasting of `AlgebraicGeometry.changeOfTopologyDirectImageSquare` and
`AlgebraicGeometry.bigSmallEtaleDirectImageSquare`. -/
public def changeOfTopologySmallEtaleBaseChange :
    E.smallPushforward f (Type (u + 1)) ⋙
        ((bigEtaleToSmallEtaleMorphism E Y.obj Y.property).inverseImage ⋙ LY) ⟶
      ((bigEtaleToSmallEtaleMorphism E X.obj X.property).inverseImage ⋙ LX) ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1)) KY KX :=
  ((mateEquiv ((bigEtaleProjectionAdjunction E X).comp adjX)
    ((bigEtaleProjectionAdjunction E Y).comp adjY)).symm
    (changeOfTopologyDirectImageSquare (BigEtaleOver.topology E X.obj X.property) KX
      (BigEtaleOver.topology E Y.obj Y.property) KY (Over.pullback f) ≫ₕ
      bigSmallEtaleDirectImageSquare E (Type (u + 1)) f)).natTrans

/-- **The base change map of a big site and the small étale site is an isomorphism**, granted
the base change map `π_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,*} ∘ π_X⁻¹` of Stacks 0DDJ (1) is one and that
`π_X⁻¹G` is a `τ` sheaf for every sheaf `G` on `X_étale`, in the form that the unit of
`ε_X⁻¹ ⊣ ε_{X,*}` is invertible there. This is the argument of Stacks 0DDN, 0DDY and 0EWA: the
base change map is the vertical pasting of that of Stacks 0DDJ (1) and that of the change of
topology, and the latter is invertible at `τ` sheaves. The input `hπ` holds for `f` finite
(`AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_of_isFinite`) and, granted Stacks 0A3U, for
`f` proper (`AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange`). -/
public theorem isIso_changeOfTopologySmallEtaleBaseChange
    (hunit : ∀ G : Sheaf (SmallEtale.topology E X.obj X.property) (Type (u + 1)),
      IsIso (adjX.unit.app ((bigEtaleToSmallEtaleMorphism E X.obj X.property).inverseImage.obj G)))
    (hπ : IsIso (bigSmallEtaleBaseChange E (Type (u + 1)) f (bigEtaleProjectionAdjunction E X)
      (bigEtaleProjectionAdjunction E Y))) :
    IsIso (changeOfTopologySmallEtaleBaseChange E f KX KY adjX adjY) := by
  set s₁ := (mateEquiv (bigEtaleProjectionAdjunction E X) (bigEtaleProjectionAdjunction E Y)).symm
    (bigSmallEtaleDirectImageSquare E (Type (u + 1)) f) with hs₁
  set s₂ := (mateEquiv adjX adjY).symm
    (changeOfTopologyDirectImageSquare (BigEtaleOver.topology E X.obj X.property) KX
      (BigEtaleOver.topology E Y.obj Y.property) KY (Over.pullback f)) with hs₂
  have hdef : changeOfTopologySmallEtaleBaseChange E f KX KY adjX adjY = (s₁ ≫ᵥ s₂).natTrans := by
    rw [changeOfTopologySmallEtaleBaseChange, ← Equiv.symm_apply_apply (mateEquiv _ _) (s₁ ≫ᵥ s₂),
      mateEquiv_hcomp, hs₁, hs₂, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [hdef]
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun c => ?_
  rw [vComp_natTrans_app]
  have := hunit c
  have : IsIso (s₁.natTrans.app c) :=
    NatIso.isIso_app_of_isIso (bigSmallEtaleBaseChange E (Type (u + 1)) f
      (bigEtaleProjectionAdjunction E X) (bigEtaleProjectionAdjunction E Y)) c
  have := isIso_mateEquiv_symm_changeOfTopologyDirectImageSquare_app
    (BigEtaleOver.topology E X.obj X.property) KX
    (BigEtaleOver.topology E Y.obj Y.property) KY (Over.pullback f) adjX adjY
    ((bigEtaleToSmallEtaleMorphism E X.obj X.property).inverseImage.obj c)
  infer_instance

end General

/-! ### The big fppf site -/

section Fppf

variable (B : BigFppfSite.{u})

/-- The adjunction `ε_X⁻¹ ⊣ ε_{X,*}` of the change of topology from fppf to étale, with its
right adjoint spelled as restriction along the identity functor, which it is by definition. -/
public def fppfToBigEtaleAdjunction (X : B.Schemes) :
    (fppfToBigEtaleMorphism B X).inverseImage ⊣
      (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology (associatedBigEtaleSite B) X.1 X.2) (B.topology.over X) :=
  (fppfToBigEtaleMorphism B X).adj

variable {X Y : B.Schemes} (f : X ⟶ Y)

/-- **The base change map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_X⁻¹`** of the square of
topoi of Stacks 0DDM, with `a_X = π_X ∘ ε_X` the comparison of the big fppf topos with the small
étale topos (`AlgebraicGeometry.fppfToSmallEtaleMorphism`). Here `f_{big,fppf,*}` is
restriction along `Over.pullback f`, which is the direct image of
`AlgebraicGeometry.bigFppfMorphism`. -/
public def bigFppfSmallEtaleBaseChange :
    (associatedBigEtaleSite B).smallPushforward f (Type (u + 1)) ⋙
        (fppfToSmallEtaleMorphism B Y).inverseImage ⟶
      (fppfToSmallEtaleMorphism B X).inverseImage ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (B.topology.over Y) (B.topology.over X) :=
  changeOfTopologySmallEtaleBaseChange (associatedBigEtaleSite B) f (B.topology.over X)
    (B.topology.over Y) (fppfToBigEtaleAdjunction B X) (fppfToBigEtaleAdjunction B Y)

/-- **Stacks 0DDN, granted the conclusion of Stacks 0A3U for `f`.** If, for every cartesian
square of schemes with `f` as its right side, the base change map
`Stacks.EtaleCohomology.smallEtaleSetBaseChange` of sheaves of sets on the small étale sites is
an isomorphism — for `f` proper this is proper base change, Stacks 0A3U — then the base change
map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_X⁻¹` is an isomorphism. The second input, that
`π_X⁻¹G` is an fppf sheaf, is Stacks 0DDL, `AlgebraicGeometry.isIso_fppfToBigEtale_unit_app`. -/
public theorem isIso_bigFppfSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange
    (hbc : ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y.obj) (g' : X' ⟶ X.obj) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' ((associatedBigEtaleSite B).inclusion.map f) g),
      IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f'
        ((associatedBigEtaleSite B).inclusion.map f) g sq.w)) :
    IsIso (bigFppfSmallEtaleBaseChange B f) :=
  isIso_changeOfTopologySmallEtaleBaseChange (associatedBigEtaleSite B) f (B.topology.over X)
    (B.topology.over Y) (fppfToBigEtaleAdjunction B X) (fppfToBigEtaleAdjunction B Y)
    (fun G => isIso_fppfToBigEtale_unit_app B X G)
    (isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange (associatedBigEtaleSite B) f
      hbc)

/-- **Stacks 0DDN, granted Stacks 0A3U.** If the base change map
`Stacks.EtaleCohomology.smallEtaleSetBaseChange` of every cartesian square of schemes with proper
right side is an isomorphism — the conclusion of Stacks 0A3U — then for `f` proper the base change
map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_X⁻¹` is an isomorphism. -/
public theorem isIso_bigFppfSmallEtaleBaseChange_of_properBaseChange
    [IsProper ((associatedBigEtaleSite B).inclusion.map f)]
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w)) :
    IsIso (bigFppfSmallEtaleBaseChange B f) :=
  isIso_bigFppfSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange B f
    fun _ _ g g' f' sq => h0A3U _ g g' f' sq inferInstance

/-- **Stacks 0DDN for `f` finite, unconditionally.** For a finite morphism `f` the base change
map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,fppf,*} ∘ a_X⁻¹` is an isomorphism: the base change map of
Stacks 0DDJ (1) is one for finite `f` by Stacks 0959,
`AlgebraicGeometry.isIso_bigSmallEtaleBaseChange_of_isFinite`, and `π_X⁻¹G` is an fppf sheaf by
Stacks 0DDL. This is the case used in the proof of Stacks 0DEU. -/
public theorem isIso_bigFppfSmallEtaleBaseChange_of_isFinite
    [IsFinite ((associatedBigEtaleSite B).inclusion.map f)] :
    IsIso (bigFppfSmallEtaleBaseChange B f) :=
  isIso_changeOfTopologySmallEtaleBaseChange (associatedBigEtaleSite B) f (B.topology.over X)
    (B.topology.over Y) (fppfToBigEtaleAdjunction B X) (fppfToBigEtaleAdjunction B Y)
    (fun G => isIso_fppfToBigEtale_unit_app B X G)
    (isIso_bigSmallEtaleBaseChange_of_isFinite (associatedBigEtaleSite B) f)

end Fppf

/-! ### The big ph site -/

section Ph

variable (B : BigPHSite.{u})

/-- The adjunction `ε_X⁻¹ ⊣ ε_{X,*}` of the change of topology from ph to étale, with its right
adjoint spelled as restriction along the identity functor, which it is by definition. -/
public def phToBigEtaleAdjunction (X : B.Schemes) :
    (phToBigEtaleMorphism B X).inverseImage ⊣
      (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology (phAssociatedBigEtaleSite B) X.1 X.2) (B.topology.over X) :=
  (phToBigEtaleMorphism B X).adj

variable {X Y : B.Schemes} (f : X ⟶ Y)

/-- **The base change map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,ph,*} ∘ a_X⁻¹`** of the square of topoi
of Stacks 0DDX, with `a_X = π_X ∘ ε_X` the comparison of the big ph topos with the small étale
topos (`AlgebraicGeometry.phToSmallEtaleMorphism`). Here `f_{big,ph,*}` is restriction along
`Over.pullback f`, which is the direct image of `AlgebraicGeometry.bigPHMorphism`. -/
public def bigPHSmallEtaleBaseChange :
    (phAssociatedBigEtaleSite B).smallPushforward f (Type (u + 1)) ⋙
        (phToSmallEtaleMorphism B Y).inverseImage ⟶
      (phToSmallEtaleMorphism B X).inverseImage ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (B.topology.over Y) (B.topology.over X) :=
  changeOfTopologySmallEtaleBaseChange (phAssociatedBigEtaleSite B) f (B.topology.over X)
    (B.topology.over Y) (phToBigEtaleAdjunction B X) (phToBigEtaleAdjunction B Y)

/-- **Stacks 0DDY, granted the conclusion of Stacks 0A3U for `f` and the proper half of Stacks
0DDW over `X`.** If the base change map `Stacks.EtaleCohomology.smallEtaleSetBaseChange` of every
cartesian square with `f` as its right side is an isomorphism (Stacks 0A3U, for `f` proper), and
for every sheaf `G` on `X_étale` the presheaf `π_X⁻¹G` satisfies descent along the proper
surjective morphisms of the big ph site over `X` (the half of Stacks 0DDW which the source
deduces from Stacks 0A3T, `AlgebraicGeometry.IsProperSurjectiveSheaf`; the Zariski half is
`AlgebraicGeometry.smallEtaleInverseImage_isZariskiSheaf_ph`), then the base change map
`a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,ph,*} ∘ a_X⁻¹` is an isomorphism. -/
public theorem isIso_bigPHSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange
    (hproper : ∀ G : Sheaf (SmallEtale.topology (phAssociatedBigEtaleSite B) X.1 X.2)
      (Type (u + 1)),
      IsProperSurjectiveSheaf B X.1 X.2
        ((bigEtaleToSmallEtaleMorphism (phAssociatedBigEtaleSite B) X.1 X.2).inverseImage.obj
          G).obj)
    (hbc : ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y.obj) (g' : X' ⟶ X.obj) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' ((phAssociatedBigEtaleSite B).inclusion.map f) g),
      IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f'
        ((phAssociatedBigEtaleSite B).inclusion.map f) g sq.w)) :
    IsIso (bigPHSmallEtaleBaseChange B f) :=
  isIso_changeOfTopologySmallEtaleBaseChange (phAssociatedBigEtaleSite B) f (B.topology.over X)
    (B.topology.over Y) (phToBigEtaleAdjunction B X) (phToBigEtaleAdjunction B Y)
    (fun G => smallEtaleInverseImage_isIso_phToBigEtale_unit_app_of_properSurjective B X.1 X.2 G
      (hproper G))
    (isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange (phAssociatedBigEtaleSite B) f
      hbc)

end Ph

/-! ### The big h site -/

section H

variable (B : BigHSite.{u})

/-- The adjunction `ε_X⁻¹ ⊣ ε_{X,*}` of the change of topology from h to étale, with its right
adjoint spelled as restriction along the identity functor, which it is by definition. -/
public def hToBigEtaleAdjunction (X : B.Schemes) :
    (hToBigEtaleMorphism B X).inverseImage ⊣
      (𝟭 (Over X)).sheafPushforwardContinuous (Type (u + 1))
        (BigEtaleOver.topology (hAssociatedBigEtaleSite B) X.1 X.2) (B.topology.over X) :=
  (hToBigEtaleMorphism B X).adj

variable {X Y : B.Schemes} (f : X ⟶ Y)

/-- **The base change map `a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,h,*} ∘ a_X⁻¹`** of the square of topoi
of Stacks 0EW9, with `a_X = π_X ∘ ε_X` the comparison of the big h topos with the small étale
topos (`AlgebraicGeometry.hToSmallEtaleMorphism`). Here `f_{big,h,*}` is restriction along
`Over.pullback f`. -/
public def bigHSmallEtaleBaseChange :
    (hAssociatedBigEtaleSite B).smallPushforward f (Type (u + 1)) ⋙
        (hToSmallEtaleMorphism B Y).inverseImage ⟶
      (hToSmallEtaleMorphism B X).inverseImage ⋙
        (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
          (B.topology.over Y) (B.topology.over X) :=
  changeOfTopologySmallEtaleBaseChange (hAssociatedBigEtaleSite B) f (B.topology.over X)
    (B.topology.over Y) (hToBigEtaleAdjunction B X) (hToBigEtaleAdjunction B Y)

/-- **Stacks 0EWA, granted the conclusion of Stacks 0A3U for `f` and the proper half of Stacks
0EW8 over `X`.** If the base change map `Stacks.EtaleCohomology.smallEtaleSetBaseChange` of every
cartesian square with `f` as its right side is an isomorphism (Stacks 0A3U, for `f` proper), and
for every sheaf `G` on `X_étale` the presheaf `π_X⁻¹G` satisfies descent along the proper
surjective morphisms of finite presentation of the big h site over `X` (the half of Stacks 0EW8
which the source deduces from Stacks 0DDW and so from Stacks 0A3T,
`AlgebraicGeometry.BigHOver.IsProperFinitePresentationSheaf`; the Zariski half is
`AlgebraicGeometry.smallEtaleInverseImage_isZariskiSheaf_h`), then the base change map
`a_Y⁻¹ ∘ f_{small,*} ⟶ f_{big,h,*} ∘ a_X⁻¹` is an isomorphism. -/
public theorem isIso_bigHSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange
    (hproper : ∀ G : Sheaf (SmallEtale.topology (hAssociatedBigEtaleSite B) X.1 X.2)
      (Type (u + 1)),
      BigHOver.IsProperFinitePresentationSheaf B X.1 X.2
        ((bigEtaleToSmallEtaleMorphism (hAssociatedBigEtaleSite B) X.1 X.2).inverseImage.obj
          G).obj)
    (hbc : ∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y.obj) (g' : X' ⟶ X.obj) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' ((hAssociatedBigEtaleSite B).inclusion.map f) g),
      IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f'
        ((hAssociatedBigEtaleSite B).inclusion.map f) g sq.w)) :
    IsIso (bigHSmallEtaleBaseChange B f) :=
  isIso_changeOfTopologySmallEtaleBaseChange (hAssociatedBigEtaleSite B) f (B.topology.over X)
    (B.topology.over Y) (hToBigEtaleAdjunction B X) (hToBigEtaleAdjunction B Y)
    (fun G => smallEtaleInverseImage_isIso_hToBigEtale_unit_app_of_properFinitePresentation B
      X.1 X.2 G (hproper G))
    (isIso_bigSmallEtaleBaseChange_of_isIso_smallEtaleSetBaseChange (hAssociatedBigEtaleSite B) f
      hbc)

end H

end AlgebraicGeometry

end
