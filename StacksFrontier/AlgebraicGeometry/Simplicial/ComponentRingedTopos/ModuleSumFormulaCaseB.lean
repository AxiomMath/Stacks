module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationRestrictCocontinuous
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleLowerShriekPresheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentModuleSumFormulaPresheaf
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationComponents

/-!
# The componentwise direct sum for module lower shriek, case (B)

Let `C` be a cocontinuous simplicial site — case (B) of the simplicial-site situation of
Stacks 09WE — and let `P` be a sheaf of commutative rings on its total site. Stacks 0D72 says
that the restriction to simplicial degree `m` of module lower shriek from degree `n` is the
direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of the module pullbacks along the transitions
`f_φ`. In case (B) the formula holds already on presheaves of modules, and passes to sheaves
through sheafification.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite.transitionModulePullbackB`: the summand `f_φ^*`, the
  sheafification of the presheaf-level module pullback along the transition of `φ`.

## Main results

* `CategoryTheory.CocontinuousSimplicialSite.componentModuleSumFormulaB`: the componentwise
  direct-sum formula of Stacks 0D72 for sheaves of modules in case (B).
* `CategoryTheory.CocontinuousSimplicialSite.presheafSumFormulaB`: the presheaf-level direct-sum
  formula at the identity structure map.
* `CategoryTheory.CocontinuousSimplicialSite.isColimitCofanB`: taking the underlying presheaf of
  modules, forming the direct sum and sheafifying is the direct sum of the three-step composites.
* `CategoryTheory.CocontinuousSimplicialSite.extendScalarsIdIso`: extension of scalars along an
  identity is the identity functor.

## References

* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.ComponentModuleSumFormula

universe u

namespace CategoryTheory.CocontinuousSimplicialSite

variable (C : CocontinuousSimplicialSite.{u})
  (P : Sheaf (situation C).totalTopology CommRingCat.{u}) (n m : SimplexCategory)

/-- The total sheaf of rings of case (B): the structure sheaf read as a sheaf of not necessarily
commutative rings. -/
abbrev totalRingSheafB : Sheaf (situation C).totalTopology RingCat.{u} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (J := (situation C).totalTopology) P)

/-- Sheafification of presheaves of modules on the degree-`m` component. -/
abbrev sheafifyB :
    PresheafOfModules.{u}
        ((situation C).componentRingSheaf (totalRingSheafB C P) m).obj ⥤
      _root_.SheafOfModules.{u}
        ((situation C).componentRingSheaf (totalRingSheafB C P) m) :=
  PresheafOfModules.sheafification.{u} (J := (situation C).componentTopology m)
    (R₀ := ((situation C).componentRingSheaf (totalRingSheafB C P) m).obj)
    (R := (situation C).componentRingSheaf (totalRingSheafB C P) m)
    (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) m).obj)

/-- The underlying presheaf of modules of a sheaf of modules on the degree-`n` component. -/
abbrev forgetB :
    _root_.SheafOfModules.{u}
        ((situation C).componentRingSheaf (totalRingSheafB C P) n) ⥤
      PresheafOfModules.{u}
        ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj :=
  _root_.SheafOfModules.forget _

/-- The summand `f_φ^*` of Stacks 0D72 in case (B): the presheaf-level module pullback along the
transition of `φ`, sheafified. -/
def transitionModulePullbackB (φ : n ⟶ m) :
    _root_.SheafOfModules.{u} ((situation C).componentRingSheaf (totalRingSheafB C P) n) ⥤
      _root_.SheafOfModules.{u} ((situation C).componentRingSheaf (totalRingSheafB C P) m) :=
  forgetB C P n ⋙ transitionPullbackPresheafModules C P.obj φ ⋙ sheafifyB C P m

/-- The direct sum of the case-(B) summands exists. -/
instance (priority := high) hasCoproduct_transitionModulePullbackB :
    HasCoproduct (fun φ : n ⟶ m => transitionModulePullbackB C P n m φ) :=
  letI : HasColimitsOfShape (Discrete (n ⟶ m))
      (_root_.SheafOfModules.{u}
          ((situation C).componentRingSheaf (totalRingSheafB C P) n) ⥤
        _root_.SheafOfModules.{u}
          ((situation C).componentRingSheaf (totalRingSheafB C P) m)) :=
    functorCategoryHasColimitsOfShape
  HasColimitsOfShape.has_colimit _

/-- Extension of scalars along an identity is isomorphic to the identity functor. -/
def extendScalarsIdIso {D : Type u} [SmallCategory D] (S : Dᵒᵖ ⥤ CommRingCat.{u}) :
    Stacks.PullbackModel.extendScalars.{u} (𝟙 S) ≅ Functor.id _ :=
  Adjunction.leftAdjointUniq (Stacks.PullbackModel.extendScalarsAdjunction (𝟙 S)) Adjunction.id

/-- Restriction of presheaves of modules along the degree-`n` component inclusion has a left
adjoint, `Stacks.PullbackColimit.modelAdjunction`. -/
instance isRightAdjoint_pushforwardIdB :
    (PresheafOfModules.pushforward.{u} (Stacks.PullbackColimit.toRingCatPullback
      (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)))).IsRightAdjoint :=
  (Stacks.PullbackColimit.modelAdjunction
    (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))).isRightAdjoint

/-- The presheaf-level formula at the identity structure map: the presheaf-level module pullback
along the degree-`n` component inclusion, restricted to degree `m`, is the direct sum over the
simplex maps of the presheaf-level module pullbacks along the transitions. -/
def presheafSumFormulaB :
    PresheafOfModules.pullback.{u} (Stacks.PullbackColimit.toRingCatPullback
        (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj))) ⋙
      PresheafOfModules.pushforward₀OfCommRingCat
        (Grothendieck.ι C.underlying (op m)) P.obj ≅
      ∐ fun φ : n ⟶ m => transitionPullbackPresheafModules C P.obj φ :=
  pullbackRestrictionIsoCompCoproduct C n m P.obj
      (𝟙 ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)) ≪≫
    Functor.isoWhiskerRight
      (extendScalarsIdIso ((Grothendieck.ι C.underlying (op n)).op ⋙ P.obj)) _ ≪≫
    Functor.leftUnitor _

/-- Taking the underlying presheaf of modules, forming the direct sum and sheafifying is the
direct sum of the three-step composites. -/
def isColimitCofanB :
    IsColimit (Cofan.mk
      (forgetB C P n ⋙ (∐ fun φ : n ⟶ m => transitionPullbackPresheafModules C P.obj φ) ⋙
        sheafifyB C P m)
      fun φ : n ⟶ m => Functor.whiskerLeft (forgetB C P n)
        (Functor.whiskerRight
          (Sigma.ι (fun φ : n ⟶ m => transitionPullbackPresheafModules C P.obj φ) φ)
          (sheafifyB C P m))) :=
  isColimitCofanOfEvaluation _ fun M => isColimitCofanMapOfPreserves (sheafifyB C P m) _
    (isColimitCofanMapOfPreserves ((evaluation _ _).obj ((forgetB C P n).obj M)) _
      (coproductIsCoproduct _))

/-- Restriction of presheaves of modules along the degree-`n` component inclusion, over the
identity structure map of the component ring sheaf, has a left adjoint. -/
local instance isRightAdjointPushforwardComponentB :
    (PresheafOfModules.pushforward.{u}
      (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)).IsRightAdjoint :=
  inferInstanceAs (PresheafOfModules.pushforward.{u}
    (F := SimplicialSiteSituation.componentFunctor (situation C) n)
    (R := (totalRingSheafB C P).obj)
    (S := (SimplicialSiteSituation.componentFunctor (situation C) n).op ⋙
      (totalRingSheafB C P).obj)
    (𝟙 ((SimplicialSiteSituation.componentFunctor (situation C) n).op ⋙
      (totalRingSheafB C P).obj))).IsRightAdjoint

/-- **The componentwise direct-sum formula for sheaves of modules in case (B).** The restriction
to simplicial degree `m` of lower shriek `g_{n!}` of sheaves of `O`-modules from degree `n` is the
direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of the pullbacks `f_φ^*` of sheaves of modules
along the transitions. -/
@[stacks 0D72 "direct-sum formula in case (B), on sheaves of modules"]
def componentModuleSumFormulaB :
    (∐ fun φ : n ⟶ m => transitionModulePullbackB C P n m φ) ≅
      (situation C).componentModuleLowerShriek (totalRingSheafB C P) n ⋙
        (situation C).componentModuleRestriction (totalRingSheafB C P) m :=
  Iso.symm <|
    calc
      (situation C).componentModuleLowerShriek (totalRingSheafB C P) n ⋙
          (situation C).componentModuleRestriction (totalRingSheafB C P) m ≅
        (forgetB C P n ⋙
            PresheafOfModules.pullback.{u}
                (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj) ⋙
              PresheafOfModules.sheafification.{u} (R₀ := (totalRingSheafB C P).obj)
                (𝟙 (totalRingSheafB C P).obj)) ⋙
          (situation C).componentModuleRestriction (totalRingSheafB C P) m :=
        Functor.isoWhiskerRight
          (SimplicialSiteSituation.componentModuleLowerShriekIsoSheafification
            (situation C) (totalRingSheafB C P) n) _
      _ ≅ (forgetB C P n ⋙
              PresheafOfModules.pullback.{u}
                (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)) ⋙
            (PresheafOfModules.sheafification.{u} (R₀ := (totalRingSheafB C P).obj)
                (𝟙 (totalRingSheafB C P).obj) ⋙
              (situation C).componentModuleRestriction (totalRingSheafB C P) m) :=
        Iso.refl _
      _ ≅ (forgetB C P n ⋙
              PresheafOfModules.pullback.{u}
                (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj)) ⋙
            (PresheafOfModules.pushforward₀.{u}
                (SimplicialSiteSituation.componentFunctor (situation C) m)
                (totalRingSheafB C P).obj ⋙
              sheafifyB C P m) :=
        Functor.isoWhiskerLeft _
          (Stacks.SheafOfModules.sheafificationCompRestrictIso
            (SimplicialSiteSituation.componentFunctor (situation C) m)
            ((situation C).componentTopology m) (situation C).totalTopology
            (totalRingSheafB C P))
      _ ≅ forgetB C P n ⋙
            ((PresheafOfModules.pullback.{u}
                  (𝟙 ((situation C).componentRingSheaf (totalRingSheafB C P) n).obj) ⋙
                PresheafOfModules.pushforward₀.{u}
                  (SimplicialSiteSituation.componentFunctor (situation C) m)
                  (totalRingSheafB C P).obj) ⋙
              sheafifyB C P m) :=
        Iso.refl _
      _ ≅ forgetB C P n ⋙
            ((∐ fun φ : n ⟶ m => transitionPullbackPresheafModules C P.obj φ) ⋙
              sheafifyB C P m) :=
        Functor.isoWhiskerLeft _
          (Functor.isoWhiskerRight (presheafSumFormulaB C P n m) (sheafifyB C P m))
      _ ≅ ∐ fun φ : n ⟶ m => transitionModulePullbackB C P n m φ :=
        (isColimitCofanB C P n m).coconePointUniqueUpToIso
          (coproductIsCoproduct fun φ : n ⟶ m => transitionModulePullbackB C P n m φ)

end CategoryTheory.CocontinuousSimplicialSite

end
