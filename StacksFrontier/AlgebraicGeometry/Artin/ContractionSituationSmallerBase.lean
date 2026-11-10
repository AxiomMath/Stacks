module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSmallerBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseModification
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase

/-!
# The situation of Artin's theorem on contractions over a smaller base

Let `g : V ⟶ S` be a morphism of a big fppf site `B` with `V` locally Noetherian. Data over `S`
lying over `V` -- an algebraic space `X` with a morphism `X ⟶ V` locally of finite type, a
closed subset `T ⊆ |X|`, a locally Noetherian formal algebraic space `W` with a morphism `W ⟶ V`,
and a formal modification `γ : X_{/T} ⟶ W` over `V` -- give the situation of Stacks 0GH8 with
base scheme `V`, through the change of base of Stacks 04SG: `X` becomes the algebraic space
`X_V` over `V`, `T` its inverse image `T_V ⊆ |X_V|`, `W` the fppf sheaf `W_V` on the big fppf site
of `V`, and `γ` the morphism `X_{V,/T_V} ⟶ W_V` attached to it by the identification of the
completions (`AlgebraicGeometry.Space.completionSheafSmallerBaseIso`). The reduction of `W_V` is
the one of Stacks 0AIN.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionSituation.ofSmallerBase`: the situation over `V`.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_terminal_from_smallerBaseInverse`: `X_V` is
  locally of finite type over `V` when `X ⟶ V` is locally of finite type.
* `AlgebraicGeometry.Artin.ContractionSituation.smallerBaseSheafFunctor_map_ofSmallerBase_g`: the
  formal modification of the situation over `V` is attached to `γ`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

namespace Space

/-- The lower-shriek extension of `X_V` mapping to `h_V` is the structural morphism of `X`. -/
theorem relocalizeToYoneda_smallerBaseInverse
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    OverShriek.relocalizeToYoneda g (smallerBaseInverse B V S hV hS g X) =
      (smallerBaseInverseRelocalizeIso B V S hV hS g X).hom ≫ X.hom := by
  ext T y
  refine Over.OverMorphism.ext ?_
  have hψ0 := OverShriek.relocalizeFactors g _ y
  have h1 := NatTrans.naturality_apply X.hom (smallerBaseFactorHom B V S hV hS g hψ0).op y.1.2.1
  have h2 : (X.hom.app _ y.1.2.1).left = y.1.1 := congrArg Over.Hom.left y.1.2.2
  change y.1.1 = (X.hom.app T (X.left.map (smallerBaseFactorHom B V S hV hS g hψ0).op y.1.2.1)).left
  rw [h1]
  change y.1.1 = (smallerBaseFactorHom B V S hV hS g hψ0 ≫ X.hom.app _ y.1.2.1).left
  rw [Over.comp_left]
  exact ((congrArg (_ ≫ ·) h2).trans (Category.id_comp _)).symm

/-- **Local finite type over a smaller base.** If `X` is a presheaf on the big fppf site of `S`
with a morphism `X ⟶ V` locally of finite type, then the presheaf `X_V` on the big fppf site of
`V` attached to it by Stacks 04SG is locally of finite type over `V`. -/
theorem isLocallyOfFiniteType_terminal_from_smallerBaseInverse
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hX : IsLocallyOfFiniteType B S hS X.hom) :
    IsLocallyOfFiniteType B V hV (terminal.from (smallerBaseInverse B V S hV hS g X)) := by
  let XV := smallerBaseInverse B V S hV hS g X
  let P : MorphismProperty Scheme.{u} := @AlgebraicGeometry.LocallyOfFiniteType
  have h0 : HoldsOnEveryEtaleChart B S hS P
      ((smallerBaseInverseRelocalizeIso B V S hV hS g X).hom ≫ X.hom) :=
    (Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS P
      (smallerBaseInverseRelocalizeIso B V S hV hS g X).hom X.hom).mpr hX
  have h1 : HoldsOnEveryEtaleChart B S hS P (OverShriek.relocalizeToYoneda g XV) :=
    (congrArg (fun f => HoldsOnEveryEtaleChart B S hS P f)
      (relocalizeToYoneda_smallerBaseInverse B V S hV hS g X)).mpr h0
  have h2 := (holdsOnEveryEtaleChart_relocalizeToYoneda_iff B V S hV hS g P XV).mp h1
  have hT : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hV)))) :=
    Over.mkIdTerminal.isTerminalObj yoneda _
  have : IsIso (terminal.from (yoneda.obj (Over.mk (𝟙 (B.obj hV))))) :=
    isIso_of_isTerminal hT terminalIsTerminal _
  have h3 : terminal.from XV = toYonedaId B V hV XV ≫
      terminal.from (yoneda.obj (Over.mk (𝟙 (B.obj hV)))) := terminal.hom_ext _ _
  exact (congrArg (fun f => HoldsOnEveryEtaleChart B V hV P f) h3).mpr
    ((holdsOnEveryEtaleChart_comp_iso_iff B V hV P _ _).mpr h2)

end Space

namespace Artin.ContractionSituation

open FormalSpace

attribute [local instance] Space.pointTopology

/-- The isomorphism between the attached sheaf of the completion of `X_V` along `T_V` and the
completion of `X` along `T`. -/
def smallerBaseCompletionIso
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hX : IsAlgebraicSpace B S hS X.left) (T : Set (Space.points B S hS X.left)) :
    (smallerBaseSheafFunctor B V S hV hS g).obj
        (Space.completionSheaf B V hV (Space.smallerBaseInverse B V S hV hS g X)
          (Space.smallerBaseInverseSet B V S hV hS g X T)) ≅
      Space.completionSheaf B S hS X.left T :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    ((Over.forget _).mapIso (Space.completionSheafSmallerBaseIso B V S hV hS g X T hX))

/-- The isomorphism `smallerBaseCompletionIso`, followed by the morphism from the completion of
`X` along `T` to `V`, is the structure morphism of the attached sheaf over `V`. -/
theorem smallerBaseCompletionIso_hom_comp
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hX : IsAlgebraicSpace B S hS X.left) (T : Set (Space.points B S hS X.left)) :
    (smallerBaseCompletionIso B V S hV hS g X hX T).hom.hom ≫
        Space.completionSheafToSmallerBase B V S hV hS g X T hX =
      (smallerBaseStr B V S hV hS g _).hom :=
  Over.w (Space.completionSheafSmallerBaseIso B V S hV hS g X T hX).hom

/-- **The situation of Stacks 0GH8 over a smaller base.** Let `V` be a locally Noetherian scheme
of the big fppf site, with `g : V ⟶ S`. An algebraic space `X` over `S` with a morphism `X ⟶ V`
locally of finite type, a closed subset `T ⊆ |X|`, an fppf sheaf `W` with a morphism `q : W ⟶ V`
and a formal modification `γ : X_{/T} ⟶ W` over `V`, such that the reduction of the sheaf `W_V`
over `V` attached to `W` is locally of finite type over `V`, form the situation of Stacks 0GH8
with base scheme `V`. -/
def ofSmallerBase (hVN : _root_.AlgebraicGeometry.IsLocallyNoetherian V)
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hX : IsAlgebraicSpace B S hS X.left) (hXlft : Space.IsLocallyOfFiniteType B S hS X.hom)
    (T : Set (Space.points B S hS X.left)) (hT : IsClosed T) (W : FppfSheaf B S hS)
    (q : W ⟶ smallerBaseTarget B V S hV hS g) (γ : Space.completionSheaf B S hS X.left T ⟶ W)
    (hγ : (γ ≫ q).hom = Space.completionSheafToSmallerBase B V S hV hS g X T hX)
    (hmod : IsFormalModification B S hS γ)
    (hred : ∀ (Wred : FppfSheaf B V hV) (i : Wred ⟶ smallerBaseSheafOf B V S hV hS g W q),
      IsReduction B V hV _ Wred i →
        Space.IsLocallyOfFiniteTypeULift.{u + 1} B V hV (terminal.from Wred.obj)) :
    ContractionSituation B V hV :=
  have hWV : FormalSpace.IsLocallyNoetherian B V hV (smallerBaseSheafOf B V S hV hS g W q) :=
    isLocallyNoetherian_of_smallerBaseSheafFunctor B V S hV hS g _
      (smallerBaseSheafOfIso B V S hV hS g W q) hmod.isLocallyNoetherian_target
  have hred' := exists_isReduction_of_isFormalAlgebraicSpace B V hV _ hWV.1
  have hcompat : ((smallerBaseCompletionIso B V S hV hS g X hX T).hom ≫ γ ≫
      (smallerBaseSheafOfIso B V S hV hS g W q).inv) ≫
        smallerBaseStr B V S hV hS g (smallerBaseSheafOf B V S hV hS g W q) =
      smallerBaseStr B V S hV hS g _ := by
    have e1 : (smallerBaseSheafOfIso B V S hV hS g W q).inv ≫
        smallerBaseStr B V S hV hS g (smallerBaseSheafOf B V S hV hS g W q) = q := by
      rw [Iso.inv_comp_eq, smallerBaseSheafOfIso_hom_comp]
    have e2 : (smallerBaseCompletionIso B V S hV hS g X hX T).hom ≫ γ ≫ q =
        smallerBaseStr B V S hV hS g _ :=
      Sheaf.hom_ext ((congrArg ((smallerBaseCompletionIso B V S hV hS g X hX T).hom.hom ≫ ·)
        hγ).trans (smallerBaseCompletionIso_hom_comp B V S hV hS g X hX T))
    rw [Category.assoc, Category.assoc, e1]
    exact e2
  { isLocallyNoetherian_base := hVN
    X' := Space.smallerBaseInverse B V S hV hS g X
    isAlgebraicSpace_X' :=
      isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g X hX
    isLocallyOfFiniteType_X' :=
      Space.isLocallyOfFiniteType_terminal_from_smallerBaseInverse B V S hV hS g X hXlft
    T' := Space.smallerBaseInverseSet B V S hV hS g X T
    isClosed_T' :=
      (Space.isClosed_preimage_pointsSmallerBaseInverseHomeomorph_iff B V S hV hS g X T).mpr hT
    W := smallerBaseSheafOf B V S hV hS g W q
    isLocallyNoetherian_W := hWV
    Wred := hred'.choose
    WredInclusion := hred'.choose_spec.choose
    isReduction_WredInclusion := hred'.choose_spec.choose_spec
    isLocallyOfFiniteType_Wred := hred _ _ hred'.choose_spec.choose_spec
    g := smallerBaseLift B V S hV hS g _ hcompat
    isFormalModification_g := isFormalModification_of_smallerBaseSheafFunctor B V S hV hS g _ γ
      (smallerBaseCompletionIso B V S hV hS g X hX T) (smallerBaseSheafOfIso B V S hV hS g W q)
      (by
        rw [smallerBaseSheafFunctor_map_smallerBaseLift, Category.assoc, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]) hmod }

/-- The formal modification of the situation over `V` is attached to `γ`: under the change of base
of Stacks 04SG it is `γ`, read through the identification of the completions and the isomorphism
`(W_V)` attached `≅ W`. -/
theorem smallerBaseSheafFunctor_map_ofSmallerBase_g
    (hVN : _root_.AlgebraicGeometry.IsLocallyNoetherian V)
    (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (hX : IsAlgebraicSpace B S hS X.left) (hXlft : Space.IsLocallyOfFiniteType B S hS X.hom)
    (T : Set (Space.points B S hS X.left)) (hT : IsClosed T) (W : FppfSheaf B S hS)
    (q : W ⟶ smallerBaseTarget B V S hV hS g) (γ : Space.completionSheaf B S hS X.left T ⟶ W)
    (hγ : (γ ≫ q).hom = Space.completionSheafToSmallerBase B V S hV hS g X T hX)
    (hmod : IsFormalModification B S hS γ)
    (hred : ∀ (Wred : FppfSheaf B V hV) (i : Wred ⟶ smallerBaseSheafOf B V S hV hS g W q),
      IsReduction B V hV _ Wred i →
        Space.IsLocallyOfFiniteTypeULift.{u + 1} B V hV (terminal.from Wred.obj)) :
    (smallerBaseSheafFunctor B V S hV hS g).map
        (ofSmallerBase B V S hV hS g hVN X hX hXlft T hT W q γ hγ hmod hred).g =
      (smallerBaseCompletionIso B V S hV hS g X hX T).hom ≫ γ ≫
        (smallerBaseSheafOfIso B V S hV hS g W q).inv :=
  smallerBaseSheafFunctor_map_smallerBaseLift B V S hV hS g _ _

end Artin.ContractionSituation

end AlgebraicGeometry

end
