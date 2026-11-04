module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEqualizerCompletion
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSituationSmallerBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionReductionFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseRepresentable

/-!
# The equalizer triple of Stacks 0GHD as a situation over `V`

In the situation of Stacks 0GH8, let `V` be an object of the big fppf site of `S` and let `d` be
the data of Stacks 0GHD over `V`: two elements of `F(V)` with chosen compatibility witnesses. The
remark constructs `E' ⟶ V`, the closed subset `(E' ⟶ V)⁻¹ Z ⊆ |E'|`, the formal algebraic space
`E_W ⟶ V_{/Z} ⟶ V` and the morphism `E'_{/Z} ⟶ E_W`, all over `S` with morphisms to `V`. This file
turns them into the situation of Stacks 0GH8 with base scheme `V`, through the change of base of
Stacks 04SG (`AlgebraicGeometry.Artin.ContractionSituation.ofSmallerBase`), given that `V` is
locally Noetherian and that `E'_{/Z} ⟶ E_W` is a formal modification over `S`. The remaining
condition, that the reduction of `E_W` viewed over `V` is locally of finite type over `V`, is
proved here: `E_W ⟶ V_{/Z}` is a base change of the diagonal of `W`, locally of finite type by
Stacks 0AIP.

## Main definitions

* `AlgebraicGeometry.Artin.ContractionEqualizer.EWToTarget`: the morphism `E_W ⟶ V`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.relocalizedSituation`: the triple as a situation
  over `V`.

## Main results

* `AlgebraicGeometry.Artin.ContractionEqualizer.completedToEW_comp_EWToTarget`: `E'_{/Z} ⟶ E_W` is
  a morphism over `V`.
* `AlgebraicGeometry.Artin.ContractionEqualizer.relative_locallyOfFiniteType_ι_EW`: `E_W ⟶ V_{/Z}`
  is representable and locally of finite type.
* `AlgebraicGeometry.Artin.ContractionEqualizer.isLocallyOfFiniteTypeULift_of_isReduction`: the
  reduction of `E_W` viewed over `V` is locally of finite type over `V`.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHD](https://stacks.math.columbia.edu/tag/0GHD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Artin.ContractionEqualizer

open FormalSpace

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {c : ContractionSituation B S hS} {V : BigFppfOver B S hS}
    (d : ContractionEqualizer c V)

/-- `E' ⟶ V`, as a presheaf over the representable presheaf of `V`. -/
abbrev E'OverV : Over (yoneda.obj (Over.mk (V.hom : B.obj V.left.property ⟶ B.obj hS)) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Over.mk d.toBase

/-- The morphism `E_W ⟶ V_{/Z} ⟶ V` into the universe-lifted representable sheaf of `V`. -/
def EWToTarget :
    d.EW ⟶ smallerBaseTarget B V.left.obj S V.left.property hS V.hom :=
  d.EWToBase ≫ ObjectProperty.homMk
    (Space.sheafifiedULiftIso B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V).isSheaf).inv

/-- The closed set `(E' ⟶ V)⁻¹ Z ⊆ |E'|` is closed. -/
theorem isClosed_centerEqz : IsClosed d.centerEqz :=
  d.isClosed_Z.preimage (Space.continuous_pointsMap B S hS d.toBase)

/-- `E'_{/Z} ⟶ E_W` is a morphism over `V`: followed by `E_W ⟶ V` it is the morphism
`E'_{/Z} ⟶ E' ⟶ V`. -/
theorem completedToEW_comp_EWToTarget :
    (d.completedToEW ≫ d.EWToTarget).hom =
      Space.completionSheafToSmallerBase B V.left.obj S V.left.property hS V.hom d.E'OverV
        d.centerEqz d.isAlgebraicSpace_eqz := by
  let J := BigFppfOver.topology B S hS
  have h1 : d.completedToEW ≫ d.EWToBase =
      Space.completionSheafInclusion B S hS d.eqz d.centerEqz ≫
        Space.sheafifiedULiftMap B S hS d.toBase := by
    rw [EWToBase, ← Category.assoc, completedToEW_comp_ι]
    exact Space.completionSheafRestrict_comp_inclusion B S hS d.toBase d.centerEqz d.Z subset_rfl
  have h2 : (d.completedToEW ≫ d.EWToTarget).hom =
      (Space.completionSheafInclusion B S hS d.eqz d.centerEqz).hom ≫
        (Space.sheafifiedULiftMap B S hS d.toBase).hom ≫
        (Space.sheafifiedULiftIso B S hS (yoneda.obj V)
          (isAlgebraicSpace_yoneda B S hS V).isSheaf).inv := by
    rw [EWToTarget, ← Category.assoc, h1]
    rfl
  rw [h2]
  apply J.sheafify_hom_ext _ _ (smallerBaseTarget B V.left.obj S V.left.property hS V.hom).property
  have hyV := (isAlgebraicSpace_yoneda B S hS V).isSheaf
  have hA : J.toSheafify (Space.completionSubfunctor B S hS d.eqz d.centerEqz).toFunctor ≫
      (Space.completionSheafInclusion B S hS d.eqz d.centerEqz).hom =
      (Space.completionSubfunctor B S hS d.eqz d.centerEqz).ι ≫ J.toSheafify _ :=
    (J.toSheafify_naturality _).symm
  have hB : J.toSheafify (d.eqz ⋙ uliftFunctor.{u + 1}) ≫
      (Space.sheafifiedULiftMap B S hS d.toBase).hom =
      Functor.whiskerRight d.toBase uliftFunctor.{u + 1} ≫ J.toSheafify _ :=
    (J.toSheafify_naturality _).symm
  let ιC := (Space.completionSubfunctor B S hS d.eqz d.centerEqz).ι
  let wR := Functor.whiskerRight d.toBase uliftFunctor.{u + 1}
  let inc := (Space.completionSheafInclusion B S hS d.eqz d.centerEqz).hom
  let mp := (Space.sheafifiedULiftMap B S hS d.toBase).hom
  let iv := (Space.sheafifiedULiftIso B S hS (yoneda.obj V) hyV).inv
  let t1 := J.toSheafify (Space.completionSubfunctor B S hS d.eqz d.centerEqz).toFunctor
  let t2 := J.toSheafify (d.eqz ⋙ uliftFunctor.{u + 1})
  let t3 := J.toSheafify (yoneda.obj V ⋙ uliftFunctor.{u + 1})
  let k :=
    (Space.completionSheafIsoSubfunctor B S hS d.isAlgebraicSpace_eqz.isSheaf d.centerEqz).hom
  have lhs : t1 ≫ inc ≫ mp ≫ iv = ιC ≫ wR :=
    (Category.assoc t1 inc (mp ≫ iv)).symm.trans <|
      (congrArg (fun z => z ≫ mp ≫ iv) hA).trans <| (Category.assoc ιC t2 (mp ≫ iv)).trans <|
      congrArg (fun z => ιC ≫ z) <| (Category.assoc t2 mp iv).symm.trans <|
      (congrArg (fun z => z ≫ iv) hB).trans <| (Category.assoc wR t3 iv).trans <|
      (congrArg (fun z => wR ≫ z)
        (Space.sheafifiedULiftIso B S hS (yoneda.obj V) hyV).hom_inv_id).trans (Category.comp_id wR)
  have rhs : t1 ≫ k ≫ ιC ≫ wR = ιC ≫ wR :=
    (Category.assoc t1 k (ιC ≫ wR)).symm.trans <|
      (congrArg (fun z => z ≫ ιC ≫ wR) (Space.completionSheafIsoSubfunctor B S hS
        d.isAlgebraicSpace_eqz.isSheaf d.centerEqz).inv_hom_id).trans (Category.id_comp _)
  exact lhs.trans rhs.symm

/-- `E_W ⟶ V_{/Z}` is representable, with represented base changes locally of finite type: it is
the base change of the diagonal of the formal algebraic space `W` along `(x̂₁, x̂₂)`, which is
representable and locally of finite type by Stacks 0AIP. -/
theorem relative_locallyOfFiniteType_ι_EW :
    (MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative uliftYoneda.{u + 1}
      (equalizer.ι d.xhat₁ d.xhat₂).hom := by
  let J := BigFppfOver.topology B S hS
  let L := MorphismProperty.inverseImage (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have hd := relative_locallyOfFiniteType_diag_of_isFormalAlgebraicSpace B S hS
    c.isLocallyNoetherian_W.1
  have h1 : L.relative (Sheaf.sheafifiedYoneda J) (equalizer.ι d.xhat₁ d.xhat₂) :=
    (MorphismProperty.relative_isStableUnderBaseChange L).of_isPullback
      (isPullback_equalizer_prod d.xhat₁ d.xhat₂).flip hd
  exact relative_of_natIso (sheafifiedYonedaPresheafIso B S hS) L _
    ((Space.relative_comp_map_iff (Sheaf.sheafifiedYoneda J) (sheafToPresheaf J (Type (u + 1)))
      L _).mpr h1)

/-- The morphism `E_W ⟶ V`, on underlying presheaves, is `E_W ⟶ V_{/Z} ⟶ V`. -/
theorem EWToTarget_hom :
    d.EWToTarget.hom = (equalizer.ι d.xhat₁ d.xhat₂).hom ≫
      Space.completionSheafToAmbient B S hS (yoneda.obj V)
        (isSheaf_comp_uliftFunctor B S hS (isAlgebraicSpace_yoneda B S hS V)) d.Z := by
  rw [← Space.completionSheafInclusion_comp_sheafifiedULiftIso_inv B S hS (yoneda.obj V)
    (isAlgebraicSpace_yoneda B S hS V).isSheaf]
  rfl

/-- **The reduction of `E_W`, viewed over `V`, is locally of finite type over `V`.** This is the
condition on the reduction of the formal algebraic space in the situation of Stacks 0GH8 with base
scheme `V`, for the triple of Stacks 0GHD (4).

Through the change of base of Stacks 04SG a reduction `W_red ⟶ W_V` gives a reduced algebraic
space over `S` with a representable closed immersion into `E_W`; since `E_W ⟶ V_{/Z}` is a base
change of the diagonal of `W` (Stacks 0AIP), the composite to `V` is representable and locally of
finite type
(`AlgebraicGeometry.FormalSpace.relative_locallyOfFiniteType_comp_completionSheafToAmbient`), and
that does not see the change of base. -/
theorem isLocallyOfFiniteTypeULift_of_isReduction
    (Wred : FppfSheaf B V.left.obj V.left.property)
    (i : Wred ⟶ smallerBaseSheafOf B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget)
    (hi : IsReduction B V.left.obj V.left.property _ Wred i) :
    Space.IsLocallyOfFiniteTypeULift.{u + 1} B V.left.obj V.left.property
      (terminal.from Wred.obj) := by
  let e := smallerBaseSheafOfIso B V.left.obj S V.left.property hS V.hom d.EW d.EWToTarget
  let Ψ := smallerBaseSheafFunctor B V.left.obj S V.left.property hS V.hom
  let CI := MorphismProperty.inverseImage (@IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B V.left.obj V.left.property)
  have hTh : MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B V.left.obj V.left.property) ≤ CI := fun _ _ _ hm ↦ hm.1
  have hiCI : CI.relative uliftYoneda.{u + 1} i.hom :=
    MorphismProperty.relative_monotone (F := uliftYoneda.{u + 1}) hTh _
      hi.isRepresentableThickening
  have hr := MorphismProperty.RespectsIso.postcomp _
    ((sheafToPresheaf _ _).mapIso e).hom _
    (relative_smallerBaseULiftMap B V.left.obj S V.left.property hS V.hom
      (@IsClosedImmersion.{u}) i.hom hiCI)
  have key := relative_locallyOfFiniteType_comp_completionSheafToAmbient B S hS
    (isAlgebraicSpace_yoneda B S hS V) d.Z d.isClosed_Z (equalizer.ι d.xhat₁ d.xhat₂)
    d.relative_locallyOfFiniteType_ι_EW (Ψ.map i ≫ e.hom)
    ((isAlgebraicSpaceULift_smallerBaseULift_iff B V.left.obj S V.left.property hS V.hom
      _).mpr hi.algebraic)
    (hasEtaleLocalPropertyULift_smallerBaseULift B V.left.obj S V.left.property hS V.hom _
      hi.reduced) hr
  refine isLocallyOfFiniteTypeULift_terminal_from_of_smallerBaseULiftHom B V.left.obj S
    V.left.property hS V.hom (Space.isLocallyOfFiniteTypeULift_of_relative B S hS _ ?_)
  have hstr : smallerBaseULiftHom B V.left.obj S V.left.property hS V.hom Wred.obj =
      (Ψ.map i ≫ e.hom).hom ≫ (equalizer.ι d.xhat₁ d.xhat₂).hom ≫
        Space.completionSheafToAmbient B S hS (yoneda.obj V)
          (isSheaf_comp_uliftFunctor B S hS (isAlgebraicSpace_yoneda B S hS V)) d.Z := by
    rw [← EWToTarget_hom]
    have h1 := smallerBaseSheafFunctor_map_comp_str B V.left.obj S V.left.property hS V.hom i
    rw [← smallerBaseSheafOfIso_hom_comp] at h1
    exact (congrArg (fun φ => φ.hom) h1).symm
  rwa [hstr]

/-- **Stacks 0GHD (4), as a construction.** The triple `E'`, `(E' ⟶ V)⁻¹ Z` and `E'_{/Z} ⟶ E_W`,
viewed over `V` through the change of base of Stacks 04SG, is a situation as in Stacks 0GH8 with
base scheme `V`, once `V` is locally Noetherian and `E'_{/Z} ⟶ E_W` is a formal modification over
`S`. The reduction of `E_W` viewed over `V` is locally of finite type over `V` by
`AlgebraicGeometry.Artin.ContractionEqualizer.isLocallyOfFiniteTypeULift_of_isReduction`. -/
def relocalizedSituation (hVN : IsLocallyNoetherian V.left.obj)
    (hmod : IsFormalModification B S hS d.completedToEW) :
    ContractionSituation B V.left.obj V.left.property :=
  ContractionSituation.ofSmallerBase B V.left.obj S V.left.property hS V.hom hVN d.E'OverV
    d.isAlgebraicSpace_eqz d.isLocallyOfFiniteType_toBase d.centerEqz d.isClosed_centerEqz d.EW
    d.EWToTarget d.completedToEW d.completedToEW_comp_EWToTarget hmod
    d.isLocallyOfFiniteTypeULift_of_isReduction

end AlgebraicGeometry.Artin.ContractionEqualizer

end
