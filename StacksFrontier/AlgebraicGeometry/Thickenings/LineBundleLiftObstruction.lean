module

public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardTorsionGeneral
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeFirstChernClass
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.Modules.ExtStructureSheafAbelian

/-!
# The obstruction to lifting a line bundle along an immersion

Let `i : X ⟶ X'` be an immersion of schemes over `q : X' ⟶ S`, with `X` smooth over `S`. The
conormal sequence

`0 ⟶ 𝒞_{X/X'} ⟶ i^*Ω_{X'/S} ⟶ Ω_{X/S} ⟶ 0`

is short exact ([Stacks, Tag 06AA]). Its class in `Ext¹(Ω_{X/S}, 𝒞_{X/X'})` is the
Kodaira–Spencer class of `X'`. This file proves: **if a line bundle `L` on `X` extends to
`X'`, then `c₁(L) ∪ KS = 0`**. Precisely, the Yoneda product of the Hodge first Chern class
`c₁(L) ∈ H¹(X, Ω_{X/S})` with the class of the conormal sequence, both read in the abelian
sheaves of `X`, vanishes in `H²(X, 𝒞_{X/X'})`.

This is the obstruction calculation of the proof of [Stacks, Tag 0D1R], specialised there to a
first-order deformation `X'` of a K3 surface. The proof follows the logarithmic
differential. `d log : 𝒪_{X'}^* ⟶ Ω_{X'/S}` composed with `Ω_{X'/S} ⟶ i_* i^*Ω_{X'/S}`
restricts, along the conormal sequence, to `d log` on `X`. So a class of `H¹(X, 𝒪_X^*)` coming
from `X'` has a `c₁` that lifts to `H¹(X, i^*Ω_{X'/S})`, and is killed by the connecting map.

## Main definitions

* `Stacks.Thickenings.LineBundleLift.extCohomologyOneIso`: first cohomology of abelian sheaves
  as right derived global sections is first cohomology as `Ext` out of the constant sheaf `ℤ`,
  naturally in the sheaf.
* `Stacks.Thickenings.LineBundleLift.unitsPullbackLift`: the transpose
  `i⁻¹𝒪_{X'}^* ⟶ 𝒪_X^*` of restriction of units.
* `Stacks.Thickenings.LineBundleLift.logDifferentialPullbackLift`: the transpose
  `i⁻¹𝒪_{X'}^* ⟶ i^*Ω_{X'/S}` of `d log` on `X'`.

## Main results

* `Stacks.Thickenings.LineBundleLift.logDifferentialPullbackLift_comp`: the transposed square
  `d log_{X'} ; (i^*Ω_{X'/S} ⟶ Ω_{X/S}) = (restriction of units) ; d log_X`.
* `Stacks.Thickenings.LineBundleLift.hodgeFirstChernClass_comp_extClass_eq_zero`: **a lifted line
  bundle has `c₁ ∪ KS = 0`**.

## References

* [Stacks Project, Tag 06AA](https://stacks.math.columbia.edu/tag/06AA)
* [Stacks Project, Tag 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.Abelian
open Stacks.Cohomology.Generators (unitsSheaf)
open Stacks.Cohomology.LerayLowDegree (abelianCohomology abelianEdgeMap abelianPushforward)
open Stacks.GlueSquishUnits (unitsPushforwardMap)
open Stacks.Picard (ofScheme schemePullbackClassHom)

universe u

namespace Stacks.Thickenings.LineBundleLift

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasExtAbelianSheaf

/-! ### Right derived first cohomology as `Ext` -/

section ExtComparison

variable (Y : TopCat.{u})

/-- **First cohomology as right derived global sections is `Ext¹(ℤ, -)`**, naturally in the
abelian sheaf. -/
def extCohomologyOneIso :
    abelianCohomology.{u, u} Y ⊤ 1 ≅
      CategoryTheory.Sheaf.functorH.{u, u, u, u} (Opens.grothendieckTopology Y) 1 :=
  ModuleSheafCohomology.rightDerivedIso (sectionsCoyonedaIso Y).symm 1 ≪≫
    ModuleSheafCohomology.rightDerivedCoyonedaSuccIso
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) 0

variable {Y}

/-- The comparison `extCohomologyOneIso` on elements. -/
abbrev toExt {F : TopCat.Sheaf AddCommGrpCat.{u} Y} (a : (abelianCohomology.{u, u} Y ⊤ 1).obj F) :
    CategoryTheory.Sheaf.H.{u} F 1 :=
  ((extCohomologyOneIso Y).hom.app F).hom a

/-- **Naturality of the comparison**: the map induced by `φ` on right derived cohomology is
composition with `φ` on `Ext`. -/
theorem toExt_map {F G : TopCat.Sheaf AddCommGrpCat.{u} Y} (φ : F ⟶ G)
    (a : (abelianCohomology.{u, u} Y ⊤ 1).obj F) :
    toExt (((abelianCohomology.{u, u} Y ⊤ 1).map φ).hom a) =
      (toExt a).comp (Ext.mk₀ φ) (add_zero 1) :=
  ConcreteCategory.congr_hom ((extCohomologyOneIso Y).hom.naturality φ) a

/-- The comparison is injective. -/
theorem toExt_injective {F : TopCat.Sheaf AddCommGrpCat.{u} Y} :
    Function.Injective (toExt (F := F)) :=
  ((extCohomologyOneIso Y).app F).addCommGroupIsoToAddEquiv.injective

end ExtComparison

/-! ### The transposed `d log` square -/

section Square

variable {X X' S : Scheme.{u}} (i : X ⟶ X') (q : X' ⟶ S)

/-- The adjunction `i⁻¹ ⊣ i_*` of abelian sheaves. -/
abbrev abelianAdj :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i.base

theorem comp_id_eq : i ≫ q = (i ≫ q) ≫ 𝟙 S := (Category.comp_id _).symm

/-- `d log` on `X'` followed by `Ω_{X'/S} ⟶ i_* i^*Ω_{X'/S}`, read in abelian sheaves. -/
def logDifferentialToPullback :
    unitsSheaf X'.toRingedSpace ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj
          ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials q))) :=
  Scheme.Hom.logarithmicDifferentialSheafHom q ≫
    (SheafOfModules.toSheaf X'.ringCatSheaf).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (Scheme.Hom.relativeDifferentials q))

/-- **The `d log` square on `X'`**: `d log_{X'}` followed by `i_*` of
`i^*Ω_{X'/S} ⟶ Ω_{X/S}` is restriction of units followed by `i_*(d log_X)`. -/
theorem logDifferentialToPullback_comp :
    logDifferentialToPullback i q ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map
            (Scheme.Hom.relativeDifferentialsMap i q (i ≫ q) (𝟙 S) (comp_id_eq i q))) =
      unitsPushforwardMap i ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map
          (Scheme.Hom.logarithmicDifferentialSheafHom (i ≫ q)) := by
  have h := Scheme.Hom.logarithmicDifferentialSheafHom_naturality i q (i ≫ q) (𝟙 S)
    (comp_id_eq i q)
  refine Eq.trans ?_ h.symm
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (Scheme.Hom.logarithmicDifferentialSheafHom q ≫ ·) ?_
  change _ = (SheafOfModules.toSheaf X'.ringCatSheaf).map
    ((Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv _ _
      (Scheme.Hom.relativeDifferentialsMap i q (i ≫ q) (𝟙 S) (comp_id_eq i q)))
  rw [Adjunction.homEquiv_unit]
  exact ((SheafOfModules.toSheaf X'.ringCatSheaf).map_comp
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
      (Scheme.Hom.relativeDifferentials q))
    ((Scheme.Modules.pushforward i).map
      (Scheme.Hom.relativeDifferentialsMap i q (i ≫ q) (𝟙 S) (comp_id_eq i q)))).symm

/-- The transpose `i⁻¹𝒪_{X'}^* ⟶ 𝒪_X^*` of restriction of units. -/
def unitsPullbackLift :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} i.base).obj (unitsSheaf X'.toRingedSpace) ⟶
      unitsSheaf X.toRingedSpace :=
  ((abelianAdj i).homEquiv _ _).symm (unitsPushforwardMap i)

/-- The transpose `i⁻¹𝒪_{X'}^* ⟶ i^*Ω_{X'/S}` of `logDifferentialToPullback`. -/
def logDifferentialPullbackLift :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} i.base).obj (unitsSheaf X'.toRingedSpace) ⟶
      (SheafOfModules.toSheaf X.ringCatSheaf).obj
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials q)) :=
  ((abelianAdj i).homEquiv _ _).symm (logDifferentialToPullback i q)

/-- **The transposed `d log` square on `X`.** -/
theorem logDifferentialPullbackLift_comp :
    logDifferentialPullbackLift i q ≫
        (SheafOfModules.toSheaf X.ringCatSheaf).map
          (Scheme.Hom.relativeDifferentialsMap i q (i ≫ q) (𝟙 S) (comp_id_eq i q)) =
      unitsPullbackLift i ≫ Scheme.Hom.logarithmicDifferentialSheafHom (i ≫ q) := by
  have e1 := (abelianAdj i).homEquiv_naturality_right_symm (logDifferentialToPullback i q)
    ((SheafOfModules.toSheaf X.ringCatSheaf).map
      (Scheme.Hom.relativeDifferentialsMap i q (i ≫ q) (𝟙 S) (comp_id_eq i q)))
  have e2 := (abelianAdj i).homEquiv_naturality_right_symm (unitsPushforwardMap i)
    (Scheme.Hom.logarithmicDifferentialSheafHom (i ≫ q))
  exact e1.symm.trans ((congrArg ((abelianAdj i).homEquiv _ _).symm
    (logDifferentialToPullback_comp i q)).trans e2)

end Square

/-! ### Lifted classes -/

section Lift

variable {X X' : Scheme.{u}} (i : X ⟶ X')

/-- **A Picard class pulled back from `X'` comes from `i⁻¹𝒪_{X'}^*`**: its class in
`H¹(X, 𝒪_X^*)` is the image of a class of `H¹(X, i⁻¹𝒪_{X'}^*)` under `unitsPullbackLift`. -/
theorem exists_h1Units_eq_map_unitsPullbackLift (c' : ofScheme X') :
    ∃ b : (abelianCohomology.{u, u} X ⊤ 1).obj
        ((TopCat.Sheaf.pullback AddCommGrpCat.{u} i.base).obj (unitsSheaf X'.toRingedSpace)),
      (Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X).symm
          (schemePullbackClassHom i c') =
        ((abelianCohomology.{u, u} X ⊤ 1).map (unitsPullbackLift i)).hom b := by
  let a := (Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard X').symm c'
  have hnat := Stacks.Picard.FirstCohomology.h1UnitsAddEquivPicard_naturality i a
  rw [AddEquiv.apply_symm_apply] at hnat
  refine ⟨((abelianEdgeMap.{u, u} i.base 1).app _).hom
    (((abelianCohomology.{u, u} X' ⊤ 1).map
      ((abelianAdj i).unit.app (unitsSheaf X'.toRingedSpace))).hom a), ?_⟩
  rw [← hnat, AddEquiv.symm_apply_apply]
  have hu : unitsPushforwardMap i =
      (abelianAdj i).unit.app (unitsSheaf X'.toRingedSpace) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map (unitsPullbackLift i) :=
    (Equiv.apply_symm_apply ((abelianAdj i).homEquiv _ _) (unitsPushforwardMap i)).symm.trans
      ((abelianAdj i).homEquiv_unit _ _ _)
  have hedge := ConcreteCategory.congr_hom
    ((abelianEdgeMap.{u, u} i.base 1).naturality (unitsPullbackLift i))
    (((abelianCohomology.{u, u} X' ⊤ 1).map
      ((abelianAdj i).unit.app (unitsSheaf X'.toRingedSpace))).hom a)
  have h1 : ((abelianCohomology.{u, u} X' ⊤ 1).map (unitsPushforwardMap i)).hom a =
      ((abelianCohomology.{u, u} X' ⊤ 1).map
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} i.base).map (unitsPullbackLift i))).hom
        (((abelianCohomology.{u, u} X' ⊤ 1).map
          ((abelianAdj i).unit.app (unitsSheaf X'.toRingedSpace))).hom a) :=
    (congrArg (fun φ => ((abelianCohomology.{u, u} X' ⊤ 1).map φ).hom a) hu).trans
      (ConcreteCategory.congr_hom ((abelianCohomology.{u, u} X' ⊤ 1).map_comp _ _) a)
  exact (congrArg ((abelianEdgeMap.{u, u} i.base 1).app _).hom h1).trans hedge

end Lift

/-! ### The obstruction -/

section Obstruction

variable {X X' S : Scheme.{u}} (i : X ⟶ X') [IsImmersion i] (q : X' ⟶ S)

/-- **A line bundle that extends along the immersion has `c₁ ∪ KS = 0`.** Let `i : X ⟶ X'` be an
immersion over `S` with `X` smooth over `S`, and let `c` be the pullback of a Picard class `c'`
of `X'`. The class `c₁(c) ∈ H¹(X, Ω_{X/S})` of the Hodge first Chern class, read as an `Ext`
class of abelian sheaves, has vanishing Yoneda product with the class of the conormal sequence
`0 ⟶ 𝒞_{X/X'} ⟶ i^*Ω_{X'/S} ⟶ Ω_{X/S} ⟶ 0`, read in abelian sheaves. -/
theorem hodgeFirstChernClass_comp_extClass_eq_zero (hsm : AlgebraicGeometry.Smooth (i ≫ q))
    (c' : ofScheme X') :
    (toExt (Scheme.Hom.hodgeFirstChernClass (i ≫ q) (schemePullbackClassHom i c'))).comp
      ((Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i q
        hsm).extClass.mapExactFunctor (Scheme.Modules.toAbelian X)) rfl = 0 := by
  obtain ⟨b, hb⟩ := exists_h1Units_eq_map_unitsPullbackLift i c'
  let ψ := unitsPullbackLift i
  let τ := logDifferentialPullbackLift i q
  let g := Scheme.Hom.relativeDifferentialsMap i q (i ≫ q) (𝟙 S) (comp_id_eq i q)
  have hsq : τ ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map g =
      ψ ≫ Scheme.Hom.logarithmicDifferentialSheafHom (i ≫ q) :=
    logDifferentialPullbackLift_comp i q
  have hc : Scheme.Hom.hodgeFirstChernClass (i ≫ q) (schemePullbackClassHom i c') =
      ((abelianCohomology.{u, u} X ⊤ 1).map
        (τ ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map g)).hom b := by
    refine Eq.trans ?_ (congrArg (fun φ => ((abelianCohomology.{u, u} X ⊤ 1).map φ).hom b)
      hsq).symm
    refine Eq.trans ?_ (ConcreteCategory.congr_hom
      ((abelianCohomology.{u, u} X ⊤ 1).map_comp _ _) b).symm
    exact congrArg ((abelianCohomology.{u, u} X ⊤ 1).map
      (Scheme.Hom.logarithmicDifferentialSheafHom (i ≫ q))).hom hb
  have hS := (Stacks.ConormalSequenceRight.conormalShortComplex_shortExact i q hsm)
  rw [Ext.mapExactFunctor_extClass, hc]
  have hmap : ((abelianCohomology.{u, u} X ⊤ 1).map
      (τ ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map g)).hom b =
      ((abelianCohomology.{u, u} X ⊤ 1).map ((SheafOfModules.toSheaf X.ringCatSheaf).map g)).hom
        (((abelianCohomology.{u, u} X ⊤ 1).map τ).hom b) :=
    ConcreteCategory.congr_hom ((abelianCohomology.{u, u} X ⊤ 1).map_comp _ _) b
  have h0 : (Ext.mk₀ ((SheafOfModules.toSheaf X.ringCatSheaf).map g)).comp
      (hS.map_of_exact (Scheme.Modules.toAbelian X)).extClass (zero_add 1) = 0 :=
    (hS.map_of_exact (Scheme.Modules.toAbelian X)).comp_extClass
  rw [hmap]
  refine (congrArg (fun z => z.comp (hS.map_of_exact (Scheme.Modules.toAbelian X)).extClass rfl)
    (toExt_map ((SheafOfModules.toSheaf X.ringCatSheaf).map g)
      (((abelianCohomology.{u, u} X ⊤ 1).map τ).hom b))).trans ?_
  refine (Ext.comp_assoc_of_second_deg_zero _ _ _ _).trans ?_
  exact (congrArg (fun z => (toExt (((abelianCohomology.{u, u} X ⊤ 1).map τ).hom b)).comp z rfl)
    h0).trans (Ext.comp_zero _ _ _ _ _)

end Obstruction

end Stacks.Thickenings.LineBundleLift

end
