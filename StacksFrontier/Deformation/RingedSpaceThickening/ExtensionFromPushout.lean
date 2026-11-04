module

public import StacksFrontier.CategoryTheory.Sites.Modules.SquareZeroPushoutIdeal
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionClassTorsor
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionCommonRefinement
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentConormalRepresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Realizing every class of `Ext¹(𝖭𝖫_{X/S}, 𝒢)` by a square-zero extension

Let `f : (X, 𝒪_X) ⟶ (S, 𝒪_S)` be a morphism of ringed spaces and `𝒢` an `𝒪_X`-module. This file
proves the surjectivity half of **Stacks 0GPZ**: *every* class of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is
the class of a square-zero extension `0 ⟶ 𝒢 ⟶ 𝒪_{X'} ⟶ 𝒪_X ⟶ 0` of `f⁻¹𝒪_S`-algebras.

The construction is the source's. Fix a family of generators `α : ℰ ⟶ 𝒪_X` whose polynomial
presentation `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X` is surjective, write `𝒥` for its kernel, and let
`δ : 𝒥/𝒥² ⟶ 𝒢` be a homomorphism out of the conormal sheaf. The square-zero pushout

`𝒪_{X'} = (f⁻¹𝒪_S[ℰ] ⋉ 𝒢)/{(g, -δ(g)) : g ∈ 𝒥}`

of `StacksFrontier/CategoryTheory/Sites/Modules/SquareZeroPushout.lean` is then a square-zero
extension of `𝒪_X` by `𝒢`, with the identification of its ideal supplied by
`StacksFrontier/CategoryTheory/Sites/Modules/SquareZeroPushoutIdeal.lean`; it is an
`f⁻¹𝒪_S`-algebra through the coefficients of the polynomial algebra, and the variables of that
algebra are a lift `α' : ℰ ⟶ 𝒪_{X'}` of `α`. Its homomorphism `𝒥/𝒥² ⟶ 𝒢` is `δ` itself,
because the relation imposed by the pushout is exactly `(g, 0) = (0, δ(g))`, so its class is the
class of `δ`.

Combined with **Stacks 08UB** in the form
`AlgebraicGeometry.RingedSpaceThickening.exists_conormalRepresentative` — every class of
`Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` *is* the class of such a `δ`, over a family of generators produced
with it — this gives surjectivity, hence a base point for the torsor of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionClassTorsor.lean` and the realization of
a prescribed class as a difference cocycle, the only hypothesis of that torsor.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.conormalPushoutData`: a homomorphism out of the
  conormal sheaf of a presentation, read as the datum the square-zero pushout consumes.
* `AlgebraicGeometry.RingedSpaceThickening.extensionOfConormalHom`: **the square-zero extension
  attached to a conormal homomorphism.**
* `AlgebraicGeometry.RingedSpaceThickening.liftGenOfPushout` and `...presentedOfPushout`: the
  variables of the polynomial algebra as a lift of `α`, and the extension read as a presented
  extension over `α`.
* `AlgebraicGeometry.RingedSpaceThickening.realizeExtClassDiff`: **the realization the torsor
  needs** — for an extension and a class, an extension whose difference cocycle against
  the first is that class.

## Main results

* `AlgebraicGeometry.RingedSpaceThickening.presentedOfPushout_lift`: the map
  `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` of the presented extension is the inclusion into the pushout.
* `AlgebraicGeometry.RingedSpaceThickening.presentedOfPushout_conormalToIdeal`: **the
  homomorphism `𝒥/𝒥² ⟶ 𝒢` of the extension attached to `δ` is `δ`.**
* `AlgebraicGeometry.RingedSpaceThickening.extClass_extensionOfConormalHom`: **its class is the
  class of `δ`.**
* `AlgebraicGeometry.RingedSpaceThickening.exists_extension_extClass_eq`: **every class of
  `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is the class of a square-zero extension.**
* `AlgebraicGeometry.RingedSpaceThickening.nonempty_algebraSquareZeroExtension`: there is a
  square-zero extension of `𝒪_X` by `𝒢`.

## Implementation notes

The hypothesis carried throughout is surjectivity of the *polynomial presentation*
`f⁻¹𝒪_S[ℰ] ⟶ 𝒪_X`, not of the family of generators `α : ℰ ⟶ 𝒪_X`. That is what **Stacks 08UB**
produces, and it is all that `𝖭𝖫(α)` and the pushout need;
`AlgebraicGeometry.RingedSpaceThickening.AlgebraSquareZeroExtension.presentedBy_extClass` of
`StacksFrontier/Deformation/RingedSpaceThickening/ExtensionCommonRefinement.lean` is stated at that
weaker hypothesis for this reason.

`extensionOfConormalHom` is *not* built as a presented extension over `α` directly. It is built
as an `AlgebraSquareZeroExtension`, and then read over `α` by
`AlgebraSquareZeroExtension.presentedBy` with the variables of the polynomial algebra as the
lift; `presentedBy_extClass` then says that reading computes the extension's own class. Building
it the other way round would leave the extension's own presentation — the family of generators
underlying `𝒪_{X'}` — unrelated to `α`.

That the map `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` of the presented extension is the inclusion into the pushout
is not definitional: the presented extension's map is the one classified by its
`f⁻¹𝒪_S`-algebra structure and its lift, and the identification is
`Stacks.Sites.FreeAlgebra.freeAlgebraSheaf_hom_ext` — two morphisms out of a free algebra sheaf
agreeing on the coefficients and on the variables are equal.

Universes are written out on the `Stacks.Sites.SqZeroPushout` names. That namespace has a single
universe parameter, fixed by the site, and leaving it to be inferred from a sheaf of modules in
the *target* of a definition lets it default to `0` before unification runs; the failure then
reports a mismatch between `SheafOfModules.{u,u,u,u}` and `SheafOfModules.{0,0,0,0}` rather than
anything mathematical.

The scalars of `𝒢` appear in two definitionally equal spellings, and only one of them carries
the module instance; `Stacks.Sites.Conormal.presentationScalar` is the spelling used, and the
annihilation field of `conormalPushoutData` is proved through a family of statements over
`↥(G.val.obj U)` so that the `•` of the goal elaborates before the defeq with the restricted
`R`-action is checked.

## References

* [Stacks Project, Tag 0GPZ](https://stacks.math.columbia.edu/tag/0GPZ)
* [Stacks Project, Tag 08UC](https://stacks.math.columbia.edu/tag/08UC)
* [Stacks Project, Tag 08UB](https://stacks.math.columbia.edu/tag/08UB)
* [Stacks Project, Tag 0GQ0](https://stacks.math.columbia.edu/tag/0GQ0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open Stacks.Sites.SqZeroPushout
open Stacks.Sites.Conormal (IdealRestriction conormalSheaf conormalDesc
  conormalDesc_toAssociatedModule conormal_hom_ext kernelIdeal presentationScalar
  toAssociatedModule conormalPresheaf)
open Stacks.Sites.FreeAlgebra (underlyingPresheaf freeAlgebraSheaf
  freeAlgebraSheafCoefficientMap freeAlgebraSheafVariable freeAlgebraSheaf_hom_ext
  freeAlgebraSheafCoefficientMap_comp_desc freeAlgebraSheafVariable_comp_desc)
open Stacks.SheafOfModules.Tensor (ringSheaf)

universe u

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S : RingedSpace.{u, u}} {f : X ⟶ S}
  {G : SheafOfModules.{u} (ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)}
  {E : Functor (Opens X.carrier)ᵒᵖ (Type u)}
  {α : E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier) X.sheaf}
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E α).hom]
  (δ : conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier)
      (freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E)
      X.sheaf (generatorsPresentation f E α) ⟶ G)

/-- A homomorphism `δ : 𝒥/𝒥² ⟶ 𝒢` out of the conormal sheaf of a presentation, read as the datum
the square-zero pushout consumes. -/
def conormalPushoutData :
    PushoutData.{u} (generatorsPresentation f E α)
      (restrictAlong.{u} (generatorsPresentation f E α) G) where
  app U := (Stacks.Sites.Conormal.conormalRestriction.{u, u, u}
    (Opens.grothendieckTopology X.carrier) (generatorsPresentation f E α) G δ).app U
  app_smul U r g := (Stacks.Sites.Conormal.conormalRestriction.{u, u, u}
    (Opens.grothendieckTopology X.carrier) (generatorsPresentation f E α) G δ).app_smul U r g
  app_map {U V} i g := (Stacks.Sites.Conormal.conormalRestriction.{u, u, u}
    (Opens.grothendieckTopology X.carrier) (generatorsPresentation f E α) G δ).app_map i g
  smul_eq_zero U g m := by
    have h0 : presentationScalar (generatorsPresentation f E α) U
        (g : ↥((freeAlgebraSheaf (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing f) E).obj.obj U)) = 0 := g.2
    have key : ∀ n : ↥(G.val.obj U),
        presentationScalar (generatorsPresentation f E α) U
          (g : ↥((freeAlgebraSheaf (Opens.grothendieckTopology X.carrier)
            (inverseImageBaseRing f) E).obj.obj U)) • n = 0 := by
      intro n
      rw [h0, zero_smul]
    exact key m

/-- The map `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` onto the pushout: the inclusion `r ↦ [(r, 0)]`. -/
abbrev pushoutLift :
    freeAlgebraSheaf (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ⟶
      pushoutSheaf.{u} (generatorsPresentation f E α)
        (restrictAlong.{u} (generatorsPresentation f E α) G) (conormalPushoutData δ) :=
  pushoutInl.{u} (generatorsPresentation f E α)
    (restrictAlong.{u} (generatorsPresentation f E α) G) (conormalPushoutData δ)

/-- **The square-zero extension of `𝒪_X` by `𝒢` attached to a conormal homomorphism.** It is the
square-zero pushout `(f⁻¹𝒪_S[ℰ] ⋉ 𝒢)/J` of the presentation along `δ`, with `𝒢` included as the
kernel of its projection onto `𝒪_X`. -/
def extensionOfConormalHom : AlgebraSquareZeroExtension f G where
  sheaf := pushoutSheaf.{u} (generatorsPresentation f E α)
    (restrictAlong.{u} (generatorsPresentation f E α) G) (conormalPushoutData δ)
  base := freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) E ≫ pushoutLift δ
  reduction := pushoutProj.{u} (generatorsPresentation f E α)
    (restrictAlong.{u} (generatorsPresentation f E α) G) (conormalPushoutData δ)
  base_comp_reduction :=
    (Category.assoc _ _ _).trans
      ((congrArg (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.carrier)
            (inverseImageBaseRing f) E ≫ ·)
          (pushoutInl_comp_pushoutProj.{u} _ _ _)).trans
        (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
          (inverseImageBaseRing f) X.sheaf E (structureRingMap f) α))
  reduction_surjective := isLocallySurjective_pushoutProj.{u} _ _ _
  ideal := idealRestriction.{u} (generatorsPresentation f E α) G (conormalPushoutData δ)

/-- The lift of the family of generators to the extension attached to `δ`: the variables of the
polynomial presentation, read in the pushout. -/
abbrev liftGenOfPushout :
    E ⟶ underlyingPresheaf (Opens.grothendieckTopology X.carrier)
      (extensionOfConormalHom δ).sheaf :=
  freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) E ≫
    Functor.whiskerRight
      ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map
        (pushoutLift δ)) (forget CommRingCat.{u})

/-- The lift of the family of generators to the extension attached to `δ` is a lift of `α`. -/
theorem liftGenOfPushout_comp :
    liftGenOfPushout δ ≫ Functor.whiskerRight
      ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map
        (extensionOfConormalHom δ).reduction) (forget CommRingCat.{u}) = α := by
  refine ((Category.assoc _ _ _).trans ?_).trans
    (freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) X.sheaf E (structureRingMap f) α)
  refine congrArg (freeAlgebraSheafVariable (Opens.grothendieckTopology X.carrier)
    (inverseImageBaseRing f) E ≫ ·) ?_
  refine (Functor.whiskerRight_comp _ _ _).symm.trans ?_
  refine congrArg (fun t ↦ Functor.whiskerRight t (forget CommRingCat.{u})) ?_
  refine ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map_comp
    (pushoutLift δ) (extensionOfConormalHom δ).reduction).symm.trans ?_
  exact congrArg
    ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).map)
    (pushoutInl_comp_pushoutProj.{u} _ _ _)

/-- The extension attached to `δ`, read as a presented extension over the prescribed family of
generators. -/
abbrev presentedOfPushout : PresentedSquareZeroExtension f G E α :=
  (extensionOfConormalHom δ).presentedBy (liftGenOfPushout δ) (liftGenOfPushout_comp δ)

/-- **The map `f⁻¹𝒪_S[ℰ] ⟶ 𝒪_{X'}` of the presented extension attached to `δ` is the inclusion
into the pushout.** Both are morphisms out of a free algebra sheaf with the same restriction to
the coefficients and to the variables. -/
theorem presentedOfPushout_lift : (presentedOfPushout δ).lift = pushoutLift δ :=
  freeAlgebraSheaf_hom_ext (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f)
    (extensionOfConormalHom δ).sheaf E
    (freeAlgebraSheafCoefficientMap_comp_desc (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (extensionOfConormalHom δ).sheaf E
      (extensionOfConormalHom δ).base (liftGenOfPushout δ))
    (freeAlgebraSheafVariable_comp_desc (Opens.grothendieckTopology X.carrier)
      (inverseImageBaseRing f) (extensionOfConormalHom δ).sheaf E
      (extensionOfConormalHom δ).base (liftGenOfPushout δ))

/-- **The restriction datum of the presented extension attached to `δ` is `δ`**, read on local
relations: the inclusion of the free algebra carries a relation `g` to the image of `δ(g)` in the
pushout, and the identification of the ideal inverts that inclusion. -/
theorem presentedOfPushout_idealRestriction_app (U : (Opens X.carrier)ᵒᵖ)
    (g : ↥(kernelIdeal (generatorsPresentation f E α).hom U)) :
    (presentedOfPushout δ).idealRestriction.app U g =
      (Stacks.Sites.Conormal.conormalRestriction.{u, u, u}
        (Opens.grothendieckTopology X.carrier) (generatorsPresentation f E α) G δ).app U g :=
  (PresentedSquareZeroExtension.idealRestriction_app (presentedOfPushout δ) U g).trans
    (idealRestriction_app_eq_of_val.{u} (generatorsPresentation f E α) G
      (conormalPushoutData δ) U _ _
      ((congrArg (fun t ↦ (t.hom.app U).hom
            (g : ↥((freeAlgebraSheaf (Opens.grothendieckTopology X.carrier)
              (inverseImageBaseRing f) E).obj.obj U))) (presentedOfPushout_lift δ)).trans
        (pushoutInl_app_kernel.{u} (generatorsPresentation f E α)
          (restrictAlong.{u} (generatorsPresentation f E α) G) (conormalPushoutData δ) U g)))

/-- **The homomorphism `𝒥/𝒥² ⟶ 𝒢` of the presented extension attached to `δ` is `δ`.** A
morphism out of the conormal sheaf is determined by its values on the conormal classes of local
relations, and there both sides are `δ(g)`. -/
theorem presentedOfPushout_conormalToIdeal : (presentedOfPushout δ).conormalToIdeal = δ :=
  conormal_hom_ext.{u, u, u, u} (generatorsPresentation f E α) G fun U g ↦
    (conormalDesc_toAssociatedModule.{u, u, u, u} (generatorsPresentation f E α) G
      (presentedOfPushout δ).idealRestriction U g).trans
      (presentedOfPushout_idealRestriction_app δ U g)

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **The class of the extension attached to `δ` is the class of `δ`**, transported to
`𝖭𝖫_{X/S}`. -/
theorem extClass_extensionOfConormalHom :
    (extensionOfConormalHom δ).toPresented.extClass =
      (PresentedSquareZeroExtension.naiveCotangentIso f E α).inv ≫
        (PresentedSquareZeroExtension.twoTerm f E α).conormalExtClass G δ :=
  (AlgebraSquareZeroExtension.presentedBy_extClass (extensionOfConormalHom δ)
      (liftGenOfPushout δ) (liftGenOfPushout_comp δ)).symm.trans
    (congrArg
      (fun t ↦ (PresentedSquareZeroExtension.naiveCotangentIso f E α).inv ≫
        (PresentedSquareZeroExtension.twoTerm f E α).conormalExtClass G t)
      (presentedOfPushout_conormalToIdeal δ))

/-! ### Surjectivity of the class, and the realization the torsor needs -/

/-- **Every class of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)` is the class of a square-zero extension of
`f⁻¹𝒪_S`-algebras.** By **Stacks 08UB** the class is the class of a homomorphism `δ : 𝒥/𝒥² ⟶ 𝒢`
out of the conormal sheaf of some surjective polynomial presentation, and the square-zero
pushout of that presentation along `δ` is an extension carrying exactly that class.

This is the surjectivity half of **Stacks 0GPZ**. -/
theorem exists_extension_extClass_eq
    (ζ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    ∃ P : AlgebraSquareZeroExtension f G, P.toPresented.extClass = ζ := by
  obtain ⟨E', α', hsurj, δ', hδ'⟩ := exists_conormalRepresentative (f := f) (G := G) ζ
  let : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier)
    (generatorsPresentation f E' α').hom := hsurj
  exact ⟨extensionOfConormalHom δ', (extClass_extensionOfConormalHom δ').trans hδ'⟩

/-- **There is a square-zero extension of `𝒪_X` by `𝒢` as `f⁻¹𝒪_S`-algebras**, namely one
carrying the zero class. This is the base point the torsor of **Stacks 08UC** needs. -/
instance nonempty_algebraSquareZeroExtension : Nonempty (AlgebraSquareZeroExtension f G) :=
  ⟨(exists_extension_extClass_eq (f := f) (G := G) 0).choose⟩

/-- **The realization the torsor needs**: for a square-zero extension `𝒪_{X'}` and a
class `ξ` of `Ext¹_{𝒪_X}(𝖭𝖫_{X/S}, 𝒢)`, a square-zero extension whose difference cocycle against
`𝒪_{X'}` is `ξ`. It is an extension carrying the class `[𝒪_{X'}] - ξ`, which exists by
`exists_extension_extClass_eq`.

This discharges the hypothesis `realize` of
`AlgebraicGeometry.RingedSpaceThickening.extClassObstruction` — the pushout construction of the
proof of **Stacks 08UC**. -/
def realizeExtClassDiff (P : AlgebraSquareZeroExtension f G)
    (ξ : PresentedSquareZeroExtension.relativeObj f ⟶
      PresentedSquareZeroExtension.shiftedSingleObj G) :
    { P' : AlgebraSquareZeroExtension f G // extClassDiff P P' = ξ } := by
  refine ⟨(exists_extension_extClass_eq (P.toPresented.extClass - ξ)).choose, ?_⟩
  change P.toPresented.extClass -
    ((exists_extension_extClass_eq (P.toPresented.extClass - ξ)).choose).toPresented.extClass = ξ
  rw [(exists_extension_extClass_eq (P.toPresented.extClass - ξ)).choose_spec, sub_sub_cancel]

end Derived

end AlgebraicGeometry.RingedSpaceThickening

end
