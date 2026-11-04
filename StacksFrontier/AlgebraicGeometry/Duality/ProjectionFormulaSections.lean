module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAffineBase
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projection-formula morphism on local sections, and locality of its invertibility

Let `h : T ⟶ S` be a morphism of schemes, `G` a sheaf of `𝒪_T`-modules and `H` a sheaf of
`𝒪_S`-modules.  `Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaMap` is the
canonical morphism

`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)`,

the adjoint transpose of the pullback-tensor comparison of Stacks 01CD followed by the counit
of `h^* ⊣ h_*` in the first tensor factor.  Stacks Tag 0FZE asserts that it is invertible when
`h` is affine and `G` and `H` are quasi-coherent;
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAffineBase` proves that when `S` is in
addition affine.

This file supplies the two things that statement needs in order to be made local on `S`: a
*closed form for the morphism on local sections*, and the *locality of invertibility* itself.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.ProjectionFormula`.

* `projectionFormulaMap_unit_tmul`: on an open `W ⊆ S`, the projection-formula morphism carries
  the sheafification-unit image of a pure tensor `x ⊗ y`, with `x` a section of `G` over
  `h⁻¹W` and `y` a section of `H` over `W`, to the sheafification-unit image over `h⁻¹W` of
  `x ⊗ η y`, where `η` is the unit of `h^* ⊣ h_*`.  This is the canonicality clause of the
  projection formula: the morphism really is `x ⊗ y ↦ x ⊗ h^♯ y`.
* `projectionFormulaMap_unique`: that computation *determines* the projection-formula
  morphism.  Any morphism of the same type with the same effect on sections of the form
  `x ⊗ y` is `projectionFormulaMap`.
* `isIso_projectionFormulaMap_of_isOpenCover` and
  `isIso_projectionFormulaMap_of_isOpenCover_moduleRestriction`: invertibility of the
  projection-formula morphism is local on `S` — it suffices that the restriction to each
  member of an open covering be invertible — in the two restriction spellings the development
  uses.
* `isIso_projectionFormulaMap_of_restrict_affineOpens`: consequently Stacks 0FZE holds in
  general as soon as the restriction of the projection-formula morphism to every *affine*
  open of `S` is invertible, since the affine opens cover.
* `isAffineHom_morphismRestrict`: the restriction `h ∣_ V` of an affine morphism to an open of
  the target is affine.  This is the instance the affine-open step needs and it was not
  available: `IsAffineHom (h ∣_ V)` does not synthesize, and the route recorded elsewhere in
  the library for it does not typecheck (see the declaration's docstring).

## Implementation notes

The closed form is proved by reading `projectionFormulaMap_eq` on sections, identifying the
native projection map with the abstract adjunction tensor comparison. The adjoint-transpose
split of that comparison is definitional on sections, as `projectionFormulaMap_app_eq`
records. The proof then applies, in order, the canonicality
clause of Stacks 01CD (`Stacks.RingedSpace.comparison_homEquiv_unit_tmul`), the description of
the tensor of two morphisms on a pure tensor
(`Stacks.RingedSpace.tensorSheaf_map_unit_tmul`), and the triangle identity of `h^* ⊣ h_*` read
on sections (`counit_pullbackUnit`).  That last step is what makes the formula as simple as it
is: the counit undoes the unit on a section that came from `h_*G` in the first place, so no
trace of the comparison's adjoint detour survives.

The three rewrites are applied through `congrArg` and `Eq.trans` rather than by `rw`.  There
are two reasons: the element being rewritten sits in a type spelled
`(restrictScalars _ |>.obj (forget _ |>.obj M)).obj W` rather than `M.val.obj W` — the two are
definitionally equal, but `rw` builds a motive against the syntactic form and fails — and the
library states the same ringed space as `S.toRingedSpace` in one place and `S.toSheafedSpace`
in another, which likewise defeats syntactic matching while `exact`-style unification crosses
it without comment.

Locality of invertibility is `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`,
which is stated for `AlgebraicGeometry.Scheme.Modules` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.  No transport is needed to apply it to
`projectionFormulaMap`, whose type is written over
`structureSheafRing S.toRingedSpace`: that sheaf of rings *is*
`AlgebraicGeometry.Scheme.ringCatSheaf S` by `rfl`.  The second spelling, over the
ringed-space restriction functor `Stacks.Cohomology.HigherDirectImage.moduleRestriction`, is
obtained from the equality of the two restriction functors,
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`; it is
the spelling in which the restriction comparison for the pushforward,
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`, is available.

**What remains for Stacks 0FZE in general, after this file.**  Exactly one statement: that for
an affine open `V ⊆ S` the restriction to `V` of `projectionFormulaMap h G H` is invertible.
With `isIso_projectionFormulaMap_of_restrict_affineOpens` that *is* the tag, and with
`projectionFormulaMap_unique` it no longer requires any identification of adjoint transposes
or any mate calculus: it suffices to exhibit isomorphisms

* `(h_*G ⊗_{𝒪_S} H)|_V ≅ (h ∣_ V)_*(G|_{h⁻¹V}) ⊗_{𝒪_V} H|_V` and
* `h_*(G ⊗_{𝒪_T} h^*H)|_V ≅ (h ∣_ V)_*(G|_{h⁻¹V} ⊗_{𝒪_{h⁻¹V}} (h ∣_ V)^*(H|_V))`

and to check, on sections of the form `x ⊗ y`, that conjugating the restricted morphism by
them satisfies the formula of `projectionFormulaMap_unit_tmul` for `h ∣_ V`; the conjugate is
then `projectionFormulaMap (h ∣_ V)` by `projectionFormulaMap_unique`, which is invertible by
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_isAffine` because `V`
is affine and `h ∣_ V` is again affine by `isAffineHom_morphismRestrict`.

Every *isomorphism* that step needs is already in the library.  The three constituents are
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso` (restriction commutes with
the pushforward), `Stacks.AlgebraicGeometry.AffinePushforward.pullbackRestrictIso` (restriction
commutes with the inverse image), and — for the tensor half — Stacks 01CD for an open
immersion: `Stacks.RingedSpace.comparisonNatTrans_isIso` in this spelling, or
`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso` in the `Scheme.Modules` one, read
through `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, which identifies the
concrete restriction with the inverse image along the open immersion.

Nothing is missing: the statement is proved in
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal`, by
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap`, with no hypothesis on
the base.  Two of the three
isomorphisms *do* come with a description of their effect on sections —
`Stacks.RingedSpace.comparison_pullbackUnit_unit_tmul` and
`…modulePushforwardRestrictIso_hom_app_val_app`, the latter by `rfl` — and the route through
`Stacks.Cohomology.RelativeMayerVietoris` is unnecessary, since Mathlib's
`Scheme.Modules.restrictAdjunction_unit_app_app` already identifies the restriction unit with
the restriction map by `rfl`, and all four `Scheme.Modules`-versus-ringed-space spelling
crossings are `rfl`.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct
open scoped CategoryTheory.Prod

universe u

namespace Stacks.RingedSpace

open RingedSpaceModuleAdjunction _root_.PresheafOfModules

/-- The triangle identity of `f^* ⊣ f_*`, read on local sections: the counit at `F` undoes, on
sections over `f⁻¹U`, the unit at `f_*F` applied to a section of `F` over `f⁻¹U`.

This is `CategoryTheory.Adjunction.right_triangle_components` for
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction`; it is stated separately
because the sections of `f_*F` over `U` are the sections of `F` over `f⁻¹U`, so the two
occurrences of a single section below are at different opens. -/
lemma counit_pullbackUnit {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X)) (U : (Opens Y.carrier)ᵒᵖ)
    (x : ((modulePushforward f).obj F).val.obj U) :
    Hom.app ((modulePullbackPushforwardAdjunction f).counit.app F).val
        ((opensMap f).op.obj U) (pullbackUnit f ((modulePushforward f).obj F) U x) = x :=
  hom_congr_apply (congrArg (fun k => SheafOfModules.Hom.val k)
    ((modulePullbackPushforwardAdjunction f).right_triangle_components (Y := F))) U x

end Stacks.RingedSpace

namespace Stacks.AlgebraicGeometry.ProjectionFormula

open RingedSpaceModuleAdjunction Stacks.RingedSpace _root_.PresheafOfModules

variable {T S : Scheme.{u}} (h : T ⟶ S)
  (G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace))
  (H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))

/-! ### The projection-formula morphism on local sections -/

/-- The projection-formula morphism, split on local sections into the adjoint transpose of the
pullback-tensor comparison of Stacks 01CD followed by the tensor of the counit with the
identity. The existing `projectionFormulaMap_eq` supplies the functorial identity-coordinate
tensor law; the abstract adjunction comparison then splits definitionally on sections. -/
lemma projectionFormulaMap_app_eq (W : (Opens S.toRingedSpace.carrier)ᵒᵖ)
    (x : ((modulePushforward h.toLRSHom.toShHom).obj G).val.obj W) (y : H.val.obj W) :
    Hom.app (projectionFormulaMap h G H).val W
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (S.toRingedSpace).presheaf)
              (((modulePushforward h.toLRSHom.toShHom).obj G)).val (H).val)) W (x ⊗ₜ y)) =
      Hom.app (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((T.toRingedSpace)).presheaf, ((T.toRingedSpace)).IsSheaf⟩)).map
          ((((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).counit.app G),
            (𝟙 ((modulePullback h.toLRSHom.toShHom).obj H))) : (_, _) ⟶ (_, _)))).val
        ((opensMap h.toLRSHom.toShHom).op.obj W)
        (Hom.app ((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).homEquiv _ _
            (comparison h.toLRSHom.toShHom
              ((modulePushforward h.toLRSHom.toShHom).obj G) H)).val W
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (S.toRingedSpace).presheaf)
                (((modulePushforward h.toLRSHom.toShHom).obj G)).val (H).val)) W (x ⊗ₜ y))) :=
  hom_congr_apply (congrArg SheafOfModules.Hom.val (projectionFormulaMap_eq h G H)) W _

/-- **The projection-formula morphism on local sections.**  Let `W` be an open of `S`, `x` a
section of `G` over `h⁻¹W` — equivalently, of `h_*G` over `W` — and `y` a section of `H` over
`W`.  Then the projection-formula morphism
`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)` carries the sheafification-unit image of the pure
tensor `x ⊗ y` to the sheafification-unit image over `h⁻¹W` of the pure tensor of `x` with the
image of `y` under the unit of `h^* ⊣ h_*`.

This is the canonicality clause of Stacks 0FZE's morphism: it is `x ⊗ y ↦ x ⊗ h^♯y` and
nothing else, as `projectionFormulaMap_unique` records. -/
lemma projectionFormulaMap_unit_tmul (W : (Opens S.toRingedSpace.carrier)ᵒᵖ)
    (x : ((modulePushforward h.toLRSHom.toShHom).obj G).val.obj W) (y : H.val.obj W) :
    Hom.app (projectionFormulaMap h G H).val W
        (Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (S.toRingedSpace).presheaf)
              (((modulePushforward h.toLRSHom.toShHom).obj G)).val (H).val)) W (x ⊗ₜ y)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction
            (R := Stacks.RingedSpace.structureRingSheaf (T.toRingedSpace))
            (𝟙 (Stacks.RingedSpace.structureRingSheaf (T.toRingedSpace)).obj)).unit.app
          (PresheafOfModules.tensorObj (O := (T.toRingedSpace).presheaf)
            (G).val (((modulePullback h.toLRSHom.toShHom).obj H)).val))
        ((opensMap h.toLRSHom.toShHom).op.obj W)
        (x ⊗ₜ pullbackUnit h.toLRSHom.toShHom H W y) := by
  refine (projectionFormulaMap_app_eq h G H W x y).trans ?_
  refine (congrArg (Hom.app _ ((opensMap h.toLRSHom.toShHom).op.obj W))
    (comparison_homEquiv_unit_tmul h.toLRSHom.toShHom
      ((modulePushforward h.toLRSHom.toShHom).obj G) H W x y)).trans ?_
  refine (tensorSheaf_map_unit_tmul T.toRingedSpace
      ((modulePullbackPushforwardAdjunction h.toLRSHom.toShHom).counit.app G)
      (𝟙 ((modulePullback h.toLRSHom.toShHom).obj H))
      ((opensMap h.toLRSHom.toShHom).op.obj W)
      (pullbackUnit h.toLRSHom.toShHom ((modulePushforward h.toLRSHom.toShHom).obj G) W x)
      (pullbackUnit h.toLRSHom.toShHom H W y)).trans ?_
  exact congrArg (Hom.app _ ((opensMap h.toLRSHom.toShHom).op.obj W))
    (congrArg (· ⊗ₜ pullbackUnit h.toLRSHom.toShHom H W y)
      (counit_pullbackUnit h.toLRSHom.toShHom G W x))

/-- **The computation of `projectionFormulaMap_unit_tmul` determines the projection-formula
morphism.**  A morphism `h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)` which carries the
sheafification-unit image of every pure tensor `x ⊗ y` to the sheafification-unit image of
`x ⊗ η y` is `projectionFormulaMap h G H`.

The source is a sheafification of an objectwise tensor product, so a morphism out of it is
determined by its effect on sections of that shape. -/
lemma projectionFormulaMap_unique
    (θ : (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((S.toRingedSpace)).presheaf, ((S.toRingedSpace)).IsSheaf⟩).obj
          (((modulePushforward h.toLRSHom.toShHom).obj G))).obj (H)) ⟶
      (modulePushforward h.toLRSHom.toShHom).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((T.toRingedSpace)).presheaf, ((T.toRingedSpace)).IsSheaf⟩).obj (G)).obj
            (((modulePullback h.toLRSHom.toShHom).obj H)))))
    (hθ : ∀ (W : (Opens S.toRingedSpace.carrier)ᵒᵖ)
      (x : ((modulePushforward h.toLRSHom.toShHom).obj G).val.obj W) (y : H.val.obj W),
      Hom.app θ.val W
          (Hom.app ((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace))
                (𝟙 (Stacks.RingedSpace.structureRingSheaf (S.toRingedSpace)).obj)).unit.app
              (PresheafOfModules.tensorObj (O := (S.toRingedSpace).presheaf)
                (((modulePushforward h.toLRSHom.toShHom).obj G)).val (H).val)) W (x ⊗ₜ y)) =
        Hom.app ((PresheafOfModules.sheafificationAdjunction
              (R := Stacks.RingedSpace.structureRingSheaf (T.toRingedSpace))
              (𝟙 (Stacks.RingedSpace.structureRingSheaf (T.toRingedSpace)).obj)).unit.app
            (PresheafOfModules.tensorObj (O := (T.toRingedSpace).presheaf)
              (G).val (((modulePullback h.toLRSHom.toShHom).obj H)).val))
          ((opensMap h.toLRSHom.toShHom).op.obj W)
          (x ⊗ₜ pullbackUnit h.toLRSHom.toShHom H W y)) :
    θ = projectionFormulaMap h G H :=
  sheafification_hom_ext (tensorObj_hom_ext fun W x y ↦
    (hθ W x y).trans (projectionFormulaMap_unit_tmul h G H W x y).symm)

/-! ### Invertibility of the projection-formula morphism is local on the base -/

/-- **Invertibility of the projection-formula morphism is local on `S`.**  If the restriction
of `projectionFormulaMap h G H` to each member of an open covering of `S` is invertible, then
it is invertible.

No hypothesis on `h`, `G` or `H` is needed: this is the locality of invertibility of a
morphism of sheaves of modules on a scheme,
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict`, applied to it. -/
theorem isIso_projectionFormulaMap_of_isOpenCover {I : Type*} (V : I → S.Opens)
    (hV : IsOpenCover V)
    (hloc : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (V i).ι).map
      (projectionFormulaMap h G H))) :
    IsIso (projectionFormulaMap h G H) :=
  AffineBaseChange.isIso_of_isIso_restrict _ V hV hloc

/-- `isIso_projectionFormulaMap_of_isOpenCover` in the ringed-space restriction spelling, the
one in which the restriction comparison for the pushforward,
`Stacks.Cohomology.HigherDirectImage.modulePushforwardRestrictIso`, is stated.  The two
restriction functors are *equal*, by
`Stacks.AlgebraicGeometry.SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction`, so
nothing is transported. -/
theorem isIso_projectionFormulaMap_of_isOpenCover_moduleRestriction {I : Type*}
    (V : I → S.Opens) (hV : IsOpenCover V)
    (hloc : ∀ i, IsIso ((Stacks.Cohomology.HigherDirectImage.moduleRestriction
      S.toRingedSpace (V i)).map (projectionFormulaMap h G H))) :
    IsIso (projectionFormulaMap h G H) := by
  refine AffineBaseChange.isIso_of_isIso_restrict _ V hV fun i => ?_
  rw [SchemeHigherDirectImage.restrictFunctor_eq_moduleRestriction S (V i)]
  exact hloc i

/-- **Stacks 0FZE is a statement about affine opens of the base.**  If the restriction of
`projectionFormulaMap h G H` to every affine open of `S` is invertible, then it is invertible.

The affine opens of a scheme form a basis of its topology, hence cover it; the general case of
Stacks 0FZE is therefore exactly the affine-open case, which is where
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap_of_isAffine` applies. -/
theorem isIso_projectionFormulaMap_of_restrict_affineOpens
    (hloc : ∀ V : S.affineOpens, IsIso ((Scheme.Modules.restrictFunctor
      (V : S.Opens).ι).map (projectionFormulaMap h G H))) :
    IsIso (projectionFormulaMap h G H) :=
  isIso_projectionFormulaMap_of_isOpenCover h G H (fun V : S.affineOpens => (V : S.Opens))
    S.isBasis_affineOpens.isOpenCover hloc

/-- The restriction `h ∣_ V` of an affine morphism over an open of the target is affine.

Affineness of a morphism is stable under base change
(`AlgebraicGeometry.isAffineHom_isStableUnderBaseChange`) and `h ∣_ V` sits in the pullback
square of `AlgebraicGeometry.isPullback_morphismRestrict`.  This is registered as an instance
because it is *not* available otherwise: neither `IsAffineHom (h ∣_ V)` nor
`CategoryTheory.MorphismProperty.IsZariskiLocalAtTarget @IsAffineHom` synthesizes, so the
affine-open step that `isIso_projectionFormulaMap_of_restrict_affineOpens` leaves could not
even appeal to `isIso_projectionFormulaMap_of_isAffine` for the restricted morphism. -/
@[ega "II 1.6.2" "(iii), special case"]
instance isAffineHom_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (V : Y.Opens) : IsAffineHom (f ∣_ V) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict f V).flip inferInstance

end Stacks.AlgebraicGeometry.ProjectionFormula

end
