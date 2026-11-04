module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentBaseChangeConormalStalk
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SquareBaseRingComparison

/-!
# The pullback of the polynomial presentation of `𝒪_X` along a square of immersions

Let `i : X ⟶ P`, `i' : X' ⟶ P'` be immersions, `h : P ⟶ Y`, `h' : P' ⟶ Y'` morphisms of
schemes, and `i' ≫ p = g' ≫ i`, `g' ≫ (i ≫ h) = (i' ≫ h') ≫ g` commutative squares.  Write
`R = i⁻¹h⁻¹𝒪_Y`, `A = i⁻¹𝒪_P` and `R[A] ⟶ 𝒪_X` for the polynomial presentation of `𝒪_X` on the
sections of `A`, and similarly `R'[A'] ⟶ 𝒪_{X'}`.  The naive cotangent complexes `NL(R[A])` and
`NL(R'[A'])` of these presentations compute `NL_{X/Y}` and `NL_{X'/Y'}`
([Stacks Project, Tag 08TL]); the proof of [Stacks Project, Tag 0FV9] needs to know the map
induced on `H^{-1}` by the base change map `(g')^*NL_{X/Y} ⟶ NL_{X'/Y'}` of
[Stacks Project, Tag 0FV5] in terms of these presentations.

This file constructs the morphism of presentations relating them and the map it induces on the
pulled-back complexes.  The square gives morphisms of sheaves of rings
`g'⁻¹R ⟶ R'` (`baseRingTowerComparison`) and `g'⁻¹A ⟶ A'` (`middleRingComparison`), hence a
morphism `g'⁻¹(R[A]) ⟶ R'[A']` over `g'⁻¹𝒪_X ⟶ 𝒪_{X'}` (`presentationRingComparison`), which
sends the variable `[s]` to `[s']` for `s'` the image of `s`.  Together with the inverse image
of conormal sheaves along `g'` this induces maps
`g'^*(I/I²) ⟶ I'/I'²` and `g'^*(𝒪_X ⊗ Ω_{R[A]/R}) ⟶ 𝒪_{X'} ⊗ Ω_{R'[A']/R'}` out of the two-step
model of the pullback, which commute with the differentials.

By `homologyMap_inv_homologyNegOneι_eq_of_degreewise`, a map of the degree `-1` terms which is
compatible with the differentials computes the map induced on `H^{-1}` by a morphism of complexes
through the inverse of an isomorphism on `H^{-1}`.  Applied to `pulledPresentationNegOne`, this
reduces the comparison of `H^{-1}` of the base change map with the map of conormal sheaves of
[Stacks Project, Tag 01R4] (`Stacks.NaiveCotangentPulledImmersion.homologyMap_negOne_comp_eq_iff`)
to two identities of maps out of the degree `-1` term of `(g')^*NL(R[A])`, which are identities
of maps of sheaves and are checked on conormal classes of local sections.  The comparison of
[Stacks Project, Tag 08TL] on such classes is `presentationComparison_conormalClassX`.

## Main definitions

* `Stacks.NaiveCotangentPulledImmersion.twoStepCompAdjunction`: the two-step pullback as the
  left adjoint of a composite of a restriction of scalars and a direct image, with an explicit
  unit.
* `Stacks.NaiveCotangentPulledImmersion.pulledConormalSheafMap` and
  `Stacks.NaiveCotangentPulledImmersion.pulledTensorSheafMap`: the maps
  `g'^*(I₁/I₁²) ⟶ I₂/I₂²` and `g'^*(𝒪_X ⊗ Ω_{A₁/R₁}) ⟶ 𝒪_{X'} ⊗ Ω_{A₂/R₂}` induced by a morphism
  of presentations `g'⁻¹A₁ ⟶ A₂` over the structure map of `g'`.
* `Stacks.NaiveCotangentPulledImmersion.presentationRingComparison`: the morphism of polynomial
  presentations attached to the square.
* `Stacks.NaiveCotangentPulledImmersion.conormalClassX`: a conormal class read in the degree
  `-1` term of a complex identified with the conormal sheaf.
* `Stacks.NaiveCotangentPulledImmersion.pulledPresentationNegOne` and
  `Stacks.NaiveCotangentPulledImmersion.pulledPresentationZero`: the induced maps of the
  degree `-1` and degree `0` terms of the pulled-back complex `(g')^*NL(R[A])` to those of
  `NL(R'[A'])`.

## Main results

* `Stacks.NaiveCotangentPulledImmersion.pulledConormalSheafMap_unit_conormalClass`: the pulled
  conormal map on the unit image of a conormal class.
* `Stacks.NaiveCotangentPulledImmersion.pulledConormalSheafMap_comp_conormalSequence_f`: the two
  pulled maps commute with the first arrows of the conormal sequences.
* `Stacks.NaiveCotangentPulledImmersion.presentationRingComparison_comp`: the morphism of
  presentations lies over the structure map of `g'`.
* `Stacks.NaiveCotangentPulledImmersion.pulledPresentationNegOne_comp_d`: the degree `-1` and
  degree `0` maps commute with the differentials.
* `Stacks.NaiveCotangentPulledImmersion.presentationComparison_conormalClassX`: the comparison
  of [Stacks Project, Tag 08TL] on conormal classes.
* `Stacks.NaiveCotangentPulledImmersion.homologyMap_inv_homologyNegOneι_eq_of_degreewise`: a map
  out of `H^{-1}` through the inverse of an isomorphism on `H^{-1}` is computed by any map of
  degree `-1` terms compatible with the differentials and with the two morphisms.

## Implementation notes

The two-step pullback `RingedSpaceModuleAdjunction.twoStepPullback` is the inverse image of
sheaves of modules followed by extension of scalars along `g'⁻¹𝒪_X ⟶ 𝒪_{X'}`.  Its adjunction
`RingedSpaceModuleAdjunction.twoStepPullbackAdjunction` is built by rewriting its right adjoint,
so its unit is behind a transport; `twoStepCompAdjunction` is the composite of the two
adjunctions, whose unit is explicit on sections (`twoStepCompAdjunction_unit_val_app`), and all
maps out of the two-step pullback here are constructed and computed through it.

Goals mixing the `TopCat.Sheaf` and `CategoryTheory.Sheaf` spellings of sheaves of rings on a
space are not type-correct at the transparency `rw` builds its motives at, so the categorical
bookkeeping is done in bare categories (`map_inv_comp_comp_eq`, `coeff_comp_eq_of_parts`,
`var_comp_eq_of_parts`, `comm_of_eqToHom_map`) and applied with `exact`.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
* [Stacks Project, Tag 0FV5](https://stacks.math.columbia.edu/tag/0FV5)
* [Stacks Project, Tag 08TL](https://stacks.math.columbia.edu/tag/08TL)
* [Stacks Project, Tag 08TM](https://stacks.math.columbia.edu/tag/08TM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction
open TopologicalSpace Opposite Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open AlgebraicGeometry.SheafOfModules (inverseImageRingHom)
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf structureSheafMap
  homEquiv_inverseImageStructureMap)

universe u

noncomputable section

namespace Stacks.NaiveCotangentPulledImmersion


section Transpose

variable {X X' : RingedSpace.{u, u}} (g' : X' ⟶ X)

/-- The two-step model of the pullback is left adjoint to restriction of scalars along
`g'⁻¹𝒪_X ⟶ 𝒪_{X'}` followed by the direct image along `𝒪_X ⟶ g'_*g'⁻¹𝒪_X`. -/
def twoStepCompAdjunction :=
  (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (inverseImageRingHom g'.hom.base X.sheaf)).comp
    (Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
      (Opens.grothendieckTopology X'.carrier) (inverseImageMiddleRing g') X'.sheaf
      (ringedSpaceStructureMap g'))

variable (M : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf))
    (N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X'.carrier) X'.sheaf))

/-- The transpose under `twoStepCompAdjunction` of `z` sends a section `x` of `M` over `U` to
`z` applied to the image of `x` under the unit. -/
theorem twoStepCompAdjunction_homEquiv_val_app (z : (twoStepPullback g').obj M ⟶ N)
    (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) :
    ((twoStepCompAdjunction g').homEquiv M N z).val.app U x =
      z.val.app ((Opens.map g'.hom.base).op.obj U)
        (((twoStepCompAdjunction g').unit.app M).val.app U x) :=
  congrArg (fun t => t.val.app U x) ((twoStepCompAdjunction g').homEquiv_unit M N z)

/-- On sections, the unit of `twoStepCompAdjunction` is the unit of the inverse image of
sheaves of modules followed by the unit of extension of scalars along `g'⁻¹𝒪_X ⟶ 𝒪_{X'}`. -/
theorem twoStepCompAdjunction_unit_val_app (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) :
    ((twoStepCompAdjunction g').unit.app M).val.app U x =
      ((Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
        (Opens.grothendieckTopology X'.carrier) (inverseImageMiddleRing g') X'.sheaf
        (ringedSpaceStructureMap g')).unit.app
          ((_root_.SheafOfModules.pullback.{u} (inverseImageRingHom g'.hom.base X.sheaf)).obj
            M)).val.app ((Opens.map g'.hom.base).op.obj U)
        (((_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
          (inverseImageRingHom g'.hom.base X.sheaf)).unit.app M).val.app U x) :=
  congrArg (fun t => t.val.app U x) (Adjunction.comp_unit_app
    (_root_.SheafOfModules.pullbackPushforwardAdjunction.{u}
      (inverseImageRingHom g'.hom.base X.sheaf))
    (Stacks.SheafOfModules.towerExtendRestrictAdjunction.{u, u, u}
      (Opens.grothendieckTopology X'.carrier) (inverseImageMiddleRing g') X'.sheaf
      (ringedSpaceStructureMap g')) M)

/-- Naturality of the unit of `twoStepCompAdjunction` on sections: the two-step pullback of
`v : M ⟶ M'` carries the unit image of `x` to the unit image of `v x`. -/
theorem twoStepPullback_map_unit_val_app
    {M M' : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)} (v : M ⟶ M')
    (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) :
    ((twoStepPullback g').map v).val.app ((Opens.map g'.hom.base).op.obj U)
        (((twoStepCompAdjunction g').unit.app M).val.app U x) =
      ((twoStepCompAdjunction g').unit.app M').val.app U (v.val.app U x) := by
  have := congrArg (fun t => t.val.app U x) ((twoStepCompAdjunction g').unit.naturality v)
  exact this.symm

end Transpose




section PulledPresentation

variable {X X' : RingedSpace.{u, u}} (g' : X' ⟶ X)

/-- The inverse image of a locally surjective morphism of sheaves of commutative rings is
locally surjective: on stalks it is the original morphism at the image point. -/
theorem isLocallySurjective_pullback_map {T T' : TopCat.{u}} (f : T' ⟶ T)
    {F G : TopCat.Sheaf CommRingCat.{u} T} (α : F ⟶ G)
    [hα : Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) α.hom] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology T')
      ((TopCat.Sheaf.pullback CommRingCat.{u} f).map α).hom := by
  have hα' := (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks α.hom).1 hα
  refine (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).2 fun x => ?_
  have e := AlgebraicGeometry.BaseChangeStalk.stalkSheafPullbackIso_hom_naturality
    CommRingCat.{u} f α x
  intro t
  obtain ⟨s, hs⟩ := hα' (f x)
    ((Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f G x).hom t)
  refine ⟨(Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f F x).inv s, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso
    (Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f G x).hom).1
  have := congrArg (fun φ => φ.hom
    ((Stacks.SheafifyStalk.stalkSheafPullbackIso CommRingCat.{u} f F x).inv s)) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, ← CommRingCat.comp_apply,
    Iso.inv_hom_id, CommRingCat.id_apply] at this
  refine this.trans (Eq.trans ?_ hs)
  exact congrArg _ (Iso.inv_hom_id_apply _ s)

variable {A₁ : TopCat.Sheaf CommRingCat.{u} X.carrier} (π₁ : A₁ ⟶ X.sheaf)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.carrier) π₁.hom]
  {A₂ : TopCat.Sheaf CommRingCat.{u} X'.carrier} (π₂ : A₂ ⟶ X'.sheaf)
  [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X'.carrier) π₂.hom]
  (ψ : (TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj A₁ ⟶ A₂)
  (hψ : ψ ≫ π₂ =
    (TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map π₁ ≫ ringedSpaceStructureMap g')

/-- The inverse image along `g'` of the locally surjective presentation `π₁` is locally
surjective. -/
instance isLocallySurjective_pullback_map_presentation :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X'.carrier)
      ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map π₁).hom :=
  isLocallySurjective_pullback_map g'.hom.base π₁

/-- The unit `A₁ ⟶ g'_*g'⁻¹A₁` is compatible with the presentation `π₁` and its inverse
image. -/
theorem unit_comp_pushforward_pullback_map :
    (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.app A₁ ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g'.hom.base).map
          ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map π₁) =
      π₁ ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.app
        X.sheaf :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.naturality
    π₁).symm

include hψ in
/-- **The pullback of the conormal sheaf of a presentation, in transposed form.**  For
presentations `π₁ : A₁ ⟶ 𝒪_X` and `π₂ : A₂ ⟶ 𝒪_{X'}` and a morphism `ψ : g'⁻¹A₁ ⟶ A₂` over
the structure map of `g'`, the map `I₁/I₁² ⟶ g'_*(I₂/I₂²)` sending the conormal class of a
section `s` of `I₁` to the conormal class of `ψ` applied to the inverse-image section of `s`. -/
def pulledConormalSheafMapTranspose :=
  conormalSheafMapAlong g'.hom.base X.sheaf π₁
      ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map π₁)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.app A₁)
      (unit_comp_pushforward_pullback_map g' π₁) ≫
    (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom g'.hom.base X.sheaf)).map
      (conormalSheafMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X'.carrier)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj A₁) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj X.sheaf) X'.sheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map π₁) π₂ ψ
        (ringedSpaceStructureMap g') hψ)

include hψ in
/-- **The pullback of the conormal sheaf of a presentation.**  The map
`g'^*(I₁/I₁²) ⟶ I₂/I₂²` of sheaves of `𝒪_{X'}`-modules, out of the two-step model of the
pullback, transposing `pulledConormalSheafMapTranspose`. -/
def pulledConormalSheafMap :
    (twoStepPullback g').obj
        (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier) A₁ X.sheaf π₁) ⟶
      conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X'.carrier) A₂ X'.sheaf π₂ :=
  ((twoStepCompAdjunction g').homEquiv _ _).symm
    (pulledConormalSheafMapTranspose g' π₁ π₂ ψ hψ)

variable (R₁ : TopCat.Sheaf CommRingCat.{u} X.carrier) (a₁ : R₁ ⟶ A₁)

/-- **The pulled conormal map on unit sections.**  It carries the image under the unit of the
two-step pullback of the conormal class of a section `s` of `I₁` to the conormal class of `ψ`
applied to the inverse-image section of `s`. -/
theorem pulledConormalSheafMap_unit_conormalClass (R₂ : TopCat.Sheaf CommRingCat.{u} X'.carrier)
    (a₂ : R₂ ⟶ A₂) (U : (Opens X.carrier)ᵒᵖ) (t : kernelIdeal π₁.hom U) :
    (pulledConormalSheafMap g' π₁ π₂ ψ hψ).val.app ((Opens.map g'.hom.base).op.obj U)
        (((twoStepCompAdjunction g').unit.app _).val.app U
          (conormalClass.{u, u, u, u} (Opens.grothendieckTopology X.carrier) R₁ A₁ X.sheaf a₁
            π₁ U t)) =
      conormalClass.{u, u, u, u} (Opens.grothendieckTopology X'.carrier) R₂ A₂ X'.sheaf a₂ π₂
        ((Opens.map g'.hom.base).op.obj U)
        ⟨ψ.hom.app _ ((sectionsMapAlong g'.hom.base
            ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.app
              A₁) U).hom t.1),
          kernelIdeal_le_comap_square _ _ ψ.hom _ (hom_of_square hψ) _
            (kernelIdeal_le_comap_sectionsMapAlong g'.hom.base X.sheaf π₁ _ _
              (unit_comp_pushforward_pullback_map g' π₁) U t.2)⟩ := by
  refine (twoStepCompAdjunction_homEquiv_val_app g' _ _ _ U _).symm.trans ?_
  refine (congrArg (fun z => z.val.app U (conormalClass.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) R₁ A₁ X.sheaf a₁ π₁ U t))
    (((twoStepCompAdjunction g').homEquiv
      (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier) A₁ X.sheaf π₁)
      (conormalSheaf.{u, u, u, u} (Opens.grothendieckTopology X'.carrier) A₂ X'.sheaf π₂)
      ).apply_symm_apply (pulledConormalSheafMapTranspose g' π₁ π₂ ψ hψ))).trans ?_
  refine congrArg (((conormalSheafMapOfSquare.{u, u, u, u}
    (Opens.grothendieckTopology X'.carrier) _ A₂ _ X'.sheaf _ π₂ ψ
    (ringedSpaceStructureMap g') hψ).val.app ((Opens.map g'.hom.base).op.obj U)))
    (conormalSheafMapAlong_conormalClass g'.hom.base X.sheaf π₁ _ _
      (unit_comp_pushforward_pullback_map g' π₁) R₁ a₁
      ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map a₁) U t) |>.trans ?_
  exact conormalSheafMapOfSquare_conormalClass.{u, u, u, u} _ _ R₂ _ A₂ _ X'.sheaf _ a₂ _ π₂ ψ
    _ hψ _ _

variable (R₂ : TopCat.Sheaf CommRingCat.{u} X'.carrier) (a₂ : R₂ ⟶ A₂)
  (ρ : (TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj R₁ ⟶ R₂)
  (hρ : ρ ≫ a₂ = (TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map a₁ ≫ ψ)

/-- The unit `R₁ ⟶ g'_*g'⁻¹R₁` is compatible with `a₁` and its inverse image. -/
theorem unit_comp_pushforward_pullback_map_base :
    a₁ ≫ (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.app A₁ =
      (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.app R₁ ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g'.hom.base).map
          ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map a₁) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.naturality a₁

include hψ hρ in
/-- **The pullback of the scalar extension of the differentials of a presentation, in
transposed form**: the map `𝒪_X ⊗[A₁] Ω[A₁/R₁] ⟶ g'_*(𝒪_{X'} ⊗[A₂] Ω[A₂/R₂])` sending
`1 ⊗ d s` to `1 ⊗ d (ψ s)`. -/
def pulledTensorSheafMapTranspose :=
  tensorSheafMapAlong g'.hom.base X.sheaf π₁
      ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map π₁)
      ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.app A₁)
      (unit_comp_pushforward_pullback_map g' π₁) R₁ a₁
      ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map a₁)
      (unit_comp_pushforward_pullback_map_base g' R₁ a₁) ≫
    (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom g'.hom.base X.sheaf)).map
      (tensorSheafMapOfSquare.{u, u, u, u} (Opens.grothendieckTopology X'.carrier)
        ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj R₁) R₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj A₁) A₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj X.sheaf) X'.sheaf
        ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map a₁) a₂
        ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map π₁) π₂ ψ
        (ringedSpaceStructureMap g') ρ hψ hρ)

include hψ hρ in
/-- **The pullback of the scalar extension of the differentials of a presentation**, out of
the two-step model of the pullback. -/
def pulledTensorSheafMap :
    (twoStepPullback g').obj
        (tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X.carrier) R₁ A₁
          X.sheaf a₁ π₁) ⟶
      tensorDifferentialsSheaf.{u, u, u, u} (Opens.grothendieckTopology X'.carrier) R₂ A₂
        X'.sheaf a₂ π₂ :=
  ((twoStepCompAdjunction g').homEquiv _ _).symm
    (pulledTensorSheafMapTranspose g' π₁ π₂ ψ hψ R₁ a₁ R₂ a₂ ρ hρ)

include hψ hρ in
/-- **The pulled conormal and tensor maps commute with the first arrows of the two conormal
sequences.** -/
theorem pulledConormalSheafMap_comp_conormalSequence_f :
    pulledConormalSheafMap g' π₁ π₂ ψ hψ ≫
        (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology X'.carrier) R₂ A₂ X'.sheaf
          a₂ π₂).f =
      (twoStepPullback g').map
          (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology X.carrier) R₁ A₁ X.sheaf
            a₁ π₁).f ≫
        pulledTensorSheafMap g' π₁ π₂ ψ hψ R₁ a₁ R₂ a₂ ρ hρ := by
  apply ((twoStepCompAdjunction g').homEquiv _ _).injective
  refine ((twoStepCompAdjunction g').homEquiv_naturality_right _ _).trans ?_
  refine Eq.trans ?_ ((twoStepCompAdjunction g').homEquiv_naturality_left _ _).symm
  refine (congrArg (fun z => z ≫ _)
    (((twoStepCompAdjunction g').homEquiv _ _).apply_symm_apply _)).trans ?_
  refine Eq.trans ?_ (congrArg (fun z => _ ≫ z)
    (((twoStepCompAdjunction g').homEquiv _ _).apply_symm_apply _)).symm
  dsimp only [pulledConormalSheafMapTranspose, pulledTensorSheafMapTranspose]
  have h₁ := conormalSequence_f_naturality_along g'.hom.base X.sheaf π₁
    ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map π₁)
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.hom.base).unit.app A₁)
    (unit_comp_pushforward_pullback_map g' π₁) R₁ a₁
    ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map a₁)
    (unit_comp_pushforward_pullback_map_base g' R₁ a₁)
  have h₂ := conormalSequence_f_naturality_square.{u, u, u, u}
    (Opens.grothendieckTopology X'.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj R₁) R₂
    ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj A₁) A₂
    ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).obj X.sheaf) X'.sheaf
    ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map a₁) a₂
    ((TopCat.Sheaf.pullback CommRingCat.{u} g'.hom.base).map π₁) π₂ ψ
    (ringedSpaceStructureMap g') ρ hψ hρ
  refine Eq.symm ?_
  refine (Category.assoc (obj := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)) _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ _) h₁).trans ?_
  refine (Category.assoc (obj := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)) _ _ _).trans ?_
  refine (congrArg (fun z => _ ≫ z)
    ((_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom g'.hom.base X.sheaf)).map_comp
      _ _).symm).trans ?_
  refine (congrArg (fun z => _ ≫
    (_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom g'.hom.base X.sheaf)).map z)
    h₂).trans ?_
  refine (congrArg (fun z => _ ≫ z)
    ((_root_.SheafOfModules.pushforward.{u} (inverseImageRingHom g'.hom.base X.sheaf)).map_comp
      _ _)).trans ?_
  exact (Category.assoc (obj := _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (J := Opens.grothendieckTopology X.carrier) X.sheaf)) _ _ _).symm

end PulledPresentation



section Bare

variable {D D' : Type*} [Category D] [Category D']

/-- For isomorphisms `e : A ≅ A'`, `e' : Z₁ ≅ Z₂` with `e.hom ≫ t = s`, `e'.hom ≫ t' = s'` and
`G.map s ≫ c = b ≫ s'`, the composite `G.map e.inv ≫ b ≫ e'.hom ≫ t'` is `G.map t ≫ c`. -/
theorem map_inv_comp_comp_eq {A A' B : D'} (G : D' ⥤ D) (e : A ≅ A') (t : A' ⟶ B) (s : A ⟶ B)
    (hs : e.hom ≫ t = s) {Z₁ Z₂ W : D} (b : G.obj A ⟶ Z₁) (e' : Z₁ ≅ Z₂) (t' : Z₂ ⟶ W)
    (s' : Z₁ ⟶ W) (hs' : e'.hom ≫ t' = s') (c : G.obj B ⟶ W) (hb : G.map s ≫ c = b ≫ s') :
    G.map e.inv ≫ b ≫ e'.hom ≫ t' = G.map t ≫ c := by
  rw [hs', ← hb, ← hs, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id_assoc]

/-- If `k ≫ ψ = cR ≫ G.map k'`, `k' ≫ q = t'`, `k ≫ r = t` and `cR ≫ G.map t' = t ≫ β`, then
`k ≫ ψ ≫ G.map q = k ≫ r ≫ β`. -/
theorem coeff_comp_eq_of_parts {A B C₀ : D} {A' B' C₀' : D'} (G : D' ⥤ D) (k : A ⟶ B)
    (ψ : B ⟶ G.obj B') (q : B' ⟶ C₀') (r : B ⟶ C₀) (β : C₀ ⟶ G.obj C₀') (cR : A ⟶ G.obj A')
    (k' : A' ⟶ B') (hψ : k ≫ ψ = cR ≫ G.map k') (t' : A' ⟶ C₀') (hq : k' ≫ q = t')
    (t : A ⟶ C₀) (hr : k ≫ r = t) (hc : cR ≫ G.map t' = t ≫ β) :
    k ≫ ψ ≫ G.map q = k ≫ r ≫ β := by
  rw [← Category.assoc, hψ, Category.assoc, ← G.map_comp, hq, hc, ← hr, Category.assoc]

/-- If `var ≫ F.map ψ = v₁ ≫ v₂`, `v₂ ≫ F.map (G.map q) = a'`, `var ≫ F.map r = a` and
`v₁ ≫ a' = a ≫ F.map β`, then `var ≫ F.map (ψ ≫ G.map q) = var ≫ F.map (r ≫ β)`. -/
theorem var_comp_eq_of_parts {S S' T : Type*} [Category S] [Category S'] [Category T]
    (F : S ⥤ T) (G : S' ⥤ S) {E : T} {B C₀ : S} {B' C₀' : S'} {E' : T}
    (var : E ⟶ F.obj B) (ψ : B ⟶ G.obj B') (q : B' ⟶ C₀') (r : B ⟶ C₀)
    (β : C₀ ⟶ G.obj C₀') (v₁ : E ⟶ E') (v₂ : E' ⟶ F.obj (G.obj B'))
    (hψ : var ≫ F.map ψ = v₁ ≫ v₂) (a' : E' ⟶ F.obj (G.obj C₀'))
    (hq : v₂ ≫ F.map (G.map q) = a') (a : E ⟶ F.obj C₀) (hr : var ≫ F.map r = a)
    (hF2 : v₁ ≫ a' = a ≫ F.map β) :
    var ≫ F.map (ψ ≫ G.map q) = var ≫ F.map (r ≫ β) := by
  rw [F.map_comp, F.map_comp, ← Category.assoc, hψ, ← Category.assoc, hr, Category.assoc, hq,
    hF2]

/-- A commutative square transported along identifications of its four vertices, the left
two of them inside a functor. -/
theorem comm_of_eqToHom_map {C₁ : Type*} [Category C₁] (F : C₁ ⥤ D) {K₀ T₀ K₁ T₁ : C₁}
    {M₀ N₀ M₁ N₁ : D} (eK₀ : K₀ = T₀) (eK₁ : K₁ = T₁) (eM₀ : M₀ = N₀) (eM₁ : M₁ = N₁)
    (dK : K₀ ⟶ K₁) (dT : T₀ ⟶ T₁) (hdK : dK = eqToHom eK₀ ≫ dT ≫ eqToHom eK₁.symm)
    (dM : M₀ ⟶ M₁) (dN : N₀ ⟶ N₁) (hdM : dM = eqToHom eM₀ ≫ dN ≫ eqToHom eM₁.symm)
    (φ₀ : F.obj T₀ ⟶ N₀) (φ₁ : F.obj T₁ ⟶ N₁) (sq : φ₀ ≫ dN = F.map dT ≫ φ₁) :
    (F.map (eqToHom eK₀) ≫ φ₀ ≫ eqToHom eM₀.symm) ≫ dM =
      F.map dK ≫ F.map (eqToHom eK₁) ≫ φ₁ ≫ eqToHom eM₁.symm := by
  subst eK₀ eK₁ eM₀ eM₁ hdK hdM
  simp [sq]

end Bare

section SquareRings

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y)

/-- The comparison `g'⁻¹i⁻¹𝒪_P ⟶ i'⁻¹𝒪_{P'}` of the middle rings of the two towers, attached
to the square `i' ≫ p = g' ≫ i`. -/
def middleRingComparison (hip : i' ≫ p = g' ≫ i) :
    inverseImageBaseRing (ringedSpaceHom g') (ringedSpaceHom i) ⟶
      inverseImageSheaf (ringedSpaceHom i') :=
  Stacks.NaiveCotangentFlatBaseChange.baseRingComparisonRingedSpace (ringedSpaceHom g')
    (ringedSpaceHom i) (ringedSpaceHom i') (ringedSpaceHom p)
    (congrArg (fun t : X' ⟶ P => t.toLRSHom.toShHom) hip.symm)

/-- `middleRingComparison` lies over the structure map `g'⁻¹𝒪_X ⟶ 𝒪_{X'}`: the square from
`g'⁻¹i⁻¹𝒪_P` to `𝒪_{X'}` commutes. -/
theorem middleRingComparison_comp (hip : i' ≫ p = g' ≫ i) :
    inverseImageFirstRingMap (ringedSpaceHom g') (ringedSpaceHom i) ≫
        ringedSpaceStructureMap (ringedSpaceHom g') =
      middleRingComparison i i' g' p hip ≫ ringedSpaceStructureMap (ringedSpaceHom i') :=
  Stacks.NaiveCotangentFlatBaseChange.baseRingComparisonRingedSpace_comp _ _ _ _ _

/-- The comparison `g'⁻¹i⁻¹h⁻¹𝒪_Y ⟶ i'⁻¹h'⁻¹𝒪_{Y'}` of the base rings of the two towers,
attached to the square `g' ≫ (i ≫ h) = (i' ≫ h') ≫ g`: the canonical base-ring comparison of
that square, read through the identifications of `(i ≫ h)⁻¹𝒪_Y` and `(i' ≫ h')⁻¹𝒪_{Y'}` with
the iterated inverse images. -/
def baseRingTowerComparison (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    (TopCat.Sheaf.pullback CommRingCat.{u} g'.base).obj
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) ⟶
      inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h') :=
  (TopCat.Sheaf.pullback CommRingCat.{u} g'.base).map
      (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)).inv ≫
    AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h') g' g w ≫
      (inverseImageCompIso (ringedSpaceHom i') (ringedSpaceHom h')).hom

/-- `baseRingTowerComparison` lies over the structure map `g'⁻¹𝒪_X ⟶ 𝒪_{X'}`: the square from
`g'⁻¹i⁻¹h⁻¹𝒪_Y` to `𝒪_{X'}` commutes. -/
theorem baseRingTowerComparison_comp (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    baseRingTowerComparison i h i' h' g' g w ≫
        (inverseImageFirstRingMap (ringedSpaceHom i') (ringedSpaceHom h') ≫
          ringedSpaceStructureMap (ringedSpaceHom i')) =
      (TopCat.Sheaf.pullback CommRingCat.{u} g'.base).map
          (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
            ringedSpaceStructureMap (ringedSpaceHom i)) ≫
        ringedSpaceStructureMap (ringedSpaceHom g') :=
  (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans
    (map_inv_comp_comp_eq (TopCat.Sheaf.pullback CommRingCat.{u} g'.base)
      (inverseImageCompIso (ringedSpaceHom i) (ringedSpaceHom h)) _ _
      (inverseImageCompIso_hom_comp (ringedSpaceHom i) (ringedSpaceHom h))
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison (i ≫ h) (i' ≫ h') g' g w)
      (inverseImageCompIso (ringedSpaceHom i') (ringedSpaceHom h')) _ _
      (inverseImageCompIso_hom_comp (ringedSpaceHom i') (ringedSpaceHom h')) _
      (AlgebraicGeometry.BaseChangeStalk.baseRingComparison_comp (i ≫ h) (i' ≫ h') g' g w)))

/-- The transpose `i⁻¹𝒪_P ⟶ g'_*i'⁻¹𝒪_{P'}` of `middleRingComparison`. -/
def middleRingMap (hip : i' ≫ p = g' ≫ i) :
    inverseImageMiddleRing (ringedSpaceHom i) ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).obj
        (inverseImageMiddleRing (ringedSpaceHom i')) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.base).homEquiv _ _
    (middleRingComparison i i' g' p hip)

/-- The transpose `i⁻¹h⁻¹𝒪_Y ⟶ g'_*i'⁻¹h'⁻¹𝒪_{Y'}` of `baseRingTowerComparison`. -/
def baseRingTowerMap (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h) ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).obj
        (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h')) :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.base).homEquiv _ _
    (baseRingTowerComparison i h i' h' g' g w)

/-- Transposing along an adjunction `F ⊣ G` turns a square `a ≫ s = F.map b ≫ c` into the square
`a^♭ ≫ G.map s = b ≫ c^♭`. -/
private theorem homEquiv_comp_map_iff {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    {G : D ⥤ C} (adj : F ⊣ G) {X W : C} {Y Z : D} (a : F.obj X ⟶ Y) (s : Y ⟶ Z) (b : X ⟶ W)
    (c : F.obj W ⟶ Z) :
    a ≫ s = F.map b ≫ c ↔
      adj.homEquiv _ _ a ≫ G.map s = b ≫ adj.homEquiv _ _ c := by
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left,
    (adj.homEquiv _ _).apply_eq_iff_eq]

/-- `middleRingMap` lies over the map `𝒪_X ⟶ g'_*𝒪_{X'}` of `g'`: the square from `i⁻¹𝒪_P` to
`g'_*𝒪_{X'}` commutes. -/
theorem middleRingMap_comp (hip : i' ≫ p = g' ≫ i) :
    middleRingMap i i' g' p hip ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).map
        (ringedSpaceStructureMap (ringedSpaceHom i')) =
      ringedSpaceStructureMap (ringedSpaceHom i) ≫ structureSheafMap (ringedSpaceHom g') := by
  exact ((homEquiv_comp_map_iff (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    g'.base) _ _ _ _).1 (middleRingComparison_comp i i' g' p hip).symm).trans
      (congrArg (fun t => _ ≫ t) (homEquiv_inverseImageStructureMap (ringedSpaceHom g')))

/-- `baseRingTowerMap` lies over the map `𝒪_X ⟶ g'_*𝒪_{X'}` of `g'`: the square from
`i⁻¹h⁻¹𝒪_Y` to `g'_*𝒪_{X'}` commutes. -/
theorem baseRingTowerMap_comp (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    baseRingTowerMap i h i' h' g' g w ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).map
        (inverseImageFirstRingMap (ringedSpaceHom i') (ringedSpaceHom h') ≫
          ringedSpaceStructureMap (ringedSpaceHom i')) =
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
          ringedSpaceStructureMap (ringedSpaceHom i)) ≫ structureSheafMap (ringedSpaceHom g') := by
  exact ((homEquiv_comp_map_iff (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    g'.base) _ _ _ _).1 (baseRingTowerComparison_comp i h i' h' g' g w)).trans
      (congrArg (fun t => _ ≫ t) (homEquiv_inverseImageStructureMap (ringedSpaceHom g')))

variable [IsImmersion i] [IsImmersion i']

/-- **The morphism of polynomial presentations of the two towers, in transposed form.**  The
morphism `i⁻¹h⁻¹𝒪_Y[i⁻¹𝒪_P] ⟶ g'_*(i'⁻¹h'⁻¹𝒪_{Y'}[i'⁻¹𝒪_{P'}])` of sheaves of rings which is
`baseRingTowerMap` on coefficients and sends the variable `[s]` to the variable
`[middleRingMap s]`. -/
def presentationRingMap (hip : i' ≫ p = g' ≫ i) (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    freeAlgebraSheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
        (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageMiddleRing (ringedSpaceHom i))) ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).obj
        (freeAlgebraSheaf (Opens.grothendieckTopology X'.toRingedSpace.carrier)
          (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h'))
          (underlyingPresheaf (Opens.grothendieckTopology X'.toRingedSpace.carrier)
            (inverseImageMiddleRing (ringedSpaceHom i')))) :=
  freeAlgebraSheafDesc _ _ _ _
    (baseRingTowerMap i h i' h' g' g w ≫ (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).map
      (freeAlgebraSheafCoefficientMap _ _ _))
    (Functor.whiskerRight (middleRingMap i i' g' p hip).hom (forget CommRingCat.{u}) ≫
      Functor.whiskerLeft (Opens.map g'.base).op (freeAlgebraSheafVariable
        (Opens.grothendieckTopology X'.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h'))
        (underlyingPresheaf (Opens.grothendieckTopology X'.toRingedSpace.carrier)
          (inverseImageMiddleRing (ringedSpaceHom i')))))

/-- **The morphism of polynomial presentations lies over the structure map of `g'`.** -/
theorem presentationRingMap_comp_presentation (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    presentationRingMap i h i' h' g' p g hip w ≫
        (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base).map
          (presentation (Opens.grothendieckTopology X'.toRingedSpace.carrier)
            (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h')) X'.toRingedSpace.sheaf
            (inverseImageFirstRingMap (ringedSpaceHom i') (ringedSpaceHom h') ≫
              ringedSpaceStructureMap (ringedSpaceHom i'))
            (underlyingPresheaf (Opens.grothendieckTopology X'.toRingedSpace.carrier)
              (inverseImageMiddleRing (ringedSpaceHom i')))
            (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i')) X'.toRingedSpace.sheaf
              (ringedSpaceStructureMap (ringedSpaceHom i')))) =
      presentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
          (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
            ringedSpaceStructureMap (ringedSpaceHom i))
          (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
            (inverseImageMiddleRing (ringedSpaceHom i)))
          (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
            (ringedSpaceStructureMap (ringedSpaceHom i))) ≫
        structureSheafMap (ringedSpaceHom g') := by
  refine freeAlgebraSheaf_hom_ext _ _ _ _ ?_ ?_
  · exact coeff_comp_eq_of_parts (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base) _ _ _ _ _ _ _
      (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _) _
      (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _) _
      (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _)
      (baseRingTowerMap_comp i h i' h' g' g w)
  · exact var_comp_eq_of_parts
      (sheafToPresheaf _ CommRingCat.{u} ⋙ (Functor.whiskeringRight _ _ _).obj
        (forget CommRingCat.{u}))
      (TopCat.Sheaf.pushforward CommRingCat.{u} g'.base) _ _ _ _ _ _ _
      (freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _) _
      ((Functor.whiskerLeft_comp _ _ _).symm.trans (congrArg (Functor.whiskerLeft _)
        (freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _)))
      _ (freeAlgebraSheafVariable_comp_desc _ _ _ _ _ _)
      ((Functor.whiskerRight_comp _ _ _).symm.trans ((congrArg (fun t =>
        Functor.whiskerRight t.hom (forget CommRingCat.{u}))
        (middleRingMap_comp i i' g' p hip)).trans (Functor.whiskerRight_comp _ _ _)))

/-- The polynomial presentation `i⁻¹h⁻¹𝒪_Y[i⁻¹𝒪_P] ⟶ 𝒪_X` of `𝒪_X` on the sections of
`i⁻¹𝒪_P`. -/
abbrev towerPresentation :=
  presentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
      ringedSpaceStructureMap (ringedSpaceHom i))
    (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageMiddleRing (ringedSpaceHom i)))
    (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom i)))

/-- The naive cotangent complex of `towerPresentation`. -/
abbrev towerPresentationComplex :=
  presentationNaiveCotangentComplex.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
      ringedSpaceStructureMap (ringedSpaceHom i))
    (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageMiddleRing (ringedSpaceHom i)))
    (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom i)))

/-- The degree `-1` term of `towerPresentationComplex` is the conormal sheaf of
`towerPresentation`. -/
theorem towerPresentationComplex_X_negOne :
    (towerPresentationComplex i h).X (-1) =
      (presentationConormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
          ringedSpaceStructureMap (ringedSpaceHom i))
        (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageMiddleRing (ringedSpaceHom i)))
        (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom i)))).X₁ :=
  presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
      ringedSpaceStructureMap (ringedSpaceHom i))
    (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageMiddleRing (ringedSpaceHom i)))
    (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom i)))

/-- The degree `0` term of `towerPresentationComplex` is the scalar extension of the
differentials of `towerPresentation`. -/
theorem towerPresentationComplex_X_zero :
    (towerPresentationComplex i h).X 0 =
      (presentationConormalSequence.{u, u, u, u}
        (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
          ringedSpaceStructureMap (ringedSpaceHom i))
        (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageMiddleRing (ringedSpaceHom i)))
        (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
          (ringedSpaceStructureMap (ringedSpaceHom i)))).X₂ :=
  presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
      ringedSpaceStructureMap (ringedSpaceHom i))
    (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageMiddleRing (ringedSpaceHom i)))
    (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom i)))

/-- The transpose `g'⁻¹(i⁻¹h⁻¹𝒪_Y[i⁻¹𝒪_P]) ⟶ i'⁻¹h'⁻¹𝒪_{Y'}[i'⁻¹𝒪_{P'}]` of
`presentationRingMap`. -/
def presentationRingComparison (hip : i' ≫ p = g' ≫ i) (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} g'.base).homEquiv _ _).symm
    (presentationRingMap i h i' h' g' p g hip w)

/-- The morphism of polynomial presentations `presentationRingComparison` lies over the
structure map `g'⁻¹𝒪_X ⟶ 𝒪_{X'}`. -/
theorem presentationRingComparison_comp (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    presentationRingComparison i h i' h' g' p g hip w ≫ towerPresentation i' h' =
      (TopCat.Sheaf.pullback CommRingCat.{u} g'.base).map (towerPresentation i h) ≫
        ringedSpaceStructureMap (ringedSpaceHom g') := by
  refine (homEquiv_comp_map_iff (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    g'.base) _ _ _ _).2 ?_
  exact ((congrArg (fun t => t ≫ _) (Equiv.apply_symm_apply _ _)).trans
    (presentationRingMap_comp_presentation i h i' h' g' p g hip w)).trans
    (congrArg (fun t => _ ≫ t) (homEquiv_inverseImageStructureMap (ringedSpaceHom g')).symm)

/-- `presentationRingComparison` is `baseRingTowerComparison` on coefficients: it commutes with
the coefficient maps `R ⟶ R[A]` and `R' ⟶ R'[A']`. -/
theorem baseRingTowerComparison_comp_coefficientMap (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    baseRingTowerComparison i h i' h' g' g w ≫
        freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X'.toRingedSpace.carrier)
          (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h'))
          (underlyingPresheaf (Opens.grothendieckTopology X'.toRingedSpace.carrier)
            (inverseImageMiddleRing (ringedSpaceHom i'))) =
      (TopCat.Sheaf.pullback CommRingCat.{u} g'.base).map
          (freeAlgebraSheafCoefficientMap (Opens.grothendieckTopology X.toRingedSpace.carrier)
            (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
            (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
              (inverseImageMiddleRing (ringedSpaceHom i)))) ≫
        presentationRingComparison i h i' h' g' p g hip w := by
  refine (homEquiv_comp_map_iff (TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
    g'.base) _ _ _ _).2 ?_
  exact (freeAlgebraSheafCoefficientMap_comp_desc _ _ _ _ _ _).symm.trans
    (congrArg (fun t => _ ≫ t) (Equiv.apply_symm_apply _ _)).symm

end SquareRings

section ChainMap

variable {X P Y X' P' Y' : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) (i' : X' ⟶ P') (h' : P' ⟶ Y')
  (g' : X' ⟶ X) (p : P' ⟶ P) (g : Y' ⟶ Y) [IsImmersion i] [IsImmersion i']

/-- The degree `-1` component of `pulledPresentationMap`. -/
def pulledPresentationMapNegOne (hip : i' ≫ p = g' ≫ i) (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :=
  pulledConormalSheafMap g'.toLRSHom.toShHom (towerPresentation i h) (towerPresentation i' h')
    (presentationRingComparison i h i' h' g' p g hip w)
    (presentationRingComparison_comp i h i' h' g' p g hip w)

/-- The degree `0` component of `pulledPresentationMap`. -/
def pulledPresentationMapZero (hip : i' ≫ p = g' ≫ i) (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :=
  pulledTensorSheafMap g'.toLRSHom.toShHom (towerPresentation i h) (towerPresentation i' h')
    (presentationRingComparison i h i' h' g' p g hip w)
    (presentationRingComparison_comp i h i' h' g' p g hip w)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
    (freeAlgebraSheafCoefficientMap _ _ _)
    (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h'))
    (freeAlgebraSheafCoefficientMap _ _ _) (baseRingTowerComparison i h i' h' g' g w)
    (baseRingTowerComparison_comp_coefficientMap i h i' h' g' p g hip w)

/-- **The degree `-1` component of the comparison of the pulled-back polynomial presentation
of `𝒪_X` with the polynomial presentation of `𝒪_{X'}`.** -/
def pulledPresentationNegOne (hip : i' ≫ p = g' ≫ i) (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    ((pulledComplexFunctor g'.toLRSHom.toShHom).obj (towerPresentationComplex i h)).X (-1) ⟶
      (towerPresentationComplex i' h').X (-1) :=
  (twoStepPullback g'.toLRSHom.toShHom).map
      (eqToHom (towerPresentationComplex_X_negOne i h)) ≫
    pulledPresentationMapNegOne i h i' h' g' p g hip w ≫
      eqToHom (towerPresentationComplex_X_negOne i' h').symm

/-- The degree `0` component of the comparison of the pulled-back polynomial presentation of
`𝒪_X` with the polynomial presentation of `𝒪_{X'}`. -/
def pulledPresentationZero (hip : i' ≫ p = g' ≫ i) (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    ((pulledComplexFunctor g'.toLRSHom.toShHom).obj (towerPresentationComplex i h)).X 0 ⟶
      (towerPresentationComplex i' h').X 0 :=
  (twoStepPullback g'.toLRSHom.toShHom).map
      (eqToHom (towerPresentationComplex_X_zero i h)) ≫
    pulledPresentationMapZero i h i' h' g' p g hip w ≫
      eqToHom (towerPresentationComplex_X_zero i' h').symm

/-- **The two components commute with the differentials.** -/
theorem pulledPresentationNegOne_comp_d (hip : i' ≫ p = g' ≫ i)
    (w : g' ≫ (i ≫ h) = (i' ≫ h') ≫ g) :
    pulledPresentationNegOne i h i' h' g' p g hip w ≫ (towerPresentationComplex i' h').d (-1) 0 =
      ((pulledComplexFunctor g'.toLRSHom.toShHom).obj (towerPresentationComplex i h)).d (-1) 0 ≫
        pulledPresentationZero i h i' h' g' p g hip w := by
  have hd' := presentationNaiveCotangentComplex_d_negOne_zero.{u, u, u, u}
      (Opens.grothendieckTopology X'.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h')) X'.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i') (ringedSpaceHom h') ≫
        ringedSpaceStructureMap (ringedSpaceHom i'))
      (underlyingPresheaf (Opens.grothendieckTopology X'.toRingedSpace.carrier)
        (inverseImageMiddleRing (ringedSpaceHom i')))
      (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i')) X'.toRingedSpace.sheaf
        (ringedSpaceStructureMap (ringedSpaceHom i')))
  have hd := presentationNaiveCotangentComplex_d_negOne_zero.{u, u, u, u}
      (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
        ringedSpaceStructureMap (ringedSpaceHom i))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageMiddleRing (ringedSpaceHom i)))
      (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (ringedSpaceStructureMap (ringedSpaceHom i)))
  have sq := pulledConormalSheafMap_comp_conormalSequence_f g'.toLRSHom.toShHom
      (towerPresentation i h) (towerPresentation i' h')
      (presentationRingComparison i h i' h' g' p g hip w)
      (presentationRingComparison_comp i h i' h' g' p g hip w)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (freeAlgebraSheafCoefficientMap _ _ _)
      (inverseImageBaseRing (ringedSpaceHom i') (ringedSpaceHom h'))
      (freeAlgebraSheafCoefficientMap _ _ _) (baseRingTowerComparison i h i' h' g' g w)
      (baseRingTowerComparison_comp_coefficientMap i h i' h' g' p g hip w)
  exact comm_of_eqToHom_map (twoStepPullback g'.toLRSHom.toShHom)
    (towerPresentationComplex_X_negOne i h) (towerPresentationComplex_X_zero i h)
    (towerPresentationComplex_X_negOne i' h') (towerPresentationComplex_X_zero i' h') _ _ hd _ _
    hd' _ _ sq


end ChainMap



section ClassX

variable {T : TopCat.{u}} {B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}

/-- `eqToHom` between sheaves of modules acts on sections as a cast, so two of them in a row
along an equation and its inverse act as the identity. -/
theorem eqToHom_symm_val_app_eqToHom_val_app
    {M N : _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology T) B)} (e : M = N) (U : (Opens T)ᵒᵖ) (x : M.val.obj U) :
    (eqToHom e.symm).val.app U ((eqToHom e).val.app U x) = x := by
  subst e
  rfl

variable {R A : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
  (a : R ⟶ A) (φ : A ⟶ B) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ.hom]

/-- The conormal class of a section of the kernel ideal of `φ`, read in the degree `-1` term of
a complex `K` whose degree `-1` term is the conormal sheaf of `φ`. -/
def conormalClassX {K : CochainComplex (_root_.SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (J := Opens.grothendieckTopology T) B)) ℤ}
    (e : K.X (-1) = (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology T) R A B a φ).X₁)
    (U : (Opens T)ᵒᵖ) (s : kernelIdeal φ.hom U) : (K.X (-1)).val.obj U :=
  (eqToHom e.symm).val.app U (conormalClass.{u, u, u, u} _ R A B a φ U s)

/-- Transported back along `e`, `conormalClassX` is the conormal class `conormalClass`. -/
theorem eqToHom_val_app_conormalClassX {K : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) ℤ}
    (e : K.X (-1) = (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology T) R A B a φ).X₁)
    (U : (Opens T)ᵒᵖ) (s : kernelIdeal φ.hom U) :
    (eqToHom e).val.app U (conormalClassX a φ e U s) =
      conormalClass.{u, u, u, u} _ R A B a φ U s :=
  eqToHom_symm_val_app_eqToHom_val_app e.symm U _

variable {R' A' : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u}}
  (a' : R' ⟶ A') (φ' : A' ⟶ B) [Presheaf.IsLocallySurjective (Opens.grothendieckTopology T) φ'.hom]

/-- A morphism of degree `-1` terms which is, up to the identifications with the conormal
sheaves, a morphism of conormal sheaves carrying the class of `s` to the class of `t`, carries
the class of `s` to the class of `t`. -/
theorem map_conormalClassX {K L : CochainComplex (_root_.SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (J := Opens.grothendieckTopology T) B)) ℤ}
    (eK : K.X (-1) = (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology T) R A B a φ).X₁)
    (eL : L.X (-1) =
      (conormalSequence.{u, u, u, u} (Opens.grothendieckTopology T) R' A' B a' φ').X₁)
    (m : K.X (-1) ⟶ L.X (-1)) (c : (conormalSequence.{u, u, u, u} _ R A B a φ).X₁ ⟶
      (conormalSequence.{u, u, u, u} _ R' A' B a' φ').X₁)
    (hm : m = eqToHom eK ≫ c ≫ eqToHom eL.symm) (U : (Opens T)ᵒᵖ) (s : kernelIdeal φ.hom U)
    (t : kernelIdeal φ'.hom U)
    (hc : c.val.app U (conormalClass.{u, u, u, u} _ R A B a φ U s) =
      conormalClass.{u, u, u, u} _ R' A' B a' φ' U t) :
    m.val.app U (conormalClassX a φ eK U s) = conormalClassX a' φ' eL U t := by
  subst hm
  show (eqToHom eL.symm).val.app U (c.val.app U ((eqToHom eK).val.app U _)) = _
  rw [eqToHom_val_app_conormalClassX, hc]
  rfl

end ClassX

section Abstract

variable {C : Type*} [Category C] [Abelian C] {K L M : CochainComplex C ℤ}

/-- **A map out of `H^{-1}` through the inverse of an isomorphism on `H^{-1}`, computed by a
map of degree `-1` terms.**  Let `Ψ : K ⟶ L` and `hh : M ⟶ L` be morphisms of complexes with
nothing in degree `-2`, `hh` inducing an isomorphism on `H^{-1}`, and let `φ₁ : K⁻¹ ⟶ M⁻¹`
and `φ₀ : K⁰ ⟶ M⁰` commute with the differentials.  If `φ₁ ≫ hh` is `Ψ` in degree `-1`, then
`H^{-1}(Ψ) ≫ H^{-1}(hh)⁻¹`, followed by the inclusion of `H^{-1}(M)`, is the inclusion of
`H^{-1}(K)` followed by `φ₁`. -/
theorem homologyMap_inv_homologyNegOneι_eq_of_degreewise (hK : IsZero (K.X (-2)))
    (hL : IsZero (L.X (-2))) (hM : IsZero (M.X (-2))) (Ψ : K ⟶ L) (hh : M ⟶ L)
    [IsIso (HomologicalComplex.homologyMap hh (-1))] (φ₁ : K.X (-1) ⟶ M.X (-1))
    (φ₀ : K.X 0 ⟶ M.X 0) (hd : φ₁ ≫ M.d (-1) 0 = K.d (-1) 0 ≫ φ₀)
    (hΨ : φ₁ ≫ hh.f (-1) = Ψ.f (-1)) :
    HomologicalComplex.homologyMap Ψ (-1) ≫ inv (HomologicalComplex.homologyMap hh (-1)) ≫
        homologyNegOneι M hM =
      homologyNegOneι K hK ≫ φ₁ := by
  have hz : (homologyNegOneι K hK ≫ φ₁) ≫ M.d (-1) 0 = 0 := by
    rw [Category.assoc, hd, homologyNegOneι, Category.assoc, ← Category.assoc (kernel.ι _),
      kernel.condition, zero_comp, comp_zero]
  let y := kernel.lift (M.d (-1) 0) (homologyNegOneι K hK ≫ φ₁) hz ≫
    (homologyNegOneIsoKernel M hM).inv
  have hy : y ≫ homologyNegOneι M hM = homologyNegOneι K hK ≫ φ₁ := by
    simp only [y, homologyNegOneι, Category.assoc, Iso.inv_hom_id_assoc, kernel.lift_ι]
  have hyH : y ≫ HomologicalComplex.homologyMap hh (-1) =
      HomologicalComplex.homologyMap Ψ (-1) := by
    have := mono_homologyNegOneι L hL
    rw [← cancel_mono (homologyNegOneι L hL), Category.assoc, homologyMap_homologyNegOneι hh hM hL,
      ← Category.assoc, hy, Category.assoc, hΨ, homologyMap_homologyNegOneι Ψ hK hL]
  rw [← hyH, Category.assoc, IsIso.hom_inv_id_assoc, hy]

end Abstract



section Presentation

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) [IsImmersion i]

/-- The morphism of presentations `R[A] ⟶ R[𝒪_X]` evaluating the variables in `𝒪_X`. -/
abbrev evaluationRingMap :=
  freeAlgebraMap (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
    (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageMiddleRing (ringedSpaceHom i)))
    (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      X.toRingedSpace.sheaf)
    (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
      (ringedSpaceStructureMap (ringedSpaceHom i)))

/-- `evaluationRingMap` followed by the canonical presentation `R[𝒪_X] ⟶ 𝒪_X` is
`towerPresentation`. -/
theorem evaluationRingMap_comp_canonicalPresentation :
    evaluationRingMap i h ≫
        canonicalPresentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
          ringedSpaceStructureMap (ringedSpaceHom i)) =
      towerPresentation i h :=
  (congrArg (fun t => evaluationRingMap i h ≫ t) (presentation_id _ _ _ _).symm).trans
    (freeAlgebraMap_comp_presentation.{u, u, u} _ _ _ _ _ _ _ _ _ (Category.comp_id _))

/-- `evaluationRingMap` carries the kernel ideal of `towerPresentation` into the kernel ideal of
the canonical presentation. -/
theorem evaluationRingMap_mem_kernelIdeal (U : (Opens X.carrier)ᵒᵖ)
    (s : kernelIdeal (towerPresentation i h).hom U) :
    (evaluationRingMap i h).hom.app U s ∈
      kernelIdeal (canonicalPresentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
          ringedSpaceStructureMap (ringedSpaceHom i))).hom U :=
  by
    have e := congrArg (fun t => (t.hom.app U).hom s.1)
      (evaluationRingMap_comp_canonicalPresentation i h)
    have hs : ((towerPresentation i h).hom.app U).hom s.1 = 0 := s.2
    exact e.trans hs

/-- The coefficient map `R ⟶ R[A]` of the polynomial presentation on the sections of `A`. -/
abbrev towerCoefficientMap :=
  freeAlgebraSheafCoefficientMap.{u, u, u} (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
    (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageMiddleRing (ringedSpaceHom i)))

/-- The coefficient map `R ⟶ R[𝒪_X]` of the canonical presentation. -/
abbrev canonicalCoefficientMap :=
  freeAlgebraSheafCoefficientMap.{u, u, u} (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
    (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
      X.toRingedSpace.sheaf)

/-- The canonical presentation `R[𝒪_X] ⟶ 𝒪_X` over `R = i⁻¹h⁻¹𝒪_Y`. -/
abbrev towerCanonicalPresentation :=
  canonicalPresentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
    (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
      ringedSpaceStructureMap (ringedSpaceHom i))

/-- The canonical presentation `R[𝒪_X] ⟶ 𝒪_X` is locally surjective. -/
instance isLocallySurjective_towerCanonicalPresentation :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (towerCanonicalPresentation i h).hom :=
  canonicalPresentation_isLocallySurjective _ _ _ _

/-- The presentation `R[𝒪_X] ⟶ 𝒪_X` attached to the identity of `𝒪_X` is locally surjective. -/
instance isLocallySurjective_towerPresentationId :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (presentation (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
        (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
          ringedSpaceStructureMap (ringedSpaceHom i))
        (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
          X.toRingedSpace.sheaf) (𝟙 _)).hom :=
  presentation_id_isLocallySurjective _ _ _ _

/-- The comparison of [Stacks Project, Tag 08TL] carries the conormal class of a polynomial
relation `s` to the conormal class of the polynomial obtained by evaluating the variables of
`s` in `𝒪_X`. -/
theorem presentationComparison_conormalClassX (U : (Opens X.carrier)ᵒᵖ)
    (s : kernelIdeal (towerPresentation i h).hom U) :
    ((presentationComparison i h).f (-1)).val.app U
        (conormalClassX (towerCoefficientMap i h) (towerPresentation i h)
          (towerPresentationComplex_X_negOne i h) U s) =
      conormalClassX (canonicalCoefficientMap i h) (towerCanonicalPresentation i h)
        (naiveCotangentComplex_X_negOne.{u, u, u, u} _ _ _ _) U
        ⟨(evaluationRingMap i h).hom.app U s, evaluationRingMap_mem_kernelIdeal i h U s⟩ := by
  have hm := presentationNaiveCotangentComplexMap_f_negOne.{u, u, u, u}
      (Opens.grothendieckTopology X.toRingedSpace.carrier)
      (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        (inverseImageMiddleRing (ringedSpaceHom i)))
      (underlyingPresheaf (Opens.grothendieckTopology X.toRingedSpace.carrier)
        X.toRingedSpace.sheaf)
      (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (ringedSpaceStructureMap (ringedSpaceHom i))) X.toRingedSpace.sheaf
      (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
        ringedSpaceStructureMap (ringedSpaceHom i))
      (towerGenerators (inverseImageMiddleRing (ringedSpaceHom i)) X.toRingedSpace.sheaf
        (ringedSpaceStructureMap (ringedSpaceHom i))) (𝟙 _) (Category.comp_id _)
  have hc := conormalSheafMapOfFac_conormalClass.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf _ _
    (towerCoefficientMap i h) (canonicalCoefficientMap i h)
    (towerPresentation i h) (towerCanonicalPresentation i h) (evaluationRingMap i h)
    (evaluationRingMap_comp_canonicalPresentation i h) U s
  exact map_conormalClassX _ _ _ _ _ _ _ _ hm U s _ hc

end Presentation

end Stacks.NaiveCotangentPulledImmersion

end
