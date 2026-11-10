module

public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Limits.EventuallyProperOverLimit
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectColimit
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectArrowIso
public import StacksFrontier.AlgebraicGeometry.Limits.ProperImageSystemModels
public import StacksFrontier.AlgebraicGeometry.ProperLimitStage.SeparatedModel
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A Noetherian model of a relatively perfect object over an affine base

Let `S` be affine and `f : X ⟶ S` flat, proper and of finite presentation, and let `E` be an
`S`-perfect object of `D(𝒪_X)`. Then `f` and `E` are the base change of a flat proper morphism of
finite presentation `X' ⟶ S'` over a Noetherian scheme `S'` and of an `S'`-perfect object on `X'`.

## Main results

* `AlgebraicGeometry.exists_descentSituation_flat_proper_model`: a flat proper morphism of finite
  presentation over an affine base `S` is the base change of a flat proper morphism of finite
  presentation over the base stage of a directed system of Noetherian schemes with affine
  transition morphisms and limit `S`.
* `AlgebraicGeometry.exists_relativeDescentSituation_flat_proper_model`: the same, as a relative
  descent situation.
* `AlgebraicGeometry.exists_isPerfectRelativeTo_noetherianModel`: a flat proper morphism of
  finite presentation over an affine base and an `S`-perfect object on its source are the base
  change of such a morphism over a Noetherian scheme and of a relatively perfect object on it.

## References

* [Stacks Project, Tag 0DI6](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Tag 0DJT](https://stacks.math.columbia.edu/tag/0DJT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StrictlyPerfect

universe u

namespace AlgebraicGeometry

/-- A flat proper morphism of finite presentation `f : X ⟶ S` over an affine base has a
Noetherian approximation: a directed system of Noetherian schemes with affine transition
morphisms with limit `S`, and at its base stage a flat proper morphism of finite presentation
whose base change to `S` is `f`. -/
@[ega "IV 12.0.2" "special case"]
theorem exists_descentSituation_flat_proper_model {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f] :
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·)) (D : DescentSituation.{u, u} J)
      (X₀ : Over (D.system.obj (op D.base))),
      (∀ j : J, IsNoetherian (D.system.obj (op j))) ∧ Flat X₀.hom ∧ IsProper X₀.hom ∧
        FinitePresentation X₀.hom ∧
        ∃ e : D.limitCone.pt ≅ S,
          Nonempty ((Over.pullback (D.limitCone.π.app (op D.base))).obj X₀ ≅
            Over.mk (f ≫ e.inv)) := by
  obtain ⟨J, _, _, _, D₀, hS, -, -⟩ := exists_limitNoetherianSituation_of_isAffine S
  let e : D₀.limitCone.pt ≅ S := eqToIso hS
  have (j : J) : IsNoetherian (D₀.system.obj (op j)) := D₀.noetherian j
  have (j : Jᵒᵖ) : IsNoetherian (D₀.system.obj j) := D₀.noetherian j.unop
  have (j : Jᵒᵖ) : CompactSpace (D₀.system.obj j) := inferInstance
  have (j : Jᵒᵖ) : QuasiSeparatedSpace (D₀.system.obj j) := inferInstance
  have : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (D₀.system.map g) := D₀.transition_affine
  let XS : Over D₀.limitCone.pt := Over.mk (f ≫ e.inv)
  have : IsProper XS.hom := by dsimp [XS]; infer_instance
  have hXfp : FinitePresentation XS.hom := by
    dsimp [XS]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨j, Xj, hXjfp, hXjp, ⟨ej⟩⟩ :=
    exists_isProper_finitePresentation_overPullbackObj_of_isLimit D₀.system D₀.limitCone
      D₀.isLimit XS hXfp
  have : IsProper Xj.hom := hXjp
  have : LocallyOfFinitePresentation Xj.hom := hXjfp.1
  have : CompactSpace Xj.left := QuasiCompact.compactSpace_of_compactSpace Xj.hom
  have : QuasiSeparatedSpace Xj.left := quasiSeparatedSpace_of_quasiSeparated Xj.hom
  let f₀ : Xj ⟶ Over.mk (𝟙 (D₀.system.obj j)) := Over.homMk Xj.hom
  have : LocallyOfFinitePresentation f₀.left :=
    (inferInstance : LocallyOfFinitePresentation Xj.hom)
  have : CompactSpace (Over.mk (𝟙 (D₀.system.obj j))).left :=
    (inferInstance : CompactSpace (D₀.system.obj j))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D₀.system.obj j))).left :=
    (inferInstance : QuasiSeparatedSpace (D₀.system.obj j))
  have hri : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Flat ((Over.pullback (D₀.limitCone.π.app j)).map f₀).left := by
    rw [flat_overPullback_terminal_iff]
    exact prop_of_overIso (@Flat) ej (show Flat (f ≫ e.inv) from inferInstance)
  obtain ⟨i, g, hg⟩ := exists_flat_baseChange_of_limitBaseChange D₀.system D₀.limitCone j Xj
    (Over.mk (𝟙 _)) f₀ D₀.isLimit
  rw [flat_overPullback_terminal_iff] at hg
  let D : DescentSituation.{u, u} J :=
    { system := D₀.system
      transition_affine := D₀.transition_affine
      quasiCompact := fun _ => inferInstance
      quasiSeparated := fun _ => inferInstance
      limitCone := D₀.limitCone
      isLimit := D₀.isLimit
      base := i.unop }
  refine ⟨J, inferInstance, inferInstance, D, (Over.pullback (D₀.system.map g)).obj Xj,
    fun k => D₀.noetherian k, hg, ?_, finitePresentation_overPullbackObj _ _ hXjfp, e,
    ⟨(overPullbackObjTransitionIso D₀.system D₀.limitCone g Xj).symm ≪≫ ej.symm⟩⟩
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback Xj.hom (D₀.system.map g)) hXjp

/-- A flat proper morphism of finite presentation `f : X ⟶ S` over an affine base is the limit
of a relative descent situation of [Stacks, Tag 0DI6] with Noetherian stages and proper
`X₀ ⟶ S₀`, up to isomorphisms of source and target. -/
theorem exists_relativeDescentSituation_flat_proper_model {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) [Flat f] [IsProper f] [LocallyOfFinitePresentation f] :
    ∃ (J : Type u) (_ : Preorder J) (_ : IsDirected J (· ≤ ·))
      (R : RelativeDescentSituation.{u, u} J),
      (∀ j : J, IsNoetherian (R.descent.system.obj (op j))) ∧ IsProper R.X₀.hom ∧
        ∃ (eX : R.limitScheme ≅ X) (eS : R.descent.limitCone.pt ≅ S),
          eX.hom ≫ f = R.structureMapLimit ≫ eS.hom := by
  obtain ⟨J, _, _, D, X₀, hN, hfl, hpr, hfp, eS, ⟨eX⟩⟩ :=
    exists_descentSituation_flat_proper_model f
  refine ⟨J, inferInstance, inferInstance, ⟨D, X₀, hfl, hfp⟩, hN, hpr, (Over.forget _).mapIso eX,
    eS, ?_⟩
  have h := Over.w eX.hom
  dsimp at h ⊢
  rw [← cancel_mono eS.inv, Category.assoc, Category.assoc, eS.hom_inv_id, Category.comp_id, h]

section Object

attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback) in
/-- Let `S` be affine, `f : X ⟶ S` flat, proper and of finite presentation, and `E` an
`S`-perfect object of `D(𝒪_X)`. Then there are a cartesian square
```
X --g'--> X'
|f        |f'
S --g---> S'
```
with `S'` Noetherian and `f'` flat, proper and of finite presentation, and an `S'`-perfect `E'`
on `X'` with `L(g')^*E' ≅ E`. -/
theorem exists_isPerfectRelativeTo_noetherianModel {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hE : f.IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) E) :
    ∃ (S' X' : Scheme.{u}) (_ : IsNoetherian S') (f' : X' ⟶ S') (_ : Flat f') (_ : IsProper f')
      (_ : LocallyOfFinitePresentation f') (g : S ⟶ S') (g' : X ⟶ X'),
      IsPullback g' f f' g ∧ ∃ E' : DerivedCategory (OXMod.{u, u} X'.toRingedSpace),
        f'.IsPerfectRelativeTo
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily.{u + 1, u} _) E' ∧
          Nonempty ((derivedPullback g'.toLRSHom.toShHom).obj E' ≅ E) := by
  obtain ⟨J, _, _, R, hN, hpr, eX, eS, hw⟩ := exists_relativeDescentSituation_flat_proper_model f
  let : Flat R.X₀.hom := R.flat
  let : LocallyOfFinitePresentation R.X₀.hom := R.finitePresentation.locallyOfFinitePresentation
  have : IsProper R.X₀.hom := hpr
  let ψ : Scheme.Hom.ringedArrow R.structureMapLimit ≅ Scheme.Hom.ringedArrow f :=
    Arrow.isoMk (Scheme.forgetToRingedSpace.mapIso eX) (Scheme.forgetToRingedSpace.mapIso eS)
      (by
        change Scheme.forgetToRingedSpace.map eX.hom ≫ Scheme.forgetToRingedSpace.map f =
          Scheme.forgetToRingedSpace.map R.structureMapLimit ≫
            Scheme.forgetToRingedSpace.map eS.hom
        rw [← Functor.map_comp, ← Functor.map_comp, hw])
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : CompactSpace R.limitScheme := (Scheme.homeoOfIso eX.symm).compactSpace
  have hElim := (Scheme.Hom.isPerfectRelativeTo_arrowIso_iff R.structureMapLimit f ψ E).2 hE
  obtain ⟨i, Ei, hEi, ⟨eE⟩⟩ := R.perfectEssentiallySurjectiveCanonical _ hElim
  have : IsNoetherian (R.descent.system.obj (op i.1)) := hN i.1
  have : Flat (R.structureMapAt i) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback R.X₀.hom (R.baseMap i)) inferInstance
  have : IsProper (R.structureMapAt i) := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback R.X₀.hom (R.baseMap i)) inferInstance
  have : LocallyOfFinitePresentation (R.structureMapAt i) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback R.X₀.hom (R.baseMap i)) inferInstance
  have hsq : IsPullback (eX.inv ≫ R.projection i) f (R.structureMapAt i)
      (eS.inv ≫ R.descent.limitCone.π.app (op i.1)) := by
    refine (IsPullback.of_hasPullback (R.structureMapAt i)
      (R.descent.limitCone.π.app (op i.1))).of_iso (R.limitIsoPullback i ≪≫ eX) (Iso.refl _) eS
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp [R.limitIsoPullback_hom_projection i]
    · rw [Iso.trans_hom, Category.assoc, hw, ← Category.assoc,
        R.limitIsoPullback_hom_structureMapLimit i]
  refine ⟨_, _, inferInstance, R.structureMapAt i, inferInstance, inferInstance, inferInstance,
    eS.inv ≫ R.descent.limitCone.π.app (op i.1), eX.inv ≫ R.projection i, hsq, Ei, hEi, ⟨?_⟩⟩
  exact ((Stacks.DerivedPullback.schemeFactorIso eX.inv (R.projection i) _ rfl).app Ei).symm ≪≫
    (derivedPullback eX.inv.toLRSHom.toShHom).mapIso eE ≪≫
    (Stacks.DerivedPullback.schemeFactorIso eX.inv eX.hom (𝟙 _) eX.inv_hom_id).app E ≪≫
    (Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso _).app E

end Object

end AlgebraicGeometry

end
