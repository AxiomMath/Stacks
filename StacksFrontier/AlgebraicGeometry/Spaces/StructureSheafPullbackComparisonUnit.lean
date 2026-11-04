module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition

/-!
# The comparison `g^*𝒪_{X'} ⟶ 𝒪_X` is an isomorphism

`AlgebraicGeometry.Space.structureModulePullbackMap` and
`AlgebraicGeometry.Space.modulePullbackUnitIso` are two descriptions of the canonical map
`g^*𝒪_{X'} ⟶ 𝒪_X` attached to a morphism `g : X ⟶ X'` of algebraic spaces: the first is
defined by its linear map of sections along `g`, pullback of regular functions on a diagram of
étale scheme charts, and the second is the identification `g^*𝒪_{X'} ≅ 𝒪_X` obtained by
corepresentability. This file shows that they agree, so that the first is an isomorphism, and
that the identification is compatible with the comparison of inverse images along a composite.

## Main results

* `AlgebraicGeometry.Space.structureModuleFMap_eq`: the linear map of sections defining
  `AlgebraicGeometry.Space.structureModulePullbackMap` is the one of the structure map.
* `AlgebraicGeometry.Space.structureModulePullbackMap_eq_modulePullbackUnitIso_hom`: **the two
  descriptions of `g^*𝒪_{X'} ⟶ 𝒪_X` agree.**
* `AlgebraicGeometry.Space.isIso_structureModulePullbackMap` and
  `AlgebraicGeometry.Space.mono_structureModulePullbackMap`: consequently the comparison is an
  isomorphism.
* `AlgebraicGeometry.Space.mono_idealSheafMap_of_mono_modulePullback_map_ι`: the map of
  defining ideal sheaves is injective as soon as the inverse image of the inclusion
  `𝓘' ⊆ 𝒪_{X'}` is.
* `AlgebraicGeometry.Space.modulePullbackTriangle_hom_app_unit_comp`: **the identification
  `h^*𝒪_X ≅ 𝒪_{X'}` is compatible with the comparison of inverse images along a composite**,
  for the composite presented as a single morphism.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X X' X'' : AlgebraicSpaces B S hS}

/-! ### The two descriptions of the comparison of structure sheaves -/

/-- **The linear map of sections defining `AlgebraicGeometry.Space.structureModulePullbackMap`
is the one of the structure map.** -/
theorem structureModuleFMap_eq (g : X ⟶ X') :
    structureModuleFMap B S hS g =
      modulePushforwardHomEquiv B S hS g
        (SheafOfModules.unit (structureRingSheaf B S hS X))
        (SheafOfModules.unit (structureRingSheaf B S hS X'))
        (pushforwardStructureProjection B S hS g) := by
  refine ModuleFMap.ext B S hS (funext fun d ↦ funext fun s ↦ ?_)
  exact ((moduleChartProjection_app_structureSharp B S hS g d.V _ s).trans
    (chartPullback_indexOfChartDiagram B S hS g d s)).symm

/-- **The two descriptions of the canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` agree.**  The map defined by
its linear map of sections, `AlgebraicGeometry.Space.structureModulePullbackMap`, is the
identification `g^*𝒪_{X'} ≅ 𝒪_X` of [Stacks Project, Tag 03LU] obtained by corepresentability.
-/
theorem structureModulePullbackMap_eq_modulePullbackUnitIso_hom (g : X ⟶ X') :
    structureModulePullbackMap B S hS g = (modulePullbackUnitIso B S hS g).hom := by
  refine ((modulePullbackAdjunction B S hS g).homEquiv _ _).injective ?_
  refine Eq.trans (structureModulePullbackMap_transpose B S hS g) ?_
  refine Eq.trans ?_ (homEquiv_modulePullbackUnitIso_hom B S hS g).symm
  exact (Equiv.symm_apply_eq _).mpr (structureModuleFMap_eq B S hS g)

/-- **The canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` is an isomorphism.** -/
theorem isIso_structureModulePullbackMap (g : X ⟶ X') :
    IsIso (structureModulePullbackMap B S hS g) := by
  rw [structureModulePullbackMap_eq_modulePullbackUnitIso_hom]
  exact Iso.isIso_hom (modulePullbackUnitIso B S hS g)

/-- The canonical map `g^*𝒪_{X'} ⟶ 𝒪_X` is a monomorphism. -/
theorem mono_structureModulePullbackMap (g : X ⟶ X') :
    Mono (structureModulePullbackMap B S hS g) :=
  @IsIso.mono_of_iso _ _ _ _ _ (isIso_structureModulePullbackMap B S hS g)

/-- **The map of defining ideal sheaves is injective as soon as the inverse image of the
inclusion `𝓘' ⊆ 𝒪_{X'}` is.** -/
theorem mono_idealSheafMap_of_mono_modulePullback_map_ι (Z : ClosedSubspaces B S hS X.1)
    (Z' : ClosedSubspaces B S hS X'.1) (g : X ⟶ X')
    (f : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z'.1.toFunctor, Z'.2.1⟩ : AlgebraicSpaces B S hS))
    (hsq : subspaceInclusion B S hS X Z ≫ g = f ≫ subspaceInclusion B S hS X' Z')
    (hι : Mono ((modulePullback B S hS g).map (definingIdealSheaf B S hS X' Z').ι)) :
    Mono (idealSheafMap B S hS Z Z' g f hsq) :=
  mono_idealSheafMap_of_mono B S hS Z Z' g f hsq hι
    (mono_structureModulePullbackMap B S hS g)

/-! ### Compatibility with the comparison of inverse images along a composite -/

/-- **The identification `h^*𝒪_X ≅ 𝒪_{X'}` of [Stacks Project, Tag 03LU] is compatible with the
comparison of inverse images along a composite.**  For `a : X ⟶ X'`, `b : X' ⟶ X''` and a
morphism `c` with `a ≫ b = c`, breaking `c^*𝒪_{X''}` into `a^*b^*𝒪_{X''}` and then identifying
the two structure sheaves in turn gives the identification for `c`. -/
theorem modulePullbackTriangle_hom_app_unit_comp (a : X ⟶ X') (b : X' ⟶ X'') {c : X ⟶ X''}
    (hk : a ≫ b = c) :
    (modulePullbackTriangle B S hS hk).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X'')) ≫
        (modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).hom ≫
        (modulePullbackUnitIso B S hS a).hom =
      (modulePullbackUnitIso B S hS c).hom := by
  subst hk
  rw [modulePullbackTriangle_rfl, ← structureModulePullbackMap_eq_modulePullbackUnitIso_hom,
    ← structureModulePullbackMap_eq_modulePullbackUnitIso_hom,
    ← structureModulePullbackMap_eq_modulePullbackUnitIso_hom,
    structureModulePullbackMap_comp B S hS a b]
  rfl

/-- For `a : X ⟶ X'`, `b : X' ⟶ X''` and `c` with `a ≫ b = c`, the identification for `a`
followed by the inverse of the identification for `c` and the comparison
`c^*𝒪_{X''} ⟶ a^*b^*𝒪_{X''}` is `a^*` of the inverse of the identification for `b`. -/
theorem modulePullbackUnitIso_hom_comp_inv_comp_modulePullbackTriangle_hom_app (a : X ⟶ X')
    (b : X' ⟶ X'') {c : X ⟶ X''} (hk : a ≫ b = c) :
    (modulePullbackUnitIso B S hS a).hom ≫ (modulePullbackUnitIso B S hS c).inv ≫
        (modulePullbackTriangle B S hS hk).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X'')) =
      (modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).inv := by
  have hMi : (modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).hom ≫
      (modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).inv =
        𝟙 ((modulePullback B S hS a).obj ((modulePullback B S hS b).obj
          (SheafOfModules.unit (structureRingSheaf B S hS X'')))) := by
    rw [← Functor.map_comp, Iso.hom_inv_id]
    exact (modulePullback B S hS a).map_id _
  have cancel : ∀ {W P Q R : Modules.{u, u} B S hS X.1 X.2} (t : W ⟶ P) (mh : P ⟶ Q)
      (mi : Q ⟶ P) (α : Q ≅ R), mh ≫ mi = 𝟙 P →
      (t ≫ mh ≫ α.hom) ≫ α.inv ≫ mi = t := by
    intro W P Q R t mh mi α h
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [h, Category.comp_id]
  have hfin := (eq_whisker
    (modulePullbackTriangle_hom_app_unit_comp B S hS a b hk).symm
    ((modulePullbackUnitIso B S hS a).inv ≫
      (modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).inv)).trans
    (cancel ((modulePullbackTriangle B S hS hk).hom.app
        (SheafOfModules.unit (structureRingSheaf B S hS X'')))
      ((modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).hom)
      ((modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).inv)
      (modulePullbackUnitIso B S hS a) hMi)
  exact (Iso.eq_inv_comp _).mp ((Iso.inv_comp_eq _).mpr hfin.symm)

end AlgebraicGeometry.Space

end
