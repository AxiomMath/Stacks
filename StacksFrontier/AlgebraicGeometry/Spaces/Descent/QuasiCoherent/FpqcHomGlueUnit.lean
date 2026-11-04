module

public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBaseChangeEtaleSquareComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit

/-!
# The identification `f^*𝒪_Y ≅ 𝒪_X` composes, and pullback of global sections is functorial

For a morphism `f : X ⟶ Y` of algebraic spaces the inverse image of Stacks 03LU carries the
structure sheaf to the structure sheaf, `AlgebraicGeometry.Space.modulePullbackUnitIso`.  This
file shows that this identification is the canonical map
`AlgebraicGeometry.Space.structureModulePullbackMap` induced by pullback of regular functions, so
that it inherits that map's composition law, and deduces that the inverse image of a global
section of a module along a composite is the iterated inverse image, read through the
composition comparison of Stacks 03LU.

## Main results

* `AlgebraicGeometry.Space.modulePullbackUnitIso_inv_comp_triangle_hom`: the identification is
  compatible with the composition comparison.
* `AlgebraicGeometry.Space.sectionsMap_modulePullbackSections_triangle`: **the inverse images of
  a global section compose.**

## Implementation notes

Both maps out of `g^*𝒪_Y` are determined by their transposes along the adjunction of Stacks 03D7,
and those by their linear maps of sections along `g`; on a chart diagram both are pullback of
regular functions along the vertical morphism.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The identification `f^*𝒪 ≅ 𝒪` of Stacks 03LU is compatible with the composition
comparison.** -/
theorem modulePullbackUnitIso_inv_comp_triangle_hom {P X' X : AlgebraicSpaces B S hS}
    (p : P ⟶ X') (f : X' ⟶ X) {k : P ⟶ X} (hk : p ≫ f = k) :
    (modulePullbackUnitIso B S hS k).inv ≫
        (modulePullbackTriangle B S hS hk).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X)) =
      (modulePullbackUnitIso B S hS p).inv ≫
        (modulePullback B S hS p).map (modulePullbackUnitIso B S hS f).inv := by
  subst hk
  have h := structureModulePullbackMap_comp B S hS p f
  simp only [structureModulePullbackMap_eq_modulePullbackUnitIso_hom] at h
  rw [modulePullbackTriangle_rfl, Iso.symm_hom]
  refine (Iso.inv_comp_eq _).2 ?_
  have e : (modulePullback B S hS p).map (modulePullbackUnitIso B S hS f).hom ≫
      (modulePullback B S hS p).map (modulePullbackUnitIso B S hS f).inv = 𝟙 _ :=
    by rw [← Functor.map_comp, Iso.hom_inv_id]; exact (modulePullback B S hS p).map_id _
  refine Eq.trans ?_ (congrArg (fun m => m ≫ (modulePullbackUnitIso B S hS p).inv ≫
    (modulePullback B S hS p).map (modulePullbackUnitIso B S hS f).inv) h.symm)
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine (congrArg (fun m => _ ≫ m) (Category.assoc _ _ _)).trans ?_
  refine (congrArg (fun m => _ ≫ _ ≫ m)
    (Iso.hom_inv_id_assoc (modulePullbackUnitIso B S hS p) _)).trans ?_
  exact (congrArg (fun m => _ ≫ m) e).trans (Category.comp_id _)

/-- **Pullback of global sections is functorial.**  A global section `σ : 𝒪_X ⟶ N`, pulled back
along `f` and then along `p`, is its pullback along `k = p ≫ f`, read through the composition
comparison of Stacks 03LU. -/
theorem modulePullbackUnitIso_inv_comp_map_comp {P X' X : AlgebraicSpaces B S hS}
    (p : P ⟶ X') (f : X' ⟶ X) {k : P ⟶ X} (hk : p ≫ f = k) {N : Modules.{u, u} B S hS X.1 X.2}
    (σ : SheafOfModules.unit (structureRingSheaf B S hS X) ⟶ N) :
    (modulePullbackUnitIso B S hS p).inv ≫ (modulePullback B S hS p).map
        ((modulePullbackUnitIso B S hS f).inv ≫ (modulePullback B S hS f).map σ) =
      ((modulePullbackUnitIso B S hS k).inv ≫ (modulePullback B S hS k).map σ) ≫
        (modulePullbackTriangle B S hS hk).hom.app N := by
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine (congrArg (fun m => _ ≫ m) ((modulePullbackTriangle B S hS hk).hom.naturality σ)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m => m ≫ _)
    (modulePullbackUnitIso_inv_comp_triangle_hom B S hS p f hk)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (fun m => _ ≫ m) ((modulePullback B S hS p).map_comp _ _).symm

/-- **The inverse images of a global section compose.**  Pulling a global section of `N` back
along `f` and then along `p` is pulling it back along `k = p ≫ f`, read through the composition
comparison of Stacks 03LU. -/
theorem sectionsMap_modulePullbackSections_triangle {P X' X : AlgebraicSpaces B S hS}
    (p : P ⟶ X') (f : X' ⟶ X) {k : P ⟶ X} (hk : p ≫ f = k) (N : Modules.{u, u} B S hS X.1 X.2)
    (σ : N.sections) :
    SheafOfModules.sectionsMap ((modulePullbackTriangle B S hS hk).hom.app N)
        (modulePullbackSections B S hS k N σ) =
      modulePullbackSections B S hS p ((modulePullback B S hS f).obj N)
        (modulePullbackSections B S hS f N σ) := by
  refine (SheafOfModules.unitHomEquiv_comp_apply _ _).symm.trans ?_
  refine congrArg (SheafOfModules.unitHomEquiv _)
    ((modulePullbackUnitIso_inv_comp_map_comp B S hS p f hk _).symm.trans ?_)
  refine congrArg
    (fun m => (modulePullbackUnitIso B S hS p).inv ≫ (modulePullback B S hS p).map m) ?_
  exact ((SheafOfModules.unitHomEquiv _).symm_apply_apply _).symm

end AlgebraicGeometry.Space

end
