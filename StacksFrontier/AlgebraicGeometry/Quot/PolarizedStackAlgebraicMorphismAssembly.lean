module

public import StacksFrontier.AlgebraicGeometry.Quot.PicardAmpleOpenLocus
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackAlgebraic
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedPicardEssSurj
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackAlgebraicMorphism
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicMorphismCostructured
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenSubstack

/-!
# The forgetful 1-morphism `Polarized ⟶ Spaces'_{fp, flat, proper}` is algebraic, from its inputs

This file assembles the proof of Stacks 0D41 from the three results it uses which are still held
elsewhere, each taken as an explicit hypothesis in the form of its statement:

* the second assertion of Stacks 0D40, that the polarized families form a stack over the big fppf
  site, which makes `Polarized` a stack in groupoids
  (`AlgebraicGeometry.polarizedStackInGroupoids`);
* Stacks 0D04, that the Picard stack `Picardstack_{X₀/V₀}` of an object `X₀ ⟶ V₀` of
  `Spaces'_{fp, flat, proper}` is an algebraic stack;
* Stacks 0D3D, the open locus of relative ampleness of a proper morphism of algebraic spaces.

The proof is the one of the source. At a scheme-valued point `X₀ ⟶ V₀` of
`Spaces'_{fp, flat, proper}`, the base change of `Polarized` is equivalent over the site to the
category of polarized families over `X₀`
(`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct_of_costructuredArrow`), which is
equivalent over the site to the relatively ample locus of `Picardstack_{X₀/V₀}`
(`AlgebraicGeometry.amplePolarizedFunctor`). That locus is open by Stacks 0D3D
(`AlgebraicGeometry.Space.hasOpenObjectPropertyLocus_picardAmple`), hence an algebraic stack as
`Picardstack_{X₀/V₀}` is by Stacks 0D04
(`AlgebraicGeometry.Stack.isAlgebraicStack_objectPropertySubcategory`).

Nothing here is registered: Stacks 0D41 is the instantiation of
`AlgebraicGeometry.isAlgebraicMorphism_forgetPolarizationBased_of` at the three results once
they are proved.

## Main results

* `AlgebraicGeometry.isAlgebraicMorphism_forgetPolarizationBased_of`: Stacks 0D41 from the
  statements of Stacks 0D40, 0D04 and 0D3D.
* `AlgebraicGeometry.isAlgebraicMorphism_forgetPolarizationBased_of_picard`: the same with
  Stacks 0D40 discharged by `AlgebraicGeometry.polarizedProjection_isStack`.
* `AlgebraicGeometry.isAlgebraicMorphism_forgetPolarizationBased_of_h09DS`: the same with Stacks
  0D04 obtained from the statement of Stacks 09DS, so that the only inputs left are
  Stacks 09DS and Stacks 0D3D.

## References

* [Stacks Project, Tag 0D41](https://stacks.math.columbia.edu/tag/0D41)
* [Stacks Project, Tag 0D40](https://stacks.math.columbia.edu/tag/0D40)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u})

/-- **Stacks 0D41 from its inputs.** Given the second assertion of Stacks 0D40 (`h0D40`), Stacks
0D04 for the Picard stacks of the objects of `Spaces'_{fp, flat, proper}` (`h0D04`) and Stacks
0D3D over the terminal scheme (`h0D3D`), the forgetful 1-morphism of Stacks 0D3Y from `Polarized`
to `Spaces'_{fp, flat, proper}` is algebraic in the sense of Stacks 06CF. -/
theorem isAlgebraicMorphism_forgetPolarizationBased_of
    (h0D40 : (polarizedProjection B).IsStack B.topology)
    (h0D04 : ∀ X₀ : CartesianProperFlatSpaces B integerBase B.contains_integerBase,
      Stack.IsAlgebraicStack.{u, w} B integerBase B.contains_integerBase
        (Space.picardCFG (Space.modulePushforwardCoherence B integerBase B.contains_integerBase)
          (properFlatPicardSituation X₀)).val)
    (h0D3D : ∀ {X Y : AlgebraicSpaces B integerBase B.contains_integerBase} {f : X ⟶ Y},
      Space.IsProper B integerBase B.contains_integerBase f.hom →
      ∀ {L : Space.Modules.{u, u} B integerBase B.contains_integerBase X.1 X.2},
        Space.IsInvertibleModule X L →
        ∃ V : Subfunctor Y.1, Space.IsOpenSubspace B integerBase B.contains_integerBase V ∧
          ∀ ⦃X' Y' : AlgebraicSpaces B integerBase B.contains_integerBase⦄ (g : Y' ⟶ Y)
            (p : X' ⟶ X) (f' : X' ⟶ Y'), IsPullback p f' f g →
              ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
                Space.IsRelativelyAmple B integerBase B.contains_integerBase f'
                  ((Space.modulePullback B integerBase B.contains_integerBase p).obj L))) :
    Stack.IsAlgebraicMorphism.{u, w, w, w} B integerBase B.contains_integerBase
      (𝒳 := polarizedStackInGroupoids.{w} B h0D40)
      (𝒴 := properFlatSpacesStackInGroupoids.{w} B integerBase B.contains_integerBase)
      (forgetPolarizationBased B) := by
  intro U y hy
  let hc := Space.modulePushforwardCoherence B integerBase B.contains_integerBase
  let X₀ := y.obj (Over.mk (𝟙 U.left))
  have hD := Stack.isAlgebraicStack_objectPropertySubcategory B integerBase
    B.contains_integerBase (Space.picardCFG hc (properFlatPicardSituation X₀))
    (Space.picardAmple hc (properFlatPicardSituation X₀)) Space.picardAmple_of_hom
    (Space.hasOpenObjectPropertyLocus_picardAmple hc (properFlatPicardSituation X₀)
      (properFlatCoherentSituation_isProper X₀) h0D3D) (h0D04 X₀)
  exact Stack.isAlgebraicStack_twoFibreProduct_of_costructuredArrow B integerBase
    B.contains_integerBase (polarizedIntegerProjection_isFiberedInGroupoids B)
    (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase B.contains_integerBase)
    (forgetPolarizationBased B) U y hy _ (amplePolarizedFunctor X₀ hc)
    (isEquivalence_amplePolarizedFunctor (X₀ := X₀) (hc := hc))
    (amplePolarizedFunctor_comp_projection X₀ hc) hD

/-- **Stacks 0D41 from Stacks 0D04 and Stacks 0D3D**, with Stacks 0D40
(`AlgebraicGeometry.polarizedProjection_isStack`) discharged. -/
theorem isAlgebraicMorphism_forgetPolarizationBased_of_picard
    (h0D04 : ∀ X₀ : CartesianProperFlatSpaces B integerBase B.contains_integerBase,
      Stack.IsAlgebraicStack.{u, w} B integerBase B.contains_integerBase
        (Space.picardCFG (Space.modulePushforwardCoherence B integerBase B.contains_integerBase)
          (properFlatPicardSituation X₀)).val)
    (h0D3D : ∀ {X Y : AlgebraicSpaces B integerBase B.contains_integerBase} {f : X ⟶ Y},
      Space.IsProper B integerBase B.contains_integerBase f.hom →
      ∀ {L : Space.Modules.{u, u} B integerBase B.contains_integerBase X.1 X.2},
        Space.IsInvertibleModule X L →
        ∃ V : Subfunctor Y.1, Space.IsOpenSubspace B integerBase B.contains_integerBase V ∧
          ∀ ⦃X' Y' : AlgebraicSpaces B integerBase B.contains_integerBase⦄ (g : Y' ⟶ Y)
            (p : X' ⟶ X) (f' : X' ⟶ Y'), IsPullback p f' f g →
              ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
                Space.IsRelativelyAmple B integerBase B.contains_integerBase f'
                  ((Space.modulePullback B integerBase B.contains_integerBase p).obj L))) :
    Stack.IsAlgebraicMorphism.{u, w, w, w} B integerBase B.contains_integerBase
      (𝒳 := polarizedStackInGroupoids.{w} B (polarizedProjection_isStack B))
      (𝒴 := properFlatSpacesStackInGroupoids.{w} B integerBase B.contains_integerBase)
      (forgetPolarizationBased B) :=
  isAlgebraicMorphism_forgetPolarizationBased_of B (polarizedProjection_isStack B) h0D04 h0D3D

/-- **Stacks 0D41 from Stacks 09DS and Stacks 0D3D**, with Stacks 0D40
(`AlgebraicGeometry.polarizedProjection_isStack`) discharged and Stacks 0D04 obtained from
Stacks 09DS by its staged form `AlgebraicGeometry.Space.isAlgebraicStack_picardCFG_of_h09DS`. -/
theorem isAlgebraicMorphism_forgetPolarizationBased_of_h09DS
    (h09DS : ∀ D' : Space.CoherentSituation B integerBase B.contains_integerBase,
      Space.IsSeparated B integerBase B.contains_integerBase D'.f.hom →
        Stack.IsAlgebraicStack.{u, w} B integerBase B.contains_integerBase
          (Space.coherentCFG D').val)
    (h0D3D : ∀ {X Y : AlgebraicSpaces B integerBase B.contains_integerBase} {f : X ⟶ Y},
      Space.IsProper B integerBase B.contains_integerBase f.hom →
      ∀ {L : Space.Modules.{u, u} B integerBase B.contains_integerBase X.1 X.2},
        Space.IsInvertibleModule X L →
        ∃ V : Subfunctor Y.1, Space.IsOpenSubspace B integerBase B.contains_integerBase V ∧
          ∀ ⦃X' Y' : AlgebraicSpaces B integerBase B.contains_integerBase⦄ (g : Y' ⟶ Y)
            (p : X' ⟶ X) (f' : X' ⟶ Y'), IsPullback p f' f g →
              ((∃ l : Y'.1 ⟶ V.toFunctor, l ≫ V.ι = g.hom) ↔
                Space.IsRelativelyAmple B integerBase B.contains_integerBase f'
                  ((Space.modulePullback B integerBase B.contains_integerBase p).obj L))) :
    Stack.IsAlgebraicMorphism.{u, w, w, w} B integerBase B.contains_integerBase
      (𝒳 := polarizedStackInGroupoids.{w} B (polarizedProjection_isStack B))
      (𝒴 := properFlatSpacesStackInGroupoids.{w} B integerBase B.contains_integerBase)
      (forgetPolarizationBased B) :=
  isAlgebraicMorphism_forgetPolarizationBased_of_picard B
    (fun X₀ => Space.isAlgebraicStack_picardCFG_of_h09DS h09DS (properFlatCoherentSituation X₀)
      (properFlatCoherentSituation_isFlat X₀) (properFlatCoherentSituation_isProper X₀)) h0D3D

end AlgebraicGeometry

end
