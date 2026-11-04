module

public import StacksFrontier.Deformation.ToposThickening.RingedToposLiftDiagramMorphisms
public import StacksFrontier.Deformation.ToposThickening.LiftingObstructionClass
public import StacksFrontier.Deformation.ToposThickening.LiftingMorphismDerivedRhoEquivSupplement
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08UG, clause (1): the obstruction class in `Ext¹_{𝒪₂}(Lg^*NL_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)`

For the general diagram `Deformation.ToposThickening.RingedToposLiftDiagram` of
[Stacks Project, Tag 08UG] this file constructs the canonical class
`RingedToposLiftDiagram.obstructionClass` in `Ext¹_{𝒪₂}(Lg^*NL_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)` and proves that
it vanishes exactly when a morphism `(Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(𝒞'₁), 𝒪'₁)` fitting into (08UH)
compatibly with `ν` exists.

The construction is the source's proof. Moving everything to `𝒞₂`
(`RingedToposLiftDiagram.toFirstOrderLiftDiagram`) turns the lifting problem into the one-site
problem for the homomorphisms `g⁻¹𝒪'₁ ⟶ 𝒪'₂` (`RingedToposLiftDiagram.compatibleLiftEquiv`),
whose obstruction is the class `[ξ]` of Step 1 in
`Ext¹_{g⁻¹𝒪₁}(NL_{g⁻¹𝒪₁/g⁻¹f₁⁻¹𝒪_{ℬ₁}}, 𝒢₂)`
(`Deformation.ToposThickening.FirstOrderLiftDiagram.obstructionClass`). The source then
identifies that group with `Ext¹_{𝒪₂}(Lg^*NL_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)`, through
`g⁻¹NL_{𝒪₁/𝒪_{ℬ₁}} = NL_{g⁻¹𝒪₁/g⁻¹f₁⁻¹𝒪_{ℬ₁}}` (Modules on Sites, Lemma 08TQ) and the flatness of
the degree `0` term; that identification is
`Deformation.ToposThickening.LiftingMorphismDerived.rhoEquiv` (Stacks 0GQ8), read along the
change of base ring `(f₁ ∘ g)⁻¹𝒪_{ℬ₁} ≅ g⁻¹f₁⁻¹𝒪_{ℬ₁}`.

## Main definitions

* `Deformation.ToposThickening.RingedToposLiftDiagram.obstructionClass`: the class of clause (1).

## Main results

* `Deformation.ToposThickening.RingedToposLiftDiagram.obstructionClass_eq_zero_iff`:
  **Stacks 08UG, clause (1)**.

## Implementation notes

`Lg^*` is `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback` (Tag 06YY), which is
constructed at the model `HasDerivedCategory.standard` of the derived categories; the class
therefore lives in that model, and the instance is passed explicitly rather than installed.

The class is a definition with a real body, not an existence statement: it is the class `[ξ]`
of the homomorphism `ξ : ℐ/ℐ² ⟶ 𝒢₂` of Step 1 of the source's proof, carried along canonical
isomorphisms only.

## References

* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 0GQ8](https://stacks.math.columbia.edu/tag/0GQ8)
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)
open Deformation.ToposThickening.InverseImageExtension (invImage)

universe u

namespace Deformation.ToposThickening.RingedToposLiftDiagram

variable {X₁ X₂ B₁ B₂ : RingedTopos.{u, u, u}}
  [X₁.J.HasSheafCompose (forget RingCat.{u})] [X₂.J.HasSheafCompose (forget RingCat.{u})]
  [B₁.J.HasSheafCompose (forget RingCat.{u})] [B₂.J.HasSheafCompose (forget RingCat.{u})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₁.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [B₂.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X₁.J.HasSheafCompose (forget CommRingCat.{u})] [X₂.J.HasSheafCompose (forget CommRingCat.{u})]
  [X₁.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [X₂.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasWeakSheafify X₂.J AddCommGrpCat.{u}] [X₂.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X₁.J AddCommGrpCat.{u}] [X₁.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X₂.J AddCommGrpCat.{u}]
  [HasWeakSheafify X₁.J CommRingCat.{u}] [HasWeakSheafify X₂.J CommRingCat.{u}]
  [X₂.J.WEqualsLocallyBijective CommRingCat.{u}]
  (D : RingedToposLiftDiagram X₁ X₂ B₁ B₂)

/-- **The obstruction class of Stacks 08UG, clause (1)**, an element of
`Ext¹_{𝒪₂}(Lg^*NL_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)`: the class `[ξ]` of Step 1 of the source's proof for the
one-site diagram on `𝒞₂`, an element of `Ext¹_{g⁻¹𝒪₁}(NL_{g⁻¹𝒪₁/g⁻¹f₁⁻¹𝒪_{ℬ₁}}, 𝒢₂)`, read along
the change of base ring `(f₁ ∘ g)⁻¹𝒪_{ℬ₁} ≅ g⁻¹f₁⁻¹𝒪_{ℬ₁}` and the identification of Stacks 0GQ8
of that group with `Ext¹_{𝒪₂}(Lg^*NL_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)`. Here `NL_{𝒪₁/𝒪_{ℬ₁}}` is the naive
cotangent complex of `f₁^♯ : f₁⁻¹𝒪_{ℬ₁} ⟶ 𝒪₁` and `Lg^*` the derived pullback of Tag 06YY. -/
def obstructionClass :
    @DerivedCategory.Ext _ _ _ (HasDerivedCategory.standard _)
      ((Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback D.g).obj
        ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj
          (Stacks.SheafOfModules.naiveCotangentComplex.{u, u, u, u} X₁.J
            ((inverseImageCommRingFunctor D.S₁.f.toToposHom).obj B₁.O) X₁.O
            D.S₁.f.fSharpInverseImage)))
      ((@DerivedCategory.singleFunctor _ _ _ (HasDerivedCategory.standard _) 0).obj D.S₂.G) 1 :=
  letI := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf ((invImage D.g).obj X₁.O)))
  (LiftingMorphismDerived.rhoEquiv (f := D.S₁.f) (G := D.S₂.G) D.g).symm
    (DerivedCategory.Q.map (LiftingMorphismDerived.baseIsoChange (f := D.S₁.f) D.g) ≫
      FirstOrderLiftDiagram.obstructionClass.{u + 1, u, u, u} (toFirstOrderLiftDiagram D)
        (hD := HasDerivedCategory.standard _))

/-- **Stacks Project, Tag 08UG, clause (1).** For the diagram (08UH) of ringed topoi, whose
horizontal arrows are first order thickenings, and a `g⁻¹𝒪₁`-linear map `ν : g⁻¹𝒢₁ ⟶ 𝒢₂` making
(08UI) commute with front and back rows solutions of (08UF), the canonical element
`obstructionClass D` of `Ext¹_{𝒪₂}(Lg^*NL_{𝒪₁/𝒪_{ℬ₁}}, 𝒢₂)` vanishes if and only if there is a
morphism of ringed topoi `(Sh(𝒞'₂), 𝒪'₂) ⟶ (Sh(𝒞'₁), 𝒪'₁)` fitting into (08UH) compatibly
with `ν`. -/
@[stacks 08UG "clause (1) for genuine morphisms of ringed topoi between four arbitrary ringed \
topoi: the canonical class in Ext^1_{O_2}(Lg^*NL_{O_1/O_{B_1}}, G_2), Lg^* the derived pullback \
of 06YY, is zero exactly when a morphism (Sh(C'_2), O'_2) -> (Sh(C'_1), O'_1) fitting into \
(08UH) compatibly with nu exists"]
theorem obstructionClass_eq_zero_iff :
    obstructionClass D = 0 ↔ Nonempty (CompatibleLift D) := by
  rw [obstructionClass, LiftingMorphismDerived.rhoEquiv_symm_eq_zero_iff]
  refine (Preadditive.IsIso.comp_left_eq_zero _ _).trans ?_
  refine (FirstOrderLiftDiagram.obstructionClass_eq_zero_iff (hD := HasDerivedCategory.standard _)
    _).trans ?_
  exact ⟨fun ⟨q⟩ => ⟨(compatibleLiftEquiv D).symm q⟩, fun ⟨p⟩ => ⟨compatibleLiftEquiv D p⟩⟩

end Deformation.ToposThickening.RingedToposLiftDiagram

end
