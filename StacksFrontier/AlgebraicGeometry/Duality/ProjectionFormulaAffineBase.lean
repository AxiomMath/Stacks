module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAffineCokernel
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic

/-!
# The projection formula for an affine morphism over an affine base

Let `h : T ⟶ S` be an affine morphism of schemes, `G` a quasi-coherent `𝒪_T`-module and `H` a
quasi-coherent `𝒪_S`-module.  Stacks Tag 0FZE asserts that the projection-formula morphism of
`StacksFrontier.AlgebraicGeometry.Duality.AffineProjectionFormula`,

`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)`,

is invertible.  `StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAffineCokernel` proves
this when `H` is isomorphic to the cokernel of a morphism between two coproducts of copies of
`𝒪_S`.  A quasi-coherent module on a general scheme has no such *global* presentation — on
`ℙ¹` the module `𝒪(-1)` has no nonzero global section at all, so it is not even a quotient of a
free module — but on an affine scheme it does, by the module-theoretic presentation of its
module of global sections.

This file supplies that step and so proves Stacks 0FZE **for an affine base**.

## Main results

All three are in the namespace `Stacks.AlgebraicGeometry.ProjectionFormula`.

* `isIso_projectionFormulaMap_of_presentation`: the projection formula for an affine morphism,
  a quasi-coherent `G`, and a module on the target carrying a
  `CategoryTheory.SheafOfModules.Presentation`.
* `nonempty_presentation_of_isAffine`: a quasi-coherent module on an affine scheme has a global
  presentation.
* `isIso_projectionFormulaMap_of_isAffine`: **Stacks 0FZE for an affine base.**  For an affine
  morphism `h : T ⟶ S` with `S` affine and quasi-coherent `G` and `H`, the projection-formula
  morphism is invertible.

## Implementation notes

`SheafOfModules.Presentation` records a family of generating sections together with generators
of the kernel of the resulting epimorphism from a free module; `Presentation.isColimit` turns
that data into an explicit colimit cocone exhibiting the module as the cokernel of a morphism
`free P.relations.I ⟶ free P.generators.I`.  That is exactly the shape consumed by
`isIso_projectionFormulaMap_of_freePresentation_of_isAffineHom`, once the two free modules are
presented as coproducts of copies of `𝒪_S` by `SheafOfModules.isColimitFreeCofan` and the
cokernel of the structural morphism is identified with the module by
`CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso`.

The global presentation on an affine base is
`Stacks.AlgebraicGeometry.AffinePushforward.nonempty_presentation_of_isoSpec`, which is stated
for `AlgebraicGeometry.Scheme.Modules` — that is, for sheaves of modules over
`AlgebraicGeometry.Scheme.ringCatSheaf` rather than over
`structureSheafRing` of the underlying ringed space.  The two sheaves of
rings agree, so the quasi-coherence hypothesis crosses the two spellings when it is passed
positionally; as elsewhere in this development every quasi-coherence hypothesis is therefore an
*explicit* argument rather than an instance, since instance search does not cross it.

**What remains for Stacks 0FZE in general, after this file.**  Exactly one thing: the statement
must be made local on `S`.  Invertibility itself is already known to be local —
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict` reduces it to the
restrictions to the members of an open covering — and the covering to use is the affine opens of
`S`, over which this file applies.  What is missing is the identification of the restriction of
the projection-formula morphism to an open `V ⊆ S` with the projection-formula morphism of the
restricted morphism `h ∣_ V : h ⁻¹ᵁ V ⟶ V`.

Three of the four ingredients of that identification are available.  The base-change
transformation `V.ι ^* ∘ h _* ⟶ (h ∣_ V) _* ∘ (h ⁻¹ᵁ V).ι ^*` of the restriction square is an
isomorphism at every module, by
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_baseChangeNatTrans_restrictSquare`, proved there
as the mate of `Stacks.AlgebraicGeometry.AffinePushforward.pushforwardSquareIso` with the mate
calculus of `Stacks.CategoryTheory.mateEquiv_symm_congr_left`; restriction along an open immersion
is an inverse image by `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, so it carries
tensor products to tensor products by Tag 01CD (`Stacks.RingedSpace.comparisonNatTrans_isIso`); and
inverse images compose, with `AlgebraicGeometry.Scheme.Modules.pullbackComp` and its mate
compatibility `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`.

The fourth ingredient named here — compatibility of `Stacks.RingedSpace.comparison` with
*composition* — turned out **not to be needed**, and this paragraph is withdrawn.  Stacks 0FZE is
proved in `StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal` as
`Stacks.AlgebraicGeometry.ProjectionFormula.isIso_projectionFormulaMap`, with no hypothesis on the
base: `projectionFormulaMap_unique` pins the morphism by its effect on sections, so no mate
calculus is required, and the affine-open step is `isIso_projectionFormulaMap_restrict`.

## References

* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace Stacks.AlgebraicGeometry.ProjectionFormula

open RingedSpaceModuleAdjunction

universe u

variable {T S : Scheme.{u}} (h : T ⟶ S)

/-! ### The projection formula at a presented module -/

/-- **The projection formula for an affine morphism and a presented module.**  Let `h : T ⟶ S`
be an affine morphism of schemes, `G` a quasi-coherent `𝒪_T`-module, and `H` an `𝒪_S`-module
equipped with a presentation, i.e. with a family of generating sections together with
generators of the relations between them.  Then the projection-formula morphism
`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)` is invertible.

A presentation exhibits `H` as the cokernel of a morphism between two free modules, which is the
case proved in
`StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaAffineCokernel`. -/
lemma isIso_projectionFormulaMap_of_presentation [IsAffineHom h]
    {G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)} (hG : G.IsQuasicoherent)
    {H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (P : H.Presentation) :
    IsIso (projectionFormulaMap h G H) :=
  isIso_projectionFormulaMap_of_freePresentation_of_isAffineHom h hG
    (SheafOfModules.freeCofan P.relations.I) (SheafOfModules.isColimitFreeCofan _)
    (SheafOfModules.freeCofan P.generators.I) (SheafOfModules.isColimitFreeCofan _)
    ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π)
    ((colimit.isColimit (parallelPair
      ((SheafOfModules.freeHomEquiv _).symm P.relations.s ≫ kernel.ι P.generators.π)
      0)).coconePointUniqueUpToIso P.isColimit)

/-! ### The global presentation on an affine base -/

/-- A quasi-coherent module on an affine scheme has a global presentation: its module of global
sections has one, and the tilde construction carries it over. -/
lemma nonempty_presentation_of_isAffine [IsAffine S]
    {H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (hH : H.IsQuasicoherent) :
    Nonempty H.Presentation :=
  have : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) H := hH
  AffinePushforward.nonempty_presentation_of_isoSpec S.isoSpec H

/-! ### Stacks 0FZE over an affine base -/

/-- **Stacks Project, Tag 0FZE, for an affine base.**  Let `h : T ⟶ S` be an affine morphism of
schemes with `S` affine, let `G` be a quasi-coherent `𝒪_T`-module and `H` a quasi-coherent
`𝒪_S`-module.  Then the projection-formula morphism
`h_*G ⊗_{𝒪_S} H ⟶ h_*(G ⊗_{𝒪_T} h^*H)` is invertible.

The affineness of `S` is used only to produce a global presentation of `H`; the general case of
the tag is this statement made local on `S`. -/
theorem isIso_projectionFormulaMap_of_isAffine [IsAffine S] [IsAffineHom h]
    {G : SheafOfModules.{u} (structureSheafRing T.toRingedSpace)} (hG : G.IsQuasicoherent)
    {H : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)} (hH : H.IsQuasicoherent) :
    IsIso (projectionFormulaMap h G H) :=
  (nonempty_presentation_of_isAffine hH).elim
    (isIso_projectionFormulaMap_of_presentation h hG)

end Stacks.AlgebraicGeometry.ProjectionFormula

end
