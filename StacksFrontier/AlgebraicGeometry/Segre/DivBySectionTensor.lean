module

public import StacksFrontier.AlgebraicGeometry.SectionDivision.Basic
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Multiplication
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors

/-!
# The ratio of two tensor sections is the product of the two ratios

For invertible modules `F`, `G` on a ringed space with local stalks and global sections
`sF, tF` of `F` and `sG, tG` of `G`, the quotient of `tF ⊗ tG` by `sF ⊗ sG`
(`Stacks.SheafOfModules.divBySection`) is the product `(tF / sF) · (tG / sG)` on any open where
both denominators are nonvanishing.

This is the computation the chart description of the Segre morphism needs: the Segre sections are
the tensors `XᵢYⱼ` of pulled-back homogeneous coordinates, and
`Stacks.ProjectiveSpaceSections.chartRatio` of two of them is therefore the product of a ratio of
`Xᵢ`'s and a ratio of `Yⱼ`'s.

The proof is the uniqueness clause `Stacks.SheafOfModules.divBySection_eq_of_smul_eq` applied to
the explicit witness: `((tF/sF)·(tG/sG)) • (sF ⊗ sG) = ((tF/sF) • sF) ⊗ ((tG/sG) • sG)` because
`toTensorSheafSection` is linear and because scalars move across an elementary tensor, and each
factor is then the defining property of its own quotient.

## Main results

* `Stacks.SheafOfModules.le_nonvanishingOpen_tensorSections`: an open on which two sections are
  nonvanishing is one on which their tensor is nonvanishing (a corollary of
  `Stacks.SheafOfModules.nonvanishingLocus_tensorSections`).
* `Stacks.SheafOfModules.divBySection_tensorSections`: **`(tF ⊗ tG) / (sF ⊗ sG)
  = (tF / sF) · (tG / sG)`.**

## Implementation notes

The file lives under `Segre/` because that is where its consumer is; it is generic and could equally
live beside `StacksFrontier/AlgebraicGeometry/SectionDivision/Basic.lean`.

`Stacks.SheafOfModules.tensorSections_eval` is an `rfl` lemma, so the two sides of the witness
computation are stated directly in terms of
  `Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection`, whose bilinearity on pure
tensors is `Stacks.Cohomology.Generators.toTensorSheafSection_smul_left` and
`Stacks.Cohomology.Generators.toTensorSheafSection_smul_right`. Those two state the scalar action
on the image at the native `Stacks.SheafOfModules.Tensor.ringSheaf` seating, which is
definitionally but not syntactically the `Γ(X, V)`-action the quotient's defining property
carries, so the last step of the proof is `rfl` rather than a rewrite.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  (F G : _root_.SheafOfModules.{u} (structureSheafRing X))
  [IsInvertible X.presheaf (structureSheafRing X).property F]
  [IsInvertible X.presheaf (structureSheafRing X).property G]
  [IsInvertible X.presheaf (structureSheafRing X).property
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
      (G)))]

/-- **An open on which two global sections are nonvanishing is one on which their tensor is
nonvanishing.** This is `Stacks.SheafOfModules.nonvanishingLocus_tensorSections` read as an
inequality of opens. -/
theorem le_nonvanishingOpen_tensorSections (sF : F.sections) (sG : G.sections)
    {V : Opens X.carrier} (hVF : V ≤ nonvanishingOpen F sF)
    (hVG : V ≤ nonvanishingOpen G sG) :
    V ≤ nonvanishingOpen
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
        (G)))
      (tensorSections F G sF sG) := by
  intro x hx
  have h : x ∈ nonvanishingLocus F sF ∩ nonvanishingLocus G sG := ⟨hVF hx, hVG hx⟩
  rwa [← nonvanishingLocus_tensorSections F G sF sG] at h

/-- **The quotient of a tensor of sections by a tensor of sections is the product of the two
quotients**: `(tF ⊗ tG) / (sF ⊗ sG) = (tF / sF) · (tG / sG)`.

No `divBySection` lemma about tensor products existed before this one, and it is what turns the
Segre morphism's chart ratios `Z_{ab} / Z_{ij}` into the products `(X_a/Xᵢ)(Y_b/Yⱼ)`. -/
theorem divBySection_tensorSections (sF tF : F.sections) (sG tG : G.sections)
    {V : Opens X.carrier} (hVF : V ≤ nonvanishingOpen F sF)
    (hVG : V ≤ nonvanishingOpen G sG) :
    divBySection
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj
        (G))) (tensorSections F G sF sG)
        (le_nonvanishingOpen_tensorSections F G sF sG hVF hVG)
        ((tensorSections F G tF tG).eval (op V))
      = divBySection F sF hVF (tF.eval (op V)) * divBySection G sG hVG (tG.eval (op V)) := by
  refine divBySection_eq_of_smul_eq _ _ _ ?_
  rw [tensorSections_eval, tensorSections_eval]
  conv_rhs => rw [← smul_divBySection F sF hVF (tF.eval (op V)),
    ← smul_divBySection G sG hVG (tG.eval (op V)),
    Stacks.Cohomology.Generators.toTensorSheafSection_smul_left,
    Stacks.Cohomology.Generators.toTensorSheafSection_smul_right]
  rw [mul_smul]
  -- The two sides now differ only in the scalar-action instance: the native bilinearity lemmas
  -- seat it at `Tensor.ringSheaf`, the quotient's defining property at `Γ(X, V)`. `rfl` identifies
  -- them at default transparency, which `rw`'s closing `rfl` does not reach.
  exact rfl

end Stacks.SheafOfModules

end
