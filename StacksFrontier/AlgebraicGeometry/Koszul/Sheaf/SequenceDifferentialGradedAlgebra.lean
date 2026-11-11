module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.DifferentialGradedAlgebra
public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.SheafCondition
public import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul complex on a finite family of global sections, as a sheaf of DGAs

Let `X` be a ringed space and let `f₁, …, f_r ∈ Γ(X, O_X)`. Stacks tag 062L defines the Koszul
complex `K_•(O_X, f₁, …, f_r)` to be the Koszul complex, in the sense of Stacks tag 062K,
associated to the map `(f₁, …, f_r) : O_X^{⊕ r} → O_X`. This file forms exactly that instance of
`SheafOfModules.ringedSpaceKoszulDifferentialGradedAlgebra`, the 062K construction on a ringed
space.

## Main definitions

* `Stacks.AlgebraicGeometry.SeqKoszul.freeSheaf`: the free sheaf of modules `O_X^{⊕ r}`, whose
  sections over `U` are the `r`-tuples of sections of `O_X` over `U`.
* `Stacks.AlgebraicGeometry.SeqKoszul.functional`: the map `(f₁, …, f_r) : O_X^{⊕ r} → O_X`.
* `Stacks.AlgebraicGeometry.SeqKoszul.koszulDifferentialGradedAlgebra`:
  **`K_•(O_X, f₁, …, f_r)`**, the Koszul complex of that map, as a sheaf of differential graded
  algebras.

## Main results

* `PresheafOfModules.isSheaf_finFree`: the free presheaf of modules of rank `r` on a ringed space
  is a sheaf.
* `Stacks.AlgebraicGeometry.SeqKoszul.functional_dual_apply`: over an open `U` the functional
  sends `v` to `∑ i, vᵢ · fᵢ|_U`.
* `Stacks.AlgebraicGeometry.SeqKoszul.koszulDifferentialGradedAlgebra_d_exteriorGenerator`: the
  differential takes a degree-one local section `v` of `O_X^{⊕ r}` to `∑ i, vᵢ · fᵢ|_U`.

## References

* [Stacks Project, Tag 062L](https://stacks.math.columbia.edu/tag/062L)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace PresheafOfModules

/-- **The free presheaf of modules of rank `r` on a ringed space is a sheaf.** Its sections over
`U` are `r`-tuples of sections of `O_X` over `U`, with the standard basis, which restriction
preserves. -/
theorem isSheaf_finFree (X : RingedSpace.{u, u}) (r : ℕ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (finFree X.presheaf r).presheaf :=
  isSheaf_of_basis X _ (finFreeBasis X.presheaf r) fun g k => by
    rw [finFreeBasis_apply, finFreeBasis_apply, map_finFreeSingle]

end PresheafOfModules

namespace Stacks.AlgebraicGeometry.SeqKoszul

variable (X : RingedSpace.{u, u}) (r : ℕ)

/-- **The free sheaf of modules `O_X^{⊕ r}`** on a ringed space: the sheaf of `r`-tuples of
sections of the structure sheaf. -/
noncomputable def freeSheaf : SheafOfModules.{u} (structureSheafRing X) where
  val := PresheafOfModules.finFree X.presheaf r
  isSheaf := PresheafOfModules.isSheaf_finFree X r

/-- The underlying presheaf of modules of `freeSheaf X r` is `PresheafOfModules.finFree`. -/
@[simp]
theorem freeSheaf_val : (freeSheaf X r).val = PresheafOfModules.finFree X.presheaf r := rfl

variable {r} (f : Fin r → X.presheaf.obj (op (⊤ : Opens X)))

/-- **The map `(f₁, …, f_r) : O_X^{⊕ r} → O_X`** attached to a family of global sections, as a
functional on the free sheaf of modules of rank `r`. -/
noncomputable def functional :
    PresheafOfModules.ExteriorFunctional.{u, u, u, u} (freeSheaf X r).val :=
  PresheafOfModules.seqExteriorFunctional (PresheafOfModules.Sequence.ofRingedSpace X f)

/-- Over an open `U`, the functional `(f₁, …, f_r)` sends a tuple `v` of sections over `U` to
`∑ i, vᵢ · fᵢ|_U`. -/
theorem functional_dual_apply (U : (Opens X)ᵒᵖ) (v : (freeSheaf X r).val.obj U) :
    (functional X f).dual U v =
      ∑ i, v i *
        ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map
          (homOfLE (le_top : U.unop ≤ ⊤)).op).hom (f i) := by
  rw [functional, PresheafOfModules.seqExteriorFunctional_dual]
  exact Koszul.seqDual_apply _ _

/-- **The Koszul complex `K_•(O_X, f₁, …, f_r)` on a family of global sections of a ringed
space**: the Koszul complex of Stacks tag 062K associated to the map
`(f₁, …, f_r) : O_X^{⊕ r} → O_X`, as a sheaf of differential graded algebras. Its underlying
graded algebra is the exterior algebra `⋀(O_X^{⊕ r})`, and its differential is the unique
derivation taking a local section `v` of `O_X^{⊕ r}` to `∑ i, vᵢ fᵢ`
(`koszulDifferentialGradedAlgebra_d_exteriorGenerator`,
`SheafOfModules.existsUnique_koszulDerivation`). -/
@[stacks 062L "the Koszul complex of 062K at `(f₁, …, f_r) : O_X^{⊕ r} → O_X`, as a sheaf of \
differential graded algebras; `sheafComplex` is its chain complex of sectionwise exterior powers"]
noncomputable def koszulDifferentialGradedAlgebra :
    SheafOfModules.DifferentialGradedAlgebra.{u, u} (structureSheafRing X) :=
  SheafOfModules.ringedSpaceKoszulDifferentialGradedAlgebra X (freeSheaf X r) (functional X f)

/-- `K_•(O_X, f₁, …, f_r)` is the Koszul DGA of 062K at the free sheaf of rank `r` and the
functional `(f₁, …, f_r)`. -/
theorem koszulDifferentialGradedAlgebra_eq :
    koszulDifferentialGradedAlgebra X f =
      SheafOfModules.koszulDifferentialGradedAlgebra (Opens.grothendieckTopology X)
        (freeSheaf X r) (functional X f) := rfl

/-- **The differential of `K_•(O_X, f₁, …, f_r)` on degree-one sections**: out of degree `-1`,
the exterior piece of degree one, it takes a local section `v` of `O_X^{⊕ r}` to
`∑ i, vᵢ · fᵢ|_U`. -/
theorem koszulDifferentialGradedAlgebra_d_exteriorGenerator (U : (Opens X)ᵒᵖ)
    (v : (freeSheaf X r).val.obj U) :
    (SheafOfModules.sheafifiedExteriorPieceZeroIso (Opens.grothendieckTopology X)
          (freeSheaf X r)).hom.val.app U
        (((koszulDifferentialGradedAlgebra X f).complex.d (-1) 0).val.app U
          ((SheafOfModules.sheafifiedExteriorGenerator (Opens.grothendieckTopology X)
            (freeSheaf X r)).val.app U v)) =
      ∑ i, v i *
        ((X.presheaf ⋙ forget₂ CommRingCat RingCat).map
          (homOfLE (le_top : U.unop ≤ ⊤)).op).hom (f i) := by
  rw [← functional_dual_apply]
  exact SheafOfModules.koszulDifferentialGradedAlgebra_d_exteriorGenerator _ _ _ U v

end Stacks.AlgebraicGeometry.SeqKoszul

end
