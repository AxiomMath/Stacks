module

public import StacksFrontier.AlgebraicGeometry.Cohomology.HypercoveringModuleComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.InjectiveModuleSheafAcyclicity

/-!
# The Čech complex of a hypercovering is a resolution of an injective module, in positive degrees

Let `X` be a scheme, let `Y` be an open subset of it and let `K` be a hypercovering of the Zariski
site of `X` with base object `Y`.  For an **injective** sheaf of `𝒪_X`-modules `I` the complex of
sections

`s(I(K)) = ( ∏_{i ∈ I₀} I(U_i) ⟶ ∏_{i ∈ I₁} I(U_i) ⟶ ⋯ )`

has vanishing cohomology in every positive degree.  This is the positive-degree half of
[Stacks, Tag 01GV] for a sheaf of modules rather than for an injective abelian sheaf.

## Main results

* `Stacks.Cohomology.HypercoveringInjective.isZero_rightDerived_sectionsOpens_toSheaf`:
  `H ^q(V, I_ab) = 0` for `q > 0`, for every open `V` of `X` and every injective sheaf of
  `𝒪_X`-modules `I`.
* `Stacks.Cohomology.HypercoveringInjective.isZero_homology_sectionsComplex_toSheaf_of_injective`:
  **the complex of sections of `K` with coefficients in the underlying abelian sheaf of an
  injective sheaf of `𝒪_X`-modules has vanishing cohomology in every positive degree.**
* `Stacks.Cohomology.HypercoveringInjective.exactAt_sectionsComplex_toSheaf_of_injective`:  the
  same statement as exactness of that complex in every nonzero degree.

## Implementation notes

The base object `Y` is arbitrary and no hypothesis is placed on the members of `K`:  in particular
they need not be affine, and the coefficient module need not be quasi-coherent.  This is what
distinguishes the statements here from those of
`StacksFrontier.AlgebraicGeometry.Cohomology.HypercoveringModuleComparison`, where the degeneration
comes from Serre vanishing on an affine open and the base object is `⊤`.

## References

* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite Simplicial TopologicalSpace
open AlgebraicGeometry
open Stacks.CategoryTheory.Hypercovering

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.HypercoveringInjective

/-- **The higher cohomology over an open subset of the underlying abelian sheaf of an injective
sheaf of `𝒪_X`-modules vanishes.**  This is [Stacks, Tag 03FD] on the Zariski site of `X`:  the
underlying abelian sheaf of an injective sheaf of modules is not an injective abelian sheaf, but it
is acyclic. -/
theorem isZero_rightDerived_sectionsOpens_toSheaf (X : Scheme.{u})
    (I : SheafOfModules.{u} X.ringCatSheaf) [Injective I] (V : X.Opens) (q : ℕ) (hq : 0 < q) :
    IsZero (((sheafToPresheaf (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u} ⋙
      (evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op V)).rightDerived q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj I)) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  exact Stacks.Cohomology.InjectiveModuleSheafAcyclicity.isZero_rightDerived_sections_toSheaf_succ
    (Opens.grothendieckTopology ↥X) X.ringCatSheaf I V p

/-- **The complex of sections of a hypercovering with coefficients in the underlying abelian sheaf
of an injective sheaf of `𝒪_X`-modules has vanishing cohomology in every positive degree.** -/
theorem isZero_homology_sectionsComplex_toSheaf_of_injective (X : Scheme.{u}) {Y : X.Opens}
    (K : SimplicialObject (FormalCoproduct.{u} (Over Y)))
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (I : SheafOfModules.{u} X.ringCatSheaf) [Injective I] (i : ℕ) (hi : 0 < i) :
    IsZero (((SectionsOver.sectionsComplexFunctor.{u} (Opens.grothendieckTopology ↥X) K).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj I)).homology i) := by
  have h := isIso_cechToSheafCohomologyOfEq_app.{u} (Opens.pretopology ↥X)
    (Opens.pretopology_toGrothendieck ↥X) Y K hK i
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj I)
    (fun n j q hq ↦ isZero_rightDerived_sectionsOpens_toSheaf X I _ q hq)
  exact IsZero.of_iso (isZero_rightDerived_sectionsOpens_toSheaf X I Y i hi)
    (@asIso _ _ _ _ _ h)

/-- **The complex of sections of a hypercovering with coefficients in the underlying abelian sheaf
of an injective sheaf of `𝒪_X`-modules is exact in every nonzero degree.** -/
theorem exactAt_sectionsComplex_toSheaf_of_injective (X : Scheme.{u}) {Y : X.Opens}
    (K : SimplicialObject (FormalCoproduct.{u} (Over Y)))
    (hK : IsHypercovering (Opens.pretopology ↥X) K)
    (I : SheafOfModules.{u} X.ringCatSheaf) [Injective I] (i : ℕ) (hi : i ≠ 0) :
    ((SectionsOver.sectionsComplexFunctor.{u} (Opens.grothendieckTopology ↥X) K).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj I)).ExactAt i :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
    (isZero_homology_sectionsComplex_toSheaf_of_injective X K hK I i (Nat.pos_of_ne_zero hi))

end Stacks.Cohomology.HypercoveringInjective

end
