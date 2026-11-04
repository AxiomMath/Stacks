module

public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyIResolutionQuasiIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.ResolutionFiltration
public import StacksCore.Tactic.StacksAttribute

/-! # Property-(I) resolutions exist

Let `(A, d)` be a differential graded algebra and `M` a right differential graded `A`-module.
Stacks 09KU asserts that there is a homomorphism `M ⟶ I` of differential graded `A`-modules
which is a quasi-isomorphism and whose target has property (I). This file assembles that
statement from the two halves proved in the two files it imports:

* `DifferentialGradedModule.quasiIso_resolutionAug`
  (`StacksFrontier/Algebra/DifferentialGraded/Module/PropertyIResolutionQuasiIso.lean`): the
  augmentation `M ⟶ I` into the totalization `I = ∏_{j ≥ 0} Iⱼ[-j]` of the resolution tower of
  Stacks 09KT is a quasi-isomorphism;
* `DifferentialGradedModule.resolutionPropertyIFiltration`
  (`StacksFrontier/Algebra/DifferentialGraded/Module/ResolutionFiltration.lean`): that totalization
  carries a property-(I) filtration.

So the witness of the existential is the quadruple `resolutionTotal M`, `resolutionAug M`,
`quasiIso_resolutionAug M`, `resolutionPropertyIFiltration M`, and the tag of Stacks 09KU is
placed here, on the single theorem that is the lemma's statement.

## Main results

* `DifferentialGradedModule.exists_propertyI_resolution`: Stacks 09KU.

## Implementation notes

*The shape is the consumer's and the mirror's.* The existential is stated with its second
conjunct as `Nonempty (PropertyIFiltration I)`, which is both how
`DifferentialGradedModule.DerivedHomData.ofPropertyIResolutions` takes its hypothesis and how
the mirror statement on the left, `DifferentialGradedModule.exists_propertyP_resolution`
(Stacks 09KP), is phrased. `PropertyIFiltration` is data, and "`I` has property (I)" is the
assertion that some such datum exists; the `Nonempty` is that assertion and nothing is lost by
it, since no consumer needs a *chosen* filtration and no statement here is natural in one.

The variant whose second conjunct is instead right-orthogonality of the class of `I` in
`K(A, d)` to the acyclic modules — the shape consumed by
`DifferentialGradedModule.exists_trW_rightOrthogonal_of_exists_quasiIso_rightOrthogonal` — is
obtained from this one by composing with Stacks 09KS, which is
`DifferentialGradedModule.exists_quasiIso_rightOrthogonal_acyclic_of_propertyI_resolutions`.

## References

* [Stacks Project, Tag 09KU](https://stacks.math.columbia.edu/tag/09KU)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DifferentialGradedModule

universe u

variable {R : Type u} [CommRing R]

/-- **Property-(I) resolutions exist** (Tag 09KU). Every right differential graded module `M`
over a differential graded algebra `(A, d)` admits a quasi-isomorphism into a differential
graded `A`-module `I` carrying a property-(I) filtration: an exhaustive decreasing filtration by
differential graded submodules with admissible inclusions whose successive quotients are
products of shifts of the graded dual `A^∨`.

The resolution is the one of the Stacks proof: `I` is the totalization
`∏_{j ≥ 0} Iⱼ[-j]` of the tower `I₀ → I₁ → ⋯` built from Stacks 09KT, and the map is its
augmentation. -/
@[stacks 09KU]
theorem exists_propertyI_resolution (A : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule A) :
    ∃ (I : DifferentialGradedModule A) (f : M ⟶ I),
      QuasiIso ((forgetToCochainComplex A).map f) ∧ Nonempty (PropertyIFiltration I) :=
  ⟨resolutionTotal M, resolutionAug M, quasiIso_resolutionAug M,
    ⟨resolutionPropertyIFiltration M⟩⟩

end DifferentialGradedModule

end
