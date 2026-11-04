module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Bundle
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic

/-!
# The projective bundle of a quasi-coherent module has separated structure morphism

`Stacks.SymGraded.isSeparated_schemeProjectiveBundleToBase` of
`StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Bundle` proves that `P(E) ⟶ X` is
separated, but carries the hypothesis `Stacks.SymGraded.IsQuasicoherentPieces E` as an explicit
argument. Tag 01OD states the assertion for a module that is merely quasi-coherent, with no such
hypothesis.

`Stacks.SymGraded.isQuasicoherentPieces_of_isQuasicoherent` of
`StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic` discharges that hypothesis for a
quasi-coherent module on an arbitrary scheme. This file feeds it in, so that the bundle and the
assertion are both stated under `[E.IsQuasicoherent]` alone.

## Main results

* `Stacks.SymGraded.isSeparated_projectiveBundleToBase`: the structure morphism of that bundle
  is separated. This is the whole of Tag 01OD.

## Implementation notes

There is no proof here. `Stacks.SymGraded.IsQuasicoherentPieces` is a `Prop`, so by definitional
proof irrelevance the bundle built from the discharged hypothesis is the same term as the bundle
built from any other proof of it, and the result below is its conditional form applied to
`isQuasicoherentPieces_of_isQuasicoherent E`.

The bundle is written out as
`Stacks.SymGraded.schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)` rather
than abbreviated behind a new definition, so that the statement mentions exactly the library's
`schemeProjectiveBundle` and needs no further unfolding.

`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra` is the degreewise sheafification of the
*sectionwise* symmetric algebra, and **it does satisfy the symmetric algebra's universal
property on an arbitrary scheme**: `SheafOfModules.GradedAlgebra.IsSymmetricAlgebra` for
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebraGen` is
`AlgebraicGeometry.Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme`, proved for
every scheme and every module sheaf on it, with no affineness and no quasi-coherence. So the
bundle this file speaks about is pinned both by its construction and by a global universal
property.

Two earlier claims in this note were wrong and are withdrawn. That universal property is **not**
an assertion of Tag 01CG: Tag 01CG is Lemma 17.21.1, whose two assertions are that `⋀ⁿ F` and
`Symⁿ F` are the sheafifications of `U ↦ ⋀ⁿ_{𝒪(U)}(F(U))` and `U ↦ Symⁿ_{𝒪(U)}(F(U))`, and they
are `SheafOfModules.exteriorPower_isSheafification` and
`SheafOfModules.symmetricPower_isSheafification`, which carry the tag between them. (The phrase
"the third assertion of Tag 01CG" in those two modules names the third *conjunct* of their own
existential statement — the sheafification clause — not a third assertion of the source.) And
`Stacks.SymGraded.isSymmetricAlgebra_qcoh` of
`StacksFrontier.AlgebraicGeometry.SheafSymmetricAlgebra.Qcoh` is not the affine case of it: it is
the universal property of `Stacks.SymGraded.symAlgebra (globalSections E)`, the symmetric algebra
of the `R`-module `Γ(E)`, a different graded algebra from `Scheme.Modules.symmetricAlgebra`.

## References

* [Stacks Project, Tag 01OD](https://stacks.math.columbia.edu/tag/01OD)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Stacks.SymGraded

universe u

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent]

/-- **The structure morphism of the projective bundle of a quasi-coherent module on an arbitrary
scheme is separated.**

This is `Stacks.SymGraded.isSeparated_schemeProjectiveBundleToBase` with its quasi-coherence
hypothesis discharged, and it is the single assertion of Tag 01OD. -/
@[stacks 01OD]
public theorem isSeparated_projectiveBundleToBase :
    IsSeparated
      (schemeProjectiveBundle E (isQuasicoherentPieces_of_isQuasicoherent E)).toBase :=
  isSeparated_schemeProjectiveBundleToBase E (isQuasicoherentPieces_of_isQuasicoherent E)

end Stacks.SymGraded

end
