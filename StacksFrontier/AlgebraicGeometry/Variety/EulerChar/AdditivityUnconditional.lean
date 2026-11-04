module

public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CoherentFiniteness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Additivity of the Euler characteristic on a proper scheme over a field, with no hypothesis

For a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of coherent modules on a scheme `X` proper
over a field `k`, `χ(X, ℱ₂) = χ(X, ℱ₁) + χ(X, ℱ₃)`. This is [Stacks, Tag 08AA], and this file
is where it is stated with no hypothesis beyond the source's own.

`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/CoherentFiniteness.lean` carries the same
conclusion against the named `Prop` `AlgebraicGeometry.CohomologyFiniteDimensionalOverField`,
which is [Stacks, Tag 02O6] over a field base. That `Prop` is now a theorem —
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`, the
`cohomologyOverField` spelling of the unconditional
`AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology` — so the hypothesis is
discharged here and the tag is attached to the result.

## Main results

* `AlgebraicGeometry.cohomologyFiniteDimensionalOverField_of_isProper`:
  `AlgebraicGeometry.CohomologyFiniteDimensionalOverField` holds. No hypothesis.
* `AlgebraicGeometry.eulerCharacteristic_add_of_shortExact`: **[Stacks, Tag 08AA]**, the
  additivity of the Euler characteristic along a short exact sequence of coherent modules on a
  scheme proper over a field. No hypothesis.

## Implementation notes

**Why the discharge is not performed in
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/CoherentFiniteness.lean` itself.** The proof of
[Stacks, Tag 02O6] is a large development — Chow's lemma, the dévissage, and the coherence of
the higher direct images under a projective morphism — and importing it into that file enlarges
the import closure of
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/ProperPushforward.lean`, where the elaboration
of the Leray spectral sequence of a morphism of schemes then picks different universe
instantiations and fails. Stating the discharged form in a separate file leaves that closure
alone. The named `Prop` and the conditional statements that still use it, namely the
[Stacks, Tag 0AYS] forms, stay where they are.

**The coherence predicate** is the root `SheafOfModules.IsCoherent` of
`StacksFrontier/Topology/Sheaves/Modules/Coherent.lean`, which is what `F.IsCoherent` means for
`F : X.Modules`,
and which is the predicate both
`AlgebraicGeometry.CohomologyFiniteDimensionalOverField` and
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper` are stated with.

## References

* [Stacks Project, Tag 08AA](https://stacks.math.columbia.edu/tag/08AA)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- **[Stacks, Tag 02O6] over a field base, as the named `Prop`.** For every field `k`, every
scheme `X` proper over `Spec k` and every coherent `𝒪_X`-module `F`, the cohomology `Hⁿ(X, F)`
is a finite-dimensional `k`-vector space. No hypothesis.

This is `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_isProper`, whose
conclusion is the body of the `Prop` at one `k`, `X` and `f`, read at every point of the
quantification. -/
@[sga "4½ Fonctions_L 3.7" "more general"]
public theorem cohomologyFiniteDimensionalOverField :
    CohomologyFiniteDimensionalOverField.{u} := fun k _ _ f hf =>
  have := hf
  forall_finiteDimensional_cohomologyOverField_of_isProper k f


/-- **[Stacks, Tag 08AA].** For a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of coherent
modules on a scheme proper over a field, `χ(X, ℱ₂) = χ(X, ℱ₁) + χ(X, ℱ₃)`.

The finiteness input [Stacks, Tag 02O6], which
`StacksFrontier/AlgebraicGeometry/Variety/EulerChar/CoherentFiniteness.lean` carried as an explicit
hypothesis `hfin : CohomologyFiniteDimensionalOverField`, is supplied here by
`AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`; the vanishing input
[Stacks, Tag 01XJ] is discharged inside
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional'`. -/
@[stacks 08AA, ega "III 2.5.2" "special case"]
public theorem eulerCharacteristic_add_of_shortExact (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsCoherent] [S.X₂.IsCoherent] [S.X₃.IsCoherent] :
    eulerCharacteristic k f S.X₂ =
      eulerCharacteristic k f S.X₁ + eulerCharacteristic k f S.X₃ :=
  eulerCharacteristic_add_of_shortExact_of_finiteDimensional' k f hS
    (fun n _ => finiteDimensional_cohomologyOverField_of_isProper k f S.X₁ n)
    fun n _ => finiteDimensional_cohomologyOverField_of_isProper k f S.X₃ n

end AlgebraicGeometry

end
