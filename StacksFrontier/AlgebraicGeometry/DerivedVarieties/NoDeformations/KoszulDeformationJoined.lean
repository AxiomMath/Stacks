module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.LiftedKoszul
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.KoszulFreeLift

/-!
# A flat local deformation of a Koszul complex is a Koszul complex

Let `R → A` be a flat local homomorphism of local rings, essentially of finite presentation, and
let `K` be a perfect object of `D(A)` whose derived restriction to the closed fibre
`A / 𝔪_R A` is the Koszul complex of a regular sequence `f̄₁, …, f̄_r` — that is, let
`AlgebraicGeometry.FlatLocalKoszulDeformationSituation` be given. This file joins the two halves
of the proof of [Stacks, Tag 0G0N] already available in the library and concludes that `K` itself
is the Koszul complex of a sequence lifting `f̄`.

## Main results

* `AlgebraicGeometry.exists_koszulDescription_of_fibrewise_koszul`: there is a sequence
  `f₁, …, f_r` in `A` reducing to `f̄₁, …, f̄_r` on the closed fibre with
  `K ≅ K(A; f₁, …, f_r)` in `D(A)`.

## Implementation notes

Both halves are already proved. `AlgebraicGeometry.exists_finiteFree_lift_of_fibrewise_koszul`
produces a finite free representative `P` of `K` with the Koszul term ranks, its closed-fibre
identification, and a lift `f` of `f̄` read off the differential `P^{-1} → P^0` in chosen bases;
`AlgebraicGeometry.derivedIso_koszulOfLift` takes exactly that data as hypotheses and concludes
`K ≅ K(A; f)`. So the only content here is the hand-off, and the existential the first produces
is the hypothesis block the second consumes.

This is the form in which Case II of [Stacks, Tag 0G0R] uses [Stacks, Tag 0G0N]: it needs a
Koszul description of the deformed complex, not the auxiliary free representative that produces
it.

No `stacks` attribute is carried here: the covering declaration for [Stacks, Tag 0G0N] is
`AlgebraicGeometry.derivedIso_koszulOfLift`, which already registers the tag, and this statement
adds no mathematics to it.

## References

* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **A flat local deformation of a Koszul complex is a Koszul complex.** In a flat local
deformation situation `R → A` with closed fibre Koszul on the regular sequence `f̄`, there is a
sequence `f` in `A` reducing to `f̄` modulo `𝔪_R A` whose Koszul complex represents the deformed
perfect complex `K` in the derived category of `A`.

This is the conclusion of [Stacks, Tag 0G0N], obtained by feeding the finite free representative
of `AlgebraicGeometry.exists_finiteFree_lift_of_fibrewise_koszul` into
`AlgebraicGeometry.derivedIso_koszulOfLift`. -/
public theorem exists_koszulDescription_of_fibrewise_koszul
    (S : FlatLocalKoszulDeformationSituation.{u}) :
    letI : CommRing S.A := S.commRingA
    ∃ f : Fin S.r → S.A,
      (∀ i, Ideal.Quotient.mk
            (Ideal.map (algebraMap S.R S.A) (IsLocalRing.maximalIdeal S.R)) (f i) =
          S.residueSequence i) ∧
        Nonempty (S.K ≅ DerivedCategory.Q.obj
          ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat)) := by
  let : CommRing S.A := S.commRingA
  obtain ⟨P, f, hPK, hPf, hterms, hpositive, e₀, e₁, hf, hfbar⟩ :=
    exists_finiteFree_lift_of_fibrewise_koszul S
  exact ⟨f, hfbar, derivedIso_koszulOfLift S P f hPK hPf hterms hpositive ⟨e₀, e₁, hf, hfbar⟩⟩

end AlgebraicGeometry

end
