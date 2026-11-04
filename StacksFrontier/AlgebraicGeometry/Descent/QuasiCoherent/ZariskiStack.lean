module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiEssSurj

/-!
# Quasi-coherent modules form a stack for the Zariski topology

`Stacks.Descent.qcohPseudofunctor`, the pseudofunctor sending a scheme to its category of
quasi-coherent modules and a morphism of schemes to pullback, is a
`CategoryTheory.Pseudofunctor.IsStack` for `AlgebraicGeometry.Scheme.zariskiTopology`.

This is the stack-shaped form of Stacks 023E, whose two halves are
`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_zariski` and
`Stacks.Descent.isEffective_zariski`.

## Main results

* `Stacks.Descent.essSurj_qcohToDescentData_zariski`: for a family of open immersions whose images
  cover the target, `CategoryTheory.Pseudofunctor.toDescentData` of
  `Stacks.Descent.qcohPseudofunctor` is essentially surjective.
* `Stacks.Descent.isEquivalence_qcohToDescentData_zariski`: that functor is an equivalence.
* `Stacks.Descent.isStack_qcohPseudofunctor`: quasi-coherent modules form a stack for the Zariski
  topology.

## Implementation notes

Essential surjectivity is transported from `Stacks.Descent.isEffective_zariski`, which is stated
for `AlgebraicGeometry.QuasicoherentDescentData`, along
`Stacks.Descent.descentDataForgetFunctor`.  That functor is an equivalence, so it suffices to
produce an isomorphism after applying it, and
`Stacks.Descent.descentDataForgetFunctor_obj_toDescentData` says it carries the canonical descent
datum of `Stacks.Descent.qcohPseudofunctor` to the canonical descent datum of Stacks 023D; the
preimage of the resulting isomorphism is taken with
`CategoryTheory.Functor.FullyFaithful.preimageIso`.  The two descent data are *definitionally*
equal, but identifications in this area are stated and then used, never left to unification, so
the equality is inserted as a `CategoryTheory.eqToIso`.

The stack condition itself is obtained from
`CategoryTheory.Pseudofunctor.IsStack.of_precoverage`, exactly as the prestack condition
`Stacks.Descent.isPrestack_qcohPseudofunctor` is: the Zariski precoverage has `HasIsos`,
`IsStableUnderBaseChange` and `IsStableUnderComposition`, so it is enough to check the condition
for the presieves of the precoverage, where
`Stacks.Descent.isOpenImmersion_of_mem_zariskiPrecoverage` and
`Stacks.Descent.iSup_opensRange_eq_top_of_mem_zariskiPrecoverage` supply the hypotheses of
Stacks 023E.

No `@[stacks 023E]` attribute is placed here.  Both halves of 023E already carry it, on
`Stacks.Descent.nonempty_fullyFaithful_canonicalDescentFunctor_zariski` and
`Stacks.Descent.isEffective_zariski`; these declarations only repackage them.

## References

* [Stacks Project, Tag 023E](https://stacks.math.columbia.edu/tag/023E)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Opposite

universe v u

namespace Stacks.Descent

variable {I : Type v} {S : Scheme.{u}} {Y : I → Scheme.{u}}

/-- Forgetting quasi-coherence from the components of a descent datum is fully faithful. -/
noncomputable def descentDataForgetFullyFaithful (f : ∀ i, Y i ⟶ S) :
    (descentDataForgetFunctor (f := f)).FullyFaithful :=
  .ofFullyFaithful _

/-- **Essential surjectivity of the descent functor of `Stacks.Descent.qcohPseudofunctor` for a
Zariski covering family.**  This is the effectivity half of Stacks 023E,
`Stacks.Descent.isEffective_zariski`, for `Stacks.Descent.qcohPseudofunctor`. -/
theorem essSurj_qcohToDescentData_zariski (f : ∀ i, Y i ⟶ S) [∀ i, IsOpenImmersion (f i)]
    (hf : ⨆ i, (f i).opensRange = ⊤) :
    (qcohPseudofunctor.toDescentData f).EssSurj where
  mem_essImage D := by
    obtain ⟨M, ⟨e⟩⟩ := isEffective_zariski f hf (descentDataForgetFunctor.obj D)
    exact ⟨M, ⟨(descentDataForgetFullyFaithful f).preimageIso
      (eqToIso (descentDataForgetFunctor_obj_toDescentData M) ≪≫ e)⟩⟩

/-- **The descent functor of `Stacks.Descent.qcohPseudofunctor` is an equivalence for a Zariski
covering family**, which is both halves of Stacks 023E at once. -/
theorem isEquivalence_qcohToDescentData_zariski (f : ∀ i, Y i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hf : ⨆ i, (f i).opensRange = ⊤) :
    (qcohPseudofunctor.toDescentData f).IsEquivalence := by
  obtain ⟨hff⟩ := nonempty_fullyFaithful_qcohToDescentData hf
  have := essSurj_qcohToDescentData_zariski f hf
  exact { faithful := hff.faithful, full := hff.full }

/-- **Quasi-coherent modules form a stack for the Zariski topology**, Stacks 023E in the form of
`CategoryTheory.Pseudofunctor.IsStack`.  It does **not** bear on Stacks 023T, whose hypothesis is
an fpqc covering family: the comparison
`AlgebraicGeometry.Scheme.zariskiPrecoverage_le_fpqcPrecoverage` runs the wrong way for that. -/
instance isStack_qcohPseudofunctor :
    qcohPseudofunctor.{u}.IsStack Scheme.zariskiTopology.{u} :=
  Pseudofunctor.IsStack.of_precoverage (J := Scheme.zariskiPrecoverage.{u}) fun _ R hR ↦ by
    obtain ⟨_, _, f, rfl⟩ := R.exists_eq_ofArrows
    have : ∀ i, IsOpenImmersion (f i) := isOpenImmersion_of_mem_zariskiPrecoverage hR
    rw [Pseudofunctor.isStackFor_ofArrows_iff]
    exact isEquivalence_qcohToDescentData_zariski f
      (iSup_opensRange_eq_top_of_mem_zariskiPrecoverage hR)

end Stacks.Descent

end

end
