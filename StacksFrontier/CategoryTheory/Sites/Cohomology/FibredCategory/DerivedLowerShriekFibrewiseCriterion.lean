module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.DerivedLowerShriekFibreHomologyIso

/-!
# Recognising the morphisms that derived lower shriek inverts, fibre by fibre

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site `(D, O_D)`, as in
the standing data of Stacks 08P8, with small fibres. Stacks 08PJ identifies the degree `n` left
derived functor `L_nπ_!(F) = H^{-n}(Lπ_! F)` of lower shriek with the sheaf `L_n(F)` on the base
associated to the presheaf `V ↦ H_n(C_V, F|_{C_V})` of Stacks 08PI, naturally in the abelian
sheaf `F`
(`Stacks.Sites.FibredCategory.FibredCategorySituation.derivedLowerShriekHomologyIso`).

Because that identification is natural, it turns a question about `L_nπ_!` into a question about
the fibres: `L_nπ_!` inverts a morphism of abelian sheaves on the total category exactly when the
associated sheaf of fibre homology does, and in particular as soon as the morphism induces an
isomorphism on the homology of each fibre. This file records both forms. They are the step
"it suffices to prove the result for the restriction to the fibre categories" by which the
proofs in this chapter — for instance that of Stacks 09D2 — descend a statement about `Lπ_!` to
the fibres.

## Main results

Both live in the namespace `Stacks.Sites.FibredCategory.FibredCategorySituation` and are named
without that prefix here.

* `isIso_derivedAbelianLowerShriekHomology_map_iff`: `L_nπ_!` inverts a morphism of abelian
  sheaves on the total category exactly when the associated sheaf of fibre homology of
  Stacks 08PI does.
* `isIso_derivedAbelianLowerShriekHomology_map_of_fibrewise`: it inverts a morphism that induces
  an isomorphism on the homology of every fibre.

## Implementation notes

Both statements carry the two hypotheses under which Stacks 08PJ is available here: the
acyclicity statement of Stacks 07AC for `π_!` and the acyclicity of the sheafified canonical
presentation by free abelian presheaves on representables. Neither is discharged in the library,
for the reason recorded in
`StacksFrontier/CategoryTheory/Sites/Cohomology/FibredCategory/ProjectionLowerShriek.lean`: the
route through the vanishing of Stacks 0D6X is not available because Stacks 0D6X is open here.
The same namespace's `uliftFreeCoverLowerShriekAcyclic_of_preservesFiniteLimits` discharges the
second whenever lower shriek is exact, so the hypotheses are not vacuous.

The fibrewise hypothesis is phrased with the components of the morphism of presheaves of fibre
homology rather than with `Stacks.CategoryHomology.categoryHomologyMap` directly, so that it
elaborates without the coefficient presheaves having to be spelled out;
`Stacks.Sites.FibredCategory.fiberHomologyPresheafFunctor_map_app` identifies the component at
`V` with the map `H_n(C_V, F|_{C_V}) ⟶ H_n(C_V, G|_{C_V})` of Stacks 08PH attached to the
identity functor of the fibre, and holds by `rfl`.

## References

* [Stacks Project, Tag 08PJ](https://stacks.math.columbia.edu/tag/08PJ)
* [Stacks Project, Tag 08PI](https://stacks.math.columbia.edu/tag/08PI)
* [Stacks Project, Tag 08P8](https://stacks.math.columbia.edu/tag/08P8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory.FibredCategorySituation

universe uD vD uC w

attribute [local instance] HasDerivedCategory.standard

variable (s : FibredCategorySituation.{uD, vD, uC, uC, w})
  [(s.abelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Sheaf s.topology AddCommGrpCat.{max w uD vD uC})
      (ComplexShape.up ℤ))]

/-- **Derived lower shriek inverts a morphism exactly when the sheaf of fibre homology does.**
By Stacks 08PJ the functor `F ↦ L_nπ_!(F)` is the functor `F ↦ L_n(F)` of Stacks 08PI, the sheaf
on the base associated to `V ↦ H_n(C_V, F|_{C_V})`, naturally in `F`; so the two functors invert
the same morphisms. -/
theorem isIso_derivedAbelianLowerShriekHomology_map_iff (h : s.AbelianLowerShriekAcyclic)
    (hcov : s.UliftFreeCoverLowerShriekAcyclic) (n : ℕ)
    {F G : Sheaf s.topology AddCommGrpCat.{max w uD vD uC}} (a : F ⟶ G) :
    IsIso ((s.derivedAbelianLowerShriekHomology n).map a) ↔
      IsIso ((presheafToSheaf s.base.J AddCommGrpCat.{max w uD vD uC}).map
        ((fiberHomologyPresheafFunctor s n).map
          ((sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).map a))) :=
  NatIso.isIso_map_iff (s.derivedLowerShriekHomologyIso h hcov n) a

/-- **A morphism of abelian sheaves that is a homology isomorphism on every fibre is inverted by
derived lower shriek.** By Stacks 08PJ it is enough that the morphism of presheaves of fibre
homology of Stacks 08PI be an isomorphism, and a morphism of presheaves is an isomorphism as
soon as all its components are; the component at `V` is the map
`H_n(C_V, F|_{C_V}) ⟶ H_n(C_V, G|_{C_V})` induced on the homology of the fibre over `V`. -/
theorem isIso_derivedAbelianLowerShriekHomology_map_of_fibrewise
    (h : s.AbelianLowerShriekAcyclic) (hcov : s.UliftFreeCoverLowerShriekAcyclic) (n : ℕ)
    {F G : Sheaf s.topology AddCommGrpCat.{max w uD vD uC}} (a : F ⟶ G)
    (ha : ∀ V : s.base.Cᵒᵖ, IsIso (((fiberHomologyPresheafFunctor s n).map
      ((sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).map a)).app V)) :
    IsIso ((s.derivedAbelianLowerShriekHomology n).map a) := by
  rw [s.isIso_derivedAbelianLowerShriekHomology_map_iff h hcov n a]
  have _ := ha
  have _ : IsIso ((fiberHomologyPresheafFunctor s n).map
      ((sheafToPresheaf s.topology AddCommGrpCat.{max w uD vD uC}).map a)) :=
    NatIso.isIso_of_isIso_app _
  infer_instance

end Stacks.Sites.FibredCategory.FibredCategorySituation

end
