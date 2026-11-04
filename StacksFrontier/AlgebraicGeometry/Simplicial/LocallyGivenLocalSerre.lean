module

public import StacksFrontier.AlgebraicGeometry.Simplicial.LocallyGivenGlueing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.LocalSerreFamily
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.HypercoveringLocalSerreTotal
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.StructureSheafAugmentation
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# Locally given derived objects with cohomology in a local family of weak Serre subcategories

In Situation 0DC9 let `A_U ⊂ Mod(O_U)` be weak Serre subcategories satisfying conditions 0DC2,
0DC3 and 0DC4 (a `LocalSerreFamily`), and assume every `E_U` lies in `D_{A_U}(O_{u(U)})`. Let `L`
be a simplicial object of `SR(B)`, `K = u(L)`, and let `E` be an object of `D(O)` on
`(C/K)_total` whose restriction to each summand `C/u(U_{n,i})` is identified with `E_{U_{n,i}}`
(Stacks 0DCA). Then:

* the summands of the cohomology modules of `E` lie in the `A_{u(U_{n,i})}`;
* an `O_C`-module whose restrictions to the degree-zero members `U_{0,j}` of a hypercovering lie
  in the `A_{U_{0,j}}` lies in `A`.

## Main results

* `AlgebraicGeometry.RingedSite.LocallyGiven.summandRestriction_homology_mem`: the first fact.
* `Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily.globalProperty_of_degreeZero`: the
  second fact.

## References

* [Stacks Project, Tag 0DCC](https://stacks.math.columbia.edu/tag/0DCC)
* [Stacks Project, Tag 0DC7](https://stacks.math.columbia.edu/tag/0DC7)
* [Stacks Project, Tag 0DCA](https://stacks.math.columbia.edu/tag/0DCA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.SimplicialSemiRepresentable Stacks.CategoryTheory.Hypercovering

universe u uB vB

namespace Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily

variable {C : Type u} [SmallCategory C] [HasEqualizers C] [HasPullbacks C] (P : Pretopology C)
  (H : HypercoveringOfTerminal.{u, u, u} P) (OC : Sheaf P.toGrothendieck CommRingCat.{u})
  (T : LocalSerreFamily.{u} (pretopologyRingedSite P OC))

/-- **An `O_C`-module whose restrictions to the degree-zero members of a hypercovering lie in the
family lies in `A`.** -/
theorem globalProperty_of_degreeZero
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf OC))
    (hN : ∀ j : (H.toSimplicialObject.obj (op (SimplexCategory.mk 0))).I,
      T.A _ ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf OC)
        ((H.toSimplicialObject.obj (op (SimplexCategory.mk 0))).obj j)).obj N)) :
    T.globalProperty _ N := fun U ↦ by
  have hU := degreeZeroSieve_mem P H U
  rw [← preZeroHypercoverOfSieve_sieve₀ (degreeZeroSieve H.toSimplicialObject U)] at hU
  refine (T.locality U _ hU _).2 fun p ↦ ?_
  obtain ⟨j, ⟨φ⟩⟩ := p.2.2
  have := T.weakSerre p.1
  refine (T.A p.1).prop_of_iso ?_ (T.restriction φ _ (hN j))
  exact (SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf OC) φ).app N ≪≫
    ((SheafOfModules.overFunctorMap (Stacks.SheafOfModules.Tensor.ringSheaf OC) p.2.1).app N).symm

end Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily

namespace AlgebraicGeometry.RingedSite.LocallyGiven

attribute [local instance] LocallyGiven.category HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable {X : RingedSite.{u, u, u}} [X.J.toCoverage.HasPullbacks]
  (G : LocallyGiven.{0, u, u, u, uB, vB} X) (L : SimplicialObject (FormalCoproduct.{u} G.B))
  (T : Stacks.Cohomology.CohomologicalDescent.LocalSerreFamily.{u} X)

/-- **The summands of the cohomology modules of a glued object lie in the family.** If every
`E_U` has its cohomology in `A_{u(U)}`, and `E` on `(C/K)_total` restricts to `E_{U_{n,i}}` on
the summand `C/u(U_{n,i})` of `C/K_n`, then the restriction to that summand of the restriction to
`C/K_n` of `H^q(E)` lies in `A_{u(U_{n,i})}`. -/
theorem summandRestriction_homology_mem
    (hA : ∀ (U : G.B) (q : ℤ), T.A (G.u.obj U)
      ((DerivedCategory.homologyFunctor _ q).obj (G.obj U)))
    (E : DerivedCategory ((situation X.J (G.image L)).totalRingedTopos
      (structureSheaf X (G.image L))).Modules)
    (σ : G.SummandIdentification L E) (n : SimplexCategory) (i : (L.obj (op n)).I) (q : ℤ) :
    T.A (G.u.obj ((L.obj (op n)).obj i))
      ((G.summandRestrictionB L n i).obj
        (((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L))
          n).obj ((DerivedCategory.homologyFunctor _ q).obj E))) := by
  have := T.weakSerre (G.u.obj ((L.obj (op n)).obj i))
  refine (T.A _).prop_of_iso ?_ (hA _ q)
  exact (DerivedCategory.homologyFunctor _ q).mapIso (σ.iso n i).symm ≪≫
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (G.summandRestrictionB L n i) q).app _ ≪≫
    (G.summandRestrictionB L n i).mapIso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        ((situation X.J (G.image L)).componentModulesRestriction (structureSheaf X (G.image L)) n)
        q).app E)

end AlgebraicGeometry.RingedSite.LocallyGiven

end
