module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfModuleSystem

/-!
# Stacks 0D9T without the flatness hypothesis: the statement

The base's Stacks 0D9T,
`CategoryTheory.SimplicialSiteSituation.exists_isCartesianDerivedModule_of_moduleSystem`, asks that
`f_φ^{-1}O_n ⟶ O_m` be flat for every simplex map `φ`. For the étale topos of an fppf
hypercovering this fails at the degeneracies, which are diagonals; the source's proof of Stacks
0DLA applies 0D9T there without checking it. This file states 0D9T without that hypothesis, as the
proposition `CategoryTheory.SimplicialSiteSituation.CartesianModuleSystemRealizes` (piece P-core
of the 0DLA programme, see
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackCechDescentInterface.lean`), and checks that
with
the hypothesis added back it is the base's statement.

It is a separate module because the statement does not elaborate under the imports of the
`Complexes` stack: there, the zero morphism of the derived category of a component is not found.

It is proved, from the base's left derived lower shriek, as
`CategoryTheory.SimplicialSiteSituation.cartesianModuleSystemRealizes_unconditional`.

## References

* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SimplicialSiteSituation

universe u

open AlgebraicGeometry Stacks.Cohomology.DerivedPushforward

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

/-- **Stacks 0D9T without hypothesis (1)** (piece P-core of the 0DLA programme). In a
simplicial-site situation (Stacks 09WE, either case) with a sheaf of rings `O` on the total site,
every simplicial system `(K_n, K_φ)` of the derived category of modules which is cartesian and
whose positively shifted self-maps `K_i[t] ⟶ K_i` vanish is the simplicial system of a cartesian
object of `D(O)`.

This is the conclusion of the base's
`CategoryTheory.SimplicialSiteSituation.exists_isCartesianDerivedModule_of_moduleSystem` with its
hypothesis `hflat` (flatness of `f_φ^{-1}O_n ⟶ O_m` for every simplex map `φ`) removed; see
`cartesianModuleSystemRealizes_of_isFlat`. -/
def CartesianModuleSystemRealizes (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) : Prop :=
  ∀ (T : SimplicialDerivedModuleSystem S O), T.Cartesian →
    (∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) →
    ∃ K : DerivedCategory (S.totalRingedTopos O).Modules,
      S.IsCartesianDerivedModule O K ∧ Nonempty (T ≅ S.derivedModuleSystem O K)

/-- Under the flatness of every transition, `CartesianModuleSystemRealizes` is the base's Stacks
0D9T. This only checks that the statement is the base's with `hflat` removed. -/
theorem cartesianModuleSystemRealizes_of_isFlat (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u})
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat) :
    S.CartesianModuleSystemRealizes O :=
  fun T hT hHom => S.exists_isCartesianDerivedModule_of_moduleSystem O hflat T hT hHom

end CategoryTheory.SimplicialSiteSituation

end
