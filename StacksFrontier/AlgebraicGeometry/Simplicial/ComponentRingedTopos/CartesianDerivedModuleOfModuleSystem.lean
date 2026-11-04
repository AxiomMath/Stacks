module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumFormulaSummandLegB
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleSumFormulaLegCaseBGerm
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition

/-!
# Cartesian objects of `D(O)` from simplicial systems of modules

Let `S` be a simplicial-site situation (Stacks 09WE), in either of its two cases, and `O` a sheaf
of commutative rings on its total site. Stacks 0D9T asserts that a simplicial system
`(K_n, K_φ)` of the derived category of modules which is cartesian, whose positively shifted
self-maps `K_i[t] ⟶ K_i` vanish, and for which the structure-sheaf transitions
`f_φ^{-1}O_n ⟶ O_m` are flat, is the simplicial system associated with a cartesian object `K` of
`D(O)`.

The construction of `K` — the totalization of the complex `n ↦ Lg_{n!}K_n` — and the
identification of its restrictions with the `K_n` are, in the namespace
`CategoryTheory.SimplicialSiteSituation`,
`exists_isCartesianDerivedModule_of_derivedModuleSumFormulaSummand`. That statement is phrased
for an arbitrary situation in terms of the summand description of the componentwise direct-sum
formula of Stacks 0D72 (6) on derived categories. This file proves that description for every
simplicial-site situation, by proving the sheaf-level leg equation in each of the two cases of
Stacks 09WE, and so obtains Stacks 0D9T for Situation 09WE as the source states it.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLegEq`: the leg equation of Stacks
  0D72 (6) on sheaves of modules holds in every simplicial-site situation.
* `CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaSummand`: the summand inclusions
  of the componentwise direct-sum formula on derived categories of modules are the canonical
  maps, whenever the structure-sheaf transitions are flat.
* `CategoryTheory.SimplicialSiteSituation.exists_isCartesianDerivedModule_of_moduleSystem`:
  **Stacks 0D9T**.

## Implementation notes

The derived pullbacks `Lf_φ^*` that the notion of a simplicial system is phrased in exist along
every transition morphism, by the instance
`CategoryTheory.SimplicialSiteSituation.hasLeftDerivedFunctor_transitionPullbackOnHomotopy`; the
statements below therefore carry no hypothesis of that kind.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **The leg equation of Stacks 0D72 (6) in every simplicial-site situation.** For every simplex
map `φ : [n] ⟶ [m]` the `φ`th summand inclusion of the componentwise direct-sum formula for
sheaves of modules, followed by the inverse of that formula, is the canonical map attached to
`φ`. In case (A) of Stacks 09WE this is
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEq_situation`, and in case (B) it is
`CategoryTheory.CocontinuousSimplicialSite.moduleSumFormulaLegEqB`. -/
@[stacks 0D72 "the summand inclusions of the direct-sum formula on sheaves of modules are the \
canonical maps f_φ^*G ⟶ g_m^*g_{n!}G, in Situation 09WE (both cases)"]
theorem moduleSumFormulaLegEq : S.ModuleSumFormulaLegEq O := by
  rcases S with ⟨C | C⟩
  · exact SimplicialSite.moduleSumFormulaLegEq_situation C O
  · exact CocontinuousSimplicialSite.moduleSumFormulaLegEq_situation_of_legEqB C O
      fun φ => CocontinuousSimplicialSite.moduleSumFormulaLegEqB C O φ

/-- **Stacks 0D72 (6) on derived categories of modules.** If the structure-sheaf transitions of a
simplicial-site situation are flat, the summand inclusions of the componentwise direct-sum formula
`g_m^* Lg_{n!} = ⨁_{φ : [n] ⟶ [m]} Lf_φ^*` are the canonical maps. -/
theorem derivedModuleSumFormulaSummand
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat) :
    DerivedModuleSumFormulaSummand S O hflat :=
  S.derivedModuleSumFormulaSummand_of_moduleSumFormulaLegEq O (S.moduleSumFormulaLegEq O) hflat

/-- **Stacks 0D9T.** In a simplicial-site situation (Stacks 09WE, either case) let `O` be a sheaf
of rings on the total site and let `(K_n, K_φ)` be a simplicial system of the derived category of
modules. Assume

1. `f_φ^{-1}O_n ⟶ O_m` is flat for every simplex map `φ`,
2. `(K_n, K_φ)` is cartesian, and
3. `Hom(K_i[t], K_i) = 0` for all `i` and all `t > 0`.

Then there exists a cartesian object `K` of `D(O)` whose associated simplicial system is
isomorphic to `(K_n, K_φ)`. -/
@[stacks 0D9T]
theorem exists_isCartesianDerivedModule_of_moduleSystem
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    ∃ K : DerivedCategory (S.totalRingedTopos O).Modules,
      S.IsCartesianDerivedModule O K ∧ Nonempty (T ≅ S.derivedModuleSystem O K) :=
  exists_isCartesianDerivedModule_of_derivedModuleSumFormulaSummand hflat
    (S.derivedModuleSumFormulaSummand O hflat) T hT hHom

end CategoryTheory.SimplicialSiteSituation

end
