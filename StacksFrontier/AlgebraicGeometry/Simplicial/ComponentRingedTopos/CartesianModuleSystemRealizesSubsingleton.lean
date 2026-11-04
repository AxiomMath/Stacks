module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModuleSystemRealizes

/-!
# Stacks 0D9T without flatness, with the negative-Ext hypothesis as subsingletons

`CategoryTheory.SimplicialSiteSituation.CartesianModuleSystemRealizes` asks that the positively
shifted self-maps `K_k[t] ⟶ K_k` vanish. Stacks 0DLA states its hypothesis as
`Ext^t(K_k, K_k) = 0` for `t < 0`, that is, as `Hom(K_k, K_k[t])` being a subsingleton for
`t < 0`. This file proves that the second form gives the first, through the shift equivalence
`Hom(K[t], K) ≃ Hom(K, K[-t])`, and so restates the proposition with the hypothesis in the source's
form.

It is a separate module, importing only the statement, because under the imports of the
spaces-étale development the zero morphism of the derived category of a component is not found
when the statement is elaborated; the subsingleton form mentions no zero morphism.

## Main results

* `CategoryTheory.SimplicialSiteSituation.CartesianModuleSystemRealizes.exists_of_subsingleton`.

## References

* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
* [Stacks Project, Tag 0DLA](https://stacks.math.columbia.edu/tag/0DLA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SimplicialSiteSituation

universe u

open Stacks.Cohomology.DerivedPushforward

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

/-- A positively shifted self-map `K[t] ⟶ K` vanishes as soon as `Hom(K, K[-t])` is a
subsingleton: it corresponds to a map `K ⟶ K[-t]` under the shift equivalence. -/
theorem eq_zero_of_subsingleton_shift_neg {C : Type*} [Category C] [HasZeroMorphisms C]
    [HasShift C ℤ] (K : C) (t : ℤ) (h : Subsingleton (K ⟶ (shiftFunctor C (-t)).obj K))
    (f : (shiftFunctor C t).obj K ⟶ K) : f = 0 :=
  ((shiftEquiv C t).toAdjunction.homEquiv K K).injective (@Subsingleton.elim _ h _ _)

/-- **Stacks 0D9T without hypothesis (1), with the hypothesis of Stacks 0DLA.** Under
`CartesianModuleSystemRealizes`, a cartesian simplicial system of the derived category of modules
with `Hom(K_k, K_k[t])` a subsingleton for every `t < 0` is the simplicial system of a cartesian
object of `D(O)`. -/
theorem CartesianModuleSystemRealizes.exists_of_subsingleton {S : SimplicialSiteSituation.{u}}
    {O : Sheaf S.totalTopology CommRingCat.{u}} (h : S.CartesianModuleSystemRealizes O)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hExt : ∀ (k : SimplexCategory) (t : ℤ), t < 0 →
      Subsingleton (T.obj k ⟶ (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        t).obj (T.obj k))) :
    ∃ K : DerivedCategory (S.totalRingedTopos O).Modules,
      S.IsCartesianDerivedModule O K ∧ Nonempty (T ≅ S.derivedModuleSystem O K) :=
  h T hT fun k t ht f =>
    eq_zero_of_subsingleton_shift_neg (T.obj k) (t : ℤ)
      (hExt k (-(t : ℤ)) (by omega)) f

end CategoryTheory.SimplicialSiteSituation

end
