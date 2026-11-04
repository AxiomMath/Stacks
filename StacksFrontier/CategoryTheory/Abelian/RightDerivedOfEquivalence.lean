module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.RightDerived

/-!
# The higher right derived functors of an equivalence vanish

For `G : 𝒞 ⥤ 𝒟` an equivalence of abelian categories and `X : 𝒞`,

`(G.rightDerived (n + 1)).obj X ≅ 0`.

## Main results

* `CategoryTheory.Functor.isZero_rightDerived_of_isEquivalence`: the higher right derived
  functors of an equivalence vanish.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

/-- For an equivalence `G` of abelian categories, the higher right derived functors
`G.rightDerived (n + 1)` vanish at every object. -/
public theorem isZero_rightDerived_of_isEquivalence {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C] (G : C ⥤ D) [G.Additive]
    [G.IsEquivalence] (X : C) (n : ℕ) :
    IsZero ((G.rightDerived (n + 1)).obj X) := by
  refine IsZero.of_iso ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 ?_)
    ((injectiveResolution X).isoRightDerivedObj G (n + 1))
  have h0 : ((G.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((CochainComplex.single₀ C).obj X)).ExactAt (n + 1) :=
    HomologicalComplex.ExactAt.of_isZero
      (G.map_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ (Nat.succ_ne_zero n)))
  exact (quasiIsoAt_iff_exactAt
    ((G.mapHomologicalComplex (ComplexShape.up ℕ)).map (injectiveResolution X).ι)
      (n + 1) h0).mp inferInstance

end CategoryTheory.Functor

end
