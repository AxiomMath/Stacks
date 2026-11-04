module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AugmentationInvertedByDerivedFunctor

/-!
# The derived direct image of étale abelian sheaves preserves bounded below objects

Let `f : X ⟶ Y` be a morphism of schemes. The unbounded derived direct image
`Rf_* : D(X_étale) ⥤ D(Y_étale)` of abelian sheaves moves cohomology to the right: if the
cohomology sheaves of `K` vanish in degrees `< a`, so do those of `Rf_* K`.

## Main results

* `Stacks.EtaleCohomology.isGE_etaleAbelianDerivedDirectImage_obj`: `Rf_*` carries objects that
  are `≥ a` to objects that are `≥ a`.

## Implementation notes

On a bounded below object the unbounded derived direct image agrees, up to isomorphism, with the
derived functor computed on `D⁺(X_étale)`
(`Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus`), because the
derived-functor unit is invertible at K-injective complexes; the latter moves cohomology to the
right (`CategoryTheory.Functor.isGE_rightDerivedFunctorPlus_obj`, Stacks 05TC).

## References

* [Stacks Project, Tag 05TC](https://stacks.math.columbia.edu/tag/05TC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.EtaleCohomology

/-- **The derived direct image moves cohomology to the right.** For `f : X ⟶ Y` and `K` in
`D(X_étale)` whose cohomology sheaves vanish in degrees `< a`, the cohomology sheaves of
`Rf_* K` vanish in degrees `< a` as well, [Stacks, Tag 05TC]. -/
public theorem isGE_etaleAbelianDerivedDirectImage_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})) (a : ℤ)
    (hK : K.IsGE a) : ((etaleAbelianDerivedDirectImage.{u, v} f).obj K).IsGE a := by
  let K' : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
    ⟨K, ⟨a, hK⟩⟩
  have hK' : K'.IsGE a := (DerivedCategory.Plus.isGE_ι_obj_iff K' a).mp hK
  obtain ⟨e⟩ := Stacks.Perfect.CechAugmentation.nonempty_obj_iso_rightDerivedFunctorPlus
    (etaleAbelianDirectImage.{u, v} f) (etaleAbelianDerivedDirectImage.{u, v} f)
    (etaleAbelianDerivedDirectImageUnit.{u, v} f)
    (Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective _ _ _
      Stacks.DerivedFunctor.exists_quasiIso_isKInjective) K' a hK
  have hR : DerivedCategory.TStructure.t.IsGE
      ((etaleAbelianDirectImage.{u, v} f).rightDerivedFunctorPlus.obj K').obj a :=
    (DerivedCategory.Plus.isGE_ι_obj_iff _ a).mpr (Functor.isGE_rightDerivedFunctorPlus_obj _ K' a)
  exact DerivedCategory.TStructure.t.isGE_of_iso e.symm a

end Stacks.EtaleCohomology

end
