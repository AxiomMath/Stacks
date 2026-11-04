module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.HomIntoCoextension
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalizationAtGlobalSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsKInjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Coextension of scalars along a localization is idempotent

Let `(𝒞, 𝒪)` be a ringed site, let `f` be a global section of `𝒪` and let `K ∈ D(𝒪)`. Then

`R𝑆heafHom_𝒪(𝒪_f, R𝑆heafHom_𝒪(𝒪_f, K)) = R𝑆heafHom_𝒪(𝒪_f, K)`.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHom_awayCoextendScalars_idempotent`: the isomorphism
  `R𝑆heafHom_𝒪(𝒪_f, K) ≅ R𝑆heafHom_𝒪(𝒪_f, R𝑆heafHom_𝒪(𝒪_f, K))`, for `K` computed by a
  K-injective complex.

## Main results

* `AlgebraicGeometry.RingedSite.isKInjective_awayCoextendRestrictComplex`: `SheafHom_𝒪(𝒪_f, I)` is
  K-injective as a complex of sheaves of `𝒪`-modules when `I` is K-injective.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSite

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **`SheafHom_𝒪(𝒪_f, I)` is K-injective as a complex of sheaves of `𝒪`-modules**, for a
K-injective complex `I` of sheaves of `𝒪`-modules. -/
instance isKInjective_awayCoextendRestrictComplex (X : RingedSite.{u, u, u})
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((coeffRestrictComplex X (awaySheaf h) (toAwaySheaf h)).obj
        ((coeffCoextendComplex X (awaySheaf h) (toAwaySheaf h)).obj I)) :=
  Stacks.SheafOfModules.ChangeOfRings.isKInjective_restrictScalars_of_isFlatMap X.J
    (toAwaySheaf h) (isFlatMap_toAwaySheaf h) _

/-- Let `(𝒞, 𝒪)` be a ringed site, let `f` be a global section of `𝒪` and let `K ∈ D(𝒪)`. Then

`R𝑆heafHom_𝒪(𝒪_f, R𝑆heafHom_𝒪(𝒪_f, K)) = R𝑆heafHom_𝒪(𝒪_f, K)`,

with `K` computed by a K-injective complex `I` of sheaves of `𝒪`-modules and
`R𝑆heafHom_𝒪(𝒪_f, K)` by the coextension of scalars of `I` along `𝒪 ⟶ 𝒪_f`. -/
@[stacks 0996 "part (2)"]
def derivedSheafHom_awayCoextendScalars_idempotent (X : RingedSite.{u, u, u})
    (h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [I.IsKInjective] :
    DerivedCategory.Q.obj ((coeffCoextendComplex X (awaySheaf h) (toAwaySheaf h)).obj I) ≅
      DerivedCategory.Q.obj ((coeffCoextendComplex X (awaySheaf h) (toAwaySheaf h)).obj
        ((coeffRestrictComplex X (awaySheaf h) (toAwaySheaf h)).obj
          ((coeffCoextendComplex X (awaySheaf h) (toAwaySheaf h)).obj I))) :=
  have : Epi (toAwaySheaf h) := epi_toAwaySheaf h
  derivedSheafHom_coextendScalars_idempotent X (awaySheaf h) (toAwaySheaf h) I

end Derived

end AlgebraicGeometry.RingedSite

end
