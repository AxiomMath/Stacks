module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIso

/-!
# The Leray isomorphism for compactly supported cohomology, with torsion coefficients

Let `f : U ⟶ S` and `f_S : S ⟶ Spec k` be separated of finite type, with compactifications `j_f`,
`j_S` and `j` of `f`, `f_S` and `f ≫ f_S`. Applying `RΓ(Spec k, -)` to the composition
isomorphism `R(f_S ∘ f)_! ≅ R f_{S!} ∘ R f_!` on `D⁺_tors(U_étale, Λ)`
([Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J),
`Stacks.EtaleCohomology.derivedLowerShriekCompIso`) gives the Leray isomorphism

`RΓ_c(U, K) ≅ RΓ_c(S, Rf_! K)`,

natural in `K`, and on cohomology `Hⁱ_c(U, K) ≅ Hⁱ_c(S, Rf_! K)`.

## Main definitions

* `Stacks.EtaleCohomology.compactlySupportedCohomologyLerayIso`.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyGroupLerayIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] {U S : Scheme.{u}} (f : U ⟶ S) (fS : S ⟶ Spec (.of k))
  [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace S] [QuasiSeparatedSpace S]
  [IsSeparated f] [LocallyOfFiniteType f]
  [LocallyOfFiniteType fS] [QuasiCompact fS] [IsSeparated fS]
  [LocallyOfFiniteType (f ≫ fS)] [QuasiCompact (f ≫ fS)] [IsSeparated (f ≫ fS)]
  (jf : CompactificationOf (Over.mk f)) (jS : CompactificationOf (Over.mk fS))
  (j : CompactificationOf (Over.mk (f ≫ fS))) (Λ : Type) [Ring Λ]

/-- **The Leray isomorphism `RΓ_c(U, K) ≅ RΓ_c(S, Rf_! K)`** on `D⁺_tors(U_étale, Λ)`, from the
composition isomorphism of Tag 0F7J. -/
def compactlySupportedCohomologyLerayIso :
    compactlySupportedCohomologyTorsion.{u, 0} k (f ≫ fS) j Λ ≅
      (isTorsionPlus.{u, 0} Λ U).ι ⋙ derivedLowerShriek.{u, 0} f jf Λ ⋙
        compactlySupportedCohomology.{u, 0} k fS jS Λ :=
  Functor.isoWhiskerRight (derivedLowerShriekCompIso Λ f fS jf jS j)
    (etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of k)))

/-- **The Leray isomorphism `Hⁱ_c(U, K) ≅ Hⁱ_c(S, Rf_! K)`** on `D⁺_tors(U_étale, Λ)`. -/
def compactlySupportedCohomologyGroupLerayIso (i : ℤ) :
    (isTorsionPlus.{u, 0} Λ U).ι ⋙ compactlySupportedCohomologyGroup.{u, 0} k (f ≫ fS) j Λ i ≅
      (isTorsionPlus.{u, 0} Λ U).ι ⋙ derivedLowerShriek.{u, 0} f jf Λ ⋙
        compactlySupportedCohomologyGroup.{u, 0} k fS jS Λ i :=
  Functor.isoWhiskerRight (compactlySupportedCohomologyLerayIso k f fS jf jS j Λ)
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)

end Stacks.EtaleCohomology
