module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.Definition
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekCoverOfCohomology

/-!
# Covering one constructible cohomology sheaf by extensions by zero, as in the source

Let `X` be a quasi-compact and quasi-separated scheme, let `Λ` be a Noetherian ring, let
`K ∈ D(X_étale, Λ)` and let `b` be an integer for which `H^b(K)` is constructible. Tag 095Z
asserts that there are a sheaf `F` which is a finite direct sum of sheaves `j_{U!} Λ-underline`
with `U` an affine object of `X_étale`, and a map `F[-b] → K` in `D(X_étale, Λ)` inducing a
surjection `F → H^b(K)`.

## Main results

* `Stacks.EtaleCohomology.exists_shriekConstant_cover_of_isConstructibleModuleEtaleSheaf` —
  **Tag 095Z**, with the clauses of the source and no typeclass argument beyond them.

## Implementation notes

The statement differs from
`Stacks.EtaleCohomology.exists_shriekConstant_cover_of_isConstructible_homology` in three ways.

* Constructibility of `H^b(K)` is `AlgebraicGeometry.IsConstructibleModuleEtaleSheaf`, Tag 03RW
  (3) as the source states it: on a finite constructible stratification of every affine open,
  the restrictions are of finite type and locally constant.
* The coefficient universe is `ModuleCat.{max (u + 1) r} Λ`, at which sheafification on the small
  étale site, weak sheafification on its localizations and the inverse image along small étale
  base change are all found by instance search. None of them is a hypothesis.
* The conclusion is the source's: the composite of the canonical identification
  `F ≅ H^b(F[-b])` (`DerivedCategory.singleFunctorCompHomologyFunctorIso`) with the map induced
  on `H^b` is an epimorphism `F → H^b(K)`.

`F[-b]` is `DerivedCategory.singleFunctor` in degree `b`, and `D(X_étale, Λ)` is the unbounded
derived category of the abelian category of sheaves of `Λ`-modules on the small étale site, in
its standard model. `j_{U!} Λ-underline` is `AlgebraicGeometry.moduleShriekConstant`.

## References

* [Stacks Project, Tag 095Z](https://stacks.math.columbia.edu/tag/095Z)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

universe u r

namespace Stacks.EtaleCohomology

open _root_.AlgebraicGeometry DerivedCategory

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- **Stacks 095Z.** Let `X` be a quasi-compact and quasi-separated scheme, let `Λ` be a
Noetherian ring, let `K ∈ D(X_étale, Λ)` and let `b` be an integer such that `H^b(K)` is
constructible. Then there exist a sheaf `F = ⊕ᵢ j_{U i!} Λ-underline`, a finite direct sum with
every `U i` an affine object of `X_étale`, and a map `F[-b] ⟶ K` in `D(X_étale, Λ)` inducing a
surjection `F ⟶ H^b(K)`. -/
@[stacks 095Z]
public theorem exists_shriekConstant_cover_of_isConstructibleModuleEtaleSheaf (X : B.Scheme)
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory (Sheaf (SmallEtale.topology B X.obj X.property)
      (ModuleCat.{max (u + 1) r} Λ))) (b : ℤ)
    (hK : IsConstructibleModuleEtaleSheaf B X Λ
      ((homologyFunctor (Sheaf (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) r} Λ)) b).obj K)) :
    ∃ (n : ℕ) (U : Fin n → SmallEtale B X.obj X.property),
      (∀ i, IsAffine ((SmallEtale.toScheme B X.obj X.property).obj (U i))) ∧
      ∃ f : (singleFunctor (Sheaf (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) r} Λ)) b).obj
          (∐ fun i : Fin n ↦ moduleShriekConstant.{u, r, r} B X Λ (U i)) ⟶ K,
        Epi ((singleFunctorCompHomologyFunctorIso (Sheaf (SmallEtale.topology B X.obj X.property)
            (ModuleCat.{max (u + 1) r} Λ)) b).inv.app
              (∐ fun i : Fin n ↦ moduleShriekConstant.{u, r, r} B X Λ (U i)) ≫
          (homologyFunctor (Sheaf (SmallEtale.topology B X.obj X.property)
            (ModuleCat.{max (u + 1) r} Λ)) b).map f) := by
  obtain ⟨n, U, hU, f, hf⟩ := exists_shriekConstant_cover_of_isConstructible_homology B Λ X K b
    ((isConstructibleModuleEtaleSheaf_iff B X Λ _).mp hK)
  exact ⟨n, U, hU, f, epi_comp' inferInstance hf⟩

end Stacks.EtaleCohomology

end
