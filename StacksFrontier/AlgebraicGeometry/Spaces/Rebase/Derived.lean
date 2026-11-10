module

public import StacksFrontier.AlgebraicGeometry.Spaces.Rebase.SmallEtaleModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedTensorPowers
public import StacksFrontier.CategoryTheory.Monoidal.BifunctorIntegerPowersMap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SiteEquivalenceDerivedDual

/-!
# Derived categories of an algebraic space and of its lower-shriek extension

Let `h : W ⟶ S` be a morphism of a big fppf site, `F` an algebraic space over `W` and `Λ_h F`
its lower-shriek extension, an algebraic space over `S` (Stacks 03I5 (2)).  The small étale sites
of `F` and of `Λ_h F` are equivalent, compatibly with the structure sheaves, so restriction of
modules along that equivalence is an exact equivalence `Mod(𝒪_{Λ_h F}) ≌ Mod(𝒪_F)`, and induces
an equivalence `Ψ : D(𝒪_{Λ_h F}) ≌ D(𝒪_F)`.  This file shows that `Ψ` commutes with the
derived tensor product, with the structure sheaf, with the derived dual and hence with the
products of integer tensor powers `E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}` of Stacks 0DNE, and with
modules placed in degree zero.

## Main definitions

* `AlgebraicGeometry.Space.rebaseDerived`: the functor `Ψ : D(𝒪_{Λ_h F}) ⥤ D(𝒪_F)`, with the
  quasi-inverse `AlgebraicGeometry.Space.rebaseDerivedExtension` and
  `AlgebraicGeometry.Space.rebaseDerivedExtensionCompIso`.
* `AlgebraicGeometry.Space.rebaseDerivedTensorIso`: `Ψ(K ⊗^𝐋 L) ≅ Ψ K ⊗^𝐋 Ψ L`.
* `AlgebraicGeometry.Space.rebaseDerivedDualIso`: `Ψ(K^∨) ≅ (Ψ K)^∨`.
* `AlgebraicGeometry.Space.rebaseDerivedTensorPowerProductIso`:
  `Ψ(E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}) ≅ (Ψ E_1)^{⊗ n_1} ⊗ ⋯ ⊗ (Ψ E_r)^{⊗ n_r}`.
* `AlgebraicGeometry.Space.rebaseDerivedSingleIso`: `Ψ(M[0]) ≅ (Ψ M)[0]` on modules.

## Implementation notes

The equivalence of module categories is the inverse of
`AlgebraicGeometry.Space.relocalizeModulesEquivalenceSE`, which is by definition the reindexing
along `AlgebraicGeometry.Space.SmallEtale.relocalizeEquivalence`; the ringed site of `F` is on the
nose the ringed site `AlgebraicGeometry.RingedSite.reindex` of that equivalence, so the comparisons
of `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.SiteEquivalenceDerivedDual` apply
directly.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS) {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
  (hF : IsAlgebraicSpace B W hW F)
  (hF' : IsAlgebraicSpace B S hS ((OverShriek.relocalizePresheafFunctor h).obj F))

/-- The equivalence of the small étale sites of `F` and of `Λ_h F`, with its target read as the
underlying category of the ringed site of `Λ_h F`. -/
abbrev rebaseSiteEquivalence :
    (smallEtaleRingedSite B W hW F hF).C ≌ (smallEtaleRingedSite B S hS _ hF').C :=
  SmallEtale.relocalizeEquivalence B W S hW hS h F

/-- The functor of `rebaseSiteEquivalence` is continuous for the étale topologies. -/
instance isContinuous_rebaseSiteEquivalence_functor :
    (rebaseSiteEquivalence B W S hW hS h hF hF').functor.IsContinuous
      (smallEtaleRingedSite B W hW F hF).J (smallEtaleRingedSite B S hS _ hF').J :=
  SmallEtale.isContinuous_relocalizeEquivalence_functor B W S hW hS h F

/-- The inverse of `rebaseSiteEquivalence` is continuous for the étale topologies. -/
instance isContinuous_rebaseSiteEquivalence_inverse :
    (rebaseSiteEquivalence B W S hW hS h hF hF').inverse.IsContinuous
      (smallEtaleRingedSite B S hS _ hF').J (smallEtaleRingedSite B W hW F hF).J :=
  SmallEtale.isContinuous_relocalizeEquivalence_inverse B W S hW hS h F

/-- The functor of `rebaseSiteEquivalence` is cocontinuous for the étale topologies. -/
instance isCocontinuous_rebaseSiteEquivalence_functor :
    (rebaseSiteEquivalence B W S hW hS h hF hF').functor.IsCocontinuous
      (smallEtaleRingedSite B W hW F hF).J (smallEtaleRingedSite B S hS _ hF').J :=
  SmallEtale.isCocontinuous_relocalizeEquivalence_functor B W S hW hS h

/-- **The functor `Ψ : D(𝒪_{Λ_h F}) ⥤ D(𝒪_F)`** induced by restriction of modules along the
equivalence of small étale sites. -/
abbrev rebaseDerived :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    DerivedCategory (Modules.{u, u} B S hS _ hF') ⥤ DerivedCategory (Modules.{u, u} B W hW F hF) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  (relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse.mapDerivedCategory

/-- **The functor `Φ : D(𝒪_F) ⥤ D(𝒪_{Λ_h F})`**, a quasi-inverse of `Ψ`, induced by the functor
of the equivalence of module categories. -/
abbrev rebaseDerivedExtension :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    DerivedCategory (Modules.{u, u} B W hW F hF) ⥤ DerivedCategory (Modules.{u, u} B S hS _ hF') :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  (relocalizeModulesEquivalenceSE B W S hW hS h hF hF').functor.mapDerivedCategory

/-- **`Ψ ∘ Φ ≅ 𝟭`**. -/
def rebaseDerivedExtensionCompIso :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    rebaseDerivedExtension B W S hW hS h hF hF' ⋙ rebaseDerived B W S hW hS h hF hF' ≅ 𝟭 _ :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  (Dualizing.mapDerivedCategoryEquivalenceOfEquivalence
    (relocalizeModulesEquivalenceSE B W S hW hS h hF hF')).unitIso.symm

/-- The ringed site of `F` is the ringed site `RingedSite.reindex` of the equivalence of small
étale sites. -/
theorem smallEtaleRingedSite_eq_reindex :
    smallEtaleRingedSite B W hW F hF =
      (smallEtaleRingedSite B S hS _ hF').reindex (smallEtaleRingedSite B W hW F hF).J
        (rebaseSiteEquivalence B W S hW hS h hF hF') :=
  rfl

/-- `Ψ` is the functor `RingedSite.reindexDerived` of the equivalence of small étale sites. -/
theorem rebaseDerived_eq_reindexDerived :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    rebaseDerived B W S hW hS h hF hF' =
      (smallEtaleRingedSite B S hS _ hF').reindexDerived (smallEtaleRingedSite B W hW F hF).J
        (rebaseSiteEquivalence B W S hW hS h hF hF') :=
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  let := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  rfl

/-- **`Ψ(K ⊗^𝐋 L) ≅ Ψ K ⊗^𝐋 Ψ L`**: restriction along the equivalence of small étale sites
commutes with the derived tensor product. -/
def rebaseDerivedTensorIso
    (K L : @DerivedCategory (Modules.{u, u} B S hS _ hF') _ _ (HasDerivedCategory.standard _)) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    (rebaseDerived B W S hW hS h hF hF').obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor
          (smallEtaleRingedSite B S hS _ hF')).obj K).obj L) ≅
      ((Stacks.SheafOfModules.derivedTensorProductFunctor (smallEtaleRingedSite B W hW F hF)).obj
          ((rebaseDerived B W S hW hS h hF hF').obj K)).obj
        ((rebaseDerived B W S hW hS h hF hF').obj L) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  ((smallEtaleRingedSite B S hS _ hF').reindexDerivedTensorFlipIso
    (smallEtaleRingedSite B W hW F hF).J (rebaseSiteEquivalence B W S hW hS h hF hF') L).app K

/-- **`Ψ 𝒪 ≅ 𝒪`**: restriction carries the structure sheaf in degree zero to the structure sheaf
in degree zero. -/
def rebaseDerivedStructureSheafIso :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    (rebaseDerived B W S hW hS h hF hF').obj
        (RingedSite.derivedStructureSheaf (smallEtaleRingedSite B S hS _ hF')) ≅
      RingedSite.derivedStructureSheaf (smallEtaleRingedSite B W hW F hF) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  (smallEtaleRingedSite B S hS _ hF').reindexDerivedStructureSheafIso
    (smallEtaleRingedSite B W hW F hF).J (rebaseSiteEquivalence B W S hW hS h hF hF')

/-- **`Ψ(K^∨) ≅ (Ψ K)^∨`**: restriction along the equivalence of small étale sites commutes with
the derived dual. -/
def rebaseDerivedDualIso
    (K : @DerivedCategory (Modules.{u, u} B S hS _ hF') _ _ (HasDerivedCategory.standard _)) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    (rebaseDerived B W S hW hS h hF hF').obj (derivedDual B S hS _ hF' K) ≅
      derivedDual B W hW F hF ((rebaseDerived B W S hW hS h hF hF').obj K) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  (smallEtaleRingedSite B S hS _ hF').reindexDerivedDualIso (smallEtaleRingedSite B W hW F hF).J
    (rebaseSiteEquivalence B W S hW hS h hF hF') K

/-- **Products of integer tensor powers commute with `Ψ`**:
`Ψ(E_1^{⊗ n_1} ⊗ ⋯ ⊗ E_r^{⊗ n_r}) ≅ (Ψ E_1)^{⊗ n_1} ⊗ ⋯ ⊗ (Ψ E_r)^{⊗ n_r}`, for any objects
`E_j` of `D(𝒪_{Λ_h F})`. -/
def rebaseDerivedTensorPowerProductIso {r : ℕ}
    (E : Fin r → @DerivedCategory (Modules.{u, u} B S hS _ hF') _ _ (HasDerivedCategory.standard _))
    (n : Fin r → ℤ) :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    (rebaseDerived B W S hW hS h hF hF').obj (derivedTensorPowerProduct B S hS _ hF' E n) ≅
      derivedTensorPowerProduct B W hW F hF
        (fun j => (rebaseDerived B W S hW hS h hF hF').obj (E j)) n :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  Functor.multiTensorPowMapIso (rebaseDerived B W S hW hS h hF hF')
    (fun A A' => rebaseDerivedTensorIso B W S hW hS h hF hF' A A')
    (rebaseDerivedStructureSheafIso B W S hW hS h hF hF') E
    (fun j => derivedDual B S hS _ hF' (E j))
    (fun j => derivedDual B W hW F hF ((rebaseDerived B W S hW hS h hF hF').obj (E j)))
    (fun j => rebaseDerivedDualIso B W S hW hS h hF hF' (E j)) n

/-- **`Ψ(M[0]) ≅ (Ψ M)[0]`** for a module `M` on `Λ_h F`. -/
def rebaseDerivedSingleIso (M : Modules.{u, u} B S hS _ hF') :
    letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
    letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
    (rebaseDerived B W S hW hS h hF hF').obj ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse.obj M) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS _ hF')
  letI := HasDerivedCategory.standard (Modules.{u, u} B W hW F hF)
  ((relocalizeModulesEquivalenceSE B W S hW hS h hF hF').inverse.mapDerivedCategorySingleFunctor
    0).app M

end AlgebraicGeometry.Space

end
