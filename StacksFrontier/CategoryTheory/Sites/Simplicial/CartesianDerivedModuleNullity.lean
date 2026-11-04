module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleProjectionVanishing
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystemOfObject
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleResolutionDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedMapVanishing
public import StacksFrontier.CategoryTheory.Triangulated.SequentialPostnikovSystems
import StacksCore.Tactic.StacksAttribute

/-!
# Nullity of maps out of a cartesian object of the derived category of modules

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. Stacks 0D9R says that a map `K ⟶ K'` in `D(O)` out of a *cartesian* object vanishes
as soon as it vanishes in simplicial degree zero, provided the structure-sheaf transitions
`f_φ^{-1}O_n ⟶ O_m` are flat and the shifted component `Hom`-groups `Hom(K_i[i], K'_i)` for
`i > 0` and `Hom(K_i[i + 1], K'_i)` for `i ≥ 0` vanish. The source proves it exactly as the
abelian-sheaf statement Stacks 0D9J, with the module Postnikov system of Stacks 0D9Q in place of
the integral one of Stacks 0D9I: a resolution `… → g_{1!}O_1 → g_{0!}O_0` of the structure sheaf
exists by Stacks 0D9B, its brutal truncations `Yₙ[n]`, tensored with `K`, have `K` as their
derived colimit, and their successive quotients are the shifted terms `Xₙ[n]` of
`Xₙ = (g_{n!}O_n) ⊗^L_O K`.

The statement here takes, beside the source's hypotheses, the invertibility of the canonical
projection maps `g_{i!}Kᵢ ⟶ g_{i!}Oᵢ ⊗^L_O K` (`moduleProjection`). For a cartesian `K` and flat
transitions this is Stacks 0D9E (2), and Stacks 0D9R with the source's hypotheses alone is
`eq_zero_of_derivedComponentModuleRestriction_map_eq_zero`. Vanishing of a `Hom`-group is
expressed by saying that every morphism in it is zero.

All names are in the namespace `CategoryTheory.SimplicialSiteSituation`.

## Main results

* `eq_zero_of_derivedComponentModule_zero`: the nullity criterion for a map out of an object `K`
  of `D(O)` whose projection maps `g_{i!}Kᵢ ⟶ g_{i!}Oᵢ ⊗^L_O K` are invertible.

## References

* [Stacks Project, Tag 0D9R](https://stacks.math.columbia.edu/tag/0D9R)
* [Stacks Project, Tag 0D9J](https://stacks.math.columbia.edu/tag/0D9J)
* [Stacks Project, Tag 0D9Q](https://stacks.math.columbia.edu/tag/0D9Q)
* [Stacks Project, Tag 0D9B](https://stacks.math.columbia.edu/tag/0D9B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

open AlgebraicGeometry Stacks.Cohomology.DerivedPushforward
open StacksDraft.BrutalPostnikov

attribute [local instance] HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

attribute [local instance] hasSheafifyTotal

attribute [local instance] CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The nullity criterion of Stacks 0D9R, from invertible projection maps.** Let `O` be a
sheaf of commutative rings on the total site of a simplicial-site situation and let `K, K'` be
objects of `D(O)`. Assume

1. every structure-sheaf transition `f_φ^{-1}O_n ⟶ O_m` is flat,
2. `K` is cartesian,
3. `Hom(K_i[i], K'_i) = 0` for `i > 0`,
4. `Hom(K_i[i + 1], K'_i) = 0` for `i ≥ 0`, and
5. the projection maps `g_{i!}K_i ⟶ g_{i!}O_i ⊗^L_O K` are isomorphisms.

Then a map `K ⟶ K'` inducing the zero map `K_0 ⟶ K'_0` is zero.

For cartesian `K` and flat transitions, hypothesis 5 holds by Stacks 0D9E (2); the statement
without it is `eq_zero_of_derivedComponentModuleRestriction_map_eq_zero`. The Postnikov
presentation of `K` is Stacks 0D9Q for the functor `- ⊗^L_O K`, built from a resolution of the
structure sheaf (Stacks 0D9B), as in Stacks 0D9J. -/
theorem eq_zero_of_derivedComponentModule_zero
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hflat : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), (S.transitionRingedToposHom O φ).IsFlat)
    (_hK : S.IsCartesianDerivedModule O K)
    (hHom : ∀ i : ℕ, 0 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules)) (i : ℤ)).obj
          ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
        (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (hHomSucc : ∀ i : ℕ,
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
            ((i : ℤ) + 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
        (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (hproj : ∀ i : ℕ, IsIso (S.moduleProjection O ⦋i⦌ (fun _ φ => hflat φ) K))
    (f : K ⟶ K')
    (hf : (S.derivedComponentModuleRestriction O ⦋0⦌).map f = 0) :
    f = 0 := by
  obtain ⟨D⟩ := nonempty_simplicialModuleResolution S
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)
  let T := Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O
  let : (derivedTensorRight O T K).CommShift ℤ := T.commShift_left K
  let : (derivedTensorRight O T K).IsTriangulated :=
    isTriangulated_derivedTensorRight O T K
  have key (i : ℕ) (n : ℤ) (h) := hom_eq_zero_of_iso
    ((shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) n).mapIso
      (moduleResolutionTensorTermIso O T D K i)) (Iso.refl K')
    (S.hom_componentModuleLowerShriekDerivedTensorTerm_eq_zero O K K' i
      (fun _ φ => hflat φ) n (hproj i) h)
  refine eq_zero_of_isHomotopyColimit_mapTruncTowerSystem (moduleResolutionComplex D)
    (derivedTensorRight O T K)
    (isHomotopyColimit_moduleResolutionTensorSystem O T D K) (fun i hi => key i i (hHom i hi))
    (fun i => key i _ (hHomSucc i)) (fun c => ?_)
  exact zero_of_epi_comp (moduleResolutionTensorTermIso O T D K 0).inv
      ((Category.assoc _ _ _).symm.trans
        (S.comp_eq_zero_of_derivedComponentModule_map_eq_zero O K K' 0 (fun _ φ => hflat φ)
          (hproj 0) ((moduleResolutionTensorTermIso O T D K 0).inv ≫ c) f hf))

end CategoryTheory.SimplicialSiteSituation

end
