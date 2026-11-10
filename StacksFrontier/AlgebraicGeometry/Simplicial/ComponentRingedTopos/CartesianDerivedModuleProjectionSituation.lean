module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfModuleSystem
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjectionAdjunctSquareDerived
public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionTensorCoherence
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionUnitor
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedModuleNullity
import StacksCore.Tactic.StacksAttribute

/-!
# Cartesian objects of `D(O)` through the projection maps

Let `S` be a simplicial-site situation (Stacks 09WE), in either of its two cases, and `O` a sheaf
of commutative rings on its total site whose structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m` are
flat. Stacks 0D9E (2) says that an object `K` of `D(O)` is cartesian exactly when the canonical map
`g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is an isomorphism in every simplicial degree. Stacks 0D9R says
that, for `K` cartesian with `Hom(K_i[i], K'_i) = 0` for `i > 0` and `Hom(K_i[i + 1], K'_i) = 0`
for `i ≥ 0`, a map `K ⟶ K'` vanishes as soon as its degree-zero restriction does.

The source proves Stacks 0D9E (2) by restricting the canonical map to a degree `m`, where both
sides become direct sums over the simplex maps `[n] ⟶ [m]` and the map becomes the sum of the
transitions of `K`. In this library that restriction is
`SimplicialSiteSituation.isCartesianDerivedModule_iff_isIso_moduleProjection_of_coherence`, whose
inputs besides flatness are the summand description of the direct-sum formula of Stacks 0D72 on
sheaves of modules and on derived categories, and the two coherences of the transition of Stacks
09WF against the comparison of Stacks 03EL. All four are theorems for every situation, so Stacks
0D9E (2) holds under the source's flatness hypothesis alone. Stacks 0D9R is then the triangulated
argument of `SimplicialSiteSituation.eq_zero_of_derivedComponentModule_zero`, whose input that the
projection maps are invertible is Stacks 0D9E (2) applied to the cartesian object `K`.

## Main results

* `SimplicialSiteSituation.isCartesianDerivedModule_iff_forall_isIso_moduleProjection`:
  **Stacks 0D9E (2)**.
* `SimplicialSiteSituation.eq_zero_of_derivedComponentModuleRestriction_map_eq_zero`:
  **Stacks 0D9R**.

## Implementation notes

Stacks 0D9E (2) and Stacks 0D9R quantify flatness differently here — the first over explicit
simplex maps, the second over strictly implicit ones — because each is stated in the shape its
consumers use; the second passes `fun _ _ φ => hflat φ` to the first.

The derived pullbacks along the transitions, in terms of which cartesianness is phrased, exist for
every situation by the instance
`SimplicialSiteSituation.hasLeftDerivedFunctor_transitionPullbackOnHomotopy`, so neither statement
carries a hypothesis of that kind.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9R](https://stacks.math.columbia.edu/tag/0D9R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat
  hasWeakSheafifyComponent wEqualsLocallyBijectiveComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- **Stacks 0D9E (2).** In a simplicial-site situation (Stacks 09WE, either case) let `O` be a
sheaf of rings on the total site such that the structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m`
are flat for every simplex map `φ : [n] ⟶ [m]`. Then an object `K` of `D(O)` is cartesian if and
only if the canonical map `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` is an isomorphism for every `n`. -/
@[stacks 0D9E "part (2)"]
theorem isCartesianDerivedModule_iff_forall_isIso_moduleProjection
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    S.IsCartesianDerivedModule O K ↔
      ∀ n : SimplexCategory, IsIso (S.moduleProjection O n (hflat n) K) :=
  S.isCartesianDerivedModule_iff_isIso_moduleProjection_of_coherence O
    (S.moduleSumFormulaLegEq O) hflat (S.derivedModuleSumFormulaSummand O hflat)
    (S.transitionTensorCoherence O) (S.transitionUnitorCoherence O) K

/-- **Stacks 0D9R.** In a simplicial-site situation (Stacks 09WE, either case) let `O` be a sheaf
of rings on the total site and `K, K'` objects of `D(O)`. Assume

1. `f_φ^{-1}O_n ⟶ O_m` is flat for every simplex map `φ`,
2. `K` is cartesian,
3. `Hom(K_i[i], K'_i) = 0` for `i > 0`, and
4. `Hom(K_i[i + 1], K'_i) = 0` for `i ≥ 0`.

Then a map `K ⟶ K'` inducing the zero map `K_0 ⟶ K'_0` is zero. -/
@[stacks 0D9R]
theorem eq_zero_of_derivedComponentModuleRestriction_map_eq_zero
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules)
    (hflat : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), (S.transitionRingedToposHom O φ).IsFlat)
    (hK : S.IsCartesianDerivedModule O K)
    (hHom : ∀ i : ℕ, 0 < i →
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules)) (i : ℤ)).obj
          ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
        (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (hHomSucc : ∀ i : ℕ,
      ∀ g : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules))
            ((i : ℤ) + 1)).obj ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
        (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', g = 0)
    (f : K ⟶ K')
    (hf : (S.derivedComponentModuleRestriction O ⦋0⦌).map f = 0) :
    f = 0 :=
  S.eq_zero_of_derivedComponentModule_zero O K K' hflat hK hHom hHomSucc
    (fun i => (S.isCartesianDerivedModule_iff_forall_isIso_moduleProjection O
      (fun _ _ φ => hflat φ) K).mp hK ⦋i⦌) f hf

end CategoryTheory.SimplicialSiteSituation

end
