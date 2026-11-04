module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjection
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianComponentInverseImage
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RingedMorphismSituation

/-!
# Vanishing out of the Postnikov term `Xₙ = g_{n!}Oₙ ⊗^L_O K`

Let `S` be a simplicial-site situation (Stacks 09WE), `O` a sheaf of commutative rings on its
total site and `K` an object of `D(O)`. The term `Xₙ = (g_{n!}Oₙ) ⊗^L_O K` of the Postnikov
presentation of Stacks 0D9Q receives the canonical projection map
`CategoryTheory.SimplicialSiteSituation.moduleProjection` out of `g_{n!}Kₙ`, which Stacks 0D9E (2)
says is invertible exactly when `K` is cartesian.

This file spends that invertibility. Granted it, the derived adjunction `Lg_{n!} ⊣ Lg_n^*` turns
a `Hom`-group out of `Xₙ` into a `Hom`-group out of `Kₙ`, in the two shapes the triangulated
argument of Stacks 0D9J consumes: the vanishing of `Hom(Xᵢ[j], K')` and the annihilation of a map
`X₀ ⟶ K` by a map `K ⟶ K'` whose degree-zero restriction vanishes. Both are the module
counterparts of
`CategoryTheory.SimplicialSiteSituation.hom_integerResolutionTensorTerm_eq_zero` and
`CategoryTheory.SimplicialSiteSituation.comp_eq_zero_of_derivedComponent_map_eq_zero`, which do
the same for abelian sheaves off Stacks 0D9E (1).

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekDerivedTensorTerm`: the term
  `Xᵢ = (g_{i!}Oᵢ) ⊗^L_O K`, with its ambient category ascribed as
  `DerivedCategory (S.totalRingedTopos O).Modules`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.hom_componentModuleLowerShriekDerivedTensorTerm_eq_zero`:
  `Hom(Xᵢ[j], K')` vanishes once `Hom(Kᵢ[j], K'ᵢ)` does.
* `CategoryTheory.SimplicialSiteSituation.comp_eq_zero_of_derivedComponentModule_map_eq_zero`: a
  map `Xᵢ ⟶ K` followed by a map `K ⟶ K'` whose degree-`i` restriction vanishes is zero.

## Implementation notes

The flatness of the transitions out of degree `i` is taken as the *named* hypothesis `hflat` in
the form `CategoryTheory.SimplicialSiteSituation.moduleProjection` itself asks for, and the
invertibility hypothesis is stated at `S.moduleProjection O ⦋i⦌ hflat K` with that same `hflat`.
This is not cosmetic: `moduleProjection` takes a *proof* as an argument, so two separately
elaborated spellings of the flatness hypothesis give two syntactically different projection maps,
and instance synthesis for `Epi` of the map then fails against an `IsIso` hypothesis about the
other spelling, even though the two are definitionally equal by proof irrelevance.

The ambient category of `Xᵢ` has to be pinned by the type ascription on
`componentModuleLowerShriekDerivedTensorTerm`. Written out, the term elaborates in the spelling
`DerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O))` that the derived
tensor product produces, and then `Zero (Xᵢ ⟶ K)` is not found; through the abbreviation the
category is `DerivedCategory (S.totalRingedTopos O).Modules` and the zero morphism is.

The shift and additivity instances for the two derived functors are rebuilt by `let` from the
exactness of lower shriek (Stacks 0D74), as
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleRealization.lean` does: the
instances it declares for the same two functors are `local`, so there is nothing to import.

## References

* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9J](https://stacks.math.columbia.edu/tag/0D9J)
* [Stacks Project, Tag 0D9Q](https://stacks.math.columbia.edu/tag/0D9Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

open AlgebraicGeometry Stacks.Cohomology.DerivedPushforward

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The object `Xᵢ = (g_{i!}Oᵢ) ⊗^L_O K` of `D(O)`: the derived tensor product of `K` with the
lower shriek image of the structure sheaf of the degree-`i` component, placed in degree zero.
These are the terms of the Postnikov presentation of `K` of Stacks 0D9Q. -/
abbrev componentModuleLowerShriekDerivedTensorTerm
    (K : DerivedCategory (S.totalRingedTopos O).Modules) (i : ℕ) :
    DerivedCategory (S.totalRingedTopos O).Modules :=
  ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.obj
    ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).obj
      ((S.componentModuleLowerShriek
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) ⦋i⦌).obj
        (SheafOfModules.unit (S.componentRingSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O) ⦋i⦌))))).obj K

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))]

omit [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))] in
/-- **`Hom(Xᵢ[j], K')` vanishes as soon as `Hom(Kᵢ[j], K'ᵢ)` does**, granted that the canonical
projection map `g_{i!}Kᵢ ⟶ Xᵢ` of Stacks 0D9E (2) is invertible — which for a cartesian `K` is
what that tag says. Lower shriek on unbounded derived categories commutes with the shift, so a
map `(g_{i!}Kᵢ)[j] ⟶ K'` is a map `g_{i!}(Kᵢ[j]) ⟶ K'`, and `Lg_{i!} ⊣ Lg_i^*` transposes it
into a map `Kᵢ[j] ⟶ K'ᵢ`. -/
theorem hom_componentModuleLowerShriekDerivedTensorTerm_eq_zero
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules) (i : ℕ)
    (hflat : ∀ (m : SimplexCategory) (φ : ⦋i⦌ ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (j : ℤ) (hproj : IsIso (S.moduleProjection O ⦋i⦌ hflat K))
    (h : ∀ v : (shiftFunctor (DerivedCategory ((S.componentRingedTopos O ⦋i⦌).Modules)) j).obj
        ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) ⟶
      (S.derivedComponentModuleRestriction O ⦋i⦌).obj K', v = 0) :
    ∀ g : (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) j).obj
      (S.componentModuleLowerShriekDerivedTensorTerm O K i) ⟶ K', g = 0 := by
  have hex := S.exactFunctor_componentModuleLowerShriek' O ⦋i⦌ hflat
  let : PreservesFiniteLimits
    (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) ⦋i⦌) := hex.1
  let : PreservesFiniteColimits
    (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) ⦋i⦌) := hex.2
  let : (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) ⦋i⦌).Additive :=
    Functor.additive_of_preserves_binary_products
      (S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) ⦋i⦌)
  let : (S.componentModuleLowerShriekDerived O ⦋i⦌ hflat).CommShift ℤ :=
    inferInstanceAs (((S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))
        ⦋i⦌).mapDerivedCategory).CommShift ℤ)
  refine hom_eq_zero_of_iso
    (((shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) j).mapIso
      (@asIso _ _ _ _ (S.moduleProjection O ⦋i⦌ hflat K) hproj)).symm) (Iso.refl K') ?_
  exact hom_eq_zero_of_shifted_leftAdjoint
    (S.componentModuleLowerShriekDerivedAdjunction O ⦋i⦌ hflat)
    ((S.derivedComponentModuleRestriction O ⦋i⦌).obj K) j
    (((S.componentModuleLowerShriekDerived O ⦋i⦌ hflat).commShiftIso j).symm.app _) h

omit [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))] in
/-- **A map `Xᵢ ⟶ K` followed by a map `K ⟶ K'` whose degree-`i` restriction vanishes is zero**,
granted that the canonical projection map `g_{i!}Kᵢ ⟶ Xᵢ` of Stacks 0D9E (2) is invertible. The
projection is then epi, so it suffices to annihilate the composite after it, and the transpose of
that composite along `Lg_{i!} ⊣ Lg_i^*` factors through the degree-`i` restriction of the second
map. -/
theorem comp_eq_zero_of_derivedComponentModule_map_eq_zero
    (K K' : DerivedCategory (S.totalRingedTopos O).Modules) (i : ℕ)
    (hflat : ∀ (m : SimplexCategory) (φ : ⦋i⦌ ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (hproj : IsIso (S.moduleProjection O ⦋i⦌ hflat K))
    (a : S.componentModuleLowerShriekDerivedTensorTerm O K i ⟶ K) (b : K ⟶ K')
    (hb : (S.derivedComponentModuleRestriction O ⦋i⦌).map b = 0) : a ≫ b = 0 := by
  let : (S.derivedComponentModuleRestriction O ⦋i⦌).Additive :=
    inferInstanceAs ((S.componentModulesRestriction O ⦋i⦌).mapDerivedCategory).Additive
  have : Epi (S.moduleProjection O ⦋i⦌ hflat K) := @IsIso.epi_of_iso _ _ _ _ _ hproj
  refine zero_of_epi_comp (S.moduleProjection O ⦋i⦌ hflat K) ?_
  exact (Category.assoc _ _ _).symm.trans
    (comp_eq_zero_of_leftAdjoint
      (S.componentModuleLowerShriekDerivedAdjunction O ⦋i⦌ hflat)
      (S.moduleProjection O ⦋i⦌ hflat K ≫ a) hb)

end CategoryTheory.SimplicialSiteSituation

end
