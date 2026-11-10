module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealization
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleOfSystem

/-!
# The restriction of the module realization to a simplicial degree

Let `S` be a simplicial-site situation (Stacks 09WE), let `O` be a sheaf of commutative rings on
its total site and let `(K_n, K_φ)` be a cartesian simplicial system of the derived category of
modules whose objects have no positively shifted self-maps.  Stacks 0D9T produces an object `K` of
`D(O)` as the totalization of the complex `n ↦ Lg_{n!}K_n`; this file identifies the restriction of
that totalization to each simplicial degree with the object of the system in that degree.

The mechanism is the one of Stacks 0D9L.  By the componentwise direct-sum formula of Stacks 0D72
and cartesianness, the restriction to degree `m` of the realization complex is the alternating face
map complex of the copower of `K_m` by the simplices of the standard simplex on `m`.  That copower
is an augmented simplicial object with an extra degeneracy, so its alternating face map complex is
contracted onto the augmentation, and the totalization of a contracted complex is its base.

## Main results

* `CategoryTheory.SimplicialSiteSituation.moduleRealization_component_iso`: the restriction of the
  totalization to degree `m` is the object of the system in degree `m`, by an isomorphism which
  inverts the transposed transitions out of degree zero.
* `CategoryTheory.SimplicialSiteSituation.moduleRealization_vertex_naturality`: those isomorphisms
  satisfy the square against every transition out of degree zero.
* `SimplicialSiteSituation.exists_isCartesianDerivedModule_of_derivedModuleSumFormulaSummand`:
  the cartesian object of `D(O)` realizing the system, granted the summand description of the
  direct-sum formula. That description holds in every simplicial-site situation, and the resulting
  statement of Stacks 0D9T is
  `CategoryTheory.SimplicialSiteSituation.exists_isCartesianDerivedModule_of_moduleSystem`.

## Implementation notes

*The summand description is an argument here.*  The comparison of the copower with the
restriction of the realization is an isomorphism only once the summand inclusions of the direct-sum
formula are known to be the canonical maps, which is the assertion of Stacks 0D72 (6) read on
derived categories, `CategoryTheory.SimplicialSiteSituation.DerivedModuleSumFormulaSummand`.
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula` is an abstract isomorphism, and
the description is proved later, from the sheaf-level leg equation in each case of Stacks 09WE, as
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaSummand`; the statements here take
it as an argument so that they depend only on the realization.

*The instances are `letI`s inside the proofs.*  Additivity, the commutation with the shift, the
triangulatedness and the preservation of countable direct sums of
`CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction` are all obtained by
`inferInstanceAs` against `CategoryTheory.Functor.mapDerivedCategory` of restriction of sheaves of
modules, which is what that functor is by definition.  Unfolding the definition instead leaves a
goal whose `Abelian` and `HasDerivedCategory` arguments are data rather than propositions and
instance search does not meet them.

*The objects and transitions of the associated system are definitionally the restrictions and the
derived transitions.*  `CategoryTheory.SimplicialSiteSituation.derivedModuleSystemData` is built
from `rfl` and `HEq.rfl`, so unlike the abelian analogue this file needs no `eqToHom` transport
between the system of Stacks 0D9P and the derived restriction functor.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D83](https://stacks.math.columbia.edu/tag/0D83)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
* [Stacks Project, Tag 0D9N](https://stacks.math.columbia.edu/tag/0D9N)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction_additive

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] CategoryTheory.simplexCopower
  CategoryTheory.simplexCopowerAugmented
  CategoryTheory.SimplicialSiteSituation.moduleRealizationSimplicial
  CategoryTheory.SimplicialSiteSituation.moduleRealizationComplex
  CategoryTheory.SimplicialSiteSituation.moduleRealizationTerm

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))]
  (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)

variable {S O}

omit [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))] in
/-- Countable direct sums in the derived category of modules on one simplicial component: sheaves
of modules have exact countable direct sums, and Stacks 0A5L carries that to the derived
category. -/
theorem derivedComponentModules_hasCountableCoproducts (m : SimplexCategory) :
    HasCountableCoproducts (DerivedCategory (S.componentRingedTopos O m).Modules) :=
  derivedCategory_hasCountableCoproducts _
    (Stacks.SheafOfModules.sheafOfModules_hasExactCountableDirectSums _)

/-- Derived restriction to a simplicial degree commutes with the shift. -/
local instance derivedComponentModuleRestriction_commShift (m : SimplexCategory) :
    (S.derivedComponentModuleRestriction O m).CommShift ℤ :=
  inferInstanceAs (((S.componentModulesRestriction O m).mapDerivedCategory).CommShift ℤ)

/-- Derived restriction to a simplicial degree is triangulated. -/
local instance derivedComponentModuleRestriction_isTriangulated (m : SimplexCategory) :
    (S.derivedComponentModuleRestriction O m).IsTriangulated :=
  inferInstanceAs ((S.componentModulesRestriction O m).mapDerivedCategory).IsTriangulated

/-- **The comparison of the copower with the restriction of the realization, as an
isomorphism.** -/
noncomputable def moduleRealizationComponentComparisonIso
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    simplexCopower (T.obj m) m ≅
      moduleRealizationSimplicial hflat T hT ⋙ S.derivedComponentModuleRestriction O m :=
  letI := moduleRealizationComponentComparison_isIso hflat hsummand T hT m
  asIso (moduleRealizationComponentComparison hflat T hT m)

/-- **The restriction of the realization to a simplicial degree, augmented by the object of the
system.** The augmentation is the comparison with the copower followed by the augmentation of the
copower; this is the augmented simplicial object whose extra degeneracy contracts the restricted
realization complex. -/
noncomputable def moduleRealizationComponentAugmented
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    SimplicialObject.Augmented (DerivedCategory (S.componentRingedTopos O m).Modules) where
  left := moduleRealizationSimplicial hflat T hT ⋙ S.derivedComponentModuleRestriction O m
  right := T.obj m
  hom := (moduleRealizationComponentComparisonIso hflat hsummand T hT m).inv ≫
    (simplexCopowerAugmented (T.obj m) m).hom

/-- The comparison with the copower is an isomorphism of *augmented* simplicial objects. -/
noncomputable def moduleRealizationComponentAugmentedIso
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    simplexCopowerAugmented (T.obj m) m ≅
      moduleRealizationComponentAugmented hflat hsummand T hT m :=
  Comma.isoMk (moduleRealizationComponentComparisonIso hflat hsummand T hT m) (Iso.refl _) (by
    dsimp only [moduleRealizationComponentAugmented, Functor.id_map, Iso.refl_hom]
    rw [Iso.hom_inv_id_assoc]
    simp)

/-- **The restriction of the realization to a simplicial degree carries an extra
degeneracy**, transported from the copower along the comparison of augmented simplicial
objects. -/
noncomputable def moduleRealizationComponentExtraDegeneracy
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    (moduleRealizationComponentAugmented hflat hsummand T hT m).ExtraDegeneracy :=
  SimplicialObject.Augmented.ExtraDegeneracy.ofIso
    (moduleRealizationComponentAugmentedIso hflat hsummand T hT m)
    (simplexCopowerExtraDegeneracy (T.obj m) m)

/-- The restriction of the differential of the realization complex is the alternating face map
differential of the restricted simplicial object. -/
theorem derivedComponentModuleRestriction_map_moduleRealizationComplex_d
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) (n : ℕ) :
    (S.derivedComponentModuleRestriction O m).map
        ((moduleRealizationComplex hflat T hT).d (n + 1) n) =
      AlgebraicTopology.AlternatingFaceMapComplex.objD
        (moduleRealizationComponentAugmented hflat hsummand T hT m).left n := by
  simp only [moduleRealizationComplex, AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Functor.map_sum, Functor.map_zsmul,
    SimplicialObject.δ, moduleRealizationComponentAugmented, Functor.comp_map]
  rfl

/-- The first identity of the contraction: the differential out of degree one kills the
augmentation. -/
theorem moduleRealizationComponent_d_comp_augmentation
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    (S.derivedComponentModuleRestriction O m).map
          ((moduleRealizationComplex hflat T hT).d (0 + 1) 0) ≫
        (moduleRealizationComponentAugmented hflat hsummand T hT m).hom.app
          (Opposite.op ⦋0⦌) = 0 := by
  have := Triangulated.extraDegeneracy_contraction
    (moduleRealizationComponentAugmented hflat hsummand T hT m)
    (moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m)
  simp only [← derivedComponentModuleRestriction_map_moduleRealizationComplex_d hflat hsummand T
    hT m] at this
  exact this.1

/-- The second identity of the contraction, in degree zero. -/
theorem moduleRealizationComponent_augmentation_contraction
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    ((moduleRealizationComponentAugmented hflat hsummand T hT m).hom.app (Opposite.op ⦋0⦌) ≫
            (moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m).s' :
          (S.derivedComponentModuleRestriction O m).obj
              (moduleRealizationTerm S O hflat T ⦋0⦌) ⟶
            (S.derivedComponentModuleRestriction O m).obj
              (moduleRealizationTerm S O hflat T ⦋0⦌)) +
        ((moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m).s 0 ≫
            (S.derivedComponentModuleRestriction O m).map
              ((moduleRealizationComplex hflat T hT).d (0 + 1) 0) :
          (S.derivedComponentModuleRestriction O m).obj
              (moduleRealizationTerm S O hflat T ⦋0⦌) ⟶
            (S.derivedComponentModuleRestriction O m).obj
              (moduleRealizationTerm S O hflat T ⦋0⦌)) = 𝟙 _ := by
  have := Triangulated.extraDegeneracy_contraction
    (moduleRealizationComponentAugmented hflat hsummand T hT m)
    (moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m)
  simp only [← derivedComponentModuleRestriction_map_moduleRealizationComplex_d hflat hsummand T
    hT m] at this
  exact this.2.1

/-- The third identity of the contraction: the extra degeneracy is a contracting homotopy for the
restricted realization complex in every positive degree. -/
theorem moduleRealizationComponent_contraction
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) (n : ℕ) :
    ((S.derivedComponentModuleRestriction O m).map
              ((moduleRealizationComplex hflat T hT).d (n + 1) n) ≫
            (moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m).s n :
          (S.derivedComponentModuleRestriction O m).obj
              (moduleRealizationTerm S O hflat T ⦋n + 1⦌) ⟶
            (S.derivedComponentModuleRestriction O m).obj
              (moduleRealizationTerm S O hflat T ⦋n + 1⦌)) +
        ((moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m).s (n + 1) ≫
            (S.derivedComponentModuleRestriction O m).map
              ((moduleRealizationComplex hflat T hT).d (n + 1 + 1) (n + 1)) :
          (S.derivedComponentModuleRestriction O m).obj
              (moduleRealizationTerm S O hflat T ⦋n + 1⦌) ⟶
            (S.derivedComponentModuleRestriction O m).obj
              (moduleRealizationTerm S O hflat T ⦋n + 1⦌)) = 𝟙 _ := by
  have := Triangulated.extraDegeneracy_contraction
    (moduleRealizationComponentAugmented hflat hsummand T hT m)
    (moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m)
  simp only [← derivedComponentModuleRestriction_map_moduleRealizationComplex_d hflat hsummand T
    hT m] at this
  exact this.2.2 n

/-- **The positively shifted morphisms from a restricted term of the realization to the object of
the system vanish.** The restricted term is a coproduct of copies of that object, by the
comparison with the copower, and the source's hypothesis (3) kills each summand. -/
theorem moduleRealizationComponent_hom_zero
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0)
    (m : SimplexCategory) (n : ℕ)
    (f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O m).Modules)
      ((n + 1 : ℕ) : ℤ)).obj ((S.derivedComponentModuleRestriction O m).obj
        (moduleRealizationTerm S O hflat T ⦋n + 2⦌)) ⟶ T.obj m) : f = 0 := by
  let := derivedComponentModules_hasCountableCoproducts (S := S) (O := O) m
  let a := (shiftFunctor (DerivedCategory (S.componentRingedTopos O m).Modules)
      ((n + 1 : ℕ) : ℤ)).mapIso
        ((moduleRealizationComponentComparisonIso hflat hsummand T hT m).app
          (Opposite.op ⦋n + 2⦌)).symm ≪≫
    Limits.PreservesCoproduct.iso (shiftFunctor
      (DerivedCategory (S.componentRingedTopos O m).Modules) ((n + 1 : ℕ) : ℤ))
      (fun _ : ⦋n + 2⦌ ⟶ m => T.obj m)
  refine hom_eq_zero_of_iso a (Iso.refl _) ?_ f
  intro g
  exact hom_eq_zero_of_coproduct
    (fun _ : ⦋n + 2⦌ ⟶ m =>
      (shiftFunctor (DerivedCategory (S.componentRingedTopos O m).Modules)
        ((n + 1 : ℕ) : ℤ)).obj (T.obj m))
    (fun _ => hHom m (n + 1) (by omega)) g

/-- The vertex component of the inverse comparison is a retraction of the transposed transition
out of degree zero: this is the identity the isomorphism of
`CategoryTheory.SimplicialSiteSituation.moduleRealization_component_iso` inherits. -/
theorem moduleRealizationComponentInclusion_comp_augmentation
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory)
    (ψ : ⦋0⦌ ⟶ m) :
    moduleRealizationComponentInclusion hflat T hT ψ ≫
      (moduleRealizationComponentAugmented hflat hsummand T hT m).hom.app
        (Opposite.op ⦋0⦌) = 𝟙 _ := by
  let e := moduleRealizationComponentComparisonIso hflat hsummand T hT m
  change moduleRealizationComponentInclusion hflat T hT ψ ≫ e.inv.app (Opposite.op ⦋0⦌) ≫
    Limits.Sigma.desc (fun _ : ⦋0⦌ ⟶ m => 𝟙 (T.obj m)) = 𝟙 _
  rw [← moduleRealizationComponentComparison_ι hflat T hT ψ]
  change (Limits.Sigma.ι (fun _ : ⦋0⦌ ⟶ m => T.obj m) ψ ≫ e.hom.app (Opposite.op ⦋0⦌)) ≫
    e.inv.app (Opposite.op ⦋0⦌) ≫ Limits.Sigma.desc _ = _
  simp

/-- **The restriction of the totalization to a simplicial degree is the object of the system.**
The restriction to degree `m` of the module realization is, by the direct-sum formula and
cartesianness, the copower of the object of the system in degree `m` by the simplices of the
standard simplex on `m`; that copower is an augmented simplicial object with an extra degeneracy,
so its alternating face map complex is contracted onto the augmentation, and the totalization of a
contracted complex is its base. -/
theorem moduleRealization_component_iso (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0)
    (P : Triangulated.SequentialPostnikovSystem
      (fun n : ℕ => moduleRealizationTerm S O hflat T ⦋n⦌)
      (fun n : ℕ => (moduleRealizationComplex hflat T hT).d (n + 1) n))
    {K : DerivedCategory (S.totalRingedTopos O).Modules}
    (p : (letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
      ∐ P.sequence.obj) ⟶ K)
    (q : K ⟶ (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) (1 : ℤ)).obj
      (letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
        ∐ P.sequence.obj))
    (hK : letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
      Triangle.mk (Triangulated.telescopeMap P.sequence) p q ∈
        distTriang (DerivedCategory (S.totalRingedTopos O).Modules))
    (i : moduleRealizationTerm S O hflat T ⦋0⦌ ⟶ K)
    (hi : letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
      P.π 0 ≫ i =
        (shiftFunctorZero (DerivedCategory (S.totalRingedTopos O).Modules) ℤ).inv.app
          (P.obj 0) ≫ Limits.Sigma.ι P.sequence.obj 0 ≫ p)
    (m : SimplexCategory) :
    ∃ γ : (S.derivedComponentModuleRestriction O m).obj K ≅ T.obj m,
      ∀ ψ : ⦋0⦌ ⟶ m, moduleRealizationComponentInclusion hflat T hT ψ ≫
        (S.derivedComponentModuleRestriction O m).map i ≫ γ.hom = 𝟙 _ := by
  let := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
  let := derivedComponentModules_hasCountableCoproducts (S := S) (O := O) m
  let := derivedComponentModuleRestriction_preservesCountableCoproducts (S := S) (O := O) m
  obtain ⟨r, s, hr, hs, ht⟩ :=
    (P.map (S.derivedComponentModuleRestriction O m)).split_sequence (T.obj m)
      ((moduleRealizationComponentAugmented hflat hsummand T hT m).hom.app (Opposite.op ⦋0⦌))
      (moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m).s'
      (moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m).s
      (moduleRealizationComponentExtraDegeneracy hflat hsummand T hT m).s'_comp_ε
      (moduleRealizationComponent_d_comp_augmentation hflat hsummand T hT m)
      (moduleRealizationComponent_augmentation_contraction hflat hsummand T hT m)
      (moduleRealizationComponent_contraction hflat hsummand T hT m)
      (moduleRealizationComponent_hom_zero hflat hsummand T hT hHom m)
  obtain ⟨γ, hγ⟩ := Triangulated.exists_iso_of_split_restriction P
    (S.derivedComponentModuleRestriction O m) p q hK i hi (T.obj m)
    ((moduleRealizationComponentAugmented hflat hsummand T hT m).hom.app (Opposite.op ⦋0⦌))
    r s hr hs ht
  refine ⟨γ, fun ψ => ?_⟩
  rw [hγ]
  exact moduleRealizationComponentInclusion_comp_augmentation hflat hsummand T hT m ψ

/-- **The comparison of the restrictions of the totalization with the objects of the system is
compatible with the transitions out of degree zero.** The inverse of the comparison in degree `n`
is the transposed transition of the realization followed by the restriction of the degree-zero map
`i`, and the transpose of `i` itself is the map `β` that mediates every vertex square. -/
theorem moduleRealization_vertex_naturality (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {K : DerivedCategory (S.totalRingedTopos O).Modules}
    (i : moduleRealizationTerm S O hflat T ⦋0⦌ ⟶ K)
    (γ : ∀ n, (S.derivedComponentModuleRestriction O n).obj K ≅ T.obj n)
    (hγ : ∀ (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n),
      moduleRealizationComponentInclusion hflat T hT ψ ≫
        (S.derivedComponentModuleRestriction O n).map i ≫ (γ n).hom = 𝟙 _)
    (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n) :
    T.map ψ ≫ (γ n).inv =
      (S.derivedTransitionPullback O ψ).map
          ((S.componentModuleLowerShriekDerivedAdjunction O ⦋0⦌ (hflat ⦋0⦌)).homEquiv _ _ i) ≫
        (S.derivedComponentModuleTransition O ψ).app K := by
  have := hT ψ
  have h : (γ n).inv = moduleRealizationComponentInclusion hflat T hT ψ ≫
      (S.derivedComponentModuleRestriction O n).map i := by
    refine (cancel_mono (γ n).hom).1 ?_
    simpa only [Category.assoc, Iso.inv_hom_id] using (hγ n ψ).symm
  rw [h]
  simp only [moduleRealizationComponentInclusion]
  rw [moduleRealizationTermMap_homEquiv]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← (S.derivedComponentModuleTransition O ψ).naturality i]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  rfl

/-- **The realization of a cartesian simplicial system of modules, granted the summand
description.** In a simplicial-site situation, let `O` be a sheaf of rings on the total site and
let `(K_n, K_φ)` be a simplicial system of the derived category of modules.  If the
structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m` are flat, the summand inclusions of the
componentwise direct-sum formula on derived categories are the canonical maps, the system is
cartesian, and `Hom(K_i[t], K_i) = 0` for `t > 0`, then there is a cartesian object `K` of `D(O)`
whose associated simplicial system of Stacks 0D9P is isomorphic to `(K_n, K_φ)`.

The object is the totalization of the complex `n ↦ Lg_{n!}K_n`, whose Postnikov system comes from
the hypotheses by
`SimplicialSiteSituation.nonempty_sequentialPostnikovSystem_moduleRealizationComplex`.
Its restriction to degree `m` is `K_m` by
`CategoryTheory.SimplicialSiteSituation.moduleRealization_component_iso`; the resulting
comparisons are mediated at the vertices by the transpose of the degree-zero map into the
totalization, and cartesianness upgrades that to compatibility with every simplex map.

The summand description holds in every simplicial-site situation with flat transitions
(`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaSummand`), and the statement
without it is Stacks 0D9T,
`CategoryTheory.SimplicialSiteSituation.exists_isCartesianDerivedModule_of_moduleSystem`. -/
theorem exists_isCartesianDerivedModule_of_derivedModuleSumFormulaSummand
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    ∃ K : DerivedCategory (S.totalRingedTopos O).Modules,
      S.IsCartesianDerivedModule O K ∧ Nonempty (T ≅ S.derivedModuleSystem O K) := by
  let := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
  obtain ⟨P, K, p, q, hp⟩ := exists_moduleRealization hflat T hT hHom
  have := P.isIso_π_zero
  let i : moduleRealizationTerm S O hflat T ⦋0⦌ ⟶ K := inv (P.π 0) ≫
    (shiftFunctorZero (DerivedCategory (S.totalRingedTopos O).Modules) ℤ).inv.app (P.obj 0) ≫
      Limits.Sigma.ι P.sequence.obj 0 ≫ p
  have hi : P.π 0 ≫ i =
      (shiftFunctorZero (DerivedCategory (S.totalRingedTopos O).Modules) ℤ).inv.app (P.obj 0) ≫
        Limits.Sigma.ι P.sequence.obj 0 ≫ p := by
    simp [i]
  choose γ hγ using fun m =>
    moduleRealization_component_iso hflat hsummand T hT hHom P p q hp i hi m
  let γ' (n : SimplexCategory) : T.obj n ≅ (S.derivedModuleSystem O K).obj n := (γ n).symm
  have hv (n : SimplexCategory) (ψ : ⦋0⦌ ⟶ n) :
      T.map ψ ≫ (γ' n).hom =
        (S.derivedTransitionPullback O ψ).map
            ((S.componentModuleLowerShriekDerivedAdjunction O ⦋0⦌ (hflat ⦋0⦌)).homEquiv _ _ i) ≫
          (S.derivedModuleSystem O K).map ψ :=
    moduleRealization_vertex_naturality hflat T hT i γ hγ n ψ
  have hn {m n : SimplexCategory} (φ : m ⟶ n) :
      T.map φ ≫ (γ' n).hom =
        (S.derivedTransitionPullback O φ).map (γ' m).hom ≫
          (S.derivedModuleSystem O K).map φ :=
    S.moduleSystem_naturality_of_vertex_compatibility O T (S.derivedModuleSystem O K) hT
      ((S.componentModuleLowerShriekDerivedAdjunction O ⦋0⦌ (hflat ⦋0⦌)).homEquiv _ _ i) γ' hv φ
  refine ⟨K, S.isCartesianDerivedModule_of_derivedModuleSystem_cartesian O K
    (S.moduleSystem_cartesian_of_iso O T (S.derivedModuleSystem O K) hT γ'
      (fun {_ _} φ => hn φ)), ⟨?_⟩⟩
  exact SimplicialDerivedModuleSystem.isoMk T (S.derivedModuleSystem O K) γ'
    (fun {_ _} φ => hn φ)

end CategoryTheory.SimplicialSiteSituation

end
