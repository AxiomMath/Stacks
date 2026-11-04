module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumComparison
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealizationComponent
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation

/-!
# The realization of a cartesian simplicial system of modules, without flatness

Let `S` be a simplicial-site situation (Stacks 09WE), let `O` be a sheaf of commutative rings on
its total site and let `T` be a cartesian simplicial system of the derived category of modules
(Stacks 0D9N). We construct the realization of `T` as an object of `D(O)`: the totalization of
the complex whose term in degree `n` is `Lg_{n!} T_n`, for the left derived lower shriek
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekLeftDerived`, with no flatness
hypothesis on the structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m`. This consists of the terms,
the transitions as transposes of the inverted transitions of the system, the simplicial object,
its alternating face map complex, the Postnikov system and its totalization, and the comparison
of the copower with the restriction of the realization.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isFlat_transitionRingedToposHom_id`: the transition
  morphism of an identity simplex map is flat, its structure map being an isomorphism.
* `nonempty_sequentialPostnikovSystem_leftDerivedModuleRealizationComplex`: the realization
  complex carries a sequential Postnikov system.
* `CategoryTheory.SimplicialSiteSituation.exists_leftDerivedModuleRealization`: its
  totalization exists.
* `CategoryTheory.SimplicialSiteSituation.leftDerivedModuleRealizationComponentComparison_isIso`:
  the comparison of the copower with the restriction of the realization is an isomorphism.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent
  CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction_additive
  CategoryTheory.SimplicialSiteSituation.derivedComponentModuleRestriction_commShift

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- The term of the realization complex in one simplicial degree: the extension by derived
lower shriek of the object of the system in that degree. -/
noncomputable def leftDerivedModuleRealizationTerm (T : SimplicialDerivedModuleSystem S O)
    (n : SimplexCategory) : DerivedCategory (S.totalRingedTopos O).Modules :=
  (S.componentModuleLowerShriekLeftDerived O n).obj (T.obj n)

attribute [local implicit_reducible]
  CategoryTheory.SimplicialSiteSituation.leftDerivedModuleRealizationTerm

variable {S O}

/-- The transition of the realization complex along a simplex map: the transpose, under
`Lg_{n!} ⊣ Lg_n^*`, of the inverse of the transition of the system, followed by the unit and the
derived transition of Stacks 0D9P. -/
noncomputable def leftDerivedModuleRealizationTermMap (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {m n : SimplexCategory} (φ : m ⟶ n) :
    leftDerivedModuleRealizationTerm S O T n ⟶ leftDerivedModuleRealizationTerm S O T m := by
  have := hT φ
  exact ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv _ _).symm
    (inv (T.map φ) ≫ (S.derivedTransitionPullback O φ).map
        ((S.componentModuleLowerShriekLeftDerivedAdjunction O m).unit.app (T.obj m)) ≫
      (S.derivedComponentModuleTransition O φ).app (leftDerivedModuleRealizationTerm S O T m))

/-- The transpose of the transition of the realization complex. -/
theorem leftDerivedModuleRealizationTermMap_homEquiv (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv _ _
        (leftDerivedModuleRealizationTermMap T hT φ) =
      @inv _ _ _ _ (T.map φ) (hT φ) ≫
        (S.derivedTransitionPullback O φ).map
          ((S.componentModuleLowerShriekLeftDerivedAdjunction O m).unit.app (T.obj m)) ≫
        (S.derivedComponentModuleTransition O φ).app
          (leftDerivedModuleRealizationTerm S O T m) := by
  simp only [leftDerivedModuleRealizationTermMap, Equiv.apply_symm_apply]

/-- The transition of the realization complex is contravariantly functorial. -/
theorem leftDerivedModuleRealizationTermMap_comp (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    leftDerivedModuleRealizationTermMap T hT (ψ ≫ φ) =
      leftDerivedModuleRealizationTermMap T hT φ ≫ leftDerivedModuleRealizationTermMap T hT ψ := by
  have hψ := hT ψ
  have hφ := hT φ
  have hnat := (S.derivedTransitionCompComparison O ψ φ).naturality
    ((S.componentModuleLowerShriekLeftDerivedAdjunction O l).unit.app (T.obj l))
  have hnat' := (S.derivedComponentModuleTransition O φ).naturality
    (leftDerivedModuleRealizationTermMap T hT ψ)
  simp only [Functor.comp_map] at hnat hnat'
  have hL : (S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv _ _
        (leftDerivedModuleRealizationTermMap T hT (ψ ≫ φ)) =
      @inv _ _ _ _ (T.map φ) hφ ≫
        (S.derivedTransitionPullback O φ).map (@inv _ _ _ _ (T.map ψ) hψ) ≫
        (S.derivedTransitionPullback O φ).map ((S.derivedTransitionPullback O ψ).map
          ((S.componentModuleLowerShriekLeftDerivedAdjunction O l).unit.app (T.obj l))) ≫
        (S.derivedTransitionPullback O φ).map ((S.derivedComponentModuleTransition O ψ).app
          (leftDerivedModuleRealizationTerm S O T l)) ≫
        (S.derivedComponentModuleTransition O φ).app
          (leftDerivedModuleRealizationTerm S O T l) := by
    refine Eq.trans (leftDerivedModuleRealizationTermMap_homEquiv T hT (ψ ≫ φ)) ?_
    refine Eq.trans (congrArg (fun k => k ≫
      (S.derivedTransitionPullback O (ψ ≫ φ)).map
          ((S.componentModuleLowerShriekLeftDerivedAdjunction O l).unit.app (T.obj l)) ≫
        (S.derivedComponentModuleTransition O (ψ ≫ φ)).app
          (leftDerivedModuleRealizationTerm S O T l)) (moduleSystem_inv_map_comp T hT ψ φ)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun k => @inv _ _ _ _ (T.map φ) hφ ≫ k) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun k =>
      (S.derivedTransitionPullback O φ).map (@inv _ _ _ _ (T.map ψ) hψ) ≫ k) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫
      (S.derivedComponentModuleTransition O (ψ ≫ φ)).app
        (leftDerivedModuleRealizationTerm S O T l)) hnat.symm) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun k => (S.derivedTransitionPullback O φ).map
        ((S.derivedTransitionPullback O ψ).map
          ((S.componentModuleLowerShriekLeftDerivedAdjunction O l).unit.app (T.obj l))) ≫ k)
      (S.derivedComponentModuleTransition_comp O ψ φ (leftDerivedModuleRealizationTerm S O T l))
  have hR : (S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv _ _
        (leftDerivedModuleRealizationTermMap T hT φ ≫ leftDerivedModuleRealizationTermMap T hT ψ) =
      @inv _ _ _ _ (T.map φ) hφ ≫
        (S.derivedTransitionPullback O φ).map (@inv _ _ _ _ (T.map ψ) hψ) ≫
        (S.derivedTransitionPullback O φ).map ((S.derivedTransitionPullback O ψ).map
          ((S.componentModuleLowerShriekLeftDerivedAdjunction O l).unit.app (T.obj l))) ≫
        (S.derivedTransitionPullback O φ).map ((S.derivedComponentModuleTransition O ψ).app
          (leftDerivedModuleRealizationTerm S O T l)) ≫
        (S.derivedComponentModuleTransition O φ).app
          (leftDerivedModuleRealizationTerm S O T l) := by
    refine Eq.trans
      ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv_naturality_right
        (leftDerivedModuleRealizationTermMap T hT φ)
        (leftDerivedModuleRealizationTermMap T hT ψ)) ?_
    refine Eq.trans (congrArg (fun k => k ≫ (S.derivedComponentModuleRestriction O n).map
      (leftDerivedModuleRealizationTermMap T hT ψ))
      (leftDerivedModuleRealizationTermMap_homEquiv T hT φ)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun k => @inv _ _ _ _ (T.map φ) hφ ≫ k) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k =>
      (S.derivedTransitionPullback O φ).map
        ((S.componentModuleLowerShriekLeftDerivedAdjunction O m).unit.app (T.obj m)) ≫ k)
      hnat'.symm) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k => k ≫
      (S.derivedComponentModuleTransition O φ).app (leftDerivedModuleRealizationTerm S O T l))
      ((S.derivedTransitionPullback O φ).map_comp _ _).symm) ?_
    refine Eq.trans (congrArg (fun k => (S.derivedTransitionPullback O φ).map k ≫
      (S.derivedComponentModuleTransition O φ).app (leftDerivedModuleRealizationTerm S O T l))
      (((S.componentModuleLowerShriekLeftDerivedAdjunction O m).homEquiv_unit _ _
        (leftDerivedModuleRealizationTermMap T hT ψ)).symm.trans
          (leftDerivedModuleRealizationTermMap_homEquiv T hT ψ))) ?_
    refine Eq.trans (congrArg (fun k => k ≫
      (S.derivedComponentModuleTransition O φ).app (leftDerivedModuleRealizationTerm S O T l))
      ((S.derivedTransitionPullback O φ).map_comp _ _)) ?_
    refine Eq.trans (congrArg (fun k =>
      ((S.derivedTransitionPullback O φ).map (@inv _ _ _ _ (T.map ψ) hψ) ≫ k) ≫
        (S.derivedComponentModuleTransition O φ).app (leftDerivedModuleRealizationTerm S O T l))
      ((S.derivedTransitionPullback O φ).map_comp _ _)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine congrArg (fun k =>
      (S.derivedTransitionPullback O φ).map (@inv _ _ _ _ (T.map ψ) hψ) ≫ k) ?_
    exact Category.assoc _ _ _
  exact ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv _ _).injective
    (hL.trans hR.symm)

/-- The transpose of the transition of the realization: a morphism from the object of the system
in degree `m` to the restriction in degree `m` of the realization in degree `n`. -/
noncomputable def leftDerivedModuleRealizationComponentInclusion
    (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {m n : SimplexCategory} (φ : n ⟶ m) :
    T.obj m ⟶ (S.derivedComponentModuleRestriction O m).obj
      (leftDerivedModuleRealizationTerm S O T n) :=
  (S.componentModuleLowerShriekLeftDerivedAdjunction O m).homEquiv _ _
    (leftDerivedModuleRealizationTermMap T hT φ)

/-- The transposes of the transitions of the realization compose. -/
theorem leftDerivedModuleRealizationComponentInclusion_comp (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {l n m : SimplexCategory} (ψ : l ⟶ n) (φ : n ⟶ m) :
    leftDerivedModuleRealizationComponentInclusion T hT φ ≫
        (S.derivedComponentModuleRestriction O m).map (leftDerivedModuleRealizationTermMap T hT ψ) =
      leftDerivedModuleRealizationComponentInclusion T hT (ψ ≫ φ) := by
  exact ((S.componentModuleLowerShriekLeftDerivedAdjunction O m).homEquiv_naturality_right
      (leftDerivedModuleRealizationTermMap T hT φ)
      (leftDerivedModuleRealizationTermMap T hT ψ)).symm.trans
    (congrArg ((S.componentModuleLowerShriekLeftDerivedAdjunction O m).homEquiv _ _)
      (leftDerivedModuleRealizationTermMap_comp T hT ψ φ).symm)

variable (S O) in
/-- The left derived lower shriek is additive. -/
instance componentModuleLowerShriekLeftDerived_additive (n : SimplexCategory) :
    (S.componentModuleLowerShriekLeftDerived O n).Additive :=
  (S.componentModuleLowerShriekLeftDerivedAdjunction O n).left_adjoint_additive

variable (S O) in
/-- The left derived lower shriek commutes with the shift. -/
instance componentModuleLowerShriekLeftDerived_commShift (n : SimplexCategory) :
    (S.componentModuleLowerShriekLeftDerived O n).CommShift ℤ :=
  (S.componentModuleLowerShriekLeftDerivedAdjunction O n).leftAdjointCommShift ℤ

/-- **The realization in a simplicial degree, shifted, is the derived lower shriek of the
shift.** -/
noncomputable def leftDerivedModuleRealizationTermShiftIso (T : SimplicialDerivedModuleSystem S O)
    (n : SimplexCategory) (t : ℤ) :
    (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) t).obj
        (leftDerivedModuleRealizationTerm S O T n) ≅
      (S.componentModuleLowerShriekLeftDerived O n).obj
        ((shiftFunctor (DerivedCategory (S.componentRingedTopos O n).Modules) t).obj
          (T.obj n)) :=
  ((S.componentModuleLowerShriekLeftDerived O n).commShiftIso t).symm.app (T.obj n)

/-- **The positively shifted morphisms between the terms of the realization vanish**, for a
cartesian system all of whose objects have no nonzero positively shifted endomorphisms. -/
theorem leftDerivedModuleRealizationTerm_hom_zero_of_biproduct
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0)
    (i j : SimplexCategory) (t : ℕ) (ht : 0 < t)
    (f : (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) (t : ℤ)).obj
        (leftDerivedModuleRealizationTerm S O T i) ⟶ leftDerivedModuleRealizationTerm S O T j) :
    f = 0 := by
  let : Fintype (j ⟶ i) := Fintype.ofFinite (j ⟶ i)
  have := S.isIso_derivedModuleSumComparison O j i (T.obj j)
  exact hom_eq_zero_of_shifted_leftAdjoint_biproduct
    (S.componentModuleLowerShriekLeftDerivedAdjunction O i)
    (fun φ : j ⟶ i => (S.derivedTransitionPullback O φ).obj (T.obj j))
    (T.obj i) (t : ℤ) (asIso (S.derivedModuleSumComparison O j i (T.obj j))).symm
    (fun φ => @asIso _ _ _ _ (T.map φ) (hT φ))
    (hHom i t ht) (leftDerivedModuleRealizationTermShiftIso T i (t : ℤ)) f

variable (S O) in
/-- **The transition morphism of an identity simplex map is flat.** -/
theorem isFlat_transitionRingedToposHom_id (n : SimplexCategory) :
    (S.transitionRingedToposHom O (𝟙 n)).IsFlat := by
  refine AlgebraicGeometry.SheafOfModules.isFlatMapULift_of_isIso _ ?_
  rw [transitionRingedToposHom_fSharpInverseImage, fiberTransitionCommRing_id]
  exact Iso.isIso_hom ((S.canonicalCommRingIdentityComparison n).app _)

/-- **The transition of the realization along an identity simplex map is the identity.** -/
theorem leftDerivedModuleRealizationTermMap_id (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) (n : SimplexCategory) :
    leftDerivedModuleRealizationTermMap T hT (𝟙 n) = 𝟙 _ := by
  have hiso := hT (𝟙 n)
  have : (S.derivedTransitionPullback O (𝟙 n)).Faithful := by
    have hφ := S.isFlat_transitionRingedToposHom_id O n
    have : PreservesFiniteLimits
        (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules :=
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O (𝟙 n) hφ)).1
    have : PreservesFiniteColimits
        (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules :=
      AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
        (S.transitionRingedToposHom O (𝟙 n))
    exact Functor.Faithful.of_iso (S.derivedTransitionPullbackIsoMapDerivedCategory O (𝟙 n) hφ ≪≫
      derivedNatIso (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules
        (𝟭 ((S.componentRingedTopos O n).Modules)) (S.transitionPullbackModulesIdToposIso O n) ≪≫
      derivedIdIso).symm
  have hstar : (S.derivedTransitionPullback O (𝟙 n)).map
        ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).unit.app (T.obj n)) ≫
      (S.derivedComponentModuleTransition O (𝟙 n)).app
        (leftDerivedModuleRealizationTerm S O T n) =
      T.map (𝟙 n) ≫
        (S.componentModuleLowerShriekLeftDerivedAdjunction O n).unit.app (T.obj n) := by
    refine (S.derivedTransitionPullback O (𝟙 n)).map_injective ?_
    refine Eq.trans ((S.derivedTransitionPullback O (𝟙 n)).map_comp _ _) ?_
    refine Eq.trans ?_ ((S.derivedTransitionPullback O (𝟙 n)).map_comp _ _).symm
    refine Eq.trans (congrArg (fun k => (S.derivedTransitionPullback O (𝟙 n)).map
      ((S.derivedTransitionPullback O (𝟙 n)).map
        ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).unit.app
          (T.obj n))) ≫ k)
      (map_derivedComponentModuleTransition_id n (leftDerivedModuleRealizationTerm S O T n))) ?_
    refine Eq.trans ?_ (congrArg (fun k => k ≫ (S.derivedTransitionPullback O (𝟙 n)).map
      ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).unit.app (T.obj n)))
      (map_derivedTransitionPullback_map_id T hT n)).symm
    exact (S.derivedTransitionCompComparison O (𝟙 n) (𝟙 n)).naturality
      ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).unit.app (T.obj n))
  refine ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv _ _).injective ?_
  refine Eq.trans (leftDerivedModuleRealizationTermMap_homEquiv T hT (𝟙 n)) ?_
  refine Eq.trans ?_
    ((S.componentModuleLowerShriekLeftDerivedAdjunction O n).homEquiv_id (T.obj n)).symm
  refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (𝟙 n)) hiso ≫ k) hstar) ?_
  exact IsIso.inv_hom_id_assoc _ _

/-- **The realization of a cartesian system as a simplicial object of the derived category of
`O`-modules on the total site**: in degree `n` the derived lower shriek of the object of the
system, and along a simplex map the transpose of the inverse of the transition of the system. -/
noncomputable def leftDerivedModuleRealizationSimplicial (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) :
    SimplicialObject (DerivedCategory (S.totalRingedTopos O).Modules) where
  obj n := leftDerivedModuleRealizationTerm S O T n.unop
  map φ := leftDerivedModuleRealizationTermMap T hT φ.unop
  map_id n := leftDerivedModuleRealizationTermMap_id T hT n.unop
  map_comp φ ψ := leftDerivedModuleRealizationTermMap_comp T hT ψ.unop φ.unop

attribute [local implicit_reducible] CategoryTheory.simplexCopower
  CategoryTheory.simplexCopowerAugmented
  CategoryTheory.SimplicialSiteSituation.leftDerivedModuleRealizationSimplicial

/-- **The complex whose totalization realizes the system**: the alternating face map complex of
Stacks 09WI of the realization. -/
noncomputable def leftDerivedModuleRealizationComplex (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) :
    ChainComplex (DerivedCategory (S.totalRingedTopos O).Modules) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (leftDerivedModuleRealizationSimplicial T hT)

/-- **The Postnikov system of the module realization.** The complex whose term in
degree `n` is the derived lower shriek `Lg_{n!} K_n` of the object of the system in degree `n`,
and whose differential is the alternating sum of the transitions along the face maps, carries a
sequential Postnikov system, when the positively shifted endomorphisms of the objects of the
system vanish. -/
theorem nonempty_sequentialPostnikovSystem_leftDerivedModuleRealizationComplex
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    Nonempty (Triangulated.SequentialPostnikovSystem
      (fun n : ℕ => leftDerivedModuleRealizationTerm S O T ⦋n⦌)
      (fun n : ℕ => (leftDerivedModuleRealizationComplex T hT).d (n + 1) n)) :=
  Triangulated.nonempty_sequentialPostnikovSystem _ _
    (fun n => (leftDerivedModuleRealizationComplex T hT).d_comp_d (n + 2) (n + 1) n)
    (fun i j t ht f =>
      leftDerivedModuleRealizationTerm_hom_zero_of_biproduct T hT hHom ⦋i⦌ ⦋j⦌ t ht f)

/-- **The module realization has a totalization.** The realization complex carries a sequential
Postnikov system `P`, and the sequence of `P` has a homotopy colimit `K` in `D(O)`. -/
theorem exists_leftDerivedModuleRealization (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    ∃ (P : Triangulated.SequentialPostnikovSystem
        (fun n : ℕ => leftDerivedModuleRealizationTerm S O T ⦋n⦌)
        (fun n : ℕ => (leftDerivedModuleRealizationComplex T hT).d (n + 1) n))
      (K : DerivedCategory (S.totalRingedTopos O).Modules),
      letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
      Pretriangulated.IsHomotopyColimit P.sequence K := by
  have := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
  obtain ⟨P⟩ := nonempty_sequentialPostnikovSystem_leftDerivedModuleRealizationComplex T hT hHom
  obtain ⟨K, hK⟩ := Triangulated.exists_isHomotopyColimit P.sequence
  exact ⟨P, K, hK⟩

/-- **The comparison of the copower of the object of the system in degree `m` with the
restriction to degree `m` of the realization**: on the simplex indexed by `φ` it is the
transpose of the transition of the realization along `φ`. -/
noncomputable def leftDerivedModuleRealizationComponentComparison
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    simplexCopower (T.obj m) m ⟶
      leftDerivedModuleRealizationSimplicial T hT ⋙ S.derivedComponentModuleRestriction O m where
  app n := Limits.Sigma.desc fun φ => leftDerivedModuleRealizationComponentInclusion T hT φ
  naturality _ _ ψ := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp only [simplexCopower, Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc, Functor.comp_map,
      leftDerivedModuleRealizationSimplicial]
    exact (leftDerivedModuleRealizationComponentInclusion_comp T hT ψ.unop φ).symm

/-- The `φ`th summand of the comparison is the transpose of the transition along `φ`. -/
theorem leftDerivedModuleRealizationComponentComparison_ι (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {m : SimplexCategory} {n : SimplexCategoryᵒᵖ} (φ : n.unop ⟶ m) :
    Limits.Sigma.ι (fun _ : n.unop ⟶ m => T.obj m) φ ≫
        (leftDerivedModuleRealizationComponentComparison T hT m).app n =
      leftDerivedModuleRealizationComponentInclusion T hT φ :=
  Limits.Sigma.ι_desc _ _

/-- **The comparison of the copower with the restriction of the realization is an
isomorphism.** -/
theorem leftDerivedModuleRealizationComponentComparison_isIso
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    IsIso (leftDerivedModuleRealizationComponentComparison T hT m) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  have (φ : n.unop ⟶ m) : IsIso (T.map φ) := hT φ
  let : Fintype (n.unop ⟶ m) := Fintype.ofFinite (n.unop ⟶ m)
  have := S.isIso_derivedModuleSumComparison O n.unop m (T.obj n.unop)
  have he : (leftDerivedModuleRealizationComponentComparison T hT m).app n =
      (Limits.Sigma.mapIso fun φ : n.unop ⟶ m => (asIso (T.map φ)).symm).hom ≫
        (Limits.biproduct.isoCoproduct
          (fun φ : n.unop ⟶ m =>
            (S.derivedTransitionPullback O φ).obj (T.obj n.unop))).inv ≫
        S.derivedModuleSumComparison O n.unop m (T.obj n.unop) := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    rw [leftDerivedModuleRealizationComponentComparison_ι,
      leftDerivedModuleRealizationComponentInclusion,
      leftDerivedModuleRealizationTermMap_homEquiv]
    simp only [Limits.Sigma.ι_mapIso_hom_assoc, Iso.symm_hom, asIso_inv,
      Limits.biproduct.isoCoproduct_inv, Limits.Sigma.ι_desc_assoc]
    exact congrArg (fun k => @inv _ _ _ _ (T.map φ) (hT φ) ≫ k)
      (S.ι_derivedModuleSumComparison O φ (T.obj n.unop)).symm
  rw [he]
  infer_instance

end CategoryTheory.SimplicialSiteSituation

end
