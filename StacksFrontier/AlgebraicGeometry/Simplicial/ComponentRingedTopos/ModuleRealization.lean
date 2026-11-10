module

public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleFaceCriterion
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSumFormula
public import
  StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRestrictionRightAdjoint
public import StacksFrontier.CategoryTheory.Sites.Modules.DerivedCountableCoproducts
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization
public import StacksFrontier.CategoryTheory.Triangulated.SequentialPostnikovSystems

/-!
# The realization of a cartesian simplicial system of the derived category of modules

Let `S` be a simplicial-site situation (Stacks 09WE), let `O` be a sheaf of commutative rings on
its total site all of whose structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m` are flat, and let `T`
be a cartesian simplicial system of the derived category of modules in the sense of Stacks 0D9N.
Stacks 0D9T realizes `T` as the simplicial system of a cartesian object of `D(O)`; that object is
the totalization of the complex whose term in degree `n` is `Lg_{n!} T_n`, the extension by
derived lower shriek of the object of the system in degree `n`.

This file builds the terms of that complex and the transitions between them. It is the
module-coefficient counterpart of
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianDerivedRealization.lean`, which does the
same for abelian coefficients on the way to Stacks 0D9L.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.moduleRealizationTerm`: the term `Lg_{n!} T_n`.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationTermMap`: the transition of the
  realization along a simplex map.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationComponentInclusion`: its transpose,
  from the object of the system in degree `m` into the degree-`m` restriction of the realization
  in degree `n`.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationTermShiftIso`: the shift of a term of
  the realization is the derived lower shriek of the shift.
* `CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIdIso`: derived pullback
  along the transition of an identity simplex map is the identity functor.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationSimplicial` and
  `…moduleRealizationComplex`: the realization as a simplicial object of the derived category of
  the total site, and its alternating face map complex.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationComponentComparison`: the comparison
  of the copower of the object of the system in degree `m` by the simplices of the standard
  simplex on `m` with the degree-`m` restriction of the realization.
* `CategoryTheory.SimplicialSiteSituation.DerivedModuleSumFormulaSummand`: the assertion of
  Stacks 0D72 (6) that the summand inclusions of the componentwise direct-sum formula on derived
  categories are the canonical maps. This development does not prove it; see the implementation
  note below.

## Main results

* `Stacks.SheafOfModules.sheafOfModules_hasExactCountableDirectSums`: sheaves of modules have
  exact countable direct sums, which is what makes the derived category of the total site
  receive the countable direct sums the totalization is built from.
* `SimplicialSiteSituation.derivedComponentModuleRestriction_preservesCountableCoproducts`:
  derived restriction to a simplicial degree preserves those direct sums, which is what lets the
  totalization be computed one simplicial degree at a time.
* `CategoryTheory.SimplicialSiteSituation.moduleSystem_inv_map_comp`: the inverse of the
  transition of a cartesian system along a composite, read through the canonical comparison of
  derived pullbacks.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationTermMap_homEquiv`: the transpose of
  the transition of the realization, which is the only description of it the consumers use.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationTermMap_comp` and
  `…moduleRealizationComponentInclusion_comp`: the transitions of the realization are
  contravariantly functorial, and their transposes compose.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationTermMap_id`: **the transition of the
  realization along an identity simplex map is the identity** — see the implementation note
  below, this is not a formality.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationTerm_hom_zero_of_biproduct`: **the
  positively shifted morphisms between the terms of the realization vanish**, which is one of
  the two inputs the Postnikov system of Stacks 0D83 asks for, and the step at which the
  source's hypothesis (3) is used.
* `SimplicialSiteSituation.nonempty_sequentialPostnikovSystem_moduleRealizationComplex`:
  **the realization complex carries a sequential Postnikov system** — the construction step of
  Stacks 0D9T. The object `K` the tag produces is the totalization of this system.
* `CategoryTheory.SimplicialSiteSituation.derivedTotalModules_hasCountableCoproducts` and
  `…exists_moduleRealization`: the derived category of the total site has countable direct sums,
  so that Postnikov system has a derived colimit — **the object `K` of Stacks 0D9T exists**.
* `CategoryTheory.SimplicialSiteSituation.moduleRealizationComponentComparison_isIso`: granted
  `…DerivedModuleSumFormulaSummand`, the comparison with the copower is an isomorphism. This is
  the step that consumes cartesianness a second time.

## Implementation notes

*The cocycle comparison points the other way.* The abelian analogue has an invertible compositor
`Lf_{ψ ≫ φ}^{-1} ≅ Lf_ψ^{-1} ⋙ Lf_φ^{-1}` of exact functors, and
`CategoryTheory.SimplicialDerivedSystem` is stated with it. For modules the canonical comparison
`CategoryTheory.SimplicialSiteSituation.derivedTransitionCompComparison` runs
`Lf_ψ^* ⋙ Lf_φ^* ⟶ Lf_{ψ ≫ φ}^*`, and its invertibility is Stacks 0D6D. The cocycle condition
of `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem` is therefore an
equation composed with it, and `…moduleSystem_inv_map_comp` is the form in which the
realization consumes that equation: no inverse of the comparison is taken, only the
invertibility of the system's own transitions.

*The identity law of the system is not a hypothesis but a theorem.* Stacks 0D9N, like Stacks
0D9G, imposes on a simplicial system only the cocycle condition; no normalization of `K_𝟙` is
asked for, and `CategoryTheory.SimplicialSiteSituation.SimplicialDerivedModuleSystem`
accordingly has no `map_id` field, whereas the abelian
`CategoryTheory.SimplicialDerivedSystem` of Stacks 0D9G does carry one. The realization needs
an identity law all the same, because its transitions have to assemble into a *simplicial
object* before the alternating face map complex of Stacks 09WI can be taken. For a cartesian
system the law is forced:
`CategoryTheory.SimplicialSiteSituation.map_derivedTransitionPullback_map_id` reads the cocycle
condition at the pair `(𝟙, 𝟙)` and cancels the invertible `K_𝟙`, which identifies
`Lf_𝟙^* K_𝟙` with the canonical comparison of derived pullbacks;
`…map_derivedComponentModuleTransition_id` does the same for the derived transitions of
Stacks 0D9P, whose identity law is known. The two then agree against the unit after one
naturality square of that comparison, and `Lf_𝟙^*` is faithful — it is the identity functor by
`…derivedTransitionPullbackIdIso` — so the identity law follows. **No unit law for the
comparison of derived pullbacks is used**, and none is available in this development.

*What the summand hypothesis is, and why it is carried.*
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula` is an abstract isomorphism:
it is assembled from `CategoryTheory.derivedCompBiproductIso`, hence from
`CategoryTheory.derivedCompIso` and `CategoryTheory.derivedBiproductIso`, none of which
describes its summand inclusions. Identifying them is what Stacks 0D72 (6) actually asserts, and
the abelian realization spends that identification twice — as
`CategoryTheory.SimplicialSiteSituation.componentLowerShriekBiproductIso_ι'` on sheaves and
`…derived_component_summand'` on derived categories. On the module side neither exists: the
canonical map is defined, as
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaLeg`, but it is never identified with
`Sigma.ι φ ≫ (S.moduleSumFormula O n m).hom`; case (A) of Stacks 09WE has only the transposed
form `CategoryTheory.SimplicialSite.homEquiv_sigma_ι_comp_componentModuleSumFormulaA_hom_eq`,
and case (B) only the presheaf-level
`CategoryTheory.CocontinuousSimplicialSite.sigma_ι_comp_presheafSumFormulaB_inv`. The assertion
is therefore carried, as `…DerivedModuleSumFormulaSummand`, by the one declaration that needs
it.

*Only the abstract direct-sum formula is used for the vanishing.*
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula` carries no description of its
summand inclusions, and
`CategoryTheory.SimplicialSiteSituation.moduleRealizationTerm_hom_zero_of_biproduct` needs none:
the generic
`CategoryTheory.hom_eq_zero_of_shifted_leftAdjoint_biproduct` asks only for *some* isomorphism of
the restriction with a finite direct sum, together with isomorphisms of the summands with one
object of the system, and cartesianness supplies the latter.

*Instances of the derived lower shriek are transported, not unfolded.* Its additivity and its
commutation with the shift are stated for
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekDerived` but proved by
`inferInstanceAs` against
`CategoryTheory.Functor.mapDerivedCategory` of the degreewise lower shriek. Unfolding the
definition with `dsimp only` instead leaves a goal whose `Abelian` and `HasDerivedCategory`
arguments — which are data, not propositions — are the ones the defining module found, and
instance search does not meet them; the exactness witnesses must be in scope at the *degreewise*
spelling, where they come from Stacks 0D74 and from flatness.

*Flatness is an explicit hypothesis.* It is the source's hypothesis (1), and it is what makes
`g_{n!}` exact (Stacks 0D74) and hence
`CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekDerived` and its adjunction
exist at all; it is passed to those as an argument rather than found by instance search, since
flatness is a proposition and not a class.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
* [Stacks Project, Tag 0D9L](https://stacks.math.columbia.edu/tag/0D9L)
* [Stacks Project, Tag 0D9N](https://stacks.math.columbia.edu/tag/0D9N)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
* [Stacks Project, Tag 0D9T](https://stacks.math.columbia.edu/tag/0D9T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open scoped Simplicial

universe u

namespace Stacks.SheafOfModules

/-- **Sheaves of modules have exact countable direct sums.** They are Grothendieck abelian at
the universe of the site, the ring and the module, and a Grothendieck abelian category has
exact countable direct sums. -/
theorem sheafOfModules_hasExactCountableDirectSums {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :
    HasExactCountableDirectSums (_root_.SheafOfModules.{u} R) :=
  let : IsGrothendieckAbelian.{u} (_root_.SheafOfModules.{u} R) :=
    sheafModulesGrothendieck.{u, u, u, u} J R
  hasExactCountableDirectSums_of_isGrothendieckAbelian _

end Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))]
  (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)

/-- The term of the realization complex in one simplicial degree: the extension by derived
lower shriek of the object of the system in that degree. -/
noncomputable def moduleRealizationTerm (T : SimplicialDerivedModuleSystem S O)
    (n : SimplexCategory) : DerivedCategory (S.totalRingedTopos O).Modules :=
  (S.componentModuleLowerShriekDerived O n (hflat n)).obj (T.obj n)

attribute [local implicit_reducible]
  CategoryTheory.SimplicialSiteSituation.moduleRealizationTerm

variable {S O}

/-- The transition of the realization complex along a simplex map: the transpose, under
`Lg_{n!} ⊣ Lg_n^*`, of the inverse of the transition of the system, followed by the unit and the
derived transition of Stacks 0D9P. -/
noncomputable def moduleRealizationTermMap (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {m n : SimplexCategory} (φ : m ⟶ n) :
    moduleRealizationTerm S O hflat T n ⟶ moduleRealizationTerm S O hflat T m := by
  have := hT φ
  exact ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).homEquiv _ _).symm
    (inv (T.map φ) ≫ (S.derivedTransitionPullback O φ).map
        ((S.componentModuleLowerShriekDerivedAdjunction O m (hflat m)).unit.app (T.obj m)) ≫
      (S.derivedComponentModuleTransition O φ).app (moduleRealizationTerm S O hflat T m))

/-- The transpose of the transition of the realization complex. -/
theorem moduleRealizationTermMap_homEquiv (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).homEquiv _ _
        (moduleRealizationTermMap hflat T hT φ) =
      @inv _ _ _ _ (T.map φ) (hT φ) ≫
        (S.derivedTransitionPullback O φ).map
          ((S.componentModuleLowerShriekDerivedAdjunction O m (hflat m)).unit.app (T.obj m)) ≫
        (S.derivedComponentModuleTransition O φ).app (moduleRealizationTerm S O hflat T m) := by
  simp only [moduleRealizationTermMap, Equiv.apply_symm_apply]

/-- The inverse of the transition of a cartesian system along a composite, read through the
canonical comparison of derived pullbacks. -/
theorem moduleSystem_inv_map_comp (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    @inv _ _ _ _ (T.map (ψ ≫ φ)) (hT (ψ ≫ φ)) =
      @inv _ _ _ _ (T.map φ) (hT φ) ≫
        (S.derivedTransitionPullback O φ).map (@inv _ _ _ _ (T.map ψ) (hT ψ)) ≫
        (S.derivedTransitionCompComparison O ψ φ).app (T.obj l) := by
  have hψ := hT ψ
  have hφ := hT φ
  have hψφ := hT (ψ ≫ φ)
  have key : (@inv _ _ _ _ (T.map φ) hφ ≫
        (S.derivedTransitionPullback O φ).map (@inv _ _ _ _ (T.map ψ) hψ) ≫
        (S.derivedTransitionCompComparison O ψ φ).app (T.obj l)) ≫ T.map (ψ ≫ φ) = 𝟙 _ := by
    simp only [Category.assoc]
    rw [T.map_comp ψ φ]
    simp only [← Functor.map_comp_assoc, IsIso.inv_hom_id, Functor.map_id, Category.id_comp]
  refine (cancel_mono (T.map (ψ ≫ φ))).1 ?_
  exact (IsIso.inv_hom_id _).trans key.symm

/-- The transition of the realization complex is contravariantly functorial. -/
theorem moduleRealizationTermMap_comp (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    moduleRealizationTermMap hflat T hT (ψ ≫ φ) =
      moduleRealizationTermMap hflat T hT φ ≫ moduleRealizationTermMap hflat T hT ψ := by
  have hnat := (S.derivedTransitionCompComparison O ψ φ).naturality
    ((S.componentModuleLowerShriekDerivedAdjunction O l (hflat l)).unit.app (T.obj l))
  have hnat' := (S.derivedComponentModuleTransition O φ).naturality
    (moduleRealizationTermMap hflat T hT ψ)
  simp only [Functor.comp_map] at hnat hnat'
  refine ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).homEquiv _ _).injective ?_
  rw [moduleRealizationTermMap_homEquiv hflat T hT (ψ ≫ φ), moduleSystem_inv_map_comp T hT ψ φ,
    Adjunction.homEquiv_naturality_right, moduleRealizationTermMap_homEquiv hflat T hT φ]
  simp only [Category.assoc]
  congr 1
  rw [← hnat', ← Functor.map_comp_assoc, ← Adjunction.homEquiv_unit,
    moduleRealizationTermMap_homEquiv hflat T hT ψ]
  simp only [Functor.map_comp, Category.assoc]
  congr 1
  rw [← S.derivedComponentModuleTransition_comp]
  exact ((reassoc_of% hnat) _).symm

/-- The transpose of the transition of the realization: a morphism from the object of the system
in degree `m` to the restriction in degree `m` of the realization in degree `n`. -/
noncomputable def moduleRealizationComponentInclusion (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {m n : SimplexCategory} (φ : n ⟶ m) :
    T.obj m ⟶ (S.derivedComponentModuleRestriction O m).obj
      (moduleRealizationTerm S O hflat T n) :=
  (S.componentModuleLowerShriekDerivedAdjunction O m (hflat m)).homEquiv _ _
    (moduleRealizationTermMap hflat T hT φ)

/-- The transposes of the transitions of the realization compose. -/
theorem moduleRealizationComponentInclusion_comp (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {l n m : SimplexCategory} (ψ : l ⟶ n) (φ : n ⟶ m) :
    moduleRealizationComponentInclusion hflat T hT φ ≫
        (S.derivedComponentModuleRestriction O m).map (moduleRealizationTermMap hflat T hT ψ) =
      moduleRealizationComponentInclusion hflat T hT (ψ ≫ φ) := by
  refine Eq.trans ((S.componentModuleLowerShriekDerivedAdjunction O m
    (hflat m)).homEquiv_naturality_right (moduleRealizationTermMap hflat T hT φ)
      (moduleRealizationTermMap hflat T hT ψ)).symm ?_
  exact congrArg ((S.componentModuleLowerShriekDerivedAdjunction O m (hflat m)).homEquiv _ _)
    (moduleRealizationTermMap_comp hflat T hT ψ φ).symm

/-- Derived lower shriek of modules from a simplicial component is additive: it is the functor
of derived categories induced by a functor which Stacks 0D74 makes exact. -/
local instance moduleLowerShriekDerived_additive (n : SimplexCategory) :
    (S.componentModuleLowerShriekDerived O n (hflat n)).Additive := by
  have h := S.exactFunctor_componentModuleLowerShriek' O n (hflat n)
  let : PreservesFiniteLimits
    (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) := h.1
  let : PreservesFiniteColimits
    (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) := h.2
  let : (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n).Additive :=
    Functor.additive_of_preserves_binary_products
      (S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n)
  exact inferInstanceAs
    ((S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))
      n).mapDerivedCategory).Additive

/-- Derived restriction to a simplicial degree is additive, restriction of sheaves of modules
being exact. -/
local instance derivedComponentModuleRestriction_additive (n : SimplexCategory) :
    (S.derivedComponentModuleRestriction O n).Additive :=
  inferInstanceAs ((S.componentModulesRestriction O n).mapDerivedCategory).Additive

/-- Derived lower shriek of modules from a simplicial component commutes with the shift. -/
local instance moduleLowerShriekDerived_commShift (n : SimplexCategory) :
    (S.componentModuleLowerShriekDerived O n (hflat n)).CommShift ℤ := by
  have h := S.exactFunctor_componentModuleLowerShriek' O n (hflat n)
  letI : PreservesFiniteLimits
    (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) := h.1
  letI : PreservesFiniteColimits
    (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) := h.2
  letI : (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n).Additive :=
    Functor.additive_of_preserves_binary_products
      (S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n)
  exact inferInstanceAs
    (((S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))
      n).mapDerivedCategory).CommShift ℤ)

/-- **The realization in a simplicial degree, shifted, is the derived lower shriek of the
shift.** This is the comparison that moves the shift of the source of a positively shifted
morphism between terms of the realization across the adjunction. -/
noncomputable def moduleRealizationTermShiftIso (T : SimplicialDerivedModuleSystem S O)
    (n : SimplexCategory) (t : ℤ) :
    (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) t).obj
        (moduleRealizationTerm S O hflat T n) ≅
      (S.componentModuleLowerShriekDerived O n (hflat n)).obj
        ((shiftFunctor (DerivedCategory (S.componentRingedTopos O n).Modules) t).obj
          (T.obj n)) :=
  ((S.componentModuleLowerShriekDerived O n (hflat n)).commShiftIso t).symm.app (T.obj n)

/-- **The positively shifted morphisms between the terms of the realization vanish.** The
restriction of a term of the realization to one simplicial degree is, by the componentwise
direct-sum formula of Stacks 0D72 (6) on derived categories, a direct sum of derived pullbacks
of the objects of the system, all of them isomorphic to one object of the system because the
system is cartesian; so the source's hypothesis (3) on the system gives the vanishing here.

This is one of the two inputs the Postnikov system of Stacks 0D83 asks for. -/
theorem moduleRealizationTerm_hom_zero_of_biproduct (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0)
    (i j : SimplexCategory) (t : ℕ) (ht : 0 < t)
    (f : (shiftFunctor (DerivedCategory (S.totalRingedTopos O).Modules) (t : ℤ)).obj
        (moduleRealizationTerm S O hflat T i) ⟶ moduleRealizationTerm S O hflat T j) :
    f = 0 := by
  let : Fintype (j ⟶ i) := Fintype.ofFinite (j ⟶ i)
  exact hom_eq_zero_of_shifted_leftAdjoint_biproduct
    (S.componentModuleLowerShriekDerivedAdjunction O i (hflat i))
    (fun φ : j ⟶ i => (S.derivedTransitionPullback O φ).obj (T.obj j))
    (T.obj i) (t : ℤ) (S.derivedModuleSumFormula O j i (hflat j) (T.obj j))
    (fun φ => by
      let := hT φ
      exact asIso (T.map φ))
    (hHom i t ht) (moduleRealizationTermShiftIso hflat T i (t : ℤ)) f

/-- Restriction of sheaves of modules to a simplicial degree preserves countable direct sums: it
is a left adjoint, by
`CategoryTheory.SimplicialSiteSituation.componentModuleRestrictionAdjunction`. -/
local instance componentModulesRestriction_preservesCountableCoproducts (n : SimplexCategory) :
    PreservesColimitsOfShape (Discrete ℕ) (S.componentModulesRestriction O n) := by
  let : PreservesColimitsOfSize.{u, u} (S.componentModulesRestriction O n) :=
    (S.componentModuleRestrictionAdjunction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))
      n).leftAdjoint_preservesColimits
  let : PreservesColimitsOfSize.{0, 0} (S.componentModulesRestriction O n) :=
    preservesColimitsOfSize_of_univLE.{u, u, 0, 0} _
  infer_instance

omit [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))] in
/-- **Derived restriction to a simplicial degree preserves countable direct sums.** Restriction
of sheaves of modules is exact and preserves countable direct sums, and both the total and the
component module categories have exact countable direct sums. -/
theorem derivedComponentModuleRestriction_preservesCountableCoproducts (n : SimplexCategory) :
    PreservesColimitsOfShape (Discrete ℕ) (S.derivedComponentModuleRestriction O n) :=
  by
  refine mapDerivedCategory_preservesCountableCoproducts ?_ ?_
    (S.componentModulesRestriction O n)
  · exact Stacks.SheafOfModules.sheafOfModules_hasExactCountableDirectSums _
  · exact Stacks.SheafOfModules.sheafOfModules_hasExactCountableDirectSums _

/-- **Derived pullback along the transition of an identity simplex map is the identity
functor.** Degreewise pullback along that transition is the identity by the unit law of
Stacks 09WF for modules, and along a flat transition nothing is derived. -/
noncomputable def derivedTransitionPullbackIdIso (n : SimplexCategory) :
    S.derivedTransitionPullback O (𝟙 n) ≅
      𝟭 (DerivedCategory (S.componentRingedTopos O n).Modules) := by
  letI : PreservesFiniteLimits (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules :=
    ((exactFunctor_iff _).1
      (S.exactFunctor_transitionPullbackModules' O (𝟙 n) (hflat n n (𝟙 n)))).1
  letI : PreservesFiniteColimits
      (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules :=
    AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
      (S.transitionRingedToposHom O (𝟙 n))
  refine ?_ ≪≫ derivedNatIso (S.transitionRingedToposHom O (𝟙 n)).toModulesHom.pullbackModules
    (𝟭 ((S.componentRingedTopos O n).Modules)) (S.transitionPullbackModulesIdToposIso O n) ≪≫
    derivedIdIso
  exact S.derivedTransitionPullbackIsoMapDerivedCategory O (𝟙 n) (hflat n n (𝟙 n))

include hflat in
/-- Derived pullback along the transition of an identity simplex map is faithful, being
isomorphic to the identity functor. -/
theorem derivedTransitionPullbackId_faithful (n : SimplexCategory) :
    (S.derivedTransitionPullback O (𝟙 n)).Faithful :=
  Functor.Faithful.of_iso (derivedTransitionPullbackIdIso hflat n).symm

/-- **The transition of a cartesian system along an identity simplex map is pinned by the
cocycle condition.** Stacks 0D9N imposes no identity law, but for a cartesian system the
cocycle condition at the pair `(𝟙, 𝟙)` identifies the image of `K_𝟙` under `Lf_𝟙^*` with the
canonical comparison of derived pullbacks. -/
theorem map_derivedTransitionPullback_map_id (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) (n : SimplexCategory) :
    (S.derivedTransitionPullback O (𝟙 n)).map (T.map (𝟙 n)) =
      (S.derivedTransitionCompComparison O (𝟙 n) (𝟙 n)).app (T.obj n) := by
  have := hT (𝟙 n)
  refine (cancel_mono (T.map (𝟙 n))).1 ?_
  exact (T.map_comp (𝟙 n) (𝟙 n)).symm

/-- The same for the derived transitions of Stacks 0D9P, whose identity law is known: their
image under `Lf_𝟙^*` is the canonical comparison of derived pullbacks as well. -/
theorem map_derivedComponentModuleTransition_id (n : SimplexCategory)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    (S.derivedTransitionPullback O (𝟙 n)).map
        ((S.derivedComponentModuleTransition O (𝟙 n)).app K) =
      (S.derivedTransitionCompComparison O (𝟙 n) (𝟙 n)).app
        ((S.derivedComponentModuleRestriction O n).obj K) := by
  have := S.isIso_derivedComponentModuleTransition_id O n
  have : IsIso ((S.derivedComponentModuleTransition O (𝟙 n)).app K) := inferInstance
  refine (cancel_mono ((S.derivedComponentModuleTransition O (𝟙 n)).app K)).1 ?_
  exact (S.derivedComponentModuleTransition_comp O (𝟙 n) (𝟙 n) K).symm

/-- **The transition of the realization along an identity simplex map is the identity.** The
two sides agree after applying `Lf_𝟙^*`, which is faithful: both become the canonical
comparison of derived pullbacks composed with the unit, by
`CategoryTheory.SimplicialSiteSituation.map_derivedTransitionPullback_map_id`,
`…map_derivedComponentModuleTransition_id` and the naturality of that comparison. No unit law
for the comparison itself is needed, and none is available. -/
theorem moduleRealizationTermMap_id (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (n : SimplexCategory) : moduleRealizationTermMap hflat T hT (𝟙 n) = 𝟙 _ := by
  have hiso := hT (𝟙 n)
  let := derivedTransitionPullbackId_faithful hflat n
  have hstar : (S.derivedTransitionPullback O (𝟙 n)).map
        ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app (T.obj n)) ≫
      (S.derivedComponentModuleTransition O (𝟙 n)).app
        (moduleRealizationTerm S O hflat T n) =
      T.map (𝟙 n) ≫
        (S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app (T.obj n) := by
    refine (S.derivedTransitionPullback O (𝟙 n)).map_injective ?_
    refine Eq.trans ((S.derivedTransitionPullback O (𝟙 n)).map_comp _ _) ?_
    refine Eq.trans ?_ ((S.derivedTransitionPullback O (𝟙 n)).map_comp _ _).symm
    refine Eq.trans (congrArg (fun k => (S.derivedTransitionPullback O (𝟙 n)).map
      ((S.derivedTransitionPullback O (𝟙 n)).map
        ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app
          (T.obj n))) ≫ k)
      (map_derivedComponentModuleTransition_id n (moduleRealizationTerm S O hflat T n))) ?_
    refine Eq.trans ?_ (congrArg (fun k => k ≫ (S.derivedTransitionPullback O (𝟙 n)).map
      ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app (T.obj n)))
      (map_derivedTransitionPullback_map_id T hT n)).symm
    exact (S.derivedTransitionCompComparison O (𝟙 n) (𝟙 n)).naturality
      ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app (T.obj n))
  refine ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).homEquiv _ _).injective ?_
  refine Eq.trans (moduleRealizationTermMap_homEquiv hflat T hT (𝟙 n)) ?_
  refine Eq.trans ?_ ((S.componentModuleLowerShriekDerivedAdjunction O n
    (hflat n)).homEquiv_id (T.obj n)).symm
  refine Eq.trans (congrArg (fun k => @inv _ _ _ _ (T.map (𝟙 n)) hiso ≫ k) hstar) ?_
  exact IsIso.inv_hom_id_assoc _ _

/-- **The realization of a cartesian system as a simplicial object of the derived category of
`O`-modules on the total site**: in degree `n` the derived lower shriek of the object of the
system, and along a simplex map the transpose of the inverse of the transition of the system. -/
noncomputable def moduleRealizationSimplicial (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) :
    SimplicialObject (DerivedCategory (S.totalRingedTopos O).Modules) where
  obj n := moduleRealizationTerm S O hflat T n.unop
  map φ := moduleRealizationTermMap hflat T hT φ.unop
  map_id n := moduleRealizationTermMap_id hflat T hT n.unop
  map_comp φ ψ := moduleRealizationTermMap_comp hflat T hT ψ.unop φ.unop

attribute [local implicit_reducible] CategoryTheory.simplexCopower
  CategoryTheory.simplexCopowerAugmented
  CategoryTheory.SimplicialSiteSituation.moduleRealizationSimplicial

/-- **The complex whose totalization realizes the system**: the alternating face map complex of
Stacks 09WI of the realization. Its differentials compose to zero because it comes from a
simplicial object. -/
noncomputable def moduleRealizationComplex (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) :
    ChainComplex (DerivedCategory (S.totalRingedTopos O).Modules) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (moduleRealizationSimplicial hflat T hT)

/-- **The Postnikov system of the module realization.** The complex whose term in
degree `n` is the derived lower shriek `Lg_{n!} K_n` of the object of the system in degree `n`,
and whose differential is the alternating sum of the transitions along the face maps, carries a
sequential Postnikov system: its differentials compose to zero, being those of the alternating
face map complex of a simplicial object, and all positively shifted morphisms between its terms
vanish by `CategoryTheory.SimplicialSiteSituation.moduleRealizationTerm_hom_zero_of_biproduct`.

This is the construction step of Stacks 0D9T: the object `K` of `D(O)` the tag produces is the
totalization of this Postnikov system. -/
theorem nonempty_sequentialPostnikovSystem_moduleRealizationComplex
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    Nonempty (Triangulated.SequentialPostnikovSystem
      (fun n : ℕ => moduleRealizationTerm S O hflat T ⦋n⦌)
      (fun n : ℕ => (moduleRealizationComplex hflat T hT).d (n + 1) n)) :=
  Triangulated.nonempty_sequentialPostnikovSystem _ _
    (fun n => (moduleRealizationComplex hflat T hT).d_comp_d (n + 2) (n + 1) n)
    (fun i j t ht f =>
      moduleRealizationTerm_hom_zero_of_biproduct hflat T hT hHom ⦋i⦌ ⦋j⦌ t ht f)

omit [∀ (m n : SimplexCategory) (φ : m ⟶ n),
    (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
      (targetQuasiIso (S.componentRingedTopos O m))] in
/-- **The derived category of modules on the total site has countable direct sums.** Sheaves of
modules have exact countable direct sums, and Stacks 0A5L carries that to the derived
category. -/
theorem derivedTotalModules_hasCountableCoproducts :
    HasCountableCoproducts (DerivedCategory (S.totalRingedTopos O).Modules) := by
  refine derivedCategory_hasCountableCoproducts _ ?_
  exact Stacks.SheafOfModules.sheafOfModules_hasExactCountableDirectSums _

/-- **The module realization has a totalization.** The realization complex carries a sequential
Postnikov system, and the system `n ↦ Yₙ⟦n⟧` of that Postnikov system has a derived colimit,
countable direct sums being available in the derived category of the total site.

This is the object `K` of `D(O)` whose existence Stacks 0D9T asserts. -/
theorem exists_moduleRealization (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian)
    (hHom : ∀ (k : SimplexCategory) (t : ℕ), 0 < t →
      ∀ f : (shiftFunctor (DerivedCategory (S.componentRingedTopos O k).Modules)
        (t : ℤ)).obj (T.obj k) ⟶ T.obj k, f = 0) :
    ∃ (P : Triangulated.SequentialPostnikovSystem
        (fun n : ℕ => moduleRealizationTerm S O hflat T ⦋n⦌)
        (fun n : ℕ => (moduleRealizationComplex hflat T hT).d (n + 1) n))
      (K : DerivedCategory (S.totalRingedTopos O).Modules),
      letI := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
      Pretriangulated.IsHomotopyColimit P.sequence K := by
  let := derivedTotalModules_hasCountableCoproducts (S := S) (O := O)
  obtain ⟨P⟩ := nonempty_sequentialPostnikovSystem_moduleRealizationComplex hflat T hT hHom
  obtain ⟨K, hK⟩ := Triangulated.exists_isHomotopyColimit P.sequence
  exact ⟨P, K, hK⟩

/-- **The comparison of the copower of the object of the system in degree `m` with the
restriction to degree `m` of the realization**: on the simplex indexed by `φ` it is the
transpose of the transition of the realization along `φ`.

It is a map of simplicial objects by
`CategoryTheory.SimplicialSiteSituation.moduleRealizationComponentInclusion_comp`. -/
noncomputable def moduleRealizationComponentComparison
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    simplexCopower (T.obj m) m ⟶
      moduleRealizationSimplicial hflat T hT ⋙ S.derivedComponentModuleRestriction O m where
  app n := Limits.Sigma.desc fun φ => moduleRealizationComponentInclusion hflat T hT φ
  naturality _ _ ψ := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    simp only [simplexCopower, Limits.Sigma.ι_comp_desc_assoc, Limits.Sigma.ι_comp_desc,
      Functor.comp_map,
      moduleRealizationSimplicial]
    exact (moduleRealizationComponentInclusion_comp hflat T hT ψ.unop φ).symm

/-- The `φ`th summand of the comparison is the transpose of the transition along `φ`. -/
theorem moduleRealizationComponentComparison_ι (T : SimplicialDerivedModuleSystem S O)
    (hT : T.Cartesian) {m : SimplexCategory} {n : SimplexCategoryᵒᵖ} (φ : n.unop ⟶ m) :
    Limits.Sigma.ι (fun _ : n.unop ⟶ m => T.obj m) φ ≫
        (moduleRealizationComponentComparison hflat T hT m).app n =
      moduleRealizationComponentInclusion hflat T hT φ :=
  Limits.Sigma.ι_comp_desc _ _

variable (S O)

/-- **The summand inclusions of the componentwise direct-sum formula on derived categories**, as
a property of a situation and a sheaf of rings. The `φ`th summand inclusion of
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula`, followed by the inverse of
that formula, is the unit of `Lg_{n!} ⊣ Lg_n^*` carried along `Lf_φ^*` and then the derived
transition of Stacks 0D9P.

This is the assertion of Stacks 0D72 (6) that the direct-sum decomposition is exhibited by the
canonical maps, read on derived categories. It is the module-coefficient counterpart of
`CategoryTheory.SimplicialSiteSituation.derived_component_summand'`, and
`…derivedModuleSumFormula` — being built from
`CategoryTheory.derivedCompBiproductIso`, which carries no summand description — does not
supply it. -/
def DerivedModuleSumFormulaSummand : Prop :=
  ∀ {n m : SimplexCategory} (φ : n ⟶ m)
    (X : DerivedCategory (S.componentRingedTopos O n).Modules),
    letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
    Limits.biproduct.ι (fun ψ : n ⟶ m => (S.derivedTransitionPullback O ψ).obj X) φ ≫
        (S.derivedModuleSumFormula O n m (hflat n) X).inv =
      (S.derivedTransitionPullback O φ).map
          ((S.componentModuleLowerShriekDerivedAdjunction O n (hflat n)).unit.app X) ≫
        (S.derivedComponentModuleTransition O φ).app
          ((S.componentModuleLowerShriekDerived O n (hflat n)).obj X)

variable {S O}

/-- **The comparison of the copower with the restriction of the realization is an
isomorphism.** Granted that the summand inclusions of the componentwise direct-sum formula are
the canonical maps, the `φ`th component of the comparison is the inverse of the transition of
the system followed by the `φ`th summand inclusion, so the comparison is the composite of three
isomorphisms: reindexing the copower by the transitions of the system, which are invertible
because it is cartesian, the identification of the coproduct with the direct sum, and the
direct-sum formula. -/
theorem moduleRealizationComponentComparison_isIso
    (hsummand : DerivedModuleSumFormulaSummand S O hflat)
    (T : SimplicialDerivedModuleSystem S O) (hT : T.Cartesian) (m : SimplexCategory) :
    IsIso (moduleRealizationComponentComparison hflat T hT m) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  have (φ : n.unop ⟶ m) : IsIso (T.map φ) := hT φ
  let : Fintype (n.unop ⟶ m) := Fintype.ofFinite (n.unop ⟶ m)
  have he : (moduleRealizationComponentComparison hflat T hT m).app n =
      ((Limits.Sigma.mapIso fun φ : n.unop ⟶ m => (asIso (T.map φ)).symm) ≪≫
        (Limits.biproduct.isoCoproduct
          (fun φ : n.unop ⟶ m =>
            (S.derivedTransitionPullback O φ).obj (T.obj n.unop))).symm ≪≫
        (S.derivedModuleSumFormula O n.unop m (hflat n.unop) (T.obj n.unop)).symm).hom := by
    refine Limits.Sigma.hom_ext _ _ fun φ => ?_
    rw [moduleRealizationComponentComparison_ι]
    have hL := moduleRealizationTermMap_homEquiv hflat T hT φ
    have hS := hsummand φ (T.obj n.unop)
    simp only [Iso.trans_hom, Iso.symm_hom, Limits.biproduct.isoCoproduct_inv] at hS ⊢
    simp only [Limits.Sigma.ι_mapIso_hom_assoc, Limits.Sigma.ι_comp_desc_assoc]
    rw [hS]
    refine hL.trans ?_
    simp only [Iso.symm_hom, asIso_inv]
    rfl
  rw [he]
  exact Iso.isIso_hom _

end CategoryTheory.SimplicialSiteSituation

end
