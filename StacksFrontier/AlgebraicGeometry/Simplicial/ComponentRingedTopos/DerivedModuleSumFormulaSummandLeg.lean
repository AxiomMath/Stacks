module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedSumFormulaLegSummand
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleRealizationComponent

/-!
# The summand inclusions of the derived module direct-sum formula

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site all of whose structure-sheaf transitions are flat. Stacks 0D72 (6) asserts not only
that the restriction to degree `m` of lower shriek from degree `n` is the direct sum of the
transition pullbacks, but that the decomposition is exhibited by the *canonical* maps. On derived
categories that assertion is
`CategoryTheory.SimplicialSiteSituation.DerivedModuleSumFormulaSummand`, and this file proves it
from the sheaf-level leg equation
`CategoryTheory.SimplicialSiteSituation.ModuleSumFormulaLegEq`, which
`CategoryTheory.SimplicialSite.moduleSumFormulaLegEq_situation` supplies in case (A) of
Stacks 09WE.

The mathematics is all in the generic statement
`CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_liftedTransition`. What this file adds is
the four restatements of the derived pullback `Lf_φ^*` and its comparisons that let that statement
be instantiated at the module formula at all; see the implementation notes.

## Main results

* `CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaSummand_of_moduleSumFormulaLegEq`:
  **the summand inclusions of the derived componentwise direct-sum formula are the canonical
  maps**, granted the sheaf-level leg equation.

The four auxiliary declarations
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackModules`,
`…derivedTransitionComparisonModules`,
`…derivedTransitionPullbackModulesIsoMapDerivedCategory` and
`…whiskerLeft_derivedTransitionPullbackModulesIsoMapDerivedCategory_hom` are
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullback` and its two comparisons, read
between the derived categories of sheaves of modules over the restricted sheaves of rings rather
than over the component ringed topoi.

## Implementation notes

*Why the four restatements exist.* A component's category of sheaves of modules has two spellings
in this development: `SheafOfModules (S.componentRingSheaf R n)`, where `R` is
`Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O`, which the sheaf-level formula
and its leg equation use, and `(S.componentRingedTopos O n).Modules`, which the derived pullbacks
use. The two are equal by `rfl`, and so are the derived categories built over them; but
`CategoryTheory.HasDerivedCategory` is data, and the witness instance search produces at one
spelling is not the term it produces at the other. The generic statement ties all three of its
categories to one `HasDerivedCategory` witness, so instantiating it needs every argument at a
single spelling.

Each crossing is affordable on its own — the four declarations below cost no measurable time — but
performing them inside the instantiation is not: with the derived-level arguments passed at the
`…Modules` spelling the application exhausts a declaration's heartbeat budget at `whnf`, and it
still does when only the functor and its comparison are restated. It is the *identification with
the degreewise functor* and its canonicity that must cross in advance, because they are where the
two exactness witnesses for `f_φ^*` meet: the formula takes `PreservesFiniteColimits` from
`CategoryTheory.SimplicialSiteSituation.exactFunctor_transitionPullbackModules` while
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIsoMapDerivedCategory` takes it
from `AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits`. The statements
below therefore fix the former, which is the witness the formula's own signature carries.

*No restatement of the transition is needed.* The sheaf-level transition
`CategoryTheory.SimplicialSiteSituation.componentModuleTransition` and the leg equation
`CategoryTheory.SimplicialSiteSituation.biproduct_ι_moduleSumFormulaBiproduct_inv` are stated over
`S.totalRingSheaf O` rather than over the ring sheaf `R` above, and that crossing *is* affordable
inside the instantiation: the generic statement builds the homotopy-category transition itself, so
nothing here has to write that term down. Writing it down by hand is what does not fit, which is
why the summand equation is not stated at the sheaf spelling first and transported afterwards.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D9P](https://stacks.math.columbia.edu/tag/0D9P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The derived pullback `Lf_φ^*` of Stacks 06YY, over the restricted sheaves of rings.**
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullback` read as a functor between the
derived categories of sheaves of modules over
`CategoryTheory.SimplicialSiteSituation.componentRingSheaf`, which is the spelling in which the
sheaf-level direct-sum formula of Stacks 0D72 (6) and its leg equation are stated. It is that
functor and nothing else; the two spellings of a component's module category agree by `rfl`. -/
def derivedTransitionPullbackModules {n m : SimplexCategory} (φ : n ⟶ m) :
    DerivedCategory
        (SheafOfModules.{u} (S.componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n)) ⥤
      DerivedCategory
        (SheafOfModules.{u} (S.componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m)) :=
  S.derivedTransitionPullback O φ

/-- **The canonical comparison from `Lf_φ^*` to degreewise pullback, over the restricted sheaves
of rings.** `CategoryTheory.SimplicialSiteSituation.derivedTransitionComparison` read at the
spelling of `CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackModules`, with its
target written through `CategoryTheory.SimplicialSiteSituation.transitionPullbackModules`. -/
def derivedTransitionComparisonModules {n m : SimplexCategory} (φ : n ⟶ m) :
    letI : (S.transitionPullbackModules' O φ).Additive :=
      inferInstanceAs ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).Additive
    DerivedCategory.Qh ⋙ S.derivedTransitionPullbackModules O φ ⟶
      (S.transitionPullbackModules' O φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh :=
  S.derivedTransitionComparison O φ

/-- **Along a flat simplex map the derived pullback is the degreewise one, over the restricted
sheaves of rings.**
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIsoMapDerivedCategory` read at
the spelling of
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackModules`, and with the exactness
of `f_φ^*` witnessed by
`CategoryTheory.SimplicialSiteSituation.exactFunctor_transitionPullbackModules` on both halves —
which is the pair of witnesses the signature of
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula` carries. -/
def derivedTransitionPullbackModulesIsoMapDerivedCategory {n m : SimplexCategory} (φ : n ⟶ m)
    (hφ : (S.transitionRingedToposHom O φ).IsFlat) :
    letI : (S.transitionPullbackModules' O φ).Additive :=
      inferInstanceAs ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).Additive
    letI : PreservesFiniteLimits (S.transitionPullbackModules' O φ) :=
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).1
    letI : PreservesFiniteColimits (S.transitionPullbackModules' O φ) :=
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).2
    S.derivedTransitionPullbackModules O φ ≅
      (S.transitionPullbackModules' O φ).mapDerivedCategory :=
  S.derivedTransitionPullbackIsoMapDerivedCategory O φ hφ

/-- **The identification is the canonical one, over the restricted sheaves of rings.** Whiskered
along the localization of the homotopy category,
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackModulesIsoMapDerivedCategory`
carries the comparison of the degreewise functor back to
`CategoryTheory.SimplicialSiteSituation.derivedTransitionComparisonModules`. It is
`…whiskerLeft_derivedTransitionPullbackIsoMapDerivedCategory_hom` of
`CategoryTheory.SimplicialSiteSituation` at that spelling, and it is the hypothesis under which
the derived transitions of Stacks 0D9P may be compared with the `Q`-level machinery. -/
theorem whiskerLeft_derivedTransitionPullbackModulesIsoMapDerivedCategory_hom
    {n m : SimplexCategory} (φ : n ⟶ m) (hφ : (S.transitionRingedToposHom O φ).IsFlat) :
    letI : (S.transitionPullbackModules' O φ).Additive :=
      inferInstanceAs ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).Additive
    letI : PreservesFiniteLimits (S.transitionPullbackModules' O φ) :=
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).1
    letI : PreservesFiniteColimits (S.transitionPullbackModules' O φ) :=
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ hφ)).2
    Functor.whiskerLeft DerivedCategory.Qh
        (S.derivedTransitionPullbackModulesIsoMapDerivedCategory O φ hφ).hom ≫
      (S.transitionPullbackModules' O φ).mapDerivedCategoryFactorsh.hom =
      S.derivedTransitionComparisonModules O φ :=
  S.whiskerLeft_derivedTransitionPullbackIsoMapDerivedCategory_hom O φ hφ

/-- **Stacks 0D72 (6) on derived categories of modules: the summand inclusions are the canonical
maps.** Granted the sheaf-level leg equation
`CategoryTheory.SimplicialSiteSituation.ModuleSumFormulaLegEq`, the `φ`th summand inclusion of
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula`, followed by the inverse of that
formula, is the unit of `Lg_{n!} ⊣ Lg_n^*` carried along `Lf_φ^*` and then the derived transition
of Stacks 0D9P.

This is
`CategoryTheory.biproduct_ι_derivedCompBiproductIso_inv_liftedTransition` instantiated at the
module formula: the sheaf-level presentation is
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaBiproduct`, its summand inclusions are
the canonical legs by
`CategoryTheory.SimplicialSiteSituation.biproduct_ι_moduleSumFormulaBiproduct_inv`, and the
summands of the derived formula are the derived pullbacks through the four restatements above. -/
theorem derivedModuleSumFormulaSummand_of_moduleSumFormulaLegEq
    (hleg : S.ModuleSumFormulaLegEq O)
    (hflat : ∀ (n m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat) :
    DerivedModuleSumFormulaSummand S O hflat := by
  intro n m φ X
  let : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  let : PreservesFiniteLimits
      (S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) :=
    ((exactFunctor_iff _).1 (S.exactFunctor_componentModuleLowerShriek' O n (hflat n))).1
  let : PreservesFiniteColimits
      (S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) :=
    ((exactFunctor_iff _).1 (S.exactFunctor_componentModuleLowerShriek' O n (hflat n))).2
  let : (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : ∀ k, (S.componentModuleRestriction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) k).Additive :=
    fun _ => ⟨rfl⟩
  let : ∀ k, PreservesFiniteLimits
      (S.componentModuleRestriction
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) k) :=
    S.componentModulesRestriction_preservesFiniteLimits O
  let : ∀ k, PreservesFiniteColimits
      (S.componentModuleRestriction
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) k) :=
    S.componentModulesRestriction_preservesFiniteColimits O
  let : ∀ ψ : n ⟶ m, (S.transitionPullbackModules' O ψ).Additive := fun ψ =>
    inferInstanceAs ((S.transitionRingedToposHom O ψ).toModulesHom.pullbackModules).Additive
  let : ∀ ψ : n ⟶ m, PreservesFiniteLimits (S.transitionPullbackModules' O ψ) := fun ψ =>
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O ψ (hflat n m ψ))).1
  let : ∀ ψ : n ⟶ m, PreservesFiniteColimits (S.transitionPullbackModules' O ψ) := fun ψ =>
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O ψ (hflat n m ψ))).2
  let : Limits.HasFiniteBiproducts
      (SheafOfModules.{u} (S.componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) ⥤
        SheafOfModules.{u} (S.componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m)) :=
    Limits.HasFiniteBiproducts.of_hasFiniteProducts
  exact biproduct_ι_derivedCompBiproductIso_inv_liftedTransition
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)))
    (SheafOfModules.{u} (S.componentRingSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n))
    (SheafOfModules.{u} (S.componentRingSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m))
    (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n)
    (S.componentModuleRestriction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n)
    (S.componentModuleRestriction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m)
    (fun ψ : n ⟶ m => S.transitionPullbackModules' O ψ)
    (S.moduleSumFormulaBiproduct O n m)
    (S.componentModuleLowerShriekAdjunction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n)
    (fun ψ => S.componentModuleTransition O ψ)
    (fun ψ => S.biproduct_ι_moduleSumFormulaBiproduct_inv O hleg ψ)
    (fun ψ => S.derivedTransitionPullbackModules O ψ)
    (fun ψ => S.derivedTransitionComparisonModules O ψ)
    (fun ψ => S.derivedTransitionPullbackModulesIsoMapDerivedCategory O ψ (hflat n m ψ))
    (fun ψ => S.whiskerLeft_derivedTransitionPullbackModulesIsoMapDerivedCategory_hom O ψ
      (hflat n m ψ)) X φ

end CategoryTheory.SimplicialSiteSituation

end
