module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedTransitionPullbackExact
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedLowerShriek
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem

/-!
# The componentwise direct sum for modules on derived categories

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site all of whose structure-sheaf transitions `f_φ^{-1}O_n ⟶ O_m` out of degree `n` are
flat. The componentwise direct-sum formula of Stacks 0D72 (6) for sheaves of modules,

`g_m^*(g_{n!}G) = ⨁_{φ : [n] ⟶ [m]} f_φ^*G`,

is `CategoryTheory.SimplicialSiteSituation.moduleSumFormula`. Under the flatness hypothesis both
`g_{n!}` (Stacks 0D74) and every transition pullback `f_φ^*` (Stacks 04JC) are exact, so the
formula descends to the unbounded derived categories: the restriction to degree `m` of the
derived lower shriek from degree `n` is the direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of
the derived pullbacks `Lf_φ^*` of Stacks 06YY.

This is the identification that Stacks 0D9E (2) restricts its canonical map along. It discharges
the `sourceIso` hypothesis of
`SimplicialSiteSituation.isCartesianDerivedModule_iff_isIso_moduleProjection_of_sourceIso`,
yielding `SimplicialSiteSituation.isCartesianDerivedModule_iff_isIso_moduleProjection`.

## Main definitions

* `CategoryTheory.derivedCompBiproductIso`: for exact functors `F : A ⥤ B` and `G : B ⥤ C` of
  abelian categories and a presentation of `F ⋙ G` as a finite direct sum of exact functors, the
  resulting presentation of `G.mapDerivedCategory ∘ F.mapDerivedCategory` at an object of `D(A)`.
* `CategoryTheory.SimplicialSiteSituation.moduleSumFormulaBiproduct`: the componentwise
  direct-sum formula of Stacks 0D72 (6) read as a biproduct rather than a coproduct.
* `CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaMapDerivedCategory`: the formula
  on derived categories, with the summands spelled as the derived functors of the degreewise
  transition pullbacks.
* `CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula`: **the componentwise
  direct-sum formula of Stacks 0D72 (6) on unbounded derived categories of sheaves of modules**,
  with the summands spelled as the derived pullbacks `Lf_φ^*` of Stacks 06YY.

## Implementation notes

*No summand description is produced.* The isomorphism is abstract, exactly as
`CategoryTheory.SimplicialSiteSituation.moduleSumFormula` is: that formula comes with no
identification of its summand inclusions, and nothing here manufactures one. What the formula is
used for is the invertibility criterion for a map of finite direct sums, which needs only the
existence of some isomorphism.

*Why the construction is split in three.* The three steps are assembled from
`CategoryTheory.derivedCompIso` (an exact-functor compositor on derived categories),
`CategoryTheory.derivedBiproductIso` (the derived functor of a finite direct sum of exact
functors) and
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIsoMapDerivedCategory` (the
derived pullback along a flat transition is the degreewise one). They are kept in separate
declarations because the two spellings of the module categories of the simplicial components —
`AlgebraicGeometry.RingedTopos.Modules` of
`CategoryTheory.SimplicialSiteSituation.componentRingedTopos`, and `SheafOfModules` over
`CategoryTheory.SimplicialSiteSituation.componentRingSheaf` — agree only by `rfl` and not
reducibly. Instance search does not cross between them, and the `Abelian` and
`HasDerivedCategory` arguments hidden in `CategoryTheory.Functor.mapDerivedCategory` are data, so
a witness found at one spelling is not the term demanded at the other. Each declaration therefore
works in a single spelling throughout, and the crossing happens once, where a term of one
spelling is accepted against a statement in the other.

*Why the statements carry `letI`s.* Flatness is a proposition and not a class, so the exactness
it yields cannot be found by instance search; since `CategoryTheory.Functor.mapDerivedCategory`
takes exactness as instance arguments, the witnesses must already be in scope in the *statement*.
They are introduced there by `letI`, from the flatness hypothesis and from nothing else. The final
statement `…derivedModuleSumFormula` needs none of them: it is spelled entirely with
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullback`, whose existence is the ambient
instance hypothesis of Stacks 06YY.

## References

* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D74](https://stacks.math.columbia.edu/tag/0D74)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules

universe u

namespace CategoryTheory

/-- **The derived functor of a composite presented as a finite direct sum.** Let `F : A ⥤ B` and
`G : B ⥤ C` be exact functors of abelian categories with derived categories, and let
`e : F ⋙ G ≅ ⨁ L` present the composite as a finite direct sum of exact functors `L i : A ⥤ C`.
Then the composite of the induced functors of derived categories is, at every object, the direct
sum of the functors induced by the `L i`.

The comparison is the compositor `CategoryTheory.derivedCompIso` followed by
`CategoryTheory.derivedBiproductIso`; like both of those it carries no description of its summand
inclusions. -/
noncomputable def derivedCompBiproductIso
    (A : Type*) [Category A] [Abelian A] [HasDerivedCategory A]
    (B : Type*) [Category B] [Abelian B] [HasDerivedCategory B]
    (C : Type*) [Category C] [Abelian C] [HasDerivedCategory C]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {ι : Type*} [Fintype ι] (L : ι → A ⥤ C) [Limits.HasBiproduct L]
    [∀ i, (L i).Additive] [∀ i, PreservesFiniteLimits (L i)]
    [∀ i, PreservesFiniteColimits (L i)] (e : F ⋙ G ≅ ⨁ L) (X : DerivedCategory A) :
    G.mapDerivedCategory.obj (F.mapDerivedCategory.obj X) ≅
      ⨁ fun i => (L i).mapDerivedCategory.obj X :=
  ((derivedCompIso F G _ (Iso.refl _)).app X).symm ≪≫ derivedBiproductIso (F ⋙ G) L e X

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] HasDerivedCategory.standard
  CategoryTheory.SimplicialSiteSituation.hasWeakSheafifyComponent

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

variable [∀ (m n : SimplexCategory) (φ : m ⟶ n),
  (pullbackOnHomotopy (S.transitionRingedToposHom O φ)).HasLeftDerivedFunctor
    (targetQuasiIso (S.componentRingedTopos O m))]

/-- **The componentwise direct-sum formula of Stacks 0D72 (6) as a biproduct.** The restriction
to degree `m` of lower shriek from degree `n` is the direct sum, over the simplex maps
`φ : [n] ⟶ [m]`, of the pullbacks of sheaves of modules along the transition morphisms of ringed
topoi.

This is `CategoryTheory.SimplicialSiteSituation.moduleSumFormula` with its coproduct replaced by
the biproduct over the same finite family, which is the form that the derived-category comparison
`CategoryTheory.derivedBiproductIso` consumes. -/
def moduleSumFormulaBiproduct (n m : SimplexCategory) :
    letI : HasFiniteBiproducts
        (SheafOfModules.{u} (S.componentRingSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) ⥤
          SheafOfModules.{u} (S.componentRingSheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m)) :=
      HasFiniteBiproducts.of_hasFiniteProducts
    S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n ⋙
        S.componentModuleRestriction
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m ≅
      ⨁ fun φ : n ⟶ m => S.transitionPullbackModules' O φ :=
  letI : HasFiniteBiproducts
      (SheafOfModules.{u} (S.componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) ⥤
        SheafOfModules.{u} (S.componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  S.moduleSumFormula O n m ≪≫
    (biproduct.isoCoproduct fun φ : n ⟶ m => S.transitionPullbackModules' O φ).symm

/-- **The componentwise direct-sum formula of Stacks 0D72 (6) on derived categories**, with each
summand spelled as the functor of derived categories induced by the degreewise transition
pullback.

Granted flatness of the transitions out of degree `n`, lower shriek `g_{n!}` is exact by
Stacks 0D74 and each transition pullback `f_φ^*` is exact by Stacks 04JC, so all of these
functors induce functors of the unbounded derived categories, and the sheaf-level formula
`CategoryTheory.SimplicialSiteSituation.moduleSumFormulaBiproduct` descends to them by
`CategoryTheory.derivedCompBiproductIso`.

`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormula` is this formula with the
summands rewritten as the derived pullbacks of Stacks 06YY, which is the shape its consumers
use. -/
def derivedModuleSumFormulaMapDerivedCategory (n m : SimplexCategory)
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (X : DerivedCategory
      (SheafOfModules.{u} (S.componentRingSheaf
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n))) :
    letI : PreservesFiniteLimits
        (S.componentModuleLowerShriek
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) :=
      ((exactFunctor_iff _).1 (S.exactFunctor_componentModuleLowerShriek' O n hflat)).1
    letI : PreservesFiniteColimits
        (S.componentModuleLowerShriek
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) :=
      ((exactFunctor_iff _).1 (S.exactFunctor_componentModuleLowerShriek' O n hflat)).2
    letI : (S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n).Additive :=
      Functor.additive_of_preserves_binary_products _
    letI : PreservesFiniteLimits
        (S.componentModuleRestriction
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m) :=
      S.componentModulesRestriction_preservesFiniteLimits O m
    letI : PreservesFiniteColimits
        (S.componentModuleRestriction
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m) :=
      S.componentModulesRestriction_preservesFiniteColimits O m
    letI : (S.componentModuleRestriction
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m).Additive :=
      ⟨rfl⟩
    letI : ∀ φ : n ⟶ m, (S.transitionPullbackModules' O φ).Additive := fun φ =>
      inferInstanceAs ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).Additive
    letI : ∀ φ : n ⟶ m, PreservesFiniteLimits (S.transitionPullbackModules' O φ) := fun φ =>
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ (hflat m φ))).1
    letI : ∀ φ : n ⟶ m, PreservesFiniteColimits (S.transitionPullbackModules' O φ) := fun φ =>
      ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ (hflat m φ))).2
    (S.componentModuleRestriction
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))
        m).mapDerivedCategory.obj
        ((S.componentModuleLowerShriek
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O))
          n).mapDerivedCategory.obj X) ≅
      ⨁ fun φ : n ⟶ m => (S.transitionPullbackModules' O φ).mapDerivedCategory.obj X := by
  letI : PreservesFiniteLimits
      (S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) :=
    ((exactFunctor_iff _).1 (S.exactFunctor_componentModuleLowerShriek' O n hflat)).1
  letI : PreservesFiniteColimits
      (S.componentModuleLowerShriek
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) :=
    ((exactFunctor_iff _).1 (S.exactFunctor_componentModuleLowerShriek' O n hflat)).2
  letI : (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n).Additive :=
    Functor.additive_of_preserves_binary_products _
  letI : PreservesFiniteLimits
      (S.componentModuleRestriction
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m) :=
    S.componentModulesRestriction_preservesFiniteLimits O m
  letI : PreservesFiniteColimits
      (S.componentModuleRestriction
        ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m) :=
    S.componentModulesRestriction_preservesFiniteColimits O m
  letI : (S.componentModuleRestriction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m).Additive :=
    ⟨rfl⟩
  letI : ∀ φ : n ⟶ m, (S.transitionPullbackModules' O φ).Additive := fun φ =>
    inferInstanceAs ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).Additive
  letI : ∀ φ : n ⟶ m, PreservesFiniteLimits (S.transitionPullbackModules' O φ) := fun φ =>
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ (hflat m φ))).1
  letI : ∀ φ : n ⟶ m, PreservesFiniteColimits (S.transitionPullbackModules' O φ) := fun φ =>
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ (hflat m φ))).2
  letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  letI : HasFiniteBiproducts
      (SheafOfModules.{u} (S.componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n) ⥤
        SheafOfModules.{u} (S.componentRingSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  exact derivedCompBiproductIso
    (SheafOfModules.{u} (S.componentRingSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n))
    (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)))
    (SheafOfModules.{u} (S.componentRingSheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m))
    (S.componentModuleLowerShriek
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) n)
    (S.componentModuleRestriction
      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.totalTopology) O)) m)
    (fun φ : n ⟶ m => S.transitionPullbackModules' O φ) (S.moduleSumFormulaBiproduct O n m) X

/-- **The componentwise direct-sum formula of Stacks 0D72 (6) on unbounded derived categories of
sheaves of modules.** Let `O` be a sheaf of commutative rings on the total site whose
structure-sheaf transitions out of degree `n` are flat. The restriction to degree `m` of the
derived lower shriek from degree `n` is the direct sum, over the simplex maps `φ : [n] ⟶ [m]`, of
the derived pullbacks `Lf_φ^*` along the transition morphisms of ringed topoi.

This is
`CategoryTheory.SimplicialSiteSituation.derivedModuleSumFormulaMapDerivedCategory` composed
summandwise with
`CategoryTheory.SimplicialSiteSituation.derivedTransitionPullbackIsoMapDerivedCategory`: along a
flat transition nothing is derived, so `Lf_φ^*` *is* the functor induced degreewise by `f_φ^*`.

Like the sheaf-level formula it comes with no description of its summand inclusions; it is the
abstract isomorphism, which is what the invertibility criterion for a map of finite direct sums
asks for. At `X = K_n` it is the identification of the restriction to degree `m` of
`g_{n!}K_n` that Stacks 0D9E (2) restricts its canonical map along, and it is supplied there by
`CategoryTheory.SimplicialSiteSituation.isCartesianDerivedModule_iff_isIso_moduleProjection`. -/
def derivedModuleSumFormula (n m : SimplexCategory)
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (X : DerivedCategory (S.componentRingedTopos O n).Modules) :
    (S.derivedComponentModuleRestriction O m).obj
        ((S.componentModuleLowerShriekDerived O n hflat).obj X) ≅
      ⨁ fun φ : n ⟶ m => (S.derivedTransitionPullback O φ).obj X := by
  letI : Fintype (n ⟶ m) := Fintype.ofFinite (n ⟶ m)
  letI : ∀ φ : n ⟶ m, (S.transitionPullbackModules' O φ).Additive := fun φ =>
    inferInstanceAs ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).Additive
  letI : ∀ φ : n ⟶ m, PreservesFiniteLimits (S.transitionPullbackModules' O φ) := fun φ =>
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ (hflat m φ))).1
  letI : ∀ φ : n ⟶ m, PreservesFiniteColimits (S.transitionPullbackModules' O φ) := fun φ =>
    ((exactFunctor_iff _).1 (S.exactFunctor_transitionPullbackModules' O φ (hflat m φ))).2
  refine ?_ ≪≫ biproduct.mapIso fun φ : n ⟶ m =>
    ((S.derivedTransitionPullbackIsoMapDerivedCategory O φ (hflat m φ)).app X).symm
  exact S.derivedModuleSumFormulaMapDerivedCategory O n m hflat X

end CategoryTheory.SimplicialSiteSituation

end
