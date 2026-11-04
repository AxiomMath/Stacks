module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleDescentSystem

/-!
# Cartesian modules on a simplicial site are pairs with a cocycle isomorphism (Stacks 07TH)

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
Stacks 07TH says that the category of cartesian sheaves of `O`-modules on the total site is
equivalent to the category of pairs `(ℱ, α)` of an `O_0`-module `ℱ` and an isomorphism
`α : f_{δ¹₁}^*ℱ ≅ f_{δ¹₀}^*ℱ` of `O_1`-modules satisfying the cocycle condition
`f_{δ²₁}^*α = f_{δ²₀}^*α ∘ f_{δ²₂}^*α` of `O_2`-modules. The functor is
`CategoryTheory.SimplicialSiteSituation.cartesianModulePairFunctor`, which takes a cartesian module
to its degree-zero restriction and the comparison of its two transitions to degree one.

## Main results

* `CategoryTheory.SimplicialSiteSituation.cartesianModuleSheafEquivCartesianModulePair`: the
  equivalence of Stacks 07TH.
* `CategoryTheory.SimplicialSiteSituation.cartesianModulePairFunctor_full`: the functor is full.
* `CategoryTheory.SimplicialSiteSituation.cartesianModulePairFunctor_essSurj`: the functor is
  essentially surjective.

## Implementation notes

Faithfulness is `CategoryTheory.SimplicialSiteSituation.cartesianModulePairFunctor_faithful`.

Fullness: a morphism of pairs is a morphism in degree zero between the degree-zero objects of
the cartesian systems of the two modules which is compatible with their comparison isomorphisms,
so by `CategoryTheory.SimplicialPseudoFamily.CartesianSystem.homFamily_naturality` it extends to a
family of morphisms compatible with every transition, which
`CategoryTheory.SimplicialSiteSituation.totalModuleHomOfFamily` assembles into a morphism of
sheaves of `O`-modules.

Essential surjectivity: a pair `(ℱ, α)` with the cocycle condition defines the cartesian system
`CategoryTheory.SimplicialPseudoFamily.pairSystem` of modules on the components, with the
pullback of `ℱ` along the last vertex `[0] → [n]` in degree `n`; it descends to the cartesian
sheaf of modules `CategoryTheory.SimplicialSiteSituation.systemTotalCartesianModule` on the total
site, whose pair is `(ℱ, α)` by `CategoryTheory.SimplicialPseudoFamily.comm_of_iso_pairSystem`.

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### Fullness -/

/-- The morphism of degree-zero modules underlying a morphism of pairs between the pairs of two
cartesian modules is compatible with their cartesian systems. -/
theorem isCompatible_of_pairHom {M N : S.CartesianModuleSheaf O}
    (f : (S.cartesianModulePairFunctor O).obj M ⟶ (S.cartesianModulePairFunctor O).obj N) :
    (S.cartesianModuleSystem O M).IsCompatible (S.cartesianModuleSystem O N) f.map :=
  SimplicialPseudoFamily.CartesianSystem.isCompatible_of_comm f.comm

/-- **Stacks 07TH**, fullness. The functor from cartesian modules to pairs is full. -/
instance cartesianModulePairFunctor_full : (S.cartesianModulePairFunctor O).Full where
  map_surjective {M N} f := by
    let β := SimplicialPseudoFamily.CartesianSystem.homFamily (N := S.cartesianModuleSystem O M)
      (N' := S.cartesianModuleSystem O N) (h := f.map)
    have hβ : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
        (S.componentModulePullback O φ).map (β m) ≫ S.componentTransition O N.obj φ =
          S.componentTransition O M.obj φ ≫ β n := fun φ =>
      SimplicialPseudoFamily.CartesianSystem.homFamily_naturality (S.isCompatible_of_pairHom O f) φ
    exact ⟨ObjectProperty.homMk (S.totalModuleHomOfFamily O β hβ),
      CartesianModulePair.hom_ext S O
        ((S.componentModuleMap_totalModuleHomOfFamily O β hβ ⦋0⦌).trans
          SimplicialPseudoFamily.CartesianSystem.homFamily_zero)⟩

/-! ### Essential surjectivity -/

section EssSurj

/-- The comparison isomorphism of the pair of a cartesian module is the transition of its
cartesian system along `δ¹₁` followed by the inverse of its transition along `δ¹₀`. -/
theorem cartesianModuleSystem_trans_comp_inv (M : S.CartesianModuleSheaf O) :
    ((S.cartesianModuleSystem O M).trans (SimplexCategory.δ (1 : Fin 2))).hom ≫
        ((S.cartesianModuleSystem O M).trans (SimplexCategory.δ (0 : Fin 2))).inv =
      ((S.cartesianModulePairFunctor O).obj M).iso.hom :=
  rfl

/-- A cartesian module whose cartesian system is identified, compatibly with the transitions,
with the cartesian system of a pair `(F, α)` has `(F, α)` as its pair, through the identification
in degree zero. -/
theorem comm_of_iso_pairSystem_modules (F : (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj F)
    (hα : (S.modulePseudoFamily O).IsCocycle F α) (M : S.CartesianModuleSheaf O)
    (e : ∀ n, (S.cartesianModuleSystem O M).obj n ≅
      ((S.modulePseudoFamily O).pairSystem F α hα).obj n)
    (he : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ((S.cartesianModuleSystem O M).trans φ).hom ≫ (e n).hom =
        ((S.modulePseudoFamily O).map φ).map (e m).hom ≫
          (((S.modulePseudoFamily O).pairSystem F α hα).trans φ).hom)
    (E : ((S.cartesianModulePairFunctor O).obj M).module ≅ F)
    (hE : E.hom = (e ⦋0⦌).hom ≫ ((S.modulePseudoFamily O).pairZeroIso F).hom) :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map E.hom ≫ α.hom =
      ((S.cartesianModulePairFunctor O).obj M).iso.hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map E.hom :=
  (S.modulePseudoFamily O).comm_of_iso_pairSystem_of_eq F α hα (S.cartesianModuleSystem O M) e he
    E hE ((S.cartesianModulePairFunctor O).obj M).iso
    (S.cartesianModuleSystem_trans_comp_inv O M).symm

variable {S O} (A : CartesianModulePair S O)

/-- A cartesian module whose cartesian system is identified, compatibly with the transitions,
with the cartesian system of a pair has that pair as its pair. -/
def pairIsoOfIsoPairSystem (hA : (S.modulePseudoFamily O).IsCocycle A.module A.iso)
    (M : S.CartesianModuleSheaf O)
    (e : ∀ n, (S.cartesianModuleSystem O M).obj n ≅
      ((S.modulePseudoFamily O).pairSystem A.module A.iso hA).obj n)
    (he : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ((S.cartesianModuleSystem O M).trans φ).hom ≫ (e n).hom =
        ((S.modulePseudoFamily O).map φ).map (e m).hom ≫
          (((S.modulePseudoFamily O).pairSystem A.module A.iso hA).trans φ).hom)
    (E : ((S.cartesianModulePairFunctor O).obj M).module ≅ A.module)
    (hE : E.hom = (e ⦋0⦌).hom ≫ ((S.modulePseudoFamily O).pairZeroIso A.module).hom) :
    (S.cartesianModulePairFunctor O).obj M ≅ A :=
  CartesianModulePair.isoMk S O E
    (comm_of_iso_pairSystem_modules S O A.module A.iso hA M e he E hE)

/-- The identification of the degree-zero module of the pair of the cartesian module descended
from a pair with the degree-zero module of that pair. -/
def pairCartesianModuleZeroIso :
    ((S.cartesianModulePairFunctor O).obj (systemTotalCartesianModule
      ((S.modulePseudoFamily O).pairSystem A.module A.iso
        (S.isCocycle_of_isModuleCocycle O A.module A.iso A.cocycle)))).module ≅ A.module :=
  systemTotalModuleObjIso ((S.modulePseudoFamily O).pairSystem A.module A.iso
      (S.isCocycle_of_isModuleCocycle O A.module A.iso A.cocycle)) ⦋0⦌ ≪≫
    (S.modulePseudoFamily O).pairZeroIso A.module

/-- The pair of the cartesian module descended from a pair is that pair. -/
def pairCartesianModulePairIso :
    (S.cartesianModulePairFunctor O).obj (systemTotalCartesianModule
      ((S.modulePseudoFamily O).pairSystem A.module A.iso
        (S.isCocycle_of_isModuleCocycle O A.module A.iso A.cocycle))) ≅ A :=
  pairIsoOfIsoPairSystem A (S.isCocycle_of_isModuleCocycle O A.module A.iso A.cocycle)
    (systemTotalCartesianModule ((S.modulePseudoFamily O).pairSystem A.module A.iso
      (S.isCocycle_of_isModuleCocycle O A.module A.iso A.cocycle)))
    (systemTotalModuleObjIso ((S.modulePseudoFamily O).pairSystem A.module A.iso
      (S.isCocycle_of_isModuleCocycle O A.module A.iso A.cocycle)))
    (fun φ => cartesianModuleSystem_trans_systemTotalCartesianModule
      ((S.modulePseudoFamily O).pairSystem A.module A.iso
        (S.isCocycle_of_isModuleCocycle O A.module A.iso A.cocycle)) φ)
    (pairCartesianModuleZeroIso A) rfl

/-- **Stacks 07TH**, essential surjectivity. Every pair is the pair of a cartesian module. -/
instance cartesianModulePairFunctor_essSurj : (S.cartesianModulePairFunctor O).EssSurj where
  mem_essImage A := ⟨_, ⟨pairCartesianModulePairIso A⟩⟩

end EssSurj

/-- The functor from cartesian modules to pairs is an equivalence. -/
instance cartesianModulePairFunctor_isEquivalence :
    (S.cartesianModulePairFunctor O).IsEquivalence := {}

/-- **Stacks 07TH.** Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on
its total site. The category of cartesian sheaves of `O`-modules is equivalent to the category of
pairs `(ℱ, α)`, where `ℱ` is an `O₀`-module and `α : f_{δ¹₁}^*ℱ ≅ f_{δ¹₀}^*ℱ` is an isomorphism
of `O₁`-modules such that `f_{δ²₁}^*α = f_{δ²₀}^*α ∘ f_{δ²₂}^*α` as `O₂`-module maps. The functor
of the equivalence takes a cartesian module to its degree-zero restriction and the comparison of
its two transitions to degree one. -/
@[stacks 07TH]
def cartesianModuleSheafEquivCartesianModulePair :
    S.CartesianModuleSheaf O ≌ CartesianModulePair S O :=
  (S.cartesianModulePairFunctor O).asEquivalence

end CategoryTheory.SimplicialSiteSituation

end
