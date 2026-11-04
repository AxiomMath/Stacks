module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CupClassOnCohomology

/-!
# Naturality of the cup product on cohomology

Let `(X, 𝒪_X)` be a ringed space, `A = Γ(X, 𝒪_X)` and `κ` a global cup product
`RΓ(X, K) ⊗^𝐋_A RΓ(X, M) ⟶ RΓ(X, K ⊗^𝐋 M)`. The induced pairing of Cohomology, Section 0FKU,

`∪ : Hⁱ(X, K) × Hʲ(X, M) ⟶ Hⁱ⁺ʲ(X, K ⊗^𝐋 M)`,

`Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing`, is natural in both complexes: for
morphisms `u : K ⟶ K'` and `v : M ⟶ M'` of `D(𝒪_X)` the cup product of the images of two classes is
the image of their cup product under `Hⁱ⁺ʲ(u ⊗^𝐋 v)`.

The pairing is formed by the tensoring of classes of Tag 068H, whose naturality the library has
only at K-projective K-flat sources
(`RingTheory.TorProducts.cohomologyTensorProduct_naturality_of_isKProjective`). That is enough: a
class `ξ ∈ Hⁱ(X, K)` is the image of the generator of `Hⁱ(A[-i])` under the morphism
`A[-i] ⟶ RΓ(X, K)` representing it, and `A[-i]` is K-projective and K-flat
(`Stacks.Cohomology.DerivedGlobalCupProduct.tensorGenerator_comp`). The representing morphism of
the image of `ξ` under `u` is the representing morphism of `ξ` followed by `RΓ(u)`, by the
naturality of the corepresentability isomorphism of Tag 06XS, and the naturality of `κ` finishes
the argument.

## Main results

* `Stacks.Cohomology.DerivedGlobalCupProduct.classRepresentative_comp`: the morphism representing
  the image of a class is the representing morphism followed by `RΓ(u)`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_naturality`: **the cup product is natural
  in both complexes**, for classes given as morphisms out of `A`.
* `Stacks.Cohomology.DerivedGlobalCupProduct.cupPairing_naturality_apply`: the same on elements.

## References

* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedGlobalCupProduct

attribute [local instance] HasDerivedCategory.standard

variable {X : RingedSpace.{u, u}}

/-- **The morphism representing the image of a class.** If `ξ ∈ Hⁱ(X, K)` is represented by
`A[-i] ⟶ RΓ(X, K)`, then its image under `u : K ⟶ K'` is represented by that morphism followed by
`RΓ(u)`. This is the naturality of the corepresentability isomorphism of Tag 06XS. -/
theorem classRepresentative_comp
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (u : K ⟶ K') (i : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i) :
    classRepresentative K' i
        (ξ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) i).map
          ((baseSections X).map u)) =
      classRepresentative K i ξ ≫ (baseSections X).map u := by
  rw [classRepresentative, LinearEquiv.symm_apply_eq,
    DerivedCategory.homologyFromSingleLinearEquiv_comp, classRepresentative,
    LinearEquiv.apply_symm_apply]

/-- **The cup product of Section 0FKU is natural in both complexes.** For morphisms `u : K ⟶ K'`
and `v : M ⟶ M'` of `D(𝒪_X)` and classes `ξ ∈ Hⁱ(X, K)` and `η ∈ Hʲ(X, M)`, given as morphisms
out of `A = Γ(X, 𝒪_X)`, the cup product of `Hⁱ(u)(ξ)` and `Hʲ(v)(η)` is the image of `ξ ∪ η` under
`Hⁱ⁺ʲ(u ⊗^𝐋 v)`. -/
theorem cupPairing_naturality (κ : GlobalCupProduct X)
    {K K' M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (u : K ⟶ K') (v : M ⟶ M') (i j : ℤ)
    (ξ : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule K i)
    (η : ModuleCat.of (baseRing X) (baseRing X) ⟶ cohomologyModule M j) :
    (λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫
        ((ξ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) i).map
            ((baseSections X).map u)) ⊗ₘ
          (η ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) j).map
            ((baseSections X).map v))) ≫
        cupPairing κ K' M' i j =
      (λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫ (ξ ⊗ₘ η) ≫ cupPairing κ K M i j ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
          ((baseSections X).map
            ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map (u ×ₘ v))) := by
  have hT : ((tensorBase X).map (classRepresentative K i ξ ≫ (baseSections X).map u)).app
        (baseShift X j) ≫
      ((tensorBase X).obj ((baseSections X).obj K')).map
        (classRepresentative M j η ≫ (baseSections X).map v) =
      (((tensorBase X).map (classRepresentative K i ξ)).app (baseShift X j) ≫
        ((tensorBase X).obj ((baseSections X).obj K)).map (classRepresentative M j η)) ≫
        (Functor.uncurry.obj (tensorBase X)).map
          ((baseSections X).map u ×ₘ (baseSections X).map v) := by
    simp only [Functor.uncurry_obj_map, Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rw [NatTrans.naturality_assoc]
  have h2 := tensorGenerator_comp K' M' i j
    (ξ ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) i).map
      ((baseSections X).map u))
    (η ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) j).map
      ((baseSections X).map v))
  rw [classRepresentative_comp, classRepresentative_comp, hT, Functor.map_comp,
    ← Category.assoc, tensorGenerator_comp] at h2
  have h3 := h2 =≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
    (κ.app (K', M'))
  simp only [Category.assoc] at h3
  have key : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
        ((Functor.uncurry.obj (tensorBase X)).map
          ((baseSections X).map u ×ₘ (baseSections X).map v)) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
        (κ.app (K', M')) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
          (κ.app (K, M)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
          ((baseSections X).map
            ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map (u ×ₘ v))) := by
    rw [← Functor.map_comp, ← Functor.map_comp, globalCupProduct_naturality]
  dsimp only [cupPairing]
  simp only [Category.assoc]
  have h4 := ((λ_ (ModuleCat.of (baseRing X) (baseRing X))).inv ≫ (ξ ⊗ₘ η) ≫
    (RingTheory.TorProducts.cohomologyTensorProduct ((baseSections X).obj K)
      ((baseSections X).obj M) i j).map) ≫= key
  simp only [Category.assoc] at h4
  exact h3.symm.trans h4

/-- A composite out of `R ⊗ R` read at `1`: precomposed with the left unitor and a tensor product
of two maps out of `R`, it is the value at the tensor of the two values at `1`. -/
private lemma leftUnitor_inv_tensorHom_comp_apply_one {R : CommRingCat.{u}}
    {P Q T : ModuleCat.{u} R} (f : ModuleCat.of R R ⟶ P) (g : ModuleCat.of R R ⟶ Q)
    (h : P ⊗ Q ⟶ T) :
    ((λ_ (ModuleCat.of R R)).inv ≫ (f ⊗ₘ g) ≫ h) (1 : R) = h (f (1 : R) ⊗ₜ g (1 : R)) := by
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply, ModuleCat.MonoidalCategory.tensorHom_tmul]

/-- **The cup product of Section 0FKU is natural in both complexes**, on elements:
`Hⁱ(u)(ξ) ∪ Hʲ(v)(η) = Hⁱ⁺ʲ(u ⊗^𝐋 v)(ξ ∪ η)`. -/
theorem cupPairing_naturality_apply (κ : GlobalCupProduct X)
    {K K' M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (u : K ⟶ K') (v : M ⟶ M') (i j : ℤ) (x : cohomologyModule K i)
    (y : cohomologyModule M j) :
    (cupPairing κ K' M' i j).hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) i).map
            ((baseSections X).map u) x ⊗ₜ
          (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) j).map
            ((baseSections X).map v) y) =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X)) (i + j)).map
          ((baseSections X).map
            ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map (u ×ₘ v)))).hom
        ((cupPairing κ K M i j).hom (x ⊗ₜ y)) := by
  have h := ConcreteCategory.congr_hom (cupPairing_naturality κ u v i j
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing X) _ x))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (baseRing X) _ y))) (1 : baseRing X)
  rw [leftUnitor_inv_tensorHom_comp_apply_one, leftUnitor_inv_tensorHom_comp_apply_one] at h
  simpa using h

end Stacks.Cohomology.DerivedGlobalCupProduct

end
