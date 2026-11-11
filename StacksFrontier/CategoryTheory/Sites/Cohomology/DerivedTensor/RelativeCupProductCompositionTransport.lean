module

public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.PullbackToposTensorIsoCompositionDescent
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# The relative cup product under a change of adjunction, and at a composite morphism

For morphisms of ringed topoi `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` and
`f' : (Sh(C'), 𝒪') ⟶ (Sh(C''), 𝒪'')`, the derived pushforwards `R(f' ∘ f)_*` and `Rf'_*Rf_*` are
isomorphic through `Stacks.Cohomology.DerivedBaseChangePasting.derivedPushforwardCompIso`, the
conjugate of the composition isomorphism `L(f')^*Lf^* ≅ L(f' ∘ f)^*`. This file shows that, along
that isomorphism, the relative cup product `relativeCupProduct (f'.comp f)` of the composite is
the composite of the relative cup products of `f'` and of `f`.

## Main results

* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_conjugate`: for two
  adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂`, a 2-cell `κ : L₂ ⟶ L₁` and comparisons `α₁`, `α₂` of the two
  bifunctors along `L₁` and along `L₂`, if `κ` is *monoidal* for `α₁` and `α₂` then the cup
  product of the first adjunction, followed by the conjugate `R₁ ⟶ R₂` of `κ`, is the conjugate
  in each tensor factor followed by the cup product of the second adjunction.
* `Stacks.Cohomology.RelativeCupProductOnRingedTopoi.relativeCupProduct_comp_pushforwardCompIso`:
  the relative cup product of `f' ∘ f`, followed by the composition isomorphism
  `R(f' ∘ f)_* ≅ Rf'_*Rf_*`, is the composition isomorphism in each tensor factor followed by the
  relative cup product of `f'` and the image under `Rf'_*` of the relative cup product of `f`.

## Implementation notes

The composite `L(f' ∘ f)^*` is written with the instance argument `HasLeftDerivedFunctor` for
`pullbackOnHomotopy (f'.comp f)`, as in
`Stacks.Cohomology.DerivedBaseChangePasting.derivedPushforwardCompIso`. The morphism-of-sites
condition on the composite is `AlgebraicGeometry.RingedToposSiteHom.isMorphismOfSites_comp_u`.

## References

* [Stacks Project, Tag 0FPN](https://stacks.math.columbia.edu/tag/0FPN)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0DV0](https://stacks.math.columbia.edu/tag/0DV0)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.Cohomology.DerivedBaseChangePasting
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

universe v₁ v₂ u₁ u₂ u

/-! ### The abstract cup product under a change of adjunction -/

section Conjugate

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
  (A : C × C ⥤ C) (B : D × D ⥤ D)
  (α₁ : A ⋙ L₁ ⟶ L₁.prod L₁ ⋙ B) (α₂ : A ⋙ L₂ ⟶ L₂.prod L₂ ⋙ B) (κ : L₂ ⟶ L₁)

/-- Let `a : L₁ ⊣ R₁` and
`b : L₂ ⊣ R₂` be adjunctions, let `A` and `B` be bifunctors on the two sides, let `α₁` and `α₂`
compare them along `L₁` and along `L₂`, and let `κ : L₂ ⟶ L₁` be *monoidal* for the two
comparisons (`hκ`).  Then the square

```
A(R₁G, R₁H) --cup a--→ R₁ B(G, H)
      | A(κ', κ')            | κ'
      ↓                      ↓
A(R₂G, R₂H) --cup b--→ R₂ B(G, H)
```

commutes, where `κ' = conjugateEquiv a b κ : R₁ ⟶ R₂` is the conjugate of `κ`. -/
theorem adjunctionCupProduct_conjugate
    (hκ : ∀ P Q : C, κ.app (A.obj (P, Q)) ≫ α₁.app (P, Q) =
      α₂.app (P, Q) ≫ B.map (κ.app P ×ₘ κ.app Q))
    (G H : D) :
    adjunctionCupProduct a A B α₁ G H ≫ (conjugateEquiv a b κ).app (B.obj (G, H)) =
      A.map ((conjugateEquiv a b κ).app G ×ₘ (conjugateEquiv a b κ).app H) ≫
        adjunctionCupProduct b A B α₂ G H := by
  rw [adjunctionCupProduct, ← Stacks.CategoryTheory.homEquiv_conjugate' a b κ,
    adjunctionCupProduct_pre]
  congr 1
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj]
  slice_lhs 1 2 => rw [hκ]
  slice_rhs 1 2 => rw [bifunctor_comparison_naturality A B α₂
    ((conjugateEquiv a b κ).app G) ((conjugateEquiv a b κ).app H)]
  simp only [Category.assoc]
  rw [← B.map_comp, ← B.map_comp, prod_comp, prod_comp,
    conjugateEquiv_counit a b κ G, conjugateEquiv_counit a b κ H]

end Conjugate

/-! ### The relative cup product at a composite morphism of ringed topoi -/

section TwoMorphisms

attribute [local instance] HasDerivedCategory.standard

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (P Q : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (f' : RingedToposSiteHom Y Z)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy f').HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (f'.comp f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) (ComplexShape.up ℤ))]
  (hmosf : f.u.IsMorphismOfSites Y.J X.J) (hmosf' : f'.u.IsMorphismOfSites Z.J Y.J)

/-- For
`f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')`, `f' : (Sh(C'), 𝒪') ⟶ (Sh(C''), 𝒪'')` and `K`, `L` in `D(𝒪)`
the diagram

```
R(f'f)_*K ⊗'' R(f'f)_*L --c⊗c--→ Rf'_*Rf_*K ⊗'' Rf'_*Rf_*L
        |                                   |
        ↓ cup for f'∘f                      ↓ cup for f'
R(f'f)_*(K ⊗ L) --c--→ Rf'_*Rf_*(K ⊗ L) ←--Rf'_*(cup for f)-- Rf'_*(Rf_*K ⊗' Rf_*L)
```

commutes in `D(𝒪'')`. The left-hand vertical arrow is the relative cup product for the composite
morphism `f' ∘ f` itself, and the two horizontal edges `c` are the components of the composition
isomorphism `derivedPushforwardCompIso`.

The proof transports `relativeCupProduct_comp`, the same square for the composite adjunction
`Rf_* ⋙ Rf'_*` with the composite of the two comparisons of [Stacks, Tag 07A4], along the
composition isomorphism, using the compatibility of the comparison of [Stacks, Tag 07A4] with
composition, `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp`. -/
@[stacks 0FPN "the square at the composite morphism itself, with no carried input: the left edge \
  is the relative cup product of Tag 0B6C for f' ∘ f and the two equality edges of the source are \
  the components of the composition isomorphism of derived pushforward, the conjugate of the \
  Tag 0D6D isomorphism"]
theorem relativeCupProduct_comp_pushforwardCompIso (K L : DerivedModules X.O) :
    relativeCupProduct (f'.comp f)
          (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf') K L ≫
        (derivedPushforwardCompIso f f' hmosf hmosf').inv.app
          ((uncurriedDerivedTensor X).obj (K, L)) =
      (uncurriedDerivedTensor Z).map
          ((derivedPushforwardCompIso f f' hmosf hmosf').inv.app K ×ₘ
            (derivedPushforwardCompIso f f' hmosf hmosf').inv.app L) ≫
        relativeCupProduct f' hmosf' ((derivedPushforward f).obj K)
              ((derivedPushforward f).obj L) ≫
          (derivedPushforward f').map (relativeCupProduct f hmosf K L) := by
  have key := adjunctionCupProduct_conjugate
    (DerivedPullbackOnRingedTopoi.derivedAdjunction (f'.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf'))
    ((DerivedPullbackOnRingedTopoi.derivedAdjunction f' hmosf').comp
      (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmosf))
    (uncurriedDerivedTensor Z) (uncurriedDerivedTensor X)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso (f'.comp f)
      (RingedToposSiteHom.isMorphismOfSites_comp_u f f' hmosf hmosf')).hom
    (compComparison (uncurriedDerivedTensor X) (uncurriedDerivedTensor Y)
      (uncurriedDerivedTensor Z)
      (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmosf).hom
      (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f' hmosf').hom)
    (derivedPullbackCompIso f f' hmosf hmosf').hom
    (fun P Q => by
      rw [compComparison_app, Category.assoc]
      exact Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso_hom_app_comp f f' hmosf hmosf'
        P Q)
    K L
  rw [conjugateEquiv_derivedPullbackCompIso_hom f f' hmosf hmosf',
    relativeCupProduct_comp f f' hmosf hmosf' K L] at key
  exact key

end TwoMorphisms

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
