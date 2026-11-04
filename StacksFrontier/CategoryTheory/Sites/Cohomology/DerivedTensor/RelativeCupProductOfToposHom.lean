module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfToposHomUnconditional
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductCoherence
import StacksCore.Tactic.StacksAttribute

/-!
# The relative cup product, for a morphism of ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi in the sense of
[Stacks, Tag 01D3], part (2): a morphism of the underlying *topoi* together with the structure
map, `AlgebraicGeometry.RingedToposHom`, with no functor between the underlying sites and no
morphism-of-sites condition.  For `K`, `L` in `D(𝒪_C)` the *relative cup product* of
[Stacks, Tag 0B6C] is the map

`Rf_*K ⊗^L_{𝒪_D} Rf_*L ⟶ Rf_*(K ⊗^L_{𝒪_C} L)`

adjoint, for the adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6], to

`Lf^*(Rf_*K ⊗^L Rf_*L) ≅ Lf^*Rf_*K ⊗^L Lf^*Rf_*L ⟶ K ⊗^L L`,

the identification of [Stacks, Tag 07A4] followed by the counit in each tensor factor.

## Main definitions

* `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct`: the relative cup product
  `Rf_*K ⊗^L Rf_*L ⟶ Rf_*(K ⊗^L L)` of a morphism of ringed topoi.

## Main results

* `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_naturality`,
  `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_naturality_left` and
  `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_naturality_right`:
  naturality in the two objects.
* `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_eq_unit_comp`: the cup
  product written through the unit.
* `Stacks.Cohomology.RelativeCupProductOfToposHom.conjugateEquiv_derivedPullbackCompIso_inv` and
  `Stacks.Cohomology.RelativeCupProductOfToposHom.conjugateEquiv_derivedPullbackCompIso_hom`: the
  composition isomorphism `Rf_* ⋙ Rg_* ≅ R(g ∘ f)_*`
  (`Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardCompIsoOfAdjoints`)
  is the conjugate of the isomorphism `Lg^* ⋙ Lf^* ≅ L(g ∘ f)^*` of [Stacks, Tag 0D6D], in both
  directions.
* `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_comp_adjunction`: the cup
  product of the composite adjunction `Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*` with the composite comparison is
  the cup product for `g` followed by `Rg_*` of the cup product for `f`.

## References

* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom
open Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

/-! ### The relative cup product of Tag 0B6C -/

section OneMorphism

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposHom X Y)

/-- For a morphism of ringed topoi
`f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` — a morphism of the underlying topoi together with the
structure map, with no functor between the underlying sites — and objects `K`, `L` of `D(𝒪_C)`,
the relative cup product

`Rf_*K ⊗^L_{𝒪_D} Rf_*L ⟶ Rf_*(K ⊗^L_{𝒪_C} L)`.

It is the map adjoint, for the adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6], to the
identification `Lf^*(Rf_*K ⊗^L Rf_*L) ≅ Lf^*Rf_*K ⊗^L Lf^*Rf_*L` of [Stacks, Tag 07A4] followed
by the counit `Lf^*Rf_* ⟶ id` in each of the two factors. -/
@[stacks 0B6C "the relative cup product, for a morphism of ringed topoi in the two-field sense \
  of Tag 01D3, part (2) -- a morphism of the underlying topoi together with the structure map, \
  with no continuous functor between the underlying sites and no morphism-of-sites hypothesis"]
def relativeCupProduct
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj K)).obj
        ((derivedPushforward f).obj L) ⟶
      (derivedPushforward f).obj (((derivedTensorProductFunctor X.O).obj K).obj L) :=
  adjunctionCupProduct (derivedAdjunction f) (uncurriedDerivedTensor Y)
    (uncurriedDerivedTensor X)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom K L

/-- The relative cup product is, by definition, the abstract cup product of the derived
adjunction of [Stacks, Tag 07A6] and the comparison of [Stacks, Tag 07A4]. -/
theorem relativeCupProduct_eq_adjunctionCupProduct
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    relativeCupProduct f K L =
      adjunctionCupProduct (derivedAdjunction f) (uncurriedDerivedTensor Y)
        (uncurriedDerivedTensor X)
        (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom K L :=
  rfl

/-- The relative cup product of [Stacks, Tag 0B6C] is natural in `K` and in `L` jointly. -/
theorem relativeCupProduct_naturality
    {K K' L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K ⟶ K') (l : L ⟶ L') :
    (((derivedTensorProductFunctor Y.O).map ((derivedPushforward f).map k)).app
            ((derivedPushforward f).obj L) ≫
          ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj K')).map
            ((derivedPushforward f).map l)) ≫
        relativeCupProduct f K' L' =
      relativeCupProduct f K L ≫
        (derivedPushforward f).map
          (((derivedTensorProductFunctor X.O).map k).app L ≫
            ((derivedTensorProductFunctor X.O).obj K').map l) :=
  adjunctionCupProduct_natural (derivedAdjunction f) (uncurriedDerivedTensor Y)
    (uncurriedDerivedTensor X)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom k l

/-- **Naturality of the relative cup product of [Stacks, Tag 0B6C] in the first object**, for a
morphism of ringed topoi. -/
theorem relativeCupProduct_naturality_left
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K ⟶ K')
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedTensorProductFunctor Y.O).map ((derivedPushforward f).map k)).app
          ((derivedPushforward f).obj L) ≫
        relativeCupProduct f K' L =
      relativeCupProduct f K L ≫
        (derivedPushforward f).map (((derivedTensorProductFunctor X.O).map k).app L) := by
  simpa using relativeCupProduct_naturality f k (𝟙 L)

/-- **Naturality of the relative cup product of [Stacks, Tag 0B6C] in the second object**, for a
morphism of ringed topoi. -/
theorem relativeCupProduct_naturality_right
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (l : L ⟶ L') :
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj K)).map
          ((derivedPushforward f).map l) ≫
        relativeCupProduct f K L' =
      relativeCupProduct f K L ≫
        (derivedPushforward f).map (((derivedTensorProductFunctor X.O).obj K).map l) := by
  simpa using relativeCupProduct_naturality f (𝟙 K) l

/-- The relative cup product of [Stacks, Tag 0B6C] written through the unit of `Lf^* ⊣ Rf_*`:
the unit at `Rf_*K ⊗^L Rf_*L`, then `Rf_*` of the comparison of [Stacks, Tag 07A4] and of the
counit in each factor. -/
theorem relativeCupProduct_eq_unit_comp
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    relativeCupProduct f K L =
      (derivedAdjunction f).unit.app
          ((uncurriedDerivedTensor Y).obj
            ((derivedPushforward f).obj K, (derivedPushforward f).obj L)) ≫
        (derivedPushforward f).map
          ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom.app
              ((derivedPushforward f).obj K, (derivedPushforward f).obj L) ≫
            (uncurriedDerivedTensor X).map
              ((derivedAdjunction f).counit.app K ×ₘ (derivedAdjunction f).counit.app L)) :=
  adjunctionCupProduct_eq_unit_comp (derivedAdjunction f) (uncurriedDerivedTensor Y)
    (uncurriedDerivedTensor X)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom K L

end OneMorphism

/-! ### The composition isomorphism for derived pushforward, as a conjugate -/

section Composition

variable {X Y Z : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [Z.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)] [HasSheafify Z.J (Type u)]
  (f : RingedToposHom X Y) (g : RingedToposHom Y Z)

/-- **The composition isomorphism for derived pushforward is the conjugate of the one for
derived pullback.**  The conjugate, for the composite of the two derived adjunctions and the
derived adjunction of the composite, of the inverse of the isomorphism of
[Stacks, Tag 0D6D] is `derivedPushforwardCompIsoOfAdjoints`. -/
theorem conjugateEquiv_derivedPullbackCompIso_inv :
    conjugateEquiv ((derivedAdjunction g).comp (derivedAdjunction f))
        (derivedAdjunction (RingedToposHom.comp (X := X) g f)) (derivedPullbackCompIso f g).inv =
      (derivedPushforwardCompIsoOfAdjoints f g).hom :=
  Stacks.Cohomology.DerivedBaseChangePasting.conjugateEquiv_iso_inv _ _ _

/-- The conjugate of the isomorphism of [Stacks, Tag 0D6D] itself, in the direction that replaces
the derived adjunction of `g ∘ f` by the composite of the two derived adjunctions, is the inverse
of `derivedPushforwardCompIsoOfAdjoints`. -/
theorem conjugateEquiv_derivedPullbackCompIso_hom :
    conjugateEquiv (derivedAdjunction (RingedToposHom.comp (X := X) g f))
        ((derivedAdjunction g).comp (derivedAdjunction f)) (derivedPullbackCompIso f g).hom =
      (derivedPushforwardCompIsoOfAdjoints f g).inv := by
  have h := conjugateEquiv_comm (derivedAdjunction (RingedToposHom.comp (X := X) g f))
    ((derivedAdjunction g).comp (derivedAdjunction f))
    (α := (derivedPullbackCompIso f g).hom) (β := (derivedPullbackCompIso f g).inv)
    (Iso.inv_hom_id _)
  rw [conjugateEquiv_derivedPullbackCompIso_inv] at h
  exact (Iso.comp_hom_eq_id _).1 h

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O) (ComplexShape.up ℤ)]

/-- **The relative cup product along the composite adjunction.**  For the composite adjunction
`Lg^* ⋙ Lf^* ⊣ Rf_* ⋙ Rg_*` of the two adjunctions of [Stacks, Tag 07A6], whose counit is the
composite of the two counits ([Stacks, Tag 0DV0]), and the composite of the two comparisons of
[Stacks, Tag 07A4], the cup product is the cup product for `g` at `(Rf_*K, Rf_*L)` followed by
`Rg_*` of the cup product for `f`. -/
theorem relativeCupProduct_comp_adjunction
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    adjunctionCupProduct ((derivedAdjunction g).comp (derivedAdjunction f))
        (uncurriedDerivedTensor Z) (uncurriedDerivedTensor X)
        (compComparison (uncurriedDerivedTensor X) (uncurriedDerivedTensor Y)
          (uncurriedDerivedTensor Z)
          (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom
          (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom) K L =
      relativeCupProduct g ((derivedPushforward f).obj K) ((derivedPushforward f).obj L) ≫
        (derivedPushforward g).map (relativeCupProduct f K L) :=
  adjunctionCupProduct_comp (derivedAdjunction f) (derivedAdjunction g)
    (uncurriedDerivedTensor X) (uncurriedDerivedTensor Y) (uncurriedDerivedTensor Z)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom K L

end Composition

end Stacks.Cohomology.RelativeCupProductOfToposHom

end
