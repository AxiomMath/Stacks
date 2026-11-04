module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorIsoCompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductCompositionTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# The relative cup product is compatible with composition, for morphisms of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` and `f' : (Sh(C'), 𝒪') ⟶ (Sh(C''), 𝒪'')` be morphisms of
ringed topoi in the sense of [Stacks, Tag 01D3], part (2) — morphisms of the underlying topoi
together with the structure maps, `AlgebraicGeometry.RingedToposHom`, with no functor between the
underlying sites and no morphism-of-sites condition.  [Stacks, Tag 0FPN] asserts that for `K`,
`L` in `D(𝒪)` the square

```
R(f'f)_*K ⊗'' R(f'f)_*L  ====  Rf'_*Rf_*K ⊗'' Rf'_*Rf_*L
        |                                  |
        ↓                                  ↓
R(f'f)_*(K ⊗ L)  ====  Rf'_*Rf_*(K ⊗ L)  ←--  Rf'_*(Rf_*K ⊗' Rf_*L)
```

commutes in `D(𝒪'')`, the vertical arrows and the lower right arrow being relative cup products of
[Stacks, Tag 0B6C].  This file proves it, as `relativeCupProduct_comp_pushforwardCompIso`.

## Main results

* `relativeCupProduct_comp_pushforwardCompIso` — **[Stacks, Tag 0FPN]** for morphisms of ringed
  topoi: the left edge is the relative cup product
  `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct` of the composite `f' ∘ f`,
  and the two edges the source draws as equalities `R(f' ∘ f)_* = Rf'_*Rf_*` are the components of
  the composition isomorphism
  `Stacks.Cohomology.DerivedPushforwardCompositionOfToposHom.derivedPushforwardCompIsoOfAdjoints`,
  the conjugate of the isomorphism of [Stacks, Tag 0D6D].

## Implementation notes

The proof is the source's.  Going around the square either way gives the map adjoint to

`L(f'f)^*(R(f'f)_*K ⊗ R(f'f)_*L) = L(f'f)^*R(f'f)_*K ⊗ L(f'f)^*R(f'f)_*L ⟶ K ⊗ L`,

because the composite of the two counits is the counit for `L(f' ∘ f)^* ⊣ R(f' ∘ f)_*`
([Stacks, Tag 0DV0]).  In Lean the two sides are cup products for two different adjunctions with
left adjoint `L(f' ∘ f)^*` up to the isomorphism of [Stacks, Tag 0D6D]; the abstract statement
comparing them is
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_conjugate`, and its
one hypothesis — that the isomorphism of [Stacks, Tag 0D6D] is monoidal for the comparisons of
[Stacks, Tag 07A4], which is what the source's first `=` uses — is
`Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_hom_app_comp`.

## References

* [Stacks Project, Tag 0FPN](https://stacks.math.columbia.edu/tag/0FPN)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0DV0](https://stacks.math.columbia.edu/tag/0DV0)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
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
  (f : RingedToposHom X Y) (f' : RingedToposHom Y Z)

/-- **[Stacks, Tag 0FPN].**  Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` and
`f' : (Sh(C'), 𝒪') ⟶ (Sh(C''), 𝒪'')` be morphisms of ringed topoi.  The relative cup product of
[Stacks, Tag 0B6C] is compatible with composition: for all `K`, `L` in `D(𝒪)` the diagram

```
R(f'f)_*K ⊗'' R(f'f)_*L --c⊗c--→ Rf'_*Rf_*K ⊗'' Rf'_*Rf_*L
        |                                   |
        ↓ cup for f'∘f                      ↓ cup for f'
R(f'f)_*(K ⊗ L) --c--→ Rf'_*Rf_*(K ⊗ L) ←--Rf'_*(cup for f)-- Rf'_*(Rf_*K ⊗' Rf_*L)
```

commutes in `D(𝒪'')`.  The left edge is the relative cup product of the composite `f' ∘ f`; the
two edges `c` the source draws as equalities `R(f' ∘ f)_* = Rf'_*Rf_*` are the components of the
composition isomorphism `derivedPushforwardCompIsoOfAdjoints`, the conjugate of the isomorphism of
[Stacks, Tag 0D6D] (`conjugateEquiv_derivedPullbackCompIso_hom`).

There is no hypothesis beyond the two morphisms of ringed topoi and the ambient instances making
the derived categories and derived tensor products exist. -/
@[stacks 0FPN "for morphisms of ringed topoi in the two-field sense of Tag 01D3, part (2) -- \
  morphisms of the underlying topoi together with the structure maps, with no continuous functor \
  between the underlying sites and no morphism-of-sites hypothesis; the left edge is the relative \
  cup product of Tag 0B6C for f' ∘ f and the two equality edges of the source are the components \
  of the composition isomorphism of derived pushforward, the conjugate of the Tag 0D6D \
  isomorphism"]
theorem relativeCupProduct_comp_pushforwardCompIso (K L : DerivedModules X.O) :
    relativeCupProduct (RingedToposHom.comp (X := X) f' f) K L ≫
        (derivedPushforwardCompIsoOfAdjoints f f').inv.app
          ((uncurriedDerivedTensor X).obj (K, L)) =
      (uncurriedDerivedTensor Z).map
          ((derivedPushforwardCompIsoOfAdjoints f f').inv.app K ×ₘ
            (derivedPushforwardCompIsoOfAdjoints f f').inv.app L) ≫
        relativeCupProduct f' ((derivedPushforward f).obj K) ((derivedPushforward f).obj L) ≫
          (derivedPushforward f').map (relativeCupProduct f K L) := by
  have key := adjunctionCupProduct_conjugate
    (derivedAdjunction (RingedToposHom.comp (X := X) f' f))
    ((derivedAdjunction f').comp (derivedAdjunction f))
    (uncurriedDerivedTensor Z) (uncurriedDerivedTensor X)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso
      (RingedToposHom.comp (X := X) f' f)).hom
    (compComparison (uncurriedDerivedTensor X) (uncurriedDerivedTensor Y)
      (uncurriedDerivedTensor Z)
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f').hom)
    (derivedPullbackCompIso f f').hom
    (fun P Q => by
      rw [compComparison_app, Category.assoc]
      exact Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_hom_app_comp
        f f' P Q)
    K L
  rw [conjugateEquiv_derivedPullbackCompIso_hom f f'] at key
  rw [relativeCupProduct_comp_adjunction f f' K L] at key
  exact key

end Stacks.Cohomology.RelativeCupProductOfToposHom

end
