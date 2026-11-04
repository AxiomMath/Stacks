module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormulaBaseChangeOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductOfToposHom

/-!
# The relative cup product and base change, for a 2-commutative square of ringed topoi

Let
```
              g'
  (Sh(𝒞'), 𝒪_{𝒞'}) ⟶ (Sh(𝒞), 𝒪_𝒞)
        | f'                | f
        v                   v
  (Sh(𝒟'), 𝒪_{𝒟'}) ⟶ (Sh(𝒟), 𝒪_𝒟)
              g
```
be a square of morphisms of ringed topoi commuting up to a 2-isomorphism `s : g ∘ f' ≅ f ∘ g'`,
and let `b : Lg^* Rf_* ⟶ Rf'_* L(g')^*` be its base change map
(`Stacks.Cohomology.ProjectionFormulaOfToposHom.squareBaseChangeMap`). For arbitrary `K`, `L` in
`D(𝒪_𝒞)` the relative cup product of [Stacks, Tag 0B6C] is compatible with `b`: this is
[Stacks, Tag 0H9A] for a square that commutes only up to a 2-isomorphism. A commutative square of
schemes gives such a square of étale ringed topoi
(`Stacks.EtaleCohomology.etaleRingedToposHomSquareTwoIso`), not a strictly commutative one, so
this is the form in which Tag 0H9A applies to the geometric fibres of a morphism of schemes.

The proof applies
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_baseChange_square` at the
derived adjunctions of [Stacks, Tag 07A6], whose one input, the compatibility of the four
comparisons of [Stacks, Tag 07A4] around the square, is
`AlgebraicGeometry.RingedToposHom.TwoIso.tensorComparisonCompatible`.

## Main results

* `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_baseChange_square_of_twoIso`.
* `Stacks.Cohomology.RelativeCupProductOfToposHom.derivedPullback_map_relativeCupProduct_of_isIso`:
  when the base change map is invertible, `Lg^*` of the relative cup product along `f` is the
  relative cup product along `f'`, read through the base change maps.
* `Stacks.Cohomology.RelativeCupProductOfToposHom.squareBaseChangeTrace`: a trace `Rf_* E ⟶ M[n]`
  carried to `Rf'_* L(g')^* E ⟶ (Lg^* M)[n]` through the inverse of the base change map, with
  its characterization `squareBaseChangeMap_comp_squareBaseChangeTrace`.

## References

* [Stacks Project, Tag 0H9A](https://stacks.math.columbia.edu/tag/0H9A)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.ProjectionFormulaOfToposHom
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOfToposHom

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X' X Y' Y : RingedTopos.{u, u, u}}
  [X'.J.HasSheafCompose (forget RingCat.{u})] [X.J.HasSheafCompose (forget RingCat.{u})]
  [Y'.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{u})] [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X'.J AddCommGrpCat.{u}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y'.J AddCommGrpCat.{u}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X'.J (Type u)] [HasSheafify X.J (Type u)]
  [HasSheafify Y'.J (Type u)] [HasSheafify Y.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X'.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y'.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y'.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  {f : RingedToposHom X Y} {g : RingedToposHom Y' Y} {f' : RingedToposHom X' Y'}
  {g' : RingedToposHom X' X} (s : RingedToposHom.TwoIso (g.comp f') (f.comp g'))

/-- **[Stacks, Tag 0H9A] for a 2-commutative square of ringed topoi.** For a square
`s : g ∘ f' ≅ f ∘ g'` of morphisms of ringed topoi and arbitrary `K`, `L` in `D(𝒪_𝒞)`, the
comparison of [Stacks, Tag 07A4] along `g`, followed by the base change map of the square in
both tensor factors and by the relative cup product of [Stacks, Tag 0B6C] along `f'`, is `Lg^*`
of the relative cup product along `f`, followed by the base change map at `K ⊗^𝐋 L` and by
`Rf'_*` of the comparison of [Stacks, Tag 07A4] along `g'`, as maps
`Lg^*(Rf_*K ⊗^𝐋 Rf_*L) ⟶ Rf'_*(L(g')^*K ⊗^𝐋 L(g')^*L)`. -/
theorem relativeCupProduct_baseChange_square_of_twoIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom.app
          ((derivedPushforward f).obj K, (derivedPushforward f).obj L) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O)).map
            (squareBaseChangeMap s K ×ₘ squareBaseChangeMap s L) ≫
          relativeCupProduct f' ((derivedPullback g').obj K) ((derivedPullback g').obj L) =
      (derivedPullback g).map (relativeCupProduct f K L) ≫
        squareBaseChangeMap s (((derivedTensorProductFunctor X.O).obj K).obj L) ≫
          (derivedPushforward f').map
            ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g').hom.app
              (K, L)) :=
  Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_baseChange_square
    (derivedAdjunction f) (derivedAdjunction f')
    (RingedToposHom.TwoIso.derivedPullbackSquareIso s) (Iso.refl _)
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X.O))
    (Functor.uncurry.obj (derivedTensorProductFunctor X'.O))
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f').hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g').hom K L
    (RingedToposHom.TwoIso.tensorComparisonCompatible s _ _)

/-- **The relative cup product is carried to the one of the base change, when the base change
map is invertible.** If the base change map of the 2-commutative square `s` is invertible at
`K`, at `L` and at `K ⊗^𝐋 L` (proper base change, for instance), then `Lg^*` of the relative cup
product of [Stacks, Tag 0B6C] along `f` is the relative cup product along `f'` read through the
base change maps and the comparisons of [Stacks, Tag 07A4] along `g` and `g'`. -/
theorem derivedPullback_map_relativeCupProduct_of_isIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hb : IsIso (squareBaseChangeMap s (((derivedTensorProductFunctor X.O).obj K).obj L))) :
    (derivedPullback g).map (relativeCupProduct f K L) =
      (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g).hom.app
          ((derivedPushforward f).obj K, (derivedPushforward f).obj L) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor Y'.O)).map
            (squareBaseChangeMap s K ×ₘ squareBaseChangeMap s L) ≫
          relativeCupProduct f' ((derivedPullback g').obj K) ((derivedPullback g').obj L) ≫
            (derivedPushforward f').map
              ((Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso g').inv.app
                (K, L)) ≫
              inv (squareBaseChangeMap s (((derivedTensorProductFunctor X.O).obj K).obj L)) := by
  rw [reassoc_of% (relativeCupProduct_baseChange_square_of_twoIso s K L),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  simp

/-- **A trace carried to the base change.** For a 2-commutative square `s` whose base change map
is invertible at `E`, a morphism `t : Rf_* E ⟶ M[n]` of `D(𝒪_𝒟)` gives
`Rf'_* L(g')^* E ⟶ (Lg^* M)[n]`: the inverse of the base change map, `Lg^* t`, and the
commutation of `Lg^*` with the shift. For the geometric fibre `X̄_s̄` of a proper curve
`f̄ : X̄ ⟶ S` this is the fibre trace `R(f̄_s̄)_* Λ ⟶ Λ[-2]` of a trace `Rf̄_* Λ ⟶ Λ[-2]`. -/
def squareBaseChangeTrace
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (n : ℤ) (hb : IsIso (squareBaseChangeMap s E)) (t : (derivedPushforward f).obj E ⟶ M⟦n⟧) :
    (derivedPushforward f').obj ((derivedPullback g').obj E) ⟶ ((derivedPullback g).obj M)⟦n⟧ :=
  inv (squareBaseChangeMap s E) ≫ (derivedPullback g).map t ≫
    ((derivedPullback g).commShiftIso n).hom.app M

/-- The base change map followed by the trace carried to the base change is `Lg^*` of the
trace, read through the commutation of `Lg^*` with the shift. -/
theorem squareBaseChangeMap_comp_squareBaseChangeTrace
    (E : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (n : ℤ) (hb : IsIso (squareBaseChangeMap s E)) (t : (derivedPushforward f).obj E ⟶ M⟦n⟧) :
    squareBaseChangeMap s E ≫ squareBaseChangeTrace s E M n hb t =
      (derivedPullback g).map t ≫ ((derivedPullback g).commShiftIso n).hom.app M := by
  simp [squareBaseChangeTrace]

end Stacks.Cohomology.RelativeCupProductOfToposHom

end
