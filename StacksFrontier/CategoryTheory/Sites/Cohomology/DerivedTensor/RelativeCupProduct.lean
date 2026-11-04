module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.OrdinaryAndDerivedCounit
import StacksCore.Tactic.StacksAttribute

/-!
# The relative cup product on a ringed topos

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `K`, `L` be objects
of `D(O_C)`.  There is a canonical map

`Rf_*K ⊗^L_{O_D} Rf_*L ⟶ Rf_*(K ⊗^L_{O_C} L)`,

the *relative cup product* of [Stacks, Tag 0B6C].  It is the map adjoint, for the adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6], to

`Lf^*(Rf_*K ⊗^L_{O_D} Rf_*L) ≅ Lf^*Rf_*K ⊗^L_{O_C} Lf^*Rf_*L ⟶ K ⊗^L_{O_C} L`,

whose first step is the compatibility of derived pullback with the derived tensor product
([Stacks, Tag 07A4]) and whose second is the counit `Lf^*Rf_* ⟶ id` in each of the two tensor
factors.

## Main definitions

All in the namespace `Stacks.Cohomology.RelativeCupProductOnRingedTopoi`.

* `adjunctionCupProduct` — the construction in the abstract setting of an adjunction `L ⊣ R`, a
  bifunctor on the base of `R`, a bifunctor on its target, and a comparison of the two along
  `L`.
* `relativeCupProductOfComparison` — the relative cup product for an arbitrary pair of derived
  tensor bifunctors on `D(O_D)` and `D(O_C)` and an arbitrary comparison `α` of derived pullback
  with them.
* `relativeCupProduct` — **the relative cup product of [Stacks, Tag 0B6C]**, at the canonical
  derived tensor products of [Stacks, Tag 06YU] and the canonical compatibility of
  [Stacks, Tag 07A4].  Its only hypothesis is that `f` is a morphism of ringed topoi.

## Main results

* `adjunctionCupProduct_natural`, `relativeCupProductOfComparison_naturality`,
  `relativeCupProduct_naturality` — the map is natural in the two objects jointly;
  `relativeCupProduct_naturality_left` and `relativeCupProduct_naturality_right` are the two
  separate naturality clauses.
* `adjunctionCupProduct_eq_unit_comp`, `relativeCupProductOfComparison_eq_unit_comp`,
  `relativeCupProduct_eq_unit_comp` — the map written through the unit of `Lf^* ⊣ Rf_*`, which
  is the form a consumer rewrites with.

## Implementation notes

*What is constructed and what is a parameter.*  Nothing beyond `f` being a morphism of ringed
topoi is assumed for `relativeCupProduct`: both inputs the source cites are available in this
repository and are used rather than carried.

* [Stacks, Tag 07A6], the adjunction `Lf^* ⊣ Rf_*` on the unbounded derived categories, is
  `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction`.
* [Stacks, Tag 07A4], the bifunctorial isomorphism `Lf^*(K ⊗^L L) ≅ Lf^*K ⊗^L Lf^*L`, is
  `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`, stated between exactly the two
  composites of uncurried bifunctors that the abstract construction consumes.  Only its forward
  map is used, so the general form takes a comparison and not an isomorphism; that the
  comparison happens to be invertible is not what makes the cup product exist.

*Why the general form is kept as well.*  The relative cup product is the same construction for
any pair of tensor bifunctors related along `Lf^*`, and a consumer holding a derived tensor
product other than the canonical one — or holding only a comparison — uses
`relativeCupProductOfComparison`.  The bifunctors are taken bare rather than packaged as
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` values, since none of the K-flat
comparisons of that structure enters the construction.

*The tensor order.*  The two bifunctors are uncurried with their arguments in the given order,
which is what makes the map come out as `Rf_*K ⊗^L Rf_*L ⟶ Rf_*(K ⊗^L L)`; no symmetry of
`⊗^L` is needed.

*What is not stated.*  That the cup product is associative, unital and graded commutative, and
that it is compatible with the shift or with distinguished triangles, are separate statements
and are not touched here.

## References

* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.DerivedTensor.RingedSite
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOnRingedTopoi

universe u

/-! ### The construction for an abstract adjunction -/

section Abstract

variable {C : Type*} {D : Type*} [Category C] [Category D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  (A : C × C ⥤ C) (B : D × D ⥤ D) (α : A ⋙ L ⟶ L.prod L ⋙ B)

/-- The canonical map `A(R G, R H) ⟶ R (B(G, H))`: the adjoint transpose of the comparison
followed by the counit in both factors. -/
def adjunctionCupProduct (G H : D) :
    A.obj (R.obj G, R.obj H) ⟶ R.obj (B.obj (G, H)) :=
  adj.homEquiv _ _
    (α.app (R.obj G, R.obj H) ≫ B.map (adj.counit.app G ×ₘ adj.counit.app H))

/-- The canonical map, written through the unit of the adjunction. -/
lemma adjunctionCupProduct_eq_unit_comp (G H : D) :
    adjunctionCupProduct adj A B α G H =
      adj.unit.app (A.obj (R.obj G, R.obj H)) ≫
        R.map (α.app (R.obj G, R.obj H) ≫
          B.map (adj.counit.app G ×ₘ adj.counit.app H)) :=
  adj.homEquiv_unit _ _ _

/-- The canonical map is natural in both arguments. -/
lemma adjunctionCupProduct_natural {G G' H H' : D} (g : G ⟶ G') (k : H ⟶ H') :
    A.map (R.map g ×ₘ R.map k) ≫ adjunctionCupProduct adj A B α G' H' =
      adjunctionCupProduct adj A B α G H ≫ R.map (B.map (g ×ₘ k)) := by
  apply (adj.homEquiv _ _).symm.injective
  unfold adjunctionCupProduct
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  simp only [Functor.comp_obj, Functor.prod_obj, Equiv.symm_apply_apply]
  have ha := α.naturality (R.map g ×ₘ R.map k)
  change L.map (A.map (R.map g ×ₘ R.map k)) ≫ α.app (R.obj G', R.obj H') =
    α.app (R.obj G, R.obj H) ≫ B.map (L.map (R.map g) ×ₘ L.map (R.map k)) at ha
  rw [← Category.assoc, ha, Category.assoc, ← Functor.map_comp,
    Category.assoc, ← Functor.map_comp]
  congr 2
  exact Prod.ext (adj.counit.naturality g) (adj.counit.naturality k)

end Abstract

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-! ### The cup product from an arbitrary pair of tensor bifunctors -/

section OfComparison

variable (TY : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  (TX : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (α : Functor.uncurry.obj TY ⋙ derivedPullback f ⟶
    (derivedPullback f).prod (derivedPullback f) ⋙ Functor.uncurry.obj TX)

/-- **The relative cup product** `Rf_*K ⊗ Rf_*L ⟶ Rf_*(K ⊗ L)` built from a tensor bifunctor
`TY` on `D(O_D)`, one `TX` on `D(O_C)`, and a comparison `α` of derived pullback with the two:
the map adjoint to `α` followed by the counit `Lf^*Rf_* ⟶ id` in each factor. -/
def relativeCupProductOfComparison
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (TY.obj ((derivedPushforward f).obj K)).obj ((derivedPushforward f).obj L) ⟶
      (derivedPushforward f).obj ((TX.obj K).obj L) :=
  adjunctionCupProduct (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (Functor.uncurry.obj TY) (Functor.uncurry.obj TX) α K L

/-- The relative cup product of an arbitrary comparison is natural in both objects. -/
theorem relativeCupProductOfComparison_naturality
    {K K' L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K ⟶ K') (l : L ⟶ L') :
    ((TY.map ((derivedPushforward f).map k)).app ((derivedPushforward f).obj L) ≫
          (TY.obj ((derivedPushforward f).obj K')).map ((derivedPushforward f).map l)) ≫
        relativeCupProductOfComparison f hmos TY TX α K' L' =
      relativeCupProductOfComparison f hmos TY TX α K L ≫
        (derivedPushforward f).map ((TX.map k).app L ≫ (TX.obj K').map l) :=
  adjunctionCupProduct_natural (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (Functor.uncurry.obj TY) (Functor.uncurry.obj TX) α k l

/-- **Naturality of the relative cup product in the first object.** -/
theorem relativeCupProductOfComparison_naturality_left
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K ⟶ K')
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (TY.map ((derivedPushforward f).map k)).app ((derivedPushforward f).obj L) ≫
        relativeCupProductOfComparison f hmos TY TX α K' L =
      relativeCupProductOfComparison f hmos TY TX α K L ≫
        (derivedPushforward f).map ((TX.map k).app L) := by
  simpa using relativeCupProductOfComparison_naturality f hmos TY TX α k (𝟙 L)

/-- **Naturality of the relative cup product in the second object.** -/
theorem relativeCupProductOfComparison_naturality_right
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (l : L ⟶ L') :
    (TY.obj ((derivedPushforward f).obj K)).map ((derivedPushforward f).map l) ≫
        relativeCupProductOfComparison f hmos TY TX α K L' =
      relativeCupProductOfComparison f hmos TY TX α K L ≫
        (derivedPushforward f).map ((TX.obj K).map l) := by
  simpa using relativeCupProductOfComparison_naturality f hmos TY TX α (𝟙 K) l

/-- The relative cup product of an arbitrary comparison, written through the unit of
`Lf^* ⊣ Rf_*`. -/
theorem relativeCupProductOfComparison_eq_unit_comp
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    relativeCupProductOfComparison f hmos TY TX α K L =
      (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).unit.app
          ((Functor.uncurry.obj TY).obj
            ((derivedPushforward f).obj K, (derivedPushforward f).obj L)) ≫
        (derivedPushforward f).map
          (α.app ((derivedPushforward f).obj K, (derivedPushforward f).obj L) ≫
            (Functor.uncurry.obj TX).map
              ((DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).counit.app K ×ₘ
                (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).counit.app L)) :=
  adjunctionCupProduct_eq_unit_comp (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos)
    (Functor.uncurry.obj TY) (Functor.uncurry.obj TX) α K L

end OfComparison

/-! ### The relative cup product of Tag 0B6C -/

variable [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **[Stacks, Tag 0B6C].**  For a morphism of ringed topoi
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and objects `K`, `L` of `D(O_C)`, the canonical relative cup
product

`Rf_*K ⊗^L_{O_D} Rf_*L ⟶ Rf_*(K ⊗^L_{O_C} L)`,

with no further hypothesis.  It is the map adjoint, for the adjunction `Lf^* ⊣ Rf_*` of
[Stacks, Tag 07A6], to the bifunctorial identification
`Lf^*(Rf_*K ⊗^L Rf_*L) ≅ Lf^*Rf_*K ⊗^L Lf^*Rf_*L` of [Stacks, Tag 07A4] followed by the counit
`Lf^*Rf_* ⟶ id` in each of the two factors. -/
@[stacks 0B6C "the relative cup product"]
def relativeCupProduct
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj K)).obj
        ((derivedPushforward f).obj L) ⟶
      (derivedPushforward f).obj (((derivedTensorProductFunctor X.O).obj K).obj L) :=
  relativeCupProductOfComparison f hmos (derivedTensorProductFunctor Y.O)
    (derivedTensorProductFunctor X.O)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom K L

/-- The relative cup product of [Stacks, Tag 0B6C] is natural in `K` and in `L` jointly. -/
theorem relativeCupProduct_naturality
    {K K' L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K ⟶ K') (l : L ⟶ L') :
    (((derivedTensorProductFunctor Y.O).map ((derivedPushforward f).map k)).app
            ((derivedPushforward f).obj L) ≫
          ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj K')).map
            ((derivedPushforward f).map l)) ≫
        relativeCupProduct f hmos K' L' =
      relativeCupProduct f hmos K L ≫
        (derivedPushforward f).map
          (((derivedTensorProductFunctor X.O).map k).app L ≫
            ((derivedTensorProductFunctor X.O).obj K').map l) :=
  relativeCupProductOfComparison_naturality f hmos (derivedTensorProductFunctor Y.O)
    (derivedTensorProductFunctor X.O)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom k l

/-- **Naturality of the relative cup product of [Stacks, Tag 0B6C] in the first object.** -/
@[stacks 0B6C "naturality in the first object"]
theorem relativeCupProduct_naturality_left
    {K K' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (k : K ⟶ K')
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedTensorProductFunctor Y.O).map ((derivedPushforward f).map k)).app
          ((derivedPushforward f).obj L) ≫
        relativeCupProduct f hmos K' L =
      relativeCupProduct f hmos K L ≫
        (derivedPushforward f).map (((derivedTensorProductFunctor X.O).map k).app L) :=
  relativeCupProductOfComparison_naturality_left f hmos (derivedTensorProductFunctor Y.O)
    (derivedTensorProductFunctor X.O)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom k L

/-- **Naturality of the relative cup product of [Stacks, Tag 0B6C] in the second object.** -/
@[stacks 0B6C "naturality in the second object"]
theorem relativeCupProduct_naturality_right
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (l : L ⟶ L') :
    ((derivedTensorProductFunctor Y.O).obj ((derivedPushforward f).obj K)).map
          ((derivedPushforward f).map l) ≫
        relativeCupProduct f hmos K L' =
      relativeCupProduct f hmos K L ≫
        (derivedPushforward f).map (((derivedTensorProductFunctor X.O).obj K).map l) :=
  relativeCupProductOfComparison_naturality_right f hmos (derivedTensorProductFunctor Y.O)
    (derivedTensorProductFunctor X.O)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom K l

/-- The relative cup product of [Stacks, Tag 0B6C] written through the unit of `Lf^* ⊣ Rf_*`:
the unit at `Rf_*K ⊗^L Rf_*L`, then `Rf_*` of the comparison of [Stacks, Tag 07A4] and of the
counit in each factor. -/
theorem relativeCupProduct_eq_unit_comp
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    relativeCupProduct f hmos K L =
      (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).unit.app
          ((Functor.uncurry.obj (derivedTensorProductFunctor Y.O)).obj
            ((derivedPushforward f).obj K, (derivedPushforward f).obj L)) ≫
        (derivedPushforward f).map
          ((Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom.app
              ((derivedPushforward f).obj K, (derivedPushforward f).obj L) ≫
            (Functor.uncurry.obj (derivedTensorProductFunctor X.O)).map
              ((DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).counit.app K ×ₘ
                (DerivedPullbackOnRingedTopoi.derivedAdjunction f hmos).counit.app L)) :=
  relativeCupProductOfComparison_eq_unit_comp f hmos (derivedTensorProductFunctor Y.O)
    (derivedTensorProductFunctor X.O)
    (Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso f hmos).hom K L

end Stacks.Cohomology.RelativeCupProductOnRingedTopoi

end
