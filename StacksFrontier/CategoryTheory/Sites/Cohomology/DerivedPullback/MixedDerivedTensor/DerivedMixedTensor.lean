module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.DerivedPullbackFactorization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.MixedTensorTotalComplex

/-!
# Stacks 08I6

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi.  **Stacks 08I6** asserts a
canonical bifunctorial isomorphism

`F ⊗^L_O Lf^*G ≅ F ⊗^L_{f⁻¹O'} f⁻¹G`

for `F` in `D(O)` and `G` in `D(O')`.  Both sides are objects of `D(f⁻¹O')`: on the left the
tensor product is formed over `O` and then read over `f⁻¹O'` by restriction of scalars, which is
the functor `D(O) ⥤ D(f⁻¹O')` of
`Stacks.Cohomology.MixedDerivedTensor.derivedRestrictToInvRing`.

The source proves it from the underived identity
`F ⊗_O f^*G = F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G`, which holds because `f^*G` is the extension of scalars
of `f⁻¹G` along `f⁻¹O' ⟶ O` and a base change then cancels.  Reading the chain at a complex `F`
of `O`-modules and a K-flat complex `G` of `O'`-modules with flat terms, left to right:

1. `Lf^*G` is `Q f^*G`, because `G` is K-flat with flat terms, by **Stacks 06YY**;
2. `F ⊗^L_O f^*G` is `Q Tot(F ⊗_O f^*G)`, by the one-sided K-flat comparison of **Stacks 06YU**:
   `f^*G` is K-flat with flat terms by **Stacks 0G7E**, and no hypothesis on `F` is needed;
3. restriction of scalars is exact, so the restriction of that is `Q (Tot(F ⊗_O f^*G)|_{f⁻¹O'})`;
4. `Tot(F ⊗_O f^*G)|_{f⁻¹O'}` is `Tot(F|_{f⁻¹O'} ⊗_{f⁻¹O'} f⁻¹G)`, by the underived identity in
   each bidegree;
5. and that total complex computes `F|_{f⁻¹O'} ⊗^L_{f⁻¹O'} f⁻¹G`, again by the one-sided K-flat
   comparison of Stacks 06YU, because `f⁻¹G` is K-flat over `f⁻¹O'` with flat terms.

The passage from these representatives to arbitrary objects is the descent along a localization:
every complex of `O`-modules is already its own model, the K-flat complexes of `O'`-modules with
flat terms localize to `D(O')` by **Stacks 06YS**, so the pairs localize to `D(O) × D(O')`, and
the value of the chain at a pair of models, being natural in both, extends uniquely.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.mixedDerivedTensorPullback` and
  `mixedDerivedTensorInverseImage`: the two uncurried bifunctors `D(O) × D(O') ⥤ D(f⁻¹O')` the
  tag compares.
* `Stacks.Cohomology.MixedDerivedTensor.derivedMixedTensorModelIso`: the chain above, at a
  complex of `O`-modules and a K-flat complex of `O'`-modules with flat terms.
* `Stacks.Cohomology.MixedDerivedTensor.derivedMixedTensorIso`: Stacks 08I6 read in
  `D(f⁻¹O')`, after restriction of scalars.  The tag, in `D(O)` and for an arbitrary morphism
  of ringed topoi, is registered on
  `Stacks.Cohomology.MixedDerivedTensor.OfToposHom.derivedMixedTensorIso`.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.mixedModelsQ_isLocalization`: pairs consisting of a
  complex of `O`-modules and a K-flat complex of `O'`-modules with flat terms localize to
  `D(O) × D(O')`.
* `Stacks.Cohomology.MixedDerivedTensor.derivedMixedTensorModelIso_naturality`: the value at a
  pair of models is natural in both complexes, which is what makes the descent possible.

## Implementation notes

*Only the complex of `O'`-modules is replaced by a model.*  The derived tensor product has a
*one-sided* K-flat comparison — the `comparisonRight` field of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`, which computes `K ⊗^L L` by the
total tensor complex as soon as `L` is K-flat, with `K` arbitrary — and on both sides of the
tag the complex coming from `O'` is the one that is K-flat.  So the descent is along
`DerivedCategory.Q` in the first variable and along the K-flat models only in the second, and
the statement carries no flatness hypothesis anywhere.

*The morphism-of-sites hypothesis.*  `AlgebraicGeometry.RingedToposSiteHom` asks only that the
underlying functor `f.u` be *continuous*; left exactness of `f^{-1}` is not a field of it, and
the inverse image along a merely continuous functor need not be exact, so such an `f` need not
present a morphism of topoi at all.  A morphism of ringed topoi in the source's sense has that
exactness, and `f.u.IsMorphismOfSites Y.J X.J` is exactly what supplies it.  So `hmos` is not a
weakening of Stacks 08I6: it is what makes the Lean object a morphism of ringed topoi, which is
what the tag assumes, and it is the hypothesis carried by every statement of this chain —
Stacks 05VD, 0G6R, 0G7E and 06YY.

*The left-derived-functor instances.*  Neither `Lf^*` nor `Lf^{-1}` can be written down without
`CategoryTheory.Functor.HasLeftDerivedFunctor`, so the two are instance arguments.  They are not
residual hypotheses: both are `Prop` classes, both are discharged for every morphism of ringed
topoi by
`Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy` — for
the geometric half of the factorization because it has the same underlying continuous functor as
`f` — and by proof irrelevance the derived pullback is the same functor whichever witness is
supplied.  Restriction of scalars needs no such argument: it is exact, so the localization lifts
it directly.

*Two spellings of one sheaf of rings.*  The derived pullback is stated over
`AlgebraicGeometry.RingedTopos.ringSheaf` and the derived tensor product over
`Stacks.SheafOfModules.Tensor.ringSheaf`; the two differ only in where the instance witnessing
that a forgetful composite is a sheaf comes from.  `derivedRestrictTensor` and
`derivedRestrictTensorQIso` restate the derived restriction of scalars and its computation once
at the second spelling, which is the one every tensor product below is indexed by.

*The universe narrowing, inherited.*  Both ringed topoi are taken at `RingedTopos.{u, u, u}`.
This is not chosen here: the derived tensor product of Stacks 06YU is available only at those
universes, a narrowing
`Stacks.DerivedTensor.RingedSite.exists_derivedTensorProduct` records as coming down from the
existence of K-flat resolutions, and the same pin is carried by Stacks 0G7E and 06YY in this
tree.  The derived categories' own hom universe stays independent.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [The Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [The Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [The Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Cohomology.MixedDerivedTensor

open StacksPullbackFactorization

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)) (ComplexShape.up ℤ)]

/-- The functor `D(O) ⥤ D(f⁻¹O')` induced by restriction of scalars, with the sheaves of rings
written as the tensor product of Tag 06YM writes them. -/
def derivedRestrictTensor :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) :=
  derivedRestrictToInvRing f

/-- The derived functor of restriction of scalars is computed by degreewise restriction of
scalars, at the same spelling. -/
def derivedRestrictTensorQIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    (derivedRestrictTensor f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((restrictComplexTensor f).obj K) :=
  derivedRestrictToInvRing_obj_Q f K

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj M).Additive] in
/-- The computation of the derived functor of restriction of scalars is natural. -/
lemma derivedRestrictTensorQIso_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (φ : K ⟶ L) :
    (derivedRestrictTensor f).map (DerivedCategory.Q.map φ) ≫
        (derivedRestrictTensorQIso f L).hom =
      (derivedRestrictTensorQIso f K).hom ≫
        DerivedCategory.Q.map ((restrictComplexTensor f).map φ) :=
  derivedRestrictToInvRing_obj_Q_naturality f φ

section Models

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  [(pullbackOnHomotopy (auxHomG f)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))]
  (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
  (hG : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) G)
  (hflatG : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (G.X i))

/-- The left-hand side of Stacks 08I6 at a K-flat complex of `O'`-modules with flat terms is
the class of the restriction of scalars of the total tensor complex. -/
def derivedMixedTensorModelLeft :
    (derivedRestrictTensor f).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj
            (DerivedCategory.Q.obj F)).obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj G))) ≅
      DerivedCategory.Q.obj ((restrictComplexTensor f).obj
        (HomologicalComplex.mapBifunctor F ((pullbackComplex f).obj G)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ))) :=
  (derivedRestrictTensor f).mapIso
      ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
          ((Iso.refl (DerivedCategory.Q.obj F)).prod (flatPullbackIso f hmos G hG hflatG)) ≪≫
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
          F ((pullbackComplex f).obj G) (kFlat_pullbackComplex' f hmos G hG hflatG)) ≪≫
    derivedRestrictTensorQIso f _

/-- The right-hand side of Stacks 08I6 at a K-flat complex of `O'`-modules with flat terms is
the class of the restriction of scalars of the total tensor complex over `O`: the total tensor
complex over `f⁻¹O'` computes it, and the two total complexes are identified by
`mixedTensorTotalIso`. -/
def derivedMixedTensorModelRight :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (invRing f)).obj
          ((derivedRestrictTensor f).obj (DerivedCategory.Q.obj F))).obj
        ((derivedPullback (auxHomG f)).obj (DerivedCategory.Q.obj G)) ≅
      DerivedCategory.Q.obj ((restrictComplexTensor f).obj
        (HomologicalComplex.mapBifunctor F ((pullbackComplex f).obj G)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ))) :=
  (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (invRing f)).tensor).mapIso
      ((derivedRestrictTensorQIso f F).prod
        (flatPullbackIso (auxHomG f) hmos G hG hflatG)) ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (invRing f)).comparisonRight
        ((restrictComplexTensor f).obj F) ((pullbackComplex (auxHomG f)).obj G)
        (kFlat_pullbackComplex_auxHomG f hmos G hG hflatG) ≪≫
      DerivedCategory.Q.mapIso (mixedTensorTotalIso f F G)

/-- **Stacks 08I6 at a K-flat complex of `O'`-modules with flat terms.**  The two sides are
computed by one and the same complex. -/
def derivedMixedTensorModelIso :
    (derivedRestrictTensor f).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj
            (DerivedCategory.Q.obj F)).obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj G))) ≅
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (invRing f)).obj
            ((derivedRestrictTensor f).obj (DerivedCategory.Q.obj F))).obj
          ((derivedPullback (auxHomG f)).obj (DerivedCategory.Q.obj G)) :=
  derivedMixedTensorModelLeft f hmos F G hG hflatG ≪≫
    (derivedMixedTensorModelRight f hmos F G hG hflatG).symm

/-! ### The two bifunctors -/

section Functors

/-- **The left-hand bifunctor of Stacks 08I6**: `(F, G) ↦ (F ⊗^L_O Lf^*G)|_{f⁻¹O'}`. -/
abbrev mixedDerivedTensorPullback :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) :=
  (𝟭 _).prod (derivedPullback f) ⋙
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O) ⋙
      derivedRestrictTensor f

/-- **The right-hand bifunctor of Stacks 08I6**:
`(F, G) ↦ F|_{f⁻¹O'} ⊗^L_{f⁻¹O'} f⁻¹G`. -/
abbrev mixedDerivedTensorInverseImage :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) :=
  (derivedRestrictTensor f).prod (derivedPullback (auxHomG f)) ⋙
    Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (invRing f))

end Functors

/-! ### Naturality at the models -/

section Naturality

variable {F F' : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (φ : F ⟶ F')
  {G G' : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ} (a : G ⟶ G')
  (hG : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) G)
  (hG' : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) G')
  (hflatG : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (G.X i))
  (hflatG' : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (G'.X i))

/-- A commuting square in the source of `T` stays commuting after `T` and `mapIso`. -/
private theorem map_square_mapIso {C D : Type*} [Category C] [Category D] (T : C ⥤ D)
    {a b c d : C} {m : a ⟶ b} {m' : c ⟶ d} {e : a ≅ c} {e' : b ≅ d}
    (h : m ≫ e'.hom = e.hom ≫ m') : T.map m ≫ (T.mapIso e').hom = (T.mapIso e).hom ≫ T.map m' := by
  rw [Functor.mapIso_hom, Functor.mapIso_hom, ← Functor.map_comp, h, Functor.map_comp]

omit [(pullbackOnHomotopy (auxHomG f)).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ))]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (invRing f))) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)) (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f)).obj M).Additive] in
/-- The left-hand side of Stacks 08I6 at the models is natural in the pair of complexes: the
computation of `Lf^*` on a K-flat complex with flat terms is, the one-sided K-flat comparison
of Stacks 06YU is, and the computation of the derived restriction of scalars is. -/
private lemma derivedMixedTensorModelLeft_naturality :
    (mixedDerivedTensorPullback f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        (derivedMixedTensorModelLeft f hmos F' G' hG' hflatG').hom =
      (derivedMixedTensorModelLeft f hmos F G hG hflatG).hom ≫
        DerivedCategory.Q.map ((restrictComplexTensor f).map
          (HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
            (ComplexShape.up ℤ))) := by
  have hprod : ((𝟭 (DerivedCategory (SheafOfModules.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).prod (derivedPullback f)).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        ((Iso.refl (DerivedCategory.Q.obj F')).prod
          (flatPullbackIso f hmos G' hG' hflatG')).hom =
      ((Iso.refl (DerivedCategory.Q.obj F)).prod (flatPullbackIso f hmos G hG hflatG)).hom ≫
        ((DerivedCategory.Q.map φ,
            DerivedCategory.Q.map ((pullbackComplex f).map a)) :
          ((DerivedCategory.Q.obj F,
              DerivedCategory.Q.obj ((pullbackComplex f).obj G)) : _ × _) ⟶
            (DerivedCategory.Q.obj F',
              DerivedCategory.Q.obj ((pullbackComplex f).obj G'))) :=
    Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
      (flatPullbackIso_naturality f hmos a hG hG' hflatG hflatG')
  have h1 := map_square_mapIso (Functor.uncurry.obj
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor) hprod
  have h2 : (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).map
          ((DerivedCategory.Q.map φ,
              DerivedCategory.Q.map ((pullbackComplex f).map a)) :
            ((DerivedCategory.Q.obj F,
                DerivedCategory.Q.obj ((pullbackComplex f).obj G)) : _ × _) ⟶
              (DerivedCategory.Q.obj F',
                DerivedCategory.Q.obj ((pullbackComplex f).obj G'))) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
          F' ((pullbackComplex f).obj G') (kFlat_pullbackComplex' f hmos G' hG' hflatG')).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
          F ((pullbackComplex f).obj G) (kFlat_pullbackComplex' f hmos G hG hflatG)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ
          ((pullbackComplex f).map a) (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ)) := by
    simpa only [Functor.uncurry_obj_map, Category.assoc] using
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight_naturality
        φ ((pullbackComplex f).map a) (kFlat_pullbackComplex' f hmos G hG hflatG)
        (kFlat_pullbackComplex' f hmos G' hG' hflatG')
  have hinner := trans_naturality h1 h2
  refine trans_naturality ?_ (derivedRestrictTensorQIso_naturality f _)
  rw [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_hom,
    Functor.comp_map, Functor.comp_map, ← Functor.map_comp, hinner]
  exact (derivedRestrictTensor f).map_comp _ _

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ))] in
/-- The right-hand side of Stacks 08I6 at the models is natural in the pair of complexes: the
computation of the derived restriction of scalars is, the computation of `Lf⁻¹` on a K-flat
complex with flat terms is, the one-sided K-flat comparison of Stacks 06YU is, and the identity
of total tensor complexes is. -/
private lemma derivedMixedTensorModelRight_naturality :
    (mixedDerivedTensorInverseImage f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        (derivedMixedTensorModelRight f hmos F' G' hG' hflatG').hom =
      (derivedMixedTensorModelRight f hmos F G hG hflatG).hom ≫
        DerivedCategory.Q.map ((restrictComplexTensor f).map
          (HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
            (ComplexShape.up ℤ))) := by
  have hprod : ((derivedRestrictTensor f).prod (derivedPullback (auxHomG f))).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        ((derivedRestrictTensorQIso f F').prod
          (flatPullbackIso (auxHomG f) hmos G' hG' hflatG')).hom =
      ((derivedRestrictTensorQIso f F).prod
          (flatPullbackIso (auxHomG f) hmos G hG hflatG)).hom ≫
        ((DerivedCategory.Q.map ((restrictComplexTensor f).map φ),
            DerivedCategory.Q.map ((pullbackComplex (auxHomG f)).map a)) :
          ((DerivedCategory.Q.obj ((restrictComplexTensor f).obj F),
              DerivedCategory.Q.obj ((pullbackComplex (auxHomG f)).obj G)) : _ × _) ⟶
            (DerivedCategory.Q.obj ((restrictComplexTensor f).obj F'),
              DerivedCategory.Q.obj ((pullbackComplex (auxHomG f)).obj G'))) :=
    Prod.ext (derivedRestrictTensorQIso_naturality f φ)
      (flatPullbackIso_naturality (auxHomG f) hmos a hG hG' hflatG hflatG')
  have h1 := map_square_mapIso (Functor.uncurry.obj
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct (invRing f)).tensor) hprod
  have h2 : (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
              (invRing f)).tensor).map
          ((DerivedCategory.Q.map ((restrictComplexTensor f).map φ),
              DerivedCategory.Q.map ((pullbackComplex (auxHomG f)).map a)) :
            ((DerivedCategory.Q.obj ((restrictComplexTensor f).obj F),
                DerivedCategory.Q.obj ((pullbackComplex (auxHomG f)).obj G)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((restrictComplexTensor f).obj F'),
                DerivedCategory.Q.obj ((pullbackComplex (auxHomG f)).obj G'))) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
            (invRing f)).comparisonRight ((restrictComplexTensor f).obj F')
          ((pullbackComplex (auxHomG f)).obj G')
          (kFlat_pullbackComplex_auxHomG f hmos G' hG' hflatG')).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          (invRing f)).comparisonRight ((restrictComplexTensor f).obj F)
        ((pullbackComplex (auxHomG f)).obj G)
        (kFlat_pullbackComplex_auxHomG f hmos G hG hflatG)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((restrictComplexTensor f).map φ) ((pullbackComplex (auxHomG f)).map a)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (invRing f))
          (ComplexShape.up ℤ)) := by
    simpa only [Functor.uncurry_obj_map, Category.assoc] using
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          (invRing f)).comparisonRight_naturality ((restrictComplexTensor f).map φ)
        ((pullbackComplex (auxHomG f)).map a)
        (kFlat_pullbackComplex_auxHomG f hmos G hG hflatG)
        (kFlat_pullbackComplex_auxHomG f hmos G' hG' hflatG')
  have h3 := map_square_mapIso DerivedCategory.Q (mixedTensorTotalIso_hom_naturality f φ a)
  rw [Functor.comp_map]
  exact trans_naturality h1 (trans_naturality h2 h3)

/-- **The isomorphism of Stacks 08I6 at a K-flat complex of `O'`-modules with flat terms is
natural in both complexes.**  This is what makes the descent to arbitrary objects of `D(O')`
possible. -/
lemma derivedMixedTensorModelIso_naturality :
    (mixedDerivedTensorPullback f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        (derivedMixedTensorModelIso f hmos F' G' hG' hflatG').hom =
      (derivedMixedTensorModelIso f hmos F G hG hflatG).hom ≫
        (mixedDerivedTensorInverseImage f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) :=
  isoOverCommonTarget_naturality
    (derivedMixedTensorModelLeft_naturality f hmos φ a hG hG' hflatG hflatG')
    (derivedMixedTensorModelRight_naturality f hmos φ a hG hG' hflatG hflatG')

end Naturality

/-! ### The descent to arbitrary objects of the derived categories -/

section Descent

/-- Pairs consisting of a cochain complex of `O`-modules and a K-flat complex of `O'`-modules
with flat terms, mapped to the pair of objects of `D(O) × D(O')` they represent. -/
abbrev mixedModelsQ :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ×
        (IsKFlat (Y := Y)).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  DerivedCategory.Q.prod (flatKFlatModelsQ Y)

/-- The morphisms of pairs that become invertible: a quasi-isomorphism of complexes of
`O`-modules and a quasi-isomorphism of K-flat complexes of `O'`-modules with flat terms. -/
abbrev mixedModelsW :
    MorphismProperty (CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ×
      (IsKFlat (Y := Y)).FullSubcategory) :=
  (HomologicalComplex.quasiIso
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (ComplexShape.up ℤ)).prod (flatKFlatModelsW Y)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive] in
/-- **These pairs localize to `D(O) × D(O')`.**  Every complex of `O`-modules is its own model,
and every object of `D(O')` is represented by a K-flat complex with flat terms, by
Stacks 06YS. -/
theorem mixedModelsQ_isLocalization :
    (mixedModelsQ (X := X) (Y := Y)).IsLocalization (mixedModelsW (X := X) (Y := Y)) := by
  have := flatKFlatModelsQ_isLocalization Y
  infer_instance

/-- The localization carries a pair of models to the pair of objects of `D(O) × D(O')` they
represent. -/
def mixedModelsIso
    (P : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ×
      (IsKFlat (Y := Y)).FullSubcategory) :
    (mixedModelsQ (X := X) (Y := Y)).obj P ≅
      (DerivedCategory.Q.obj P.1, DerivedCategory.Q.obj P.2.obj.as) :=
  (Iso.refl (DerivedCategory.Q.obj P.1)).prod
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app P.2.obj.as)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive] in
/-- The identification of a pair of models with the pair of objects it represents is natural in
the pair of models. -/
lemma mixedModelsIso_naturality
    {P R : CochainComplex (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ ×
      (IsKFlat (Y := Y)).FullSubcategory} (g : P ⟶ R) :
    (mixedModelsQ (X := X) (Y := Y)).map g ≫ (mixedModelsIso R).hom =
      (mixedModelsIso P).hom ≫
        ((DerivedCategory.Q.map g.1, DerivedCategory.Q.map g.2.hom.out) :
          ((DerivedCategory.Q.obj P.1, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
            (DerivedCategory.Q.obj R.1, DerivedCategory.Q.obj R.2.obj.as)) := by
  apply Prod.ext
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have h := DerivedCategory.quotientCompQhIso_hom_naturality
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) g.2.hom.out
    rw [HomotopyCategory.quotient_map_out] at h
    exact h

/-- The isomorphism of Stacks 08I6 at the models, as an isomorphism of the two functors on the
category of pairs of models. -/
def mixedModelsTensorIso :
    mixedModelsQ (X := X) (Y := Y) ⋙ mixedDerivedTensorPullback f ≅
      mixedModelsQ (X := X) (Y := Y) ⋙ mixedDerivedTensorInverseImage f :=
  NatIso.ofComponents
    (fun P =>
      (mixedDerivedTensorPullback f).mapIso (mixedModelsIso P) ≪≫
        derivedMixedTensorModelIso f hmos P.1 P.2.obj.as P.2.property.1 P.2.property.2 ≪≫
          ((mixedDerivedTensorInverseImage f).mapIso (mixedModelsIso P)).symm)
    (fun {P R} g => transportedIso_naturality
      (mixedDerivedTensorPullback f) (mixedDerivedTensorInverseImage f)
      (mixedModelsIso P) (mixedModelsIso R)
      (derivedMixedTensorModelIso f hmos P.1 P.2.obj.as P.2.property.1 P.2.property.2)
      (derivedMixedTensorModelIso f hmos R.1 R.2.obj.as R.2.property.1 R.2.property.2)
      ((mixedModelsQ (X := X) (Y := Y)).map g)
      ((DerivedCategory.Q.map g.1, DerivedCategory.Q.map g.2.hom.out) :
        ((DerivedCategory.Q.obj P.1, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
          (DerivedCategory.Q.obj R.1, DerivedCategory.Q.obj R.2.obj.as))
      (mixedModelsIso_naturality g)
      (derivedMixedTensorModelIso_naturality f hmos g.1 g.2.hom.out
        P.2.property.1 R.2.property.1 P.2.property.2 R.2.property.2))

/-- **Stacks 08I6, read after restriction of scalars to `f⁻¹O'`.**  The bifunctorial
isomorphism

`(F ⊗^L_O Lf^*G)|_{f⁻¹O'} ≅ F|_{f⁻¹O'} ⊗^L_{f⁻¹O'} f⁻¹G`

in `D(f⁻¹O')`, for a site-presented morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(C'), O')`,
`F` in `D(O)` and `G` in `D(O')`.  It is stated between the two uncurried bifunctors on
`D(O) × D(O')`, so that naturality in both variables is part of its type.  The tag itself, in
`D(O)` and for an arbitrary morphism of ringed topoi, is
`Stacks.Cohomology.MixedDerivedTensor.OfToposHom.derivedMixedTensorIso`.

Its value at a complex of `O`-modules and a K-flat complex of `O'`-modules with flat terms is
the chain of the source (`derivedMixedTensorModelIso`): there both sides are computed by total
tensor complexes and the identity is the underived one of the source, applied in each bidegree.
The passage to arbitrary objects is the descent of that value along the localization of pairs
of models. -/
@[stacks 08I6 "variant: the isomorphism read in D(f⁻¹O') after restriction of scalars, for a
site-presented morphism; the tag in D(O) for an arbitrary morphism of ringed topoi is
Stacks.Cohomology.MixedDerivedTensor.OfToposHom.derivedMixedTensorIso"]
def derivedMixedTensorIso :
    mixedDerivedTensorPullback f ≅ mixedDerivedTensorInverseImage f := by
  letI : (mixedModelsQ (X := X) (Y := Y)).IsLocalization (mixedModelsW (X := X) (Y := Y)) :=
    mixedModelsQ_isLocalization
  letI : Localization.Lifting (mixedModelsQ (X := X) (Y := Y))
      (mixedModelsW (X := X) (Y := Y))
      (mixedModelsQ (X := X) (Y := Y) ⋙ mixedDerivedTensorPullback f)
      (mixedDerivedTensorPullback f) := ⟨Iso.refl _⟩
  letI : Localization.Lifting (mixedModelsQ (X := X) (Y := Y))
      (mixedModelsW (X := X) (Y := Y))
      (mixedModelsQ (X := X) (Y := Y) ⋙ mixedDerivedTensorInverseImage f)
      (mixedDerivedTensorInverseImage f) := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (mixedModelsQ (X := X) (Y := Y))
    (mixedModelsW (X := X) (Y := Y)) _ _ _ _ (mixedModelsTensorIso f hmos)

end Descent

end Models

end Stacks.Cohomology.MixedDerivedTensor

end
