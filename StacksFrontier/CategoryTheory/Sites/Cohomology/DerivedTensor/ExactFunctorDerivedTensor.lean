module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorTotalSquare
import StacksCore.Tactic.StacksAttribute

/-!
# An exact functor commuting with the total tensor complex commutes with the derived tensor product

Let `(Sh(C), O)` and `(Sh(D), O')` be ringed topoi and let `F : Mod(O') ⥤ Mod(O)` be an exact
additive functor which

* carries K-flat complexes with flat terms to K-flat complexes (**Stacks 0G7E** for `F`), and
* commutes with the total tensor complex, `F Tot(K ⊗_{O'} L) ≅ Tot(FK ⊗_O FL)` naturally in the
  pair of complexes (**Stacks 03EL** for `F`, assembled on total complexes).

Then the induced functor `LF = F.mapDerivedCategory` of unbounded derived categories commutes with
the derived tensor product of **Stacks 06YU**:

`LF(A ⊗^L_{O'} B) ≅ LF A ⊗^L_O LF B`,

bifunctorially in `A, B ∈ D(O')`. This is **Stacks 07A4** for `F`, and it is proved by the
source's argument: replace `A` and `B` by K-flat complexes with flat terms, where both sides are
computed by total tensor complexes, and descend along the localization.

## Main definitions

* `Stacks.DerivedTensor.ExactFunctorTensor.modelLeft` and `modelRight`: the two halves of the
  chain at a pair of models, meeting at `Q(F Tot(K ⊗_{O'} L))`.
* `Stacks.DerivedTensor.ExactFunctorTensor.modelIso`: their composite.
* `Stacks.DerivedTensor.ExactFunctorTensor.derivedTensorIso`: **Stacks 07A4 for `F`**.

## Main results

* `Stacks.DerivedTensor.ExactFunctorTensor.modelIso_naturality`: the value at a pair of models is
  natural in both complexes, which is what makes the descent possible.

## Implementation notes

*Why this is separate from `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`.* That
declaration is Stacks 07A4 for an `AlgebraicGeometry.RingedToposSiteHom` together with a
`CategoryTheory.Functor.IsMorphismOfSites` hypothesis — a morphism of ringed topoi *presented by a
continuous functor of the underlying sites in the opposite direction*. Several functors of sheaves
of modules that commute with the tensor product are not presented that way; the inclusion of a
simplicial component is one (its site functor points at the source and is continuous *and*
cocontinuous, so the geometric morphism comes from the cocontinuity and there is no functor of
sites to supply). This file is the same descent with the geometric input replaced by the two
properties of `F` that the descent actually consumes, so it applies to any of them.

*What the exactness of `F` buys.* `LF` is `CategoryTheory.Functor.mapDerivedCategory`, not a
`totalLeftDerived`, so the step computing `LF` on a representative is
`CategoryTheory.Functor.mapDerivedCategoryFactors` and carries **no** K-flatness hypothesis; in
the pullback case the corresponding step is available only on a K-flat complex with flat terms and
the hypotheses have to be threaded through both halves of the chain. Here the K-flatness
hypothesis `hkflat` is consumed only in the second half, by the K-flat comparison of Stacks 06YU
on the target.

*The localization is reused, not rebuilt.*
`Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ` and its companions depend only on the source
ringed topos `Y`, not on any morphism, so they are taken from the 07A4 file unchanged; likewise
the three bookkeeping lemmas `isoOverCommonTarget_naturality`, `transportedIso_naturality` and
`trans_naturality`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe u

namespace Stacks.DerivedTensor.ExactFunctorTensor

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Degreewise application of `F` to cochain complexes of sheaves of modules. -/
abbrev complexFunctor :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ :=
  F.mapHomologicalComplex (ComplexShape.up ℤ)

variable
  (hkflat : ∀ (K : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K →
    (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) →
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) ((complexFunctor F).obj K))
  (tot : ∀ (K L : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    (complexFunctor F).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((complexFunctor F).obj K) ((complexFunctor F).obj L)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ))
  (tot_nat : ∀ {K K' L L' : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
      (a : K ⟶ K') (b : L ⟶ L'),
    (complexFunctor F).map (HomologicalComplex.mapBifunctorMap a b
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)) ≫
        (tot K' L').hom =
      (tot K L).hom ≫ HomologicalComplex.mapBifunctorMap ((complexFunctor F).map a)
        ((complexFunctor F).map b) (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
        (ComplexShape.up ℤ))

/-! ### The comparison at a pair of K-flat complexes with flat terms -/

/-- **The first half of the chain.** For K-flat `K` and `L`, `LF(QK ⊗^L QL)` is the image in
`D(O)` of `F` of the total tensor complex: the K-flat comparison of Stacks 06YU followed by the
factorisation of `LF` through degreewise `F`. No flatness of the terms is needed; `F` is exact. -/
def modelLeft
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L) :
    F.mapDerivedCategory.obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O).obj
          (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj ((complexFunctor F).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) :=
  F.mapDerivedCategory.mapIso
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
        K L hK hL) ≪≫
    F.mapDerivedCategoryFactors.app (HomologicalComplex.mapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))

/-- **The second half of the chain.** For K-flat `K` and `L` with flat terms,
`LF QK ⊗^L LF QL` is the image in `D(O)` of `F` of the total tensor complex: the factorisation of
`LF` in each tensor factor, then the K-flat comparison of Stacks 06YU — legitimate by `hkflat` —
then the comparison of total tensor complexes. -/
def modelRight
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj
          (F.mapDerivedCategory.obj (DerivedCategory.Q.obj K))).obj
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj ((complexFunctor F).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) :=
  (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
      ((F.mapDerivedCategoryFactors.app K).prod (F.mapDerivedCategoryFactors.app L)) ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
        ((complexFunctor F).obj K) ((complexFunctor F).obj L)
        (hkflat K hK hflatK) (hkflat L hL hflatL) ≪≫
      (DerivedCategory.Q.mapIso (tot K L)).symm

/-- **The comparison of Stacks 07A4 for `F` at a pair of K-flat complexes with flat terms**: the
two halves of the chain, which land in the same object of `D(O)`. -/
def modelIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          F.mapDerivedCategory).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  modelLeft F K L hK hL ≪≫ (modelRight F hkflat tot K L hK hL hflatK hflatL).symm

/-! ### Naturality of the value at a pair of models -/

section Naturality

variable {K K' L L' : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}

variable (a : K ⟶ K') (b : L ⟶ L')

variable (hK : CochainComplex.KFlatBifunctor.KFlat
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)

variable (hK' : CochainComplex.KFlatBifunctor.KFlat
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K')

variable (hL : CochainComplex.KFlatBifunctor.KFlat
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)

variable (hL' : CochainComplex.KFlatBifunctor.KFlat
  (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L')

variable (hflatK : ∀ i : ℤ,
  AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))

variable (hflatK' : ∀ i : ℤ,
  AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K'.X i))

variable (hflatL : ∀ i : ℤ,
  AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))

variable (hflatL' : ∀ i : ℤ,
  AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L'.X i))

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive] in
/-- The first half of the chain is natural in the pair of complexes: the K-flat comparison of
Stacks 06YU is, and so is the factorisation of `LF` through degreewise `F`. -/
private lemma modelLeft_naturality :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          F.mapDerivedCategory).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (modelLeft F K' L' hK' hL').hom =
      (modelLeft F K L hK hL).hom ≫
        DerivedCategory.Q.map ((complexFunctor F).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))) := by
  dsimp only [modelLeft]
  have s1 : (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          F.mapDerivedCategory).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        F.mapDerivedCategory.map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
            K' L' hK' hL').hom =
      F.mapDerivedCategory.map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
            K L hK hL).hom ≫
        F.mapDerivedCategory.map (DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))) := by
    rw [Functor.comp_map, Functor.uncurry_obj_map, ← Functor.map_comp, ← Functor.map_comp,
      Category.assoc]
    exact congrArg F.mapDerivedCategory.map
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison_naturality
        a b hK hK' hL hL')
  exact Stacks.Sheaves.DerivedPullback.trans_naturality s1
    (F.mapDerivedCategoryFactors_hom_naturality (HomologicalComplex.mapBifunctorMap a b
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)))

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include tot_nat in
/-- The second half of the chain is natural in the pair of complexes: the factorisation of `LF`
in each tensor factor is, the K-flat comparison of Stacks 06YU is, and the comparison of total
tensor complexes is, by `tot_nat`. -/
private lemma modelRight_naturality :
    (F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (modelRight F hkflat tot K' L' hK' hL' hflatK' hflatL').hom =
      (modelRight F hkflat tot K L hK hL hflatK hflatL).hom ≫
        DerivedCategory.Q.map ((complexFunctor F).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))) := by
  dsimp only [modelRight]
  have he : (F.mapDerivedCategory.prod F.mapDerivedCategory).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        ((F.mapDerivedCategoryFactors.app K').prod
          (F.mapDerivedCategoryFactors.app L')).hom =
      ((F.mapDerivedCategoryFactors.app K).prod
          (F.mapDerivedCategoryFactors.app L)).hom ≫
        ((DerivedCategory.Q.map ((complexFunctor F).map a),
            DerivedCategory.Q.map ((complexFunctor F).map b)) :
          ((DerivedCategory.Q.obj ((complexFunctor F).obj K),
              DerivedCategory.Q.obj ((complexFunctor F).obj L)) : _ × _) ⟶
            (DerivedCategory.Q.obj ((complexFunctor F).obj K'),
              DerivedCategory.Q.obj ((complexFunctor F).obj L'))) :=
    Prod.ext (F.mapDerivedCategoryFactors_hom_naturality a)
      (F.mapDerivedCategoryFactors_hom_naturality b)
  have h1 : (F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
          ((F.mapDerivedCategoryFactors.app K').prod
            (F.mapDerivedCategoryFactors.app L'))).hom =
      ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
          ((F.mapDerivedCategoryFactors.app K).prod
            (F.mapDerivedCategoryFactors.app L))).hom ≫
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).map
          ((DerivedCategory.Q.map ((complexFunctor F).map a),
              DerivedCategory.Q.map ((complexFunctor F).map b)) :
            ((DerivedCategory.Q.obj ((complexFunctor F).obj K),
                DerivedCategory.Q.obj ((complexFunctor F).obj L)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((complexFunctor F).obj K'),
                DerivedCategory.Q.obj ((complexFunctor F).obj L'))) := by
    rw [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_hom,
      Functor.comp_map, ← Functor.map_comp, he, Functor.map_comp]
  have h2 : (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).map
          ((DerivedCategory.Q.map ((complexFunctor F).map a),
              DerivedCategory.Q.map ((complexFunctor F).map b)) :
            ((DerivedCategory.Q.obj ((complexFunctor F).obj K),
                DerivedCategory.Q.obj ((complexFunctor F).obj L)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((complexFunctor F).obj K'),
                DerivedCategory.Q.obj ((complexFunctor F).obj L'))) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          ((complexFunctor F).obj K') ((complexFunctor F).obj L')
          (hkflat K' hK' hflatK') (hkflat L' hL' hflatL')).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          ((complexFunctor F).obj K) ((complexFunctor F).obj L)
          (hkflat K hK hflatK) (hkflat L hL hflatL)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexFunctor F).map a) ((complexFunctor F).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
    simpa only [Functor.uncurry_obj_map, Category.assoc] using
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison_naturality
        ((complexFunctor F).map a) ((complexFunctor F).map b)
        (hkflat K hK hflatK) (hkflat K' hK' hflatK')
        (hkflat L hL hflatL) (hkflat L' hL' hflatL')
  have hth : DerivedCategory.Q.map ((complexFunctor F).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) ≫
        (DerivedCategory.Q.mapIso (tot K' L')).hom =
      (DerivedCategory.Q.mapIso (tot K L)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexFunctor F).map a) ((complexFunctor F).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
    rw [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_hom,
      ← Functor.map_comp, ← Functor.map_comp, tot_nat a b]
  have h3 : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((complexFunctor F).map a) ((complexFunctor F).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) ≫
        (DerivedCategory.Q.mapIso (tot K' L')).symm.hom =
      (DerivedCategory.Q.mapIso (tot K L)).symm.hom ≫
        DerivedCategory.Q.map ((complexFunctor F).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) :=
    (CommSq.vert_inv ⟨hth⟩).w
  exact Stacks.Sheaves.DerivedPullback.trans_naturality h1
    (Stacks.Sheaves.DerivedPullback.trans_naturality h2 h3)

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Y.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include tot_nat in
/-- **The value of the comparison at a pair of K-flat complexes with flat terms is natural in
both complexes.** This is what makes the descent to arbitrary objects of `D(O')` possible. -/
lemma modelIso_naturality :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          F.mapDerivedCategory).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (modelIso F hkflat tot K' L' hK' hL' hflatK' hflatL').hom =
      (modelIso F hkflat tot K L hK hL hflatK hflatL).hom ≫
        (F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
            Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
          ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
            ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
              (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) := by
  dsimp only [modelIso]
  exact Stacks.Sheaves.DerivedPullback.isoOverCommonTarget_naturality
    (modelLeft_naturality F a b hK hK' hL hL')
    (modelRight_naturality F hkflat tot tot_nat a b hK hK' hL hL'
      hflatK hflatK' hflatL hflatL')

end Naturality

/-! ### The descent to arbitrary objects of the derived category -/

section Descent

include tot_nat in
/-- The comparison at a pair of K-flat complexes with flat terms, as an isomorphism of the two
functors on the category of pairs of models. -/
def flatKFlatModelPairsTensorIso :
    Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y ⋙
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          F.mapDerivedCategory) ≅
      Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y ⋙
        (F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)) :=
  NatIso.ofComponents
    (fun P =>
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          F.mapDerivedCategory).mapIso
          (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso Y P) ≪≫
        modelIso F hkflat tot P.1.obj.as P.2.obj.as
            P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2 ≪≫
          ((F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
            Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).mapIso
            (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso Y P)).symm)
    (fun {P R} g => Stacks.Sheaves.DerivedPullback.transportedIso_naturality
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
        F.mapDerivedCategory)
      (F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
        Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso Y P)
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso Y R)
      (modelIso F hkflat tot P.1.obj.as P.2.obj.as
        P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2)
      (modelIso F hkflat tot R.1.obj.as R.2.obj.as
        R.1.property.1 R.2.property.1 R.1.property.2 R.2.property.2)
      ((Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).map g)
      ((DerivedCategory.Q.map g.1.hom.out, DerivedCategory.Q.map g.2.hom.out) :
        ((DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
          (DerivedCategory.Q.obj R.1.obj.as, DerivedCategory.Q.obj R.2.obj.as))
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso_naturality Y g)
      (modelIso_naturality F hkflat tot tot_nat g.1.hom.out g.2.hom.out
        P.1.property.1 R.1.property.1 P.2.property.1 R.2.property.1
        P.1.property.2 R.1.property.2 P.2.property.2 R.2.property.2))

include tot_nat in
/-- **Stacks 07A4 for an exact functor commuting with the total tensor complex.** The canonical
bifunctorial isomorphism

`LF(A ⊗^L_{O'} B) ≅ LF A ⊗^L_O LF B`,

stated between the two uncurried bifunctors on `D(O') × D(O')`, so that naturality in both
variables is part of its type.

Its value on a pair of K-flat complexes with flat terms is
`Stacks.DerivedTensor.ExactFunctorTensor.modelIso`, and the passage to arbitrary objects of
`D(O')` is the descent of that value along the localization of pairs of models. -/
@[stacks 07A4 "for an exact functor of sheaves of modules commuting with the total tensor complex"]
def derivedTensorIso :
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
        F.mapDerivedCategory ≅
      F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O) := by
  letI : (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).IsLocalization
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsW Y) :=
    Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ_isLocalization Y
  letI : Localization.Lifting (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y)
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsW Y)
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y ⋙
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          F.mapDerivedCategory))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
        F.mapDerivedCategory) := ⟨Iso.refl _⟩
  letI : Localization.Lifting (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y)
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsW Y)
      (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y ⋙
        (F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)))
      (F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)) := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y)
    (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsW Y) _ _ _ _
    (flatKFlatModelPairsTensorIso F hkflat tot tot_nat)

end Descent

/-! ### The value of the comparison at a pair of models -/

section Model

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include tot_nat in
/-- The comparison evaluated on the image of a pair of K-flat complexes with flat terms is the
transported value out of which it was descended. -/
lemma derivedTensorIso_hom_app_modelPair
    (PP : (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
          (Y := Y)).FullSubcategory ×
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)).FullSubcategory) :
    (derivedTensorIso F hkflat tot tot_nat).hom.app
        ((Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y).obj PP) =
      (flatKFlatModelPairsTensorIso F hkflat tot tot_nat).hom.app PP := by
  have := Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ_isLocalization Y
  have hdef : derivedTensorIso F hkflat tot tot_nat =
      Localization.liftNatIso (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ Y)
        (Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsW Y) _ _ _ _
        (h₁ := ⟨Iso.refl _⟩) (h₂ := ⟨Iso.refl _⟩)
        (flatKFlatModelPairsTensorIso F hkflat tot tot_nat) :=
    rfl
  rw [hdef, Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  simp

omit [X.J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
include tot_nat in
/-- **The comparison at a pair of K-flat complexes with flat terms is the composite of the two
halves of the chain.** This is what pins the comparison down: everything proved about it beyond
its bifunctoriality is proved here and transported along the descent. -/
lemma derivedTensorIso_hom_app_model
    (P N : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hP : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) P)
    (hN : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) N)
    (hflatP : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (hflatN : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (N.X i)) :
    (derivedTensorIso F hkflat tot tot_nat).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj N) =
      (modelIso F hkflat tot P N hP hN hflatP hflatN).hom := by
  let e := Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsIso Y
    ((⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P, ⟨hP, hflatP⟩⟩,
      ⟨(HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj N, ⟨hN, hflatN⟩⟩) :
      (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat (Y := Y)).FullSubcategory ×
        (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
          (Y := Y)).FullSubcategory)
  have hnat := (derivedTensorIso F hkflat tot tot_nat).hom.naturality e.hom
  rw [derivedTensorIso_hom_app_modelPair F hkflat tot tot_nat] at hnat
  refine (cancel_epi ((Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
    F.mapDerivedCategory).map e.hom)).1 (hnat.trans ?_)
  exact Stacks.Sheaves.DerivedPullback.transportedIso_hom_comp
    ((Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
      F.mapDerivedCategory).mapIso e)
    ((F.mapDerivedCategory.prod F.mapDerivedCategory ⋙
      Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).mapIso e)
    (modelIso F hkflat tot P N hP hN hflatP hflatN)

end Model

end Stacks.DerivedTensor.ExactFunctorTensor

end
