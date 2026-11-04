module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparison

/-! # Derived pullback and the derived tensor product, for a morphism of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi in the sense of Stacks 01D3,
part (2) — a morphism of the underlying *topoi* together with the structure map, so that no
functor between the underlying sites is asked for. **Stacks 07A4** asserts a canonical
bifunctorial isomorphism

`Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L`

for `K, L ∈ D(O')`. This file proves it with that geometric datum, and therefore with **no
morphism-of-sites hypothesis anywhere in its statement**.

The proof is the source's, and is the one
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackTensorComparison.lean`
runs for a site-presented morphism. Reading the composite at a pair of K-flat complexes with flat
terms left to right:

1. `K ⊗^L L` is `Q Tot(K ⊗ L)`, by the K-flat comparison of **Stacks 06YU**;
2. `Lf^*` of that is `Q(f^*Tot(K ⊗ L))`, because `Tot(K ⊗ L)` is again K-flat with flat terms by
   **Stacks 079R** and **Stacks 0G6Q**, and such a complex computes `Lf^*` by **Stacks 06YY**;
3. `f^*Tot(K ⊗ L)` is `Tot(f^*K ⊗ f^*L)`, degreewise by **Stacks 03EL**;
4. `Tot(f^*K ⊗ f^*L)` is `f^*K ⊗^L f^*L`, because `f^*K` and `f^*L` are K-flat by
   **Stacks 0G7E**;
5. `f^*K` and `f^*L` are `Lf^*K` and `Lf^*L`, by the same computation as step 2.

The passage from K-flat representatives to arbitrary objects of `D(O')` is the descent along a
localization, exactly as in the site-presented development: the K-flat complexes with flat terms
already localize to `D(O')`, so pairs of them localize to pairs of objects of `D(O')`, and the
value of the composite at a pair of models, being natural in homotopy classes of maps between
models, extends uniquely.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.OfToposHom.flatPullbackIso`: **Stacks 06YY**, the computation
  `Lf^*(QK) ≅ Q(f^*K)` on a K-flat complex with flat terms, for a morphism of ringed topoi.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorModelIso`: the isomorphism of
  Stacks 07A4 at a pair of K-flat complexes with flat terms, as the five-step composite above.
* `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso`: **Stacks 07A4**, the
  canonical bifunctorial isomorphism `Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L`.

## Main results

* `Stacks.Sheaves.DerivedPullback.OfToposHom.flatPullbackIso_naturality` and
  `derivedPullbackTensorModelIso_naturality`: the computation of Stacks 06YY and the value of the
  comparison at a pair of models are natural, which is what makes the descent possible.

## Implementation notes

*No morphism-of-sites hypothesis, and why the site-presented statement had one.*
`AlgebraicGeometry.RingedToposSiteHom` asks only that the underlying functor `f.u` be
*continuous*; the inverse image along a merely continuous functor need not be exact, so such an
`f` need not present a morphism of topoi at all, and the site-presented development carries
`f.u.IsMorphismOfSites Y.J X.J` to supply that exactness. For an
`AlgebraicGeometry.RingedToposHom` the exactness is a field of
`AlgebraicGeometry.MorphismOfTopoi`, so every input of the chain is unconditional and the
hypothesis disappears. Concretely: the derived pullback is
`Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback` (Stacks 06YY), whose existence is
`Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy` and whose
computation on the K-flat class is `isIso_derivedPullbackComparison_app_isKFlat` of
`Stacks.Cohomology.DerivedPullbackCompositionOfToposHom`;
Stacks 0G7E is `Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex`;
and Stacks 03EL at the level of total tensor complexes is
`Stacks.Sheaves.DerivedPullback.pullbackTensorTotalIso`, which is stated for the pullback of
Stacks 03D6 part (2) and so needs no transport along a comparison of two pullbacks — that
transport, `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso`, is the last place the
site-presented development consumed the hypothesis.

*What is reused rather than restated.* Everything that does not mention `f`: the localization of
pairs of models (`Stacks.Sheaves.DerivedPullback.flatKFlatModelPairsQ_isLocalization`,
`flatKFlatModelPairsIso` and its naturality), the two pieces of naturality bookkeeping
(`trans_naturality`, `isoOverCommonTarget_naturality`, `transportedIso_naturality`), the
flatness of the terms of a total tensor complex (`isFlat_tensorComplex_X`) and the K-flatness of
a total tensor complex (`Stacks.SheafOfModules.kFlat_tensorComplex`). Only the seven statements
that mention `f` are proved here.

*The left-derived-functor instance.* Unlike the site-presented development this file does not
carry `(pullbackOnHomotopy f).HasLeftDerivedFunctor` at all: it is installed as a file-local
instance from `hasLeftDerivedFunctor_pullbackOnHomotopy`, which holds for every morphism of
ringed topoi. The same is true of the three inputs of Stacks 0G7E, which
`Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom` has already discharged.

*The universe narrowing, inherited.* Both ringed topoi are taken at `RingedTopos.{u, u, u}`:
the object, morphism and section universes agree, and the site is small. This is **not** chosen
here, and it is not what the morphism-of-sites hypothesis used to force. The derived tensor
product of Stacks 06YU is available only at those universes, a narrowing
`Stacks.DerivedTensor.RingedSite.exists_derivedTensorProduct` records as coming down from
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution` and ultimately from
`Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeYoneda`, which pins the ring universe to the
site's hom universe. The derived pullback of Stacks 06YY and the comparison of Stacks 03EL used
below are both stated with all six universes of the two ringed topoi free; the derived category's
own hom universe stays independent too.

*Uncurrying.* The isomorphism is stated between the two uncurried bifunctors on
`D(O') × D(O')`, so that naturality in both variables is part of its type rather than two
separate clauses, and so that the descent is a single application of
`CategoryTheory.Localization.liftNatIso` along one localization functor.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 079R](https://stacks.math.columbia.edu/tag/079R)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
  (isIso_derivedPullbackComparison_app_isKFlat)
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

namespace Stacks.Sheaves.DerivedPullback.OfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- A functor sends a commuting square of isomorphisms (on `hom` components) to one. -/
private lemma map_mapIso_hom_naturality {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A A' B B' : C} {u : A ⟶ A'} {v : B ⟶ B'} {e : A ≅ B} {e' : A' ≅ B'}
    (h : u ≫ e'.hom = e.hom ≫ v) : F.map u ≫ (F.mapIso e').hom = (F.mapIso e).hom ≫ F.map v := by
  rw [Functor.mapIso_hom, Functor.mapIso_hom, ← F.map_comp, h, F.map_comp]

/-! ## The computation of Stacks 06YY on a K-flat complex with flat terms -/

section Computation

/-- **A K-flat complex with flat terms computes the derived pullback along a morphism of ringed
topoi.** For such a complex `K` of `O'`-modules the derived pullback `Lf^*(QK)` is the image in
`D(O)` of the degreewise pullback `f^*K`.

This is the computation assertion of Stacks 06YY, packaged as an isomorphism with the two
comparisons between `Q` and `Qh ∘ quotient` inserted at either end, so that its source and
target are written with `Q`, which is the functor the derived tensor product of Stacks 06YU is
stated against. -/
def flatPullbackIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (K.X i)) :
    (derivedPullback f).obj (DerivedCategory.Q.obj K) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj K) :=
  (derivedPullback f).mapIso ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app K).symm ≪≫
    (@asIso _ _ _ _ ((derivedPullbackComparison f).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
      (isIso_derivedPullbackComparison_app_isKFlat f _ ⟨hK, hflat⟩) ≪≫
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app
          ((pullbackComplex f).obj K))

/-- **The identification of the derived pullback of a K-flat complex with flat terms with its
degreewise pullback is natural in the complex.** -/
lemma flatPullbackIso_naturality
    {K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (a : K ⟶ L)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (L.X i)) :
    (derivedPullback f).map (DerivedCategory.Q.map a) ≫
        (flatPullbackIso f L hL hflatL).hom =
      (flatPullbackIso f K hK hflatK).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map a) := by
  have hC : (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) ≫
        (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L) =
      (derivedPullbackComparison f).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((pullbackComplex f).map a)) :=
    (derivedPullbackComparison f).naturality
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)
  have hD : (derivedPullback f).map (DerivedCategory.Q.map a) ≫
        (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app L) =
      (derivedPullback f).map ((DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).inv.app K) ≫
        (derivedPullback f).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map a)) := by
    rw [← Functor.map_comp, ← Functor.map_comp, DerivedCategory.quotientCompQhIso_inv_naturality
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) a]
  exact trans_naturality hD (trans_naturality hC
    (DerivedCategory.quotientCompQhIso_hom_naturality
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((pullbackComplex f).map a)))

end Computation

/-! ## The comparison at a pair of K-flat complexes with flat terms -/

section Models

variable
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

/-- **Stacks 0G7E with every input discharged**: the degreewise pullback of a K-flat complex of
`O'`-modules with flat terms along a morphism of ringed topoi is a K-flat complex of
`O`-modules. -/
theorem kFlatBifunctor_pullbackComplex
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (K.X i)) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      ((pullbackComplex f).obj K) :=
  (Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor X.O _).1
    (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex f K
      ((Stacks.SheafOfModules.KFlat.kFlat_iff_kFlatBifunctor Y.O K).2 hK) hflat)

/-- **Steps 1 and 2 of the chain**: for K-flat `K` and `L` with flat terms, `Lf^*(K ⊗^L L)` is
the image in `D(O)` of the degreewise pullback of the total tensor complex. -/
def derivedPullbackTensorModelLeft
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (L.X i)) :
    (derivedPullback f).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O).obj
          (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) :=
  (derivedPullback f).mapIso
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
        K L hK hL) ≪≫
    flatPullbackIso f
      (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))
      (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
      (isFlat_tensorComplex_X Y.O K L hflatK hflatL)

/-- **Steps 3, 4 and 5 of the chain**: for K-flat `K` and `L` with flat terms,
`Lf^*K ⊗^L Lf^*L` is the image in `D(O)` of the degreewise pullback of the total tensor
complex. -/
def derivedPullbackTensorModelRight
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (L.X i)) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj K))).obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) :=
  (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
      ((flatPullbackIso f K hK hflatK).prod (flatPullbackIso f L hL hflatL)) ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
        ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlatBifunctor_pullbackComplex f K hK hflatK)
        (kFlatBifunctor_pullbackComplex f L hL hflatL) ≪≫
      (DerivedCategory.Q.mapIso (pullbackTensorTotalIso f.toModulesHom K L)).symm

/-- **The isomorphism of Stacks 07A4 at a pair of K-flat complexes with flat terms**: the two
halves of the five-step chain, which land in the same object of `D(O)`. -/
def derivedPullbackTensorModelIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := Y.O) (L.X i)) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  derivedPullbackTensorModelLeft f K L hK hL hflatK hflatL ≪≫
    (derivedPullbackTensorModelRight f K L hK hL hflatK hflatL).symm

section Naturality

variable {K K' L L' : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
  (a : K ⟶ K') (b : L ⟶ L')
  (hK : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
  (hK' : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K')
  (hL : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
  (hL' : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L')
  (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
  (hflatK' : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K'.X i))
  (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i))
  (hflatL' : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L'.X i))

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- The first half of the chain is natural in the pair of complexes: the K-flat comparison of
Stacks 06YU is, and so is the computation of `Lf^*` on a K-flat complex with flat terms. -/
private lemma derivedPullbackTensorModelLeft_naturality :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullbackTensorModelLeft f K' L' hK' hL' hflatK' hflatL').hom =
      (derivedPullbackTensorModelLeft f K L hK hL hflatK hflatL).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))) := by
  dsimp only [derivedPullbackTensorModelLeft]
  have s1 : (Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
            K' L' hK' hL').hom =
      (derivedPullback f).map
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
            K L hK hL).hom ≫
        (derivedPullback f).map (DerivedCategory.Q.map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))) := by
    rw [Functor.comp_map, Functor.uncurry_obj_map, ← Functor.map_comp, ← Functor.map_comp,
      Category.assoc]
    exact congrArg (derivedPullback f).map
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison_naturality
        a b hK hK' hL hL')
  exact trans_naturality s1 (flatPullbackIso_naturality f
    (HomologicalComplex.mapBifunctorMap a b
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK' hL')
    (isFlat_tensorComplex_X Y.O K L hflatK hflatL)
    (isFlat_tensorComplex_X Y.O K' L' hflatK' hflatL'))

/-- The second half of the chain is natural in the pair of complexes: the computation of `Lf^*`
in each tensor factor is, the K-flat comparison of Stacks 06YU is, and the comparison of total
tensor complexes of Stacks 03EL is. -/
private lemma derivedPullbackTensorModelRight_naturality :
    ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullbackTensorModelRight f K' L' hK' hL' hflatK' hflatL').hom =
      (derivedPullbackTensorModelRight f K L hK hL hflatK hflatL).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))) := by
  dsimp only [derivedPullbackTensorModelRight]
  have he : ((derivedPullback f).prod (derivedPullback f)).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        ((flatPullbackIso f K' hK' hflatK').prod
          (flatPullbackIso f L' hL' hflatL')).hom =
      ((flatPullbackIso f K hK hflatK).prod
          (flatPullbackIso f L hL hflatL)).hom ≫
        ((DerivedCategory.Q.map ((pullbackComplex f).map a),
            DerivedCategory.Q.map ((pullbackComplex f).map b)) :
          ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
              DerivedCategory.Q.obj ((pullbackComplex f).obj L)) : _ × _) ⟶
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K'),
              DerivedCategory.Q.obj ((pullbackComplex f).obj L'))) :=
    Prod.ext (flatPullbackIso_naturality f a hK hK' hflatK hflatK')
      (flatPullbackIso_naturality f b hL hL' hflatL hflatL')
  have h2 : (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).map
          ((DerivedCategory.Q.map ((pullbackComplex f).map a),
              DerivedCategory.Q.map ((pullbackComplex f).map b)) :
            ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                DerivedCategory.Q.obj ((pullbackComplex f).obj L)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((pullbackComplex f).obj K'),
                DerivedCategory.Q.obj ((pullbackComplex f).obj L'))) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          ((pullbackComplex f).obj K') ((pullbackComplex f).obj L')
          (kFlatBifunctor_pullbackComplex f K' hK' hflatK')
          (kFlatBifunctor_pullbackComplex f L' hL' hflatL')).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (kFlatBifunctor_pullbackComplex f K hK hflatK)
          (kFlatBifunctor_pullbackComplex f L hL hflatL)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((pullbackComplex f).map a) ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ)) := by
    simpa only [Functor.uncurry_obj_map, Category.assoc] using
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison_naturality
        ((pullbackComplex f).map a) ((pullbackComplex f).map b)
        (kFlatBifunctor_pullbackComplex f K hK hflatK)
        (kFlatBifunctor_pullbackComplex f K' hK' hflatK')
        (kFlatBifunctor_pullbackComplex f L hL hflatL)
        (kFlatBifunctor_pullbackComplex f L' hL' hflatL')
  have h3 : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((pullbackComplex f).map a) ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ)) ≫
        (DerivedCategory.Q.mapIso (pullbackTensorTotalIso f.toModulesHom K' L')).symm.hom =
      (DerivedCategory.Q.mapIso (pullbackTensorTotalIso f.toModulesHom K L)).symm.hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))) :=
    (CommSq.vert_inv ⟨map_mapIso_hom_naturality _
      (pullbackTensorTotalIso_hom_naturality f.toModulesHom a b)⟩).w
  exact trans_naturality
    (map_mapIso_hom_naturality (Functor.uncurry.obj
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor) he)
    (trans_naturality h2 h3)

/-- **The value of the comparison at a pair of K-flat complexes with flat terms is natural in
both complexes.** This is what makes the descent to arbitrary objects of `D(O')` possible. -/
lemma derivedPullbackTensorModelIso_naturality :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullbackTensorModelIso f K' L' hK' hL' hflatK' hflatL').hom =
      (derivedPullbackTensorModelIso f K L hK hL hflatK hflatL).hom ≫
        ((derivedPullback f).prod (derivedPullback f) ⋙
            Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
          ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
            ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
              (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) := by
  dsimp only [derivedPullbackTensorModelIso]
  exact isoOverCommonTarget_naturality
    (derivedPullbackTensorModelLeft_naturality f a b hK hK' hL hL'
      hflatK hflatK' hflatL hflatL')
    (derivedPullbackTensorModelRight_naturality f a b hK hK' hL hL'
      hflatK hflatK' hflatL hflatL')

end Naturality

/-! ## The descent to arbitrary objects of the derived category -/

section Descent

/-- The comparison at a pair of K-flat complexes with flat terms, as an isomorphism of the two
functors on the category of pairs of models. -/
def flatKFlatModelPairsTensorIso :
    flatKFlatModelPairsQ Y ⋙
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f) ≅
      flatKFlatModelPairsQ Y ⋙
        ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)) :=
  NatIso.ofComponents
    (fun P =>
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f).mapIso (flatKFlatModelPairsIso Y P) ≪≫
        derivedPullbackTensorModelIso f P.1.obj.as P.2.obj.as
            P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2 ≪≫
          (((derivedPullback f).prod (derivedPullback f) ⋙
            Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).mapIso
            (flatKFlatModelPairsIso Y P)).symm)
    (fun {P R} g => transportedIso_naturality
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
        derivedPullback f)
      ((derivedPullback f).prod (derivedPullback f) ⋙
        Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))
      (flatKFlatModelPairsIso Y P) (flatKFlatModelPairsIso Y R)
      (derivedPullbackTensorModelIso f P.1.obj.as P.2.obj.as
        P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2)
      (derivedPullbackTensorModelIso f R.1.obj.as R.2.obj.as
        R.1.property.1 R.2.property.1 R.1.property.2 R.2.property.2)
      ((flatKFlatModelPairsQ Y).map g)
      ((DerivedCategory.Q.map g.1.hom.out, DerivedCategory.Q.map g.2.hom.out) :
        ((DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
          (DerivedCategory.Q.obj R.1.obj.as, DerivedCategory.Q.obj R.2.obj.as))
      (flatKFlatModelPairsIso_naturality Y g)
      (derivedPullbackTensorModelIso_naturality f g.1.hom.out g.2.hom.out
        P.1.property.1 R.1.property.1 P.2.property.1 R.2.property.1
        P.1.property.2 R.1.property.2 P.2.property.2 R.2.property.2))

/-- **Stacks 07A4.** The canonical bifunctorial isomorphism

`Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L`

for a morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(D), O')` — a morphism of the underlying
topoi together with the structure map, with no hypothesis on the underlying sites — stated
between the two uncurried bifunctors on `D(O') × D(O')`, so that naturality in both variables
is part of its type.

Its value on a pair of K-flat complexes with flat terms is the five-step composite of the source
(`derivedPullbackTensorModelIso`), and the passage to arbitrary objects of `D(O')` is the
descent of that value along the localization of pairs of models. -/
@[stacks 07A4 "the canonical bifunctorial isomorphism, for a morphism of ringed topoi whose
geometric datum is a morphism of the underlying topoi rather than of the underlying sites"]
def derivedPullbackTensorIso :
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
        derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O) := by
  letI : (flatKFlatModelPairsQ Y).IsLocalization (flatKFlatModelPairsW Y) :=
    flatKFlatModelPairsQ_isLocalization Y
  letI : Localization.Lifting (flatKFlatModelPairsQ Y) (flatKFlatModelPairsW Y)
      (flatKFlatModelPairsQ Y ⋙
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f))
      (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
        derivedPullback f) := ⟨Iso.refl _⟩
  letI : Localization.Lifting (flatKFlatModelPairsQ Y) (flatKFlatModelPairsW Y)
      (flatKFlatModelPairsQ Y ⋙
        ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)))
      ((derivedPullback f).prod (derivedPullback f) ⋙
        Functor.uncurry.obj
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)) := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (flatKFlatModelPairsQ Y) (flatKFlatModelPairsW Y) _ _ _ _
    (flatKFlatModelPairsTensorIso f)

end Descent

end Models

end Stacks.Sheaves.DerivedPullback.OfToposHom

end
