module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOnKFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackCyclesInput
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.TensorProduct

/-! # Derived pullback and the derived tensor product on a ringed topos

Let `f : (Sh(C), O) ⟶ (Sh(D), O')` be a morphism of ringed topoi. **Stacks 07A4** asserts a
canonical bifunctorial isomorphism

`Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L`

for `K, L ∈ D(O')`. The source proves it by replacing `K` and `L` by K-flat complexes with flat
terms, where both sides are computed by total tensor complexes, and exhibiting the isomorphism
`f^*Tot(K ⊗_{O'} L) ≅ Tot(f^*K ⊗_O f^*L)` whose constituents are the comparisons
`f^*(K^p ⊗_{O'} L^q) ≅ f^*K^p ⊗_O f^*L^q` of **Stacks 03EL**.

Reading the composite at a pair of K-flat complexes with flat terms left to right:

1. `K ⊗^L L` is `Q Tot(K ⊗ L)`, by the K-flat comparison of **Stacks 06YU**;
2. `Lf^*` of that is `Q(f^*Tot(K ⊗ L))`, because `Tot(K ⊗ L)` is again K-flat with flat terms by
   **Stacks 079R** and **Stacks 0G6Q**, and such a complex computes `Lf^*` by **Stacks 06YY**;
3. `f^*Tot(K ⊗ L)` is `Tot(f^*K ⊗ f^*L)`, degreewise by **Stacks 03EL**;
4. `Tot(f^*K ⊗ f^*L)` is `f^*K ⊗^L f^*L`, because `f^*K` and `f^*L` are K-flat by
   **Stacks 0G7E**;
5. `f^*K` and `f^*L` are `Lf^*K` and `Lf^*L`, by the same computation as step 2.

The passage from K-flat representatives to arbitrary objects of `D(O')` is the descent along a
localization: the K-flat complexes with flat terms already localize to `D(O')`, so pairs of them
localize to pairs of objects of `D(O')`, and the value of the composite at a pair of models,
being natural in homotopy classes of maps between models, extends uniquely.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ`: the localization functor from the K-flat
  complexes with flat terms to `D(O')`, and `flatKFlatModelPairsQ` its square.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorModelIso`: the isomorphism of Stacks 07A4
  at a pair of K-flat complexes with flat terms, as the five-step composite above.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorIso`: **Stacks 07A4**, the canonical
  bifunctorial isomorphism `Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L`.

## Main results

* `Stacks.Sheaves.DerivedPullback.flatKFlatModelsQ_isLocalization` and
  `flatKFlatModelPairsQ_isLocalization`: the K-flat complexes with flat terms, and pairs of
  them, localize to `D(O')` and to `D(O') × D(O')`.
* `Stacks.Sheaves.DerivedPullback.derivedPullbackTensorModelIso_naturality`: the value at a pair
  of models is natural in both complexes, which is what makes the descent possible.

## Implementation notes

*The morphism-of-sites hypothesis.* `AlgebraicGeometry.RingedToposSiteHom` asks only that the
underlying functor `f.u` be *continuous*; left exactness of `f^{-1}` is not a field of it, and
the inverse image along a merely continuous functor need not be exact, so such an `f` need not
present a morphism of topoi at all. A morphism of ringed topoi in the source's sense has that
exactness, and `f.u.IsMorphismOfSites Y.J X.J` is exactly what supplies it. So `hmos` is not a
weakening of Stacks 07A4: it is what makes the Lean object a morphism of ringed topoi, which is
what the tag assumes, and it is the hypothesis carried by every statement of this chain —
Stacks 05VD, 0G6R, 0G7E and 06YY. It is additionally what the passage from a site-presented
morphism of ringed topoi to a morphism of ringed sites consumes, which is how the comparison of
Stacks 03EL becomes available to the site-presented pullback at all.

*The left-derived-functor instance.* `Lf^*` cannot be written down without
`(pullbackOnHomotopy f).HasLeftDerivedFunctor`, so it is an instance argument. It is not a
residual hypothesis: it is a `Prop` class, it is discharged for every morphism of ringed topoi
by `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy`,
and by proof irrelevance `derivedPullback f` is the same functor whichever witness is supplied.
The same applies to the two `PullbackPreservesIsFlat` and `PullbackPreservesShortExact` inputs
of Stacks 0G7E and to the `CyclesIsFlat` input: all three are theorems of the tree
(`AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat`,
`AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesShortExact` and
`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat`) and are supplied here rather than
carried.

*The universe narrowing, inherited.* Both ringed topoi are taken at `RingedTopos.{u, u, u}`: the
object, morphism and section universes agree, and the site is small. This is **not** chosen
here. The derived tensor product of Stacks 06YU is available only at those universes, a
narrowing `Stacks.DerivedTensor.RingedSite.exists_derivedTensorProduct` records as coming down
from `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution` and ultimately from
`Stacks.PresheafOfModules.FlatFreeYoneda.isFlat_freeYoneda`, which pins the ring universe to the
site's hom universe; the same pin is carried by Stacks 0G7E and by Stacks 06YY in this tree. The
derived category's own hom universe stays independent.

*Uncurrying.* The isomorphism is stated between the two uncurried bifunctors on
`D(O') × D(O')`, so that naturality in both variables is part of its type rather than two
separate clauses, and so that the descent is a single application of
`CategoryTheory.Localization.liftNatIso` along one localization functor.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [Stacks Project, Tag 079R](https://stacks.math.columbia.edu/tag/079R)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## Two pieces of naturality bookkeeping -/

section Bookkeeping

universe v₀ u₀ v₁ u₁

variable {Z : Type u₀} [Category.{v₀} Z]

/-- Two isomorphisms onto a common target give a naturality square for the induced isomorphism
of their sources. -/
lemma isoOverCommonTarget_naturality {A B D A' B' D' : Z} {u : A ⟶ A'} {v : B ⟶ B'}
    {w : D ⟶ D'} {e : A ≅ D} {e' : A' ≅ D'} {i : B ≅ D} {i' : B' ≅ D'}
    (he : u ≫ e'.hom = e.hom ≫ w) (hi : v ≫ i'.hom = i.hom ≫ w) :
    u ≫ (e' ≪≫ i'.symm).hom = (e ≪≫ i.symm).hom ≫ v := by
  apply (cancel_mono i'.hom).1
  calc
    (u ≫ (e' ≪≫ i'.symm).hom) ≫ i'.hom = u ≫ e'.hom := by
      simp [Iso.trans_hom, Category.assoc]
    _ = e.hom ≫ w := he
    _ = ((e ≪≫ i.symm).hom ≫ v) ≫ i'.hom := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rw [hi]
      simp


/-- Transporting a pointwise isomorphism of two functors along isomorphisms of the objects
preserves naturality. -/
lemma transportedIso_naturality {W : Type u₁} [Category.{v₁} W] (F G : Z ⥤ W)
    {A B A' B' : Z} (eA : A ≅ A') (eB : B ≅ B')
    (α : F.obj A' ≅ G.obj A') (β : F.obj B' ≅ G.obj B')
    (g : A ⟶ B) (g' : A' ⟶ B') (hg : g ≫ eB.hom = eA.hom ≫ g')
    (hg' : F.map g' ≫ β.hom = α.hom ≫ G.map g') :
    F.map g ≫ (F.mapIso eB ≪≫ β ≪≫ (G.mapIso eB).symm).hom =
      (F.mapIso eA ≪≫ α ≪≫ (G.mapIso eA).symm).hom ≫ G.map g := by
  have hgi : eA.inv ≫ g = g' ≫ eB.inv := by
    apply (cancel_mono eB.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hg, Iso.inv_hom_id_assoc]
  dsimp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_inv]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, hg, F.map_comp_assoc, reassoc_of% hg', ← G.map_comp, ← G.map_comp, hgi]

end Bookkeeping

/-! ## The K-flat complexes with flat terms as a localization -/

section Localization

attribute [local instance] HasDerivedCategory.standard

variable (Y : RingedTopos.{u, u, u})
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The localization functor from the K-flat complexes of `O'`-modules with flat terms, as a
full subcategory of the unbounded homotopy category, to the derived category. -/
abbrev flatKFlatModelsQ :
    (IsKFlat (Y := Y)).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (IsKFlat (Y := Y)).ι ⋙ DerivedCategory.Qh

/-- The quasi-isomorphisms between K-flat complexes with flat terms. -/
abbrev flatKFlatModelsW :
    MorphismProperty (IsKFlat (Y := Y)).FullSubcategory :=
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ)).inverseImage (IsKFlat (Y := Y)).ι

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Localizing only the K-flat complexes with flat terms already produces `D(O')`.** Every
complex receives a quasi-isomorphism from such a complex, by Stacks 06YS, so the inclusion of
the class into the homotopy category is a localized equivalence. -/
theorem flatKFlatModelsQ_isLocalization :
    (flatKFlatModelsQ Y).IsLocalization (flatKFlatModelsW Y) := by
  have hres : (LeftDerivedByResolutions.inclusionLocalizerMorphism
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))
      (IsKFlat (Y := Y))).HasLeftResolutions := fun M => by
    obtain ⟨K, hK, s, hs⟩ := hasResolutions_isKFlat (Y := Y) M
    exact ⟨{ X₁ := ⟨K, hK⟩, w := s, hw := hs }⟩
  have := LeftDerivedByResolutions.isLocalizedEquivalence_inclusionLocalizerMorphism
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))
    (IsKFlat (Y := Y))
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization
    (LeftDerivedByResolutions.inclusionLocalizerMorphism _ (IsKFlat (Y := Y)))
    DerivedCategory.Qh

/-- Pairs of K-flat complexes with flat terms, as a localization of pairs of objects of
`D(O')`. -/
abbrev flatKFlatModelPairsQ :
    (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  (flatKFlatModelsQ Y).prod (flatKFlatModelsQ Y)

/-- Pairs of quasi-isomorphisms between K-flat complexes with flat terms. -/
abbrev flatKFlatModelPairsW :
    MorphismProperty ((IsKFlat (Y := Y)).FullSubcategory ×
      (IsKFlat (Y := Y)).FullSubcategory) :=
  (flatKFlatModelsW Y).prod (flatKFlatModelsW Y)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **Pairs of K-flat complexes with flat terms localize to pairs of objects of `D(O')`.** -/
theorem flatKFlatModelPairsQ_isLocalization :
    (flatKFlatModelPairsQ Y).IsLocalization (flatKFlatModelPairsW Y) := by
  have := flatKFlatModelsQ_isLocalization Y
  infer_instance

/-- The localization carries a pair of models to the pair of the objects of `D(O')` they
represent. -/
def flatKFlatModelPairsIso
    (P : (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory) :
    (flatKFlatModelPairsQ Y).obj P ≅
      (DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app P.1.obj.as).prod
    ((DerivedCategory.quotientCompQhIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).app P.2.obj.as)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- The identification of a pair of models with the pair of objects it represents is natural in
the pair of models. -/
lemma flatKFlatModelPairsIso_naturality
    {P R : (IsKFlat (Y := Y)).FullSubcategory × (IsKFlat (Y := Y)).FullSubcategory}
    (g : P ⟶ R) :
    (flatKFlatModelPairsQ Y).map g ≫ (flatKFlatModelPairsIso Y R).hom =
      (flatKFlatModelPairsIso Y P).hom ≫
        ((DerivedCategory.Q.map g.1.hom.out, DerivedCategory.Q.map g.2.hom.out) :
          ((DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
            (DerivedCategory.Q.obj R.1.obj.as, DerivedCategory.Q.obj R.2.obj.as)) := by
  apply Prod.ext
  · have h := DerivedCategory.quotientCompQhIso_hom_naturality g.1.hom.out
    rwa [HomotopyCategory.quotient_map_out] at h
  · have h := DerivedCategory.quotientCompQhIso_hom_naturality g.2.hom.out
    rwa [HomotopyCategory.quotient_map_out] at h

end Localization

/-! ## The comparison at a pair of K-flat complexes with flat terms -/

section Models

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
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)

/-- **Stacks 0G7E with every input discharged**: the degreewise pullback of a K-flat complex of
`O'`-modules with flat terms is a K-flat complex of `O`-modules. -/
theorem kFlat_pullbackComplex' (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i)) :
    CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
      ((pullbackComplex f).obj K) :=
  kFlat_pullbackComplex f hmos (RingedToposSiteHom.pullbackPreservesIsFlat f)
    (RingedToposSiteHom.pullbackPreservesShortExact f) (cyclesIsFlat Y) K hK hflat

variable [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-- **Steps 1 and 2 of the chain**: for K-flat `K` and `L` with flat terms, `Lf^*(K ⊗^L L)` is
the image in `D(O)` of the degreewise pullback of the total tensor complex. -/
def derivedPullbackTensorModelLeft
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (derivedPullback f).obj
        (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O).obj
          (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) :=
  (derivedPullback f).mapIso
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.O).comparison
        K L hK hL) ≪≫
    flatPullbackIso f hmos
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
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O).obj
          ((derivedPullback f).obj (DerivedCategory.Q.obj K))).obj
        ((derivedPullback f).obj (DerivedCategory.Q.obj L)) ≅
      DerivedCategory.Q.obj ((pullbackComplex f).obj (HomologicalComplex.mapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) :=
  (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
      ((flatPullbackIso f hmos K hK hflatK).prod (flatPullbackIso f hmos L hL hflatL)) ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
        ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
        (kFlat_pullbackComplex' f hmos K hK hflatK)
        (kFlat_pullbackComplex' f hmos L hL hflatL) ≪≫
      (DerivedCategory.Q.mapIso (pullbackToposTensorTotalIso f hmos K L)).symm

/-- **The isomorphism of Stacks 07A4 at a pair of K-flat complexes with flat terms**: the two
halves of the five-step chain, which land in the same object of `D(O)`. -/
def derivedPullbackTensorModelIso
    (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) L)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (K.X i))
    (hflatL : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L.X i)) :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  derivedPullbackTensorModelLeft f hmos K L hK hL hflatK hflatL ≪≫
    (derivedPullbackTensorModelRight f hmos K L hK hL hflatK hflatL).symm

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
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive] in
/-- The first half of the chain is natural in the pair of complexes: the K-flat comparison of
Stacks 06YU is, and so is the computation of `Lf^*` on a K-flat complex with flat terms. -/
private lemma derivedPullbackTensorModelLeft_naturality :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullbackTensorModelLeft f hmos K' L' hK' hL' hflatK' hflatL').hom =
      (derivedPullbackTensorModelLeft f hmos K L hK hL hflatK hflatL).hom ≫
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
  exact trans_naturality s1 (flatPullbackIso_naturality f hmos
    (HomologicalComplex.mapBifunctorMap a b
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK hL)
    (Stacks.SheafOfModules.kFlat_tensorComplex Y.O hK' hL')
    (isFlat_tensorComplex_X Y.O K L hflatK hflatL)
    (isFlat_tensorComplex_X Y.O K' L' hflatK' hflatL'))

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- The computation of `Lf^*` on K-flat complexes with flat terms, paired over two factors, is
natural in the pair of complexes. -/
lemma flatPullbackIso_prod_naturality {K K' L L' : CochainComplex
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
    (hflatL' : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (L'.X i)) :
    ((derivedPullback f).prod (derivedPullback f)).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        ((flatPullbackIso f hmos K' hK' hflatK').prod
          (flatPullbackIso f hmos L' hL' hflatL')).hom =
      ((flatPullbackIso f hmos K hK hflatK).prod
          (flatPullbackIso f hmos L hL hflatL)).hom ≫
        ((DerivedCategory.Q.map ((pullbackComplex f).map a),
            DerivedCategory.Q.map ((pullbackComplex f).map b)) :
          ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
              DerivedCategory.Q.obj ((pullbackComplex f).obj L)) : _ × _) ⟶
            (DerivedCategory.Q.obj ((pullbackComplex f).obj K'),
              DerivedCategory.Q.obj ((pullbackComplex f).obj L'))) :=
  Prod.ext (flatPullbackIso_naturality f hmos a hK hK' hflatK hflatK')
    (flatPullbackIso_naturality f hmos b hL hL' hflatL hflatL')

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ))] in
/-- The K-flat comparison of Stacks 06YU is natural on degreewise pullbacks. -/
private lemma comparison_pullbackComplex_naturality :
    (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).map
          ((DerivedCategory.Q.map ((pullbackComplex f).map a),
              DerivedCategory.Q.map ((pullbackComplex f).map b)) :
            ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                DerivedCategory.Q.obj ((pullbackComplex f).obj L)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((pullbackComplex f).obj K'),
                DerivedCategory.Q.obj ((pullbackComplex f).obj L'))) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          ((pullbackComplex f).obj K') ((pullbackComplex f).obj L')
          (kFlat_pullbackComplex' f hmos K' hK' hflatK')
          (kFlat_pullbackComplex' f hmos L' hL' hflatL')).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison
          ((pullbackComplex f).obj K) ((pullbackComplex f).obj L)
          (kFlat_pullbackComplex' f hmos K hK hflatK)
          (kFlat_pullbackComplex' f hmos L hL hflatL)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((pullbackComplex f).map a) ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
  simpa only [Functor.uncurry_obj_map, Category.assoc] using
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparison_naturality
      ((pullbackComplex f).map a) ((pullbackComplex f).map b)
      (kFlat_pullbackComplex' f hmos K hK hflatK)
      (kFlat_pullbackComplex' f hmos K' hK' hflatK')
      (kFlat_pullbackComplex' f hmos L hL hflatL)
      (kFlat_pullbackComplex' f hmos L' hL' hflatL')

omit [(pullbackOnHomotopy f).HasLeftDerivedFunctor
  (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (ComplexShape.up ℤ))] in
/-- The comparison of total tensor complexes of Stacks 03EL is natural, in the direction of its
inverse, after passing to the derived category. -/
lemma Q_map_pullbackToposTensorTotalIso_inv_naturality :
    DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((pullbackComplex f).map a) ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) ≫
        (DerivedCategory.Q.mapIso (pullbackToposTensorTotalIso f hmos K' L')).symm.hom =
      (DerivedCategory.Q.mapIso (pullbackToposTensorTotalIso f hmos K L)).symm.hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))) := by
  have hth : DerivedCategory.Q.map ((pullbackComplex f).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ))) ≫
        (DerivedCategory.Q.mapIso (pullbackToposTensorTotalIso f hmos K' L')).hom =
      (DerivedCategory.Q.mapIso (pullbackToposTensorTotalIso f hmos K L)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap
          ((pullbackComplex f).map a) ((pullbackComplex f).map b)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
    rw [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_hom,
      ← Functor.map_comp, ← Functor.map_comp,
      pullbackToposTensorTotalIso_hom_naturality f hmos a b]
  exact (CommSq.vert_inv ⟨hth⟩).w

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
        (derivedPullbackTensorModelRight f hmos K' L' hK' hL' hflatK' hflatL').hom =
      (derivedPullbackTensorModelRight f hmos K L hK hL hflatK hflatL).hom ≫
        DerivedCategory.Q.map ((pullbackComplex f).map
          (HomologicalComplex.mapBifunctorMap a b
            (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O)
            (ComplexShape.up ℤ))) := by
  dsimp only [derivedPullbackTensorModelRight]
  have he := flatPullbackIso_prod_naturality f hmos a b hK hK' hL hL' hflatK hflatK' hflatL hflatL'
  have h1 : ((derivedPullback f).prod (derivedPullback f) ⋙
          Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
          ((flatPullbackIso f hmos K' hK' hflatK').prod
            (flatPullbackIso f hmos L' hL' hflatL'))).hom =
      ((Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
          ((flatPullbackIso f hmos K hK hflatK).prod
            (flatPullbackIso f hmos L hL hflatL))).hom ≫
        (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).map
          ((DerivedCategory.Q.map ((pullbackComplex f).map a),
              DerivedCategory.Q.map ((pullbackComplex f).map b)) :
            ((DerivedCategory.Q.obj ((pullbackComplex f).obj K),
                DerivedCategory.Q.obj ((pullbackComplex f).obj L)) : _ × _) ⟶
              (DerivedCategory.Q.obj ((pullbackComplex f).obj K'),
                DerivedCategory.Q.obj ((pullbackComplex f).obj L'))) := by
    rw [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_hom,
      Functor.comp_map, ← Functor.map_comp, he, Functor.map_comp]
  exact trans_naturality h1 (trans_naturality
    (comparison_pullbackComplex_naturality f hmos a b hK hK' hL hL' hflatK hflatK' hflatL hflatL')
    (Q_map_pullbackToposTensorTotalIso_inv_naturality f hmos a b))

/-- **The value of the comparison at a pair of K-flat complexes with flat terms is natural in
both complexes.** This is what makes the descent to arbitrary objects of `D(O')` possible. -/
lemma derivedPullbackTensorModelIso_naturality :
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.O) ⋙
          derivedPullback f).map
        ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
          ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
            (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) ≫
        (derivedPullbackTensorModelIso f hmos K' L' hK' hL' hflatK' hflatL').hom =
      (derivedPullbackTensorModelIso f hmos K L hK hL hflatK hflatL).hom ≫
        ((derivedPullback f).prod (derivedPullback f) ⋙
            Functor.uncurry.obj
              (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)).map
          ((DerivedCategory.Q.map a, DerivedCategory.Q.map b) :
            ((DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) : _ × _) ⟶
              (DerivedCategory.Q.obj K', DerivedCategory.Q.obj L')) := by
  dsimp only [derivedPullbackTensorModelIso]
  exact isoOverCommonTarget_naturality
    (derivedPullbackTensorModelLeft_naturality f hmos a b hK hK' hL hL'
      hflatK hflatK' hflatL hflatL')
    (derivedPullbackTensorModelRight_naturality f hmos a b hK hK' hL hL'
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
        derivedPullbackTensorModelIso f hmos P.1.obj.as P.2.obj.as
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
      (derivedPullbackTensorModelIso f hmos P.1.obj.as P.2.obj.as
        P.1.property.1 P.2.property.1 P.1.property.2 P.2.property.2)
      (derivedPullbackTensorModelIso f hmos R.1.obj.as R.2.obj.as
        R.1.property.1 R.2.property.1 R.1.property.2 R.2.property.2)
      ((flatKFlatModelPairsQ Y).map g)
      ((DerivedCategory.Q.map g.1.hom.out, DerivedCategory.Q.map g.2.hom.out) :
        ((DerivedCategory.Q.obj P.1.obj.as, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
          (DerivedCategory.Q.obj R.1.obj.as, DerivedCategory.Q.obj R.2.obj.as))
      (flatKFlatModelPairsIso_naturality Y g)
      (derivedPullbackTensorModelIso_naturality f hmos g.1.hom.out g.2.hom.out
        P.1.property.1 R.1.property.1 P.2.property.1 R.2.property.1
        P.1.property.2 R.1.property.2 P.2.property.2 R.2.property.2))

/-- **Stacks 07A4.** The canonical bifunctorial isomorphism

`Lf^*(K ⊗^L_{O'} L) ≅ Lf^*K ⊗^L_O Lf^*L`

for a morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(D), O')`, stated between the two uncurried
bifunctors on `D(O') × D(O')`, so that naturality in both variables is part of its type.

Its value on a pair of K-flat complexes with flat terms is the five-step composite of the source
(`derivedPullbackTensorModelIso`), and the passage to arbitrary objects of `D(O')` is the
descent of that value along the localization of pairs of models. -/
@[stacks 07A4 "the canonical bifunctorial isomorphism"]
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
    (flatKFlatModelPairsTensorIso f hmos)

end Descent

end Models

end Stacks.Sheaves.DerivedPullback

end
