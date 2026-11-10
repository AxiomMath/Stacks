module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.ComparisonWithTheDerivedTensorProduct
public import StacksFrontier.Homology.KFlat.BifunctorComplexLocalization

/-!
# The tensor product of `D(Mod(O))` is the canonical derived tensor product of Tag 06YU

Stacks Tag 0FPT asks for a symmetric monoidal structure on `D(Mod(O))` whose tensor product
*is* the derived tensor product.  `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso`
identifies the tensor product of `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` with the
generic derived bifunctor `CochainComplex.KFlatBifunctor.derivedBifunctor`, but Tag 06YU hands its
consumers the derived tensor product
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`, which is made opaque with
`irreducible_def` (defining equation
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct_def`): no amount of unfolding
relates its bifunctor to `derivedBifunctor`.

This file closes that last gap.  It identifies the bifunctor of an **arbitrary**
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct` with `derivedBifunctor`, using only the two
fields every such structure carries — the K-flat comparison and its naturality — and then
specializes to the canonical one.

## Main definitions

* `Stacks.SheafOfModules.DerivedMonoidal.KFlatComplexes`,
  `Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ`,
  `Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQuasiIso`: K-flatness as a property of
  *complexes*, the functor from the K-flat complexes to `D(Mod(O))`, and the quasi-isomorphisms
  between them — the bifunctor-generic `CochainComplex.KFlatBifunctor.kFlatComplexes`,
  `CochainComplex.KFlatBifunctor.kFlatComplexQ` and
  `CochainComplex.KFlatBifunctor.kFlatComplexQuasiIso` of
  `StacksFrontier.Homology.KFlat.BifunctorComplexLocalization`, read at the tensor product of
  `O`-modules.
* `Stacks.SheafOfModules.DerivedMonoidal.kFlatTensorSource`: the bifunctor on K-flat complexes that
  both sides descend, namely `(K, L) ↦ Q(K ⊗ L)`.
* `Stacks.SheafOfModules.DerivedMonoidal.tensorLifting`,
  `Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorLifting`: the two
  `CategoryTheory.Localization.Lifting₂` data exhibiting each bifunctor as a descent of
  `kFlatTensorSource`.
* `Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso`: the resulting comparison, for
  an arbitrary derived tensor product.
* `Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`: its value at
  `Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`.
* `Stacks.SheafOfModules.DerivedMonoidal.monoidalTensorCanonicalIso`: the composite with
  `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso`, identifying the tensor product
  of `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal` with
  `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.kFlatComplexQ_isLocalization`: `D(Mod(O))` is the
  localization of the K-flat *complexes* of `O`-modules at the quasi-isomorphisms between them.
  This is `CochainComplex.KFlatBifunctor.kFlatComplexQ_isLocalization` with its hypothesis
  discharged, kept here because the consumers of the comparisons below carry no such hypothesis.
* `Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app`: the comparison, on
  the image of a pair of K-flat complexes, is the K-flat comparison of one side followed by the
  inverse of the K-flat comparison of the other.  This is what makes the comparison usable:
  without it the isomorphism is a black box produced by a universal property.

## Implementation notes

The localization is taken at the level of **complexes** rather than of objects of `K(Mod(O))`,
by `CochainComplex.KFlatBifunctor.kFlatComplexQ_isLocalization`.  That is forced by the shape
of the data available: both K-flat comparisons are stated at `DerivedCategory.Q.obj K` for a
complex `K`, so a lifting datum along `kFlatQ` — whose source is the K-flat objects of the
*homotopy* category — would have to be transported across
`DerivedCategory.quotientCompQhIso` twice before either comparison could be used.  Along
`kFlatComplexQ` the two comparisons are the lifting data verbatim.

Note that the two bifunctors are **not** liftings of one bifunctor along one pair of
localization functors: `derivedBifunctor` descends along `kFlatQLeft` in its first variable
and `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.tensor` is not a descent of anything by
construction at all.  Hence the comparison cannot come from the uniqueness of a lift of the chosen
functor, and is instead assembled from the `comparison` field, which is the only handle an
arbitrary derived tensor product offers.

No coherence is checked.  The two one-variable naturality squares needed by
`CategoryTheory.NatIso.ofComponents` come from the merged two-variable naturality with an
identity in the other variable, and the three spellings of the total tensor product in play —
`K ⊗ L`, `HomologicalComplex.mapBifunctorMap` and
`CategoryTheory.Functor.map₂HomologicalComplex` — agree by `rfl`, so every statement below is
written in the monoidal spelling and proved in term mode.  A `rw` or `simp` would not
survive: with `Stacks.SheafOfModules.Tensor.tensorComplex` a semireducible `def`, a goal mixing the
monoidal spelling with the one `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.comparison`
uses is not type-correct at `implicit` transparency, which blocks both.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CochainComplex.KFlatBifunctor

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

/- The monoidal structures on `Mod(O)` and `Comp(Mod(O))` at pinned universes, of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Monoidal/DerivedCategory.lean`, back in scope.  The
sections universe of `SheafOfModules.monoidalCategorySheafTensor` is `max u v` in the two site
universes, which instance synthesis has to solve from the `u` of `Mod R` at every use; a monoidal
structure on `Comp(Mod(O))` synthesized from one whose universes are still unsolved is a structure
the whiskerings below cannot reduce through. -/
attribute [local instance] monoidalCategoryMod symmetricCategoryMod monoidalPreadditiveMod
  monoidalClosedMod hasTensorMod monoidalComplexes

/-! ### Two bookkeeping lemmas -/

private theorem eq_of_comp_id_comp {D : Type*} [Category D] {X Y Z : D} {a : X ⟶ Y}
    {b : Y ⟶ Y} {c : Y ⟶ Z} {d : X ⟶ Z} (h : a ≫ b ≫ c = d) (hb : b = 𝟙 Y) : a ≫ c = d := by
  rw [hb, Category.id_comp] at h
  exact h

private theorem eq_of_id_comp_comp {D : Type*} [Category D] {X Y Z : D} {a : X ⟶ X}
    {b : X ⟶ Y} {c : Y ⟶ Z} {d : X ⟶ Z} (h : a ≫ b ≫ c = d) (ha : a = 𝟙 X) : b ≫ c = d := by
  rw [ha, Category.id_comp] at h
  exact h

/-! ### The K-flat complexes localize to `D(Mod(O))` -/

/-- `D(Mod(O))` is the localization of the K-flat objects of `K(Mod(O))` at the
quasi-isomorphisms.  This is `CochainComplex.KFlatBifunctor.kFlatQ_isLocalization` fed the
supply of K-flat resolutions of Tag 06YS, named here so that it can be a local instance. -/
theorem kFlatQ_isLocalization :
    (kFlatQ (curriedTensor (Mod R))).IsLocalization (kFlatQuasiIso (curriedTensor (Mod R))) :=
  CochainComplex.KFlatBifunctor.kFlatQ_isLocalization _ (exists_kFlat_resolution R)

/-- The mirror of `Stacks.SheafOfModules.DerivedMonoidal.kFlatQ_isLocalization` for the *left*
K-flat objects, which is the localization `CochainComplex.KFlatBifunctor.derivedBifunctor`
descends along in its first variable. -/
theorem kFlatQLeft_isLocalization :
    (kFlatQLeft (curriedTensor (Mod R))).IsLocalization
      (kFlatQuasiIsoLeft (curriedTensor (Mod R))) :=
  CochainComplex.KFlatBifunctor.kFlatQLeft_isLocalization _
    (CochainComplex.KFlatMonoidal.exists_kFlatLeft_quasiIso (Mod R) (exists_kFlat_resolution R))

attribute [local instance] kFlatQ_isLocalization kFlatQLeft_isLocalization

/-- K-flatness as a property of cochain complexes of `O`-modules: the class of the complex in
`K(Mod(O))` is K-flat.  This is `Stacks.SheafOfModules.IsKFlat R`, read off the
bifunctor-generic `CochainComplex.KFlatBifunctor.kFlatComplexes` at the tensor product of
`O`-modules. -/
abbrev KFlatComplexes : ObjectProperty (Complexes R) :=
  CochainComplex.KFlatBifunctor.kFlatComplexes (curriedTensor (Mod R))

/-- The functor from the K-flat complexes of `O`-modules to `D(Mod(O))`. -/
abbrev kFlatComplexQ : (KFlatComplexes R).FullSubcategory ⥤ DerivedModules R :=
  CochainComplex.KFlatBifunctor.kFlatComplexQ (curriedTensor (Mod R))

/-- The quasi-isomorphisms between K-flat complexes of `O`-modules. -/
abbrev kFlatComplexQuasiIso : MorphismProperty (KFlatComplexes R).FullSubcategory :=
  CochainComplex.KFlatBifunctor.kFlatComplexQuasiIso (curriedTensor (Mod R))

/-- **`D(Mod(O))` is the localization of the K-flat complexes of `O`-modules at the
quasi-isomorphisms between them.**  So a bifunctor on K-flat complexes inverting those
quasi-isomorphisms descends to `D(Mod(O))`, and a pair of such descents of one bifunctor are
isomorphic.

This is `CochainComplex.KFlatBifunctor.kFlatComplexQ_isLocalization` with its hypothesis that
`D(Mod(O))` localizes the K-flat *objects* of `K(Mod(O))` discharged by
`Stacks.SheafOfModules.DerivedMonoidal.kFlatQ_isLocalization`.  It is named, and stated
unconditionally, because the consumers of the comparisons below carry no such hypothesis. -/
instance kFlatComplexQ_isLocalization :
    (kFlatComplexQ R).IsLocalization (kFlatComplexQuasiIso R) :=
  inferInstance

/-- The bifunctor on K-flat complexes of `O`-modules that both the derived tensor product of
Tag 06YU and `CochainComplex.KFlatBifunctor.derivedBifunctor` descend: the total tensor
product of complexes, pushed into `D(Mod(O))`. -/
abbrev kFlatTensorSource :
    (KFlatComplexes R).FullSubcategory ⥤ (KFlatComplexes R).FullSubcategory ⥤
      DerivedModules R :=
  (((Functor.whiskeringLeft₂ (DerivedModules R)).obj (KFlatComplexes R).ι).obj
      (KFlatComplexes R).ι).obj
    (curriedTensor (Complexes R) ⋙ (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q)

/-! ### The two descents -/

variable (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct R)

/-- Naturality of the K-flat comparison of a derived tensor product in its first variable
alone, in the monoidal spelling of the total tensor product.  This is the merged naturality
with an identity in the second variable. -/
theorem tensorComparison_naturality_left {K K' L : Complexes R} (f : K ⟶ K')
    (hK : Stacks.SheafOfModules.IsKFlat R K) (hK' : Stacks.SheafOfModules.IsKFlat R K')
    (hL : Stacks.SheafOfModules.IsKFlat R L) :
    (T.tensor.map (DerivedCategory.Q.map f)).app (DerivedCategory.Q.obj L) ≫
        (T.comparison K' L hK' hL).hom =
      (T.comparison K L hK hL).hom ≫ DerivedCategory.Q.map (f ▷ L) :=
  eq_of_comp_id_comp (T.comparison_naturality f (𝟙 L) hK hK' hL hL)
    (by rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id])

/-- Naturality of the K-flat comparison of a derived tensor product in its second variable
alone, the mirror of `Stacks.SheafOfModules.DerivedMonoidal.tensorComparison_naturality_left`. -/
theorem tensorComparison_naturality_right (K : Complexes R) {L L' : Complexes R} (g : L ⟶ L')
    (hK : Stacks.SheafOfModules.IsKFlat R K) (hL : Stacks.SheafOfModules.IsKFlat R L)
    (hL' : Stacks.SheafOfModules.IsKFlat R L') :
    (T.tensor.obj (DerivedCategory.Q.obj K)).map (DerivedCategory.Q.map g) ≫
        (T.comparison K L' hK hL').hom =
      (T.comparison K L hK hL).hom ≫ DerivedCategory.Q.map (K ◁ g) :=
  eq_of_id_comp_comp (T.comparison_naturality (𝟙 K) g hK hK hL hL')
    (by rw [DerivedCategory.Q.map_id, CategoryTheory.Functor.map_id, NatTrans.id_app])

/-- Naturality of `CochainComplex.KFlatBifunctor.comparisonRight` in the arbitrary left
complex, in the monoidal spelling.  No K-flatness is assumed on the left. -/
theorem derivedComparison_naturality_left {K K' L : Complexes R} (f : K ⟶ K')
    (hL : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) L) :
    ((derivedBifunctor (curriedTensor (Mod R))).map (DerivedCategory.Q.map f)).app
          (DerivedCategory.Q.obj L) ≫
        (comparisonRight (curriedTensor (Mod R)) K' L hL).hom =
      (comparisonRight (curriedTensor (Mod R)) K L hL).hom ≫
        DerivedCategory.Q.map (f ▷ L) :=
  comparisonRight_naturality_left (curriedTensor (Mod R)) f L hL

/-- Naturality of `CochainComplex.KFlatBifunctor.comparisonRight` in the K-flat right
complex, in the monoidal spelling. -/
theorem derivedComparison_naturality_right (K : Complexes R) {L L' : Complexes R} (g : L ⟶ L')
    (hL : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) L)
    (hL' : CochainComplex.KFlatBifunctor.KFlat (curriedTensor (Mod R)) L') :
    ((derivedBifunctor (curriedTensor (Mod R))).obj (DerivedCategory.Q.obj K)).map
          (DerivedCategory.Q.map g) ≫
        (comparisonRight (curriedTensor (Mod R)) K L' hL').hom =
      (comparisonRight (curriedTensor (Mod R)) K L hL).hom ≫
        DerivedCategory.Q.map (K ◁ g) :=
  comparisonRight_naturality_right (curriedTensor (Mod R)) K g hL hL'

/-- **The bifunctor of a derived tensor product descends the total tensor product of K-flat
complexes.**  The lifting isomorphism is the `comparison` field and nothing else; its two
naturality squares are the merged naturality field read one variable at a time. -/
@[instance_reducible]
def tensorLifting :
    Localization.Lifting₂ (kFlatComplexQ R) (kFlatComplexQ R)
      (kFlatComplexQuasiIso R) (kFlatComplexQuasiIso R)
      (kFlatTensorSource R) T.tensor where
  iso := NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents (fun Y ↦ T.comparison X.1 Y.1 X.2 Y.2)
      (fun g ↦ tensorComparison_naturality_right R T _ g.hom _ _ _))
    (fun f ↦ by ext Y; exact tensorComparison_naturality_left R T f.hom _ _ _)

/-- **`derivedBifunctor` descends the same bifunctor.**  Its own lifting datum is along
`kFlatQLeft` in the first variable and `kFlatQ` in the second; read along `kFlatComplexQ` in
both it is the one-sided comparison `CochainComplex.KFlatBifunctor.comparisonRight`, whose
naturality in each variable is already proved. -/
@[instance_reducible]
def derivedBifunctorLifting :
    Localization.Lifting₂ (kFlatComplexQ R) (kFlatComplexQ R)
      (kFlatComplexQuasiIso R) (kFlatComplexQuasiIso R)
      (kFlatTensorSource R) (derivedBifunctor (curriedTensor (Mod R))) where
  iso := NatIso.ofComponents
    (fun X ↦ NatIso.ofComponents
      (fun Y ↦ comparisonRight (curriedTensor (Mod R)) X.1 Y.1 Y.2)
      (fun g ↦ derivedComparison_naturality_right R _ g.hom _ _))
    (fun f ↦ by ext Y; exact derivedComparison_naturality_left R f.hom _)

attribute [local instance] tensorLifting derivedBifunctorLifting

/-! ### The comparison -/

/-- **The derived tensor bifunctor of `CochainComplex.KFlatBifunctor` is the bifunctor of any
derived tensor product in the sense of Tag 06YU.**  Both descend the total tensor product of
K-flat complexes along `kFlatComplexQ` in each variable, so the comparison is
`CategoryTheory.Localization.lift₂NatIso` of the identity and no coherence is checked. -/
def derivedBifunctorTensorIso :
    derivedBifunctor (curriedTensor (Mod R)) ≅ T.tensor :=
  Localization.lift₂NatIso (kFlatComplexQ R) (kFlatComplexQ R)
    (kFlatComplexQuasiIso R) (kFlatComplexQuasiIso R)
    (kFlatTensorSource R) (kFlatTensorSource R)
    (derivedBifunctor (curriedTensor (Mod R))) T.tensor (Iso.refl _)

/-- **The comparison, computed on a pair of K-flat complexes**: it is the one-sided K-flat
comparison of `derivedBifunctor` followed by the inverse of the K-flat comparison of `T`.
Both sides of a statement about the derived tensor product are therefore expressible through
either comparison, which is what the comparison is for. -/
theorem derivedBifunctorTensorIso_hom_app_app (K L : Complexes R)
    (hK : Stacks.SheafOfModules.IsKFlat R K) (hL : Stacks.SheafOfModules.IsKFlat R L) :
    ((derivedBifunctorTensorIso R T).hom.app (DerivedCategory.Q.obj K)).app
        (DerivedCategory.Q.obj L) =
      (comparisonRight (curriedTensor (Mod R)) K L hL).hom ≫
        (T.comparison K L hK hL).inv := by
  refine (Localization.lift₂NatTrans_app_app (kFlatComplexQ R) (kFlatComplexQ R)
    (kFlatComplexQuasiIso R) (kFlatComplexQuasiIso R)
    (kFlatTensorSource R) (kFlatTensorSource R)
    (derivedBifunctor (curriedTensor (Mod R))) T.tensor (Iso.refl _).hom
    (⟨K, hK⟩ : (KFlatComplexes R).FullSubcategory)
    (⟨L, hL⟩ : (KFlatComplexes R).FullSubcategory)).trans ?_
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp]
  rfl

/-- **The derived tensor bifunctor of `CochainComplex.KFlatBifunctor` is the *canonical*
derived tensor product of Tag 06YU.**  The canonical derived tensor product is
made opaque with `irreducible_def`; this is the comparison
that makes statements about it available to the monoidal structure of Tag 0FPT. -/
def canonicalTensorIso :
    derivedBifunctor (curriedTensor (Mod R)) ≅
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).tensor :=
  derivedBifunctorTensorIso R (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R)

/-- **The tensor product of the monoidal derived category of Tag 0FPT is the canonical
derived tensor product of Tag 06YU**, as an isomorphism of bifunctors.  This is the
comparison `Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorIso` followed by
`Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso`, and it is the datum from which a
monoidal structure whose tensor product is
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor` *on the nose* is obtained by
re-seating. -/
def monoidalTensorCanonicalIso :
    @curriedTensor (DerivedModules R) _ (derivedMonoidal R) ≅
      Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R :=
  derivedTensorBifunctorIso R ≪≫ canonicalTensorIso R

end Stacks.SheafOfModules.DerivedMonoidal

end
