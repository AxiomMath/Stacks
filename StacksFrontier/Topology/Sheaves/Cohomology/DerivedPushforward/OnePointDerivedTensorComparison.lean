module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OnePointKFlat
public import Mathlib.CategoryTheory.Localization.Prod
public import StacksFrontier.CategoryTheory.CommutingSquares

/-!
# The one-point identification carries the derived tensor product to the derived tensor product

Let `R` be a commutative ring, let `({*}, R)` be the one-point ringed space and write
`A = Γ({*}, 𝒪)`.  The one-point identification `E : Mod(A) ≌ Mod(𝒪_{({*}, R)})` carries the
tensor product of modules to the tensor product of sheaves of modules
(`Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparisonIso`), and carries K-flat
complexes to K-flat complexes
(`Stacks.Cohomology.DerivedSectionsOnAPoint.kFlat_onePointSections`).  This file descends the
first along the K-flat localizations to an isomorphism of bifunctors on derived categories

`E(x ⊗^𝐋_A y) ≅ E x ⊗^𝐋_{𝒪_{({*}, R)}} E y`,

which is the one datum of `Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison` that
the repository did not construct, in place of the zero morphism of bifunctors.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedTensorIso` — **the comparison**,
  `E(x ⊗^𝐋_A y) ≅ E x ⊗^𝐋_{𝒪} E y`, bifunctorial in `x, y ∈ D(A)`.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointTensorComparison` — its underlying
  morphism of bifunctors, which is what `OnePointComparison.tensorComparison` asks for.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointComparisonWithTensor` — **a one-point
  comparison on `({*}, R)` whose tensor comparison is that one**, and not the zero morphism.

## Main results

* `Stacks.Cohomology.DerivedSectionsOnAPoint.isIso_onePointTensorComparison` — the comparison
  is invertible, so in particular it is not the zero morphism of bifunctors on a ringed space
  carrying cohomology.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointComparisonWithTensor_tensorComparison` —
  the tensor comparison of `onePointComparisonWithTensor` is `onePointTensorComparison`.

## Implementation notes

*The construction is the one of Stacks 079U, for an equivalence in place of a pullback.*  It
follows `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison` step
for step: both sides are computed on a pair of K-flat representatives by the ordinary total
tensor complex, there the comparison is the degreewise one of `onePointTensorComparisonIso`
assembled on total complexes, and the product of two copies of the K-flat localization of
Stacks 06Y4 descends the result to the whole of `D(A) × D(A)`.

*Where the two sides differ from the pullback case.*  On the sheaf side the canonical map to the
ordinary total tensor complex is a morphism of bifunctors on *all* complexes, namely the
`toTensor` field of Stacks 06YU, so the right-hand comparison is a natural transformation and
its naturality is free; that is
`Stacks.Cohomology.DerivedPullbackTensor.derivedToTensorNatTrans`, reused here at the one-point
ringed space.  On the module side `CochainComplex.DerivedTensor.DerivedTensorProduct` of Tag
064M records no such map — only the comparison on a pair of K-flat complexes, with its
naturality — so the left-hand comparison is built at a K-flat pair and its naturality is
`CochainComplex.DerivedTensor.DerivedTensorProduct.comparison_naturality` followed by the
naturality of `CategoryTheory.Functor.mapDerivedCategoryFactors`.

*Which localization.*  Only the *module*-side localization is used, the source of the
transformation being `D(A) × D(A)`: it is the instance
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` at the K-flat
resolutions of Stacks 06Y4,
`CochainComplex.DerivedTensor.OneSided.moduleKFlatLocalizer_hasLeftResolutions`, in each variable,
and `CategoryTheory.Functor.IsLocalization.prod` for the pair.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
* [Stacks Project, Tag 06Y4](https://stacks.math.columbia.edu/tag/06Y4)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth
open Stacks.DerivedTensor.RingedSite
open CochainComplex.KFlatBifunctor
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

attribute [local instance 10000] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-! ### The two bifunctors to be compared -/

/-- The one-point identification on derived categories, `D(A) ⥤ D(𝒪_{({*}, R)})`. -/
abbrev onePointDerived := (onePointSheafFunctor R).mapDerivedCategory

/-- The one-point identification on cochain complexes. -/
abbrev onePointComplexFunctor :=
  (onePointSheafFunctor R).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The bifunctor `(x, y) ↦ E(x ⊗^𝐋_A y)` on `D(A) × D(A)`. -/
abbrev sectionsOfDerivedTensor :
    DerivedCategory (onePointModuleCat R) × DerivedCategory (onePointModuleCat R) ⥤
      DerivedCategory (onePointSheafCat R) :=
  Functor.uncurry.obj (tensorBase (onePointRingedSpace R)) ⋙ onePointDerived R

/-- The bifunctor `(x, y) ↦ E x ⊗^𝐋_{𝒪} E y` on `D(A) × D(A)`. -/
abbrev derivedTensorOfSections :
    DerivedCategory (onePointModuleCat R) × DerivedCategory (onePointModuleCat R) ⥤
      DerivedCategory (onePointSheafCat R) :=
  (onePointDerived R).prod (onePointDerived R) ⋙
    Functor.uncurry.obj (derivedTensorProductFunctor (onePointRingedSpace R).sheaf)

/-- The bifunctor `(K, L) ↦ Q(E(Tot(K ⊗_A L)))` on pairs of cochain complexes: the ordinary
total tensor complex, carried over by the one-point identification.  Both sides of the
comparison map to it on K-flat representatives. -/
abbrev modelTarget :
    CochainComplex (onePointModuleCat R) ℤ × CochainComplex (onePointModuleCat R) ℤ ⥤
      DerivedCategory (onePointSheafCat R) :=
  totalComplexPair (MonoidalCategory.curriedTensor (onePointModuleCat R)) ⋙
    onePointComplexFunctor R ⋙ DerivedCategory.Q

/-! ### The comparison of `E x ⊗^𝐋 E y` with the ordinary total tensor complex -/

/-- **The right-hand comparison**, a morphism of bifunctors on pairs of cochain complexes of
`A`-modules

`E(QK) ⊗^𝐋_{𝒪} E(QL) ⟶ Q(E(Tot(K ⊗_A L)))`:

the identification of `E ∘ Q` with `Q ∘ E` in both variables, the canonical map of Stacks 06YU
to the ordinary total tensor complex of sheaves of modules, and the comparison of total
complexes of `onePointTensorComplexIso`. -/
def rightComparison :
    DerivedCategory.Q.prod DerivedCategory.Q ⋙ derivedTensorOfSections R ⟶ modelTarget R :=
  Functor.whiskerRight
      (((onePointSheafFunctor R).mapDerivedCategoryFactors.hom).prod
        ((onePointSheafFunctor R).mapDerivedCategoryFactors.hom))
      (Functor.uncurry.obj (derivedTensorProductFunctor (onePointRingedSpace R).sheaf)) ≫
    Functor.whiskerLeft ((onePointComplexFunctor R).prod (onePointComplexFunctor R))
        (derivedToTensorNatTrans (onePointRingedSpace R)) ≫
      Functor.whiskerRight (onePointTensorComplexIso R).inv DerivedCategory.Q

/-- **On a pair of K-flat complexes the right-hand comparison is invertible.**  The two
identifications of `E ∘ Q` with `Q ∘ E` are components of isomorphisms, the images of `K` and
`L` are K-flat by `kFlat_onePointSections`, so the canonical map of Stacks 06YU at them is the
K-flat comparison, and the comparison of total complexes is an isomorphism. -/
theorem isIso_rightComparison_app (K L : CochainComplex (onePointModuleCat R) ℤ)
    (hK : CochainComplex.KFlatBifunctor.KFlat
      (MonoidalCategory.curriedTensor (onePointModuleCat R)) K)
    (hL : CochainComplex.KFlatBifunctor.KFlat
      (MonoidalCategory.curriedTensor (onePointModuleCat R)) L) :
    IsIso ((rightComparison R).app (K, L)) := by
  have hKx := kFlat_onePointSections R K hK
  have hLx := kFlat_onePointSections R L hL
  have hpair : IsIso
      ((onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app K ×ₘ
        (onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app L) := by
    rw [isIso_prod_iff]
    exact ⟨inferInstance, inferInstance⟩
  have hcx : IsIso ((onePointTensorComplexIso R).inv.app (K, L)) :=
    inferInstanceAs (IsIso ((onePointTensorComplexIso R).symm.app (K, L)).hom)
  dsimp only [rightComparison, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, derivedToTensorNatTrans, NatTrans.prod, Functor.prod_obj]
  rw [(canonicalDerivedTensorProduct (onePointRingedSpace R).sheaf).toTensor_eq_comparison
    _ _ hKx hLx]
  exact IsIso.comp_isIso' (@Functor.map_isIso _ _ _ _ _ _ _ _ hpair)
    (IsIso.comp_isIso' (Iso.isIso_hom _) (@Functor.map_isIso _ _ _ _ _ _ _ _ hcx))

/-- The model target on a morphism of the product category.  The total complex of a bifunctor
splits a morphism of a product into its two one-sided parts, and
`Stacks.Cohomology.DerivedPullbackTensor.totalComplexPair_map` recombines them into the tensor
product of the two morphisms; the identity is not `rfl`. -/
theorem modelTarget_map {K K' L L' : CochainComplex (onePointModuleCat R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L') :
    (modelTarget R).map (a ×ₘ b) =
      DerivedCategory.Q.map
        ((onePointComplexFunctor R).map (HomologicalComplex.tensorHom a b)) :=
  congrArg (fun m => DerivedCategory.Q.map ((onePointComplexFunctor R).map m))
    (totalComplexPair_map (MonoidalCategory.curriedTensor (onePointModuleCat R)) a b)

/-! ### The comparison of `E(x ⊗^𝐋 y)` with the ordinary total tensor complex -/

/-- **The left-hand comparison on a pair of K-flat complexes**,

`E(QK ⊗^𝐋_A QL) ≅ Q(E(Tot(K ⊗_A L)))`:

the K-flat comparison of Tag 064M, carried over by `E`, followed by the identification of
`E ∘ Q` with `Q ∘ E`.  Unlike the right-hand comparison this is not available on all pairs:
`CochainComplex.DerivedTensor.DerivedTensorProduct` records no canonical map to the ordinary
total tensor complex. -/
def leftComparisonIso (K L : CochainComplex (onePointModuleCat R) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) (hL : CochainComplex.KFlat.{u, u} L) :
    (DerivedCategory.Q.prod DerivedCategory.Q ⋙ sectionsOfDerivedTensor R).obj (K, L) ≅
      (modelTarget R).obj (K, L) :=
  (onePointDerived R).mapIso
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        ↥(baseRing (onePointRingedSpace R))).comparison K L hK hL) ≪≫
    (onePointSheafFunctor R).mapDerivedCategoryFactors.app
      (MonoidalCategory.tensorObj K L)

/-- The left-hand comparison, written out as a composite of two morphisms.  The naturality
statement is proved at this spelling: a goal mentioning `CategoryTheory.Iso.trans` is not type
correct at `implicit` transparency here, the two spellings of the structure sheaf of the
one-point ringed space crossing inside it, so no `dsimp` may be applied to it. -/
theorem leftComparisonIso_hom (K L : CochainComplex (onePointModuleCat R) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) (hL : CochainComplex.KFlat.{u, u} L) :
    (leftComparisonIso R K L hK hL).hom =
      (onePointDerived R).map
          ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
            ↥(baseRing (onePointRingedSpace R))).comparison K L hK hL).hom ≫
        (onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app
          (MonoidalCategory.tensorObj K L) :=
  rfl

/-- The left-hand comparison `leftComparisonIso` is natural in cochain maps between K-flat
complexes. -/
theorem leftComparison_naturality {K K' L L' : CochainComplex (onePointModuleCat R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (hK : CochainComplex.KFlat.{u, u} K) (hK' : CochainComplex.KFlat.{u, u} K')
    (hL : CochainComplex.KFlat.{u, u} L) (hL' : CochainComplex.KFlat.{u, u} L') :
    (DerivedCategory.Q.prod DerivedCategory.Q ⋙ sectionsOfDerivedTensor R).map (a ×ₘ b) ≫
        (leftComparisonIso R K' L' hK' hL').hom =
      (leftComparisonIso R K L hK hL).hom ≫
        DerivedCategory.Q.map
          ((onePointComplexFunctor R).map (HomologicalComplex.tensorHom a b)) :=
  CategoryTheory.map_comp_naturality (onePointDerived R)
    ((DerivedCategory.Q.prod DerivedCategory.Q ⋙
      Functor.uncurry.obj (tensorBase (onePointRingedSpace R))).map (a ×ₘ b))
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
      ↥(baseRing (onePointRingedSpace R))).comparison K' L' hK' hL').hom
    ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
      ↥(baseRing (onePointRingedSpace R))).comparison K L hK hL).hom
    (DerivedCategory.Q.map (HomologicalComplex.tensorHom a b))
    ((onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app
      (MonoidalCategory.tensorObj K' L'))
    ((onePointSheafFunctor R).mapDerivedCategoryFactors.hom.app
      (MonoidalCategory.tensorObj K L))
    (DerivedCategory.Q.map
      ((onePointComplexFunctor R).map (HomologicalComplex.tensorHom a b)))
    ((Category.assoc _ _ _).trans
      ((CochainComplex.DerivedTensor.canonicalDerivedTensorProduct
        ↥(baseRing (onePointRingedSpace R))).comparison_naturality a b hK hK' hL hL'))
    ((onePointSheafFunctor R).mapDerivedCategoryFactors_hom_naturality
      (HomologicalComplex.tensorHom a b))

/-- **The left-hand comparison is natural**, with the target read as the model bifunctor.  This
is `leftComparison_naturality` after `modelTarget_map`; it is a separate declaration because the
rewrite is the one expensive unification of the file. -/
theorem leftComparison_naturality_modelTarget
    {K K' L L' : CochainComplex (onePointModuleCat R) ℤ} (a : K ⟶ K') (b : L ⟶ L')
    (hK : CochainComplex.KFlat.{u, u} K) (hK' : CochainComplex.KFlat.{u, u} K')
    (hL : CochainComplex.KFlat.{u, u} L) (hL' : CochainComplex.KFlat.{u, u} L') :
    (DerivedCategory.Q.prod DerivedCategory.Q ⋙ sectionsOfDerivedTensor R).map (a ×ₘ b) ≫
        (leftComparisonIso R K' L' hK' hL').hom =
      (leftComparisonIso R K L hK hL).hom ≫ (modelTarget R).map (a ×ₘ b) := by
  rw [modelTarget_map R a b]
  exact leftComparison_naturality R a b hK hK' hL hL'

/-! ### The comparison on K-flat representatives -/

/-- **The comparison on a pair of K-flat representatives**: both comparisons into
`Q(E(Tot(K ⊗_A L)))` are invertible there, so they compose to
`E(QK ⊗^𝐋_A QL) ≅ E(QK) ⊗^𝐋_{𝒪} E(QL)`. -/
def modelComparison (K L : CochainComplex (onePointModuleCat R) ℤ)
    (hK : CochainComplex.KFlat.{u, u} K) (hL : CochainComplex.KFlat.{u, u} L) :
    (sectionsOfDerivedTensor R).obj (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) ≅
      (derivedTensorOfSections R).obj
        (DerivedCategory.Q.obj K, DerivedCategory.Q.obj L) :=
  have := isIso_rightComparison_app R K L hK hL
  leftComparisonIso R K L hK hL ≪≫ (asIso ((rightComparison R).app (K, L))).symm

/-- The comparison on K-flat representatives is natural in cochain maps between them. -/
theorem modelComparison_naturality {K K' L L' : CochainComplex (onePointModuleCat R) ℤ}
    (a : K ⟶ K') (b : L ⟶ L')
    (hK : CochainComplex.KFlat.{u, u} K) (hK' : CochainComplex.KFlat.{u, u} K')
    (hL : CochainComplex.KFlat.{u, u} L) (hL' : CochainComplex.KFlat.{u, u} L') :
    (sectionsOfDerivedTensor R).map (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (modelComparison R K' L' hK' hL').hom =
      (modelComparison R K L hK hL).hom ≫
        (derivedTensorOfSections R).map
          (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) := by
  have h₁ := isIso_rightComparison_app R K' L' hK' hL'
  have h₂ := isIso_rightComparison_app R K L hK hL
  have hl := leftComparison_naturality_modelTarget R a b hK hK' hL hL'
  have hr : (derivedTensorOfSections R).map
        (DerivedCategory.Q.map a ×ₘ DerivedCategory.Q.map b) ≫
        (rightComparison R).app (K', L') =
      (rightComparison R).app (K, L) ≫ (modelTarget R).map (a ×ₘ b) :=
    (rightComparison R).naturality (a ×ₘ b)
  apply (cancel_mono ((rightComparison R).app (K', L'))).1
  dsimp only [modelComparison, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hr, IsIso.inv_hom_id_assoc]
  exact hl

/-! ### Descent along the K-flat localization -/

/-- The K-flat objects of `K(Mod A)`, viewed in `D(A)`. -/
abbrev kFlatQModules := kFlatQ (MonoidalCategory.curriedTensor (onePointModuleCat R))

/-- Pairs of K-flat objects of `K(Mod A)`, viewed in `D(A) × D(A)`. -/
abbrev kFlatQModulesPair := (kFlatQModules R).prod (kFlatQModules R)

/-- The quasi-isomorphisms between pairs of K-flat objects. -/
abbrev kFlatQuasiIsoModulesPair :=
  (kFlatQuasiIso (MonoidalCategory.curriedTensor (onePointModuleCat R))).prod
    (kFlatQuasiIso (MonoidalCategory.curriedTensor (onePointModuleCat R)))

/-- **`D(A) × D(A)` is the localization of the pairs of K-flat objects at the
quasi-isomorphisms.**  A localization of a product is the product of the localizations, and
each factor is the instance
`CochainComplex.KFlatBifunctor.kFlatQ_isLocalization_of_hasLeftResolutions` at the K-flat
resolutions of Stacks 06Y4,
`CochainComplex.DerivedTensor.OneSided.moduleKFlatLocalizer_hasLeftResolutions`. -/
theorem kFlatQModulesPair_isLocalization :
    (Stacks.Cohomology.DerivedSectionsOnAPoint.kFlatQModulesPair R).IsLocalization
      (Stacks.Cohomology.DerivedSectionsOnAPoint.kFlatQuasiIsoModulesPair R) := by
  have : (kFlatQuasiIso (MonoidalCategory.curriedTensor
      (onePointModuleCat R))).ContainsIdentities := by infer_instance
  exact Functor.IsLocalization.prod (kFlatQModules R) _ (kFlatQModules R) _

/-- The image in `D(A) × D(A)` of a pair of K-flat objects of the homotopy category is the
image of the underlying pair of complexes: the `Q` versus `Qh ∘ quotient` bridge, in both
variables. -/
def kFlatQModulesPairIso
    (M : (kFlatObjects (MonoidalCategory.curriedTensor (onePointModuleCat R))).FullSubcategory ×
      (kFlatObjects (MonoidalCategory.curriedTensor (onePointModuleCat R))).FullSubcategory) :
    (kFlatQModulesPair R).obj M ≅
      (DerivedCategory.Q.obj M.1.obj.as, DerivedCategory.Q.obj M.2.obj.as) :=
  ((DerivedCategory.quotientCompQhIso _).app M.1.obj.as).prod
    ((DerivedCategory.quotientCompQhIso _).app M.2.obj.as)

/-- The bridge is natural: a homotopy class between K-flat objects is the class of a cochain
map, and the bridge is natural in cochain maps. -/
theorem kFlatQModulesPairIso_naturality
    {M N : (kFlatObjects (MonoidalCategory.curriedTensor
        (onePointModuleCat R))).FullSubcategory ×
      (kFlatObjects (MonoidalCategory.curriedTensor
        (onePointModuleCat R))).FullSubcategory} (g : M ⟶ N) :
    (kFlatQModulesPair R).map g ≫ (kFlatQModulesPairIso R N).hom =
      (kFlatQModulesPairIso R M).hom ≫
        (DerivedCategory.Q.map g.1.hom.out ×ₘ DerivedCategory.Q.map g.2.hom.out) := by
  have key : ∀ {X Y : (kFlatObjects (MonoidalCategory.curriedTensor
      (onePointModuleCat R))).FullSubcategory} (f : X ⟶ Y),
      DerivedCategory.Qh.map f.hom ≫ (DerivedCategory.quotientCompQhIso _).hom.app Y.obj.as =
        (DerivedCategory.quotientCompQhIso _).hom.app X.obj.as ≫
          DerivedCategory.Q.map f.hom.out := fun {X Y} f => by
    have h := DerivedCategory.quotientCompQhIso_hom_naturality
      (C := onePointModuleCat R) f.hom.out
    rwa [HomotopyCategory.quotient_map_out] at h
  exact Prod.ext (key g.1) (key g.2)

/-- Conjugating an isomorphism of values by isomorphisms of the objects preserves a naturality
square.  This carries the comparison from the chosen cochain representatives of a pair of
K-flat objects to the images of those objects in the derived category. -/
private lemma naturality_transport {C E : Type*} [Category C] [Category E] (F G : C ⥤ E)
    {Z₁ Z₂ Z₁' Z₂' : C} (e₁ : Z₁ ≅ Z₁') (e₂ : Z₂ ≅ Z₂')
    (x : F.obj Z₁' ≅ G.obj Z₁') (y : F.obj Z₂' ≅ G.obj Z₂')
    (u : Z₁ ⟶ Z₂) (v : Z₁' ⟶ Z₂') (hu : u ≫ e₂.hom = e₁.hom ≫ v)
    (hv : F.map v ≫ y.hom = x.hom ≫ G.map v) :
    F.map u ≫ (F.mapIso e₂ ≪≫ y ≪≫ (G.mapIso e₂).symm).hom =
      (F.mapIso e₁ ≪≫ x ≪≫ (G.mapIso e₁).symm).hom ≫ G.map u := by
  have hui : e₁.inv ≫ u = v ≫ e₂.inv := by
    apply (cancel_mono e₂.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hu, Iso.inv_hom_id_assoc]
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.mapIso_inv]
  simp only [Category.assoc]
  rw [← F.map_comp_assoc, hu, F.map_comp_assoc, reassoc_of% hv, ← G.map_comp, ← G.map_comp, hui]

/-- **The comparison on K-flat representatives, as an isomorphism of functors** on pairs of
K-flat objects of `K(Mod A)`.  Its value at a pair is `modelComparison`, transported along the
`Q` versus `Qh ∘ quotient` bridge, and its naturality in homotopy classes is
`modelComparison_naturality` at any cochain representatives of those classes. -/
def modelsComparison :
    kFlatQModulesPair R ⋙ sectionsOfDerivedTensor R ≅
      kFlatQModulesPair R ⋙ derivedTensorOfSections R :=
  NatIso.ofComponents
    (fun M => (sectionsOfDerivedTensor R).mapIso (kFlatQModulesPairIso R M) ≪≫
      modelComparison R M.1.obj.as M.2.obj.as M.1.property M.2.property ≪≫
        ((derivedTensorOfSections R).mapIso (kFlatQModulesPairIso R M)).symm)
    (fun {M N} g => by
      refine naturality_transport _ _ (kFlatQModulesPairIso R M) (kFlatQModulesPairIso R N)
        (modelComparison R M.1.obj.as M.2.obj.as M.1.property M.2.property)
        (modelComparison R N.1.obj.as N.2.obj.as N.1.property N.2.property)
        ((kFlatQModulesPair R).map g) _ (kFlatQModulesPairIso_naturality R g) ?_
      exact modelComparison_naturality R g.1.hom.out g.2.hom.out
        M.1.property N.1.property M.2.property N.2.property)

attribute [local instance] kFlatQModulesPair_isLocalization

/-- **The one-point identification carries the derived tensor product of `A`-modules to the
derived tensor product of sheaves of modules.**

`E(x ⊗^𝐋_A y) ≅ E x ⊗^𝐋_{𝒪_{({*}, R)}} E y`,

bifunctorial in `x, y ∈ D(A)`.  On K-flat representatives both sides are computed by the
ordinary total tensor complex — the K-flat comparisons of Tags 064M and 06YU, and the stability
of K-flatness under `E` — and there the comparison is the degreewise isomorphism
`E(M ⊗_A N) ≅ E M ⊗_{𝒪} E N` assembled on total complexes.  Since `D(A)` is the localization of
the K-flat objects of the homotopy category at the quasi-isomorphisms, the product of two
copies of that localization descends the comparison to the whole of `D(A) × D(A)`. -/
def onePointDerivedTensorIso : sectionsOfDerivedTensor R ≅ derivedTensorOfSections R :=
  Localization.liftNatIso (kFlatQModulesPair R) (kFlatQuasiIsoModulesPair R) _ _ _ _
    (modelsComparison R)

/-- **The one datum of `OnePointComparison` on the one-point ringed space**: the morphism of
bifunctors `E(x ⊗^𝐋_A y) ⟶ E x ⊗^𝐋_{𝒪} E y` underlying `onePointDerivedTensorIso`. -/
def onePointTensorComparison :
    Functor.uncurry.obj (tensorBase (onePointRingedSpace R)) ⋙
        (onePointSectionsEquivalence R).functor.mapDerivedCategory ⟶
      ((onePointSectionsEquivalence R).functor.mapDerivedCategory).prod
          ((onePointSectionsEquivalence R).functor.mapDerivedCategory) ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor (onePointRingedSpace R).sheaf) :=
  (onePointDerivedTensorIso R).hom

/-- The comparison is invertible: it is the morphism underlying an isomorphism of
bifunctors. -/
instance isIso_onePointTensorComparison : IsIso (onePointTensorComparison R) :=
  inferInstanceAs (IsIso (onePointDerivedTensorIso R).hom)

/-- **The comparison is not the zero morphism of bifunctors**, for a nontrivial ring.  Were it
zero, the zero morphism would be invertible at every pair, so `E(x ⊗^𝐋_A A[0])` — that is `E x`,
by the right unitor of Tag 064M — would vanish for every `x`; the adjunction `E ⊣ RΓ({*}, -)`
would then make `RΓ({*}, U)` vanish for every `U`, which
`Stacks.Cohomology.DerivedSectionsOnAPoint.not_forall_isZero_baseSections` refutes. -/
theorem isZero_of_onePointTensorComparison_eq_zero
    (hzero : onePointTensorComparison R = 0)
    (x : DerivedCategory (onePointModuleCat R)) :
    IsZero ((onePointDerived R).obj x) := by
  have happ : (onePointTensorComparison R).app
      (x, (DerivedCategory.singleFunctor (onePointModuleCat R) 0).obj
        (ModuleCat.of ↥(baseRing (onePointRingedSpace R))
          ↥(baseRing (onePointRingedSpace R)))) = 0 := by
    rw [hzero]
    exact NatTrans.app_zero _
  have hiso : IsIso ((onePointTensorComparison R).app
      (x, (DerivedCategory.singleFunctor (onePointModuleCat R) 0).obj
        (ModuleCat.of ↥(baseRing (onePointRingedSpace R))
          ↥(baseRing (onePointRingedSpace R))))) := inferInstance
  rw [happ] at hiso
  have hzsrc : IsZero ((sectionsOfDerivedTensor R).obj
      (x, (DerivedCategory.singleFunctor (onePointModuleCat R) 0).obj
        (ModuleCat.of ↥(baseRing (onePointRingedSpace R))
          ↥(baseRing (onePointRingedSpace R))))) := by
    rw [IsZero.iff_id_eq_zero]
    have h := @IsIso.hom_inv_id _ _ _ _ _ hiso
    rw [zero_comp] at h
    exact h.symm
  exact hzsrc.of_iso ((onePointDerived R).mapIso
    (CochainComplex.DerivedTensor.derivedTensorProductRightUnitorIso x).symm)

/-- **The comparison is not the zero morphism of bifunctors**, for a nontrivial ring.  Were it
zero, `E x` would vanish for every `x` by
`isZero_of_onePointTensorComparison_eq_zero`, and the adjunction `E ⊣ RΓ({*}, -)` would then make
`RΓ({*}, U)` vanish for every `U`, which
`Stacks.Cohomology.DerivedSectionsOnAPoint.not_forall_isZero_baseSections` refutes: the zero
morphism is not a comparison of the two derived tensor products on a one-point ringed space
carrying cohomology. -/
theorem onePointTensorComparison_ne_zero [Nontrivial R] :
    onePointTensorComparison R ≠ 0 := by
  intro hzero
  refine not_forall_isZero_baseSections R fun U => ?_
  have hzEx := isZero_of_onePointTensorComparison_eq_zero R hzero
    ((baseSections (onePointRingedSpace R)).obj U)
  rw [IsZero.iff_id_eq_zero]
  exact ((onePointDerivedAdjunction R).homEquiv
      ((baseSections (onePointRingedSpace R)).obj U) U).symm.injective (hzEx.eq_of_src _ _)

/-! ### A one-point comparison with a genuine tensor comparison -/

/-- **A one-point comparison on `({*}, R)` whose tensor comparison is the comparison of the two
derived tensor products**, and not the zero morphism of bifunctors.  The functor is the
one-point identification on derived categories and the adjunction is
`onePointDerivedAdjunction`. -/
def onePointComparisonWithTensor : OnePointComparison (onePointRingedSpace R) where
  pullback := (onePointSectionsEquivalence R).functor.mapDerivedCategory
  adjunction := onePointDerivedAdjunction R
  tensorComparison := onePointTensorComparison R

/-- The tensor comparison of `onePointComparisonWithTensor` is `onePointTensorComparison`. -/
theorem onePointComparisonWithTensor_tensorComparison :
    (onePointComparisonWithTensor R).tensorComparison = onePointTensorComparison R :=
  rfl

/-- The left adjoint of `onePointComparisonWithTensor` is the one-point identification on
derived categories. -/
theorem onePointComparisonWithTensor_pullback :
    (onePointComparisonWithTensor R).pullback =
      (onePointSectionsEquivalence R).functor.mapDerivedCategory :=
  rfl

end Stacks.Cohomology.DerivedSectionsOnAPoint

end
