module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposInverseImageTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorComparisonOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.CoefficientMixedDerivedTensor

/-!
# Stacks 08I6 for a morphism of ringed topoi, in `D(O)`

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi in the sense of Stacks 01D3,
part (2): a morphism of the underlying topoi together with the structure map, with no functor
between the underlying sites.  **Stacks 08I6** asserts a canonical bifunctorial isomorphism

`F ⊗^L_O Lf^*G ≅ F ⊗^L_{f⁻¹O'} f⁻¹G`

for `F` in `D(O)` and `G` in `D(O')`.  Both sides are objects of `D(O)`: on the right the
tensor product over the smaller sheaf of rings `f⁻¹O' ⟶ O` carries the `O`-action of its first
factor, and `f⁻¹G` is the inverse image of Stacks 03D2, which is exact (Stacks 04JC), applied
termwise.

The proof is the source's.  Write `α : f⁻¹O' ⟶ O` for the structure map.  For a sheaf `F` of
`O`-modules and a sheaf `G` of `O'`-modules,

`F ⊗_{f⁻¹O'} f⁻¹G ≅ F ⊗_O (O ⊗_{f⁻¹O'} f⁻¹G) = F ⊗_O f^*G`,

the first isomorphism being the cancellation of a base change and the second the definition of
`f^*` (Stacks 03D6, part (2)).  At a complex `F` of `O`-modules and a K-flat complex `G` of
`O'`-modules with flat terms both derived tensor products are total complexes: on the left
because `Lf^*G = f^*G` (Stacks 06YY) is K-flat (Stacks 0G7E), on the right because `f⁻¹G` is a
K-flat complex of `f⁻¹O'`-modules with flat terms.  The underived identity in each bidegree then
identifies them, and the passage to arbitrary objects is the descent along the localization of
pairs of models.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.OfToposHom.inverseImageRing`: the sheaf of commutative
  rings `f⁻¹O'` on the site of the source, and `inverseImageRingMap` the structure map
  `f⁻¹O' ⟶ O`.
* `Stacks.Cohomology.MixedDerivedTensor.OfToposHom.derivedInverseImage`: `f⁻¹ : D(O') ⥤ D(f⁻¹O')`,
  the functor induced by the exact inverse image of sheaves of modules.
* `Stacks.Cohomology.MixedDerivedTensor.OfToposHom.derivedTensorPullback` and
  `derivedMixedTensorInverseImage`: the two bifunctors `D(O) × D(O') ⥤ D(O)` of the tag.
* `Stacks.Cohomology.MixedDerivedTensor.OfToposHom.derivedMixedTensorIso`: **Stacks 08I6**.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.OfToposHom.isKFlat_inverseImageComplex`: the inverse
  image of a K-flat complex of `O'`-modules with flat terms is a K-flat complex of
  `f⁻¹O'`-modules with flat terms.

## Implementation notes

*The geometric half of the factorization.*  The inverse image of modules is the pullback along
the morphism of ringed topoi `g : (Sh(C), f⁻¹O') ⟶ (Sh(C'), O')` with underlying morphism of
topoi that of `f` and structure map the unit `O' ⟶ f_*f⁻¹O'` (`inverseImageHom`), up to the
extension of scalars along the identity of `f⁻¹O'`.  So Stacks 0G7E and 05VD for `g`, which hold
for every morphism of ringed topoi, give the K-flatness and the flatness of the terms of `f⁻¹G`.

*No morphism-of-sites hypothesis.*  Every input — the derived pullback and its computation on
K-flat complexes with flat terms, Stacks 0G7E, the exactness of the inverse image of modules —
is available for an arbitrary `AlgebraicGeometry.RingedToposHom`, so nothing about the
underlying sites is assumed.  The derived pullback exists by the file-local instance
`Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`.

*The universe narrowing, inherited.*  Both ringed topoi are taken at `RingedTopos.{u, u, u}`,
because the derived tensor product of Stacks 06YU is available only there.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [The Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [The Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [The Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [The Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (IsKFlat)
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom (pullbackComplex)

namespace Stacks.Cohomology.MixedDerivedTensor.OfToposHom

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

/-! ### The sheaf of rings `f⁻¹O'` and the inverse image of modules -/

section InverseImage

/-- The sheaf of commutative rings `f⁻¹O'` on the site of the source. -/
abbrev inverseImageRing : Sheaf X.J CommRingCat.{u} :=
  RingedToposHom.inverseImageStructureSheaf f.toModulesHom

/-- The structure map `f⁻¹O' ⟶ O`, in its inverse-image form. -/
abbrev inverseImageRingMap : inverseImageRing f ⟶ X.O :=
  RingedToposHom.coefficientMap f.toModulesHom

/-- The ringed topos `(Sh(C), f⁻¹O')`. -/
abbrev inverseImageTopos : RingedTopos.{u, u, u} :=
  Stacks.Cohomology.ringedTopos X.J (inverseImageRing f)

/-- **The inverse image of sheaves of modules** `f⁻¹`, from `O'`-modules to `f⁻¹O'`-modules
(Stacks 03D2). -/
abbrev inverseImage :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRing f)) :=
  Stacks.Sheaves.RingedToposModules.inverseImageModules f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)

/-- The inverse image of sheaves of modules preserves finite limits. -/
instance inverseImage_preservesFiniteLimits : PreservesFiniteLimits (inverseImage f) :=
  Stacks.Sheaves.RingedToposModules.inverseImageModules_preservesFiniteLimits f.toToposHom _

/-- The inverse image of sheaves of modules preserves finite colimits. -/
instance inverseImage_preservesFiniteColimits : PreservesFiniteColimits (inverseImage f) :=
  Stacks.Sheaves.RingedToposModules.inverseImageModules_preservesFiniteColimits f.toToposHom _

/-- The inverse image of sheaves of modules is additive. -/
instance inverseImage_additive : (inverseImage f).Additive := by
  have : (inverseImage f).IsLeftAdjoint :=
    Stacks.Sheaves.RingedToposModules.inverseImageModules_isLeftAdjoint f.toToposHom _
  have : (inverseImage f).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_isLeftAdjoint _
  have : PreservesBinaryBiproducts (inverseImage f) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

/-- **The derived inverse image** `f⁻¹ : D(O') ⥤ D(f⁻¹O')`: the inverse image of modules is
exact, so it induces a functor on derived categories, computed termwise. -/
abbrev derivedInverseImage :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRing f))) :=
  (inverseImage f).mapDerivedCategory

/-- `f^*` is the extension of scalars of `f⁻¹` along `f⁻¹O' ⟶ O`: the two extensions of scalars
are left adjoint to one restriction of scalars. -/
def extendScalarsFSharpIso :
    extendScalarsFSharp f.toModulesHom ≅
      Stacks.FlatChangeOfRings.extendScalars (inverseImageRingMap f) :=
  (extendRestrictScalarsAdjunction X.J (fSharpCommRing f.toModulesHom) _ _).leftAdjointUniq
    (Stacks.FlatChangeOfRings.extendScalarsAdjunction (inverseImageRingMap f))

/-- **`f^* ≅ O ⊗_{f⁻¹O'} f⁻¹(-)`**, as functors from `O'`-modules to `O`-modules. -/
def pullbackIsoExtendInverseImage :
    f.toModulesHom.pullbackModules ≅
      inverseImage f ⋙ Stacks.FlatChangeOfRings.extendScalars (inverseImageRingMap f) :=
  Functor.isoWhiskerLeft (inverseImage f) (extendScalarsFSharpIso f)

end InverseImage

/-! ### The geometric half `(Sh(C), f⁻¹O') ⟶ (Sh(C'), O')` -/

section GeometricHalf

/-- The morphism of ringed topoi `(Sh(C), f⁻¹O') ⟶ (Sh(C'), O')` with underlying morphism of
topoi that of `f` and structure map the unit `O' ⟶ f_*f⁻¹O'`. -/
def inverseImageHom : AlgebraicGeometry.RingedToposHom (inverseImageTopos f) Y where
  toToposHom := f.toToposHom
  fSharp := (commRingImageAdjunction f.toToposHom).unit.app Y.O

/-- The inverse-image form of the structure map of `inverseImageHom` is the identity. -/
lemma inverseImageHom_fSharpInverseImage :
    (inverseImageHom f).fSharpInverseImage = 𝟙 _ := by
  show ((commRingImageAdjunction f.toToposHom).homEquiv Y.O _).symm
    ((commRingImageAdjunction f.toToposHom).unit.app Y.O) = 𝟙 _
  rw [Adjunction.homEquiv_counit]
  exact (commRingImageAdjunction f.toToposHom).left_triangle_components Y.O

/-- The inverse-image form of the structure map of `inverseImageHom`, at the level of sheaves of
rings along which scalars are extended, is the identity. -/
lemma inverseImageHom_fSharpInverseImageRing :
    (inverseImageHom f).fSharpInverseImageRing = 𝟙 _ := by
  have e := inverseImageHom_fSharpInverseImage f
  have h := (inverseImageHom f).forgetRing_map_fSharpInverseImage
  refine (sheafCompose X.J (forget RingCat.{u})).map_injective ?_
  exact h.symm.trans ((congrArg (inverseImageTopos f).forgetRing.map e).trans
    ((CategoryTheory.Functor.map_id _ _).trans (CategoryTheory.Functor.map_id _ _).symm))

/-- Restriction of scalars along a map of sheaves of rings equal to the identity is right
adjoint to the identity functor. -/
def adjunctionRestrictScalarsOfEqId {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (ψ : R ⟶ R) (h : ψ = 𝟙 R) :
    𝟭 (SheafOfModules.{u} R) ⊣ SheafOfModules.restrictScalars.{u} ψ := by
  subst h
  exact Adjunction.id

/-- Extension of scalars along the structure map of `inverseImageHom` is the identity. -/
def extendScalarsFSharpInverseImageHomIso :
    extendScalarsFSharp (inverseImageHom f).toModulesHom ≅ 𝟭 _ :=
  (extendRestrictScalarsAdjunction X.J (fSharpCommRing (inverseImageHom f).toModulesHom) _ _
    ).leftAdjointUniq (adjunctionRestrictScalarsOfEqId _ (inverseImageHom_fSharpInverseImageRing f))

/-- Pullback along `inverseImageHom` is the inverse image of modules. -/
def pullbackInverseImageHomIso :
    (inverseImageHom f).toModulesHom.pullbackModules ≅ inverseImage f :=
  Functor.isoWhiskerLeft (inverseImage f) (extendScalarsFSharpInverseImageHomIso f) ≪≫
    Functor.rightUnitor _

/-- **The inverse image of a K-flat complex of `O'`-modules with flat terms is a K-flat complex
of `f⁻¹O'`-modules with flat terms**: it is the pullback along `inverseImageHom`, so this is
Stacks 0G7E and 05VD for that morphism of ringed topoi. -/
theorem isKFlat_inverseImageComplex
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hG : CochainComplex.KFlatBifunctor.KFlat
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) G)
    (hflatG : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (G.X i)) :
    IsKFlat (Y := inverseImageTopos f) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)) := by
  have := (inverseImageHom f).pullbackModules_additive
  refine ⟨?_, fun i ↦ ?_⟩
  · exact CochainComplex.KFlatBifunctor.KFlat.of_iso
      (F := Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (inverseImageRing f))
      (K := (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.pullbackComplex
        (inverseImageHom f)).obj G)
      (K' := ((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
      (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.kFlat_pullbackComplex
        (inverseImageHom f) G hG hflatG)
      ((NatIso.mapHomologicalComplex (pullbackInverseImageHomIso f) (ComplexShape.up ℤ)).app G)
  · exact Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize (inverseImageRing f)
      ((pullbackInverseImageHomIso f).app (G.X i))
      (Stacks.Sheaves.DerivedPullback.KFlatPullbackOfToposHom.isFlat_pullbackModules_obj
        (inverseImageHom f) _ (hflatG i))

end GeometricHalf

/-! ### The underived identity -/

section Underived

/-- **The underived identity of Stacks 08I6**: `F ⊗_{f⁻¹O'} f⁻¹G ≅ F ⊗_O f^*G` as sheaves of
`O`-modules, for a sheaf `F` of `O`-modules and a sheaf `G` of `O'`-modules. -/
def mixedTensorPullbackIso
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((Stacks.MixedBaseChange.mixedSheafTensor (inverseImageRingMap f)).obj H).obj
        ((inverseImage f).obj G) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).obj
        (f.toModulesHom.pullbackModules.obj G) :=
  coeffMixedTensorExtendIso (inverseImageRingMap f) H ((inverseImage f).obj G) ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).mapIso
      ((pullbackIsoExtendInverseImage f).app G).symm

/-- The underived identity is natural in the sheaf of `O`-modules. -/
lemma mixedTensorPullbackIso_naturality_fst
    {H H' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (φ : H ⟶ H')
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((Stacks.MixedBaseChange.mixedSheafTensor (inverseImageRingMap f)).map φ).app
          ((inverseImage f).obj G) ≫ (mixedTensorPullbackIso f H' G).hom =
      (mixedTensorPullbackIso f H G).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map φ).app
          (f.toModulesHom.pullbackModules.obj G) :=
  Stacks.MixedBaseChange.paste_squares
    (coeffMixedTensorExtendIso_naturality_fst (inverseImageRingMap f) φ ((inverseImage f).obj G))
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).map φ).naturality
      ((pullbackIsoExtendInverseImage f).inv.app G)).symm

/-- The underived identity is natural in the sheaf of `O'`-modules. -/
lemma mixedTensorPullbackIso_naturality_snd
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    {G G' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (v : G ⟶ G') :
    ((Stacks.MixedBaseChange.mixedSheafTensor (inverseImageRingMap f)).obj H).map
          ((inverseImage f).map v) ≫ (mixedTensorPullbackIso f H G').hom =
      (mixedTensorPullbackIso f H G).hom ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map
          (f.toModulesHom.pullbackModules.map v) :=
  Stacks.MixedBaseChange.paste_squares
    (coeffMixedTensorExtendIso_naturality_snd (inverseImageRingMap f) H ((inverseImage f).map v))
    ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map_comp
        _ _).symm.trans
      ((congrArg ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map
        ((pullbackIsoExtendInverseImage f).inv.naturality v)).trans
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj H).map_comp _ _)))

end Underived

/-! ### Stacks 08I6 -/

section Tag

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

/-- **The left-hand bifunctor of Stacks 08I6**: `(F, G) ↦ F ⊗^L_O Lf^*G`, in `D(O)`. -/
abbrev derivedTensorPullback :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (𝟭 _).prod (derivedPullback f) ⋙
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)

/-- **The right-hand bifunctor of Stacks 08I6**: `(F, G) ↦ F ⊗^L_{f⁻¹O'} f⁻¹G`, the derived
tensor product over `f⁻¹O'` of `F` and the inverse image `f⁻¹G`, an object of `D(O)` through
`F`. -/
abbrev derivedMixedTensorInverseImage :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (𝟭 _).prod (derivedInverseImage f) ⋙
    Functor.uncurry.obj (coeffMixedDerivedTensor (inverseImageRingMap f))

/-- `Tot(F ⊗_{f⁻¹O'} f⁻¹G) ≅ Tot(F ⊗_O f^*G)` as complexes of `O`-modules: the underived
identity of Stacks 08I6 in each bidegree. -/
def mixedTotalPullbackIso
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ) :
    HomologicalComplex.mapBifunctor F
        (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
        (Stacks.MixedBaseChange.mixedSheafTensor (inverseImageRingMap f)) (ComplexShape.up ℤ) ≅
      HomologicalComplex.mapBifunctor F ((pullbackComplex f).obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  transportTotalIso (Stacks.MixedBaseChange.mixedSheafTensor (inverseImageRingMap f))
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (inverseImage f)
    f.toModulesHom.pullbackModules (mixedTensorPullbackIso f)
    (fun u e ↦ mixedTensorPullbackIso_naturality_fst f u e)
    (fun a _ _ v ↦ mixedTensorPullbackIso_naturality_snd f a v) F G

/-- The identification of total complexes is natural in both complexes. -/
lemma mixedTotalPullbackIso_hom_naturality
    {F F' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {G G' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (φ : F ⟶ F') (a : G ⟶ G') :
    HomologicalComplex.mapBifunctorMap φ
          (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map a)
          (Stacks.MixedBaseChange.mixedSheafTensor (inverseImageRingMap f)) (ComplexShape.up ℤ) ≫
        (mixedTotalPullbackIso f F' G').hom =
      (mixedTotalPullbackIso f F G).hom ≫
        HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ) :=
  transportTotalIso_hom_naturality (Stacks.MixedBaseChange.mixedSheafTensor (inverseImageRingMap f))
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (inverseImage f)
    f.toModulesHom.pullbackModules (mixedTensorPullbackIso f)
    (fun u e ↦ mixedTensorPullbackIso_naturality_fst f u e)
    (fun a _ _ v ↦ mixedTensorPullbackIso_naturality_snd f a v) φ a

section Models

variable (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
  (G : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
  (hG : CochainComplex.KFlatBifunctor.KFlat
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) G)
  (hflatG : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (G.X i))

/-- The left-hand side of Stacks 08I6 at a K-flat complex of `O'`-modules with flat terms is the
class of `Tot(F ⊗_O f^*G)`. -/
def modelLeft :
    (derivedTensorPullback f).obj (DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor F ((pullbackComplex f).obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) :=
  (Functor.uncurry.obj
        (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).mapIso
      ((Iso.refl (DerivedCategory.Q.obj F)).prod
        (Stacks.Sheaves.DerivedPullback.OfToposHom.flatPullbackIso f G hG hflatG)) ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
      F ((pullbackComplex f).obj G)
      (Stacks.Sheaves.DerivedPullback.OfToposHom.kFlatBifunctor_pullbackComplex f G hG hflatG)

/-- The right-hand side of Stacks 08I6 at a K-flat complex of `O'`-modules with flat terms is
the class of `Tot(F ⊗_{f⁻¹O'} f⁻¹G)`, which the underived identity identifies with
`Tot(F ⊗_O f^*G)`. -/
def modelRight :
    (derivedMixedTensorInverseImage f).obj
        (DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) ≅
      DerivedCategory.Q.obj (HomologicalComplex.mapBifunctor F ((pullbackComplex f).obj G)
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) :=
  (Functor.uncurry.obj (coeffMixedDerivedTensor (inverseImageRingMap f))).mapIso
      ((Iso.refl (DerivedCategory.Q.obj F)).prod
        ((inverseImage f).mapDerivedCategoryFactors.app G)) ≪≫
    coeffMixedDerivedTensorComparison (inverseImageRingMap f) F
      (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
      (isKFlat_inverseImageComplex f G hG hflatG) ≪≫
    DerivedCategory.Q.mapIso (mixedTotalPullbackIso f F G)

/-- **Stacks 08I6 at a K-flat complex of `O'`-modules with flat terms.** -/
def modelIso :
    (derivedTensorPullback f).obj (DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) ≅
      (derivedMixedTensorInverseImage f).obj
        (DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) :=
  modelLeft f F G hG hflatG ≪≫ (modelRight f F G hG hflatG).symm

end Models

/-- A natural isomorphism `T.mapIso (𝟙 ×ˢ e) ≪≫ c` is natural in `(F, G)` as soon as `e` and `c`
are. -/
private lemma map_mapIso_prod_trans_naturality
    {A B D : Type*} [Category A] [Category B] [Category D] (T : A × B ⥤ D)
    {F F' : A} (φ : F ⟶ F') {G G' G₂ G₂' : B} (a : G ⟶ G') (b : G₂ ⟶ G₂')
    (e : G ≅ G₂) (e' : G' ≅ G₂') (he : a ≫ e'.hom = e.hom ≫ b)
    {Z Z' : D} (c : T.obj (F, G₂) ≅ Z) (c' : T.obj (F', G₂') ≅ Z') (w : Z ⟶ Z')
    (hc : T.map (φ, b) ≫ c'.hom = c.hom ≫ w) :
    T.map (φ, a) ≫ (T.mapIso ((Iso.refl F').prod e') ≪≫ c').hom =
      (T.mapIso ((Iso.refl F).prod e) ≪≫ c).hom ≫ w := by
  refine Stacks.Sheaves.DerivedPullback.trans_naturality ?_ hc
  rw [Functor.mapIso_hom, Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg T.map (Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm) he)

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

/-- The left-hand side of Stacks 08I6 at the models is natural in the pair of complexes. -/
lemma modelLeft_naturality :
    (derivedTensorPullback f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        (modelLeft f F' G' hG' hflatG').hom =
      (modelLeft f F G hG hflatG).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
  have h2 : (Functor.uncurry.obj
            (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).tensor).map
          ((DerivedCategory.Q.map φ,
              DerivedCategory.Q.map ((pullbackComplex f).map a)) :
            ((DerivedCategory.Q.obj F,
                DerivedCategory.Q.obj ((pullbackComplex f).obj G)) : _ × _) ⟶
              (DerivedCategory.Q.obj F',
                DerivedCategory.Q.obj ((pullbackComplex f).obj G'))) ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
          F' ((pullbackComplex f).obj G')
          (Stacks.Sheaves.DerivedPullback.OfToposHom.kFlatBifunctor_pullbackComplex f G' hG'
            hflatG')).hom =
      ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight
          F ((pullbackComplex f).obj G)
          (Stacks.Sheaves.DerivedPullback.OfToposHom.kFlatBifunctor_pullbackComplex f G hG
            hflatG)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ
          ((pullbackComplex f).map a) (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ)) := by
    simpa only [Functor.uncurry_obj_map, Category.assoc] using
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.O).comparisonRight_naturality
        φ ((pullbackComplex f).map a)
        (Stacks.Sheaves.DerivedPullback.OfToposHom.kFlatBifunctor_pullbackComplex f G hG hflatG)
        (Stacks.Sheaves.DerivedPullback.OfToposHom.kFlatBifunctor_pullbackComplex f G' hG'
          hflatG')
  rw [Functor.comp_map]
  exact map_mapIso_prod_trans_naturality _ (DerivedCategory.Q.map φ)
    ((derivedPullback f).map (DerivedCategory.Q.map a))
    (DerivedCategory.Q.map ((pullbackComplex f).map a)) _ _
    (Stacks.Sheaves.DerivedPullback.OfToposHom.flatPullbackIso_naturality f a hG hG' hflatG
      hflatG') _ _ _ h2

/-- The right-hand side of Stacks 08I6 at the models is natural in the pair of complexes. -/
lemma modelRight_naturality :
    (derivedMixedTensorInverseImage f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        (modelRight f F' G' hG' hflatG').hom =
      (modelRight f F G hG hflatG).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
  have h2 : (Functor.uncurry.obj (coeffMixedDerivedTensor (inverseImageRingMap f))).map
          ((DerivedCategory.Q.map φ,
              DerivedCategory.Q.map (((inverseImage f).mapHomologicalComplex
                (ComplexShape.up ℤ)).map a)) :
            ((DerivedCategory.Q.obj F,
                DerivedCategory.Q.obj (((inverseImage f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj G)) : _ × _) ⟶
              (DerivedCategory.Q.obj F',
                DerivedCategory.Q.obj (((inverseImage f).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj G'))) ≫
        (coeffMixedDerivedTensorComparison (inverseImageRingMap f) F'
          (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G')
          (isKFlat_inverseImageComplex f G' hG' hflatG')).hom =
      (coeffMixedDerivedTensorComparison (inverseImageRingMap f) F
          (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).obj G)
          (isKFlat_inverseImageComplex f G hG hflatG)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ
          (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map a)
          (Stacks.MixedBaseChange.mixedSheafTensor (inverseImageRingMap f))
          (ComplexShape.up ℤ)) := by
    simpa only [Functor.uncurry_obj_map, Category.assoc] using
      coeffMixedDerivedTensorComparison_naturality (inverseImageRingMap f) φ
        (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map a)
        (isKFlat_inverseImageComplex f G hG hflatG)
        (isKFlat_inverseImageComplex f G' hG' hflatG')
  have h3 : DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ
          (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map a)
          (Stacks.MixedBaseChange.mixedSheafTensor (inverseImageRingMap f))
          (ComplexShape.up ℤ)) ≫
        (DerivedCategory.Q.mapIso (mixedTotalPullbackIso f F' G')).hom =
      (DerivedCategory.Q.mapIso (mixedTotalPullbackIso f F G)).hom ≫
        DerivedCategory.Q.map (HomologicalComplex.mapBifunctorMap φ ((pullbackComplex f).map a)
          (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)) := by
    rw [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.mapIso_hom,
      ← Functor.map_comp, ← Functor.map_comp, mixedTotalPullbackIso_hom_naturality f φ a]
  rw [Functor.comp_map]
  exact map_mapIso_prod_trans_naturality _ (DerivedCategory.Q.map φ)
    ((derivedInverseImage f).map (DerivedCategory.Q.map a))
    (DerivedCategory.Q.map (((inverseImage f).mapHomologicalComplex (ComplexShape.up ℤ)).map a))
    _ _ ((inverseImage f).mapDerivedCategoryFactors_hom_naturality a) _ _ _
    (Stacks.Sheaves.DerivedPullback.trans_naturality h2 h3)

/-- **Stacks 08I6 at the models is natural in the pair of complexes.** -/
lemma modelIso_naturality :
    (derivedTensorPullback f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) ≫
        (modelIso f F' G' hG' hflatG').hom =
      (modelIso f F G hG hflatG).hom ≫
        (derivedMixedTensorInverseImage f).map
          ((DerivedCategory.Q.map φ, DerivedCategory.Q.map a) :
            ((DerivedCategory.Q.obj F, DerivedCategory.Q.obj G) : _ × _) ⟶
              (DerivedCategory.Q.obj F', DerivedCategory.Q.obj G')) :=
  Stacks.Sheaves.DerivedPullback.isoOverCommonTarget_naturality
    (modelLeft_naturality f φ a hG hG' hflatG hflatG')
    (modelRight_naturality f φ a hG hG' hflatG hflatG')

end Naturality

/-! ### The descent to arbitrary objects of the derived categories -/

/-- The isomorphism of Stacks 08I6 at the models, as an isomorphism of the two functors on the
category of pairs of models. -/
def modelsTensorIso :
    mixedModelsQ (X := X) (Y := Y) ⋙ derivedTensorPullback f ≅
      mixedModelsQ (X := X) (Y := Y) ⋙ derivedMixedTensorInverseImage f :=
  NatIso.ofComponents
    (fun P =>
      (derivedTensorPullback f).mapIso (mixedModelsIso P) ≪≫
        modelIso f P.1 P.2.obj.as P.2.property.1 P.2.property.2 ≪≫
          ((derivedMixedTensorInverseImage f).mapIso (mixedModelsIso P)).symm)
    (fun {P R} g => Stacks.Sheaves.DerivedPullback.transportedIso_naturality
      (derivedTensorPullback f) (derivedMixedTensorInverseImage f)
      (mixedModelsIso P) (mixedModelsIso R)
      (modelIso f P.1 P.2.obj.as P.2.property.1 P.2.property.2)
      (modelIso f R.1 R.2.obj.as R.2.property.1 R.2.property.2)
      ((mixedModelsQ (X := X) (Y := Y)).map g)
      ((DerivedCategory.Q.map g.1, DerivedCategory.Q.map g.2.hom.out) :
        ((DerivedCategory.Q.obj P.1, DerivedCategory.Q.obj P.2.obj.as) : _ × _) ⟶
          (DerivedCategory.Q.obj R.1, DerivedCategory.Q.obj R.2.obj.as))
      (mixedModelsIso_naturality g)
      (modelIso_naturality f g.1 g.2.hom.out
        P.2.property.1 R.2.property.1 P.2.property.2 R.2.property.2))

/-- **Stacks 08I6.**  For a morphism of ringed topoi `f : (Sh(C), O) ⟶ (Sh(C'), O')` — a
morphism of the underlying topoi together with the structure map, with no hypothesis on the
underlying sites — the canonical bifunctorial isomorphism

`F ⊗^L_O Lf^*G ≅ F ⊗^L_{f⁻¹O'} f⁻¹G`

in `D(O)`, for `F` in `D(O)` and `G` in `D(O')`.  The right-hand side is the derived tensor
product over `f⁻¹O'` (`coeffMixedDerivedTensor` along the structure map `f⁻¹O' ⟶ O`) of `F` and
the inverse image `f⁻¹G` (`derivedInverseImage`), an object of `D(O)` through `F`.  It is stated
between the two uncurried bifunctors on `D(O) × D(O')`, so that bifunctoriality is part of its
type.

At a complex `F` of `O`-modules and a K-flat complex `G` of `O'`-modules with flat terms both
sides are total complexes and the isomorphism is the underived identity
`F ⊗_{f⁻¹O'} f⁻¹G ≅ F ⊗_O f^*G` in each bidegree (`modelIso`); the passage to arbitrary objects
is the descent along the localization of pairs of models. -/
@[stacks 08I6 "the canonical bifunctorial isomorphism in D(O), for an arbitrary morphism of
ringed topoi"]
def derivedMixedTensorIso :
    derivedTensorPullback f ≅ derivedMixedTensorInverseImage f := by
  letI : (mixedModelsQ (X := X) (Y := Y)).IsLocalization (mixedModelsW (X := X) (Y := Y)) :=
    mixedModelsQ_isLocalization
  letI : Localization.Lifting (mixedModelsQ (X := X) (Y := Y))
      (mixedModelsW (X := X) (Y := Y))
      (mixedModelsQ (X := X) (Y := Y) ⋙ derivedTensorPullback f)
      (derivedTensorPullback f) := ⟨Iso.refl _⟩
  letI : Localization.Lifting (mixedModelsQ (X := X) (Y := Y))
      (mixedModelsW (X := X) (Y := Y))
      (mixedModelsQ (X := X) (Y := Y) ⋙ derivedMixedTensorInverseImage f)
      (derivedMixedTensorInverseImage f) := ⟨Iso.refl _⟩
  exact Localization.liftNatIso (mixedModelsQ (X := X) (Y := Y))
    (mixedModelsW (X := X) (Y := Y)) _ _ _ _ (modelsTensorIso f)

end Tag

end Stacks.Cohomology.MixedDerivedTensor.OfToposHom

end
