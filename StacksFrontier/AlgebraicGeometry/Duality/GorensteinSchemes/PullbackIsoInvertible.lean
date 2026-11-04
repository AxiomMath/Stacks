module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackSheafTensorMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.OverEquivInvertible
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAndResolutions.KInjectiveRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles

/-!
# Invertibility carried along the pullback of an isomorphism of schemes

Let `f : X ⟶ Y` be an **isomorphism** of schemes. This file carries invertibility of an object
of `D(𝒪_Y)` forward to `D(𝒪_X)`, along both of the two functors `Mod(𝒪_Y) ⥤ Mod(𝒪_X)` that
Mathlib attaches to `f`:

* `AlgebraicGeometry.Scheme.Modules.pullback f`, the inverse image, and
* `AlgebraicGeometry.Scheme.Modules.restrictFunctor f`, the restriction along the open
  immersion `f`, which `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` identifies
  with the first.

## Main definitions

* `Stacks.SheafOfModules.PullbackIsoTensor.schemeRingSheaf`, `modRingSheaf` and `modTensor`: the
  structure sheaf of a scheme, the sheaf of (not necessarily commutative) rings it defines, and
  the tensor product bifunctor of sheaves of modules over it.
* `Stacks.SheafOfModules.PullbackIsoTensor.pullbackEquivMod`: `f^*` as an **equivalence**
  `Mod(𝒪_Y) ≌ Mod(𝒪_X)`.
* `Stacks.SheafOfModules.PullbackIsoTensor.pullbackTensorIso`: **`f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`**,
  the comparison of [Stacks, Tag 01CD].
* `Stacks.SheafOfModules.PullbackIsoTensor.pullbackDerivedTensorObjIso`:
  **`f^*(K ⊗^𝐋 L) ≅ f^*K ⊗^𝐋 f^*L`** on arbitrary objects of the derived categories.

## Main results

* `Stacks.SheafOfModules.PullbackIsoTensor.pullbackTensorIso_naturality_left` and
  `pullbackTensorIso_naturality_right`: the abelian comparison is natural in each variable
  separately.
* `Stacks.SheafOfModules.PullbackIsoTensor.isInvertible_pullback_obj` and
  `isInvertible_pullback`: **the image under `f^*` of an invertible object of `D(𝒪_Y)` is an
  invertible object of `D(𝒪_X)`**, with the two monoidal structures explicit and then at the
  structure of [Stacks, Tag 0FPT] on both sides.
* `Stacks.SheafOfModules.PullbackIsoTensor.isInvertible_restrictFunctor`: **the same for
  `Scheme.Modules.restrictFunctor f`**.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace
open CochainComplex.KFlatBifunctor
open Stacks.SheafOfModules.DerivedMonoidal (derivedMonoidal derivedSymmetric
  derivedTensorBifunctorIso canonicalUnitIso)

universe d u

namespace Stacks.SheafOfModules.PullbackIsoTensor

/-! ### The structure sheaf, the ring sheaf and the tensor product -/

/-- **The structure sheaf of a scheme**, as a sheaf of commutative rings on the site of its
opens: `AlgebraicGeometry.Scheme.sheaf`. -/
abbrev schemeRingSheaf (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) CommRingCat.{u} :=
  X.sheaf

/-- **The structure sheaf read as a sheaf of (not necessarily commutative) rings**, which is
what `CategoryTheory.SheafOfModules` takes its modules over. This is
`AlgebraicGeometry.Scheme.ringCatSheaf` and
`Stacks.RingedSpace.structureRingSheaf X.toRingedSpace`, all three equal by `rfl`. -/
abbrev modRingSheaf (X : Scheme.{u}) :
    Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (schemeRingSheaf X)

/-- **The tensor product of sheaves of modules on a scheme**, [Stacks, Tag 01CA], as a
bifunctor. -/
abbrev modTensor (X : Scheme.{u}) :
    _root_.SheafOfModules.{u} (modRingSheaf X) ⥤ _root_.SheafOfModules.{u} (modRingSheaf X) ⥤
      _root_.SheafOfModules.{u} (modRingSheaf X) :=
  Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (schemeRingSheaf X)

/-- **`Mod(𝒪_X)` is abelian.** -/
instance abelianModules (X : Scheme.{u}) :
    Abelian (_root_.SheafOfModules.{u} (modRingSheaf X)) :=
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian (schemeRingSheaf X)

/-! ### The pullback of an isomorphism of schemes, as an equivalence -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]

/-- **The morphism of ringed spaces underlying `f`.** -/
abbrev ringedHom : X.toRingedSpace ⟶ Y.toRingedSpace :=
  f.toLRSHom.toShHom

/-- **`f^* : Mod(𝒪_Y) ⥤ Mod(𝒪_X)`**: `AlgebraicGeometry.Scheme.Modules.pullback f`. -/
abbrev pullbackMod : _root_.SheafOfModules.{u} (modRingSheaf Y) ⥤
    _root_.SheafOfModules.{u} (modRingSheaf X) :=
  Scheme.Modules.pullback f

/-- `f^*` is additive. -/
instance pullbackMod_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive (pullbackMod f) :=
  inferInstanceAs (Functor.Additive (Scheme.Modules.pullback f))

/-- **`f^*` is an equivalence of categories of modules** when `f` is an isomorphism. -/
instance isEquivalence_pullbackMod : (pullbackMod f).IsEquivalence :=
  Stacks.Cohomology.modulePullbackIso_isEquivalence (asIso (ringedHom f))

/-- **`f^*` packaged as an equivalence `Mod(𝒪_Y) ≌ Mod(𝒪_X)`.** -/
abbrev pullbackEquivMod : _root_.SheafOfModules.{u} (modRingSheaf Y) ≌
    _root_.SheafOfModules.{u} (modRingSheaf X) :=
  (pullbackMod f).asEquivalence

/-- The functor of the equivalence `f^*` is additive. -/
instance pullbackEquivMod_functor_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
      (pullbackEquivMod f).functor :=
  inferInstanceAs (Functor.Additive (Scheme.Modules.pullback f))

/-- The inverse of `f^*` is additive, being the inverse of an additive equivalence. -/
instance pullbackEquivMod_inverse_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive
      (pullbackEquivMod f).inverse :=
  Equivalence.inverse_additive _

/-- **`f^*` preserves finite limits** when `f` is an isomorphism. -/
instance preservesFiniteLimits_pullbackMod : PreservesFiniteLimits (pullbackMod f) :=
  letI : PreservesLimits (pullbackMod f) :=
    (pullbackMod f).asEquivalence.symm.toAdjunction.rightAdjoint_preservesLimits
  inferInstance

/-- **Restriction along `f`**: `AlgebraicGeometry.Scheme.Modules.restrictFunctor f`. -/
abbrev restrictMod : _root_.SheafOfModules.{u} (modRingSheaf Y) ⥤
    _root_.SheafOfModules.{u} (modRingSheaf X) :=
  Scheme.Modules.restrictFunctor f

/-- Restriction along `f` is additive. -/
instance restrictMod_additive :
    @Functor.Additive _ _ _ _ Abelian.toPreadditive Abelian.toPreadditive (restrictMod f) :=
  inferInstanceAs (Functor.Additive (Scheme.Modules.restrictFunctor f))

/-- Restriction along `f` preserves finite limits. -/
instance preservesFiniteLimits_restrictMod : PreservesFiniteLimits (restrictMod f) :=
  inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.restrictFunctor f))

/-- Restriction along `f` preserves finite colimits. -/
instance preservesFiniteColimits_restrictMod : PreservesFiniteColimits (restrictMod f) :=
  inferInstanceAs (PreservesFiniteColimits (Scheme.Modules.restrictFunctor f))

/-! ### The comparison of the tensor products, at the abelian level -/

/-- **`f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`**: the comparison of [Stacks, Tag 01CD], which is an
isomorphism for every morphism of ringed spaces. -/
def pullbackTensorIso (A B : _root_.SheafOfModules.{u} (modRingSheaf Y)) :
    (pullbackEquivMod f).functor.obj (((modTensor Y).obj A).obj B) ≅
      ((modTensor X).obj ((pullbackEquivMod f).functor.obj A)).obj
        ((pullbackEquivMod f).functor.obj B) :=
  Stacks.PullbackSheafTensor.sheafTensorComparisonIso (ringedHom f) A B

/-- **The comparison `pullbackTensorIso` is natural in the first variable.** -/
theorem pullbackTensorIso_naturality_left
    {A A' : _root_.SheafOfModules.{u} (modRingSheaf Y)} (v : A ⟶ A')
    (B : _root_.SheafOfModules.{u} (modRingSheaf Y)) :
    (pullbackEquivMod f).functor.map (((modTensor Y).map v).app B) ≫
        (pullbackTensorIso f A' B).hom =
      (pullbackTensorIso f A B).hom ≫
        ((modTensor X).map ((pullbackEquivMod f).functor.map v)).app
          ((pullbackEquivMod f).functor.obj B) :=
  (Stacks.PullbackSheafTensor.sheafTensorComparison_naturality_left (ringedHom f) v B).symm

/-- **The comparison `pullbackTensorIso` is natural in the second variable.** -/
theorem pullbackTensorIso_naturality_right
    (A : _root_.SheafOfModules.{u} (modRingSheaf Y))
    {B B' : _root_.SheafOfModules.{u} (modRingSheaf Y)} (w : B ⟶ B') :
    (pullbackEquivMod f).functor.map (((modTensor Y).obj A).map w) ≫
        (pullbackTensorIso f A B').hom =
      (pullbackTensorIso f A B).hom ≫
        ((modTensor X).obj ((pullbackEquivMod f).functor.obj A)).map
          ((pullbackEquivMod f).functor.map w) :=
  (Stacks.PullbackSheafTensor.sheafTensorComparison_naturality_right (ringedHom f) A w).symm

/-- **`f^*` carries the structure sheaf of `Y` to the structure sheaf of `X`**: this is
`Stacks.PullbackSheafTensor.sheafTensorUnitIso`, the comparison `ν : f^*𝒪_Y ≅ 𝒪_X`. -/
def pullbackUnitIso :
    (pullbackEquivMod f).functor.obj (_root_.SheafOfModules.unit (modRingSheaf Y)) ≅
      _root_.SheafOfModules.unit (modRingSheaf X) :=
  Stacks.PullbackSheafTensor.sheafTensorUnitIso (ringedHom f)

/-! ### The comparison on the derived categories, and invertibility -/

section Derived

variable
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} (modRingSheaf X))]
  [HasDerivedCategory.{d} (_root_.SheafOfModules.{u} (modRingSheaf Y))]

/-- **`f^*` carries the structure sheaf of `Y` in degree zero to the structure sheaf of `X` in
degree zero.** This is `Stacks.SheafOfModules.PullbackIsoTensor.pullbackUnitIso` moved through
the degree-zero inclusion by
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor`. -/
def pullbackDerivedUnitIso :
    (pullbackEquivMod f).functor.mapDerivedCategory.obj
        ((DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (modRingSheaf Y)) 0).obj
          (_root_.SheafOfModules.unit (modRingSheaf Y))) ≅
      (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (modRingSheaf X)) 0).obj
        (_root_.SheafOfModules.unit (modRingSheaf X)) :=
  (((pullbackEquivMod f).functor).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor (_root_.SheafOfModules.{u} (modRingSheaf X)) 0).mapIso
      (pullbackUnitIso f)

/-- **`f^*(K ⊗^𝐋 L) ≅ f^*K ⊗^𝐋 f^*L`** on arbitrary objects of the derived categories. -/
def pullbackDerivedTensorObjIso
    (K L : DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf Y))) :
    (pullbackEquivMod f).functor.mapDerivedCategory.obj
        (((derivedBifunctor (modTensor Y)).obj K).obj L) ≅
      ((derivedBifunctor (modTensor X)).obj
          ((pullbackEquivMod f).functor.mapDerivedCategory.obj K)).obj
        ((pullbackEquivMod f).functor.mapDerivedCategory.obj L) :=
  derivedTransportObjIsoOfEquivalence (modTensor Y) (modTensor X) (pullbackEquivMod f)
    (pullbackTensorIso f) (pullbackTensorIso_naturality_left f)
    (pullbackTensorIso_naturality_right f) K L

/-- **`f^*` preserves invertibility on the derived categories**, with the two monoidal
structures as explicit arguments, each identified by a pairwise comparison of its tensor product
with the derived tensor bifunctor of [Stacks, Tag 06YU], and `unitε` identifying the images of
the units. -/
theorem isInvertible_pullback_obj
    (mY : MonoidalCategory (DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf Y))))
    (mX : MonoidalCategory (DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf X))))
    (bX : letI := mX; BraidedCategory
      (DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf X))))
    (cmpY : letI := mY; ∀ A B : DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf Y)),
      A ⊗ B ≅ ((derivedBifunctor (modTensor Y)).obj A).obj B)
    (cmpX : letI := mX; ∀ A B : DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf X)),
      A ⊗ B ≅ ((derivedBifunctor (modTensor X)).obj A).obj B)
    (unitε : letI := mY; letI := mX;
      (pullbackEquivMod f).functor.mapDerivedCategory.obj
          (𝟙_ (DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf Y)))) ≅
        𝟙_ (DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf X))))
    (K : DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf Y)))
    (hK : letI := mY; MonoidalCategory.IsInvertible K) :
    letI := mX; MonoidalCategory.IsInvertible
      ((pullbackEquivMod f).functor.mapDerivedCategory.obj K) :=
  isInvertible_mapDerivedCategory_of_isInvertible (modTensor Y) (modTensor X)
    (pullbackEquivMod f) (pullbackTensorIso f) (pullbackTensorIso_naturality_left f)
    (pullbackTensorIso_naturality_right f) mY mX bX cmpY cmpX unitε K hK

/-- **`f^*` preserves invertibility on the derived categories**, at the symmetric monoidal
structure of [Stacks, Tag 0FPT] on both sides: if `K` is an invertible object of `D(𝒪_Y)` then
`f^*K` is an invertible object of `D(𝒪_X)`. -/
theorem isInvertible_pullback
    (K : DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf Y)))
    (hK : letI := derivedMonoidal (schemeRingSheaf Y); MonoidalCategory.IsInvertible K) :
    letI := derivedMonoidal (schemeRingSheaf X)
    MonoidalCategory.IsInvertible
      ((pullbackEquivMod f).functor.mapDerivedCategory.obj K) :=
  isInvertible_pullback_obj f
    (derivedMonoidal (schemeRingSheaf Y)) (derivedMonoidal (schemeRingSheaf X))
    (derivedSymmetric (schemeRingSheaf X)).toBraidedCategory
    (fun A B => ((derivedTensorBifunctorIso (schemeRingSheaf Y)).app A).app B)
    (fun A B => ((derivedTensorBifunctorIso (schemeRingSheaf X)).app A).app B)
    ((pullbackEquivMod f).functor.mapDerivedCategory.mapIso
        (canonicalUnitIso (schemeRingSheaf Y)) ≪≫
      pullbackDerivedUnitIso f ≪≫ (canonicalUnitIso (schemeRingSheaf X)).symm)
    K hK

/-- **Restriction along an isomorphism of schemes is isomorphic to the pullback, on derived
categories**: `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` on derived
categories. -/
def restrictFunctorDerivedIsoPullback :
    (restrictMod f).mapDerivedCategory ≅ (pullbackEquivMod f).functor.mapDerivedCategory :=
  Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso
    (restrictMod f) (pullbackMod f) (Scheme.Modules.restrictFunctorIsoPullback f)

/-- **Restriction along an isomorphism of schemes preserves invertibility on the derived
categories**, at the symmetric monoidal structure of [Stacks, Tag 0FPT] on both sides: if `K`
is an invertible object of `D(𝒪_Y)` then so is its restriction along `f`. -/
theorem isInvertible_restrictFunctor
    (K : DerivedCategory (_root_.SheafOfModules.{u} (modRingSheaf Y)))
    (hK : letI := derivedMonoidal (schemeRingSheaf Y); MonoidalCategory.IsInvertible K) :
    letI := derivedMonoidal (schemeRingSheaf X)
    MonoidalCategory.IsInvertible ((restrictMod f).mapDerivedCategory.obj K) :=
  let _ := derivedMonoidal (schemeRingSheaf X)
  MonoidalCategory.isInvertible_of_iso
    ((restrictFunctorDerivedIsoPullback f).app K).symm (isInvertible_pullback f K hK)

end Derived

end Stacks.SheafOfModules.PullbackIsoTensor

end
