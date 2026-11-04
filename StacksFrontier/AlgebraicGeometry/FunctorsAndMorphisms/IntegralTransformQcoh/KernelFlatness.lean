module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.Sets.OpenCover
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.FunctorsBetweenCategories.TensorFunctorExactness
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Equivalence
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.RightExact
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria

/-!
# Flatness of the kernel of an exact integral transform

Let `R` be a commutative ring and let `X` and `Y` be schemes over `R`.  A quasi-coherent module
`K` on `X ×_R Y` has an integral transform `F ↦ pr_{2,*}(pr_1^* F ⊗ K)` from quasi-coherent
modules on `X` to quasi-coherent modules on `Y`, and by Tag 0FZD every `R`-linear right exact
functor commuting with arbitrary direct sums arises this way when `X` is affine.  This file
proves that the kernel of such a functor is flat over `X` as soon as the functor is exact, in
the case where `Y` is affine as well.

With `X` and `Y` both affine the assertion is the geometric reading of Tag 0GNX.  Modules over
the ring of global functions of an affine scheme are equivalent to its quasi-coherent modules by
Tag 01I8, and the equivalence is set up here with the global sections as its inverse.  Through
it the integral transform becomes the functor of tensoring with the module of global sections of
the kernel: both functors are right exact and commute with arbitrary direct sums, and they agree
on the structure sheaf equivariantly for the global functions of `X`, which determines a functor
of that kind on the quasi-coherent modules of an affine scheme.  Tensoring with a module is left
exact exactly when the module is flat, so exactness of the transform is flatness of the global
sections of the kernel over `Γ(X, ⊤)`, and that is flatness of the kernel over `X` by the
affine-open criterion of Tag 01U4 applied to the one-element covers by the whole space.

## Main definitions

* `AlgebraicGeometry.qcohPushforward`: the direct image of quasi-coherent modules along a
  quasi-compact quasi-separated morphism.
* `AlgebraicGeometry.qcohPushforwardEquivOfIso`: the direct image of quasi-coherent modules
  along an isomorphism of schemes, as an equivalence of categories.
* `AlgebraicGeometry.affineGammaEquivalence`: for an affine scheme, the equivalence between
  modules over its ring of global functions and its quasi-coherent modules, with the global
  sections as its inverse.

## Main results

* `AlgebraicGeometry.isFlatOver_of_flat_sections_top`: for a morphism of affine schemes,
  flatness of the global sections of a quasi-coherent module over the ring of global functions
  of the target is flatness of that module over the target.
* `AlgebraicGeometry.isFlatOver_of_exactFunctor_affine`: Tag 0FZG in the case of Tag 0FZD
  with the target `Y` affine as well.

## Implementation notes

`AlgebraicGeometry.overSectionsAlgebra` is the `R`-algebra structure on the ring of global
functions of a scheme over `R`; it is registered as a local instance so that tensor products
over `R` of such rings can be written.  The `Γ(X, ⊤)`-module structure on the global sections
of the kernel cannot be a local instance, since the morphism it restricts scalars along does not
appear in its type; it is therefore written out, in the spelling that the affine-open criterion
of Tag 01U4 uses, so that the flatness statement produced here is the one that criterion
consumes.

The canonical module structure that does appear, the one of the sections of the kernel over the
sections of the structure sheaf of `X ×_R Y`, is Mathlib's, but Mathlib declares it for a module
of type `S.Modules` while the kernel is given as an object of the full subcategory of
quasi-coherent sheaves of modules.  `AlgebraicGeometry.qcohSectionsModule` names that instance
at the latter spelling and is registered as a local instance, so that instance search has one
candidate for it and no definition has to be made reducible to reach it.

`AlgebraicGeometry.affineGammaEquivalence` is built from the direct image along
`AlgebraicGeometry.Scheme.isoSpec` rather than from the inverse image along its inverse, because
the sections of a direct image over `⊤` are literally the sections of the original module over
`⊤` and the induced map of sections is literally the original one.  That is what makes the
inverse of the equivalence computable on morphisms, which the comparison on the structure sheaf
needs: there the transform of the kernel is the direct image of the kernel along the second
projection (`AlgebraicGeometry.IntegralTransformQcoh.integralTransformUnitIso`) and
multiplication by a global function of `X` becomes multiplication by its pullback
(`AlgebraicGeometry.IntegralTransformQcoh.integralTransformUnitIso_sectionScalar`), so both
sides of the comparison are the global sections of the kernel with the same action of
`Γ(X, ⊤)`.

The comparison is made in abelian groups rather than in modules.  Both functors are then
literally valued in the same abelian group on the structure sheaf, the two module structures
over `Γ(Y, ⊤)` and over `Γ(X, ⊤)` play no role, and flatness is read off through
`Module.Flat.iff_preservesFiniteLimits_tensorRight`, the forgetful functor from modules to
abelian groups both preserving and reflecting finite limits.

## References

* [Stacks Project, Tag 0FZG](https://stacks.math.columbia.edu/tag/0FZG)
* [Stacks Project, Tag 0GNX](https://stacks.math.columbia.edu/tag/0GNX)
* [Stacks Project, Tag 0FZD](https://stacks.math.columbia.edu/tag/0FZD)
* [Stacks Project, Tag 0FZB](https://stacks.math.columbia.edu/tag/0FZB)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Tag 01U4](https://stacks.math.columbia.edu/tag/01U4)
-/

@[expose] public noncomputable section

-- `AlgebraicGeometry` is not opened: everything below is inside that namespace already, and
-- opening it as well would demote its names from taking precedence to competing on equal terms
-- with the other opened namespaces, so a later `AlgebraicGeometry.pullback` or the like would
-- make a name in this file ambiguous rather than resolve it.
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
open AlgebraicGeometry.IntegralTransformQcoh
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The module structure on the sections of a quasi-coherent `𝒪_S`-module over the sections of
the structure sheaf of `S`, for a module presented as an object of the full subcategory of
quasi-coherent sheaves of modules.

Mathlib declares that module structure for `M : S.Modules`, and `AlgebraicGeometry.Scheme.Modules`
is a definition, so instance search does not see through `K.obj : SheafOfModules S.ringCatSheaf`
to it.  Naming it here, and registering the name as a local instance, is what lets the file
elaborate; the alternative of making `AlgebraicGeometry.Scheme.Modules` reducible leaves the
elaboration at the mercy of whatever other paths instance search can then find.  It is
`instance_reducible`, so it is interchangeable with Mathlib's instance for unification. -/
@[instance_reducible]
def qcohSectionsModule {S : Scheme.{u}}
    (K : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory) (U : S.Opens) :
    Module Γ(S, U) Γ(K.obj, U) :=
  let M : S.Modules := K.obj
  inferInstanceAs (Module Γ(S, U) Γ(M, U))

attribute [local instance] qcohSectionsModule

/-- The `R`-algebra structure on the ring of global functions of a scheme over `R`, through the
global sections of the structure morphism. -/
abbrev overSectionsAlgebra (R : Type u) [CommRing R] (X : Over (Spec (.of R))) :
    Algebra R Γ(X.left, ⊤) :=
  (((Scheme.ΓSpecIso (.of R)).inv ≫ X.hom.appTop)).hom.toAlgebra

attribute [local instance] overSectionsAlgebra

/-- **Flatness over an affine target from the global sections.**  For a morphism `f : Z ⟶ S` of
affine schemes and a quasi-coherent module `G` on `Z`, flatness of the global sections of `G` as
a module over the ring of global functions of `S` is flatness of `G` over `S`.  This is the
affine-open criterion of Tag 01U4 at the one-element covers of `S` and of `Z` by the whole
space. -/
theorem isFlatOver_of_flat_sections_top {S Z : Scheme.{u}} (f : Z ⟶ S) [IsAffine S] [IsAffine Z]
    (G : Z.Modules) [G.IsQuasicoherent]
    (h : @Module.Flat Γ(S, ⊤) Γ(G, ⊤) _ _
      (Module.compHom Γ(G, ⊤) (f.appLE ⊤ ⊤ le_rfl).hom)) :
    IsFlatOver f.toLRSHom.toShHom G := by
  refine ((isFlatOver_tfae f G).out 4 1).mp ?_
  refine ⟨PUnit.{u + 1}, fun _ => ⊤, IsOpenCover.mk iSup_const,
    fun _ => isAffineOpen_top S, ?_⟩
  intro _
  refine ⟨PUnit.{u + 1}, fun _ => ⊤, iSup_const.trans (f.preimage_top).symm,
    fun _ => isAffineOpen_top Z, ?_⟩
  intro _
  exact h

/-- **Direct image of quasi-coherent modules.**  Along a quasi-compact quasi-separated morphism
of schemes the direct image of a quasi-coherent module is quasi-coherent, by Tag 01LC, so direct
image restricts to a functor between the categories of quasi-coherent modules. -/
def qcohPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Scheme.Modules.pushforward f)
    (fun M => @pushforward_isQuasicoherent _ _ f _ _ M.obj M.property)

/-- The direct image of quasi-coherent modules along an isomorphism of schemes is an equivalence
of categories, with the direct image along the inverse isomorphism as its inverse. -/
def qcohPushforwardEquivOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
      (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory :=
  CategoryTheory.Equivalence.mk (qcohPushforward e.hom) (qcohPushforward e.inv)
    (NatIso.ofComponents
      (fun M => ObjectProperty.isoMk _
        ((Scheme.Modules.pushforwardEquivOfIso e).unitIso.app M.obj))
      (fun f => ObjectProperty.hom_ext _
        ((Scheme.Modules.pushforwardEquivOfIso e).unitIso.hom.naturality f.hom)))
    (NatIso.ofComponents
      (fun M => ObjectProperty.isoMk _
        ((Scheme.Modules.pushforwardEquivOfIso e).counitIso.app M.obj))
      (fun f => ObjectProperty.hom_ext _
        ((Scheme.Modules.pushforwardEquivOfIso e).counitIso.hom.naturality f.hom)))

/-- **Stacks Project, Tag 01I8 on an affine scheme.**  For an affine scheme `X`, modules over
its ring of global functions are equivalent to its quasi-coherent modules.  The inverse of the
equivalence is the global sections: it is the Spec--Γ dictionary composed with the direct image
along `AlgebraicGeometry.Scheme.isoSpec`, and the sections of a direct image over `⊤` are the
sections of the original module over `⊤`. -/
def affineGammaEquivalence (X : Scheme.{u}) [IsAffine X] :
    ModuleCat.{u} Γ(X, ⊤) ≌ (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory :=
  tildeEquiv.trans (qcohPushforwardEquivOfIso X.isoSpec.symm)

/-- The structure sheaf of a scheme, as an object of the category of its quasi-coherent
modules. -/
private abbrev unitQcoh (Z : Scheme.{u}) :
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory :=
  ⟨SheafOfModules.unit Z.ringCatSheaf,
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit Z⟩

/-- On global sections, multiplication by a global function of the structure sheaf is
multiplication by that function. -/
private lemma sectionScalar_app_top (Z : Scheme.{u}) (c : Γ(Z, ⊤)) (M : Z.Modules)
    (x : Γ(M, ⊤)) :
    (sectionScalar Z c M).val.app (op ⊤) x = c • x := by
  show (Z.presheaf.map (⊤ : Z.Opens).leTop.op) c • x = c • x
  congr 1
  rw [show ((⊤ : Z.Opens).leTop).op = 𝟙 (op (⊤ : Z.Opens)) from Subsingleton.elim _ _,
    Z.presheaf.map_id]
  rfl

/-- The global sections of the structure sheaf of an affine scheme are its ring of global
functions, as a module over itself. -/
private def unitSectionsIso (X : Scheme.{u}) [IsAffine X] :
    (affineGammaEquivalence X).inverse.obj (unitQcoh X) ≅ ModuleCat.of Γ(X, ⊤) Γ(X, ⊤) :=
  @LinearEquiv.toModuleIso Γ(X, ⊤) _
    (((affineGammaEquivalence X).inverse.obj (unitQcoh X) : Type u)) Γ(X, ⊤)
    _ _ ((affineGammaEquivalence X).inverse.obj (unitQcoh X)).isModule _
    (specΓSectionsEquiv X (SheafOfModules.unit X.ringCatSheaf))

/-- The global sections of quasi-coherent modules on an affine scheme, as a functor to abelian
groups. -/
private abbrev qcohSectionsAddFunctor (Z : Scheme.{u}) [IsAffine Z] :
    (SheafOfModules.isQuasicoherent Z.ringCatSheaf).FullSubcategory ⥤ AddCommGrpCat.{u} :=
  (affineGammaEquivalence Z).inverse ⋙ forget₂ (ModuleCat.{u} Γ(Z, ⊤)) AddCommGrpCat.{u}

/-- Multiplication by a global function, as an endomorphism of the structure sheaf in the
category of quasi-coherent modules. -/
private abbrev unitScalarHom (Z : Scheme.{u}) (s : Γ(Z, ⊤)) : unitQcoh Z ⟶ unitQcoh Z :=
  ObjectProperty.homMk (sectionScalar Z s (SheafOfModules.unit Z.ringCatSheaf))

section Affine

/-- Pasting two commutative squares side by side gives a commutative square for the composite. -/
private lemma comp_comm_of_comm_squares {C : Type*} [Category C] {A B D : C} {f : A ⟶ A}
    {g : A ⟶ B} {f' : B ⟶ B} {k : B ⟶ D} {f'' : D ⟶ D} (h1 : f ≫ g = g ≫ f')
    (h2 : f' ≫ k = k ≫ f'') : f ≫ g ≫ k = (g ≫ k) ≫ f'' := by
  rw [← Category.assoc, h1, Category.assoc, h2, Category.assoc]

variable (R : Type u) [CommRing R] (X Y : Over (Spec (.of R)))
  [IsAffine X.left] [IsAffine Y.left]
  (K : (SheafOfModules.isQuasicoherent (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)

/-- The direct image of the kernel along the second projection, as a quasi-coherent module on
`Y`. -/
private abbrev kernelPushforwardQcoh :
    (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory :=
  letI : IsAffineHom (pullback.snd X.hom Y.hom) := isAffineHom_pullback_snd R X Y
  ⟨(Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).obj K.obj,
    @pushforward_isQuasicoherent _ _ (pullback.snd X.hom Y.hom) _ _ K.obj K.property⟩

/-- Multiplication by the pullback of a global function of `X`, as an endomorphism of the direct
image of the kernel along the second projection. -/
private abbrev kernelScalarHom (s : Γ(X.left, ⊤)) :
    kernelPushforwardQcoh R X Y K ⟶ kernelPushforwardQcoh R X Y K :=
  ObjectProperty.homMk ((Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
    (sectionScalar (pullback X.hom Y.hom) ((pullback.fst X.hom Y.hom).appTop s) K.obj))

/-- The integral transform of the kernel, at the structure sheaf of `X`, is the direct image of
the kernel along the second projection. -/
private def transformUnitQcohIso :
    (quasicoherentIntegralTransform R X Y K).obj (unitQcoh X.left) ≅
      kernelPushforwardQcoh R X Y K :=
  ObjectProperty.isoMk _
    ((quasicoherentIntegralTransformData R X Y K).comparison.app (unitQcoh X.left) ≪≫
      integralTransformUnitIso R X Y K.obj)

omit [IsAffine Y.left] in
/-- At the structure sheaf of `X`, the integral transform takes multiplication by a global
function of `X` to multiplication by its pullback to `X ×_R Y`. -/
private lemma transformUnitQcohIso_sectionScalar (s : Γ(X.left, ⊤)) :
    (quasicoherentIntegralTransform R X Y K).map (unitScalarHom X.left s) ≫
      (transformUnitQcohIso R X Y K).hom =
    (transformUnitQcohIso R X Y K).hom ≫ kernelScalarHom R X Y K s := by
  apply ObjectProperty.hom_ext
  have h1 := (quasicoherentIntegralTransformData R X Y K).comparison.hom.naturality
    (unitScalarHom X.left s)
  have h2 := integralTransformUnitIso_sectionScalar R X Y K.obj s
  show ((quasicoherentIntegralTransformData R X Y K).functor ⋙
        (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).ι).map (unitScalarHom X.left s) ≫
      ((quasicoherentIntegralTransformData R X Y K).comparison.hom.app (unitQcoh X.left) ≫
        (integralTransformUnitIso R X Y K.obj).hom) =
    ((quasicoherentIntegralTransformData R X Y K).comparison.hom.app (unitQcoh X.left) ≫
        (integralTransformUnitIso R X Y K.obj).hom) ≫
      (Scheme.Modules.pushforward (pullback.snd X.hom Y.hom)).map
        (sectionScalar (pullback X.hom Y.hom) ((pullback.fst X.hom Y.hom).appTop s) K.obj)
  exact comp_comm_of_comm_squares h1 h2

/-- The global sections of the kernel, as a module over the ring of global functions of `X`, in
the spelling that the affine-open flatness criterion consumes. -/
private abbrev kernelSourceModule : ModuleCat.{u} Γ(X.left, ⊤) :=
  (ModuleCat.restrictScalars ((pullback.fst X.hom Y.hom).appLE ⊤ ⊤ le_rfl).hom).obj
    (ModuleCat.of Γ(pullback X.hom Y.hom, ⊤) Γ(K.obj, ⊤))

/-- The global sections of the integral transform of the kernel, as a functor from the
quasi-coherent modules on `X` to abelian groups. -/
private abbrev transformSections :
    (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤ AddCommGrpCat.{u} :=
  quasicoherentIntegralTransform R X Y K ⋙ qcohSectionsAddFunctor Y.left

/-- Tensoring the global sections of a quasi-coherent module on `X` with the global sections of
the kernel, as a functor to abelian groups. -/
private abbrev tensorSections :
    (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤ AddCommGrpCat.{u} :=
  (affineGammaEquivalence X.left).inverse ⋙
    MonoidalCategory.tensorRight (kernelSourceModule R X Y K) ⋙
    forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u}

/-- The unit constraint identifying the global sections of the kernel with their tensor product
with the global sections of the structure sheaf of `X`, as an isomorphism. -/
private abbrev generatorUnitorIso :
    kernelSourceModule R X Y K ≅
      (MonoidalCategory.tensorRight (kernelSourceModule R X Y K)).obj
        ((affineGammaEquivalence X.left).inverse.obj (unitQcoh X.left)) :=
  (MonoidalCategory.leftUnitor (kernelSourceModule R X Y K)).symm ≪≫
    (MonoidalCategory.tensorRight (kernelSourceModule R X Y K)).mapIso
      (unitSectionsIso X.left).symm

/-- The unit constraint identifying the global sections of the kernel with their tensor product
with the global sections of the structure sheaf of `X`. -/
private abbrev generatorUnitor :
    kernelSourceModule R X Y K ⟶
      (MonoidalCategory.tensorRight (kernelSourceModule R X Y K)).obj
        ((affineGammaEquivalence X.left).inverse.obj (unitQcoh X.left)) :=
  (generatorUnitorIso R X Y K).hom

/-- At the structure sheaf of `X`, the global sections of the integral transform of the kernel
are the global sections of the kernel, tensored with the global sections of the structure
sheaf. -/
private def generatorIso :
    (transformSections R X Y K).obj (unitQcoh X.left) ≅
      (tensorSections R X Y K).obj (unitQcoh X.left) :=
  (qcohSectionsAddFunctor Y.left).mapIso (transformUnitQcohIso R X Y K) ≪≫
    (forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u}).mapIso (generatorUnitorIso R X Y K)

omit [IsAffine Y.left] in
/-- The unit constraint sends a global section of the kernel to its tensor product with the
unit global function of `X`. -/
private lemma generatorUnitor_apply (z : ((kernelSourceModule R X Y K) : Type u)) :
    (generatorUnitor R X Y K).hom z =
      TensorProduct.tmul Γ(X.left, ⊤)
        ((unitSectionsIso X.left).inv.hom (1 : Γ(X.left, ⊤))) z := rfl

/-- The unit constraint intertwines multiplication by the pullback of a global function of `X`
on the global sections of the kernel with multiplication by that function on the first factor of
the tensor product. -/
private lemma generatorUnitor_sectionScalar (s : Γ(X.left, ⊤)) :
    (qcohSectionsAddFunctor Y.left).map (kernelScalarHom R X Y K s) ≫
      (forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u}).map
        (generatorUnitor R X Y K) =
      (forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u}).map
          (generatorUnitor R X Y K) ≫
        (tensorSections R X Y K).map (unitScalarHom X.left s) := by
  apply AddCommGrpCat.hom_ext
  ext y
  show (generatorUnitor R X Y K).hom
      ((sectionScalar (pullback X.hom Y.hom)
        ((pullback.fst X.hom Y.hom).appTop s) K.obj).val.app (op ⊤) y) =
    ((MonoidalCategory.tensorRight (kernelSourceModule R X Y K)).map
        ((affineGammaEquivalence X.left).inverse.map (unitScalarHom X.left s))).hom
      ((generatorUnitor R X Y K).hom y)
  refine Eq.trans (congrArg (ModuleCat.Hom.hom (generatorUnitor R X Y K))
    (sectionScalar_app_top (pullback X.hom Y.hom)
      ((pullback.fst X.hom Y.hom).appTop s) K.obj y)) ?_
  refine Eq.trans (generatorUnitor_apply R X Y K _) ?_
  refine Eq.trans ?_ (congrArg (ModuleCat.Hom.hom
      ((MonoidalCategory.tensorRight (kernelSourceModule R X Y K)).map
        ((affineGammaEquivalence X.left).inverse.map (unitScalarHom X.left s))))
    (generatorUnitor_apply R X Y K y)).symm
  refine Eq.trans ?_ (ModuleCat.MonoidalCategory.whiskerRight_apply
    ((affineGammaEquivalence X.left).inverse.map (unitScalarHom X.left s))
    (kernelSourceModule R X Y K)
    ((unitSectionsIso X.left).inv.hom (1 : Γ(X.left, ⊤))) y).symm
  have hg : (ConcreteCategory.hom ((affineGammaEquivalence X.left).inverse.map
        (unitScalarHom X.left s)))
      ((unitSectionsIso X.left).inv.hom (1 : Γ(X.left, ⊤))) =
      s • ((unitSectionsIso X.left).inv.hom (1 : Γ(X.left, ⊤))) := by
    refine Eq.trans (sectionScalar_app_top X.left s (SheafOfModules.unit X.left.ringCatSheaf)
      ((unitSectionsIso X.left).inv.hom (1 : Γ(X.left, ⊤)))) ?_
    exact ((specΓSectionsEquiv X.left (SheafOfModules.unit X.left.ringCatSheaf)).map_smul s
      ((unitSectionsIso X.left).inv.hom (1 : Γ(X.left, ⊤)))).symm
  refine Eq.trans ?_ (congrArg (fun w => TensorProduct.tmul Γ(X.left, ⊤) w
    (show ((kernelSourceModule R X Y K) : Type u) from y)) hg).symm
  have hconv : (pullback.fst X.hom Y.hom).appTop.hom s • (show Γ(K.obj, ⊤) from y) =
      ((pullback.fst X.hom Y.hom).appLE ⊤ ⊤ le_rfl).hom s • (show Γ(K.obj, ⊤) from y) :=
    congrArg (fun (k : Γ(X.left, ⊤) ⟶ Γ(pullback X.hom Y.hom, ⊤)) =>
      k.hom s • (show Γ(K.obj, ⊤) from y)) (Scheme.Hom.appLE_eq_app _).symm
  refine Eq.trans (congrArg (fun z => TensorProduct.tmul Γ(X.left, ⊤)
    ((unitSectionsIso X.left).inv.hom (1 : Γ(X.left, ⊤)))
    (show ((kernelSourceModule R X Y K) : Type u) from z)) hconv) ?_
  exact (TensorProduct.smul_tmul s ((unitSectionsIso X.left).inv.hom (1 : Γ(X.left, ⊤)))
    (show ((kernelSourceModule R X Y K) : Type u) from y)).symm

/-- The comparison at the structure sheaf is equivariant for multiplication by a global function
of `X`. -/
private lemma generatorIso_sectionScalar (s : Γ(X.left, ⊤)) :
    (transformSections R X Y K).map (unitScalarHom X.left s) ≫ (generatorIso R X Y K).hom =
      (generatorIso R X Y K).hom ≫
        (tensorSections R X Y K).map (unitScalarHom X.left s) := by
  have e1 : (qcohSectionsAddFunctor Y.left).map
        ((quasicoherentIntegralTransform R X Y K).map (unitScalarHom X.left s)) ≫
        (qcohSectionsAddFunctor Y.left).map (transformUnitQcohIso R X Y K).hom =
      (qcohSectionsAddFunctor Y.left).map (transformUnitQcohIso R X Y K).hom ≫
        (qcohSectionsAddFunctor Y.left).map (kernelScalarHom R X Y K s) := by
    rw [← Functor.map_comp, ← Functor.map_comp, transformUnitQcohIso_sectionScalar]
  show (qcohSectionsAddFunctor Y.left).map
        ((quasicoherentIntegralTransform R X Y K).map (unitScalarHom X.left s)) ≫
      ((qcohSectionsAddFunctor Y.left).map (transformUnitQcohIso R X Y K).hom ≫
        (forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u}).map
          (generatorUnitor R X Y K)) =
    ((qcohSectionsAddFunctor Y.left).map (transformUnitQcohIso R X Y K).hom ≫
        (forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u}).map
          (generatorUnitor R X Y K)) ≫
      (tensorSections R X Y K).map (unitScalarHom X.left s)
  exact comp_comm_of_comm_squares e1 (generatorUnitor_sectionScalar R X Y K s)

/-- The comparison at the structure sheaf is equivariant for every endomorphism of the structure
sheaf: each of them is multiplication by a global function. -/
private lemma generatorIso_equivariant (a : End (unitQcoh X.left)) :
    (transformSections R X Y K).map a ≫ (generatorIso R X Y K).hom =
      (generatorIso R X Y K).hom ≫ (tensorSections R X Y K).map a := by
  obtain ⟨s, hs⟩ := sectionScalar_unit_surjective X.left a.hom
  obtain rfl : a = unitScalarHom X.left s := ObjectProperty.hom_ext _ hs.symm
  exact generatorIso_sectionScalar R X Y K s

/-- On an affine scheme `X`, the global sections of the integral transform of the kernel,
precomposed with the equivalence of Tag 01I8, are tensoring with the global sections of the
kernel. -/
private lemma nonempty_transformSections_iso_tensor :
    Nonempty ((affineGammaEquivalence X.left).functor ⋙ transformSections R X Y K ≅
      MonoidalCategory.tensorRight (kernelSourceModule R X Y K) ⋙
        forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u}) := by
  have := preservesFiniteColimits_quasicoherentIntegralTransform R X Y K
  have : PreservesColimitsOfSize.{u, u}
      (MonoidalCategory.tensorRight (kernelSourceModule R X Y K)) :=
    inferInstanceAs (PreservesColimitsOfSize.{u, u}
      ((MonoidalCategory.tensoringRight (ModuleCat.{u} Γ(X.left, ⊤))).obj
        (kernelSourceModule R X Y K)))
  have hFd : ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (transformSections R X Y K) := fun I => by
    have := quasicoherentIntegralTransform_preservesDirectSums R X Y K I
    infer_instance
  have hGd : ∀ I : Type u, PreservesColimitsOfShape (Discrete I)
      (tensorSections R X Y K) := fun _ => inferInstance
  obtain ⟨iso⟩ := affineFunctorIsoOfUnitIso X.left
    (transformSections R X Y K) (tensorSections R X Y K) hFd hGd
    (generatorIso R X Y K) (generatorIso_equivariant R X Y K)
  have h1 : MonoidalCategory.tensorRight (kernelSourceModule R X Y K) ⋙
      forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u} ≅
      (affineGammaEquivalence X.left).functor ⋙ tensorSections R X Y K :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (affineGammaEquivalence X.left).unitIso
        (MonoidalCategory.tensorRight (kernelSourceModule R X Y K) ⋙
          forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u}) ≪≫
      Functor.associator _ _ _
  exact ⟨Functor.isoWhiskerLeft (affineGammaEquivalence X.left).functor iso ≪≫ h1.symm⟩

/-- **The case of Tag 0FZG with `X` and `Y` affine.**  In the situation of Tag 0FZD with `X`
and `Y` affine, if the `R`-linear right exact direct-sum-preserving functor `F` is exact, then
the quasi-coherent module `K` on `X ×_R Y` corresponding to it is flat over `X`.

The correspondence between `F` and `K` is the isomorphism `hFK`.  Through the equivalence of Tag
01I8 between modules over the ring of global functions of an affine scheme and its quasi-coherent
modules, whose inverse is the global sections, the integral transform of `K` becomes the functor
of tensoring with the global sections of `K`: the two agree on the structure sheaf of `X`,
equivariantly for the global functions of `X`, and that determines a right exact
direct-sum-preserving functor out of the quasi-coherent modules on an affine scheme.  Exactness
of `F` therefore makes the global sections of `K` flat over `Γ(X, ⊤)`, by the criterion of Tag
0GNX, and that is flatness of `K` over `X` by the affine-open criterion of Tag 01U4. -/
theorem isFlatOver_of_exactFunctor_affine (R : Type u) [CommRing R]
    (X Y : Over (Spec (.of R))) [IsAffine X.left] [IsAffine Y.left]
    (K : (SheafOfModules.isQuasicoherent
      (pullback X.hom Y.hom).ringCatSheaf).FullSubcategory)
    (F : (SheafOfModules.isQuasicoherent X.left.ringCatSheaf).FullSubcategory ⥤
      (SheafOfModules.isQuasicoherent Y.left.ringCatSheaf).FullSubcategory)
    (hFK : F ≅ quasicoherentIntegralTransform R X Y K)
    (hF : exactFunctor _ _ F) :
    IsFlatOver (pullback.fst X.hom Y.hom).toLRSHom.toShHom K.obj := by
  have hlim : PreservesFiniteLimits (quasicoherentIntegralTransform R X Y K) :=
    ((exactFunctor_iff _).mp ((exactFunctor _ _).prop_of_iso hFK hF)).1
  obtain ⟨h2⟩ := nonempty_transformSections_iso_tensor R X Y K
  have hcomp : PreservesFiniteLimits ((affineGammaEquivalence X.left).functor ⋙
      transformSections R X Y K) := by infer_instance
  have hforget : PreservesFiniteLimits
      (MonoidalCategory.tensorRight (kernelSourceModule R X Y K) ⋙
        forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u}) :=
    preservesFiniteLimits_of_natIso h2
  have : K.obj.IsQuasicoherent := K.property
  exact isFlatOver_of_flat_sections_top (pullback.fst X.hom Y.hom) K.obj
    ((Module.Flat.iff_preservesFiniteLimits_tensorRight (kernelSourceModule R X Y K)).mpr
      (preservesFiniteLimits_of_reflects_of_preserves _
        (forget₂ (ModuleCat.{u} Γ(X.left, ⊤)) AddCommGrpCat.{u})))

end Affine

end AlgebraicGeometry

end
