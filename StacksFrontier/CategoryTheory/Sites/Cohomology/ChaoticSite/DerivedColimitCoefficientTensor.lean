module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.DerivedColimitPreservesColimits

/-!
# Derived lower shriek and the derived tensor product with a new coefficient ring

Let `C` be a small category with the chaotic topology, so that a sheaf of rings on `C` is a
presheaf of rings `O` and a sheaf of `O`-modules is a presheaf of `O`-modules
(`Stacks.ChaoticSite.moduleSheafPresheafEquivalence`). Let `a : O ⟶ O'` be a map of presheaves of
rings. This file assembles the three functors that the statement of [Stacks, Tag 08RX] is about:

* `Lπ_! : D(Mod(O)) ⥤ D(Ab)`, the composite of the exact forgetful functor to abelian presheaves
  with the derived colimit over `Cᵒᵖ` of Stacks 08Q6;
* `- ⊗^L_O O' : D(Mod(O)) ⥤ D(Mod(O'))`, the total left derived functor of extension of scalars
  along `a`, which exists unconditionally because extension of scalars is a right exact left
  adjoint out of a category with enough projectives (Stacks 0794 at the projective objects);
* the canonical comparison `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_O O')`, obtained by applying `Lπ_!` to the unit
  `K ⟶ K ⊗^L_O O'` of the derived change-of-rings adjunction and then forgetting the `O'`-module
  structure, which does not change the underlying abelian presheaf.

Tag 08RX asserts that the comparison is invertible when `C` admits a cosimplicial point
resolution and `Lπ_!(O) ⟶ Lπ_!(O')` is invertible. **That assertion is not proved here**; what is
proved here is that the three functors exist, that the comparison exists, and the two
compatibilities of the generators with change of coefficients that the source's proof uses.

## Main definitions

* `Stacks.ChaoticSite.abelianDerivedColimitOfModules`: `Lπ_! : D(Mod(O)) ⥤ D(Ab)`.
* `Stacks.ChaoticSite.extendScalars` and `Stacks.ChaoticSite.changeOfRingsAdjunction`: extension
  of scalars along `a`, left adjoint to restriction of scalars.
* `Stacks.ChaoticSite.derivedExtendScalars`: `- ⊗^L_O O' : D(Mod(O)) ⥤ D(Mod(O'))`, with its
  comparison `derivedExtendScalarsCounit` and its adjunction `derivedExtendScalarsAdjunction`.
* `Stacks.ChaoticSite.derivedColimitTensorComparison`: the canonical comparison
  `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_O O')` whose invertibility is the conclusion of Tag 08RX.

## Main results

* `Stacks.ChaoticSite.restrictScalarsDerivedColimitIso`: restriction of scalars along `a` does
  not change derived lower shriek, since it does not change the underlying abelian presheaf.
* `Stacks.ChaoticSite.derivedExtendScalars_isTriangulated` and
  `Stacks.ChaoticSite.derivedExtendScalars_preservesColimitsOfSize`: the derived tensor product
  is exact and commutes with colimits, both because it is a left adjoint.
* `Stacks.ChaoticSite.freeCompExtendScalarsIso`: **`j_{W!}O_W ⊗_O O' = j_{W!}O'_W`** in the form
  the chaotic site gives it — extension of scalars takes the free `O`-module on a presheaf of
  types to the free `O'`-module on it, by uniqueness of left adjoints. At the representable
  presheaf of an object `W` the free module is the extension by zero of the structure sheaf of
  the slice `C/W`, the generator of the source's proof.
* `Stacks.ChaoticSite.freeYonedaProjective` (in
  `StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedLowerShriek.lean`) says that
  generator is projective, so no higher derived functors of extension of scalars enter at it.

## Implementation notes

The comparison is built from the unit of the *derived* change-of-rings adjunction rather than
from the underived unit followed by a derived-functor universal property: both factors of
`Lπ_!` are already available as functors on derived categories, and the only identification
needed is `restrictScalars a ⋙ toPresheaf O = toPresheaf O'`, which holds by `rfl`. That
identification is promoted to the derived categories by uniqueness of lifts through the
localisation `DerivedCategory.Q`, which is what `restrictScalarsToPresheafLifting` and
`CategoryTheory.Localization.liftNatIso` do; the same technique is used for the analogous
comparison of Tag 08Q8 in
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedChangeOfCoefficients.lean`.

All universes collapse to the universe `u` of the site: that is the convention under which
`Stacks.CategoryHomology.presheafEnoughProjectives` and
`PresheafOfModules.enoughProjectives` supply the hypotheses of Stacks 0794.

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 08Q6](https://stacks.math.columbia.edu/tag/08Q6)
* [Stacks Project, Tag 09CZ](https://stacks.math.columbia.edu/tag/09CZ)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CategoryHomology

universe w' w u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.ChaoticSite

variable {C : Type u} [SmallCategory C]

/-- **Derived lower shriek with coefficients in a presheaf of rings, read on abelian groups**:
`Lπ_! : D(Mod(O)) ⥤ D(Ab)`, the composite of the exact functor forgetting the module structure
with the derived colimit over `Cᵒᵖ` of Stacks 08Q6. This is the functor both sides of
[Stacks, Tag 08RX] are formed with. -/
abbrev abelianDerivedColimitOfModules (O : Cᵒᵖ ⥤ RingCat.{u}) :
    DerivedCategory (PresheafOfModules.{u} O) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  (PresheafOfModules.toPresheaf O).mapDerivedCategory ⋙ totalDerivedColimit C AddCommGrpCat.{u}

variable {O O' : Cᵒᵖ ⥤ RingCat.{u}} (a : O ⟶ O')

/-- Extension of scalars along a map of presheaves of rings, `M ↦ M ⊗_O O'`. -/
abbrev extendScalars : PresheafOfModules.{u} O ⥤ PresheafOfModules.{u} O' :=
  (PresheafOfModules.restrictScalars.{u} a).leftAdjoint

/-- **Stacks 03CZ for presheaves of modules**: extension of scalars along `a` is left adjoint to
restriction of scalars along `a`. -/
abbrev changeOfRingsAdjunction :
    extendScalars a ⊣ PresheafOfModules.restrictScalars.{u} a :=
  Adjunction.ofIsRightAdjoint (PresheafOfModules.restrictScalars.{u} a)

/-- Extension of scalars along `a` is an additive functor. -/
instance extendScalars_additive : (extendScalars a).Additive :=
  (changeOfRingsAdjunction a).left_adjoint_additive

/-- **The derived tensor product with the new coefficient ring**, `- ⊗^L_O O'`. It exists
unconditionally: extension of scalars is a right exact left adjoint out of a category of
presheaves of modules, which has enough projectives, so Stacks 0794 applies at the projective
objects. -/
def derivedExtendScalars :
    DerivedCategory (PresheafOfModules.{u} O) ⥤ DerivedCategory (PresheafOfModules.{u} O') :=
  totalDerivedLeftAdjoint (extendScalars a)

/-- The comparison transformation exhibiting `- ⊗^L_O O'` as the total left derived functor of
extension of scalars. -/
def derivedExtendScalarsCounit :
    DerivedCategory.Qh ⋙ derivedExtendScalars a ⟶
      (extendScalars a).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  totalDerivedLeftAdjointCounit (extendScalars a)

/-- The comparison does exhibit `- ⊗^L_O O'` as a total left derived functor of extension of
scalars. -/
theorem derivedExtendScalars_isLeftDerivedFunctor :
    (derivedExtendScalars a).IsLeftDerivedFunctor (derivedExtendScalarsCounit a)
      (HomotopyCategory.quasiIso (PresheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  totalDerivedLeftAdjoint_isLeftDerivedFunctor (extendScalars a)

/-- `- ⊗^L_O O'` is left adjoint to the degreewise derived restriction of scalars. -/
def derivedExtendScalarsAdjunction :
    derivedExtendScalars a ⊣ (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory :=
  totalDerivedLeftAdjointAdjunction (extendScalars a) (changeOfRingsAdjunction a)

/-- The derived tensor product commutes with the shift, being a left adjoint of a functor that
does. -/
instance derivedExtendScalars_commShift : (derivedExtendScalars a).CommShift ℤ :=
  (derivedExtendScalarsAdjunction a).leftAdjointCommShift ℤ

/-- The derived tensor product is an exact functor of triangulated categories. -/
instance derivedExtendScalars_isTriangulated : (derivedExtendScalars a).IsTriangulated :=
  have : (derivedExtendScalarsAdjunction a).CommShift ℤ :=
    (derivedExtendScalarsAdjunction a).commShift_of_rightAdjoint ℤ
  (derivedExtendScalarsAdjunction a).isTriangulated_leftAdjoint

/-- The derived tensor product commutes with colimits, being a left adjoint. This is the input
the dévissage of [Stacks, Tag 08RX] needs on the right-hand side. -/
instance derivedExtendScalars_preservesColimitsOfSize :
    PreservesColimitsOfSize.{w', w} (derivedExtendScalars a) :=
  (derivedExtendScalarsAdjunction a).leftAdjoint_preservesColimits

/-- The composite of the degreewise derived functors of restriction of scalars and of the
forgetful functor lifts, through the localisation `DerivedCategory.Q`, the degreewise functor of
the forgetful functor on `O'`-modules: the two underived composites are equal. -/
instance restrictScalarsToPresheafLifting :
    Localization.Lifting DerivedCategory.Q
      (HomologicalComplex.quasiIso (PresheafOfModules.{u} O') (ComplexShape.up ℤ))
      ((PresheafOfModules.toPresheaf O').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q)
      ((PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory ⋙
        (PresheafOfModules.toPresheaf O).mapDerivedCategory) :=
  ⟨(Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategoryFactors
      (PresheafOfModules.toPresheaf O).mapDerivedCategory ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      ((PresheafOfModules.restrictScalars.{u} a).mapHomologicalComplex (ComplexShape.up ℤ))
      (PresheafOfModules.toPresheaf O).mapDerivedCategoryFactors ≪≫
    (Functor.associator _ _ _).symm⟩

/-- **Restriction of scalars does not change the underlying complex of abelian presheaves**, in
the derived categories: a lift through the localisation is determined up to isomorphism by what
it lifts. -/
def restrictScalarsToPresheafMapDerivedCategoryIso :
    (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory ⋙
        (PresheafOfModules.toPresheaf O).mapDerivedCategory ≅
      (PresheafOfModules.toPresheaf O').mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (PresheafOfModules.{u} O') (ComplexShape.up ℤ)) _ _ _ _
    (Iso.refl ((PresheafOfModules.toPresheaf O').mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q))

/-- **Derived lower shriek does not see the coefficient ring**: an `O'`-module read as an
`O`-module has the same `Lπ_!`. -/
def restrictScalarsDerivedColimitIso :
    (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory ⋙
        abelianDerivedColimitOfModules O ≅
      abelianDerivedColimitOfModules O' :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (restrictScalarsToPresheafMapDerivedCategoryIso a)
      (totalDerivedColimit C AddCommGrpCat.{u})

/-- **The canonical comparison `Lπ_!(K) ⟶ Lπ_!(K ⊗^L_O O')`.** It is `Lπ_!` applied to the unit
`K ⟶ K ⊗^L_O O'` of the derived change-of-rings adjunction, followed by the identification of
`Lπ_!` on `O'`-modules with `Lπ_!` on their underlying `O`-modules.

[Stacks, Tag 08RX] asserts that this map is invertible for every `K` as soon as `C` admits a
cosimplicial point resolution and `Lπ_!(O) ⟶ Lπ_!(O')` is invertible. That assertion is not
proved in this file. -/
def derivedColimitTensorComparison :
    abelianDerivedColimitOfModules O ⟶
      derivedExtendScalars a ⋙ abelianDerivedColimitOfModules O' :=
  (Functor.leftUnitor (abelianDerivedColimitOfModules O)).inv ≫
    Functor.whiskerRight (derivedExtendScalarsAdjunction a).unit
      (abelianDerivedColimitOfModules O) ≫
    (Functor.associator (derivedExtendScalars a)
      (PresheafOfModules.restrictScalars.{u} a).mapDerivedCategory
      (abelianDerivedColimitOfModules O)).hom ≫
    Functor.whiskerLeft (derivedExtendScalars a) (restrictScalarsDerivedColimitIso a).hom

/-- **`j_{W!}O_W ⊗_O O' = j_{W!}O'_W`.** Extension of scalars along `a` takes the free
`O`-module on a presheaf of types to the free `O'`-module on it: both are left adjoint to the
same functor, since restriction of scalars does not change the underlying presheaf of sets.

At the presheaf represented by an object `W` the free module is the extension by zero of the
structure sheaf of the slice `C/W`, so this is the identification of the generators used in the
proof of [Stacks, Tag 08RX]. No flatness has to be discharged, and no higher derived functor of
extension of scalars enters, because the generator is projective
(`Stacks.ChaoticSite.freeYonedaProjective`).

The body is exposed because consumers need to evaluate this isomorphism on the tautological
generators of a free presheaf of modules, which is a property of the adjoint transpose that
only `CategoryTheory.Adjunction.leftAdjointUniq` provides. -/
@[expose]
def freeCompExtendScalarsIso :
    PresheafOfModules.free.{u} O ⋙ extendScalars a ≅ PresheafOfModules.free.{u} O' :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.freeAdjunction.{u} O).comp (changeOfRingsAdjunction a))
    (PresheafOfModules.freeAdjunction.{u} O')

end Stacks.ChaoticSite

end
