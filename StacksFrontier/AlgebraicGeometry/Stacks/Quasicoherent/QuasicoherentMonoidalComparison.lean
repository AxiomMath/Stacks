module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.BraidedEquivalenceInverse
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedMonoidalStructure

/-!
# The two monoidal structures on the quasi-coherent modules of an algebraic stack

Two monoidal structures on `QCoh(𝒪_𝒳)` are in the library.

* (I) `AlgebraicGeometry.FibredSite.monoidalCategoryQuasicoherentModules`, the full monoidal
  subcategory of `Mod(𝒪_𝒳)` for the *localized* structure
  `AlgebraicGeometry.FibredSite.monoidalCategory`, whose tensor product is a localization of the
  objectwise tensor product along sheafification and is only isomorphic to the tensor product
  sheaf.
* (II) the full monoidal subcategory of `Mod(𝒪_𝒳)` for the *strict* structure
  `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal` of Tag 01CA, whose tensor product
  is the tensor product sheaf on the nose, with the braiding
  `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesBraided`.

The two underlying categories are the same category: for an algebraic stack `𝒳`,
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules` is by definition
`AlgebraicGeometry.FibredSite.quasicoherentModules` at the fppf site of `𝒳`, at universes
`u, u + 1, u, u` (`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules_eq`). So the
comparison is an *isomorphism* of categories, the identity, and is packaged as the equivalence
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison` whose functor, inverse,
unit and counit are identities. The two tensor products are *not* equal on objects; the units
are. The identity is a braided monoidal functor from (II) to (I) whose tensorator is
`Stacks.SheafOfModules.tensorObjIso` and whose unit morphism is the identity.

## Main definitions

* `Stacks.SheafOfModules.Strict.toLocalizedMonoidalBraided`: on any ringed site, the identity of
  sheaves of modules is braided monoidal from the strict to the localized structure, and
  `Stacks.SheafOfModules.Strict.liftToLocalizedMonoidalBraided` restricts it to a full
  subcategory which is monoidal for both.
* `AlgebraicGeometry.FibredSite.braidedCategory` and
  `AlgebraicGeometry.FibredSite.symmetricCategory`: the braiding of the localized monoidal
  structure on sheaves of modules on an associated site of a fibred category, and its symmetry;
  `AlgebraicGeometry.FibredSite.braidedCategoryQuasicoherentModules` and
  `AlgebraicGeometry.FibredSite.symmetricCategoryQuasicoherentModules` complete (I).
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesMonoidal` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesBraided` name (II), exactly as
  instance search produces it.
* `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesComparisonBraided`: on `Mod(𝒪_𝒳)`, the
  identity is braided monoidal from the strict to the localized structure.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison`: the isomorphism of
  categories from (II) to (I), and
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonBraided` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonInverseBraided`: its
  functor and its inverse are braided monoidal.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules_eq`: the two categories are
  equal; `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison_μ_hom` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison_ε_hom` compute the
  tensorator and the unit morphism of the comparison.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isMonoidal_quasicoherentModulesComparison`: the
  comparison is a monoidal equivalence.
* `AlgebraicGeometry.Stack.AlgebraicStacks.nonempty_braided_comparisonFunctor_comp_iff`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.nonempty_monoidal_comparisonFunctor_comp_iff`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.additive_comparisonFunctor_comp_iff`,
  `AlgebraicGeometry.Stack.AlgebraicStacks.preservesFiniteColimits_comparisonFunctor_comp_iff`
  and their conjunction (in the same namespace)
  `braided_additive_preservesFiniteColimits_comparisonFunctor_comp_iff`:
  a functor out of (I) is braided monoidal, monoidal, additive, right exact if and only if its
  composite with the comparison is, for (II). The `…_comparisonInverse_comp_iff` statements are
  the same for functors out of (II) and the inverse of the comparison, and the definitions
  `…CompBraided`, `braidedOf…Comp` and their monoidal analogues carry the structures across.

## Implementation notes

The two monoidal structures live on one type, so neither is an instance and every statement
names both explicitly with `@`. The structure (II) on `QCoh(𝒪_𝒳)` is spelled exactly as
instance search produces it under `attribute [local instance] fppfModulesMonoidal
fppfModulesBraided`, so that the statements here apply to the functors of the files which use
(II) without any conversion.

The ambient comparison is `CategoryTheory.Monoidal.fromInducedCoreMonoidal` applied to
`Stacks.SheafOfModules.Strict.inducingFunctorData`, the data from which the strict structure is
induced, and its braided axiom is `Stacks.SheafOfModules.Strict.braiding_aux`; nothing about
sheaves is proved here. Because the functor and the inverse of the comparison are both the
identity, a structure on a composite with them *is* a structure on the functor itself, up to
definitional unfolding of the composite, which is how the transfer statements are proved.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w u₂ v₂

namespace Stacks.SheafOfModules.Strict

open _root_.Stacks.Localization _root_.CategoryTheory.Localization

variable {C : Type u₂} [Category.{v₂} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The identity functor `Stacks.SheafOfModules.Strict.toLocalizedMonoidal` is monoidal from the
strict monoidal structure `Stacks.SheafOfModules.Strict.monoidalCategory` to the localized one,
with tensorator `Stacks.SheafOfModules.tensorObjIso` and the identity as unit morphism: it is the
structure `Stacks.SheafOfModules.Strict.inducingFunctorData` with which the strict structure was
induced. -/
@[instance_reducible]
def toLocalizedMonoidalMonoidal :
    letI := monoidalCategory 𝒪 h𝒪
    (toLocalizedMonoidal 𝒪 h𝒪).Monoidal :=
  letI := monoidalCategory 𝒪 h𝒪
  letI := monoidalCategoryStruct 𝒪 h𝒪
  (CategoryTheory.Monoidal.fromInducedCoreMonoidal (toLocalizedMonoidal 𝒪 h𝒪)
    (inducingFunctorData 𝒪 h𝒪)).toMonoidal

/-- The identity functor `Stacks.SheafOfModules.Strict.toLocalizedMonoidal` is braided monoidal
from the strict structure with its braiding `Stacks.SheafOfModules.Strict.braidedCategory` to the
localized structure with its braiding: this is `Stacks.SheafOfModules.Strict.braiding_aux`. -/
@[instance_reducible]
def toLocalizedMonoidalBraided :
    letI := monoidalCategory 𝒪 h𝒪
    letI := braidedCategory 𝒪 h𝒪
    (toLocalizedMonoidal 𝒪 h𝒪).Braided :=
  letI := monoidalCategory 𝒪 h𝒪
  letI := braidedCategory 𝒪 h𝒪
  letI := toLocalizedMonoidalMonoidal 𝒪 h𝒪
  { braided := fun X Y => braiding_aux 𝒪 h𝒪 X Y }

/-- Let `P` be a property of sheaves of `𝒪`-modules which is monoidal for both the localized
structure (`hP`) and the strict structure (`hP'`). Then the identity of the full subcategory `P`
is braided monoidal from the full braided subcategory of the strict structure to the full
braided subcategory of the localized one. It is the lift of
`Stacks.SheafOfModules.Strict.toLocalizedMonoidalBraided`, by
`CategoryTheory.ObjectProperty.liftMonoidal` and `CategoryTheory.ObjectProperty.liftLaxBraided`. -/
@[instance_reducible]
def liftToLocalizedMonoidalBraided
    (P : ObjectProperty (SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf 𝒪 h𝒪)))
    (hP : letI := Stacks.SheafOfModules.monoidalCategory 𝒪 h𝒪; P.IsMonoidal)
    (hP' : letI := monoidalCategory 𝒪 h𝒪; P.IsMonoidal) :
    letI := monoidalCategory 𝒪 h𝒪
    letI := braidedCategory 𝒪 h𝒪
    letI := hP'
    letI : ObjectProperty.IsMonoidal
        (C := LocalizedMonoidal (L := Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪)
          (W := Stacks.SheafOfModules.localIso (J := J) 𝒪) (sheafifyUnitIso 𝒪 h𝒪)) P := hP
    (ObjectProperty.lift
      (show ObjectProperty (LocalizedMonoidal (L := Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪)
        (W := Stacks.SheafOfModules.localIso (J := J) 𝒪) (sheafifyUnitIso 𝒪 h𝒪)) from P)
      (P.ι ⋙ toLocalizedMonoidal 𝒪 h𝒪) (fun X => X.property)).Braided :=
  letI := monoidalCategory 𝒪 h𝒪
  letI := braidedCategory 𝒪 h𝒪
  letI := toLocalizedMonoidalBraided 𝒪 h𝒪
  letI := hP'
  letI : ObjectProperty.IsMonoidal
      (C := LocalizedMonoidal (L := Stacks.SheafOfModules.sheafifyFunctor 𝒪 h𝒪)
        (W := Stacks.SheafOfModules.localIso (J := J) 𝒪) (sheafifyUnitIso 𝒪 h𝒪)) P := hP
  @Functor.Braided.mk _ _ _ _ _ _ _ _ _ (ObjectProperty.liftMonoidal _ _ _)
    (ObjectProperty.liftLaxBraided _ _ _).braided

end Stacks.SheafOfModules.Strict

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{u} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) [EssentiallySmall.{u} 𝒳]

/-- The braiding of `AlgebraicGeometry.FibredSite.monoidalCategory`, the localized monoidal
structure on sheaves of modules on an associated site of the fibred category: the braiding
`Stacks.SheafOfModules.braidedCategory` of Tag 05NA, transported along
`AlgebraicGeometry.FibredSite.ringStructureSheafCore_eq_structureSheaf`. -/
@[instance_reducible]
def braidedCategory (τ : SiteKind) :
    letI := monoidalCategory B S hS p hp τ
    BraidedCategory (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :=
  letI := hasWeakSheafify_associatedTopology B S hS p τ
  letI := wEqualsLocallyBijective_associatedTopology B S hS p τ
  Stacks.SheafOfModules.braidedCategory (J := BigFppfOver.associatedTopology B S hS p τ)
    (structureSheaf B S hS p hp τ).obj (structureRingPresheaf_isSheaf B S hS p hp τ)

/-- The braiding `AlgebraicGeometry.FibredSite.braidedCategory` is a symmetry. -/
@[instance_reducible]
def symmetricCategory (τ : SiteKind) :
    letI := monoidalCategory B S hS p hp τ
    letI := braidedCategory B S hS p hp τ
    SymmetricCategory (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) :=
  letI := hasWeakSheafify_associatedTopology B S hS p τ
  letI := wEqualsLocallyBijective_associatedTopology B S hS p τ
  Stacks.SheafOfModules.symmetricCategory (J := BigFppfOver.associatedTopology B S hS p τ)
    (structureSheaf B S hS p hp τ).obj (structureRingPresheaf_isSheaf B S hS p hp τ)

/-- The braiding of `QCoh(𝒪_𝒳)` for
`AlgebraicGeometry.FibredSite.monoidalCategoryQuasicoherentModules`: that of the ambient
category of sheaves of modules, `AlgebraicGeometry.FibredSite.braidedCategory`, restricted to
the full monoidal subcategory. -/
@[instance_reducible]
def braidedCategoryQuasicoherentModules :
    letI := monoidalCategoryQuasicoherentModules B S hS p hp
    BraidedCategory (quasicoherentModules.{u, v, u, u} B S hS p hp) :=
  letI := monoidalCategory B S hS p hp .fppf
  letI := braidedCategory B S hS p hp .fppf
  ObjectProperty.fullBraidedSubcategory _

/-- The braiding `AlgebraicGeometry.FibredSite.braidedCategoryQuasicoherentModules` of
`QCoh(𝒪_𝒳)` is a symmetry. -/
@[instance_reducible]
def symmetricCategoryQuasicoherentModules :
    letI := monoidalCategoryQuasicoherentModules B S hS p hp
    letI := braidedCategoryQuasicoherentModules B S hS p hp
    SymmetricCategory (quasicoherentModules.{u, v, u, u} B S hS p hp) :=
  letI := monoidalCategory B S hS p hp .fppf
  letI := braidedCategory B S hS p hp .fppf
  letI := symmetricCategory B S hS p hp .fppf
  ObjectProperty.fullSymmetricSubcategory _

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack.AlgebraicStacks

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-! ### The comparison on `Mod(𝒪_𝒳)` -/

/-- On `Mod(𝒪_𝒳)`, the identity is a braided monoidal functor from the strict structure
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal` with its braiding
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesBraided` to the localized structure
`AlgebraicGeometry.FibredSite.monoidalCategory` with its braiding
`AlgebraicGeometry.FibredSite.braidedCategory`. Its tensorator is
`Stacks.SheafOfModules.tensorObjIso` and its unit morphism is the identity. -/
@[instance_reducible]
def fppfModulesComparisonBraided :
    @Functor.Braided (Stack.fppfModules B S hS 𝒳) _ (fppfModulesMonoidal B S hS 𝒳)
      (fppfModulesBraided B S hS 𝒳) (Stack.fppfModules B S hS 𝒳) _
      (FibredSite.monoidalCategory B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)
      (FibredSite.braidedCategory B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) (𝟭 _) :=
  Stacks.SheafOfModules.Strict.toLocalizedMonoidalBraided (FlatFppf.fppfRingedTopos B S hS 𝒳).O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
      (FlatFppf.fppfRingedTopos B S hS 𝒳).O)

/-! ### The two monoidal structures on `QCoh(𝒪_𝒳)` -/

/-- **The two categories of quasi-coherent modules on an algebraic stack are one category.**
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules` is
`AlgebraicGeometry.FibredSite.quasicoherentModules` at the fppf site of the stack, at module
universe `u`, by definition. -/
theorem quasicoherentModules_eq :
    quasicoherentModules B S hS 𝒳 =
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  rfl

/-- The strict monoidal structure (II) on `QCoh(𝒪_𝒳)`: the full monoidal subcategory of
`Mod(𝒪_𝒳)` with `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal`. This is, on the
nose, the structure instance search finds on `QCoh(𝒪_𝒳)` under
`attribute [local instance] fppfModulesMonoidal`. -/
abbrev quasicoherentModulesMonoidal : MonoidalCategory (quasicoherentModules B S hS 𝒳) :=
  @ObjectProperty.fullMonoidalSubcategory _ _ (fppfModulesMonoidal B S hS 𝒳) _
    (isMonoidal_isQuasicoherentOnSite B S hS 𝒳)

/-- The braiding of the strict monoidal structure (II) on `QCoh(𝒪_𝒳)`: the full braided
subcategory of `Mod(𝒪_𝒳)` with `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesBraided`.
This is, on the nose, the braiding instance search finds on `QCoh(𝒪_𝒳)` under
`attribute [local instance] fppfModulesMonoidal fppfModulesBraided`. -/
abbrev quasicoherentModulesBraided :
    @BraidedCategory (quasicoherentModules B S hS 𝒳) _ (quasicoherentModulesMonoidal B S hS 𝒳) :=
  @ObjectProperty.fullBraidedSubcategory _ _ (fppfModulesMonoidal B S hS 𝒳) _
    (isMonoidal_isQuasicoherentOnSite B S hS 𝒳) (fppfModulesBraided B S hS 𝒳)

/-- The isomorphism of categories between `QCoh(𝒪_𝒳)` as
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModules` and as
`AlgebraicGeometry.FibredSite.quasicoherentModules`: the identity, with identity unit and
counit. It is braided monoidal from the strict structure (II) to the localized structure (I),
by `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonBraided`. -/
def quasicoherentModulesComparison :
    quasicoherentModules B S hS 𝒳 ≌
      FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids :=
  CategoryTheory.Equivalence.refl

/-- The functor of `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison` is
the identity. -/
theorem quasicoherentModulesComparison_functor :
    (quasicoherentModulesComparison B S hS 𝒳).functor = 𝟭 _ :=
  rfl

/-- The inverse of `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison` is
the identity. -/
theorem quasicoherentModulesComparison_inverse :
    (quasicoherentModulesComparison B S hS 𝒳).inverse = 𝟭 _ :=
  rfl

/-- The unit of `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison` is the
identity: the comparison is an isomorphism of categories. -/
theorem quasicoherentModulesComparison_unitIso :
    (quasicoherentModulesComparison B S hS 𝒳).unitIso = Iso.refl _ :=
  rfl

/-- The counit of `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison` is
the identity: the comparison is an isomorphism of categories. -/
theorem quasicoherentModulesComparison_counitIso :
    (quasicoherentModulesComparison B S hS 𝒳).counitIso = Iso.refl _ :=
  rfl

/-- **The comparison of the two monoidal structures on `QCoh(𝒪_𝒳)` is braided monoidal.** The
functor of `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison`, the
identity, is a braided monoidal functor from the strict structure (II),
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesMonoidal` with
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesBraided`, to the localized
structure (I), `AlgebraicGeometry.FibredSite.monoidalCategoryQuasicoherentModules` with
`AlgebraicGeometry.FibredSite.braidedCategoryQuasicoherentModules`. Its tensorator is
`Stacks.SheafOfModules.tensorObjIso` and its unit morphism is the identity. -/
@[instance_reducible]
def quasicoherentModulesComparisonBraided :
    @Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
      (quasicoherentModulesBraided B S hS 𝒳) _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (quasicoherentModulesComparison B S hS 𝒳).functor :=
  Stacks.SheafOfModules.Strict.liftToLocalizedMonoidalBraided
    (FlatFppf.fppfRingedTopos B S hS 𝒳).O.obj
    (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
      (FlatFppf.fppfRingedTopos B S hS 𝒳).O)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf))
    (FibredSite.isMonoidal_isQuasicoherentOnSite B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      .fppf)
    (isMonoidal_isQuasicoherentOnSite B S hS 𝒳)

/-- The monoidal structure underlying
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonBraided`. -/
abbrev quasicoherentModulesComparisonMonoidal :
    @Functor.Monoidal _ _ (quasicoherentModulesMonoidal B S hS 𝒳) _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (quasicoherentModulesComparison B S hS 𝒳).functor :=
  @Functor.Braided.toMonoidal _ _ (_) (_) _ _ (_) (_) _
    (quasicoherentModulesComparisonBraided B S hS 𝒳)

/-- The tensorator of
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonBraided` is
`Stacks.SheafOfModules.tensorObjIso`: the two tensor products of `QCoh(𝒪_𝒳)` differ on objects,
and this is the isomorphism between them. -/
theorem quasicoherentModulesComparison_μ_hom (X Y : quasicoherentModules B S hS 𝒳) :
    (@Functor.LaxMonoidal.μ _ _ (quasicoherentModulesMonoidal B S hS 𝒳) _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) _
      (@Functor.Monoidal.toLaxMonoidal _ _ _ _ _ _ _
        (quasicoherentModulesComparisonMonoidal B S hS 𝒳)) X Y).hom =
      (Stacks.SheafOfModules.tensorObjIso (FlatFppf.fppfRingedTopos B S hS 𝒳).O.obj
        (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
          (FlatFppf.fppfRingedTopos B S hS 𝒳).O) X.obj Y.obj).hom :=
  rfl

/-- The unit morphism of
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonBraided` is the identity:
the two monoidal structures on `QCoh(𝒪_𝒳)` have the same unit, the structure sheaf. -/
theorem quasicoherentModulesComparison_ε_hom :
    (@Functor.LaxMonoidal.ε _ _ (quasicoherentModulesMonoidal B S hS 𝒳) _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) _
      (@Functor.Monoidal.toLaxMonoidal _ _ _ _ _ _ _
        (quasicoherentModulesComparisonMonoidal B S hS 𝒳))).hom = 𝟙 _ :=
  rfl

/-- The inverse of `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparison`, the
identity, is braided monoidal from the localized structure (I) to the strict structure (II), for
the monoidal structure `CategoryTheory.Equivalence.inverseMonoidal`. -/
@[instance_reducible]
def quasicoherentModulesComparisonInverseBraided :
    @Functor.Braided _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) _ _
      (quasicoherentModulesMonoidal B S hS 𝒳) (quasicoherentModulesBraided B S hS 𝒳)
      (quasicoherentModulesComparison B S hS 𝒳).inverse :=
  @Equivalence.inverseBraided _ _ _ _ (_) (_) (_) (_) _
    (quasicoherentModulesComparisonBraided B S hS 𝒳)

/-- The monoidal structure underlying
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonInverseBraided`. -/
abbrev quasicoherentModulesComparisonInverseMonoidal :
    @Functor.Monoidal _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) _ _
      (quasicoherentModulesMonoidal B S hS 𝒳)
      (quasicoherentModulesComparison B S hS 𝒳).inverse :=
  @Functor.Braided.toMonoidal _ _ (_) (_) _ _ (_) (_) _
    (quasicoherentModulesComparisonInverseBraided B S hS 𝒳)

/-- **The comparison of the two monoidal structures on `QCoh(𝒪_𝒳)` is a monoidal equivalence**:
its unit and counit, both identities, are monoidal natural transformations for
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonMonoidal` and
`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesComparisonInverseMonoidal`. -/
theorem isMonoidal_quasicoherentModulesComparison :
    @Equivalence.IsMonoidal _ _ (quasicoherentModulesMonoidal B S hS 𝒳) _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (quasicoherentModulesComparison B S hS 𝒳)
      (quasicoherentModulesComparisonMonoidal B S hS 𝒳)
      (quasicoherentModulesComparisonInverseMonoidal B S hS 𝒳) :=
  @Equivalence.isMonoidal_inverseMonoidal _ _ _ _ (_) (_) _
    (quasicoherentModulesComparisonMonoidal B S hS 𝒳)

/-! ### Transfer of tensor functors along the comparison -/

section Transfer

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]

/-! #### Functors out of `QCoh(𝒪_𝒳)` with the localized structure (I) -/

/-- A braided monoidal functor out of `QCoh(𝒪_𝒳)` with the localized structure (I) gives a
braided monoidal functor out of `QCoh(𝒪_𝒳)` with the strict structure (II), by composing with
the comparison. -/
@[instance_reducible]
def comparisonFunctorCompBraided
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ D)
    (hF : @Functor.Braided _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _ _ F) :
    @Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
      (quasicoherentModulesBraided B S hS 𝒳) D _ _ _
      ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F) :=
  @Functor.Braided.instComp _ _ (_) (_) _ _ (_) (_) D _ _ _ _ F
    (quasicoherentModulesComparisonBraided B S hS 𝒳) hF

/-- A functor out of `QCoh(𝒪_𝒳)` with the localized structure (I) whose composite with the
comparison is braided monoidal for the strict structure (II) is itself braided monoidal: it is
the composite of the inverse of the comparison with that composite. -/
@[instance_reducible]
def braidedOfComparisonFunctorComp
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ D)
    (hF : @Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
      (quasicoherentModulesBraided B S hS 𝒳) D _ _ _
      ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F)) :
    @Functor.Braided _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _ _ F :=
  @Functor.Braided.instComp _ _ (_) (_) _ _ (_) (_) D _ _ _ _ _
    (quasicoherentModulesComparisonInverseBraided B S hS 𝒳) hF

/-- A monoidal functor out of `QCoh(𝒪_𝒳)` with the localized structure (I) gives a monoidal
functor out of `QCoh(𝒪_𝒳)` with the strict structure (II), by composing with the comparison. -/
@[instance_reducible]
def comparisonFunctorCompMonoidal
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ D)
    (hF : @Functor.Monoidal _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _ F) :
    @Functor.Monoidal _ _ (quasicoherentModulesMonoidal B S hS 𝒳) D _ _
      ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F) :=
  @Functor.Monoidal.instComp _ _ (_) _ _ (_) D _ _ _ F
    (quasicoherentModulesComparisonMonoidal B S hS 𝒳) hF

/-- A functor out of `QCoh(𝒪_𝒳)` with the localized structure (I) whose composite with the
comparison is monoidal for the strict structure (II) is itself monoidal. -/
@[instance_reducible]
def monoidalOfComparisonFunctorComp
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ D)
    (hF : @Functor.Monoidal _ _ (quasicoherentModulesMonoidal B S hS 𝒳) D _ _
      ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F)) :
    @Functor.Monoidal _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _ F :=
  @Functor.Monoidal.instComp _ _ (_) _ _ (_) D _ _ _ _
    (quasicoherentModulesComparisonInverseMonoidal B S hS 𝒳) hF

/-- **Transfer of braided monoidal functors.** A functor out of `QCoh(𝒪_𝒳)` with the localized
structure (I) is braided monoidal if and only if its composite with the comparison is braided
monoidal for the strict structure (II). -/
theorem nonempty_braided_comparisonFunctor_comp_iff
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ D) :
    Nonempty (@Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
      (quasicoherentModulesBraided B S hS 𝒳) D _ _ _
      ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F)) ↔
    Nonempty (@Functor.Braided _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _ _ F) :=
  ⟨fun ⟨h⟩ => ⟨braidedOfComparisonFunctorComp B S hS 𝒳 F h⟩,
    fun ⟨h⟩ => ⟨comparisonFunctorCompBraided B S hS 𝒳 F h⟩⟩

omit [BraidedCategory D] in
/-- **Transfer of monoidal functors.** A functor out of `QCoh(𝒪_𝒳)` with the localized structure
(I) is monoidal if and only if its composite with the comparison is monoidal for the strict
structure (II). -/
theorem nonempty_monoidal_comparisonFunctor_comp_iff
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ D) :
    Nonempty (@Functor.Monoidal _ _ (quasicoherentModulesMonoidal B S hS 𝒳) D _ _
      ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F)) ↔
    Nonempty (@Functor.Monoidal _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _ F) :=
  ⟨fun ⟨h⟩ => ⟨monoidalOfComparisonFunctorComp B S hS 𝒳 F h⟩,
    fun ⟨h⟩ => ⟨comparisonFunctorCompMonoidal B S hS 𝒳 F h⟩⟩

omit [MonoidalCategory D] [BraidedCategory D] in
/-- A functor out of `QCoh(𝒪_𝒳)` is additive if and only if its composite with the comparison
is: the comparison is the identity of the underlying category. -/
theorem additive_comparisonFunctor_comp_iff [Preadditive D]
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ D) :
    ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F).Additive ↔ F.Additive :=
  Iff.rfl

omit [MonoidalCategory D] [BraidedCategory D] in
/-- A functor out of `QCoh(𝒪_𝒳)` preserves finite colimits if and only if its composite with the
comparison does: the comparison is the identity of the underlying category. -/
theorem preservesFiniteColimits_comparisonFunctor_comp_iff
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ D) :
    PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F) ↔
      PreservesFiniteColimits F :=
  Iff.rfl

/-- **Transfer of right exact tensor functors.** A functor out of `QCoh(𝒪_𝒳)` with the localized
structure (I) is braided monoidal, additive and right exact if and only if its composite with
the comparison is so for the strict structure (II). -/
theorem braided_additive_preservesFiniteColimits_comparisonFunctor_comp_iff [Preadditive D]
    (F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids ⥤ D) :
    (Nonempty (@Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
        (quasicoherentModulesBraided B S hS 𝒳) D _ _ _
        ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F)) ∧
      ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F).Additive ∧
      PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).functor ⋙ F)) ↔
    (Nonempty (@Functor.Braided _ _
        (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids)
        (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids) D _ _ _ F) ∧
      F.Additive ∧ PreservesFiniteColimits F) :=
  and_congr (nonempty_braided_comparisonFunctor_comp_iff B S hS 𝒳 F) Iff.rfl

/-! #### Functors out of `QCoh(𝒪_𝒳)` with the strict structure (II) -/

/-- A braided monoidal functor out of `QCoh(𝒪_𝒳)` with the strict structure (II) gives a braided
monoidal functor out of `QCoh(𝒪_𝒳)` with the localized structure (I), by composing with the
inverse of the comparison. -/
@[instance_reducible]
def comparisonInverseCompBraided (G : quasicoherentModules B S hS 𝒳 ⥤ D)
    (hG : @Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
      (quasicoherentModulesBraided B S hS 𝒳) D _ _ _ G) :
    @Functor.Braided _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _ _
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G) :=
  @Functor.Braided.instComp _ _ (_) (_) _ _ (_) (_) D _ _ _ _ G
    (quasicoherentModulesComparisonInverseBraided B S hS 𝒳) hG

/-- A functor out of `QCoh(𝒪_𝒳)` with the strict structure (II) whose composite with the inverse
of the comparison is braided monoidal for the localized structure (I) is itself braided
monoidal. -/
@[instance_reducible]
def braidedOfComparisonInverseComp (G : quasicoherentModules B S hS 𝒳 ⥤ D)
    (hG : @Functor.Braided _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _ _
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G)) :
    @Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
      (quasicoherentModulesBraided B S hS 𝒳) D _ _ _ G :=
  @Functor.Braided.instComp _ _ (_) (_) _ _ (_) (_) D _ _ _ _ _
    (quasicoherentModulesComparisonBraided B S hS 𝒳) hG

/-- A monoidal functor out of `QCoh(𝒪_𝒳)` with the strict structure (II) gives a monoidal functor
out of `QCoh(𝒪_𝒳)` with the localized structure (I), by composing with the inverse of the
comparison. -/
@[instance_reducible]
def comparisonInverseCompMonoidal (G : quasicoherentModules B S hS 𝒳 ⥤ D)
    (hG : @Functor.Monoidal _ _ (quasicoherentModulesMonoidal B S hS 𝒳) D _ _ G) :
    @Functor.Monoidal _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G) :=
  @Functor.Monoidal.instComp _ _ (_) _ _ (_) D _ _ _ G
    (quasicoherentModulesComparisonInverseMonoidal B S hS 𝒳) hG

/-- A functor out of `QCoh(𝒪_𝒳)` with the strict structure (II) whose composite with the inverse
of the comparison is monoidal for the localized structure (I) is itself monoidal. -/
@[instance_reducible]
def monoidalOfComparisonInverseComp (G : quasicoherentModules B S hS 𝒳 ⥤ D)
    (hG : @Functor.Monoidal _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G)) :
    @Functor.Monoidal _ _ (quasicoherentModulesMonoidal B S hS 𝒳) D _ _ G :=
  @Functor.Monoidal.instComp _ _ (_) _ _ (_) D _ _ _ _
    (quasicoherentModulesComparisonMonoidal B S hS 𝒳) hG

/-- **Transfer of braided monoidal functors.** A functor out of `QCoh(𝒪_𝒳)` with the strict
structure (II) is braided monoidal if and only if its composite with the inverse of the
comparison is braided monoidal for the localized structure (I). -/
theorem nonempty_braided_comparisonInverse_comp_iff (G : quasicoherentModules B S hS 𝒳 ⥤ D) :
    Nonempty (@Functor.Braided _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids)
      (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _ _
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G)) ↔
    Nonempty (@Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
      (quasicoherentModulesBraided B S hS 𝒳) D _ _ _ G) :=
  ⟨fun ⟨h⟩ => ⟨braidedOfComparisonInverseComp B S hS 𝒳 G h⟩,
    fun ⟨h⟩ => ⟨comparisonInverseCompBraided B S hS 𝒳 G h⟩⟩

omit [BraidedCategory D] in
/-- **Transfer of monoidal functors.** A functor out of `QCoh(𝒪_𝒳)` with the strict structure
(II) is monoidal if and only if its composite with the inverse of the comparison is monoidal for
the localized structure (I). -/
theorem nonempty_monoidal_comparisonInverse_comp_iff (G : quasicoherentModules B S hS 𝒳 ⥤ D) :
    Nonempty (@Functor.Monoidal _ _
      (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids) D _ _
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G)) ↔
    Nonempty (@Functor.Monoidal _ _ (quasicoherentModulesMonoidal B S hS 𝒳) D _ _ G) :=
  ⟨fun ⟨h⟩ => ⟨monoidalOfComparisonInverseComp B S hS 𝒳 G h⟩,
    fun ⟨h⟩ => ⟨comparisonInverseCompMonoidal B S hS 𝒳 G h⟩⟩

omit [MonoidalCategory D] [BraidedCategory D] in
/-- A functor out of `QCoh(𝒪_𝒳)` is additive if and only if its composite with the inverse of
the comparison is. -/
theorem additive_comparisonInverse_comp_iff [Preadditive D]
    (G : quasicoherentModules B S hS 𝒳 ⥤ D) :
    ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G).Additive ↔ G.Additive :=
  Iff.rfl

omit [MonoidalCategory D] [BraidedCategory D] in
/-- A functor out of `QCoh(𝒪_𝒳)` preserves finite colimits if and only if its composite with the
inverse of the comparison does. -/
theorem preservesFiniteColimits_comparisonInverse_comp_iff
    (G : quasicoherentModules B S hS 𝒳 ⥤ D) :
    PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G) ↔
      PreservesFiniteColimits G :=
  Iff.rfl

/-- **Transfer of right exact tensor functors.** A functor out of `QCoh(𝒪_𝒳)` with the strict
structure (II) is braided monoidal, additive and right exact if and only if its composite with
the inverse of the comparison is so for the localized structure (I). -/
theorem braided_additive_preservesFiniteColimits_comparisonInverse_comp_iff [Preadditive D]
    (G : quasicoherentModules B S hS 𝒳 ⥤ D) :
    (Nonempty (@Functor.Braided _ _
        (FibredSite.monoidalCategoryQuasicoherentModules B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids)
        (FibredSite.braidedCategoryQuasicoherentModules B S hS 𝒳.val.val.p
          𝒳.val.isFiberedInGroupoids) D _ _ _
        ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G)) ∧
      ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G).Additive ∧
      PreservesFiniteColimits ((quasicoherentModulesComparison B S hS 𝒳).inverse ⋙ G)) ↔
    (Nonempty (@Functor.Braided _ _ (quasicoherentModulesMonoidal B S hS 𝒳)
        (quasicoherentModulesBraided B S hS 𝒳) D _ _ _ G) ∧
      G.Additive ∧ PreservesFiniteColimits G) :=
  and_congr (nonempty_braided_comparisonInverse_comp_iff B S hS 𝒳 G) Iff.rfl

end Transfer

end AlgebraicGeometry.Stack.AlgebraicStacks

end
