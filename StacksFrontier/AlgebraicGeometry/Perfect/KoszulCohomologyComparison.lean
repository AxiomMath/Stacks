module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Perfect.KoszulDerivedSystem
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.FromTheStructureSheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedRestrictionToOpens
import StacksCore.Tactic.StacksAttribute

/-!
# The Koszul comparison map to cohomology over a union of basic opens

Let `A` be a commutative ring, let `f = (f₁, …, f_r)` be a finite sequence of elements of `A`,
let `X = Spec A` and let `U = D(f₁) ∪ ⋯ ∪ D(f_r) ⊆ X`.  Let `e ↦ Iₑ` be the inverse system in
`D(𝒪_X)` obtained by sheafifying the truncated Koszul complexes on the powers of `f`, together
with its compatible system of maps `Iₑ → 𝒪_X`.  Those maps become isomorphisms after restriction
to `U`, so a map `α : Iₑ → E` in `D(𝒪_X)` restricts to a map `𝒪_U → E|_U`, namely the inverse of
`Iₑ|_U ≅ 𝒪_U` followed by `α|_U`.  These maps are compatible with the transition maps of the
Koszul system, so they descend to a homomorphism out of the colimit, and composing with the
identification `Hom_{D(𝒪_U)}(𝒪_U, E|_U) = H⁰(U, E)` of Stacks 08DK gives the comparison map

`colimₑ Hom_{D(𝒪_X)}(Iₑ, E) ⟶ H⁰(U, E)`

of Stacks 08DC into the degree-zero hypercohomology of `E` over `U`.

## Main definitions

* `Koszul.DerivedSystem.sectionsDegreeZero` is degree-zero hypercohomology `H⁰(U, -)` over an
  open of a topological space carrying a sheaf of commutative rings.
* `Koszul.DerivedSystem.sectionsEquiv` is the identification
  `Hom_{D(𝒪_U)}(𝒪_U, E|_U) ≅ H⁰(U, E)`, for `𝒪_U`-modules in the open-subspace model.
* `Koszul.DerivedSystem.homGroupSystem` is the direct system `e ↦ Hom_{D(𝒪_X)}(Iₑ, E)` of
  morphism groups, whose transition maps are precomposition with the transition maps of the
  Koszul system.
* `Koszul.DerivedSystem.restrictionCocone` is the cocone whose leg at stage `e` sends
  `α : Iₑ → E` to the restriction of `α` precomposed with the isomorphism `𝒪_U ≅ Iₑ|_U`, and
  `Koszul.DerivedSystem.cohomologyComparisonHom` is the induced homomorphism
  `colimₑ Hom_{D(𝒪_X)}(Iₑ, E) ⟶ Hom_{D(𝒪_U)}(𝒪_U, E|_U)`.
* `Koszul.DerivedSystem.cohomologyComparison` is the comparison map
  `colimₑ Hom_{D(𝒪_X)}(Iₑ, E) ⟶ H⁰(U, E)`.

## Main results

* `Koszul.DerivedSystem.restrictionIsoOfUnion_hom_comp_map`: the isomorphisms `𝒪_U ≅ Iₑ|_U`
  are compatible with the transition maps of the Koszul system.
* `Koszul.DerivedSystem.cohomologyComparison_colimit_ι`: the comparison map sends the class of
  `α : Iₑ → E` to the section of `E` over `U` corresponding to the restriction of `α`
  precomposed with `𝒪_U ≅ Iₑ|_U`.  Since a homomorphism out of a colimit is determined by its
  restrictions to the stages, this equation determines the comparison map.
* `Koszul.DerivedSystem.cohomologyComparisonHom_naturality`: the homomorphism into the group of
  morphisms `𝒪_U ⟶ E|_U` is natural in `E`.
* `Koszul.DerivedSystem.sectionsDegreeZero_eq_derivedSectionsOnOpen`: hypercohomology over an
  open is the same whether the open is read as an object of the site of opens or as an open
  subspace.

## Implementation notes

The identification `Hom_{D(𝒪_U)}(𝒪_U, E|_U) = H⁰(U, E)` of Stacks 08DK is stated for the
derived internal Hom and for the restriction of `𝒪_X`-modules to the opens contained in `U`.
It is specialised to `𝒪_X` in the first variable, where the derived internal Hom is the
identity, and transported to the open-subspace model of `𝒪_U`-modules along the equivalence
between the two models; the transport is possible on morphism groups because the equivalence
induces a fully faithful functor on derived categories.

Following the indexing of the Koszul system, the index `e : ℕ` stands for the exponent `e + 1`,
so stage `e` is attached to `I^•(f₁^{e+1}, …, f_r^{e+1})`; this is a cofinal reindexing and does
not change the colimit.

Several steps are isolated as lemmas about an arbitrary functor between arbitrary categories.
The restriction functor is a derived functor whose source and target are categories of sheaves
of modules on a space and on an open subspace, and the two spellings of the relevant sheaf of
rings agree only up to unfolding; stating the steps for an abstract functor keeps the rewrites
type-correct without relaxing the transparency used for unification.

## Invertibility of this map is Tag 08DD, and it is proved

What is built here is the map of [Stacks, Tag 08DC]; that it is an **isomorphism** for every `E`
of `D_QCoh(𝒪_X)` is [Stacks, Tag 08DD], and that is
`Koszul.DerivedSystem.bijective_cohomologyComparison` in
`StacksFrontier/AlgebraicGeometry/Perfect/KoszulCohomologyBijective.lean`, for an object with
quasi-coherent cohomology sheaves. It carries no `@[stacks 08DD]` attribute because that
registration is owned elsewhere. The statement matters beyond its own tag: it is the input that
produces the `E₁ = E ⊗^𝐋 I` clause of [Stacks, Tag 08EH], hence the support clause of
[Stacks, Tag 08EK], hence [Stacks, Tag 09IM] and [Stacks, Tag 09IN]. Both halves of the source's
proof of it are formalized here in the trees:

* `Koszul.koszulHomColimitIsoAlternatingCechTotal` in
  `StacksFrontier/Algebra/Homology/Koszul/AlternatingCechTotal.lean` is [Stacks, Tag 08D1]:
  `colimₑ Hom^•(I^•(f^{e+1}), M^•) ≅ Tot(Č_alt^•(𝒰, M~))`, natural in `M`.
* `Koszul.CechSituation.alternatingCechTotalNatIsoDerivedSections` in
  `StacksFrontier/Algebra/Homology/Koszul/AlternatingCechComputesCohomology.lean` is
  [Stacks, Tag 08D2]: `Tot(Č_alt^•(𝒰, F^•)) ≅ RΓ(U, F^•)` in `D(A)`.

Composing the two gives the source's quasi-isomorphism
`colimₑ Hom^•(I^•(f^{e+1}), M^•) ≅ RΓ(U, F^•)`; the passage to `H⁰` on both sides
([Stacks, Tag 0A66] and equation [Stacks, Tag 0A64]), the reduction of `E` to a complex of
quasi-coherent sheaves along [Stacks, Tag 06Z0], and the identification of the resulting map
with `Koszul.DerivedSystem.cohomologyComparison` below — for which
`Koszul.DerivedSystem.cohomologyComparison_colimit_ι` is the characterization — are what
`KoszulCohomologyBijective.lean` and its five companion modules carry out.

## References

* [Stacks Project, Tag 08DC](https://stacks.math.columbia.edu/tag/08DC)
* [Stacks Project, Tag 08DD](https://stacks.math.columbia.edu/tag/08DD)
* [Stacks Project, Tag 08D1](https://stacks.math.columbia.edu/tag/08D1)
* [Stacks Project, Tag 08D2](https://stacks.math.columbia.edu/tag/08D2)
* [Stacks Project, Tag 08CZ](https://stacks.math.columbia.edu/tag/08CZ)
* [Stacks Project, Tag 08CY](https://stacks.math.columbia.edu/tag/08CY)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open ExtensionByZeroModules Stacks.Cohomology.OpenSubspace
open Stacks.SheafOfModules (StructureSheafModules ringedSite derivedRestrict sliceToSubspaceFunctor
  derivedRestrictToSubspaceIso derivedSheafHomSectionsEquiv)

universe u

namespace Koszul.DerivedSystem

attribute [local instance] HasDerivedCategory.standard

/-! ### Morphism groups under functors and isomorphisms -/

/-- A fully faithful additive functor induces an isomorphism of morphism groups. -/
public def mapHomAddEquiv {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] (X Y : C) :
    (X ⟶ Y) ≃+ (F.obj X ⟶ F.obj Y) where
  toFun := F.map
  invFun := F.preimage
  left_inv := F.preimage_map
  right_inv := F.map_preimage
  map_add' _ _ := F.map_add

/-- Transporting a morphism along isomorphisms of its source and target is additive. -/
public def homCongrAddEquiv {C : Type*} [Category C] [Preadditive C] {X X' Y Y' : C}
    (i : X ≅ X') (j : Y ≅ Y') : (X ⟶ Y) ≃+ (X' ⟶ Y') where
  toEquiv := i.homCongr j
  map_add' _ _ := by
    simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-! ### Morphisms out of the structure sheaf as sections over an open -/

section Sections

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X) (U : Opens X)

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

/-- The total complexes of the tensor double complexes of complexes of `O_X`-modules exist,
named for the same reason. -/
local instance hasMapBifunctorSheafTensor :
    ∀ K₁ K₂ : HomologicalComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Rc))
        (ComplexShape.up ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor Rc) (ComplexShape.up ℤ) :=
  fun _ _ ↦ inferInstance

/-- Restriction of `O_X`-modules to the opens contained in `U` is left exact. -/
local instance preservesFiniteLimitsOver :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U) :=
  Stacks.Cohomology.Localization.preservesFiniteLimits_restriction (ringedSite Rc) U

/-- Restriction of `O_X`-modules to the opens contained in `U` is right exact. -/
local instance preservesFiniteColimitsOver :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (structureSheaf Rc) U) :=
  Stacks.Cohomology.Localization.preservesFiniteColimits_restriction (ringedSite Rc) U

/-- Degree-zero hypercohomology `H⁰(U, -)` over an open `U`, on the unbounded derived category
of `O_X`-modules. -/
public abbrev sectionsDegreeZero :
    DerivedCategory (StructureSheafModules Rc) ⥤ AddCommGrpCat.{u} :=
  Stacks.Cohomology.Localization.derivedSectionsOverObject (ringedSite Rc) U ⋙
    DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0

/-- The two readings of `H⁰(U, -)` agree.  Sections of an `O_X`-module over `U` are the same
group whether `U` is read as an object of the site of opens of `X` or as an open subspace, so
the two total right derived functors are the same functor and so are their degree-zero
cohomologies. -/
public lemma sectionsDegreeZero_eq_derivedSectionsOnOpen :
    sectionsDegreeZero Rc U =
      Stacks.Cohomology.OpenSubspace.derivedSectionsOnOpen (structureSheaf Rc) U ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0 :=
  rfl

/-- Passing between the slice-site and the open-subspace model of `O_U`-modules is an
equivalence on derived categories, being induced by an equivalence of abelian categories. -/
public instance sliceToSubspace_isEquivalence :
    (sliceToSubspaceFunctor Rc U).mapDerivedCategory.IsEquivalence :=
  inferInstanceAs
    ((U.sheafOfModulesEquivOver (structureSheaf Rc)).functor.mapDerivedCategory.IsEquivalence)

/-- **Degree-zero hypercohomology over an open is morphisms out of the structure sheaf.** For
an object `E` of `D(O_X)` and an open `U ⊆ X`, the group of morphisms `O_U ⟶ E|_U` in the
derived category of `O_U`-modules is `H⁰(U, E)`.

This is Stacks 08DK for `RSheafHom(O_X, E) = E`, read in the open-subspace model of
`O_U`-modules. -/
public def sectionsEquiv (E : DerivedCategory (StructureSheafModules Rc)) :
    ((derivedRestriction (structureSheaf Rc) U).obj
          (RingedSite.derivedStructureSheaf (ringedSite Rc)) ⟶
        (derivedRestriction (structureSheaf Rc) U).obj E) ≃+
      ↥((sectionsDegreeZero Rc U).obj E) :=
  (homCongrAddEquiv ((derivedRestrictToSubspaceIso Rc U).app _).symm
        ((derivedRestrictToSubspaceIso Rc U).app E).symm).trans
    ((mapHomAddEquiv (sliceToSubspaceFunctor Rc U).mapDerivedCategory _ _).symm.trans
      ((derivedSheafHomSectionsEquiv Rc U _ E).symm.trans
        ((sectionsDegreeZero Rc U).mapIso
          ((RingedSite.derivedStructureSheafHomNatIso
            (ringedSite Rc)).app E)).addCommGroupIsoToAddEquiv))

end Sections

/-! ### Additivity of derived restriction -/

/-- Derived restriction `(-)|_U` to an open is additive: restriction of module sheaves is exact,
so the comparison map from restriction on homotopy categories to its total right derived functor
is an isomorphism, and an additive functor stays additive after such a comparison. -/
public instance restrictionToUnion_additive {A : CommRingCat.{u}} {r : ℕ} (f : Fin r → A) :
    (restrictionToUnion f).Additive := by
  let O := (Spec A).ringCatSheaf
  let U := unionOfBasicOpens f
  let F := jStar U O
  let W := HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)
  let η := (homotopyRestriction O U).totalRightDerivedUnit DerivedCategory.Qh W
  have : IsIso η := Functor.isIso_of_isRightDerivedFunctor_of_inverts (restrictionToUnion f) η <|
    (MorphismProperty.IsInvertedBy.iff_of_iso W F.mapDerivedCategoryFactorsh).mp
      (MorphismProperty.IsInvertedBy.of_comp W DerivedCategory.Qh
        (Localization.inverts DerivedCategory.Qh W) F.mapDerivedCategory)
  rw [Localization.functor_additive_iff DerivedCategory.Qh W]
  exact Functor.additive_of_iso (asIso η)

/-! ### Composing with an inverted morphism -/

section Abstract

variable {C D : Type*} [Category C] [Category D] (R : C ⥤ D)

/-- Let `a : X ⟶ O` and `b : Y ⟶ O` become invertible under `R`, with inverse isomorphisms
`ρX : R O ≅ R X` and `ρY : R O ≅ R Y`, and let `t : Y ⟶ X` satisfy `t ≫ a = b`.  Then `R t`
carries `ρY` to `ρX`. -/
private lemma iso_hom_comp_map {O X Y : C} (ρX : R.obj O ≅ R.obj X) (ρY : R.obj O ≅ R.obj Y)
    {a : X ⟶ O} {b : Y ⟶ O} (t : Y ⟶ X)
    (hρX : ρX.inv = R.map a) (hρY : ρY.inv = R.map b) (ht : t ≫ a = b) :
    ρY.hom ≫ R.map t = ρX.hom := by
  apply (cancel_mono ρX.inv).mp
  have h1 : R.map t ≫ ρX.inv = ρY.inv := by rw [hρX, ← R.map_comp, ht, hρY]
  rw [Category.assoc, h1, Iso.hom_inv_id, Iso.hom_inv_id]

/-- Precomposition with `t` leaves the morphism obtained by restricting along `ρ` unchanged, as
soon as `R t` carries `ρY` to `ρX`. -/
private lemma iso_hom_comp_map_comp {O X Y Z : C} (ρX : R.obj O ≅ R.obj X)
    (ρY : R.obj O ≅ R.obj Y) (t : Y ⟶ X) (h : ρY.hom ≫ R.map t = ρX.hom) (α : X ⟶ Z) :
    ρY.hom ≫ R.map (t ≫ α) = ρX.hom ≫ R.map α := by
  rw [R.map_comp, ← Category.assoc, h]

/-- Postcomposition with `g` commutes with restricting along `ρ`. -/
private lemma iso_hom_comp_map_comp_right {O X Y Z : C} (ρ : R.obj O ≅ R.obj X)
    (α : X ⟶ Y) (g : Y ⟶ Z) :
    ρ.hom ≫ R.map (α ≫ g) = (ρ.hom ≫ R.map α) ≫ R.map g := by
  rw [R.map_comp, Category.assoc]

end Abstract

/-! ### The direct system of morphism groups and the group of sections -/

variable {A : CommRingCat.{u}} {r : ℕ}

/-- The direct system `e ↦ Hom_{D(𝒪_X)}(Iₑ, E)` of morphism groups out of the derived Koszul
system, whose transition maps are precomposition with the transition maps of that system. -/
public abbrev homGroupSystem (f : Fin r → A) (E : derivedCat A) : ℕ ⥤ AddCommGrpCat.{u + 1} :=
  (koszulDerivedSystem f).rightOp ⋙ preadditiveYoneda.obj E

/-- The group of morphisms `𝒪_U ⟶ E|_U` in the derived category of `𝒪_U`-modules, for
`U = D(f₁) ∪ ⋯ ∪ D(f_r)`. -/
public abbrev sectionsOnUnionHom (f : Fin r → A) : derivedCat A ⥤ AddCommGrpCat.{u + 1} :=
  restrictionToUnion f ⋙
    preadditiveCoyoneda.obj (op ((restrictionToUnion f).obj (structureSheafObject A)))

/-- Degree-zero hypercohomology `H⁰(U, -)` over `U = D(f₁) ∪ ⋯ ∪ D(f_r)`. -/
public abbrev sectionsOnUnion (f : Fin r → A) : derivedCat A ⥤ AddCommGrpCat.{u} :=
  sectionsDegreeZero (Spec A).sheaf (unionOfBasicOpens f)

/-- **Degree-zero hypercohomology over `U` is morphisms out of the structure sheaf.** For an
object `E` of `D(𝒪_X)` the group of morphisms `𝒪_U ⟶ E|_U` in the derived category of
`𝒪_U`-modules is `H⁰(U, E)`, for `U = D(f₁) ∪ ⋯ ∪ D(f_r)`. -/
public def sectionsEquivOfUnion (f : Fin r → A) (E : derivedCat A) :
    ((restrictionToUnion f).obj (structureSheafObject A) ⟶
        (restrictionToUnion f).obj E) ≃+ ↥((sectionsOnUnion f).obj E) :=
  sectionsEquiv (Spec A).sheaf (unionOfBasicOpens f) E

/-- The isomorphisms `𝒪_U ≅ Iₑ|_U` are compatible with the transition maps of the Koszul
system: restricting a transition map `I_{j} ⟶ I_{i}` to `U` carries the isomorphism at stage `j`
to the one at stage `i`, because the maps `Iₑ → 𝒪_X` form a morphism of systems. -/
public lemma restrictionIsoOfUnion_hom_comp_map (f : Fin r → A) {i j : ℕ} (g : i ⟶ j) :
    (restrictionIsoOfUnion f j).hom ≫
        (restrictionToUnion f).map ((koszulDerivedSystem f).map g.op) =
      (restrictionIsoOfUnion f i).hom :=
  iso_hom_comp_map (restrictionToUnion f) (restrictionIsoOfUnion f i)
    (restrictionIsoOfUnion f j) _ (restrictionIsoOfUnion_inv f i)
    (restrictionIsoOfUnion_inv f j)
    (by simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.comp_id,
          koszulSystemToStructureSheaf_app] using
        (koszulSystemToStructureSheaf f).naturality g.op)

/-! ### The comparison map -/

/-- The cocone on the direct system of morphism groups whose leg at stage `e` sends
`α : Iₑ ⟶ E` to the morphism `𝒪_U ⟶ E|_U` obtained by restricting `α` to `U` and precomposing
with the isomorphism `𝒪_U ≅ Iₑ|_U`. -/
public def restrictionCocone (f : Fin r → A) (E : derivedCat A) :
    Cocone (homGroupSystem f E) where
  pt := (sectionsOnUnionHom f).obj E
  ι :=
    { app := fun e ↦ AddCommGrpCat.ofHom
        ((Preadditive.leftComp ((restrictionToUnion f).obj E)
          (restrictionIsoOfUnion f e).hom).comp (restrictionToUnion f).mapAddHom)
      naturality := by
        intro i j g
        ext α
        exact iso_hom_comp_map_comp (restrictionToUnion f) (restrictionIsoOfUnion f i)
          (restrictionIsoOfUnion f j) _ (restrictionIsoOfUnion_hom_comp_map f g) α }

/-- The homomorphism `colimₑ Hom_{D(𝒪_X)}(Iₑ, E) ⟶ Hom_{D(𝒪_U)}(𝒪_U, E|_U)` induced by the
restriction cocone: on the class of `α : Iₑ → E` it is the restriction of `α` to `U`,
precomposed with the isomorphism `𝒪_U ≅ Iₑ|_U`. -/
public def cohomologyComparisonHom (f : Fin r → A) (E : derivedCat A) :
    ↥(colimit (homGroupSystem f E)) →+ ↥((sectionsOnUnionHom f).obj E) :=
  (colimit.desc _ (restrictionCocone f E)).hom

/-- The equation characterizing the homomorphism out of the colimit: on the class of a map
`α : Iₑ → E` it is the restriction of `α` to `U`, precomposed with the isomorphism
`𝒪_U ≅ Iₑ|_U` inverse to the restriction of `Iₑ → 𝒪_X`. -/
public lemma cohomologyComparisonHom_colimit_ι (f : Fin r → A) (E : derivedCat A) (e : ℕ)
    (α : (koszulDerivedSystem f).obj (op e) ⟶ E) :
    cohomologyComparisonHom f E (colimit.ι (homGroupSystem f E) e α) =
      (restrictionIsoOfUnion f e).hom ≫ (restrictionToUnion f).map α :=
  ConcreteCategory.congr_hom (colimit.ι_desc (restrictionCocone f E) e) α

/-- **The comparison map of Stacks 08DC.** For every object `E` of `D(𝒪_X)` the maps
`Iₑ → 𝒪_X`, which become isomorphisms after restriction to `U = D(f₁) ∪ ⋯ ∪ D(f_r)`, induce a
canonical homomorphism

`colimₑ Hom_{D(𝒪_X)}(Iₑ, E) ⟶ H⁰(U, E)`,

sending the class of `α : Iₑ → E` to the restriction of `α` to `U` precomposed with the inverse
of the restriction of `Iₑ → 𝒪_X`, read as a degree-zero hypercohomology class over `U`. -/
@[stacks 08DC]
public def cohomologyComparison (f : Fin r → A) (E : derivedCat A) :
    ↥(colimit (homGroupSystem f E)) →+ ↥((sectionsOnUnion f).obj E) :=
  (sectionsEquivOfUnion f E).toAddMonoidHom.comp (cohomologyComparisonHom f E)

/-- **The equation characterizing the comparison map.** On the class of a map `α : Iₑ → E` the
comparison map of Stacks 08DC is the hypercohomology class over `U` of the restriction of `α`,
precomposed with the isomorphism `𝒪_U ≅ Iₑ|_U` inverse to the restriction of `Iₑ → 𝒪_X`.  A
homomorphism out of a colimit is determined by its restrictions to the stages, so this
determines the comparison map. -/
public lemma cohomologyComparison_colimit_ι (f : Fin r → A) (E : derivedCat A) (e : ℕ)
    (α : (koszulDerivedSystem f).obj (op e) ⟶ E) :
    cohomologyComparison f E (colimit.ι (homGroupSystem f E) e α) =
      sectionsEquivOfUnion f E
        ((restrictionIsoOfUnion f e).hom ≫ (restrictionToUnion f).map α) :=
  congrArg (sectionsEquivOfUnion f E) (cohomologyComparisonHom_colimit_ι f E e α)

/-- **The homomorphism into the group of morphisms `𝒪_U ⟶ E|_U` is natural in `E`.**
Postcomposition with `g : E ⟶ E'` on the morphism groups out of the Koszul system corresponds
to the map induced by `g` on morphisms out of `𝒪_U`. -/
public lemma cohomologyComparisonHom_naturality (f : Fin r → A) (E E' : derivedCat A)
    (g : E ⟶ E') (x : ↥(colimit (homGroupSystem f E))) :
    cohomologyComparisonHom f E' ((colim.map (Functor.whiskerLeft
        (koszulDerivedSystem f).rightOp (preadditiveYoneda.map g))) x) =
      ((sectionsOnUnionHom f).map g).hom (cohomologyComparisonHom f E x) := by
  have heq : colim.map (Functor.whiskerLeft (koszulDerivedSystem f).rightOp
          (preadditiveYoneda.map g)) ≫ colimit.desc _ (restrictionCocone f E') =
      colimit.desc _ (restrictionCocone f E) ≫ (sectionsOnUnionHom f).map g := by
    refine colimit.hom_ext fun e ↦ ?_
    rw [← Category.assoc, colimit.ι_map, Category.assoc, colimit.ι_desc]
    refine Eq.trans ?_ (colimit.ι_desc_assoc (restrictionCocone f E) e _).symm
    ext α
    exact iso_hom_comp_map_comp_right (restrictionToUnion f) (restrictionIsoOfUnion f e) α g
  exact ConcreteCategory.congr_hom heq x

end Koszul.DerivedSystem

end
