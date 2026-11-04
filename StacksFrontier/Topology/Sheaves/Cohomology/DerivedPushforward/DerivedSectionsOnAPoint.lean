module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalCupProductOnAPoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnePointModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors

/-!
# Derived global sections on the one-point ringed space

Let `R` be a commutative ring and let `({*}, R)` be the one-point ringed space.  Taking sections
on the whole space is one half of the identification `Mod(𝒪_{({*}, R)}) ≌ Mod(R)`, so it is
exact, and therefore its total right derived functor is the functor it induces termwise on
derived categories:

`RΓ({*}, -) : D(𝒪_{({*}, R)}) ⥤ D(R)`

is the derived functor of an equivalence of abelian categories, and in particular it has a left
adjoint.  That left adjoint is the one datum of
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison` that the degenerate witness over
the zero ring supplies only because every object there vanishes; here it is constructed over an
arbitrary ring, and for a nontrivial ring derived global sections do not vanish identically, so
the zero morphism of bifunctors is not a unital global cup product.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointSectionsEquivalence` — the identification
  `Mod(Γ({*}, 𝒪)) ≌ Mod(𝒪_{({*}, R)})` whose quasi-inverse is, on the nose, sections on the whole
  space.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedSectionsIso` — **derived global
  sections on the point are sections**: the canonical comparison
  `RΓ({*}, -) ≅ Γ({*}, -)` of derived functors is an isomorphism.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointDerivedAdjunction` — **a left adjoint of
  `RΓ({*}, -)`**, namely the functor induced on derived categories by the quasi-inverse of
  `onePointSectionsEquivalence`.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.onePointComparisonOnAPoint` — a one-point comparison
  on `({*}, R)` for an arbitrary `R`.

## Main results

* `Stacks.Cohomology.DerivedSectionsOnAPoint.not_forall_isZero_baseSections` — over a nontrivial
  ring, derived global sections on `({*}, R)` do not kill every object of `D(𝒪_{({*}, R)})`.
* `Stacks.Cohomology.DerivedSectionsOnAPoint.not_isGlobalCupProduct_zero` — hence the zero
  morphism of bifunctors is not a unital global cup product on `({*}, R)`, so
  `onePointComparisonOnAPoint` lives on a ringed space with nonvanishing derived global
  sections.

## Implementation notes

*Why sections on the point are exact.*  `Stacks.AssociatedSheaf.onePointEquivalence` is an
equivalence of abelian categories whose quasi-inverse is sections on the whole space read as an
`R`-module through the ring isomorphism `R ≅ Γ({*}, 𝒪)`.  Composing it with the equivalence of
module categories that this ring isomorphism induces, and replacing the quasi-inverse by the
isomorphic functor `SheafOfModules.evaluation _ ⊤`, produces an equivalence whose inverse *is*
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen`, so that functor inherits exactness and
additivity from being one half of an equivalence.

*Why the derived functor is the induced one.*  Both
`Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen` and
`CategoryTheory.Functor.mapDerivedCategory` are right derived functors of sections read on the
homotopy category of cochain complexes: the first by construction, the second by
`Stacks.DerivedFunctor.HigherDerivedOfExact.everywhere_defined`, which is available exactly
because sections are exact.  The comparison induced by the universal property is therefore
invertible.

*Where the left adjoint comes from.*  An adjunction between exact functors descends to derived
categories along the localizations `Q`, by `CategoryTheory.Adjunction.localization` applied to the
adjunction of the equivalence read termwise on cochain complexes.  Transporting the resulting
adjunction along `onePointDerivedSectionsIso` gives the left adjoint of `RΓ({*}, -)` itself.

*What the comparison of bifunctors is.*  The field
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison.tensorComparison` asks only for a
morphism of bifunctors `L(x ⊗^𝐋_A y) ⟶ L x ⊗^𝐋_{𝒪_S} L y`, and the one used here is the zero
morphism: a comparison of the derived tensor product over `A = Γ(S, 𝒪_S)` with the derived tensor
product over the structure sheaf, which is what
`Stacks.Cohomology.DerivedGlobalCupProduct.OnePointComparison.IsUnitalWith` constrains, is not
constructed here.  It is constructed — as an *isomorphism*, and on an arbitrary ringed space —
by `Stacks.Cohomology.DerivedSectionsLeftAdjoint.derivedSectionsTensorIso`, and that is the
field carried by
`Stacks.Cohomology.DerivedSectionsLeftAdjoint.onePointComparisonOnARingedSpace`; the witness
below keeps the zero morphism, nothing stated about it asking for more.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AssociatedSheaf
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.GlobalKunneth

universe u

namespace Stacks.Cohomology.DerivedSectionsOnAPoint

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-! ### Sections on the one-point ringed space -/

/-- The one-point ringed space with ring `R`, as a ringed space over which derived global
sections are taken. -/
abbrev onePointRingedSpace : RingedSpace.{u, u} := coefficientPoint (CommRingCat.of R)

/-- The quasi-inverse of the one-point identification is sections on the whole space, followed by
restriction of scalars along `R ≅ Γ({*}, 𝒪)`. -/
theorem onePointEquivalence_inverse_eq :
    (onePointEquivalence R).inverse =
      sectionsOverOpen (onePointRingedSpace R) ⊤ ⋙
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (coefficientRingEquiv (R := R))).functor :=
  onePointEquivalence_inverse R

/-- **The one-point identification, with sections on the whole space as its quasi-inverse.**  An
`Γ({*}, 𝒪)`-module is the same thing as a sheaf of modules on `({*}, R)`, and the identification
sends a sheaf to its sections. -/
def onePointSectionsEquivalence :
    ModuleCat.{u} (baseRing (onePointRingedSpace R)) ≌
      SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)) :=
  ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv (coefficientRingEquiv (R := R))).trans
      (onePointEquivalence R)).changeInverse
    (eqToIso (congrArg
        (fun F => F ⋙ (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (coefficientRingEquiv (R := R))).inverse) (onePointEquivalence_inverse_eq R)) ≪≫
      Functor.isoWhiskerLeft (sectionsOverOpen (onePointRingedSpace R) ⊤)
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (coefficientRingEquiv (R := R))).unitIso.symm ≪≫
      (sectionsOverOpen (onePointRingedSpace R) ⊤).rightUnitor)

/-- The quasi-inverse of `onePointSectionsEquivalence` is sections on the whole space. -/
theorem onePointSectionsEquivalence_inverse :
    (onePointSectionsEquivalence R).inverse = sectionsOverOpen (onePointRingedSpace R) ⊤ := rfl

/-- Sections on the whole space of the one-point ringed space are an equivalence of abelian
categories, hence exact. -/
instance sectionsOverOpen_onePointRingedSpace_isEquivalence :
    (sectionsOverOpen (onePointRingedSpace R) ⊤).IsEquivalence :=
  (onePointSectionsEquivalence R).isEquivalence_inverse

/-- The one-point identification is additive, being one half of an equivalence of additive
categories. -/
instance onePointSectionsEquivalence_functor_additive :
    (onePointSectionsEquivalence R).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Sections on the whole space of the one-point ringed space are additive, being the other half
of the same equivalence of additive categories. -/
instance onePointSectionsEquivalence_inverse_additive :
    (onePointSectionsEquivalence R).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### Derived global sections on the point are sections -/

/-- The comparison `RΓ({*}, -) ⟶ Γ({*}, -)` from derived global sections to the functor induced
termwise by sections, given by the universal property of the right derived functor. -/
def onePointDerivedSectionsComparison :
    baseSections (onePointRingedSpace R) ⟶
      (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategory :=
  (derivedSectionsOverOpen (onePointRingedSpace R) ⊤).rightDerivedDesc
    (derivedSectionsOverOpenUnit (onePointRingedSpace R) ⊤)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)))
      (ComplexShape.up ℤ)) _
    (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical
      (sectionsOverOpen (onePointRingedSpace R) ⊤))

/-- **Derived global sections on the one-point ringed space are sections.**  Sections there are
exact, so the functor they induce termwise on derived categories is already a right derived
functor, and the comparison out of `RΓ({*}, -)` is invertible. -/
instance isIso_onePointDerivedSectionsComparison :
    IsIso (onePointDerivedSectionsComparison R) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _
      (derivedSectionsOverOpenUnit (onePointRingedSpace R) ⊤) _ _
      (Stacks.DerivedFunctor.HigherDerivedOfExact.canonical
        (sectionsOverOpen (onePointRingedSpace R) ⊤))).1
    (Stacks.DerivedFunctor.HigherDerivedOfExact.everywhere_defined
      (sectionsOverOpen (onePointRingedSpace R) ⊤)).2

/-- The natural isomorphism `RΓ({*}, -) ≅ Γ({*}, -)` of
`isIso_onePointDerivedSectionsComparison`. -/
def onePointDerivedSectionsIso :
    baseSections (onePointRingedSpace R) ≅
      (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategory :=
  asIso (onePointDerivedSectionsComparison R)

/-! ### The left adjoint of derived global sections on the point -/

/-- The one-point identification commutes with the localizations defining the derived
categories. -/
instance catCommSq_onePointSectionsEquivalence_functor :
    CatCommSq ((onePointSectionsEquivalence R).mapHomologicalComplex (ComplexShape.up ℤ)).functor
      DerivedCategory.Q DerivedCategory.Q
      (onePointSectionsEquivalence R).functor.mapDerivedCategory :=
  ⟨((onePointSectionsEquivalence R).functor.mapDerivedCategoryFactors).symm⟩

/-- Sections on the whole space commute with the localizations defining the derived
categories. -/
instance catCommSq_onePointSectionsEquivalence_inverse :
    CatCommSq ((onePointSectionsEquivalence R).mapHomologicalComplex (ComplexShape.up ℤ)).inverse
      DerivedCategory.Q DerivedCategory.Q
      (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategory :=
  ⟨((sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategoryFactors).symm⟩

/-- **The one-point identification on derived categories, as an adjunction.**  The adjunction of
`onePointSectionsEquivalence`, read termwise on cochain complexes, descends along the
localizations `Q` because both of its functors are exact. -/
def onePointDerivedSectionsAdjunction :
    (onePointSectionsEquivalence R).functor.mapDerivedCategory ⊣
      (sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategory :=
  Adjunction.localization
    ((onePointSectionsEquivalence R).mapHomologicalComplex (ComplexShape.up ℤ)).toAdjunction
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat.{u} (baseRing (onePointRingedSpace R)))
      (ComplexShape.up ℤ))
    DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R)))
      (ComplexShape.up ℤ))
    _ _

/-- **A left adjoint of derived global sections on the one-point ringed space**, for an arbitrary
ring `R`: the functor induced on derived categories by the one-point identification, transported
along `onePointDerivedSectionsIso`. -/
def onePointDerivedAdjunction :
    (onePointSectionsEquivalence R).functor.mapDerivedCategory ⊣
      baseSections (onePointRingedSpace R) :=
  Adjunction.ofNatIsoRight (onePointDerivedSectionsAdjunction R)
    (onePointDerivedSectionsIso R).symm

/-! ### A one-point comparison on the one-point ringed space -/

/-- **A one-point comparison on `({*}, R)` for an arbitrary ring `R`**: the left adjoint of
derived global sections is `onePointDerivedAdjunction`, and the comparison of bifunctors is the
zero morphism, which is all that the structure requires. -/
def onePointComparisonOnAPoint : OnePointComparison (onePointRingedSpace R) where
  pullback := (onePointSectionsEquivalence R).functor.mapDerivedCategory
  adjunction := onePointDerivedAdjunction R
  tensorComparison := 0

/-! ### Nonvanishing of derived global sections on the point -/

/-- **Derived global sections on `({*}, R)` do not vanish identically** when `R` is nontrivial:
they send the sheaf attached to `R` itself, placed in degree `0`, to a complex with nonzero
cohomology. -/
theorem not_forall_isZero_baseSections [Nontrivial R] :
    ¬ ∀ U : DerivedCategory (SheafOfModules.{u} (structureSheafRing (onePointRingedSpace R))),
        IsZero ((baseSections (onePointRingedSpace R)).obj U) := by
  intro h
  set N := (onePointEquivalence R).functor.obj (ModuleCat.of R R) with hN
  have h0 := h ((DerivedCategory.singleFunctor _ 0).obj N)
  have h1 : IsZero (((sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategory).obj
      ((DerivedCategory.singleFunctor _ 0).obj N)) :=
    h0.of_iso ((onePointDerivedSectionsIso R).app _).symm
  have h2 : IsZero ((DerivedCategory.singleFunctor
      (ModuleCat.{u} (baseRing (onePointRingedSpace R))) 0).obj
      ((sectionsOverOpen (onePointRingedSpace R) ⊤).obj N)) :=
    h1.of_iso (((sectionsOverOpen (onePointRingedSpace R) ⊤).mapDerivedCategorySingleFunctor
      0).app N).symm
  have h3 : IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (onePointRingedSpace R))) 0).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((sectionsOverOpen (onePointRingedSpace R) ⊤).obj N))) :=
    Functor.map_isZero _ h2
  have h4 : IsZero ((sectionsOverOpen (onePointRingedSpace R) ⊤).obj N) :=
    h3.of_iso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (baseRing (onePointRingedSpace R))) 0).app _).symm
  have h5 : IsZero ((ModuleCat.restrictScalars
      (coefficientRingEquiv (R := R)).toRingHom).obj
      ((sectionsOverOpen (onePointRingedSpace R) ⊤).obj N)) :=
    Functor.map_isZero _ h4
  have h6 : IsZero ((onePointEquivalence R).inverse.obj N) :=
    (congrFun (congrArg Functor.obj (onePointEquivalence_inverse_eq R)) N) ▸ h5
  have h7 : IsZero (ModuleCat.of R R) :=
    h6.of_iso ((onePointEquivalence R).unitIso.app (ModuleCat.of R R))
  exact one_ne_zero (congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R =>
    ModuleCat.Hom.hom f (1 : R)) (h7.eq_of_src (𝟙 (ModuleCat.of R R)) 0))

/-- **The zero morphism of bifunctors is not a unital global cup product on `({*}, R)`** when `R`
is nontrivial.  By `Stacks.Cohomology.DerivedGlobalCupProduct.isGlobalCupProduct_zero_iff` this is
exactly the statement that derived global sections there do not vanish identically, so
`onePointComparisonOnAPoint` is a one-point comparison on a ringed space carrying cohomology. -/
theorem not_isGlobalCupProduct_zero [Nontrivial R] :
    ¬ IsGlobalCupProduct (0 : GlobalCupProduct (onePointRingedSpace R)) :=
  fun h => not_forall_isZero_baseSections R (isGlobalCupProduct_zero_iff.1 h)

end Stacks.Cohomology.DerivedSectionsOnAPoint

end
