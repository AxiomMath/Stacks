module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering

/-!
# Derived sections and derived global sections on the fppf site of a stack

Let `𝒳` be a category fibred in groupoids over the big fppf category of a scheme `S` contained
in a big fppf site `B`, and give its total category the fppf topology of Stacks 06TP. This file
provides the derived functors used to state the vanishing results of the chapter on derived
categories of stacks:

* `R Γ(x, -)`, unbounded derived sections over an object `x` of the site, and
* `R Γ(𝒳, -)`, unbounded derived global sections,

each as the total right derived functor of the corresponding left exact functor on abelian
sheaves, together with the additivity instances those derivations need.

The vanishing statement it is aimed at, Stacks 0H14, is **not** proved here; see the
implementation notes.

## Main definitions

* `AlgebraicGeometry.Stack.derivedSections`: unbounded derived sections over an object of the
  fppf site of `𝒳`.
* `AlgebraicGeometry.Stack.derivedGlobalSections`: unbounded derived global sections on the
  fppf site of `𝒳`.

## Main results

* `AlgebraicGeometry.Stack.isZero_homology_derivedGlobalSections_of_isCoveringFamily`: all
  global hypercohomology groups of a complex of abelian fppf sheaves vanish once each of its
  homology sheaves has vanishing sections on a family of objects covering every object of the
  site.

## Implementation notes

Stacks 0H14 says that a complex `K` of abelian fppf sheaves on an algebraic stack has vanishing
global hypercohomology as soon as `R Γ(x, K) = 0` for every object `x` lying over an affine
scheme whose morphism to `𝒳` is flat. Its proof is in two halves. The second half is the
vanishing argument "the homology sheaves vanish on a family covering every object, hence the
complex is zero, hence its derived global sections vanish"; that half is general site theory and
is what the result above is, through
`CategoryTheory.Sheaf.isZero_derived_of_isCoveringFamily`. The first half passes to the
flat-fppf site of Stacks 08MZ and uses the comparison of Stacks 0H10, which identifies derived
sections and derived global sections across the morphism of topoi between the fppf site and its
flat-fppf subsite; the flat-fppf site is not yet available in this library, and the hypothesis
of 0H14 is a statement about flat affine objects only, which do *not* cover every object of the
fppf site.

Passing from the vanishing of derived sections `R Γ(x, K)` to the vanishing of the sections of
the homology sheaves of `K` at `x` — hypercohomology against cohomology sheaves — is a further
missing input: it is the statement that an unbounded total right derived functor is computed on
K-injective resolutions, which Mathlib currently has only in the bounded-below case
(`CochainComplex.Plus.localizerMorphism`).

The same gap is why the result above carries the hypothesis that derived global sections
preserve zero morphisms. `CategoryTheory.Functor.totalRightDerived` is a left Kan extension
along a localization functor and carries no additivity instance: additivity would follow from
`CategoryTheory.Functor.isTriangulated_of_leftExtension`, whose hypothesis is precisely that the
unit of the derivation is an isomorphism on a cofinal class of triangles, i.e. again that the
derived functor is computed by resolutions. For the bounded-below case this library has it,
through `CategoryTheory.Functor.isIso_totalRightDerivedUnit_app_of_rightAcyclic` in
`StacksFrontier/Algebra/Homology/DerivedCategory/RightDerivedFunctorInjective.lean`; in the
unbounded case it is open, so the condition is left as an instance argument rather than
silently assumed. -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- Sections of abelian sheaves over an object of the fppf site of `𝒳` form an additive
functor. -/
instance sections_additive (x : 𝒳.val.obj) :
    ((sheafSections (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj (op x)).Additive where
  map_add := rfl

/-- Global sections of abelian sheaves on the fppf site of `𝒳` form an additive functor: the
global sections functor is a right adjoint, so it preserves binary products. -/
instance globalSections_additive
    [HasSheafify (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}] :
    (Sheaf.Γ (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Unbounded derived sections over an object of the fppf site of `𝒳`: the total right derived
functor of sections over that object. -/
abbrev derivedSections (x : 𝒳.val.obj)
    [HasSheafify (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}]
    [((((sheafSections (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
        (op x)).mapHomotopyCategory (.up ℤ)) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) (.up ℤ))] :
    DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) ⥤
      DerivedCategory AddCommGrpCat.{u + 1} :=
  (((sheafSections (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
      (op x)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) (.up ℤ))

/-- Unbounded derived global sections on the fppf site of `𝒳`: the total right derived functor
of global sections. -/
abbrev derivedGlobalSections
    [HasSheafify (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}]
    [HasGlobalSectionsFunctor (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}]
    [((Sheaf.Γ (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}) (.up ℤ))] :
    DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}) ⥤
      DerivedCategory AddCommGrpCat.{v} :=
  ((Sheaf.Γ (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived
    DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{v}) (.up ℤ))

/-- If the homology sheaves of a complex of abelian fppf sheaves on `𝒳` have no sections over
the objects of a family covering every object of the fppf site, then all of its global
hypercohomology groups vanish.

The complex is zero by `CategoryTheory.Sheaf.isZero_derived_of_isCoveringFamily`, and a derived
functor of an additive functor carries a zero object to a zero object. -/
theorem isZero_homology_derivedGlobalSections_of_isCoveringFamily
    [HasSheafify (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}]
    [((Sheaf.Γ (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
        DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) (.up ℤ))]
    [(derivedGlobalSections.{u, u + 1} B S hS 𝒳).PreservesZeroMorphisms]
    {P : ObjectProperty 𝒳.val.obj}
    (hP : (fppfTopology B S hS 𝒳).IsCoveringFamily P)
    (K : DerivedCategory (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}))
    (hK : ∀ (n : ℤ) (y : 𝒳.val.obj), P y →
      IsZero (((DerivedCategory.homologyFunctor
        (Sheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}) n).obj K).obj.obj (op y)))
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} i).obj
      ((derivedGlobalSections.{u, u + 1} B S hS 𝒳).obj K)) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} i).map_isZero
    ((derivedGlobalSections.{u, u + 1} B S hS 𝒳).map_isZero
      (Sheaf.isZero_derived_of_isCoveringFamily hP K hK))

end AlgebraicGeometry.Stack

end
