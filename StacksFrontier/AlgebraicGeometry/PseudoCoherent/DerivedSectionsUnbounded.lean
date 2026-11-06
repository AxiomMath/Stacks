module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedSectionsComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence of derived sections of an arbitrary complex

Let `f : X ⟶ S` be a morphism of schemes locally of finite type. This file compares relative
`m`-pseudo-coherence of an object `E` of `D_{QCoh}(𝒪_X)` with `m`-pseudo-coherence of the
complexes of sections `RΓ(U, E)` over the compatible pairs of affine opens `U ⊆ f ⁻¹ᵁ V`, for
every object of `D_{QCoh}(𝒪_X)`, with no boundedness hypothesis.

## Main definitions

* `AlgebraicGeometry.derivedSectionsUnbounded`: `RΓ(U, -) : D(𝒪_X) ⥤ D(Γ(X, U))`, the total
  right derived functor of sections over `U` on the unbounded derived category.
* `AlgebraicGeometry.derivedSectionsUnboundedUnit` and
  `AlgebraicGeometry.derivedSectionsUnboundedUnitPlus`: the comparison exhibiting it as that
  right derived functor, in the unbounded and the bounded below shape.
* `AlgebraicGeometry.Scheme.Hom.DerivedSectionsPseudoCoherentOn'`: `RΓ(U, E)` is
  `m`-pseudo-coherent relative to `Γ(S, V)`, at one compatible pair of affine opens, for an
  arbitrary object `E` of `D(𝒪_X)`.
* `AlgebraicGeometry.DerivedSectionsPseudoCoherentComparison'`: relative `m`-pseudo-coherence of
  `E`, the condition on one affine open covering and the condition at every compatible pair of
  affine opens are equivalent, for an arbitrary object `E` of `D_{QCoh}(𝒪_X)`.

## Main results

* `AlgebraicGeometry.derivedSectionsUnboundedιIso`: on bounded below objects, unbounded derived
  sections agree with the bounded below derived sections `Stacks.Cohomology.derivedSections`.
* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPseudoCoherentOn'_ι_obj_iff`: the condition at a
  compatible pair of affine opens is the same whether it is read through the unbounded or the
  bounded below derived sections.
* `AlgebraicGeometry.exists_affineCover_derivedSectionsPseudoCoherentOn'`: if `RΓ(U, E)` is
  `m`-pseudo-coherent relative to `Γ(S, V)` at every compatible pair of affine opens, then it is
  so on some affine open covering, for an arbitrary object `E` of `D(𝒪_X)`.

## References

* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Definition 15.82.4 (065I)](https://stacks.math.columbia.edu/tag/065I)
* [The Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [The Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

section Sections

variable (X : Scheme.{u}) (U : X.Opens)

/-- `RΓ(U, -)`, the derived sections over an open subscheme `U`, on the unbounded derived
category of `𝒪_X`-modules: the total right derived functor of
`Stacks.Cohomology.sectionsFunctor` along the quasi-isomorphisms of cochain complexes. -/
public abbrev derivedSectionsUnbounded :
    DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, U)) :=
  ((Stacks.Cohomology.sectionsFunctor X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The canonical comparison from the termwise sections of a cochain complex of `𝒪_X`-modules to
its unbounded derived sections: the unit exhibiting `AlgebraicGeometry.derivedSectionsUnbounded`
as a right derived functor of sections. -/
public abbrev derivedSectionsUnboundedUnit :
    (Stacks.Cohomology.sectionsFunctor X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsUnbounded X U :=
  ((Stacks.Cohomology.sectionsFunctor X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))

/-- The comparison `AlgebraicGeometry.derivedSectionsUnboundedUnit` restricted to bounded below
complexes. -/
public abbrev derivedSectionsUnboundedUnitPlus :
    (Stacks.Cohomology.sectionsFunctor X U).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Qh ⋙ (DerivedCategory.Plus.ι ⋙ derivedSectionsUnbounded X U) :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι X.Modules) (derivedSectionsUnboundedUnit X U)

/-- Unbounded derived sections, restricted to the bounded below derived category, are a right
derived functor of sections along the quasi-isomorphisms of bounded below complexes, with unit
`AlgebraicGeometry.derivedSectionsUnboundedUnitPlus`. -/
public instance isRightDerivedFunctor_derivedSectionsUnboundedUnitPlus :
    (DerivedCategory.Plus.ι ⋙ derivedSectionsUnbounded X U).IsRightDerivedFunctor
      (derivedSectionsUnboundedUnitPlus X U) (HomotopyCategory.Plus.quasiIso X.Modules) := by
  apply (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso
  intro K
  obtain ⟨n, hn⟩ : CochainComplex.plus X.Modules
      ((InjectiveObject.ι X.Modules).mapHomotopyCategoryPlus.obj K).obj.as :=
    (HomotopyCategory.plus_quotient_obj_iff _).1
      ((InjectiveObject.ι X.Modules).mapHomotopyCategoryPlus.obj K).property
  have := CochainComplex.isKInjective_of_injective
    ((InjectiveObject.ι X.Modules).mapHomotopyCategoryPlus.obj K).obj.as n
  exact Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _
    (derivedSectionsUnboundedUnit X U)
    ((InjectiveObject.ι X.Modules).mapHomotopyCategoryPlus.obj K).obj.as

/-- On bounded below complexes the two derived sections functors agree: the restriction of the
unbounded derived sections `AlgebraicGeometry.derivedSectionsUnbounded` to the bounded below
derived category is isomorphic to `Stacks.Cohomology.derivedSections` followed by the inclusion
of the bounded below derived category into the unbounded one. -/
@[sga "4 XVII 1.2.4" "special case"]
public def derivedSectionsUnboundedιIso :
    DerivedCategory.Plus.ι ⋙ derivedSectionsUnbounded X U ≅
      Stacks.Cohomology.derivedSections X U ⋙ DerivedCategory.Plus.ι :=
  have : (Stacks.Cohomology.derivedSections X U ⋙ DerivedCategory.Plus.ι).IsRightDerivedFunctor
      (Functor.whiskerRight (Stacks.Cohomology.sectionsFunctor X U).rightDerivedFunctorPlusUnith
        DerivedCategory.Plus.ι) (HomotopyCategory.Plus.quasiIso X.Modules) :=
    Functor.isRightDerivedFunctor_postcomp (Stacks.Cohomology.sectionsFunctor X U)
      DerivedCategory.Plus.ι
  Functor.rightDerivedNatIso _ _ (derivedSectionsUnboundedUnitPlus X U)
    (Functor.whiskerRight (Stacks.Cohomology.sectionsFunctor X U).rightDerivedFunctorPlusUnith
      DerivedCategory.Plus.ι)
    (HomotopyCategory.Plus.quasiIso X.Modules) (Iso.refl _)

end Sections

section Comparison

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For a compatible pair of affine opens `U ⊆ f ⁻¹ᵁ V` and an arbitrary object `E` of the
derived category of `𝒪_X`-modules, the complex of `Γ(X, U)`-modules `RΓ(U, E)`, taken with
`AlgebraicGeometry.derivedSectionsUnbounded`, is `m`-pseudo-coherent relative to `Γ(S, V)`, where
`Γ(X, U)` is a finite type `Γ(S, V)`-algebra through `f`. -/
public abbrev Scheme.Hom.DerivedSectionsPseudoCoherentOn' [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ) {U : X.Opens} (hU : IsAffineOpen U)
    {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) : Prop :=
  letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  letI : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  PseudoCoherence.IsRelativelyPseudoCoherentFrom (R := Γ(S, V)) (A := Γ(X, U))
    ((derivedSectionsUnbounded X U).obj E) m

/-- For a bounded below object `E` and a compatible pair of affine opens, relative
`m`-pseudo-coherence of the unbounded derived sections of `DerivedCategory.Plus.ι.obj E` is
equivalent to relative `m`-pseudo-coherence of the bounded below derived sections of `E`. -/
public theorem Scheme.Hom.derivedSectionsPseudoCoherentOn'_ι_obj_iff [LocallyOfFiniteType f]
    (E : DerivedCategory.Plus X.Modules) (m : ℤ) {U : X.Opens} (hU : IsAffineOpen U)
    {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) :
    f.DerivedSectionsPseudoCoherentOn' (DerivedCategory.Plus.ι.obj E) m hU hV e ↔
      f.DerivedSectionsPseudoCoherentOn E m hU hV e :=
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have : Algebra.FiniteType Γ(S, V) Γ(X, U) := algebraFiniteType_appLE f U hU V hV e
  PseudoCoherence.isRelativelyPseudoCoherentFrom_iff_of_iso (R := Γ(S, V))
    ((derivedSectionsUnboundedιIso X U).app E) m

/-- For `f : X ⟶ S` locally of finite type, `E` an object of the derived category of
`𝒪_X`-modules all of whose cohomology sheaves are quasi-coherent, and `m` an integer, the
following three conditions are equivalent:

1. `E` is `m`-pseudo-coherent relative to `S`, that is
   `AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFrom`;
2. there are an affine open covering of `S` and, over each of its members `V i`, an affine open
   covering of `f ⁻¹ᵁ V i` such that `RΓ(U, E)` is `m`-pseudo-coherent relative to `Γ(S, V i)`
   for each member `U` of the latter;
3. `RΓ(U, E)` is `m`-pseudo-coherent relative to `Γ(S, V)` for *every* compatible pair of affine
   opens `U ⊆ f ⁻¹ᵁ V`. -/
public abbrev DerivedSectionsPseudoCoherentComparison' [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules)
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (m : ℤ) : Prop :=
  List.TFAE [
    Scheme.Hom.IsPseudoCoherentFrom f E m,
    ∃ (ι : Type u) (V : ι → S.affineOpens),
      (⨆ i, (V i : S.Opens)) = ⊤ ∧
        ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens),
          (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
            ∀ j, ∃ h : (U j).1 ≤ f ⁻¹ᵁ (V i).1,
              f.DerivedSectionsPseudoCoherentOn' E m (U j).2 (V i).2 h,
    ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V), f.DerivedSectionsPseudoCoherentOn' E m hU hV e]

/-- For an arbitrary object `E` of the derived category of `𝒪_X`-modules, if the derived sections
`RΓ(U, E)` are `m`-pseudo-coherent relative to `Γ(S, V)` for every compatible pair of affine
opens, then this holds on an affine open covering: all the affine opens of `S`, and over each of
them all the affine opens of `X` contained in its inverse image. -/
public theorem exists_affineCover_derivedSectionsPseudoCoherentOn' [LocallyOfFiniteType f]
    (E : DerivedCategory X.Modules) (m : ℤ)
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
      (e : U ≤ f ⁻¹ᵁ V), f.DerivedSectionsPseudoCoherentOn' E m hU hV e) :
    ∃ (ι : Type u) (V : ι → S.affineOpens),
      (⨆ i, (V i : S.Opens)) = ⊤ ∧
        ∀ i, ∃ (κ : Type u) (U : κ → X.affineOpens),
          (⨆ j, (U j : X.Opens)) = f ⁻¹ᵁ (V i).1 ∧
            ∀ j, ∃ h : (U j).1 ≤ f ⁻¹ᵁ (V i).1,
              f.DerivedSectionsPseudoCoherentOn' E m (U j).2 (V i).2 h :=
  ⟨S.affineOpens, id, iSup_affineOpens_eq_top S, fun V ↦
    ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.Opens)}, fun U ↦ U.1,
      iSup_affineOpens_subtype_eq _, fun U ↦ ⟨U.2, h _ U.1.2 _ V.2 _⟩⟩⟩

end Comparison

end AlgebraicGeometry

end
