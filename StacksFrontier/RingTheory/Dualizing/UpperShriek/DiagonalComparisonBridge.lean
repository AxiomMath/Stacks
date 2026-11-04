module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparison

/-!
# The hypothesis of Comparison I, read against the counit of extension of scalars

`StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparison` proves **Comparison I** of
[stacks 0E2H] -- derived restriction of scalars carries the `B`-linear tensor--Hom diagonal along
`φ : A →+* B` to the single-ring tensor--Hom diagonal at the algebra -- from one hypothesis,
written out there rather than named: that the projection formula
`Dualizing.ProjectionFormula.derivedProjNatIso` is linear for the action
`Dualizing.ProjectionFormula.restrictedAction` of the algebra `T = i_*(1_B)`.

`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit`, on the other hand, names
`Dualizing.ProjectionFormula.ProjCounitCompat`: the compatibility of the projection formula with
the counit `ε` of [stacks 0GMT] and the lax monoidal structure map `μ` of derived base change,
equivalently (`Dualizing.ProjectionFormula.projCounitCompatAt_iff_inv_eq`) the statement that
the inverse projection formula is the morphism the two adjunctions produce by themselves.

This file relates the two.

## Main results

* `Dualizing.ProjectionFormula.restrictedAction_comp_derivedProj_iff` -- **the algebra action
  cancels off the left.**  The linearity hypothesis holds exactly when the *restricted counit* of
  [stacks 0GMT] commutes with the projection formula.  Both sides of the hypothesis are
  precomposed with `Dualizing.ProjectionFormula.restrictExtendIso`, which turns the action into
  `i_*(ε)` on the left and, by naturality, the action-tensored morphism into `i_*Ext` of it on the
  right.
* `Dualizing.ProjectionFormula.restrictedAction_comp_derivedProj_of_projCounitCompatAt` -- **the
  linearity hypothesis from `ProjCounitCompat` and one further coherence.**
* `restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal_of_projCounitCompatAt` and
  `isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_projCounitCompatAt`, both in the
  namespace `Dualizing.ProjectionFormula` -- hence **Comparison I, and the invertibility
  [stacks 0E2H] needs, on named coherences only.**

## What the two vocabularies differ by

Writing `M = i_*G`, the hypothesis of Comparison I at `(Y, G)` is, after the cancellation above,

`i_*(ε_{G ⊗ᴸ_B Ext Y}) ≫ proj = i_*Ext(proj ≫ swap) ≫ r ≫ assoc ≫ (𝟙 ⊗ a) ≫ swap`,

and `ProjCounitCompat` computes `ε_{G ⊗ᴸ_B Ext Y}` as `Ext(proj) ≫ ν ≫ (ε_G ⊗ 𝟙)`, with `ν` the
inverse of `μ`.  Cancelling the isomorphism `i_*Ext(proj)` off both sides and moving the counit
out of the way by naturality of the projection formula in the object of `D(B)` leaves an equation
in which no counit and no object of `D(B)` occurs at all:
`Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat`, the statement that `proj`, `ν` and
`Dualizing.ProjectionFormula.restrictExtendIso` compose to the symmetry rearrangement
`(M ⊗ᴸ_A Y) ⊗ᴸ_A T ≅ (M ⊗ᴸ_A T) ⊗ᴸ_A Y`.

So the two obligations are *not* literally the same: the linearity hypothesis of Comparison I is
`ProjCounitCompat` **plus** that rearrangement, and this file proves exactly that implication.
Nothing here discharges either one.

They are not independent either, and
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCanonical` measures by how much:
`ProjTensorBaseChangeCompat` mentions the projection formula at exactly three pairs -- at
`(M ⊗ᴸ_A Y, 1_B)` and `(M, 1_B)` through `restrictExtendIso`, and at `(Y, Ext M)` directly --
and `Dualizing.ProjectionFormula.projTensorBaseChangeCompat_iff_canonical` shows that granted
`ProjCounitCompatAt` at those three pairs it becomes
`Dualizing.ProjectionFormula.CanonicalProjTensorBaseChangeCompat`, in which the projection
formula does not occur at all: an identity among the unit and counit of [stacks 0GMT], the
section `ν` of `μ`, and the unitor, symmetry and associator of [stacks 0A63].

No `@[stacks]` attribute is placed here: nothing in this file is unconditional, and the
identities it proves belong to the tags of the morphisms they are about.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

universe u v

namespace Dualizing.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Dualizing.extendScalarsAdditiveOfRingHom

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The algebra action, precomposed with `restrictExtendIso`, is the restricted counit. -/
private theorem restrictExtendIso_hom_comp_restrictedAction (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) (adjE : E.functor ⊣ iStar)
    (G : DerivedCategory (ModuleCat.{max u v} B)) :
    (restrictExtendIso.{u, v} φ E iStar adj).hom.app (iStar.obj G) ≫
        restrictedAction.{u, v} φ E iStar adj adjE G = iStar.map (adjE.counit.app G) := by
  dsimp only [restrictedAction]
  rw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

/-- **The linearity hypothesis of Comparison I, with the algebra action cancelled off the left.**
The hypothesis of
`Dualizing.ProjectionFormula.restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal` at
`(Y, G)` holds exactly when derived restriction of the counit of [stacks 0GMT] at `G ⊗ᴸ_B Ext Y`,
followed by the projection formula, is derived restriction of `Ext` of the projection formula
followed by the identification `Dualizing.ProjectionFormula.restrictExtendIso` of restricted
derived extension of scalars with tensoring by the algebra, and then the same rearrangement and
action as before.

Both sides are precomposed with the isomorphism `restrictExtendIso` at `i_*(G ⊗ᴸ_B Ext Y)`: on
the left that turns `Dualizing.ProjectionFormula.restrictedAction` into the restricted counit,
because the action is by definition the inverse of `restrictExtendIso` followed by it, and on the
right it moves past the action-tensored morphism by naturality of `restrictExtendIso`. -/
theorem restrictedAction_comp_derivedProj_iff (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, v, u, max u v + 1, max u v + 1} φ)
    (iStar : DerivedCategory (ModuleCat.{max u v} B) ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (adj : iStar ⊣ Dualizing.derivedHom.{u, v, u} φ) (adjE : E.functor ⊣ iStar)
    (Y : DerivedCategory (ModuleCat.{max u v} A))
    (G : DerivedCategory (ModuleCat.{max u v} B)) :
    (restrictedAction.{u, v} φ E iStar adj adjE
            ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
              (G, E.functor.obj Y)) ≫
          (derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app G =
        (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
                (G, E.functor.obj Y)), restrictedAlgebra.{u, v} iStar))
            (Y := ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
                (Y, iStar.obj G), restrictedAlgebra.{u, v} iStar))
            ((derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app G ≫
              ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
                (iStar.obj G) Y).hom,
              𝟙 (restrictedAlgebra.{u, v} iStar)) ≫
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorAssoc
            Y (iStar.obj G) (restrictedAlgebra.{u, v} iStar)).hom ≫
          (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (Y, (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
                (iStar.obj G, restrictedAlgebra.{u, v} iStar)))
            (Y := (Y, iStar.obj G))
            (𝟙 Y, restrictedAction.{u, v} φ E iStar adj adjE G) ≫
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
            Y (iStar.obj G)).hom) ↔
      (iStar.map (adjE.counit.app ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
              (G, E.functor.obj Y))) ≫
          (derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app G =
        iStar.map (E.functor.map
            ((derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app G ≫
              ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
                (iStar.obj G) Y).hom)) ≫
          (restrictExtendIso.{u, v} φ E iStar adj).hom.app
            ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj (Y, iStar.obj G)) ≫
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorAssoc
            Y (iStar.obj G) (restrictedAlgebra.{u, v} iStar)).hom ≫
          (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
            (X := (Y, (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
                (iStar.obj G, restrictedAlgebra.{u, v} iStar)))
            (Y := (Y, iStar.obj G))
            (𝟙 Y, restrictedAction.{u, v} φ E iStar adj adjE G) ≫
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
            Y (iStar.obj G)).hom) := by
  have hnat : (restrictExtendIso.{u, v} φ E iStar adj).hom.app
        (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
          (G, E.functor.obj Y))) ≫
      (derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.map
          (X := (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
              (G, E.functor.obj Y)), restrictedAlgebra.{u, v} iStar))
          (Y := ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj
              (Y, iStar.obj G), restrictedAlgebra.{u, v} iStar))
          ((derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app G ≫
            ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
              (iStar.obj G) Y).hom,
            𝟙 (restrictedAlgebra.{u, v} iStar)) =
      iStar.map (E.functor.map
          ((derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app G ≫
            ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
              (iStar.obj G) Y).hom)) ≫
        (restrictExtendIso.{u, v} φ E iStar adj).hom.app
          ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensor.obj (Y, iStar.obj G)) :=
    ((restrictExtendIso.{u, v} φ E iStar adj).hom.naturality
      ((derivedProjNatIso.{u, v} φ E iStar adj Y).hom.app G ≫
        ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} A).tensorSwap
          (iStar.obj G) Y).hom)).symm
  constructor
  · intro h
    rw [← restrictExtendIso_hom_comp_restrictedAction φ E iStar adj adjE,
      Category.assoc, h, ← Category.assoc, hnat, Category.assoc]
  · intro h
    refine (cancel_epi ((restrictExtendIso.{u, v} φ E iStar adj).hom.app
      (iStar.obj ((derivedHomAdjunctionOverRing.{u, v, max u v + 1} B).tensor.obj
        (G, E.functor.obj Y))))).mp ?_
    simp only [← Category.assoc]
    rw [restrictExtendIso_hom_comp_restrictedAction φ E iStar adj adjE, hnat]
    simpa only [Category.assoc] using h

/-! ### The projection formula against the lax monoidal structure map -/

/-- **The compatibility of the projection formula with the lax monoidal structure map of derived
base change.**  Writing `Ext` for the model `E`, `i_*` for derived restriction of scalars,
`T = i_*(1_B)` for the algebra, `ν` for the inverse
`Dualizing.derivedTensorBaseChangeSection` of the lax monoidal structure map of derived base
change and `r` for `Dualizing.ProjectionFormula.restrictExtendIso`, this asserts that the
composite

`(M ⊗ᴸ_A Y) ⊗ᴸ_A T --r⁻¹--> i_*Ext(M ⊗ᴸ_A Y) --i_*ν--> i_*(Ext M ⊗ᴸ_B Ext Y) --proj-->
i_*(Ext M) ⊗ᴸ_A Y --r ⊗ 𝟙--> (M ⊗ᴸ_A T) ⊗ᴸ_A Y`

is the rearrangement `(M ⊗ Y) ⊗ T ≅ (M ⊗ T) ⊗ Y` of the symmetry and the associativity of
[stacks 0A63].

Both sides are isomorphisms, no object of `D(B)` occurs and neither counit does: this is purely
the statement that the projection formula, the identification of restricted derived extension of
scalars with tensoring by the algebra, and the monoidality of derived base change fit together.
It is the one coherence beyond
`Dualizing.ProjectionFormula.ProjCounitCompat` that the hypothesis of Comparison I costs; see
`Dualizing.ProjectionFormula.restrictedAction_comp_derivedProj_of_projCounitCompatAt`. -/
def ProjTensorBaseChangeCompat (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (Y M : DerivedCategory (ModuleCat.{max u v} A)) : Prop :=
  (restrictExtendIso.{u, max u v} φ E
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj).inv.app
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y)) ≫
      (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          (Dualizing.derivedTensorBaseChangeSection.{u, u, v} φ E.functor
            (modelComparison.{u, v} φ E) M Y) ≫
        (derivedProjNatIso.{u, max u v} φ E
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj Y).hom.app
            (E.functor.obj M) ≫
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
            (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              (E.functor.obj M), Y))
            (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
              (M, restrictedAlgebra.{u, max u v}
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory), Y))
            ((restrictExtendIso.{u, max u v} φ E
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj).hom.app M, 𝟙 Y) =
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
        (X := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (M, Y),
          restrictedAlgebra.{u, max u v}
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
        (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj (Y, M),
          restrictedAlgebra.{u, max u v}
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
        (((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap M Y).hom,
          𝟙 (restrictedAlgebra.{u, max u v}
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)) ≫
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorAssoc Y M
        (restrictedAlgebra.{u, max u v}
          (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)).hom ≫
      ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap Y
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
          (M, restrictedAlgebra.{u, max u v}
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))).hom

/-- `ProjTensorBaseChangeCompat` with the inverse of `restrictExtendIso` moved to the right-hand
side, as the restricted section followed by the projection formula and `restrictExtendIso`. -/
private theorem ProjTensorBaseChangeCompat.map_section_comp_derivedProj {φ : A →+* B}
    {E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ}
    {adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ}
    {Y M : DerivedCategory (ModuleCat.{max u v} A)}
    (hC : ProjTensorBaseChangeCompat.{u, v} φ E adj Y M) :
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
        (Dualizing.derivedTensorBaseChangeSection.{u, u, v} φ E.functor
          (modelComparison.{u, v} φ E) M Y) ≫
      (derivedProjNatIso.{u, max u v} φ E _ adj Y).hom.app (E.functor.obj M) ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            (E.functor.obj M), Y))
          (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
              (M, restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory), Y))
          ((restrictExtendIso.{u, max u v} φ E _ adj).hom.app M, 𝟙 Y) =
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
        (E.functor.map
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap
            M Y).hom) ≫
      (restrictExtendIso.{u, max u v} φ E _ adj).hom.app
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
            (Y, M)) ≫
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorAssoc Y M
          (restrictedAlgebra.{u, max u v}
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)).hom ≫
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap Y
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
            (M, restrictedAlgebra.{u, max u v}
                (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))).hom := by
  have hr : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          (E.functor.map
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap
              M Y).hom) ≫
        (restrictExtendIso.{u, max u v} φ E _ adj).hom.app
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
            (Y, M)) =
      (restrictExtendIso.{u, max u v} φ E _ adj).hom.app
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
            (M, Y)) ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
              (M, Y),
            restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
          (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
              (Y, M),
            restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
          (((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap
            M Y).hom,
            𝟙 (restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)) :=
    (restrictExtendIso.{u, max u v} φ E _ adj).hom.naturality _
  dsimp only [ProjTensorBaseChangeCompat] at hC
  rw [reassoc_of% hr, ← hC, Iso.hom_inv_id_app_assoc]

/-- The counit of [stacks 0GMT] at `G ⊗ᴸ_B Ext Y`, computed from `ProjCounitCompatAt` as the
projection formula, the section of the lax monoidal structure map, and the counit at `G`. -/
private theorem ProjCounitCompatAt.counit_eq {φ : A →+* B}
    {E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ}
    {adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ}
    {Y : DerivedCategory (ModuleCat.{max u v} A)} {G : DerivedCategory (ModuleCat.{max u v} B)}
    (h : ProjCounitCompatAt.{u, v} φ E adj Y G) :
    (modelAdjunction.{u, v} φ E).counit.app
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
          (G, E.functor.obj Y)) =
      E.functor.map ((derivedProjNatIso.{u, max u v} φ E _ adj Y).hom.app G) ≫
        Dualizing.derivedTensorBaseChangeSection.{u, u, v} φ E.functor (modelComparison.{u, v} φ E)
            ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) Y ≫
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
            (X := (E.functor.obj ((ModuleCat.restrictScalars.{max u v}
                φ).mapDerivedCategory.obj G), E.functor.obj Y))
            (Y := (G, E.functor.obj Y))
            ((modelAdjunction.{u, v} φ E).counit.app G, 𝟙 (E.functor.obj Y)) := by
  have hstep : E.functor.map ((derivedProjNatIso.{u, max u v} φ E _ adj Y).inv.app G) ≫
        (modelAdjunction.{u, v} φ E).counit.app
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
            (G, E.functor.obj Y)) =
      Dualizing.derivedTensorBaseChangeSection.{u, u, v} φ E.functor (modelComparison.{u, v} φ E)
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) Y ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
          (X := (E.functor.obj ((ModuleCat.restrictScalars.{max u v}
              φ).mapDerivedCategory.obj G), E.functor.obj Y))
          (Y := (G, E.functor.obj Y))
          ((modelAdjunction.{u, v} φ E).counit.app G, 𝟙 (E.functor.obj Y)) := by
    dsimp only [ProjCounitCompatAt] at h
    rw [← h, ← Category.assoc,
      Dualizing.derivedTensorBaseChangeSection_comp_derivedTensorBaseChange.{u, u, v},
      Category.id_comp]
    rfl
  rw [← hstep, ← Category.assoc, ← E.functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The hypothesis of Comparison I from the owed coherence and the monoidal compatibility.**
The linearity of the projection formula for the action of the algebra -- the hypothesis of
`Dualizing.ProjectionFormula.restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal` -- follows
from `Dualizing.ProjectionFormula.ProjCounitCompatAt` at the same pair together with
`Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat`.

The first hypothesis says the counit of [stacks 0GMT] at `G ⊗ᴸ_B Ext Y` is the projection formula
followed by the inverse of the lax monoidal structure map and the counit in the first factor; the
second contributes the rearrangement that identifies the two ways of moving the algebra past the
projection formula.  Nothing else is used: the algebra action is cancelled off both sides by
`Dualizing.ProjectionFormula.restrictedAction_comp_derivedProj_iff`, and what is left is
naturality of the projection formula in the object of `D(B)`, naturality of
`Dualizing.ProjectionFormula.restrictExtendIso`, and naturality of the symmetry. -/
theorem restrictedAction_comp_derivedProj_of_projCounitCompatAt (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (Y : DerivedCategory (ModuleCat.{max u v} A))
    (G : DerivedCategory (ModuleCat.{max u v} B))
    (hC : ProjTensorBaseChangeCompat.{u, v} φ E adj Y
      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G))
    (h : ProjCounitCompatAt.{u, v} φ E adj Y G) :
    restrictedAction.{u, max u v} φ E _ adj (modelAdjunction.{u, v} φ E)
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
            (G, E.functor.obj Y)) ≫
        (derivedProjNatIso.{u, max u v} φ E _ adj Y).hom.app G =
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
              ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.obj
                (G, E.functor.obj Y)),
            restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
          (Y := ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
              (Y, (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G),
            restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))
          ((derivedProjNatIso.{u, max u v} φ E _ adj Y).hom.app G ≫
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G) Y).hom,
            𝟙 (restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)) ≫
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorAssoc Y
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G)
          (restrictedAlgebra.{u, max u v}
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)).hom ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := (Y, (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.obj
              ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G,
                restrictedAlgebra.{u, max u v}
                  (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)))
          (Y := (Y, (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G))
          (𝟙 Y, restrictedAction.{u, max u v} φ E _ adj (modelAdjunction.{u, v} φ E) G) ≫
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap Y
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G)).hom := by
  refine (restrictedAction_comp_derivedProj_iff.{u, max u v} φ E
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj
    (modelAdjunction.{u, v} φ E) Y G).mpr ?_
  -- naturality of the projection formula in the object of `D(B)`, at the counit
  have hproj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} B).tensor.map
            (X := (E.functor.obj ((ModuleCat.restrictScalars.{max u v}
                φ).mapDerivedCategory.obj G), E.functor.obj Y))
            (Y := (G, E.functor.obj Y))
            ((modelAdjunction.{u, v} φ E).counit.app G, 𝟙 (E.functor.obj Y))) ≫
        (derivedProjNatIso.{u, max u v} φ E _ adj Y).hom.app G =
      (derivedProjNatIso.{u, max u v} φ E _ adj Y).hom.app
          (E.functor.obj ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G)) ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            (E.functor.obj ((ModuleCat.restrictScalars.{max u v}
              φ).mapDerivedCategory.obj G)), Y))
          (Y := ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj G, Y))
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
            ((modelAdjunction.{u, v} φ E).counit.app G), 𝟙 Y) :=
    (derivedProjNatIso.{u, max u v} φ E _ adj Y).hom.naturality
      ((modelAdjunction.{u, v} φ E).counit.app G)
  have hsplit : ∀ {K₁ K₂ K₃ : DerivedCategory (ModuleCat.{max u v} A)} (f : K₁ ⟶ K₂) (g : K₂ ⟶ K₃),
      (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := (K₁, Y)) (Y := (K₃, Y)) (f ≫ g, 𝟙 Y) =
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
            (X := (K₁, Y)) (Y := (K₂, Y)) (f, 𝟙 Y) ≫
          (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
            (X := (K₂, Y)) (Y := (K₃, Y)) (g, 𝟙 Y) := by
    intro K₁ K₂ K₃ f g
    rw [(derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor_map_comp,
      Category.comp_id]
  rw [ProjCounitCompatAt.counit_eq.{u, v} h]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [hproj, ← restrictExtendIso_hom_comp_restrictedAction φ E _ adj (modelAdjunction.{u, v} φ E),
    hsplit]
  simp only
  rw [reassoc_of% (ProjTensorBaseChangeCompat.map_section_comp_derivedProj.{u, v} hC),
    (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap_naturality (𝟙 Y)
    (restrictedAction.{u, max u v} φ E _ adj (modelAdjunction.{u, v} φ E) G)]

/-! ### Comparison I on the named coherences -/

/-- **Comparison I of [stacks 0E2H], on the two named coherences.**  This is
`Dualizing.ProjectionFormula.restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal` with its
written-out linearity hypothesis replaced by
`Dualizing.ProjectionFormula.ProjCounitCompatAt` -- the compatibility of the projection formula
with the counit of [stacks 0GMT], which is the whole residue of Comparison I in the vocabulary of
`StacksFrontier.RingTheory.Dualizing.UpperShriek.ProjectionFormulaCounit` -- together with
`Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat`.

It is stated at derived restriction of scalars and at the adjunction of [stacks 0GMT] carried by
the model, which is the situation
`Dualizing.ProjectionFormula.ProjCounitCompatAt` is stated in; the adjunction of [stacks 0A70] is
still arbitrary. -/
theorem restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal_of_projCounitCompatAt
    (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (Y X : DerivedCategory (ModuleCat.{max u v} A))
    (hC : ProjTensorBaseChangeCompat.{u, v} φ E adj Y
      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
        ((Dualizing.derivedHom.{u, max u v, u} φ).obj X)))
    (h : ProjCounitCompatAt.{u, v} φ E adj Y
      ((Dualizing.derivedHom.{u, max u v, u} φ).obj X)) :
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
          ((derivedTensorHomDiagonalAlongRingHom.{u, max u v} φ E _ adj Y).app X) ≫
        (restrictCoextendInternalHomIso.{u, max u v} φ E _ adj
            (modelAdjunction.{u, v} φ E)).hom.app
          ((tensorRightDerived.{u, max u v} A Y).obj X) =
      (derivedProjNatIso.{u, max u v} φ E _ adj Y).hom.app
          ((Dualizing.derivedHom.{u, max u v, u} φ).obj X) ≫
        ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap
          ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            ((Dualizing.derivedHom.{u, max u v, u} φ).obj X)) Y).hom ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensor.map
          (X := (Y, (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
            ((Dualizing.derivedHom.{u, max u v, u} φ).obj X)))
          (Y := (Y, (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).hom.obj
            (Opposite.op (restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory), X)))
          (𝟙 Y, (restrictCoextendInternalHomIso.{u, max u v} φ E _ adj
            (modelAdjunction.{u, v} φ E)).hom.app X) ≫
        Dualizing.derivedTensorHomDiagonalOverRing.{u, max u v} Y X
          (restrictedAlgebra.{u, max u v}
            (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory) ≫
        (derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).hom.map
          (𝟙 (Opposite.op (restrictedAlgebra.{u, max u v}
              (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory)),
            ((derivedHomAdjunctionOverRing.{u, max u v, max u v + 1} A).tensorSwap Y X).hom) :=
  restrict_derivedTensorHomDiagonalAlongRingHom_eq_diagonal.{u, max u v} φ E
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj (modelAdjunction.{u, v} φ E)
    Y X
    (restrictedAction_comp_derivedProj_of_projCounitCompatAt.{u, v} φ E adj Y
      ((Dualizing.derivedHom.{u, max u v, u} φ).obj X) hC h)

/-- **The invertibility that [stacks 0E2H] needs, on the two named coherences.**  The restriction
of the `B`-linear tensor--Hom diagonal along `φ` is invertible as soon as the single-ring
tensor--Hom diagonal of `D(A)` at `(Y, X, B[0])` is, given
`Dualizing.ProjectionFormula.ProjCounitCompatAt` and
`Dualizing.ProjectionFormula.ProjTensorBaseChangeCompat`. -/
theorem isIso_restrict_derivedTensorHomDiagonalAlongRingHom_of_projCounitCompatAt
    (φ : A →+* B)
    (E : TotalDerivedExtensionScalars.{u, max u v, u, max u v + 1, max u v + 1} φ)
    (adj : (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory ⊣
      Dualizing.derivedHom.{u, max u v, u} φ)
    (Y X : DerivedCategory (ModuleCat.{max u v} A))
    (hC : ProjTensorBaseChangeCompat.{u, v} φ E adj Y
      ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.obj
        ((Dualizing.derivedHom.{u, max u v, u} φ).obj X)))
    (h : ProjCounitCompatAt.{u, v} φ E adj Y
      ((Dualizing.derivedHom.{u, max u v, u} φ).obj X))
    (hdiag : IsIso (Dualizing.derivedTensorHomDiagonalOverRing.{u, max u v} Y X
      (restrictedAlgebra.{u, max u v}
        (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory))) :
    IsIso ((ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory.map
      ((derivedTensorHomDiagonalAlongRingHom.{u, max u v} φ E _ adj Y).app X)) :=
  isIso_restrict_derivedTensorHomDiagonalAlongRingHom.{u, max u v} φ E
    (ModuleCat.restrictScalars.{max u v} φ).mapDerivedCategory adj (modelAdjunction.{u, v} φ E)
    Y X
    (restrictedAction_comp_derivedProj_of_projCounitCompatAt.{u, v} φ E adj Y
      ((Dualizing.derivedHom.{u, max u v, u} φ).obj X) hC h) hdiag

end Dualizing.ProjectionFormula

end
