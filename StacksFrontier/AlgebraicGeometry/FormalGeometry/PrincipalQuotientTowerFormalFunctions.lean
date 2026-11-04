module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerDiagram
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerProducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksCore.Tactic.StacksAttribute

/-!
# Formal functions for a principal ideal on a scheme, with the countable products supplied

Let `A` be a ring, let `f ∈ A`, let `X` be a scheme over `A` through `ρ : A ⟶ Γ(X, 𝒪_X)` and let
`ℱ` be a quasi-coherent `𝒪_X`-module whose `f`-power torsion `ℱ[fⁿ] = Ker(fⁿ : ℱ → ℱ)`
stabilizes. [Stacks, Tag 0BLD] asserts the displayed equality

`RΓ(X, lim ℱ/fⁿℱ) = RΓ(X, ℱ)^∧`

and, for every `p`, a commutative diagram with exact rows and columns

```
                     0                              0
                     ↑                              ↑
0 ⟶  Hᵖ(X, ℱ)^   ⟶  lim Hᵖ(X, ℱ/fⁿℱ)  ⟶  T_f(Hᵖ⁺¹(X, ℱ))  ⟶  0
                     ↑                              ↑              ‖
0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶  T_f(Hᵖ⁺¹(X, ℱ))  ⟶  0
                     ↑                              ↑
      R¹lim Hᵖ(X, ℱ)[fⁿ]  ≅  R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)
                     ↑                              ↑
                     0                              0
```

The library proves these in
`FormalGeometry/PrincipalQuotientTowerDerivedCompletion.lean`,
`FormalGeometry/PrincipalQuotientTowerSections.lean` and
`FormalGeometry/PrincipalQuotientTowerDiagram.lean`, with the existence of the countable products
of the inverse systems involved carried as instance binders. Those products exist with no
hypothesis at all: `D(𝒪_X)` has countable products by
`Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules`, and `D(A)` has them by
`Stacks.DerivedProducts.hasProductsOfShape_derivedCategory`. This file states the displayed
equality, the whole diagram and each of its rows, columns and the bottom isomorphism with those
binders discharged, so that every statement here has exactly the hypotheses of the source.

## Main results

* `Stacks.Algebraization.PrincipalQuotientTowerFormalFunctions`
  `.nonempty_iso_derivedSections_limit_derivedCompletion` — the displayed equality.
* `Stacks.Algebraization.PrincipalQuotientTowerFormalFunctions`
  `.exists_diagram_derivedSections_limit_quotientTower` — the whole commutative diagram.
* `Stacks.Algebraization.PrincipalQuotientTowerFormalFunctions.exists_shortExact_topRow_quotients`,
  `exists_shortExact_middleRow_quotients`, `exists_shortExact_leftColumn_quotients`,
  `exists_shortExact_middleColumn_quotients` and `nonempty_iso_firstDerivedLimit_torsion_quotients`
  — its rows, columns and bottom isomorphism, one at a time.

## Implementation notes

The results this file builds on are stated at the standard model
`CategoryTheory.HasDerivedCategory.standard` of `D(𝒪_X)` and of `D(A)`; so are the objects
(`derivedSectionsOver`, `derivedSectionsModule`, `quotientCohomology`, ...) in which they are
expressed. Every statement here therefore names that model with a `letI` at its head, rather than
leaving the choice to instance search, which in this import closure may answer with another model.

## References

* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
* [Stacks Project, Tag 0BKG](https://stacks.math.columbia.edu/tag/0BKG)
* [Stacks Project, Tag 0H32](https://stacks.math.columbia.edu/tag/0H32)
* [Stacks Project, Tag 0H3E](https://stacks.math.columbia.edu/tag/0H3E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsOverBase (derivedSectionsOver)
open Stacks.Algebraization.PrincipalQuotientTower (mulF quotientTower)
open Stacks.Algebraization.PrincipalQuotientTowerCompletion (derivedSectionsModule)
open Stacks.Algebraization.PrincipalQuotientTowerDiagram (quotientCohomology
  limitQuotientSections)

universe u

namespace Stacks.Algebraization.PrincipalQuotientTowerFormalFunctions

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.toRingedSpace.carrier)))
  (f : A) (ℱ : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- **The displayed equality of [Stacks, Tag 0BLD].** Let `A` be a ring, `f ∈ A`, let `X` be a
scheme over `A` through `ρ : A ⟶ Γ(X, 𝒪_X)` and let `ℱ` be a quasi-coherent `𝒪_X`-module whose
`f`-power torsion stabilizes. Let `completion` be a left adjoint to the inclusion of the objects
of `D(A)` that are derived complete for the ideal `(f)`, so that `(-)^∧ = completion ⋙ P.ι` is
derived `f`-adic completion as in [Stacks, Tag 0BKG]. Then

`RΓ(X, lim ℱ/f^(n+1)ℱ) ≅ RΓ(X, ℱ)^∧`,

the object `RΓ(X, lim ℱ/f^(n+1)ℱ)` is derived complete for `(f)`, and for every `p` its `p`-th
cohomology module is that of `RΓ(X, ℱ)^∧`.

This is `nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion` (in the namespace
`PrincipalQuotientTowerCompletion`) with the countable products of `D(𝒪_X)` and of `D(A)` it
takes as instance binders supplied. -/
@[stacks 0BLD "the displayed equality `RΓ(X, lim ℱ/fⁿℱ) = RΓ(X, ℱ)^∧`, with derived f-adic \
completion presented as in Stacks 0BKG by an arbitrary left adjoint to the inclusion of the \
derived-complete objects; also derived completeness of `RΓ(X, lim ℱ/fⁿℱ)` and the identification \
`Hᵖ(X, lim ℱ/fⁿℱ) = Hᵖ(RΓ(X, ℱ)^∧)`. Unconditional: the countable products of D(𝒪_X) and D(A) \
are supplied, not assumed"]
theorem nonempty_iso_derivedSections_limit_derivedCompletion
    (hℱ : (ℱ : X.Modules).IsQuasicoherent) (hstab : Stabilizes (mulF X ρ f ℱ)) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (_ : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      let Fhat : DerivedCategory (ModuleCat.{u} A) :=
        (derivedSectionsOver X.toRingedSpace ρ).obj
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
            (limit (quotientTower X ρ f ℱ)))
      Nonempty (Fhat ≅ completed.obj (derivedSectionsModule X ρ ℱ)) ∧
        IsDerivedComplete (Ideal.span {f}) Fhat ∧
        ∀ p : ℤ, Nonempty
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj Fhat ≅
            (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
              (completed.obj (derivedSectionsModule X ρ ℱ))) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules X
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  open PrincipalQuotientTowerCompletion in
  exact nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion X ρ f ℱ hℱ hstab

/-- **The middle column of the diagram of [Stacks, Tag 0BLD], in the form of [Stacks, Tag 0H3E].**
With `A`, `f`, `X` and `ℱ` as in the source, let `E^` be a derived limit of the `f`-power Koszul
tower `ℱ ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)`. Then `E^ ≅ lim ℱ/f^(n+1)ℱ`, and for every `p` there is
a short exact sequence

`0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0`,

whose inclusion descends the connecting morphism of the Milnor triangle and whose projection is
characterized by the limit projections, and whose outer terms are isomorphic to those of the
corresponding sequence for the Koszul tower.

This is `PrincipalQuotientTower.exists_shortExact_homology_derivedSections_limit_quotientTower`
with the countable products of `D(𝒪_X)` and of `D(A)` it takes as instance binders supplied; the
statement names them, since it mentions products and derived limits. -/
@[stacks 0BLD "the middle column of the diagram: the short exact sequence \
`0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0` at the ordinary limit, \
together with the isomorphism of a derived limit of the f-power Koszul tower with `lim ℱ/fⁿℱ`. \
Unconditional: the countable products of D(𝒪_X) and D(A) are supplied, not assumed"]
theorem exists_shortExact_middleColumn_quotients
    (hℱ : (ℱ : X.Modules).IsQuasicoherent) (hstab : Stabilizes (mulF X ρ f ℱ)) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    letI := Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules X
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    ∀ (Ehat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))),
      IsDerivedLimit (Ksys (mulF X ρ f ℱ)) Ehat →
    let Fhat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
        (limit (quotientTower X ρ f ℱ))
    let F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      Csys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ
    let G : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      Ksys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ F.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    Nonempty (Ehat ≅ Fhat) ∧
      ∃ (a : (derivedSectionsOver X.toRingedSpace ρ).obj Fhat ⟶ ∏ᶜ Y)
        (b : (∏ᶜ Y) ⟶ ((derivedSectionsOver X.toRingedSpace ρ).obj Fhat)⟦(1 : ℤ)⟧),
        let T := Triangle.mk a d b
        T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
          ∀ p : ℤ,
            let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) p
            let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p - 1)
            let homologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H
            let shiftedHomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H₁
            let P : ModuleCat.{u} A :=
              ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (op n)
            let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) n -
                Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) (n + 1) ≫
                  shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
            ∃ (e : H₁.obj (∏ᶜ Y) ≅ P)
              (i : cokernel δ ⟶ H.obj ((derivedSectionsOver X.toRingedSpace ρ).obj Fhat))
              (q : H.obj ((derivedSectionsOver X.toRingedSpace ρ).obj Fhat) ⟶
                limit homologySystem)
              (w : i ≫ q = 0),
              e.hom = piComparison H₁ Y ∧
                cokernel.π δ ≫ i = e.inv ≫
                  DerivedCategory.HomologySequence.δ T (p - 1) p (by omega) ∧
                (∀ n : ℕ, q ≫ limit.π homologySystem (op n) =
                  H.map a ≫ H.map (Pi.π Y n)) ∧
                (ShortComplex.mk i q w).ShortExact ∧
                Nonempty (limit homologySystem ≅ limit (G ⋙ H)) ∧
                Nonempty (cokernel δ ≅
                  CompletionSequences.firstDerivedLimit A (G ⋙ H₁)) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules X
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  intro Ehat hEhat
  exact PrincipalQuotientTower.exists_shortExact_homology_derivedSections_limit_quotientTower
    X ρ f ℱ hℱ hstab Ehat hEhat

section Diagram

variable (hℱ : (ℱ : X.Modules).IsQuasicoherent) (hstab : Stabilizes (mulF X ρ f ℱ))

include hℱ hstab

/-- **The commutative diagram of [Stacks, Tag 0BLD].** Let `A` be a ring, `f ∈ A`, let `X` be a
scheme over `A` through `ρ : A ⟶ Γ(X, 𝒪_X)` and let `ℱ` be a quasi-coherent `𝒪_X`-module whose
`f`-power torsion stabilizes. Let `completion` be a left adjoint to the inclusion of the objects
of `D(A)` that are derived complete for `(f)`, so that `(-)^∧ = completion ⋙ P.ι` is derived
`f`-adic completion as in [Stacks, Tag 0BKG]. Then for every `p` there is a commutative diagram

```
                     0                              0
                     ↑                              ↑
0 ⟶  Hᵖ(X, ℱ)^   ⟶  lim Hᵖ(X, ℱ/fⁿℱ)  ⟶  T_f(Hᵖ⁺¹(X, ℱ))  ⟶  0
                     ↑                              ↑              ‖
0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶  T_f(Hᵖ⁺¹(X, ℱ))  ⟶  0
                     ↑                              ↑
      R¹lim Hᵖ(X, ℱ)[fⁿ]  ≅  R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)
                     ↑                              ↑
                     0                              0
```

with exact rows and columns, where `Hᵖ(X, ℱ)^ = lim Hᵖ(X, ℱ)/fⁿHᵖ(X, ℱ)` is the ordinary `f`-adic
completion and `T_f(-)` is the `f`-adic Tate module. The right-hand column is the identity: the
two projections to `T_f(Hᵖ⁺¹(X, ℱ))` agree after the middle vertical map.

This is `PrincipalQuotientTowerDiagram.exists_formalFunctionsDiagram` with the countable products
of `D(𝒪_X)` and of `D(A)` it takes as instance binders supplied. -/
@[stacks 0BLD "the commutative diagram with exact rows and columns, in full: the top row \
`0 ⟶ Hᵖ(X, ℱ)^ ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`, the middle row \
`0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`, the left column \
`0 ⟶ R¹lim Hᵖ(X, ℱ)[fⁿ] ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, ℱ)^ ⟶ 0`, the middle column \
`0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0`, the bottom isomorphism \
`R¹lim Hᵖ(X, ℱ)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)`, the identity right column, and the commutativity of \
the three squares. Unconditional: the countable products of D(𝒪_X) and D(A) are supplied, not \
assumed"]
theorem exists_diagram_derivedSections_limit_quotientTower (p : ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    let Hq : ℤ → ModuleCat.{u} A := fun q ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (derivedSectionsModule X ρ ℱ)
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (_ : completion ⊣ P.ι),
      let completed := completion ⋙ P.ι
      let ordinaryCompletion := limit (CompletionSequences.powerQuotientSystem A (Hq p) f)
      let tate := CompletionSequences.adicTateModule A (Hq (p + 1)) f
      let h0Completion := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (completed.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (Hq p)))
      let torsionR1 := CompletionSequences.firstDerivedLimit A
        (PrincipalTorsionTower.powerTorsionSystem A (Hq p) f)
      let limitQuotientCohomology := limit (quotientCohomology X ρ f ℱ p)
      let previousQuotientR1 := CompletionSequences.firstDerivedLimit A
        (quotientCohomology X ρ f ℱ (p - 1))
      let sectionsCohomology := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
        (limitQuotientSections X ρ f ℱ)
      ∃ (topIn : ordinaryCompletion ⟶ limitQuotientCohomology)
        (topOut : limitQuotientCohomology ⟶ tate)
        (htop : topIn ≫ topOut = 0)
        (middleIn : h0Completion ⟶ sectionsCohomology)
        (middleOut : sectionsCohomology ⟶ tate)
        (hmiddle : middleIn ≫ middleOut = 0)
        (leftIn : torsionR1 ⟶ h0Completion) (leftOut : h0Completion ⟶ ordinaryCompletion)
        (hleft : leftIn ≫ leftOut = 0)
        (columnIn : previousQuotientR1 ⟶ sectionsCohomology)
        (columnOut : sectionsCohomology ⟶ limitQuotientCohomology)
        (hcolumn : columnIn ≫ columnOut = 0)
        (bottom : torsionR1 ≅ previousQuotientR1),
        (ShortComplex.mk topIn topOut htop).ShortExact ∧
          (ShortComplex.mk middleIn middleOut hmiddle).ShortExact ∧
          (ShortComplex.mk leftIn leftOut hleft).ShortExact ∧
          (ShortComplex.mk columnIn columnOut hcolumn).ShortExact ∧
          middleIn ≫ columnOut = leftOut ≫ topIn ∧
          middleOut = columnOut ≫ topOut ∧
          bottom.hom ≫ columnIn = leftIn ≫ middleIn := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules X
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  exact PrincipalQuotientTowerDiagram.exists_formalFunctionsDiagram X ρ f ℱ hℱ hstab p

/-- **The top row of the diagram of [Stacks, Tag 0BLD].** With `A`, `f`, `X` and `ℱ` as in the
source, for every `p` there is a short exact sequence

`0 ⟶ Hᵖ(X, ℱ)^ ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`,

where `Hᵖ(X, ℱ)^ = lim Hᵖ(X, ℱ)/fⁿHᵖ(X, ℱ)` is the ordinary `f`-adic completion and `T_f(-)` the
`f`-adic Tate module. This is `PrincipalQuotientTowerDiagram.exists_shortExact_topRow` with its
countable products supplied. -/
@[stacks 0BLD "the top row of the diagram: the short exact sequence \
`0 ⟶ Hᵖ(X, ℱ)^ ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`. Unconditional: no reflector onto the \
derived-complete objects and no countable products are assumed"]
theorem exists_shortExact_topRow_quotients (p : ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    let Hq : ℤ → ModuleCat.{u} A := fun q ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (derivedSectionsModule X ρ ℱ)
    ∃ (topIn : limit (CompletionSequences.powerQuotientSystem A (Hq p) f) ⟶
        limit (quotientCohomology X ρ f ℱ p))
      (topOut : limit (quotientCohomology X ρ f ℱ p) ⟶
        CompletionSequences.adicTateModule A (Hq (p + 1)) f)
      (htop : topIn ≫ topOut = 0),
      (ShortComplex.mk topIn topOut htop).ShortExact := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules X
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  exact PrincipalQuotientTowerDiagram.exists_shortExact_topRow X ρ f ℱ hℱ hstab p

/-- **The middle row of the diagram of [Stacks, Tag 0BLD].** With `A`, `f`, `X` and `ℱ` as in the
source and `(-)^∧` derived `f`-adic completion presented by an arbitrary left adjoint to the
inclusion of the derived-complete objects, for every `p` there is a short exact sequence

`0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`.

This is `PrincipalQuotientTowerDiagram.exists_shortExact_middleRow` with its countable products
supplied. -/
@[stacks 0BLD "the middle row of the diagram: the short exact sequence \
`0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`, with `(-)^∧` the derived f-adic \
completion presented as in Stacks 0BKG by an arbitrary left adjoint to the inclusion of the \
derived-complete objects. Unconditional: no countable products are assumed"]
theorem exists_shortExact_middleRow_quotients (p : ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    let Hq : ℤ → ModuleCat.{u} A := fun q ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (derivedSectionsModule X ρ ℱ)
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (_ : completion ⊣ P.ι),
      ∃ (middleIn : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
          ((completion ⋙ P.ι).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (Hq p))) ⟶
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
            (limitQuotientSections X ρ f ℱ))
        (middleOut : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
            (limitQuotientSections X ρ f ℱ) ⟶
          CompletionSequences.adicTateModule A (Hq (p + 1)) f)
        (hmiddle : middleIn ≫ middleOut = 0),
        (ShortComplex.mk middleIn middleOut hmiddle).ShortExact := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules X
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  exact PrincipalQuotientTowerDiagram.exists_shortExact_middleRow X ρ f ℱ hℱ hstab p

/-- **The left column of the diagram of [Stacks, Tag 0BLD].** With `A`, `f`, `X` and `ℱ` as in the
source and `(-)^∧` derived `f`-adic completion presented by an arbitrary left adjoint to the
inclusion of the derived-complete objects, for every `p` there is a short exact sequence

`0 ⟶ R¹lim Hᵖ(X, ℱ)[fⁿ] ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, ℱ)^ ⟶ 0`.

This is `PrincipalQuotientTowerDiagram.exists_shortExact_leftColumn` with its countable products
supplied. -/
@[stacks 0BLD "the left column of the diagram: the short exact sequence \
`0 ⟶ R¹lim Hᵖ(X, ℱ)[fⁿ] ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, ℱ)^ ⟶ 0`, with `(-)^∧` the derived f-adic \
completion presented as in Stacks 0BKG by an arbitrary left adjoint to the inclusion of the \
derived-complete objects. Unconditional: no countable products are assumed"]
theorem exists_shortExact_leftColumn_quotients (p : ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    let Hq : ℤ → ModuleCat.{u} A := fun q ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (derivedSectionsModule X ρ ℱ)
    let P : ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
      fun L ↦ IsDerivedComplete (Ideal.span {f}) L
    ∀ (completion : DerivedCategory (ModuleCat.{u} A) ⥤ P.FullSubcategory)
      (_ : completion ⊣ P.ι),
      ∃ (leftIn : CompletionSequences.firstDerivedLimit A
            (PrincipalTorsionTower.powerTorsionSystem A (Hq p) f) ⟶
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((completion ⋙ P.ι).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (Hq p))))
        (leftOut : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
            ((completion ⋙ P.ι).obj
              ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (Hq p))) ⟶
          limit (CompletionSequences.powerQuotientSystem A (Hq p) f))
        (hleft : leftIn ≫ leftOut = 0),
        (ShortComplex.mk leftIn leftOut hleft).ShortExact := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules X
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  exact PrincipalQuotientTowerDiagram.exists_shortExact_leftColumn X ρ f ℱ hℱ hstab p

/-- **The bottom isomorphism of the diagram of [Stacks, Tag 0BLD].** With `A`, `f`, `X` and `ℱ` as
in the source, for every `p`

`R¹lim Hᵖ(X, ℱ)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)`.

This is `PrincipalQuotientTowerDiagram.nonempty_iso_firstDerivedLimit_torsion` with its countable
products supplied. -/
@[stacks 0BLD "the bottom isomorphism of the diagram: \
`R¹lim Hᵖ(X, ℱ)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)`. Unconditional: no reflector onto the \
derived-complete objects and no countable products are assumed"]
theorem nonempty_iso_firstDerivedLimit_torsion_quotients (p : ℤ) :
    letI := HasDerivedCategory.standard (ModuleCat.{u} A)
    let Hq : ℤ → ModuleCat.{u} A := fun q ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (derivedSectionsModule X ρ ℱ)
    Nonempty (CompletionSequences.firstDerivedLimit A
        (PrincipalTorsionTower.powerTorsionSystem A (Hq p) f) ≅
      CompletionSequences.firstDerivedLimit A (quotientCohomology X ρ f ℱ (p - 1))) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  let := Stacks.Algebraization.hasProductsOfShape_nat_derivedCategory_modules X
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  exact PrincipalQuotientTowerDiagram.nonempty_iso_firstDerivedLimit_torsion X ρ f ℱ hℱ hstab p

end Diagram

end Stacks.Algebraization.PrincipalQuotientTowerFormalFunctions

end
