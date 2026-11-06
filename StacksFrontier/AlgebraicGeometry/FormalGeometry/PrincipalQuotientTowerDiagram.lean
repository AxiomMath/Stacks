module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerDerivedCompletion
public import StacksFrontier.Homology.DerivedComplete.PrincipalFormalFunctionsDegreeZero
public import StacksCore.Tactic.StacksAttribute

/-!
# The formal-functions diagram for a principal ideal on a scheme

Let `A` be a ring, let `f ∈ A`, let `X` be a scheme over `A` through `ρ : A ⟶ Γ(X, 𝒪_X)` and let
`ℱ` be a quasi-coherent `𝒪_X`-module whose `f`-power torsion `ℱ[fⁿ] = Ker(fⁿ : ℱ → ℱ)`
stabilizes. The displayed equality `RΓ(X, lim ℱ/fⁿℱ) = RΓ(X, ℱ)^∧` of [Stacks, Tag 0BLD] is
`nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion` in the namespace
`PrincipalQuotientTowerCompletion`, and the middle column of the diagram the source deduces from
it is `PrincipalQuotientTower.exists_shortExact_homology_derivedSections_limit_quotientTower`.
This file supplies the rest of that diagram: for every `p` the commutative diagram with exact rows
and columns

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

where `Hᵖ(X, ℱ)^ = lim Hᵖ(X, ℱ)/fⁿHᵖ(X, ℱ)` is the ordinary `f`-adic completion and `T_f(-)` is
the `f`-adic Tate module of [Stacks, Tag 0BKG].

The source deduces the whole diagram from the displayed equality together with the diagram of
[Stacks, Tag 0H32] for `K = RΓ(X, ℱ)`. That is exactly what is done here: the library's form of
Tag 0H32 is `PrincipalCompletionDiagram.derivedCompletion_principal_homology_comparison`, whose
diagram is expressed in the inverse limits of the cohomology of the derived reductions
`RΓ(X, ℱ) ⊗^L_A (A --fⁿ--> A)`, and the two bridges needed to rewrite those at the honest
quotients `ℱ/fⁿℱ` are already available: the isomorphism
`RΓ(X, lim ℱ/fⁿℱ) ≅ RΓ(X, ℱ)^∧` of the displayed equality, and the two comparisons
`lim Hᵖ(X, ℱ/fⁿℱ) ≅ lim Hᵖ(RΓ(X, ℱ) ⊗^L A/fⁿ)` and
`R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ≅ R¹lim Hᵖ⁻¹(RΓ(X, ℱ) ⊗^L A/fⁿ)` carried by the middle-column
theorem (which gets them from the pro-isomorphism of [Stacks, Tag 0H3D] and the levelwise
identification of [Stacks, Tag 0H3C]).

## Main results

* `Stacks.Algebraization.PrincipalQuotientTowerDiagram.exists_formalFunctionsDiagram` — the whole
  commutative diagram: the four short exact sequences, the bottom isomorphism, the identity right
  column, and the commutativity of the three squares.
* `Stacks.Algebraization.PrincipalQuotientTowerDiagram.exists_shortExact_topRow` — the top row,
  with no hypothesis on a reflector.
* `Stacks.Algebraization.PrincipalQuotientTowerDiagram.exists_shortExact_middleRow` — the middle
  row.
* `Stacks.Algebraization.PrincipalQuotientTowerDiagram.exists_shortExact_leftColumn` — the left
  column.
* `Stacks.Algebraization.PrincipalQuotientTowerDiagram.nonempty_iso_firstDerivedLimit_torsion` —
  the bottom isomorphism `R¹lim Hᵖ(X, ℱ)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)`.

## Implementation notes

`transportDiagram` is the purely formal step: a diagram of the shape of [Stacks, Tag 0H32] and
three isomorphisms identifying its lower-right three objects with others produce the same diagram
at the new objects. Keeping it separate means the geometric input is confined to the three
isomorphisms, and it lets the components of Tag 0H32's conclusion be matched by unification
instead of being written out.

Derived completion is presented as in [Stacks, Tags 0BKG and 0H32]: the statements that mention
`Hᵖ(X, ℱ)^∧` are quantified over an arbitrary left adjoint `completion` to the inclusion of the
derived-complete objects, as the displayed equality is. The top row and the bottom
isomorphism do not mention it, so for those the reflector is supplied internally from
`Stacks.FormalFunctions.derivedComplete_principal_ι_isRightAdjoint` and the statements are
unconditional.

The `HasProduct` side conditions are the instance binders of the two theorems this file
builds on; they are not strengthened. The countable products of `D(A)` that Tag 0H32 asks for are
discharged from `Stacks.DerivedProducts.hasProductsOfShape_derivedCategory`.

## References

* [Stacks Project, Tag 0BLD](https://stacks.math.columbia.edu/tag/0BLD)
* [Stacks Project, Tag 0H32](https://stacks.math.columbia.edu/tag/0H32)
* [Stacks Project, Tag 0BKG](https://stacks.math.columbia.edu/tag/0BKG)
* [Stacks Project, Tag 0H3C](https://stacks.math.columbia.edu/tag/0H3C)
* [Stacks Project, Tag 0H3D](https://stacks.math.columbia.edu/tag/0H3D)
* [Stacks Project, Tag 0H3E](https://stacks.math.columbia.edu/tag/0H3E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsOverBase (derivedSectionsOver)
open Stacks.Algebraization.PrincipalQuotientTower (mulF quotientTower
  exists_shortExact_homology_derivedSections_limit_quotientTower)
open Stacks.Algebraization.PrincipalQuotientTowerCompletion (derivedSectionsModule
  nonempty_iso_koszulTower_comp_derivedSections
  nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion)

universe u

namespace Stacks.Algebraization.PrincipalQuotientTowerDiagram

attribute [local instance] HasDerivedCategory.standard

/-! ### Transporting `R¹lim` along an isomorphism of inverse systems -/

/-- The map `1 - shift` is natural in an inverse system of modules. -/
private lemma moduleDifference_naturality {A : Type u} [CommRing A]
    {E E' : ℕᵒᵖ ⥤ ModuleCat.{u} A} (e : E ≅ E') :
    CompletionSequences.moduleDifference A E ≫ (Pi.mapIso fun n : ℕ ↦ e.app ⟨n⟩).hom =
      (Pi.mapIso fun n : ℕ ↦ e.app ⟨n⟩).hom ≫ CompletionSequences.moduleDifference A E' := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.mapIso_hom_π, CompletionSequences.moduleDifference,
    Pi.lift_comp_π_assoc, Pi.lift_comp_π, comp_sub, sub_comp, Pi.mapIso_hom_π_assoc]
  simp only [Iso.app_hom]
  rw [e.hom.naturality]

/-- **`R¹lim` transported along an isomorphism of inverse systems of modules.** -/
private def firstDerivedLimitMapIso {A : Type u} [CommRing A]
    {E E' : ℕᵒᵖ ⥤ ModuleCat.{u} A} (e : E ≅ E') :
    CompletionSequences.firstDerivedLimit A E ≅ CompletionSequences.firstDerivedLimit A E' :=
  cokernel.mapIso _ _ (Pi.mapIso fun n : ℕ ↦ e.app ⟨n⟩)
    (Pi.mapIso fun n : ℕ ↦ e.app ⟨n⟩) (moduleDifference_naturality e)

/-! ### The formal step: moving the diagram along three isomorphisms -/

/-- **Transport of a diagram of the shape of [Stacks, Tag 0H32].** Given the commutative diagram
with exact rows and columns

```
0 ⟶ ordCompl ⟶  limTensor  ⟶ tate ⟶ 0
                     ↑              ‖
0 ⟶  h0Compl  ⟶ homCompl   ⟶ tate ⟶ 0
                     ↑
             r1Tors ≅ r1Prev
```

and isomorphisms identifying `homCompl`, `limTensor` and `r1Prev` with objects `homQuot`,
`limQuot` and `r1Quot`, the same diagram is obtained at those objects. -/
private theorem transportDiagram {C : Type*} [Category C] [Abelian C]
    {ordCompl h0Compl tate r1Tors limTensor homCompl r1Prev limQuot homQuot r1Quot : C}
    (γ : r1Quot ≅ r1Prev) (α : homQuot ≅ homCompl) (β : limQuot ≅ limTensor)
    {topIn : ordCompl ⟶ limTensor} {topOut : limTensor ⟶ tate}
    {htop : topIn ≫ topOut = 0}
    {middleIn : h0Compl ⟶ homCompl} {middleOut : homCompl ⟶ tate}
    {hmiddle : middleIn ≫ middleOut = 0}
    {leftIn : r1Tors ⟶ h0Compl} {leftOut : h0Compl ⟶ ordCompl}
    {hleft : leftIn ≫ leftOut = 0}
    {columnIn : r1Prev ⟶ homCompl} {columnOut : homCompl ⟶ limTensor}
    {hcolumn : columnIn ≫ columnOut = 0}
    (bottom : r1Tors ≅ r1Prev)
    (hTop : (ShortComplex.mk topIn topOut htop).ShortExact)
    (hMiddle : (ShortComplex.mk middleIn middleOut hmiddle).ShortExact)
    (hLeft : (ShortComplex.mk leftIn leftOut hleft).ShortExact)
    (hColumn : (ShortComplex.mk columnIn columnOut hcolumn).ShortExact)
    (hsquare : middleIn ≫ columnOut = leftOut ≫ topIn)
    (hright : middleOut = columnOut ≫ topOut)
    (hbottom : bottom.hom ≫ columnIn = leftIn ≫ middleIn) :
    ∃ (topIn' : ordCompl ⟶ limQuot) (topOut' : limQuot ⟶ tate)
      (htop' : topIn' ≫ topOut' = 0)
      (middleIn' : h0Compl ⟶ homQuot) (middleOut' : homQuot ⟶ tate)
      (hmiddle' : middleIn' ≫ middleOut' = 0)
      (leftIn' : r1Tors ⟶ h0Compl) (leftOut' : h0Compl ⟶ ordCompl)
      (hleft' : leftIn' ≫ leftOut' = 0)
      (columnIn' : r1Quot ⟶ homQuot) (columnOut' : homQuot ⟶ limQuot)
      (hcolumn' : columnIn' ≫ columnOut' = 0)
      (bottom' : r1Tors ≅ r1Quot),
      (ShortComplex.mk topIn' topOut' htop').ShortExact ∧
        (ShortComplex.mk middleIn' middleOut' hmiddle').ShortExact ∧
        (ShortComplex.mk leftIn' leftOut' hleft').ShortExact ∧
        (ShortComplex.mk columnIn' columnOut' hcolumn').ShortExact ∧
        middleIn' ≫ columnOut' = leftOut' ≫ topIn' ∧
        middleOut' = columnOut' ≫ topOut' ∧
        bottom'.hom ≫ columnIn' = leftIn' ≫ middleIn' := by
  refine ⟨topIn ≫ β.inv, β.hom ≫ topOut, by
      simp [htop],
    middleIn ≫ α.inv, α.hom ≫ middleOut, by
      simp [hmiddle],
    leftIn, leftOut, hleft,
    γ.hom ≫ columnIn ≫ α.inv, α.hom ≫ columnOut ≫ β.inv, by
      rw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc columnIn,
        hcolumn, zero_comp, comp_zero],
    bottom ≪≫ γ.symm, ?_, ?_, hLeft, ?_, ?_, ?_, ?_⟩
  · refine ShortComplex.shortExact_of_iso ?_ hTop
    exact ShortComplex.isoMk (Iso.refl _) β.symm (Iso.refl _) (by simp) (by simp)
  · refine ShortComplex.shortExact_of_iso ?_ hMiddle
    exact ShortComplex.isoMk (Iso.refl _) α.symm (Iso.refl _) (by simp) (by simp)
  · refine ShortComplex.shortExact_of_iso ?_ hColumn
    exact ShortComplex.isoMk γ.symm α.symm β.symm (by simp) (by simp)
  · rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc, hsquare, Category.assoc]
  · rw [hright]
    simp
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
      hbottom, Category.assoc]

/-! ### The diagram of Stacks 0BLD -/

variable (X : Scheme.{u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X.toRingedSpace).obj.obj (op (⊤ : Opens X.toRingedSpace.carrier)))
  (f : A) (ℱ : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The inverse system `n ↦ RΓ(X, ℱ/f^(n+1)ℱ)` of objects of `D(A)`. -/
abbrev quotientSections : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Csys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ

/-- The inverse system `n ↦ Hᵖ(X, ℱ/f^(n+1)ℱ)` of `A`-modules. -/
abbrev quotientCohomology (p : ℤ) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  quotientSections X ρ f ℱ ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) p

/-- The object `RΓ(X, lim ℱ/f^(n+1)ℱ)` of `D(A)`. -/
abbrev limitQuotientSections : DerivedCategory (ModuleCat.{u} A) :=
  (derivedSectionsOver X.toRingedSpace ρ).obj
    ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).obj
      (limit (quotientTower X ρ f ℱ)))

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

This is the diagram of [Stacks, Tag 0H32] for `K = RΓ(X, ℱ)`, carried to the honest quotients
`ℱ/fⁿℱ` along the displayed equality `RΓ(X, lim ℱ/fⁿℱ) ≅ RΓ(X, ℱ)^∧` and the two comparisons of
limits provided by the middle-column theorem. -/
@[stacks 0BLD "the commutative diagram with exact rows and columns, in full: the top row \
`0 ⟶ Hᵖ(X, ℱ)^ ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`, the middle row \
`0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`, the left column \
`0 ⟶ R¹lim Hᵖ(X, ℱ)[fⁿ] ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, ℱ)^ ⟶ 0`, the middle column \
`0 ⟶ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ 0`, the bottom isomorphism \
`R¹lim Hᵖ(X, ℱ)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)`, the identity right column, and the commutativity of \
the three squares"]
theorem exists_formalFunctionsDiagram
    [HasProduct fun n : ℕ ↦ (Csys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (quotientSections X ρ f ℱ).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (Ksys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦
      (Ksys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ).obj ⟨n⟩]
    (p : ℤ) :
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
  intro Hq P completion adj completed ordinaryCompletion tate h0Completion torsionR1
    limitQuotientCohomology previousQuotientR1 sectionsCohomology
  have hprod : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  -- The displayed equality: `RΓ(X, lim ℱ/fⁿℱ) ≅ RΓ(X, ℱ)^∧`.
  obtain ⟨eFhat⟩ :=
    (nonempty_iso_derivedSections_limit_quotientTower_derivedCompletion
      X ρ f ℱ hℱ hstab completion adj).1
  -- The middle column, whose last two conclusions are the comparisons of the limits of the
  -- cohomology of the quotient tower with those of the Koszul tower.
  obtain ⟨Ehat, hEhat⟩ := exists_isDerivedLimit (Ksys (mulF X ρ f ℱ))
  obtain ⟨_, aT, bT, hT, hdeg⟩ :=
    exists_shortExact_homology_derivedSections_limit_quotientTower
      X ρ f ℱ hℱ hstab Ehat hEhat
  obtain ⟨_, _, _, _, _, _, _, _, ⟨βq⟩, ⟨γq⟩⟩ := hdeg p
  -- The levelwise identification of the two `f`-power Koszul towers.
  obtain ⟨eKos⟩ :=
    nonempty_iso_koszulTower_comp_derivedSections X ρ f ℱ
  have e := fun q ↦
    Functor.isoWhiskerRight eKos (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q)
  -- Tag 0H32 for `K = RΓ(X, ℱ)`.
  have h32 := PrincipalCompletionDiagram.derivedCompletion_principal_homology_comparison A f
    (derivedSectionsModule X ρ ℱ) p
  obtain ⟨S, hS⟩ := h32 completion adj
  dsimp only at hS
  obtain ⟨_, _, _, _, _, _, _, _, _, _, bottom, _, _, _, _, _, _, _, _, _,
    hTop, hMiddle, hLeft, hColumn, hsquare, hright, hbottom⟩ := hS
  exact transportDiagram
    (γq ≪≫ firstDerivedLimitMapIso (e (p - 1)))
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).mapIso eFhat)
    (βq ≪≫ HasLimit.isoOfNatIso (e p))
    bottom hTop hMiddle hLeft hColumn hsquare hright hbottom

/-- **The top row of the diagram of [Stacks, Tag 0BLD].** With `A`, `f`, `X` and `ℱ` as in the
source, for every `p` there is a short exact sequence

`0 ⟶ Hᵖ(X, ℱ)^ ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`,

where `Hᵖ(X, ℱ)^ = lim Hᵖ(X, ℱ)/fⁿHᵖ(X, ℱ)` is the ordinary `f`-adic completion and `T_f(-)` the
`f`-adic Tate module. No reflector onto the derived-complete objects appears in the statement;
one is supplied internally. -/
@[stacks 0BLD "the top row of the diagram: the short exact sequence \
`0 ⟶ Hᵖ(X, ℱ)^ ⟶ lim Hᵖ(X, ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0` relating the ordinary f-adic completion \
of Hᵖ(X, ℱ) to the inverse limit of the cohomology of the quotients and the f-adic Tate module of \
Hᵖ⁺¹(X, ℱ). Unconditional: no reflector onto the derived-complete objects is assumed"]
theorem exists_shortExact_topRow
    [HasProduct fun n : ℕ ↦ (Csys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (quotientSections X ρ f ℱ).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (Ksys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦
      (Ksys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ).obj ⟨n⟩]
    (p : ℤ) :
    let Hq : ℤ → ModuleCat.{u} A := fun q ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (derivedSectionsModule X ρ ℱ)
    ∃ (topIn : limit (CompletionSequences.powerQuotientSystem A (Hq p) f) ⟶
        limit (quotientCohomology X ρ f ℱ p))
      (topOut : limit (quotientCohomology X ρ f ℱ p) ⟶
        CompletionSequences.adicTateModule A (Hq (p + 1)) f)
      (htop : topIn ≫ topOut = 0),
      (ShortComplex.mk topIn topOut htop).ShortExact := by
  intro Hq
  have := Stacks.FormalFunctions.derivedComplete_principal_ι_isRightAdjoint A f
  obtain ⟨topIn, topOut, htop, _, _, _, _, _, _, _, _, _, _, hTop, _⟩ :=
    exists_formalFunctionsDiagram X ρ f ℱ hℱ hstab p
      (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun L ↦ IsDerivedComplete (Ideal.span {f}) L).ι.leftAdjoint
      (Adjunction.ofIsRightAdjoint _)
  exact ⟨topIn, topOut, htop, hTop⟩

/-- **The middle row of the diagram of [Stacks, Tag 0BLD].** With `A`, `f`, `X` and `ℱ` as in the
source and `(-)^∧` derived `f`-adic completion presented by an arbitrary left adjoint to the
inclusion of the derived-complete objects, for every `p` there is a short exact sequence

`0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`. -/
@[stacks 0BLD "the middle row of the diagram: the short exact sequence \
`0 ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, lim ℱ/fⁿℱ) ⟶ T_f(Hᵖ⁺¹(X, ℱ)) ⟶ 0`, with `(-)^∧` the derived f-adic \
completion presented as in Stacks 0BKG by an arbitrary left adjoint to the inclusion of the \
derived-complete objects"]
theorem exists_shortExact_middleRow
    [HasProduct fun n : ℕ ↦ (Csys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (quotientSections X ρ f ℱ).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (Ksys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦
      (Ksys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ).obj ⟨n⟩]
    (p : ℤ) :
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
  intro Hq P completion adj
  obtain ⟨_, _, _, middleIn, middleOut, hmiddle, _, _, _, _, _, _, _, _, hMiddle, _⟩ :=
    exists_formalFunctionsDiagram X ρ f ℱ hℱ hstab p completion adj
  exact ⟨middleIn, middleOut, hmiddle, hMiddle⟩

/-- **The left column of the diagram of [Stacks, Tag 0BLD].** With `A`, `f`, `X` and `ℱ` as in the
source and `(-)^∧` derived `f`-adic completion presented by an arbitrary left adjoint to the
inclusion of the derived-complete objects, for every `p` there is a short exact sequence

`0 ⟶ R¹lim Hᵖ(X, ℱ)[fⁿ] ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, ℱ)^ ⟶ 0`

relating the derived completion of `Hᵖ(X, ℱ)` in degree zero to its ordinary `f`-adic completion
and to the first derived inverse limit of its `f`-power torsion. -/
@[stacks 0BLD "the left column of the diagram: the short exact sequence \
`0 ⟶ R¹lim Hᵖ(X, ℱ)[fⁿ] ⟶ H⁰(Hᵖ(X, ℱ)^∧) ⟶ Hᵖ(X, ℱ)^ ⟶ 0` comparing the degree-zero derived \
f-adic completion of Hᵖ(X, ℱ) with its ordinary f-adic completion and with the first derived \
inverse limit of its f-power torsion"]
theorem exists_shortExact_leftColumn
    [HasProduct fun n : ℕ ↦ (Csys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (quotientSections X ρ f ℱ).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (Ksys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦
      (Ksys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ).obj ⟨n⟩]
    (p : ℤ) :
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
  intro Hq P completion adj
  obtain ⟨_, _, _, _, _, _, leftIn, leftOut, hleft, _, _, _, _, _, _, hLeft, _⟩ :=
    exists_formalFunctionsDiagram X ρ f ℱ hℱ hstab p completion adj
  exact ⟨leftIn, leftOut, hleft, hLeft⟩

/-- **The bottom isomorphism of the diagram of [Stacks, Tag 0BLD].** With `A`, `f`, `X` and `ℱ` as
in the source, for every `p` the first derived inverse limit of the `f`-power torsion of
`Hᵖ(X, ℱ)` is isomorphic to the first derived inverse limit of `Hᵖ⁻¹(X, ℱ/fⁿℱ)`:

`R¹lim Hᵖ(X, ℱ)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)`. -/
@[stacks 0BLD "the bottom isomorphism of the diagram: \
`R¹lim Hᵖ(X, ℱ)[fⁿ] ≅ R¹lim Hᵖ⁻¹(X, ℱ/fⁿℱ)` between the first derived inverse limit of the \
f-power torsion of Hᵖ(X, ℱ) and the first derived inverse limit of Hᵖ⁻¹ of the quotients. \
Unconditional: no reflector onto the derived-complete objects is assumed"]
theorem nonempty_iso_firstDerivedLimit_torsion
    [HasProduct fun n : ℕ ↦ (Csys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (quotientSections X ρ f ℱ).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦ (Ksys (mulF X ρ f ℱ)).obj ⟨n⟩]
    [HasProduct fun n : ℕ ↦
      (Ksys (mulF X ρ f ℱ) ⋙ derivedSectionsOver X.toRingedSpace ρ).obj ⟨n⟩]
    (p : ℤ) :
    let Hq : ℤ → ModuleCat.{u} A := fun q ↦
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj (derivedSectionsModule X ρ ℱ)
    Nonempty (CompletionSequences.firstDerivedLimit A
        (PrincipalTorsionTower.powerTorsionSystem A (Hq p) f) ≅
      CompletionSequences.firstDerivedLimit A (quotientCohomology X ρ f ℱ (p - 1))) := by
  intro Hq
  have := Stacks.FormalFunctions.derivedComplete_principal_ι_isRightAdjoint A f
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, bottom, _⟩ :=
    exists_formalFunctionsDiagram X ρ f ℱ hℱ hstab p
      (show ObjectProperty (DerivedCategory (ModuleCat.{u} A)) from
        fun L ↦ IsDerivedComplete (Ideal.span {f}) L).ι.leftAdjoint
      (Adjunction.ofIsRightAdjoint _)
  exact ⟨bottom⟩

end Diagram

end Stacks.Algebraization.PrincipalQuotientTowerDiagram

end
