module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.Assembly
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.SquareStep
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple

/-!
# Quasi-coherent modules on a quasi-compact quasi-separated algebraic space are filtered
colimits of modules of finite presentation

**Stacks 07V9.**  Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme
`S`.  Every quasi-coherent `𝒪_X`-module is a filtered colimit of `𝒪_X`-modules of finite
presentation.

**Stacks 086Y.**  On such an `X`, a quasi-coherent `𝒪_X`-module of finite type is a colimit,
over a directed poset, of `𝒪_X`-modules of finite presentation with surjective transition maps.

## The proof

The source deduces Stacks 07V9 from absolute Noetherian approximation (Stacks 07SU), and
remarks just before the lemma that it "can also be deduced directly from Decent Spaces,
Lemma 07ST without passing through absolute Noetherian approximation".  This file takes that
route; Stacks 07SU is neither used nor assumed.

The key property is local generation by modules of finite presentation
(`AlgebraicGeometry.Space.IsLocallyFpGenerated`): every section of the module over every étale
chart is, locally on the chart, the image of a section of a module of finite presentation
mapping to it.  It holds for every quasi-coherent module on every quasi-compact quasi-separated
algebraic space, by the induction principle of Stacks 08GP
(`AlgebraicGeometry.Space.qcqs_induction_on_self`), which rests on the filtration of
Stacks 07ST:

* on an affine space it holds because sections over affine charts are combinations of global
  sections (Descent 03DX(2)), `AlgebraicGeometry.Space.isLocallyFpGenerated_of_isAffineSpace`;
* it passes across an elementary distinguished square with affine étale member,
  `AlgebraicGeometry.Space.isLocallyFpGenerated_of_isElementaryDistinguishedSquare`, by
  extending modules of finite presentation from the open subspace and glueing them across the
  square.

Local generation then gives the filtered colimit presentation by the argument of Stacks 07UW's
second half (a quotient of a direct sum of modules of finite presentation, compactness of
modules of finite presentation on a quasi-compact quasi-separated space, Stacks 07U7, and
cokernels, Stacks 0H98), and the directed system with surjective transition maps of Stacks 086Y
by the source's proof of that lemma; see
`StacksFrontier/AlgebraicGeometry/Spaces/FinitePresentationGeneration/Assembly.lean`.

## Main results

* `AlgebraicGeometry.Space.isLocallyFpGenerated_of_isQuasiCompactSpace`: local generation on a
  quasi-compact quasi-separated algebraic space.
* `AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentationOnSite`:
  **Stacks 07V9**, with a small filtered index category and finite presentation in the on-site
  rendering of Stacks 03DL(7).
* `AlgebraicGeometry.Space.exists_isFilteredColimit_isFinitePresentation`: **Stacks 07V9** in
  the conclusion shape of the earlier conditional statement
  `AlgebraicGeometry.Space.isFilteredColimit_isFinitePresentation_of_isQuasiCompactSpace`.
* `AlgebraicGeometry.Space.exists_directed_isFinitePresentation_epi`: **Stacks 086Y**.

## References

* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 086Y](https://stacks.math.columbia.edu/tag/086Y)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Local generation by modules of finite presentation on a quasi-compact quasi-separated
algebraic space.**  Every section of a quasi-coherent `𝒪_X`-module over an étale chart is,
locally on the chart, the image of a section of an `𝒪_X`-module of finite presentation mapping
to it.  Proved by the induction principle of Stacks 08GP. -/
theorem isLocallyFpGenerated_of_isQuasiCompactSpace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (F : Modules.{u, u} B S hS X hX) (hF : F.IsQuasicoherentOnSite) :
    IsLocallyFpGenerated B S hS hX F := by
  refine qcqs_induction_on_self B S hS hZ ⟨X, hX⟩ hqc hqs
    (fun Y _ => ∀ (hY : IsAlgebraicSpace B S hS Y) (K : Modules.{u, u} B S hS Y hY),
      K.IsQuasicoherentOnSite → IsLocallyFpGenerated B S hS hY K) ?_ ?_ hX F hF
  · intro V hVaff hY K hK
    exact isLocallyFpGenerated_of_isAffineSpace B S hS (V := ⟨V.1.left.1, hY⟩) hVaff K hK
  · intro W V U f _ hsq _ hWqs hUqc hVaff hPU _ _ hY K hK
    exact isLocallyFpGenerated_of_isElementaryDistinguishedSquare B S hS hZ hsq hVaff hUqc hWqs
      (fun K' hK' => hPU (edsOpen B S hS hsq).2 K' hK') K hK

/-- **Stacks 07V9.**  Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme
`S`.  Then every quasi-coherent `𝒪_X`-module `F` is a filtered colimit of `𝒪_X`-modules of
finite presentation: there is a small filtered category `I`, a diagram `D` of `𝒪_X`-modules of
finite presentation indexed by it and a colimit cocone on `D` with vertex `F`.

The hypotheses are the source's.  The proof does not use absolute Noetherian approximation; it
follows the route the source indicates, through the filtration of Decent Spaces, Lemma 07ST, in
the form of the induction principle of Stacks 08GP. -/
@[stacks 07V9 "with a small filtered index category and finite presentation in the on-site \
rendering of Stacks 03DL(7)"]
theorem exists_isFilteredColimit_isFinitePresentationOnSite
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (F : Modules.{u, u} B S hS X hX) (hF : F.IsQuasicoherentOnSite) :
    ∃ (I : Type u) (inst : SmallCategory I),
      let _ := inst
      ∃ (_ : IsFiltered I) (D : I ⥤ Modules.{u, u} B S hS X hX)
        (φ : D ⟶ (Functor.const I).obj F),
        (∀ i, (D.obj i).IsFinitePresentationOnSite) ∧ Nonempty (IsColimit (Cocone.mk F φ)) :=
  exists_small_isFilteredColimit_isFinitePresentationOnSite_of_isLocallyFpGenerated B S hS hZ hX
    hqc hqs (isLocallyFpGenerated_of_isQuasiCompactSpace B S hS hZ hX hqc hqs)
    F hF

/-- **Stacks 07V9**, in the conclusion shape of the conditional statement
`AlgebraicGeometry.Space.isFilteredColimit_isFinitePresentation_of_isQuasiCompactSpace` (an index
category with objects in `Type (u + 1)` and morphisms in `Type u`, finite presentation in the
sense of Mathlib's `SheafOfModules.IsFinitePresentation`), with none of its carried inputs. -/
@[stacks 07V9 "in the rendering by Mathlib's finite presentation predicate"]
theorem exists_isFilteredColimit_isFinitePresentation
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (F : Modules.{u, u} B S hS X hX) (hF : F.IsQuasicoherentOnSite) :
    ∃ (K : Type (u + 1)) (inst : Category.{u} K),
      let _ := inst
      ∃ (_ : IsFiltered K) (D : K ⥤ Modules.{u, u} B S hS X hX)
        (φ : D ⟶ (Functor.const K).obj F),
        (∀ k, (D.obj k).IsFinitePresentation) ∧ Nonempty (IsColimit (Cocone.mk F φ)) :=
  exists_isFilteredColimit_isFinitePresentation_of_isLocallyFpGenerated B S hS hZ hX hqc hqs
    (isLocallyFpGenerated_of_isQuasiCompactSpace B S hS hZ hX hqc hqs) F hF

/-- **Stacks 086Y.**  Let `X` be a quasi-compact and quasi-separated algebraic space over a
scheme `S` and let `M` be a finite type quasi-coherent `𝒪_X`-module.  Then `M` is the colimit of
a system of `𝒪_X`-modules of finite presentation indexed by a directed poset, all of whose
transition maps are surjective.

The source writes `ℱ = lim ℱ_i`, but its proof produces `colim 𝒢_i/𝒦_a`; the conclusion is a
colimit, as in the scheme-level counterpart Stacks 086M. -/
@[stacks 086Y]
theorem exists_directed_isFinitePresentation_epi
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (M : Modules.{u, u} B S hS X hX) [M.IsQuasicoherentOnSite] [M.IsFiniteTypeOnSite] :
    ∃ (I : Type (u + 1)) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
      (D : I ⥤ Modules.{u, u} B S hS X hX) (φ : D ⟶ (Functor.const I).obj M)
      (_ : IsColimit (Cocone.mk M φ)),
      (∀ i, (D.obj i).IsFinitePresentationOnSite) ∧
        ∀ (i j : I) (h : i ≤ j), Epi (D.map (homOfLE h)) :=
  exists_directed_isFinitePresentation_epi_of_isLocallyFpGenerated B S hS hZ hX hqc hqs
    (isLocallyFpGenerated_of_isQuasiCompactSpace B S hS hZ hX hqc hqs) M

end AlgebraicGeometry.Space

end
