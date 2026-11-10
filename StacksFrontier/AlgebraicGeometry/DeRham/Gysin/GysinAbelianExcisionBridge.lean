module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionAbelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompIsoSpellings
public import
  StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.AbelianLocalCohomologyExcision

/-!
# The abelian excision at the spelling of the Gysin target, and what 0G87 is now down to

`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso` is excision for
the local cohomology sheaves of sheaves of abelian groups, in every degree: for a closed subset
`T` of a topological space and an open subset `W`,

`(i_*ℋ ⁿ_T(G))|_W ≅ i'_*ℋ ⁿ_{W ∩ T}(G|_W)`,

naturally in the abelian sheaf `G`.  This file reads it at the spelling of the Gysin target of
[Stacks, Tag 0G87] — the ambient space is a scheme, the open subset is a chart, and the functor is
`Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward` — and reduces the
compatibility the square of that tag needs,
`Stacks.Gysin.SupportCohomologyRestrictAbNatural`, to one equation.

## Main definitions and results

* `Stacks.Gysin.abelianExcision`: the abelian excision read at the Gysin spelling.  The three
  identifications it needs — of `Stacks.Gysin.abelianRestrict` with Mathlib's restriction of
  abelian sheaves to an open subset, of `W.ι ⁻¹' T` with the preimage subset read on the open
  subspace, and of `Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward` with the
  abelian local cohomology sheaf functor followed by the direct image from the closed subset — all
  hold by `rfl`, on `Y` and on the chart alike, so this is a reading and not a transport.
* `Stacks.Gysin.abelianExcision_naturality`: **it is natural in an arbitrary sheaf of abelian
  groups**, in particular along a morphism that is additive but not `𝒪_Y`-linear.  This is the
  naturality of the natural isomorphism and nothing more, and it is the statement the library did
  not have: every excision in it was for sheaves of modules, so none of them applied to a de Rham
  differential.
* `Stacks.Gysin.excisionAbComparison_eq`: `Stacks.Gysin.excisionAbComparison` written out as the
  conjugation of the abelian reading of the *derived* excision by the two copies of
  [Stacks, Tag 0G74] part (2).
* `Stacks.Gysin.ExcisionAbComparisonEqAbelianExcision`: **the one statement between the library
  and the abelian reading of the excision** — that those two comparisons agree.  Both are
  isomorphisms with the same source and target.  It is **proved**, as
  `Stacks.Gysin.excisionAbComparisonEqAbelianExcision` of
  `StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean`.
* `Stacks.Gysin.supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq`: **that one
  statement is all it takes** — granting it,
  `Stacks.Gysin.SupportCohomologyRestrictAbNatural` holds for *every* morphism of the underlying
  abelian sheaves, the de Rham differential included.  Its modular half is
  `Stacks.Gysin.supportCohomologyRestrictAbNatural_of_excisionAbComparison_naturality`, which asks
  only for the naturality of `Stacks.Gysin.excisionAbComparison` along the one morphism in
  question.

## Implementation notes

**How the cancellation is carried out.**  By `excisionAbComparison_eq`,
`Stacks.Gysin.restrictAbHom_supportCohomologySheafAbelianMap` and
`Stacks.Gysin.supportCohomologySheafAbelianMap_eq`, both sides of
`Stacks.Gysin.SupportCohomologyRestrictAbNatural` are three-factor composites whose outer factors
are the four copies of [Stacks, Tag 0G74] part (2); the two inner vertical sides are
`excisionAbComparison` at the source and at the target module, so cancelling the outer factors
reduces the square to the naturality of that comparison.

The cancellation mixes the two spellings `(abelianRestrict W).obj ((abelianSheaf Y).obj ℱ)` and
`(abelianSheaf W).obj (ℱ|_W)` of one object, which are definitionally equal by
`Stacks.Gysin.restrictFunctorCompAbelianSheafIso` but syntactically different.  What makes the
identification affordable at `ℱ := Stacks.Perfect.SupportedFraction.supportCohomologySheaf hT F n`
is that no *metavariable* ever meets it: `cancel_conj` is stated at an arbitrary category with all
eight objects implicit and all ten morphisms explicit, so every object is read off a given
argument's type rather than solved for, and the reassociation that follows is a `calc` of
`CategoryTheory.Category.assoc` steps inside that one variable-category lemma.  The outer step
likewise avoids a rewrite under the crossing: it is `congrArg` at an explicit lambda, not `rw`.

**No `@[stacks 0G87]` attribute is attached here.**  The tag counts only on a declaration proved
under the source's own hypotheses, and `ExcisionAbComparisonEqAbelianExcision` is a `Prop`, not a
theorem: the two reductions below take it as an explicit hypothesis and are implications, not
registrations.  Both of the things that used to stand between the library and the tag are now
theorems — that equation, by
`Stacks.Gysin.excisionAbComparisonEqAbelianExcision` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean`, and the
chart-local naturality of the class map of [Stacks, Tag 0G7Q], by
`Stacks.Gysin.chartFractionCommutesWithDeRham` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinChartFractionDeRham.lean` — and the tag itself
is registered on `Stacks.Gysin.gysinHom_comm_deRham_of_conormalRank` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinDeRhamConormalRank.lean`.

## References

* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SupportedComplexes (abelianLocalCohomologySheafRestrictNatIso)
open Stacks.Perfect.AbelianFraction (abelianSheaf)
open Stacks.Perfect.GysinAbelianSquare
  (abelianLocalCohomologyPushforward supportCohomologySheafForgetIso)

universe u

namespace Stacks.Gysin

variable {Y : Scheme.{u}} (W : Y.Opens) {T : Set Y} (hT : IsClosed T)
  (hTW : IsClosed (W.ι ⁻¹' T))

/-! ### The abelian excision at the spelling of the Gysin target -/

/-- **Excision for the abelian local cohomology sheaves, at the spelling of the Gysin target of
[Stacks, Tag 0G87].**  For an arbitrary sheaf of abelian groups `G` on `Y`, the restriction to the
chart `W` of `i_*ℋ ⁿ_T(G)` is `i'_*ℋ ⁿ_{W ∩ T}(G|_W)`.

This is `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso` at the
space `Y`, with no transport: `Stacks.Gysin.abelianRestrict W` *is* the restriction of abelian
sheaves to the open subset `W`, and
`Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward` *is* the abelian local
cohomology sheaf followed by the direct image from the closed subset, on `Y` and on `W` alike. -/
def abelianExcision (n : ℕ)
    (G : Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}) :
    (abelianRestrict W).obj
        ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).obj G) ⟶
      (abelianLocalCohomologyPushforward W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW n).obj
        ((abelianRestrict W).obj G) :=
  (abelianLocalCohomologySheafRestrictNatIso (X := Y.carrier) T W hT hTW n).hom.app G

/-- **The abelian excision is natural in an arbitrary sheaf of abelian groups.**  In particular it
is natural along a morphism `ψ` that is additive but not `𝒪_Y`-linear, which is the case the chart
transport of [Stacks, Tag 0G87] needs and the case no module-level excision can supply. -/
theorem abelianExcision_naturality (n : ℕ)
    {G H : Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}} (ψ : G ⟶ H) :
    (abelianRestrict W).map
          ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).map ψ) ≫
        abelianExcision W hT hTW n H =
      abelianExcision W hT hTW n G ≫
        (abelianLocalCohomologyPushforward W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW n).map
          ((abelianRestrict W).map ψ) :=
  (abelianLocalCohomologySheafRestrictNatIso (X := Y.carrier) T W hT hTW n).hom.naturality ψ

/-! ### What 0G87's remaining compatibility is now, and nothing else -/

/-- **`Stacks.Gysin.excisionAbComparison` spelled out**: the abelian reading of the *derived*
excision of [Stacks, Tag 0G78], conjugated by the two copies of [Stacks, Tag 0G74] part (2).  True
by definition, and recorded because it is the left-hand side of the one equation
`ExcisionAbComparisonEqAbelianExcision` below. -/
theorem excisionAbComparison_eq (n : ℕ) (F : Y.Modules) :
    excisionAbComparison W hT hTW n F =
      (abelianRestrict W).map ((supportCohomologySheafForgetIso hT n).inv.app F) ≫
        supportCohomologyRestrictAbHom W hT hTW (n : ℤ) F ≫
          (supportCohomologySheafForgetIso hTW n).hom.app
            ((Scheme.Modules.restrictFunctor W.ι).obj F) := rfl

/-- **The one statement between the library and the abelian reading of the excision that the
square of [Stacks, Tag 0G87] needs**: the abelian
reading of the derived excision agrees, at the underlying abelian sheaf of every `𝒪_Y`-module, with
the classical abelian excision of
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso`.

Both sides are isomorphisms with *the same* source and target — that the equation is even
well-typed is the content of the three `rfl` identifications described in the module docstring —
and each is the comparison `(i_*ℋ ⁿ_T(ℱ_ab))|_W ⟶ i'_*ℋ ⁿ_{W ∩ T}(ℱ_ab|_W)`, one built from the
derived excision of [Stacks, Tag 0G78] and one from the classical derived functors of abelian
sections with support.  It is the derived-versus-classical comparison, and it is proved:
`Stacks.Gysin.excisionAbComparison_eq_abelianExcision` of
`StacksFrontier/AlgebraicGeometry/DeRham/Gysin/GysinExcisionAbelianAgreement.lean`, from the
degree-`n` forget square and the identification of the derived excision of [Stacks, Tag 0G78]
with `Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`.

Granting it, `Stacks.Gysin.SupportCohomologyRestrictAbNatural` holds for every morphism `ψ` of the
underlying abelian sheaves: that is
`Stacks.Gysin.supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq` below. -/
def ExcisionAbComparisonEqAbelianExcision (n : ℕ) : Prop :=
  ∀ F : Y.Modules, excisionAbComparison W hT hTW n F =
    abelianExcision W hT hTW n ((abelianSheaf Y).obj F)

/-! ### The cancellation: that one equation gives the square for every additive `ψ` -/

/-- **A square conjugated by two pairs of mutually inverse morphisms.**  Given a commuting square
`m ≫ b₂ ≫ v ≫ d₁ = (a₂ ≫ u ≫ c₁) ≫ m'` whose vertical sides are the three-factor conjugates
`a₂ ≫ u ≫ c₁` and `b₂ ≫ v ≫ d₁`, cancelling `a₁` against `a₂` on the left and `d₁` against `d₂`
on the right leaves the square `(a₁ ≫ m ≫ b₂) ≫ v = u ≫ c₁ ≫ m' ≫ d₂` between `u` and `v`.
Stated at an arbitrary category, every object and morphism explicit, so that applying it never
asks the elaborator to solve an object metavariable. -/
private theorem cancel_conj {D : Type*} [Category* D] {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : D}
    (a₁ : x₀ ⟶ x₁) (a₂ : x₁ ⟶ x₀) (m : x₁ ⟶ y₁) (b₂ : y₁ ⟶ y₀) (v : y₀ ⟶ y₂)
    (u : x₀ ⟶ x₂) (c₁ : x₂ ⟶ x₃) (m' : x₃ ⟶ y₃) (d₁ : y₂ ⟶ y₃) (d₂ : y₃ ⟶ y₂)
    (hnat : m ≫ b₂ ≫ v ≫ d₁ = (a₂ ≫ u ≫ c₁) ≫ m')
    (ha : a₁ ≫ a₂ = CategoryStruct.id x₀) (hd : d₁ ≫ d₂ = CategoryStruct.id y₂) :
    (a₁ ≫ m ≫ b₂) ≫ v = u ≫ c₁ ≫ m' ≫ d₂ := by
  calc (a₁ ≫ m ≫ b₂) ≫ v = a₁ ≫ (m ≫ b₂ ≫ v ≫ d₁) ≫ d₂ := by simp [hd]
    _ = u ≫ c₁ ≫ m' ≫ d₂ := by
      rw [hnat]
      simp [reassoc_of% ha]

/-- **`Stacks.Gysin.excisionAbComparison` is natural in an arbitrary morphism of the underlying
abelian sheaves, as soon as it is the abelian excision.**  Its naturality in a morphism of
*modules* is `Stacks.Gysin.supportCohomologyRestrictIso_naturality`; the content here is that
`abelianExcision` is a natural transformation of functors on **all** sheaves of abelian groups, so
once the two comparisons are identified the square is `abelianExcision_naturality`. -/
theorem excisionAbComparison_naturality (n : ℕ)
    (hC : ExcisionAbComparisonEqAbelianExcision W hT hTW n)
    {F G : Y.Modules} (ψ : (abelianSheaf Y).obj F ⟶ (abelianSheaf Y).obj G) :
    (abelianRestrict W).map
          ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).map ψ) ≫
        excisionAbComparison W hT hTW n G =
      excisionAbComparison W hT hTW n F ≫
        (abelianLocalCohomologyPushforward W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW n).map
          ((abelianRestrict W).map ψ) := by
  rw [hC F, hC G]
  exact abelianExcision_naturality W hT hTW n ψ

/-- **The square of [Stacks, Tag 0G87] for every additive `ψ`, from the naturality of
`Stacks.Gysin.excisionAbComparison`.**  By
`Stacks.Gysin.restrictAbHom_supportCohomologySheafAbelianMap` and
`Stacks.Gysin.supportCohomologySheafAbelianMap_eq` both sides of
`Stacks.Gysin.SupportCohomologyRestrictAbNatural` are three-factor composites whose outer factors
are the four copies of [Stacks, Tag 0G74] part (2); the two inner vertical sides are exactly
`excisionAbComparison` at `F` and at `G`, so cancelling the outer factors — `cancel_conj` — turns
the naturality of that comparison into the square. -/
theorem supportCohomologyRestrictAbNatural_of_excisionAbComparison_naturality (n : ℕ)
    {F G : Y.Modules} (ψ : (abelianSheaf Y).obj F ⟶ (abelianSheaf Y).obj G)
    (hnat : (abelianRestrict W).map
          ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).map ψ) ≫
        excisionAbComparison W hT hTW n G =
      excisionAbComparison W hT hTW n F ≫
        (abelianLocalCohomologyPushforward W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW n).map
          ((abelianRestrict W).map ψ)) :
    SupportCohomologyRestrictAbNatural W hT hTW n ψ :=
  (congrArg (fun x => x ≫ supportCohomologyRestrictAbHom W hT hTW (n : ℤ) G)
    ((abelianRestrict W).map_comp₃ ((supportCohomologySheafForgetIso hT n).hom.app F)
      ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).map ψ)
      ((supportCohomologySheafForgetIso hT n).inv.app G))).trans
    (cancel_conj
      ((abelianRestrict W).map ((supportCohomologySheafForgetIso hT n).hom.app F))
      ((abelianRestrict W).map ((supportCohomologySheafForgetIso hT n).inv.app F))
      ((abelianRestrict W).map
        ((abelianLocalCohomologyPushforward Y.toRingedSpace T hT n).map ψ))
      ((abelianRestrict W).map ((supportCohomologySheafForgetIso hT n).inv.app G))
      (supportCohomologyRestrictAbHom W hT hTW (n : ℤ) G)
      (supportCohomologyRestrictAbHom W hT hTW (n : ℤ) F)
      ((supportCohomologySheafForgetIso hTW n).hom.app
        ((Scheme.Modules.restrictFunctor W.ι).obj F))
      ((abelianLocalCohomologyPushforward W.toScheme.toRingedSpace (W.ι ⁻¹' T) hTW n).map
        ((abelianRestrict W).map ψ))
      ((supportCohomologySheafForgetIso hTW n).hom.app
        ((Scheme.Modules.restrictFunctor W.ι).obj G))
      ((supportCohomologySheafForgetIso hTW n).inv.app
        ((Scheme.Modules.restrictFunctor W.ι).obj G))
      hnat (Stacks.DerivedIndexing.map_comp_id (abelianRestrict W) _ _ (Iso.hom_inv_id_app _ _))
      (Iso.hom_inv_id_app _ _))

/-- **The one equation gives the compatibility the square of [Stacks, Tag 0G87] needs, for every
morphism `ψ` of the underlying abelian sheaves** — in particular for one that is additive and
`𝒪_Y`-linear for no `Y`, which is the case
`Stacks.Gysin.supportCohomologyRestrictAbNatural_abelianSheaf_map` cannot reach.

So `Stacks.Gysin.ExcisionAbComparisonEqAbelianExcision` is not merely *sufficient* in prose: it is
the single remaining input, and everything between it and
`Stacks.Gysin.SupportCohomologyRestrictAbNatural` is proved. -/
theorem supportCohomologyRestrictAbNatural_of_excisionAbComparison_eq (n : ℕ)
    (hC : ExcisionAbComparisonEqAbelianExcision W hT hTW n)
    {F G : Y.Modules} (ψ : (abelianSheaf Y).obj F ⟶ (abelianSheaf Y).obj G) :
    SupportCohomologyRestrictAbNatural W hT hTW n ψ :=
  supportCohomologyRestrictAbNatural_of_excisionAbComparison_naturality W hT hTW n ψ
    (excisionAbComparison_naturality W hT hTW n hC ψ)

end Stacks.Gysin

end
