module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonSituation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CohomologyViaSectionComplex

/-!
# The higher change-of-topology direct image as a sheafification

Let `C` carry a finer coverage `τ` and a coarser coverage `τ'` as in Stacks 0EZ3, and write
`ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology morphism over an object `X`. For an abelian
sheaf `ℱ` on the finer localized site and an injective resolution `I` of `ℱ`, the higher direct
image `R^i ε_{X,*} ℱ` is the sheafification, for the coarser localized topology, of the presheaf
`V ↦ H^i(I^•(V))` of `i`-th cohomology of the sections of `I`.

Consequently `R^i ε_{X,*} ℱ` vanishes as soon as every cohomology class of degree `i` dies after
restriction to the members of some covering for the *coarser* topology — the criterion by which
the vanishing condition `(V_n)` of Stacks 0EZ3 is verified in practice.

## Main definitions

* `Stacks.ComparingTopologies.rightDerivedAbelianComparisonPushforwardIso`: the identification
  of `R^i ε_{X,*} ℱ` with the coarse sheafification of the `i`-th homology presheaf of the
  section complex of an injective resolution of `ℱ`.

## Main results

* `Stacks.ComparingTopologies.sheafToPresheaf_mapHomologicalComplex_abelianComparisonPushforward`:
  the change-of-topology direct image of an injective resolution has, as its underlying complex
  of presheaves, exactly the section complex of that resolution.
* `Stacks.ComparingTopologies.isZero_rightDerived_abelianComparisonPushforward_of_locally_zero`
  and its primed variant: the vanishing criterion, stated for the homology presheaf of the
  section complex and for cohomology classes respectively.

## Implementation notes

This is the abelian-sheaf instance, for the change-of-topology morphism, of Stacks 072W; the tag
itself is about ringed sites and sheaves of modules and carries its attribute in
`StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf`,
so nothing here is tagged.

The identification is elementary because the change-of-topology direct image leaves the
underlying presheaf of a sheaf unchanged, remembering only a weaker sheaf condition: the complex
of presheaves underlying the image of `I` is *equal* to the section complex of `I`, which is what
`sheafToPresheaf_mapHomologicalComplex_abelianComparisonPushforward` records. Sheafification is
exact, hence commutes with homology by `ShortComplex.mapHomologyIso`, and is a left inverse of
the forgetful functor on sheaves by `sheafificationNatIso`; so the coarse sheafification of the
`i`-th homology presheaf of the section complex is the `i`-th homology of the complex of coarse
sheaves obtained from `I`, which `InjectiveResolution.isoRightDerivedObj` identifies with
`R^i ε_{X,*} ℱ`.

The primed form of the vanishing criterion is the one a consumer who thinks in terms of
cohomology classes wants: its hypothesis speaks of `Stacks.sheafCohomology` and
`Stacks.sheafCohomologyRestriction`, and mentions no resolution. It is deduced from the
unprimed one through `Stacks.Cohomology.Locality.sectionHomologyIso`.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Locality

variable {C : Type u} [Category.{v} C]

/-- The change-of-topology direct image of Stacks 0EZ3 leaves the underlying presheaf of a sheaf
unchanged, so the complex of presheaves underlying the image of an injective resolution `I` of
`ℱ` is the complex of section presheaves of `I`. -/
lemma sheafToPresheaf_mapHomologicalComplex_abelianComparisonPushforward
    (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) (I : InjectiveResolution F) :
    ((sheafToPresheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj
      (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine
        X).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) =
      sectionComplex F I :=
  rfl

/-- **The abelian-sheaf form of Stacks 072W for a change of topology.** The higher direct image
`R^i ε_{X,*} ℱ` is the sheafification, for the coarser localized topology, of the presheaf
`V ↦ H^i(I^•(V))` of `i`-th cohomology of the sections of an injective resolution `I` of `ℱ`. -/
def rightDerivedAbelianComparisonPushforwardIso (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (I : InjectiveResolution F) (i : ℕ) :
    ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightDerived i).obj F ≅
      (presheafToSheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}).obj
        ((sectionComplex F I).homology i) := by
  let T := abelianComparisonPushforward S.fineCoverage S.coarseCoverage S.coarse_le_fine X
  let A := presheafToSheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}
  let K := (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let P := sectionComplex F I
  let ecpx : (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj P ≅ K :=
    ((NatIso.mapHomologicalComplex
        (sheafificationNatIso (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v})
        (ComplexShape.up ℕ)).app K).symm ≪≫
      (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℕ)).app K
  exact I.isoRightDerivedObj T i ≪≫
    (((P.sc i).mapHomologyIso A).symm ≪≫
      (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) i).mapIso ecpx).symm

/-- **The vanishing criterion for a higher change-of-topology direct image**, a consequence of
Stacks 072W. If every section of the `i`-th homology presheaf of the section complex of an
injective resolution of `ℱ` dies after restriction to the members of some covering for the
coarser topology, then `R^i ε_{X,*} ℱ = 0`. This is how the vanishing condition `(V_n)` of
Stacks 0EZ3 is verified. -/
theorem isZero_rightDerived_abelianComparisonPushforward_of_locally_zero
    (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v})
    (I : InjectiveResolution F) (i : ℕ)
    (h : ∀ (U : Over X) (η : ((sectionComplex F I).homology i).obj (op U)),
      ∃ R : (S.coarseCoverage.toGrothendieck.over X).Cover U, ∀ g : R.Arrow,
        ((sectionComplex F I).homology i).map g.f.op η = 0) :
    IsZero (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).rightDerived i).obj F) :=
  (isZero_presheafToSheaf_of_locally_zero (S.coarseCoverage.toGrothendieck.over X) _ h).of_iso
    (rightDerivedAbelianComparisonPushforwardIso S X F I i)

/-- **The vanishing criterion of Stacks 072W, in terms of cohomology classes.** If every
cohomology class of degree `i` over an object of the finer localized site dies after restriction
to the members of some covering for the coarser topology, then `R^i ε_{X,*} ℱ = 0`. No resolution
is mentioned: this is the form in which the vanishing condition `(V_n)` of Stacks 0EZ3 is met. -/
theorem isZero_rightDerived_abelianComparisonPushforward_of_locally_zero'
    (S : CohomologyComparison C) (X : C)
    (F : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) (i : ℕ)
    (h : ∀ (U : Over X)
        (ξ : Stacks.sheafCohomology (S.fineCoverage.toGrothendieck.over X) F U i),
      ∃ R : (S.coarseCoverage.toGrothendieck.over X).Cover U, ∀ g : R.Arrow,
        Stacks.sheafCohomologyRestriction (S.fineCoverage.toGrothendieck.over X) g.f i F ξ = 0) :
    IsZero (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).rightDerived i).obj F) := by
  let J := S.fineCoverage.toGrothendieck.over X
  let I := injectiveResolution F
  refine isZero_rightDerived_abelianComparisonPushforward_of_locally_zero S X F I i fun U η => ?_
  obtain ⟨R, hR⟩ := h U ((sectionHomologyIso J F I i U).inv η)
  refine ⟨R, fun g => ?_⟩
  have hx := sectionHomologyIso_restrict J F I i g.f ((sectionHomologyIso J F I i U).inv η)
  rw [hR g, map_zero, (sectionHomologyIso J F I i U).inv_hom_id_apply] at hx
  exact hx.symm

end Stacks.ComparingTopologies

end
