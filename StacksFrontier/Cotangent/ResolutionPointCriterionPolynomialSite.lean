module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitByPointResolutionLargeSite
public import StacksFrontier.Cotangent.ResolutionPointCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# Tag 08PS at the site `C_{B/A}` itself: `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)` and in `D(B)`

Let `A → B` be a ring map, let `C_{B/A}` be the site of polynomial `A`-algebras augmented to `B`
of Tag 08PR -- `CommAlgCat.polynomialSite` -- and let `ε : P_• ⟶ B` be a simplicial `A`-algebra
with an augmentation to `B` such that every `P_n` is a polynomial algebra over `A` and `ε` is a
trivial Kan fibration on underlying simplicial sets. Tag 08PS asserts

`Lπ_!(ℱ) = ℱ(P_•, ε)`

in `D(Ab)`, resp. `D(B)`, functorially in `ℱ` in `Ab(C_{B/A})`, resp. `Mod(B̲)`. This file proves
both halves, **at `CommAlgCat.polynomialSite` itself**.

What was previously available was the same pair of statements read at the small model of the
footnote-restricted site, `CommAlgCat.smallResolutionDerivedColimitNatIso` and
`CommAlgCat.smallResolutionModuleDerivedColimitNatIso`. Those are statements about different
coefficients: the footnote cuts `C_{B/A}` down to the full subcategory of the augmentations whose
set of variables has cardinality at most a fixed bound, and both `Ab(-)` and `Lπ_!` change when
one passes to a full subcategory. The obstruction to stating the tag at `C_{B/A}` was not
mathematical but a size mismatch -- the criterion of Tag 08Q9 was available only for a small site,
while the objects of `C_{B/A}` live in `Type (u + 1)` and its morphisms in `Type u` -- and it is
removed by
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge`, the criterion with no
smallness hypothesis.

## Main results

* `CommAlgCat.polynomialSiteResolutionDerivedColimitNatIso`: **Tag 08PS in `D(Ab)`** -- the
  extended Moore complex of `ℱ(P_•, ε)` is `Lπ_!(ℱ)` in `D(Ab)`, as an isomorphism of functors of
  the abelian sheaf `ℱ` on `C_{B/A}`.
* `CommAlgCat.polynomialSiteResolutionModuleDerivedColimitNatIso`: **Tag 08PS in `D(B)`** -- the
  same for a sheaf of `B`-modules `ℱ`, in `D(B)`.

## Implementation notes

**Where the mathematics is.** Nothing is reproved here. The hypothesis the criterion of Tag 08Q9
asks of the cosimplicial object of the resolution is proved at `CommAlgCat.polynomialSite`, for
every object of the site, by `CommAlgCat.exists_homotopyEquivalences_resolutionMor`: that is the
content of the source's proof, the decomposition of `Mor_C((P_•, ε), (Q, β))` into the fibres of
`ε` and the stability of trivial Kan fibrations under base change and products. It is literally
`Stacks.ChaoticSite.IsPointResolution` of that cosimplicial object, the condition mentioning only
the simplicial sets of morphisms and so being available at a site of any size. The criterion is
then applied in the form that carries no smallness hypothesis.

**The coefficient universe.** `Ab(C_{B/A})` is read at `AddCommGrpCat.{u + 1}`: the objects of
the site live in `Type (u + 1)`, so that is the smallest universe in which the index category of
a presheaf has colimits of abelian groups, and it is the universe at which
`CommAlgCat.polynomialAbelianLowerShriekEvaluationIso` names `π_!` for this site. Correspondingly
`Mod(B̲)` is read at `ModuleCat.{u + 1} (ULift.{u + 1} B)`; the universe lift of the coefficient
ring is not a choice made here but the one the site's own ringed point makes, the ring of
`CommAlgCat.polynomialRingedPoint` being `CommRingCat.of (ULift.{u + 1} B)`.

**`Lπ_!` is the total left derived colimit.** On a chaotic site `π_!` is the colimit over the
index category (Tag 08PF, `Stacks.ChaoticSite.lowerShriek_pointSections_colimitIso`), and `Lπ_!`
below is `Stacks.CategoryHomology.totalDerivedColimit'`, the total left derived functor of that
colimit, as in `CommAlgCat.smallResolutionDerivedColimitNatIso`.

**Enough projectives.** The criterion asks that the category of coefficients have enough
projectives. For a small site that is an instance; here it is supplied by
`Stacks.CategoryHomology.diagramsEnoughProjectives'`, from the coproducts of the free diagrams on
the objects of the site, which exist because the coefficient universe `u + 1` is at least that of
the objects and of the morphisms.

## References

* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryHomology

universe u

namespace CommAlgCat

attribute [local instance] HasDerivedCategory.standard

/-! ### Enough projectives on the site `C_{B/A}` -/

section Projectives

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- **Abelian presheaves on the site `C_{B/A}` have enough projectives**, at the coefficient
universe `u + 1`. The site is not small -- its objects live in `Type (u + 1)` and its morphisms in
`Type u` -- so `Stacks.CategoryHomology.presheafEnoughProjectives` does not apply; the free
diagrams on the objects still exist at `u + 1`, which is what
`Stacks.CategoryHomology.diagramsEnoughProjectives'` needs. -/
instance enoughProjectives_polynomialSitePresheaf :
    EnoughProjectives ((polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
  diagramsEnoughProjectives' _ _

/-- **Diagrams of `R`-modules on the site `C_{B/A}` have enough projectives**, at the coefficient
universe `u + 1`, for a ring `R` in that universe. -/
instance enoughProjectives_polynomialSiteModules (R : Type (u + 1)) [Ring R] :
    EnoughProjectives ((polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} R) := by
  have hpr (a b : (polynomialSite A B)ᵒᵖ) : HasProductsOfShape (a ⟶ b) (ModuleCat.{u + 1} R) := by
    change HasLimitsOfShape (Discrete (a ⟶ b)) (ModuleCat.{u + 1} R)
    have : Small.{u + 1} (Discrete (a ⟶ b)) := inferInstance
    exact ModuleCat.hasLimitsOfShape
  exact diagramsEnoughProjectives' _ _

/-- Countable filtered colimits of `ULift.{u + 1} B`-modules in `Type (u + 1)` are exact. This is
`Stacks.CategoryHomology.hasExactColimitsOfShapeNatModuleCat` with its universes pinned: that
instance is stated at `ModuleCat.{max u' w} R` for a ring `R : Type w`, and with `w = u + 1` the
constraint `max u' (u + 1) = u + 1` leaves `u'` undetermined, so instance search reports a stuck
universe constraint rather than finding it. -/
instance hasExactColimitsOfShapeNat_polynomialPointModules :
    HasExactColimitsOfShape ℕ (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
  hasExactColimitsOfShapeNatModuleCat.{u + 1, u + 1} _

end Projectives

/-! ### Tag 08PS at the site `C_{B/A}` -/

section Resolution

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))

/-- **The cosimplicial object of a resolution is a point resolution of the site `C_{B/A}`.**
Let `ε : P_• ⟶ B` be a simplicial `A`-algebra with an augmentation to `B` whose terms are
polynomial algebras over `A` and whose augmentation is a trivial Kan fibration on underlying
simplicial sets. Then every simplicial set `Mor_{C_{B/A}}((P_•, ε), W)` is homotopy equivalent to
a singleton, which is the hypothesis of the criterion of Tag 08Q9.

This is `CommAlgCat.exists_homotopyEquivalences_resolutionMor` read as
`Stacks.ChaoticSite.IsPointResolution`: the two statements are the same, the condition mentioning
only the simplicial sets of morphisms of the site and so being stated for a category whose objects
and morphisms live in unrelated universes. -/
theorem isPointResolution_resolutionCosimplicialObject
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    Stacks.ChaoticSite.IsPointResolution (resolutionCosimplicialObject ε hP) :=
  exists_homotopyEquivalences_resolutionMor ε hP hε

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)`, functorially in `ℱ`, at the site `C_{B/A}`.**
Let `ε : P_• ⟶ B` be a simplicial `A`-algebra endowed with an augmentation to `B`, assume every
`P_n` is a polynomial algebra over `A` and that `ε` is a trivial Kan fibration on underlying
simplicial sets. Then the extended Moore complex of the simplicial abelian group `ℱ(P_•, ε)` is
`Lπ_!(ℱ)` in `D(Ab)`, as an **isomorphism of functors** of the abelian sheaf `ℱ` on the site
`C_{B/A}` of Tag 08PR -- the abelian presheaves being its abelian sheaves, the topology being
chaotic.

This is the abelian half of the conclusion of Tag 08PS. The hypothesis of the criterion of
Tag 08Q9 is `CommAlgCat.isPointResolution_resolutionCosimplicialObject`, and
`Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge` is that criterion in
its derived form, natural in the coefficient presheaf and with no smallness hypothesis on the
site. -/
@[stacks 08PS "the conclusion `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(Ab)` functorially in `ℱ` in \
  `Ab(C_{B/A})`, at `CommAlgCat.polynomialSite` -- the site of Tag 08PR itself, not a restriction \
  of it -- as an isomorphism in the derived category, with `π_!` in its colimit presentation of \
  Tag 08PF and the coefficients at the universe `u + 1` of the site's objects"]
def polynomialSiteResolutionDerivedColimitNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
          (resolutionCosimplicialObject ε hP) AddCommGrpCat.{u + 1} ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single ((polynomialSite A B)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
          (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙
          totalDerivedColimit' (polynomialSite A B) AddCommGrpCat.{u + 1} :=
  Stacks.ChaoticSite.AbelianValued.mooreCochainNatIsoDerivedColimitOfLarge _
    (isPointResolution_resolutionCosimplicialObject ε hP hε)

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)`, functorially in `ℱ`, at the site `C_{B/A}`.**
Under the hypotheses of Tag 08PS, the extended Moore complex of the simplicial `B`-module
`ℱ(P_•, ε)` is `Lπ_!(ℱ)` in `D(B)`, as an **isomorphism of functors** of the sheaf of `B`-modules
`ℱ` on the site `C_{B/A}` of Tag 08PR -- the diagrams of `B`-modules on the site being its
`B̲`-modules, the topology being chaotic.

This is the module half of the conclusion of Tag 08PS, beside the abelian half
`CommAlgCat.polynomialSiteResolutionDerivedColimitNatIso`: the same hypothesis
`CommAlgCat.isPointResolution_resolutionCosimplicialObject` -- which does not mention the
coefficients -- is fed to
`Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimitOfLarge`. The coefficient ring is
`ULift.{u + 1} B`, the ring of the site's ringed point
`CommAlgCat.polynomialRingedPoint`. -/
@[stacks 08PS "the conclusion `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)` functorially in `ℱ` in `Mod(B̲)`, \
  at `CommAlgCat.polynomialSite` -- the site of Tag 08PR itself, not a restriction of it -- as an \
  isomorphism in the derived category, with the coefficient ring read as `ULift.{u+1} B` exactly \
  as the site's own ringed point `CommAlgCat.polynomialRingedPoint` reads it"]
def polynomialSiteResolutionModuleDerivedColimitNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    Stacks.ChaoticSite.GeneralValued.mooreCochainComplex'
          (resolutionCosimplicialObject ε hP)
          (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) ⋙ DerivedCategory.Q ≅
      HomologicalComplex.single
          ((polynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u)))
          (ComplexShape.up ℤ) 0 ⋙
        DerivedCategory.Q ⋙
          totalDerivedColimit' (polynomialSite A B)
            (ModuleCat.{u + 1} (ULift.{u + 1} (B : Type u))) :=
  Stacks.ChaoticSite.ModuleValued.mooreCochainNatIsoDerivedColimitOfLarge _
    (isPointResolution_resolutionCosimplicialObject ε hP hε)

end Resolution

end CommAlgCat

end
