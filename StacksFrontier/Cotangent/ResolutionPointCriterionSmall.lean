module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfAResolution
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.PointResolutionTransfer
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteSmall
public import StacksFrontier.Cotangent.ResolutionPointCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# The criterion of Tag 08Q9 applied to the restricted polynomial site

Let `A → B` be a ring map and let `ε : P_• ⟶ B` be a resolution of `B` over `A` in the sense of
Tag 08QI. Tag 08PS proves that each simplicial set `Mor_{C_{B/A}}((P_•, ε), W)` is homotopy
equivalent to a singleton; that is the hypothesis of the criterion of Tag 08Q9, which then
computes `L_nπ_!` as the homology of the Moore complex of `ℱ(P_•, ε)`. The criterion asks for a
*small* site, and `CommAlgCat.polynomialSite` — the site with the source's footnote omitted — is
not even essentially small. This file supplies the missing step: the resolution is a cosimplicial
object of the footnote-restricted site of `StacksFrontier/Cotangent/PolynomialAlgebraSiteSmall.lean`
as soon as its terms have boundedly many variables, that site has a genuinely small model, the
homotopy equivalences of Tag 08PS transfer to the model, and the criterion of Tag 08Q9 applies
there.

## Main definitions

* `CommAlgCat.boundedResolutionAugmentation` and
  `CommAlgCat.boundedResolutionCosimplicialObject`: a resolution whose terms are polynomial
  algebras on at most `κ` variables, read as a simplicial object of
  `CommAlgCat.BoundedPolynomialAugmentation` and then as a cosimplicial object of
  `CommAlgCat.boundedPolynomialSite`.
* `CommAlgCat.smallResolutionCosimplicialObject`: the same, transported to the small model
  `CommAlgCat.smallBoundedPolynomialSite`.
* `CommAlgCat.standardResolutionVarCardinal`: the cardinal bounding the variables of every term
  of the standard resolution of `B` over `A`, namely the cardinality of the disjoint union of the
  iterates of the polynomial-algebra comonad at `B`.

## Main results

* `CommAlgCat.isPointResolution_smallResolutionCosimplicialObject`: **the hypothesis of the
  criterion of Tag 08Q9 holds for the small model.** This is Tag 08PS's conclusion transported
  along the fully faithful inclusion of the small model into `CommAlgCat.polynomialSite`.
* `CommAlgCat.smallResolutionLeftDerivedColimitNatIso`: **the criterion of Tag 08Q9 at the
  restricted site**: the left derived functors of the colimit over the small model are the
  homology of the Moore complex of `ℱ(P_•, ε)`, naturally in `ℱ`.
* `CommAlgCat.standardResolution_isPolynomialAlgebraBelow`: every term of the standard resolution
  of `B` over `A` is a polynomial algebra on at most
  `CommAlgCat.standardResolutionVarCardinal A B` variables.
* `CommAlgCat.standardResolutionLeftDerivedColimitNatIso`: the same conclusion for the standard
  resolution.
* `CommAlgCat.smallResolutionLeftDerivedLowerShriekNatIso` and
  `CommAlgCat.standardResolutionLeftDerivedLowerShriekNatIso`: **the source's conclusion
  `Lπ_!(ℱ) = ℱ(P_•, ε)`**, read at the small model of the restricted site: the sections at the
  point of `L_nπ_!(ℱ)` are the homology of the Moore complex of `ℱ(P_•, ε)`, naturally in `ℱ`.

## Implementation notes

**What this does and does not close.** The source's conclusion at Tag 08PS and Tag 08PT is
`Lπ_!(ℱ) = ℱ(P_•, ε)` for the morphism of ringed topoi `π` of Tag 08PR. The derived functors of
the criterion of Tag 08Q9 are those of `colim` over the index category of presheaves, and `π_!`
*is* that colimit — undierived — by Tag 08PF. Identifying the two *derived* functors is
`Stacks.ChaoticSite.leftDerivedPointLowerShriekNatIso`, which transports
`CategoryTheory.Functor.leftDerived` along the equivalence relating sheaves for the chaotic
topology to presheaves and along the equivalence relating sheaves on the point to abelian
groups; the transports themselves are in
`StacksFrontier/CategoryTheory/Abelian/LeftDerivedTransport.lean`. The two declarations named last
above are therefore the source's conclusion, for the point morphism of the small model of the
footnote-restricted site. The site of Tag 08PR itself carries no such statement: it is large,
so Tag 08Q9 does not apply to it, which is the whole reason for the small model; and the `π_!`
named for it in `StacksFrontier/Cotangent/PolynomialAlgebraSiteShriek.lean` is formed at a
coefficient universe at least `u + 1`, whereas the criterion of Tag 08Q9 is stated for a small
site with coefficients in the site's own universe.

**The cardinal bound is a hypothesis, not `#B`.** The source's footnote restricts the sets of
variables to cardinality at most `#B`. That bound does not contain the standard resolution: the
degree `n + 1` term of the standard resolution is a polynomial algebra over `A` on the underlying
set of the degree `n` term, so while `P_0 = A[B]` has exactly `#B` variables, `P_1 = A[A[B]]` has
`#(A[B]) = max ℵ₀ #A #B` of them (`MvPolynomial.cardinalMk_eq_max`), which exceeds `#B` whenever
`B` is finite or smaller than `A`. The bound is therefore
left as a parameter `κ`, and `CommAlgCat.standardResolutionVarCardinal` supplies a correct one
for the standard resolution with no cardinal arithmetic at all: the disjoint union over `n` of
the index types of the terms is itself a `Type u`, and each index type injects into it.

**Choice.** The quasi-inverse of `CommAlgCat.boundedPolynomialSiteEquiv` is built from essential
surjectivity, so `CommAlgCat.smallResolutionCosimplicialObject` depends on `Classical.choice`.
This is unavoidable in substance: the small model's objects are polynomial algebras on subsets of
a fixed representative of `κ`, and replacing a term of the resolution by one of those requires
choosing an embedding of its variables. Only the construction uses the choice; every statement
below is about the chosen model and is insensitive to which quasi-inverse is used, the criterion
of Tag 08Q9 being invariant under isomorphism of cosimplicial objects.

## References

* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace CommAlgCat

/-! ### A bounded resolution as a cosimplicial object of the small model -/

section Bounded

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B) (κ : Cardinal.{u})
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- The augmentation `ε : P_• ⟶ B` of a simplicial `A`-algebra whose terms are polynomial algebras
on at most `κ` variables, read as a simplicial object of the restricted category of polynomial
augmentations. -/
def boundedResolutionAugmentation : SimplicialObject (BoundedPolynomialAugmentation A B κ) :=
  (IsPolynomialAlgebraOverBelow A B κ).lift (resolutionOver ε) hPκ

/-- The same, read as a cosimplicial object of the restricted site `C_{B/A}`. -/
def boundedResolutionCosimplicialObject : CosimplicialObject (boundedPolynomialSite A B κ) :=
  (boundedResolutionAugmentation ε κ hPκ).rightOp

/-- Read in the unrestricted site `CommAlgCat.polynomialSite`, the cosimplicial object of a
bounded resolution is the cosimplicial object of that resolution: the restriction only cuts down
the ambient category. -/
def boundedResolutionCosimplicialObjectι :
    boundedResolutionCosimplicialObject ε κ hPκ ⋙ boundedPolynomialSiteι A B κ ≅
      resolutionCosimplicialObject ε fun n => (hPκ n).isPolynomialAlgebra :=
  Iso.refl _

/-- The cosimplicial object of a bounded resolution, transported to the genuinely small model of
the restricted site. -/
def smallResolutionCosimplicialObject :
    CosimplicialObject (smallBoundedPolynomialSite A B κ) :=
  boundedResolutionCosimplicialObject ε κ hPκ ⋙ (boundedPolynomialSiteEquiv A B κ).inverse

/-- Read in the unrestricted site, the cosimplicial object of the small model is the cosimplicial
object of the resolution. -/
def smallResolutionCosimplicialObjectι :
    smallResolutionCosimplicialObject ε κ hPκ ⋙
        smallBoundedPolynomialSiteToPolynomialSite A B κ ≅
      resolutionCosimplicialObject ε fun n => (hPκ n).isPolynomialAlgebra :=
  Functor.isoWhiskerLeft (boundedResolutionCosimplicialObject ε κ hPκ)
      (Functor.isoWhiskerRight (boundedPolynomialSiteEquiv A B κ).counitIso
        (boundedPolynomialSiteι A B κ)) ≪≫
    boundedResolutionCosimplicialObjectι ε κ hPκ

/-- **The hypothesis of the criterion of Tag 08Q9, for the small model of the restricted site.**
Let `ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms are polynomial algebras on at most
`κ` variables. Then its cosimplicial object in the small model of the restricted site `C_{B/A}`
is a point resolution: every simplicial set of morphisms from it into an object of the model is
homotopy equivalent to a singleton.

This is Tag 08PS read in the small model. Nothing is reproved: the homotopy equivalences are
those of `CommAlgCat.exists_homotopyEquivalences_resolutionMor`, supplied in the unrestricted
site, and they descend because the model embeds fully faithfully in it. -/
theorem isPointResolution_smallResolutionCosimplicialObject
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    Stacks.ChaoticSite.IsPointResolution (smallResolutionCosimplicialObject ε κ hPκ) :=
  Stacks.ChaoticSite.isPointResolution_of_fullyFaithful
    (fullyFaithfulSmallBoundedPolynomialSiteToPolynomialSite A B κ) _
    (smallResolutionCosimplicialObjectι ε κ hPκ)
    (exists_homotopyEquivalences_resolutionMor ε (fun n => (hPκ n).isPolynomialAlgebra) hε)

/-- **The criterion of Tag 08Q9 at the restricted site `C_{B/A}`.** Let `ε : P_• ⟶ B` be a
resolution of `B` over `A` whose terms are polynomial algebras on at most `κ` variables. For
every abelian presheaf `ℱ` on the small model of the restricted site, the left derived functors
of the colimit over the index category are the homology of the Moore complex of `ℱ(P_•, ε)`,
naturally in `ℱ`.

This is `Stacks.ChaoticSite.leftDerivedColimitNatIso` — Tag 08Q9 — at a site that really is
small. See the first implementation note for what separates it from the conclusion of
Tag 08PS. -/
def smallResolutionLeftDerivedColimitNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (n : ℕ) :
    (colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        AddCommGrpCat.{u}).leftDerived n ≅
      Stacks.ChaoticSite.cosimplicialMooreComplex (smallResolutionCosimplicialObject ε κ hPκ) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  Stacks.ChaoticSite.leftDerivedColimitNatIso _
    (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε) n

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` for a resolution, at the small model of the restricted site
`C_{B/A}`.** Let `ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms are polynomial
algebras on at most `κ` variables. For every abelian sheaf `ℱ` on the small model of the
restricted site, the sections at the point of `L_nπ_!(ℱ)` are the degree `n` homology of the
Moore complex of `ℱ(P_•, ε)`, naturally in `ℱ`; here `π` is the point morphism of the small
model, whose `π_!` is the lower shriek of Tag 08PR formed for that site.

This is the conclusion of Tag 08PS at the small model: the criterion of Tag 08Q9 applies by
`CommAlgCat.isPointResolution_smallResolutionCosimplicialObject`, and
`Stacks.ChaoticSite.leftDerivedPointLowerShriekNatIso` carries it from the left derived functors
of `colim` to those of `π_!`. -/
def smallResolutionLeftDerivedLowerShriekNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (n : ℕ) :
    (Stacks.ChaoticSite.abelianPointLowerShriek
          (smallBoundedPolynomialSite A B κ)).leftDerived n ⋙
        Stacks.ChaoticSite.pointSections AddCommGrpCat.{u} ≅
      sheafToPresheaf
          (GrothendieckTopology.trivial (smallBoundedPolynomialSite A B κ))
          AddCommGrpCat.{u} ⋙
        Stacks.ChaoticSite.cosimplicialMooreComplex
            (smallResolutionCosimplicialObject ε κ hPκ) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  Stacks.ChaoticSite.leftDerivedPointLowerShriekNatIso _ _
    (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε) n

end Bounded

/-! ### The standard resolution -/

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- A cardinal bounding the variables of every term of the standard resolution of `B` over `A`:
the cardinality of the disjoint union, over the degree `n`, of the underlying set of the `n`-th
iterate of the polynomial-algebra comonad at `B`, which is the index type of the degree `n` term.
That disjoint union is a `Type u`, so no cardinal arithmetic is needed to bound the terms by
it. -/
abbrev standardResolutionVarCardinal : Cardinal.{u} :=
  Cardinal.mk (Σ m : ℕ, (((polynomialComonad.{u, u} A).toFunctor.iterate m).obj B : Type u))

/-- Every term of the standard resolution of `B` over `A` is a polynomial algebra over `A` on at
most `CommAlgCat.standardResolutionVarCardinal A B` variables: the degree `n` term is the
polynomial algebra on the `n`-th iterate of the comonad, which injects into the disjoint union of
all the iterates. -/
theorem standardResolution_isPolynomialAlgebraBelow (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebraBelow A (standardResolutionVarCardinal A B)
      ((standardResolution.{u, u} A B).left.obj n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = op ⦋m⦌ := ⟨n.unop.len, by rw [SimplexCategory.mk_len]⟩
  refine ⟨(((polynomialComonad.{u, u} A).toFunctor.iterate m).obj B : Type u), ?_, ?_⟩
  · exact Cardinal.mk_le_of_injective (f := fun x => (⟨m, x⟩ :
      Σ k : ℕ, (((polynomialComonad.{u, u} A).toFunctor.iterate k).obj B : Type u)))
      fun _ _ h => by simpa using h
  · rw [standardResolution_obj_mvPolynomial]
    exact ⟨AlgEquiv.refl⟩

/-- **The criterion of Tag 08Q9 for the standard resolution, at the restricted site `C_{B/A}`.**
For every abelian presheaf `ℱ` on the small model of the site restricted to polynomial algebras
on at most `CommAlgCat.standardResolutionVarCardinal A B` variables, the left derived functors of
the colimit over the index category are the homology of the Moore complex of `ℱ(P_•, ε)` for
`P_•` the standard resolution of `B` over `A`, naturally in `ℱ`.

This is Tag 08PT's missing step: the two hypotheses of Tag 08PS hold for the standard resolution
by Tag 08QI, its terms are boundedly many variables wide, and the criterion of Tag 08Q9 applies
to the small model. See the first implementation note for what separates it from the conclusion
of Tag 08PT. -/
def standardResolutionLeftDerivedColimitNatIso (n : ℕ) :
    (colim : ((smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B))ᵒᵖ ⥤
        AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived n ≅
      Stacks.ChaoticSite.cosimplicialMooreComplex
          (smallResolutionCosimplicialObject (standardResolution.{u, u} A B).hom
            (standardResolutionVarCardinal A B)
            (standardResolution_isPolynomialAlgebraBelow A B)) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  smallResolutionLeftDerivedColimitNatIso (standardResolution.{u, u} A B).hom
    (standardResolutionVarCardinal A B) (standardResolution_isPolynomialAlgebraBelow A B)
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration n

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` for the standard resolution, at the small model of the restricted
site `C_{B/A}`.** For every abelian sheaf `ℱ` on the small model of the site restricted to
polynomial algebras on at most `CommAlgCat.standardResolutionVarCardinal A B` variables, the
sections at the point of `L_nπ_!(ℱ)` are the degree `n` homology of the Moore complex of
`ℱ(P_•, ε)` for `P_•` the standard resolution of `B` over `A`, naturally in `ℱ`.

This is the conclusion of Tag 08PT at the small model: the two hypotheses of Tag 08PS hold for
the standard resolution by Tag 08QI, its terms are boundedly many variables wide, and
`CommAlgCat.smallResolutionLeftDerivedLowerShriekNatIso` applies. -/
def standardResolutionLeftDerivedLowerShriekNatIso (n : ℕ) :
    (Stacks.ChaoticSite.abelianPointLowerShriek
          (smallBoundedPolynomialSite A B
            (standardResolutionVarCardinal A B))).leftDerived n ⋙
        Stacks.ChaoticSite.pointSections AddCommGrpCat.{u} ≅
      sheafToPresheaf
          (GrothendieckTopology.trivial
            (smallBoundedPolynomialSite A B (standardResolutionVarCardinal A B)))
          AddCommGrpCat.{u} ⋙
        Stacks.ChaoticSite.cosimplicialMooreComplex
            (smallResolutionCosimplicialObject (standardResolution.{u, u} A B).hom
              (standardResolutionVarCardinal A B)
              (standardResolution_isPolynomialAlgebraBelow A B)) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n :=
  smallResolutionLeftDerivedLowerShriekNatIso (standardResolution.{u, u} A B).hom
    (standardResolutionVarCardinal A B) (standardResolution_isPolynomialAlgebraBelow A B)
    (standardResolution_isResolution.{u, u} A B).trivialKanFibration n

end CommAlgCat

end
