module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedLowerShriekOfAResolutionFunctoriality
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmall
public import StacksFrontier.Cotangent.ResolutionTorBaseChange
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek is unchanged by a base change of the polynomial site

Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings, let `C_{B/A}` and `C_{B'/A'}` be the sites of polynomial
algebras augmented to `B`, resp. `B'`, of Tag 08PR, and let `u : C_{B/A} ⟶ C_{B'/A'}` be the
base-change functor of Tag 08QN, with `g^{-1}` the induced inverse image on abelian presheaves —
that is, restriction along `u`. If the square induces a quasi-isomorphism `B ⊗_A^L A' = B'` then

`Lπ_!(g^{-1}ℱ') = Lπ'_!(ℱ')`

for every abelian sheaf `ℱ'` on `C_{B'/A'}` (Tag 08QP). Both sites are read at the small model of
their restriction to polynomial algebras on at most `κ` variables.

## Main definitions

* `CommAlgCat.boundedPolynomialBaseChangeAugmentations` and
  `CommAlgCat.boundedPolynomialBaseChange`: the base-change functor of Tag 08QN, restricted to
  the polynomial algebras on at most `κ` variables.
* `CommAlgCat.smallPolynomialBaseChange`: the same functor between the *small models* of the
  restricted sites.

## Main results

* `CommAlgCat.smallPolynomialBaseChangeCompι`: read in the unrestricted sites, the base-change
  functor of the small models is the base-change functor of Tag 08QN.
* `CommAlgCat.isPointResolution_smallPolynomialBaseChange`: the image under base change of the
  cosimplicial object of a resolution is a point resolution, as soon as the base-changed
  augmentation is again a resolution.
* `CommAlgCat.leftDerivedColimitPolynomialBaseChangeNatIso`: the identification for the left
  derived functors of the colimit over the index category, at the small models of the restricted
  sites.
* `CommAlgCat.leftDerivedPointLowerShriekPolynomialBaseChangeNatIso`: the same for the
  sheaf-theoretic `Lπ_!`, read through the sections at the point, assuming that the base-changed
  augmentation is a resolution.
* `CommAlgCat.leftDerivedPointLowerShriekPolynomialBaseChangeNatIsoOfTorIndependent`: the same,
  assuming that the square induces a quasi-isomorphism `B ⊗_A^L A' = B'`.

## References

* [Stacks Project, Tag 08QP](https://stacks.math.columbia.edu/tag/08QP)
* [Stacks Project, Tag 08QN](https://stacks.math.columbia.edu/tag/08QN)
* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommAlgCat

variable {A A' : Type u} [CommRing A] [CommRing A'] [Algebra A A']
  {B : CommAlgCat.{u} A} {B' : CommAlgCat.{u} A'}
  [Algebra A (B' : Type u)] [IsScalarTower A A' (B' : Type u)]
  (b : (B : Type u) →ₐ[A] (B' : Type u)) (κ : Cardinal.{u})

/-! ### Base change on the restricted site and on its small model -/

/-- Extension of scalars as a functor between the categories of polynomial algebras augmented to
`B`, resp. to `B'`, on at most `κ` variables: the restriction of
`CommAlgCat.polynomialBaseChangeAugmentations`. -/
def boundedPolynomialBaseChangeAugmentations :
    BoundedPolynomialAugmentation A B κ ⥤ BoundedPolynomialAugmentation A' B' κ :=
  (IsPolynomialAlgebraOverBelow A' B' κ).lift
    ((IsPolynomialAlgebraOverBelow A B κ).ι ⋙ baseChangeOver b)
    (fun X => isPolynomialAlgebraBelow_baseChange (A' := A') κ X.obj.left X.property)

/-- The base-change functor of sites `C_{B/A} ⟶ C_{B'/A'}`, between the sites restricted to
polynomial algebras on at most `κ` variables. -/
@[stacks 08QN "polynomial-site base change, with the section's footnote in force: the functor \
  between the sites restricted to at most κ variables. The unrestricted version is \
  `CommAlgCat.polynomialBaseChange`"]
def boundedPolynomialBaseChange :
    boundedPolynomialSite A B κ ⥤ boundedPolynomialSite A' B' κ :=
  (boundedPolynomialBaseChangeAugmentations b κ).op

/-- Read in the unrestricted sites, base change on the restricted sites is base change. -/
lemma boundedPolynomialBaseChange_comp_ι :
    boundedPolynomialBaseChange b κ ⋙ boundedPolynomialSiteι A' B' κ =
      boundedPolynomialSiteι A B κ ⋙ polynomialBaseChange b := rfl

/-- The base-change functor between the *small models* of the restricted sites: the composite of
the inclusion of the model of `C_{B/A}`, of base change on the restricted sites, and of a
quasi-inverse of the equivalence between the model of `C_{B'/A'}` and that restricted site. -/
def smallPolynomialBaseChange :
    smallBoundedPolynomialSite A B κ ⥤ smallBoundedPolynomialSite A' B' κ :=
  smallBoundedPolynomialSiteι A B κ ⋙ boundedPolynomialBaseChange b κ ⋙
    (boundedPolynomialSiteEquiv A' B' κ).inverse

/-- Read in the unrestricted sites, the base-change functor of the small models is the
base-change functor `CommAlgCat.polynomialBaseChange`. -/
def smallPolynomialBaseChangeCompι :
    smallPolynomialBaseChange b κ ⋙ smallBoundedPolynomialSiteToPolynomialSite A' B' κ ≅
      smallBoundedPolynomialSiteToPolynomialSite A B κ ⋙ polynomialBaseChange b :=
  Functor.isoWhiskerLeft
    (smallBoundedPolynomialSiteι A B κ ⋙ boundedPolynomialBaseChange b κ)
    (Functor.isoWhiskerRight (boundedPolynomialSiteEquiv A' B' κ).counitIso
      (boundedPolynomialSiteι A' B' κ))

/-! ### The base change of a resolution as a point resolution -/

section Resolution

variable {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B)
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- The cosimplicial object of a base-changed resolution: the image of the cosimplicial object of
`ε` under base change on the small models, read in the unrestricted site `C_{B'/A'}`, is the
cosimplicial object of the base-changed augmentation `A' ⊗_A P_• ⟶ B'`. -/
def smallResolutionCosimplicialObjectBaseChangeι :
    (smallResolutionCosimplicialObject ε κ hPκ ⋙ smallPolynomialBaseChange b κ) ⋙
        smallBoundedPolynomialSiteToPolynomialSite A' B' κ ≅
      resolutionCosimplicialObject (augmentationBaseChange b ε)
        (fun n => isPolynomialAlgebra_simplicialBaseChange b ε
          (fun m => (hPκ m).isPolynomialAlgebra) n) :=
  Functor.isoWhiskerLeft (smallResolutionCosimplicialObject ε κ hPκ)
      (smallPolynomialBaseChangeCompι b κ) ≪≫
    Functor.isoWhiskerRight (smallResolutionCosimplicialObjectι ε κ hPκ)
      (polynomialBaseChange b)

/-- Let `ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms are polynomial algebras on at
most `κ` variables and assume the base change `A' ⊗_A P_• ⟶ B'` is again a resolution of `B'`
over `A'`. Then the image of the cosimplicial object of `ε` under base change is a point
resolution in the small model of the restricted site `C_{B'/A'}`. -/
theorem isPointResolution_smallPolynomialBaseChange
    (hres : IsResolution A' (B' : Type u)
      (simplicialBaseChange b ε) (augmentationBaseChange b ε)) :
    Stacks.ChaoticSite.IsPointResolution
      (smallResolutionCosimplicialObject ε κ hPκ ⋙ smallPolynomialBaseChange b κ) :=
  Stacks.ChaoticSite.isPointResolution_of_fullyFaithful
    (fullyFaithfulSmallBoundedPolynomialSiteToPolynomialSite A' B' κ) _
    (smallResolutionCosimplicialObjectBaseChangeι b κ ε hPκ)
    (exists_homotopyEquivalences_resolutionMor (augmentationBaseChange b ε) _
      hres.trivialKanFibration)

/-- Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings, let `ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms
are polynomial algebras on at most `κ` variables, and assume that the base-changed augmentation
`A' ⊗_A P_• ⟶ B'` is again a resolution of `B'` over `A'`. Then, for every degree `n`,
restriction along the base-change functor of the sites followed by the `n`-th left derived
functor of the colimit over the index category of abelian presheaves on `C_{B/A}` is the `n`-th
left derived functor of the colimit over the index category of abelian presheaves on
`C_{B'/A'}`. Both sites are read at the small model of their restriction to at most `κ`
variables. -/
def leftDerivedColimitPolynomialBaseChangeNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (hres : IsResolution A' (B' : Type u)
      (simplicialBaseChange b ε) (augmentationBaseChange b ε))
    (n : ℕ) :
    Stacks.CategoryHomology.presheafRestriction.{u, u, u} (smallPolynomialBaseChange b κ) ⋙
        (colim : ((smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
          AddCommGrpCat.{u}).leftDerived n ≅
      (colim : ((smallBoundedPolynomialSite A' B' κ)ᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
        AddCommGrpCat.{u}).leftDerived n :=
  Stacks.ChaoticSite.leftDerivedColimitPresheafRestrictionNatIso
    (smallPolynomialBaseChange b κ) (smallResolutionCosimplicialObject ε κ hPκ)
    (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε)
    (isPointResolution_smallPolynomialBaseChange b κ ε hPκ hres) n

/-- Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings, let `C_{B/A}` and `C_{B'/A'}` be the sites of polynomial
algebras augmented to `B`, resp. to `B'`, of Tag 08PR, and let `g` be the morphism of topoi
induced by the base-change functor of Tag 08QN, so that `g^{-1}` is restriction along it. Let
`ε : P_• ⟶ B` be a resolution of `B` over `A` whose terms are polynomial algebras on at most
`κ` variables, and assume that the base-changed augmentation `A' ⊗_A P_• ⟶ B'` is again a
resolution of `B'` over `A'`. Then

`Lπ_!(g^{-1}ℱ') = Lπ'_!(ℱ')`

in every degree `n` and naturally in the abelian sheaf `ℱ'` on `C_{B'/A'}`, read through the
sections at the point. Both sites are read at the small model of their restriction to at most `κ`
variables. -/
@[stacks 08QP "a GENERALIZATION of the lemma: the identification `Lπ_!(g^{-1}ℱ') = Lπ'_!(ℱ')` \
  under the weaker hypothesis that the base change `A' ⊗_A P_• ⟶ B'` of the chosen resolution is \
  again a resolution, which is what the source's proof derives from `B ⊗_A^L A' = B'`. The \
  source's own statement is \
  `CommAlgCat.leftDerivedPointLowerShriekPolynomialBaseChangeNatIsoOfTorIndependent`, proved \
  from this one. Both are read at the small model of the footnote-restricted site `C_{B/A}` and \
  through the sections at the point"]
def leftDerivedPointLowerShriekPolynomialBaseChangeNatIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A))))
    (hres : IsResolution A' (B' : Type u)
      (simplicialBaseChange b ε) (augmentationBaseChange b ε))
    (n : ℕ) :
    (smallPolynomialBaseChange b κ).sheafPushforwardContinuous AddCommGrpCat.{u}
          (GrothendieckTopology.trivial (smallBoundedPolynomialSite A B κ))
          (GrothendieckTopology.trivial (smallBoundedPolynomialSite A' B' κ)) ⋙
        (Stacks.ChaoticSite.abelianPointLowerShriek
            (smallBoundedPolynomialSite A B κ)).leftDerived n ⋙
          Stacks.ChaoticSite.pointSections AddCommGrpCat.{u} ≅
      (Stacks.ChaoticSite.abelianPointLowerShriek
          (smallBoundedPolynomialSite A' B' κ)).leftDerived n ⋙
        Stacks.ChaoticSite.pointSections AddCommGrpCat.{u} :=
  Stacks.ChaoticSite.leftDerivedPointLowerShriekPresheafRestrictionNatIso
    (smallPolynomialBaseChange b κ) (smallResolutionCosimplicialObject ε κ hPκ)
    (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε)
    (isPointResolution_smallPolynomialBaseChange b κ ε hPκ hres) n

/-- Let
```
A  --→  A'
|       |
B  --→  B'
```
be a commutative square of rings which induces a quasi-isomorphism `B ⊗_A^L A' = B'` — that is,
`Tor_i^A(A', B) = 0` for `i > 0` and the canonical map `A' ⊗_A B → B'` is bijective. Let
`C_{B/A}` and `C_{B'/A'}` be the sites of polynomial algebras augmented to `B`, resp. to `B'`, of
Tag 08PR, and let `g` be the morphism of topoi induced by the base-change functor of Tag 08QN, so
that `g^{-1}` is restriction along it. Then

`Lπ_!(g^{-1}ℱ') = Lπ'_!(ℱ')`

in every degree `n` and naturally in the abelian sheaf `ℱ'` on `C_{B'/A'}`, read through the
sections at the point. Both sites are read at the small model of their restriction to at most `κ`
variables, for any `κ` bounding the variables of a chosen resolution `ε : P_• ⟶ B` of `B` over
`A`. -/
@[stacks 08QP "the lemma as stated: the identification `Lπ_!(g^{-1}ℱ') = Lπ'_!(ℱ')` from the \
  source's own hypothesis that the square induce a quasi-isomorphism `B ⊗_A^L A' = B'`, written \
  out as vanishing of the positive `Tor_i^A(A', B)` together with bijectivity of \
  `A' ⊗_A B → B'`. Read at the small model of the footnote-restricted site `C_{B/A}` and through \
  the sections at the point; the generalization assuming only that the base-changed \
  augmentation is a resolution is \
  `CommAlgCat.leftDerivedPointLowerShriekPolynomialBaseChangeNatIso`"]
def leftDerivedPointLowerShriekPolynomialBaseChangeNatIsoOfTorIndependent
    (hres : IsResolution A (B : Type u) P ε)
    (hTor : RingTheory.TorIndependence.TorIndependent A A' (B : Type u))
    (hφ : Function.Bijective (baseChangeUnit b))
    (n : ℕ) :
    (smallPolynomialBaseChange b κ).sheafPushforwardContinuous AddCommGrpCat.{u}
          (GrothendieckTopology.trivial (smallBoundedPolynomialSite A B κ))
          (GrothendieckTopology.trivial (smallBoundedPolynomialSite A' B' κ)) ⋙
        (Stacks.ChaoticSite.abelianPointLowerShriek
            (smallBoundedPolynomialSite A B κ)).leftDerived n ⋙
          Stacks.ChaoticSite.pointSections AddCommGrpCat.{u} ≅
      (Stacks.ChaoticSite.abelianPointLowerShriek
          (smallBoundedPolynomialSite A' B' κ)).leftDerived n ⋙
        Stacks.ChaoticSite.pointSections AddCommGrpCat.{u} :=
  leftDerivedPointLowerShriekPolynomialBaseChangeNatIso b κ ε hPκ hres.trivialKanFibration
    (isResolution_augmentationBaseChange b ε hres hTor hφ) n

end Resolution

end CommAlgCat

end
