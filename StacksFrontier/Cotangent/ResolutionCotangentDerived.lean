module

public import StacksFrontier.Cotangent.PolynomialAlgebraSiteBaseChangeDifferentials
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteModuleShriekDerived
import StacksCore.Tactic.StacksAttribute

/-!
# Any resolution computes the cotangent complex, in the derived category

Let `A → B` be a ring map, let `π` and `i` be as in [Stacks, Tag 08PR] and let `𝒪` be the
structure sheaf of the site `C_{B/A}` of polynomial `A`-algebras augmented to `B`. [Stacks, Tag
08PU] identifies `Lπ_!(i^*Ω_{𝒪/A})` with the cotangent complex `L_{B/A}` of [Stacks, Tag 08PN],
computed from the *standard* resolution;
`StacksFrontier/Cotangent/PolynomialAlgebraSiteModuleShriekDerived.lean` carries that identification
as an isomorphism in `D(B)`.

The right-hand side `Lπ_!(i^*Ω_{𝒪/A})` does not mention a resolution. So the same computation,
run at a different resolution, identifies the complex of *that* resolution with the same object
of `D(B)`; this is the principle of [Stacks, Remark 08QI] that any resolution computes `L_{B/A}`.
This file states that principle: for every resolution `ε : P_• ⟶ B` of [Stacks, Tag 08QI] whose
terms are polynomial algebras on at most `κ` variables,

`Q(Ω[P_•⁄A] ⊗_{P_•} B) ≅ Lπ_!(i^*Ω_{𝒪/A})` in `D(B)`,

and in particular any two such resolutions, read at one cardinal bound `κ`, give isomorphic
objects of `D(B)`.

## Main results

* `CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso`: **[Stacks, Tag 08PU] in `D(B)` for
  an arbitrary bounded resolution**: the extended Moore complex of `Ω[P_•⁄A] ⊗_{P_•} B` is
  `Lπ_!(i^*Ω_{𝒪/A})`.
* `CommAlgCat.standardResolutionCotangentDerivedLowerShriekIsoOfLE`: the same at the standard
  resolution and an arbitrary cardinal bound `κ` large enough to contain it, which identifies the
  right-hand side with `Q(L_{B/A})`.

## Implementation notes

`CommAlgCat.standardResolutionCotangentDerivedLowerShriekIso` is the special case of
`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso` at the standard resolution and at
`κ = CommAlgCat.standardResolutionVarCardinal A B`. It is not restated in that form here: the
cardinal bound has to be left free for two resolutions to be compared, since a resolution coming
from elsewhere — the standard resolution of `B` over an intermediate ring, say — has no reason to
be contained in the bound that the standard resolution over `A` needs.

Like the comparison it rests on, the isomorphism is produced for the one sheaf `i^*Ω_{𝒪/A}` and
is not asserted to be natural in the coefficient sheaf; a projective resolution of the latter is
chosen to produce it.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PT](https://stacks.math.columbia.edu/tag/08PT)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.ChaoticSite.ModuleValued

universe u

namespace CommAlgCat

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B) (κ : Cardinal.{u})
  (hPκ : ∀ n, IsPolynomialAlgebraBelow A κ (P.obj n))

/-- **The extended Moore complex of `(i^*Ω_{𝒪/A})(P_•, ε)` is the complex of
`Ω[P_•⁄A] ⊗_{P_•} B`.** Both are the alternating face map complex of the simplicial `B`-module of
base-changed differentials of `P_•`, reindexed into cohomological degrees `≤ 0`; the
identification of the simplicial modules is
`CommAlgCat.smallResolutionCotangentModuleIso`. -/
def smallResolutionCotangentMooreCochainIso :
    (mooreCochainComplex (smallResolutionCosimplicialObject ε κ hPκ)).obj
        (smallPolynomialCotangentModulePresheaf A B κ) ≅
      ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
          (resolutionOver ε ⋙ overDifferentialsFunctor)).extend
        (ComplexShape.embeddingUpIntLE (0 : ℤ)) :=
  ((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
    (ModuleCat.{u} (B : Type u))).mapIso
      ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).mapIso
        (smallResolutionCotangentModuleIso ε κ hPκ))

/-- **[Stacks, Tag 08PU] in `D(B)` for an arbitrary bounded resolution.** Let `ε : P_• ⟶ B` be a
resolution of `B` over `A` in the sense of [Stacks, Tag 08QI] whose terms are polynomial algebras
on at most `κ` variables. Then the complex `Ω[P_•⁄A] ⊗_{P_•} B` of that resolution, read in
cohomological degrees `≤ 0`, is derived lower shriek of the sheaf of `B̲`-modules
`i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲`, as an object of `D(B)`:

`Q(Ω[P_•⁄A] ⊗_{P_•} B) ≅ Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`.

Here `Lπ_!` is `CommAlgCat.smallPolynomialModuleDerivedLowerShriek`, the total left derived
functor of the colimit over the index category of `B̲`-modules, which is the `π_!` of
[Stacks, Tag 08PF].

The proof is the source's, with the standard resolution replaced by `P_•`: the resolution is a
point resolution of the small model of the footnote-restricted site
(`CommAlgCat.isPointResolution_smallResolutionCosimplicialObject`), so the derived form of
[Stacks, Tag 08PT] at module coefficients
(`Stacks.ChaoticSite.ModuleValued.mooreCochainQIsoDerivedColimit`) computes `Lπ_!` of
`i^*Ω_{𝒪/A}` as the extended Moore complex of its evaluation on `P_•`, and that evaluation is
`Ω[P_•⁄A] ⊗_{P_•} B`. Since the right-hand side does not mention the resolution, this is also
the assertion of [Stacks, Remark 08QI] that any resolution computes `L_{B/A}`. -/
@[stacks 08PU "in D(B), at module coefficients, for an arbitrary resolution whose terms have at \
  most κ variables: Q of the complex of that resolution is L pi_!(Omega ⊗ B-underline) for the \
  point morphism of the small model of the footnote-restricted site C_{B/A}. Combined with the \
  same statement at the standard resolution this is Remark 08QI, that any resolution computes \
  L_{B/A}"]
def smallResolutionCotangentDerivedLowerShriekIso
    (hε : SSet.trivialKanFibrations (Functor.whiskerRight ε (forget (CommAlgCat.{u} A)))) :
    DerivedCategory.Q.obj
        (((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).obj
            (resolutionOver ε ⋙ overDifferentialsFunctor)).extend
          (ComplexShape.embeddingUpIntLE (0 : ℤ))) ≅
      smallPolynomialCotangentDerivedLowerShriek A B κ :=
  (DerivedCategory.Q.mapIso (smallResolutionCotangentMooreCochainIso ε κ hPκ)).symm ≪≫
    mooreCochainQIsoDerivedColimit (smallResolutionCosimplicialObject ε κ hPκ)
      (smallPolynomialCotangentModulePresheaf A B κ)
      (isPointResolution_smallResolutionCosimplicialObject ε κ hPκ hε)

end Derived

section Standard

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-- Every term of the standard resolution of `B` over `A` is a polynomial algebra on at most `κ`
variables, for any bound `κ` containing
`CommAlgCat.standardResolutionVarCardinal A B`. -/
theorem standardResolution_isPolynomialAlgebraBelow_of_le
    (hκ : standardResolutionVarCardinal A B ≤ κ) (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebraBelow A κ ((standardResolution.{u, u} A B).left.obj n) :=
  (standardResolution_isPolynomialAlgebraBelow A B n).mono hκ

/-- **[Stacks, Tag 08PU] in `D(B)` at an arbitrary cardinal bound.** The cotangent complex
`L_{B/A}` of [Stacks, Tag 08PN] is derived lower shriek of the sheaf of `B̲`-modules
`i^*Ω_{𝒪/A} = Ω_{𝒪/A} ⊗_𝒪 B̲` on the small model of the site restricted to polynomial algebras
on at most `κ` variables, for any bound `κ` containing the standard resolution:

`Q(L_{B/A}) ≅ Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`.

This is `CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso` at the standard resolution,
whose complex `Ω[P_•⁄A] ⊗_{P_•} B` is the cotangent complex by
`CommAlgCat.standardResolutionOverDifferentialsIso`. At
`κ = CommAlgCat.standardResolutionVarCardinal A B` it is
`CommAlgCat.standardResolutionCotangentDerivedLowerShriekIso`; the point of the free bound is
that a second resolution may need a larger one. -/
@[stacks 08PU "in D(B), at module coefficients, at an arbitrary cardinal bound κ containing the \
  standard resolution: Q(L_{B/A}) = L pi_!(Omega ⊗ B-underline) for the point morphism of the \
  small model of the site restricted to at most κ variables"]
def standardResolutionCotangentDerivedLowerShriekIsoOfLE
    (hκ : standardResolutionVarCardinal A B ≤ κ) :
    DerivedCategory.Q.obj (cotangentComplex.{u, u} A B) ≅
      smallPolynomialCotangentDerivedLowerShriek A B κ :=
  (DerivedCategory.Q.mapIso
      (((ComplexShape.embeddingUpIntLE (0 : ℤ)).extendFunctor
        (ModuleCat.{u} (B : Type u))).mapIso
          ((alternatingFaceMapComplex (ModuleCat.{u} (B : Type u))).mapIso
            (standardResolutionOverDifferentialsIso A B)))).symm ≪≫
    smallResolutionCotangentDerivedLowerShriekIso (standardResolution.{u, u} A B).hom κ
      (standardResolution_isPolynomialAlgebraBelow_of_le A B κ hκ)
      (standardResolution_isResolution.{u, u} A B).trivialKanFibration

end Standard

end CommAlgCat

end
