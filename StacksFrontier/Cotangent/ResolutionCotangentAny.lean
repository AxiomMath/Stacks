module

public import StacksFrontier.Cotangent.ResolutionComplex
public import StacksFrontier.Cotangent.ResolutionCotangentDerived
public import StacksFrontier.Cotangent.ResolutionPointCriterionSmallOfModules
import StacksCore.Tactic.StacksAttribute

/-!
# Any resolution computes the cotangent complex

Let `A → B` be a ring map. [Stacks, Remark 08QI] records what a resolution `ε : P_• ⟶ B` of `B`
over `A` — every `P_n` a polynomial algebra, `ε` a trivial Kan fibration of simplicial sets — is
good for: it gives a cosimplicial object of the site `C_{B/A}` along which `Lπ_!ℱ` is `ℱ(P_•, ε)`
functorially in `ℱ`, resolutions exist, and for **any** resolution there is a canonical
isomorphism

`L_{B/A} ≅ Ω[P_•⁄A] ⊗_{P_•, ε} B` in `D(B)`.

`StacksFrontier/Cotangent/ResolutionCotangentDerived.lean` and
`StacksFrontier/Cotangent/ResolutionPointCriterionSmallOfModules.lean` prove both identifications for
a resolution whose terms are polynomial algebras on at most `κ` variables, `κ` a cardinal fixed in
advance — the bound being what puts the resolution on the small model of the site that
[Stacks, Tag 08PR] is read at here. This file removes the bound: an arbitrary resolution has
countably many terms, so the disjoint union of their index types bounds all of them at once, and
enlarging that bound by `CommAlgCat.standardResolutionVarCardinal A B` puts the given resolution
and the standard resolution on one site, where the two instances of [Stacks, Tag 08PU] compose.

## Main definitions

* `CommAlgCat.resolutionVarCardinal`: a cardinal bounding the variables of every term of a
  degreewise polynomial simplicial `A`-algebra and of every term of the standard resolution.

## Main results

* `CommAlgCat.exists_isResolution`: **resolutions exist**.
* `CommAlgCat.cotangentComplexIsoOfResolution`: **[Stacks, Remark 08QI] for an arbitrary
  resolution**: `Q(L_{B/A}) ≅ Q(Ω[P_•⁄A] ⊗_{P_•} B)` in `D(B)`, with no bound on the resolution.
* `CommAlgCat.resolutionModuleLeftDerivedLowerShriekNatIso`: `Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)`
  functorially in `ℱ`, for an arbitrary resolution.

## Implementation notes

`CommAlgCat.resolutionVarCardinal` is the cardinality of `Σ n, ι n` for `ι n` an index type
witnessing that `P_n` is a polynomial algebra, chosen by `Exists.choose`; since
`SimplexCategoryᵒᵖ` is a `Type`, that disjoint union is a `Type u` and no cardinal arithmetic is
needed, exactly as for `CommAlgCat.standardResolutionVarCardinal`. The cardinal therefore depends
on the proof `hP` that the terms are polynomial algebras, not only on `P_•`; nothing downstream
needs it to be canonical, since it occurs in no statement of a main result.

The sheaf-level identification is still read at the small model of the footnote-restricted site
rather than at the morphism of ringed topoi `π` of [Stacks, Tag 08PR], for the reason recorded in
the implementation notes of `StacksFrontier/Cotangent/ResolutionPointCriterionSmall.lean`; what is
removed here is only the cardinal bound on the resolution.

Like [Stacks, Tag 08PU] in `D(B)`, the isomorphism of complexes is produced for the one sheaf
`i^*Ω_{𝒪/A}` and is not asserted to be natural in the coefficient sheaf. Its functoriality in the
resolution, at a fixed bound, is
`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso_naturality`.

## References

* [Stacks Project, Tag 08PN](https://stacks.math.columbia.edu/tag/08PN)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open Stacks.ChaoticSite.ModuleValued

universe u v

namespace CommAlgCat

/-! ### Existence of resolutions -/

/-- **[Stacks, Remark 08QI]: resolutions exist.** Every commutative `A`-algebra `B` admits a
resolution over `A`: the standard resolution of `B` over `A` is one, by
`CommAlgCat.standardResolution_isResolution`. -/
@[stacks 08QI "existence of resolutions: every A-algebra B admits a resolution, namely the \
  standard resolution"]
theorem exists_isResolution (A : Type u) [CommRing A] (B : Type (max u v)) [CommRing B]
    [Algebra A B] :
    ∃ (P : SimplicialObject (CommAlgCat.{max u v} A))
      (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{max u v} A)).obj (CommAlgCat.of A B)),
      IsResolution A B P ε :=
  ⟨_, _, standardResolution_isResolution.{u, v} A (CommAlgCat.of A B)⟩

/-! ### A cardinal bounding an arbitrary resolution -/

section Cardinal

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)
  {P : SimplicialObject (CommAlgCat.{u} A)} (hP : ∀ n, IsPolynomialAlgebra A (P.obj n))

/-- A cardinal bounding the variables of every term of a degreewise polynomial simplicial
`A`-algebra `P_•` and of every term of the standard resolution of `B` over `A`: the cardinality of
the disjoint union, over the simplicial degree, of index types witnessing that the terms of `P_•`
are polynomial algebras, enlarged by `CommAlgCat.standardResolutionVarCardinal A B`.

The disjoint union is a `Type u`, so no cardinal arithmetic is needed to bound the terms by it. -/
def resolutionVarCardinal : Cardinal.{u} :=
  max (standardResolutionVarCardinal A B)
    (Cardinal.mk (Σ n : SimplexCategoryᵒᵖ, (hP n).choose))

/-- `CommAlgCat.resolutionVarCardinal` bounds the standard resolution of `B` over `A`. -/
theorem standardResolutionVarCardinal_le_resolutionVarCardinal :
    standardResolutionVarCardinal A B ≤ resolutionVarCardinal A B hP :=
  le_max_left _ _

/-- Every term of `P_•` is a polynomial algebra over `A` on at most
`CommAlgCat.resolutionVarCardinal A B hP` variables: the chosen index type of the degree `n` term
injects into the disjoint union of all of them. -/
theorem isPolynomialAlgebraBelow_resolutionVarCardinal (n : SimplexCategoryᵒᵖ) :
    IsPolynomialAlgebraBelow A (resolutionVarCardinal A B hP) (P.obj n) :=
  ⟨(hP n).choose,
    le_trans
      (Cardinal.mk_le_of_injective
        (f := fun x => (⟨n, x⟩ : Σ m : SimplexCategoryᵒᵖ, (hP m).choose))
        fun _ _ h => by simpa using h)
      (le_max_right _ _),
    (hP n).choose_spec⟩

end Cardinal

/-! ### Remark 08QI for an arbitrary resolution -/

section Any

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {B : CommAlgCat.{u} A}
  {P : SimplicialObject (CommAlgCat.{u} A)}
  (ε : P ⟶ (SimplicialObject.const (CommAlgCat.{u} A)).obj B) (hε : IsResolution A B P ε)

/-- **[Stacks, Remark 08QI]: any resolution computes the cotangent complex.** Let `ε : P_• ⟶ B` be
a resolution of `B` over `A` — every `P_n` a polynomial algebra over `A`, `ε` a trivial Kan
fibration of the underlying simplicial sets — with no bound on the number of variables. Then the
cotangent complex `L_{B/A}` of [Stacks, Tag 08PN], which is built from the *standard* resolution,
is the complex of base-changed differentials of `P_•`, as objects of `D(B)`:

`Q(L_{B/A}) ≅ Q(Ω[P_•⁄A] ⊗_{P_•, ε} B)`.

The proof is the source's. At the cardinal `CommAlgCat.resolutionVarCardinal`, which bounds the
terms of `P_•` and those of the standard resolution at once, both resolutions lie on the small
model of the footnote-restricted site, so the two instances of [Stacks, Tag 08PU] in `D(B)` —
`CommAlgCat.standardResolutionCotangentDerivedLowerShriekIsoOfLE` and
`CommAlgCat.smallResolutionCotangentDerivedLowerShriekIso` — identify both complexes with
`Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)`, which mentions no resolution. -/
@[stacks 08QI "in D(B): for an arbitrary resolution of B over A, with no bound on the number of \
  variables, Q(L_{B/A}) = Q(Omega[P_bullet/A] ⊗_{P_bullet} B); the cardinal bound of the two \
  instances of Tag 08PU this composes is supplied by the resolution itself"]
def cotangentComplexIsoOfResolution :
    DerivedCategory.Q.obj (cotangentComplex.{u, u} A B) ≅
      DerivedCategory.Q.obj (resolutionCotangentComplex.{u, u} A B P ε) :=
  standardResolutionCotangentDerivedLowerShriekIsoOfLE A B
      (resolutionVarCardinal A B hε.isPolynomialAlgebra)
      (standardResolutionVarCardinal_le_resolutionVarCardinal A B hε.isPolynomialAlgebra) ≪≫
    (smallResolutionCotangentDerivedLowerShriekIso ε
      (resolutionVarCardinal A B hε.isPolynomialAlgebra)
      (isPolynomialAlgebraBelow_resolutionVarCardinal A B hε.isPolynomialAlgebra)
      hε.trivialKanFibration).symm

/-- **`Lπ_!(ℱ) = ℱ(P_•, ε)` in `D(B)` for an arbitrary resolution.** Let `ε : P_• ⟶ B` be a
resolution of `B` over `A`, with no bound on the number of variables. For every sheaf of
`B`-modules `ℱ` on the small model of the site `C_{B/A}` restricted to polynomial algebras on at
most `CommAlgCat.resolutionVarCardinal A B hε.isPolynomialAlgebra` variables — a bound the
resolution supplies — the sections at the point of `L_nπ_!(ℱ)` are the degree `n` homology of the
Moore complex of the simplicial `B`-module `ℱ(P_•, ε)`, naturally in `ℱ`.

This is `CommAlgCat.smallResolutionModuleLeftDerivedLowerShriekNatIso` at that cardinal. A bound
cannot be dispensed with altogether here, as it can in
`CommAlgCat.cotangentComplexIsoOfResolution`: the site, and with it `π_!`, is the one restricted
by the bound. -/
@[stacks 08QI "the cosimplicial object of a resolution and the conclusion Lpi_!(F) = F(P_bullet, \
  ε) in D(B) functorially in F, for an arbitrary resolution with no bound on the number of \
  variables, read at the small model of the footnote-restricted site for the reason recorded in \
  `StacksFrontier/Cotangent/ResolutionPointCriterionSmall.lean`"]
def resolutionModuleLeftDerivedLowerShriekNatIso (n : ℕ) :
    (modulePointLowerShriek
          (smallBoundedPolynomialSite A B (resolutionVarCardinal A B hε.isPolynomialAlgebra))
          (B : Type u)).leftDerived n ⋙
        Stacks.ChaoticSite.pointSections.{u, u + 1, u} (ModuleCat.{u} (B : Type u)) ≅
      sheafToPresheaf (GrothendieckTopology.trivial
            (smallBoundedPolynomialSite A B (resolutionVarCardinal A B hε.isPolynomialAlgebra)))
          (ModuleCat.{u} (B : Type u)) ⋙
        moduleCosimplicialMooreComplex (smallResolutionCosimplicialObject ε
            (resolutionVarCardinal A B hε.isPolynomialAlgebra)
            (isPolynomialAlgebraBelow_resolutionVarCardinal A B hε.isPolynomialAlgebra)) ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} (B : Type u))
            (ComplexShape.down ℕ) n :=
  smallResolutionModuleLeftDerivedLowerShriekNatIso ε
    (resolutionVarCardinal A B hε.isPolynomialAlgebra)
    (isPolynomialAlgebraBelow_resolutionVarCardinal A B hε.isPolynomialAlgebra)
    hε.trivialKanFibration n

end Any

end CommAlgCat

end
