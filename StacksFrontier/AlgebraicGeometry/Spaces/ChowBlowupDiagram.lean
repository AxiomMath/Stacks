module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DenseOpenEmbeddingIntoAffineSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceOver
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# The blowup-and-compactify diagram of Stacks 088R and 088S

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`, let
`U ⊆ X` be an open subspace and let `i : U ⟶ ℙⁿ_Y` be a morphism over `Y`.  Stacks 088R and
Stacks 088S produce the commutative diagram
```
        U
     ↙  ↓  ↘  ↘
   X ← X' → Z' → Z
     ↘  ↓  ↙    ↓
        Y  ←  ℙⁿ_Y
```
in which the arrows out of `U` are open immersions, `X' ⟶ X` is a `U`-admissible blowup,
`X' ⟶ Z'` is an open immersion, `Z' ⟶ Y` is proper and representable, `Z' ⟶ Z` is a
`U`-admissible blowup and `Z ⟶ ℙⁿ_Y` is a closed immersion.
`AlgebraicGeometry.Space.HasChowBlowupDiagram` records the existence of such a diagram, every
listed property and every commutativity, the arrow `U ⟶ Z` composed with `Z ⟶ ℙⁿ_Y` being `i`.

## Main definitions

* `AlgebraicGeometry.Space.HasChowBlowupDiagram`: the diagram of Stacks 088R and 088S exists.

## Main results

* `AlgebraicGeometry.Space.exists_denseOpen_hasChowBlowupDiagram_of_forall`: the reduction of
  Stacks 088S to Stacks 088R, by Stacks 088N and the standard open chart `𝔸ⁿ_Y ⟶ ℙⁿ_Y`.

## Implementation notes

The admissibility of `Z' ⟶ Z` is measured against the image of `U` in `Z`, the range of the
open immersion `U ⟶ Z`; the witness that this range is an open subspace is part of the data, so
that it can be packaged as an element of `AlgebraicGeometry.Space.OpenSubspaces`.  The
morphism `Z' ⟶ Y` of the source is the composite `Z' ⟶ Z ⟶ ℙⁿ_Y ⟶ Y`.

Stacks 088R is not yet available in this library, so the reduction theorem takes its
conclusion, for the given `f`, as an explicit input; it carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 088R](https://stacks.math.columbia.edu/tag/088R)
* [Stacks Project, Tag 088S](https://stacks.math.columbia.edu/tag/088S)
* [Stacks Project, Tag 088N](https://stacks.math.columbia.edu/tag/088N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The diagram of Stacks 088R and 088S exists.**  For a morphism `f : X ⟶ Y` of algebraic
spaces over `S`, an open subspace `U ⊆ X` and a morphism `i : U ⟶ ℙⁿ_Y`, there are algebraic
spaces `X'`, `Z'`, `Z` and morphisms
`π : X' ⟶ X`, `j : X' ⟶ Z'`, `q : Z' ⟶ Z`, `k : Z ⟶ ℙⁿ_Y`, `uX' : U ⟶ X'`, `uZ' : U ⟶ Z'`,
`uZ : U ⟶ Z` such that

* `uX'`, `uZ'` and `uZ` are open immersions;
* `π` is a `U`-admissible blowup;
* `j` is an open immersion;
* the composite `g = q ≫ k ≫ (ℙⁿ_Y ⟶ Y) : Z' ⟶ Y` is proper and representable;
* `q` is a `U`-admissible blowup, `U` being identified with its image in `Z` under `uZ`;
* `k` is a closed immersion;
* the diagram commutes: `uX' ≫ π` is the inclusion of `U`, `uX' ≫ j = uZ'`, `uZ' ≫ q = uZ`,
  `uZ ≫ k = i` and `π ≫ f = j ≫ g`. -/
def HasChowBlowupDiagram {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) (U : Subfunctor X)
    (hU : IsOpenSubspace B S hS U) (n : ℕ) (i : U.toFunctor ⟶ projectiveSpaceOver B S hS Y n) :
    Prop :=
  ∃ (X' Z' Z : AlgebraicSpaces B S hS) (π : X' ⟶ ⟨X, hX⟩) (j : X' ⟶ Z') (q : Z' ⟶ Z)
    (k : Z.1 ⟶ projectiveSpaceOver B S hS Y n) (uX' : U.toFunctor ⟶ X'.1)
    (uZ' : U.toFunctor ⟶ Z'.1) (uZ : U.toFunctor ⟶ Z.1)
    (hUZ : IsOpenSubspace B S hS (Subfunctor.range uZ)),
    IsOpenImmersion B S hS uX' ∧ IsOpenImmersion B S hS uZ' ∧ IsOpenImmersion B S hS uZ ∧
    IsAdmissibleBlowup B S hS ⟨U, hU⟩ π ∧
    IsOpenImmersion B S hS j.hom ∧
    IsProper B S hS (q.hom ≫ k ≫ prod.fst) ∧
    yoneda.relativelyRepresentable (q.hom ≫ k ≫ prod.fst) ∧
    IsAdmissibleBlowup B S hS ⟨Subfunctor.range uZ, hUZ⟩ q ∧
    IsClosedImmersion B S hS k ∧
    uX' ≫ π.hom = U.ι ∧ uX' ≫ j.hom = uZ' ∧ uZ' ≫ q.hom = uZ ∧ uZ ≫ k = i ∧
    π.hom ≫ f = j.hom ≫ q.hom ≫ k ≫ prod.fst

/-- **Stacks 088S from Stacks 088R.**  Let `f : X ⟶ Y` be a separated morphism of finite type
of algebraic spaces over `S` with `Y` Noetherian.  Suppose that the diagram of Stacks 088R
exists for every quasi-compact open subspace `U ⊆ X` and every immersion `i : U ⟶ ℙⁿ_Y` over
`Y` — this is what Stacks 088R gives, `Y` being quasi-compact and quasi-separated.  Then there
are a dense open subspace `U ⊆ X`, an integer `n` and an immersion `i : U ⟶ ℙⁿ_Y` for which the
diagram of Stacks 088S exists.

The proof is the source's: Stacks 088N gives a dense open subspace `U ⊆ X` with an immersion
`U ⟶ 𝔸ⁿ_Y` over `Y` (the morphism `f` is of finite presentation by Stacks 06G4, `Y` being
locally Noetherian), and composing with the standard open chart `𝔸ⁿ_Y ⟶ ℙⁿ_Y` gives an
immersion into `ℙⁿ_Y` over `Y`; `U` is quasi-compact because `X` is Noetherian (Stacks 04ZL).

This declaration carries no `@[stacks]` attribute: it takes the conclusion of Stacks 088R as
the input `hdiagram`. -/
theorem exists_denseOpen_hasChowBlowupDiagram_of_forall
    (hTop : B.Contains (⊤_ Scheme.{u}))
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f)
    (hYnoeth : IsNoetherian B S hS hTop Y)
    (hdiagram : ∀ (U : Subfunctor X) (hU : IsOpenSubspace B S hS U) (n : ℕ)
      (i : U.toFunctor ⟶ projectiveSpaceOver B S hS Y n),
      IsQuasiCompactSpace B S hS U.toFunctor → IsImmersion B S hS i →
      i ≫ prod.fst = U.ι ≫ f → HasChowBlowupDiagram B S hS hX f U hU n i) :
    ∃ (U : Subfunctor X) (hU : IsOpenSubspace B S hS U),
      (letI : TopologicalSpace (points B S hS X) := pointTopology B S hS X;
        DenseRange (pointsMap B S hS U.toFunctor U.ι)) ∧
      ∃ (n : ℕ) (i : U.toFunctor ⟶ projectiveSpaceOver B S hS Y n),
        IsImmersion B S hS i ∧ i ≫ prod.fst = U.ι ≫ f ∧
          HasChowBlowupDiagram B S hS hX f U hU n i := by
  have hfp : IsFinitePresentation B S hS f :=
    isFinitePresentation_of_isFiniteType B S hS hX hY f hYnoeth.2.2 hft
      (isQuasiSeparated_of_isSeparated B S hS hsep)
  have hXnoeth : IsNoetherian B S hS hTop X :=
    isNoetherian_of_isFinitePresentation B S hS hTop f hX hY hfp hYnoeth
  obtain ⟨U, hU, hdense, n, a, ha, hfac⟩ :=
    exists_denseOpen_isImmersion_affineSpaceOver B S hS hTop f hX hY hYnoeth hfp
  have hUqc : IsQuasiCompactSpace B S hS U.toFunctor :=
    isQuasiCompactSpace_of_isImmersion_of_isNoetherian B S hS hTop hX hU.1 hXnoeth U.ι
      (isImmersion_of_isOpenImmersion B S hS hU.2)
  let i := a ≫ affineSpaceOverToProjectiveSpaceOver B S hS Y n
  have hi : IsImmersion B S hS i :=
    isImmersion_comp B S hS a _ ha
      (isImmersion_of_isOpenImmersion B S hS
        (isOpenImmersion_affineSpaceOverToProjectiveSpaceOver B S hS Y n))
  have hifac : i ≫ prod.fst = U.ι ≫ f := by
    simp only [i, Category.assoc, affineSpaceOverToProjectiveSpaceOver_fst, hfac]
  exact ⟨U, hU, hdense, n, i, hi, hifac, hdiagram U hU n i hUqc hi hifac⟩

end AlgebraicGeometry.Space

end
