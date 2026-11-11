module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.ColumnAcyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceColumnZeroSections

/-!
# The double complex of a general crystal, once the per-degree connections are given

`StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/WholeSpaceCosimplicialModule.lean` builds
the **module** half of the double complex

`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}`

of [Stacks, Proposition 60.21.3, Tag 07LG] for an arbitrary crystal in quasi-coherent
`𝒪_{X/S}`-modules, as `...SmallSite.wholeSpaceCosimplicialModule`.  What
`Crystalline.CosimplicialCompletedPair` carries beyond the module is three fields: a completed
connection in each cosimplicial degree, its horizontality for the cosimplicial transitions, and
the vanishing of the square of the resulting de Rham differential.

This module does two things.

* `...SmallSite.wholeSpaceCosimplicialPair` assembles the pair, and so the double complex `K`,
  from those three fields.  Its underlying cosimplicial module is
  `...SmallSite.wholeSpaceCosimplicialModule` by definition, which is what makes the two edge
  identifications below land on the nose.
* It reads off the two hypotheses of `...SmallSite.computes07LG_of_edges_of_isGradedExterior`
  that are statements about the columns of `K`, and **both are theorems** for this `K`:

  - `hcolumns`, the acyclicity of the columns `a > 0`, is
    `Crystalline.isZero_homology_alternatingCofaceMapComplex_doubleComplex_X` — the library's
    [Stacks, Lemma 60.19.3, Tag 07LF], which needs only the surjectivity of the presentation and
    holds for **every** pair over the cosimplicial envelope, connections and all;
  - `hcolumn0`, the identification of the column `a = 0` with the complex
    `M(0) → M(1) → M(2) → ⋯` of [Stacks, Proposition 60.20.1, Tag 07JN], is
    `...SmallSite.wholeSpaceColumnZeroSectionsHomologyIso`.

So after this module the double complex of a general crystal, and everything about its
cosimplicial direction, rests on the connections alone.

## Main definitions

* `...SmallSite.wholeSpaceCosimplicialPair` — **the pair, hence `K`**, from the three connection
  fields.
* `...SmallSite.wholeSpaceDoubleComplex` — the double complex `K` of a general crystal.

## Main results

* `...SmallSite.wholeSpaceCosimplicialPair_toCosimplicialCompletedModule` — its module half is
  `...SmallSite.wholeSpaceCosimplicialModule`, by definition.
* `...SmallSite.isZero_homology_wholeSpaceDoubleComplex_X` — **`hcolumns` for this `K`.**
* `...SmallSite.wholeSpaceDoubleComplexColumnZeroHomologyIso` — **`hcolumn0` for this `K`.**

## What is and is not proved

**No `@[stacks …]` attribute is placed here.**  [Stacks, Tag 07LG] is
`...SmallSite.crystalPairDeRhamDerivedPlusIso` of
`SmallSite/CrystalDeRhamDerived07LG.lean`.  The three connection fields are parameters of
every definition below; nothing in this module constructs a connection.  For a crystal, the pair on
the same cosimplicial module with the base-change connections is
`...SmallSite.crystalCosimplicialPair` of `SmallSite/CrystalCosimplicialPair.lean`.  What falls is
the column half of the double complex hypotheses of the reduction.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.3, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry Simplicial AlgebraicTopology
open CategoryTheory.Limits

universe u

namespace Crystalline

namespace GlobalCrystallineSituation.SmallSite

open Crystalline

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme] (Fc : QuasiCoherentCrystal S)

/-- **The cosimplicial module `M(•)` of a general crystal, with a completed connection in each
cosimplicial degree.**

The three arguments are exactly the three fields `Crystalline.CosimplicialCompletedPair` carries
beyond its underlying `Crystalline.CosimplicialCompletedModule`: the connection `∇_b` of
[Stacks, Tag 07JC] on `M(b)`, its compatibility with the cosimplicial transitions, and the
vanishing of the square of the de Rham differential it induces. -/
def wholeSpaceCosimplicialPair
    (nabla : ∀ b : ℕ, CompletedConnection S.p ((wholeSpaceDPAlgebra hp).completedRing S.p b)
      ((wholeSpaceDPAlgebra hp).forms S.p 1 b) ((wholeSpaceDPAlgebra hp).differential S.p b)
      ((wholeSpaceCosimplicialModule hp Fc).carrier b))
    (hnabla : ∀ {m n : SimplexCategory} (φ : m ⟶ n)
      (x : (wholeSpaceCosimplicialModule hp Fc).carrier m.len),
      nabla n.len ((wholeSpaceCosimplicialModule hp Fc).map φ x) =
        (wholeSpaceCosimplicialModule hp Fc).tensorMap φ 1 (nabla m.len x))
    (hsq : ∀ b : ℕ, CompletedDeRham.IsSquareZero S.p
      ((wholeSpaceDPAlgebra hp).completedRing S.p b)
      (fun a => (wholeSpaceDPAlgebra hp).forms S.p a b) ((wholeSpaceDPAlgebra hp).wedge S.p b)
      ((wholeSpaceDPAlgebra hp).deRham S.p b)
      ((wholeSpaceCosimplicialModule hp Fc).carrier b) (nabla b)
      ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p b)) :
    CosimplicialCompletedPair.{u, u, u} (wholeSpaceDPAlgebra hp) S.p where
  toCosimplicialCompletedModule := wholeSpaceCosimplicialModule hp Fc
  nabla := nabla
  nabla_tensorMap φ x := hnabla φ x
  isSquareZero := hsq

variable
    (nabla : ∀ b : ℕ, CompletedConnection S.p ((wholeSpaceDPAlgebra hp).completedRing S.p b)
      ((wholeSpaceDPAlgebra hp).forms S.p 1 b) ((wholeSpaceDPAlgebra hp).differential S.p b)
      ((wholeSpaceCosimplicialModule hp Fc).carrier b))
    (hnabla : ∀ {m n : SimplexCategory} (φ : m ⟶ n)
      (x : (wholeSpaceCosimplicialModule hp Fc).carrier m.len),
      nabla n.len ((wholeSpaceCosimplicialModule hp Fc).map φ x) =
        (wholeSpaceCosimplicialModule hp Fc).tensorMap φ 1 (nabla m.len x))
    (hsq : ∀ b : ℕ, CompletedDeRham.IsSquareZero S.p
      ((wholeSpaceDPAlgebra hp).completedRing S.p b)
      (fun a => (wholeSpaceDPAlgebra hp).forms S.p a b) ((wholeSpaceDPAlgebra hp).wedge S.p b)
      ((wholeSpaceDPAlgebra hp).deRham S.p b)
      ((wholeSpaceCosimplicialModule hp Fc).carrier b) (nabla b)
      ((wholeSpaceDPAlgebra hp).isGradedLeibniz S.p b))

/-- The module half of the pair is the cosimplicial module `M(•)` of a general crystal. -/
theorem wholeSpaceCosimplicialPair_toCosimplicialCompletedModule :
    (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).toCosimplicialCompletedModule =
      wholeSpaceCosimplicialModule hp Fc := rfl

/-- **The double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of a general crystal in
quasi-coherent `𝒪_{X/S}`-modules**, given a completed connection in each cosimplicial degree. -/
def wholeSpaceDoubleComplex : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ :=
  (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq).doubleComplex

/-- The exterior degree `a` of `K` is the column `K^{a,•}` of `M(•)`. -/
theorem wholeSpaceDoubleComplex_X (a : ℕ) :
    (wholeSpaceDoubleComplex hp Fc nabla hnabla hsq).X a =
      (wholeSpaceCosimplicialModule hp Fc).column a := rfl

/-- **The hypothesis `hcolumns` of [Stacks, Proposition 60.21.3, Tag 07LG] for the double complex
of a general crystal**: the columns `a > 0` of `K` are acyclic.

This is [Stacks, Lemma 60.19.3, Tag 07LF] in the form
`Crystalline.isZero_homology_alternatingCofaceMapComplex_doubleComplex_X`, whose only input
besides the pair is the surjectivity of the presentation of `Γ(X, 𝒪_X)`; the presentation here is
the tautological one, surjective by `Crystalline.canonicalPresentation_surjective`.  Nothing about
the connections enters. -/
theorem isZero_homology_wholeSpaceDoubleComplex_X (a : ℕ) (ha : 0 < a) (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
      ((wholeSpaceDoubleComplex hp Fc nabla hnabla hsq).X a)).homology j) :=
  isZero_homology_alternatingCofaceMapComplex_doubleComplex_X (affineSituation S hp)
    (wholeSpacePresentation S hp)
    (wholeSpacePresentation_surjective S hp)
    (wholeSpaceCosimplicialPair hp Fc nabla hnabla hsq) a ha j

/-- **The hypothesis `hcolumn0` of [Stacks, Proposition 60.21.3, Tag 07LG] for the double complex
of a general crystal**: the cohomology of the Moore complex of the column `a = 0` of `K` is the
cohomology of the complex `M(0) → M(1) → M(2) → ⋯` of [Stacks, Proposition 60.20.1, Tag 07JN].

The column `a = 0` of this `K` is the column `a = 0` of
`...SmallSite.wholeSpaceCosimplicialModule` by definition, so this is
`...SmallSite.wholeSpaceColumnZeroSectionsHomologyIso` with nothing transported. -/
def wholeSpaceDoubleComplexColumnZeroHomologyIso (j : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj
          ((wholeSpaceDoubleComplex hp Fc nabla hnabla hsq).X 0)).homology j) ≅
      (sectionsComplex (wholeSpaceSystem S hp) (abelianSheaf Fc.obj).obj).homology j :=
  wholeSpaceColumnZeroSectionsHomologyIso hp Fc j

end GlobalCrystallineSituation.SmallSite

end Crystalline

end
