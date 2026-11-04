module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningLciDeformationEtaleChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.CoverDeformationChart
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.CoverDeformationPackaging
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.CoverDeformationThickening

/-!
# Stacks 06D8: deforming an unramified local complete intersection cover

Let `U ⊂ U'` be a first-order thickening of affine schemes, `X'` an algebraic space flat over
`U'` and `X = U ×_{U'} X'`. Let `Z ⟶ U` be finite locally free of degree `d` and let
`f : Z ⟶ X` be unramified and a local complete intersection morphism. **Stacks 06D8** asserts
that there is a commutative diagram `(Z ⊂ Z') ⟶ (X ⊂ X')` of first-order thickenings over
`(U ⊂ U')` with `Z' ⟶ U'` finite locally free of degree `d` and `Z = U ×_{U'} Z'`.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation`: **Stacks 06D8**.
* `AlgebraicGeometry.Stack.FiniteHilbert.hasCoverDeformations`: the deformation problem
  `AlgebraicGeometry.Stack.FiniteHilbert.HasCoverDeformations` that the proof of Stacks 06D9
  consumes holds, for every big fppf site and every degree.

## Implementation notes

The statement is made in the language of `HasCoverDeformations`. `U ⟶ U'` is a morphism of the
big fppf site of `S`. `X'` is an algebraic space over `U'`, a presheaf on the big fppf site of
`U'`, and the special fibre `X` is its restriction
`CategoryTheory.OverShriek.relocalizeRestrict` to the big fppf site of `U`. The cover `Z' ⟶ U'`
comes out as an object of the site, a scheme. That loses nothing, since a finite locally free
algebraic space over the affine `U'` is an affine scheme. `Z = U ×_{U'} Z'` is the cartesian
square `hg`. The morphism of thickenings `(f, f') : (Z ⊂ Z') ⟶ (X ⊂ X')` is `f'` together with
the identity of its restriction along `U ⟶ U'` with `f`. The square `hg` makes `Z ⊂ Z'` a
first-order thickening, as a base change of `U ⊂ U'`. Affineness of `U'` is not used.

The proof is the source's, and the conormal sequence is read on an étale chart of `X'`:

1. The first step is
   `FiniteHilbert.exists_universalThickening_scheme_of_coverDeformationData`:
   the universal first-order thickening `Z ⊂ W` of `Z` over `X'` (Stacks 0606) is an affine
   scheme, by the first-order case of Stacks 05ZR.
2. `AlgebraicGeometry.Stack.FiniteHilbert.exists_etaleChart_of_coverDeformationData`: an étale
   atlas `V' ⟶ X'` localizes `Z ⊂ W` to a scheme-level universal first-order thickening
   `Z_V ⊂ W_V` over `V'` (Stacks 060D) of the unramified lci `Z_V ⟶ X_V`.
3. `Stacks.Thickenings.exists_finiteLocallyFreeOfRank_deformation_of_etaleChart`: there the
   sequence `0 → i^*𝒞_{X/X'} → 𝒞_{Z/X'} → 𝒞_{Z/X} → 0` of the source is short exact by
   Stacks 06BA, and its third term is finite locally free by Stacks 06B9. Both properties
   descend to `Z`, the sequence splits on the affine `Z`, and the summand cuts `Z'` out of `W`.
   Stacks 063Y and 06AG carry the degree and the cartesian square up the thickening.
4. `AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation_of_schemeDeformation` reads
   `Z' ⟶ W ⟶ X'` back into the site.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 06D9](https://stacks.math.columbia.edu/tag/06D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Stack.FiniteHilbert

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 06D8.** Let `i : U ⟶ U'` be a first-order thickening of objects of the big fppf
site of `S` with `U` affine, let `X'` be an algebraic space over `U'` flat over `U'`, let
`q : Z ⟶ U` be finite locally free of degree `d`, and let `f : Z ⟶ X` be an unramified local
complete intersection morphism into the special fibre `X = U ×_{U'} X'` (the restriction of
`X'` along `U ⟶ U'`). Then there are `q' : Z' ⟶ U'` finite locally free of degree `d`, a
cartesian square `hg` exhibiting `Z = U ×_{U'} Z'`, and `f' : Z' ⟶ X'` restricting to `f`.

The source also assumes `U'` affine; that follows from `U` affine (Stacks 06AD) and is not
used. -/
@[stacks 06D8]
theorem exists_coverDeformation (d : ℕ) {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hi : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    (X' : (BigFppfOver B U'.left.1 U'.left.2)ᵒᵖ ⥤ Type u)
    (hX' : IsAlgebraicSpace B U'.left.1 U'.left.2 X')
    (hflat : Space.IsFlat B U'.left.1 U'.left.2 (Space.toYonedaId B U'.left.1 U'.left.2 X'))
    {Z : BigFppfOver B S hS} (q : Z ⟶ U)
    (hq : Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q) d)
    (f : yoneda.obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶
      (OverShriek.relocalizeRestrict i.left).obj X')
    (hunr : Space.IsUnramified B U.left.1 U.left.2 f)
    (hlci : Space.IsLocalCompleteIntersection B U.left.1 U.left.2 f) :
    ∃ (Z' : BigFppfOver B S hS) (q' : Z' ⟶ U') (g : Z ⟶ Z') (hg : IsPullback g q q' i),
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((BigFppfOver.toScheme B S hS).map q') d ∧
        ∃ f' : yoneda.obj (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) ⟶ X',
          OverShriek.restrictYonedaHom i.left (coverComparisonOfSquare hg.w) ≫
              (OverShriek.relocalizeRestrict i.left).map f' = f := by
  obtain ⟨W, j, y, hj, hjy, -, huniv⟩ :=
    exists_universalThickening_scheme_of_coverDeformationData i hX' q f hunr hU hi hq
  obtain ⟨ZV, WV, XV, V', a, b, jV, pV, iV, qV, fV, gV, ha, ha', hb, hsq, hpV, hX, hfV, hfVlci,
      hfVq, hUniv, hgV⟩ :=
    exists_etaleChart_of_coverDeformationData i hX' hflat q f hunr hlci j hj y hjy huniv
  have := hq
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj Z) :=
    AlgebraicGeometry.Space.isAffine_of_isFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map q)
      (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d) hU
  have hjg : (BigFppfOver.toScheme B U'.left.1 U'.left.2).map j ≫ B.inclusion.map W.hom =
      (BigFppfOver.toScheme B S hS).map q ≫ (BigFppfOver.toScheme B S hS).map i := by
    have h := congrArg (fun k => B.inclusion.map k) (Over.w j)
    simp only [Functor.map_comp] at h
    exact h
  obtain ⟨Z', iZ, k, -, -, hik, hfl, hpb⟩ :=
    @Stacks.Thickenings.exists_finiteLocallyFreeOfRank_deformation_of_etaleChart _ _ _ _ _ _ _ _
      _ hi _ d hq inferInstance _ hj _ hjg a ha ha' b hb jV hsq pV hpV iV qV hX fV hfV hfVlci
      hfVq gV hUniv hgV
  exact exists_coverDeformation_of_schemeDeformation B S hS d i X' q f j y hjy iZ k hik hfl hpb

/-- **The deformation problem of Stacks 06D8 holds**: for every big fppf site, every scheme `S`
in it and every degree `d`, `HasCoverDeformations B S hS d`. Local finite presentation of `X'`
and affineness of `U'`, which the problem also grants, are not used. -/
theorem hasCoverDeformations (d : ℕ) : HasCoverDeformations B S hS d :=
  fun _ _ i hU _ hi X' hX' hflat _ _ q hq f hunr hlci =>
    exists_coverDeformation B S hS d i hU hi X' hX' hflat q hq f hunr hlci

end AlgebraicGeometry.Stack.FiniteHilbert
