module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Scheme-theoretic density of a morphism of the site, from dominance of the schemes

The scheme-theoretic image of Stacks 082X of a morphism of algebraic spaces is a *subfunctor* of
the target. For a morphism of the big fppf category over `S` — a morphism of schemes in the site
— there is also the scheme-level notion: the morphism is scheme-theoretically dominant when its
kernel ideal sheaf vanishes. This file proves that the second implies the first being everything,
which is what lets the scheme-level results of
`StacksFrontier/AlgebraicGeometry/Morphisms/Closure/ImmersionImage.lean` be used where Stacks 084N
asks for a scheme-theoretically dense open subspace.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.exists_closedImmersion_range`: a closed subspace of a representable
  presheaf on the big fppf site is the range of a morphism of the site which is a closed
  immersion of schemes.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_top_of_isSchemeTheoreticallyDominant`:
  a morphism of the site which is scheme-theoretically dominant as a morphism of schemes has the
  scheme-theoretic image subfunctor of its yoneda image equal to the whole target.

## What is and is not proved

Stacks 089J is **not** proved here, and no declaration in this file carries a Stacks attribute:
Stacks 082X is carried by `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor` and its three
companion results.

Only one implication is proved; the converse — that scheme-theoretic image subfunctor `⊤` forces
the kernel ideal sheaf to vanish — holds and is not needed below.

## References

* [Stacks Project, Tag 01RB](https://stacks.math.columbia.edu/tag/01RB)
* [Stacks Project, Tag 082X](https://stacks.math.columbia.edu/tag/082X)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A closed subspace of a representable presheaf on the big fppf site is the range of a
morphism of the site which is a closed immersion of schemes.** The base change of its inclusion
along the identity is represented, and the first projection of that base change is an
isomorphism. -/
theorem exists_closedImmersion_range {V : BigFppfOver B S hS} (Zs : Subfunctor (yoneda.obj V))
    (hZ : IsClosedSubspace B S hS Zs) :
    ∃ (R : BigFppfOver B S hS) (j : R ⟶ V),
      AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
        Zs = Subfunctor.range (yoneda.map j) := by
  have hpull : IsPullback (hZ.2.rep.fst (𝟙 (yoneda.obj V)))
      (yoneda.map (hZ.2.rep.snd (𝟙 (yoneda.obj V)))) Zs.ι (𝟙 (yoneda.obj V)) :=
    hZ.2.rep.isPullback (𝟙 (yoneda.obj V))
  have ha : IsIso (hZ.2.rep.fst (𝟙 (yoneda.obj V))) := hpull.isIso_fst_of_isIso
  refine ⟨_, hZ.2.rep.snd (𝟙 (yoneda.obj V)),
    hZ.2.property (𝟙 (yoneda.obj V)) _ _ hpull, Eq.symm ?_⟩
  calc Subfunctor.range (yoneda.map (hZ.2.rep.snd (𝟙 (yoneda.obj V))))
      = Subfunctor.range (hZ.2.rep.fst (𝟙 (yoneda.obj V)) ≫ Zs.ι) := by rw [hpull.w]; simp
    _ = Zs := by
        rw [Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top,
          Subfunctor.range_ι]

/-- **A scheme-theoretically dominant morphism of the big fppf category over `S` has
scheme-theoretic image subfunctor the whole target.** The image is a closed subspace, hence by
`AlgebraicGeometry.Space.exists_closedImmersion_range` the range of a closed immersion `j` of
schemes in the site; the given morphism factors through `j`, so the kernel ideal sheaf of `j` is
below that of the given morphism, which is `⊥` by dominance. A closed immersion with vanishing
kernel is an isomorphism, and the functor to schemes reflects isomorphisms, so `j` is an
isomorphism and its range is everything.

With `AlgebraicGeometry.isSchemeTheoreticallyDominant_toImage_of_quasiCompact` this is what makes
the scheme-theoretic density hypothesis of
`AlgebraicGeometry.Space.existsUnique_glueHom_unionPreimageObj_of_eq_on_dense` available for the
inclusion of a quasi-compact morphism's source into its scheme-theoretic image. -/
@[ega "IV 11.10.3" "(iv)"]
theorem schemeTheoreticImageSubfunctor_eq_top_of_isSchemeTheoreticallyDominant
    {A V : BigFppfOver B S hS} (f : A ⟶ V)
    (hdom : IsSchemeTheoreticallyDominant ((BigFppfOver.toScheme B S hS).map f)) :
    schemeTheoreticImageSubfunctor B S hS (yoneda.map f) = ⊤ := by
  obtain ⟨R, j, hj, heq⟩ := exists_closedImmersion_range B S hS
    (schemeTheoreticImageSubfunctor B S hS (yoneda.map f))
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS (yoneda.map f)
      (isAlgebraicSpace_yoneda B S hS V))
  obtain ⟨l, hl⟩ : ∃ l : A ⟶ R, l ≫ j = f := by
    have hmem : Subfunctor.range (yoneda.map f) ≤ Subfunctor.range (yoneda.map j) := by
      rw [← heq]
      exact range_le_schemeTheoreticImageSubfunctor B S hS (yoneda.map f)
    exact hmem (op A) ⟨𝟙 A, by simp⟩
  have hjc := hj
  have hkerJ : ((BigFppfOver.toScheme B S hS).map j).ker = ⊥ := by
    have hle : ((BigFppfOver.toScheme B S hS).map j).ker ≤
        ((BigFppfOver.toScheme B S hS).map f).ker := by
      rw [show (BigFppfOver.toScheme B S hS).map f =
        (BigFppfOver.toScheme B S hS).map l ≫ (BigFppfOver.toScheme B S hS).map j by
          rw [← Functor.map_comp, hl]]
      exact Scheme.Hom.le_ker_comp _ _
    rw [hdom.ker_eq_bot] at hle
    exact le_antisymm hle bot_le
  have hJiso : IsIso ((BigFppfOver.toScheme B S hS).map j) := by
    rw [IsClosedImmersion.isIso_iff_ker_eq_bot]
    exact hkerJ
  have hrefl : (BigFppfOver.toScheme B S hS).ReflectsIsomorphisms := inferInstance
  have : IsIso j := (isIso_iff_of_reflects_iso j (BigFppfOver.toScheme B S hS)).mp hJiso
  rw [heq]
  exact Subfunctor.range_eq_top (yoneda.map j)

end AlgebraicGeometry.Space

end
