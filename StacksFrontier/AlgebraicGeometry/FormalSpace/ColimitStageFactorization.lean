module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlongClosedSubspaceReduction

/-!
# Factoring a point of a colimit along thickenings through a stage

Let `S` be a scheme contained in a big fppf site `B` and let `E` be a directed system of fppf
sheaves over `S` whose transition morphisms are representable thickenings. A point of the colimit
`colim E` indexed by a *quasi-compact* object `U` of the site factors through one of the stages
`E.obj i`.

This is the step that the proof of **Stacks 0AIU** uses without proof, at the generality the
source states it: there the point is indexed by an affine scheme, and an affine scheme is a
quasi-compact object of the site
(`AlgebraicGeometry.FormalSpace.isQuasiCompactObject_over_of_compact_scheme`). It is *not* true
for an arbitrary object of the site: for a strictly increasing system, a point of `colim E`
indexed by a disjoint union `⨿ₙ Uₙ` whose `n`-th component reaches the `n`-th stage and no
earlier one factors through no single stage, because the sheaf `Hom` out of a representable
disjoint union is the product of the `Hom`s out of the members.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_factor_through_stage_of_isQuasiCompactObject`: the
  factorization through a stage, for a quasi-compact indexing object.

## Implementation notes

Two inputs carry the argument, and both are already in the library. The transition morphisms are
representable thickenings, hence monomorphisms of presheaves
(`AlgebraicGeometry.FormalSpace.mono_of_isRepresentableThickeningULift`), hence monomorphisms of
sheaves; and the sections of a filtered colimit of sheaves of sets over a quasi-compact object of
the site with monomorphic transition maps are the colimit of the sections, which is part (3) of
Stacks 0738 (`CategoryTheory.Sheaf.injective_and_bijective_colimit_post_sheafSections`). The
combination of the two is
`AlgebraicGeometry.FormalSpace.compact_map_factors_through_filtered_colimit`, and all that is
done here is to restate it for this site and to transport it from the sheafified Yoneda
spelling, in which that lemma is stated, to the universe-lifted Yoneda spelling, in which the
consumers of the factorization state it. The two spellings are related by Yoneda's lemma for
sheaves (`CategoryTheory.Sheaf.sectionEquiv`) composed with Yoneda's lemma for presheaves
(`CategoryTheory.uliftYonedaEquiv`), and the transport is a computation with those two
equivalences and their compatibility with composition.

**No Stacks tag is registered.** The source asserts this step inside the proof of Stacks 0AIU,
parenthetically and without proof ("details omitted"), and gives it no tag of its own; Stacks
0AIA, the nearest tagged statement, is the factorization of a morphism out of a quasi-compact
*algebraic space* into a *presented affine formal algebraic space*, which is this library's
`AlgebraicGeometry.exists_factor_through_thickening` and is neither more nor less general than
the statement here.

## References

* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A point of a directed colimit along representable thickenings, indexed by a quasi-compact
object of the site, factors through a stage.** This is the step the proof of Stacks 0AIU omits,
at the generality the source states it: the source indexes the point by an affine scheme, and an
affine scheme is a quasi-compact object of the big fppf site.

The factorization is an equality with the canonical colimit injection, so nothing beyond the
diagram and the quasi-compactness of the indexing object enters: the system is not assumed to
consist of algebraic spaces, and the colimit is not assumed to satisfy the set-theoretic
condition of Stacks 0AIS. -/
theorem exists_factor_through_stage_of_isQuasiCompactObject
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hthick : ∀ ⦃i j : Λ⦄ (g : i ⟶ j),
      Space.IsRepresentableThickeningULift.{u + 1} B S hS (E.map g).hom)
    (U : BigFppfOver B S hS)
    (hU : (BigFppfOver.topology B S hS).IsQuasiCompactObject U)
    (ξ : (uliftYoneda.{u + 1}).obj U ⟶ (colimit E).obj) :
    ∃ (i : Λ) (ξ' : (uliftYoneda.{u + 1}).obj U ⟶ (E.obj i).obj),
      ξ = ξ' ≫ (colimit.ι E i).hom := by
  classical
  have hmono : ∀ (i j : Λ) (g : i ⟶ j), Mono (E.map g) := fun i j g ↦
    let : Mono (E.map g).hom := mono_of_isRepresentableThickeningULift B S hS (hthick g)
    Sheaf.Hom.mono_of_presheaf_mono (BigFppfOver.topology B S hS) (Type (u + 1)) (E.map g)
  obtain ⟨i, g, hg⟩ := compact_map_factors_through_filtered_colimit E hmono U hU
    ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm (uliftYonedaEquiv.{u + 1} ξ))
  refine ⟨i, uliftYonedaEquiv.{u + 1}.symm
    (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g), ?_⟩
  refine uliftYonedaEquiv.{u + 1}.injective ?_
  calc uliftYonedaEquiv.{u + 1} ξ
      = Sheaf.sectionEquiv (BigFppfOver.topology B S hS)
          ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).symm
            (uliftYonedaEquiv.{u + 1} ξ)) :=
        ((Sheaf.sectionEquiv (BigFppfOver.topology B S hS)).apply_symm_apply _).symm
    _ = Sheaf.sectionEquiv (BigFppfOver.topology B S hS) (g ≫ colimit.ι E i) :=
        congrArg (Sheaf.sectionEquiv (BigFppfOver.topology B S hS)) hg.symm
    _ = (colimit.ι E i).hom.app (op U)
          (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g) :=
        Sheaf.sectionEquiv_comp (BigFppfOver.topology B S hS) g (colimit.ι E i)
    _ = (colimit.ι E i).hom.app (op U)
          (uliftYonedaEquiv.{u + 1} (uliftYonedaEquiv.{u + 1}.symm
            (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g))) :=
        congrArg ((colimit.ι E i).hom.app (op U))
          (uliftYonedaEquiv.{u + 1}.apply_symm_apply _).symm
    _ = uliftYonedaEquiv.{u + 1} (uliftYonedaEquiv.{u + 1}.symm
          (Sheaf.sectionEquiv (BigFppfOver.topology B S hS) g) ≫ (colimit.ι E i).hom) :=
        (uliftYonedaEquiv_comp _ _).symm

end AlgebraicGeometry.FormalSpace

end
