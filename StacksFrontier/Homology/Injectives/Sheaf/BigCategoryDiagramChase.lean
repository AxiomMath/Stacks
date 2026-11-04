module

public import StacksFrontier.CategoryTheory.Abelian.SmallSubcategory.AbelianOnly
public import StacksFrontier.Homology.Injectives.Sheaf.EpiTopologyEmbedding
import StacksCore.Tactic.StacksAttribute

/-!
# Diagram chasing in a big abelian category

Tag 05PP embeds an abelian category with a *set* of objects into the abelian sheaves on its
epimorphism site (Tag 05PN), which is what makes diagram chases available there. Tag 05PQ
explains how to reach a big abelian category `𝒜`, one whose objects form a class: given a set
`E` of objects of `𝒜` there is an abelian full subcategory `𝒜' ⊆ 𝒜` with `Ob(𝒜')` a set and
`E ⊆ Ob(𝒜')`, and Tag 05PN applies to `𝒜'`. A statement about finitely many objects and
morphisms of `𝒜` whose proof is a diagram chase can therefore be proved by taking for `E` the
objects it mentions, as the inclusion `𝒜' ⥤ 𝒜` is exact and fully faithful.

This file assembles that composite: for every abelian `𝒜` and every family of objects indexed
by a set there is a small abelian full subcategory containing them which admits a fully
faithful exact embedding into the abelian sheaves on its epimorphism site, a site which has
enough points.

## Main results

* `Stacks.Injectives.exists_small_abelian_subcategory_yonedaSheaf`: the composite of Tag 05PQ
  with Tag 05PN.

## Implementation notes

The subcategory is produced by `exists_small_abelian_full_subcategory`, which assumes nothing
of `𝒜` beyond being abelian — in particular not that it has enough injectives, which Tag 05PQ
does not assume either. "`Ob(𝒜')` is a set" is `Small.{max v w} P.FullSubcategory`, where
`S : Type w` indexes the given family; the abelian structure on `𝒜'` is existentially
quantified because it is not canonical, and the embedding and its properties are stated
relative to it.

The embedding is `Stacks.Injectives.yonedaSheaf` applied to `𝒜'`, and the site is the
epimorphism pretopology of Tag 05PM on `𝒜'`; both come from
`StacksFrontier.Homology.Injectives.Sheaf.EpiTopologyEmbedding`, as does the conservative family
of points.

## References

* [Stacks Project, Tag 05PQ](https://stacks.math.columbia.edu/tag/05PQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

namespace Stacks.Injectives

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {S : Type w}

/-- **Stacks 05PQ.** Let `𝒜` be an abelian category — in particular one whose objects form a
class, so that Tag 05PN does not apply to `𝒜` itself — and let `A : S → 𝒜` be a family of
objects indexed by a set `S`. There is an object property `P` such that the full subcategory
`𝒜' = P.FullSubcategory` has a set of objects, contains every `A s`, and admits an abelian
structure for which:

* the inclusion `P.ι : 𝒜' ⥤ 𝒜` is additive and exact, and
* there is a full, faithful and exact functor from `𝒜'` to the category of abelian sheaves on
  the epimorphism site of `𝒜'`, a site which has a conservative family of points.

The second item is Tag 05PN applied to `𝒜'`, and together with the first it is what lets a
result in `𝒜` whose proof is a diagram chase be proved by chasing in abelian sheaves. -/
@[stacks 05PQ]
theorem exists_small_abelian_subcategory_yonedaSheaf (A : S → 𝒜) :
    ∃ (P : ObjectProperty 𝒜),
      Small.{max v w} P.FullSubcategory ∧
      (∀ s, P (A s)) ∧
      ∃ (_ : Abelian P.FullSubcategory),
        P.ι.Additive ∧
        Nonempty (PreservesFiniteLimits P.ι) ∧
        Nonempty (PreservesFiniteColimits P.ι) ∧
        ∃ F : P.FullSubcategory ⥤
            Sheaf (epiPretopology P.FullSubcategory).toGrothendieck AddCommGrpCat.{v},
          F.Full ∧ F.Faithful ∧
            Nonempty (PreservesFiniteLimits F) ∧ Nonempty (PreservesFiniteColimits F) ∧
            GrothendieckTopology.HasConservativeFamily.{max u v}
              (epiPretopology P.FullSubcategory).toGrothendieck := by
  obtain ⟨P, hclos, hsmall, hA⟩ := exists_abelian_closureCore A
  refine ⟨P, hsmall, hA, ?_⟩
  -- Fix an abelian structure on the subcategory, then apply Tag 05PN to it.
  let : Abelian P.FullSubcategory := (nonempty_abelian_of_closureCore hclos).some
  exact ⟨inferInstance, Functor.fullSubcategoryInclusion_additive P,
    nonempty_preservesFiniteLimits_of_closureCore hclos,
    nonempty_preservesFiniteColimits_of_closureCore hclos,
    yonedaSheaf P.FullSubcategory, yonedaSheaf_full P.FullSubcategory,
    yonedaSheaf_faithful P.FullSubcategory,
    ⟨yonedaSheaf_preservesFiniteLimits P.FullSubcategory⟩,
    ⟨yonedaSheaf_preservesFiniteColimits P.FullSubcategory⟩,
    epiPretopology_hasEnoughPoints P.FullSubcategory⟩

end Stacks.Injectives
