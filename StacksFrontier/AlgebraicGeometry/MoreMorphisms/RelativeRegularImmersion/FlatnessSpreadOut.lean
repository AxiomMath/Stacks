module

public import StacksFrontier.AlgebraicGeometry.Descent.GermSourceAndTarget.Flat
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.StalkIdeal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
# Spreading out flatness of a closed subscheme at a point

Let `f : X ⟶ S` be locally of finite presentation and let `T` be a closed subscheme of `X` which
is locally of finite presentation over `X` and flat over `S` at one point `x` of it.  Then there
is an open neighbourhood `U` of `x` in `X` over which `T` is flat over `S`, and the same holds for
every smaller open.

## Main results

* `Stacks.AlgebraicGeometry.flat_stalkMap_comp_of_isOpenImmersion`: precomposing with an open
  immersion does not change flatness of a stalk map.
* `Stacks.AlgebraicGeometry.isOpenImmersion_subschemeMap_comap`: the comparison of the subscheme
  of a restricted ideal sheaf with the subscheme itself is an open immersion.
* `Stacks.AlgebraicGeometry.exists_mem_flat_subschemeι_comap`: the flatness half of Stacks tag
  063W.

## Implementation notes

The flat locus of `T.subschemeι ≫ f` is open in `T.subscheme`
(`AlgebraicGeometry.isOpen_setOf_isFlatAt`, Stacks tag 0399), and `T.subschemeι` is an
embedding, so that locus is the preimage of an open `V` of `X`.  Over any open `U' ≤ V` the
subscheme of `T.comap U'.ι` maps into the flat locus by an open immersion, so every stalk map of
its structure morphism is flat, which is flatness of that morphism by
`AlgebraicGeometry.Flat.iff_flat_stalkMap`.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
* [Stacks Project, Tag 0399](https://stacks.math.columbia.edu/tag/0399)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

namespace Stacks.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **Precomposition with an open immersion preserves flatness of a stalk map.** -/
theorem flat_stalkMap_comp_of_isOpenImmersion {D Z : Scheme.{u}} (k : D ⟶ Z)
    [IsOpenImmersion k] (g : Z ⟶ S) (z : D) (hg : (g.stalkMap (k z)).hom.Flat) :
    ((k ≫ g).stalkMap z).hom.Flat := by
  have _ : IsIso (k.stalkMap z) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 z
  rw [Scheme.Hom.stalkMap_comp]
  exact RingHom.Flat.comp hg
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (k.stalkMap z)))

/-- **The subscheme of a restricted ideal sheaf sits inside the subscheme by an open
immersion.** -/
theorem isOpenImmersion_subschemeMap_comap (T : X.IdealSheafData) (U : X.Opens) :
    IsOpenImmersion ((T.comap U.ι).subschemeMap T U.ι (T.le_map_comap U.ι)) := by
  have hiso : (T.comapIso U.ι).hom ≫ pullback.snd U.ι T.subschemeι
      = (T.comap U.ι).subschemeMap T U.ι (T.le_map_comap U.ι) := T.comapIso_hom_snd U.ι
  have _ : IsOpenImmersion (pullback.snd U.ι T.subschemeι) :=
    MorphismProperty.pullback_snd U.ι T.subschemeι inferInstance
  exact hiso ▸ (inferInstance : IsOpenImmersion
    ((T.comapIso U.ι).hom ≫ pullback.snd U.ι T.subschemeι))

/-- **The flatness half of Stacks tag 063W.**  If `T` is flat over `S` at a point `x`, then there
is an open neighbourhood `V` of `x` such that over every open contained in `V` the restriction of
`T` is flat over `S`. -/
theorem exists_mem_flat_subschemeι_comap (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (T : X.IdealSheafData) [LocallyOfFinitePresentation T.subschemeι] (x : X)
    (hx : x ∈ T.support)
    (hflat : ((T.subschemeι ≫ f).stalkMap (⟨x, hx⟩ : T.subscheme)).hom.Flat) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ U : X.Opens, U ≤ V →
      Flat ((T.comap U.ι).subschemeι ≫ U.ι ≫ f) := by
  have _ : LocallyOfFinitePresentation (T.subschemeι ≫ f) := inferInstance
  have hopen := isOpen_setOf_isFlatAt (T.subschemeι ≫ f)
  obtain ⟨V, hV, hpre⟩ := T.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.mp hopen
  refine ⟨⟨V, hV⟩, ?_, fun U hU => ?_⟩
  · exact hpre.superset hflat
  · have _ := isOpenImmersion_subschemeMap_comap T U
    have hkcomp : (T.comap U.ι).subschemeMap T U.ι (T.le_map_comap U.ι) ≫ T.subschemeι
        = (T.comap U.ι).subschemeι ≫ U.ι :=
      Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
    have hcomp : (T.comap U.ι).subschemeι ≫ U.ι ≫ f
        = (T.comap U.ι).subschemeMap T U.ι (T.le_map_comap U.ι) ≫ (T.subschemeι ≫ f) := by
      rw [← Category.assoc, ← hkcomp, Category.assoc]
    rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
    intro z
    rw [hcomp]
    refine flat_stalkMap_comp_of_isOpenImmersion _ (T.subschemeι ≫ f) z ?_
    have hpt : T.subschemeι ((T.comap U.ι).subschemeMap T U.ι (T.le_map_comap U.ι) z)
        = U.ι ((T.comap U.ι).subschemeι z) := by
      have h := congrArg (fun m : (T.comap U.ι).subscheme ⟶ X => m.base z) hkcomp
      simpa only [Scheme.Hom.comp_apply] using h
    exact hpre.subset (show T.subschemeι _ ∈ V from hpt ▸ hU ((T.comap U.ι).subschemeι z).2)

end Stacks.AlgebraicGeometry

end
