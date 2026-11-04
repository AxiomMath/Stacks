module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
public import StacksFrontier.CategoryTheory.Sites.Topos.PushforwardEquality

/-!
# Property (C) and direct image on the small étale site

A morphism of schemes `f : X ⟶ Y` has *property (C)* when every scheme étale over `X` is
dominated, by a surjection over `X`, by the base change along `f` of a scheme étale over `Y`.
This file proves [Stacks, Tag 04DT]: if `f` has property (C), then the direct image functor
`f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` reflects injections and surjections.

## The shape of the argument

Property (C) says precisely that the site functor underlying `f_small`, namely base change
`Stacks.EtaleCohomology.smallEtaleBaseChange f : Y.Etale ⥤ X.Etale`, is cover dense: an object
`U` of the small étale site of `X` receives a *surjective* arrow out of the base change of an
étale `Y`-scheme, and a single surjective arrow of the small étale site already generates a
covering sieve. Direct image is restriction along base change, so [Stacks, Tag 04D9] makes it
faithful, and a faithful functor reflects monomorphisms and epimorphisms. For sheaves of sets
those are the injections and the surjections.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChange_isCoverDense_of_hasPropertyC` — property (C)
  makes base change between small étale sites cover dense. This is the verification that the
  Stacks Project proof omits.
* `Stacks.EtaleCohomology.smallEtalePushforward_reflectsMonomorphisms_of_hasPropertyC` and
  `Stacks.EtaleCohomology.smallEtalePushforward_reflectsEpimorphisms_of_hasPropertyC` are the
  two halves of [Stacks, Tag 04DT].

## Implementation notes

The base change of `v : V ⟶ Y` along `f` is `pullback v f`, with its structure morphism to `X`
the second projection, whereas property (C) produces a surjection out of `pullback f v`. The two
are exchanged by `CategoryTheory.Limits.pullbackSymmetry`, which is an isomorphism and hence
surjective, so composing with it preserves the surjectivity that cover density needs.

## References

* [Stacks Project, Tag 04DT](https://stacks.math.columbia.edu/tag/04DT)
* [Stacks Project, Tag 04D9](https://stacks.math.columbia.edu/tag/04D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v

namespace Stacks.EtaleCohomology

/-- A single arrow of the small étale site of `X` whose underlying morphism of schemes is
surjective generates a covering sieve. -/
lemma mem_smallEtaleTopology_of_surjective {X : Scheme.{u}} {A U : X.Etale} (e : A ⟶ U)
    (he : Surjective e.left) :
    Sieve.generate (Presieve.singleton e) ∈ smallEtaleTopology X U := by
  have h : Sieve.ofArrows (fun _ : PUnit.{1} ↦ A) (fun _ ↦ e) ∈ smallEtaleTopology X U := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    have := he
    simp [Set.range_eq_univ.mpr e.left.surjective, Set.iUnion_const]
  simpa [Sieve.ofArrows, Presieve.ofArrows_pUnit] using h

/-- If `f : X ⟶ Y` has property (C), then base change `Y.Etale ⥤ X.Etale` along `f` is cover
dense for the small étale topology of `X`: every étale `X`-scheme is covered by the single
surjection out of a base change that property (C) provides. -/
lemma smallEtaleBaseChange_isCoverDense_of_hasPropertyC {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hC : HasPropertyC f) :
    (smallEtaleBaseChange f).IsCoverDense (smallEtaleTopology X) := by
  refine Functor.isCoverDense_of_generate_singleton_functor_π_mem _ _ fun U ↦ ?_
  obtain ⟨V, v, hv, w, hw, hcomm⟩ := hC U.hom U.prop
  have : Etale v := hv
  have : Surjective w := hw
  have hover : ((pullbackSymmetry v f).hom ≫ w) ≫ U.hom = pullback.snd v f := by
    rw [Category.assoc, hcomm, pullbackSymmetry_hom_comp_fst]
  refine ⟨Scheme.Etale.mk v,
    MorphismProperty.Over.homMk ((pullbackSymmetry v f).hom ≫ w) hover trivial,
    mem_smallEtaleTopology_of_surjective _ ?_⟩
  exact inferInstanceAs (Surjective ((pullbackSymmetry v f).hom ≫ w))

/-- **Stacks Project, Tag 04DT.** If `f : X ⟶ Y` has property (C), then direct image
`f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` on sheaves of sets reflects injections. -/
@[stacks 04DT "reflects injections"]
theorem smallEtalePushforward_reflectsMonomorphisms_of_hasPropertyC
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hC : HasPropertyC f) :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type v)
      (smallEtaleTopology Y) (smallEtaleTopology X)).ReflectsMonomorphisms :=
  have := smallEtaleBaseChange_isCoverDense_of_hasPropertyC f hC
  sheafPushforwardContinuous_reflectsMonomorphisms_of_isCoverDense _ _ _ _

/-- **Stacks Project, Tag 04DT.** If `f : X ⟶ Y` has property (C), then direct image
`f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` on sheaves of sets reflects surjections. -/
@[stacks 04DT "reflects surjections"]
theorem smallEtalePushforward_reflectsEpimorphisms_of_hasPropertyC
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hC : HasPropertyC f) :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type v)
      (smallEtaleTopology Y) (smallEtaleTopology X)).ReflectsEpimorphisms :=
  have := smallEtaleBaseChange_isCoverDense_of_hasPropertyC f hC
  sheafPushforwardContinuous_reflectsEpimorphisms_of_isCoverDense _ _ _ _

end Stacks.EtaleCohomology

end
