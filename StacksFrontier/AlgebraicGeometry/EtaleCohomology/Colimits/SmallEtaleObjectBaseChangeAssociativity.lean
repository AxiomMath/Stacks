module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLimitLevelTransitionCoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleOpensLeg

/-!
# The base change of an object of a level to the limit, read as a base change through a lower level

Let `(X_i)` be an inverse system of schemes over a nonempty directed index with affine transition
morphisms, all objects of a big étale site `B`, let `X` be the vertex of a limit cone and let `V₀`
be an object of the small étale category of a stage `X_{i₀}`. For every arrow `a : n ⟶ i₀` of the
index of [Stacks, Tag 0EYL] the base change of `V₀` to the limit,
`Stacks.EtaleCohomology.QcSeparatedColimit.toLimitBaseChangeEtaleObj`, is the base change *to the
limit* of its base change to the stage `X_n`,
`Stacks.EtaleCohomology.QcSeparatedColimit.transitionBaseChangeEtaleObj` — the associativity of
two fibre products.

## Main results

All in the namespace `Stacks.EtaleCohomology.AffineLimitCohomology`.

* `toLimitBaseChangeEtaleObjIso` — **that identification**, as an isomorphism of Mathlib's small
  étale site of `X`.
* `mono_hom_smallEtaleBaseChangeTransitionBaseChangeEtaleObj` — the structure morphism of the
  iterated base change is a monomorphism as soon as that of `V₀` is, monomorphisms being stable
  under base change.
* `toEtaleSite_map_fV_comp_toLimitBaseChangeEtaleObjIso_hom` — **the square comparing the leg
  `fV k` of a one-hypercover datum at the limit with the base change of its leg `fVn a k` at a
  stage**, closed by `Stacks.EtaleCohomology.etale_hom_ext_of_mono`.

## How it goes

`V₀ ×_{X_{i₀}} X` and `(V₀ ×_{X_{i₀}} X_n) ×_{X_n} X` are two fibre products of the same cospan,
because the projection of the cone at `i₀` factors through the one at `n`
(`Stacks.EtaleCohomology.AffineLimitCohomology.conePi_transition`) and a pullback square pasted
onto a pullback square on its right is a pullback square
(`CategoryTheory.IsPullback.of_right'`). The two squares are the structure fields
`Stacks.EtaleCohomology.QcSeparatedColimit.toLimitBaseChangeEtaleObj_isPullback` and
`transitionBaseChangeEtaleObj_isPullback`; base change on Mathlib's site is
`CategoryTheory.MorphismProperty.Over.pullback`, i.e. the *chosen* fibre product, so the
comparison is `CategoryTheory.IsPullback.isoPullback` packaged over `X` by
`CategoryTheory.MorphismProperty.Over.isoMk`, exactly as in
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingComponent` and
`Stacks.EtaleCohomology.opensToEtaleBaseChangeIso`.

## Why this is wanted

It is one of the two geometric comparisons that the degree-zero step of [Stacks, Tag 09YQ] over an
object — `Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` — owes
after the pinning lemma
`Stacks.EtaleCohomology.AffineLimitCohomology.levelPullbackLeg_comp_app`: that lemma produces the
leg of a level over the *base change along the projection* of an object of Mathlib's site of the
stage, and the hypothesis `hρ` of the one-hypercover step speaks about the object
`toLimitBaseChangeEtaleObj` of the datum. The implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLevelLegPinning.lean` record the
two, and both are here. The second is the commuting square comparing the leg `fV k` of the datum at
the limit with the base change of its leg `fVn a k` at the level. `OneHypercoverDatum` carries
`fV` and `fVn` as **independent fields** with no field relating them, and
`exists_oneHypercoverOf_datum` returns only `Nonempty`, so nothing about the legs can be read off
the datum; the square is closed instead by `Stacks.EtaleCohomology.etale_hom_ext_of_mono`, from a
monomorphic structure morphism on `V₀`, which has to be carried as a hypothesis because
`exists_oneHypercoverOf_datum` does not ask for it.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex transitionScheme
  toLimitBaseChangeEtaleObj toLimitBaseChangeProj toLimitBaseChangeEtaleObj_isPullback
  transitionBaseChangeEtaleObj transitionBaseChangeEtaleObj_isPullback)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]

/-- **The base change of an object of a stage to the limit is a fibre product over any lower
stage.** The square `(V₀ ×_{X_{i₀}} X) ⟶ (V₀ ×_{X_{i₀}} X_n)` over `X ⟶ X_n` is a pullback square,
by `CategoryTheory.IsPullback.of_right'` applied to the base change to the limit and the base
change along the transition, the projection of the cone at `i₀` factoring through the one at
`n`. -/
theorem isPullback_toLimitBaseChange_transitionBaseChange
    {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i) :
    IsPullback
      ((transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ a).lift
        (toLimitBaseChangeProj D c B hD hX hc V₀)
        (B.inclusion.map (toLimitBaseChangeEtaleObj D c B hD hX hc V₀).obj.hom ≫
          c.π.app (levelIndex D c B hD hX hc n))
        (by
          rw [(toLimitBaseChangeEtaleObj_isPullback D c B hD hX hc V₀).w,
            conePi_transition D c B hD hX hc a, Category.assoc]))
      (B.inclusion.map (toLimitBaseChangeEtaleObj D c B hD hX hc V₀).obj.hom)
      (B.inclusion.map (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a).obj.hom)
      (c.π.app (levelIndex D c B hD hX hc n)) := by
  refine IsPullback.of_right' ?_ (transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ a)
  rw [← conePi_transition D c B hD hX hc a]
  exact toLimitBaseChangeEtaleObj_isPullback D c B hD hX hc V₀

/-- **The base change of an object of a stage to the limit, read as the base change to the limit
of its base change to a lower stage** — the associativity of the two fibre products, as an
isomorphism of Mathlib's small étale site of the limit.

Base change on Mathlib's site is the *chosen* fibre product, so this is
`CategoryTheory.IsPullback.isoPullback` of
`isPullback_toLimitBaseChange_transitionBaseChange` packaged over the limit. -/
def toLimitBaseChangeEtaleObjIso {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i) :
    (AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).obj
        (toLimitBaseChangeEtaleObj D c B hD hX hc V₀) ≅
      (Stacks.EtaleCohomology.smallEtaleBaseChange
          (c.π.app (levelIndex D c B hD hX hc n))).obj
        ((AlgebraicGeometry.SmallEtale.toEtaleSite B
            (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
          (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)) :=
  MorphismProperty.Over.isoMk
    (isPullback_toLimitBaseChange_transitionBaseChange D c B hD hX hc V₀ a).isoPullback
    (IsPullback.isoPullback_hom_snd _)

/-- **The structure morphism of the base change of `V₀` to a stage and then to the limit is a
monomorphism as soon as that of `V₀` is.** Both steps are base changes, and monomorphisms are
stable under base change. -/
theorem mono_hom_smallEtaleBaseChangeTransitionBaseChangeEtaleObj
    {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    (hV₀ : Mono (B.inclusion.map V₀.obj.hom))
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i) :
    Mono ((Stacks.EtaleCohomology.smallEtaleBaseChange
        (c.π.app (levelIndex D c B hD hX hc n))).obj
      ((AlgebraicGeometry.SmallEtale.toEtaleSite B
          (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
        (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a))).hom := by
  have h₁ : (MorphismProperty.monomorphisms AlgebraicGeometry.Scheme.{max u v})
      (B.inclusion.map (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a).obj.hom) :=
    MorphismProperty.of_isPullback
      (transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ a) hV₀
  exact MorphismProperty.of_isPullback
    (P := MorphismProperty.monomorphisms AlgebraicGeometry.Scheme.{max u v})
    (IsPullback.of_hasPullback _ _) h₁

/-- **The square comparing the leg of the one-hypercover datum at the limit with the base change
of its leg at a stage.** For an object `W₀ k` of the datum of
`Stacks.EtaleCohomology.QcSeparatedColimit.OneHypercoverDatum`, the leg `fV k` to the base change
of `V₀` to the limit, read through `toLimitBaseChangeEtaleObjIso`, is the level crossing followed
by the base change of the leg `fVn a k` at the stage `n`.

`OneHypercoverDatum` carries `fV` and `fVn` as **independent fields** with no field relating them,
and `exists_oneHypercoverOf_datum` returns only `Nonempty`, so nothing about the legs can be read
off the datum. The square is instead closed by `Stacks.EtaleCohomology.etale_hom_ext_of_mono`: two
morphisms into an object of Mathlib's small étale site of the limit whose structure morphism is a
monomorphism agree, and that structure morphism is one here as soon as `V₀`'s is
(`mono_hom_smallEtaleBaseChangeTransitionBaseChangeEtaleObj`). The hypothesis `Mono` on `V₀` is
*not* a hypothesis of `exists_oneHypercoverOf_datum` and has to be carried; it holds in both
applications — an open immersion for the surjectivity `hqc`, an identity for the degree-zero
statement `H0`.

Note the transport on the left. `fV k` goes out of the image of `W₀ k` under
`toLimitSmall i₀`, whereas the level crossing at `n` goes out of the image of
`(sys.u a).obj (W₀ k)` under `toLimitSmall n`; the two objects are equal only
propositionally, by the cocone identity `toLimitSmall_transition`, and the hypothesis `hρ` of
`Stacks.WeakSites.ColimitGlobalSections.sectionOver_colimit_of_oneHypercoverOf_ab` carries exactly
this `eqToHom` for that reason. -/
theorem toEtaleSite_map_fV_comp_toLimitBaseChangeEtaleObjIso_hom
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (hV₀ : Mono (B.inclusion.map V₀.obj.hom))
    (E : Stacks.EtaleCohomology.QcSeparatedColimit.OneHypercoverDatum D c B hD hX hc i₀ V₀)
    {n : (sys D c B hD hX hc).I} (a : n ⟶ i₀) (k : E.κ') :
    (AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).map
          ((limitToSmallEtale D c B hX).map
            (eqToHom (Functor.congr_obj
              (toLimitSmall_transition D c B hD hX hc a) (E.W₀ k)))) ≫
        (AlgebraicGeometry.SmallEtale.toEtaleSite B c.pt hX).map (E.fV k) ≫
          (toLimitBaseChangeEtaleObjIso D c B hD hX hc V₀ a).hom =
      (levelCrossingIso D c B hD hX hc n).hom.app (((sys D c B hD hX hc).u a).obj (E.W₀ k)) ≫
        (Stacks.EtaleCohomology.smallEtaleBaseChange
            (c.π.app (levelIndex D c B hD hX hc n))).map
          ((AlgebraicGeometry.SmallEtale.toEtaleSite B
              (D.obj (levelIndex D c B hD hX hc n)) (hD _)).map (E.fVn n a k)) :=
  Stacks.EtaleCohomology.etale_hom_ext_of_mono
    (mono_hom_smallEtaleBaseChangeTransitionBaseChangeEtaleObj D c B hD hX hc V₀ hV₀ a) _ _

end Stacks.EtaleCohomology.AffineLimitCohomology

end
