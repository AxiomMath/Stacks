module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitOpensSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleLevelTransitionPinning

/-!
# The base change of an object of a level to a lower level, read through an intermediate one

`Stacks.EtaleCohomology.AffineLimitCohomology.toLimitBaseChangeEtaleObjIso` reads the base change
of an object `V₀` of a stage `X_{i₀}` **to the limit** as the base change to the limit of its base
change to an intermediate stage. This file is the same associativity with the limit replaced by a
**lower stage**: for composable arrows `b : m ⟶ n` and `a : n ⟶ i₀` of the index of the levels of
[Stacks, Tag 0EYL], the base change of `V₀` to `X_m` is the base change along the transition
`X_m ⟶ X_n` of its base change to `X_n`.

It is what the separatedness half of the degree-zero step of [Stacks, Tag 09YQ] needs. That half
returns an agreement of two sections of `F_m` over the objects of the covering datum at the level
`m`, and the sheaf condition that turns such an agreement into an equality of sections is the
covering `OneHypercoverDatum.isLevelDatum m (b ≫ a)` of the base change of `V₀` to `X_m` — whereas
the sections themselves, being values of
`Stacks.EtaleCohomology.AffineLimitCohomology.levelDirTransition`, live over the base change along
the transition of the base change to `X_n`. The two objects are identified here, and the legs of
the datum are compared through that identification.

## Main results

All in the namespace `Stacks.EtaleCohomology.AffineLimitCohomology`:

* `isPullback_transitionBaseChange_transitionBaseChange` — the square exhibiting the iterated
  base change as a fibre product, by `CategoryTheory.IsPullback.of_right'`.
* `transitionBaseChangeEtaleObjIso` — **that identification**, as an isomorphism of Mathlib's
  small étale site of `X_m`.
* `mono_hom_smallEtaleBaseChange_transitionBaseChangeEtaleObj` — the structure morphism of the
  iterated base change is a monomorphism as soon as that of `V₀` is.
* `toEtaleSite_map_fVn_comp_transitionBaseChangeEtaleObjIso_hom` — **the square comparing the
  leg `fVn (b ≫ a) k` of the datum at the level `m` with the base change along the transition of
  its leg `fVn a k` at the level `n`**, closed by `Stacks.EtaleCohomology.etale_hom_ext_of_mono`.

## Implementation notes

Everything is the transition counterpart of the limit case in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleObjectBaseChangeAssociativity`
(`Stacks.EtaleCohomology.AffineLimitCohomology.toLimitBaseChangeEtaleObjIso`), with the
projection `c.π.app (levelIndex n)` of the limit cone replaced by the transition morphism
`Stacks.EtaleCohomology.QcSeparatedColimit.transitionScheme` and the factorisation
`Stacks.EtaleCohomology.AffineLimitCohomology.conePi_transition` of the projections replaced by
`Stacks.EtaleCohomology.AffineLimitCohomology.transitionScheme_comp`. `V₀ ×_{X_{i₀}} X_m` and
`(V₀ ×_{X_{i₀}} X_n) ×_{X_n} X_m` are two fibre products of the same cospan, because a pullback
square pasted onto a pullback square on its right is a pullback square; base change on Mathlib's
site is the *chosen* fibre product, so the comparison is
`CategoryTheory.IsPullback.isoPullback` packaged over `X_m` by
`CategoryTheory.MorphismProperty.Over.isoMk`.

`Stacks.EtaleCohomology.QcSeparatedColimit.OneHypercoverDatum` relates its legs `fVn` at
different levels by no field at all, and
`Stacks.EtaleCohomology.QcSeparatedColimit.exists_oneHypercoverOf_datum` returns only `Nonempty`,
so the square comparing them cannot be read off the datum; as in the limit case it is closed
instead by `Stacks.EtaleCohomology.etale_hom_ext_of_mono`, from a monomorphic structure morphism
on `V₀`. Note the transport on the right: the datum's leg at `m` goes out of the image of
`(sys.u (b ≫ a)).obj (W₀ k)` whereas the level transition identification goes out of the image of
`(sys.u b).obj ((sys.u a).obj (W₀ k))`, and the two objects are equal only propositionally, by the
strictness field `comp` of the system of [Stacks, Tag 0EYL] — the same `eqToHom` that
`Stacks.EtaleCohomology.AffineLimitCohomology.levelTransitionIso_hom_app_comp` carries.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0EYL](https://stacks.math.columbia.edu/tag/0EYL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace Stacks.EtaleCohomology.AffineLimitCohomology

open AlgebraicGeometry CategoryTheory.Sites.InverseSystem
open Stacks.EtaleCohomology.QcSeparatedColimit (levelIndex transitionScheme
  transitionBaseChangeEtaleObj transitionBaseChangeProj transitionBaseChangeEtaleObj_isPullback
  OneHypercoverDatum)

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (D : Iᵒᵖ ⥤ AlgebraicGeometry.Scheme.{max u v}) (c : Cone D)
  (B : AlgebraicGeometry.BigEtaleSite.{max u v})
  (hD : ∀ i, B.Contains (D.obj i)) (hX : B.Contains c.pt)
  (hc : IsLimit c)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), AlgebraicGeometry.IsAffineHom (D.map a)]

/-- **The base change of an object of a stage to a lower stage is a fibre product over any
intermediate stage.** The square `(V₀ ×_{X_{i₀}} X_m) ⟶ (V₀ ×_{X_{i₀}} X_n)` over `X_m ⟶ X_n` is a
pullback square, by `CategoryTheory.IsPullback.of_right'` applied to the base change along the
composite transition and the base change along `a`, the composite transition factoring through
the one at `b`. -/
theorem isPullback_transitionBaseChange_transitionBaseChange
    {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    {n m : (sys D c B hD hX hc).I} (a : n ⟶ i) (b : m ⟶ n) :
    IsPullback
      ((transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ a).lift
        (transitionBaseChangeProj D c B hD hX hc V₀ (b ≫ a))
        (B.inclusion.map
            (transitionBaseChangeEtaleObj D c B hD hX hc V₀ (b ≫ a)).obj.hom ≫
          transitionScheme D c B hD hX hc b)
        (by
          rw [(transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ (b ≫ a)).w,
            transitionScheme_comp D c B hD hX hc b a, Category.assoc]))
      (B.inclusion.map (transitionBaseChangeEtaleObj D c B hD hX hc V₀ (b ≫ a)).obj.hom)
      (B.inclusion.map (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a).obj.hom)
      (transitionScheme D c B hD hX hc b) := by
  refine IsPullback.of_right' ?_ (transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ a)
  rw [← transitionScheme_comp D c B hD hX hc b a]
  exact transitionBaseChangeEtaleObj_isPullback D c B hD hX hc V₀ (b ≫ a)

/-- **The base change of an object of a stage to a lower stage, read as the base change along the
transition of its base change to an intermediate stage** — the associativity of the two fibre
products, as an isomorphism of Mathlib's small étale site of the lower stage.

Base change on Mathlib's site is the *chosen* fibre product, so this is
`CategoryTheory.IsPullback.isoPullback` of
`isPullback_transitionBaseChange_transitionBaseChange` packaged over `X_m`. -/
def transitionBaseChangeEtaleObjIso {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    {n m : (sys D c B hD hX hc).I} (a : n ⟶ i) (b : m ⟶ n) :
    (AlgebraicGeometry.SmallEtale.toEtaleSite B
          (D.obj (levelIndex D c B hD hX hc m)) (hD _)).obj
        (transitionBaseChangeEtaleObj D c B hD hX hc V₀ (b ≫ a)) ≅
      (Stacks.EtaleCohomology.smallEtaleBaseChange
          (transitionScheme D c B hD hX hc b)).obj
        ((AlgebraicGeometry.SmallEtale.toEtaleSite B
            (D.obj (levelIndex D c B hD hX hc n)) (hD _)).obj
          (transitionBaseChangeEtaleObj D c B hD hX hc V₀ a)) :=
  MorphismProperty.Over.isoMk
    (isPullback_transitionBaseChange_transitionBaseChange D c B hD hX hc V₀ a b).isoPullback
    (IsPullback.isoPullback_hom_snd _)

/-- **The structure morphism of the base change of `V₀` to a stage and then along a transition is
a monomorphism as soon as that of `V₀` is.** Both steps are base changes, and monomorphisms are
stable under base change. The transition counterpart of
`mono_hom_smallEtaleBaseChangeTransitionBaseChangeEtaleObj`,
whose second base change is along a projection of the limit cone. -/
theorem mono_hom_smallEtaleBaseChange_transitionBaseChangeEtaleObj
    {i : (sys D c B hD hX hc).I}
    (V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i)) (hD _))
    (hV₀ : Mono (B.inclusion.map V₀.obj.hom))
    {n m : (sys D c B hD hX hc).I} (a : n ⟶ i) (b : m ⟶ n) :
    Mono ((Stacks.EtaleCohomology.smallEtaleBaseChange
        (transitionScheme D c B hD hX hc b)).obj
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

/-- **The square comparing the leg of the one-hypercover datum at a level with the base change
along a transition of its leg at an intermediate level.** For an object `W₀ k` of the datum of
`Stacks.EtaleCohomology.QcSeparatedColimit.OneHypercoverDatum`, the leg `fVn m (b ≫ a) k` to the
base change of `V₀` at the level `m`, read through `transitionBaseChangeEtaleObjIso`, is the level
transition identification followed by the base change along the transition of the leg `fVn n a k`
at the level `n`.

`OneHypercoverDatum` carries the legs `fVn` at different levels as values of ONE field with no
relation between them, and `exists_oneHypercoverOf_datum` returns only `Nonempty`, so nothing about
the legs can be read off the datum. The square is instead closed by
`Stacks.EtaleCohomology.etale_hom_ext_of_mono`: two morphisms into an object of Mathlib's small
étale site of `X_m` whose structure morphism is a monomorphism agree, and that structure morphism
is one here as soon as `V₀`'s is
(`mono_hom_smallEtaleBaseChange_transitionBaseChangeEtaleObj`). The hypothesis `Mono` on `V₀` is
*not* a hypothesis of `exists_oneHypercoverOf_datum` and has to be carried; it holds in the
application, where `V₀` is the object of the open `⊤` of a stage and its structure morphism an
open immersion. -/
theorem toEtaleSite_map_fVn_comp_transitionBaseChangeEtaleObjIso_hom
    {i₀ : (sys D c B hD hX hc).I}
    {V₀ : AlgebraicGeometry.SmallEtale B (D.obj (levelIndex D c B hD hX hc i₀)) (hD _)}
    (hV₀ : Mono (B.inclusion.map V₀.obj.hom))
    (E : OneHypercoverDatum D c B hD hX hc i₀ V₀)
    {n m : (sys D c B hD hX hc).I} (a : n ⟶ i₀) (b : m ⟶ n) (k : E.κ') :
    (AlgebraicGeometry.SmallEtale.toEtaleSite B
            (D.obj (levelIndex D c B hD hX hc m)) (hD _)).map (E.fVn m (b ≫ a) k) ≫
        (transitionBaseChangeEtaleObjIso D c B hD hX hc V₀ a b).hom =
      (levelEtaleSite D c B hD hX hc m).map
          (eqToHom (Functor.congr_obj ((sys D c B hD hX hc).comp b a) (E.W₀ k))) ≫
        (levelTransitionIso D c B hD hX hc b).hom.app
            (((sys D c B hD hX hc).u a).obj (E.W₀ k)) ≫
          (Stacks.EtaleCohomology.smallEtaleBaseChange
              (transitionScheme D c B hD hX hc b)).map
            ((AlgebraicGeometry.SmallEtale.toEtaleSite B
                (D.obj (levelIndex D c B hD hX hc n)) (hD _)).map (E.fVn n a k)) :=
  Stacks.EtaleCohomology.etale_hom_ext_of_mono
    (mono_hom_smallEtaleBaseChange_transitionBaseChangeEtaleObj D c B hD hX hc V₀ hV₀ a b) _ _

end Stacks.EtaleCohomology.AffineLimitCohomology

end
