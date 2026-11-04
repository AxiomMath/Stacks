module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# Testing a representable transformation on a scheme atlas (Stacks 02WZ)

Let `S` be a scheme contained in a big fppf site `B`, let `P` be a property of morphisms of
schemes which is stable under base change and local on the target for the fppf topology, and
let `f : G ⟶ F` be a representable transformation of presheaves on the big fppf site of `S`.
Write `P'` for the associated relative property
`(P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf` of transformations: it asks that
every representable base change of `f` be a morphism of the site whose underlying morphism of
schemes has `P`.

If `q : h_U ⟶ F` is surjective and étale after every representable base change — for instance
a scheme atlas of an algebraic space `F`, by **Stacks 025Y** — then `P'` holds for `f` as soon
as it holds for the single base change of `f` along `q`. So a relative property of this kind
may be tested on one atlas of the target.

## Main results

* `AlgebraicGeometry.presheaf_inverseImage_iff_atlas_snd`: **Stacks 02WZ**.

## Implementation notes

The forward implication is immediate. For the converse, `CategoryTheory.MorphismProperty`'s
`relative_of_snd` reduces the goal to the base change `h_T ×_F G ⟶ h_T` of `f` along an
arbitrary representable `g : h_T ⟶ F`, so the task is to pass from the atlas `U` to an
arbitrary `T`. Both base changes are compared over the fibre product `U ×_F T` of the site:
writing `v` for the base change of `f` along `q` and `w` for its base change along `g`, and
`s, t` for the two projections of `U ×_F T`, the two squares

```
U ×_F T ×_U (U ×_F G) ⟶ U ×_F G        U ×_F T ×_T (T ×_F G) ⟶ T ×_F G
      |                     |                 |                   |
      v                     v                 v                   v
   U ×_F T    ⟶            U              U ×_F T   ⟶             T
```

both present `G ⟶ F` pulled back along the *same* transformation `h_{U ×_F T} ⟶ F`, so their
sources are canonically isomorphic. Hence `pullback.snd w s`, the base change of `w` along
`s`, has `P` because `pullback.snd v t` does, `P` being stable under base change. Now `s` is
the base change of the atlas `q` along `g`, so the morphism of schemes underlying `s` is flat,
surjective and locally of finite presentation, i.e. a one-member fppf covering of the scheme
underlying `T`; since `P` is fppf local on the target and holds for the base change of `w`
along it, it holds for `w`.

The two comparisons of a Yoneda-image pullback with the pullback taken in the site are made by
`CategoryTheory.Functor.preimageIso` and `CategoryTheory.Limits.IsPullback.isoIsPullback`, and
transported to `P` by `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`.

## References

* [Stacks Project, Tag 02WZ](https://stacks.math.columbia.edu/tag/02WZ)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 02WZ.** A representable transformation of presheaves on the big fppf site of `S`
has a base-change stable, fppf local relative property exactly when its base change along one
surjective étale representable transformation to the target has it. The presheaves are
arbitrary: no algebraic space condition on `F` or `G` enters the argument. -/
@[stacks 02WZ]
theorem presheaf_inverseImage_iff_atlas_snd
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] [P.IsLocalAtTarget Scheme.fppfPrecoverage]
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : G ⟶ F) (hf : yoneda.relativelyRepresentable f)
    (U : BigFppfOver B S hS) (q : yoneda.obj U ⟶ F)
    (hq_surj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hq_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q) :
    (MorphismProperty.presheaf
      (P.inverseImage (BigFppfOver.toScheme B S hS))) f ↔
      P ((BigFppfOver.toScheme B S hS).map (hf.snd q)) := by
  let T : BigFppfOver B S hS ⥤ Scheme.{u} := BigFppfOver.toScheme B S hS
  let Q : MorphismProperty (BigFppfOver B S hS) := P.inverseImage T
  show Q.presheaf f ↔ P (T.map (hf.snd q))
  refine ⟨fun h => h.property_snd q, fun h => ?_⟩
  refine MorphismProperty.relative_of_snd (F := yoneda) (P := Q) hf fun a g => ?_
  let qrep := hq_surj.rep
  let s := qrep.snd g
  let t := qrep.fst' g
  let v := hf.snd q
  let w := hf.snd g
  have hxC := IsPullback.of_hasPullback v t
  have hzC := IsPullback.of_hasPullback w s
  have hxF := (hxC.map yoneda).paste_horiz (hf.isPullback q)
  have hzF := (hzC.map yoneda).paste_horiz (hf.isPullback g)
  have hbase : yoneda.map t ≫ q = yoneda.map s ≫ g := by
    show yoneda.map (qrep.fst' g) ≫ q = yoneda.map (qrep.snd g) ≫ g
    rw [qrep.map_fst']
    exact qrep.w g
  let eD := hxF.isoIsPullback _ _ (by simpa only [hbase] using hzF)
  let e := yoneda.preimageIso eD
  have he_snd : e.hom ≫ pullback.snd w s = pullback.snd v t := by
    apply yoneda.map_injective
    simp [e, eD, hxF.isoIsPullback_hom_snd _ _ (by simpa only [hbase] using hzF)]
  have he_snd' : T.map e.hom ≫ T.map (pullback.snd w s) = T.map (pullback.snd v t) := by
    rw [← T.map_comp, he_snd]
  have hP_x : P (T.map (pullback.snd v t)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (hxC.map T) h
  have hP_z : P (T.map (pullback.snd w s)) :=
    (P.arrow_mk_iso_iff (Arrow.isoMk (T.mapIso e) (Iso.refl _) he_snd')).1 hP_x
  have : Surjective (T.map s) := hq_surj.property g (qrep.fst g) s (qrep.isPullback g)
  have : Etale (T.map s) := hq_etale.property g (qrep.fst g) s (qrep.isPullback g)
  have hPcanonical : P (pullback.snd (T.map w) (T.map s)) := by
    rwa [← P.cancel_left_of_respectsIso (hzC.map T).isoPullback.hom,
      (hzC.map T).isoPullback_hom_snd]
  refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd (P := P)
    (Scheme.Hom.singleton_mem_fppfPrecoverage (T.map s)) (f := T.map w)).mpr ?_
  rintro _ _ _ ⟨⟩
  exact hPcanonical

end AlgebraicGeometry

end
