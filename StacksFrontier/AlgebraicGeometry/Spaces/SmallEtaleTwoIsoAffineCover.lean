module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleTwoIsoAffineChart

/-!
# From affine charts to a surjective chart

Stacks 04M6 is finished here.  The affine step
`AlgebraicGeometry.Space.exists_smallBaseChange_iso_projection_affine` gives the compatibility
of the chart isomorphism with the two cartesian projections over every *affine* étale scheme
chart of `Y`, while `AlgebraicGeometry.Space.eq_of_chartHom_projection` consumes it over a
*surjective* one.  The two are bridged by the affine coproduct atlas of Stacks 03FX: a
surjective étale chart `U` of `Y` whose underlying scheme is a disjoint union of affine charts
`W i`, each an open immersion into `U`.

Base change of charts along a morphism of charts is cartesian, so the base changes of the `W i`
form an open cover of the base change of `U`; naturality of the chart isomorphism transports the
affine compatibility to each member of that cover, and an equality of morphisms of schemes may
be checked on an open cover.

## Main results

* `AlgebraicGeometry.Space.isPullback_smallBaseChange_map`: base change of étale scheme charts
  along a morphism of charts is cartesian, as a square of schemes.
* `AlgebraicGeometry.Space.eq_of_twoIso_representable`: Stacks 04M6 for two *representable*
  morphisms.
* `AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso`: **Stacks 04M6.** Two
  morphisms of algebraic spaces over `S` whose morphisms of small étale ringed topoi are
  2-isomorphic are equal.

## References

* [Stacks Project, Tag 04M6](https://stacks.math.columbia.edu/tag/04M6)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- A point of the source of a cartesian square of schemes above a compatible pair of points of
the two middle objects. -/
theorem exists_preimage_of_isPullback {P A A' C : Scheme.{u}} {p₁ : P ⟶ A} {p₂ : P ⟶ A'}
    {q₁ : A ⟶ C} {q₂ : A' ⟶ C} (h : IsPullback p₁ p₂ q₁ q₂) (x : A) (y : A')
    (hxy : q₁ x = q₂ y) : ∃ z : P, p₁ z = x := by
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  exact ⟨h.isoPullback.inv w, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hw]⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Base change of étale scheme charts along a morphism of charts is cartesian.** For a
representable `b : X ⟶ Y` and a morphism `k : V ⟶ W` of étale scheme charts of `Y`, the square
formed by the two base-changed charts, their cartesian projections and `k` is a pullback square
of schemes.

Both the morphism and the projections are read off the two cartesian squares of Stacks 03G2
part (4) over `V` and over `W`; the square in question is the left half of their horizontal
pasting, so it is cartesian. -/
theorem isPullback_smallBaseChange_map (b : X ⟶ Y)
    (hb : yoneda.relativelyRepresentable b.hom) {V W : SmallEtale B S hS Y.1} (k : V ⟶ W) :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map ((smallBaseChange B S hS b hb).map k).hom.left)
      ((BigFppfOver.toScheme B S hS).map (hb.snd V.1.hom))
      ((BigFppfOver.toScheme B S hS).map (hb.snd W.1.hom))
      ((BigFppfOver.toScheme B S hS).map k.hom.left) := by
  have hw : yoneda.map ((smallBaseChange B S hS b hb).map k).hom.left ≫ hb.fst W.1.hom =
      hb.fst V.1.hom := CostructuredArrow.w ((smallBaseChange B S hS b hb).map k).hom
  have hk : yoneda.map k.hom.left ≫ W.1.hom = V.1.hom := CostructuredArrow.w k.hom
  have hp : yoneda.map ((smallBaseChange B S hS b hb).map k).hom.left ≫
        yoneda.map (hb.snd W.1.hom) =
      yoneda.map (hb.snd V.1.hom) ≫ yoneda.map k.hom.left :=
    (yoneda.map_comp _ _).symm.trans
      ((congrArg (fun q => yoneda.map q) (smallBaseChange_map_snd B S hS b hb k)).trans
        (yoneda.map_comp _ _))
  have hs : IsPullback
      (yoneda.map ((smallBaseChange B S hS b hb).map k).hom.left ≫ hb.fst W.1.hom)
      (yoneda.map (hb.snd V.1.hom)) b.hom (yoneda.map k.hom.left ≫ W.1.hom) := by
    rw [hw, hk]
    exact hb.isPullback V.1.hom
  exact (IsPullback.of_map_of_faithful yoneda
    (IsPullback.of_right hs hp (hb.isPullback W.1.hom))).map (BigFppfOver.toScheme B S hS)

/-- **Stacks 04M6 for a representable morphism.** Two *representable* morphisms `a, b : X ⟶ Y`
of algebraic spaces over `S` whose morphisms of small étale ringed topoi are 2-isomorphic are
equal. -/
theorem eq_of_twoIso_representable (a b : X ⟶ Y)
    (ha : yoneda.relativelyRepresentable a.hom) (hb : yoneda.relativelyRepresentable b.hom)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS a) (smallEtaleRingedToposHom B S hS b)) :
    a = b := by
  let := isContinuous_smallBaseChange B S hS a ha
  let := isContinuous_smallBaseChange B S hS b hb
  obtain ⟨e, hcompat⟩ := exists_smallBaseChange_iso_projection_affine B S hS a b ha hb t
  obtain ⟨U, f, I, W, j, eco, hsurj, hetale, haff, hι, hopen, hetj, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS Y.1 Y.property
  set UC : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk f, hetale⟩ with hUC
  set VC : I → SmallEtale B S hS Y.1 :=
    fun i => ⟨CostructuredArrow.mk (yoneda.map (j i) ≫ f), hetj i⟩ with hVC
  set kk : ∀ i, VC i ⟶ UC :=
    fun i => ObjectProperty.homMk (CostructuredArrow.homMk (j i) rfl) with hkk
  refine eq_of_chartHom_projection B S hS a b ha hb UC hsurj (e.hom.app UC) ?_
  have hpb := fun i => isPullback_smallBaseChange_map B S hS b hb (kk i)
  have hjsurj : ∀ z : (BigFppfOver.toScheme B S hS).obj U,
      ∃ (i : I) (y : (BigFppfOver.toScheme B S hS).obj (W i)),
        (BigFppfOver.toScheme B S hS).map (j i) y = z := by
    intro z
    obtain ⟨q, key⟩ : ∃ q, sigmaMk (fun i => (BigFppfOver.toScheme B S hS).obj (W i)) q =
        eco.inv z := ⟨_, Homeomorph.apply_symm_apply _ _⟩
    obtain ⟨i, y⟩ := q
    refine ⟨i, y, ?_⟩
    have h1 : Sigma.ι (fun i => (BigFppfOver.toScheme B S hS).obj (W i)) i y = eco.inv z := by
      rw [← sigmaMk_mk]
      exact key
    calc (BigFppfOver.toScheme B S hS).map (j i) y
        = (Sigma.ι (fun i => (BigFppfOver.toScheme B S hS).obj (W i)) i ≫ eco.hom) y := by
          rw [hι]
      _ = eco.hom (Sigma.ι (fun i => (BigFppfOver.toScheme B S hS).obj (W i)) i y) :=
          Scheme.Hom.comp_apply _ _ _
      _ = eco.hom (eco.inv z) := by rw [h1]
      _ = z := by rw [← Scheme.Hom.comp_apply, eco.inv_hom_id]; rfl
  have hnat : ∀ i, ((smallBaseChange B S hS b hb).map (kk i)).hom.left ≫
        (e.hom.app UC).hom.left =
      (e.hom.app (VC i)).hom.left ≫ ((smallBaseChange B S hS a ha).map (kk i)).hom.left :=
    fun i => congrArg (fun φ => φ.hom.left) (e.hom.naturality (kk i))
  have hA : ∀ i, ((smallBaseChange B S hS b hb).map (kk i)).hom.left ≫
        ((e.hom.app UC).hom.left ≫ ha.snd UC.1.hom) =
      ((smallBaseChange B S hS b hb).map (kk i)).hom.left ≫ hb.snd UC.1.hom := by
    intro i
    erw [← Category.assoc, hnat i, Category.assoc, smallBaseChange_map_snd B S hS a ha (kk i),
      ← Category.assoc, hcompat (VC i) (haff i), smallBaseChange_map_snd B S hS b hb (kk i)]
    rfl
  apply (BigFppfOver.toScheme B S hS).map_injective
  let 𝒰 : Scheme.OpenCover.{u} ((BigFppfOver.toScheme B S hS).obj
      ((smallBaseChange B S hS b hb).obj UC).1.left) :=
    Scheme.Cover.mkOfCovers I
      (fun i => (BigFppfOver.toScheme B S hS).obj
        ((smallBaseChange B S hS b hb).obj (VC i)).1.left)
      (fun i => (BigFppfOver.toScheme B S hS).map
        ((smallBaseChange B S hS b hb).map (kk i)).hom.left)
      (fun z => by
        obtain ⟨i, y, hy⟩ := hjsurj ((BigFppfOver.toScheme B S hS).map (hb.snd UC.1.hom) z)
        obtain ⟨w, hw⟩ := exists_preimage_of_isPullback (hpb i) z y hy.symm
        exact ⟨i, w, hw⟩)
      (fun i => MorphismProperty.IsStableUnderBaseChange.of_isPullback (hpb i).flip (hopen i))
  refine 𝒰.hom_ext _ _ fun i => ?_
  show (BigFppfOver.toScheme B S hS).map
        ((smallBaseChange B S hS b hb).map (kk i)).hom.left ≫
      (BigFppfOver.toScheme B S hS).map ((e.hom.app UC).hom.left ≫ ha.snd UC.1.hom) =
    (BigFppfOver.toScheme B S hS).map
        ((smallBaseChange B S hS b hb).map (kk i)).hom.left ≫
      (BigFppfOver.toScheme B S hS).map (hb.snd UC.1.hom)
  erw [← Functor.map_comp, ← Functor.map_comp, hA i]

/-- **Stacks 04M6.** Let `S` be a scheme and let `X, Y` be algebraic spaces over `S`. Two
morphisms `a, b : X ⟶ Y` of algebraic spaces over `S` for which there exists a 2-isomorphism
`(a_small, a^♯) ≅ (b_small, b^♯)` in the 2-category of ringed topoi are equal.

No representability is assumed: the general case is reduced to a scheme source by
`AlgebraicGeometry.Space.eq_of_twoIso_of_schemeSource`, where the two morphisms are
automatically representable because the diagonal of an algebraic space is. -/
@[stacks 04M6]
theorem eq_of_smallEtaleRingedToposHom_twoIso (a b : X ⟶ Y)
    (t : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS a) (smallEtaleRingedToposHom B S hS b)) :
    a = b :=
  eq_of_twoIso_of_schemeSource B S hS
    (fun _ Z a' b' t' => eq_of_twoIso_representable B S hS a' b'
      (relativelyRepresentable_of_isAlgebraicSpace B S hS Z.property a'.hom)
      (relativelyRepresentable_of_isAlgebraicSpace B S hS Z.property b'.hom) t') a b t

/-! ### The uniqueness half of Stacks 04KL over a base -/

/-- **The uniqueness half of Stacks 04KL over a base.** A morphism `ψ` of the small étale ringed
topoi of two algebraic spaces over `S` is 2-isomorphic to `(f_small, f♯)` for *at most one*
morphism `f : X ⟶ Y` of algebraic spaces over `S`.

Neither hypothesis of Stacks 04KL is needed: `ψ` is an arbitrary morphism of ringed topoi, not
assumed locally ringed, and no compatibility with structure morphisms to a further base is
assumed.  Two morphisms both 2-isomorphic to `ψ` are 2-isomorphic to each other, so this is
Stacks 04M6 — `AlgebraicGeometry.Space.eq_of_smallEtaleRingedToposHom_twoIso` — applied to the
composite of one 2-isomorphism with the inverse of the other.  This is the space-level analogue
of `AlgebraicGeometry.eq_of_twoIso_smallEtaleRingedToposHom`, which is the same clause of
Stacks 04I6 and Stacks 04I7 for schemes. -/
theorem eq_of_twoIso_smallEtaleRingedToposHom
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (a b : X ⟶ Y)
    (ta : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} ψ (smallEtaleRingedToposHom B S hS a))
    (tb : RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} ψ (smallEtaleRingedToposHom B S hS b)) :
    a = b :=
  eq_of_smallEtaleRingedToposHom_twoIso B S hS a b (ta.symm.trans tb)

add_to_stacks 04KL "the uniqueness clause over a base: at most one morphism of algebraic spaces
  over S induces a given morphism of the small étale ringed topoi. This is the faithfulness half
  of the asserted full faithfulness, and it needs neither of the theorem's hypotheses — not
  local ringedness of the morphism of topoi, and not 2-compatibility with structure morphisms to
  a further base"
  AlgebraicGeometry.Space.eq_of_twoIso_smallEtaleRingedToposHom

/-- **The existence half of Stacks 04KL over a base implies the whole of it.** If *some*
morphism `f : X ⟶ Y` of algebraic spaces over `S` has `(f_small, f♯)` 2-isomorphic to `ψ`, then
exactly one does.

So the uniqueness quantifier of Stacks 04KL — and of
`AlgebraicGeometry.Space.IsRecoveredFromSmallEtale`, which is that theorem over a base in the
form its consumers use — carries no content beyond Stacks 04M6, and the open part of the
theorem is purely the existence of `f`. -/
theorem existsUnique_of_exists_twoIso_smallEtaleRingedToposHom
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (h : ∃ f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} ψ
      (smallEtaleRingedToposHom B S hS f))) :
    ∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u} ψ
      (smallEtaleRingedToposHom B S hS f)) := by
  obtain ⟨f, ⟨tf⟩⟩ := h
  exact ⟨f, ⟨tf⟩, fun g ⟨tg⟩ => eq_of_twoIso_smallEtaleRingedToposHom B S hS ψ g f tg tf⟩

/-- `AlgebraicGeometry.Space.existsUnique_of_exists_twoIso_smallEtaleRingedToposHom` with the
2-isomorphism written in the other orientation, which is the one
`AlgebraicGeometry.Space.InducesSmallEtaleRingedToposHom` uses: a morphism of algebraic spaces
*induces* `ψ` when the morphism of small étale ringed topoi attached to it is 2-isomorphic
*to* `ψ`.  In that spelling too, existence upgrades to existence and uniqueness. -/
theorem existsUnique_of_exists_smallEtaleRingedToposHom_twoIso
    (ψ : RingedToposHom (smallEtaleRingedTopos B S hS X) (smallEtaleRingedTopos B S hS Y))
    (h : ∃ f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS f) ψ)) :
    ∃! f : X ⟶ Y, Nonempty (RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS f) ψ) := by
  obtain ⟨f, ⟨tf⟩⟩ := h
  exact ⟨f, ⟨tf⟩, fun g ⟨tg⟩ =>
    eq_of_twoIso_smallEtaleRingedToposHom B S hS ψ g f tg.symm tf.symm⟩

end Space

end AlgebraicGeometry

end
