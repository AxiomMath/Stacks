module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubfunctorDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# The pieces of a coproduct of algebraic spaces are open and closed subspaces

Let `P` be a coproduct of a family of algebraic spaces `F i` over a scheme `S`, presented by a
colimit cofan with legs `ι i`. The range of a leg is a subfunctor of `P`, and this file proves
that it is an *open and closed subspace* of `P` in the sense of Stacks 02YU: it is an algebraic
space over `S`, and its inclusion is both an open immersion and a closed immersion of algebraic
spaces.

Together with `AlgebraicGeometry.Sheaf.sheafify_sup_range_eq_top_of_isColimit_cofan` and
`AlgebraicGeometry.Sheaf.range_inf_range_eq_sheafify_bot` this turns a two-piece coproduct
presentation of an algebraic space into the open-and-closed subfunctor data in which Stacks
082H and Stacks 0ADU phrase the decomposition `U ×_Y X = W ⨿ V`.

## Main definitions

No new definitions are introduced.

## Main results

* `CategoryTheory.Subfunctor.isPullback_yoneda_of_forall_exists`: a subobject of an object of
  the site which carries a section of a subfunctor `G` of `F`, and through which every morphism
  carrying that section factors, presents the base change of `G.ι` along the section.
* `AlgebraicGeometry.Sheaf.exists_isPullback_range_cofan_inj`: every representable base change
  of the inclusion of the range of a leg is presented by an open subobject of the test object
  whose image is in addition closed.
* `AlgebraicGeometry.Space.isOpenSubspace_range_cofan_inj` and
  `AlgebraicGeometry.Space.isClosedSubspace_range_cofan_inj`: the range of a leg is an open
  subspace and a closed subspace of the coproduct.
* `AlgebraicGeometry.Sheaf.exists_clopen_subspace_decomposition_of_isColimit_cofan`: the
  two-piece form, collecting the four subspace conditions and the two lattice identities.
* `AlgebraicGeometry.Space.isFinite_isIso_comp` and
  `AlgebraicGeometry.Space.pointsMap_range_ι_comp`: finiteness of a morphism of algebraic
  spaces is unchanged by precomposition with an isomorphism, and the map on points of a
  composite is computed through the range factorisation of its first factor. These are
  general, and are stated for any presheaves on the site; neither mentions a coproduct.

## Implementation notes

The geometric input is `AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan`:
a section `x` of `P` over an object `W` of the site decomposes `W` into pairwise disjoint open
subobjects `W' i` covering `W`, the `i`-th of which is universal among the objects over `W` on
which `x` comes from `F i`. Two things are extracted from it.

First, that universal property is exactly a cartesian square: the base change of the inclusion
of the range of `ι i` along `x` is `W' i`. This is `Subfunctor.isPullback_yoneda_of_forall_exists`,
proved pointwise — the fibre of the square over an object `T` of the site is the set of
morphisms `T ⟶ W` whose restriction of `x` lies in the subfunctor, and the universal property
says `W' i` represents it, injectivity of the factorisation coming from `W' i ⟶ W` being a
monomorphism. Representability with the open-immersion property then follows through
`CategoryTheory.MorphismProperty.relative.of_exists`, which asks for *one* represented pullback
per test morphism.

Second, closedness. The image of `W' i₀` is the complement of the union of the images of the
other pieces: the pieces cover, so a point outside the image of `W' i₀` is in the image of some
other piece, and they are disjoint, so no point of another piece is in the image of `W' i₀`.
That union is open, so the image of `W' i₀` is closed, and an open immersion with closed image is
a closed immersion (`AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion`). The argument needs
no finiteness of the index type, since an arbitrary union of opens is open.

That the range of a leg is an algebraic space is the one place where the coproduct is used
through `AlgebraicGeometry.Sheaf.mono_cofan_inj_bigFppfOver`: a leg is a monomorphism, so the
map from its source onto its range is an isomorphism.

That same isomorphism carries data stated for the legs of the cofan over to the subfunctors:
finiteness transfers because precomposition with an isomorphism does not change the affine
representable base changes, and conditions on points transfer because the map on points induced
by an isomorphism is surjective.

Nothing here carries a Stacks tag, for the same reason as in
`StacksFrontier.AlgebraicGeometry.Spaces.ClopenSubfunctorDecomposition`: Stacks 082H, 0ADU and
02WO assert the *existence* of such a decomposition, which is not proved here, and these are the
properties its conclusion is phrased with.

A coproduct presentation is in any case not the datum the source produces. Stacks 082H obtains
the piece `V` as the image of a scheme étale onto it and finite over the base, so what the source
constructs is a clopen *set of points*, and the decomposition is deduced from that in
`StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition`. A coproduct presentation of
`U ×_Y X` is differently shaped and strictly stronger, so assuming one as a hypothesis does not
discharge any part of Stacks 082H; that is the route to the decomposition, and only the
subspace properties of the pieces are taken from here.

## References

* [Stacks Project, Tag 02WO](https://stacks.math.columbia.edu/tag/02WO)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ConcreteCategory Opposite

universe w u

namespace CategoryTheory.Subfunctor

/-- **A universal subobject carrying a section presents the base change of a subfunctor.**
Let `G` be a subfunctor of a presheaf of types `F`, let `x` be a section of `F` over `W`, and
let `p : W₀ ⟶ W` be a monomorphism such that the restriction of `x` to `W₀` lies in `G` and
every morphism to `W` along which `x` restricts into `G` factors through `p`. Then the square
formed by `p` and the section of `G` over `W₀` is cartesian over `G.ι` and `x`.

The square is tested pointwise: over an object `T`, a morphism `T ⟶ W` together with a section
of `G` over `T` agreeing with the restriction of `x` is the same thing as a morphism `T ⟶ W`
along which `x` restricts into `G`, and the hypotheses say exactly that `p` represents those —
surjectively by the factorisation property, injectively because `p` is a monomorphism. -/
theorem isPullback_yoneda_of_forall_exists {C : Type u} [Category.{w} C]
    {F : Cᵒᵖ ⥤ Type w} (G : Subfunctor F) {W W₀ : C} (p : W₀ ⟶ W) [Mono p]
    (x : F.obj (op W)) (y : G.toFunctor.obj (op W₀)) (hy : (y : F.obj (op W₀)) = F.map p.op x)
    (huniv : ∀ (T : C) (t : T ⟶ W), F.map t.op x ∈ G.obj (op T) →
      ∃ t' : T ⟶ W₀, t' ≫ p = t) :
    IsPullback (yonedaEquiv.symm y) (yoneda.map p) G.ι (yonedaEquiv.symm x) := by
  classical
  have hcomm : yonedaEquiv.symm y ≫ G.ι = yoneda.map p ≫ yonedaEquiv.symm x := by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_left, ← hy]
    simp
  refine IsPullback.of_isLimit' (CommSq.mk hcomm) ?_
  have key : ∀ (s : PullbackCone G.ι (yonedaEquiv.symm x)) (T : Cᵒᵖ) (e : s.pt.obj T),
      (s.fst.app T e).val = F.map (s.snd.app T e).op x := by
    intro s T e
    have h := congrArg (fun n : s.pt ⟶ F => n.app T e) s.condition
    simpa using h
  have hmem : ∀ (s : PullbackCone G.ι (yonedaEquiv.symm x)) (T : Cᵒᵖ) (e : s.pt.obj T),
      F.map (s.snd.app T e).op x ∈ G.obj (op T.unop) := by
    intro s T e
    rw [← key s T e]
    exact (s.fst.app T e).2
  have hfac : ∀ (s : PullbackCone G.ι (yonedaEquiv.symm x)) (T : Cᵒᵖ) (e : s.pt.obj T),
      (huniv T.unop (s.snd.app T e) (hmem s T e)).choose ≫ p = s.snd.app T e :=
    fun s T e => (huniv T.unop (s.snd.app T e) (hmem s T e)).choose_spec
  let L : ∀ s : PullbackCone G.ι (yonedaEquiv.symm x), s.pt ⟶ yoneda.obj W₀ := fun s =>
    { app := fun T => ↾fun e => (huniv T.unop (s.snd.app T e) (hmem s T e)).choose
      naturality := by
        intro T T' f
        refine hom_ext _ _ fun e => ?_
        refine (cancel_mono p).1 ?_
        simp only [comp_apply, TypeCat.ofHom_apply, yoneda_obj_map]
        rw [hfac s T' ((s.pt.map f) e), Category.assoc, hfac s T e]
        simp }
  have hL : ∀ (s : PullbackCone G.ι (yonedaEquiv.symm x)) (T : Cᵒᵖ) (e : s.pt.obj T),
      (L s).app T e ≫ p = s.snd.app T e := fun s T e => hfac s T e
  have hfr : ∀ s : PullbackCone G.ι (yonedaEquiv.symm x), L s ≫ yoneda.map p = s.snd := by
    intro s
    refine NatTrans.ext (funext fun T => hom_ext _ _ fun e => ?_)
    simpa using hL s T e
  have hfl : ∀ s : PullbackCone G.ι (yonedaEquiv.symm x),
      L s ≫ yonedaEquiv.symm y = s.fst := by
    intro s
    refine (cancel_mono G.ι).1 ?_
    rw [Category.assoc, hcomm, ← Category.assoc, hfr s]
    exact s.condition.symm
  refine PullbackCone.IsLimit.mk hcomm L hfl hfr fun s m _ hm₂ => ?_
  refine NatTrans.ext (funext fun T => hom_ext _ _ fun e => ?_)
  refine (cancel_mono p).1 ?_
  rw [hL s T e]
  have h := congrArg (fun n : s.pt ⟶ yoneda.obj W => n.app T e) hm₂
  simpa using h

/-- The inclusion of the range of a monomorphism is the monomorphism itself, read through the
isomorphism onto its range. -/
theorem ι_eq_inv_toRange_comp {C : Type u} [Category.{w} C] {F F' : Cᵒᵖ ⥤ Type w}
    (m : F' ⟶ F) [Mono m] :
    (Subfunctor.range m).ι = inv (Subfunctor.toRange m) ≫ m := by
  rw [IsIso.eq_inv_comp]
  exact Subfunctor.toRange_ι m

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Pieces

variable {I : Type w} {F : I → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {P : Sheaf (BigFppfOver.topology B S hS) (Type u)}

/-- A leg of a coproduct cofan of sheaves on the big fppf site over `S` is a monomorphism of
the underlying presheaves. -/
theorem Sheaf.mono_hom_cofan_inj (ι : ∀ i, F i ⟶ P) (hP : IsColimit (Cofan.mk P ι)) (i₀ : I) :
    Mono (ι i₀).hom := by
  have : Mono (ι i₀) := Sheaf.mono_cofan_inj_bigFppfOver ι hP i₀
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  exact CategoryTheory.Sheaf.injective_app_of_mono (ι i₀) T.unop

/-- **Every representable base change of the inclusion of a piece of a coproduct is an open
subobject with closed image.** For a coproduct cofan of sheaves on the big fppf site over `S`
with legs `ι i`, a leg `i₀` and a morphism `t` from a representable presheaf into the vertex,
the base change of the inclusion of the range of `ι i₀` along `t` is represented by an object
`W₀` of the site whose structure morphism is an open immersion with closed image.

The object is the piece supplied by
`AlgebraicGeometry.Sheaf.exists_clopen_decomposition_of_isColimit_cofan`; its universal property
is turned into a cartesian square by
`CategoryTheory.Subfunctor.isPullback_yoneda_of_forall_exists`, and its image is closed because
the complement is the union of the images of the other pieces. -/
theorem Sheaf.exists_isPullback_range_cofan_inj (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (i₀ : I) (W : BigFppfOver B S hS)
    (t : yoneda.obj W ⟶ P.obj) :
    ∃ (W₀ : BigFppfOver B S hS)
      (a : yoneda.obj W₀ ⟶ (Subfunctor.range (ι i₀).hom).toFunctor) (p : W₀ ⟶ W),
      IsPullback a (yoneda.map p) (Subfunctor.range (ι i₀).hom).ι t ∧
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p) ∧
      IsClosed (Set.range ((BigFppfOver.toScheme B S hS).map p)) := by
  classical
  obtain ⟨W', p, hoi, hsec, hdisj, hcov, huniv⟩ :=
    Sheaf.exists_clopen_decomposition_of_isColimit_cofan ι hP W (yonedaEquiv t)
  obtain ⟨z, hz⟩ := hsec i₀
  have hmono : Mono (p i₀) :=
    have := hoi i₀
    (BigFppfOver.toScheme B S hS).mono_of_mono_map (IsOpenImmersion.mono _)
  -- the image of the `i₀`-th piece is closed: its complement is the union of the others
  have hcompl : (Set.range ((BigFppfOver.toScheme B S hS).map (p i₀)))ᶜ
      = ⋃ i : {i : I // i ≠ i₀}, Set.range ((BigFppfOver.toScheme B S hS).map (p i.1)) := by
    refine Set.eq_of_subset_of_subset (fun v hv => ?_) (fun v hv => ?_)
    · obtain ⟨i, hi⟩ := hcov v
      exact Set.mem_iUnion.2 ⟨⟨i, fun h => hv (h ▸ hi)⟩, hi⟩
    · obtain ⟨⟨i, hi⟩, w, hw⟩ := Set.mem_iUnion.1 hv
      exact fun ⟨w₀, hw₀⟩ => hdisj i i₀ hi w w₀ (hw.trans hw₀.symm)
  have hclosed : IsClosed (Set.range ((BigFppfOver.toScheme B S hS).map (p i₀))) := by
    rw [← isOpen_compl_iff, hcompl]
    exact isOpen_iUnion fun i =>
      have := hoi i.1
      IsOpenImmersion.isOpen_range ((BigFppfOver.toScheme B S hS).map (p i.1))
  refine ⟨W' i₀, yonedaEquiv.symm ⟨P.obj.map (p i₀).op (yonedaEquiv t), z, hz⟩, p i₀, ?_,
    hoi i₀, hclosed⟩
  have hpb := Subfunctor.isPullback_yoneda_of_forall_exists (Subfunctor.range (ι i₀).hom)
    (p i₀) (yonedaEquiv t) ⟨P.obj.map (p i₀).op (yonedaEquiv t), z, hz⟩ rfl
    (fun T s hs => huniv i₀ T s hs)
  rwa [Equiv.symm_apply_apply] at hpb

/-- **A piece of a coproduct of algebraic spaces is an open subspace.** The range of a leg of a
coproduct cofan of sheaves on the big fppf site over `S` whose `i₀`-th member is an algebraic
space is an open subspace of the vertex in the sense of Stacks 02YU. -/
theorem Space.isOpenSubspace_range_cofan_inj (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (i₀ : I)
    (halg : IsAlgebraicSpace B S hS (F i₀).obj) :
    Space.IsOpenSubspace B S hS (Subfunctor.range (ι i₀).hom) := by
  have hmono : Mono (ι i₀).hom := Sheaf.mono_hom_cofan_inj ι hP i₀
  refine ⟨halg.of_iso (asIso (Subfunctor.toRange (ι i₀).hom)),
    MorphismProperty.relative.of_exists fun {W} t => ?_⟩
  obtain ⟨W₀, a, p, hpb, hoi, -⟩ := Sheaf.exists_isPullback_range_cofan_inj ι hP i₀ W t
  exact ⟨W₀, a, p, hpb, hoi⟩

/-- **A piece of a coproduct of algebraic spaces is a closed subspace.** The range of a leg of a
coproduct cofan of sheaves on the big fppf site over `S` whose `i₀`-th member is an algebraic
space is a closed subspace of the vertex in the sense of Stacks 02YU.

Closedness comes from the pieces being disjoint and covering, so that the image of one piece in
a representable base change is the complement of the union of the images of the others. -/
theorem Space.isClosedSubspace_range_cofan_inj (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (i₀ : I)
    (halg : IsAlgebraicSpace B S hS (F i₀).obj) :
    Space.IsClosedSubspace B S hS (Subfunctor.range (ι i₀).hom) := by
  have hmono : Mono (ι i₀).hom := Sheaf.mono_hom_cofan_inj ι hP i₀
  have hRI : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
    MorphismProperty.RespectsIso.inverseImage _ _
  refine ⟨halg.of_iso (asIso (Subfunctor.toRange (ι i₀).hom)),
    MorphismProperty.relative.of_exists fun {W} t => ?_⟩
  obtain ⟨W₀, a, p, hpb, hoi, hclosed⟩ := Sheaf.exists_isPullback_range_cofan_inj ι hP i₀ W t
  have := hoi
  exact ⟨W₀, a, p, hpb, IsClosedImmersion.of_isPreimmersion _ hclosed⟩

end Pieces

/-- **A two-piece coproduct presentation of an algebraic space is a decomposition into
complementary open-and-closed subspaces.** If an algebraic space `P` over `S` is the coproduct
of a `Bool`-indexed family of algebraic spaces, then the ranges of the two legs are open and
closed subspaces of `P` whose join sheafifies to the whole of `P` and whose meet is the
sheafification of the bottom subfunctor.

This is the shape in which Stacks 082H and Stacks 0ADU state the conclusion
`U ×_Y X = W ⨿ V`. -/
theorem Sheaf.exists_clopen_subspace_decomposition_of_isColimit_cofan
    {F : Bool → Sheaf (BigFppfOver.topology B S hS) (Type u)}
    {P : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ i, F i ⟶ P)
    (hP : IsColimit (Cofan.mk P ι)) (halg : ∀ i, IsAlgebraicSpace B S hS (F i).obj) :
    Space.IsOpenSubspace B S hS (Subfunctor.range (ι false).hom) ∧
    Space.IsClosedSubspace B S hS (Subfunctor.range (ι false).hom) ∧
    Space.IsOpenSubspace B S hS (Subfunctor.range (ι true).hom) ∧
    Space.IsClosedSubspace B S hS (Subfunctor.range (ι true).hom) ∧
    (Subfunctor.range (ι false).hom ⊔ Subfunctor.range (ι true).hom).sheafify
      (BigFppfOver.topology B S hS) = ⊤ ∧
    Subfunctor.range (ι false).hom ⊓ Subfunctor.range (ι true).hom
      = (⊥ : Subfunctor P.obj).sheafify (BigFppfOver.topology B S hS) :=
  ⟨Space.isOpenSubspace_range_cofan_inj ι hP false (halg false),
    Space.isClosedSubspace_range_cofan_inj ι hP false (halg false),
    Space.isOpenSubspace_range_cofan_inj ι hP true (halg true),
    Space.isClosedSubspace_range_cofan_inj ι hP true (halg true),
    Sheaf.sheafify_sup_range_eq_top_of_isColimit_cofan ι hP,
    Sheaf.range_inf_range_eq_sheafify_bot ι hP (by simp)⟩

/-! ### Transfer along an isomorphism and along a range factorisation

The two lemmas below are general statements about morphisms of presheaves on the site: they
say nothing about coproducts. `AlgebraicGeometry.Space.isFinite_isIso_comp` is the only
permanence lemma of `AlgebraicGeometry.Space.IsFinite` under precomposition with an
isomorphism. The companion fact that the map on points of an isomorphism is surjective is
`AlgebraicGeometry.Space.pointsMap_surjective_of_isIso`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Points.lean`. -/

section Transfer

variable {F' G' Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Finiteness of a morphism of algebraic spaces is inherited by its precomposition with an
isomorphism: an affine representable base change of the one is an affine representable base
change of the other, read through the isomorphism. -/
theorem Space.isFinite_isIso_comp {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F' ⟶ X)
    [IsIso e] {f : X ⟶ G'} (hf : Space.IsFinite B S hS f) :
    Space.IsFinite B S hS (e ≫ f) := by
  intro U hU ξ
  obtain ⟨V, p, i, hV, hfin, hpb⟩ := hf U hU ξ
  exact ⟨V, p, i ≫ inv e, hV, hfin,
    hpb.of_iso (Iso.refl _) (asIso e).symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp) (by simp)⟩

/-- A point of the range of a morphism, composed with a further morphism, is computed from any
preimage of it in the source. -/
theorem Space.pointsMap_range_ι_comp (m : F' ⟶ G') (k : G' ⟶ Z)
    (v₀ : Space.points B S hS F') :
    Space.pointsMap B S hS F' (m ≫ k) v₀
      = Space.pointsMap B S hS (Subfunctor.range m).toFunctor ((Subfunctor.range m).ι ≫ k)
          (Space.pointsMap B S hS F' (Subfunctor.toRange m) v₀) := by
  conv_lhs => rw [← Subfunctor.toRange_ι m]
  rw [Category.assoc, Space.pointsMap_comp_apply B S hS]

end Transfer

end AlgebraicGeometry

end
