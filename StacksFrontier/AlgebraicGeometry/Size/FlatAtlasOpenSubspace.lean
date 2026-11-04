module

public import StacksFrontier.AlgebraicGeometry.Size.AtlasOpenSubspace

/-!
# The size of a representable open subspace of a sheaf with a flat chart

`StacksFrontier.AlgebraicGeometry.Size.AtlasOpenSubspace` bounds the size of every object of the big
fppf site representing an open subspace of a presheaf `X` which carries a *surjective étale*
chart `a : yoneda.obj U ⟶ X`, by a cardinal built from `U` alone. This file records that
étaleness is not used: the same bound holds for a surjective *flat* chart, and with the same
proof.

That matters because a descent datum along a covering sieve of the big fppf site produces a flat
chart and not an étale one. Over an affine base object
`AlgebraicGeometry.Space.coveringSieveBody_affineBase_of_affineFlatSource` replaces the covering
sieve by a single surjective flat morphism of finite presentation of affines, whose base change
is a chart of the descended sheaf; the étale bound does not apply to it, this one does.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_openImmersion_surjective_flat_of_atlas`: the base change of a
  surjective flat chart along a representable open subspace is an open of the chart mapping onto
  the representing object by a surjective flat morphism.
* `AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_flatAtlas`:
  `size V ≤ 2 ^ 2 ^ size U`.
* `AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_flatAtlas`:
  `size V ≤ max (2 ^ #U) (2 ^ size U)`.

## Implementation notes

The three proofs are those of
`AlgebraicGeometry.Space.exists_openImmersion_surjective_etale_of_atlas`,
`AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas` and
`AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas` with `AlgebraicGeometry.Etale`
replaced by `AlgebraicGeometry.Flat` throughout. Nothing else changes, because the only use
those proofs make of étaleness of the base-changed chart is to feed
`AlgebraicGeometry.Scheme.size_le_of_flat_of_surjective` and
`AlgebraicGeometry.Scheme.size_le_two_pow_two_pow_size_of_flat_of_surjective`, both of which ask
only for flatness and surjectivity. The étale statements are kept: they are what the
surjective-étale descent predicate consumes, and an étale chart is the usual case.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Base change of a flat chart along a representable open subspace.** Let
`a : yoneda.obj U ⟶ X` be a chart of a presheaf `X` on the big fppf site of `S` which is
surjective and flat after every represented base change, and let `g : yoneda.obj V ⟶ X` be an
open immersion from a representable presheaf. Then there is an object `W` of the site, an *open
immersion* `W ⟶ U` of schemes and a *surjective flat* morphism `W ⟶ V` of schemes.

This is `AlgebraicGeometry.Space.exists_openImmersion_surjective_etale_of_atlas` with étaleness
weakened to flatness; `W` is again the represented fibre product `U ×_X V`. -/
theorem exists_openImmersion_surjective_flat_of_atlas
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X}
    (hsurj : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hflat : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Flat.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ X} (hg : IsOpenImmersion B S hS g) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ U) (p : W ⟶ V),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
        _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map p) ∧
        _root_.AlgebraicGeometry.Flat ((BigFppfOver.toScheme B S hS).map p) := by
  have hbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have hsq := hsurj.rep.isPullback g
  refine ⟨hsurj.rep.pullback g, hsurj.rep.fst' g, hsurj.rep.snd g, ?_,
    hsurj.property_snd g, hflat.property g (hsurj.rep.fst g) (hsurj.rep.snd g) hsq⟩
  refine MorphismProperty.of_relative_map (P := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)) (F := yoneda) ?_
  show IsOpenImmersion B S hS (yoneda.map (hsurj.rep.fst' g))
  rw [Functor.relativelyRepresentable.map_fst']
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hg

/-- **The size of a scheme representing an open subspace of a presheaf with a surjective flat
chart is bounded in terms of the chart alone:** `size V ≤ 2 ^ 2 ^ size U`.

This is `AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas` with étaleness of the
chart weakened to flatness. -/
theorem size_le_two_pow_two_pow_size_of_flatAtlas {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X}
    (hsurj : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hflat : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Flat.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ X} (hg : IsOpenImmersion B S hS g) :
    ((BigFppfOver.toScheme B S hS).obj V).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        ((BigFppfOver.toScheme B S hS).obj U).size := by
  obtain ⟨W, j, p, hj, hps, hpf⟩ :=
    exists_openImmersion_surjective_flat_of_atlas B S hS hsurj hflat hg
  refine (Scheme.size_le_two_pow_two_pow_size_of_flat_of_surjective
    ((BigFppfOver.toScheme B S hS).map p)).trans ?_
  exact Cardinal.power_le_power_left two_ne_zero (Cardinal.power_le_power_left two_ne_zero
    (Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map j)))

/-- **An open subspace of a presheaf with a surjective flat chart is bounded by the chart:**
`size V ≤ max (2 ^ #U) (2 ^ size U)`.

This is `AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas` with étaleness of the
chart weakened to flatness. The right-hand side does not mention `V`, so it bounds every open
subspace of `X` represented by an object of the site, uniformly. -/
theorem size_le_of_isOpenImmersion_of_flatAtlas
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ X}
    (hsurj : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hflat : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Flat.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    {g : yoneda.obj V ⟶ X} (hg : IsOpenImmersion B S hS g) :
    ((BigFppfOver.toScheme B S hS).obj V).size ≤
      max (2 ^ #((BigFppfOver.toScheme B S hS).obj U : Type u))
        (2 ^ ((BigFppfOver.toScheme B S hS).obj U).size) := by
  obtain ⟨W, j, p, hj, hps, hpf⟩ :=
    exists_openImmersion_surjective_flat_of_atlas B S hS hsurj hflat hg
  refine (Scheme.size_le_of_flat_of_surjective
    ((BigFppfOver.toScheme B S hS).map p)).trans (max_le_max ?_ ?_)
  · exact power_le_power_left two_ne_zero
      (mk_le_of_injective ((BigFppfOver.toScheme B S hS).map j).injective)
  · exact power_le_power_left two_ne_zero
      (Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map j))

end AlgebraicGeometry.Space

end
