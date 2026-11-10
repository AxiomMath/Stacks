module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Size.FlatSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# The size of a representable open subspace of an algebraic space

An algebraic space `X` over a scheme `S` is presented by a surjective étale atlas
`a : yoneda.obj U ⟶ X`, and this file bounds the size of *every* object of the big fppf site
which represents an open subspace of `X` by a cardinal built from `U` alone: the represented
fibre product `U ×_X V` receives an open immersion to `U` and a surjective étale morphism to `V`,
and this gives the bounds `size V ≤ 2 ^ 2 ^ size U` and `size V ≤ max (2 ^ #U) (2 ^ size U)`.

## Main results

* `AlgebraicGeometry.Space.exists_openImmersion_surjective_etale_of_atlas`: the base change of a
  surjective étale atlas along a representable open subspace is an open of the atlas mapping
  onto the representing object by a surjective étale morphism.
* `AlgebraicGeometry.Space.size_le_two_pow_two_pow_size_of_atlas`: `size V ≤ 2 ^ 2 ^ size U`.
* `AlgebraicGeometry.Space.size_le_of_isOpenImmersion_of_atlas`:
  `size V ≤ max (2 ^ #U) (2 ^ size U)`.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
-/

@[expose] public section

open CategoryTheory Cardinal

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Base change of the atlas along a representable open subspace.** Let `a : yoneda.obj U ⟶ X`
be a surjective étale atlas of a presheaf `X` on the big fppf site of `S`, and let
`g : yoneda.obj V ⟶ X` be an open immersion from a representable presheaf. Then there is an
object `W` of the site, an *open immersion* `W ⟶ U` of schemes and a *surjective étale*
morphism `W ⟶ V` of schemes. -/
theorem exists_openImmersion_surjective_etale_of_atlas
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X}
    (hsurj : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ X} (hg : IsOpenImmersion B S hS g) :
    ∃ (W : BigFppfOver B S hS) (j : W ⟶ U) (p : W ⟶ V),
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
        _root_.AlgebraicGeometry.Surjective ((BigFppfOver.toScheme B S hS).map p) ∧
        _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map p) := by
  have hbc := MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) (F := yoneda)
  have hsq := hsurj.rep.isPullback g
  refine ⟨hsurj.rep.pullback g, hsurj.rep.fst' g, hsurj.rep.snd g, ?_,
    hsurj.property_snd g, hetale.property g (hsurj.rep.fst g) (hsurj.rep.snd g) hsq⟩
  refine MorphismProperty.of_relative_map (P := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)) (F := yoneda) ?_
  change IsOpenImmersion B S hS (yoneda.map (hsurj.rep.fst' g))
  rw [Functor.relativelyRepresentable.map_fst']
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hg

/-- **The size of a scheme representing an open subspace is bounded in terms of the atlas
alone.** Let `a : yoneda.obj U ⟶ X` be a surjective étale atlas of a presheaf `X` on the big fppf
site of `S`, and let `g : yoneda.obj V ⟶ X` be an open immersion from a representable presheaf.
Then `size V ≤ 2 ^ 2 ^ size U`. -/
theorem size_le_two_pow_two_pow_size_of_atlas {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} {a : yoneda.obj U ⟶ X}
    (hsurj : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Surjective.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.Etale.{u} :
      MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf a)
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ X} (hg : IsOpenImmersion B S hS g) :
    ((BigFppfOver.toScheme B S hS).obj V).size ≤
      (2 : Cardinal.{u}) ^ (2 : Cardinal.{u}) ^
        ((BigFppfOver.toScheme B S hS).obj U).size := by
  obtain ⟨W, j, p, _, _, _⟩ :=
    exists_openImmersion_surjective_etale_of_atlas B S hS hsurj hetale hg
  exact (Scheme.size_le_two_pow_two_pow_size_of_flat_of_surjective
    ((BigFppfOver.toScheme B S hS).map p)).trans <| power_le_power_left two_ne_zero <|
      power_le_power_left two_ne_zero <|
        Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map j)

/-- **An open subspace of an algebraic space is bounded by the atlas.** Let `X` be a presheaf on
the big fppf category over `S` with a surjective étale chart `a : yoneda.obj U ⟶ X`, and let
`g : yoneda.obj V ⟶ X` be an open immersion of algebraic spaces with `V` an object of the site.
Then `size V ≤ max (2 ^ #U) (2 ^ size U)`. -/
theorem size_le_of_isOpenImmersion_of_atlas
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : BigFppfOver B S hS}
    {a : yoneda.obj U ⟶ X}
    (hsurj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hetale : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    {g : yoneda.obj V ⟶ X} (hg : IsOpenImmersion B S hS g) :
    ((BigFppfOver.toScheme B S hS).obj V).size ≤
      max (2 ^ #((BigFppfOver.toScheme B S hS).obj U : Type u))
        (2 ^ ((BigFppfOver.toScheme B S hS).obj U).size) := by
  obtain ⟨W, j, p, _, _, _⟩ :=
    exists_openImmersion_surjective_etale_of_atlas B S hS hsurj hetale hg
  refine (Scheme.size_le_of_flat_of_surjective
    ((BigFppfOver.toScheme B S hS).map p)).trans (max_le_max ?_ ?_)
  · exact power_le_power_left two_ne_zero
      (mk_le_of_injective ((BigFppfOver.toScheme B S hS).map j).injective)
  · exact power_le_power_left two_ne_zero
      (Scheme.size_le_of_isOpenImmersion ((BigFppfOver.toScheme B S hS).map j))

end AlgebraicGeometry.Space
