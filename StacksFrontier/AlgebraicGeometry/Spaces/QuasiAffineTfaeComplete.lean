module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent

/-!
# The local criteria for a quasi-affine morphism of algebraic spaces

For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, the following are equivalent:
`f` is representable with quasi-affine represented base changes; `f` is quasi-affine in the sense
of Stacks 03WL; the base change of `f` along some surjective étale scheme chart of `Y` is
quasi-affine; and `f` is quasi-affine over the members of some Zariski covering of `Y`.

## Main results

* `AlgebraicGeometry.Space.exists_representing_isQuasiAffineHom_of_pullback_fst`: a quasi-affine
  base change of a morphism of algebraic spaces along a morphism from a representable presheaf
  is itself represented by an object of the site, with quasi-affine projection to it.
* `AlgebraicGeometry.Space.isQuasiAffineHom_tfae_etaleChart_of_isAlgebraicSpace`: the four
  conditions above are equivalent for a morphism of algebraic spaces over `S`.
* `AlgebraicGeometry.Space.isQuasiAffineHom_tfae_of_isAlgebraicSpace`: the same equivalence, with
  the third condition carrying a representing object for the base change.

## References

* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
* [Stacks Project, Tag 03WL](https://stacks.math.columbia.edu/tag/03WL)
* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the following four conditions
are equivalent: `f` is relatively representable and all of its represented base changes are
quasi-affine morphisms of schemes; `f` is quasi-affine in the sense of Stacks 03WL; there is a
surjective étale scheme chart of `Y` over which the base change of `f` is represented by an
object of the site, via an isomorphism `e`, with quasi-affine projection to that chart; and there
is a Zariski covering of `Y` over whose members `f` is quasi-affine. -/
theorem isQuasiAffineHom_tfae_of_isAlgebraicSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f,
      IsQuasiAffineHom B S hS f,
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y)
          (W : BigFppfOver B S hS)
          (e : yoneda.obj W ≅ pullback g f),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        _root_.AlgebraicGeometry.IsQuasiAffineHom
          ((BigFppfOver.toScheme B S hS).map
            (yoneda.preimage (e.hom ≫ pullback.fst g f)))),
      (∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsQuasiAffineHom B S hS (pullback.fst (U i).ι f))
    ] :=
  isQuasiAffineHom_tfae B S hS
    (isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom B S hS) hX hY f

/-- The base change of a morphism of algebraic spaces over `S` along a morphism from a
representable presheaf is representable as soon as it is quasi-affine in the sense of Stacks
03WL, and then its projection to the representing object is a quasi-affine morphism of schemes. -/
theorem exists_representing_isQuasiAffineHom_of_pullback_fst
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} {V : BigFppfOver B S hS}
    {g : yoneda.obj V ⟶ Y} (hq : IsQuasiAffineHom B S hS (pullback.fst g f)) :
    ∃ (W : BigFppfOver B S hS) (e : yoneda.obj W ≅ pullback g f),
      _root_.AlgebraicGeometry.IsQuasiAffineHom
        ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (e.hom ≫ pullback.fst g f))) := by
  have hpres := presheaf_isQuasiAffineHom_of_isQuasiAffineHom_of_isAlgebraicSpace B S hS
    (isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS V) hX hY)
    (isAlgebraicSpace_yoneda B S hS V) hq
  have : (pullback g f).IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _ hpres.rep
  refine ⟨_, (pullback g f).reprW, ?_⟩
  refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).1 ?_
  rw [Functor.map_preimage]
  exact MorphismProperty.RespectsIso.precomp _ _ _ hpres

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` the following four conditions
are equivalent: `f` is relatively representable and all of its represented base changes are
quasi-affine morphisms of schemes; `f` is quasi-affine in the sense of Stacks 03WL; the base
change of `f` along some surjective étale scheme chart of `Y` is quasi-affine; and there is a
Zariski covering of `Y` over whose members `f` is quasi-affine. -/
@[stacks 03WM]
theorem isQuasiAffineHom_tfae_etaleChart_of_isAlgebraicSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f,
      IsQuasiAffineHom B S hS f,
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsQuasiAffineHom B S hS (pullback.fst g f)),
      (∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsQuasiAffineHom B S hS (pullback.fst (U i).ι f))
    ] := by
  have H := isQuasiAffineHom_tfae_of_isAlgebraicSpace hX hY f
  tfae_have 1 → 2 := (H.out 1 2).1
  tfae_have 2 → 3 := by
    intro h
    obtain ⟨V, g, hs, he⟩ := hY.exists_atlas
    exact ⟨V, g, hs, he,
      IsQuasiAffineHom.of_isPullback (IsPullback.of_hasPullback g f).flip h⟩
  tfae_have 3 → 1 := by
    rintro ⟨V, g, hs, he, hq⟩
    obtain ⟨W, e, hW⟩ := exists_representing_isQuasiAffineHom_of_pullback_fst hX hY hq
    refine (H.out 3 1).1 ?_
    exact ⟨V, g, W, e, hs, he, hW⟩
  tfae_have 2 → 4 := (H.out 2 4).1
  tfae_have 4 → 1 := (H.out 4 1).1
  tfae_finish

end AlgebraicGeometry.Space

end
