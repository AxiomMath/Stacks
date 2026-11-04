module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcAffine
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete

/-!
# The five equivalent characterisations of an affine morphism of algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. Stacks 03WG characterises the affine
morphisms of algebraic spaces over `S` by five equivalent conditions, and
`AlgebraicGeometry.Space.isAffineHom_tfae` proves that equivalence from one named hypothesis:
effective descent for affine morphisms of schemes along the surjective étale morphisms of the
site, which is Stacks 03I2 for the class of affine morphisms. That hypothesis is available
outright, so this file records the equivalence unconditionally and carries the tag.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace`: **Stacks 03WG**, all five
  conditions and no hypothesis beyond the two algebraicity assumptions of the source.
* `AlgebraicGeometry.Space.presheaf_isAffineHom_iff`: **Stacks 03WE**, affineness of a
  representable morphism in the sense of Stacks 03HA is affineness of every base change to an
  affine object of the site, the test object ranging over *all* morphisms from an affine object.

## Implementation notes

The result is a corollary of two statements that already exist, and no geometry is redone here.

The descent hypothesis is discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`, proved in
`StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent` and reaching this file through
the imports below. Stacks 03I2 is not proved in general anywhere: what that theorem supplies is
its instance at the class of affine morphisms of schemes, which is all that Stacks 03WG consumes.
The hypothesis of `AlgebraicGeometry.Space.isAffineHom_tfae` is kept, so that the conditional
form stays available to callers that have a descent hypothesis of their own.

## References

* [Stacks Project, Tag 03HA](https://stacks.math.columbia.edu/tag/03HA)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03WE](https://stacks.math.columbia.edu/tag/03WE)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 03WG.** For a morphism `f : X ⟶ Y` of algebraic spaces over `S` the following are
equivalent: `f` is representable and affine as a morphism of presheaves; `f` is affine in the
sense of Stacks 03WF; for every affine object of the site étale over `Y` the base change of `f`
is represented by an affine object of the site; there is a surjective étale scheme chart of `Y`
along which the base change of `f` is affine; and there is a Zariski covering of `Y` over whose
members the base changes of `f` are affine.

This is `AlgebraicGeometry.Space.isAffineHom_tfae` with its descent hypothesis discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`. -/
@[stacks 03WG,
  stacks 03WE "items (1) and (2): affine as a representable morphism iff every base change to"]
theorem isAffineHom_tfae_of_isAlgebraicSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) :
    List.TFAE [
      (yoneda.relativelyRepresentable f ∧
        (MorphismProperty.inverseImage
          (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf f),
      IsAffineHom B S hS f,
      (∀ (V : BigAffineFppf B S hS)
        (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj V) ⟶ Y),
        IsEtale B S hS g →
          ∃ (W : BigAffineFppf B S hS)
            (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ X)
            (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
              (BigAffineFppf.inclusion B S hS).obj V),
            IsPullback p (yoneda.map q) f g),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧
        IsEtale B S hS g ∧
        IsAffineHom B S hS (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsAffineHom B S hS (pullback.snd f (U i).ι))] :=
  isAffineHom_tfae B S hS f hX hY
    (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS)

/-- **Stacks 03WE.** Let `f : X ⟶ Y` be a representable morphism of algebraic spaces over a
scheme `S`. Then `f` is affine in the sense of Stacks 03HA — every represented base change of
`f` is an affine morphism of schemes — if and only if for every affine object `Z` of the site
and every morphism `yoneda.obj Z ⟶ Y` the fibre product `X ×_Y Z` is represented by an affine
object of the site.

The right-hand side is `AlgebraicGeometry.Space.IsAffineHom`, Stacks 03WF, with its
abbreviation unfolded, so that the quantifier over the test object stands in the statement: it
ranges over *all* morphisms from an affine object of the site, not over the étale ones alone.
That is what separates it from condition (3) of
`AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace`, which is the same condition
restricted to the étale test morphisms.

The equivalence is the one between conditions (1) and (2) of that theorem, whose condition (1)
conjoins representability to the Stacks 03HA condition; representability is the hypothesis `hf`
of the source here, and `MorphismProperty.presheaf` carries it on the left anyway. -/
@[stacks 03WE]
theorem presheaf_isAffineHom_iff
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : yoneda.relativelyRepresentable f) :
    (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f ↔
      ∀ (Z : BigAffineFppf B S hS)
        (g : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z) ⟶ Y),
        ∃ (W : BigAffineFppf B S hS)
          (p : yoneda.obj ((BigAffineFppf.inclusion B S hS).obj W) ⟶ X)
          (q : (BigAffineFppf.inclusion B S hS).obj W ⟶
            (BigAffineFppf.inclusion B S hS).obj Z),
          IsPullback p (yoneda.map q) f g :=
  ⟨fun h => isAffineHom_of_presheaf h,
    fun h => ⟨hf, (presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS hX hY h).2.2⟩⟩

end AlgebraicGeometry.Space

end
