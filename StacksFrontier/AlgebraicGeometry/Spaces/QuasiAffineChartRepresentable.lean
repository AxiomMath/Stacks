module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage

/-!
# Representability of an algebraic space quasi-affine over a chart

Let `f : X ⟶ yoneda.obj a` be a morphism from an algebraic space over `S` to an object of the
big fppf site, and let `q : c ⟶ a` be a surjective étale morphism of the site. If the base
change `c ×_a X` is represented by an object of the site which is quasi-affine over `c`, then
`X` is itself representable and `f` is quasi-affine.

This is the descent step: the one hypothesis the statement rests on is effective descent of
quasi-affine morphisms along the surjective étale morphisms of the site, which is
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom`, and that is
available with nothing left open. The implication out of the third condition of Stacks 03WM —
`AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_surjectiveEtaleChart` — therefore applies
outright, and representability of `X` follows from relative representability of `f` over the
representable target by Stacks 03KC.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_surjectiveEtaleChart_of_isAlgebraicSpace`:
  `AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_surjectiveEtaleChart` with its hypothesis
  `hdesc` discharged.
* `AlgebraicGeometry.Space.isRepresentable_isQuasiAffineHom_of_surjectiveEtaleChart`: the shape in
  which the descent step is used, with the chart presented as a morphism `q : c ⟶ a` of the site
  rather than as a morphism of sheaves: `X` is representable and `f` is quasi-affine.

## Implementation notes

The two hypotheses `hs` and `he` of
`AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_surjectiveEtaleChart` ask for surjectivity
and étaleness of the chart in the relatively representable sense. For a chart of the form
`yoneda.map q` these are equivalent to the corresponding properties of the underlying morphism of
schemes, by `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`, both properties
being stable under base change; that equivalence is what lets the second result below take the
hypotheses on `(BigFppfOver.toScheme B S hS).map q` directly.

No Stacks tag is carried. The statements are implications between conditions of Stacks 03WM
together with Stacks 03KC, and the tag 03WM is carried by
`AlgebraicGeometry.Space.isQuasiAffineHom_tfae_etaleChart_of_isAlgebraicSpace` of
`StacksFrontier.AlgebraicGeometry.Spaces.QuasiAffineTfaeComplete`. The hypothesis `e` below assumes
the representability of the base change outright, which the tag's third condition instead
derives; that step is
`AlgebraicGeometry.Space.exists_representing_isQuasiAffineHom_of_pullback_fst`.

## References

* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
* [Stacks Project, Tag 03KC](https://stacks.math.columbia.edu/tag/03KC)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 03WM, (3) implies (1), with nothing left open.** This is
`AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_surjectiveEtaleChart` with its hypothesis
`hdesc` — the geometric input of Stacks 03I2 at the quasi-affine morphisms, for which the source
cites Stacks 02L7 and Stacks 0247 — discharged by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom`, and with base
change stability of quasi-affineness supplied by the instance
`AlgebraicGeometry.isQuasiAffineHom_isStableUnderBaseChange`.

As with the conditional form, the tag 03WM is not carried here: the hypothesis `e` assumes the
base change of `f` to the chart to be representable, which the tag's third condition derives. -/
theorem presheaf_isQuasiAffineHom_of_surjectiveEtaleChart_of_isAlgebraicSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {V W : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y} (e : yoneda.obj W ≅ pullback g f)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hq : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (e.hom ≫ pullback.fst g f)))) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_isQuasiAffineHom_of_surjectiveEtaleChart inferInstance
    (isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom B S hS) hX hY e hs he hq

/-- **The descent step.** Let `f : X ⟶ yoneda.obj a` be a morphism from an algebraic space over
`S` to an object of the big fppf site, let `q : c ⟶ a` be a morphism of the site whose underlying
morphism of schemes is surjective and étale, and suppose the base change `c ×_a X` is represented
by an object `W` of the site whose projection to `c` is a quasi-affine morphism of schemes. Then
`X` is representable and `f` is quasi-affine.

Quasi-affineness of `f` and relative representability are
`AlgebraicGeometry.Space.presheaf_isQuasiAffineHom_of_surjectiveEtaleChart_of_isAlgebraicSpace`,
the surjectivity and étaleness of the chart being transported to the relatively representable
form by `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff`. Representability of
`X` is then Stacks 03KC, the target `yoneda.obj a` being representable. -/
theorem isRepresentable_isQuasiAffineHom_of_surjectiveEtaleChart
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {a c W : BigFppfOver B S hS} {f : X ⟶ yoneda.obj a} {q : c ⟶ a}
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    (e : yoneda.obj W ≅ pullback (yoneda.map q) f)
    (hq : _root_.AlgebraicGeometry.IsQuasiAffineHom
      ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (e.hom ≫ pullback.fst (yoneda.map q) f)))) :
    X.IsRepresentable ∧ IsQuasiAffineHom B S hS f := by
  have hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs
  have he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map q) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe
  have hf : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsQuasiAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f :=
    presheaf_isQuasiAffineHom_of_surjectiveEtaleChart_of_isAlgebraicSpace hX
      (isAlgebraicSpace_yoneda B S hS a) e hs he hq
  exact ⟨Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable f hf.rep,
    isQuasiAffineHom_of_presheaf hf⟩

end AlgebraicGeometry.Space

end
