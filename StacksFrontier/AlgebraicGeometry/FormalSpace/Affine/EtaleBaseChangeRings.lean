module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.EtaleSite

/-!
# The coordinate rings of an étale base change of affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces over `S` which is representable by algebraic spaces and étale.
Stacks 0AKN represents the base change of `f` along a morphism to `Y` from the sheaf
represented by an object `U` of the site with affine underlying scheme by an object `V` of the
site with affine underlying scheme, and
`AlgebraicGeometry.FormalSpace.nonempty_affineEtaleBaseChange` shows that the projection
`V ⟶ U` is étale as a morphism of schemes. Since both underlying schemes are affine, étaleness
of that projection is a property of the single ring map it induces on global sections, and this
file records it in that form.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_etale_baseChange_of_isRepresentableEtale`: the
  base change is represented by an affine object of the site whose coordinate ring is an étale
  algebra over the coordinate ring of the test object.

## Implementation notes

This is the étale-descent-to-rings step required by the essential-surjectivity clause of
Stacks 0AN8, whose consumer in this library is
`AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf'`: that clause produces an étale
algebra over the ring presenting the target out of the étale algebras over the rings presenting
its thickening stages, and this is the statement that those algebras are étale.

Nothing is proved here beyond assembling two existing results. Representability by an affine
object of the site and étaleness of the projection are
`AlgebraicGeometry.FormalSpace.nonempty_affineEtaleBaseChange`, applied to the chart
`f : X ⟶ Y` bundled as an object of
`AlgebraicGeometry.FormalSpace.AffineEtaleFormalCharts B S hS Y`. Passing from étaleness of a
morphism of affine schemes to étaleness of the ring map on global sections is
`AlgebraicGeometry.HasRingHomProperty.appTop` for the morphism property
`AlgebraicGeometry.Etale`, whose associated property of ring maps is `RingHom.Etale`.

## References

* [Stacks Project, Tag 0AKN](https://stacks.math.columbia.edu/tag/0AKN)
* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
* [Stacks Project, Tag 0DEE](https://stacks.math.columbia.edu/tag/0DEE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The coordinate rings of an étale base change of affine formal algebraic spaces.** Let
`f : X ⟶ Y` be a morphism of affine formal algebraic spaces over `S` which is representable by
algebraic spaces and étale, let `U` be an object of the site whose underlying scheme is affine
and let `g` be a morphism to `Y` from the sheaf represented by `U`. Then the fibre product of
`f` and `g` is represented by an object `V` of the site whose underlying scheme is affine, and
the ring map `Γ(U, ⊤) ⟶ Γ(V, ⊤)` induced on global sections by the projection `V ⟶ U` is
étale.

This is the étale-descent-to-rings step required by the essential-surjectivity clause of
Stacks 0AN8; its consumer in this library is
`AlgebraicGeometry.FormalSpace.IsEssentiallySurjectiveSpf'`. Representability by an affine
object of the site is Stacks 0AKN and étaleness of the projection is
`AlgebraicGeometry.FormalSpace.nonempty_affineEtaleBaseChange`; both underlying schemes being
affine, étaleness of the projection is étaleness of the single ring map it induces on global
sections. -/
theorem exists_affine_etale_baseChange_of_isRepresentableEtale
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X)
    (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : IsRepresentableEtale B S hS f)
    (U : BigFppfOver B S hS) (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj U ⟶ Y) :
    ∃ (V : BigFppfOver B S hS)
      (p : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj V ⟶ X) (q : V ⟶ U),
      IsPullback p ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map q) f g ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        RingHom.Etale ((BigFppfOver.toScheme B S hS).map q).appTop.hom := by
  obtain ⟨d⟩ :=
    nonempty_affineEtaleBaseChange B S hS hY U hU g ⟨Over.mk f, hX, hf⟩
  refine ⟨d.obj, d.fst, d.proj, d.isPullback, d.isAffine, d.etale, ?_⟩
  -- both underlying schemes are affine, so étaleness of the projection is étaleness of the
  -- single ring map it induces on global sections
  have _ := hU
  have _ := d.isAffine
  exact HasRingHomProperty.appTop @Etale ((BigFppfOver.toScheme B S hS).map d.proj) d.etale

end AlgebraicGeometry.FormalSpace

end
