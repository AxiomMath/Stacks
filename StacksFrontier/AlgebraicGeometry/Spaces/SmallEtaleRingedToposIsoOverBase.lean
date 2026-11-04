module

public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ArbitraryBaseMain
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.ChartOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoLocallyRinged

/-!
# A morphism of algebraic spaces over a base inducing an isomorphism of small étale ringed topoi

Let `c : X ⟶ Y` be a morphism of algebraic spaces over an arbitrary scheme `S` whose morphism of
small étale ringed topoi `(c_small, c♯)` (Stacks 03G8) is an isomorphism of ringed topoi: its
direct image is an equivalence and `c♯ : 𝒪_Y ⟶ c_*𝒪_X` is an isomorphism.  Then `c` is an
isomorphism of algebraic spaces.

Over `ℤ` this is the last clause of Stacks 05YZ
(`AlgebraicGeometry.Space.existsUnique_spaceHom_twoIso_of_smallEtaleRingedToposIso`); the proof
there goes through Stacks 04KL over a terminal base.  Over an arbitrary base the recovery of a
morphism from a locally ringed morphism of small étale ringed topoi needs the chart morphisms to
lie over the base (`AlgebraicGeometry.Space.IsChartOverBase`), and that holds for any morphism
which is 2-compatible with a pair of morphisms of algebraic spaces
(`AlgebraicGeometry.Space.isChartOverBase_of_twoCompatible`).  The inverse `g⁻¹` of
`g = (c_small, c♯)` is 2-compatible with `c` and `𝟙 Y`, since `g ∘ g⁻¹` is 2-isomorphic to
`(𝟙 Y)_small`; so it is induced by a morphism `c' : Y ⟶ X`.  Then `(g⁻¹)⁻¹` is 2-compatible with
`c'` and `𝟙 X`, so it is induced by a morphism too, and
`AlgebraicGeometry.Space.isIso_of_twoIso_of_inverse` concludes.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_smallEtaleRingedToposHom`: a morphism of algebraic
  spaces over `S` inducing an isomorphism of small étale ringed topoi is an isomorphism.

## References

* [Stacks Project, Tag 05YZ](https://stacks.math.columbia.edu/tag/05YZ)
* [Stacks Project, Tag 04KL](https://stacks.math.columbia.edu/tag/04KL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism of algebraic spaces over `S` inducing an isomorphism of small étale ringed topoi
is an isomorphism.**  The inverse of `(c_small, c♯)` and the inverse of that are induced by
morphisms of algebraic spaces over `S`: they are morphisms of locally ringed topoi, being
isomorphisms of ringed topoi, and their chart morphisms lie over `S`, each being 2-compatible
with a pair of morphisms of algebraic spaces. -/
theorem isIso_of_isIso_smallEtaleRingedToposHom {X Y : AlgebraicSpaces B S hS} (c : X ⟶ Y)
    [(smallEtaleRingedToposHom B S hS c).toToposHom.pushforward.IsEquivalence]
    [IsIso (smallEtaleRingedToposHom B S hS c).fSharp] :
    IsIso c := by
  let g := smallEtaleRingedToposHom B S hS c
  have hb' : IsChartOverBase g.inverse :=
    isChartOverBase_of_twoCompatible (𝟙 Y) c g.inverse (compInverseTwoIso B S hS g)
  obtain ⟨c', ⟨s'⟩, -⟩ := existsUnique_spaceHom_twoIso_of_isChartOverBase hb'
    (isLocallyRinged_of_smallEtaleRingedToposIso B S hS g.inverse)
  have hb'' : IsChartOverBase g.inverse.inverse :=
    isChartOverBase_of_twoCompatible (𝟙 X) c' g.inverse.inverse
      ((RingedToposHom.TwoIso.whiskerLeft g.inverse.inverse s').symm.trans
        (compInverseTwoIso B S hS g.inverse))
  obtain ⟨c'', ⟨s''⟩, -⟩ := existsUnique_spaceHom_twoIso_of_isChartOverBase hb''
    (isLocallyRinged_of_smallEtaleRingedToposIso B S hS g.inverse.inverse)
  exact isIso_of_twoIso_of_inverse B S hS g (RingedToposHom.TwoIso.refl g) s' s''

end AlgebraicGeometry.Space

end
