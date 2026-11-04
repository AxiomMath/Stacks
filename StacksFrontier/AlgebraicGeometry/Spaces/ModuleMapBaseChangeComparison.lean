module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Pulling a map of modules back along a morphism of the source space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`u : F ⟶ G` be a map of quasi-coherent `𝒪_X`-modules.  A morphism `g : X' ⟶ X` turns this
datum into the same datum on `X'`: the structure morphism `g ≫ f : X' ⟶ Y` and the inverse
image `g^*u : g^*F ⟶ g^*G`.  For a test scheme `T` over `Y` the two base-change spaces are
then related by a comparison `X' ×_Y T ⟶ X ×_Y T`, and that comparison square is cartesian —
it identifies `X' ×_Y T` with `X' ×_X (X ×_Y T)`.  Consequently the comparison inherits every
property of `g` that is stable under base change; flatness is recorded here.

## Main definitions

* `AlgebraicGeometry.Space.ModuleMapSituation.pullbackSituation`: the situation on `X'`
  obtained by pulling the map of modules back along `g : X' ⟶ X`.
* `AlgebraicGeometry.Space.ModuleMapSituation.pullbackBaseChangeMap`: the comparison
  `X' ×_Y T ⟶ X ×_Y T` of base-change spaces.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isPullback_pullbackBaseChangeMap`: the comparison
  square is cartesian, that is, `X' ×_Y T` is the fibre product of `X'` and `X ×_Y T` over `X`.
* `AlgebraicGeometry.Space.ModuleMapSituation.isFlat_pullbackBaseChangeMap`: the comparison is
  flat as soon as `g` is.

## References

* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03MO](https://stacks.math.columbia.edu/tag/03MO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ModuleMapSituation

variable (D : ModuleMapSituation.{u, u} B S hS) {X' : AlgebraicSpaces B S hS} (g : X' ⟶ D.X)
    (hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite)

/-- The inverse image of a map of quasi-coherent modules along a morphism `g : X' ⟶ X` of the
source space, as a situation over the same target space: the structure morphism is `g ≫ f` and
the map of modules is `g^*u : g^*F ⟶ g^*G`.  Quasi-coherence of the two inverse images is
supplied as a hypothesis.

This is reducible: its target space is `D.Y` on the nose, so that the test schemes of the two
situations are the same category and a test scheme of one is accepted as a test scheme of the
other without an explicit transport. -/
@[reducible]
def pullbackSituation : ModuleMapSituation.{u, u} B S hS where
  X := X'
  Y := D.Y
  f := g ≫ D.f
  F := (modulePullback B S hS g).obj D.F
  G := (modulePullback B S hS g).obj D.G
  quasicoherent_F := hF
  quasicoherent_G := hG
  u := (modulePullback B S hS g).map D.u

/-- The comparison `X' ×_Y T ⟶ X ×_Y T` of base-change spaces induced by a morphism
`g : X' ⟶ X` of source spaces over `Y`: the morphism whose projection to `X` is the projection
of `X' ×_Y T` to `X'` followed by `g` and whose projection to `T` is that of `X' ×_Y T`. -/
def pullbackBaseChangeMap (T : D.SchemesOver) :
    (D.pullbackSituation g hF hG).baseChangeSpace T ⟶ D.baseChangeSpace T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).flip.lift
    ((D.pullbackSituation g hF hG).baseChangeInclusion T)
    ((D.pullbackSituation g hF hG).baseChangeProjection T ≫ g)
    (((AlgebraicSpaces.isPullback_fiberProduct B S hS (g ≫ D.f) T.hom).flip.w).trans
      (Category.assoc _ _ _).symm)

/-- The comparison of base-change spaces lies over `g`. -/
theorem pullbackBaseChangeMap_comp_baseChangeProjection (T : D.SchemesOver) :
    D.pullbackBaseChangeMap g hF hG T ≫ D.baseChangeProjection T =
      (D.pullbackSituation g hF hG).baseChangeProjection T ≫ g :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).flip.lift_snd _ _ _

/-- The comparison of base-change spaces commutes with the projections to the test scheme. -/
theorem pullbackBaseChangeMap_comp_baseChangeInclusion (T : D.SchemesOver) :
    D.pullbackBaseChangeMap g hF hG T ≫ D.baseChangeInclusion T =
      (D.pullbackSituation g hF hG).baseChangeInclusion T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).flip.lift_fst _ _ _

/-- **The comparison of base-change spaces is cartesian**: the projection `X' ×_Y T ⟶ X'` and
the comparison `X' ×_Y T ⟶ X ×_Y T` exhibit `X' ×_Y T` as the fibre product of `g : X' ⟶ X`
and the projection `X ×_Y T ⟶ X`, that is, `X' ×_Y T = X' ×_X (X ×_Y T)`.

This is the pasting of the two cartesian squares defining `X' ×_Y T` and `X ×_Y T` over
`T ⟶ Y`. -/
theorem isPullback_pullbackBaseChangeMap (T : D.SchemesOver) :
    IsPullback ((D.pullbackSituation g hF hG).baseChangeProjection T)
      (D.pullbackBaseChangeMap g hF hG T) g (D.baseChangeProjection T) :=
  (IsPullback.of_right'
    (AlgebraicSpaces.isPullback_fiberProduct B S hS (g ≫ D.f) T.hom).flip
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).flip).flip

/-- The comparison of base-change spaces is flat whenever `g` is, flatness of morphisms of
algebraic spaces being stable under base change. -/
theorem isFlat_pullbackBaseChangeMap (hg : IsFlat B S hS g.hom) (T : D.SchemesOver) :
    IsFlat B S hS (D.pullbackBaseChangeMap g hF hG T).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (D.isPullback_pullbackBaseChangeMap g hF hG T) hg

end ModuleMapSituation

end AlgebraicGeometry.Space

end
