module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplex
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.TorIndependenceBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional

/-!
# The diagonal datum of a relative dualizing complex after a base change

Consider a cartesian square of schemes with `X' = X ×_S S'`, write `g' : X' ⟶ X` for the
projection and let `f : X ⟶ S` be flat. Let `W ⊆ X ×_S X` be an open through which the relative
diagonal of `f` factors as a closed immersion, and let `W' ⊆ X' ×_{S'} X'` be one for `f'`
mapping into `W`. This file proves two identifications attached to the square, and constructs
the morphism they produce.

The first is the Tor independence of `X` and `X' ×_{S'} X'` over `X ×_S X`, which is Stacks 0CTA
at the square whose right-hand map is `f` and whose upper-left map is the identity of `X`. The
square is the compatibility of the relative diagonals: the relative diagonal of `f'` followed by
`g' × g'` is `g'` followed by the relative diagonal of `f`.

The second is the comparison of the two ways of pulling the complex back to `W'`: along
`W' ⟶ W ⟶ X` and along `W' ⟶ X' ⟶ X`.

Given an identification of the derived pullback of `Δ_*𝒪_X` with `Δ'_*𝒪_{X'}`, the two combine
into the derived base change of a map `ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W`, which is a map
`Δ'_*𝒪_{X'} ⟶ L pr₁^*(L(g')^*K)|_{W'}`.

## Main definitions

* `AlgebraicGeometry.diagonalBaseChangeMap` is the morphism `X' ×_{S'} X' ⟶ X ×_S X` induced by
  the projection `g'` on each factor.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.derivedPullbackProjBaseChangeIso` is the comparison
  of the two derived pullbacks of `K` to `W'`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.baseChangeComplex` is `L(g')^*K`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.baseChangeDiagonalMap` is the derived base change of
  `ξ`, formed from the comparison above and an identification of the pulled back diagonal
  algebra.

## Main results

* `AlgebraicGeometry.diagonal_comp_diagonalBaseChangeMap` is the compatibility of the relative
  diagonal with the base change.
* `AlgebraicGeometry.torIndependent_diagonalBaseChangeMap` is Stacks 0CTA at the diagonal square:
  the morphism `X' ×_{S'} X' ⟶ X ×_S X` and the relative diagonal of `f` are Tor independent.

## References

* [Stacks Project, Lemma 48.28.6 (Tag 0E2Y)](https://stacks.math.columbia.edu/tag/0E2Y)
* [Stacks Project, Definition 48.28.1 (Tag 0E2T)](https://stacks.math.columbia.edu/tag/0E2T)
* [Stacks Project, Lemma 37.62.4 (Tag 0CTA)](https://stacks.math.columbia.edu/tag/0CTA)
* [Stacks Project, Lemma 20.27.3 (Tag 0D5S)](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### Tor independence of the relative diagonal against a base change -/

/-- The morphism `X' ×_{S'} X' ⟶ X ×_S X` induced on each factor by the projection
`g' : X' ⟶ X`, where `X' = X ×_S S'`. -/
abbrev diagonalBaseChangeMap {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    pullback (pullback.snd f g) (pullback.snd f g) ⟶ pullback f f :=
  pullback.map _ _ _ _ (pullback.fst f g) (pullback.fst f g) g
    pullback.condition.symm pullback.condition.symm

/-- **The relative diagonal is compatible with the base change.** The relative diagonal of
`f' : X' ⟶ S'` followed by the morphism induced by `g'` on each factor is `g'` followed by the
relative diagonal of `f`. -/
theorem diagonal_comp_diagonalBaseChangeMap {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) :
    pullback.diagonal (pullback.snd f g) ≫ diagonalBaseChangeMap f g
      = pullback.fst f g ≫ pullback.diagonal f := by
  apply pullback.hom_ext <;>
    first
    | rw [Category.assoc, pullback.lift_fst]
    | rw [Category.assoc, pullback.lift_snd]
  all_goals simp

/-- **Stacks 0CTA at the diagonal square.** For `f : X ⟶ S` flat and `g : S' ⟶ S` arbitrary, the
morphism `X' ×_{S'} X' ⟶ X ×_S X` induced by the projection `X' = X ×_S S' ⟶ X` and the relative
diagonal of `f` are Tor independent over `X ×_S X`. -/
theorem torIndependent_diagonalBaseChangeMap {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat f] :
    TorIndependent (diagonalBaseChangeMap f g) (pullback.diagonal f) :=
  torIndependent_pullback_product_of_flat g f f (𝟙 X) (𝟙 X) rfl

/-! ### Transitivity of derived pullback at the two factorizations of `W' ⟶ X` -/

namespace Scheme.Hom

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace DiagonalOpen

/-- `L(g')^*K`, the derived pullback of `K` along the projection `g' : X' ⟶ X`. -/
abbrev baseChangeComplex {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    DerivedCategory (OXMod.{u, u} X'.toRingedSpace) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
    g'.toLRSHom.toShHom).obj K

/-- **Transitivity of derived pullback at the two factorizations of `W' ⟶ X`.** For `w : W' ⟶ W`
with `w ≫ pr₁|_W = pr₁|_{W'} ≫ g'`, the derived pullback along `w` of `L pr₁^*K|_W` is
`L pr₁^*(L(g')^*K)|_{W'}`. -/
def derivedPullbackProjBaseChangeIso {X' S' : Scheme.{u}} {f' : X' ⟶ S'}
    (D : DiagonalOpen f) (D' : DiagonalOpen f') (g' : X' ⟶ X) (w : D'.W ⟶ D.W)
    (hw : w ≫ D.proj = D'.proj ≫ g')
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace)) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        w.toLRSHom.toShHom).obj (D.derivedPullbackProj K) ≅
      D'.derivedPullbackProj (baseChangeComplex g' K) := by
  have hw' : w.toLRSHom.toShHom ≫ D.proj.toLRSHom.toShHom
      = D'.proj.toLRSHom.toShHom ≫ g'.toLRSHom.toShHom := by
    rw [← LocallyRingedSpace.comp_toShHom, ← LocallyRingedSpace.comp_toShHom,
      ← Scheme.Hom.comp_toLRSHom, ← Scheme.Hom.comp_toLRSHom, hw]
  exact (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      w.toLRSHom.toShHom D.proj.toLRSHom.toShHom).app K ≪≫ eqToIso (by rw [hw']) ≪≫
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      D'.proj.toLRSHom.toShHom g'.toLRSHom.toShHom).app K).symm

/-- **The derived base change of `ξ`.** Let `ξ : Δ_*𝒪_X ⟶ L pr₁^*K|_W` be a map in `D(𝒪_W)`, let
`w : W' ⟶ W` satisfy `w ≫ pr₁|_W = pr₁|_{W'} ≫ g'`, and let `eΔ` identify the derived pullback
along `w` of `Δ_*𝒪_X` with `Δ'_*𝒪_{X'}`. The derived pullback of `ξ` along `w`, read through `eΔ`
and through the transitivity comparison, is a map
`Δ'_*𝒪_{X'} ⟶ L pr₁^*(L(g')^*K)|_{W'}` in `D(𝒪_{W'})`. -/
def baseChangeDiagonalMap {X' S' : Scheme.{u}} {f' : X' ⟶ S'}
    (D : DiagonalOpen f) (D' : DiagonalOpen f') (g' : X' ⟶ X) (w : D'.W ⟶ D.W)
    (hw : w ≫ D.proj = D'.proj ≫ g')
    (eΔ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        w.toLRSHom.toShHom).obj D.diagonalObject ≅ D'.diagonalObject)
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K) :
    D'.diagonalObject ⟶ D'.derivedPullbackProj (baseChangeComplex g' K) :=
  eΔ.inv ≫
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      w.toLRSHom.toShHom).map ξ ≫
    (derivedPullbackProjBaseChangeIso D D' g' w hw K).hom

end DiagonalOpen

end Scheme.Hom

end AlgebraicGeometry

end
