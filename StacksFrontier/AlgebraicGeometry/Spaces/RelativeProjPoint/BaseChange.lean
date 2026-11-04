module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PullbackPointAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesComap

/-!
# Base change of the constructed relative Proj along a morphism of algebraic spaces

In Situation 0849 let `g : X' ⟶ X` be a morphism of algebraic spaces over `S`, let `F` be the
functor of quadruples of Stacks 084A for `𝒜` on `X`, which is the relative homogeneous spectrum
`Proj_X(𝒜)` (`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjFunctor`, an algebraic
space by Stacks 084B), and let `F'` be the one for the pulled-back algebra `g^*𝒜` on `X'`
(`AlgebraicGeometry.Space.RelativeProjSituation.pullback`).  This file proves the first assertion
of Stacks 085C: there is a canonical isomorphism

`r : Proj_{X'}(g^*𝒜) ⟶ X' ×_X Proj_X(𝒜)`

of algebraic spaces over `X'`.  As in the source, `r` sends the class of a quadruple
`(d', f', ℒ', ψ')` for `g^*𝒜` to the pair `(f', (d', g ∘ f', ℒ', ψ'))`, the identification
`(g ∘ f')^*𝒜 = (f')^*(g^*𝒜)` being the comparison
`AlgebraicGeometry.Space.pullbackPointHom`; it is a bijection on every quasi-compact test object,
natural in the test object, and the bijection extends through the limit over the quasi-compact
opens (`AlgebraicGeometry.Space.GradedAlgebraRestriction.ComapHom.isPullback_quadrupleSpaceMap`).

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjSituation.comapHomOfIso`: for an algebra `𝒜'` on `X'`
  identified with `g^*𝒜`, the identification of the restriction datum of `𝒜'` with that of `𝒜`
  along `g`.
* `AlgebraicGeometry.Space.RelativeProjSituation.pullbackComapHom`: the identification of the
  restriction datum of `g^*𝒜` with that of `𝒜` along `g`.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjBaseChangeHom`: the morphism
  `Proj_{X'}(g^*𝒜) ⟶ Proj_X(𝒜)` sending `(d', f', ℒ', ψ')` to `(d', g ∘ f', ℒ', ψ')`.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjBaseChangeIso`: **Stacks 085C, the
  isomorphism `r`.**

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.isPullback_relativeProjBaseChangeHom`: the square
  `Proj_{X'}(g^*𝒜) ⟶ Proj_X(𝒜)`, `Proj_{X'}(g^*𝒜) ⟶ X'`, `Proj_X(𝒜) ⟶ X`, `g` is cartesian.
* `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjBaseChangeIso_hom_fst` and
  `AlgebraicGeometry.Space.RelativeProjSituation.relativeProjBaseChangeIso_hom_snd`: `r` is an
  isomorphism over `X'`, compatible with the projections to `Proj_X(𝒜)`.

## Implementation notes

The algebra `g^*𝒜` is the pullback of the re-presentation of `𝒜` with sections in the universe
`u` of the site (`AlgebraicGeometry.Space.RelativeProjSituation.pullbackAlgebra`), for the reason
explained there; the restrictions `f^*𝒜` of Stacks 084B are formed from the same re-presentation.

The isomorphism `θ` of the twists, the second assertion of Stacks 085C, is not stated here: it
compares the sheaves `𝒪_{Proj_X(𝒜)}(d)` on the two relative Projs, which are constructed by
Stacks 084D.

The identification of the restriction data is stated for a situation on `X'` built from its
fields over the site of `s` (`AlgebraicGeometry.Space.RelativeProjSituation.comapHomOfIso`), and
its goals are first brought by `dsimp only` to terms over that one site: the restrictions of the
two data are `abbrev`s over the site of each situation, and unifying them across the two
syntactically different (though equal) sites unfolds them instead of comparing their arguments.

## References

* [Stacks Project, Tag 085C](https://stacks.math.columbia.edu/tag/085C)
* [Stacks Project, Tag 084A](https://stacks.math.columbia.edu/tag/084A)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

namespace AlgebraicGeometry.Space

namespace RelativeProjSituation

section Generic

variable (t : RelativeProjSituation.{u, u}) {X' : AlgebraicSpaces t.site t.base t.containsBase}
  (g : X' ⟶ t.space)
  (A' : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf t.site t.base t.containsBase X'))
  (hmul : ∀ (i j : ℤ) (U : (SmallEtale t.site t.base t.containsBase X'.1)ᵒᵖ)
    (a : (A'.piece i).val.obj U) (b : (A'.piece j).val.obj U),
    HEq ((A'.mul i j).app U a b) ((A'.mul j i).app U b a))
  (hneg : ∀ n : ℤ, n < 0 → IsZero (A'.piece n))
  (hqc : ∀ n : ℤ, (A'.piece n).IsQuasicoherentOnSite)
  (hcard : ∀ (n : ℤ) (U : (SmallEtale t.site t.base t.containsBase X'.1)ᵒᵖ),
    HasCardinalLT ((A'.piece n).val.obj U) t.site.cutoff)
  (σ : A' ≅ (gradedPull (X := smallEtaleRingedTopos t.site t.base t.containsBase X')
    (Y := smallEtaleRingedTopos t.site t.base t.containsBase t.space)
    (smallEtaleRingedToposHom t.site t.base t.containsBase g)).obj t.algebra)

/-- **The identification of the restriction datum of a pulled-back algebra with that of `𝒜`
along `g`**, for Situation 0849 `t` and a situation on `X'` over the same site whose algebra `𝒜'`
is identified with `g^*𝒜` by `σ`: at a scheme point `f : T ⟶ X'`, the comparison
`f^*𝒜' ≅ f^*(g^*𝒜) ≅ (g ∘ f)^*𝒜` of `AlgebraicGeometry.Space.pullbackPointHom`, compatible with
the restriction maps by `AlgebraicGeometry.Space.pullbackPointHom_restrict`. -/
def comapHomOfIso :
    @GradedAlgebraRestriction.ComapHom t.site t.base t.containsBase t.space.1 X'.1 _ _
      (RelativeProjSituation.mk t.site t.base t.containsBase X' A' hmul hneg hqc
        hcard).gradedAlgebraRestriction t.gradedAlgebraRestriction g.hom where
  hom {T} f := by
    dsimp only [gradedAlgebraPoints]
    exact pullbackPointHom g t.algebra σ T f
  isIso_hom_app {T} f n := by
    dsimp only [gradedAlgebraPoints]
    exact isIso_pullbackPointHom_app g t.algebra σ T f n
  restrict_comp_hom {T T'} τ f f₂ hf h := by
    subst hf
    dsimp only [gradedAlgebraRestriction, pointRestrict, pointComparisonUnital, gradedAlgebraPoints]
    exact pullbackPointHom_restrict g t.algebra σ t.isQuasicoherent hqc τ f h

end Generic

variable (s : RelativeProjSituation.{u, m}) {X' : AlgebraicSpaces s.site s.base s.containsBase}
  (g : X' ⟶ s.space)

/-- **The identification of the restriction datum of `g^*𝒜` with that of `𝒜` along `g`**: at a
scheme point `f : T ⟶ X'`, the comparison `f^*(g^*𝒜) ≅ (g ∘ f)^*𝒜` of
`AlgebraicGeometry.Space.pullbackPointHom`, which is compatible with the restriction maps of the
two restriction data by `AlgebraicGeometry.Space.pullbackPointHom_restrict`. -/
def pullbackComapHom :
    GradedAlgebraRestriction.ComapHom (s.pullback g).shrink.gradedAlgebraRestriction
      s.shrink.gradedAlgebraRestriction g.hom :=
  comapHomOfIso s.shrink g (s.pullback g).shrink.algebra (s.pullback g).shrink.mul_comm
    (s.pullback g).shrink.negative_isZero (s.pullback g).shrink.isQuasicoherent
    (s.pullback g).shrink.sections_hasCardinalLT (s.pullback g).smallAlgebraIso

/-- **The morphism `Proj_{X'}(g^*𝒜) ⟶ Proj_X(𝒜)`**, sending the class of a quadruple
`(d', f', ℒ', ψ')` for `g^*𝒜` to the class of `(d', g ∘ f', ℒ', ψ')` for `𝒜`. -/
def relativeProjBaseChangeHom : (s.pullback g).relativeProjFunctor ⟶ s.relativeProjFunctor :=
  GradedAlgebraRestriction.ComapHom.quadrupleSpaceMap (Â := s.shrink.pointAlgebra)
    (Â' := (s.pullback g).shrink.pointAlgebra) (ρ₁ := s.quadrupleRestriction)
    (ρ₁' := (s.pullback g).quadrupleRestriction) (s.pullbackComapHom g)
    s.shrink.contains_relativeProj_pointAlgebra
    (s.pullback g).shrink.contains_relativeProj_pointAlgebra s.space.property.isSheaf
    X'.property.isSheaf

/-- **The square of Stacks 085C is cartesian**: `Proj_{X'}(g^*𝒜) = X' ×_X Proj_X(𝒜)`, through
the morphism `relativeProjBaseChangeHom` and the projections to `X'` and `X`. -/
theorem isPullback_relativeProjBaseChangeHom :
    IsPullback (s.relativeProjBaseChangeHom g) (s.pullback g).relativeProjπ s.relativeProjπ g.hom :=
  GradedAlgebraRestriction.ComapHom.isPullback_quadrupleSpaceMap (ρ₁ := s.quadrupleRestriction)
    (ρ₁' := (s.pullback g).quadrupleRestriction) (s.pullbackComapHom g)
    s.shrink.contains_relativeProj_pointAlgebra
    (s.pullback g).shrink.contains_relativeProj_pointAlgebra s.space.property.isSheaf
    X'.property.isSheaf

/-- **Stacks 085C, the isomorphism `r : Proj_{X'}(g^*𝒜) ⟶ X' ×_X Proj_X(𝒜)`**, for a morphism
`g : X' ⟶ X` of algebraic spaces over `S` and the quasi-coherent graded `𝒪_X`-algebra `𝒜` of
Situation 0849: an isomorphism of algebraic spaces from the relative Proj of `g^*𝒜` on `X'`
(`relativeProjFunctor` of `s.pullback g`) to the fibre product of `g` and the structure morphism
`Proj_X(𝒜) ⟶ X`.  It is an isomorphism over `X'` (`relativeProjBaseChangeIso_hom_fst`) and its
second component is `relativeProjBaseChangeHom`, which sends the class of a quadruple
`(d', f', ℒ', ψ')` to the class of `(d', g ∘ f', ℒ', ψ')`
(`relativeProjBaseChangeIso_hom_snd`). -/
@[stacks 085C "the isomorphism r on the constructed relative Proj: Proj_{X'}(g^*A) ≅ \
X' x_X Proj_X(A), over X' and compatible with the projections"]
def relativeProjBaseChangeIso :
    (s.pullback g).relativeProjFunctor ≅ Limits.pullback g.hom s.relativeProjπ :=
  (s.isPullback_relativeProjBaseChangeHom g).flip.isoPullback

/-- **`r` is an isomorphism over `X'`.** -/
@[stacks 085C "r is an isomorphism over X', on the constructed relative Proj: r followed by \
the first projection X' x_X Proj_X(A) -> X' is the structure morphism \
Proj_{X'}(g^*A) -> X'", reassoc (attr := simp)]
theorem relativeProjBaseChangeIso_hom_fst :
    (s.relativeProjBaseChangeIso g).hom ≫ Limits.pullback.fst g.hom s.relativeProjπ =
      (s.pullback g).relativeProjπ :=
  (s.isPullback_relativeProjBaseChangeHom g).flip.isoPullback_hom_fst

/-- **The second component of `r` is the morphism `(d', f', ℒ', ψ') ↦ (d', g ∘ f', ℒ', ψ')`.** -/
@[stacks 085C "r on the constructed relative Proj sends the class of a quadruple \
(d', f', L', psi') to (f', (d', g f', L', psi')): followed by the second projection it is the \
morphism Proj_{X'}(g^*A) -> Proj_X(A) of quadruples", reassoc (attr := simp)]
theorem relativeProjBaseChangeIso_hom_snd :
    (s.relativeProjBaseChangeIso g).hom ≫ Limits.pullback.snd g.hom s.relativeProjπ =
      s.relativeProjBaseChangeHom g :=
  (s.isPullback_relativeProjBaseChangeHom g).flip.isoPullback_hom_snd

end RelativeProjSituation

end AlgebraicGeometry.Space

end
