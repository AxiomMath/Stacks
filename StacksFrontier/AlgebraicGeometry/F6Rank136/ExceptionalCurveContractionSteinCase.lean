module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionSteinStep

/-!
# The hypotheses of Stacks 0C2L in the Stein case

Two results carry the proof of [Stacks, Tag 0C2L] as far as this development has taken it, and
neither of them reaches the tag on its own:

* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying`
  grants the conclusion from the four steps of the source's proof that remain open — `hreg` and
  `hdim`, that `𝒪_{Y, y}` is regular of dimension two, `hfibre`, that the scheme-theoretic fibre
  over `y` is the curve, and `hclassify`, that the classifying morphism to the blowup at `y` is
  an isomorphism;
* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_steinCase` replaces `f` by the
  first factor of its Stein factorization, which inherits every hypothesis of the tag and in
  addition has geometrically connected fibres, satisfies `f_* 𝒪_X = 𝒪_Y`, and carries the curve
  to a *closed* point.

The extra data of the second is exactly what the four binders of the first need and do not have:
`hclassify` asks, among other things, that the classifying morphism be an isomorphism away from
the exceptional curve, which the source reads off from `f_* 𝒪_X = 𝒪_Y` together with
quasi-finiteness off the curve. This file composes the two, so that the four binders may be
discharged in the presence of the Stein data.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup` — the hypotheses of
  [Stacks, Tag 0C2L] on a morphism, together with the three extra properties the Stein
  factorization supplies, bundled so that the four remaining binders can quantify over them.
* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_steinSetup` — the composition: a
  contraction of an exceptional curve of the first kind exists as soon as `hreg`, `hdim`,
  `hfibre` and `hclassify` hold for every morphism carrying such a setup.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 03H0](https://stacks.math.columbia.edu/tag/03H0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The hypotheses of [Stacks, Tag 0C2L] in the Stein case.** A morphism `f : X ⟶ Y` carries
this data when it satisfies the hypotheses the tag places on it — `Y` Noetherian, `f` proper,
every point of the closed subscheme cut out by `D` sent to `y`, and `f` quasi-finite at every
point off the support of `D` — together with the three further properties that the first factor
of a Stein factorization enjoys: geometrically connected fibres, `f_* 𝒪_X = 𝒪_Y`, and `{y}`
closed.

The reduction `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_steinCase` says the
tag may be proved for such morphisms alone, so the steps of the source's proof that are still
open may assume all of it. -/
public structure Scheme.IdealSheafData.IsSteinContractionSetup {X : Scheme.{u}}
    (D : X.IdealSheafData) {Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) : Prop where
  /-- The target is Noetherian. -/
  isNoetherian : IsNoetherian Y
  /-- The morphism is proper. -/
  isProper : IsProper f
  /-- The fibres of the morphism are geometrically connected. -/
  geometricallyConnected : GeometricallyConnected f
  /-- The canonical map `𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism. -/
  isIso_c : IsIso f.c
  /-- The point the curve is carried to is closed. -/
  isClosed_singleton : IsClosed ({y} : Set Y)
  /-- Every point of the closed subscheme cut out by `D` is carried to `y`. -/
  base_eq : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y
  /-- The morphism is quasi-finite at every point off the support of `D`. -/
  quasiFinite_of_notMem : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x

/-- **A contraction of an exceptional curve of the first kind exists**, under the hypotheses of
[Stacks, Tag 0C2L] on `f` together with the four steps of that proof which this development
cannot yet perform — each of them now allowed to use the whole of the Stein data.

This is
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying`
composed with `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_steinCase`: the
binders `hreg`, `hdim`, `hfibre` and `hclassify` are asked for not of `f` itself but of every
morphism carrying an
`AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup`, which is strictly less to
prove, because such a morphism satisfies `f_* 𝒪_X = 𝒪_Y` and has geometrically connected
fibres. -/
public theorem exists_isContractionOfExceptionalCurve_of_steinSetup
    {X Y : Scheme.{u}} [IsNoetherian Y] {D : X.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x)
    (hreg : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → IsRegularLocalRing (Y'.presheaf.stalk y'))
    (hdim : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → ringKrullDim (Y'.presheaf.stalk y') = 2)
    (hfibre : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → ∀ hy' : IsClosed ({y'} : Set Y'),
        D = (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y')).comap f')
    (hclassify : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → ∀ (hy' : IsClosed ({y'} : Set Y'))
        (g : X ⟶ AlgebraicGeometry.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y'))),
        g ≫ AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y')) = f' → IsIso g) :
    ∃ (Z : Scheme.{u}) (b : X ⟶ Z), IsContractionOfExceptionalCurve D b := by
  refine exists_isContractionOfExceptionalCurve_of_steinCase e f y hmaps hqf ?_
  intro Y' hY' f' hf' hgc hc y' hy' hmaps' hqf'
  have hsetup : D.IsSteinContractionSetup f' y' := ⟨hY', hf', hgc, hc, hy', hmaps', hqf'⟩
  exact exists_isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying hE f' y'
    hmaps' (hreg Y' f' y' hsetup) (hdim Y' f' y' hsetup)
    (fun _ ↦ hfibre Y' f' y' hsetup _) (fun _ ↦ hclassify Y' f' y' hsetup _)

end AlgebraicGeometry

end
