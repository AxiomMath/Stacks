module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionSteinCase

/-!
# The contraction of an exceptional curve is the Stein factorization

[Stacks, Tag 0C2L] has **two** conjuncts. Let `X` be Noetherian, let `E ⊆ X` be an exceptional
curve of the first kind, and let `f : X ⟶ Y` be a morphism to a Noetherian scheme which is
proper, carries `E` to a point `y`, and is quasi-finite at every point off `E`. Then

1. a contraction of `E` exists, **and**
2. it *is* the Stein factorization of `f`.

Everything before this file states only the first conjunct: the results of
`StacksFrontier/AlgebraicGeometry/F6Rank136/ExceptionalCurveContractionSteinCase.lean` and its
imports conclude `∃ Z b, IsContractionOfExceptionalCurve D b`, which says nothing about *which*
morphism out of `X` the contraction is. The second conjunct is what pins it down, and this file
supplies it.

The device is to stop throwing the witness away. The source's proof opens by replacing `f` by
the first factor `f' = f.toNormalization` of its Stein factorization, and then shows that *that*
morphism is the blowup; so the contraction the tag produces is `f.toNormalization` on the nose,
and the sharp form of the tag's conclusion is

`IsContractionOfExceptionalCurve D f.toNormalization`,

which asserts both conjuncts at once: a contraction exists (the witness being exhibited), and it
is the first factor of the Stein factorization of `f` (the factorization itself being
`Stacks.SteinFactorization.toNormalization_fromNormalization`). Accordingly every statement
below carries the *morphism* through where its predecessor carried only an existential.

For a reader who would rather not depend on the particular construction of the normalization,
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_isSteinFactorization_of_steinSetup`
states the same thing through the characterisation of a Stein factorization in
[Stacks, Tag 03H0]: a factorization `f = b ≫ π` with `b_* 𝒪_X = 𝒪_Z` and `π` integral, whose
first factor is a contraction of `E`.

## Main results

* `AlgebraicGeometry.isContractionOfExceptionalCurve_of_isIso_blowUpClassifying_of_eq` — the
  non-existential form of
  `AlgebraicGeometry.isContractionOfExceptionalCurve_of_isIso_blowUpClassifying`: the morphism
  itself, rather than some unnamed morphism, is a contraction of `D`.
* `AlgebraicGeometry.isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying` —
  the same with the binder `hy` discharged from properness, as in
  `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying`.
* `AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinCase` — the Stein
  reduction with the witness kept: if the tag holds for every morphism carrying the Stein data,
  with the morphism itself as the contraction, then `f.toNormalization` is a contraction of `D`.
* `AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinSetup` — the two
  conjuncts of [Stacks, Tag 0C2L] at the tag's own four hypotheses on `f`, modulo the four steps
  of the source's proof that this development cannot yet perform, each of them allowed to use
  the whole of the Stein data.
* `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_isSteinFactorization_of_steinSetup` —
  the same conclusion phrased through the characterisation of the Stein factorization of
  [Stacks, Tag 03H0], without naming the normalization.

## What 0C2L still asks for

The tag is **not** registered in this file. The four binders that
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_steinSetup` carries are carried
here unchanged — `hreg` and `hdim`, that `𝒪_{Y', y'}` is regular of dimension two, `hfibre`,
that the scheme-theoretic fibre over `y'` is the curve, and `hclassify`, that the classifying
morphism to the blowup at `y'` is an isomorphism. What this file changes is the *conclusion*, not
the hypotheses: the second conjunct of the tag was absent from the development and is now
stated. The implementation notes of
`StacksFrontier/AlgebraicGeometry/F6Rank136/ExceptionalCurveContractionExistence.lean` and
`StacksFrontier/AlgebraicGeometry/F6Rank136/ExceptionalCurveContractionClassifying.lean` say what
each binder still needs.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 03H0](https://stacks.math.columbia.edu/tag/03H0)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The morphism itself is a contraction**, not merely some morphism out of `X`. This is
`AlgebraicGeometry.isContractionOfExceptionalCurve_of_isIso_blowUpClassifying` with the
contracted ideal presented as `D` rather than as the inverse image of the vanishing ideal of
`y`, which is what the hypothesis `hfibre` identifies it with.

Its predecessor
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isIso_blowUpClassifying` discards
the witness; keeping it is what the second conjunct of [Stacks, Tag 0C2L] needs. -/
public theorem isContractionOfExceptionalCurve_of_isIso_blowUpClassifying_of_eq
    {X Y : Scheme.{u}} [IsNoetherian Y] {D : X.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (y : Y) (hy : IsClosed ({y} : Set Y))
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2) (f : X ⟶ Y)
    (hfibre : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f)
    (hclassify : ∀ g : X ⟶ AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      g ≫ AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f → IsIso g) :
    IsContractionOfExceptionalCurve D f := by
  subst hfibre
  exact isContractionOfExceptionalCurve_of_isIso_blowUpClassifying y hy hreg hdim f
    hE.isEffectiveCartierDivisor hclassify

/-- **The morphism itself is a contraction**, with the binder `hy` discharged from the properness
of `f`: a proper morphism carries the nonempty closed curve `E` to a closed point.

This is
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying`
with its witness kept. What remains carried is `hreg` and `hdim`, that `𝒪_{Y, y}` is regular of
dimension two, `hfibre`, that the scheme-theoretic fibre over `y` is `E`, and `hclassify`, that
the classifying morphism to the blowup at `y` is an isomorphism. -/
public theorem isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying
    {X Y : Scheme.{u}} [IsNoetherian Y] {D : X.IdealSheafData} {k : Type u} [Field k]
    {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2)
    (hfibre : ∀ hy : IsClosed ({y} : Set Y),
      D = (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)).comap f)
    (hclassify : ∀ (hy : IsClosed ({y} : Set Y)) (g : X ⟶ AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))),
      g ≫ AlgebraicGeometry.blowUpToBase
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f → IsIso g) :
    IsContractionOfExceptionalCurve D f :=
  have hy : IsClosed ({y} : Set Y) :=
    isClosed_singleton_of_isProper_of_forall_subschemeι_base_eq e f y hmaps
  isContractionOfExceptionalCurve_of_isIso_blowUpClassifying_of_eq hE y hy hreg hdim f
    (hfibre hy) (hclassify hy)

/-- **The Stein reduction for [Stacks, Tag 0C2L], with the witness kept.** Suppose the tag's
conclusion holds, *with the morphism itself as the contraction*, for every morphism out of `X`
which carries the hypotheses of the tag together with the three extra properties a Stein
factorization supplies. Then the first factor `f.toNormalization` of the Stein factorization of
`f` is a contraction of `D`.

This is `AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_steinCase` with the
existential in both the hypothesis and the conclusion replaced by the morphism, which is what
identifies the contraction as the Stein factorization of `f`. -/
public theorem isContractionOfExceptionalCurve_toNormalization_of_steinCase
    {X Y : Scheme.{u}} [IsNoetherian Y] {D : X.IdealSheafData} {k : Type u} [Field k]
    (e : projectiveLineProj k ≅ D.subscheme) (f : X ⟶ Y) [IsProper f] (y : Y)
    (hmaps : ∀ z : D.subscheme, f.base (D.subschemeι.base z) = y)
    (hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x)
    (H : ∀ (Y' : Scheme.{u}) (_ : IsNoetherian Y') (f' : X ⟶ Y') (_ : IsProper f')
      (_ : GeometricallyConnected f') (_ : IsIso f'.c) (y' : Y') (_ : IsClosed ({y'} : Set Y'))
      (_ : ∀ z : D.subscheme, f'.base (D.subschemeι.base z) = y')
      (_ : ∀ x ∉ (D.support : Set X), quasiFiniteAt f' x),
      IsContractionOfExceptionalCurve D f') :
    IsContractionOfExceptionalCurve D f.toNormalization := by
  have hconn : _root_.IsConnected (D.support : Set X) :=
    D.isConnected_support_of_iso_projectiveLineProj k e
  have hmaps' : ∀ x ∈ (D.support : Set X), f.base x = y :=
    (D.forall_subschemeι_base_eq_iff_forall_mem_support f y).1 hmaps
  obtain ⟨y', hy'maps, -⟩ :=
    exists_forall_toNormalization_base_eq f (D.support : Set X) hconn y hmaps'
  have := Stacks.SteinFactorization.isProper_toNormalization f
  exact H f.normalization (isNoetherian_normalization f) f.toNormalization inferInstance
    (Stacks.SteinFactorization.geometricallyConnected_toNormalization f)
    (Stacks.SteinFactorization.isIso_c_toNormalization_of_isProper f) y'
    (isClosed_singleton_of_isProper_of_forall_base_eq f.toNormalization D.support hconn.1 y'
      hy'maps)
    ((D.forall_subschemeι_base_eq_iff_forall_mem_support f.toNormalization y').2 hy'maps)
    fun x hx ↦ quasiFiniteAt_toNormalization f x (hqf x hx)

/-- **Both conjuncts of [Stacks, Tag 0C2L]**, at the tag's own four hypotheses on `f`, modulo
the four steps of the source's proof that this development cannot yet perform.

The conclusion is that the first factor `f.toNormalization` of the Stein factorization of `f` is
a contraction of the exceptional curve. That is the tag's full conclusion: a contraction exists,
and it is the Stein factorization of `f`, the factorization being
`Stacks.SteinFactorization.toNormalization_fromNormalization`. Its predecessor
`AlgebraicGeometry.exists_isContractionOfExceptionalCurve_of_steinSetup` asserts only the first
conjunct.

The four binders are unchanged from that predecessor, and the tag is not registered: `hreg` and
`hdim` ask that `𝒪_{Y', y'}` be regular of dimension two, `hfibre` that the scheme-theoretic
fibre over `y'` be the curve, and `hclassify` that the classifying morphism to the blowup at
`y'` be an isomorphism. Each is asked not of `f` but of every morphism carrying an
`AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup`. -/
public theorem isContractionOfExceptionalCurve_toNormalization_of_steinSetup
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
    IsContractionOfExceptionalCurve D f.toNormalization := by
  refine isContractionOfExceptionalCurve_toNormalization_of_steinCase e f y hmaps hqf ?_
  intro Y' hY' f' hf' hgc hc y' hy' hmaps' hqf'
  have hsetup : D.IsSteinContractionSetup f' y' := ⟨hY', hf', hgc, hc, hy', hmaps', hqf'⟩
  exact isContractionOfExceptionalCurve_of_isProper_of_isIso_blowUpClassifying hE f' y'
    hmaps' (hreg Y' f' y' hsetup) (hdim Y' f' y' hsetup)
    (fun _ ↦ hfibre Y' f' y' hsetup _) (fun _ ↦ hclassify Y' f' y' hsetup _)

/-- **Both conjuncts of [Stacks, Tag 0C2L], without naming the normalization.** The second
conjunct says that the contraction is the Stein factorization of `f`; by [Stacks, Tag 03H0] a
factorization `f = b ≫ π` is *the* Stein factorization exactly when the canonical map
`𝒪_Z ⟶ b_* 𝒪_X` is an isomorphism and `π` is integral. So the tag's conclusion is: there is a
factorization of `f` of that shape whose first factor is a contraction of the exceptional curve.

This is `AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinSetup` with
the Stein factorization of `f` presented through its characterisation instead of through
`AlgebraicGeometry.Scheme.Hom.normalization`. The four binders are the same, and the tag is not
registered. -/
public theorem exists_isContractionOfExceptionalCurve_isSteinFactorization_of_steinSetup
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
    ∃ (Z : Scheme.{u}) (b : X ⟶ Z) (π : Z ⟶ Y), b ≫ π = f ∧ IsIso b.c ∧ IsIntegralHom π ∧
      IsContractionOfExceptionalCurve D b :=
  ⟨f.normalization, f.toNormalization, f.fromNormalization,
    Stacks.SteinFactorization.toNormalization_fromNormalization f,
    Stacks.SteinFactorization.isIso_c_toNormalization_of_isProper f,
    inferInstance,
    isContractionOfExceptionalCurve_toNormalization_of_steinSetup hE f y hmaps hqf hreg hdim
      hfibre hclassify⟩

end AlgebraicGeometry

end
