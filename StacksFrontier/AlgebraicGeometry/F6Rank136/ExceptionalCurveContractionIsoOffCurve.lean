module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionClassifying
public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionSteinIdentification
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SplittingStep
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic

/-!
# A contraction is an isomorphism away from the curve it contracts

`AlgebraicGeometry.isIso_of_comp_blowUpToBase_eq_of_isBirational` reduces the hypothesis
`hclassify` of the [Stacks, Tag 0C2L] chain — that the classifying morphism `g : X ⟶ Bl_y Y` is
an isomorphism — to three inputs. One of them, `hres`, is that `g` is locally an isomorphism
over every point of `Bl_y Y` off the exceptional curve. This file discharges it, from data the
Stein reduction already supplies.

The argument is the source's own. Let `W = Y ∖ {y}`. Every point of `X` lying over `W` is off
the curve `E`, because `f` carries `E` to `y`; so `f` is quasi-finite at every such point, and
the restriction `f|_W : f^{-1}(W) ⟶ W` is proper and locally quasi-finite, hence *finite* by
[Stacks, Tag 02LS], hence affine. An affine morphism whose map on sections over each affine open
is an isomorphism is an isomorphism — and that is exactly what `f_* 𝒪_X = 𝒪_Y` supplies. So
`f|_W` is an isomorphism. The blowup morphism `b : Bl_y Y ⟶ Y` is an isomorphism over `W` as
well ([Stacks, Tag 02OS]), so cancelling the second factor in

`f|_W = g|_{b^{-1}W} ≫ b|_W`

makes `g` an isomorphism over `b^{-1}(W)`, an open containing every point off the exceptional
curve.

Both halves of the input are carried by
`AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup`: quasi-finiteness off the
curve is one of the tag's own hypotheses, and `f_* 𝒪_X = 𝒪_Y` is what the Stein reduction adds.
So the whole of `hres` comes for free in the Stein case, and the last result below states both
conjuncts of [Stacks, Tag 0C2L] with `hres` gone from the list of open inputs.

## Main results

* `AlgebraicGeometry.isIso_morphismRestrict_of_isIso_c_of_quasiFiniteAt` — a proper morphism
  satisfying `f_* 𝒪_X = 𝒪_Y` which is quasi-finite at every point lying over an open `W`
  restricts to an isomorphism over `W`.
* `AlgebraicGeometry.isIso_morphismRestrict_blowUpClassifying` — the classifying morphism is an
  isomorphism over `b^{-1}(Y ∖ {y})`, named as an open rather than existentially, which is what
  the birationality argument downstream needs.
* `AlgebraicGeometry.exists_isIso_morphismRestrict_blowUpClassifying` — the binder `hres` of
  `AlgebraicGeometry.isIso_of_comp_blowUpToBase_eq_of_isBirational` discharged: the classifying
  morphism of such an `f` is locally an isomorphism over every point of the blowup off the
  exceptional curve.
* `AlgebraicGeometry.isIso_blowUpClassifying_of_steinSetup` — `hclassify` for a morphism
  carrying the Stein data, with only the inputs that integrality and the conormal comparison
  still owe.
* `AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinSetup_of_isBirational`
  — both conjuncts of [Stacks, Tag 0C2L], with `hres` discharged.

## What 0C2L still asks for

The tag is **not** registered here. After this file the open inputs are:

* `hreg`, `hdim` and `hfibre`, which in the source come from [Stacks, Tag 0C2K] and need the
  transport of `AlgebraicGeometry.Scheme.IdealSheafData.formalNeighborhoodRing` to the completed
  local ring of the base, together with an
  `AlgebraicGeometry.Scheme.IdealSheafData.ExceptionalMonomialData`. That bundle *is*
  constructed — see
  `StacksFrontier/AlgebraicGeometry/Surfaces/FormalNeighborhoodFromMonomialValueLaw.lean`, which
  retracts an earlier claim here to the contrary — so the live blocker is the transport alone;
* integrality of `X` and of the Stein base, with the centre a nonzero ideal sheaf, and
  birationality of the morphism. These are **surplus** hypotheses, not standing conventions of
  the source, as an earlier draft of this note claimed: the section [Stacks, Tag 0C2I] in which
  0C2L lives carries no standing situation, the word "integral" does not occur anywhere in it,
  and each of its lemmas restates "let `X` be a Noetherian scheme" from scratch. The nonzero
  centre and the birationality are discharged in
  `StacksFrontier/AlgebraicGeometry/F6Rank136/ExceptionalCurveContractionBirational.lean`, and the
  integrality itself in
  `StacksFrontier/AlgebraicGeometry/F6Rank136/ExceptionalCurveContractionReduced.lean`, which
  weakens it to `[IsReduced X]`;
* `AlgebraicGeometry.Scheme.Hom.QuasiFiniteAt` for the classifying morphism somewhere over each
  point of the exceptional curve of the blowup, which in the source is the non-constancy of the
  induced map of exceptional curves, coming from the conormal sheaf comparison of
  [Stacks, Tag 01R4].

What is gone is `hres`.

## References

* [Stacks Project, Tag 0C2I](https://stacks.math.columbia.edu/tag/0C2I)
* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 02LS](https://stacks.math.columbia.edu/tag/02LS)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Restriction of a structure sheaf along an equality of opens is an isomorphism. This is the
`eqToHom` factor that `AlgebraicGeometry.morphismRestrict_app` leaves behind. -/
private instance isIso_presheaf_map_eqToHom_op {X : Scheme.{u}} {U V : X.Opens} (h : U = V) :
    IsIso (X.presheaf.map (eqToHom h).op) := by
  subst h
  simp only [eqToHom_refl, op_id, CategoryTheory.Functor.map_id]
  infer_instance

/-- **A proper morphism with `f_* 𝒪_X = 𝒪_Y` is an isomorphism over any open above which it is
quasi-finite.** Over such an open `W` the restriction `f|_W` is proper and locally quasi-finite,
hence finite by [Stacks, Tag 02LS], hence affine; and an affine morphism whose map on sections
over each affine open is an isomorphism is an isomorphism, which is what `IsIso f.c` supplies.

This is the step of [Stacks, Tag 0C2L] reading: the restriction `f^{-1}(Y ∖ {y}) ⟶ Y ∖ {y}` of
`f` is a finite morphism, hence an isomorphism since `f_* 𝒪_X = 𝒪_Y` and finite morphisms are
affine. -/
public theorem isIso_morphismRestrict_of_isIso_c_of_quasiFiniteAt {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [IsIso f.c] (W : Y.Opens)
    (hqf : ∀ x : X, f.base x ∈ W → quasiFiniteAt f x) :
    IsIso (f ∣_ W) := by
  have : LocallyQuasiFinite (f ∣_ W) := by
    refine ((forall_quasiFiniteAt_iff (f ∣_ W)).1 fun x' ↦ ?_).2
    refine ⟨finiteTypeAt_of_locallyOfFiniteType _ x', ?_⟩
    exact (RingHom.QuasiFinite.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f W x')).mpr (hqf x'.1 x'.2).2
  have : IsFinite (f ∣_ W) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have : IsIso ((f ∣_ W) ∣_ (⊤ : (W : Scheme.{u}).Opens)) := by
    refine Stacks.GlueSquishFactor.isIso_of_isAffineHom_of_isIso_app (f ∣_ W) ?_
    intro V _ _
    rw [morphismRestrict_app]
    have h1 : IsIso (f.app (W.ι ''ᵁ V)) := inferInstance
    exact IsIso.comp_isIso' h1 (isIso_presheaf_map_eqToHom_op _)
  exact Stacks.AlgebraicGeometry.InvertibleFiniteDescent.isIso_of_isIso_morphismRestrict_top _

/-- Membership in an open whose underlying set is `{y}ᶜ` means being different from `y`. -/
private theorem mem_iff_ne_of_coe_eq_compl {Y : Scheme.{u}} {y : Y} {W : Y.Opens}
    (hWc : (W : Set Y) = ({y} : Set Y)ᶜ) (p : Y) : p ∈ W ↔ p ≠ y := by
  rw [← SetLike.mem_coe, hWc]
  rfl

/-- **The classifying morphism is an isomorphism over every point off the exceptional curve.**
This is the binder `hres` of `AlgebraicGeometry.isIso_of_comp_blowUpToBase_eq_of_isBirational`,
discharged from the data [Stacks, Tag 0C2L] and its Stein reduction supply: `f` proper and
quasi-finite off the curve, carrying the curve to `y`, and satisfying `f_* 𝒪_X = 𝒪_Y`.

The open is `b^{-1}(Y ∖ {y})`, over which both `f` (by
`AlgebraicGeometry.isIso_morphismRestrict_of_isIso_c_of_quasiFiniteAt`) and the blowup morphism
`b` (by [Stacks, Tag 02OS]) are isomorphisms; cancelling `b` in `f|_W = g|_{b^{-1}W} ≫ b|_W`
leaves `g`. -/
public theorem isIso_morphismRestrict_blowUpClassifying {X Y : Scheme.{u}}
    {D : X.IdealSheafData} (f : X ⟶ Y) [IsProper f] [IsIso f.c] (y : Y)
    (hy : IsClosed ({y} : Set Y))
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y)
    (hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x)
    (g : X ⟶ AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))
    (hg : g ≫ AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f)
    (W : Y.Opens) (hWc : (W : Set Y) = ({y} : Set Y)ᶜ) :
    IsIso (g ∣_ (AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) ⁻¹ᵁ W)) := by
  subst hg
  set b := AlgebraicGeometry.blowUpToBase
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))
  have hfW : IsIso ((g ≫ b) ∣_ W) := by
    refine isIso_morphismRestrict_of_isIso_c_of_quasiFiniteAt _ W fun x hx ↦
      hqf x fun hmem ↦ (mem_iff_ne_of_coe_eq_compl hWc _).1 hx (hmaps x hmem)
  have hbW : IsIso (b ∣_ W) := by
    refine isIso_blowUpToBase_restrict_of_subset_compl_support _ W ?_
    rw [hWc, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact fun a ha ↦ ha
  have : IsIso (g ∣_ b ⁻¹ᵁ W ≫ b ∣_ W) := by
    rw [← morphismRestrict_comp]
    exact hfW
  exact IsIso.of_isIso_comp_right (g ∣_ b ⁻¹ᵁ W) (b ∣_ W)

/-- **The binder `hres` itself**, read off
`AlgebraicGeometry.isIso_morphismRestrict_blowUpClassifying` at the open `Y ∖ {y}`. -/
public theorem exists_isIso_morphismRestrict_blowUpClassifying {X Y : Scheme.{u}}
    {D : X.IdealSheafData} (f : X ⟶ Y) [IsProper f] [IsIso f.c] (y : Y)
    (hy : IsClosed ({y} : Set Y))
    (hmaps : ∀ x ∈ (D.support : Set X), f.base x = y)
    (hqf : ∀ x ∉ (D.support : Set X), quasiFiniteAt f x)
    (g : X ⟶ AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))
    (hg : g ≫ AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f)
    (w : AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))
    (hw : AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w ≠ y) :
    ∃ V : (AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))).Opens,
      w ∈ V ∧ IsIso (g ∣_ V) := by
  obtain ⟨W, hWc⟩ : ∃ W : Y.Opens, (W : Set Y) = ({y} : Set Y)ᶜ :=
    ⟨⟨{y}ᶜ, hy.isOpen_compl⟩, rfl⟩
  refine ⟨AlgebraicGeometry.blowUpToBase
    (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) ⁻¹ᵁ W, ?_,
    isIso_morphismRestrict_blowUpClassifying (D := D) f y hy hmaps hqf g hg W hWc⟩
  exact (mem_iff_ne_of_coe_eq_compl hWc _).2 hw

/-- **`hclassify` for a morphism carrying the Stein data.** The classifying morphism
`g : X ⟶ Bl_y Y` of a morphism `f` with an
`AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup` is an isomorphism, granted
integrality of the schemes with a nonzero centre, birationality of `f`, regularity of
`𝒪_{Y, y}` in dimension two, and quasi-finiteness of `g` somewhere over each point of the
exceptional curve of the blowup.

Against `AlgebraicGeometry.isIso_of_comp_blowUpToBase_eq_of_isBirational_of_isIntegral` the
binder `hres` is gone: the Stein data supplies `f_* 𝒪_X = 𝒪_Y`, which with quasi-finiteness off
the curve is all `AlgebraicGeometry.exists_isIso_morphismRestrict_blowUpClassifying` needs. -/
public theorem isIso_blowUpClassifying_of_steinSetup {X Y : Scheme.{u}} [IsIntegral X]
    [IsIntegral Y] {D : X.IdealSheafData} (f : X ⟶ Y) (y : Y)
    (hsetup : D.IsSteinContractionSetup f y) (hbir : IsBirational f)
    (hy : IsClosed ({y} : Set Y))
    (hI0 : Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) ≠ ⊥)
    (hreg : IsRegularLocalRing (Y.presheaf.stalk y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2)
    (g : X ⟶ AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))
    (hg : g ≫ AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f)
    (hqfE : ∀ w : AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w = y →
        ∃ x : X, g.base x = w ∧ g.QuasiFiniteAt x) :
    IsIso g :=
  have := hsetup.isNoetherian
  have := hsetup.isProper
  have := hsetup.isIso_c
  isIso_of_comp_blowUpToBase_eq_of_isBirational_of_isIntegral _ hI0 y hy rfl hreg hdim f hbir g
    hg hqfE fun w hw ↦ exists_isIso_morphismRestrict_blowUpClassifying f y hy
      ((D.forall_subschemeι_base_eq_iff_forall_mem_support f y).1 hsetup.base_eq)
      hsetup.quasiFinite_of_notMem g hg w hw

/-- **Both conjuncts of [Stacks, Tag 0C2L], with `hres` discharged.** The first factor
`f.toNormalization` of the Stein factorization of `f` is a contraction of the exceptional curve
— so a contraction exists and it is the Stein factorization of `f` — granted, of every morphism
carrying an `AlgebraicGeometry.Scheme.IdealSheafData.IsSteinContractionSetup`:

* `hreg` and `hdim`, that the local ring at the image point is regular of dimension two;
* `hfibre`, that the scheme-theoretic fibre over that point is the curve;
* `hintegral`, `hI0` and `hbir`, the chapter's standing conventions — the base integral, the
  centre a nonzero ideal sheaf, the morphism birational;
* `hqfE`, that the classifying morphism is quasi-finite somewhere over each point of the
  exceptional curve of the blowup.

Against
`AlgebraicGeometry.isContractionOfExceptionalCurve_toNormalization_of_steinSetup` the binder
`hclassify` has been traded for those; what it asked for beyond them, that the classifying
morphism be an isomorphism away from the exceptional curve, is now proved. -/
public theorem isContractionOfExceptionalCurve_toNormalization_of_steinSetup_of_isBirational
    {X Y : Scheme.{u}} [IsNoetherian Y] [IsIntegral X] {D : X.IdealSheafData} {k : Type u}
    [Field k] {e : projectiveLineProj k ≅ D.subscheme} (hE : D.IsExceptionalCurveOfFirstKind k e)
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
    (hintegral : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → IsIntegral Y')
    (hbir : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → IsBirational f')
    (hI0 : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → ∀ hy' : IsClosed ({y'} : Set Y'),
        Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y') ≠ ⊥)
    (hqfE : ∀ (Y' : Scheme.{u}) (f' : X ⟶ Y') (y' : Y'),
      D.IsSteinContractionSetup f' y' → ∀ (hy' : IsClosed ({y'} : Set Y'))
        (g : X ⟶ AlgebraicGeometry.blowUp
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y'))),
        g ≫ AlgebraicGeometry.blowUpToBase
            (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y')) = f' →
        ∀ w : AlgebraicGeometry.blowUp
            (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y')),
          AlgebraicGeometry.blowUpToBase
              (Scheme.IdealSheafData.vanishingIdeal (⟨{y'}, hy'⟩ : Closeds Y')) w = y' →
            ∃ x : X, g.base x = w ∧ g.QuasiFiniteAt x) :
    IsContractionOfExceptionalCurve D f.toNormalization :=
  isContractionOfExceptionalCurve_toNormalization_of_steinSetup hE f y hmaps hqf hreg hdim
    hfibre fun Y' f' y' hsetup hy' g hgf ↦
      have := hintegral Y' f' y' hsetup
      isIso_blowUpClassifying_of_steinSetup f' y' hsetup (hbir Y' f' y' hsetup) hy'
        (hI0 Y' f' y' hsetup hy') (hreg Y' f' y' hsetup) (hdim Y' f' y' hsetup) g hgf
        (hqfE Y' f' y' hsetup hy' g hgf)

end AlgebraicGeometry

end
