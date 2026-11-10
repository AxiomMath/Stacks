module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesSpecStructureSections
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesComapHomogeneousSections

/-!
# The ring map of `f' : X' ⟶ Spec B` on a homogeneous element of `B`

[Stacks, Tag 0897]'s comparison is `B`-linear, and the `B`-action on the target is through the
ring map `specAlgebraRingHom B f' : B →+* Γ(X', ⊤)` of the structure morphism
`f' : X' ⟶ Spec B`. This file **computes that ring map on a homogeneous element** `b` of degree
`k` of `B = ⨁ₙ Iⁿ`: it is the degree-`k` inclusion, into the total algebra `⨁ₙ ℐⁿ`, of the
global section `Stacks.Cohomology.FormalFunctions.gradedReesSection` of `ℐᵏ` that `b` names,
read in `Γ(X', ⊤)` through [Stacks, Tag 01LX] part (3).

That identity is the whole arithmetic content of the sheaf-level identity
`Stacks.Cohomology.FormalFunctions.ReesSmulCompatible`: on one side of that identity the scalar
`b` acts degreewise on `∐ₙ Mₙ` through `gradedReesSection`, and on the other it acts on `F'` as
a global function on `X'`, so the two agree exactly when this computation holds.

The computation is `Stacks.Cohomology.FormalFunctions.appTop_reesSpecStructure` — which presents
`f'.appTop` as four composable maps — evaluated factor by factor:

* the first factor, `Stacks.Cohomology.FormalFunctions.specReesAlgebraSheafIso`, is an
  isomorphism of algebra sheaves over the affine `Spec A`, so its component at `⊤` is the ring
  isomorphism it was built from (`Stacks.RelativeSpec.AlgebraSheaf.algebraHom_right_app_top`),
  namely `Stacks.Cohomology.FormalFunctions.specReesSectionsEquiv`;
* the second and third factors are the algebra-pullback unit followed by `ψ`, which is the exact
  shape `Stacks.Blowup.reesComapPullbackHom_app_unit` computes, and
  `Stacks.Cohomology.FormalFunctions.reesComapSections_specReesSectionsEquiv` evaluates the
  result at a homogeneous element;
* the fourth factor, [Stacks, Tag 01LX] part (3), is left standing: it is the identification
  `π_* 𝒪_{X'} ≅ ⨁ₙ ℐⁿ` along which the statement is read.

## Main results

* `Stacks.Cohomology.FormalFunctions.specReesAlgebraSheafIso_inv_right_app_top`: the first
  factor at `⊤`.
* `Stacks.Cohomology.FormalFunctions.ringSectionToGamma_baseRingToSections_top`: the function on
  `X` attached to an element of `A`, in the two spellings the two halves use.
* `Stacks.Cohomology.FormalFunctions.specAlgebraRingHom_reesSpecStructure_reesGrading`: **the
  ring map of `f'` on a homogeneous element of degree `k` is the degree-`k` inclusion of
  `gradedReesSection`.**

## Implementation notes

`Stacks.Cohomology.FormalFunctions.baseReesComapPullbackHom` is
`Stacks.Blowup.reesComapPullbackHom` transported along the equality
`baseIdealSheaf A I f = (specIdealSheaf I).comap f` of ideal sheaves, so nothing can be said about
it without moving that transport out of the way. The private lemma below does so in the only way
that works: the ideal sheaf is generalised to a variable `K` together with an equation
`K = (specIdealSheaf I).comap f`, which `subst` then eliminates, leaving the untransported
statement. The homogeneous section of the degree-`k` piece is an argument constrained only by its
ambient section, which determines it in nonnegative degree
(`Stacks.Blowup.reesPieceAmbient_injective`), so the caller may supply whichever spelling of it it
has a formula for.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 01OG](https://stacks.math.columbia.edu/tag/01OG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.Blowup Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.GradedProperCohomology

universe u

namespace Stacks.Cohomology.FormalFunctions

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-- **The identification `B̃ ≅ (Spec B ⟶ Spec A)_* 𝒪` at `⊤`**, read backwards: it carries the
global function on `Spec B` attached to `b ∈ B` to the section of `B̃` that
`Stacks.Cohomology.FormalFunctions.specReesSectionsEquiv` attaches to `b`. The isomorphism was
built by `Stacks.RelativeSpec.AlgebraSheaf.isoOfSectionsRingEquiv` out of exactly that ring
isomorphism, so its component at `⊤` is the ring isomorphism itself. -/
public theorem specReesAlgebraSheafIso_inv_right_app_top (b : ↥(reesAlgebra I)) :
    (specReesAlgebraSheafIso I).inv.right.hom.app (op ⊤)
        ((Scheme.ΓSpecIso (.of ↥(reesAlgebra I))).inv.hom b) =
      specReesSectionsEquiv I b := by
  let := isQuasicoherent_pushforwardAlgebra (reesSpecToBase I)
  rw [show (specReesAlgebraSheafIso I).inv.right.hom.app (op ⊤) =
    CommRingCat.ofHom ((specReesPushforwardSectionsEquiv I).symm :
      ↥((pushforwardAlgebra (reesSpecToBase I)).sections ⊤) →+*
        ↥((specReesAlgebraSheaf I).sections ⊤)) from
    AlgebraSheaf.algebraHom_right_app_top _ _ _]
  have h2 : (Scheme.ΓSpecIso (.of ↥(reesAlgebra I))).hom.hom
      ((Scheme.ΓSpecIso (.of ↥(reesAlgebra I))).inv.hom b) = b :=
    congrArg (fun φ : CommRingCat.of ↥(reesAlgebra I) ⟶ CommRingCat.of ↥(reesAlgebra I) =>
      φ.hom b) (Scheme.ΓSpecIso (.of ↥(reesAlgebra I))).inv_hom_id
  exact congrArg (specReesSectionsEquiv I) h2

/-- **The function on `X` attached to an element of the base ring, in the two spellings**: the
image of `a : A` under `AlgebraicGeometry.baseRingToSections` at `⊤`, which is how the Rees
sections of `ℐᵏ` are pinned down, is its image under the ring map of `f : X ⟶ Spec A` at `⊤`,
which is how the inverse image of a section of `Ĩᵏ` is computed. At `⊤` the restriction in
`baseRingToSections` is along the identity. -/
public theorem ringSectionToGamma_baseRingToSections_top (a : A) :
    ringSectionToGamma (baseRingToSections A X (op (⊤ : X.left.Opens)) a) =
      (X.hom.app (⊤ : (Spec (.of A)).Opens)) (specTopEquiv a) := by
  have h1 : (TopologicalSpace.Opens.leTop (⊤ : X.left.Opens)).op =
      𝟙 (op (⊤ : X.left.Opens)) := rfl
  change (X.left.ringCatSheaf.obj.map (TopologicalSpace.Opens.leTop (⊤ : X.left.Opens)).op).hom
      (((Scheme.ΓSpecIso (.of A)).inv ≫ X.hom.appTop).hom a) = _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

/-- **`ψ` on the unit image of a homogeneous element of `B`**, with the ideal sheaf generalised
so that the transport inside
`Stacks.Cohomology.FormalFunctions.baseReesComapPullbackHom` can be substituted away. The
homogeneous section of `ℐᵏ` is an argument constrained only by its ambient section, which
determines it (`Stacks.Blowup.reesPieceAmbient_injective`). -/
private theorem psi_app_unit_gen {K : X.left.IdealSheafData}
    (hK : K = (specIdealSheaf I).comap X.hom) (k : ℕ) (b : ↥(reesGrading I k))
    (σ : (reesPiece K (k : ℤ)).val.obj (op (⊤ : X.left.Opens)))
    (hσ : reesPieceAmbient K (k : ℤ) ⊤ σ =
      ringSectionToGamma (baseRingToSections A X (op ⊤) (reesElt I b))) :
    (hK ▸ reesComapPullbackHom X.hom (specIdealSheaf I) :
        (algebraPullback X.hom).obj (specReesAlgebraSheaf I) ⟶
          reesAlgebraSheaf K).right.hom.app (op ⊤)
        (((algebraPullbackPushforwardAdjunction X.hom).unit.app
          (specReesAlgebraSheaf I)).right.hom.app (op ⊤)
          (specReesSectionsEquiv I (b : ↥(reesAlgebra I)))) =
      (reesGradedAlgebra K).ungradedIncl (k : ℤ) σ := by
  subst hK
  have hcomp : (reesComapPullbackHom X.hom (specIdealSheaf I)).right.hom.app (op ⊤)
      (((algebraPullbackPushforwardAdjunction X.hom).unit.app
        (specReesAlgebraSheaf I)).right.hom.app (op ⊤)
        (specReesSectionsEquiv I (b : ↥(reesAlgebra I)))) =
      (reesGradedAlgebra ((specIdealSheaf I).comap X.hom)).ungradedIncl (k : ℤ)
        ((reesPieceComap X.hom (specIdealSheaf I) (k : ℤ)).val.app (op ⊤)
          (specReesSection I k b)) :=
    (reesComapPullbackHom_app_unit X.hom (specIdealSheaf I)
      (specReesSectionsEquiv I (b : ↥(reesAlgebra I)))).trans
      (reesComapSections_specReesSectionsEquiv I X.hom k b)
  refine hcomp.trans (congrArg ((reesGradedAlgebra ((specIdealSheaf I).comap X.hom)).ungradedIncl
    (k : ℤ)) ?_)
  refine reesPieceAmbient_injective ((specIdealSheaf I).comap X.hom) (k : ℤ)
    (Int.natCast_nonneg k) ⊤ ?_
  refine Eq.trans (reesPieceAmbient_comap X.hom (specIdealSheaf I) (k : ℤ) ⊤
    (specReesSection I k b)) ?_
  refine Eq.trans (congrArg (fun z => (X.hom.app (⊤ : (Spec (.of A)).Opens)) z)
    (reesPieceAmbient_specReesSection I k b)) ?_
  exact (hσ.trans (ringSectionToGamma_baseRingToSections_top X (reesElt I b))).symm

/-- **The ring map of `f' : X' ⟶ Spec B` on a homogeneous element of degree `k` of
`B = ⨁ₙ Iⁿ`**: it is the degree-`k` inclusion, into the total algebra `⨁ₙ ℐⁿ`, of the global
section `Stacks.Cohomology.FormalFunctions.gradedReesSection` of `ℐᵏ` attached to that element,
read in `Γ(X', ⊤)` through [Stacks, Tag 01LX] part (3).

This is `Stacks.Cohomology.FormalFunctions.appTop_reesSpecStructure` with its first three
factors evaluated: the first by
`Stacks.Cohomology.FormalFunctions.specReesAlgebraSheafIso_inv_right_app_top`, the second and
third by `Stacks.Blowup.reesComapPullbackHom_app_unit` and
`Stacks.Cohomology.FormalFunctions.reesComapSections_specReesSectionsEquiv`. -/
public theorem specAlgebraRingHom_reesSpecStructure_reesGrading (k : ℕ)
    (b : ↥(reesGrading I k)) :
    specAlgebraRingHom ↥(reesAlgebra I)
        (reesClosedImmersion I X ≫ pullback.fst (Over.mk (reesSpecToBase I)).hom X.hom)
        (b : ↥(reesAlgebra I)) =
      (pushforwardAlgebraIso
            (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv.right.hom.app (op ⊤)
        ((reesGradedAlgebra (baseIdealSheaf A I X.hom)).ungradedIncl (k : ℤ)
          ((gradedReesSection I X b).eval (op (⊤ : X.left.Opens)))) := by
  have hψ := psi_app_unit_gen I X (baseIdealSheaf_eq_comap_specIdealSheaf I X) k b
    ((gradedReesSection I X b).eval (op (⊤ : X.left.Opens)))
    (reesPieceAmbient_gradedReesSection I X b (op (⊤ : X.left.Opens)))
  have happ := congrArg (fun φ : Γ(Spec (.of ↥(reesAlgebra I)), ⊤) ⟶
      Γ((reesRelativeSpec I X).left, ⊤) => φ.hom
    ((Scheme.ΓSpecIso (.of ↥(reesAlgebra I))).inv.hom b)) (appTop_reesSpecStructure I X)
  refine happ.trans ?_
  refine Eq.trans (congrArg (fun z =>
    (pushforwardAlgebraIso (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv.right.hom.app
        (op ⊤)
      ((baseReesComapPullbackHom I X).right.hom.app (op ⊤)
        (((algebraPullbackPushforwardAdjunction X.hom).unit.app
          (specReesAlgebraSheaf I)).right.hom.app (op ⊤) z)))
    (specReesAlgebraSheafIso_inv_right_app_top I b)) ?_
  exact congrArg (fun z =>
    (pushforwardAlgebraIso (reesAlgebraSheaf (baseIdealSheaf A I X.hom))).inv.right.hom.app
      (op ⊤) z) hψ

end Stacks.Cohomology.FormalFunctions

end
