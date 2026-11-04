module

public import StacksFrontier.AlgebraicGeometry.SymGenDegreeOne.Unit
public import StacksFrontier.AlgebraicGeometry.SymAlgebraQcohPieces.Basic

/-!
# The sections of a homogeneous piece of `Sym(E)` over an affine open

Let `X` be a scheme and `E` a quasi-coherent `𝒪_X`-module. The degree-`n` piece of
`AlgebraicGeometry.Scheme.Modules.symmetricAlgebra X E` is the sheafification of the
sectionwise symmetric power
`U ↦ Sym^n_{Γ(X, U)}(Γ(E, U))`, and a sheafification is not computed by its presheaf's sections.
**This file shows that over an affine open it is**: the sheafification unit
`Sym^n_{Γ(X, V)}(Γ(E, V)) ⟶ Γ(Sym^n(E), V)` is surjective for `V` affine.

That surjectivity is what makes degree-one generation of the graded ring of sections provable:
every section of a homogeneous piece over an affine open is the image of an actual element of a
symmetric power, which is a sum of products of degree-one elements.

## Main results

* `Stacks.SymGraded.AffinePieces.surjective_toTilde_top`: the base-change comparison with an
  associated sheaf is surjective on global sections, because `D(1)` is all of `Spec R`.
* `Stacks.SymGraded.AffinePieces.surjective_sheafifyUnit_affineBaseChange` and
  `surjective_sheafifyUnit_presheafRestrict`: the intermediate steps on `Spec Γ(X, V)`.
* `Stacks.SymGraded.AffinePieces.surjective_sheafifyUnit_image_top`: **the target.** The
  sheafification unit of the sectionwise degree-`n` symmetric power is surjective on the sections
  over an affine open of `X`.

## Implementation notes

**The route is the three morphisms `Stacks.SymGraded.AffinePieces` already has, read through the
criterion of `StacksDraft.AlgebraicGeometry.F3.SymGenDegreeOne.Unit`.** Writing `P` for the
sectionwise symmetric power on `X` and `V` for an affine open:

1. `Stacks.AffineBaseChange.toTilde` is a locally bijective comparison from the base-change
   presheaf of `Sym^n_{Γ(X, V)}(Γ(E, V))` into an *associated sheaf*, and it is surjective over
   `⊤` because over the basic open `D(1) = ⊤` it is the identification `R ⊗_R N ≅ N`. The
   criterion turns that into surjectivity of the unit of the base-change presheaf over `⊤`.
2. `Stacks.SymGraded.AffinePieces.toPiece` is locally bijective from the base-change presheaf to
   the restriction of `P` along `fromSpec`, so surjectivity of the unit transfers to the
   restriction of `P`.
3. The restriction along `fromSpec` of the unit of `P` is itself locally bijective into the
   restriction of `P^#`, a sheaf, so the criterion applies again — and the restricted unit over
   `⊤` *is* the unit of `P` over `fromSpec ''ᵁ ⊤`, on the nose, because the sections of a
   restricted presheaf over `⊤` are the sections over the image of `⊤`.

No multiplicativity of any of these comparisons is needed, which is the point of routing through
surjectivity of the unit rather than through the isomorphism
`Stacks.SymGraded.AffinePieces.sheafificationIsoTilde`: the unit is multiplicative for free, by
`Stacks.GradedAlgebra.sheafify_mul_unit`, whereas the isomorphism's multiplicativity is not
proved anywhere.

**The affine open is carried as an equation rather than rewritten.** The statement is for an open
`W` with `fromSpec ''ᵁ ⊤ = W` and is used at `W = V`. Rewriting `V` into `fromSpec ''ᵁ ⊤` is not
possible: the right-hand side mentions `hV`, hence `V`, so the rewrite is circular. `subst` on a
hypothesis of that shape is.

## References

* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)

## Not done here

**No tag is claimed.** This is one input to Tag 01CG's third assertion over an affine base, whose
isomorphism form is `Stacks.SymGraded.AffinePieces.sheafificationIsoTilde`; nothing here states
that tag. Injectivity of the unit over an affine open is not proved, nor is anything about the
sections over a non-affine open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ImmersionRestrict
open scoped TensorProduct

namespace Stacks.SymGraded.AffinePieces

universe u

/-- **The comparison with the associated sheaf is surjective on global sections.** `D(1)` is all
of `Spec R`, so this is `Stacks.AffineBaseChange.surjective_toTildeₗ_basicOpen` at `1`. -/
theorem surjective_toTilde_top {R : CommRingCat.{u}} (N : ModuleCat.{u} R) :
    Function.Surjective fun x => PresheafOfModules.Hom.app (AffineBaseChange.toTilde N)
      (op (⊤ : (Spec R).Opens)) x := by
  rw [show (⊤ : (Spec R).Opens) = AffineBaseChange.specBasicOpen (1 : R) from
    PrimeSpectrum.basicOpen_one.symm]
  exact AffineBaseChange.surjective_toTildeₗ_basicOpen N 1

variable {X : Scheme.{u}} (E : X.Modules) {V : X.Opens} (hV : IsAffineOpen V) (n : ℤ)

/-- The sheafification unit of the base-change presheaf of `Sym^n_{Γ(X, V)}(Γ(E, V))` is
surjective on the global sections of `Spec Γ(X, V)`. -/
theorem surjective_sheafifyUnit_affineBaseChange [E.IsQuasicoherent] :
    Function.Surjective fun x => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
        (AffineBaseChange.presheaf (pieceAt E V n))) (op (⊤ : (Spec Γ(X, V)).Opens)) x := by
  refine (Stacks.PresheafOfModules.surjective_sheafifyUnit_app_iff
    (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj) (tilde (pieceAt E V n))
    (AffineBaseChange.toTilde (pieceAt E V n))
    (AffineBaseChange.isLocallyInjective_toTilde (pieceAt E V n))
    (AffineBaseChange.isLocallySurjective_toTilde (pieceAt E V n)) (op ⊤)).2 ?_
  exact surjective_toTilde_top _

/-- The sheafification unit of the restriction along `fromSpec` of the sectionwise degree-`n`
symmetric power is surjective on the global sections of `Spec Γ(X, V)`. -/
theorem surjective_sheafifyUnit_presheafRestrict [E.IsQuasicoherent] :
    Function.Surjective fun x => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
        ((presheafRestrict hV.fromSpec).obj (siteGradedPiece E.val n)))
      (op (⊤ : (Spec Γ(X, V)).Opens)) x :=
  Stacks.PresheafOfModules.surjective_sheafifyUnit_app_of_isLocallyBijective _
    (toPiece E hV n) (isLocallyInjective_toPiece E hV n) (isLocallySurjective_toPiece E hV n)
    (op ⊤) (surjective_sheafifyUnit_affineBaseChange E n)

/-- **The sheafification unit of the sectionwise degree-`n` symmetric power is surjective on the
sections over an affine open.** Every section of the degree-`n` piece of `Sym(E)` over an affine
open `V` is the image of an element of `Sym^n_{Γ(X, V)}(Γ(E, V))`. -/
theorem surjective_sheafifyUnit_image_top [E.IsQuasicoherent] (W : X.Opens)
    (hW : hV.fromSpec ''ᵁ (⊤ : (Spec Γ(X, V)).Opens) = W) :
    Function.Surjective fun x => PresheafOfModules.Hom.app
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n))
      (op W) x := by
  subst hW
  have hunitinj := Stacks.AlgebraicGeometry.SheafifyRestrict.isLocallyInjective_sheafifyUnit
    (siteGradedPiece E.val n)
  have hunitsurj := Stacks.AlgebraicGeometry.SheafifyRestrict.isLocallySurjective_sheafifyUnit
    (siteGradedPiece E.val n)
  exact (Stacks.PresheafOfModules.surjective_sheafifyUnit_app_iff
    (𝟙 (Spec Γ(X, V)).ringCatSheaf.obj)
    ((Scheme.Modules.restrictFunctor hV.fromSpec).obj
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (siteGradedPiece E.val n)))
    ((presheafRestrict hV.fromSpec).map
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)))
    (isLocallyInjective_presheafRestrict_map hV.fromSpec
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)))
    (isLocallySurjective_presheafRestrict_map hV.fromSpec
      (PresheafOfModules.sheafifyUnit (𝟙 X.ringCatSheaf.obj) (siteGradedPiece E.val n)))
    (op ⊤)).1 (surjective_sheafifyUnit_presheafRestrict E hV n)

end Stacks.SymGraded.AffinePieces

end
