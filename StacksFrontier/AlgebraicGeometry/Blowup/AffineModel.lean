module

public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The affine model of the blowup is the blowup of an affine scheme

`StacksFrontier/AlgebraicGeometry/Blowup/Basic.lean` builds the affine model
`Stacks.Blowup.blowUpSpec I = Proj (⨁ₙ Iⁿ)` of the blowup of `Spec R` in an ideal `I ⊆ R`, and
`StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean` builds the blowup
`Stacks.Blowup.blowUp ℐ` of an arbitrary scheme `S` in a quasi-coherent sheaf of ideals `ℐ` as a
relative `Proj`. The two have so far been related only through
`Stacks.Blowup.isPullback_blowUpChart`, which exhibits the affine model over an affine open `U` of
`S` as the part of the blowup lying over `U`.

This file draws the consequence that was missing: when `S` itself is affine the chart at `U = ⊤`
is already the whole blowup, because `(⊤ : S.Opens).ι` is an isomorphism and the chart square is
its base change. So the blowup of an affine scheme *is* its affine model, and every statement
proved about `blowUpSpec` transfers to `blowUp`.

## Main definitions

* `Stacks.Blowup.blowUpSpecIso`: the isomorphism `blowUpSpec (ℐ(⊤)) ≅ blowUp ℐ` for an ideal
  sheaf `ℐ` on an affine scheme `S`.
* `Stacks.Blowup.blowUpSpecIsoRees`: the same isomorphism onto `AlgebraicGeometry.blowUp ℐ`, the
  blowup built as the relative `Proj` of the Rees algebra *sheaf*. This is the spelling the rest
  of the library uses.

## Main results

* `Stacks.Blowup.isIso_blowUpChart_top`: the chart of the blowup at the top affine open of an
  affine base is an isomorphism.
* `Stacks.Blowup.blowUpSpecIso_hom_blowUpToBase` and
  `Stacks.Blowup.blowUpSpecIsoRees_hom_blowUpToBase`: the isomorphisms are isomorphisms *over the
  base*, carrying the structure morphism `Stacks.Blowup.toSpec` of the affine model to the blowup
  morphism. A bare isomorphism of schemes would not identify the two constructions.

## Implementation notes

No `@[stacks]` attribute is attached. Tag 01OG, the blowup of a scheme in a quasi-coherent sheaf
of ideals, and tag 0804, the identification of the part of the blowup over an affine open with
`Proj` of the Rees algebra, are both already registered on the global construction in
`StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean`; the content here is the degenerate case
`U = ⊤` of that identification, not a further assertion of the source.

## References

* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Blowup

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData) [IsAffine S]

/-- **The chart of the blowup at the top affine open of an affine base is an isomorphism.** -/
instance isIso_blowUpChart_top :
    IsIso (blowUpChart ℐ ⟨⊤, isAffineOpen_top S⟩) :=
  (isPullback_blowUpChart ℐ ⟨⊤, isAffineOpen_top S⟩).isIso_snd_of_isIso
    ⟨S.topIso.inv, S.topIso.hom_inv_id, S.topIso.inv_hom_id⟩

/-- The chart of the blowup at the top affine open of an affine base, read as a morphism out of
the affine model `Stacks.Blowup.blowUpSpec` of the blowup. -/
def blowUpSpecToBlowUp : blowUpSpec (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) ⟶ blowUp ℐ :=
  blowUpChart ℐ ⟨⊤, isAffineOpen_top S⟩

/-- The morphism `Stacks.Blowup.blowUpSpecToBlowUp ℐ` from the affine model to the blowup of an
affine scheme is an isomorphism. -/
instance isIso_blowUpSpecToBlowUp : IsIso (blowUpSpecToBlowUp ℐ) :=
  isIso_blowUpChart_top ℐ

/-- **The blowup of an affine scheme is the affine model of the blowup.** The blowup of `S` in a
quasi-coherent sheaf of ideals `ℐ`, built as a relative `Proj`, is the ordinary `Proj` of the Rees
algebra of the single ideal `ℐ(⊤) ⊆ Γ(S, ⊤)`. The isomorphism is over `S`: see
`Stacks.Blowup.blowUpSpecIso_hom_blowUpToBase`. -/
def blowUpSpecIso : blowUpSpec (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) ≅ blowUp ℐ :=
  asIso (blowUpSpecToBlowUp ℐ)

/-- The forward morphism of `Stacks.Blowup.blowUpSpecIso ℐ` is
`Stacks.Blowup.blowUpSpecToBlowUp ℐ`. -/
@[simp]
theorem blowUpSpecIso_hom :
    (blowUpSpecIso ℐ).hom = blowUpSpecToBlowUp ℐ :=
  rfl

/-- **The identification of the blowup with its affine model is an isomorphism over the base**: it
carries the blowup morphism to the structure morphism `Stacks.Blowup.toSpec` of the affine model,
read through the identification `Spec Γ(S, ⊤) ≅ S` of the affine base with the spectrum of its
global sections. -/
theorem blowUpSpecToBlowUp_blowUpToBase :
    blowUpSpecToBlowUp ℐ ≫ blowUpToBase ℐ =
      toSpec (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) ≫ S.isoSpec.inv :=
  (((isPullback_blowUpChart ℐ ⟨⊤, isAffineOpen_top S⟩).w.symm.trans
        (congrArg (· ≫ (⊤ : S.Opens).ι)
          (chartToOpen_eq ℐ ⟨⊤, isAffineOpen_top S⟩))).trans
      (Category.assoc _ _ _)).trans
    (congrArg (toSpec (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) ≫ ·)
      ((IsAffineOpen.isoSpec_inv_ι (isAffineOpen_top S)).trans IsAffineOpen.fromSpec_top))

/-- The identification of the blowup with its affine model, as an isomorphism over the base. -/
theorem blowUpSpecIso_hom_blowUpToBase :
    (blowUpSpecIso ℐ).hom ≫ blowUpToBase ℐ =
      toSpec (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) ≫ S.isoSpec.inv :=
  blowUpSpecToBlowUp_blowUpToBase ℐ

/-- The inverse of the identification is an isomorphism over the base, in the form that rewrites
the structure morphism of the affine model. -/
theorem blowUpSpecIso_inv_toSpec :
    (blowUpSpecIso ℐ).inv ≫ toSpec (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) ≫ S.isoSpec.inv =
      blowUpToBase ℐ :=
  (Iso.inv_comp_eq _).mpr (blowUpSpecIso_hom_blowUpToBase ℐ).symm

/-! ### The affine model and the blowup of the Rees algebra sheaf -/

/-- **The blowup of an affine scheme, built as the relative `Proj` of the Rees algebra sheaf, is
the affine model of the blowup.** This is `Stacks.Blowup.blowUpSpecIso` read through
`AlgebraicGeometry.blowUpIso`, the identification of the two global constructions of the blowup.
It is over `S`: see `Stacks.Blowup.blowUpSpecIsoRees_hom_blowUpToBase`. -/
@[sga "6 VII 1.8" "special case"]
def blowUpSpecIsoRees :
    blowUpSpec (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) ≅ AlgebraicGeometry.blowUp ℐ :=
  blowUpSpecIso ℐ ≪≫ (AlgebraicGeometry.blowUpIso ℐ).symm

omit [IsAffine S] in
/-- The identification of the two global blowups is over the base in the form that rewrites the
structure morphism of the relative `Proj` of the Rees algebra sheaf. -/
theorem blowUpIso_inv_blowUpToBase :
    (AlgebraicGeometry.blowUpIso ℐ).inv ≫ AlgebraicGeometry.blowUpToBase ℐ = blowUpToBase ℐ :=
  (Iso.inv_comp_eq _).mpr (AlgebraicGeometry.blowUpIso_hom_blowUpToBase ℐ).symm

/-- **The identification of the blowup of the Rees algebra sheaf with the affine model is an
isomorphism over the base.** This is the form in which the affine model reaches the rest of the
library, which states its blowups as `AlgebraicGeometry.blowUp`. -/
theorem blowUpSpecIsoRees_hom_blowUpToBase :
    (blowUpSpecIsoRees ℐ).hom ≫ AlgebraicGeometry.blowUpToBase ℐ =
      toSpec (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) ≫ S.isoSpec.inv := by
  rw [blowUpSpecIsoRees, Iso.trans_hom, Category.assoc, Iso.symm_hom,
    blowUpIso_inv_blowUpToBase]
  exact blowUpSpecIso_hom_blowUpToBase ℐ

end Stacks.Blowup

end
