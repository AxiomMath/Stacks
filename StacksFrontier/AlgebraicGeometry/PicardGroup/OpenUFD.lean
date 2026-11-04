module

public import StacksFrontier.AlgebraicGeometry.PicardGroup.Descent
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Affine
public import StacksFrontier.AlgebraicGeometry.PicardUFD.Basic
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.StructureSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard group of an open subscheme of affine space over a UFD

Let `R` be a unique factorization domain. This file proves
[Stacks, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA): the Picard group of every open
subscheme of `Spec R`, and of every open subscheme of affine space `𝔸(ι; Spec R)` over `R`, is
trivial. In particular the Picard group of every open subscheme of affine space over a field is
trivial.

The argument is the one of the Stacks proof, in its general — not Noetherian — form, and no
Noetherian hypothesis is used anywhere:

* a polynomial ring over `R` is again a unique factorization domain, so part (2) reduces to
  part (1) along Mathlib's `AlgebraicGeometry.AffineSpace.SpecIso`;
* for `U ⊆ Spec R` a nonempty open, prime avoidance produces nonzero `f, g ∈ R` with
  `D(f) ∪ D(g) ⊆ U` whose common prime factors vanish identically on `U`
  (`Stacks.PicardUFD.exists_two_basicOpens_common_factors`);
* `D(f)` is the spectrum of the localization `R_f`, again a unique factorization domain, so its
  Picard group is trivial by the affine case
  `Stacks.PicardUFD.isTrivial_of_isInvertible_spec_of_ufd`;
* the map `R_f^* × R_g^* → R_{fg}^*` is surjective
  (`Stacks.PicardUFD.localization_units_split`), so an invertible module trivialized over each
  of `D(f)` and `D(g)` is trivial over their union
  (`Stacks.SheafOfModules.nonempty_iso_unit_of_two_opens`);
* finally, every regular function on `V ∩ (D(f) ∪ D(g))` extends uniquely to `V` for every open
  `V ⊆ U` (`Stacks.PicardUFD.functions_bijective_open_two_basicOpens`), which descends triviality
  from `D(f) ∪ D(g)` to `U` by `Stacks.PicardGroup.subsingleton_of_functions`.

## Main results

* `Stacks.PicardUFD.subsingleton_picardGroup_basicOpen`: the Picard group of a nonempty
  principal open of `Spec R` is trivial.
* `Stacks.PicardUFD.units_split_basicOpens` and `Stacks.PicardUFD.units_split_opens`: every unit
  on `D(f) ∩ D(g)` is a product of the restrictions of a unit on `D(f)` and a unit on `D(g)`,
  stated for the structure sheaf of `Spec R` and transported to two opens of an open subscheme.
* `Stacks.PicardUFD.subsingleton_picardGroup_two_basicOpens`: the Picard group of
  `D(f) ∪ D(g)` is trivial.
* `Stacks.PicardUFD.subsingleton_picardGroup_open_spectrum`: **Tag 0BDA, part (1)**.
* `Stacks.PicardUFD.subsingleton_picardGroup_open_affineSpace`: **Tag 0BDA, part (2)**.

## Implementation notes

The Noetherian shortcut of the Stacks proof — reduce to `Spec R` by extending an invertible
module across the complement, which is [Stacks, Tag 0BD9] — is **not** used. The tagged
statement carries no Noetherian hypothesis, and the general argument above covers the Noetherian
case too, so Tag 0BD9 is not a prerequisite of this tag.

That a polynomial ring in arbitrarily many variables over a unique factorization domain is again
one ([Stacks, Tag 0BC1]) is supplied by Mathlib's instance for `MvPolynomial`, so part (2) needs
no separate input.

## References

* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
* [Stacks Project, Tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
* [Stacks Project, Tag 0BC1](https://stacks.math.columbia.edu/tag/0BC1)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace Stacks.SheafOfModules

universe u

namespace Stacks.PicardUFD

/-- The Picard group of a nonempty principal open of the spectrum of a UFD is trivial: it is the
spectrum of a localization of `R`, which is again a UFD. -/
theorem subsingleton_picardGroup_basicOpen (R : CommRingCat.{u}) [IsDomain R]
    [UniqueFactorizationMonoid R] (f : R) (hf : f ≠ 0) :
    Subsingleton (PicardGroup
      (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f)).presheaf
      (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f)).ringCatSheaf.2) := by
  let S := Localization.Away f
  have : IsDomain S := IsLocalization.Away.isDomain S hf
  have : UniqueFactorizationMonoid S :=
    UniqueFactorizationMonoid.of_isLocalization (S := Submonoid.powers f) S
  have hS : Subsingleton (PicardGroup (Spec (.of S)).presheaf (Spec (.of S)).ringCatSheaf.2) :=
    subsingleton_picardGroup _ _ fun L hL =>
      have := hL; Stacks.PicardUFD.isTrivial_of_isInvertible_spec_of_ufd S L
  exact Stacks.PicardGroup.subsingleton_of_iso (basicOpenIsoSpecAway f).symm hS

/-- Every unit on `D(f) ∩ D(g)` is the product of the restrictions of a unit on `D(f)` and a
unit on `D(g)`. -/
theorem units_split_basicOpens (R : CommRingCat.{u}) [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (w : ((Spec.structureSheaf R).obj.obj
      (op (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g)))ˣ) :
    ∃ (u : ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen f)))ˣ)
      (v : ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen g)))ˣ),
      (Spec.structureSheaf R).obj.map (homOfLE (inf_le_left :
            PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g ≤
              PrimeSpectrum.basicOpen f)).op
          (u : (Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen f))) *
        (Spec.structureSheaf R).obj.map (homOfLE (inf_le_right :
            PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g ≤
              PrimeSpectrum.basicOpen g)).op
          (v : (Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen g))) = (w : _) := by
  have hA : IsLocalization.Away (f * g) ((Spec.structureSheaf R).obj.obj
      (op (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g))) := by
    have H : ∀ (V : (Spec R).Opens), V = PrimeSpectrum.basicOpen (f * g) →
        IsLocalization.Away (f * g) ((Spec.structureSheaf R).obj.obj (op V)) := by
      rintro V rfl
      infer_instance
    exact H _ (PrimeSpectrum.basicOpen_mul f g).symm
  let φ : ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen f))) →ₐ[R]
      ((Spec.structureSheaf R).obj.obj
        (op (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g))) :=
    { __ := ((Spec.structureSheaf R).obj.map (homOfLE (inf_le_left :
        PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g ≤
          PrimeSpectrum.basicOpen f)).op).hom
      commutes' := fun _ => rfl }
  let ψ : ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen g))) →ₐ[R]
      ((Spec.structureSheaf R).obj.obj
        (op (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g))) :=
    { __ := ((Spec.structureSheaf R).obj.map (homOfLE (inf_le_right :
        PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g ≤
          PrimeSpectrum.basicOpen g)).op).hom
      commutes' := fun _ => rfl }
  exact Stacks.PicardUFD.localization_units_split f g hf hg φ ψ w

/-- The unit-splitting statement transported to two opens of an open subscheme of `Spec R`
whose images are the two principal opens. -/
theorem units_split_opens (R : CommRingCat.{u}) [IsDomain R] [UniqueFactorizationMonoid R]
    [NormalizationMonoid R] (U : (Spec R).Opens) (V W : U.toScheme.Opens) (f g : R)
    (hf : f ≠ 0) (hg : g ≠ 0) (hV : U.ι ''ᵁ V = PrimeSpectrum.basicOpen f)
    (hW : U.ι ''ᵁ W = PrimeSpectrum.basicOpen g) :
    ∀ w : (U.toScheme.presheaf.obj (op (V ⊓ W)))ˣ,
      ∃ (u : (U.toScheme.presheaf.obj (op V))ˣ) (v : (U.toScheme.presheaf.obj (op W))ˣ),
        U.toScheme.presheaf.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op u.val *
            U.toScheme.presheaf.map (homOfLE (inf_le_right : V ⊓ W ≤ W)).op v.val = w.val := by
  have hi : U.ι ''ᵁ (V ⊓ W) = PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g := by
    rw [← hV, ← hW]
    exact Opens.ext (Set.image_inter U.ι.isOpenEmbedding.injective)
  show ∀ w : ((Spec.structureSheaf R).obj.obj (op (U.ι ''ᵁ (V ⊓ W))))ˣ,
    ∃ (u : ((Spec.structureSheaf R).obj.obj (op (U.ι ''ᵁ V)))ˣ)
      (v : ((Spec.structureSheaf R).obj.obj (op (U.ι ''ᵁ W)))ˣ),
      (Spec.structureSheaf R).obj.map (homOfLE (U.ι.image_mono
          (inf_le_left : V ⊓ W ≤ V))).op u.val *
        (Spec.structureSheaf R).obj.map (homOfLE (U.ι.image_mono
          (inf_le_right : V ⊓ W ≤ W))).op v.val = w.val
  have H : ∀ (P Q T : (Spec R).Opens) (hTP : T ≤ P) (hTQ : T ≤ Q),
      P = PrimeSpectrum.basicOpen f → Q = PrimeSpectrum.basicOpen g →
      T = PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g →
      ∀ w : ((Spec.structureSheaf R).obj.obj (op T))ˣ,
        ∃ (u : ((Spec.structureSheaf R).obj.obj (op P))ˣ)
          (v : ((Spec.structureSheaf R).obj.obj (op Q))ˣ),
          (Spec.structureSheaf R).obj.map (homOfLE hTP).op u.val *
            (Spec.structureSheaf R).obj.map (homOfLE hTQ).op v.val = w.val := by
    rintro P Q T hTP hTQ rfl rfl rfl
    exact units_split_basicOpens R f g hf hg
  exact H _ _ _ _ _ hV hW hi

/-- The image under `U.ι` of the preimage of an open `T ≤ U` is `T`. -/
private theorem image_preimage_eq_of_le {R : CommRingCat.{u}} (U T : (Spec R).Opens) (h : T ≤ U) :
    U.ι ''ᵁ (U.ι ⁻¹ᵁ T) = T :=
  (U.ι.image_preimage_eq_opensRange_inf T).trans <| by
    simpa only [Scheme.Opens.opensRange_ι] using inf_eq_right.mpr h

/-- Triviality of the Picard group of an open `T ⊆ Spec R` passes to any open of `U` whose
image under `U.ι` is `T`. -/
private theorem subsingleton_picardGroup_preimage {R : CommRingCat.{u}} {U T : (Spec R).Opens}
    {V : U.toScheme.Opens} (h : U.ι ''ᵁ V = T)
    (hT : Subsingleton (PicardGroup T.toScheme.presheaf T.toScheme.ringCatSheaf.2)) :
    Subsingleton (PicardGroup V.toScheme.presheaf V.toScheme.ringCatSheaf.2) :=
  Stacks.PicardGroup.subsingleton_of_iso (U.ι.isoImage _ ≪≫ (Spec R).isoOfEq h).symm hT

/-- The Picard group of the union of two nonempty principal opens of the spectrum of a UFD is
trivial. -/
theorem subsingleton_picardGroup_two_basicOpens (R : CommRingCat.{u}) [IsDomain R]
    [UniqueFactorizationMonoid R] [NormalizationMonoid R] (f g : R) (hf : f ≠ 0) (hg : g ≠ 0)
    (P : (Spec R).Opens)
    (hP : P = PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g) :
    Subsingleton (PicardGroup P.toScheme.presheaf P.toScheme.ringCatSheaf.2) := by
  have hVim := image_preimage_eq_of_le P (PrimeSpectrum.basicOpen f)
    (by rw [hP]; exact le_sup_left)
  have hWim := image_preimage_eq_of_le P (PrimeSpectrum.basicOpen g)
    (by rw [hP]; exact le_sup_right)
  have hcover : (P.ι ⁻¹ᵁ PrimeSpectrum.basicOpen f) ⊔ (P.ι ⁻¹ᵁ PrimeSpectrum.basicOpen g)
      = ⊤ :=
    (congrArg (fun T : (Spec R).Opens => P.ι ⁻¹ᵁ T) hP).symm.trans
      (Scheme.Opens.ι_preimage_self P)
  refine Stacks.PicardGroup.subsingleton_of_two_opens _ _ hcover ?_ ?_
    (units_split_opens R P _ _ f g hf hg hVim hWim)
  · exact subsingleton_picardGroup_preimage hVim (subsingleton_picardGroup_basicOpen R f hf)
  · exact subsingleton_picardGroup_preimage hWim (subsingleton_picardGroup_basicOpen R g hg)

/-- **Stacks Project, Tag 0BDA, part (1).** The Picard group of any open subscheme of the
spectrum of a unique factorization domain is trivial.

The empty open is handled separately; for a nonempty one, prime avoidance gives two principal
opens `D(f), D(g) ⊆ U` whose union has trivial Picard group and across whose complement in `U`
regular functions extend, so triviality descends to `U`. -/
@[stacks 0BDA "part (1)", sga "1 XI 6.5" "factorial-ring example"]
theorem subsingleton_picardGroup_open_spectrum (R : Type u) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (U : (Spec (.of R)).Opens) :
    Subsingleton (PicardGroup U.toScheme.presheaf U.toScheme.ringCatSheaf.2) := by
  classical
  by_cases hU : IsEmpty U.toScheme
  · exact Stacks.PicardGroup.subsingleton_of_isEmpty hU
  let _ : StrongNormalizationMonoid R := UniqueFactorizationMonoid.strongNormalizationMonoid
  obtain ⟨f, g, hf, hg, hfU, hgU, hfg⟩ :=
    Stacks.PicardUFD.exists_two_basicOpens_common_factors R U (not_isEmpty_iff.mp hU)
  have hWim := image_preimage_eq_of_le U (PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g)
    (sup_le hfU hgU)
  have hPic := subsingleton_picardGroup_preimage hWim
    (subsingleton_picardGroup_two_basicOpens (.of R) f g hf hg _ rfl)
  exact Stacks.PicardGroup.subsingleton_of_functions _
    (Stacks.PicardUFD.functions_bijective_open_two_basicOpens (.of R) f g hf hg U hfU hgU hfg)
    hPic

/-- **Stacks Project, Tag 0BDA, part (2).** The Picard group of any open subscheme of affine
space over a unique factorization domain is trivial. In particular this holds over a field.

Affine space over `R` is the spectrum of `R[ι]`, which is again a unique factorization domain
(Tag 0BC1, Mathlib's instance for `MvPolynomial`), so this is part (1) transported along
`AlgebraicGeometry.AffineSpace.SpecIso`. -/
@[stacks 0BDA "part (2)", ega "I 2.4.8" "more general"]
theorem subsingleton_picardGroup_open_affineSpace (R : Type u) [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (ι : Type u) (U : (AffineSpace ι (Spec (.of R))).Opens) :
    Subsingleton (PicardGroup U.toScheme.presheaf U.toScheme.ringCatSheaf.2) :=
  Stacks.PicardGroup.subsingleton_of_iso
    (Scheme.Hom.preimageIso (AffineSpace.SpecIso ι (.of R)).symm.hom U)
    (subsingleton_picardGroup_open_spectrum (MvPolynomial ι R) _)

end Stacks.PicardUFD

end
