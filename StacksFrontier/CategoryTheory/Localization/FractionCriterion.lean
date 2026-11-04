module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

/-!
# A functor that computes fractions is a localization

Let `W` be a class of morphisms of `C` with a right calculus of fractions and let `F : C ⥤ D`
invert `W`.  Then `F` presents `D` as the localization of `C` at `W` as soon as three
conditions hold, one for each of the ways a functor can fail to be an equivalence:

* `F` is essentially surjective;
* every morphism `F.obj a ⟶ F.obj b` is the image of a right fraction `a ⟵ c ⟶ b`, that is, is
  of the form `(F.map s)⁻¹ ≫ F.map f` with `W s`;
* two morphisms of `C` with the same image under `F` are equalized by precomposition with a
  morphism of `W`.

This is the criterion the Verdier-localization arguments of a derived category are organised
around: the three conditions are exactly "every object is represented", "every morphism is
represented by a roof" and "a morphism represented by zero is annihilated by a roof", and each
is a statement about `C` and `F` alone, with no mention of `W.Localization`.

## Main results

* `CategoryTheory.MorphismProperty.rightFractionRel_of_map_eq`: two right fractions with the
  same image under `F` are equivalent, as soon as `F` is faithful up to precomposition by a
  morphism of `W`.
* `CategoryTheory.Localization.isLocalization_of_rightFractions`: the criterion.

## Implementation notes

The proof factors through the canonical localization `W.Q : C ⥤ W.Localization` and the lift
`G := Localization.lift F hF W.Q`: the criterion is that `G` is an equivalence, and
`CategoryTheory.Functor.IsLocalization.of_equivalence_target` then transports the predicate from
`W.Q` to `F`.

Everything about `G` is read off a single identity, `map_rightFraction_comp_fac` below: the
image under `G` of the fraction computed in `W.Localization` is the fraction computed in `D`,
conjugated by `CategoryTheory.Localization.fac`.  It is proved by cancelling the isomorphism
`G.map (W.Q.map φ.s)`, so no inverse of `F.map φ.s` is ever written down and no `Functor.map_inv`
is needed.

Fullness and faithfulness of `G` are stated for the objects of `W.Localization` in the image of
`W.Q` and then transported to arbitrary objects along `CategoryTheory.Functor.objObjPreimageIso`,
`W.Q` being essentially surjective.  Writing them directly for arbitrary objects is not possible:
a morphism of `W.Localization` is only a fraction between objects of the form `W.Q.obj a`.

The hypotheses are stated with the denominator of the fraction existentially bound as a bare
object and morphism rather than as a `MorphismProperty.RightFraction`, so that a caller which has
produced a roof does not have to package it first; the packaging happens inside.
-/

@[expose] public noncomputable section

open CategoryTheory Category

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace MorphismProperty

/-- **Two right fractions with the same image under `F` are equivalent.**  Choose by the Ore
condition a common refinement `t₁ ≫ φ.s = t₂ ≫ ψ.s` of the two denominators; the two numerators
then have the same image under `F` after composing with it, so a further morphism of `W`
equalizes them, and that is the datum of the equivalence. -/
theorem rightFractionRel_of_map_eq (F : C ⥤ D) (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] (hF : W.IsInvertedBy F)
    (hfaithful : ∀ ⦃a b : C⦄ (u v : a ⟶ b), F.map u = F.map v →
      ∃ (c : C) (t : c ⟶ a), W t ∧ t ≫ u = t ≫ v)
    {a b : C} (φ ψ : W.RightFraction a b)
    (h : φ.map F hF = ψ.map F hF) :
    RightFractionRel φ ψ := by
  obtain ⟨χ, hχ⟩ :=
    (MorphismProperty.LeftFraction.mk (W := W) φ.s ψ.s ψ.hs).exists_rightFraction
  have hst : χ.s ≫ φ.s = χ.f ≫ ψ.s := hχ
  have key : ∀ (θ : W.RightFraction a b) (d : C) (t : d ⟶ θ.X'),
      F.map (t ≫ θ.f) = F.map (t ≫ θ.s) ≫ θ.map F hF := fun θ _ t => by
    rw [F.map_comp, F.map_comp, assoc, RightFraction.map_s_comp_map]
  have hnum : F.map (χ.s ≫ φ.f) = F.map (χ.f ≫ ψ.f) := by
    rw [key φ _, key ψ _, hst, h]
  obtain ⟨c, r, hr, hrfac⟩ := hfaithful _ _ hnum
  refine ⟨c, r ≫ χ.s, r ≫ χ.f, ?_, ?_, ?_⟩
  · rw [assoc, assoc, hst]
  · simpa only [assoc] using hrfac
  · rw [assoc]
    exact W.comp_mem _ _ hr (W.comp_mem _ _ χ.hs φ.hs)

end MorphismProperty

namespace Localization

/-- The image under the lift `G` of a right fraction computed in `W.Localization` is the right
fraction computed in `D`, conjugated by `Localization.fac`.  Both sides become
`(fac …).hom.app φ.X' ≫ F.map φ.f` after composing with the isomorphism `G.map (W.Q.map φ.s)`. -/
theorem map_rightFraction_comp_fac (F : C ⥤ D) (W : MorphismProperty C)
    (hF : W.IsInvertedBy F) {a b : C} (φ : W.RightFraction a b) :
    (Localization.lift F hF W.Q).map (φ.map W.Q (Localization.inverts W.Q W)) ≫
        (Localization.fac F hF W.Q).hom.app b =
      (Localization.fac F hF W.Q).hom.app a ≫ φ.map F hF := by
  set G := Localization.lift F hF W.Q with hG
  set e := Localization.fac F hF W.Q with he
  have : IsIso (W.Q.map φ.s) := Localization.inverts W.Q W _ φ.hs
  rw [← cancel_epi (G.map (W.Q.map φ.s))]
  have hleft : G.map (W.Q.map φ.s) ≫
      G.map (φ.map W.Q (Localization.inverts W.Q W)) ≫ e.hom.app b =
        G.map (W.Q.map φ.f) ≫ e.hom.app b := by
    rw [← assoc, ← G.map_comp, MorphismProperty.RightFraction.map_s_comp_map]
  erw [hleft, e.hom.naturality φ.f, ← assoc, e.hom.naturality φ.s, assoc,
    MorphismProperty.RightFraction.map_s_comp_map]

/-- **A functor that computes fractions is a localization.**  Let `W` have a right calculus of
fractions and let `F : C ⥤ D` invert `W`.  If `F` is essentially surjective, if every morphism
between objects of the image of `F` is the image of a right fraction, and if `F` is faithful up
to precomposition by a morphism of `W`, then `F` presents `D` as the localization of `C` at `W`.

The lift of `F` through `W.Q` is an equivalence: essential surjectivity is that of `F`,
fullness is the fraction representation and faithfulness is the fraction equivalence
`MorphismProperty.rightFractionRel_of_map_eq`. -/
theorem isLocalization_of_rightFractions (F : C ⥤ D) (W : MorphismProperty C)
    [W.HasRightCalculusOfFractions] (hF : W.IsInvertedBy F) [F.EssSurj]
    (hfull : ∀ (a b : C) (g : F.obj a ⟶ F.obj b),
      ∃ (c : C) (s : c ⟶ a) (_ : W s) (f : c ⟶ b),
        g = (MorphismProperty.RightFraction.mk s ‹W s› f).map F hF)
    (hfaithful : ∀ ⦃a b : C⦄ (u v : a ⟶ b), F.map u = F.map v →
      ∃ (c : C) (t : c ⟶ a), W t ∧ t ≫ u = t ≫ v) :
    F.IsLocalization W := by
  have hQsurj : W.Q.EssSurj := Localization.essSurj W.Q W
  have hGsurj : (Localization.lift F hF W.Q).EssSurj :=
    ⟨fun Y => ⟨W.Q.obj (F.objPreimage Y),
      ⟨(Localization.fac F hF W.Q).app _ ≪≫ F.objObjPreimageIso Y⟩⟩⟩
  have hGfull : (Localization.lift F hF W.Q).Full := by
    have hcore : ∀ (a b : C) (g : (Localization.lift F hF W.Q).obj (W.Q.obj a) ⟶
          (Localization.lift F hF W.Q).obj (W.Q.obj b)),
        ∃ h : W.Q.obj a ⟶ W.Q.obj b, (Localization.lift F hF W.Q).map h = g := by
      intro a b g
      obtain ⟨c, s, hs, f, hg⟩ := hfull a b ((Localization.fac F hF W.Q).inv.app a ≫ g ≫
        (Localization.fac F hF W.Q).hom.app b)
      refine ⟨(MorphismProperty.RightFraction.mk s hs f).map W.Q
        (Localization.inverts W.Q W), ?_⟩
      rw [← cancel_mono ((Localization.fac F hF W.Q).hom.app b),
        map_rightFraction_comp_fac F W hF, ← hg]
      simp
    constructor
    intro A B g
    obtain ⟨h, hh⟩ := hcore (W.Q.objPreimage A) (W.Q.objPreimage B)
      ((Localization.lift F hF W.Q).map (W.Q.objObjPreimageIso A).hom ≫ g ≫
        (Localization.lift F hF W.Q).map (W.Q.objObjPreimageIso B).inv)
    refine ⟨(W.Q.objObjPreimageIso A).inv ≫ h ≫ (W.Q.objObjPreimageIso B).hom, ?_⟩
    rw [Functor.map_comp, Functor.map_comp, hh]
    simp [← Functor.map_comp]
  have hGfaithful : (Localization.lift F hF W.Q).Faithful := by
    have hcore : ∀ (a b : C) (h₁ h₂ : W.Q.obj a ⟶ W.Q.obj b),
        (Localization.lift F hF W.Q).map h₁ = (Localization.lift F hF W.Q).map h₂ →
          h₁ = h₂ := by
      intro a b h₁ h₂ hh
      obtain ⟨φ, hφ⟩ := Localization.exists_rightFraction W.Q W h₁
      obtain ⟨ψ, hψ⟩ := Localization.exists_rightFraction W.Q W h₂
      have hmap : φ.map F hF = ψ.map F hF := by
        rw [← cancel_epi ((Localization.fac F hF W.Q).hom.app a),
          ← map_rightFraction_comp_fac F W hF,
          ← map_rightFraction_comp_fac F W hF, ← hφ, ← hψ, hh]
      rw [hφ, hψ, MorphismProperty.RightFraction.map_eq_iff]
      exact MorphismProperty.rightFractionRel_of_map_eq F W hF hfaithful φ ψ hmap
    constructor
    intro A B h₁ h₂ hh
    have key := hcore (W.Q.objPreimage A) (W.Q.objPreimage B)
      ((W.Q.objObjPreimageIso A).hom ≫ h₁ ≫ (W.Q.objObjPreimageIso B).inv)
      ((W.Q.objObjPreimageIso A).hom ≫ h₂ ≫ (W.Q.objObjPreimageIso B).inv)
      (by rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp, hh])
    rw [cancel_epi, cancel_mono] at key
    exact key
  have hGequiv : (Localization.lift F hF W.Q).IsEquivalence :=
    { faithful := hGfaithful, full := hGfull, essSurj := hGsurj }
  exact Functor.IsLocalization.of_equivalence_target W.Q W F
    (Localization.lift F hF W.Q).asEquivalence (Localization.fac F hF W.Q)

end Localization

end CategoryTheory

end
