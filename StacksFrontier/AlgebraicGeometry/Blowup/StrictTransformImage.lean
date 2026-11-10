module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransform
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
import StacksFrontier.AlgebraicGeometry.LimitMorphismAt.Dominant

/-!
# The scheme-theoretic image of a lift to an admissible blowup

Let `p : X ⟶ S` and `q : Y ⟶ S` be morphisms of schemes, let `U ⊆ X` be open and let
`f : V ⟶ X ×_S Y` be quasi-compact with `pr_X ∘ f` landing in `U`. Write `Z` for the
scheme-theoretic image of `f`. If `b : X' ⟶ X` is a `U`-admissible blowup and `g : V ⟶ X' ×_S Y`
lifts `f`, then the scheme-theoretic image of `g` is the strict transform of `Z` along `b`.

## Main results

* `Stacks.Blowup.exists_iso_image_strictTransform_of_centre`: the identification for a named
  centre of the blowup, which is the form consumers matching a particular centre need.
* `Stacks.Blowup.exists_iso_image_strictTransform`: **Stacks tag 0F3Y**, the identification of the
  scheme-theoretic image of the lift with the strict transform of the original image, as closed
  subschemes of `X' ×_S Y`.

## Implementation notes

Both sides are closed subschemes of `X' ×_S Y`, so the identification is an isomorphism over that
scheme; it is produced by `AlgebraicGeometry.IsClosedImmersion.lift` from the equality of the two
defining ideals, and the two equations recorded alongside it pin the embedding of the strict
transform down by its two projections, independently of the choice of centre.

The strict transform of `Z` is a closed subscheme of `Z ×_X X'`, and `Z ×_X X' ⟶ X' ×_S Y` is a
closed immersion because `Z ×_X X'` is the base change along `X' ×_S Y ⟶ X ×_S Y` of the closed
immersion `Z ⟶ X ×_S Y`. The equality of the two ideals is then read off the exceptional
complement: away from the centre the blowup is an isomorphism (Stacks tag 02OS), so `V` maps
scheme-theoretically dominantly onto the part of `Z ×_X X'` lying over the complement of the
centre, while the defining ideal of the strict transform is exactly the kernel of the inclusion of
that part (`Stacks.Blowup.strictTransformIdeal_eq_ker`).

## References

* [Stacks Project, Tag 0F3Y](https://stacks.math.columbia.edu/tag/0F3Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Blowup

/-- The restriction of a quasi-compact scheme-theoretically dominant morphism to an open of its
target is again scheme-theoretically dominant. -/
private theorem isSchemeTheoreticallyDominant_morphismRestrict {A B : Scheme.{u}} (k : A ⟶ B)
    [QuasiCompact k] [IsSchemeTheoreticallyDominant k] (W : B.Opens) :
    IsSchemeTheoreticallyDominant (k ∣_ W) :=
  IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict k W).flip

/-- The compatibility making `Z ×_X B ⟶ X' ×_S Y` well defined, for `Z ⟶ X ×_S Y` and
`b : X' ⟶ X` identified with `b₀ : B ⟶ X` through `e`. -/
theorem pullback_snd_inv_comp_eq {X Y S X' B Z : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (b : X' ⟶ X) (b₀ : B ⟶ X) (e : X' ≅ B) (he : e.hom ≫ b₀ = b) (i : Z ⟶ pullback p q) :
    (pullback.snd (i ≫ pullback.fst p q) b₀ ≫ e.inv) ≫ b ≫ p =
      (pullback.fst (i ≫ pullback.fst p q) b₀ ≫ i ≫ pullback.snd p q) ≫ q := by
  subst he
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← pullback.condition_assoc]
  simp only [Category.assoc, pullback.condition]

/-- For a closed immersion `i : Z ⟶ X ×_S Y`, the induced morphism `Z ×_X B ⟶ X' ×_S Y` is a
closed immersion, being a base change of `i`. -/
theorem isClosedImmersion_of_comp_fst_of_comp_snd {X Y S X' B Z : Scheme.{u}} (p : X ⟶ S)
    (q : Y ⟶ S) (b : X' ⟶ X) (b₀ : B ⟶ X) (e : X' ≅ B) (he : e.hom ≫ b₀ = b)
    (i : Z ⟶ pullback p q) [IsClosedImmersion i]
    (l : pullback (i ≫ pullback.fst p q) b₀ ⟶ pullback (b ≫ p) q)
    (hl₁ : l ≫ pullback.fst (b ≫ p) q = pullback.snd (i ≫ pullback.fst p q) b₀ ≫ e.inv)
    (hl₂ : l ≫ pullback.snd (b ≫ p) q =
      pullback.fst (i ≫ pullback.fst p q) b₀ ≫ i ≫ pullback.snd p q) :
    IsClosedImmersion l := by
  let f₁ : pullback p q ⟶ X := pullback.fst p q
  let m := pullback.map b f₁ b₀ f₁ e.hom (𝟙 (pullback p q)) (𝟙 X) he.symm (by simp)
  let τ : pullback (b ≫ p) q ⟶ pullback f₁ b₀ :=
    (pullbackRightPullbackFstIso p q b).inv ≫ m ≫ (pullbackSymmetry f₁ b₀).inv
  have hm₁ : m ≫ pullback.fst b₀ f₁ = pullback.fst b f₁ ≫ e.hom := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd b₀ f₁ = pullback.snd b f₁ :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hτfst : τ ≫ pullback.fst f₁ b₀ =
      (pullbackRightPullbackFstIso p q b).inv ≫ pullback.snd b f₁ := by
    simp [τ, hm₂]
  have hτsnd : τ ≫ pullback.snd f₁ b₀ = pullback.fst (b ≫ p) q ≫ e.hom := by
    simp [τ, hm₁, f₁]
  have : IsIso m :=
    pullback.map_isIso b f₁ b₀ f₁ e.hom (𝟙 (pullback p q)) (𝟙 X) he.symm (by simp)
  have : IsIso τ := by
    dsimp only [τ]
    infer_instance
  have hτInvFst : inv τ ≫ pullback.fst (b ≫ p) q = pullback.snd f₁ b₀ ≫ e.inv := by
    rw [IsIso.inv_comp_eq, reassoc_of% hτsnd]
    simp
  have hτInvSnd : inv τ ≫ pullback.snd (b ≫ p) q = pullback.fst f₁ b₀ ≫ pullback.snd p q := by
    rw [IsIso.inv_comp_eq, reassoc_of% hτfst, pullbackRightPullbackFstIso_inv_snd_snd]
  have hl : l =
      (pullbackRightPullbackFstIso f₁ b₀ i).inv ≫ pullback.snd i (pullback.fst f₁ b₀) ≫ inv τ :=
    pullback.hom_ext (by simp [hl₁, hτInvFst, f₁]) (by simp [hl₂, hτInvSnd, f₁])
  rw [hl]
  infer_instance

/-- If `b₀ : B ⟶ X` restricts to an isomorphism over an open `C ⊆ X`, then so does its base
change `pullback.fst h b₀` over `h ⁻¹ᵁ C`. -/
theorem isIso_morphismRestrict_pullbackFst {Z X B : Scheme.{u}} (h : Z ⟶ X) (b₀ : B ⟶ X)
    (C : X.Opens) [IsIso (b₀ ∣_ C)] : IsIso (pullback.fst h b₀ ∣_ h ⁻¹ᵁ C) := by
  let R : (pullback h b₀).Opens := pullback.fst h b₀ ⁻¹ᵁ (h ⁻¹ᵁ C)
  let pR : R.toScheme ⟶ (h ⁻¹ᵁ C).toScheme := pullback.fst h b₀ ∣_ (h ⁻¹ᵁ C)
  have hRB : R = pullback.snd h b₀ ⁻¹ᵁ (b₀ ⁻¹ᵁ C) := by
    change (pullback.fst h b₀ ≫ h) ⁻¹ᵁ C = (pullback.snd h b₀ ≫ b₀) ⁻¹ᵁ C
    rw [pullback.condition]
  let qR : R.toScheme ⟶ (b₀ ⁻¹ᵁ C).toScheme :=
    ((pullback h b₀).isoOfEq hRB).hom ≫ (pullback.snd h b₀ ∣_ (b₀ ⁻¹ᵁ C))
  have hqR : qR ≫ (b₀ ⁻¹ᵁ C).ι = R.ι ≫ pullback.snd h b₀ := by
    simp [qR, morphismRestrict_ι]
  have hBig : IsPullback pR (R.ι ≫ pullback.snd h b₀) ((h ⁻¹ᵁ C).ι ≫ h) b₀ := by
    refine IsPullback.flip ?_
    have h₁ := (isPullback_morphismRestrict (pullback.fst h b₀) (h ⁻¹ᵁ C)).flip
    have h₂ := (IsPullback.of_hasPullback h b₀).flip
    simpa [pR, morphismRestrict_ι] using h₁.paste_horiz h₂
  have hBig' : IsPullback pR (qR ≫ (b₀ ⁻¹ᵁ C).ι) ((h ∣_ C) ≫ C.ι) b₀ := by
    rw [hqR, morphismRestrict_ι]
    exact hBig
  refine (IsPullback.of_bot hBig' ?_ (isPullback_morphismRestrict b₀ C)).isIso_fst_of_isIso
  apply (cancel_mono C.ι).1
  simp only [Category.assoc, morphismRestrict_ι, reassoc_of% hqR]
  simpa only [Category.assoc] using hBig.w

/-- Over the complement of the centre, the base change of `h : Z ⟶ X` to the blowup is the
complement of the inverse image of the exceptional divisor. -/
theorem preimage_compl_support_eq_exceptionalPullbackCompl {Z X : Scheme.{u}} (h : Z ⟶ X)
    (I : X.IdealSheafData) :
    pullback.fst h (blowUpToBase I) ⁻¹ᵁ h ⁻¹ᵁ I.support.compl = exceptionalPullbackCompl h I := by
  rw [← Scheme.Hom.comp_preimage, pullback.condition]
  ext z
  change blowUpToBase I (pullback.snd h (blowUpToBase I) z) ∉ I.support ↔
    z ∉ exceptionalPullbackSet h I
  rw [exceptionalPullbackSet_eq_preimage_support]
  rfl

/-- Precomposing with a scheme-theoretically dominant morphism does not change the kernel: the
kernel of `t ≫ ι ≫ l` is that of `l` on the closed subscheme cut out by the kernel of `ι`. -/
private theorem ker_comp_comp_of_isSchemeTheoreticallyDominant {V R Q P : Scheme.{u}} (t : V ⟶ R)
    [IsSchemeTheoreticallyDominant t] (ι : R ⟶ Q) (l : Q ⟶ P) :
    (t ≫ ι ≫ l).ker = (ι.ker.subschemeι ≫ l).ker := by
  rw [Scheme.Hom.ker_comp t, IsSchemeTheoreticallyDominant.ker_eq_bot t,
    Scheme.IdealSheafData.map_bot, Scheme.Hom.ker_comp ι l,
    Scheme.Hom.ker_comp ι.ker.subschemeι l, Scheme.IdealSheafData.ker_subschemeι]

/-- **The scheme-theoretic image of a lift is the strict transform, for a named centre.** This is
the content of [Stacks, Tag 0F3Y] with the centre of the blowup given rather than extracted from
the admissibility hypothesis: for `f : V ⟶ X ×_S Y` quasi-compact with first projection landing in
an open `U` disjoint from the centre `I`, and a lift `g : V ⟶ X' ×_S Y` of `f` along a morphism `b`
identified with the blowup of `X` in `I`, the scheme-theoretic image of `g` is the strict transform
along `b` of the scheme-theoretic image of `f`.

Consumers that have to match the strict transform of one particular centre — the centre produced by
another lemma — need this form; `Stacks.Blowup.exists_iso_image_strictTransform` is the tagged
statement, which picks a centre out of the admissibility hypothesis. -/
theorem exists_iso_image_strictTransform_of_centre
    {X Y S V X' : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (U : X.Opens) (b : X' ⟶ X)
    (f : V ⟶ pullback p q) [QuasiCompact f]
    (g : V ⟶ pullback (b ≫ p) q)
    (hfU : Set.range (f ≫ pullback.fst p q).base ⊆ (U : Set X))
    (hbgX : g ≫ pullback.fst (b ≫ p) q ≫ b = f ≫ pullback.fst p q)
    (hbgY : g ≫ pullback.snd (b ≫ p) q = f ≫ pullback.snd p q)
    (I : X.IdealSheafData) (e : X' ≅ blowUp I)
    (he : e.hom ≫ blowUpToBase I = b)
    (hdisj : Disjoint (U : Set X) (I.support : Set X)) :
    ∃ (j : strictTransform (f.imageι ≫ pullback.fst p q) I ⟶ pullback (b ≫ p) q)
      (a : g.image ≅ strictTransform (f.imageι ≫ pullback.fst p q) I),
      j ≫ pullback.fst (b ≫ p) q ≫ e.hom =
        strictTransformι (f.imageι ≫ pullback.fst p q) I ≫
          pullback.snd (f.imageι ≫ pullback.fst p q) (blowUpToBase I) ∧
      j ≫ pullback.snd (b ≫ p) q =
        strictTransformι (f.imageι ≫ pullback.fst p q) I ≫
          pullback.fst (f.imageι ≫ pullback.fst p q) (blowUpToBase I) ≫
            f.imageι ≫ pullback.snd p q ∧
      a.hom ≫ j = g.imageι := by
  classical
  let b₀ : blowUp I ⟶ X := blowUpToBase I
  let h : f.image ⟶ X := f.imageι ≫ pullback.fst p q
  let l : pullback h b₀ ⟶ pullback (b ≫ p) q :=
    pullback.lift (pullback.snd h b₀ ≫ e.inv) (pullback.fst h b₀ ≫ f.imageι ≫ pullback.snd p q)
      (pullback_snd_inv_comp_eq p q b b₀ e he f.imageι)
  have hl₁ : l ≫ pullback.fst (b ≫ p) q = pullback.snd h b₀ ≫ e.inv := pullback.lift_fst _ _ _
  have hl₂ : l ≫ pullback.snd (b ≫ p) q = pullback.fst h b₀ ≫ f.imageι ≫ pullback.snd p q :=
    pullback.lift_snd _ _ _
  have := isClosedImmersion_of_comp_fst_of_comp_snd p q b b₀ e he f.imageι l hl₁ hl₂
  let j : strictTransform h I ⟶ pullback (b ≫ p) q := strictTransformι h I ≫ l
  let t : V ⟶ pullback h b₀ := pullback.lift f.toImage (g ≫ pullback.fst (b ≫ p) q ≫ e.hom)
    (by simp [h, b₀, he, hbgX])
  have ht₁ : t ≫ pullback.fst h b₀ = f.toImage := pullback.lift_fst _ _ _
  have ht₂ : t ≫ pullback.snd h b₀ = g ≫ pullback.fst (b ≫ p) q ≫ e.hom := pullback.lift_snd _ _ _
  have ht_l : t ≫ l = g := pullback.hom_ext (by simp [hl₁, reassoc_of% ht₂])
    (by simp [hl₂, reassoc_of% ht₁, reassoc_of% f.toImage_imageι, hbgY])
  let C : X.Opens := I.support.compl
  let W : f.image.Opens := h ⁻¹ᵁ C
  let R : (pullback h b₀).Opens := pullback.fst h b₀ ⁻¹ᵁ W
  have hWpre : f.toImage ⁻¹ᵁ W = ⊤ := by
    ext x
    change ((f.toImage ≫ f.imageι) ≫ pullback.fst p q) x ∈ C ↔ True
    rw [Scheme.Hom.toImage_imageι]
    exact iff_true_intro (Set.disjoint_left.mp hdisj (hfU ⟨x, rfl⟩))
  have := isSchemeTheoreticallyDominant_morphismRestrict f.toImage W
  have hRcomp : R = exceptionalPullbackCompl h I :=
    preimage_compl_support_eq_exceptionalPullbackCompl h I
  have : IsIso (b₀ ∣_ C) := isIso_blowUpToBase_restrict_compl_support_reesData I
  have : IsIso (pullback.fst h b₀ ∣_ W) := isIso_morphismRestrict_pullbackFst h b₀ C
  have hTpre : t ⁻¹ᵁ R = ⊤ := by rw [← hWpre, ← ht₁, Scheme.Hom.comp_preimage]
  let t₀ : V ⟶ R.toScheme := (V.topIso.symm ≪≫ V.isoOfEq hTpre.symm).hom ≫ (t ∣_ R)
  have ht₀ι : t₀ ≫ R.ι = t := by simp [t₀, morphismRestrict_ι]
  have ht₀p : t₀ ≫ (pullback.fst h b₀ ∣_ W) =
      (V.topIso.symm ≪≫ V.isoOfEq hWpre.symm).hom ≫ (f.toImage ∣_ W) := by
    apply (cancel_mono W.ι).1
    rw [Category.assoc, morphismRestrict_ι, reassoc_of% ht₀ι, ht₁]
    simp [morphismRestrict_ι]
  have : IsSchemeTheoreticallyDominant t₀ := by
    rw [(IsIso.eq_comp_inv _).2 ht₀p]
    infer_instance
  have hgker : g.imageι.ker = j.ker := by
    rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι, ← ht_l, ← ht₀ι, Category.assoc,
      ker_comp_comp_of_isSchemeTheoreticallyDominant, hRcomp, ← strictTransformIdeal_eq_ker]
    rfl
  have : IsIso (IsClosedImmersion.lift j g.imageι hgker.ge) :=
    IsClosedImmersion.isIso_lift j g.imageι hgker.symm
  exact ⟨j, asIso (IsClosedImmersion.lift j g.imageι hgker.ge), by simp [j, h, b₀, reassoc_of% hl₁],
    by simp [j, h, b₀, hl₂], IsClosedImmersion.lift_fac j g.imageι hgker.ge⟩

/-- **Stacks Project, Tag 0F3Y.** For `f : V ⟶ X ×_S Y` quasi-compact with first projection landing
in an open `U ⊆ X`, a `U`-admissible blowup `b : X' ⟶ X` and a lift `g : V ⟶ X' ×_S Y` of `f`, the
scheme-theoretic image of `g` is the strict transform along `b` of that of `f`. -/
@[stacks 0F3Y]
theorem exists_iso_image_strictTransform
    {X Y S V X' : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S)
    (U : X.Opens) (b : X' ⟶ X)
    (f : V ⟶ pullback p q) [QuasiCompact f]
    (g : V ⟶ pullback (b ≫ p) q)
    (hfU : Set.range (f ≫ pullback.fst p q).base ⊆ (U : Set X))
    (hbgX : g ≫ pullback.fst (b ≫ p) q ≫ b = f ≫ pullback.fst p q)
    (hbgY : g ≫ pullback.snd (b ≫ p) q = f ≫ pullback.snd p q)
    (hb : IsAdmissibleBlowup U b) :
    ∃ I : X.IdealSheafData,
      ∃ e : X' ≅ blowUp I,
        e.hom ≫ blowUpToBase I = b ∧
        Disjoint (U : Set X) (I.support : Set X) ∧
        ∃ (j : strictTransform (f.imageι ≫ pullback.fst p q) I ⟶ pullback (b ≫ p) q)
          (a : g.image ≅ strictTransform (f.imageι ≫ pullback.fst p q) I),
          j ≫ pullback.fst (b ≫ p) q ≫ e.hom =
            strictTransformι (f.imageι ≫ pullback.fst p q) I ≫
              pullback.snd (f.imageι ≫ pullback.fst p q) (blowUpToBase I) ∧
          j ≫ pullback.snd (b ≫ p) q =
            strictTransformι (f.imageι ≫ pullback.fst p q) I ≫
              pullback.fst (f.imageι ≫ pullback.fst p q) (blowUpToBase I) ≫
                f.imageι ≫ pullback.snd p q ∧
          a.hom ≫ j = g.imageι := by
  obtain ⟨I, -, hdisj, e, he⟩ := hb
  obtain ⟨j, a, hj₁, hj₂, ha⟩ :=
    exists_iso_image_strictTransform_of_centre p q U b f g hfU hbgX hbgY I e he hdisj
  exact ⟨I, e, he, hdisj, j, a, hj₁, hj₂, ha⟩

end Stacks.Blowup

end
