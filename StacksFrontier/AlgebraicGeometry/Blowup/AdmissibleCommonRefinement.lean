module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleExtension
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Basic

/-!
# Tools for refining two admissible blowups to a common one

This file collects the steps of [Stacks, Tag 0F3X] that are statements about admissible blowups
alone, so that they can be reused by the rest of the Nagata compactification chain.

## Main results

* `AlgebraicGeometry.exists_lift_of_isIso_morphismRestrict` and
  `AlgebraicGeometry.exists_section_of_isAdmissibleBlowup`: **a `V`-admissible blowup has a
  section over any open immersion landing in `V`.** This is what produces the morphism from the
  common open subscheme into the blown-up schemes.
* `AlgebraicGeometry.isAdmissibleBlowup_strictTransformToSource`: **the strict transform of `Z`
  along a `V`-admissible blowup of `X` is a `p⁻¹(V)`-admissible blowup of `Z`**, where
  `p : Z ⟶ X` is the structure morphism. This is [Stacks, Tag 080E]: that strict transform is the
  blowup of `Z` in the inverse image of the centre.
* `AlgebraicGeometry.opensRange_eq_preimage_of_isIso_pullbackSnd`: a section of a morphism over an
  open subscheme has image exactly the inverse image of that open, as soon as the fibre product is
  trivial there.
* `AlgebraicGeometry.isClosedImmersion_lift_of_isProper`: **the overlap stays closed after a
  proper modification.** If the graph of a pair of morphisms out of `Z` is a closed immersion into
  `X₁ ×_S X₂` and `W ⟶ Z` is proper, then the graph of the lifted pair is a closed immersion into
  `Y₁ ×_S Y₂`.

## Implementation notes

The section of a blowup over the admissible open is the inverse of the restriction of the blowup
morphism there, which is an isomorphism by [Stacks, Tag 02OS]
(`AlgebraicGeometry.isIso_blowUpToBase_restrict_of_subset_compl_support`); the open immersion is
first factored through that open by `AlgebraicGeometry.IsOpenImmersion.lift`.

The last statement is [Stacks, Tag 01W6] in the form
`AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono`: the lifted graph is proper, being
a factor of the composite of a proper morphism with a closed immersion through a separated
morphism, and it is a monomorphism because its first component is.

## References

* [Stacks Project, Tag 0F3X](https://stacks.math.columbia.edu/tag/0F3X)
* [Stacks Project, Tag 080E](https://stacks.math.columbia.edu/tag/080E)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A morphism which restricts to an isomorphism over an open subscheme has a section over any
open immersion whose image lies in that open. -/
theorem exists_lift_of_isIso_morphismRestrict {X Y Z : Scheme.{u}} (b : Y ⟶ X) (V : X.Opens)
    [IsIso (b ∣_ V)] (j : Z ⟶ X) [IsOpenImmersion j] (hj : j.opensRange ≤ V) :
    ∃ v : Z ⟶ Y, v ≫ b = j := by
  have hrange : Set.range j.base ⊆ Set.range V.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hj
  refine ⟨IsOpenImmersion.lift V.ι j hrange ≫ inv (b ∣_ V) ≫ (b ⁻¹ᵁ V).ι, ?_⟩
  calc IsOpenImmersion.lift V.ι j hrange ≫ inv (b ∣_ V) ≫ (b ⁻¹ᵁ V).ι ≫ b
      = IsOpenImmersion.lift V.ι j hrange ≫ inv (b ∣_ V) ≫ (b ∣_ V) ≫ V.ι := by
        rw [morphismRestrict_ι]
    _ = IsOpenImmersion.lift V.ι j hrange ≫ V.ι := by
        rw [IsIso.inv_hom_id_assoc]
    _ = j := IsOpenImmersion.lift_fac _ _ _

/-- **A `V`-admissible blowup has a section over any open immersion landing in `V`.** The blowup
morphism is an isomorphism over the complement of its centre, and `V` avoids that centre. -/
theorem exists_section_of_isAdmissibleBlowup {X X' Z : Scheme.{u}} {V : X.Opens} {b : X' ⟶ X}
    (hb : Stacks.Blowup.IsAdmissibleBlowup V b) (j : Z ⟶ X) [IsOpenImmersion j]
    (hj : j.opensRange ≤ V) : ∃ v : Z ⟶ X', v ≫ b = j := by
  obtain ⟨I, hfp, hdisj, e, he⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff V b).mp hb
  have hsub : (V : Set X) ⊆ (I.support : Set X)ᶜ := fun x hx hc =>
    Set.disjoint_left.mp hdisj hx hc
  have _ : IsIso (blowUpToBase I ∣_ V) :=
    isIso_blowUpToBase_restrict_of_subset_compl_support I V hsub
  obtain ⟨v₀, hv₀⟩ := exists_lift_of_isIso_morphismRestrict (blowUpToBase I) V j hj
  have hinv : e.inv ≫ b = blowUpToBase I := by rw [← he, Iso.inv_hom_id_assoc]
  exact ⟨v₀ ≫ e.inv, by rw [Category.assoc, hinv, hv₀]⟩

/-- **Stacks Project, Tag 080E, as an admissibility statement.** Let `p : Z ⟶ X` be a morphism and
let `I` be a finitely presented centre on `X` avoiding an open `V`. The structure morphism to `Z`
of the strict transform of `Z` along the blowup of `X` in `I` is a `p⁻¹(V)`-admissible blowup:
that strict transform is the blowup of `Z` in the inverse image of `I`. -/
theorem isAdmissibleBlowup_strictTransformToSource {X Z : Scheme.{u}} (p : Z ⟶ X) (V : X.Opens)
    (I : X.IdealSheafData) (hI : FinitePresentation I.subschemeι)
    (hd : Disjoint (V : Set X) (I.support : Set X)) :
    Stacks.Blowup.IsAdmissibleBlowup (p ⁻¹ᵁ V)
      ((Stacks.StrictTransform.ideal p (blowUpToBase I) (exceptionalIdeal I)).subschemeι ≫
        pullback.fst p (blowUpToBase I)) := by
  refine (Stacks.Blowup.isAdmissibleBlowup_iff _ _).mpr
    ⟨I.comap p, finitePresentation_comap_subschemeι I p hI, ?_,
      (Over.forget Z).mapIso (strictTransformBlowUpIso p I), ?_⟩
  · rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : p.base x ∈ (V : Set X) := hx
    have h2 : p.base x ∈ (I.support : Set X) := by
      have h : x ∈ ((I.comap p).support : Set Z) := hx'
      rwa [Scheme.IdealSheafData.support_comap] at h
    exact Set.disjoint_left.mp hd h1 h2
  · exact Over.w (strictTransformBlowUpIso p I).hom

/-- **A section of a morphism over an open subscheme has image exactly the inverse image of that
open**, provided the fibre product of the morphism with that open is trivial. -/
theorem opensRange_eq_preimage_of_isIso_pullbackSnd {U Z X : Scheme.{u}}
    (s : U ⟶ Z) (q : Z ⟶ X) (j : U ⟶ X) [IsOpenImmersion s] [IsOpenImmersion j]
    (hs : s ≫ q = j) [IsIso (pullback.snd q j.opensRange.ι)] :
    s.opensRange = q ⁻¹ᵁ j.opensRange := by
  have hcond : s ≫ q = j.isoOpensRange.hom ≫ j.opensRange.ι := by
    rw [Scheme.Hom.isoOpensRange_hom_ι, hs]
  set l : U ⟶ pullback q j.opensRange.ι := pullback.lift s j.isoOpensRange.hom hcond with hl
  have hlsnd : l ≫ pullback.snd q j.opensRange.ι = j.isoOpensRange.hom := by
    rw [hl, pullback.lift_snd]
  have hiso : IsIso (l ≫ pullback.snd q j.opensRange.ι) := by rw [hlsnd]; infer_instance
  have hliso : IsIso l := IsIso.of_isIso_comp_right l (pullback.snd q j.opensRange.ι)
  have hlfst : l ≫ pullback.fst q j.opensRange.ι = s := by rw [hl, pullback.lift_fst]
  have hsurj : Function.Surjective l.base := (Scheme.homeoOfIso (asIso l)).surjective
  apply TopologicalSpace.Opens.ext
  show Set.range s.base = q.base ⁻¹' (j.opensRange : Set X)
  rw [← hlfst]
  show Set.range ((pullback.fst q j.opensRange.ι).base ∘ l.base) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ,
    Scheme.Pullback.range_fst]
  simp

/-- **The overlap of two schemes over a base stays closed after a proper modification.** Let
`p₁ : Z ⟶ X₁` and `p₂ : Z ⟶ X₂` be morphisms over `S` whose graph is a closed immersion into
`X₁ ×_S X₂`, let `b₁ : Y₁ ⟶ X₁` and `b₂ : Y₂ ⟶ X₂` be separated, and let `c : W ⟶ Z` be proper
with lifts `j₁ : W ⟶ Y₁` and `j₂ : W ⟶ Y₂` of `c ≫ p₁` and `c ≫ p₂`, with `j₁` a monomorphism.
Then the graph of `(j₁, j₂)` is a closed immersion into `Y₁ ×_S Y₂`. -/
theorem isClosedImmersion_lift_of_isProper {S X₁ X₂ Y₁ Y₂ Z W : Scheme.{u}}
    (f₁ : X₁ ⟶ S) (f₂ : X₂ ⟶ S) [IsSeparated f₁] [IsSeparated f₂]
    (p₁ : Z ⟶ X₁) (p₂ : Z ⟶ X₂) (hp : p₁ ≫ f₁ = p₂ ≫ f₂)
    [IsClosedImmersion (pullback.lift p₁ p₂ hp)]
    (b₁ : Y₁ ⟶ X₁) (b₂ : Y₂ ⟶ X₂) [IsSeparated b₁] [IsSeparated b₂]
    (c : W ⟶ Z) [IsProper c]
    (j₁ : W ⟶ Y₁) (j₂ : W ⟶ Y₂) [Mono j₁]
    (h₁ : j₁ ≫ b₁ = c ≫ p₁) (h₂ : j₂ ≫ b₂ = c ≫ p₂) :
    ∃ h : j₁ ≫ (b₁ ≫ f₁) = j₂ ≫ (b₂ ≫ f₂),
      IsClosedImmersion (pullback.lift j₁ j₂ h) := by
  have h : j₁ ≫ (b₁ ≫ f₁) = j₂ ≫ (b₂ ≫ f₂) := by
    rw [← Category.assoc, h₁, Category.assoc, hp, ← Category.assoc, ← h₂, Category.assoc]
  set k := pullback.lift j₁ j₂ h with hk
  set m := pullback.map (b₁ ≫ f₁) (b₂ ≫ f₂) f₁ f₂ b₁ b₂ (𝟙 S) (by simp) (by simp) with hm
  have hmsep : IsSeparated m := by
    have he : m ≫ (pullback.fst f₁ f₂ ≫ f₁) =
        pullback.fst (b₁ ≫ f₁) (b₂ ≫ f₂) ≫ (b₁ ≫ f₁) := by
      rw [hm]
      simp [pullback.map, pullback.lift_fst_assoc]
    have h' : IsSeparated (m ≫ (pullback.fst f₁ f₂ ≫ f₁)) := by
      rw [he]; infer_instance
    exact IsSeparated.of_comp m (pullback.fst f₁ f₂ ≫ f₁)
  have he : k ≫ m = c ≫ pullback.lift p₁ p₂ hp := by
    apply pullback.hom_ext <;>
      simp [hk, hm, pullback.map, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, h₁, h₂]
  have _ : IsProper (k ≫ m) := by rw [he]; infer_instance
  have _ : IsProper k := IsProper.of_comp k m
  have hmono : Mono (k ≫ pullback.fst (b₁ ≫ f₁) (b₂ ≫ f₂)) := by
    rw [hk, pullback.lift_fst]
    infer_instance
  have _ : Mono k := mono_of_mono k (pullback.fst (b₁ ≫ f₁) (b₂ ≫ f₂))
  exact ⟨h, (IsClosedImmersion.iff_isProper_and_mono _).mpr ⟨inferInstance, inferInstance⟩⟩

end AlgebraicGeometry

end
