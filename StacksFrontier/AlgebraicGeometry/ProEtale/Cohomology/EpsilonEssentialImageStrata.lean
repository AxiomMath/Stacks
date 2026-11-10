module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.EpsilonEssentialImageGluing

/-!
# The essential image of `ε⁻¹` contains sheaves coming from the étale site on strata

Let `Y` be an affine scheme and `t_k : P_k ⟶ Y`, `k = 1, …, n`, finitely many immersions whose
images cover `Y` and are constructible. An abelian sheaf `ℱ` on `Y_proétale` whose inverse
images `t_k⁻¹ ℱ` come from the small étale sites of the `P_k` comes from `Y_étale`.

The images of the `t_k` are determined by the vanishing pattern of finitely many functions
`E ⊆ Γ(Y, 𝒪_Y)` (Stacks 096Y), and the proof is by induction on `E`: for `f ∈ E` the basic open
`D(f)` and its closed complement `V(f)` are affine, the images of the base changes of the `t_k`
to them are determined by the remaining functions, and the two pieces are glued by the
open-closed sequence (`AlgebraicGeometry.ProEtale.epsilonInverseImage_essImage_of_restrictions`).
When `E` is empty, one of the `t_k` is a surjective immersion, hence a closed immersion with
empty complement.

This is the heart of the proof of Stacks 09AK.

## Main results

* `AlgebraicGeometry.exists_finset_determinedBy_of_isConstructible`: Stacks 096Y in the form
  used here.
* `AlgebraicGeometry.ProEtale.epsilonInverseImage_essImage_of_determinedBy`: an abelian sheaf whose
  inverse images to finitely many strata determined by finitely many functions come from the
  étale sites comes from the étale site.

## References

* [Stacks Project, Tag 096Y](https://stacks.math.columbia.edu/tag/096Y)
* [Stacks Project, Tag 09AK](https://stacks.math.columbia.edu/tag/09AK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe v u

namespace AlgebraicGeometry

/-- A subset `T` of a scheme `Y` is *determined* by a finite set `E` of global functions when
two points of `Y` at which the same functions of `E` are invertible are both in `T` or both not
in `T`. -/
def Scheme.DeterminedBy (Y : Scheme.{u}) (E : Finset Γ(Y, ⊤)) (T : Set Y) : Prop :=
  ∀ x y : Y, (∀ g ∈ E, x ∈ Y.basicOpen g ↔ y ∈ Y.basicOpen g) → (x ∈ T ↔ y ∈ T)

/-- A subset determined by `E` is determined by every finite set of global functions containing
`E`. -/
theorem Scheme.DeterminedBy.mono {Y : Scheme.{u}} {E E' : Finset Γ(Y, ⊤)} {T : Set Y}
    (h : Y.DeterminedBy E T) (hE : E ⊆ E') : Y.DeterminedBy E' T :=
  fun x y hxy ↦ h x y fun g hg ↦ hxy g (hE hg)

/-- **Stacks 096Y.** A constructible subset of an affine scheme is determined by finitely many
global functions. -/
theorem exists_finset_determinedBy_of_isConstructible {Y : Scheme.{u}} [IsAffine Y] {T : Set Y}
    (hT : IsConstructible T) : ∃ E : Finset Γ(Y, ⊤), Y.DeterminedBy E T := by
  classical
  have hbasis : TopologicalSpace.IsTopologicalBasis
      (Set.range fun g : Γ(Y, ⊤) ↦ (Y.basicOpen g : Set Y)) := by
    have := isBasis_basicOpen Y
    rw [TopologicalSpace.Opens.IsBasis, ← Set.range_comp] at this
    exact this
  refine IsConstructible.induction_of_isTopologicalBasis
    (P := fun T _ ↦ ∃ E : Finset Γ(Y, ⊤), Y.DeterminedBy E T)
    (fun g : Γ(Y, ⊤) ↦ (Y.basicOpen g : Set Y)) hbasis
    (fun g ↦ ((isAffineOpen_top Y).basicOpen g).isCompact) (fun g s hs ↦ ?_)
    (fun s _ t _ ⟨E₁, h₁⟩ ⟨E₂, h₂⟩ ↦ ⟨E₁ ∪ E₂, fun x y hxy ↦ ?_⟩) T hT
  · refine ⟨insert g hs.toFinset, fun x y hxy ↦ ?_⟩
    simp only [Set.mem_sdiff, Set.mem_iUnion, exists_prop, not_exists, not_and, SetLike.mem_coe]
    rw [hxy g (Finset.mem_insert_self _ _)]
    refine and_congr Iff.rfl (forall_congr' fun h ↦ imp_congr_right fun hh ↦ ?_)
    exact not_congr (hxy h (Finset.mem_insert_of_mem (by simpa using hh)))
  · rw [Set.mem_union, Set.mem_union,
      h₁ x y fun g hg ↦ hxy g (Finset.mem_union_left _ hg),
      h₂ x y fun g hg ↦ hxy g (Finset.mem_union_right _ hg)]

/-- The closed complement `V(f)` of a basic open subset of an affine scheme, as a closed
immersion from the spectrum of the quotient ring. -/
def Scheme.zeroLocusImmersion (Y : Scheme.{u}) [IsAffine Y] (f : Γ(Y, ⊤)) :
    Spec (CommRingCat.of (Γ(Y, ⊤) ⧸ Ideal.span {f})) ⟶ Y :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ Y.isoSpec.inv

/-- The immersion `Y.zeroLocusImmersion f` of `V(f)` is a closed immersion. -/
instance (Y : Scheme.{u}) [IsAffine Y] (f : Γ(Y, ⊤)) : IsClosedImmersion (Y.zeroLocusImmersion f) :=
  by dsimp [Scheme.zeroLocusImmersion]; infer_instance

/-- The image of `Y.zeroLocusImmersion f` is the complement of the basic open `D(f)`. -/
theorem Scheme.range_zeroLocusImmersion (Y : Scheme.{u}) [IsAffine Y] (f : Γ(Y, ⊤)) :
    Set.range (Y.zeroLocusImmersion f) = (Y.basicOpen f : Set Y)ᶜ := by
  have h₂ : Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))) =
      (PrimeSpectrum.zeroLocus ((Ideal.span {f} : Ideal Γ(Y, ⊤)) : Set Γ(Y, ⊤))) := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {f}))) = _
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    simp [Ideal.mk_ker]
  ext x
  have hx : x ∈ Set.range (Y.zeroLocusImmersion f) ↔
      Y.isoSpec.hom x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {f})))) := by
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [Scheme.zeroLocusImmersion, Scheme.Hom.comp_apply,
        ← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, by rw [Scheme.zeroLocusImmersion, Scheme.Hom.comp_apply, hz,
        ← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl⟩
  rw [hx, h₂, PrimeSpectrum.zeroLocus_span, Set.mem_compl_iff, SetLike.mem_coe,
    ← Scheme.map_PrimeSpectrum_basicOpen_of_affine]
  exact (PrimeSpectrum.mem_zeroLocus (x := Y.isoSpec.hom x) {f}).trans
    (Set.singleton_subset_iff.trans (PrimeSpectrum.mem_basicOpen _ _ |>.not.trans not_not).symm)

namespace ProEtale

variable {ι : Type*}

/-- **The essential image of `ε⁻¹` and finitely many strata.** Let `Y` be affine and
`t_k : P_k ⟶ Y` immersions whose images cover `Y` and are determined by a finite set `E` of
global functions. An abelian sheaf on `Y_proétale` whose inverse images along the `t_k` come
from the étale sites comes from `Y_étale`. -/
theorem epsilonInverseImage_essImage_of_determinedBy (n : ℕ) :
    ∀ (Y : Scheme.{u}) [IsAffine Y] (E : Finset Γ(Y, ⊤)), E.card ≤ n →
      ∀ (P : ι → Scheme.{u}) (t : ∀ k, P k ⟶ Y) [∀ k, IsImmersion (t k)],
      (∀ y : Y, ∃ k, y ∈ Set.range (t k)) → (∀ k, Y.DeterminedBy E (Set.range (t k))) →
      ∀ F : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{max (u + 1) v},
      (∀ k, (epsilonInverseImage.{u, v} (P k)).essImage
        ((Abelian.proetaleInverseImage.{u, v} (t k)).obj F)) →
      (epsilonInverseImage.{u, v} Y).essImage F := by
  classical
  induction n with
  | zero =>
    intro Y _ E hE P t _ hcov hdet F hF
    have hE : E = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hE)
    by_cases hY : IsEmpty Y
    · exact epsilonInverseImage_essImage_of_isEmpty F
    obtain ⟨y₀⟩ := not_isEmpty_iff.1 hY
    obtain ⟨k, hk⟩ := hcov y₀
    have hrange : Set.range (t k) = Set.univ := Set.eq_univ_of_forall fun y ↦
      (hdet k y₀ y (by simp [hE])).1 hk
    have : IsClosedImmersion (t k) :=
      IsClosedImmersion.of_isPreimmersion _ (hrange ▸ isClosed_univ)
    have hij : Set.range (⊥ : Y.Opens).ι = (Set.range (t k))ᶜ := by
      simp [hrange]
    have : IsEmpty (⊥ : Y.Opens).toScheme := ⟨fun x ↦ by simpa using x.2⟩
    exact epsilonInverseImage_essImage_of_restrictions (t k) (⊥ : Y.Opens).ι hij F
      (epsilonInverseImage_essImage_of_isEmpty _) (hF k)
  | succ n ih =>
    intro Y _ E hE P t _ hcov hdet F hF
    rcases E.eq_empty_or_nonempty with hE₀ | ⟨f, hf⟩
    · exact ih Y E (by simp [hE₀]) P t hcov hdet F hF
    have hfE : (E.erase f).card ≤ n := by
      have := Finset.card_erase_of_mem hf
      omega
    let U : Y.Opens := Y.basicOpen f
    have : IsAffine U := ((isAffineOpen_top Y).basicOpen f)
    let j := U.ι
    let i := Y.zeroLocusImmersion f
    have : QuasiCompact j := inferInstance
    have hij : Set.range j = (Set.range i)ᶜ := by
      rw [Scheme.range_zeroLocusImmersion, compl_compl, Scheme.Opens.range_ι]
    have key : ∀ (W : Scheme.{u}) [IsAffine W] (g : W ⟶ Y) (p : Prop),
        (∀ x : W, g x ∈ Y.basicOpen f ↔ p) →
        (epsilonInverseImage.{u, v} W).essImage
          ((Abelian.proetaleInverseImage.{u, v} g).obj F) := by
      intro W _ g p hp
      refine ih W ((E.erase f).image g.appTop) (Finset.card_image_le.trans hfE)
        (fun k ↦ pullback (t k) g) (fun k ↦ pullback.snd (t k) g) (fun x ↦ ?_) (fun k x y hxy ↦ ?_)
        _ (fun k ↦ ?_)
      · obtain ⟨k, z, hz⟩ := hcov (g x)
        obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
        exact ⟨k, w, hw⟩
      · rw [Scheme.Pullback.range_snd, Set.mem_preimage, Set.mem_preimage]
        refine hdet k (g x) (g y) fun e he ↦ ?_
        by_cases hef : e = f
        · subst hef; exact (hp x).trans (hp y).symm
        · have := hxy (g.appTop e) (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨hef, he⟩))
          change x ∈ g ⁻¹ᵁ Y.basicOpen e ↔ y ∈ g ⁻¹ᵁ Y.basicOpen e
          rw [Scheme.preimage_basicOpen_top]
          exact this
      · refine (epsilonInverseImage.{u, v} _).essImage.prop_of_iso
          ((Abelian.proetaleInverseImageCompIso (pullback.snd (t k) g) g).app F ≪≫
            eqToIso (congrArg (fun h ↦ (Abelian.proetaleInverseImage.{u, v} h).obj F)
              pullback.condition.symm) ≪≫
            ((Abelian.proetaleInverseImageCompIso (pullback.fst (t k) g) (t k)).app F).symm).symm ?_
        exact epsilonInverseImage_essImage_proetaleInverseImage _ _ (hF k)
    refine epsilonInverseImage_essImage_of_restrictions i j hij F ?_ ?_
    · refine (epsilonInverseImage.{u, v} _).essImage.prop_of_iso
        ((Abelian.proetaleInverseImageIsoRestriction j).app F) (key _ j True fun x ↦ ?_)
      exact iff_true_intro (by simpa [j, U] using (Scheme.Opens.range_ι U ▸ Set.mem_range_self x :))
    · have : IsAffine (Spec (CommRingCat.of (Γ(Y, ⊤) ⧸ Ideal.span {f}))) := inferInstance
      refine key _ i False fun x ↦ iff_false_intro ?_
      have := Set.mem_range_self (f := i) x
      rwa [Scheme.range_zeroLocusImmersion] at this

end ProEtale

end AlgebraicGeometry

end
