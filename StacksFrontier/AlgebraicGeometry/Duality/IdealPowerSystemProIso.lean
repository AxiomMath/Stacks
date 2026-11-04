module

public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerCohomologyProIso
import all StacksFrontier.AlgebraicGeometry.Duality.IdealPowerCohomologyProIso
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerCohomologyProIsomorphism
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.ProIsomorphismOfKernelSystems
import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm
import StacksFrontier.Homology.DerivedCategory.InverseSystem.ProIsomorphismInterleaving

/-!
# Changing the ideal and the module in an ideal-power system

Let `X` be a Noetherian scheme, let `𝓘` and `𝓙` be quasi-coherent sheaves of ideals on `X` with the
same vanishing locus and let `M ≅ N` be an isomorphism of sheaves of modules. Then the inverse
systems `(𝓘^n M)` and `(𝓙^n N)` of `Stacks.Duality.idealPowerSystem` are pro-isomorphic.

## Main definitions

* `Stacks.Duality.idealPowerMultipleMapOfLE`: the restriction of a morphism `M ⟶ N` to a map
  `𝓘^n M ⟶ 𝓙^m N` of ideal-power subsheaves.

## Main results

* `Stacks.Duality.exists_pow_le_of_support_le`: if the vanishing locus of `𝓙` is contained in that
  of `𝓘`, then `𝓘^c ⊆ 𝓙` for some `c`.
* `Stacks.Duality.idealPowerMultiple_mul_le`: if `𝓘^c ⊆ 𝓙`, then `𝓘^{cn} M ⊆ 𝓙^n M`.
* `Stacks.Duality.nonempty_proIso_idealPowerSystem`: the inverse systems `(𝓘^n M)` and `(𝓙^n N)`
  are pro-isomorphic.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open InverseSequence

universe v v' u u' w

namespace Stacks.Duality

variable {X : Scheme.{u}}

variable (I : X.IdealSheafData) (F : CochainComplex X.Modules ℤ) (p : ℤ)

/-! ### Changing the ideal and the module -/

/-- **Comparing ideals with nested vanishing loci.** On a Noetherian scheme, if the vanishing locus
of `𝓙` is contained in that of `𝓘`, then `𝓘^c ⊆ 𝓙` for some `c`. -/
lemma exists_pow_le_of_support_le [IsNoetherian X] {I J : X.IdealSheafData}
    (h : J.support ≤ I.support) : ∃ c : ℕ, I ^ c ≤ J := by
  have hrad : I ≤ J.radical := by
    rw [← Scheme.IdealSheafData.vanishingIdeal_support]
    exact Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp h
  have hpow : ∀ U : X.affineOpens, ∃ n : ℕ, I.ideal U ^ n ≤ J.ideal U := fun U =>
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    Ideal.exists_pow_le_of_le_radical_of_fg (Scheme.IdealSheafData.le_def.mp hrad U)
      (Ideal.fg_of_isNoetherianRing _)
  choose n hn using hpow
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens ↦ (U.1 : Set X))
    (fun U ↦ U.1.2) fun x _ ↦ by
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
      exact Set.mem_iUnion.mpr ⟨U, hU⟩
  refine ⟨s.sup n, Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : s ↦ U.1) ?_ fun U ↦ ?_⟩
  · refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨U, hU⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U, hU.1⟩, hU.2⟩
  · simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
    exact (Ideal.pow_le_pow_right (Finset.le_sup U.2)).trans (hn U.1)

/-- If `𝓘^c ⊆ 𝓙`, then `𝓘^{cn} M ⊆ 𝓙^n M` for every sheaf of modules `M`. -/
lemma idealPowerMultiple_mul_le {I J : X.IdealSheafData} {c : ℕ} (h : I ^ c ≤ J) (n : ℕ)
    (M : X.Modules) :
    Stacks.Algebraization.idealPowerMultiple I (c * n) M ≤
      Stacks.Algebraization.idealPowerMultiple J n M := by
  rw [Stacks.Algebraization.idealPowerMultiple_le_iff]
  intro U
  refine (Submodule.smul_mono_left ?_).trans
    ((Stacks.Algebraization.idealPowerMultiple_le_iff J n M _).1 le_rfl U)
  rw [pow_mul]
  exact pow_le_pow_left' (by simpa using Scheme.IdealSheafData.le_def.mp h U) n

/-- The restriction of a morphism `M ⟶ N` to a map `𝓘^n M ⟶ 𝓙^m N` of ideal-power subsheaves, which
exists once `𝓘^n N ⊆ 𝓙^m N`. -/
def idealPowerMultipleMapOfLE {I J : X.IdealSheafData} {M N : X.Modules} (f : M ⟶ N) {n m : ℕ}
    (h : Stacks.Algebraization.idealPowerMultiple I n N ≤
      Stacks.Algebraization.idealPowerMultiple J m N) :
    ((Stacks.Algebraization.idealPowerMultiple I n M).toSheafOfModules : X.Modules) ⟶
      ((Stacks.Algebraization.idealPowerMultiple J m N).toSheafOfModules : X.Modules) :=
  sheafSubmoduleMap f (Stacks.Algebraization.idealPowerMultiple I n M)
    (Stacks.Algebraization.idealPowerMultiple J m N) (idealPowerMultiple_le_comap I n f _ h)

/-- The restriction of `f` to ideal-power subsheaves is compatible with the inclusions. -/
lemma idealPowerMultipleMapOfLE_subι {I J : X.IdealSheafData} {M N : X.Modules} (f : M ⟶ N)
    {n m : ℕ} (h : Stacks.Algebraization.idealPowerMultiple I n N ≤
      Stacks.Algebraization.idealPowerMultiple J m N) :
    idealPowerMultipleMapOfLE f h ≫ subι (Stacks.Algebraization.idealPowerMultiple J m N) =
      subι (Stacks.Algebraization.idealPowerMultiple I n M) ≫ f :=
  sheafSubmoduleMap_comp_subι _ _ _ _

/-- Restrictions of composable maps to ideal-power subsheaves compose. -/
lemma idealPowerMultipleMapOfLE_comp {I J K : X.IdealSheafData} {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) {n m k : ℕ}
    (h₁ : Stacks.Algebraization.idealPowerMultiple I n N ≤
      Stacks.Algebraization.idealPowerMultiple J m N)
    (h₂ : Stacks.Algebraization.idealPowerMultiple J m P ≤
      Stacks.Algebraization.idealPowerMultiple K k P)
    (h₃ : Stacks.Algebraization.idealPowerMultiple I n P ≤
      Stacks.Algebraization.idealPowerMultiple K k P) :
    idealPowerMultipleMapOfLE f h₁ ≫ idealPowerMultipleMapOfLE g h₂ =
      idealPowerMultipleMapOfLE (f ≫ g) h₃ :=
  cancel_subι _ _ _ <|
    (Category.assoc _ _ _).trans <|
      (congrArg (idealPowerMultipleMapOfLE f h₁ ≫ ·) (idealPowerMultipleMapOfLE_subι g h₂)).trans <|
        (Category.assoc _ _ _).symm.trans <|
          (congrArg (· ≫ g) (idealPowerMultipleMapOfLE_subι f h₁)).trans <|
            (Category.assoc _ _ _).trans (idealPowerMultipleMapOfLE_subι (f ≫ g) h₃).symm

/-- The restriction of the identity to ideal-power subsheaves is the inclusion. -/
lemma idealPowerMultipleMapOfLE_id {I J : X.IdealSheafData} {M : X.Modules} {n m : ℕ}
    (h : Stacks.Algebraization.idealPowerMultiple I n M ≤
      Stacks.Algebraization.idealPowerMultiple J m M) :
    idealPowerMultipleMapOfLE (𝟙 M) h = subHom h :=
  cancel_subι _ _ _ <|
    (idealPowerMultipleMapOfLE_subι (𝟙 M) h).trans <|
      (Category.comp_id _).trans (homOfLE_comp_subι h).symm

/-- Restrictions of maps to ideal-power subsheaves compose, when the composite is known. -/
private theorem idealPowerMultipleMapOfLE_comp_of_eq {I J K : X.IdealSheafData}
    {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (k : M ⟶ P) (hk : f ≫ g = k) {n m l : ℕ}
    (h₁ : Stacks.Algebraization.idealPowerMultiple I n N ≤
      Stacks.Algebraization.idealPowerMultiple J m N)
    (h₂ : Stacks.Algebraization.idealPowerMultiple J m P ≤
      Stacks.Algebraization.idealPowerMultiple K l P)
    (h₃ : Stacks.Algebraization.idealPowerMultiple I n P ≤
      Stacks.Algebraization.idealPowerMultiple K l P) :
    idealPowerMultipleMapOfLE f h₁ ≫ idealPowerMultipleMapOfLE g h₂ =
      idealPowerMultipleMapOfLE k h₃ := by
  subst hk
  exact idealPowerMultipleMapOfLE_comp f g h₁ h₂ h₃

/-- **Changing the ideal and the module in an ideal-power system.** On a Noetherian scheme, two
quasi-coherent sheaves of ideals `𝓘` and `𝓙` with the same vanishing locus and an isomorphism
`M ≅ N` of sheaves of modules give pro-isomorphic inverse systems `(𝓘^n M)` and `(𝓙^n N)`. -/
theorem nonempty_proIso_idealPowerSystem [IsNoetherian X] {I J : X.IdealSheafData}
    (hIJ : I.support = J.support) {M N : X.Modules} (e : M ≅ N) :
    Nonempty (ProIso (idealPowerSystem I M) (idealPowerSystem J N)) := by
  obtain ⟨c, hc⟩ := exists_pow_le_of_support_le hIJ.ge
  obtain ⟨d, hd⟩ := exists_pow_le_of_support_le hIJ.le
  have hle : ∀ {I J : X.IdealSheafData} {c : ℕ}, I ^ c ≤ J → ∀ (m : ℕ) (P : X.Modules),
      Stacks.Algebraization.idealPowerMultiple I ((c + 1) * m) P ≤
        Stacks.Algebraization.idealPowerMultiple J m P := fun h m P =>
    (idealPowerMultiple_antitone _ P (Nat.mul_le_mul_right m (Nat.le_succ _))).trans
      (idealPowerMultiple_mul_le h m P)
  refine ⟨{
    α := fun m => (c + 1) * m
    β := fun m => (d + 1) * m
    αmono := fun _ _ h => Nat.mul_le_mul_left _ h
    βmono := fun _ _ h => Nat.mul_le_mul_left _ h
    αle := fun m => Nat.le_mul_of_pos_left m (Nat.succ_pos c)
    βle := fun m => Nat.le_mul_of_pos_left m (Nat.succ_pos d)
    φ := fun m => idealPowerMultipleMapOfLE e.hom (hle hc m N)
    ψ := fun m => idealPowerMultipleMapOfLE e.inv (hle hd m M)
    φnat := ?_
    ψnat := ?_
    ψφ := ?_
    φψ := ?_ }⟩
  · intro m m' h
    rw [tr_idealPowerSystem, tr_idealPowerSystem, ← idealPowerMultipleMapOfLE_id,
      ← idealPowerMultipleMapOfLE_id]
    have h₃ := (idealPowerMultiple_antitone I N (Nat.mul_le_mul_left (c + 1) h)).trans
      (hle hc m N)
    exact (idealPowerMultipleMapOfLE_comp_of_eq _ _ e.hom (Category.id_comp _) _ _ h₃).trans
      (idealPowerMultipleMapOfLE_comp_of_eq _ _ e.hom (Category.comp_id _) _ _ h₃).symm
  · intro m m' h
    rw [tr_idealPowerSystem, tr_idealPowerSystem, ← idealPowerMultipleMapOfLE_id,
      ← idealPowerMultipleMapOfLE_id]
    have h₃ := (idealPowerMultiple_antitone J M (Nat.mul_le_mul_left (d + 1) h)).trans
      (hle hd m M)
    exact (idealPowerMultipleMapOfLE_comp_of_eq _ _ e.inv (Category.id_comp _) _ _ h₃).trans
      (idealPowerMultipleMapOfLE_comp_of_eq _ _ e.inv (Category.comp_id _) _ _ h₃).symm
  · intro m
    rw [tr_idealPowerSystem]
    exact (idealPowerMultipleMapOfLE_comp_of_eq _ _ _ e.hom_inv_id _ _ _).trans
      (idealPowerMultipleMapOfLE_id _)
  · intro m
    rw [tr_idealPowerSystem]
    exact (idealPowerMultipleMapOfLE_comp_of_eq _ _ _ e.inv_hom_id _ _ _).trans
      (idealPowerMultipleMapOfLE_id _)

end Stacks.Duality

end
