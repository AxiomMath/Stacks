module

public import StacksFrontier.AlgebraicGeometry.VanishingSystemImmersion.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingFamilyDivisorsOnX
public import StacksFrontier.AlgebraicGeometry.Variety.Bertini.VanishingSystemFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniImmersionCondition

/-!
# The complete linear system of a high power of an ample module is an immersion

Let `X` be a nonempty proper scheme over a field `k` with an ample invertible module `ℒ`. For all
large `n`, the complete linear system `Γ(X, ℒ ^⊗ n)` generates `ℒ ^⊗ n`, and the morphism
`X ⟶ 𝐏(Γ(X, ℒ ^⊗ n))` it defines is an immersion. In the language of the Bertini files these are
hypotheses (2) and (3) of [Stacks, Tag 0FD6] for
`Stacks.SectionsVanishingOnSubscheme.ambientFamilyDivisors`.

The proof is [Stacks, Tag 0FD5] at the unit ideal. The closed subscheme it cuts out is empty, so
every global section vanishes on it (`vanishingSections_top_eq_top`), and its open complement is
all of `X`. The immersion `X ∖ ∅ ⟶ 𝐏(V_n)` that 0FD5 provides is therefore the immersion of the
complete linear system, precomposed with the isomorphism `X ∖ ∅ ≅ X`.

## Main results

* `Stacks.SectionsVanishingOnSubscheme.vanishingSections_top_eq_top`: every global section
  vanishes on the empty closed subscheme.
* `Stacks.SectionsVanishingOnSubscheme.exists_bound_isImmersive_ambientFamilyDivisors`: for all
  large `n` some basis of `Γ(X, ℒ ^⊗ n)` generates, and the complete linear system is an immersion
  in that basis.

## References

* [Stacks Project, Tag 0FD5](https://stacks.math.columbia.edu/tag/0FD5)
* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Ample Stacks.ProjectiveFromSections

universe u

namespace Stacks.SectionsVanishingOnSubscheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  {L : X.Modules} [IsInvertibleModule X L]

/-- The closed subscheme cut out by the unit ideal is empty. -/
instance isEmpty_subscheme_top : IsEmpty (⊤ : X.IdealSheafData).subscheme := by
  refine ⟨fun z => ?_⟩
  have hz : (⊤ : X.IdealSheafData).subschemeι z ∈ Set.range (⊤ : X.IdealSheafData).subschemeι :=
    ⟨z, rfl⟩
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_top] at hz
  exact hz

/-- **Every global section vanishes on the empty closed subscheme**: the space `V_n` attached to
the unit ideal is all of `Γ(X, ℒ ^⊗ n)`. -/
theorem vanishingSections_top_eq_top (n : ℤ) :
    vanishingSections k f (⊤ : X.IdealSheafData) L n = ⊤ := by
  refine eq_top_iff.2 fun s _ => ?_
  rw [mem_vanishingSections_iff]
  have : Subsingleton Γ((⊤ : X.IdealSheafData).subscheme, ⊤) := inferInstance
  have : Subsingleton Γ((Scheme.Modules.pullback (⊤ : X.IdealSheafData).subschemeι).obj
      (tensorPowModule X L n), ⊤) :=
    Module.subsingleton Γ((⊤ : X.IdealSheafData).subscheme, ⊤) _
  exact Subsingleton.elim (α := Γ((Scheme.Modules.pullback (⊤ : X.IdealSheafData).subschemeι).obj
      (tensorPowModule X L n), ⊤)) _ _

/-- The open complement of the empty closed subscheme is the whole of `X`. -/
theorem openComplement_top : openComplement (⊤ : X.IdealSheafData) = ⊤ := by
  ext x
  simp [openComplement, Scheme.IdealSheafData.support_top]

/-- Every point of `X` lies in the open complement of the empty closed subscheme. -/
private theorem mem_openComplement_top (x : X) : x ∈ openComplement (⊤ : X.IdealSheafData) := by
  rw [openComplement_top]; exact trivial

/-- The inclusion of the open complement of the empty closed subscheme into `X` is an
isomorphism. -/
instance isIso_openComplement_top_ι : IsIso (openComplement (⊤ : X.IdealSheafData)).ι := by
  rw [isIso_iff_isOpenImmersion_and_surjective]
  refine ⟨inferInstance, ⟨fun x => ?_⟩⟩
  have hx : x ∈ openComplement (⊤ : X.IdealSheafData) := by
    rw [openComplement_top]; exact trivial
  exact ⟨⟨x, hx⟩, rfl⟩

/-- **Hypotheses (2) and (3) of [Stacks, Tag 0FD6] for the complete linear system of a high power
of an ample module.** Let `X` be nonempty and proper over `k` and `ℒ` ample. Then for all large
`n` there is a basis `b'` of `Γ(X, ℒ ^⊗ n)` whose sections generate `ℒ ^⊗ n` and in which the
morphism `X ⟶ 𝐏(Γ(X, ℒ ^⊗ n))` of the complete linear system is an immersion. The immersion
hypothesis does not depend on the basis
(`Stacks.Bertini.FamilyDivisors.isImmersive_congr_basis'`), so one basis is enough. -/
theorem exists_bound_isImmersive_ambientFamilyDivisors [IsProper f] [Nonempty X]
    (hL : IsAmple X L) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n → ∃ (p : ℕ) (b' : Module.Basis (Fin (p + 1)) k
        (Stacks.Bertini.globalSections k f (tensorPowModule X L n)))
        (hb' : (ambientFamilyDivisors k f (L := L) n).GeneratesBy b'),
      (ambientFamilyDivisors k f (L := L) n).IsImmersive b' hb' := by
  obtain ⟨n₀, hn₀⟩ := exists_bound_generatesOffSupport_and_isImmersion k f
    (⊤ : X.IdealSheafData) hL
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨h, himm⟩ := hn₀ n hn
  have hnt : Nontrivial (vanishingSections k f (⊤ : X.IdealSheafData) L n) := by
    obtain ⟨x⟩ := ‹Nonempty X›
    obtain ⟨t, ht⟩ := Stacks.StalkwiseGeneration.exists_mem_nvOpen_of_span_eq_top
      (tensorPowModule X L n) _ x (h x (mem_openComplement_top x))
    refine ⟨⟨t, 0, fun h0 => ne_zero_of_mem_nvOpen _ ht ?_⟩⟩
    rw [h0]; rfl
  obtain ⟨N, hN⟩ : ∃ N : ℕ,
      Module.finrank k (vanishingSections k f (⊤ : X.IdealSheafData) L n) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Module.finrank_pos.ne'
  let b := Module.finBasisOfFinrankEq k _ hN
  let e := LinearEquiv.ofTop _ (vanishingSections_top_eq_top k f (L := L) n)
  have hgen : GeneratesStalks (basisSection k f b) :=
    Stacks.AmpleImmersionReduction.generatesStalks_of_forall_exists_mem _ fun x =>
      exists_mem_nvCover_basisSection k f b h (mem_openComplement_top x)
  refine ⟨N, b.map e, hgen, ?_⟩
  refine ((ambientFamilyDivisors k f (L := L) n).isImmersive_iff_isImmersion_toProjectiveSpaceOver
    (b.map e) hgen).2 ?_
  have h1 := (isImmersion_iff_isImmersion_toProjectiveSpaceOver k f b h).1 (himm N b).1
  rw [toProjectiveSpaceOverOffSupport_eq] at h1
  have h1' : IsImmersion ((openComplement (⊤ : X.IdealSheafData)).ι ≫
      toProjectiveSpaceOver (basisSection k f b) hgen f) := by
    rwa [comp_toProjectiveSpaceOver_self (openComplement (⊤ : X.IdealSheafData)).ι
      (basisSection k f b) hgen f (generatesStalks_restrictedBasisSection k f ⊤ b h)]
  have h2 : IsImmersion (inv (openComplement (⊤ : X.IdealSheafData)).ι ≫
      (openComplement (⊤ : X.IdealSheafData)).ι ≫
        toProjectiveSpaceOver (basisSection k f b) hgen f) :=
    inferInstance
  rwa [IsIso.inv_hom_id_assoc] at h2

end Stacks.SectionsVanishingOnSubscheme

end
