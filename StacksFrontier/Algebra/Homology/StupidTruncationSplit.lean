module

public import StacksFrontier.Algebra.Homology.StupidTruncation

/-!
# A complex with vanishing first differential splits off its bottom term

Let `K` be a cochain complex in an abelian category, concentrated in degrees `≥ 0`, whose
differential `K⁰ ⟶ K¹` vanishes. Then `K` is the direct sum of its bottom term placed in degree
`0` and its brutal truncation `σ^{≥1}K`:

`K ≅ (single 0).obj K⁰ ⊞ σ^{≥1}K`.

## Main results

* `StacksDraft.StupidTruncation.nonempty_iso_single_biprod_stupidTrunc`: the decomposition.

## Implementation notes

The short exact sequence `0 ⟶ σ^{≥1}K ⟶ σ^{≥0}K ⟶ (single 0).obj K⁰ ⟶ 0` of
`StacksDraft.StupidTruncation.stupidTruncGEShortComplex_shortExact` acquires a section as soon as
the differential out of degree `0` vanishes: the inclusion of `K⁰` in degree `0` is then a chain
map. A short exact sequence with a section of its quotient map splits
(`CategoryTheory.ShortComplex.Splitting.ofExactOfSection`), and the inclusion `σ^{≥0}K ⟶ K` is
an isomorphism because `K` is concentrated in degrees `≥ 0`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex ComplexShape

namespace StacksDraft.StupidTruncation

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C] (K : CochainComplex C ℤ)

/-- The inclusion `σ^{≥a}K ⟶ K` is an isomorphism when `K` is concentrated in degrees `≥ a`. -/
theorem isIso_ιStupidTrunc_of_isStrictlyGE (a : ℤ) [K.IsStrictlyGE a] :
    IsIso (ιStupidTrunc K (embeddingUpIntGE a)) := by
  have : ∀ n, IsIso ((ιStupidTrunc K (embeddingUpIntGE a)).f n) := fun n => by
    by_cases hn : a ≤ n
    · rw [ιStupidTruncGE_f K a n hn]
      infer_instance
    · exact ⟨0, (CochainComplex.isZero_of_isStrictlyGE (K.stupidTrunc (embeddingUpIntGE a)) a n
          (by omega)).eq_of_src _ _,
        (K.isZero_of_isStrictlyGE a n (by omega)).eq_of_src _ _⟩
  exact HomologicalComplex.Hom.isIso_of_components _

/-- In degrees `≥ a` the differential of `σ^{≥a}K` is that of `K`, read through the
identifications of terms. -/
theorem stupidTruncGE_d (a n m : ℤ) (hn : a ≤ n) (hm : a ≤ m) :
    (K.stupidTrunc (embeddingUpIntGE a)).d n m =
      (stupidTruncGEXIso K a n hn).hom ≫ K.d n m ≫ (stupidTruncGEXIso K a m hm).inv := by
  have h := (ιStupidTrunc K (embeddingUpIntGE a)).comm n m
  rw [ιStupidTruncGE_f K a n hn, ιStupidTruncGE_f K a m hm] at h
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A complex concentrated in degrees `≥ 0` with vanishing differential `K⁰ ⟶ K¹` is the direct
sum of `K⁰` in degree `0` and of its brutal truncation `σ^{≥1}K`.** -/
theorem nonempty_iso_single_biprod_stupidTrunc [K.IsStrictlyGE 0] (hd : K.d 0 1 = 0) :
    Nonempty (K ≅ (single C (.up ℤ) 0).obj (K.X 0) ⊞ K.stupidTrunc (embeddingUpIntGE 1)) := by
  let S := stupidTruncGEShortComplex K 0
  have hS : S.ShortExact := stupidTruncGEShortComplex_shortExact K 0
  have hd0 : (K.stupidTrunc (embeddingUpIntGE 0)).d 0 1 = 0 := by
    rw [stupidTruncGE_d K 0 0 1 le_rfl (by omega), hd, zero_comp, comp_zero]
  let s : (single C (.up ℤ) 0).obj (K.X 0) ⟶ K.stupidTrunc (embeddingUpIntGE 0) :=
    mkHomFromSingle (stupidTruncGEXIso K 0 0 le_rfl).inv fun k hk => by
      obtain rfl : k = 1 := by simpa using hk.symm
      rw [hd0, comp_zero]
  have hs : s ≫ S.g = 𝟙 _ := by
    apply from_single_hom_ext
    change s.f 0 ≫ (stupidTruncGEπ K 0).f 0 = 𝟙 _
    rw [mkHomFromSingle_f, stupidTruncGEπ_f, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id]
  have := isIso_ιStupidTrunc_of_isStrictlyGE K 0
  exact ⟨(asIso (ιStupidTrunc K (embeddingUpIntGE 0))).symm ≪≫
    (ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f).isoBinaryBiproduct ≪≫
    biprod.braiding _ _⟩

end StacksDraft.StupidTruncation

end
