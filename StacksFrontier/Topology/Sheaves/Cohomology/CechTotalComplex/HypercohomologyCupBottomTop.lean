module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyGradedPairingTop

/-!
# The cup product of the bottom and the top graded pieces

Let `K` be a bounded below complex of `𝒪_X`-modules concentrated in degrees `[0, d]` and
`γ : K ⊗ K ⟶ K` a pairing. A class `ξ ∈ Hⁱ(X, K)` and a class of `Hʲ(X, K)` coming from the top
truncation `σ^{≥d}K = Kᵈ[-d]` multiply through the graded pieces: only the bidegree `(0, d)`
component of `γ` contributes, so

`ξ ∪ w = x ∪ w̄`

where `x ∈ Hⁱ(X, K⁰[0])` is the image of `ξ` under `K ⟶ σ^{≤0}K = K⁰[0]`, `w̄ ∈ Hʲ(X, Kᵈ[-d])`
is the image of `w ∈ Hʲ(X, σ^{≥d}K)` and the product on the right is that of the pairing of the
graded pieces (`Stacks.Cech.Hypercohomology.gradedPairing`). This is how the identifications
`H⁰_{dR}(X/k) = H⁰(X, 𝒪_X)` and `H^{2d}_{dR}(X/k) = Hᵈ(X, Ωᵈ)` of the proof of
[Stacks, Tag 0FW7] carry the cup product `H⁰ × H^{2d} ⟶ H^{2d}` to the module structure.

## Main results

* `Stacks.Cech.Hypercohomology.ιTruncPlus_truncLEπ`: `σ^{≥p}K ⟶ K ⟶ σ^{≤p}K` factors through the
  term `Kᵖ[-p]`.
* `Stacks.Cech.Hypercohomology.bijective_hypercohomologyMap_truncPlusπ`: `σ^{≥p}L ⟶ Lᵖ[-p]` is
  bijective on hypercohomology when `L` vanishes above `p`.
* `Stacks.Cech.Hypercohomology.bijective_hypercohomologyMap_truncLEπ`: `K ⟶ σ^{≤p}K` is bijective
  on hypercohomology when `K` vanishes above `p`.
* `Stacks.Cech.Hypercohomology.bijective_hypercohomologyMap_ιTruncPlus_of_truncLEι`:
  `σ^{≥p}K ⟶ K` is bijective on `Hⁿ` when `K` vanishes above `p` and `Kᵖ[-p] ⟶ σ^{≤p}K` is
  bijective on `Hⁿ`.
* `Stacks.Cech.Hypercohomology.hypercohomologyMap_truncLEπ_cup_gradedPairing`: the cup product of
  the graded pieces in complementary bidegrees, read in `σ^{≤d}K`, lands in the top term.
* `Stacks.Cech.Hypercohomology.cup_ιTruncPlus_eq_cup_gradedPairing`: **`ξ ∪ w = x ∪ w̄`.**

## References

* [Stacks Project, Tag 0FW7](https://stacks.math.columbia.edu/tag/0FW7)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor)
open Stacks.Cech.LinearCupProduct (ComplexPairing tensorPresheafModules)
open StacksDraft.StupidTruncation
open Stacks.Cohomology.RightDerivedBoundary (toSC)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-! ### The two truncations at the same degree -/

section Truncations

variable (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))

/-- **`σ^{≥p}K ⟶ K ⟶ σ^{≤p}K` factors through the term in degree `p`**: it is the projection
`σ^{≥p}K ⟶ Kᵖ[-p]` followed by the inclusion `Kᵖ[-p] ⟶ σ^{≤p}K`. -/
theorem ιTruncPlus_truncLEπ (p : ℤ) :
    ιTruncPlus O K p ≫ truncLEπ O K p = truncPlusπ K.obj p ≫ truncLEι O K p := by
  refine ObjectProperty.hom_ext _ (HomologicalComplex.hom_ext _ _ fun n => ?_)
  change (HomologicalComplex.ιStupidTrunc K.obj (embeddingUpIntGE p)).f n ≫
      (K.obj.πStupidTrunc (embeddingUpIntLE p)).f n =
    (stupidTruncGEπ K.obj p).f n ≫ (stupidTruncLEι K.obj p).f n
  by_cases hn : n = p
  · subst hn
    rw [ιStupidTruncGE_f K.obj n n le_rfl, stupidTruncGEπ_f, stupidTruncLEι_f, Category.assoc,
      Iso.inv_hom_id_assoc, πStupidTrunc_f K.obj (embeddingUpIntLE n) (i := (n - n).toNat)
        (by change n - ((n - n).toNat : ℤ) = n; omega)]
  · by_cases hlt : n < p
    · exact (CochainComplex.isZero_of_isStrictlyGE (K.obj.stupidTrunc (embeddingUpIntGE p)) p n
        hlt).eq_of_src _ _
    · exact (isZero_truncLEPlus_X O K (show p < n by omega)).eq_of_tgt _ _

variable (L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)

/-- **`σ^{≥p}L ⟶ Lᵖ[-p]` is bijective on hypercohomology when `L` vanishes above `p`**: its
kernel `σ^{≥p+1}L` has zero terms. -/
theorem bijective_hypercohomologyMap_truncPlusπ (p : ℤ) (hL : ∀ q, p < q → IsZero (L.X q))
    (n : ℤ) : Function.Bijective (hypercohomologyMap O (truncPlusπ L p) n) := by
  have hS := truncSC_shortExact O L p
  have hz : ∀ m, Subsingleton (hypercohomology O (truncSC O L p).X₁ m) := fun m =>
    ModuleCat.subsingleton_of_isZero
      (isZero_hypercohomology_truncPlus_of_lt O L hL (show p < p + 1 by omega) m)
  change Function.Bijective (hypercohomologyMap O (truncSC O L p).g n)
  refine ⟨fun b b' hbb' => ?_, fun c => ?_⟩
  · have hker : ∀ c, hypercohomologyMap O (truncSC O L p).g n c = 0 → c = 0 := fun c hc => by
      obtain ⟨a, rfl⟩ := (exact_f_g O (truncSC O L p) hS n c).1 hc
      rw [(hz n).elim a 0, map_zero]
    exact sub_eq_zero.1 (hker _ (by rw [map_sub, hbb', sub_self]))
  · exact (exact_g_boundary O (truncSC O L p) hS n (n + 1) rfl c).1 ((hz (n + 1)).elim _ _)

/-- **`K ⟶ σ^{≤p}K` is bijective on hypercohomology when `K` vanishes above `p`**: it is then an
isomorphism of complexes. -/
theorem bijective_hypercohomologyMap_truncLEπ (p n : ℤ) (hd : ∀ q, p < q → IsZero (K.obj.X q)) :
    Function.Bijective (hypercohomologyMap O (truncLEπ O K p) n) := by
  have : K.obj.IsStrictlyLE p := (CochainComplex.isStrictlyLE_iff K.obj p).2 hd
  let eπ : K ≅ truncLEPlus O K p :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ (K.obj.πStupidTrunc (embeddingUpIntLE p))
      (isIso_πStupidTruncLE K.obj p))
  exact ConcreteCategory.bijective_of_isIso (hypercohomologyMapIso O eπ n).hom

/-- **`σ^{≥p}K ⟶ K` is bijective on `Hⁿ`** when `K` vanishes above `p` and the inclusion of the
top term `Kᵖ[-p] ⟶ σ^{≤p}K` is bijective on `Hⁿ`. -/
theorem bijective_hypercohomologyMap_ιTruncPlus_of_truncLEι (p n : ℤ)
    (hd : ∀ q, p < q → IsZero (K.obj.X q))
    (hι : Function.Bijective (hypercohomologyMap O (truncLEι O K p) n)) :
    Function.Bijective (hypercohomologyMap O (ιTruncPlus O K p) n) := by
  have hcomp : (hypercohomologyMap O (truncLEπ O K p) n) ∘
      (hypercohomologyMap O (ιTruncPlus O K p) n) =
      (hypercohomologyMap O (truncLEι O K p) n) ∘
        (hypercohomologyMap O (truncPlusπ K.obj p) n) := by
    funext w
    change (hypercohomologyMap O (ιTruncPlus O K p) n ≫ hypercohomologyMap O (truncLEπ O K p) n) w =
      (hypercohomologyMap O (truncPlusπ K.obj p) n ≫ hypercohomologyMap O (truncLEι O K p) n) w
    rw [← hypercohomologyMap_comp, ← hypercohomologyMap_comp, ιTruncPlus_truncLEπ]
  have h := hι.comp (bijective_hypercohomologyMap_truncPlusπ K.obj p hd n)
  rw [← hcomp] at h
  exact (Function.Bijective.of_comp_iff' (bijective_hypercohomologyMap_truncLEπ K p n hd) _).1 h

end Truncations

/-! ### The cup product of the bottom and the top graded pieces -/

section Cup

variable (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
  (hK : ∀ j, CechComputesSheaf O (K.obj.X j)) (γ : Pairing O K K K) (d : ℤ)
  (hd : ∀ n, d < n → IsZero (K.obj.X n))

/-- **The cup product of the graded pieces in complementary bidegrees, read in `σ^{≤d}K`, lands
in the top term**: it is the cup product for the bidegree `(a, b)` component `μ₀` of `γ`,
followed by the inclusion `Kᵈ[-d] ⟶ σ^{≤d}K`. -/
theorem hypercohomologyMap_truncLEπ_cup_gradedPairing (a b : ℤ) (hab : a + b = d)
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤)
      (sectionsP O (K.obj.X a)) (sectionsP O (K.obj.X b)) (sectionsP O (K.obj.X d)))
    (hγ : γ.μ a b d hab = μ₀) (hA : CechComputes O (singlePlus O (K.obj.X a) a))
    (hB : CechComputes O (singlePlus O (K.obj.X b) b)) (i j n : ℤ) (hij : i + j = n)
    (x : hypercohomology O (singlePlus O (K.obj.X a) a) i)
    (y : hypercohomology O (singlePlus O (K.obj.X b) b) j) :
    hypercohomologyMap O (truncLEπ O K d) n
        (cup O hA hB (gradedPairing K γ d hd a b hab) i j n hij x y) =
      hypercohomologyMap O (truncLEι O K d) n
        (cup O hA hB (singlePairingAtTo O a b d hab μ₀) i j n hij x y) :=
  ((cup_comp O hA hB (gradedPairing K γ d hd a b hab) (truncLEπ O K d) i j n hij x y).symm.trans
    (congrArg (fun D => cup O hA hB D i j n hij x y)
      (gradedPairing_comp_truncLEπ K γ d hd a b hab μ₀ hγ))).trans
    (cup_comp O hA hB (singlePairingAtTo O a b d hab μ₀) (truncLEι O K d) i j n hij x y)

include hd in
/-- The pairing `γ` on `K ⊗ σ^{≥d}K`, descended to `σ^{≤0}K ⊗ σ^{≥d}K` and restricted along
`K⁰[0] ⟶ σ^{≤0}K`, is the pairing of the graded pieces in bidegree `(0, d)` after
`σ^{≥d}K ⟶ Kᵈ[-d]`. -/
theorem pairingHom_truncLEι_zero_truncLEGEPairing :
    PairingHom O (truncLEι O K 0) (𝟙 _) (𝟙 K)
      ((gradedPairing K γ d hd 0 d (zero_add d)).precompRight (truncPlusπ K.obj d))
      (truncLEGEPairing K γ d hd 0 d (by omega)) := fun a b n h => by
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f,
    ObjectProperty.FullSubcategory.id_hom, Category.comp_id, Category.id_comp]
  rw [ComplexPairing.precompRight_μ]
  by_cases ha : a = 0
  · subst ha
    by_cases hb : b = d
    · subst hb h
      rw [gradedPairing_μ, truncLEGEPairing_μ K γ b hd 0 b (by omega) _ _ _ rfl le_rfl,
        ← NatTrans.comp_app_assoc, ← Functor.map_comp, sectionsComplex_truncLEι_f K 0,
        NatTrans.naturality_assoc, ← Functor.map_comp_assoc,
        sectionsComplex_truncSC_g_singleXIsoAt]
      rfl
    · rw [gradedPairing_μ_of_ne K γ d hd _ _ (zero_add d) _ _ n h (fun h => hb h.2),
        Limits.comp_zero, truncLEGEPairing_μ K γ d hd 0 d (by omega) _ _ _ h le_rfl]
      by_cases hqb : d ≤ b
      · exact (isZero_sections (hd n (by omega))).eq_of_tgt _ _
      · have h0 : ((Stacks.Cech.Refinement.sectionsComplex O).map (ιTruncPlus O K d).hom).f b = 0 :=
          (isZero_sections (CochainComplex.isZero_of_isStrictlyGE
            (K.obj.stupidTrunc (embeddingUpIntGE d)) d b (by omega))).eq_of_src _ _
        rw [h0, tensorPresheafModules_obj_map_zero, Limits.zero_comp, Limits.comp_zero,
          Limits.comp_zero]
  · rw [gradedPairing_μ_of_ne K γ d hd _ _ (zero_add d) _ _ n h (fun h => ha h.1), Limits.comp_zero]
    have h0 : ((Stacks.Cech.Refinement.sectionsComplex O).map (truncLEι O K 0).hom).f a = 0 :=
      (isZero_sections (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 (K.obj.X 0) a
        ha)).eq_of_src _ _
    rw [h0, tensorPresheafModules_map_zero, Limits.zero_comp]

include hd in
/-- **The cup product of a class of `K` with a class of the top truncation is computed by the
graded pieces in bidegree `(0, d)`**: for `ξ ∈ Hⁱ(X, K)` with image `x ∈ Hⁱ(X, K⁰[0])` in
`σ^{≤0}K = K⁰[0]` and `w ∈ Hʲ(X, σ^{≥d}K)`, `ξ ∪ w = x ∪ w̄` with `w̄ ∈ Hʲ(X, Kᵈ[-d])` the
image of `w`. -/
theorem cup_ιTruncPlus_eq_cup_gradedPairing (i j n : ℤ) (hij : i + j = n)
    (ξ : hypercohomology O K i) (w : hypercohomology O (truncPlus O K.obj d) j)
    (x : hypercohomology O (singlePlus O (K.obj.X 0) 0) i)
    (hx : hypercohomologyMap O (truncLEι O K 0) i x = hypercohomologyMap O (truncLEπ O K 0) i ξ) :
    cup O (cechComputes_of_terms O K hK) (cechComputes_of_terms O K hK) γ i j n hij ξ
        (hypercohomologyMap O (ιTruncPlus O K d) j w) =
      cup O (cechComputes_singlePlus_X K hK 0) (cechComputes_singlePlus_X K hK d)
        (gradedPairing K γ d hd 0 d (zero_add d)) i j n hij x
        (hypercohomologyMap O (truncPlusπ K.obj d) j w) := by
  have hKK := cechComputes_of_terms O K hK
  have hT := cechComputes_truncPlus K hK d
  have hL := cechComputes_truncLEPlus K hK 0
  have h₁ := cup_precompRight O hKK hKK hT γ (ιTruncPlus O K d) i j n hij ξ w
  have h₂ := cup_natural O hKK hT hL hT (truncLEπ O K 0) (𝟙 _) (𝟙 _)
    (γ.precompRight (ιTruncPlus O K d)) (truncLEGEPairing K γ d hd 0 d (by omega))
    (pairingHom_descLE _ 0 _) i j n hij ξ w
  have h₃ := cup_natural O (cechComputes_singlePlus_X K hK 0) hT hL hT (truncLEι O K 0) (𝟙 _)
    (𝟙 _) _ _ (pairingHom_truncLEι_zero_truncLEGEPairing K γ d hd) i j n hij x w
  have h₄ := cup_precompRight O (cechComputes_singlePlus_X K hK 0)
    (cechComputes_singlePlus_X K hK d) hT (gradedPairing K γ d hd 0 d (zero_add d))
    (truncPlusπ K.obj d) i j n hij x w
  rw [hypercohomologyMap_id, hypercohomologyMap_id] at h₂ h₃
  refine h₁.symm.trans ((h₂.trans ?_).trans (h₃.symm.trans h₄))
  rw [← hx]

end Cup

end Stacks.Cech.Hypercohomology

end
