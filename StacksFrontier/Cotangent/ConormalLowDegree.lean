module

public import StacksFrontier.Cotangent.Surjection
public import StacksFrontier.Cotangent.SurjectivePresentationHigherHomology

/-!
# The conormal complex of the standard resolution is acyclic in degrees `0` and `-1`

Let `A → B` be an arbitrary ring map, let `P_•` be the standard resolution of `B` over `A` and
let `𝒥_n = ker(P_n → B)`. Remark 08R7 records that

`H₀(C_{B/A}, 𝒥/𝒥²) = 0` and `H₁(C_{B/A}, 𝒥/𝒥²) = 0`,

which it reads off the spectral sequence of `𝒥 ⊗^L_𝒪 B̲` together with the vanishing
`Lπ_!(𝒥) = 0` of Tag 08QK. Both groups are computed on the standard resolution — that is Tag
08PS — and this file proves the two vanishings there, directly, for the Moore complex
`Stacks.Cotangent.conormalMooreComplex` of the simplicial conormal module.

## Main results

* `Stacks.Cotangent.isZero_conormalMooreComplex_homology_zero` and
  `Stacks.Cotangent.isZero_conormalMooreComplex_homology_one`: the two vanishings.
* `Stacks.Cotangent.isLE_conormalComplex`: consequently the conormal complex lies in
  `D^{≤ -2}(B)`.

## Implementation notes

The two computations are the ones already carried out, for a *surjective* `A → B`, in
`StacksFrontier/Cotangent/Surjection.lean`: `H₀` vanishes because every conormal class in degree
zero is the boundary of the class of `[p] - [0]`
(`CommAlgCat.delta_varOne_sub`), and `H₁` vanishes because a degree-one conormal cycle differs by
an element of `𝒥₁²` from a cycle of the standard resolution — which is a boundary, the standard
resolution being a resolution — while the correcting element is itself a boundary because `𝒥₀²`
consists of boundaries (`CommAlgCat.exists_sq_of_mem_sq`). Neither input uses the surjectivity of
`A → B`: what both need is the surjectivity of the *augmentation* `P_n → B`, which holds for the
standard resolution of any ring map. So the statements here carry no hypothesis, and are proved
from the same hypothesis-free lemmas of `StacksFrontier/Cotangent/Surjection.lean`, restated for the
hypothesis-free simplicial conormal module
`Stacks.Cotangent.conormalSimplicialModule` of
`StacksFrontier/Cotangent/SurjectivePresentationHigherHomology.lean`.

## References

* [Stacks Project, Tag 08R7](https://stacks.math.columbia.edu/tag/08R7)
* [Stacks Project, Tag 08PS](https://stacks.math.columbia.edu/tag/08PS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v

namespace Stacks.Cotangent

open CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- The kernel of the presentation `Pₙ → B` is the augmentation ideal. -/
theorem conormalExtension_ker (n : SimplexCategoryᵒᵖ) :
    (conormalExtension A B n).ker = augmentationIdeal A B n := rfl

/-- The first differential of the Moore complex is the difference of the two faces. -/
theorem conormalMooreComplex_d_one_zero :
    (conormalMooreComplex A B).d 1 0 =
      (conormalSimplicialModule A B).δ (0 : Fin 2) -
        (conormalSimplicialModule A B).δ (1 : Fin 2) := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_two, sub_eq_add_neg]
  simp

/-- The second differential of the Moore complex is the alternating sum of the three faces. -/
theorem conormalMooreComplex_d_two_one :
    (conormalMooreComplex A B).d 2 1 =
      (conormalSimplicialModule A B).δ (0 : Fin 3) -
        (conormalSimplicialModule A B).δ (1 : Fin 3) +
        (conormalSimplicialModule A B).δ (2 : Fin 3) := by
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.AlternatingFaceMapComplex.objD, Fin.sum_univ_three, sub_eq_add_neg]
  simp

/-- Conormal classes of two elements of the kernel with the same underlying element agree. -/
private theorem cotangent_mk_congr {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {P : Algebra.Extension R S} {y z : P.ker}
    (h : z.1 = y.1) : Algebra.Extension.Cotangent.mk y = Algebra.Extension.Cotangent.mk z :=
  congrArg _ (Subtype.ext h).symm

/-- The value of a simplicial operator of the conormal module on a conormal class: it is the
class of the image, whichever representative of that image is supplied. -/
theorem conormalSimplicialModule_map_mk {i j : SimplexCategoryᵒᵖ} (f : i ⟶ j)
    (y : (conormalExtension A B i).ker) (z : (conormalExtension A B j).ker)
    (hz : (z : (conormalExtension A B j).Ring) =
      (conormalExtensionHom A B f).toAlgHom (y : (conormalExtension A B i).Ring)) :
    (conormalSimplicialModule A B).map f (Algebra.Extension.Cotangent.mk y) =
      Algebra.Extension.Cotangent.mk z := by
  change Algebra.Extension.Cotangent.map (conormalExtensionHom A B f)
    (Algebra.Extension.Cotangent.mk y) = _
  rw [Algebra.Extension.Cotangent.map_mk]
  exact cotangent_mk_congr hz

/-- The value of a face map of the conormal simplicial module on a conormal class. -/
theorem conormalSimplicialModule_delta_mk (n : ℕ) (i : Fin (n + 2))
    (y : (conormalExtension A B (op ⦋n + 1⦌)).ker)
    (z : (conormalExtension A B (op ⦋n⦌)).ker)
    (hz : z.1 = (standardResolution A B).left.δ i y.1) :
    (conormalSimplicialModule A B).δ i (Algebra.Extension.Cotangent.mk y) =
      Algebra.Extension.Cotangent.mk z :=
  conormalSimplicialModule_map_mk A B (SimplexCategory.δ i).op y z hz

/-- The alternating sum of the two faces, computed on conormal classes. -/
theorem conormalDelta_sub_mk (w : (conormalExtension A B (op ⦋0 + 1⦌)).ker)
    (z₀ z₁ z : (conormalExtension A B (op ⦋0⦌)).ker)
    (h₀ : z₀.1 = (standardResolution A B).left.δ (0 : Fin 2) w.1)
    (h₁ : z₁.1 = (standardResolution A B).left.δ (1 : Fin 2) w.1)
    (hz : z.1 = z₀.1 - z₁.1) :
    (conormalSimplicialModule A B).δ (0 : Fin 2) (Algebra.Extension.Cotangent.mk w) -
        (conormalSimplicialModule A B).δ (1 : Fin 2) (Algebra.Extension.Cotangent.mk w) =
      Algebra.Extension.Cotangent.mk z := by
  rw [conormalSimplicialModule_delta_mk A B 0 (0 : Fin 2) w z₀ h₀,
    conormalSimplicialModule_delta_mk A B 0 (1 : Fin 2) w z₁ h₁]
  change (Algebra.Extension.Cotangent.mk z₀ - Algebra.Extension.Cotangent.mk z₁ :
    (conormalExtension A B (op ⦋0⦌)).Cotangent) = Algebra.Extension.Cotangent.mk z
  rw [← map_sub]
  exact cotangent_mk_congr hz

/-- The alternating sum of the three faces, computed on conormal classes. -/
theorem conormalDelta_alt_mk (w : (conormalExtension A B (op ⦋1 + 1⦌)).ker)
    (z₀ z₁ z₂ z : (conormalExtension A B (op ⦋1⦌)).ker)
    (h₀ : z₀.1 = (standardResolution A B).left.δ (0 : Fin 3) w.1)
    (h₁ : z₁.1 = (standardResolution A B).left.δ (1 : Fin 3) w.1)
    (h₂ : z₂.1 = (standardResolution A B).left.δ (2 : Fin 3) w.1)
    (hz : z.1 = z₀.1 - z₁.1 + z₂.1) :
    (conormalSimplicialModule A B).δ (0 : Fin 3) (Algebra.Extension.Cotangent.mk w) -
        (conormalSimplicialModule A B).δ (1 : Fin 3) (Algebra.Extension.Cotangent.mk w) +
        (conormalSimplicialModule A B).δ (2 : Fin 3) (Algebra.Extension.Cotangent.mk w) =
      Algebra.Extension.Cotangent.mk z := by
  rw [conormalSimplicialModule_delta_mk A B 1 (0 : Fin 3) w z₀ h₀,
    conormalSimplicialModule_delta_mk A B 1 (1 : Fin 3) w z₁ h₁,
    conormalSimplicialModule_delta_mk A B 1 (2 : Fin 3) w z₂ h₂]
  change (Algebra.Extension.Cotangent.mk z₀ - Algebra.Extension.Cotangent.mk z₁ +
      Algebra.Extension.Cotangent.mk z₂ :
    (conormalExtension A B (op ⦋1⦌)).Cotangent) = Algebra.Extension.Cotangent.mk z
  rw [← map_sub, ← map_add]
  exact cotangent_mk_congr hz

/-! ### The two vanishing theorems -/

/-- **`H₀` of the simplicial conormal module vanishes.** Every conormal class in degree zero is
the boundary of the class of `[p] - [0]`. -/
theorem surjective_conormalMooreComplex_d_one_zero :
    Function.Surjective ((conormalMooreComplex A B).d 1 0) := by
  rw [conormalMooreComplex_d_one_zero]
  intro c
  obtain ⟨y, hy⟩ := Algebra.Extension.Cotangent.mk_surjective c
  have hw := varOne_sub_mem_augmentationIdeal A B y.1 y.2
  refine ⟨Algebra.Extension.Cotangent.mk ⟨standardResolutionVarOne A B y.1 -
    standardResolutionVarOne A B 0, hw⟩, ?_⟩
  rw [← hy]
  exact conormalDelta_sub_mk A B ⟨_, hw⟩
    ⟨_, delta_mem_augmentationIdeal A B 0 (0 : Fin 2) _ hw⟩
    ⟨_, delta_mem_augmentationIdeal A B 0 (1 : Fin 2) _ hw⟩ y rfl rfl
    (delta_varOne_sub A B y.1 y.2).symm

/-- The degree-zero homology of the Moore complex of the simplicial conormal module vanishes. -/
theorem isZero_conormalMooreComplex_homology_zero :
    IsZero ((conormalMooreComplex A B).homology 0) := by
  have hepi : Epi ((conormalMooreComplex A B).d 1 0) :=
    (ModuleCat.epi_iff_surjective _).2 (surjective_conormalMooreComplex_d_one_zero A B)
  refine IsZero.of_iso ?_ (conormalMooreComplex A B).isoHomologyι₀
  rw [IsZero.iff_id_eq_zero]
  have hp : (conormalMooreComplex A B).pOpcycles 0 = 0 := by
    rw [← cancel_epi ((conormalMooreComplex A B).d 1 0), Limits.comp_zero]
    exact (conormalMooreComplex A B).d_pOpcycles 1 0
  rw [← cancel_epi ((conormalMooreComplex A B).pOpcycles 0), Category.comp_id,
    Limits.comp_zero, hp]

/-- **`H₁` of the simplicial conormal module vanishes.** A degree-one conormal cycle differs by
an element of `𝒥₁²` from a cycle of the standard resolution, which is a boundary because the
standard resolution is a resolution; the correcting element is itself a boundary because `𝒥₀²`
consists of boundaries. -/
theorem exact_conormalDelta (c : (conormalSimplicialModule A B).obj (op ⦋0 + 1⦌))
    (hc : ((conormalSimplicialModule A B).δ (0 : Fin 2) -
      (conormalSimplicialModule A B).δ (1 : Fin 2)) c = 0) :
    ∃ c' : (conormalSimplicialModule A B).obj (op ⦋1 + 1⦌),
      ((conormalSimplicialModule A B).δ (0 : Fin 3) -
        (conormalSimplicialModule A B).δ (1 : Fin 3) +
        (conormalSimplicialModule A B).δ (2 : Fin 3)) c' = c := by
  obtain ⟨w, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective c
  set p : (standardResolution A B).left.obj (op ⦋1⦌) := w.1
  have hpker : p ∈ augmentationIdeal A B (op ⦋1⦌) := w.2
  have hd₀ := delta_mem_augmentationIdeal A B 0 (0 : Fin 2) p hpker
  have hd₁ := delta_mem_augmentationIdeal A B 0 (1 : Fin 2) p hpker
  have hc1 : Algebra.Extension.Cotangent.mk (P := conormalExtension A B (op ⦋0⦌))
      ⟨(standardResolution A B).left.δ (0 : Fin 2) p -
        (standardResolution A B).left.δ (1 : Fin 2) p,
        Ideal.sub_mem _ hd₀ hd₁⟩ = 0 :=
    (conormalDelta_sub_mk A B w ⟨_, hd₀⟩ ⟨_, hd₁⟩ ⟨_, Ideal.sub_mem _ hd₀ hd₁⟩
      rfl rfl rfl).symm.trans hc
  have hsq := (Algebra.Extension.Cotangent.mk_eq_zero_iff _).1 hc1
  obtain ⟨v, hvmem, hv⟩ := exists_sq_of_mem_sq A B _ hsq
  have hvker : v ∈ augmentationIdeal A B (op ⦋1⦌) := Ideal.pow_le_self two_ne_zero hvmem
  have hv' : (standardResolution A B).left.δ (0 : Fin 2) v -
      (standardResolution A B).left.δ (1 : Fin 2) v =
      (standardResolution A B).left.δ (0 : Fin 2) p -
        (standardResolution A B).left.δ (1 : Fin 2) p := hv
  have hcycle : (standardResolution A B).left.δ (0 : Fin 2) (p - v) -
      (standardResolution A B).left.δ (1 : Fin 2) (p - v) = 0 := by
    rw [map_sub, map_sub, sub_sub_sub_comm, hv', sub_self]
  obtain ⟨y, hy⟩ := standardResolution_exists_of_delta_sub_delta_eq_zero A B (p - v) hcycle
  have hyker : y ∈ augmentationIdeal A B (op ⦋2⦌) := by
    have e₀ := standardResolution_augmentation_δ A B 1 (0 : Fin 3) y
    have e₁ := standardResolution_augmentation_δ A B 1 (1 : Fin 3) y
    have e₂ := standardResolution_augmentation_δ A B 1 (2 : Fin 3) y
    have key : (standardResolution A B).hom.app (op ⦋1⦌)
        ((standardResolution A B).left.δ (0 : Fin 3) y -
          (standardResolution A B).left.δ (1 : Fin 3) y +
          (standardResolution A B).left.δ (2 : Fin 3) y) =
        (standardResolution A B).hom.app (op ⦋2⦌) y := by
      rw [map_add, map_sub, e₀, e₁, e₂]
      ring
    rw [hy, map_sub, show (standardResolution A B).hom.app (op ⦋1⦌) p = 0 from hpker,
      show (standardResolution A B).hom.app (op ⦋1⦌) v = 0 from hvker, sub_zero] at key
    exact key.symm
  have he₀ := delta_mem_augmentationIdeal A B 1 (0 : Fin 3) y hyker
  have he₁ := delta_mem_augmentationIdeal A B 1 (1 : Fin 3) y hyker
  have he₂ := delta_mem_augmentationIdeal A B 1 (2 : Fin 3) y hyker
  have hvzero : Algebra.Extension.Cotangent.mk
      (P := conormalExtension A B (op ⦋1⦌)) ⟨v, hvker⟩ = 0 :=
    (Algebra.Extension.Cotangent.mk_eq_zero_iff _).2 hvmem
  refine ⟨Algebra.Extension.Cotangent.mk ⟨y, hyker⟩, ?_⟩
  have halt := conormalDelta_alt_mk A B ⟨y, hyker⟩ ⟨_, he₀⟩ ⟨_, he₁⟩ ⟨_, he₂⟩
    ⟨p - v, Ideal.sub_mem _ hpker hvker⟩ rfl rfl rfl hy.symm
  rwa [show (⟨p - v, Ideal.sub_mem _ hpker hvker⟩ :
      (conormalExtension A B (op ⦋1⦌)).ker) = w - ⟨v, hvker⟩ from Subtype.ext rfl,
    map_sub, hvzero, sub_zero] at halt

/-- The Moore complex of the simplicial conormal module is exact in degree one. -/
theorem exactAt_conormalMooreComplex_one :
    (conormalMooreComplex A B).ExactAt 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rw [show (HomologicalComplex.sc' (conormalMooreComplex A B) 2 1 0).g = _ from
    conormalMooreComplex_d_one_zero A B, show (HomologicalComplex.sc' (conormalMooreComplex A B)
    2 1 0).f = _ from conormalMooreComplex_d_two_one A B]
  exact exact_conormalDelta A B

/-- The degree-one homology of the Moore complex of the simplicial conormal module vanishes. -/
theorem isZero_conormalMooreComplex_homology_one :
    IsZero ((conormalMooreComplex A B).homology 1) :=
  (HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (exactAt_conormalMooreComplex_one A B)

/-! ### The conormal complex lies in `D^{≤ -2}(B)` -/

/-- The conormal complex has no cohomology in degree `0`. -/
theorem isZero_conormalComplex_homology_zero :
    IsZero ((conormalComplex A B).homology 0) :=
  (isZero_conormalMooreComplex_homology_zero A B).of_iso
    (HomologicalComplex.extendHomologyIso (conormalMooreComplex A B)
      (ComplexShape.embeddingUpIntLE 0) (j := 0) (j' := 0) (by simp))

/-- The conormal complex has no cohomology in degree `-1`. -/
theorem isZero_conormalComplex_homology_negOne :
    IsZero ((conormalComplex A B).homology (-1)) :=
  (isZero_conormalMooreComplex_homology_one A B).of_iso
    (HomologicalComplex.extendHomologyIso (conormalMooreComplex A B)
      (ComplexShape.embeddingUpIntLE 0) (j := 1) (j' := -1) (by simp))

/-- The conormal complex vanishes in positive cohomological degrees. -/
theorem isZero_conormalComplex_X_pos (i : ℤ) (hi : 0 < i) :
    IsZero ((conormalComplex A B).X i) :=
  (conormalMooreComplex A B).isZero_extend_X (ComplexShape.embeddingUpIntLE 0) i
    ((ComplexShape.notMem_range_embeddingUpIntLE_iff (p := 0) i).2 hi)

/-- **The conormal complex is acyclic in degrees `> -2`.** -/
theorem isLE_conormalComplex : (conormalComplex A B).IsLE (-2) := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  rcases lt_trichotomy i 0 with h | h | h
  · obtain rfl : i = -1 := by lia
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_conormalComplex_homology_negOne A B)
  · subst h
    exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2
      (isZero_conormalComplex_homology_zero A B)
  · exact HomologicalComplex.ExactAt.of_isZero (isZero_conormalComplex_X_pos A B i h)

end Stacks.Cotangent

end
