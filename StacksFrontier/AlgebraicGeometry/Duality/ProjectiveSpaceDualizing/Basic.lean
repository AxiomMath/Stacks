module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensChaoticQuasicoherentEquality
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceDualizing.TwistHom
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QcqsRightAdjoint
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.WeakSerre.DerivedComparison

/-!
# The trace map `𝒪(-n-1)[n] ⟶ a(𝒪_S)` on projective space

Let `S` be a quasi-compact scheme, let `n = m + 1 ≥ 1`, let `f : X = ℙⁿ_S ⟶ S` be the structure
morphism and let `a` be the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` of
[Stacks, Tag 0A9E], the library's `Stacks.Duality.twistedInverseImage`. Following the proof of
[Stacks, Tag 0A9W], the isomorphism `Rf_*(𝒪_X(-n-1)[n]) ≅ 𝒪_S`, which holds because `𝒪_X(-n-1)`
has cohomology only in degree `n` where the trace identifies it with `𝒪_S`, determines by
adjunction an arrow

  `c : 𝒪_X(-n-1)[n] ⟶ a(𝒪_S)`.

This file constructs `c` and proves everything the source says about it except the final
appeal to a generator: **for `i ∈ {-n, …, 0}` and every `p`, the functor
`Hom(𝒪_X(i)[p], -)` carries `c` to a bijection.**

* For `i = 0` this holds "by construction of `c`": `Rf_*` is bijective on maps out of `𝒪_X[p]`
  (`Stacks.Duality.ProjectiveSpaceDualizing.bijective_derivedPushforward_map_unit`), and the
  transpose of `s ↦ s ≫ c` is `s ↦ Rf_* s ≫ (Rf_*(𝒪_X(-n-1)[n]) ≅ 𝒪_S)`.
* For `i ∈ {-n, …, -1}` both sides vanish: maps `𝒪_X(i)[p] ⟶ 𝒪_X(-n-1)[n]` vanish
  (`Stacks.Duality.ProjectiveSpaceDualizing.subsingleton_hom_single_twistOver`), and maps
  `𝒪_X(i)[p] ⟶ a(𝒪_S)` are maps `Rf_*(𝒪_X(i)[p]) = 0 ⟶ 𝒪_S`.

No hypothesis on `S` beyond quasi-compactness (which makes `a` exist) is used.

## Main definitions

* `Stacks.Duality.ProjectiveSpaceDualizing.twistDualizing`: `𝒪_X(-n-1)[n]` as an object of
  `D_QCoh(𝒪_X)`.
* `Stacks.Duality.ProjectiveSpaceDualizing.pushforwardTwistDualizingIso`:
  `Rf_*(𝒪_X(-n-1)[n]) ≅ 𝒪_S`.
* `Stacks.Duality.ProjectiveSpaceDualizing.traceDualizing`: the arrow
  `c : 𝒪_X(-n-1)[n] ⟶ a(𝒪_S)` it determines.

## Main results

* `Stacks.Duality.ProjectiveSpaceDualizing.bijective_comp_traceDualizing`: for `0 ≤ k ≤ n` and
  every degree `p`, composition with `c` is a bijection
  `Hom(𝒪_X(-k)[p], 𝒪_X(-n-1)[n]) ≅ Hom(𝒪_X(-k)[p], a(𝒪_S))`.

## Implementation notes

The objects `𝒪_X(i)[p]` are written with the single functors, `𝒪_X(i)` placed in cohomological
degree `-p`; in particular `𝒪_X(-n-1)[n]` is `𝒪_X(-n-1)` placed in degree `-n`.

## References

* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistZeroIsoUnit)

universe u

namespace Stacks.Duality.ProjectiveSpaceDualizing

/-! ### Transposition criteria -/

section Transpose

variable {C D : Type*} [Category C] [Category D] {F : C ⥤ D} {a : D ⥤ C} (adj : F ⊣ a)

/-- Postcomposition with an isomorphism is bijective. -/
theorem bijective_comp_iso_right {A B K : C} (e : A ≅ B) :
    Function.Bijective (fun s : K ⟶ A => s ≫ e.hom) :=
  ⟨fun s t h => by simpa using congrArg (· ≫ e.inv) h,
    fun t => ⟨t ≫ e.inv, by simp⟩⟩

/-- **Composition with a transposed isomorphism.** Let `c : M ⟶ a N` be the transpose of an
isomorphism `F M ⟶ N`. If `F` is bijective on maps `G ⟶ M`, then composition with `c` is
bijective on maps `G ⟶ M`: its transpose is `s ↦ F s ≫ (F M ⟶ N)`. -/
theorem bijective_comp_of_bijective_map {G M : C} {N : D} (c : M ⟶ a.obj N)
    [IsIso ((adj.homEquiv M N).symm c)]
    (hG : Function.Bijective (fun s : G ⟶ M => F.map s)) :
    Function.Bijective (fun s : G ⟶ M => s ≫ c) := by
  have h : (fun s : G ⟶ M => s ≫ c) = adj.homEquiv G N ∘
      (fun t => t ≫ (adj.homEquiv M N).symm c) ∘ (fun s => F.map s) := by
    funext s
    simp only [Function.comp_apply, ← Adjunction.homEquiv_naturality_left_symm,
      Equiv.apply_symm_apply]
  rw [h]
  exact (adj.homEquiv G N).bijective.comp
    ((bijective_comp_iso_right (asIso ((adj.homEquiv M N).symm c))).comp hG)

include adj in
/-- **Composition with any map into `a N` is bijective on maps out of `G` when both sides
vanish**: there is only the zero map `G ⟶ M`, and maps `G ⟶ a N` are maps `F G ⟶ N` out of a zero
object. -/
theorem bijective_comp_of_subsingleton [Preadditive C] [Preadditive D] {G M : C} {N : D}
    (c : M ⟶ a.obj N) [Subsingleton (G ⟶ M)] (hG : IsZero (F.obj G)) :
    Function.Bijective (fun s : G ⟶ M => s ≫ c) :=
  ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, (adj.homEquiv G N).symm.injective
    (hG.eq_of_src _ _)⟩⟩

end Transpose

/-! ### The arrow `c` -/

variable (m : ℕ) (S : Scheme.{u}) [CompactSpace S]

/-- The derived direct image along the structure morphism of `ℙⁿ_S` has a right adjoint on the
quasi-coherent derived categories ([Stacks, Tag 0A9E]). -/
instance isLeftAdjoint_qcqsRestrictedDerivedPushforward_projectiveSpaceOver :
    (quasiCoherentDerivedPushforward (projectiveSpaceOver (m + 1) S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).IsLeftAdjoint :=
  isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward _

/-- A quasi-coherent module placed in any single degree lies in `D_QCoh(𝒪_X)`: it is a shift of
the module placed in degree zero. -/
theorem derivedCategoryB_singleFunctor_obj_of_isQuasicoherent {X : Scheme.{u}} (M : X.Modules)
    (hM : M.IsQuasicoherent) (q : ℤ) :
    DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.singleFunctor X.Modules q).obj M) :=
  (DerivedCategoryB.derivedCategoryB _).prop_of_iso
    (((DerivedCategory.singleFunctors X.Modules).shiftIso (-q) q 0 (by omega)).app M)
    ((DerivedCategoryB.derivedCategoryB _).le_shift (-q) _
      (DerivedPushforward.derivedCategoryB_singleFunctor_obj M hM))

/-- `𝒪_X(d)[p]`, the twist `𝒪_X(d)` placed in cohomological degree `-p`, as an object of
`D_QCoh(𝒪_X)` for `X = ℙⁿ_S`. -/
def twistQCoh (d p : ℤ) : quasiCoherentDerivedCategory (projectiveSpaceOver (m + 1) S) :=
  ⟨(DerivedCategory.singleFunctor _ (-p)).obj (twistOver (m + 1) S d),
    derivedCategoryB_singleFunctor_obj_of_isQuasicoherent _ inferInstance _⟩

/-- **`𝒪_X(-n-1)[n]`** as an object of `D_QCoh(𝒪_X)`, `X = ℙⁿ_S`. -/
abbrev twistDualizing : quasiCoherentDerivedCategory (projectiveSpaceOver (m + 1) S) :=
  twistQCoh m S (-((m + 1 : ℕ) : ℤ) - 1) ((m + 1 : ℕ) : ℤ)

/-- **`Rf_*(𝒪_X(-n-1)[n]) ≅ 𝒪_S`** in `D_QCoh(𝒪_S)`: `𝒪_X(-n-1)` has cohomology only in degree
`n`, where the trace identifies it with `𝒪_S`. -/
def pushforwardTwistDualizingIso :
    (DerivedPushforward.qcqsRestrictedDerivedPushforward (projectiveSpaceOver (m + 1) S ↘ S)).obj
        (twistDualizing m S) ≅ DerivedPushforward.derivedStructureSheaf S :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (derivedPushforwardTwistDualizingIso m S (-((m + 1 : ℕ) : ℤ)) ≪≫
      eqToIso (by rw [show -((m + 1 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ) = 0 by omega]; rfl))

/-- **The arrow `c : 𝒪_X(-n-1)[n] ⟶ a(𝒪_S)`** of the proof of [Stacks, Tag 0A9W]: the transpose,
across `Rf_* ⊣ a`, of the isomorphism `Rf_*(𝒪_X(-n-1)[n]) ≅ 𝒪_S`. -/
def traceDualizing :
    twistDualizing m S ⟶ (twistedInverseImage (projectiveSpaceOver (m + 1) S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
        (DerivedPushforward.derivedStructureSheaf S) :=
  (twistedInverseImageAdjunction _ _).homEquiv _ _ (pushforwardTwistDualizingIso m S).hom

/-- The transpose of `traceDualizing` across `Rf_* ⊣ a`, the map `Rf_*(𝒪_X(-n-1)[n]) ⟶ 𝒪_S`, is
an isomorphism. -/
instance isIso_homEquiv_symm_traceDualizing :
    IsIso (((twistedInverseImageAdjunction (projectiveSpaceOver (m + 1) S ↘ S)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).homEquiv _ _).symm
        (traceDualizing m S)) := by
  rw [traceDualizing, Equiv.symm_apply_apply]
  infer_instance

/-! ### `Hom(𝒪_X(i)[p], -)` carries `c` to a bijection for `-n ≤ i ≤ 0` -/

/-- A full subcategory object with zero underlying object is zero. -/
theorem isZero_of_isZero_obj {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
    {P : ObjectProperty 𝒞} {K : P.FullSubcategory} (h : IsZero K.obj) : IsZero K :=
  (IsZero.iff_id_eq_zero _).2 ((ObjectProperty.fullyFaithfulι P).map_injective
    (h.eq_of_src _ _))

/-- `Rf_*` is bijective on maps `𝒪_X[p] ⟶ K` in `D_QCoh(𝒪_X)`. -/
theorem bijective_qcqsRestrictedDerivedPushforward_map_twistQCoh_zero (p : ℤ)
    (K : quasiCoherentDerivedCategory (projectiveSpaceOver (m + 1) S)) :
    Function.Bijective (fun s : twistQCoh m S 0 p ⟶ K =>
      (DerivedPushforward.qcqsRestrictedDerivedPushforward
        (projectiveSpaceOver (m + 1) S ↘ S)).map s) := by
  set g := projectiveSpaceOver (m + 1) S ↘ S
  set P := DerivedCategoryB.derivedCategoryB (A := (projectiveSpaceOver (m + 1) S).Modules)
    (SheafOfModules.isQuasicoherent (projectiveSpaceOver (m + 1) S).ringCatSheaf)
  set e := (DerivedCategory.singleFunctor (projectiveSpaceOver (m + 1) S).Modules (-p)).mapIso
    (twistZeroIsoUnit (m + 1) S)
  have hD : Function.Bijective (fun s : (twistQCoh m S 0 p).obj ⟶ K.obj =>
      (derivedPushforward g).map s) := by
    have h : (fun s : (twistQCoh m S 0 p).obj ⟶ K.obj => (derivedPushforward g).map s) =
        (fun t => (derivedPushforward g).map e.hom ≫ t) ∘
          (fun t => (derivedPushforward g).map t) ∘ (fun s => e.inv ≫ s) := by
      funext s
      change _ = (derivedPushforward g).map e.hom ≫ (derivedPushforward g).map (e.inv ≫ s)
      rw [← Functor.map_comp]
      exact congrArg (derivedPushforward g).map (e.hom_inv_id_assoc s).symm
    rw [h]
    exact ((bijective_comp_iso ((derivedPushforward g).mapIso e)).comp
      (bijective_derivedPushforward_map_unit m S (-p) K.obj)).comp (bijective_comp_iso e.symm)
  exact (Function.Bijective.of_comp_iff' ((ObjectProperty.fullyFaithfulι _).map_bijective _ _)
    _).1 (hD.comp ((ObjectProperty.fullyFaithfulι P).map_bijective _ _))

/-- **[Stacks, Tag 0A9W], the step before the generator.** For `0 ≤ k ≤ n` and every degree `p`,
composition with `c : 𝒪_X(-n-1)[n] ⟶ a(𝒪_S)` is a bijection
`Hom(𝒪_X(-k)[p], 𝒪_X(-n-1)[n]) ≅ Hom(𝒪_X(-k)[p], a(𝒪_S))`. -/
theorem bijective_comp_traceDualizing (k : ℕ) (hk : k ≤ m + 1) (p : ℤ) :
    Function.Bijective (fun s : twistQCoh m S (-(k : ℤ)) p ⟶ twistDualizing m S =>
      s ≫ traceDualizing m S) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact bijective_comp_of_bijective_map (twistedInverseImageAdjunction _ _) _
      (bijective_qcqsRestrictedDerivedPushforward_map_twistQCoh_zero m S p _)
  · have : Subsingleton (twistQCoh m S (-(k : ℤ)) p ⟶ twistDualizing m S) :=
      ⟨fun s t => (ObjectProperty.fullyFaithfulι _).map_injective
        ((subsingleton_hom_single_twistOver m S (i := -(k : ℤ))
          (j := -((m + 1 : ℕ) : ℤ) - 1) (by omega) (by omega) (-p)
            (-((m + 1 : ℕ) : ℤ))).elim _ _)⟩
    exact bijective_comp_of_subsingleton (twistedInverseImageAdjunction _ _) _
      (isZero_of_isZero_obj (isZero_derivedPushforward_twistOver m S (by omega) (by omega) _))

end Stacks.Duality.ProjectiveSpaceDualizing

end
