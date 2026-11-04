module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyDevissage

/-!
# Collapse of hypercohomology along the brutal filtration

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings and let `L` be a complex
of `𝒪_X`-modules concentrated in degrees `0, …, N`. The brutal truncations `σ^{≥p}L` filter `L`,
with graded pieces the terms `Lᵖ[-p]`, and the short exact sequences

`0 ⟶ σ^{≥p+1}L ⟶ σ^{≥p}L ⟶ Lᵖ[-p] ⟶ 0`

give long exact sequences of hypercohomology. Suppose that `Hᵏ(X, Lᵖ[-p]) = 0` unless `k = 2p`;
for the de Rham complex this says that `H^q(X, Ωᵖ) = 0` unless `p = q`. Then the spectral
sequence of the filtered complex degenerates on its first page and in every degree a single
graded piece survives.

## Main definitions

* `Stacks.Cech.Hypercohomology.truncPlusMap`: the comparison `σ^{≥b}L ⟶ σ^{≥a}L` for `a ≤ b`.
* `Stacks.Cech.Hypercohomology.ιTruncPlus`: the inclusion `σ^{≥i}K ⟶ K` of bounded below
  complexes.

## Main results

* `Stacks.Cech.Hypercohomology.isZero_hypercohomology_truncPlus_of_forall_ne`: `Hᵏ(X, σ^{≥p}L)`
  vanishes unless `k = 2i` for some `p ≤ i ≤ N`.
* `Stacks.Cech.Hypercohomology.bijective_hypercohomologyMap_ιTruncPlus`: for `i ≥ 0` the
  inclusion `σ^{≥i}K ⟶ K` is bijective on `H^{2i}`.
* `Stacks.Cech.Hypercohomology.bijective_hypercohomologyMap_truncSC_g_two_mul`: the projection
  `σ^{≥i}L ⟶ Lⁱ[-i]` is bijective on `H^{2i}`.
* `Stacks.Cech.Hypercohomology.isZero_hypercohomology_of_forall_ne`: `Hᵏ(X, K)` vanishes unless
  `k = 2i` with `0 ≤ i ≤ N`.

## References

* [Stacks Project, Section 0FM6](https://stacks.math.columbia.edu/tag/0FM6)
* [Stacks Project, Section 0118](https://stacks.math.columbia.edu/tag/0118)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.RightDerivedBoundary
open Stacks.SheafOfModules.Tensor (ringSheaf)
open StacksDraft.StupidTruncation

universe u

namespace Stacks.Cech.Hypercohomology

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-! ### Zero complexes -/

/-- **A bounded below complex all of whose terms vanish has no hypercohomology.** -/
theorem isZero_hypercohomology_of_isZero_X
    (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (hK : ∀ q, IsZero (K.obj.X q))
    (n : ℤ) : IsZero (hypercohomology O K n) :=
  isZero_hypercohomology_of_homotopy O K
    (Homotopy.ofEq (HomologicalComplex.hom_ext _ _ fun q => (hK q).eq_of_src _ _)) n

/-- The hypercohomology of a sheaf placed in degree `p` vanishes below degree `p`. -/
theorem isZero_hypercohomology_singlePlus_of_lt (F : SheafOfModules.{u} (ringSheaf O)) {p n : ℤ}
    (h : n < p) : IsZero (hypercohomology O (singlePlus O F p) n) :=
  isZero_hypercohomology O _ p n h

/-- A zero sheaf placed in any degree has no hypercohomology. -/
theorem isZero_hypercohomology_singlePlus_of_isZero {F : SheafOfModules.{u} (ringSheaf O)}
    (hF : IsZero F) (p n : ℤ) : IsZero (hypercohomology O (singlePlus O F p) n) :=
  isZero_hypercohomology_of_isZero_X O _ (fun q => by
    show IsZero (((HomologicalComplex.single _ (up ℤ) p).obj F).X q)
    by_cases hq : q = p
    · subst hq
      exact hF.of_iso (HomologicalComplex.singleObjXSelf (up ℤ) q F)
    · exact HomologicalComplex.isZero_single_obj_X (up ℤ) p F q hq) n

/-- The isomorphism induced on hypercohomology by an isomorphism of bounded below complexes. -/
def hypercohomologyMapIso {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (e : K ≅ L) (n : ℤ) : hypercohomology O K n ≅ hypercohomology O L n where
  hom := hypercohomologyMap O e.hom n
  inv := hypercohomologyMap O e.inv n
  hom_inv_id := by rw [← hypercohomologyMap_comp, e.hom_inv_id, hypercohomologyMap_id]
  inv_hom_id := by rw [← hypercohomologyMap_comp, e.inv_hom_id, hypercohomologyMap_id]

variable (L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ)

/-- The brutal truncation `σ^{≥p}L` has zero terms as soon as `L` vanishes in degrees `≥ p`. -/
theorem isZero_truncPlus_X {p : ℤ} (h : ∀ q, p ≤ q → IsZero (L.X q)) (q : ℤ) :
    IsZero ((truncPlus O L p).obj.X q) := by
  show IsZero ((L.stupidTrunc (embeddingUpIntGE p)).X q)
  by_cases hq : p ≤ q
  · exact (h q hq).of_iso (stupidTruncGEXIso L p q hq)
  · exact CochainComplex.isZero_of_isStrictlyGE (L.stupidTrunc (embeddingUpIntGE p)) p q
      (by omega)

/-! ### The long exact sequence of a brutal truncation -/

/-- A linear map out of a zero module sends every element to zero. -/
private theorem hom_apply_eq_zero_of_isZero {R : Type*} [Ring R] {M N : ModuleCat R}
    (f : M ⟶ N) (h : IsZero M) (a : M) : f.hom a = 0 := by
  rw [(ModuleCat.subsingleton_of_isZero h).elim a 0]
  exact map_zero _

/-- **The step `σ^{≥p+1}L ⟶ σ^{≥p}L` is bijective on `Hᵏ`** as soon as the graded piece
`Lᵖ[-p]` has no hypercohomology in degrees `k - 1` and `k`. -/
theorem bijective_hypercohomologyMap_truncSC_f (p k : ℤ)
    (h₀ : IsZero (hypercohomology O (singlePlus O (L.X p) p) k))
    (h₁ : IsZero (hypercohomology O (singlePlus O (L.X p) p) (k - 1))) :
    Function.Bijective (hypercohomologyMap O (truncSC O L p).f k).hom := by
  have hS := truncSC_shortExact O L p
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [add_sub_cancel_right] at h₁
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun b => ?_⟩
  · obtain ⟨c, rfl⟩ := hypercohomology_exact₁ O (truncSC O L p) hS j a ha
    exact hom_apply_eq_zero_of_isZero _ h₁ c
  · exact hypercohomology_exact₂ O (truncSC O L p) hS (j + 1) b
      ((ModuleCat.subsingleton_of_isZero h₀).elim _ _)

/-- **The projection `σ^{≥p}L ⟶ Lᵖ[-p]` is bijective on `Hᵏ`** as soon as `σ^{≥p+1}L` has no
hypercohomology in degrees `k` and `k + 1`. -/
theorem bijective_hypercohomologyMap_truncSC_g (p k : ℤ)
    (h₀ : IsZero (hypercohomology O (truncPlus O L (p + 1)) k))
    (h₁ : IsZero (hypercohomology O (truncPlus O L (p + 1)) (k + 1))) :
    Function.Bijective (hypercohomologyMap O (truncSC O L p).g k).hom := by
  have hS := truncSC_shortExact O L p
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb => ?_, fun c => ?_⟩
  · obtain ⟨a, rfl⟩ := hypercohomology_exact₂ O (truncSC O L p) hS k b hb
    exact hom_apply_eq_zero_of_isZero _ h₀ a
  · exact exact_boundary O (truncSC O L p) hS k c
      ((ModuleCat.subsingleton_of_isZero h₁).elim _ _)

/-! ### The collapse -/

section Collapse

variable {N : ℤ} (hN : ∀ q, N < q → IsZero (L.X q))
  (hdiag : ∀ p k : ℤ, k ≠ 2 * p → IsZero (hypercohomology O (singlePlus O (L.X p) p) k))

include hN in
/-- Above the top degree the brutal truncation has no hypercohomology. -/
theorem isZero_hypercohomology_truncPlus_of_lt {p : ℤ} (hp : N < p) (k : ℤ) :
    IsZero (hypercohomology O (truncPlus O L p) k) :=
  isZero_hypercohomology_of_isZero_X O _ (isZero_truncPlus_X O L fun q hq => hN q (by omega)) k

include hN hdiag in
/-- **`Hᵏ(X, σ^{≥p}L)` vanishes unless `k = 2i` for some `p ≤ i ≤ N`.** -/
theorem isZero_hypercohomology_truncPlus_of_forall_ne (p k : ℤ)
    (hk : ∀ i : ℤ, p ≤ i → i ≤ N → k ≠ 2 * i) :
    IsZero (hypercohomology O (truncPlus O L p) k) := by
  suffices key : ∀ m : ℕ, ∀ k : ℤ, (∀ i : ℤ, N + 1 - (m : ℤ) ≤ i → i ≤ N → k ≠ 2 * i) →
      IsZero (hypercohomology O (truncPlus O L (N + 1 - (m : ℤ))) k) by
    by_cases hp : N < p
    · exact isZero_hypercohomology_truncPlus_of_lt O L hN hp k
    · have h := key (N + 1 - p).toNat k fun i hi hi' => hk i (by omega) hi'
      rwa [show N + 1 - (((N + 1 - p).toNat : ℕ) : ℤ) = p by omega] at h
  intro m
  induction m with
  | zero =>
    intro k _
    exact isZero_hypercohomology_truncPlus_of_lt O L hN (by omega) k
  | succ m ih =>
    intro k hk
    set p := N + 1 - ((m + 1 : ℕ) : ℤ) with hp
    have e : N + 1 - (m : ℤ) = p + 1 := by omega
    have ih' := ih k fun i hi hi' => hk i (by omega) hi'
    rw [e] at ih'
    have hpk : IsZero (hypercohomology O (singlePlus O (L.X p) p) k) :=
      hdiag p k (hk p le_rfl (by omega))
    rw [ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun b b' => ?_⟩
    have hS := truncSC_shortExact O L p
    have h₀ : ∀ c : hypercohomology O (truncPlus O L p) k, c = 0 := fun c => by
      obtain ⟨a, rfl⟩ := hypercohomology_exact₂ O (truncSC O L p) hS k c
        ((ModuleCat.subsingleton_of_isZero hpk).elim _ _)
      exact hom_apply_eq_zero_of_isZero (hypercohomologyMap O (truncSC O L p).f k) ih' a
    rw [h₀ b, h₀ b']

end Collapse

/-! ### Comparisons between the truncations -/

/-- The comparison `σ^{≥b}L ⟶ σ^{≥a}L` for `a ≤ b`, as a morphism of bounded below complexes. -/
def truncPlusMap {a b : ℤ} (h : a ≤ b) : truncPlus O L b ⟶ truncPlus O L a :=
  ObjectProperty.homMk (stupidTruncGEMapLE L h)

variable {O} in
/-- The projection `σ^{≥a}L ⟶ Lᵃ[-a]` of a brutal truncation onto its bottom term, as a
morphism of bounded below complexes. -/
def truncPlusπ (L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) (a : ℤ) :
    truncPlus O L a ⟶ singlePlus O (L.X a) a :=
  ObjectProperty.homMk (stupidTruncGEπ L a)

variable {O} in
/-- The second map of the short exact sequence of a brutal truncation is its projection onto
the bottom term. -/
theorem truncSC_g (L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) (a : ℤ) :
    (truncSC O L a).g = truncPlusπ L a :=
  rfl

/-- The first map of the short exact sequence of a brutal truncation is a comparison of the
tower. -/
theorem truncSC_f (p : ℤ) : (truncSC O L p).f = truncPlusMap O L (show p ≤ p + 1 by omega) :=
  rfl

/-- The comparisons of the tower compose. -/
theorem stupidTruncGEMapLE_comp {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    stupidTruncGEMapLE L hbc ≫ stupidTruncGEMapLE L hab = stupidTruncGEMapLE L (hab.trans hbc) := by
  have := mono_ιStupidTrunc L (embeddingUpIntGE a)
  apply (cancel_mono (HomologicalComplex.ιStupidTrunc L (embeddingUpIntGE a))).1
  rw [Category.assoc, stupidTruncGEMapLE_ι, stupidTruncGEMapLE_ι, stupidTruncGEMapLE_ι]

/-- The comparison of the tower from a truncation to itself is the identity. -/
theorem stupidTruncGEMapLE_refl (a : ℤ) : stupidTruncGEMapLE L (le_refl a) = 𝟙 _ := by
  have := mono_ιStupidTrunc L (embeddingUpIntGE a)
  apply (cancel_mono (HomologicalComplex.ιStupidTrunc L (embeddingUpIntGE a))).1
  rw [stupidTruncGEMapLE_ι, Category.id_comp]

/-- The comparisons of the tower compose, as morphisms of bounded below complexes. -/
theorem truncPlusMap_comp {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    truncPlusMap O L hbc ≫ truncPlusMap O L hab = truncPlusMap O L (hab.trans hbc) :=
  ObjectProperty.hom_ext _ (stupidTruncGEMapLE_comp O L hab hbc)

/-- The comparison of the tower from a truncation to itself is the identity, as a morphism of
bounded below complexes. -/
theorem truncPlusMap_refl (a : ℤ) : truncPlusMap O L (le_refl a) = 𝟙 _ :=
  ObjectProperty.hom_ext _ (stupidTruncGEMapLE_refl O L a)

section Collapse

variable {N : ℤ} (hN : ∀ q, N < q → IsZero (L.X q))
  (hdiag : ∀ p k : ℤ, k ≠ 2 * p → IsZero (hypercohomology O (singlePlus O (L.X p) p) k))

include hdiag in
/-- **For `j ≤ i` the comparison `σ^{≥i}L ⟶ σ^{≥j}L` is bijective on `H^{2i}`.** -/
theorem bijective_hypercohomologyMap_truncPlusMap_two_mul {j i : ℤ} (hji : j ≤ i) :
    Function.Bijective (hypercohomologyMap O (truncPlusMap O L hji) (2 * i)).hom := by
  suffices key : ∀ m : ℕ, ∀ j : ℤ, i - j = m → ∀ h : j ≤ i,
      Function.Bijective (hypercohomologyMap O (truncPlusMap O L h) (2 * i)).hom from
    key (i - j).toNat j (by omega) hji
  intro m
  induction m with
  | zero =>
    intro j hj h
    obtain rfl : j = i := by omega
    rw [show truncPlusMap O L h = truncPlusMap O L (le_refl j) from rfl, truncPlusMap_refl,
      hypercohomologyMap_id]
    exact Function.bijective_id
  | succ m ih =>
    intro j hj h
    have h₁ : j + 1 ≤ i := by omega
    rw [show truncPlusMap O L h = truncPlusMap O L ((show j ≤ j + 1 by omega).trans h₁) from rfl,
      ← truncPlusMap_comp O L (show j ≤ j + 1 by omega) h₁, hypercohomologyMap_comp,
      ModuleCat.hom_comp, LinearMap.coe_comp]
    refine (bijective_hypercohomologyMap_truncSC_f O L j (2 * i) ?_ ?_).comp
      (ih (j + 1) (by omega) h₁)
    · exact hdiag j (2 * i) (by omega)
    · exact hdiag j (2 * i - 1) (by omega)

include hN in
/-- **The projection `σ^{≥i}L ⟶ Lⁱ[-i]` is bijective on `H^{2i}`.** -/
theorem bijective_hypercohomologyMap_truncSC_g_two_mul
    (hdiag : ∀ p k : ℤ, k ≠ 2 * p → IsZero (hypercohomology O (singlePlus O (L.X p) p) k))
    (i : ℤ) : Function.Bijective (hypercohomologyMap O (truncSC O L i).g (2 * i)).hom :=
  bijective_hypercohomologyMap_truncSC_g O L i (2 * i)
    (isZero_hypercohomology_truncPlus_of_forall_ne O L hN hdiag (i + 1) (2 * i)
      fun i' hi _ => by omega)
    (isZero_hypercohomology_truncPlus_of_forall_ne O L hN hdiag (i + 1) (2 * i + 1)
      fun i' _ _ => by omega)

/-! ### A complex in nonnegative degrees -/

variable (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))

/-- The inclusion `σ^{≥i}K ⟶ K` of bounded below complexes. -/
def ιTruncPlus (i : ℤ) : truncPlus O K.obj i ⟶ K :=
  ObjectProperty.homMk (HomologicalComplex.ιStupidTrunc K.obj (embeddingUpIntGE i))

/-- The inclusion of `σ^{≥i}K` factors through `σ^{≥j}K` for `j ≤ i`. -/
theorem truncPlusMap_ιTruncPlus {j i : ℤ} (h : j ≤ i) :
    truncPlusMap O K.obj h ≫ ιTruncPlus O K j = ιTruncPlus O K i :=
  ObjectProperty.hom_ext _ (stupidTruncGEMapLE_ι K.obj h)

/-- For a complex in nonnegative degrees the inclusion `σ^{≥0}K ⟶ K` is an isomorphism. -/
theorem ιTruncPlus_zero_eq [K.obj.IsStrictlyGE 0] : ιTruncPlus O K 0 = (truncPlusIso O K 0).hom :=
  rfl

end Collapse

section CollapseNonneg

variable (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) [K.obj.IsStrictlyGE 0]
  {N : ℤ} (hN : ∀ q, N < q → IsZero (K.obj.X q))
  (hdiag : ∀ p k : ℤ, k ≠ 2 * p → IsZero (hypercohomology O (singlePlus O (K.obj.X p) p) k))

include hdiag in
/-- **For `i ≥ 0` the inclusion `σ^{≥i}K ⟶ K` is bijective on `H^{2i}`.** -/
theorem bijective_hypercohomologyMap_ιTruncPlus {i : ℤ} (hi : 0 ≤ i) :
    Function.Bijective (hypercohomologyMap O (ιTruncPlus O K i) (2 * i)).hom := by
  rw [← truncPlusMap_ιTruncPlus O K hi, hypercohomologyMap_comp, ModuleCat.hom_comp,
    LinearMap.coe_comp, ιTruncPlus_zero_eq]
  refine Function.Bijective.comp ?_
    (bijective_hypercohomologyMap_truncPlusMap_two_mul O K.obj hdiag hi)
  exact ConcreteCategory.bijective_of_isIso
    (hypercohomologyMapIso O (truncPlusIso O K 0) (2 * i)).hom

include hN hdiag in
/-- **`Hᵏ(X, K)` vanishes unless `k = 2i` with `0 ≤ i ≤ N`.** -/
theorem isZero_hypercohomology_of_forall_ne (k : ℤ)
    (hk : ∀ i : ℤ, 0 ≤ i → i ≤ N → k ≠ 2 * i) : IsZero (hypercohomology O K k) :=
  (isZero_hypercohomology_truncPlus_of_forall_ne O K.obj hN hdiag 0 k hk).of_iso
    (hypercohomologyMapIso O (truncPlusIso O K 0) k).symm

include hN hdiag in
/-- **The collapse identifies `H^{2i}(X, K)` with `H^{2i}(X, Kⁱ[-i])`**, linearly over the global
sections of `𝒪_X`: the inclusion `σ^{≥i}K ⟶ K` and the projection `σ^{≥i}K ⟶ Kⁱ[-i]` are both
bijective on `H^{2i}`. -/
def collapseLinearEquiv {i : ℤ} (hi : 0 ≤ i) :
    hypercohomology O K (2 * i) ≃ₗ[(ringSheaf O).obj.obj (Opposite.op ⊤)]
      hypercohomology O (singlePlus O (K.obj.X i) i) (2 * i) :=
  (LinearEquiv.ofBijective (hypercohomologyMap O (ιTruncPlus O K i) (2 * i)).hom
      (bijective_hypercohomologyMap_ιTruncPlus O K hdiag hi)).symm.trans
    (LinearEquiv.ofBijective (hypercohomologyMap O (truncPlusπ K.obj i) (2 * i)).hom
      (bijective_hypercohomologyMap_truncSC_g_two_mul O K.obj hN hdiag i))

include hN hdiag in
/-- The collapse carries the image of a class of `σ^{≥i}K` to the image of that class in
`H^{2i}(X, Kⁱ[-i])`. -/
theorem collapseLinearEquiv_apply {i : ℤ} (hi : 0 ≤ i)
    (x : hypercohomology O (truncPlus O K.obj i) (2 * i)) :
    collapseLinearEquiv O K hN hdiag hi (hypercohomologyMap O (ιTruncPlus O K i) (2 * i) x) =
      hypercohomologyMap O (truncPlusπ K.obj i) (2 * i) x :=
  congrArg (LinearEquiv.ofBijective (hypercohomologyMap O (truncPlusπ K.obj i) (2 * i)).hom
      (bijective_hypercohomologyMap_truncSC_g_two_mul O K.obj hN hdiag i))
    ((LinearEquiv.ofBijective (hypercohomologyMap O (ιTruncPlus O K i) (2 * i)).hom
      (bijective_hypercohomologyMap_ιTruncPlus O K hdiag hi)).symm_apply_apply x)

end CollapseNonneg

end Stacks.Cech.Hypercohomology

end
