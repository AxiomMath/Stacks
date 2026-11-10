module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCap42.ClosedSubschemeZeroCycle
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.EulerCharacteristicComparison
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.Models.DegreePairingSymmetry
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormula
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaSpecialFiber
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequenceGenericFibre
public import StacksFrontier.AlgebraicGeometry.Curves.Models.GenusFormulaDecomposition
public import StacksFrontier.AlgebraicGeometry.Curves.Models.ReducedFibreFiltration
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFibreRadicalComponents
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.ComparisonNatural
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.GlobalFunctionsConstant
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoefficientScalars
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.ProjectiveLineVanishing
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberIntersectionForm
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurve
import StacksCore.Tactic.StacksAttribute

/-!
# Meeting exceptional components of a regular model

Work in progress.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Models

/-! ### Arithmetic and combinatorial inputs -/

/-- The indicator function of a pair of distinct indices. -/
def indicatorPair {α : Type*} [DecidableEq α] (i j : α) (Z : α) : ℚ :=
  if Z = i then 1 else if Z = j then 1 else 0

/-- The indicator of a pair of distinct indices splits as a sum of two single indicators. -/
theorem indicatorPair_eq_add {α : Type*} [DecidableEq α] {i j : α} (hij : i ≠ j) (Z : α) :
    indicatorPair i j Z = (if Z = i then (1 : ℚ) else 0) + (if Z = j then (1 : ℚ) else 0) := by
  unfold indicatorPair
  by_cases hZi : Z = i
  · subst hZi; simp [hij]
  · by_cases hZj : Z = j <;> simp [hZi, hZj, Ne.symm hij]

/-- **A bilinear form evaluated at the indicator of a pair of distinct indices** is the sum of
the four entries at that pair. -/
theorem sum_sum_indicatorPair {α : Type*} [Fintype α] [DecidableEq α] {i j : α} (hij : i ≠ j)
    (N : α → α → ℚ) :
    ∑ Z, ∑ Y, indicatorPair i j Z * indicatorPair i j Y * N Z Y =
      N i i + N i j + N j i + N j j := by
  classical
  have key : ∀ (p : α) (g : α → ℚ), (∑ Z, (if Z = p then (1 : ℚ) else 0) * g Z) = g p := by
    intro p g; simp
  have inner : ∀ Z : α, (∑ Y, indicatorPair i j Y * N Z Y) = N Z i + N Z j := by
    intro Z
    simp only [indicatorPair_eq_add hij, add_mul, Finset.sum_add_distrib]
    rw [key i (N Z), key j (N Z)]
  have outer : ∀ Z : α, (∑ Y, indicatorPair i j Z * indicatorPair i j Y * N Z Y) =
      indicatorPair i j Z * (N Z i + N Z j) := by
    intro Z
    rw [← inner Z, Finset.mul_sum]
    exact Finset.sum_congr rfl fun Y _ => by ring
  simp only [outer]
  simp only [indicatorPair_eq_add hij, add_mul, Finset.sum_add_distrib]
  rw [key i fun Z => N Z i + N Z j, key j fun Z => N Z i + N Z j]
  ring

/-- **Two distinct indices whose indicator is proportional to a strictly positive weight vector
exhaust the index type, and the two weights agree.** -/
theorem forall_eq_or_eq_and_weight_eq_of_indicatorPair_eq_smul
    {α : Type*} [DecidableEq α] {i j : α} (hij : i ≠ j) (m : α → ℕ) (hm : ∀ Z, 0 < m Z)
    (hnull : ∃ q : ℚ, ∀ Z, indicatorPair i j Z = q * (m Z : ℚ)) :
    (∀ Z, Z = i ∨ Z = j) ∧ m i = m j := by
  obtain ⟨q, hq⟩ := hnull
  have hiq : (1 : ℚ) = q * (m i : ℚ) := by
    simpa [indicatorPair] using hq i
  have hjq : (1 : ℚ) = q * (m j : ℚ) := by
    simpa [indicatorPair, hij.symm] using hq j
  have hqne : q ≠ 0 := by
    intro h
    rw [h] at hiq
    simp at hiq
  refine ⟨fun Z => ?_, ?_⟩
  · by_contra hZ
    have hZi : Z ≠ i := fun h => hZ (Or.inl h)
    have hZj : Z ≠ j := fun h => hZ (Or.inr h)
    have hzero : (0 : ℚ) = q * (m Z : ℚ) := by
      simpa [indicatorPair, hZi, hZj] using hq Z
    have hmq : (m Z : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hm Z))
    exact hmq ((mul_eq_zero.mp hzero.symm).resolve_left hqne)
  · have hcast : (m i : ℚ) = (m j : ℚ) := by
      refine mul_left_cancel₀ hqne ?_
      calc q * (m i : ℚ) = 1 := hiq.symm
        _ = q * (m j : ℚ) := hjq
    exact_mod_cast hcast

/-- An index type covered by two distinct elements is equivalent to `Fin 2`. -/
theorem nonempty_fin_two_equiv_of_forall_eq_or_eq {α : Type*} (i j : α) (hij : i ≠ j)
    (hcover : ∀ Z : α, Z = i ∨ Z = j) : Nonempty (Fin 2 ≃ α) := by
  classical
  refine ⟨Equiv.ofBijective (fun n : Fin 2 => if n = 0 then i else j) ⟨?_, ?_⟩⟩
  · intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd (by simpa using hab : i = j) hij
    · exact absurd (by simpa using hab : j = i) hij.symm
    · rfl
  · intro Z
    rcases hcover Z with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩

/-- If two indices with equal multiplicities cover the index type, `univ = {i, j}` and the gcd of
the multiplicities is their common value. -/
private theorem univ_eq_pair_and_gcd_eq {α : Type*} [Fintype α] [DecidableEq α] {i j : α}
    (m : α → ℕ) (hcover : ∀ Z : α, Z = i ∨ Z = j) (hmult : m i = m j) :
    (Finset.univ : Finset α) = {i, j} ∧ Finset.univ.gcd m = m i := by
  have huniv : (Finset.univ : Finset α) = {i, j} :=
    Finset.ext fun Z => ⟨fun _ => by simpa using hcover Z, fun _ => Finset.mem_univ Z⟩
  refine ⟨huniv, ?_⟩
  rw [huniv, Finset.gcd_insert, Finset.gcd_singleton, ← hmult]
  simp

/-! ### The dimension of a space covered by its irreducible components -/

/-- An irreducible closed subset contained in a subspace, viewed as an irreducible closed subset
of that subspace. -/
def restrictIrreducibleCloseds {X : Type*} [TopologicalSpace X] (Z : Set X)
    (Y : IrreducibleCloseds X) (hY : (Y : Set X) ⊆ Z) : IrreducibleCloseds Z where
  carrier := Subtype.val ⁻¹' (Y : Set X)
  isClosed' := Y.isClosed.preimage continuous_subtype_val
  isIrreducible' := by
    let : IrreducibleSpace (Y : Set X) := isIrreducible_iff_irreducibleSpace.mp Y.isIrreducible
    have h := (IrreducibleSpace.isIrreducible_univ (Y : Set X)).image (Set.inclusion hY)
      (continuous_inclusion hY).continuousOn
    convert h using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_univ, true_and, Set.inclusion]
    exact ⟨fun hx => ⟨⟨x.1, hx⟩, Subtype.ext rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

/-- A space all of whose irreducible components have dimension at most one has dimension at most
one: a chain of three irreducible closed subsets would lift to any component containing the
largest of them. -/
theorem topologicalKrullDim_le_one_of_forall_irreducibleComponents {X : Type*}
    [TopologicalSpace X] (h : ∀ Z : irreducibleComponents X, topologicalKrullDim Z.1 ≤ 1) :
    topologicalKrullDim X ≤ 1 := by
  refine Order.krullDim_le_one_iff.mpr fun B => ?_
  by_cases hB : IsMax B
  · exact Or.inr hB
  refine Or.inl ?_
  rw [isMin_iff_forall_not_lt]
  intro A hAB
  obtain ⟨C, hBC⟩ := not_isMax_iff.mp hB
  obtain ⟨Z, hZ, hCZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (C : Set X) C.isIrreducible
  have lift_strict {P Q : IrreducibleCloseds X} (hPQ : P < Q)
      (hP : (P : Set X) ⊆ Z) (hQ : (Q : Set X) ⊆ Z) :
      restrictIrreducibleCloseds Z P hP < restrictIrreducibleCloseds Z Q hQ := by
    have hle : restrictIrreducibleCloseds Z P hP ≤ restrictIrreducibleCloseds Z Q hQ :=
      fun x hx => hPQ.le hx
    refine lt_of_le_not_ge hle fun hQP => hPQ.not_ge fun z hz => ?_
    exact hQP (show (⟨z, hQ hz⟩ : Z) ∈ restrictIrreducibleCloseds Z Q hQ from hz)
  have hab : restrictIrreducibleCloseds Z A (fun x hx => hCZ (hBC.le (hAB.le hx))) <
      restrictIrreducibleCloseds Z B (fun x hx => hCZ (hBC.le hx)) := lift_strict hAB _ _
  have hbc : restrictIrreducibleCloseds Z B (fun x hx => hCZ (hBC.le hx)) <
      restrictIrreducibleCloseds Z C hCZ := lift_strict hBC _ _
  rcases Order.krullDim_le_one_iff.mp (h ⟨Z, hZ⟩) _ with hb | hb
  · exact hab.not_ge (hb hab.le)
  · exact hbc.not_ge (hb hbc.le)

/-! ### Nonemptiness of a scheme-theoretic intersection -/

/-- A closed subscheme whose support contains a point is nonempty. -/
private theorem nonempty_subscheme_of_mem_support {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}
    (hx : x ∈ I.support) : Nonempty I.subscheme := by
  rw [← SetLike.mem_coe, ← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨z, -⟩ := hx
  exact ⟨z⟩

/-- **The scheme-theoretic intersection of two closed subschemes is nonempty exactly when their
supports meet.** The ideal sheaf of the intersection is the supremum, whose support is the
intersection of the two supports. -/
theorem nonempty_sup_subscheme_iff {X : Scheme.{u}} (I J : X.IdealSheafData) :
    Nonempty (I ⊔ J).subscheme ↔ (I.supportSet ∩ J.supportSet).Nonempty := by
  constructor
  · rintro ⟨z⟩
    have hz := (I ⊔ J).mem_supportSet_subschemeι z
    rw [Scheme.IdealSheafData.mem_supportSet_iff_mem_support,
      Scheme.IdealSheafData.support_sup] at hz
    exact ⟨(I ⊔ J).subschemeι z,
      (Scheme.IdealSheafData.mem_supportSet_iff_mem_support).2 hz.1,
      (Scheme.IdealSheafData.mem_supportSet_iff_mem_support).2 hz.2⟩
  · rintro ⟨x, hxI, hxJ⟩
    refine nonempty_subscheme_of_mem_support (x := x) ?_
    rw [Scheme.IdealSheafData.support_sup]
    exact ⟨(Scheme.IdealSheafData.mem_supportSet_iff_mem_support).1 hxI,
      (Scheme.IdealSheafData.mem_supportSet_iff_mem_support).1 hxJ⟩

/-- **If two closed subschemes meet, the inverse image of the second on the first is nonempty.**
A common point of the two supports is the image of a point of the first subscheme, and that point
lies on the inverse image. -/
theorem nonempty_comap_subscheme_of_nonempty_sup {X : Scheme.{u}} (I J : X.IdealSheafData)
    (hmeet : Nonempty (I ⊔ J).subscheme) : Nonempty (J.comap I.subschemeι).subscheme := by
  obtain ⟨x, hxI, hxJ⟩ := (nonempty_sup_subscheme_iff I J).1 hmeet
  have hxr : x ∈ Set.range I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.1 hxI
  obtain ⟨y, rfl⟩ := hxr
  refine nonempty_subscheme_of_mem_support (x := y) ?_
  rw [Scheme.IdealSheafData.support_comap]
  exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.1 hxJ

/-! ### Global sections of a curve and of a divisor on it -/

/-- **The global functions on an integral proper curve inject into those of a nonempty effective
Cartier divisor on it**, so the dimension over the ground field does not decrease. The global
functions on the curve form a field, the restriction map is a `k`-algebra map, and the target is
nontrivial because the divisor is nonempty. -/
theorem finrank_globalSections_le_finrank_globalSections_divisor
    {k : Type u} [Field k] {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim Y ≤ 1)
    (D : Y.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Nonempty D.subscheme] :
    letI : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank k Γ(Y, ⊤) ≤ Module.finrank k Γ(D.subscheme, ⊤) := by
  let : Algebra k Γ(Y, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : Algebra k Γ(D.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
  let : Field Γ(Y, ⊤) := (isField_of_universallyClosed k f).toField
  have hflf := isFiniteLocallyFreeOfRank_divisorSubscheme k f hdim D
  let : IsAffineHom (D.subschemeι ≫ f) := hflf.toIsAffineHom
  let : IsFinite (D.subschemeι ≫ f) :=
    IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have hfinite : (((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom).Finite :=
    (D.subschemeι ≫ f).finite_appTop.comp
      (RingHom.Finite.of_surjective (Scheme.ΓSpecIso (.of k)).inv.hom
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  let : Module.Finite k Γ(D.subscheme, ⊤) := hfinite
  let r : Γ(Y, ⊤) →ₐ[k] Γ(D.subscheme, ⊤) :=
    { __ := D.subschemeι.appTop.hom
      commutes' := fun a => by
        change D.subschemeι.appTop.hom (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a) =
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom a
        rw [Scheme.Hom.comp_appTop]
        rfl }
  let : Nonempty (⊤ : D.subscheme.Opens) :=
    ⟨⟨Classical.choice ‹Nonempty D.subscheme›, trivial⟩⟩
  let : Nontrivial Γ(D.subscheme, ⊤) := D.subscheme.component_nontrivial ⊤
  exact r.toLinearMap.finrank_le_finrank_of_injective r.toRingHom.injective

/-! ### The cohomology of `𝒪(-1)` on the projective line -/

attribute [local instance] MvPolynomial.gradedAlgebra

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **`𝒪(-1)` on the projective line has no cohomology in any degree.** Serre's computation of
the cohomology of the twists of projective space, [Stacks, Tag 01XT], gives `H⁰ = 0` because the
twist is negative, `H¹ = 0` because `-1 ≥ -1` leaves no monomial with all exponents negative and
total degree `-1`, and `Hᑫ = 0` for `q ≥ 2` by dimension. -/
theorem isZero_cohomologyOverField_twistingSheaf_neg_one (k : Type u) [Field k] (q : ℕ) :
    IsZero (cohomologyOverField k (projToSpecCoeff k 1)
      (ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1)) q) := by
  have hz : IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology k 1 (-1) q) := by
    rcases eq_or_ne q 1 with rfl | hq1
    · exact Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_one_of_neg_one_le k le_rfl
    rcases Nat.lt_or_ge q 2 with hlt | hge
    · have hq0 : q = 0 := by omega
      subst hq0
      exact Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_zero_of_neg k
        (by norm_num)
    · exact Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_of_two_le k (-1) hge
  exact hz.of_iso
    (Stacks.ProjectiveSpace.Cohomology.cohomologyOverFieldIsoRestrictScalarsCoeffScalar k 1 _ q)

/-- **The restriction `𝒪_X(E)|_E` of the invertible module of an exceptional curve of the first
kind has no cohomology.** It is the normal sheaf of `E` in `X`, which pulls back along the
projective-line presentation to `𝒪(-1)`, and `𝒪(-1)` on `𝐏¹` has no cohomology. -/
theorem isZero_cohomologyOverField_pullback_invertibleSheaf_of_isExceptionalCurveOfFirstKind
    {X : Scheme.{u}} (D : X.IdealSheafData) (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ D.subscheme}
    (hE : D.IsExceptionalCurveOfFirstKind k e)
    {κ : Type u} [Field κ] (g : D.subscheme ⟶ Spec (.of κ)) (q : ℕ) :
    IsZero (cohomologyOverField κ g
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' D)) q) := by
  have := hE.isEffectiveCartierDivisor
  obtain ⟨t⟩ := hE.nonempty_normalSheafIso
  have hn : Stacks.Divisors.normalSheaf D.subschemeι ≅
      (Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' D) :=
    Stacks.Divisors.normalSheafIsoInvertibleSheaf D
  have hiso : (Scheme.Modules.pullback e.hom).obj
      ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' D)) ≅
      ProjectiveSpectrum.Proj.twistingSheaf
        (MvPolynomial.homogeneousSubmodule (Fin 2) k) (-1) :=
    (Scheme.Modules.pullback e.hom).mapIso hn.symm ≪≫ t
  have hup : IsZero (Hgroup (projectiveLineProj k).ringCatSheaf ⊤ q
      ((Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback D.subschemeι).obj (Stacks.Divisors.invertibleSheaf' D)))) := by
    refine IsZero.of_iso ?_ ((Hfunctor
      (projectiveLineProj k).ringCatSheaf ⊤ q).mapIso hiso)
    exact (isZero_cohomologyOverField_iff_isZero_hgroup k
      (Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff k 1) _ q).1
      (isZero_cohomologyOverField_twistingSheaf_neg_one k q)
  exact (isZero_cohomologyOverField_iff_isZero_hgroup κ g _ q).2
    ((Stacks.Cohomology.SchemeIso.isZero_Hgroup_pullback_iff e _ q).1 hup)

/-! ### The degree of an invertible module with no cohomology -/

/-- **An invertible module with no cohomology has degree `-dim_k Γ(X, 𝒪_X) + g_X`.** The degree
of [Stacks, Tag 0AYR] is `χ(ℒ) - χ(𝒪_X)`; the first term vanishes by hypothesis, and the second
is `dim_k Γ(X, 𝒪_X) - g_X`. -/
theorem invertibleCurveDegree_eq_neg_finrank_globalSections_add_genus (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : ∀ q, Module.finrank k (cohomologyOverField k f L q) = 0) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
    invertibleCurveDegree k f hdim L =
      -(Module.finrank k Γ(X, ⊤) : ℤ) + (genus f : ℤ) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  let : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  have h2 : (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      (Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) n) : ℤ)) =
      (Module.finrank k Γ(X, ⊤) : ℤ) - (genus f : ℤ) := by
    rw [← eulerCharacteristic_eq_finsum k f (SheafOfModules.unit X.ringCatSheaf)]
    exact eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus k f hdim
  unfold invertibleCurveDegree
  rw [h2]
  simp only [hL, Nat.cast_zero, mul_zero, finsum_zero, zero_sub, neg_sub]
  ring

/-! ### Rigidity of the graded projective line -/

open Stacks.ProjectiveCohomology (projModelMap projModelToSpec projModelMap_comp
  projModelMap_comp_projModelToSpec projToSpecCoeff_eq_projModelToSpec polyGradedMap_id
  polyGradedMap Proj_map_congr) in
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **Rigidity of the graded projective line.** An isomorphism `ψ : k ≅ κ` of the coefficient
fields induces an isomorphism of the projective lines carrying the structure morphism of
`𝐏¹_κ`, read over `k` through `ψ`, to the structure morphism of `𝐏¹_k`.

The isomorphism is `Proj` of the coefficientwise map on polynomials, which is functorial and
identity at the identity, and the compatibility is the naturality of the structure morphism in
the coefficients. -/
theorem exists_iso_projectiveLineProj_of_isIso {k κ : Type u} [Field k] [Field κ]
    (ψ : CommRingCat.of k ⟶ CommRingCat.of κ) [IsIso ψ] :
    ∃ e : projectiveLineProj k ≅ projectiveLineProj κ,
      e.hom ≫ projToSpecCoeff κ 1 ≫ Spec.map ψ = projToSpecCoeff k 1 := by
  have hidk : (inv ψ).hom.comp ψ.hom = RingHom.id k :=
    congrArg CommRingCat.Hom.hom (IsIso.hom_inv_id ψ)
  have hidκ : ψ.hom.comp (inv ψ).hom = RingHom.id κ :=
    congrArg CommRingCat.Hom.hom (IsIso.inv_hom_id ψ)
  have hmapid (R : Type u) [CommRing R] : projModelMap 1 (RingHom.id R) = 𝟙 _ := by
    refine Eq.trans (Proj_map_congr (polyGradedMap (Fin (1 + 1)) (RingHom.id R))
      (GradedRingHom.id _) _ (by simp) (polyGradedMap_id ..)) ?_
    exact AlgebraicGeometry.Proj.map_id
  refine ⟨⟨projModelMap 1 (inv ψ).hom, projModelMap 1 ψ.hom, ?_, ?_⟩, ?_⟩
  · rw [projModelMap_comp, hidk, hmapid]
  · rw [projModelMap_comp, hidκ, hmapid]
  · rw [projToSpecCoeff_eq_projModelToSpec, projToSpecCoeff_eq_projModelToSpec,
      ← Category.assoc, projModelMap_comp_projModelToSpec, Category.assoc, ← Spec.map_comp]
    have hhi : ψ ≫ CommRingCat.ofHom (inv ψ).hom = 𝟙 (CommRingCat.of k) := IsIso.hom_inv_id ψ
    rw [hhi, Spec.map_id, Category.comp_id]

/-! ### A scheme over a field with one-dimensional global functions -/

/-- **If the global functions of a scheme over `k` are one-dimensional over `k`, the structure
map on global functions is an isomorphism.** A one-dimensional `k`-algebra with `1 ≠ 0` is
spanned by `1`, so `k ⟶ Γ(X, 𝒪_X)` is surjective, and it is injective because `k` is a field. -/
theorem isIso_constants_of_finrank_globalSections_eq_one {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Nontrivial Γ(X, ⊤)]
    (h : letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
      Module.finrank k Γ(X, ⊤) = 1) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
  refine (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(algebraMap k Γ(X, ⊤)).injective, fun x => ?_⟩
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one h (one_ne_zero : (1 : Γ(X, ⊤)) ≠ 0) x
  refine ⟨a, ?_⟩
  change (algebraMap k Γ(X, ⊤)) a = x
  simpa only [Algebra.smul_def, mul_one] using ha

/-- **An affine scheme over a field whose global functions are one-dimensional is the spectrum of
that field**, its structure morphism being an isomorphism. -/
theorem isIso_of_isAffine_of_finrank_globalSections_eq_one {k : Type u} [Field k]
    {X : Scheme.{u}} [IsAffine X] (f : X ⟶ Spec (.of k)) [Nontrivial Γ(X, ⊤)]
    (h : letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom.toAlgebra
      Module.finrank k Γ(X, ⊤) = 1) : IsIso f := by
  have := isIso_constants_of_finrank_globalSections_eq_one f h
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  have : IsIso (f ≫ (Spec (.of k)).toSpecΓ) := by
    rw [Scheme.toSpecΓ_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right f (Spec (.of k)).toSpecΓ

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- **The two structure morphisms of a component over the residue field agree**: the closed
immersion of a component into the special fibre is the one the filtration of [Stacks, Tag 0C68]
uses, both being determined by composition with the monomorphism `X_k ⟶ X`. -/
theorem fibreSubschemeToSpec_specialFiberComponentIdeal
    (Z : irreducibleComponents S.specialFiber) :
    S.fibreSubschemeToSpec (S.specialFiberComponentIdeal Z)
        (S.specialFiberIdeal_le_specialFiberComponentIdeal Z) =
      S.specialFiberComponentToSpec Z := by
  have hι : S.fibreSubschemeι (S.specialFiberComponentIdeal Z)
      (S.specialFiberIdeal_le_specialFiberComponentIdeal Z) = S.specialFiberComponentι Z := by
    refine (cancel_mono S.specialFiberι).mp ?_
    rw [S.fibreSubschemeι_comp, S.specialFiberComponentι_specialFiberι]
  change S.fibreSubschemeι _ _ ≫ S.specialFiberToSpec = _
  rw [hι]
  rfl

/-- The Euler characteristic depends on the structure morphism only through its value, the
properness and coherence arguments being propositions. -/
theorem eulerCharacteristic_congr_morphism {X : Scheme.{u}} {k : Type u} [Field k]
    {f g : X ⟶ Spec (.of k)} (hf : IsProper f) (hg : IsProper g)
    (F : X.Modules) (hc : F.IsCoherent) (h : f = g) :
    @eulerCharacteristic k _ X f hf F hc = @eulerCharacteristic k _ X g hg F hc := by
  subst h; rfl

/-- The degree of an invertible module on a closed subscheme depends on the structure morphism
only through its value. -/
theorem componentDegree_congr_morphism {k : Type u} [Field k] {X : Scheme.{u}}
    (D : X.IdealSheafData) {g g' : D.subscheme ⟶ Spec (.of k)}
    (hg : IsProper g) (hg' : IsProper g')
    (hdim hdim' : topologicalKrullDim D.subscheme ≤ 1) (L : X.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property L) (h : g = g') :
    componentDegree k D g hg hdim L hL = componentDegree k D g' hg' hdim' L hL := by
  subst h; rfl

/-- **The Euler characteristic of the structure sheaf of a component is its weight**, once the
component is known to have genus zero: `χ(C_Z, 𝒪) = dim_k Γ(C_Z, 𝒪) - g_{C_Z} = [κ_Z : k]`. -/
theorem fibreEuler_specialFiberComponentIdeal_eq_weight
    (Z : irreducibleComponents S.specialFiber)
    (hgz : genus (S.specialFiberComponentToSpec Z) = 0) :
    fibreEuler S (S.specialFiberComponentIdeal Z)
        (S.specialFiberIdeal_le_specialFiberComponentIdeal Z) =
      (S.specialFiberComponentWeight Z : ℤ) := by
  have h1 := AlgebraicGeometry.eulerCharacteristic_unit_eq_finrank_globalSections_sub_genus
    S.k (S.specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
  rw [hgz, Nat.cast_zero, sub_zero] at h1
  refine Eq.trans ?_ h1
  exact eulerCharacteristic_congr_morphism _ _ _ _
    (S.fibreSubschemeToSpec_specialFiberComponentIdeal Z)

section DecidableComponents

variable [DecidableEq (irreducibleComponents S.specialFiber)]

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **The divisor of one component pulls back to an effective Cartier divisor on another.**
The component `C_W` is the zero scheme of the canonical section of `𝒪_X(C_W)`, the component
`C_Z` is integral, and `C_W` does not contain `C_Z`, so [Stacks, Tag 02OR] applies. -/
theorem isPullbackDefined_specialFiberComponentIdeal
    {Z W : irreducibleComponents S.specialFiber} (h : Z ≠ W) :
    Stacks.Divisors.IsPullbackDefined (S.specialFiberComponentIdeal Z).subschemeι
      (S.specialFiberComponentIdeal W) := by
  have := S.isEffectiveCartierDivisor_specialFiberComponent W
  have hcan : Stacks.Divisors.zeroScheme S.X
      (Stacks.Divisors.modulesInvertibleSheaf (S.specialFiberComponentIdeal W))
      ((Stacks.Divisors.canonicalSections (S.specialFiberComponentIdeal W)).eval (op ⊤)) =
      S.specialFiberComponentIdeal W :=
    Stacks.Divisors.zeroScheme_canonicalSections _
  have hle : ¬ Stacks.Divisors.zeroScheme S.X
      (Stacks.Divisors.modulesInvertibleSheaf (S.specialFiberComponentIdeal W))
      ((Stacks.Divisors.canonicalSections (S.specialFiberComponentIdeal W)).eval (op ⊤)) ≤
      S.specialFiberComponentIdeal Z := by
    rw [hcan]
    intro hcon
    refine S.not_supportSet_specialFiberComponentIdeal_subset h fun x hx => ?_
    exact Scheme.IdealSheafData.mem_supportSet_iff_mem_support.2
      (Scheme.IdealSheafData.support_antitone hcon
        (Scheme.IdealSheafData.mem_supportSet_iff_mem_support.1 hx))
  have hres := Stacks.Divisors.isEffectiveCartierDivisor_comap_zeroScheme_of_isIntegral
    (Stacks.Divisors.modulesInvertibleSheaf (S.specialFiberComponentIdeal W))
    ((Stacks.Divisors.canonicalSections (S.specialFiberComponentIdeal W)).eval (op ⊤))
    (S.specialFiberComponentIdeal Z) inferInstance hle
  rw [hcan] at hres
  exact hres

/-- Abbreviation for the scheme-theoretic intersection of two components, formed on the first. -/
abbrev componentIntersectionIdeal (Z W : irreducibleComponents S.specialFiber) :
    (S.specialFiberComponentIdeal Z).subscheme.IdealSheafData :=
  (S.specialFiberComponentIdeal W).comap (S.specialFiberComponentIdeal Z).subschemeι

/-- **The intersection number of two distinct components is the degree of their intersection**,
`(C_Z · C_W) = dim_k Γ(C_Z ∩ C_W, 𝒪)`. The entry is the degree of `𝒪_X(C_W)` restricted to
`C_Z`, that restriction is `𝒪_{C_Z}(C_Z ∩ C_W)` by [Stacks, Tag 0C4U], and the degree of the
invertible module of an effective Cartier divisor on a proper curve is the dimension of its ring
of global functions by [Stacks, Tag 0AYY]. -/
theorem specialFiberIntersectionMatrix_eq_finrank_globalSections
    {Z W : irreducibleComponents S.specialFiber} (h : Z ≠ W) :
    letI : Stacks.Divisors.IsEffectiveCartierDivisor (S.componentIntersectionIdeal Z W) :=
      S.isPullbackDefined_specialFiberComponentIdeal h
    letI : Algebra S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of S.k)).inv ≫
        ((S.componentIntersectionIdeal Z W).subschemeι ≫
          S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
    S.specialFiberIntersectionMatrix Z W =
      (Module.finrank S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) : ℤ) := by
  have := S.isEffectiveCartierDivisor_specialFiberComponent W
  have := S.isPullbackDefined_specialFiberComponentIdeal h
  let : Algebra S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      ((S.componentIntersectionIdeal Z W).subschemeι ≫
        S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  have : SheafOfModules.IsInvertible (S.specialFiberComponentIdeal Z).subscheme.presheaf
      (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal W))) :=
    isInvertible_restrict (S.specialFiberComponentIdeal Z)
      (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal W))
      (Stacks.Divisors.isTensorInvertible_invertibleSheaf (S.specialFiberComponentIdeal W))
  rw [S.specialFiberIntersectionMatrix_eq_componentDegree Z W]
  simp only [componentDegree]
  rw [invertibleCurveDegree_eq_of_iso S.k (S.specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
    (Stacks.Divisors.invertibleSheafPullbackIso
      (S.specialFiberComponentIdeal Z).subschemeι (S.specialFiberComponentIdeal W))]
  exact invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections S.k
    (S.specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
    (S.componentIntersectionIdeal Z W)

/-- **The weight of a component is at most its intersection number with any other component it
meets**, `[κ_Z : k] ≤ (C_Z · C_W)`. The right-hand side is the dimension of the global functions
on `C_Z ∩ C_W`, which is nonempty, and the global functions on the integral proper curve `C_Z`
inject into them. -/
theorem specialFiberComponentWeight_le_specialFiberIntersectionMatrix
    {Z W : irreducibleComponents S.specialFiber} (h : Z ≠ W)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W).subscheme) :
    (S.specialFiberComponentWeight Z : ℤ) ≤ S.specialFiberIntersectionMatrix Z W := by
  have := S.isEffectiveCartierDivisor_specialFiberComponent W
  have := S.isPullbackDefined_specialFiberComponentIdeal h
  have : Nonempty (S.componentIntersectionIdeal Z W).subscheme :=
    nonempty_comap_subscheme_of_nonempty_sup _ _ hmeet
  rw [S.specialFiberIntersectionMatrix_eq_finrank_globalSections h]
  exact_mod_cast finrank_globalSections_le_finrank_globalSections_divisor
    (S.specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
    (S.componentIntersectionIdeal Z W)

/-- **The self-intersection of an exceptional component of the first kind.**
`(C_Z · C_Z) = -[κ_Z : k] + g_{C_Z}`: the restriction `𝒪_X(C_Z)|_{C_Z}` is the normal sheaf,
which has no cohomology, so its degree is `-χ(𝒪_{C_Z})`. -/
theorem specialFiberIntersectionMatrix_self_eq_neg_weight_add_genus
    (Z : irreducibleComponents S.specialFiber) (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ (S.specialFiberComponentIdeal Z).subscheme}
    (hE : (S.specialFiberComponentIdeal Z).IsExceptionalCurveOfFirstKind k e) :
    S.specialFiberIntersectionMatrix Z Z =
      -(S.specialFiberComponentWeight Z : ℤ) +
        (genus (S.specialFiberComponentToSpec Z) : ℤ) := by
  have := S.isEffectiveCartierDivisor_specialFiberComponent Z
  have : SheafOfModules.IsInvertible
      (S.specialFiberComponentIdeal Z).subscheme.presheaf
      (S.specialFiberComponentIdeal Z).subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))) :=
    isInvertible_restrict (S.specialFiberComponentIdeal Z)
      (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))
      (Stacks.Divisors.isTensorInvertible_invertibleSheaf (S.specialFiberComponentIdeal Z))
  have hvan : ∀ q, Module.finrank S.k (cohomologyOverField S.k
      (S.specialFiberComponentToSpec Z)
      ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
        (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))) q) = 0 := by
    intro q
    have : Subsingleton (cohomologyOverField S.k (S.specialFiberComponentToSpec Z)
        ((Scheme.Modules.pullback (S.specialFiberComponentIdeal Z).subschemeι).obj
          (Stacks.Divisors.invertibleSheaf' (S.specialFiberComponentIdeal Z))) q) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_cohomologyOverField_pullback_invertibleSheaf_of_isExceptionalCurveOfFirstKind
          (S.specialFiberComponentIdeal Z) k hE (S.specialFiberComponentToSpec Z) q)
    exact Module.finrank_zero_of_subsingleton
  rw [S.specialFiberIntersectionMatrix_eq_componentDegree Z Z]
  simp only [componentDegree]
  exact invertibleCurveDegree_eq_neg_finrank_globalSections_add_genus S.k
    (S.specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z) _ hvan

/-- **The self-intersection of an exceptional component is at least `-[κ_Z : k]`**, the genus
being nonnegative. -/
theorem neg_weight_le_specialFiberIntersectionMatrix_self
    (Z : irreducibleComponents S.specialFiber) (k : Type u) [Field k]
    {e : projectiveLineProj k ≅ (S.specialFiberComponentIdeal Z).subscheme}
    (hE : (S.specialFiberComponentIdeal Z).IsExceptionalCurveOfFirstKind k e) :
    -(S.specialFiberComponentWeight Z : ℤ) ≤ S.specialFiberIntersectionMatrix Z Z := by
  rw [S.specialFiberIntersectionMatrix_self_eq_neg_weight_add_genus Z k hE]
  exact le_add_of_nonneg_right (Int.natCast_nonneg _)

/-- **The numerical reduction at the heart of [Stacks, Tag 0C6A].** For two distinct exceptional
components of the first kind that meet, every one of the estimates entering the intersection form
is an equality: the self-intersections are exactly `-[κ : k]`, the two weights agree, and the
cross term is that common weight.

The intersection form is negative semidefinite, [Stacks, Tag 0C66] part (4). On the indicator of
`{i, j}` its value is `(C_i · C_i) + 2(C_i · C_j) + (C_j · C_j)`, and the estimates
`(C_i · C_i) ≥ -[κ_i : k]`, `[κ_i : k] ≤ (C_i · C_j)` with their counterparts for `j` make that
value nonnegative. So it vanishes and all four estimates are tight. The last conclusion is the
equality case of part (4): the indicator is proportional to the multiplicity vector. -/
theorem specialFiberIntersectionMatrix_eq_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    S.specialFiberIntersectionMatrix i i = -(S.specialFiberComponentWeight i : ℤ) ∧
      S.specialFiberIntersectionMatrix j j = -(S.specialFiberComponentWeight j : ℤ) ∧
      S.specialFiberIntersectionMatrix i j = (S.specialFiberComponentWeight i : ℤ) ∧
      S.specialFiberComponentWeight i = S.specialFiberComponentWeight j ∧
      (∃ q : ℚ, ∀ Z, indicatorPair i j Z = q * (S.specialFiberMultiplicity Z : ℚ)) := by
  have hli := S.neg_weight_le_specialFiberIntersectionMatrix_self i κi hi
  have hlj := S.neg_weight_le_specialFiberIntersectionMatrix_self j κj hj
  have hbi := S.specialFiberComponentWeight_le_specialFiberIntersectionMatrix hij hmeet
  have hbj := S.specialFiberComponentWeight_le_specialFiberIntersectionMatrix hij.symm
    (by rw [sup_comm]; exact hmeet)
  rw [S.specialFiberIntersectionMatrix_comm j i] at hbj
  obtain ⟨hnonpos, hzeroiff⟩ :=
    S.specialFiberIntersectionForm_nonpos_and_eq_zero_iff (indicatorPair i j)
  rw [sum_sum_indicatorPair hij fun Z Y => (S.specialFiberIntersectionMatrix Z Y : ℚ),
    S.specialFiberIntersectionMatrix_comm j i] at hnonpos hzeroiff
  have hnonpos' : S.specialFiberIntersectionMatrix i i +
      S.specialFiberIntersectionMatrix i j + S.specialFiberIntersectionMatrix i j +
      S.specialFiberIntersectionMatrix j j ≤ 0 := by exact_mod_cast hnonpos
  have hzeroInt : S.specialFiberIntersectionMatrix i i +
      S.specialFiberIntersectionMatrix i j + S.specialFiberIntersectionMatrix i j +
      S.specialFiberIntersectionMatrix j j = 0 := by omega
  have hzero : (S.specialFiberIntersectionMatrix i i : ℚ) +
      (S.specialFiberIntersectionMatrix i j : ℚ) +
      (S.specialFiberIntersectionMatrix i j : ℚ) +
      (S.specialFiberIntersectionMatrix j j : ℚ) = 0 := by exact_mod_cast hzeroInt
  have hwcast : (S.specialFiberComponentWeight i : ℤ) = S.specialFiberComponentWeight j := by
    omega
  exact ⟨by omega, by omega, by omega, by exact_mod_cast hwcast, hzeroiff.1 hzero⟩

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- The special fibre is contained in the scheme-theoretic intersection of two of its
components. -/
theorem specialFiberIdeal_le_sup_specialFiberComponentIdeal
    (Z W : irreducibleComponents S.specialFiber) :
    S.specialFiberIdeal ≤
      S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W :=
  (S.specialFiberIdeal_le_specialFiberComponentIdeal Z).trans le_sup_left

omit [DecidableEq (irreducibleComponents S.specialFiber)] in
/-- **The two presentations of the scheme-theoretic intersection of two components carry the same
structure morphism over the residue field.** Both factor through the closed immersion of the
special fibre, which is a monomorphism. -/
theorem comp_fibreSubschemeToSpec_sup
    {Z W : irreducibleComponents S.specialFiber}
    (e : (S.componentIntersectionIdeal Z W).subscheme ≅
      (S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W).subscheme)
    (he : e.hom ≫ (S.specialFiberComponentIdeal Z ⊔
          S.specialFiberComponentIdeal W).subschemeι =
      (S.componentIntersectionIdeal Z W).subschemeι ≫
        (S.specialFiberComponentIdeal Z).subschemeι) :
    e.hom ≫ S.fibreSubschemeToSpec
        (S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W)
        (S.specialFiberIdeal_le_sup_specialFiberComponentIdeal Z W) =
      (S.componentIntersectionIdeal Z W).subschemeι ≫ S.specialFiberComponentToSpec Z := by
  have hmono : e.hom ≫ S.fibreSubschemeι
        (S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W)
        (S.specialFiberIdeal_le_sup_specialFiberComponentIdeal Z W) =
      (S.componentIntersectionIdeal Z W).subschemeι ≫ S.specialFiberComponentι Z := by
    refine (cancel_mono S.specialFiberι).mp ?_
    rw [Category.assoc, Category.assoc, S.fibreSubschemeι_comp,
      S.specialFiberComponentι_specialFiberι]
    exact he
  change e.hom ≫ S.fibreSubschemeι _ _ ≫ S.specialFiberToSpec = _
  rw [← Category.assoc, hmono, Category.assoc]
  rfl

/-- **The intersection of two distinct components with intersection number one is a rational
point of the residue field.** The intersection is finite locally free over `k` of rank
`(C_Z · C_W) = 1`, hence affine with one-dimensional global functions, so its structure morphism
over `k` is an isomorphism. -/
theorem isIso_fibreSubschemeToSpec_sup_of_specialFiberIntersectionMatrix_eq_one
    {Z W : irreducibleComponents S.specialFiber} (h : Z ≠ W)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W).subscheme)
    (hM : S.specialFiberIntersectionMatrix Z W = 1) :
    IsIso (S.fibreSubschemeToSpec
      (S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W)
      (S.specialFiberIdeal_le_sup_specialFiberComponentIdeal Z W)) := by
  have := S.isEffectiveCartierDivisor_specialFiberComponent W
  have := S.isPullbackDefined_specialFiberComponentIdeal h
  have hne : Nonempty (S.componentIntersectionIdeal Z W).subscheme :=
    nonempty_comap_subscheme_of_nonempty_sup _ _ hmeet
  let : Algebra S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      ((S.componentIntersectionIdeal Z W).subschemeι ≫
        S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  have hfr : Module.finrank S.k Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) = 1 := by
    have hid := S.specialFiberIntersectionMatrix_eq_finrank_globalSections h
    rw [hM] at hid
    exact_mod_cast hid.symm
  have hflf := isFiniteLocallyFreeOfRank_divisorSubscheme S.k
    (S.specialFiberComponentToSpec Z)
    (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
    (S.componentIntersectionIdeal Z W)
  let : IsAffineHom ((S.componentIntersectionIdeal Z W).subschemeι ≫
    S.specialFiberComponentToSpec Z) := hflf.toIsAffineHom
  let : IsAffine (S.componentIntersectionIdeal Z W).subscheme :=
    isAffine_of_isAffineHom ((S.componentIntersectionIdeal Z W).subschemeι ≫
      S.specialFiberComponentToSpec Z)
  let : Nonempty (⊤ : (S.componentIntersectionIdeal Z W).subscheme.Opens) :=
    ⟨⟨Classical.choice hne, trivial⟩⟩
  let : Nontrivial Γ((S.componentIntersectionIdeal Z W).subscheme, ⊤) :=
    (S.componentIntersectionIdeal Z W).subscheme.component_nontrivial ⊤
  have hiso : IsIso ((S.componentIntersectionIdeal Z W).subschemeι ≫
      S.specialFiberComponentToSpec Z) :=
    isIso_of_isAffine_of_finrank_globalSections_eq_one _ hfr
  obtain ⟨e, he⟩ := Stacks.ChernCap42.exists_iso_comap_sup
    (S.specialFiberComponentIdeal Z) (S.specialFiberComponentIdeal W)
    (S.specialFiberComponentIdeal Z).subschemeι (Iso.refl _) (by simp)
  have : IsIso (e.hom ≫ S.fibreSubschemeToSpec
      (S.specialFiberComponentIdeal Z ⊔ S.specialFiberComponentIdeal W)
      (S.specialFiberIdeal_le_sup_specialFiberComponentIdeal Z W)) := by
    rw [S.comp_fibreSubschemeToSpec_sup e he]
    exact hiso
  exact IsIso.of_isIso_comp_left e.hom _

end DecidableComponents

/-- **Two meeting exceptional components exhaust the special fibre and have equal
multiplicities.** The equality case of the negative semidefiniteness of the intersection form
says the indicator of `{i, j}` is proportional to the multiplicity vector; since every
multiplicity is positive, there is no third component and the two multiplicities agree. -/
theorem forall_eq_or_eq_and_multiplicity_eq_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    (∀ Z : irreducibleComponents S.specialFiber, Z = i ∨ Z = j) ∧
      S.specialFiberMultiplicity i = S.specialFiberMultiplicity j := by
  classical
  exact forall_eq_or_eq_and_weight_eq_of_indicatorPair_eq_smul hij S.specialFiberMultiplicity
    S.specialFiberMultiplicity_pos
    (S.specialFiberIntersectionMatrix_eq_of_isExceptionalCurveOfFirstKind hij hi hj hmeet).2.2.2.2

/-- **Two meeting exceptional components have equal weights and genus zero.** Tightness of the
self-intersection estimate `(C_Z · C_Z) = -[κ_Z : k] + g_{C_Z} ≥ -[κ_Z : k]` forces the genus
term to vanish. -/
theorem weight_eq_and_genus_eq_zero_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    S.specialFiberComponentWeight i = S.specialFiberComponentWeight j ∧
      genus (S.specialFiberComponentToSpec i) = 0 ∧
      genus (S.specialFiberComponentToSpec j) = 0 := by
  classical
  obtain ⟨hii, hjj, -, hw, -⟩ :=
    S.specialFiberIntersectionMatrix_eq_of_isExceptionalCurveOfFirstKind hij hi hj hmeet
  rw [S.specialFiberIntersectionMatrix_self_eq_neg_weight_add_genus i κi hi] at hii
  rw [S.specialFiberIntersectionMatrix_self_eq_neg_weight_add_genus j κj hj] at hjj
  exact ⟨hw, by omega, by omega⟩


open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **A component whose field of constants is the residue field is the projective line over the
residue field.** The component is already a projective line over its own field of constants `κ`;
since `𝐏¹_κ` has no nonconstant global functions, the structure morphism over `k` factors
through `Spec κ` by a ring map, which `[κ : k] = 1` makes an isomorphism, and rigidity of the
graded projective line transports the presentation along it. -/
theorem exists_iso_projectiveLineProj_specialFiberComponentIdeal_of_weight_eq_one
    (Z : irreducibleComponents S.specialFiber) (κ : Type u) [Field κ]
    (e : projectiveLineProj κ ≅ (S.specialFiberComponentIdeal Z).subscheme)
    (hw : S.specialFiberComponentWeight Z = 1) :
    ∃ e' : projectiveLineProj S.k ≅ (S.specialFiberComponentIdeal Z).subscheme,
      e'.hom ≫ S.specialFiberComponentToSpec Z = projToSpecCoeff S.k 1 := by
  let : Algebra S.k Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of S.k)).inv ≫
      (S.specialFiberComponentToSpec Z).appTop).hom.toAlgebra
  obtain ⟨hfield, -⟩ := S.isField_and_finite_globalSections_specialFiberComponent Z
  let : Field Γ((S.specialFiberComponentIdeal Z).subscheme, ⊤) := hfield.toField
  have hcon := isIso_constants_of_finrank_globalSections_eq_one
    (S.specialFiberComponentToSpec Z) hw
  have hetop : IsIso e.hom.appTop :=
    ⟨e.inv.appTop, by rw [← Scheme.Hom.comp_appTop, e.inv_hom_id]; simp,
      by rw [← Scheme.Hom.comp_appTop, e.hom_inv_id]; simp⟩
  set u := e.hom ≫ S.specialFiberComponentToSpec Z with hu
  have hp : IsIso ((Scheme.ΓSpecIso (.of κ)).inv ≫ (projToSpecCoeff κ 1).appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).2
      (Stacks.ProjectiveSpace.Cohomology.bijective_coeffToGlobalSections κ 1)
  obtain ⟨ψ, hψ⟩ :=
    exists_comp_eq_of_isIso_ΓSpecIso_inv_comp_appTop (projToSpecCoeff κ 1) hp u
  have huiso : IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ u.appTop) := by
    rw [hu, Scheme.Hom.comp_appTop, ← Category.assoc]
    infer_instance
  have hψiso : IsIso ψ := by
    have hfac : (Scheme.ΓSpecIso (.of S.k)).inv ≫ u.appTop =
        ψ ≫ (Scheme.ΓSpecIso (.of κ)).inv ≫ (projToSpecCoeff κ 1).appTop := by
      have hnat : (Scheme.ΓSpecIso (.of S.k)).inv ≫ (Spec.map ψ).appTop =
          ψ ≫ (Scheme.ΓSpecIso (.of κ)).inv := (Scheme.ΓSpecIso_inv_naturality ψ).symm
      rw [hψ, Scheme.Hom.comp_appTop, ← Category.assoc, hnat, Category.assoc]
    rw [hfac] at huiso
    exact IsIso.of_isIso_comp_right ψ
      ((Scheme.ΓSpecIso (.of κ)).inv ≫ (projToSpecCoeff κ 1).appTop)
  obtain ⟨e₀, he₀⟩ := exists_iso_projectiveLineProj_of_isIso ψ
  refine ⟨e₀ ≪≫ e, ?_⟩
  rw [Iso.trans_hom, Category.assoc, ← hu, hψ]
  exact he₀

/-- **The reduced multiple fibre of two meeting exceptional components is their sum.** The two
multiplicities are equal, so the greatest common divisor is their common value and every exponent
`m_Z / d` is one. -/
theorem reducedSpecialFibre_eq_mul_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal S.specialFiberMultiplicity =
      S.specialFiberComponentIdeal i * S.specialFiberComponentIdeal j := by
  classical
  obtain ⟨hcover, hmult⟩ :=
    S.forall_eq_or_eq_and_multiplicity_eq_of_isExceptionalCurveOfFirstKind hij hi hj hmeet
  obtain ⟨huniv, hgcd⟩ := univ_eq_pair_and_gcd_eq S.specialFiberMultiplicity hcover hmult
  have hexp : ∀ Z : irreducibleComponents S.specialFiber,
      S.specialFiberMultiplicity Z / Finset.univ.gcd S.specialFiberMultiplicity = 1 := by
    intro Z
    rw [hgcd]
    rcases hcover Z with rfl | rfl
    · exact Nat.div_self (S.specialFiberMultiplicity_pos Z)
    · rw [← hmult]
      exact Nat.div_self (S.specialFiberMultiplicity_pos i)
  calc reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal S.specialFiberMultiplicity
      = ∏ Z : irreducibleComponents S.specialFiber, S.specialFiberComponentIdeal Z :=
        Finset.prod_congr rfl fun Z _ => by rw [hexp Z, pow_one]
    _ = S.specialFiberComponentIdeal i * S.specialFiberComponentIdeal j := by
        rw [huniv, Finset.prod_insert (by simpa using hij), Finset.prod_singleton]

/-- **`χ(D, 𝒪_D) = [κ_i : k]` for the reduced multiple fibre of two meeting exceptional
components.** The reduced multiple fibre is `D = C_i + C_j`, and the sequence
`0 ⟶ 𝒪_X(-C_i)|_{C_j} ⟶ 𝒪_D ⟶ 𝒪_{C_i} ⟶ 0` of [Stacks, Tag 0C4T] gives
`χ(𝒪_D) = χ(𝒪_X(-C_i)|_{C_j}) + χ(𝒪_{C_i})`. The first term is
`-(C_j · C_i) + χ(𝒪_{C_j}) = -[κ_i : k] + [κ_j : k] = 0` and the second is `[κ_i : k]`. -/
theorem fibreEuler_reducedSpecialFibre_eq_weight_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    fibreEuler S (reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
        S.specialFiberMultiplicity)
        (specialFiberIdeal_le_reducedSpecialFibre S Finset.univ S.specialFiberComponentIdeal
          S.specialFiberMultiplicity S.specialFiberIdeal_eq_prod) =
      (S.specialFiberComponentWeight i : ℤ) := by
  classical
  set Ci := S.specialFiberComponentIdeal i with hCidef
  set Cj := S.specialFiberComponentIdeal j with hCjdef
  set Dred := reducedSpecialFibre Finset.univ S.specialFiberComponentIdeal
    S.specialFiberMultiplicity with hDreddef
  obtain ⟨hw, hgi, hgj⟩ :=
    S.weight_eq_and_genus_eq_zero_of_isExceptionalCurveOfFirstKind hij hi hj hmeet
  obtain ⟨-, -, hcross, -, -⟩ :=
    S.specialFiberIntersectionMatrix_eq_of_isExceptionalCurveOfFirstKind hij hi hj hmeet
  have hsum : Dred = Ci * Cj :=
    S.reducedSpecialFibre_eq_mul_of_isExceptionalCurveOfFirstKind hij hi hj hmeet
  have hECi : Stacks.Divisors.IsEffectiveCartierDivisor Ci :=
    S.isEffectiveCartierDivisor_specialFiberComponent i
  have hsub : Dred ≤ Ci := hsum ▸ Scheme.IdealSheafData.mul_le_left _ _
  have hleCi := S.specialFiberIdeal_le_specialFiberComponentIdeal i
  have hleCj := S.specialFiberIdeal_le_specialFiberComponentIdeal j
  have hleD := specialFiberIdeal_le_reducedSpecialFibre S Finset.univ
    S.specialFiberComponentIdeal S.specialFiberMultiplicity S.specialFiberIdeal_eq_prod
  obtain ⟨f, hz, hex⟩ := Stacks.Divisors.addEffectiveCartierDivisor_shortExact
    Ci Dred Cj hECi hsub hsum
  have : IsLocallyNoetherian Cj.subscheme :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field
      S.k (S.specialFiberComponentToSpec j)
  have hinv : AlgebraicGeometry.SheafOfModules.IsInvertible Cj.subscheme.presheaf
      Cj.subscheme.ringCatSheaf.2
      ((Scheme.Modules.pullback Cj.subschemeι).obj (Stacks.Divisors.negativeTwist Ci)) :=
    isInvertible_restrict Cj (Stacks.Divisors.negativeTwist' Ci)
      (Stacks.Divisors.isTensorInvertible_negativeTwist Ci)
  have hctw : ((Scheme.Modules.pullback Cj.subschemeι).obj
      (Stacks.Divisors.negativeTwist Ci)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank S.k
      (S.specialFiberComponentToSpec j) _ 1
  have key := eulerCharacteristic_add_of_shortExact_pushforward S hleCj hleD hleCi
    (T := ShortComplex.mk f (Scheme.IdealSheafData.closedSubschemeRestriction hsub) hz)
    hex (Iso.refl _) (Iso.refl _) (Iso.refl _) hctw
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
      (S.fibreSubschemeToSpec Dred hleD))
    (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
      (S.fibreSubschemeToSpec Ci hleCi))
  -- the twist contributes zero
  have htwzero : @eulerCharacteristic S.k _ _ (S.fibreSubschemeToSpec Cj hleCj) _
      ((Scheme.Modules.pullback Cj.subschemeι).obj (Stacks.Divisors.negativeTwist Ci))
      hctw = 0 := by
    have hmor := S.fibreSubschemeToSpec_specialFiberComponentIdeal j
    have hdeg := componentDegree_eq_eulerCharacteristic_restrict_sub S.k Cj
      (S.specialFiberComponentToSpec j) (S.isProper_specialFiberComponentToSpec j)
      (S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent j)
      (Stacks.Divisors.negativeTwist' Ci)
      (Stacks.Divisors.isTensorInvertible_negativeTwist Ci) hctw
      (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
        (S.specialFiberComponentToSpec j))
    have hneg := componentDegree_negativeTwist_eq_neg S S.specialFiberComponentIdeal
      (fun Z => S.specialFiberComponentToSpec Z)
      (fun Z => S.isProper_specialFiberComponentToSpec Z)
      (fun Z => S.toRegularModelSituation.topologicalKrullDim_specialFiberComponent Z)
      j Ci hECi
    have hmat := S.specialFiberIntersectionMatrix_eq_componentDegree j i
    have hcj : @eulerCharacteristic S.k _ _ (S.specialFiberComponentToSpec j) _
        (SheafOfModules.unit Cj.subscheme.ringCatSheaf)
        (Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
          (S.specialFiberComponentToSpec j)) = (S.specialFiberComponentWeight j : ℤ) := by
      refine Eq.trans ?_ (S.fibreEuler_specialFiberComponentIdeal_eq_weight j hgj)
      exact eulerCharacteristic_congr_morphism _ _ _ _ hmor.symm
    rw [hneg, ← hmat, hcj] at hdeg
    have hswap : @eulerCharacteristic S.k _ _ (S.fibreSubschemeToSpec Cj hleCj) _
        ((Scheme.Modules.pullback Cj.subschemeι).obj (Stacks.Divisors.negativeTwist Ci)) hctw =
        @eulerCharacteristic S.k _ _ (S.specialFiberComponentToSpec j) _
        ((Scheme.Modules.pullback Cj.subschemeι).obj (Stacks.Divisors.negativeTwist Ci)) hctw :=
      eulerCharacteristic_congr_morphism _ _ _ _ hmor
    rw [S.specialFiberIntersectionMatrix_comm j i, hcross, hw] at hdeg
    have hdeg' : -(S.specialFiberComponentWeight j : ℤ) =
        @eulerCharacteristic S.k _ _ (S.specialFiberComponentToSpec j) _
          ((Scheme.Modules.pullback Cj.subschemeι).obj (Stacks.Divisors.negativeTwist Ci))
          hctw - (S.specialFiberComponentWeight j : ℤ) := hdeg
    rw [hswap]
    omega
  rw [htwzero, zero_add] at key
  refine key.trans ?_
  exact S.fibreEuler_specialFiberComponentIdeal_eq_weight i hgi

/-- **The genus formula of [Stacks, Tag 0C69] at two meeting exceptional components**:
`1 - g_C = d · [κ_i : k]`. Tag 0C69 gives `1 - g_C = d · [κ : k](1 - g_D)` for the reduced
multiple fibre `D`; its two hypotheses are discharged here, the identification of `(X_k)_red`
with `Σ C_Z` by `Stacks.Models.RegularModelSituation.radical_specialFiberIdeal_eq_prod` and the
comparison of the Euler characteristics of the generic and special fibre by
`eulerCharacteristic_unit_eq_eulerCharacteristic_unit_specialFibre`. The remaining factor
`[κ : k](1 - g_D)` is `χ(D, 𝒪_D)`, which is `[κ_i : k]`. -/
theorem one_sub_genus_eq_gcd_mul_weight_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    (1 : ℤ) - (genus S.C_to_K : ℤ) =
      ((Finset.univ.gcd S.specialFiberMultiplicity : ℕ) : ℤ) *
        (S.specialFiberComponentWeight i : ℤ) := by
  classical
  have := isProper_curveToFractionField S
  have : (SheafOfModules.unit S.C.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.K S.C_to_K
  have : (SheafOfModules.unit S.specialFiberIdeal.subscheme.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit S.k
      (S.fibreSubschemeToSpec S.specialFiberIdeal le_rfl)
  obtain ⟨hκ, -, hform⟩ :=
    one_sub_genus_eq_gcd_mul_finrank_mul_one_sub_genus_specialFiberComponents S
  have hchi := fibreEuler_reducedSpecialFibre_eq S Finset.univ S.specialFiberComponentIdeal
    S.specialFiberMultiplicity S.specialFiberIdeal_eq_prod hκ
  have hwt := S.fibreEuler_reducedSpecialFibre_eq_weight_of_isExceptionalCurveOfFirstKind
    hij hi hj hmeet
  rw [mul_assoc, ← hchi, hwt] at hform
  exact hform

/-! ### The numerical consequences of the genus formula

The genus formula of [Stacks, Tag 0C69] reads `1 - g_C = d · [κ_i : k]` here, by
`one_sub_genus_eq_gcd_mul_weight_of_isExceptionalCurveOfFirstKind` above. Both factors on the right
are at least one and the genus is nonnegative, so the product is exactly one: that is what pins
the multiplicities, the weights and the genus simultaneously. -/

/-- **The multiplicities, the weights and the genus are all pinned by the genus formula.** With
the cover established, the greatest common divisor of the multiplicities is their common value
`m`, so the genus formula reads `1 - g = m · [κ_i : k]`. Both factors on the right are at least
one and the genus is nonnegative, so the product is exactly one and the genus is zero. -/
theorem multiplicity_and_weight_eq_one_and_genus_eq_zero_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    S.specialFiberMultiplicity i = 1 ∧ S.specialFiberMultiplicity j = 1 ∧
      S.specialFiberComponentWeight i = 1 ∧ S.specialFiberComponentWeight j = 1 ∧
      genus S.C_to_K = 0 := by
  classical
  have hgenus := S.one_sub_genus_eq_gcd_mul_weight_of_isExceptionalCurveOfFirstKind
    hij hi hj hmeet
  obtain ⟨hcover, hmult⟩ :=
    S.forall_eq_or_eq_and_multiplicity_eq_of_isExceptionalCurveOfFirstKind hij hi hj hmeet
  obtain ⟨hw, -, -⟩ :=
    S.weight_eq_and_genus_eq_zero_of_isExceptionalCurveOfFirstKind hij hi hj hmeet
  obtain ⟨huniv, hgcd⟩ := univ_eq_pair_and_gcd_eq S.specialFiberMultiplicity hcover hmult
  rw [hgcd] at hgenus
  have hmpos : (1 : ℤ) ≤ (S.specialFiberMultiplicity i : ℤ) := by
    exact_mod_cast S.specialFiberMultiplicity_pos i
  have hwpos : (1 : ℤ) ≤ (S.specialFiberComponentWeight i : ℤ) := by
    exact_mod_cast S.specialFiberComponentWeight_pos i
  have hge : (1 : ℤ) ≤ (S.specialFiberMultiplicity i : ℤ) *
      (S.specialFiberComponentWeight i : ℤ) := by nlinarith
  have hg0 : genus S.C_to_K = 0 := by
    have h3 : (0 : ℤ) ≤ (genus S.C_to_K : ℤ) := Int.natCast_nonneg _
    have : (genus S.C_to_K : ℤ) = 0 := by omega
    exact_mod_cast this
  have hprodInt : (S.specialFiberMultiplicity i : ℤ) *
      (S.specialFiberComponentWeight i : ℤ) = 1 := by
    rw [hg0] at hgenus
    omega
  have hprod : S.specialFiberMultiplicity i * S.specialFiberComponentWeight i = 1 := by
    exact_mod_cast hprodInt
  have hm1 : S.specialFiberMultiplicity i = 1 := Nat.dvd_one.mp ⟨_, hprod.symm⟩
  have hw1 : S.specialFiberComponentWeight i = 1 :=
    Nat.dvd_one.mp ⟨_, by rw [Nat.mul_comm]; exact hprod.symm⟩
  exact ⟨hm1, hmult ▸ hm1, hw1, hw ▸ hw1, hg0⟩

/-- **Stacks Project, Tag 0C6A: `m₁ = m₂ = 1`.** Every irreducible component of the special
fibre occurs in `X_k` with multiplicity one. -/
@[stacks 0C6A "m_1 = m_2 = 1, every component of the special fibre has multiplicity one"]
theorem specialFiberMultiplicity_eq_one_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    ∀ Z : irreducibleComponents S.specialFiber, S.specialFiberMultiplicity Z = 1 := by
  classical
  obtain ⟨hcover, -⟩ :=
    S.forall_eq_or_eq_and_multiplicity_eq_of_isExceptionalCurveOfFirstKind hij hi hj hmeet
  obtain ⟨hmi, hmj, -, -, -⟩ :=
    S.multiplicity_and_weight_eq_one_and_genus_eq_zero_of_isExceptionalCurveOfFirstKind
      hij hi hj hmeet
  intro Z
  rcases hcover Z with rfl | rfl
  · exact hmi
  · exact hmj

/-- **Stacks Project, Tag 0C6A: the generic curve has genus zero.** -/
@[stacks 0C6A "C has genus 0, the generic fibre of the model has genus zero"]
theorem genus_eq_zero_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    genus S.C_to_K = 0 :=
  (S.multiplicity_and_weight_eq_one_and_genus_eq_zero_of_isExceptionalCurveOfFirstKind
    hij hi hj hmeet).2.2.2.2

/-- **Stacks Project, Tag 0C6A: the two components meet in a `k`-rational point.** The
scheme-theoretic intersection `C_i ∩ C_j`, as a closed subscheme of the model, carries a
structure morphism over the residue field compatible with the model morphism, and that morphism
is an isomorphism — so the intersection is a single rational point of `k`. -/
@[stacks 0C6A "C_1 and C_2 meet in a k-rational point"]
theorem exists_section_fibreSubschemeToSpec_sup_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    ∃ f : (S.specialFiberComponentIdeal i ⊔
        S.specialFiberComponentIdeal j).subscheme ⟶ Spec (.of S.k),
      (f ≫ Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) =
        (S.specialFiberComponentIdeal i ⊔
          S.specialFiberComponentIdeal j).subschemeι ≫ S.X_to_R) ∧
      ∃ e : Spec (.of S.k) ≅ (S.specialFiberComponentIdeal i ⊔
        S.specialFiberComponentIdeal j).subscheme, e.hom ≫ f = 𝟙 (Spec (.of S.k)) := by
  classical
  obtain ⟨-, -, hwi, -, -⟩ :=
    S.multiplicity_and_weight_eq_one_and_genus_eq_zero_of_isExceptionalCurveOfFirstKind
      hij hi hj hmeet
  have hM : S.specialFiberIntersectionMatrix i j = 1 := by
    rw [(S.specialFiberIntersectionMatrix_eq_of_isExceptionalCurveOfFirstKind
      hij hi hj hmeet).2.2.1, hwi]
    norm_num
  have := S.isIso_fibreSubschemeToSpec_sup_of_specialFiberIntersectionMatrix_eq_one
    hij hmeet hM
  refine ⟨S.fibreSubschemeToSpec _ (S.specialFiberIdeal_le_sup_specialFiberComponentIdeal i j),
    S.fibreSubschemeToSpec_comp _ _, ?_⟩
  exact ⟨(asIso (S.fibreSubschemeToSpec _
    (S.specialFiberIdeal_le_sup_specialFiberComponentIdeal i j))).symm, by simp⟩

open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff) in
/-- **Stacks Project, Tag 0C6A: `C₁ ≅ 𝐏¹_k` and `C₂ ≅ 𝐏¹_k`.** Each irreducible component of
the special fibre is the projective line over the residue field, compatibly with the structure
morphism of the model: the component carries a morphism to `Spec k` lying over `Spec R`, and an
isomorphism with `𝐏¹_k` carrying that morphism to the structure morphism of `𝐏¹_k`.

The projective line is the graded model `Proj k[T₀, T₁]`. -/
@[stacks 0C6A "C_1 and C_2 are isomorphic to the projective line over the residue field"]
theorem exists_iso_projectiveLineProj_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    ∀ Z : irreducibleComponents S.specialFiber,
      ∃ f : (S.specialFiberComponentIdeal Z).subscheme ⟶ Spec (.of S.k),
        (f ≫ Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)) =
          (S.specialFiberComponentIdeal Z).subschemeι ≫ S.X_to_R) ∧
        ∃ e : projectiveLineProj S.k ≅ (S.specialFiberComponentIdeal Z).subscheme,
          e.hom ≫ f = projToSpecCoeff S.k 1 := by
  classical
  obtain ⟨hcover, -⟩ :=
    S.forall_eq_or_eq_and_multiplicity_eq_of_isExceptionalCurveOfFirstKind hij hi hj hmeet
  obtain ⟨-, -, hwi, hwj, -⟩ :=
    S.multiplicity_and_weight_eq_one_and_genus_eq_zero_of_isExceptionalCurveOfFirstKind
      hij hi hj hmeet
  intro Z
  rcases hcover Z with rfl | rfl
  · exact ⟨S.specialFiberComponentToSpec Z, S.specialFiberComponentToSpec_comp Z,
      S.exists_iso_projectiveLineProj_specialFiberComponentIdeal_of_weight_eq_one Z κi ei hwi⟩
  · exact ⟨S.specialFiberComponentToSpec Z, S.specialFiberComponentToSpec_comp Z,
      S.exists_iso_projectiveLineProj_specialFiberComponentIdeal_of_weight_eq_one Z κj ej hwj⟩

/-! ### Tag 0C6A -/

/-- **Stacks Project, Tag 0C6A: `n = 2`.** In Situation [Stacks, Tag 0C61], if two distinct
irreducible components `C_i` and `C_j` of the special fibre are exceptional curves of the first
kind and meet, then the special fibre has exactly two irreducible components.

The components are indexed by `irreducibleComponents S.specialFiber` itself, so the assertion
`n = 2` is an equivalence of that index type with `Fin 2`; no ordering of the components is
chosen. -/
@[stacks 0C6A "n = 2, the special fibre has exactly two irreducible components"]
theorem nonempty_fin_two_equiv_irreducibleComponents_of_isExceptionalCurveOfFirstKind
    {i j : irreducibleComponents S.specialFiber} (hij : i ≠ j)
    {κi κj : Type u} [Field κi] [Field κj]
    {ei : projectiveLineProj κi ≅ (S.specialFiberComponentIdeal i).subscheme}
    {ej : projectiveLineProj κj ≅ (S.specialFiberComponentIdeal j).subscheme}
    (hi : (S.specialFiberComponentIdeal i).IsExceptionalCurveOfFirstKind κi ei)
    (hj : (S.specialFiberComponentIdeal j).IsExceptionalCurveOfFirstKind κj ej)
    (hmeet : Nonempty
      (S.specialFiberComponentIdeal i ⊔ S.specialFiberComponentIdeal j).subscheme) :
    Nonempty (Fin 2 ≃ irreducibleComponents S.specialFiber) :=
  nonempty_fin_two_equiv_of_forall_eq_or_eq i j hij
    (S.forall_eq_or_eq_and_multiplicity_eq_of_isExceptionalCurveOfFirstKind hij hi hj hmeet).1

end RegularProperModelSituation

end Stacks.Models

end
