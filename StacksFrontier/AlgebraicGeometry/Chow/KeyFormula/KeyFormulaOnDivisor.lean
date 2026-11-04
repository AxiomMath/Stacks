module

public import StacksFrontier.AlgebraicGeometry.Chow.CycleAdditivity
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.SituationKeyFormula
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionNonvanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme

/-!
# The rational equivalence of the key formula is carried by an effective Cartier divisor

Let `X` be integral and locally Noetherian, let `L` and `N` be invertible `𝒪_X`-modules with
nonzero meromorphic sections `s` and `t`, and let `ℱ` be a situation of Stacks 0AYB for them: a
locally finite family `{Z_i}` of prime divisors with chosen generators `s_i` of `L_{ξ_i}` and
`t_i` of `N_{ξ_i}`. The key formula Stacks 0AYC exhibits the cycle

`∑_i (Z_i → X)_* (ord_{B_i}(f_i) div_{N|Z_i}(t_i|Z_i) - ord_{B_i}(g_i) div_{L|Z_i}(s_i|Z_i))`

as the locally finite sum `∑_i (Z_i → X)_* div_{Z_i}(∂_{B_i}(f_i, g_i))` of principal divisors.
Where the chosen generator `s_i` has `s` for its generic value the ratio `f_i` is `1`, so the tame
symbol `∂_{B_i}(1, g_i)` is trivial and the `i`-th principal divisor vanishes. The rational
equivalence to zero is therefore witnessed by the members of the family along which `s` is not the
generic value of a generator.

For `L = 𝒪_X(E)` the invertible sheaf of an effective Cartier divisor and `s = 1_E` its canonical
section, those members are the ones whose generic point lies on `E`: the canonical section
generates `𝒪_X(E)` exactly off `E`, which is
`Stacks.Divisors.nonvanishingLocus_canonicalSections`. So the rational equivalence to zero is
witnessed inside `E`, which is the step of the proof of Stacks 02TM that reads the key formula on
the divisor rather than on `X`.

## Main definitions

* `Stacks.Chow.KeyFormulaSituation.normalizedGeneratorL` — a generator of `L_{ξ_i}` whose generic
  value is the section `s`, where one exists.
* `Stacks.Chow.KeyFormulaSituation.normalizeL` — the situation with those generators.

## Main results

* `Stacks.Chow.KeyFormulaSituation.ratioL_eq_one_iff` — `f_i = 1` exactly when the generic value
  of `s_i` is `s`.
* `Stacks.Chow.KeyFormulaSituation.tameSymbol_eq_one_of_ratioL_eq_one` — `∂_{B_i}(1, g_i) = 1`.
* `Stacks.Chow.KeyFormulaSituation.principalDivisorPushforward_tameSymbol_eq_zero_of_ratioL_eq_one`
  — the `i`-th summand of the right hand side of the key formula vanishes.
* `Stacks.Chow.KeyFormulaSituation.isRationallyEquivalentToZeroWithin_leftCoeff` — the left hand
  side of the key formula is rationally equivalent to zero with witnesses among the members where
  `f_i ≠ 1`.
* `Stacks.Chow.isStalkBasis_germ_top_of_mem_nonvanishingLocus` — a global section of an invertible
  module is a stalk basis at every point of its nonvanishing locus.
* `Stacks.Chow.isCoordinateAt_one_divisorSheafGlobalSection` — off `E` the canonical section of
  `𝒪_X(E)` is the generic value of a generator of the stalk.
* `Stacks.Chow.KeyFormulaSituation.isRationallyEquivalentToZeroWithin_leftCoeff_divisorSheaf` —
  for `𝒪_X(E)` and its canonical section the rational equivalence is witnessed inside `E`.

## References

* [Stacks Project, Tag 0AYB](https://stacks.math.columbia.edu/tag/0AYB)
* [Stacks Project, Tag 0AYC](https://stacks.math.columbia.edu/tag/0AYC)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
* [Stacks Project, Tag 02TM](https://stacks.math.columbia.edu/tag/02TM)
* [Stacks Project, Section 0EAH](https://stacks.math.columbia.edu/tag/0EAH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Order TopologicalSpace


universe u

namespace Stacks.Chow

open Stacks.Divisors

/-! ### Where a global section generates -/

/-- **A global section of an invertible module is a stalk basis at every point of its nonvanishing
locus.** Over a neighbourhood on which the section pairs to the unit section against a section of
a tensor inverse, multiplication by its germ is a bijection onto the stalk. -/
theorem isStalkBasis_germ_top_of_mem_nonvanishingLocus {X : Scheme.{u}} (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (s : L.sections) {x : X}
    (hx : x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) L s) :
    IsStalkBasis L x (L.presheaf.germ ⊤ x trivial (s.eval (op ⊤))) := by
  have hinv : Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ inferInstance
  obtain ⟨M, ⟨ψ⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.toRingedSpace.presheaf)
    (hO := (structureSheafRing X.toRingedSpace).property) L).mp hinv
  obtain ⟨W, hxW, b, hb⟩ := (Stacks.SheafOfModules.mem_nonvanishingLocus_iff ψ s x).mp hx
  have h := Stacks.SheafOfModules.bijective_smul_grpGerm_of_tensorPairing_eq_one hb x hxW
  have hres : L.presheaf.map (homOfLE (le_top (a := W))).op (s.eval (op ⊤)) = s.eval (op W) :=
    PresheafOfModules.sections_property s (homOfLE (le_top (a := W))).op
  have hgerm : L.presheaf.germ W x hxW (s.eval (op W))
      = L.presheaf.germ ⊤ x trivial (s.eval (op ⊤)) := by
    rw [← hres]
    exact L.presheaf.germ_res_apply (homOfLE (le_top (a := W))) x hxW (s.eval (op ⊤))
  change Function.Bijective fun r : X.presheaf.stalk x =>
    r • L.presheaf.germ ⊤ x trivial (s.eval (op ⊤))
  rw [← hgerm]
  exact h

/-- **The canonical section of `𝒪_X(E)` is a coordinate `1` of itself at every point off `E`.**
Away from `E` the canonical section generates `𝒪_X(E)`, by
`Stacks.Divisors.nonvanishingLocus_canonicalSections`, and the generic value of its germ there is
its generic value. -/
theorem isCoordinateAt_one_divisorSheafGlobalSection {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (E : X.IdealSheafData) [IsEffectiveCartierDivisor E] {ξ : X}
    (hξ : ξ ∉ (E.support : Set X)) :
    IsCoordinateAt (divisorSheaf E) ξ
      ((divisorSheaf E).presheaf.germ ⊤ (genericPoint X) trivial
        (divisorSheafGlobalSection E)) 1 := by
  have := isInvertible_presheaf (divisorSheaf E)
  have hmem : ξ ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace)
      (invertibleSheaf E) (canonicalSections E) := by
    rw [nonvanishingLocus_canonicalSections E]
    exact hξ
  refine ⟨(divisorSheaf E).presheaf.germ ⊤ ξ trivial (divisorSheafGlobalSection E),
    isStalkBasis_germ_top_of_mem_nonvanishingLocus (divisorSheaf E) (canonicalSections E) hmem,
    ?_⟩
  rw [one_smul]
  exact (toGenericStalk_germ (Opens.mem_top ξ) (Opens.mem_top (genericPoint X))
    (divisorSheafGlobalSection E)).symm

namespace KeyFormulaSituation

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {L N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
  (ℱ : KeyFormulaSituation L N)

/-! ### The members along which the section is the chosen generator -/

omit [IsLocallyNoetherian X] in
/-- **`f_i = 1` exactly when the generic value of the chosen generator `s_i` is the section
`s`.** -/
theorem ratioL_eq_one_iff (i : ℱ.Index) :
    ℱ.ratioL i = 1 ↔
      toGenericStalk L (ℱ.componentPoint i) (ℱ.localGeneratorL i) = ℱ.sectionL := by
  have := isInvertible_presheaf L
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h1 := ℱ.ratioL_smul_localGeneratorL i
    rwa [h, one_smul] at h1
  · refine ((ℱ.isStalkBasis_localGeneratorL i).toGenericStalk
      (isTrivializedNear_of_isInvertible L (ℱ.componentPoint i))).injective ?_
    change ℱ.ratioL i • _ = (1 : X.functionField) • _
    rw [one_smul, ℱ.ratioL_smul_localGeneratorL i, h]

/-- **`∂_{B_i}(1, g_i) = 1`.** The tame symbol is trivial in its first argument, Stacks 0EAJ
together with Stacks 0EAI. -/
theorem tameSymbol_eq_one_of_ratioL_eq_one {i : ℱ.Index} (h : ℱ.ratioL i = 1) :
    ℱ.tameSymbol i = 1 := by
  have h1 : Units.mk0 (ℱ.ratioL i) (ℱ.ratioL_ne_zero i) = 1 := Units.val_eq_one.mp h
  change tameSymbolAtCoheightOne (ℱ.coheight_componentPoint i)
      (Units.mk0 (ℱ.ratioL i) (ℱ.ratioL_ne_zero i))
      (Units.mk0 (ℱ.ratioN i) (ℱ.ratioN_ne_zero i)) = 1
  rw [h1]
  exact TameSymbol.one_left _ _

/-! ### Normalizing the chosen generator of `L` -/

omit [IsLocallyNoetherian X] in
/-- **A generator of `L_{ξ_i}` whose generic value is the section `s` exists exactly where `1` is
a coordinate of `s` at `ξ_i`**, and elsewhere the generator of the situation serves. -/
theorem exists_isStalkBasis_toGenericStalk_eq_sectionL (i : ℱ.Index) :
    ∃ m : L.presheaf.stalk (ℱ.componentPoint i), IsStalkBasis L (ℱ.componentPoint i) m ∧
      (IsCoordinateAt L (ℱ.componentPoint i) ℱ.sectionL 1 →
        toGenericStalk L (ℱ.componentPoint i) m = ℱ.sectionL) := by
  by_cases h : IsCoordinateAt L (ℱ.componentPoint i) ℱ.sectionL 1
  · refine ⟨h.choose, h.choose_spec.1, fun _ ↦ ?_⟩
    have h2 := h.choose_spec.2
    rw [one_smul] at h2
    exact h2.symm
  · exact ⟨ℱ.localGeneratorL i, ℱ.isStalkBasis_localGeneratorL i, fun hc ↦ absurd hc h⟩

/-- **A generator of `L_{ξ_i}` whose generic value is the section `s`, where one exists.** Such a
generator exists exactly when `1` is a coordinate of `s` at `ξ_i`; elsewhere the generator of the
situation is kept. -/
def normalizedGeneratorL (i : ℱ.Index) : L.presheaf.stalk (ℱ.componentPoint i) :=
  (ℱ.exists_isStalkBasis_toGenericStalk_eq_sectionL i).choose

omit [IsLocallyNoetherian X] in
/-- The normalized generator `normalizedGeneratorL i` is a generator of the stalk `L_{ξ_i}`. -/
theorem isStalkBasis_normalizedGeneratorL (i : ℱ.Index) :
    IsStalkBasis L (ℱ.componentPoint i) (ℱ.normalizedGeneratorL i) :=
  (ℱ.exists_isStalkBasis_toGenericStalk_eq_sectionL i).choose_spec.1

omit [IsLocallyNoetherian X] in
/-- Where `1` is a coordinate of `s` at `ξ_i`, the generic value of the normalized generator is
the section. -/
theorem toGenericStalk_normalizedGeneratorL (i : ℱ.Index)
    (h : IsCoordinateAt L (ℱ.componentPoint i) ℱ.sectionL 1) :
    toGenericStalk L (ℱ.componentPoint i) (ℱ.normalizedGeneratorL i) = ℱ.sectionL :=
  (ℱ.exists_isStalkBasis_toGenericStalk_eq_sectionL i).choose_spec.2 h

/-- **The situation with the generator of `L` at each member normalized.** Every other datum is
that of the given situation: the two sections, the family and the generators of `N` are unchanged,
so the orders of vanishing of `t` and the divisors `div_{N|Z_i}(t_i|Z_i)` are too. -/
def normalizeL : KeyFormulaSituation L N :=
  { ℱ with
    localGeneratorL := ℱ.normalizedGeneratorL
    isStalkBasis_localGeneratorL := ℱ.isStalkBasis_normalizedGeneratorL }

omit [IsLocallyNoetherian X] in
/-- The normalized situation has the same section of `L`. -/
@[simp]
theorem normalizeL_sectionL : ℱ.normalizeL.sectionL = ℱ.sectionL := rfl

omit [IsLocallyNoetherian X] in
/-- The normalized situation has the same section of `N`. -/
@[simp]
theorem normalizeL_sectionN : ℱ.normalizeL.sectionN = ℱ.sectionN := rfl

omit [IsLocallyNoetherian X] in
/-- The normalized situation has the same members `Z_i`. -/
@[simp]
theorem normalizeL_component (i : ℱ.Index) : ℱ.normalizeL.component i = ℱ.component i := rfl

omit [IsLocallyNoetherian X] in
/-- The generator of `L` at `ξ_i` in the normalized situation is the normalized generator. -/
@[simp]
theorem normalizeL_localGeneratorL (i : ℱ.Index) :
    ℱ.normalizeL.localGeneratorL i = ℱ.normalizedGeneratorL i := rfl

omit [IsLocallyNoetherian X] in
/-- The normalized situation has the same generator of `N` at each `ξ_i`. -/
@[simp]
theorem normalizeL_localGeneratorN (i : ℱ.Index) :
    ℱ.normalizeL.localGeneratorN i = ℱ.localGeneratorN i := rfl

omit [IsLocallyNoetherian X] in
/-- **For the normalized situation `f_i = 1` wherever `1` is a coordinate of `s` at `ξ_i`.** -/
theorem normalizeL_ratioL_eq_one (i : ℱ.Index)
    (h : IsCoordinateAt L (ℱ.componentPoint i) ℱ.sectionL 1) :
    ℱ.normalizeL.ratioL i = 1 :=
  (ℱ.normalizeL.ratioL_eq_one_iff i).mpr (ℱ.toGenericStalk_normalizedGeneratorL i h)

/-! ### The rational equivalence of the key formula and its carrier -/

section Cycles

variable (C : ChowSituation.{u}) (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- The tame symbol of the cycle-level data is trivial where `f_i = 1`. -/
theorem toKeyFormulaData_tameSymbol_eq_one_of_ratioL_eq_one {i : ℱ.Index}
    (h : ℱ.ratioL i = 1) : (ℱ.toKeyFormulaData C p).tameSymbol i = 1 := by
  rw [ℱ.toKeyFormulaData_tameSymbol C p i, ℱ.tameSymbol_eq_one_of_ratioL_eq_one h, map_one]
  rfl

/-- **The `i`-th summand of the right hand side of the key formula vanishes where `f_i = 1`**:
the principal divisor of the constant rational function `1` is the zero cycle. -/
theorem principalDivisorPushforward_tameSymbol_eq_zero_of_ratioL_eq_one {i : ℱ.Index}
    (h : ℱ.ratioL i = 1) :
    principalDivisorPushforward C p ((ℱ.toKeyFormulaData C p).component i)
        ((ℱ.toKeyFormulaData C p).isIntegral_component i)
        ((ℱ.toKeyFormulaData C p).tameSymbol i) = 0 := by
  rw [ℱ.toKeyFormulaData_tameSymbol_eq_one_of_ratioL_eq_one C p h]
  exact principalDivisorPushforward_one C p _ _

/-- **The right hand side of the key formula is carried by the members where `f_i ≠ 1`.** -/
theorem tameSymbolCoeff_eq_finsum_subtype (P : ℱ.Index → Prop)
    (hP : ∀ i, ¬ P i → ℱ.ratioL i = 1) (x : X) :
    (ℱ.toKeyFormulaData C p).tameSymbolCoeff C p x =
      ∑ᶠ j : {i : ℱ.Index // P i},
        principalDivisorPushforward C p ((ℱ.toKeyFormulaData C p).component j.1)
          ((ℱ.toKeyFormulaData C p).isIntegral_component j.1)
          ((ℱ.toKeyFormulaData C p).tameSymbol j.1) x := by
  refine finsum_eq_finsum_subtype _ fun i hi ↦ ?_
  rw [ℱ.principalDivisorPushforward_tameSymbol_eq_zero_of_ratioL_eq_one C p (hP i hi)]
  rfl

/-- **The left hand side of the key formula is rationally equivalent to zero on the members where
`f_i ≠ 1`.** Stacks 0AYC presents it as the locally finite sum of the principal divisors
`div_{Z_i}(∂_{B_i}(f_i, g_i))`, and the members where the generic value of the chosen generator
`s_i` is the section `s` contribute nothing. So the witnessing family of Stacks 02RW can be taken
inside the union of the remaining members. -/
theorem isRationallyEquivalentToZeroWithin_leftCoeff {k : ℤ} (P : ℱ.Index → Prop)
    (hP : ∀ i, ¬ P i → ℱ.ratioL i = 1)
    (hdim : ∀ i : ℱ.Index,
      schemeDeltaDimension C (((ℱ.toKeyFormulaData C p).component i).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt))
    (α : CycleGroup C p k)
    (hα : ∀ x : X, α.1 x = (ℱ.toKeyFormulaData C p).leftCoeff C p x) :
    IsRationallyEquivalentToZeroWithin C p k α
      (⋃ j : {i : ℱ.Index // P i},
        (((ℱ.toKeyFormulaData C p).component j.1).support : Set X)) := by
  have hlocal : LocallyFinite fun j : {i : ℱ.Index // P i} ↦
      (((ℱ.toKeyFormulaData C p).component j.1).support : Set X) :=
    (ℱ.toKeyFormulaData C p).locallyFinite_support_component.comp_injective
      Subtype.val_injective
  refine ⟨{i : ℱ.Index // P i}, fun j ↦ (ℱ.toKeyFormulaData C p).component j.1,
    fun j ↦ (ℱ.toKeyFormulaData C p).isIntegral_component j.1, fun j ↦ hdim j.1, hlocal,
    fun j ↦ Set.subset_iUnion_of_subset j subset_rfl,
    fun j ↦ (ℱ.toKeyFormulaData C p).tameSymbol j.1, fun x ↦ ?_⟩
  rw [hα x, ((ℱ.toKeyFormulaData C p).keyFormula_iff_forall C p).1
    (ℱ.keyFormula_toKeyFormulaData C p) x]
  exact ℱ.tameSymbolCoeff_eq_finsum_subtype C p P hP x

end Cycles

end KeyFormulaSituation

/-! ### The carrier for the invertible sheaf of an effective Cartier divisor -/

section Divisor

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]
  [IsIntegral X] [IsLocallyNoetherian X] (E : X.IdealSheafData)
  [IsEffectiveCartierDivisor E] {N : X.Modules}
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]

/-- **The rational equivalence of the key formula for `𝒪_X(E)` and its canonical section is
witnessed inside `E`.** The canonical section `1_E` generates `𝒪_X(E)` at every point off `E`, so
for the situation whose generators of `𝒪_X(E)` are normalized the ratio `f_i` is `1` at every
member `Z_i` whose generic point is not on `E`, and the corresponding tame symbols drop out of the
key formula. The surviving members are contained in `E`, their supports being the closures of
their generic points.

This is the step of the proof of Stacks 02TM that reads the rational equivalence of Stacks 0AYC on
the divisor rather than on `X`. -/
theorem KeyFormulaSituation.isRationallyEquivalentToZeroWithin_leftCoeff_divisorSheaf {k : ℤ}
    (ℱ : KeyFormulaSituation (divisorSheaf E) N)
    (hsection : ℱ.sectionL = (divisorSheaf E).presheaf.germ ⊤ (genericPoint X) trivial
      (divisorSheafGlobalSection E))
    (hdim : ∀ i : ℱ.Index,
      schemeDeltaDimension C (((ℱ.normalizeL.toKeyFormulaData C p).component i).subschemeι ≫ p) =
        ((k + 1 : ℤ) : EInt))
    (α : CycleGroup C p k)
    (hα : ∀ x : X, α.1 x = (ℱ.normalizeL.toKeyFormulaData C p).leftCoeff C p x) :
    IsRationallyEquivalentToZeroWithin C p k α (E.support : Set X) := by
  refine (ℱ.normalizeL.isRationallyEquivalentToZeroWithin_leftCoeff C p
    (fun i ↦ ℱ.componentPoint i ∈ (E.support : Set X)) (fun i hi ↦ ?_) hdim α hα).mono ?_
  · refine ℱ.normalizeL_ratioL_eq_one i ?_
    rw [hsection]
    exact isCoordinateAt_one_divisorSheafGlobalSection E hi
  · refine Set.iUnion_subset fun j ↦ ?_
    rw [coe_support_integralComponentAt]
    exact (E.support.isClosed.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr j.2)

end Divisor

end Stacks.Chow

end
