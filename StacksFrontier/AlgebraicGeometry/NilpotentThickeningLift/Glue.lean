module

public import StacksFrontier.AlgebraicGeometry.NilpotentThickeningLift.Algebra
public import StacksFrontier.AlgebraicGeometry.NormInvertible.TensorPowerGenerator
public import StacksFrontier.AlgebraicGeometry.SectionExtension.Nilpotent
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.IntersectionGeneration

/-!
# Gluing powers of local lifts of a section

Let `X` be a quasi-separated scheme and `L` an invertible `𝒪_X`-module, trivialized on a finite
affine open cover `U_j` by generators `g_j`, with transition functions `c_{jk}`
(`g_k = c_{jk} g_j` on `U_j ∩ U_k`). Let `f_j ∈ Γ(U_j, 𝒪_X)` be functions such that the
`D(f_j)` are the traces `W ∩ U_j` of one open `W` contained in `U_{j₀}`, and such that each
`f_j - c_{j j₀}^n f_{j₀}` is nilpotent on `U_j ∩ U_{j₀}`. Then a power of the local sections
`f_j g_j^{⊗ n}` glues: there is a global section of a positive tensor power of `L` whose
nonvanishing locus is `W`.

This is the gluing step of the proof of [Stacks, Tag 09MS], for the local lifts of a section on a
closed subscheme with nilpotent ideal and the same underlying space.

## Main results

* `Stacks.NilpotentThickeningLift.exists_pow_lift_on_basicOpen`: on an affine open, a nilpotent
  perturbation `φ` of `f` on `D(f)` has all large powers equal to the restrictions of multiples
  of `f`.
* `Stacks.NilpotentThickeningLift.exists_sections_nonvanishingOpen_eq`: the global section.

## References

* [Stacks Project, Tag 09MS](https://stacks.math.columbia.edu/tag/09MS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.NilpotentThickeningLift

open Stacks.SheafOfModules Stacks.SheafOfModules.Invertible

variable {X : Scheme.{u}}

/-- Restriction of functions along an inclusion of opens, as a ring homomorphism:
`AlgebraicGeometry.sectionsRestrict`. -/
local notation "rs" => AlgebraicGeometry.sectionsRestrict

/-- **A nilpotent perturbation of `f` on `D(f)` is invertible there.** -/
theorem isUnit_of_isNilpotent_sub {U : X.Opens} (f : Γ(X, U)) (φ : Γ(X, X.basicOpen f))
    (hφ : IsNilpotent (φ - rs (X.basicOpen_le f) f)) : IsUnit φ := by
  have hu : IsUnit (rs (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  have h := hφ.isUnit_add_left_of_commute hu (Commute.all _ _)
  rwa [add_sub_cancel] at h

/-- **Large powers of a nilpotent perturbation of `f` on `D(f)` are restrictions of multiples of
`f`**, over an affine open: `Γ(D(f), 𝒪_X)` is the localization of `Γ(U, 𝒪_X)` away from `f`. -/
theorem exists_pow_lift_on_basicOpen {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (φ : Γ(X, X.basicOpen f)) (hφ : IsNilpotent (φ - rs (X.basicOpen_le f) f)) :
    ∃ q₀ : ℕ, ∀ q, q₀ ≤ q → ∃ h : Γ(X, U), rs (X.basicOpen_le f) (f * h) = φ ^ q := by
  have := hU.isLocalization_basicOpen f
  obtain ⟨q₀, hq₀⟩ := exists_algebraMap_mul_eq_pow_add (S := Γ(X, X.basicOpen f)) f _ hφ
  refine ⟨q₀, fun q hq => ?_⟩
  obtain ⟨h, hh⟩ := hq₀ q hq
  exact ⟨h, hh.trans (congrArg (· ^ q) (add_sub_cancel (rs (X.basicOpen_le f) f) φ))⟩

/-- **The basic open of a multiple of `f` restricting to a unit on `D(f)` is `D(f)`.** -/
theorem basicOpen_mul_eq {U : X.Opens} (f h : Γ(X, U))
    (hh : IsUnit (rs (X.basicOpen_le f) (f * h))) :
    X.basicOpen (f * h) = X.basicOpen f := by
  refine le_antisymm (by rw [X.basicOpen_mul]; exact inf_le_left) ?_
  have e := X.basicOpen_res (f * h) (homOfLE (X.basicOpen_le f)).op
  rw [X.basicOpen_of_isUnit hh] at e
  exact e.le.trans inf_le_right

/-! ### Transition functions of local generators -/

section Transition

variable (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- The transition function `c` of two local generators `g` on `U` and `g'` on `V`:
`g' = c • g` on `U ∩ V`. -/
abbrev transitionFn {U V : X.Opens} (g : GeneratorSections X.toRingedSpace L U)
    (g' : GeneratorSections X.toRingedSpace L V) : Γ(X, U ⊓ V) :=
  generatorRatio L (U ⊓ V) (generatorRestrict L inf_le_left g) (generatorRestrict L inf_le_right g')

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L] in
/-- On `U ∩ V`, the restriction of `g'` is `transitionFn L g g'` times the restriction of `g`. -/
theorem transitionFn_spec {U V : X.Opens} (g : GeneratorSections X.toRingedSpace L U)
    (g' : GeneratorSections X.toRingedSpace L V) :
    (generatorRestrict L inf_le_right g').val =
      transitionFn L g g' • (generatorRestrict L inf_le_left g).val :=
  generatorRatio_spec L _ _ _

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L] in
/-- The restriction of a transition function is the comparison of the restricted generators. -/
theorem rs_transitionFn {U V O : X.Opens} (hU : O ≤ U) (hV : O ≤ V)
    (g : GeneratorSections X.toRingedSpace L U) (g' : GeneratorSections X.toRingedSpace L V) :
    rs (le_inf hU hV) (transitionFn L g g') =
      generatorRatio L O (generatorRestrict L hU g) (generatorRestrict L hV g') := by
  have e := generatorRatio_restrict L (le_inf hU hV) (generatorRestrict L inf_le_left g)
    (generatorRestrict L inf_le_right g')
  refine e.symm.trans ?_
  exact congrArg₂ (generatorRatio L O) (generatorRestrict_trans L _ _ g)
    (generatorRestrict_trans L _ _ g')

omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L] in
/-- **The cocycle identity** for transition functions, on an open inside the triple overlap. -/
theorem rs_transitionFn_comp {U V W O : X.Opens} (hU : O ≤ U) (hV : O ≤ V) (hW : O ≤ W)
    (g : GeneratorSections X.toRingedSpace L U) (g' : GeneratorSections X.toRingedSpace L V)
    (g'' : GeneratorSections X.toRingedSpace L W) :
    rs (le_inf hU hW) (transitionFn L g g'') =
      rs (le_inf hU hV) (transitionFn L g g') * rs (le_inf hV hW) (transitionFn L g' g'') := by
  refine (rs_transitionFn L hU hW g g'').trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) (rs_transitionFn L hU hV g g').symm
    (rs_transitionFn L hV hW g' g'').symm)
  refine (generatorRatio_comp L O (generatorRestrict L hU g) (generatorRestrict L hV g')
    (generatorRestrict L hW g'')).symm.trans ?_
  exact mul_comm (G := Γ(X, O)) _ _

/-- **The tensor powers of two generators differ by the power of their transition function.** -/
theorem tensorPowerGenerator_restrict_spec {U V : X.Opens}
    (g : GeneratorSections X.toRingedSpace L U) (g' : GeneratorSections X.toRingedSpace L V)
    (D : ℕ) :
    (generatorRestrict (tensorPowerModule' L (D : ℤ)) inf_le_right
        (tensorPowerGenerator L g' D)).val =
      transitionFn L g g' ^ D •
        (generatorRestrict (tensorPowerModule' L (D : ℤ)) inf_le_left
          (tensorPowerGenerator L g D)).val := by
  have h := generatorRatioUnit_tensorPowerGenerator L (U ⊓ V) (generatorRestrict L inf_le_left g)
    (generatorRestrict L inf_le_right g') D
  have h' : generatorRatio (tensorPowerModule' L (D : ℤ)) (U ⊓ V)
      (tensorPowerGenerator L (generatorRestrict L inf_le_left g) D)
      (tensorPowerGenerator L (generatorRestrict L inf_le_right g') D) = transitionFn L g g' ^ D :=
    ((generatorRatioUnit_val _ _ _ _).symm.trans (congrArg Units.val h)).trans
      ((Units.val_pow_eq_pow_val _ D).trans
        (congrArg (· ^ D) (generatorRatioUnit_val _ _ _ _)))
  have e1 := tensorPowerGenerator_restrict L (inf_le_right : U ⊓ V ≤ V) g' D
  have e2 := tensorPowerGenerator_restrict L (inf_le_left : U ⊓ V ≤ U) g D
  have hs := generatorRatio_spec (tensorPowerModule' L (D : ℤ)) (U ⊓ V)
    (tensorPowerGenerator L (generatorRestrict L inf_le_left g) D)
    (tensorPowerGenerator L (generatorRestrict L inf_le_right g') D)
  rw [h'] at hs
  refine (congrArg Subtype.val e1).trans (hs.trans ?_)
  exact congrArg (fun z => transitionFn L g g' ^ D • z) (congrArg Subtype.val e2).symm

end Transition

/-! ### The gluing -/

section Glue

variable (L : _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

variable {J : Type u} (U : J → X.Opens) (g : ∀ j, GeneratorSections X.toRingedSpace L (U j))
  (n : ℕ) (f : ∀ j, Γ(X, U j)) (W : X.Opens) (j₀ : J)

/-- The reference function `c_{j j₀}^n f_{j₀}` on `D(f_j)`. -/
abbrev refFn (j : J) (hB : X.basicOpen (f j) ≤ U j ⊓ U j₀) : Γ(X, X.basicOpen (f j)) :=
  rs hB (transitionFn L (g j) (g j₀) ^ n * rs inf_le_right (f j₀))

include L in
omit [AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L] in
/-- On an open `O` inside `W ∩ U_j ∩ U_k`, the restrictions of two functions `a_j`, `a_k` which
restrict on `D(f_j)`, `D(f_k)` to the `q`-th powers of the reference functions differ by
`c_{jk}^{nq}`. -/
theorem rs_eq_of_le (hW : W ≤ U j₀) (hf : ∀ j, X.basicOpen (f j) = W ⊓ U j) (q : ℕ)
    (a : ∀ j, Γ(X, U j)) (hB : ∀ j, X.basicOpen (f j) ≤ U j ⊓ U j₀)
    (ha : ∀ j, rs (X.basicOpen_le (f j)) (a j) = refFn L U g n f j₀ j (hB j) ^ q)
    (j k : J) {O : X.Opens} (hOj : O ≤ U j) (hOk : O ≤ U k) (hOW : O ≤ W) :
    rs hOj (a j) = rs (le_inf hOj hOk) (transitionFn L (g j) (g k)) ^ (n * q) * rs hOk (a k) := by
  have h0 : O ≤ U j₀ := hOW.trans hW
  have E : ∀ i (hOi : O ≤ U i), rs hOi (a i) =
      (rs (le_inf hOi h0) (transitionFn L (g i) (g j₀)) ^ n * rs h0 (f j₀)) ^ q := by
    intro i hOi
    have hBi : O ≤ X.basicOpen (f i) := by rw [hf i]; exact le_inf hOW hOi
    have e := congrArg (rs hBi) (ha i)
    rw [sectionsRestrict_comp, map_pow, sectionsRestrict_comp, map_mul, map_pow,
      sectionsRestrict_comp] at e
    exact e
  have E3 := rs_transitionFn_comp L hOj hOk h0 (g j) (g k) (g j₀)
  rw [E j hOj, E k hOk, E3]
  ring

include L in
/-- **Sections `c_j g_j^{⊗ D}` compatible on the overlaps glue to a global section** of
`L^{⊗ D}`. -/
theorem exists_sections_of_compatible (hcov : ∀ x, ∃ j, x ∈ U j) (D : ℕ) (c : ∀ j, Γ(X, U j))
    (hc : ∀ j k, rs inf_le_left (c j) =
      transitionFn L (g j) (g k) ^ D * rs inf_le_right (c k)) :
    ∃ s : (tensorPowerModule' L (D : ℤ)).sections,
      ∀ j, s.eval (op (U j)) = c j • (tensorPowerGenerator L (g j) D).val := by
  set M := tensorPowerModule' L (D : ℤ)
  let a : ∀ j, M.val.presheaf.obj (op (U j)) := fun j => c j • (tensorPowerGenerator L (g j) D).val
  have hsmul : ∀ {V V' : X.Opens} (h : V' ≤ V) (r : Γ(X, V)) (z : M.val.obj (op V)),
      M.val.map (homOfLE h).op (r • z) = rs h r • M.val.map (homOfLE h).op z :=
    fun h r z => PresheafOfModules.map_smul M.val (homOfLE h).op r z
  have hcomp : TopCat.Presheaf.IsCompatible M.val.presheaf U a := by
    intro j k
    have e1 := hsmul (inf_le_left : U j ⊓ U k ≤ U j) (c j) (tensorPowerGenerator L (g j) D).val
    have e2 := hsmul (inf_le_right : U j ⊓ U k ≤ U k) (c k) (tensorPowerGenerator L (g k) D).val
    have e3 := tensorPowerGenerator_restrict_spec L (g j) (g k) D
    have e4 : rs (inf_le_left : U j ⊓ U k ≤ U j) (c j) •
          (generatorRestrict M (inf_le_left : U j ⊓ U k ≤ U j)
            (tensorPowerGenerator L (g j) D)).val =
        rs (inf_le_right : U j ⊓ U k ≤ U k) (c k) • (transitionFn L (g j) (g k) ^ D •
          (generatorRestrict M (inf_le_left : U j ⊓ U k ≤ U j)
            (tensorPowerGenerator L (g j) D)).val) := by
      rw [hc j k, mul_comm, mul_smul]
    exact e1.trans (e4.trans ((congrArg (fun z => rs (inf_le_right : U j ⊓ U k ≤ U k) (c k) • z)
      e3.symm).trans e2.symm))
  obtain ⟨b, hb, -⟩ := TopCat.Presheaf.IsSheaf.isSheafUniqueGluing M.isSheaf U a hcomp
  have hsup : iSup U = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨j, hj⟩ := hcov x
    exact Opens.mem_iSup.mpr ⟨j, hj⟩
  refine ⟨sectionsOfTop M (M.val.map (homOfLE hsup.ge).op b), fun j => ?_⟩
  have e := hb j
  have e0 := PresheafOfModules.sections_property
    (sectionsOfTop M (M.val.map (homOfLE hsup.ge).op b)) (homOfLE (le_top : U j ≤ ⊤)).op
  refine e0.symm.trans ?_
  refine (congrArg (fun z => M.val.map (homOfLE (le_top : U j ≤ ⊤)).op z)
    (sectionsOfTop_eval_top M _)).trans ?_
  refine (PresheafOfModules.map_comp_apply M.val (homOfLE hsup.ge).op
    (homOfLE (le_top : U j ≤ ⊤)).op b).symm.trans ?_
  refine (PresheafOfModules.congr_map_apply M.val (Subsingleton.elim _ _) b).trans ?_
  exact e

include L in
/-- **The gluing of [Stacks, Tag 09MS].** On a quasi-separated scheme, let `g_j` be generators of
`L` on a finite affine open cover `U_j`, let `f_j ∈ Γ(U_j, 𝒪_X)` be functions with
`D(f_j) = W ∩ U_j` for an open `W ⊆ U_{j₀}`, and such that every `f_j - c_{j j₀}^n f_{j₀}` is
nilpotent on `U_j ∩ U_{j₀}`. Then some global section of a positive tensor power of `L` has
nonvanishing locus `W`. -/
theorem exists_sections_nonvanishingOpen_eq [QuasiSeparatedSpace X] [Finite J]
    (hU : ∀ j, IsAffineOpen (U j)) (hcov : ∀ x, ∃ j, x ∈ U j) (hn : 1 ≤ n)
    (hW : W ≤ U j₀) (hf : ∀ j, X.basicOpen (f j) = W ⊓ U j)
    (hnil : ∀ j, IsNilpotent (rs inf_le_left (f j) -
      transitionFn L (g j) (g j₀) ^ n * rs inf_le_right (f j₀))) :
    ∃ D : ℕ, 1 ≤ D ∧ ∃ s : (tensorPowerModule' L (D : ℤ)).sections,
      Stacks.SheafOfModules.nonvanishingOpen (X := X.toRingedSpace) _ s = W := by
  classical
  have := Fintype.ofFinite J
  have hB : ∀ j, X.basicOpen (f j) ≤ U j ⊓ U j₀ := fun j => by
    rw [hf j]; exact le_inf inf_le_right (inf_le_left.trans hW)
  have hφ : ∀ j, IsNilpotent (refFn L U g n f j₀ j (hB j) - rs (X.basicOpen_le (f j)) (f j)) := by
    intro j
    have h1 := ((hnil j).map (rs (hB j))).neg
    have e : -(rs (hB j)) (rs inf_le_left (f j) -
        transitionFn L (g j) (g j₀) ^ n * rs inf_le_right (f j₀)) =
        refFn L U g n f j₀ j (hB j) - rs (X.basicOpen_le (f j)) (f j) := by
      rw [map_sub, sectionsRestrict_comp, neg_sub]
    rwa [e] at h1
  choose q₀ hq₀ using fun j => exists_pow_lift_on_basicOpen (hU j) (f j) _ (hφ j)
  set q : ℕ := Finset.univ.sup q₀ + 1 with hq
  have hq1 : 1 ≤ q := by omega
  choose h hh using fun j => hq₀ j q
    ((Finset.le_sup (f := q₀) (Finset.mem_univ j)).trans (Nat.le_succ _))
  obtain ⟨a, ha⟩ : ∃ a : ∀ j, Γ(X, U j), ∀ j, a j = f j * h j := ⟨_, fun _ => rfl⟩
  have hh' : ∀ j, rs (X.basicOpen_le (f j)) (a j) = refFn L U g n f j₀ j (hB j) ^ q :=
    fun j => by rw [ha]; exact hh j
  have hunit : ∀ j, IsUnit (rs (X.basicOpen_le (f j)) (f j * h j)) := fun j => by
    rw [hh j]; exact (isUnit_of_isNilpotent_sub (f j) _ (hφ j)).pow q
  have hba : ∀ j, X.basicOpen (a j) = W ⊓ U j := fun j => by
    rw [ha]; exact (basicOpen_mul_eq (f j) (h j) (hunit j)).trans (hf j)
  -- the agreement of the `a_j` on `W`
  have hagree : ∀ j k {O : X.Opens} (hOj : O ≤ U j) (hOk : O ≤ U k), O ≤ W →
      rs hOj (a j) = rs (le_inf hOj hOk) (transitionFn L (g j) (g k)) ^ (n * q) * rs hOk (a k) :=
    fun j k _ hOj hOk hOW => rs_eq_of_le L U g n f W j₀ hW hf q a hB hh' j k hOj hOk hOW
  -- the exponents killing the differences
  have hκ : ∀ j k, ∃ κ : ℕ, ∀ κ', κ ≤ κ' →
      rs inf_le_left (f j) ^ κ' * (rs inf_le_left (a j) -
        transitionFn L (g j) (g k) ^ (n * q) * rs inf_le_right (a k)) = 0 ∧
      rs inf_le_right (f k) ^ κ' * (rs inf_le_left (a j) -
        transitionFn L (g j) (g k) ^ (n * q) * rs inf_le_right (a k)) = 0 := by
    intro j k
    have hV : IsCompact ((U j ⊓ U k : X.Opens) : Set X) :=
      (hU j).isCompact.inter_of_isOpen (hU k).isCompact (U j).isOpen (U k).isOpen
    have hzero : ∀ {O : X.Opens} (hO : O ≤ U j ⊓ U k), O ≤ W →
        rs hO (rs inf_le_left (a j) -
          transitionFn L (g j) (g k) ^ (n * q) * rs inf_le_right (a k)) = 0 := by
      intro O hO hOW
      rw [map_sub, map_mul, map_pow, sectionsRestrict_comp, sectionsRestrict_comp, sub_eq_zero]
      exact hagree j k (hO.trans inf_le_left) (hO.trans inf_le_right) hOW
    have key : ∀ (i : J) (hi : U j ⊓ U k ≤ U i), ∃ κ : ℕ, ∀ κ', κ ≤ κ' →
        rs hi (f i) ^ κ' * (rs inf_le_left (a j) -
          transitionFn L (g j) (g k) ^ (n * q) * rs inf_le_right (a k)) = 0 := by
      intro i hi
      have hO : X.basicOpen (rs hi (f i)) ≤ W := by
        rw [X.basicOpen_res, hf i]; exact inf_le_right.trans inf_le_left
      obtain ⟨κ, hκ⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hV _
        (rs hi (f i)) (hzero (X.basicOpen_le _) hO)
      refine ⟨κ, fun κ' hκ' => ?_⟩
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hκ'
      rw [pow_add, mul_comm (_ ^ κ), mul_assoc, hκ, mul_zero]
    obtain ⟨κ₁, hκ₁⟩ := key j inf_le_left
    obtain ⟨κ₂, hκ₂⟩ := key k inf_le_right
    exact ⟨max κ₁ κ₂, fun κ' hκ' =>
      ⟨hκ₁ _ ((le_max_left _ _).trans hκ'), hκ₂ _ ((le_max_right _ _).trans hκ')⟩⟩
  choose κ hκ using hκ
  set K : ℕ := Finset.univ.sup (fun p : J × J => κ p.1 p.2) with hK
  have hKle : ∀ j k, κ j k ≤ K := fun j k =>
    Finset.le_sup (f := fun p : J × J => κ p.1 p.2) (Finset.mem_univ (j, k))
  set m : ℕ := 2 * K + 1 with hm
  -- the powers agree on the overlaps
  have hpow : ∀ j k, rs inf_le_left (a j ^ m) =
      transitionFn L (g j) (g k) ^ (n * q * m) * rs inf_le_right (a k ^ m) := by
    intro j k
    obtain ⟨h1, h2⟩ := hκ j k K (hKle j k)
    have hA : rs (inf_le_left : U j ⊓ U k ≤ U j) (a j) =
        rs (inf_le_left : U j ⊓ U k ≤ U j) (f j) * rs (inf_le_left : U j ⊓ U k ≤ U j) (h j) := by
      rw [ha, map_mul]
    have hBk : transitionFn L (g j) (g k) ^ (n * q) * rs (inf_le_right : U j ⊓ U k ≤ U k) (a k) =
        rs (inf_le_right : U j ⊓ U k ≤ U k) (f k) * (transitionFn L (g j) (g k) ^ (n * q) *
          rs (inf_le_right : U j ⊓ U k ≤ U k) (h k)) := by
      rw [ha, map_mul]; ring
    rw [hA, hBk] at h1 h2
    have e := pow_eq_pow_of_mul_pow_sub_eq_zero (rs (inf_le_left : U j ⊓ U k ≤ U j) (h j))
      (transitionFn L (g j) (g k) ^ (n * q) * rs (inf_le_right : U j ⊓ U k ≤ U k) (h k))
      (rs (inf_le_left : U j ⊓ U k ≤ U j) (f j)) (rs (inf_le_right : U j ⊓ U k ≤ U k) (f k))
      K m h1 h2 (by omega)
    calc rs inf_le_left (a j ^ m) = (rs (inf_le_left : U j ⊓ U k ≤ U j) (a j)) ^ m := map_pow _ _ _
      _ = (rs (inf_le_left : U j ⊓ U k ≤ U j) (f j) *
            rs (inf_le_left : U j ⊓ U k ≤ U j) (h j)) ^ m := by rw [hA]
      _ = (rs (inf_le_right : U j ⊓ U k ≤ U k) (f k) * (transitionFn L (g j) (g k) ^ (n * q) *
            rs (inf_le_right : U j ⊓ U k ≤ U k) (h k))) ^ m := e
      _ = (transitionFn L (g j) (g k) ^ (n * q) * rs (inf_le_right : U j ⊓ U k ≤ U k) (a k)) ^ m :=
          by rw [hBk]
      _ = transitionFn L (g j) (g k) ^ (n * q * m) * rs inf_le_right (a k ^ m) := by
          rw [map_pow, mul_pow, ← pow_mul]
  obtain ⟨s, hs⟩ := exists_sections_of_compatible L U g hcov (n * q * m) (fun j => a j ^ m) hpow
  refine ⟨n * q * m, Nat.mul_le_mul (Nat.mul_le_mul hn hq1) (by omega : 1 ≤ m), s, ?_⟩
  ext x
  obtain ⟨j, hj⟩ := hcov x
  have e := AlgebraicGeometry.Scheme.Modules.basicOpen_eq_inf_nonvanishingOpen_of_generator L s
    (tensorPowerGenerator L (g j) (n * q * m)) (a j ^ m) (hs j)
  rw [X.basicOpen_pow _ (by omega : 0 < m), hba j] at e
  simpa [hj] using (SetLike.ext_iff.mp e x).symm

end Glue


end Stacks.NilpotentThickeningLift
