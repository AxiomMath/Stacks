module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwist
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.RingTheory.GradedAlgebra.VeroneseGrading
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseAssociatedSheaf

/-!
# Twists under the Veronese isomorphism of projective spectra

Let `S = ⨁_{i ≥ 0} S_i` be a graded ring and `d ≥ 1`, and let `S⁽ᵈ⁾` be the Veronese subring,
graded by `(S⁽ᵈ⁾)_n = S_{nd}`. The canonical isomorphism `Proj S ≅ Proj S⁽ᵈ⁾` identifies the
`nd`-th twisting sheaf on `Proj S` with the pullback of the `n`-th twisting sheaf on
`Proj S⁽ᵈ⁾`, for every integer `n`.

## Main definitions

* `Stacks.Veronese.twistGradingAddSubgroup`: the grading of the twist `S(n)` by additive subgroups
  rather than `ℤ`-submodules.
* `Stacks.Veronese.veroneseShiftSheafIso`: on `Proj S⁽ᵈ⁾`, the sheaf associated to the Veronese part
  of `S(nd)` is the sheaf associated to the twist `S⁽ᵈ⁾(n)`.
* `Stacks.Veronese.veroneseTwistingSheafIso`: the comparison isomorphism
  `𝒪_{Proj S}(nd) ≅ (Proj S ≅ Proj S⁽ᵈ⁾)^* 𝒪_{Proj S⁽ᵈ⁾}(n)`.

## Implementation notes

The isomorphism is oriented from the twist on `Proj S` to the pullback of the twist on
`Proj S⁽ᵈ⁾`, as in the source, and the pullback is the pullback of sheaves of modules along the
canonical isomorphism of schemes.

It is assembled in two steps. The Veronese comparison of associated sheaves identifies the sheaf
associated to a `ℤ`-graded `S`-module with the pullback of the sheaf associated to its Veronese
part; applied to `S(nd)` it reduces the statement to `veroneseShiftSheafIso`, which identifies
the Veronese part of `S(nd)` with `S⁽ᵈ⁾(n)`. Both sides of that identification have underlying
module the Veronese subring, and in degree `i` both are `S_{(i+n)d}` when `i + n ≥ 0` and zero
otherwise; so the comparison is a graded `S⁽ᵈ⁾`-linear equivalence, which the functoriality of the
associated-sheaf construction turns into an isomorphism of sheaves.

That the two underlying modules agree is proved by a double induction rather than by a formula,
because the two are cut out differently: the Veronese part of a graded module is a
`Submodule.span` of homogeneous pieces, whereas the Veronese subring is a `Subring.closure`.

`twistGradingAddSubgroup` exists only because the Veronese part of a graded module is defined for
gradings valued in `AddSubgroup`, whereas `Stacks.GradedModule.twistGrading` is valued in
`Submodule ℤ`; it is the same grading, re-seated in the other `SetLike` type, together with the
two instances the associated-sheaf construction needs.

## References

* [Stacks Project, Tag 0B5J](https://stacks.math.columbia.edu/tag/0B5J)
-/

@[expose] public noncomputable section

namespace Stacks.Veronese

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality

universe u w

variable {S : Type u} {σ : Type w} [CommRing S]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The grading of the twist `S(n)`, valued in additive subgroups of `S`: the degree-`i` piece
is `S_{i+n}`, and zero for `i + n < 0`. -/
public noncomputable def twistGradingAddSubgroup (n : ℤ) : ℤ → AddSubgroup S :=
  fun i => (twistGrading (S := S) 𝒮 n i).toAddSubgroup

public noncomputable instance twistGradingAddSubgroupDecomposition (n : ℤ) :
    DirectSum.Decomposition (twistGradingAddSubgroup 𝒮 n) := by
  let e : DirectSum.Decomposition (twistGrading (S := S) 𝒮 n) := twistGradingDecomposition 𝒮 n
  exact { decompose' := e.decompose', left_inv := e.left_inv, right_inv := e.right_inv }

public instance twistGradingAddSubgroupGradedSMul (n : ℤ) :
    SetLike.GradedSMul 𝒮 (twistGradingAddSubgroup 𝒮 n) := by
  constructor
  intro i j a b ha hb
  have hb' : b ∈ twistGrading (S := S) 𝒮 n j := by simpa [twistGradingAddSubgroup] using hb
  have h := SetLike.GradedSMul.smul_mem ha hb'
  simpa [twistGradingAddSubgroup] using h

/-- The degree-`id` piece of the twist `S(nd)` is `S_{kd}` when `i + n = k` for a natural
number `k`. -/
private theorem mem_twistGrading_mul_iff_of_eq {R : Type u} {τ : Type w} [CommRing R]
    [SetLike τ R] [AddSubgroupClass τ R] (𝒯 : ℕ → τ) (d : ℕ) (n i : ℤ) (k : ℕ) (hk : i + n = k)
    (x : R) : x ∈ twistGrading (S := R) 𝒯 (n * d) (i * d) ↔ x ∈ 𝒯 (k * d) := by
  have hdegree : i * (d : ℤ) + n * d = ((k * d : ℕ) : ℤ) := by
    rw [Nat.cast_mul, ← hk]
    ring
  rw [twistGrading_apply, hdegree, integerGrading_natCast, mem_homogeneousSubmodule]

omit [GradedRing 𝒮] in
/-- The degree-`id` piece of the twist `S(nd)` is `S_{(i+n)d}` when `i + n ≥ 0` and zero
otherwise. -/
public theorem mem_twistGrading_mul_iff (d : ℕ) (hd : 0 < d) (n i : ℤ) (x : S) :
    x ∈ twistGrading (S := S) 𝒮 (n * d) (i * d) ↔
      (if 0 ≤ i + n then x ∈ 𝒮 ((i + n).toNat * d) else x = 0) := by
  have hdegreeNeg (hi : ¬ 0 ≤ i + n) : i * (d : ℤ) + n * d < 0 := by
    calc
      i * (d : ℤ) + n * d = (i + n) * d := by ring
      _ < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hi) (by exact_mod_cast hd)
  by_cases hi : 0 ≤ i + n
  · rw [ite_eq_left hi]
    exact mem_twistGrading_mul_iff_of_eq 𝒮 d n i _ (Int.toNat_of_nonneg hi).symm x
  · rw [ite_eq_right hi, twistGrading_apply,
      integerGrading_neg (S := S) 𝒮 _ (hdegreeNeg hi)]
    simp

omit [GradedRing 𝒮] in
/-- The degree-`i` piece of the twist `S⁽ᵈ⁾(n)` is `S_{(i+n)d}` when `i + n ≥ 0` and zero
otherwise. -/
public theorem mem_veroneseTwistGrading_iff (d : ℕ) (n i : ℤ) (x : veroneseSubring 𝒮 d) :
    x ∈ twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) n i ↔
      (if 0 ≤ i + n then (x : S) ∈ 𝒮 ((i + n).toNat * d) else x = 0) := by
  by_cases hi : 0 ≤ i + n
  · simp only [twistGrading_apply, integerGrading, ite_eq_left hi,
      homogeneousSubmodule, veroneseGrading]
    rfl
  · simp [twistGrading_apply, integerGrading, hi]

omit [GradedRing 𝒮] in
/-- Every element of the Veronese part of `S(nd)` lies in the Veronese subring. -/
public theorem coe_mem_veroneseSubring_of_twist (d : ℕ) (hd : 0 < d) (n : ℤ)
    (x : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d) :
    (x : S) ∈ veroneseSubring 𝒮 d := by
  show (x : S) ∈ Subring.closure (veroneseSet 𝒮 d)
  refine Submodule.span_induction (p := fun y _ => y ∈ veroneseSubring 𝒮 d) ?_ ?_ ?_ ?_ x.2
  · intro y hy
    rcases Set.mem_iUnion.mp hy with ⟨i, hyi⟩
    have hm := (mem_twistGrading_mul_iff 𝒮 d hd n i y).mp hyi
    by_cases hi : 0 ≤ i + n
    · exact Subring.subset_closure (Set.mem_iUnion.mpr ⟨(i + n).toNat, by simpa [hi] using hm⟩)
    · simp [show y = 0 by simpa [hi] using hm]
  · exact (veroneseSubring 𝒮 d).zero_mem
  · exact fun _ _ _ _ hy hz => (veroneseSubring 𝒮 d).add_mem hy hz
  · intro r y _ hy
    show (r : S) * y ∈ veroneseSubring 𝒮 d
    exact (veroneseSubring 𝒮 d).mul_mem r.2 hy

/-- Every element of the Veronese subring lies in the Veronese part of `S(nd)`. -/
public theorem coe_mem_veroneseSubmodule_twist (d : ℕ) (n : ℤ) (x : veroneseSubring 𝒮 d) :
    (x : S) ∈ veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d := by
  let A := veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d
  let V := veroneseSubring 𝒮 d
  have hp : (x : S) ∈ A ∧ (x : S) ∈ V := by
    refine Subring.closure_induction (p := fun y _ => y ∈ A ∧ y ∈ V) ?_ ?_ ?_ ?_ ?_ ?_ x.2
    · intro y hys
      have hyV : y ∈ veroneseSet 𝒮 d := hys
      rcases Set.mem_iUnion.mp hyV with ⟨j, hy⟩
      refine ⟨Submodule.subset_span (Set.mem_iUnion.mpr ⟨(j : ℤ) - n, ?_⟩),
        Subring.subset_closure hyV⟩
      exact (mem_twistGrading_mul_iff_of_eq 𝒮 d n _ j (sub_add_cancel _ _) y).2 hy
    · exact ⟨A.zero_mem, V.zero_mem⟩
    · refine ⟨Submodule.subset_span (Set.mem_iUnion.mpr ⟨-n, ?_⟩), V.one_mem⟩
      refine (mem_twistGrading_mul_iff_of_eq 𝒮 d n (-n) 0 (neg_add_cancel n) 1).2 ?_
      simpa using SetLike.GradedOne.one_mem
    · intro y z _ _ hy hz
      exact ⟨A.add_mem hy.1 hz.1, V.add_mem hy.2 hz.2⟩
    · intro y _ hy
      exact ⟨A.neg_mem hy.1, V.neg_mem hy.2⟩
    · intro y z _ _ hy hz
      exact ⟨A.smul_mem ⟨y, hy.2⟩ hz.1, V.mul_mem hy.2 hz.2⟩
  exact hp.1

/-- The Veronese part of `S(nd)` and the twist `S⁽ᵈ⁾(n)` have the same underlying `S⁽ᵈ⁾`-module,
the Veronese subring: this is the identity of their elements, as a linear equivalence. -/
public noncomputable def veroneseShiftLinearEquiv (d : ℕ) (hd : 0 < d) (n : ℤ) :
    veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d ≃ₗ[veroneseSubring 𝒮 d]
      veroneseSubring 𝒮 d :=
  LinearEquiv.ofBijective
    { toFun := fun x => ⟨x.1, coe_mem_veroneseSubring_of_twist 𝒮 d hd n x⟩
      map_add' := by intro x y; apply Subtype.ext; rfl
      map_smul' := by intro r x; apply Subtype.ext; rfl }
    ⟨fun x y hxy => Subtype.ext (by simpa using congrArg Subtype.val hxy),
      fun y => ⟨⟨y.1, coe_mem_veroneseSubmodule_twist 𝒮 d n y⟩, Subtype.ext rfl⟩⟩

/-- `veroneseShiftLinearEquiv` is the identity on underlying elements of `S`. -/
@[simp]
public theorem coe_veroneseShiftLinearEquiv (d : ℕ) (hd : 0 < d) (n : ℤ)
    (x : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d) :
    ((veroneseShiftLinearEquiv 𝒮 d hd n x : veroneseSubring 𝒮 d) : S) = (x : S) :=
  rfl

/-- `veroneseShiftLinearEquiv` preserves the gradings. -/
public theorem veroneseShiftLinearEquiv_mem (d : ℕ) (hd : 0 < d) (n : ℤ) (i : ℤ)
    (x : veroneseSubmodule 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
    (hx : x ∈ veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d i) :
    veroneseShiftLinearEquiv 𝒮 d hd n x ∈
      twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) n i := by
  change (x : S) ∈ twistGrading (S := S) 𝒮 (n * d) (i * d) at hx
  have hm := (mem_twistGrading_mul_iff 𝒮 d hd n i (x : S)).mp hx
  refine (mem_veroneseTwistGrading_iff 𝒮 d n i _).2 ?_
  by_cases hi : 0 ≤ i + n
  · simpa [hi] using hm
  · have hzero : (veroneseShiftLinearEquiv 𝒮 d hd n x : veroneseSubring 𝒮 d) = 0 := by
      apply Subtype.ext
      simpa [hi] using hm
    simpa [hi] using hzero

/-- The inverse of `veroneseShiftLinearEquiv` preserves the gradings. -/
public theorem veroneseShiftLinearEquiv_symm_mem (d : ℕ) (hd : 0 < d) (n : ℤ) (i : ℤ)
    (x : veroneseSubring 𝒮 d)
    (hx : x ∈ twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) n i) :
    (veroneseShiftLinearEquiv 𝒮 d hd n).symm x ∈
      veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d i := by
  have hm := (mem_veroneseTwistGrading_iff 𝒮 d n i x).mp hx
  show ((veroneseShiftLinearEquiv 𝒮 d hd n).symm x : S) ∈
    twistGrading (S := S) 𝒮 (n * d) (i * d)
  have hval : ((veroneseShiftLinearEquiv 𝒮 d hd n).symm x : S) = (x : S) :=
    congrArg Subtype.val ((veroneseShiftLinearEquiv 𝒮 d hd n).apply_symm_apply x)
  apply (mem_twistGrading_mul_iff 𝒮 d hd n i _).2
  by_cases hi : 0 ≤ i + n
  · simpa [hval, hi] using hm
  · simp [hi, show x = 0 by simpa [hi] using hm]

/-- On `Proj S⁽ᵈ⁾` the sheaf associated to the Veronese part of the twist `S(nd)` is the sheaf
associated to the twist `S⁽ᵈ⁾(n)`: the associated-sheaf map of `veroneseShiftLinearEquiv`. -/
public noncomputable def veroneseShiftSheafIso (d : ℕ) (hd : 0 < d) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    associatedModuleSheaf (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d) ≅
      associatedModuleSheaf (veroneseGrading 𝒮 d)
        (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) n) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  let moduleGrade := twistGradingAddSubgroup 𝒮 (n * d)
  let sourceGrade := veroneseModuleGrading 𝒮 moduleGrade d
  let targetGrade := twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) n
  letI : DirectSum.Decomposition sourceGrade :=
    veroneseModuleGradingDecomposition 𝒮 moduleGrade d hd
  letI : SetLike.GradedSMul (veroneseGrading 𝒮 d) sourceGrade :=
    veroneseModuleGrading_gradedSMul 𝒮 moduleGrade d
  let e := veroneseShiftLinearEquiv 𝒮 d hd n
  have hφ := veroneseShiftLinearEquiv_mem 𝒮 d hd n
  have hsymm := veroneseShiftLinearEquiv_symm_mem 𝒮 d hd n
  let f := associatedModuleSheafMap (veroneseGrading 𝒮 d) sourceGrade targetGrade
    e.toLinearMap hφ
  let g := associatedModuleSheafMap (veroneseGrading 𝒮 d) targetGrade sourceGrade
    e.symm.toLinearMap hsymm
  have hfg : f ≫ g = 𝟙 _ := by
    have hc := associatedModuleSheafMap_comp
      (𝒮 := veroneseGrading 𝒮 d) (𝒨 := sourceGrade) (𝒩 := targetGrade) (𝒬 := sourceGrade)
      e.toLinearMap hφ e.symm.toLinearMap hsymm
    have heq : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      ext
      simp
    calc
      f ≫ g = associatedModuleSheafMap (veroneseGrading 𝒮 d) sourceGrade sourceGrade
          (e.symm.toLinearMap.comp e.toLinearMap) _ := hc.symm
      _ = associatedModuleSheafMap (veroneseGrading 𝒮 d) sourceGrade sourceGrade
          (LinearMap.id) _ := by congr 1
      _ = 𝟙 _ := associatedModuleSheafMap_id
        (𝒮 := veroneseGrading 𝒮 d) (𝒨 := sourceGrade)
  have hgf : g ≫ f = 𝟙 _ := by
    have hc := associatedModuleSheafMap_comp
      (𝒮 := veroneseGrading 𝒮 d) (𝒨 := targetGrade) (𝒩 := sourceGrade) (𝒬 := targetGrade)
      e.symm.toLinearMap hsymm e.toLinearMap hφ
    have heq : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      ext
      simp
    calc
      g ≫ f = associatedModuleSheafMap (veroneseGrading 𝒮 d) targetGrade targetGrade
          (e.toLinearMap.comp e.symm.toLinearMap) _ := hc.symm
      _ = associatedModuleSheafMap (veroneseGrading 𝒮 d) targetGrade targetGrade
          (LinearMap.id) _ := by congr 1
      _ = 𝟙 _ := associatedModuleSheafMap_id
        (𝒮 := veroneseGrading 𝒮 d) (𝒨 := targetGrade)
  exact ⟨f, g, hfg, hgf⟩

/-- `veroneseShiftSheafIso` is the associated-sheaf map of `veroneseShiftLinearEquiv`. -/
public theorem veroneseShiftSheafIso_hom (d : ℕ) (hd : 0 < d) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    letI := veroneseModuleGradingDecomposition 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d hd
    (veroneseShiftSheafIso 𝒮 d hd n).hom =
      associatedModuleSheafMap (veroneseGrading 𝒮 d)
        (veroneseModuleGrading 𝒮 (twistGradingAddSubgroup 𝒮 (n * d)) d)
        (twistGrading (S := veroneseSubring 𝒮 d) (veroneseGrading 𝒮 d) n)
        (veroneseShiftLinearEquiv 𝒮 d hd n).toLinearMap
        (veroneseShiftLinearEquiv_mem 𝒮 d hd n) :=
  rfl

/-- The canonical comparison of twists under the Veronese isomorphism of projective
spectra. -/
public noncomputable def veroneseTwistingSheafIso (d : ℕ) (hd : 0 < d) (n : ℤ) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    twistingSheaf 𝒮 (n * d) ≅
      (Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).obj
        (twistingSheaf (veroneseGrading 𝒮 d) n) := by
  letI := veroneseGradingGradedRing 𝒮 d hd
  exact (associatedModuleSheafVeroneseIso (𝒮 := 𝒮)
      (𝒨 := twistGradingAddSubgroup 𝒮 (n * d)) d hd).trans
    ((Scheme.Modules.pullback (veroneseProjIso 𝒮 d hd).hom).mapIso
      (veroneseShiftSheafIso 𝒮 d hd n))

end Stacks.Veronese

end
