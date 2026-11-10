module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CharacterDualEval
public import StacksFrontier.Algebra.DifferentialGraded.Module.CharacterDualExact
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftNativeCover
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyI
public import StacksCore.Tactic.StacksAttribute

/-! # Injections into products of shifts of `A^∨`

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. Stacks 09KT is the
dual of Stacks 09KN: every right differential graded `A`-module `M` admits an injection into a
module `I` sitting in an admissible short exact sequence whose two ends are products of shifts
of the graded dual `A^∨`.

The construction is the one of the source. Dualize `M` to the left differential graded module
`M^∨`; cover it, by Stacks 09KN for left modules, with a direct sum of two-cell free modules
`⨁ᵢ Q_{kᵢ} ↠ M^∨` sitting in an admissible short exact sequence with ends `⨁ᵢ A[-kᵢ-1]` and
`⨁ᵢ A[-kᵢ]`; then dualize everything back. (The cover carries bare `A[k]`-cells as well as
two-cells; that is what part (2) needs, and it changes neither of the two ends.) The dual of a
surjection is injective and the dual of a direct sum of shifts of `A` is a product of shifts of
`A^∨`, so

`M → (M^∨)^∨ → (⨁ᵢ Q_{kᵢ})^∨`

is an injection into a module with the required admissible sequence, the two ends having been
exchanged by the dualization.

## Main results

* `DifferentialGraded.LeftModule.dualGradedMap`: the graded dual of a map of *graded* left
  modules, which is what transports the splittings.
* `DifferentialGraded.LeftModule.isAdmissibleShortExact_dualMap`: the graded dual of an
  admissible short exact sequence of left modules is an admissible short exact sequence of right
  modules, with the ends exchanged.
* `DifferentialGradedModule.exists_separating_cocycle`: a homogeneous element of `M` that is not
  a coboundary is not killed by some cocycle of `M^∨`.
* `DifferentialGradedModule.exists_dual_injection`: Stacks 09KT.

## Implementation notes

*How part (2) is obtained.* Part (2) of the source lemma asks that `Coker(d_M) → Coker(d_I)` be
injective, and the source obtains it by *adding a product of copies of shifts of `A^∨`* to `I`.
Dually that is a bare `A[k]`-cell in the cover of `M^∨`, which is exactly what part (2) of
Stacks 09KN for left modules supplies: `exists_cover` produces, for every homogeneous cocycle of
`M^∨` of degree `m`, a cocycle of the cover of degree `m` mapping onto it. The argument is then
the source's. A homogeneous `x ∈ M^n` that is not a coboundary is separated from `d (M^{n-1})` by
a character `μ` of `M^n`, whose extension by zero is a cocycle `l` of `M^∨` with `l x ≠ 0`; lift
`l` to a homogeneous cocycle `q` of the cover; and observe that the character `d_I w` kills `q`,
because the differential of a graded dual is precomposition with the *signed* differential, which
on a homogeneous element is a scalar multiple of `d`. So `x` cannot be in the preimage of
`Im(d_I)`. The general case follows because the statement is closed under sums and an element is
the sum of its homogeneous components, whose images under `φ` are the homogeneous components of
its image (`DifferentialGraded.LeftModule.gradedProjection_comm`) and are coboundaries whenever
its image is (`DirectSum.gradedProjection_comp_of_degree_one`).

*Why admissibility survives dualization.* An admissible monomorphism is one with a retraction by
a map of graded modules — a map not required to commute with the differentials. The graded dual
of such a map is again a map of graded modules, by `dualGradedMap`, and it is a *section* of the
dualized map; so an admissible monomorphism dualizes to an admissible epimorphism and conversely.
Nothing about the differentials is needed, which is the point of the admissible notion.

## References

* [Stacks Project, Tag 09KT](https://stacks.math.columbia.edu/tag/09KT)
* [Stacks Project, Tag 09KN](https://stacks.math.columbia.edu/tag/09KN)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.LeftModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

attribute [local instance] charModule charIsScalarTower


/-- A character of `N` pulled back along a graded map stays homogeneous of the same degree. -/
theorem gradedDual_mem_dualPiece {M N : LeftModule A} (g : GradedHom M N) {n : ℤ}
    {l : CharacterModule N.M} (hl : l ∈ dualPiece N n) :
    CharacterModule.dual g.toFun l ∈ dualPiece M n :=
  fun m hm x hx => hl m hm _ (g.map_grading m x hx)

/-- A sum of homogeneous characters pulls back along a graded map to a sum of homogeneous
characters. -/
theorem gradedDual_mem_dualCarrier {M N : LeftModule A} (g : GradedHom M N)
    {l : CharacterModule N.M} (hl : l ∈ dualCarrier N) :
    CharacterModule.dual g.toFun l ∈ dualCarrier M := by
  rw [mem_dualCarrier] at hl ⊢
  induction hl using Submodule.iSup_induction' with
  | mem n z hz => exact Submodule.mem_iSup_of_mem n (gradedDual_mem_dualPiece g hz)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add z z' _ _ ihz ihz' => rw [map_add]; exact Submodule.add_mem _ ihz ihz'

/-- The underlying map of the graded dual of a map of graded left modules. -/
def dualGradedMapFun {M N : LeftModule A} (g : GradedHom M N) : (dual N).M →ₗ[R] (dual M).M :=
  LinearMap.restrict (CharacterModule.dual g.toFun)
    (p := (dualSub N).restrictScalars R) (q := (dualSub M).restrictScalars R)
    (fun _ hl => gradedDual_mem_dualCarrier g hl)

/-- Read as a character of `M`, `dualGradedMapFun g x` is the character `x` precomposed with
`g`. -/
@[simp] theorem dualChar_dualGradedMapFun {M N : LeftModule A} (g : GradedHom M N)
    (x : (dual N).M) (y : M.M) :
    dualChar (dualGradedMapFun g x) y = dualChar x (g.toFun y) := rfl

/-- The graded dual of a map of graded left modules: a map of graded right modules
`N^∨ → M^∨`, not required to commute with the differentials. -/
def dualGradedMap {M N : LeftModule A} (g : GradedHom M N) :
    DifferentialGradedModule.GradedHom (dual N) (dual M) where
  toFun := dualGradedMapFun g
  map_smul x a := dualChar_injective (by
    ext y
    rw [dualChar_op_smul, charSMul_apply, dualChar_dualGradedMapFun,
      dualChar_dualGradedMapFun, dualChar_op_smul, charSMul_apply, MulOpposite.unop_op,
      g.map_smul])
  map_grading n x hx :=
    mem_dual_grading.mpr (gradedDual_mem_dualPiece g (mem_dual_grading.mp hx))

/-- Read as a character of `M`, `(dualGradedMap g).toFun x` is the character `x` precomposed
with `g`. -/
@[simp] theorem dualChar_dualGradedMap {M N : LeftModule A} (g : GradedHom M N)
    (x : (dual N).M) (y : M.M) :
    dualChar ((dualGradedMap g).toFun x) y = dualChar x (g.toFun y) := rfl

/-- The graded dual of an admissible monomorphism of left modules is an admissible epimorphism
of right modules: the graded retraction dualizes to a graded section. -/
theorem isAdmissibleEpi_dualMap {K L : LeftModule A} {f : K ⟶ L}
    (hf : IsAdmissibleMono f) : DifferentialGradedModule.IsAdmissibleEpi (dualMap f) := by
  obtain ⟨π, hπ⟩ := hf
  refine ⟨dualGradedMap π, fun x => dualChar_injective ?_⟩
  ext y
  rw [dualChar_dualMap, dualChar_dualGradedMap, hπ y]

/-- The graded dual of an admissible epimorphism of left modules is an admissible monomorphism
of right modules: the graded section dualizes to a graded retraction. -/
theorem isAdmissibleMono_dualMap {L M : LeftModule A} {g : L ⟶ M}
    (hg : IsAdmissibleEpi g) : DifferentialGradedModule.IsAdmissibleMono (dualMap g) := by
  obtain ⟨s, hs⟩ := hg
  refine ⟨dualGradedMap s, fun x => dualChar_injective ?_⟩
  ext y
  rw [dualChar_dualGradedMap, dualChar_dualMap, hs y]


/-- **The graded dual of an admissible short exact sequence of left modules** is an admissible
short exact sequence of right modules, with the two ends exchanged. -/
theorem isAdmissibleShortExact_dualMap {K L M : LeftModule A} {f : K ⟶ L} {g : L ⟶ M}
    (h : IsAdmissibleShortExact f g)
    (hexact : LinearMap.range (dualMap g).toFun = LinearMap.ker (dualMap f).toFun) :
    DifferentialGradedModule.IsAdmissibleShortExact (dualMap g) (dualMap f) where
  injective := dualMap_injective g h.surjective
  surjective := dualMap_surjective f h.injective
  exact := hexact
  admissibleMono := isAdmissibleMono_dualMap h.admissibleEpi
  admissibleEpi := isAdmissibleEpi_dualMap h.admissibleMono

end DifferentialGraded.LeftModule

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

local notation "Ldual" => DifferentialGraded.LeftModule.dual

/-- `∏ᵢ A^∨[kᵢ + 1]` is the graded dual of `⨁ᵢ A[-kᵢ - 1]`, which is the end of the admissible
sequence that Stacks 09KN for left modules produces. -/
theorem productDualShifts_succ {ι : Type u} [DecidableEq ι] (k : ι → ℤ) :
    productDualShifts A (fun c => k c + 1)
      = Ldual (DifferentialGraded.LeftModule.directSumShifts A (fun c => -k c - 1)) := by
  unfold productDualShifts
  rw [show (fun i : ι => -((fun c => k c + 1) i)) = (fun c : ι => -k c - 1) from
    funext fun i => by ring]

/-! ### The separating cocycle of the graded dual

Part (2) of Stacks 09KT asks that `Coker(d_M) → Coker(d_I)` be injective. The source obtains it
by separating a nonzero class of `Coker(d_M)` by a character: a homogeneous `x ∈ M^n` that is not
a coboundary is not killed by some character `μ` of `M^n` vanishing on `d (M^{n-1})`, and the
extension of `μ` by zero is then a *cocycle* of `M^∨` of degree `-n` not killing `x`. Part (2) of
Stacks 09KN for left modules supplies a cocycle of the cover mapping onto it, and a character in
the image of `d_I` kills every cocycle of the cover — which is the contradiction. -/

attribute [local instance] CharacterDual.charModule CharacterDual.charIsScalarTower

/-- The differential of `M`, restricted to a map of graded pieces `M^{n-1} → M^n`. -/
def dRestrictGrading (M : DifferentialGradedModule A) (n : ℤ) :
    (M.grading (n - 1) : Type u) →ₗ[R] (M.grading n : Type u) :=
  LinearMap.restrict M.d (p := M.grading (n - 1)) (q := M.grading n)
    (fun x hx => by simpa using M.d_mem (n - 1) x hx)

/-- The restricted differential, read in `M`. -/
@[simp] theorem dRestrictGrading_apply (M : DifferentialGradedModule A) (n : ℤ)
    (x : (M.grading (n - 1) : Type u)) :
    (dRestrictGrading M n x : M.M) = M.d (x : M.M) := rfl

/-- **A character separating a nonzero class of `Coker(d_M)`.** If a homogeneous `x ∈ M^n` is not
a coboundary then `x` is not in the image of `d : M^{n-1} → M^n`, so `ℚ/ℤ` separates its class in
the quotient of `M^n` by that image: there is a character of `M^n` vanishing on `d (M^{n-1})` and
not on `x`. -/
theorem exists_separating_char (M : DifferentialGradedModule A) {n : ℤ} {x : M.M}
    (hx : x ∈ M.grading n) (hnot : ∀ y : M.M, M.d y ≠ x) :
    ∃ μ : CharacterModule (M.grading n : Type u),
      (∀ z : (M.grading (n - 1) : Type u), μ (dRestrictGrading M n z) = 0) ∧
        μ ⟨x, hx⟩ ≠ 0 := by
  classical
  have hmem : (⟨x, hx⟩ : (M.grading n : Type u)) ∉ LinearMap.range (dRestrictGrading M n) := by
    rintro ⟨z, hz⟩
    exact hnot (z : M.M) (congrArg Subtype.val hz)
  have hne : (LinearMap.range (dRestrictGrading M n)).mkQ ⟨x, hx⟩ ≠ 0 := fun h =>
    hmem ((Submodule.Quotient.mk_eq_zero _).mp h)
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hne
  refine ⟨CharacterModule.dual (LinearMap.range (dRestrictGrading M n)).mkQ c, fun z => ?_, hc⟩
  have hz : (LinearMap.range (dRestrictGrading M n)).mkQ (dRestrictGrading M n z) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ z)
  change c ((LinearMap.range (dRestrictGrading M n)).mkQ (dRestrictGrading M n z)) = 0
  rw [hz]
  exact map_zero c

/-- **The cocycle of `M^∨` separating a nonzero class of `Coker(d_M)`.** The extension by zero of
a separating character of `M^n` is a homogeneous element of `M^∨` which is killed by the dual
differential: that differential is precomposition with the signed differential of `M`, and a
character supported on `M^n` and vanishing on `d (M^{n-1})` kills every value of `d_M`. -/
theorem exists_separating_cocycle (M : DifferentialGradedModule A) {n : ℤ} {x : M.M}
    (hx : x ∈ M.grading n) (hnot : ∀ y : M.M, M.d y ≠ x) :
    ∃ (m : ℤ) (l : (dual M).M), l ∈ (dual M).grading m ∧ (dual M).d l = 0 ∧
      CharacterDual.dualChar l x ≠ 0 := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, -m = n := ⟨-n, neg_neg n⟩
  obtain ⟨μ, hμ0, hμx⟩ := exists_separating_char M hx hnot
  have hcar : CharacterDual.extendChar M m μ ∈ CharacterDual.dualCarrier M :=
    Submodule.mem_iSup_of_mem m (CharacterDual.extendChar_mem M m μ)
  have hext : ∀ (z : M.M) (hz : z ∈ M.grading (-m)),
      CharacterDual.extendChar M m μ z = μ ⟨z, hz⟩ := fun z hz => by
    rw [CharacterDual.extendChar_apply,
      show ((DirectSum.decompose M.grading z) (-m)) = ⟨z, hz⟩ from
        Subtype.ext (DirectSum.decompose_of_mem_same M.grading hz)]
  have hzero : ∀ (p : ℤ) (z : M.M), z ∈ M.grading p →
      CharacterDual.extendChar M m μ (M.d z) = 0 := by
    intro p z hz
    by_cases hp : p + 1 = -m
    · have hz' : z ∈ M.grading (-m - 1) := by rw [show -m - 1 = p by omega]; exact hz
      have hdz : M.d z ∈ M.grading (-m) := by
        rw [show (-m : ℤ) = p + 1 from hp.symm]; exact M.d_mem p z hz
      rw [hext _ hdz]
      exact hμ0 ⟨z, hz'⟩
    · exact CharacterDual.extendChar_mem M m μ (p + 1) hp _ (M.d_mem p z hz)
  have hd : CharacterDual.dualD0 M (CharacterDual.extendChar M m μ) = 0 := by
    ext y
    refine CharacterDual.induction_homogeneous (M := M)
      (p := fun z => CharacterDual.dualD0 M (CharacterDual.extendChar M m μ) z = 0) y
      (fun p z hz => ?_) (map_zero _)
      (fun z z' hz hz' => by rw [map_add, hz, hz', add_zero])
    rw [CharacterDual.dualD0_apply, CharacterDual.signedDifferential_apply_mem M hz, map_neg,
      map_zsmul, hzero p z hz, smul_zero, neg_zero]
  refine ⟨m, CharacterDual.dualOf (CharacterDual.extendChar M m μ) hcar, ?_, ?_, ?_⟩
  · exact CharacterDual.mem_dual_grading.mpr (CharacterDual.extendChar_mem M m μ)
  · exact CharacterDual.dualChar_injective ((CharacterDual.dualChar_d _).trans hd)
  · rw [CharacterDual.dualChar_dualOf, hext x hx]
    exact hμx

/-- To prove a property closed under `0` and `+` for every element of a differential graded
module it suffices to prove it for each homogeneous component, since an element is the finite
sum of those. -/
theorem induction_gradedProjection {M : DifferentialGradedModule A} {p : M.M → Prop} (x : M.M)
    (hhom : ∀ n : ℤ, p (DirectSum.gradedProjection M.grading n x)) (hzero : p 0)
    (hadd : ∀ y z, p y → p z → p (y + z)) : p x := by
  classical
  have hsum : (∑ n ∈ DFinsupp.support (DirectSum.decompose M.grading x),
      ((DirectSum.decompose M.grading x) n : M.M)) = x :=
    DirectSum.sum_support_decompose M.grading x
  rw [← hsum]
  exact Finset.sum_induction _ p hadd hzero fun n _ => hhom n

/-- **The key step of Stacks 09KT(2).** A homogeneous element of `M` whose image in
`I = (⨁ᵢ Q_{kᵢ})^∨` is a coboundary is itself a coboundary. If it were not, the separating
cocycle `l` of `M^∨` would not kill it; part (2) of Stacks 09KN gives a cocycle `q` of the cover
mapping to `l`, and the character `d_I w` kills `q` — because the differential of a graded dual
is precomposition with the signed differential, which on the homogeneous `q` is a scalar multiple
of `d q = 0`. -/
theorem exists_eq_d_of_mem_grading {M : DifferentialGradedModule A} {ι : Type u}
    [DecidableEq ι] {k : ι → ℤ} {b : ι → Bool}
    {f : DifferentialGraded.LeftModule.twoCellSum A k b ⟶ dual M}
    (hcoc : ∀ (m : ℤ) (z : (dual M).M), z ∈ (dual M).grading m → (dual M).d z = 0 →
      ∃ q : (DifferentialGraded.LeftModule.twoCellSum A k b).M,
        q ∈ (DifferentialGraded.LeftModule.twoCellSum A k b).grading m ∧
        (DifferentialGraded.LeftModule.twoCellSum A k b).d q = 0 ∧ f.toFun q = z)
    {n : ℤ} {x : M.M} (hx : x ∈ M.grading n)
    (hw : ∃ w : (Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).M,
      (Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).d w
        = (dualEval M ≫ DifferentialGraded.LeftModule.dualMap f).toFun x) :
    ∃ y : M.M, M.d y = x := by
  by_contra hcon
  obtain ⟨m, l, hlgr, hld, hlx⟩ :=
    exists_separating_cocycle M hx fun y hy => hcon ⟨y, hy⟩
  obtain ⟨q, hqgr, hqd, hqf⟩ := hcoc m l hlgr hld
  obtain ⟨w, hwd⟩ := hw
  have h1 : DifferentialGraded.LeftModule.dualChar
      ((dualEval M ≫ DifferentialGraded.LeftModule.dualMap f).toFun x) q
      = CharacterDual.dualChar l x := by
    rw [show (dualEval M ≫ DifferentialGraded.LeftModule.dualMap f).toFun x
        = (DifferentialGraded.LeftModule.dualMap f).toFun (dualEvalFun M x) from rfl,
      DifferentialGraded.LeftModule.dualChar_dualMap, dualChar_dualEvalFun,
      CharacterDual.evalChar_apply, hqf]
  have h2 : DifferentialGraded.LeftModule.dualChar
      ((Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).d w) q = 0 := by
    rw [DifferentialGraded.LeftModule.dualChar_d,
      DifferentialGraded.LeftModule.dualD0_apply,
      DifferentialGraded.LeftModule.signedDifferential,
      LinearMap.comp_apply,
      DirectSum.parity_apply_of_mem
        (DifferentialGraded.LeftModule.twoCellSum A k b).grading hqgr,
      map_zsmul, hqd, smul_zero, map_zero]
  rw [hwd] at h2
  exact hlx (h1.symm.trans h2)

/-- **Stacks 09KT.** Every right differential graded `A`-module `M` admits an injection `φ` into
the graded dual `I` of a direct sum of cells of left modules, such that
`Coker(d_M) → Coker(d_I)` is injective, and `I` sits in an admissible short exact sequence whose
two ends are the products of shifts of `A^∨`

`∏ᵢ A^∨[kᵢ]` and `∏ᵢ A^∨[kᵢ + 1]`. -/
@[stacks 09KT]
theorem exists_dual_injection (A : DifferentialGradedAlgebra R)
    (M : DifferentialGradedModule A) :
    ∃ (ι : Type u) (_ : DecidableEq ι) (k : ι → ℤ) (b : ι → Bool)
      (φ : M ⟶ Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)),
      Function.Injective φ.toFun ∧
      (∀ x : M.M,
        (∃ w : (Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).M,
          (Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).d w = φ.toFun x) →
        ∃ y : M.M, M.d y = x) ∧
      ∃ (i : productDualShifts A k ⟶ Ldual (DifferentialGraded.LeftModule.twoCellSum A k b))
        (p : Ldual (DifferentialGraded.LeftModule.twoCellSum A k b) ⟶
          productDualShifts A (fun c => k c + 1)),
        IsAdmissibleShortExact i p := by
  obtain ⟨ι, dec, k, b, f, hf, hcoc, -, j, q, hses⟩ :=
    DifferentialGraded.LeftModule.exists_cover A (dual M)
  refine ⟨ι, dec, k, b, dualEval M ≫ DifferentialGraded.LeftModule.dualMap f,
    (DifferentialGraded.LeftModule.dualMap_injective f hf).comp (dualEval_injective M), ?_, ?_⟩
  · intro x hx
    refine induction_gradedProjection (M := M) (p := fun u => ∃ y : M.M, M.d y = u) x ?_
      ⟨0, map_zero _⟩ ?_
    · intro n
      refine exists_eq_d_of_mem_grading hcoc
        (DirectSum.gradedProjection_mem M.grading n x) ?_
      obtain ⟨w, hwd⟩ := hx
      refine ⟨DirectSum.gradedProjection
        (Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).grading (n - 1) w, ?_⟩
      have hkey := LinearMap.congr_fun (DirectSum.gradedProjection_comp_of_degree_one
        (Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).grading
        (Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).d
        (Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).d_mem (n - 1)) w
      simp only [LinearMap.comp_apply, show n - 1 + 1 = n by ring] at hkey
      rw [← hkey, hwd]
      exact (DifferentialGraded.LeftModule.gradedProjection_comm M.grading
        (Ldual (DifferentialGraded.LeftModule.twoCellSum A k b)).grading
        (dualEval M ≫ DifferentialGraded.LeftModule.dualMap f).toFun
        (dualEval M ≫ DifferentialGraded.LeftModule.dualMap f).map_grading n x).symm
    · rintro u u' ⟨y, rfl⟩ ⟨y', rfl⟩
      exact ⟨y + y', map_add _ _ _⟩
  · rw [productDualShifts_succ k]
    exact ⟨DifferentialGraded.LeftModule.dualMap q, DifferentialGraded.LeftModule.dualMap j,
      DifferentialGraded.LeftModule.isAdmissibleShortExact_dualMap hses
        (DifferentialGraded.LeftModule.dualMap_exact j q hses.surjective hses.exact)⟩

end DifferentialGradedModule

end
