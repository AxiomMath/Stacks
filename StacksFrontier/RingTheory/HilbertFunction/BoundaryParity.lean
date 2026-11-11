module

public import StacksFrontier.RingTheory.HilbertFunction.AdmissibleModule
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.Module

/-!
# Parity of Hilbert functions of modules killed by sums of two squares

Let `k` be a field in which `-1` is not a square and let `A` be an admissible graded module
over `S = k[X_0, …, X_{d-1}]`. Fix indices `w` and `u i, v i` for `i < r`. Suppose that
`X_w` acts as `0` on `A`, that `X_{u i}^2 + X_{v i}^2` acts as `0` for every `i`, and that every
variable other than `w, u i, v i` acts as `0`. Then `dim_k A_n` is even for all large `n`.

The proof is by induction on the set of pairs `(u i, v i)` which may act nontrivially. For one
such pair `(u, v)` put `T = ker(v^j)` for `j` large (an ascending chain of graded submodules
of a Noetherian module). On `N = A/T` multiplication by `v` is injective, and on
`W = vN + uN` the rule `J (v a + u b) = u a - v b` is a well defined degree preserving
`k`-linear map with `J^2 = -1`; hence every `W_n` is even dimensional. The quotients `N/W`,
and the subquotients of `T` cut out by `ker v^m` and by multiplication by `u`, are killed by
both `u` and `v`, so the induction hypothesis applies to them.

We work throughout with *graded families*: families `F n ≤ A_n` of `k`-subspaces stable
under the variables. A pair `P ≤ Q` of graded families stands for the graded subquotient
`Q/P`, and `dim (Q/P)_n ≡ dim Q_n + dim P_n (mod 2)`, so parities add along chains without
forming quotient modules.

## Main definitions

* `AdmissibleGradedModule.IsGradedFamily`: a family of subspaces `F n ≤ A_n` stable under
  multiplication by the variables.
* `AdmissibleGradedModule.SMulMapsTo`: `p • Q_n ⊆ P_{n+e}` for all `n`.
* `AdmissibleGradedModule.vTorsion`: the elements `x ∈ Q_n` with `X_i^j • x ∈ P_{n+j}`.

## Main results

* `even_finrank_of_comp_self_eq_neg`: if `-1` is not a square in `K`, a finite dimensional
  `K`-space carrying an endomorphism `J` with `J ∘ J = -1` has even dimension.
* `AdmissibleGradedModule.eventually_even_finrank_iff_of_pairs`: the inductive statement for
  graded subquotients.
* `AdmissibleGradedModule.eventually_even_finrank_mgr` and
  `AdmissibleGradedModule.eventually_even_hilb`: the evenness lemma.
-/

@[expose] public section

open Module

namespace Stacks.HilbertFunction.PolynomialQuotient

/-! ### Linear algebra: endomorphisms squaring to `-1` -/

/-- If `-1` is not a square in the field `K`, then a finite dimensional `K`-vector space with an
endomorphism `J` satisfying `J (J x) = -x` is even dimensional: `det(J)^2 = (-1)^dim`. -/
theorem even_finrank_of_comp_self_eq_neg {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hK : ¬ IsSquare (-1 : K)) (J : V →ₗ[K] V)
    (hJ : ∀ x, J (J x) = -x) : Even (finrank K V) := by
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have h1 : J * J = (-1 : K) • (LinearMap.id : V →ₗ[K] V) := by
    ext x
    rw [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply, neg_one_smul, hJ]
  have h2 : LinearMap.det (J * J) = -1 := by
    rw [h1, LinearMap.det_smul, LinearMap.det_id, mul_one, hodd.neg_one_pow]
  exact hK ⟨LinearMap.det J, by rw [← h2, map_mul]⟩

/-- Let `Φ : V → W` be linear with `V` finite dimensional, `T ≤ W` finite dimensional, and
`J : V → V` with `J ∘ J = -1` preserving `Φ⁻¹(T)`. If `-1` is not a square in `K`, then
`dim (T + Φ(V)) ≡ dim T (mod 2)`: indeed `dim (T + Φ V) - dim T = dim V - dim Φ⁻¹(T)`, and
both `V` and `Φ⁻¹(T)` carry `J`. -/
theorem even_finrank_sup_range_add_finrank {K V W : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (hK : ¬ IsSquare (-1 : K)) (Φ : V →ₗ[K] W) (T : Submodule K W) [FiniteDimensional K T]
    (J : V →ₗ[K] V) (hJ : ∀ x, J (J x) = -x) (hJT : ∀ x, Φ x ∈ T → Φ (J x) ∈ T) :
    Even (finrank K ↥(T ⊔ LinearMap.range Φ) + finrank K ↥T) := by
  have hJK : ∀ x ∈ T.comap Φ, J x ∈ T.comap Φ := fun x hx => hJT x hx
  have hevV : Even (finrank K V) := even_finrank_of_comp_self_eq_neg hK J hJ
  have hevK : Even (finrank K ↥(T.comap Φ)) := by
    refine even_finrank_of_comp_self_eq_neg hK (J.restrict hJK) fun x => ?_
    apply Subtype.ext
    exact hJ (x : V)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq T (LinearMap.range Φ)
  have h2 := LinearMap.finrank_range_add_finrank_ker Φ
  have h3 := LinearMap.finrank_range_add_finrank_ker (Φ ∘ₗ (T.comap Φ).subtype)
  have h4 : LinearMap.range (Φ ∘ₗ (T.comap Φ).subtype) = T ⊓ LinearMap.range Φ := by
    rw [LinearMap.range_comp, Submodule.range_subtype, Submodule.map_comap_eq, inf_comm]
  have hle : LinearMap.ker Φ ≤ T.comap Φ := fun x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker.mp hx]
    exact T.zero_mem
  have h5 : finrank K ↥(LinearMap.ker (Φ ∘ₗ (T.comap Φ).subtype)) =
      finrank K ↥(LinearMap.ker Φ) := by
    rw [LinearMap.ker_comp]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  rw [h4, h5] at h3
  rw [Nat.even_iff] at hevV hevK ⊢
  omega

/-- The rotation `(a, b) ↦ (-b, a)` of `V × V`; it squares to `-1`. -/
def prodRotation (K V : Type*) [Ring K] [AddCommGroup V] [Module K V] :
    (V × V) →ₗ[K] (V × V) :=
  LinearMap.prod (-(LinearMap.snd K V V)) (LinearMap.fst K V V)

/-- `prodRotation` sends `(a, b)` to `(-b, a)`. -/
theorem prodRotation_apply {K V : Type*} [Ring K] [AddCommGroup V] [Module K V] (a b : V) :
    prodRotation K V (a, b) = (-b, a) :=
  rfl

/-- `prodRotation` squares to `-1`. -/
theorem prodRotation_prodRotation {K V : Type*} [Ring K] [AddCommGroup V] [Module K V]
    (x : V × V) : prodRotation K V (prodRotation K V x) = -x := by
  obtain ⟨a, b⟩ := x
  rfl

variable {k : Type*} [Field k] {d : ℕ}

namespace AdmissibleGradedModule

/-! ### Graded families -/

section Defs

variable (A : AdmissibleGradedModule k d)

/-- Multiplication by `p : k[X]` on an admissible graded module, as a `k`-linear map. -/
noncomputable def smulK (p : MvPolynomial (Fin d) k) : A.M →ₗ[k] A.M :=
  (LinearMap.lsmul (MvPolynomial (Fin d) k) A.M p).restrictScalars k

/-- A **graded family** of an admissible graded module `A`: subspaces `F n ≤ A_n` with
`X_i • F n ⊆ F (n + 1)` for every variable. It stands for the graded submodule `⊕ F n`. -/
structure IsGradedFamily (F : ℕ → Submodule k A.M) : Prop where
  /-- each member lies in the corresponding graded piece -/
  le_mgr : ∀ n, F n ≤ A.Mgr n
  /-- the variables raise the index by one -/
  smul_mem : ∀ (i : Fin d) (n : ℕ) (x : A.M), x ∈ F n →
    (MvPolynomial.X i : MvPolynomial (Fin d) k) • x ∈ F (n + 1)

/-- `p • Q n ⊆ P (n + e)` for all `n`: for graded families `P ≤ Q`, multiplication by `p`
(homogeneous of degree `e`) acts as zero on the graded subquotient `Q / P`. -/
def SMulMapsTo (P Q : ℕ → Submodule k A.M) (p : MvPolynomial (Fin d) k) (e : ℕ) : Prop :=
  ∀ (n : ℕ) (x : A.M), x ∈ Q n → p • x ∈ P (n + e)

/-- The image of a family under multiplication by the variable `X_i`, shifted by one:
`varImage F i 0 = 0` and `varImage F i (n + 1) = X_i • F n`. -/
noncomputable def varImage (F : ℕ → Submodule k A.M) (i : Fin d) : ℕ → Submodule k A.M
  | 0 => ⊥
  | n + 1 => (F n).map (A.smulK (MvPolynomial.X i))

/-- The family `m ↦ Q m` for `m ≤ N` and `m ↦ P m` for `m > N`. -/
def truncFamily (P Q : ℕ → Submodule k A.M) (N m : ℕ) : Submodule k A.M :=
  if m ≤ N then Q m else P m

/-- The `X_i^j`-torsion of `Q` modulo `P`: the elements `x ∈ Q n` with `X_i^j • x ∈ P (n + j)`.
-/
noncomputable def vTorsion (P Q : ℕ → Submodule k A.M) (i : Fin d) (j n : ℕ) :
    Submodule k A.M :=
  Q n ⊓ (P (n + j)).comap (A.smulK ((MvPolynomial.X i : MvPolynomial (Fin d) k) ^ j))

/-- The pair map `(a, b) ↦ X_v • a + X_u • b` on `Q × Q`. -/
noncomputable def pairMap (Q : Submodule k A.M) (iv iu : Fin d) : (↥Q × ↥Q) →ₗ[k] A.M :=
  ((A.smulK (MvPolynomial.X iv)) ∘ₗ Q.subtype).coprod ((A.smulK (MvPolynomial.X iu)) ∘ₗ Q.subtype)

/-- The `k`-submodule `D`, closed under the variables, viewed as a `k[X]`-submodule. -/
noncomputable def toSubmoduleOfXSMul (D : Submodule k A.M)
    (hD : ∀ (i : Fin d) (x : A.M), x ∈ D → (MvPolynomial.X i : MvPolynomial (Fin d) k) • x ∈ D)
    : Submodule (MvPolynomial (Fin d) k) A.M where
  carrier := D
  add_mem' := D.add_mem
  zero_mem' := D.zero_mem
  smul_mem' c x hx := by
    induction c using MvPolynomial.induction_on generalizing x with
    | C a =>
      change (MvPolynomial.C a : MvPolynomial (Fin d) k) • x ∈ D
      rw [MvPolynomial.C_eq_smul_one, smul_assoc, one_smul]
      exact D.smul_mem a hx
    | add p q hp hq =>
      change (p + q) • x ∈ D
      rw [add_smul]
      exact D.add_mem (hp x hx) (hq x hx)
    | mul_X p i hp =>
      change (p * MvPolynomial.X i) • x ∈ D
      rw [mul_smul]
      exact hp _ (hD i x hx)

end Defs

variable {A : AdmissibleGradedModule k d}

/-- `smulK p` is multiplication by `p`. -/
theorem smulK_apply (p : MvPolynomial (Fin d) k) (x : A.M) : A.smulK p x = p • x :=
  rfl

/-- Membership in `varImage F i (n + 1) = X_i • F n`. -/
theorem mem_varImage_succ {F : ℕ → Submodule k A.M} {i : Fin d} {n : ℕ} {x : A.M} :
    x ∈ A.varImage F i (n + 1) ↔
      ∃ y ∈ F n, (MvPolynomial.X i : MvPolynomial (Fin d) k) • y = x := by
  exact Iff.rfl

/-- Membership in the torsion family `vTorsion P Q i j`. -/
theorem mem_vTorsion {P Q : ℕ → Submodule k A.M} {i : Fin d} {j n : ℕ} {x : A.M} :
    x ∈ A.vTorsion P Q i j n ↔
      x ∈ Q n ∧ (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ j • x ∈ P (n + j) := by
  exact Iff.rfl

/-- Membership in `toSubmoduleOfXSMul D hD` is membership in `D`. -/
theorem mem_toSubmoduleOfXSMul {D : Submodule k A.M}
    {hD : ∀ (i : Fin d) (x : A.M), x ∈ D → (MvPolynomial.X i : MvPolynomial (Fin d) k) • x ∈ D}
    {x : A.M} : x ∈ A.toSubmoduleOfXSMul D hD ↔ x ∈ D :=
  Iff.rfl

/-- `pairMap Q iv iu (a, b) = X_iv • a + X_iu • b`. -/
theorem pairMap_apply (Q : Submodule k A.M) (iv iu : Fin d) (a b : ↥Q) :
    A.pairMap Q iv iu (a, b) =
      (MvPolynomial.X iv : MvPolynomial (Fin d) k) • (a : A.M) +
        (MvPolynomial.X iu : MvPolynomial (Fin d) k) • (b : A.M) :=
  rfl

/-- The range of `pairMap Q iv iu` is `X_iv • Q + X_iu • Q`. -/
theorem range_pairMap (Q : Submodule k A.M) (iv iu : Fin d) :
    LinearMap.range (A.pairMap Q iv iu) =
      Q.map (A.smulK (MvPolynomial.X iv)) ⊔ Q.map (A.smulK (MvPolynomial.X iu)) := by
  rw [pairMap, LinearMap.range_coprod, LinearMap.range_comp, LinearMap.range_comp,
    Submodule.range_subtype]

/-- `SMulMapsTo` passes to a smaller subquotient. -/
theorem SMulMapsTo.mono {P Q P' Q' : ℕ → Submodule k A.M} {p : MvPolynomial (Fin d) k}
    {e : ℕ} (h : A.SMulMapsTo P Q p e) (hP : ∀ n, P n ≤ P' n) (hQ : ∀ n, Q' n ≤ Q n) :
    A.SMulMapsTo P' Q' p e := by
  intro n x hx
  exact hP _ (h n x (hQ n hx))

/-- A power `X_i ^ j` raises the index of a graded family by `j`. -/
theorem IsGradedFamily.pow_smul_mem {F : ℕ → Submodule k A.M} (hF : A.IsGradedFamily F)
    (i : Fin d) (j : ℕ) {n : ℕ} {x : A.M} (hx : x ∈ F n) :
    (MvPolynomial.X i : MvPolynomial (Fin d) k) ^ j • x ∈ F (n + j) := by
  induction j with
  | zero =>
    rw [pow_zero, one_smul]
    exact hx
  | succ j ih =>
    rw [pow_succ', mul_smul]
    exact hF.smul_mem i (n + j) _ ih

/-- The grading itself is a graded family. -/
theorem isGradedFamily_mgr (A : AdmissibleGradedModule k d) : A.IsGradedFamily A.Mgr :=
  ⟨fun _ => le_rfl, A.smul_mem⟩

/-- The zero family is a graded family. -/
theorem isGradedFamily_bot (A : AdmissibleGradedModule k d) :
    A.IsGradedFamily (fun _ => ⊥) where
  le_mgr _ := bot_le
  smul_mem i n x hx := by
    have hx0 : x = 0 := (Submodule.mem_bot k).mp hx
    rw [hx0, smul_zero]
    exact Submodule.zero_mem _

/-- The termwise sum of two graded families is a graded family. -/
theorem IsGradedFamily.sup {F E : ℕ → Submodule k A.M} (hF : A.IsGradedFamily F)
    (hE : A.IsGradedFamily E) : A.IsGradedFamily (fun n => F n ⊔ E n) where
  le_mgr n := sup_le (hF.le_mgr n) (hE.le_mgr n)
  smul_mem i n x hx := by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [smul_add]
    exact Submodule.add_mem_sup (hF.smul_mem i n y hy) (hE.smul_mem i n z hz)

/-- The shifted image `X_i • F` of a graded family is a graded family. -/
theorem isGradedFamily_varImage {F : ℕ → Submodule k A.M} (hF : A.IsGradedFamily F)
    (i : Fin d) : A.IsGradedFamily (A.varImage F i) where
  le_mgr n := by
    intro x hx
    cases n with
    | zero =>
      rw [(Submodule.mem_bot k).mp hx]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy, rfl⟩ := mem_varImage_succ.mp hx
      exact A.smul_mem i n y (hF.le_mgr n hy)
  smul_mem j n x hx := by
    cases n with
    | zero =>
      rw [(Submodule.mem_bot k).mp hx, smul_zero]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨y, hy, rfl⟩ := mem_varImage_succ.mp hx
      exact mem_varImage_succ.mpr ⟨_, hF.smul_mem j n y hy, smul_comm _ _ _⟩

/-- For a graded family `F`, `X_i • F (n - 1) ≤ F n`. -/
theorem IsGradedFamily.varImage_le {F : ℕ → Submodule k A.M} (hF : A.IsGradedFamily F)
    (i : Fin d) (n : ℕ) : A.varImage F i n ≤ F n := by
  intro x hx
  cases n with
  | zero =>
    rw [(Submodule.mem_bot k).mp hx]
    exact Submodule.zero_mem _
  | succ n =>
    obtain ⟨y, hy, rfl⟩ := mem_varImage_succ.mp hx
    exact hF.smul_mem i n y hy

/-! ### Homogeneity and the Noetherian property -/

/-- If `F m ≤ A_m` for all `m`, an element of `A_n` lying in `⨆ m, F m` lies in `F n`. -/
theorem mem_of_mem_iSup_of_mem_mgr {F : ℕ → Submodule k A.M} (hF : ∀ n, F n ≤ A.Mgr n)
    {n : ℕ} {x : A.M} (hx : x ∈ ⨆ m, F m) (hxn : x ∈ A.Mgr n) : x ∈ F n := by
  rw [iSup_split_single F n, Submodule.mem_sup] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hx
  have hle : (⨆ (m) (_ : m ≠ n), F m) ≤ ⨆ (m) (_ : m ≠ n), A.Mgr m :=
    iSup₂_mono fun m _ => hF m
  have hz' : z ∈ ⨆ (m) (_ : m ≠ n), A.Mgr m := hle hz
  have hzn : z ∈ A.Mgr n := by
    have hzeq : z = (y + z) - y := by abel
    rw [hzeq]
    exact Submodule.sub_mem _ hxn (hF n hy)
  have hz0 : z = 0 := (Submodule.disjoint_def.mp (iSupIndep_def.mp A.iSupIndep n)) z hzn hz'
  rw [hz0, add_zero]
  exact hy

/-- The span `⨆ n, F n` of a graded family is closed under the variables. -/
theorem IsGradedFamily.iSup_X_smul_mem {F : ℕ → Submodule k A.M} (hF : A.IsGradedFamily F)
    (i : Fin d) (x : A.M) (hx : x ∈ ⨆ n, F n) :
    (MvPolynomial.X i : MvPolynomial (Fin d) k) • x ∈ ⨆ n, F n := by
  refine Submodule.iSup_induction F
    (motive := fun y => (MvPolynomial.X i : MvPolynomial (Fin d) k) • y ∈ ⨆ n, F n) hx ?_ ?_ ?_
  · intro n y hy
    exact Submodule.mem_iSup_of_mem (n + 1) (hF.smul_mem i n y hy)
  · change (MvPolynomial.X i : MvPolynomial (Fin d) k) • (0 : A.M) ∈ ⨆ n, F n
    rw [smul_zero]
    exact Submodule.zero_mem _
  · intro y z hy hz
    show (MvPolynomial.X i : MvPolynomial (Fin d) k) • (y + z) ∈ ⨆ n, F n
    rw [smul_add]
    exact Submodule.add_mem _ hy hz

/-- An increasing sequence `F 0 ≤ F 1 ≤ …` of graded families is eventually constant: the
spans `⨆ n, F j n` form an ascending chain of submodules of the Noetherian module `A`. -/
theorem exists_stable_of_monotone (F : ℕ → ℕ → Submodule k A.M)
    (hF : ∀ j, A.IsGradedFamily (F j)) (hmono : ∀ j n, F j n ≤ F (j + 1) n) :
    ∃ J, ∀ j, J ≤ j → ∀ n, F j n ≤ F J n := by
  have : Module.Finite (MvPolynomial (Fin d) k) A.M := A.fg
  have : IsNoetherian (MvPolynomial (Fin d) k) A.M :=
    isNoetherian_of_isNoetherianRing_of_finite (MvPolynomial (Fin d) k) A.M
  have hc : Monotone fun j => A.toSubmoduleOfXSMul (⨆ n, F j n) (hF j).iSup_X_smul_mem := by
    refine monotone_nat_of_le_succ fun j => ?_
    intro x hx
    exact (iSup_mono (hmono j) : (⨆ n, F j n) ≤ ⨆ n, F (j + 1) n) hx
  obtain ⟨J, hJ⟩ := (monotone_stabilizes_iff_noetherian (R := MvPolynomial (Fin d) k)
    (M := A.M)).mpr inferInstance ⟨_, hc⟩
  refine ⟨J, fun j hj n x hx => ?_⟩
  have h1 : x ∈ A.toSubmoduleOfXSMul (⨆ n, F j n) (hF j).iSup_X_smul_mem :=
    Submodule.mem_iSup_of_mem n hx
  have h2 : A.toSubmoduleOfXSMul (⨆ n, F J n) (hF J).iSup_X_smul_mem =
      A.toSubmoduleOfXSMul (⨆ n, F j n) (hF j).iSup_X_smul_mem :=
    hJ j hj
  rw [← h2] at h1
  exact mem_of_mem_iSup_of_mem_mgr (hF J).le_mgr h1 ((hF j).le_mgr n hx)

/-- **Base case.** If every variable maps the graded family `Q` into `P ≤ Q`, then `P n = Q n`
for all large `n` (a finitely generated module killed by the irrelevant ideal is
concentrated in finitely many degrees). -/
theorem eventually_eq_of_forall_X {P Q : ℕ → Submodule k A.M} (hP : A.IsGradedFamily P)
    (hQ : A.IsGradedFamily Q) (hPQ : ∀ n, P n ≤ Q n)
    (hX : ∀ i : Fin d, A.SMulMapsTo P Q (MvPolynomial.X i) 1) :
    ∀ᶠ n in Filter.atTop, P n = Q n := by
  have hF : ∀ N, A.IsGradedFamily (A.truncFamily P Q N) := by
    intro N
    refine ⟨fun m => ?_, fun i m x hx => ?_⟩
    · change (if m ≤ N then Q m else P m) ≤ A.Mgr m
      split_ifs
      · exact hQ.le_mgr m
      · exact hP.le_mgr m
    · change (MvPolynomial.X i : MvPolynomial (Fin d) k) • x ∈
        (if m + 1 ≤ N then Q (m + 1) else P (m + 1))
      have hx' : x ∈ (if m ≤ N then Q m else P m) := hx
      have hPm : (MvPolynomial.X i : MvPolynomial (Fin d) k) • x ∈ P (m + 1) := by
        split_ifs at hx'
        · exact hX i m x hx'
        · exact hP.smul_mem i m x hx'
      split_ifs
      · exact hPQ _ hPm
      · exact hPm
  have hmono : ∀ N m, A.truncFamily P Q N m ≤ A.truncFamily P Q (N + 1) m := by
    intro N m
    change (if m ≤ N then Q m else P m) ≤ (if m ≤ N + 1 then Q m else P m)
    by_cases h1 : m ≤ N
    · simp only [ite_eq_left h1, ite_eq_left (show m ≤ N + 1 by omega), le_refl]
    · by_cases h2 : m ≤ N + 1
      · simp only [ite_eq_right h1, ite_eq_left h2]
        exact hPQ m
      · simp only [ite_eq_right h1, ite_eq_right h2, le_refl]
  obtain ⟨J, hJ⟩ := exists_stable_of_monotone (A.truncFamily P Q) hF hmono
  rw [Filter.eventually_atTop]
  refine ⟨J + 1, fun n hn => le_antisymm (hPQ n) ?_⟩
  have h1 : A.truncFamily P Q n n ≤ A.truncFamily P Q J n := hJ n (by omega) n
  have h2 : A.truncFamily P Q n n = Q n := by
    change (if n ≤ n then Q n else P n) = Q n
    exact ite_eq_left le_rfl
  have h3 : A.truncFamily P Q J n = P n := by
    change (if n ≤ J then Q n else P n) = P n
    exact ite_eq_right (by omega)
  rw [h2, h3] at h1
  exact h1

/-! ### Torsion for a power of a variable -/

/-- The torsion family lies in `Q`. -/
theorem vTorsion_le {P Q : ℕ → Submodule k A.M} {i : Fin d} {j n : ℕ} :
    A.vTorsion P Q i j n ≤ Q n :=
  fun _ hx => (mem_vTorsion.mp hx).1

/-- The torsion family contains `P`. -/
theorem le_vTorsion {P Q : ℕ → Submodule k A.M} (hP : A.IsGradedFamily P)
    (hPQ : ∀ n, P n ≤ Q n) (i : Fin d) (j n : ℕ) : P n ≤ A.vTorsion P Q i j n :=
  fun _ hx => mem_vTorsion.mpr ⟨hPQ n hx, hP.pow_smul_mem i j hx⟩

/-- The `X_i^0`-torsion of `Q` modulo `P` is `P`. -/
theorem vTorsion_zero {P Q : ℕ → Submodule k A.M} (hPQ : ∀ n, P n ≤ Q n) {i : Fin d}
    {n : ℕ} : A.vTorsion P Q i 0 n = P n := by
  apply le_antisymm
  · intro x hx
    have h := (mem_vTorsion.mp hx).2
    rw [pow_zero, one_smul] at h
    exact h
  · intro x hx
    refine mem_vTorsion.mpr ⟨hPQ n hx, ?_⟩
    rw [pow_zero, one_smul]
    exact hx

/-- The torsion family increases with the exponent. -/
theorem vTorsion_mono {P Q : ℕ → Submodule k A.M} (hP : A.IsGradedFamily P) (i : Fin d)
    (j n : ℕ) : A.vTorsion P Q i j n ≤ A.vTorsion P Q i (j + 1) n := by
  intro x hx
  rw [mem_vTorsion] at hx ⊢
  refine ⟨hx.1, ?_⟩
  rw [pow_succ', mul_smul]
  exact hP.smul_mem i (n + j) _ hx.2

/-- The torsion family is a graded family. -/
theorem isGradedFamily_vTorsion {P Q : ℕ → Submodule k A.M} (hP : A.IsGradedFamily P)
    (hQ : A.IsGradedFamily Q) (i : Fin d) (j : ℕ) :
    A.IsGradedFamily (A.vTorsion P Q i j) where
  le_mgr n := fun x hx => hQ.le_mgr n (mem_vTorsion.mp hx).1
  smul_mem l n x hx := by
    rw [mem_vTorsion] at hx ⊢
    refine ⟨hQ.smul_mem l n x hx.1, ?_⟩
    rw [smul_comm]
    have h := hP.smul_mem l (n + j) _ hx.2
    rw [show n + 1 + j = n + j + 1 by omega]
    exact h

/-- `X_i` maps the `X_i^(j+1)`-torsion into the `X_i^j`-torsion. -/
theorem X_smul_mem_vTorsion {P Q : ℕ → Submodule k A.M} (hQ : A.IsGradedFamily Q)
    {i : Fin d} {j n : ℕ} {x : A.M} (hx : x ∈ A.vTorsion P Q i (j + 1) n) :
    (MvPolynomial.X i : MvPolynomial (Fin d) k) • x ∈ A.vTorsion P Q i j (n + 1) := by
  rw [mem_vTorsion] at hx ⊢
  refine ⟨hQ.smul_mem i n x hx.1, ?_⟩
  rw [← mul_smul, ← pow_succ, show n + 1 + j = n + (j + 1) by omega]
  exact hx.2

/-! ### The rotation step -/

/-- **The rotation step.** Let `T ≤ Q` be graded families and `u = X_iu`, `v = X_iv` such
that `v a + u b ∈ T` implies `u a - v b ∈ T` for `a, b ∈ Q`. Then in every positive degree
the subquotient `(T + vQ + uQ)/T` is even dimensional. -/
theorem even_finrank_sup_varImage_add {Q T : ℕ → Submodule k A.M} (hk : ¬ IsSquare (-1 : k))
    (hQ : A.IsGradedFamily Q) (hT : A.IsGradedFamily T) (iu iv : Fin d)
    (hrot : ∀ (n : ℕ) (a b : A.M), a ∈ Q n → b ∈ Q n →
      (MvPolynomial.X iv : MvPolynomial (Fin d) k) • a +
          (MvPolynomial.X iu : MvPolynomial (Fin d) k) • b ∈ T (n + 1) →
        (MvPolynomial.X iv : MvPolynomial (Fin d) k) • (-b) +
          (MvPolynomial.X iu : MvPolynomial (Fin d) k) • a ∈ T (n + 1))
    (n : ℕ) :
    Even (finrank k ↥(T (n + 1) ⊔ (A.varImage Q iv (n + 1) ⊔ A.varImage Q iu (n + 1))) +
      finrank k ↥(T (n + 1))) := by
  have : FiniteDimensional k ↥(A.Mgr n) := A.finite n
  have : FiniteDimensional k ↥(A.Mgr (n + 1)) := A.finite (n + 1)
  have : FiniteDimensional k ↥(Q n) := Submodule.finiteDimensional_of_le (hQ.le_mgr n)
  have : FiniteDimensional k ↥(T (n + 1)) :=
    Submodule.finiteDimensional_of_le (hT.le_mgr (n + 1))
  have hJT : ∀ x, A.pairMap (Q n) iv iu x ∈ T (n + 1) →
      A.pairMap (Q n) iv iu (prodRotation k ↥(Q n) x) ∈ T (n + 1) := by
    rintro ⟨a, b⟩ h
    rw [pairMap_apply] at h
    rw [prodRotation_apply, pairMap_apply]
    exact hrot n a b a.2 b.2 h
  have key := even_finrank_sup_range_add_finrank hk (A.pairMap (Q n) iv iu) (T (n + 1))
    (prodRotation k ↥(Q n)) prodRotation_prodRotation hJT
  rw [range_pairMap] at key
  exact key

/-! ### The induction -/

section Main

variable (A)

/-- **Inductive form of the evenness lemma.** Let `-1` be a nonsquare in `k`, `u v : Fin r → Fin d`
and `s` a set of pair indices. Let `P ≤ Q` be graded families such that every variable
which is none of `u i, v i` (`i ∈ s`) maps `Q` into `P`, and `X_{u i}^2 + X_{v i}^2` maps `Q`
into `P` for `i ∈ s`. Then `dim P_n ≡ dim Q_n (mod 2)` for all large `n`. -/
theorem eventually_even_finrank_iff_of_pairs (hk : ¬ IsSquare (-1 : k)) {r : ℕ}
    (u v : Fin r → Fin d) (s : Finset (Fin r)) :
    ∀ P Q : ℕ → Submodule k A.M, A.IsGradedFamily P → A.IsGradedFamily Q →
      (∀ n, P n ≤ Q n) →
      (∀ j : Fin d, (∀ i ∈ s, j ≠ u i ∧ j ≠ v i) → A.SMulMapsTo P Q (MvPolynomial.X j) 1) →
      (∀ i ∈ s, A.SMulMapsTo P Q
        ((MvPolynomial.X (u i) : MvPolynomial (Fin d) k) ^ 2 + MvPolynomial.X (v i) ^ 2) 2) →
      ∀ᶠ n in Filter.atTop, (Even (finrank k ↥(P n)) ↔ Even (finrank k ↥(Q n))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro P Q hP hQ hPQ hvar _
    have hX : ∀ j : Fin d, A.SMulMapsTo P Q (MvPolynomial.X j) 1 :=
      fun j => hvar j (fun i hi => absurd hi (Finset.notMem_empty i))
    filter_upwards [eventually_eq_of_forall_X hP hQ hPQ hX] with n hn
    rw [hn]
  | insert a s ha ih =>
    intro P Q hP hQ hPQ hvar hpair
    -- subquotients of `Q / P` killed by both variables of the pair `a`
    have key : ∀ P' Q' : ℕ → Submodule k A.M, A.IsGradedFamily P' → A.IsGradedFamily Q' →
        (∀ n, P' n ≤ Q' n) → (∀ n, P n ≤ P' n) → (∀ n, Q' n ≤ Q n) →
        A.SMulMapsTo P' Q' (MvPolynomial.X (u a)) 1 →
        A.SMulMapsTo P' Q' (MvPolynomial.X (v a)) 1 →
        ∀ᶠ n in Filter.atTop, (Even (finrank k ↥(P' n)) ↔ Even (finrank k ↥(Q' n))) := by
      intro P' Q' hP' hQ' hPQ' hPP' hQ'Q hu hv
      refine ih P' Q' hP' hQ' hPQ' (fun j hj => ?_) (fun i hi => ?_)
      · by_cases hju : j = u a
        · rw [hju]
          exact hu
        · by_cases hjv : j = v a
          · rw [hjv]
            exact hv
          · refine (hvar j (fun i hi => ?_)).mono hPP' hQ'Q
            rcases Finset.mem_insert.mp hi with rfl | hi
            · exact ⟨hju, hjv⟩
            · exact hj i hi
      · exact (hpair i (Finset.mem_insert_of_mem hi)).mono hPP' hQ'Q
    have hpa := hpair a (Finset.mem_insert_self a s)
    have hTgr : ∀ j, A.IsGradedFamily (A.vTorsion P Q (v a) j) :=
      fun j => isGradedFamily_vTorsion hP hQ (v a) j
    -- consecutive torsion levels differ by pieces killed by both `u` and `v`
    have hstep : ∀ m, ∀ᶠ n in Filter.atTop,
        (Even (finrank k ↥(A.vTorsion P Q (v a) m n)) ↔
          Even (finrank k ↥(A.vTorsion P Q (v a) (m + 1) n))) := by
      intro m
      have hT0 := hTgr m
      have hT1 := hTgr (m + 1)
      have hmid := hT0.sup (isGradedFamily_varImage hT1 (u a))
      have hvk : ∀ n x, x ∈ A.vTorsion P Q (v a) (m + 1) n →
          (MvPolynomial.X (v a) : MvPolynomial (Fin d) k) • x ∈
            A.vTorsion P Q (v a) m (n + 1) :=
        fun n x hx => X_smul_mem_vTorsion hQ hx
      have hu2 : ∀ n x, x ∈ A.vTorsion P Q (v a) (m + 1) n →
          (MvPolynomial.X (u a) : MvPolynomial (Fin d) k) •
              (MvPolynomial.X (u a) : MvPolynomial (Fin d) k) • x ∈
            A.vTorsion P Q (v a) m (n + 2) := by
        intro n x hx
        have e1 := le_vTorsion hP hPQ (v a) m (n + 2) (hpa n x (mem_vTorsion.mp hx).1)
        have e2 := hT0.smul_mem (v a) (n + 1) _ (hvk n x hx)
        have e : (MvPolynomial.X (u a) : MvPolynomial (Fin d) k) •
              (MvPolynomial.X (u a) : MvPolynomial (Fin d) k) • x =
            ((MvPolynomial.X (u a) : MvPolynomial (Fin d) k) ^ 2 +
                MvPolynomial.X (v a) ^ 2) • x -
              (MvPolynomial.X (v a) : MvPolynomial (Fin d) k) •
                (MvPolynomial.X (v a) : MvPolynomial (Fin d) k) • x := by
          module
        rw [e]
        exact Submodule.sub_mem _ e1 e2
      have hU1 : A.SMulMapsTo (A.vTorsion P Q (v a) m)
          (fun n => A.vTorsion P Q (v a) m n ⊔ A.varImage (A.vTorsion P Q (v a) (m + 1)) (u a) n)
          (MvPolynomial.X (u a)) 1 := by
        intro n x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
        rw [smul_add]
        refine Submodule.add_mem _ (hT0.smul_mem (u a) n y hy) ?_
        cases n with
        | zero =>
          rw [(Submodule.mem_bot k).mp hz, smul_zero]
          exact Submodule.zero_mem _
        | succ n =>
          obtain ⟨z', hz', rfl⟩ := mem_varImage_succ.mp hz
          exact hu2 n z' hz'
      have hV1 : A.SMulMapsTo (A.vTorsion P Q (v a) m)
          (fun n => A.vTorsion P Q (v a) m n ⊔ A.varImage (A.vTorsion P Q (v a) (m + 1)) (u a) n)
          (MvPolynomial.X (v a)) 1 := by
        intro n x hx
        obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
        rw [smul_add]
        refine Submodule.add_mem _ (hT0.smul_mem (v a) n y hy) ?_
        cases n with
        | zero =>
          rw [(Submodule.mem_bot k).mp hz, smul_zero]
          exact Submodule.zero_mem _
        | succ n =>
          obtain ⟨z', hz', rfl⟩ := mem_varImage_succ.mp hz
          rw [smul_comm]
          exact hT0.smul_mem (u a) (n + 1) _ (hvk n z' hz')
      have hU2 : A.SMulMapsTo
          (fun n => A.vTorsion P Q (v a) m n ⊔ A.varImage (A.vTorsion P Q (v a) (m + 1)) (u a) n)
          (A.vTorsion P Q (v a) (m + 1)) (MvPolynomial.X (u a)) 1 := by
        intro n x hx
        exact Submodule.mem_sup_right (mem_varImage_succ.mpr ⟨x, hx, rfl⟩)
      have hV2 : A.SMulMapsTo
          (fun n => A.vTorsion P Q (v a) m n ⊔ A.varImage (A.vTorsion P Q (v a) (m + 1)) (u a) n)
          (A.vTorsion P Q (v a) (m + 1)) (MvPolynomial.X (v a)) 1 := by
        intro n x hx
        exact Submodule.mem_sup_left (hvk n x hx)
      have h1 := key (A.vTorsion P Q (v a) m)
        (fun n => A.vTorsion P Q (v a) m n ⊔ A.varImage (A.vTorsion P Q (v a) (m + 1)) (u a) n)
        hT0 hmid (fun n => le_sup_left) (fun n => le_vTorsion hP hPQ (v a) m n)
        (fun n => sup_le vTorsion_le (le_trans (hT1.varImage_le (u a) n) vTorsion_le)) hU1 hV1
      have h2 := key
        (fun n => A.vTorsion P Q (v a) m n ⊔ A.varImage (A.vTorsion P Q (v a) (m + 1)) (u a) n)
        (A.vTorsion P Q (v a) (m + 1)) hmid hT1
        (fun n => sup_le (vTorsion_mono hP (v a) m n) (hT1.varImage_le (u a) n))
        (fun n => le_trans (le_vTorsion hP hPQ (v a) m n) le_sup_left)
        (fun n => vTorsion_le) hU2 hV2
      filter_upwards [h1, h2] with n h1n h2n
      exact h1n.trans h2n
    have hchain : ∀ m, ∀ᶠ n in Filter.atTop,
        (Even (finrank k ↥(P n)) ↔ Even (finrank k ↥(A.vTorsion P Q (v a) m n))) := by
      intro m
      induction m with
      | zero =>
        refine Filter.Eventually.of_forall fun n => ?_
        rw [vTorsion_zero hPQ]
      | succ m ihm =>
        filter_upwards [ihm, hstep m] with n h1 h2
        exact h1.trans h2
    -- the torsion stabilizes
    obtain ⟨J, hJ⟩ := exists_stable_of_monotone (A.vTorsion P Q (v a)) hTgr
      (fun j n => vTorsion_mono hP (v a) j n)
    have hTJ := hTgr J
    -- the rotation `J (v x + u y) = u x - v y` is well defined modulo the stable torsion
    have hrot : ∀ (n : ℕ) (x y : A.M), x ∈ Q n → y ∈ Q n →
        (MvPolynomial.X (v a) : MvPolynomial (Fin d) k) • x +
            (MvPolynomial.X (u a) : MvPolynomial (Fin d) k) • y ∈
          A.vTorsion P Q (v a) J (n + 1) →
        (MvPolynomial.X (v a) : MvPolynomial (Fin d) k) • (-y) +
            (MvPolynomial.X (u a) : MvPolynomial (Fin d) k) • x ∈
          A.vTorsion P Q (v a) J (n + 1) := by
      intro n x y hx hy hxy
      refine hJ (J + 1) (Nat.le_succ J) (n + 1) ?_
      rw [mem_vTorsion] at hxy ⊢
      refine ⟨?_, ?_⟩
      · refine Submodule.add_mem _ ?_ (hQ.smul_mem _ _ _ hx)
        rw [smul_neg]
        exact Submodule.neg_mem _ (hQ.smul_mem _ _ _ hy)
      · have e : (MvPolynomial.X (v a) : MvPolynomial (Fin d) k) ^ (J + 1) •
              ((MvPolynomial.X (v a) : MvPolynomial (Fin d) k) • (-y) +
                (MvPolynomial.X (u a) : MvPolynomial (Fin d) k) • x) =
            (MvPolynomial.X (u a) : MvPolynomial (Fin d) k) •
                ((MvPolynomial.X (v a) : MvPolynomial (Fin d) k) ^ J •
                  ((MvPolynomial.X (v a) : MvPolynomial (Fin d) k) • x +
                    (MvPolynomial.X (u a) : MvPolynomial (Fin d) k) • y)) -
              (MvPolynomial.X (v a) : MvPolynomial (Fin d) k) ^ J •
                (((MvPolynomial.X (u a) : MvPolynomial (Fin d) k) ^ 2 +
                  MvPolynomial.X (v a) ^ 2) • y) := by
          module
        rw [e]
        refine Submodule.sub_mem _ ?_ ?_
        · exact hP.smul_mem (u a) _ _ hxy.2
        · rw [show n + 1 + (J + 1) = n + 2 + J by omega]
          exact hP.pow_smul_mem (v a) J (hpa n y hy)
    -- `W = T + v Q + u Q`
    have hW := hTJ.sup ((isGradedFamily_varImage hQ (v a)).sup (isGradedFamily_varImage hQ (u a)))
    have hTW : ∀ᶠ n in Filter.atTop, (Even (finrank k ↥(A.vTorsion P Q (v a) J n)) ↔
        Even (finrank k ↥(A.vTorsion P Q (v a) J n ⊔
          (A.varImage Q (v a) n ⊔ A.varImage Q (u a) n)))) := by
      rw [Filter.eventually_atTop]
      refine ⟨1, fun n hn => ?_⟩
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have h := even_finrank_sup_varImage_add hk hQ hTJ (u a) (v a) hrot m
      exact (Nat.even_add.mp h).symm
    have hWU : A.SMulMapsTo
        (fun n => A.vTorsion P Q (v a) J n ⊔ (A.varImage Q (v a) n ⊔ A.varImage Q (u a) n))
        Q (MvPolynomial.X (u a)) 1 := by
      intro n x hx
      exact Submodule.mem_sup_right (Submodule.mem_sup_right
        (mem_varImage_succ.mpr ⟨x, hx, rfl⟩))
    have hWV : A.SMulMapsTo
        (fun n => A.vTorsion P Q (v a) J n ⊔ (A.varImage Q (v a) n ⊔ A.varImage Q (u a) n))
        Q (MvPolynomial.X (v a)) 1 := by
      intro n x hx
      exact Submodule.mem_sup_right (Submodule.mem_sup_left
        (mem_varImage_succ.mpr ⟨x, hx, rfl⟩))
    have hWQ := key
      (fun n => A.vTorsion P Q (v a) J n ⊔ (A.varImage Q (v a) n ⊔ A.varImage Q (u a) n)) Q
      hW hQ
      (fun n => sup_le vTorsion_le (sup_le (hQ.varImage_le (v a) n) (hQ.varImage_le (u a) n)))
      (fun n => le_trans (le_vTorsion hP hPQ (v a) J n) le_sup_left)
      (fun n => le_rfl) hWU hWV
    filter_upwards [hchain J, hTW, hWQ] with n h1 h2 h3
    exact h1.trans (h2.trans h3)

/-- **The evenness lemma.** Let `-1` be a nonsquare in `k` (e.g. `k = ℚ`) and `A` an admissible
graded module over `k[X_0, …, X_{d-1}]`. Let `w : Fin d` and `u v : Fin r → Fin d`. If `X_w`
acts as `0`, every `X_{u i}^2 + X_{v i}^2` acts as `0`, and every variable other than
`w, u i, v i` acts as `0`, then `dim_k A_n` is even for all large `n`. -/
theorem eventually_even_finrank_mgr (hk : ¬ IsSquare (-1 : k)) {r : ℕ} (u v : Fin r → Fin d)
    (w : Fin d) (hw : ∀ x : A.M, (MvPolynomial.X w : MvPolynomial (Fin d) k) • x = 0)
    (huv : ∀ (i : Fin r) (x : A.M),
      ((MvPolynomial.X (u i) : MvPolynomial (Fin d) k) ^ 2 + MvPolynomial.X (v i) ^ 2) • x = 0)
    (hother : ∀ j : Fin d, j ≠ w → (∀ i, j ≠ u i ∧ j ≠ v i) →
      ∀ x : A.M, (MvPolynomial.X j : MvPolynomial (Fin d) k) • x = 0) :
    ∀ᶠ n in Filter.atTop, Even (finrank k ↥(A.Mgr n)) := by
  have hzero : ∀ (p : MvPolynomial (Fin d) k) (e : ℕ), (∀ x : A.M, p • x = 0) →
      A.SMulMapsTo (fun _ => ⊥) A.Mgr p e := by
    intro p e hp n x _
    rw [hp x]
    exact Submodule.zero_mem _
  have h := eventually_even_finrank_iff_of_pairs A hk u v Finset.univ (fun _ => ⊥) A.Mgr
    A.isGradedFamily_bot A.isGradedFamily_mgr (fun n => bot_le)
    (fun j hj => by
      by_cases hjw : j = w
      · rw [hjw]
        exact hzero _ 1 hw
      · exact hzero _ 1 (hother j hjw fun i => hj i (Finset.mem_univ i)))
    (fun i _ => hzero _ 2 (huv i))
  filter_upwards [h] with n hn
  have hb : Even (finrank k ↥(⊥ : Submodule k A.M)) := by
    rw [finrank_bot]
    exact Even.zero
  exact hn.mp hb

/-- **The evenness lemma**, for the Hilbert function `A.hilb`. -/
theorem eventually_even_hilb (hk : ¬ IsSquare (-1 : k)) {r : ℕ} (u v : Fin r → Fin d)
    (w : Fin d) (hw : ∀ x : A.M, (MvPolynomial.X w : MvPolynomial (Fin d) k) • x = 0)
    (huv : ∀ (i : Fin r) (x : A.M),
      ((MvPolynomial.X (u i) : MvPolynomial (Fin d) k) ^ 2 + MvPolynomial.X (v i) ^ 2) • x = 0)
    (hother : ∀ j : Fin d, j ≠ w → (∀ i, j ≠ u i ∧ j ≠ v i) →
      ∀ x : A.M, (MvPolynomial.X j : MvPolynomial (Fin d) k) • x = 0) :
    ∀ᶠ n in Filter.atTop, Even (A.hilb n) := by
  filter_upwards [eventually_even_finrank_mgr A hk u v w hw huv hother] with n hn
  exact (Int.even_coe_nat _).mpr hn

end Main

end AdmissibleGradedModule

end Stacks.HilbertFunction.PolynomialQuotient
