module

public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Quasi-isomorphisms of filtered complexes of modules

Let `K` be a cochain complex of `R`-modules. A *finite filtration* of `K` is a decreasing family
`K = F^0K ⊇ F^1K ⊇ F^2K ⊇ ⋯` of subcomplexes, given degreewise by submodules, such that the
`k`-th step vanishes in every degree `< k`. Its graded pieces `gr^kK = F^kK / F^{k+1}K` are
complexes, and a morphism of complexes respecting two such filtrations induces morphisms of the
graded pieces.

The standard comparison principle holds: **a morphism of finitely filtered complexes which is a
quasi-isomorphism on every graded piece is a quasi-isomorphism.** This is the argument that ends
the proof of [Stacks, Tag 0FUM]: the quotients `K / F^kK` form a tower

`0 ⟶ gr^kK ⟶ K / F^{k+1}K ⟶ K / F^kK ⟶ 0`

of short exact sequences of complexes, so by induction on `k` the morphism is a
quasi-isomorphism on every `K / F^kK`, and `K ⟶ K / F^kK` is an isomorphism in degrees `< k`.

## Main definitions

* `CochainComplex.ofSubmodules` and `CochainComplex.quotientOfSubmodules`: the subcomplex and the
  quotient complex attached to a family of submodules of the terms stable under the
  differentials.
* `CochainComplex.SubmoduleFiltration`: a finite decreasing filtration by subcomplexes.
* `CochainComplex.SubmoduleFiltration.quotient` and `CochainComplex.SubmoduleFiltration.graded`:
  the complexes `K / F^kK` and `gr^kK`.
* `CochainComplex.SubmoduleFiltration.gradedMap`: the morphism of graded pieces induced by a
  morphism respecting the filtrations.

## Main results

* `CochainComplex.SubmoduleFiltration.shortExact`: the sequence
  `0 ⟶ gr^kK ⟶ K / F^{k+1}K ⟶ K / F^kK ⟶ 0` is short exact.
* `CochainComplex.SubmoduleFiltration.quasiIso_of_quasiIso_gradedMap`: **a morphism of finitely
  filtered complexes inducing quasi-isomorphisms on all graded pieces is a quasi-isomorphism.**

## References

* [Stacks Project, Tag 0FUM](https://stacks.math.columbia.edu/tag/0FUM)
* [Stacks Project, Tag 012K](https://stacks.math.columbia.edu/tag/012K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {R : Type u} [Ring R]

/-! ### Subcomplexes and quotient complexes given by submodules -/

section Construction

variable (K : CochainComplex (ModuleCat.{v} R) ℤ) (F : ∀ n : ℤ, Submodule R (K.X n))
  (hF : ∀ n m : ℤ, (F n).map (K.d n m).hom ≤ F m)

/-- The subcomplex of `K` whose degree-`n` term is the submodule `F n`, for a family of
submodules carried into one another by the differentials. -/
def ofSubmodules : CochainComplex (ModuleCat.{v} R) ℤ where
  X n := ModuleCat.of R (F n)
  d n m := ModuleCat.ofHom ((K.d n m).hom.restrict fun x hx => hF n m ⟨x, hx, rfl⟩)
  shape n m h := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    change (K.d n m).hom (x : K.X n) = 0
    rw [K.shape n m h]
    rfl
  d_comp_d' i j k _ _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => Subtype.ext ?_)
    change (K.d j k).hom ((K.d i j).hom (x : K.X i)) = 0
    exact congrArg (fun g => g.hom (x : K.X i)) (K.d_comp_d i j k)

/-- The quotient complex of `K` by the family of submodules `F`, carried into one another by the
differentials. -/
def quotientOfSubmodules : CochainComplex (ModuleCat.{v} R) ℤ where
  X n := ModuleCat.of R (K.X n ⧸ F n)
  d n m := ModuleCat.ofHom ((F n).mapQ (F m) (K.d n m).hom
    (Submodule.map_le_iff_le_comap.1 (hF n m)))
  shape n m h := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk ((K.d n m).hom x) = 0
    rw [K.shape n m h]
    exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.zero_mem _)
  d_comp_d' i j k _ _ := by
    refine ModuleCat.hom_ext (Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_))
    change Submodule.Quotient.mk ((K.d j k).hom ((K.d i j).hom x)) = 0
    rw [show (K.d j k).hom ((K.d i j).hom x) = 0 from
      congrArg (fun g => g.hom x) (K.d_comp_d i j k)]
    rfl

/-- The differential of the quotient complex sends the class of `x` to the class of `d x`. -/
@[simp]
theorem quotientOfSubmodules_d_mk (n m : ℤ) (x : K.X n) :
    (K.quotientOfSubmodules F hF).d n m (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (K.d n m x) :=
  rfl

/-- The projection of `K` onto its quotient complex by `F`. -/
def toQuotientOfSubmodules : K ⟶ K.quotientOfSubmodules F hF where
  f n := ModuleCat.ofHom (F n).mkQ
  comm' n m _ := by
    ext x
    rfl

/-- The projection onto the quotient complex sends `x` to its class. -/
@[simp]
theorem toQuotientOfSubmodules_f_apply (n : ℤ) (x : K.X n) :
    (K.toQuotientOfSubmodules F hF).f n x = Submodule.Quotient.mk x :=
  rfl

variable {K F hF} {L : CochainComplex (ModuleCat.{v} R) ℤ} {G : ∀ n : ℤ, Submodule R (L.X n)}
  {hG : ∀ n m : ℤ, (G n).map (L.d n m).hom ≤ G m}

/-- The morphism of subcomplexes induced by a morphism of complexes carrying `F` into `G`. -/
def ofSubmodulesMap (φ : K ⟶ L) (hφ : ∀ n, (F n).map (φ.f n).hom ≤ G n) :
    K.ofSubmodules F hF ⟶ L.ofSubmodules G hG where
  f n := ModuleCat.ofHom ((φ.f n).hom.restrict fun x hx => hφ n ⟨x, hx, rfl⟩)
  comm' n m _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun (x : F n) => Subtype.ext ?_)
    exact congrArg (fun g => g.hom (x : K.X n)) (φ.comm n m)

/-- The morphism of quotient complexes induced by a morphism of complexes carrying `F` into
`G`. -/
def quotientOfSubmodulesMap (φ : K ⟶ L) (hφ : ∀ n, (F n).map (φ.f n).hom ≤ G n) :
    K.quotientOfSubmodules F hF ⟶ L.quotientOfSubmodules G hG where
  f n := ModuleCat.ofHom ((F n).mapQ (G n) (φ.f n).hom (Submodule.map_le_iff_le_comap.1 (hφ n)))
  comm' n m _ := by
    ext x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    exact congrArg Submodule.Quotient.mk (congrArg (fun g => g.hom x) (φ.comm n m))

/-- The induced morphism of quotient complexes sends the class of `x` to the class of `φ x`. -/
@[simp]
theorem quotientOfSubmodulesMap_f_mk (φ : K ⟶ L) (hφ : ∀ n, (F n).map (φ.f n).hom ≤ G n)
    (n : ℤ) (x : K.X n) :
    (quotientOfSubmodulesMap (hF := hF) (hG := hG) φ hφ).f n (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (φ.f n x) :=
  rfl

/-- The projections onto the quotient complexes commute with `φ` and the induced morphism of
quotient complexes. -/
@[reassoc (attr := simp)]
theorem toQuotientOfSubmodules_comp_quotientOfSubmodulesMap (φ : K ⟶ L)
    (hφ : ∀ n, (F n).map (φ.f n).hom ≤ G n) :
    K.toQuotientOfSubmodules F hF ≫ quotientOfSubmodulesMap φ hφ =
      φ ≫ L.toQuotientOfSubmodules G hG := by
  ext n x
  rfl

end Construction

/-! ### Finite filtrations -/

/-- A **finite decreasing filtration** of a cochain complex of `R`-modules by subcomplexes: steps
`F^kK^n ⊆ K^n` for `k : ℕ`, carried into one another by the differentials, decreasing in `k`,
with `F^0K = K` and `F^kK^n = 0` for `n < k`. -/
structure SubmoduleFiltration (K : CochainComplex (ModuleCat.{v} R) ℤ) where
  /-- The `k`-th step of the filtration, in degree `n`. -/
  step : ℕ → ∀ n : ℤ, Submodule R (K.X n)
  /-- Each step is a subcomplex. -/
  map_d_le : ∀ (k : ℕ) (n m : ℤ), (step k n).map (K.d n m).hom ≤ step k m
  /-- The steps decrease. -/
  step_succ_le : ∀ (k : ℕ) (n : ℤ), step (k + 1) n ≤ step k n
  /-- The zeroth step is the whole complex. -/
  step_zero : ∀ n : ℤ, step 0 n = ⊤
  /-- The `k`-th step vanishes in degrees `< k`. -/
  step_eq_bot : ∀ (k : ℕ) (n : ℤ), n < k → step k n = ⊥

namespace SubmoduleFiltration

variable {K : CochainComplex (ModuleCat.{v} R) ℤ} (F : SubmoduleFiltration K)

/-- The `k`-th step `F^kK` of the filtration, as a complex. -/
abbrev stepComplex (k : ℕ) : CochainComplex (ModuleCat.{v} R) ℤ :=
  K.ofSubmodules (F.step k) (F.map_d_le k)

/-- The quotient `K / F^kK`, as a complex. -/
abbrev quotient (k : ℕ) : CochainComplex (ModuleCat.{v} R) ℤ :=
  K.quotientOfSubmodules (F.step k) (F.map_d_le k)

/-- The `(k+1)`-st step, read inside the `k`-th one. -/
def stepIn (k : ℕ) (n : ℤ) : Submodule R ((F.stepComplex k).X n) :=
  (F.step (k + 1) n).comap (F.step k n).subtype

/-- The differentials of `F^kK` carry `F^{k+1}K` into itself. -/
theorem map_d_stepIn_le (k : ℕ) (n m : ℤ) :
    (F.stepIn k n).map ((F.stepComplex k).d n m).hom ≤ F.stepIn k m := by
  rintro _ ⟨(x : F.step k n), hx, rfl⟩
  exact F.map_d_le (k + 1) n m ⟨(x : K.X n), hx, rfl⟩

/-- The `k`-th graded piece `gr^kK = F^kK / F^{k+1}K`, as a complex. -/
abbrev graded (k : ℕ) : CochainComplex (ModuleCat.{v} R) ℤ :=
  (F.stepComplex k).quotientOfSubmodules (F.stepIn k) (F.map_d_stepIn_le k)

/-- The inclusion `gr^kK ⟶ K / F^{k+1}K`. -/
def gradedToQuotient (k : ℕ) : F.graded k ⟶ F.quotient (k + 1) where
  f n := ModuleCat.ofHom ((F.stepIn k n).mapQ (F.step (k + 1) n) (F.step k n).subtype le_rfl)
  comm' n m _ := by
    ext x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl

/-- The inclusion `gr^kK ⟶ K / F^{k+1}K` sends the class of `x ∈ F^kK` to the class of `x`. -/
@[simp]
theorem gradedToQuotient_f_mk (k : ℕ) (n : ℤ) (x : F.step k n) :
    (F.gradedToQuotient k).f n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x : K.X n) :=
  rfl

/-- The projection `K / F^{k+1}K ⟶ K / F^kK`. -/
def quotientSucc (k : ℕ) : F.quotient (k + 1) ⟶ F.quotient k where
  f n := ModuleCat.ofHom ((F.step (k + 1) n).mapQ (F.step k n) LinearMap.id
    (by simpa using F.step_succ_le k n))
  comm' n m _ := by
    ext x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl

/-- The projection `K / F^{k+1}K ⟶ K / F^kK` sends the class of `x` to the class of `x`. -/
@[simp]
theorem quotientSucc_f_mk (k : ℕ) (n : ℤ) (x : K.X n) :
    (F.quotientSucc k).f n (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  rfl

/-- The sequence `gr^kK ⟶ K / F^{k+1}K ⟶ K / F^kK`. -/
@[simps]
def shortComplex (k : ℕ) : ShortComplex (CochainComplex (ModuleCat.{v} R) ℤ) where
  X₁ := F.graded k
  X₂ := F.quotient (k + 1)
  X₃ := F.quotient k
  f := F.gradedToQuotient k
  g := F.quotientSucc k
  zero := by
    ext n x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    exact (Submodule.Quotient.mk_eq_zero _).2 x.2

/-- **The sequence `0 ⟶ gr^kK ⟶ K / F^{k+1}K ⟶ K / F^kK ⟶ 0` is short exact.** -/
theorem shortExact (k : ℕ) : (F.shortComplex k).ShortExact := by
  refine HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n => ?_
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro y hy
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk ⟨y, (Submodule.Quotient.mk_eq_zero _).1 hy⟩, rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    intro x x' hxx'
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective _ x'
    refine (Submodule.Quotient.eq _).2 ?_
    have := (Submodule.Quotient.eq _).1 hxx'
    exact this
  · rw [ModuleCat.epi_iff_surjective]
    intro y
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.Quotient.mk y, rfl⟩

/-- `K / F^0K` is zero. -/
theorem isZero_quotient_zero : IsZero (F.quotient 0) := by
  have h : ∀ n, IsZero ((F.quotient 0).X n) := fun n => by
    rw [ModuleCat.isZero_iff_subsingleton]
    exact Submodule.Quotient.subsingleton_iff.2 (F.step_zero n)
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.hom_ext _ _ fun n => (h n).eq_of_src _ _

/-- The projection `K ⟶ K / F^kK`. -/
abbrev toQuotient (k : ℕ) : K ⟶ F.quotient k :=
  K.toQuotientOfSubmodules (F.step k) (F.map_d_le k)

/-- The projection `K ⟶ K / F^kK` is bijective in every degree `< k`. -/
theorem isIso_toQuotient_f (k : ℕ) (n : ℤ) (hn : n < k) : IsIso ((F.toQuotient k).f n) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, Submodule.mkQ_surjective _⟩
  rw [← LinearMap.ker_eq_bot]
  exact (Submodule.ker_mkQ _).trans (F.step_eq_bot k n hn)

/-- The projection `K ⟶ K / F^kK` induces an isomorphism on cohomology in every degree `n` with
`n + 1 < k`. -/
theorem quasiIsoAt_toQuotient (k : ℕ) (n : ℤ) (hn : n + 1 < k) : QuasiIsoAt (F.toQuotient k) n := by
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  let ψ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{v} R) (ComplexShape.up ℤ)
      (n - 1) n (n + 1)).map (F.toQuotient k)
  have : IsIso ψ.τ₁ := F.isIso_toQuotient_f k (n - 1) (by omega)
  have : IsIso ψ.τ₂ := F.isIso_toQuotient_f k n (by omega)
  have : IsIso ψ.τ₃ := F.isIso_toQuotient_f k (n + 1) (by omega)
  have : IsIso ψ := ShortComplex.isIso_of_isIso ψ
  infer_instance

/-! ### Morphisms respecting filtrations -/

variable {M : CochainComplex (ModuleCat.{v} R) ℤ} (FM : SubmoduleFiltration M)
  (FK : SubmoduleFiltration K) (φ : M ⟶ K)
  (hφ : ∀ (k : ℕ) (n : ℤ), (FM.step k n).map (φ.f n).hom ≤ FK.step k n)

/-- The morphism `M / F^kM ⟶ K / F^kK` induced by a morphism respecting the filtrations. -/
abbrev quotientMap (k : ℕ) : FM.quotient k ⟶ FK.quotient k :=
  quotientOfSubmodulesMap φ (hφ k)

/-- The morphism `F^kM ⟶ F^kK` induced by `φ` carries `F^{k+1}M` into `F^{k+1}K`. -/
theorem map_stepIn_le (k : ℕ) (n : ℤ) :
    (FM.stepIn k n).map ((ofSubmodulesMap (hF := FM.map_d_le k) (hG := FK.map_d_le k) φ
      (hφ k)).f n).hom ≤ FK.stepIn k n := by
  rintro _ ⟨(x : FM.step k n), hx, rfl⟩
  exact hφ (k + 1) n ⟨(x : M.X n), hx, rfl⟩

/-- **The morphism `gr^kM ⟶ gr^kK` induced by a morphism respecting the filtrations.** -/
abbrev gradedMap (k : ℕ) : FM.graded k ⟶ FK.graded k :=
  quotientOfSubmodulesMap (ofSubmodulesMap φ (hφ k)) (map_stepIn_le FM FK φ hφ k)

/-- The morphism of the short exact sequences `0 ⟶ gr^k ⟶ · / F^{k+1} ⟶ · / F^k ⟶ 0` induced by
a morphism respecting the filtrations. -/
def shortComplexMap (k : ℕ) : FM.shortComplex k ⟶ FK.shortComplex k where
  τ₁ := gradedMap FM FK φ hφ k
  τ₂ := quotientMap FM FK φ hφ (k + 1)
  τ₃ := quotientMap FM FK φ hφ k
  comm₁₂ := by
    ext n x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl
  comm₂₃ := by
    ext n x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    rfl

/-- If `φ` induces quasi-isomorphisms on all graded pieces, it induces quasi-isomorphisms on all
the quotients `M / F^kM ⟶ K / F^kK`. -/
theorem quasiIso_quotientMap (h : ∀ k : ℕ, QuasiIso (gradedMap FM FK φ hφ k)) (k : ℕ) :
    QuasiIso (quotientMap FM FK φ hφ k) := by
  induction k with
  | zero =>
    have : IsIso (quotientMap FM FK φ hφ 0) :=
      ⟨⟨0, FM.isZero_quotient_zero.eq_of_src _ _, FK.isZero_quotient_zero.eq_of_src _ _⟩⟩
    infer_instance
  | succ k ih =>
    have : QuasiIso (shortComplexMap FM FK φ hφ k).τ₁ := h k
    have : QuasiIso (shortComplexMap FM FK φ hφ k).τ₃ := ih
    exact StacksDraft.TotalComplexQuasiIso.quasiIso_τ₂ (shortComplexMap FM FK φ hφ k)
      (FM.shortExact k) (FK.shortExact k)

/-- **A morphism of finitely filtered complexes inducing quasi-isomorphisms on all graded pieces
is a quasi-isomorphism.** -/
theorem quasiIso_of_quasiIso_gradedMap (h : ∀ k : ℕ, QuasiIso (gradedMap FM FK φ hφ k)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  let k : ℕ := (n + 2).toNat
  have hk : n + 1 < (k : ℤ) := by omega
  have h₁ := FM.quasiIsoAt_toQuotient k n hk
  have h₂ := FK.quasiIsoAt_toQuotient k n hk
  have h₃ : QuasiIsoAt (quotientMap FM FK φ hφ k) n :=
    (quasiIso_iff _).1 (quasiIso_quotientMap FM FK φ hφ h k) n
  have h₄ : QuasiIsoAt (FM.toQuotient k ≫ quotientMap FM FK φ hφ k) n := quasiIsoAt_comp _ _ n
  rw [toQuotientOfSubmodules_comp_quotientOfSubmodulesMap φ (hφ k)] at h₄
  exact (quasiIsoAt_iff_comp_right φ (FK.toQuotient k) n).1 h₄

end SubmoduleFiltration

end CochainComplex

end
