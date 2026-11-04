module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksFrontier.Homology.HomComplex.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The periodic resolution of `A/eA` for `e² = 0`

Let `A` be a commutative ring and `e ∈ A` an element with `e² = 0` whose annihilator is `eA`,
and put `k = A/eA`; for example `A = ℤ/4` and `e = 2`, or `A = k[ε]/(ε²)` and `e = ε`. Then the
periodic complex

`P : ⋯ --e--> A --e--> A --e--> A`

concentrated in degrees `≤ 0` is a resolution of `k` by finite free `A`-modules, and its
`A`-linear dual `Hom^•(P, A)`, the complex `A --±e--> A --±e--> ⋯` in degrees `≥ 0`, is a
resolution of `k`: the map `k ⟶ A`, `x ↦ e x`, induces a quasi-isomorphism
`k[0] ⟶ Hom^•(P, A)`. In particular `RHom_A(k, A) ≅ k[0]`.

For a ring `B` over `A` in which `e` vanishes, the complex `B ⊗_A P` has zero differentials, so
its cohomology in degree `-1`, which is `Tor_1^A(B, k)`, is `B ⊗_A A ≅ B`.

## Main definitions

* `DualNumberLike.resolution`: the resolution `P` of `A/eA`.
* `DualNumberLike.coaugmentation`: the map `(A/eA)[0] ⟶ Hom^•(P, A)`.

## Main results

* `DualNumberLike.quasiIso_coaugmentation`: it is a quasi-isomorphism.
* `DualNumberLike.resolutionIsoDual`: `P ≅ Hom^•(P, A)` in the derived category.
* `DualNumberLike.not_isZero_homology_reducedResolution`: for a nonzero ring `B` over `A` in
  which `e` vanishes, `H^{-1}(B ⊗_A P) ≠ 0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
open scoped ChangeOfRings

universe u

namespace DualNumberLike

variable {A : Type u} [CommRing A] (e : A)

/-- Multiplication by `e`. -/
def mulE : ModuleCat.of A A ⟶ ModuleCat.of A A := ModuleCat.ofHom (LinearMap.mulLeft A e)

/-- Multiplication by `e` sends `x` to `e * x`. -/
theorem mulE_apply (x : A) : (mulE e).hom x = e * x := rfl

/-- The residue module `A/eA`. -/
abbrev residue : ModuleCat.{u} A := ModuleCat.of A (A ⧸ Ideal.span {e})

/-- The augmentation `A ⟶ A/eA`. -/
def augmentation : ModuleCat.of A A ⟶ residue e :=
  ModuleCat.ofHom (Submodule.mkQ (Ideal.span {e}))

variable {e}

/-- If `e² = 0`, then multiplication by `e` composed with itself is zero. -/
theorem mulE_comp_mulE (he : e * e = 0) : mulE e ≫ mulE e = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show e * (e * x) = 0
  rw [← mul_assoc, he, zero_mul]

/-- Multiplication by `e` followed by the augmentation `A ⟶ A/eA` is zero. -/
theorem mulE_comp_augmentation : mulE e ≫ augmentation e = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show Submodule.mkQ (Ideal.span {e}) (e * x) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self e)

variable (he : e * e = 0)

/-- The periodic complex `⋯ --e--> A --e--> A`, as a chain complex indexed by `ℕ`. -/
abbrev periodic : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (fun _ => ModuleCat.of A A) (fun _ => mulE e) (fun _ => mulE_comp_mulE he)

/-- Every differential of the periodic complex is multiplication by `e`. -/
theorem periodic_d (i : ℕ) : (periodic he).d (i + 1) i = mulE e :=
  ChainComplex.of_d (fun _ : ℕ => ModuleCat.of A A) (fun _ => mulE e) i

/-- The differential of the periodic complex in degree `1` followed by the augmentation is
zero. -/
theorem periodic_d_comp_augmentation : (periodic he).d 1 0 ≫ augmentation e = 0 := by
  rw [periodic_d he 0, mulE_comp_augmentation]

/-- The `A`-module `A` is projective. -/
instance : Projective (ModuleCat.of A A) :=
  (IsProjective.iff_projective A).1 inferInstance

variable (hker : ∀ x : A, e * x = 0 → ∃ y, e * y = x)

include hker in
/-- If the annihilator of `e` is `eA`, the sequence `A --e--> A --e--> A` is exact. -/
theorem exact_mulE_mulE :
    (ShortComplex.mk (mulE e) (mulE e) (mulE_comp_mulE he)).Exact :=
  (ShortComplex.moduleCat_exact_iff _).2 hker

/-- The sequence `A --e--> A ⟶ A/eA` is exact. -/
theorem exact_mulE_augmentation :
    (ShortComplex.mk (mulE e) (augmentation e) mulE_comp_augmentation).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  change Submodule.mkQ (Ideal.span {e}) x = 0 at hx
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at hx
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, by rw [← hy, mul_comm]; rfl⟩

include hker in
/-- The augmentation of the periodic complex to `(A/eA)[0]` is a quasi-isomorphism. -/
theorem quasiIso_periodic :
    QuasiIso ((ChainComplex.toSingle₀Equiv (periodic he) (residue e)).symm
      ⟨augmentation e, periodic_d_comp_augmentation he⟩) := by
  have hπ : ((ChainComplex.toSingle₀Equiv (periodic he) (residue e)).symm
      ⟨augmentation e, periodic_d_comp_augmentation he⟩).f 0 = augmentation e :=
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _
  rw [quasiIso_iff]
  rintro (_ | i)
  · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff]
        intro x hx
        have hx' : (augmentation e).hom x = 0 := by rwa [← hπ]
        obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).1 exact_mulE_augmentation x hx'
        refine ⟨y, ?_⟩
        show ((periodic he).d 1 0).hom y = x
        rwa [periodic_d he 0]
      · show Epi (((ChainComplex.toSingle₀Equiv (periodic he) (residue e)).symm
          ⟨augmentation e, periodic_d_comp_augmentation he⟩).f 0)
        rw [hπ]
        exact (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
    · exact (periodic he).shape 0 0 (by simp)
    · exact HomologicalComplex.single_obj_d (c := ComplexShape.down ℕ) _ _ _ _
    · exact HomologicalComplex.single_obj_d (c := ComplexShape.down ℕ) _ _ _ _
  · rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _),
      HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff]
    intro x hx
    change ((periodic he).d (i + 1) i).hom x = 0 at hx
    rw [periodic_d he i] at hx
    obtain ⟨y, hy⟩ := hker x hx
    refine ⟨y, ?_⟩
    show ((periodic he).d (i + 1 + 1) (i + 1)).hom y = x
    rwa [periodic_d he (i + 1)]

/-- The periodic resolution `⋯ --e--> A --e--> A ⟶ A/eA`. -/
def resolution : ProjectiveResolution (residue e) where
  complex := periodic he
  projective := fun _ => inferInstance
  π := (ChainComplex.toSingle₀Equiv (periodic he) (residue e)).symm
    ⟨augmentation e, periodic_d_comp_augmentation he⟩
  quasiIso := quasiIso_periodic he hker

/-- The resolution as a cochain complex concentrated in degrees `≤ 0`. -/
abbrev P : CochainComplex (ModuleCat.{u} A) ℤ := (resolution he hker).cochainComplex

/-- The term of `P` in degree `n = -j` is `A`. -/
abbrev eX (n : ℤ) (j : ℕ) (h : -(j : ℤ) = n) : (P he hker).X n ≅ ModuleCat.of A A :=
  (resolution he hker).cochainComplexXIso n j h

/-- The differential of `P` from degree `-(j + 1)` to degree `-j` is multiplication by `e`, under
the identifications of both terms with `A`. -/
theorem P_d (j : ℕ) (n₁ n₂ : ℤ) (h₁ : -((j + 1 : ℕ) : ℤ) = n₁) (h₂ : -(j : ℤ) = n₂) :
    (P he hker).d n₁ n₂ = (eX he hker n₁ (j + 1) h₁).hom ≫ mulE e ≫ (eX he hker n₂ j h₂).inv := by
  rw [ProjectiveResolution.cochainComplex_d _ n₁ n₂ (j + 1) j h₁ h₂]
  show _ ≫ (periodic he).d (j + 1) j ≫ _ = _
  rw [periodic_d]

end DualNumberLike

namespace CochainComplex.HomComplex.Cochain

variable {C : Type*} [Category* C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  [HasZeroObject C] {K : CochainComplex C ℤ} {X : C}

/-- `Cochain.toSingleMk` is compatible with scalar multiplication. -/
theorem toSingleMk_smul {p q : ℤ} (r : R) (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (r • f) h = r • toSingleMk f h := by
  apply (toSingleEquiv h).injective
  rw [toSingleEquiv_toSingleMk]
  show _ = (r • toSingleMk f h).v p q h ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).hom
  rw [smul_v, toSingleMk_v, Linear.smul_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CochainComplex.HomComplex.Cochain

namespace DualNumberLike

variable {A : Type u} [CommRing A] {e : A} (he : e * e = 0)
  (hker : ∀ x : A, e * x = 0 → ∃ y, e * y = x)


/-- The dual complex `Hom^•(P, A)`. -/
abbrev dual : CochainComplex (ModuleCat.{u} A) ℤ :=
  CochainComplex.HomComplexR A (P he hker)
    ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))

/-- The differential of `dual` is the differential `δ` of the Hom complex. -/
theorem dual_d_apply (n m : ℤ)
    (z : Cochain (P he hker)
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) n) :
    ((dual he hker).d n m).hom z = δ n m z := rfl

/-- If `δ` of the cochain `toSingleMk a` vanishes, the component of `a` is a multiple of `e`. -/
private theorem exists_mul_eq_of_δ_toSingleMk_eq_zero (j : ℕ) (p d d' : ℤ) (hp : -(j : ℤ) = p)
    (hd' : d + 1 = d') (a : (P he hker).X p ⟶ ModuleCat.of A A) (h₁ : p + d = 0)
    (hz : δ d d' (Cochain.toSingleMk a h₁) = 0) :
    ∃ c, e * c = ((eX he hker p j hp).inv ≫ a).hom 1 := by
  obtain rfl : d = j := by omega
  subst hp hd'
  have h₂ : -((j : ℤ) + 1) + ((j : ℤ) + 1) = 0 := by omega
  rw [Cochain.δ_toSingleMk a h₁ _ (-((j : ℤ) + 1)) h₂, smul_eq_zero_iff_eq,
    ← Cochain.toSingleMk_zero (K := P he hker) (X := ModuleCat.of A A) _ _ _ h₂] at hz
  have hz' := congrArg (Cochain.toSingleEquiv h₂) hz
  rw [Cochain.toSingleEquiv_toSingleMk, Cochain.toSingleEquiv_toSingleMk,
    P_d he hker j _ _ (by push_cast; ring) rfl] at hz'
  have hb0 : mulE e ≫ (eX he hker (-(j : ℤ)) j rfl).inv ≫ a = 0 := by
    rw [← cancel_epi (eX he hker (-((j : ℤ) + 1)) (j + 1) (by push_cast; ring)).hom,
      comp_zero, ← hz']
    simp only [Category.assoc]
  generalize (eX he hker (-(j : ℤ)) j rfl).inv ≫ a = b at hb0 ⊢
  refine hker _ ?_
  have h := congrArg (fun φ => φ.hom 1) hb0
  change b.hom (e * 1) = 0 at h
  rw [mul_one] at h
  rw [← smul_eq_mul, ← b.hom.map_smul, smul_eq_mul, mul_one]
  exact h

/-- The dual complex `Hom^•(P, A)` vanishes in negative degrees. -/
theorem isZero_dual_X (n : ℤ) (hn : n < 0) : IsZero ((dual he hker).X n) := by
  have hP : IsZero ((P he hker).X (-n)) := (P he hker).isZero_of_isStrictlyLE 0 (-n) (by omega)
  have : Subsingleton
      (Cochain (P he hker)
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)) n) := by
    refine ⟨fun a b => (Cochain.toSingleEquiv (show -n + n = 0 by omega)).injective ?_⟩
    exact hP.eq_of_src _ _
  exact @ModuleCat.isZero_of_subsingleton _ _ ((dual he hker).X n) this

/-- The dual complex `Hom^•(P, A)` is exact in every positive degree. -/
theorem exactAt_dual (n : ℤ) (hn : 0 < n) : (dual he hker).ExactAt n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  rw [HomologicalComplex.exactAt_iff' _ (m : ℤ) ((m : ℤ) + 1) ((m : ℤ) + 2) (by simp)
    (by simp; omega), ShortComplex.moduleCat_exact_iff]
  intro z hz
  change δ ((m : ℤ) + 1) ((m : ℤ) + 2) z = 0 at hz
  have h₁ : -((m : ℤ) + 1) + ((m : ℤ) + 1) = 0 := by omega
  obtain ⟨a, rfl⟩ := Cochain.toSingleMk_surjective z (-((m : ℤ) + 1)) h₁
  obtain ⟨c, hc⟩ := exists_mul_eq_of_δ_toSingleMk_eq_zero he hker (m + 1) _ _ _
    (by push_cast; ring) (by ring) a h₁ hz
  set b := (eX he hker _ (m + 1) (by push_cast; ring)).inv ≫ a with hb
  have hbc : b = mulE e ≫ (c • 𝟙 (ModuleCat.of A A)) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    show b.hom x = c • (e * x)
    rw [smul_eq_mul, show c * (e * x) = x * (e * c) by ring, hc, ← smul_eq_mul,
      ← b.hom.map_smul, smul_eq_mul, mul_one]
  have h₃ : -(m : ℤ) + m = 0 := by omega
  refine ⟨((m : ℤ) + 1).negOnePow •
    Cochain.toSingleMk ((eX he hker (-(m : ℤ)) m rfl).hom ≫ (c • 𝟙 (ModuleCat.of A A))) h₃, ?_⟩
  show δ (m : ℤ) ((m : ℤ) + 1) _ = _
  rw [δ_units_smul, Cochain.δ_toSingleMk _ h₃ ((m : ℤ) + 1) (-((m : ℤ) + 1)) h₁, smul_smul,
    Int.units_mul_self, one_smul, P_d he hker m _ _ (by push_cast; ring) rfl]
  congr 1
  rw [hb] at hbc
  rw [← cancel_epi (eX he hker _ (m + 1) (by push_cast; ring)).inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact hbc.symm

/-- The map `A/eA ⟶ A`, `x ↦ e x`. -/
def coaugmentationA : residue e ⟶ ModuleCat.of A A :=
  ModuleCat.ofHom (Submodule.liftQ (Ideal.span {e}) (LinearMap.mulLeft A e) (by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hx
    change e * (a * e) = 0
    rw [mul_comm a e, ← mul_assoc, he, zero_mul]))

/-- `coaugmentationA` sends the class of `a` to `e * a`. -/
theorem coaugmentationA_mk (a : A) :
    (coaugmentationA he).hom (Submodule.Quotient.mk a) = e * a := rfl

/-- The map `A ⟶ Hom^0(P, A)` sending `c` to `c` times the identification `P^0 ≅ A`. -/
def toDualZero : ModuleCat.of A A ⟶ (dual he hker).X 0 :=
  ModuleCat.ofHom
    { toFun := fun c => Cochain.toSingleMk (c • (eX he hker 0 0 (by simp)).hom)
        (show (0 : ℤ) + 0 = 0 from rfl)
      map_add' := fun c d => by rw [add_smul, Cochain.toSingleMk_add]
      map_smul' := fun r c => by
        change Cochain.toSingleMk ((r * c) • _) _ = r • Cochain.toSingleMk _ _
        rw [mul_smul, Cochain.toSingleMk_smul] }

/-- `toDualZero` sends `c` to the cochain `c` times the identification `P^0 ≅ A`. -/
theorem toDualZero_apply (c : A) : (toDualZero he hker).hom c =
    Cochain.toSingleMk (c • (eX he hker 0 0 (by simp)).hom) (show (0 : ℤ) + 0 = 0 from rfl) :=
  rfl

/-- If `c * e = 0`, then `c` times multiplication by `e` is zero. -/
theorem smul_mulE_eq_zero (c : A) (hc : c * e = 0) : c • mulE e = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  show c • (e * x) = 0
  rw [smul_eq_mul, ← mul_assoc, hc, zero_mul]

/-- If `c * e = 0`, then the image of `c` under `toDualZero` is a cocycle. -/
theorem δ_toDualZero (c : A) (hc : c * e = 0) :
    δ 0 1 ((toDualZero he hker).hom c) = 0 := by
  rw [toDualZero_apply, Cochain.δ_toSingleMk _ _ 1 (-1) (by norm_num),
    P_d he hker 0 (-1) 0 (by simp) (by simp)]
  have : ((eX he hker (-1) (0 + 1) (by simp)).hom ≫ mulE e ≫ (eX he hker 0 0 (by simp)).inv) ≫
      (c • (eX he hker 0 0 (by simp)).hom) = 0 := by
    rw [Linear.comp_smul]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Linear.comp_smul, smul_mulE_eq_zero c hc, comp_zero]
  rw [this, Cochain.toSingleMk_zero, smul_zero]

/-- The degree-`0` component of the coaugmentation `A/eA ⟶ Hom^0(P, A)`. -/
def coaugmentationZero : residue e ⟶ (dual he hker).X 0 :=
  coaugmentationA he ≫ toDualZero he hker

/-- The degree-`0` coaugmentation followed by the differential of `dual` is zero. -/
theorem coaugmentationZero_comp_d (j : ℤ) (hj : (ComplexShape.up ℤ).Rel 0 j) :
    coaugmentationZero he hker ≫ (dual he hker).d 0 j = 0 := by
  obtain rfl : j = 1 := by simpa using hj.symm
  refine ModuleCat.hom_ext (LinearMap.ext fun t => ?_)
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  show δ 0 1 ((toDualZero he hker).hom ((coaugmentationA he).hom (Submodule.Quotient.mk a))) = 0
  rw [coaugmentationA_mk]
  exact δ_toDualZero he hker _ (by rw [mul_comm e a, mul_assoc, he, mul_zero])

/-- **The coaugmentation** `(A/eA)[0] ⟶ Hom^•(P, A)`, induced by `x ↦ e x`. -/
def coaugmentation :
    (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (residue e) ⟶ dual he hker :=
  HomologicalComplex.mkHomFromSingle (coaugmentationZero he hker)
    (coaugmentationZero_comp_d he hker)

include hker in
/-- If the annihilator of `e` is `eA`, the map `A/eA ⟶ A`, `x ↦ e x`, is injective. -/
theorem injective_coaugmentationA : Function.Injective (coaugmentationA he).hom := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  rw [coaugmentationA_mk] at ht
  obtain ⟨y, rfl⟩ := hker a ht
  rw [Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right y _ (Ideal.mem_span_singleton_self e)

/-- The map `toDualZero : A ⟶ Hom^0(P, A)` is injective. -/
theorem injective_toDualZero : Function.Injective (toDualZero he hker).hom := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  have h := congrArg (Cochain.toSingleEquiv (K := P he hker) (X := ModuleCat.of A A)
    (show (0 : ℤ) + 0 = 0 from rfl)) (show Cochain.toSingleMk (c • (eX he hker 0 0 (by simp)).hom)
      (show (0 : ℤ) + 0 = 0 from rfl) = 0 from hc)
  rw [Cochain.toSingleEquiv_toSingleMk, map_zero] at h
  have h1 := congrArg (fun φ => φ.hom ((eX he hker 0 0 (by simp)).inv.hom 1)) h
  change c • ((eX he hker 0 0 (by simp)).inv ≫ (eX he hker 0 0 (by simp)).hom).hom 1 = 0 at h1
  rw [Iso.inv_hom_id] at h1
  simpa using h1

include hker in
/-- **`Hom^•(P, A)` is a resolution of `A/eA`.** The coaugmentation `(A/eA)[0] ⟶ Hom^•(P, A)` is
a quasi-isomorphism. -/
theorem quasiIso_coaugmentation : QuasiIso (coaugmentation he hker) := by
  rw [quasiIso_iff]
  intro n
  obtain rfl | hn := eq_or_ne n 0
  · rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp), ShortComplex.quasiIso_iff_of_zeros]
    · have hf : (coaugmentation he hker).f 0 =
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (residue e)).hom ≫
            coaugmentationZero he hker :=
        HomologicalComplex.mkHomFromSingle_f _ _
      refine ⟨?_, ?_⟩
      · rw [ShortComplex.moduleCat_exact_iff]
        intro z hz
        change δ 0 1 z = 0 at hz
        obtain ⟨a, rfl⟩ := Cochain.toSingleMk_surjective z 0 (show (0 : ℤ) + 0 = 0 from rfl)
        obtain ⟨a₀, ha₀⟩ := exists_mul_eq_of_δ_toSingleMk_eq_zero he hker 0 _ _ _ (by simp)
          (by simp) a _ hz
        set b := (eX he hker 0 0 (by simp)).inv ≫ a with hb
        refine ⟨(HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (residue e)).inv
          (Submodule.Quotient.mk a₀), ?_⟩
        show ((coaugmentation he hker).f 0).hom _ = _
        rw [hf]
        show (coaugmentationZero he hker).hom
          (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (residue e)).inv ≫
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (residue e)).hom).hom
              (Submodule.Quotient.mk a₀)) = _
        rw [Iso.inv_hom_id]
        show (toDualZero he hker).hom ((coaugmentationA he).hom (Submodule.Quotient.mk a₀)) = _
        rw [coaugmentationA_mk, toDualZero_apply, ha₀]
        congr 1
        rw [← cancel_epi (eX he hker 0 0 (by simp)).inv, Linear.comp_smul, Iso.inv_hom_id]
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        show b.hom 1 • x = b.hom x
        rw [smul_eq_mul, mul_comm, ← smul_eq_mul, ← b.hom.map_smul, smul_eq_mul, mul_one]
      · show Mono ((coaugmentation he hker).f 0)
        rw [hf, ModuleCat.mono_iff_injective]
        exact (injective_toDualZero he hker).comp ((injective_coaugmentationA he hker).comp
          (ConcreteCategory.bijective_of_isIso
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (residue e)).hom).1)
    · exact HomologicalComplex.single_obj_d (c := ComplexShape.up ℤ) _ _ _ _
    · exact HomologicalComplex.single_obj_d (c := ComplexShape.up ℤ) _ _ _ _
    · exact (isZero_dual_X he hker (-1) (by norm_num)).eq_of_src _ _
  · rw [quasiIsoAt_iff_exactAt _ _ (HomologicalComplex.exactAt_single_obj _ _ _ _ hn)]
    rcases lt_or_gt_of_ne hn with hn | hn
    · rw [HomologicalComplex.exactAt_iff]
      exact ShortComplex.exact_of_isZero_X₂ _ (isZero_dual_X he hker n hn)
    · exact exactAt_dual he hker n hn

/-- **`RHom` into `A` of the residue module, computed on the resolution.** In the derived
category, `P ≅ Hom^•(P, A)`: both are resolutions of `A/eA`. -/
def resolutionIsoDual [HasDerivedCategory (ModuleCat.{u} A)] :
    DerivedCategory.Q.obj (P he hker) ≅ DerivedCategory.Q.obj (dual he hker) :=
  haveI : IsIso (DerivedCategory.Q.map (resolution he hker).π') :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  haveI : IsIso (DerivedCategory.Q.map (coaugmentation he hker)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (quasiIso_coaugmentation he hker)
  asIso (DerivedCategory.Q.map (resolution he hker).π') ≪≫
    asIso (DerivedCategory.Q.map (coaugmentation he hker))

variable {B : Type u} [CommRing B] (f : A →+* B) (hf : f e = 0)

include hf in
/-- If `f e = 0`, then extending scalars along `f` sends multiplication by `e` to zero. -/
theorem extendScalars_map_mulE : (ModuleCat.extendScalars f).map (mulE e) = 0 := by
  let M := (ModuleCat.restrictScalars f).obj (ModuleCat.of B B)
  refine ModuleCat.ExtendScalars.hom_ext (fun m => ?_)
  show (show ↑M from (1 : B)) ⊗ₜ[A] (e • m : ↑(ModuleCat.of A A)) = 0
  have : (e • (show ↑M from (1 : B)) : ↑M) = 0 := by
    show f e * 1 = 0
    rw [hf, zero_mul]
  rw [← TensorProduct.smul_tmul, this, TensorProduct.zero_tmul]

/-- `B ⊗_A P`, the complex computing `B ⊗^L_A A/eA`. -/
abbrev reducedResolution : CochainComplex (ModuleCat.{u} B) ℤ :=
  ((ModuleCat.extendScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj (P he hker)

include hf in
/-- If `f e = 0`, every differential of `B ⊗_A P` from degree `-(j + 1)` to `-j` is zero. -/
theorem reducedResolution_d (j : ℕ) (n₁ n₂ : ℤ) (h₁ : -((j + 1 : ℕ) : ℤ) = n₁)
    (h₂ : -(j : ℤ) = n₂) : (reducedResolution he hker f).d n₁ n₂ = 0 := by
  show (ModuleCat.extendScalars f).map ((P he hker).d n₁ n₂) = 0
  rw [P_d he hker j n₁ n₂ h₁ h₂, Functor.map_comp, Functor.map_comp, extendScalars_map_mulE f hf,
    zero_comp, comp_zero]

/-- For a nonzero ring `B`, the extension of scalars `B ⊗_A A` is nonzero. -/
theorem not_isZero_extendScalars_self [Nontrivial B] :
    ¬ IsZero ((ModuleCat.extendScalars f).obj (ModuleCat.of A A)) := by
  let M := (ModuleCat.restrictScalars f).obj (ModuleCat.of B B)
  intro h
  have h1 : ((show ↑M from (1 : B)) ⊗ₜ[A] (show ↑(ModuleCat.of A A) from (1 : A)) :
      (ModuleCat.extendScalars f).obj (ModuleCat.of A A)) = 0 :=
    (ModuleCat.isZero_iff_subsingleton.1 h).elim _ _
  have h3 : TensorProduct.rid A M ((show ↑M from (1 : B)) ⊗ₜ[A]
      (show ↑(ModuleCat.of A A) from (1 : A))) = (show ↑M from (1 : B)) :=
    (TensorProduct.rid_tmul _ _).trans (one_smul _ _)
  exact one_ne_zero (α := B)
    (h3.symm.trans ((congrArg (TensorProduct.rid A M) h1).trans (map_zero _)))

include hf in
/-- **`Tor_1^A(B, A/eA) ≠ 0`.** For a nonzero ring `B` over `A` in which `e` vanishes, the
cohomology of `B ⊗_A P` in degree `-1` is `B ⊗_A A ≅ B`, which is not zero. -/
theorem not_isZero_homology_reducedResolution [Nontrivial B] :
    ¬ IsZero ((reducedResolution he hker f).homology (-1)) := by
  intro h
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ (-2) (-1) 0 (by simp) (by simp)] at h
  have hX := h.isZero_X₂ (reducedResolution_d he hker f hf 1 (-2) (-1) (by norm_num)
    (by norm_num)) (reducedResolution_d he hker f hf 0 (-1) 0 (by norm_num) (by norm_num))
  exact not_isZero_extendScalars_self f
    (hX.of_iso ((ModuleCat.extendScalars f).mapIso (eX he hker (-1) 1 (by norm_num))).symm)

end DualNumberLike
