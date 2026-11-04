module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Enlarging a subcomplex in a single degree

Let `𝒜` be an abelian category, let `θ : K ⟶ 𝓜` be a degreewise monomorphism of cochain
complexes — so `K` is a subcomplex of `𝓜` — and let `e : E ⟶ 𝓜^{m-1}` be a map into one term of
`𝓜` which need not land in `K`. If `θ^m` is an isomorphism, then **the subobjects `K^{m-1}` and
the image of `e` span a subcomplex of `𝓜`**: replacing the single term `K^{m-1}` by the image of

`K^{m-1} ⊕ E ⟶ 𝓜^{m-1}`

and leaving every other term alone produces a complex `K'` with `K ⊆ K' ⊆ 𝓜` through which `e`
factors. No condition on `e` is needed for this: the differential carries the image of `e` into
`𝓜^m = K^m`, because `θ^m` is an isomorphism.

If moreover `K^{m-1}` and `E` are quotients of `P^{⊕r}` and `P^{⊕r'}` for an object `P` — in the
application `P` is the structure sheaf and these are finite free modules — then the enlarged term
is a quotient of `P^{⊕(r+r')}`, so the enlargement stays finitely generated.

This is the step of the proof of [Stacks, Tag 0FPV] which, in the descending induction on
pseudo-coherence, enlarges the finitely generated subcomplex `K` so that it absorbs the single
component `h^m : E^m ⟶ 𝓜^{m-1}` of a null-homotopy which does not already factor through `K`.
The source asserts in passing that the enlargement is again finitely generated; that is the last
clause below.

## Main results

* `CochainComplex.exists_enlarged_subcomplex`: **the enlargement.** For a degreewise monic
  `θ : K ⟶ 𝓜` with `θ^m` invertible, a map `e : E ⟶ 𝓜^{m-1}`, and epimorphisms onto `K^{m-1}` and
  `E` from finite sums of copies of an object `P`, there are a complex `K'`, a map `ρ : K ⟶ K'`
  and a degreewise monic `θ' : K' ⟶ 𝓜` with `ρ ≫ θ' = θ`, with `ρ` invertible in every degree
  other than `m - 1`, through which `e` factors, and whose term in degree `m - 1` is a quotient
  of the sum of the two given ones.

## Implementation notes

**No complex is defined by cases on the degree.** The enlarged complex is built as the family of
degreewise images of the maps `K^n ⊕ E ⟶ 𝓜^n` whose second component is `e` in degree `m - 1`
and zero elsewhere; the same second summand `E` is carried in *every* degree, so the terms are
given by one formula and no `eqToHom` arising from an equality of objects appears. Where the
extra summand contributes nothing — every degree other than `m - 1` — the comparison
`ρ^n : K^n ⟶ K'^n` is an isomorphism rather than an identity, which is all the statement claims.
This is the pattern of `Stacks.AlgebraicGeometry.ExtendBoundedComplex.subComplex` and of
`Stacks.Sites.ExtensionByZeroSpan.subcomplex`, with a different generating map.

**Why `θ^m` invertible and nothing else.** Lifting the differential to the generating maps asks
for a factorization of `e ≫ 𝓜.d (m-1) m` through `θ^m`, and invertibility of that one component
supplies it. The induction of [Stacks, Tag 0FPV] has `θ^n` invertible for every `n ≥ m`, but only
the single degree `m` is used here. Degreewise monicity of `θ` is used only for the invertibility
of `ρ^n` away from `m - 1`.

**The factorization of `e`.** The map `E ⟶ K'^{m-1}` is obtained from the epimorphism onto `E`
and the monomorphism `K'^{m-1} ⟶ 𝓜^{m-1}` by the lifting property every epimorphism of an
abelian category has against a monomorphism, `CategoryTheory.strongEpi_of_epi`; this is the one
place where the hypothesis that `E` is a quotient of a sum of copies of `P` is used for anything
beyond counting generators.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] Abelian.hasFiniteBiproducts

/-! ### Splitting a sum of copies of one object into two blocks -/

/-- The comparison of `P^{⊕(r+s)}` with `P^{⊕r} ⊕ P^{⊕s}`. -/
private def finAddDesc (P : A) (r s : ℕ) :
    (⨁ fun _ : Fin (r + s) => P) ⟶ (⨁ fun _ : Fin r => P) ⊞ (⨁ fun _ : Fin s => P) :=
  biproduct.desc fun i =>
    Fin.addCases (motive := fun _ : Fin (r + s) =>
        P ⟶ (⨁ fun _ : Fin r => P) ⊞ (⨁ fun _ : Fin s => P))
      (fun j => biproduct.ι (fun _ : Fin r => P) j ≫ biprod.inl)
      (fun j => biproduct.ι (fun _ : Fin s => P) j ≫ biprod.inr) i

/-- The section of `CochainComplex.finAddDesc` splitting the index set into its two blocks. -/
private def finAddSec (P : A) (r s : ℕ) :
    (⨁ fun _ : Fin r => P) ⊞ (⨁ fun _ : Fin s => P) ⟶ (⨁ fun _ : Fin (r + s) => P) :=
  biprod.desc (biproduct.desc fun j => biproduct.ι (fun _ : Fin (r + s) => P) (Fin.castAdd s j))
    (biproduct.desc fun j => biproduct.ι (fun _ : Fin (r + s) => P) (Fin.natAdd r j))

private theorem finAddSec_desc (P : A) (r s : ℕ) :
    finAddSec P r s ≫ finAddDesc P r s = 𝟙 _ := by
  refine biprod.hom_ext' _ _ ?_ ?_ <;>
    exact biproduct.hom_ext' _ _ fun j => by simp [finAddSec, finAddDesc]

private theorem epi_finAddDesc (P : A) (r s : ℕ) : Epi (finAddDesc P r s) := by
  have := finAddSec_desc P r s
  exact epi_of_epi_fac this

/-! ### The generating maps of the enlarged complex -/

variable {K M : CochainComplex A ℤ}

/-- The second component of the generating map of the enlarged complex: the given map in the
degree being enlarged, and zero in every other degree. -/
private def enlTau {G : A} (k : ℤ) (ee : G ⟶ M.X k) (n : ℤ) : G ⟶ M.X n :=
  if h : k = n then ee ≫ (M.XIsoOfEq h).hom else 0

private theorem enlTau_self {G : A} (k : ℤ) (ee : G ⟶ M.X k) : enlTau k ee k = ee := by
  simp [enlTau]

private theorem enlTau_of_ne {G : A} (k : ℤ) (ee : G ⟶ M.X k) (n : ℤ) (h : k ≠ n) :
    enlTau k ee n = 0 := dif_neg h

/-- **The generating map of the enlarged complex in degree `n`**: `K^n ⊕ G ⟶ 𝓜^n`, the inclusion
of `K^n` on the first summand and the prescribed map on the second. -/
private def enlGen (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) (n : ℤ) :
    (K.X n ⊞ G) ⟶ M.X n :=
  biprod.desc (θ.f n) (enlTau k ee n)

private theorem enlGen_inl (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) (n : ℤ) :
    biprod.inl ≫ enlGen θ k ee n = θ.f n := biprod.inl_desc _ _

private theorem enlGen_inr (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) (n : ℤ) :
    biprod.inr ≫ enlGen θ k ee n = enlTau k ee n := biprod.inr_desc _ _

/-- The factorization of the inclusion of `K^n` through the image of the generating map. -/
private theorem enlargeρ_fac (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) (n : ℤ) :
    (biprod.inl ≫ factorThruImage (enlGen θ k ee n)) ≫ image.ι (enlGen θ k ee n) = θ.f n := by
  rw [Category.assoc, image.fac, enlGen_inl]

/-- The lift of the differential of `𝓜` on the second summand: the prescribed map followed by the
differential lands in `K^{k+1}`, because `θ^{k+1}` is invertible. -/
private def enlLift (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))] (n : ℤ) :
    G ⟶ K.X (n + 1) :=
  if h : k = n then
    ee ≫ M.d k (k + 1) ≫ inv (θ.f (k + 1)) ≫ (K.XIsoOfEq (by rw [h])).hom
  else 0

private theorem enlLift_comp (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k)
    [IsIso (θ.f (k + 1))] (n : ℤ) :
    enlLift θ k ee n ≫ θ.f (n + 1) = enlTau k ee n ≫ M.d n (n + 1) := by
  by_cases h : k = n
  · subst h
    simp [enlLift, enlTau]
  · simp [enlLift, enlTau, h]

/-- **The lift of the differential of `𝓜` to the generating maps.** -/
private def enlD (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))] (n : ℤ) :
    (K.X n ⊞ G) ⟶ (K.X (n + 1) ⊞ G) :=
  biprod.desc (K.d n (n + 1) ≫ biprod.inl) (enlLift θ k ee n ≫ biprod.inl)

private theorem enlD_inl (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))]
    (n : ℤ) : biprod.inl ≫ enlD θ k ee n = K.d n (n + 1) ≫ biprod.inl := biprod.inl_desc _ _

private theorem enlD_inr (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))]
    (n : ℤ) : biprod.inr ≫ enlD θ k ee n = enlLift θ k ee n ≫ biprod.inl := biprod.inr_desc _ _

private theorem enlD_gen (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))]
    (n : ℤ) :
    enlD θ k ee n ≫ enlGen θ k ee (n + 1) = enlGen θ k ee n ≫ M.d n (n + 1) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [← Category.assoc, enlD_inl, Category.assoc, enlGen_inl, ← Category.assoc, enlGen_inl]
    exact (θ.comm n (n + 1)).symm
  · rw [← Category.assoc, enlD_inr, Category.assoc, enlGen_inl, ← Category.assoc, enlGen_inr]
    exact enlLift_comp θ k ee n

/-! ### The enlarged complex -/

/-- The differential of the enlarged complex, induced on the images by the lift. -/
private def enlDimg (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))] (n : ℤ) :
    image (enlGen θ k ee n) ⟶ image (enlGen θ k ee (n + 1)) :=
  image.map (Arrow.homMk' (enlD θ k ee n) (M.d n (n + 1)) (enlD_gen θ k ee n))

private theorem enlDimg_ι (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))]
    (n : ℤ) :
    enlDimg θ k ee n ≫ image.ι (enlGen θ k ee (n + 1)) =
      image.ι (enlGen θ k ee n) ≫ M.d n (n + 1) :=
  image.map_homMk'_ι _

private theorem enlDimg_comp (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))]
    (n : ℤ) : enlDimg θ k ee n ≫ enlDimg θ k ee (n + 1) = 0 := by
  rw [← cancel_mono (image.ι (enlGen θ k ee (n + 1 + 1))), Category.assoc, enlDimg_ι,
    ← Category.assoc, enlDimg_ι, Category.assoc, HomologicalComplex.d_comp_d, comp_zero,
    zero_comp]

/-- **The enlarged complex**: in degree `n` the image of `K^n ⊕ G ⟶ 𝓜^n`. -/
private def enlarge (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))] :
    CochainComplex A ℤ :=
  CochainComplex.of (fun n => image (enlGen θ k ee n)) (enlDimg θ k ee) (enlDimg_comp θ k ee)

private theorem enlarge_d (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))]
    (n : ℤ) : (enlarge θ k ee).d n (n + 1) = enlDimg θ k ee n :=
  CochainComplex.of_d (fun n => image (enlGen θ k ee n)) (enlDimg θ k ee) n

/-- **The inclusion of the enlarged complex into `𝓜`.** -/
private def enlargeι (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))] :
    enlarge θ k ee ⟶ M where
  f n := image.ι (enlGen θ k ee n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [enlarge_d]
    exact (enlDimg_ι θ k ee i).symm

private instance mono_enlargeι_f (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k)
    [IsIso (θ.f (k + 1))] (n : ℤ) : Mono ((enlargeι θ k ee).f n) :=
  inferInstanceAs (Mono (image.ι (enlGen θ k ee n)))

/-- **The comparison of `K` with the enlarged complex.** -/
private def enlargeρ (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))] :
    K ⟶ enlarge θ k ee where
  f n := biprod.inl ≫ factorThruImage (enlGen θ k ee n)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    rw [enlarge_d]
    change (biprod.inl ≫ factorThruImage (enlGen θ k ee i)) ≫ enlDimg θ k ee i =
      K.d i (i + 1) ≫ (biprod.inl ≫ factorThruImage (enlGen θ k ee (i + 1)))
    refine (cancel_mono (image.ι (enlGen θ k ee (i + 1)))).1 ?_
    rw [Category.assoc, enlDimg_ι, ← Category.assoc, enlargeρ_fac, Category.assoc, enlargeρ_fac]
    exact θ.comm i (i + 1)

private theorem enlargeρ_ι (θ : K ⟶ M) {G : A} (k : ℤ) (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))]
    (n : ℤ) : (enlargeρ θ k ee).f n ≫ (enlargeι θ k ee).f n = θ.f n :=
  enlargeρ_fac θ k ee n

private theorem isIso_enlargeρ_f (θ : K ⟶ M) (hθ : ∀ n, Mono (θ.f n)) {G : A} (k : ℤ)
    (ee : G ⟶ M.X k) [IsIso (θ.f (k + 1))] (n : ℤ) (hn : k ≠ n) :
    IsIso ((enlargeρ θ k ee).f n) := by
  have := hθ n
  have : Mono ((enlargeρ θ k ee).f n) := mono_of_mono_fac (enlargeρ_ι θ k ee n)
  have hgen : enlGen θ k ee n = biprod.fst ≫ θ.f n := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [enlGen_inl, ← Category.assoc, biprod.inl_fst, Category.id_comp]
    · rw [enlGen_inr, enlTau_of_ne k ee n hn, ← Category.assoc, biprod.inr_fst, zero_comp]
  have hfst : (biprod.fst : K.X n ⊞ G ⟶ K.X n) ≫
      (biprod.inl ≫ factorThruImage (enlGen θ k ee n)) = factorThruImage (enlGen θ k ee n) := by
    refine (cancel_mono (image.ι (enlGen θ k ee n))).1 ?_
    rw [Category.assoc, enlargeρ_fac, image.fac, hgen]
  have hcomp : Epi ((biprod.fst : K.X n ⊞ G ⟶ K.X n) ≫
      (biprod.inl ≫ factorThruImage (enlGen θ k ee n))) := by
    rw [hfst]; infer_instance
  have : Epi ((enlargeρ θ k ee).f n) := 
    epi_of_epi (biprod.fst : K.X n ⊞ G ⟶ K.X n)
      (biprod.inl ≫ factorThruImage (enlGen θ k ee n))
  exact isIso_of_mono_of_epi _

/-! ### The statement -/

/-- **Enlarging a subcomplex at one degree so that it absorbs a prescribed map.**

Let `θ : K ⟶ 𝓜` be a degreewise monomorphism of cochain complexes in an abelian category whose
component in degree `m` is an isomorphism, let `e : Em ⟶ 𝓜^{m-1}` be any map, and let
`q : P^{⊕r} ⟶ K^{m-1}` and `qE : P^{⊕r'} ⟶ Em` be epimorphisms. Then there are a complex `K'`,
a map `ρ : K ⟶ K'` and a degreewise monomorphism `θ' : K' ⟶ 𝓜` with `ρ ≫ θ' = θ` whose
comparison `ρ` is an isomorphism in every degree other than `m - 1`, such that `e` factors
through `θ'^{m-1}` and `K'^{m-1}` is a quotient of `P^{⊕(r+r')}`.

In other words `K'` is the subcomplex of `𝓜` spanned by `K` and by the image of `e`; it differs
from `K` only in degree `m - 1`, and it is again finitely generated there. -/
theorem exists_enlarged_subcomplex (θ : K ⟶ M) (hθ : ∀ n, Mono (θ.f n)) (m : ℤ)
    (hm : IsIso (θ.f m)) {Em P : A} (e : Em ⟶ M.X (m - 1)) {r rE : ℕ}
    (q : (⨁ fun _ : Fin r => P) ⟶ K.X (m - 1)) (hq : Epi q)
    (qE : (⨁ fun _ : Fin rE => P) ⟶ Em) (hqE : Epi qE) :
    ∃ (K' : CochainComplex A ℤ) (ρ : K ⟶ K') (θ' : K' ⟶ M),
      (∀ n, Mono (θ'.f n)) ∧ ρ ≫ θ' = θ ∧ (∀ n, n ≠ m - 1 → IsIso (ρ.f n)) ∧
        (∃ t : Em ⟶ K'.X (m - 1), t ≫ θ'.f (m - 1) = e) ∧
        ∃ q' : (⨁ fun _ : Fin (r + rE) => P) ⟶ K'.X (m - 1), Epi q' := by
  have := hq
  have := hqE
  have : IsIso (θ.f (m - 1 + 1)) := by
    have h : m - 1 + 1 = m := by omega
    rw [h]; exact hm
  refine ⟨enlarge θ (m - 1) (qE ≫ e), enlargeρ θ (m - 1) (qE ≫ e),
    enlargeι θ (m - 1) (qE ≫ e), fun n => inferInstanceAs (Mono (image.ι _)), ?_,
    fun n hn => isIso_enlargeρ_f θ hθ (m - 1) (qE ≫ e) n (Ne.symm hn), ?_, ?_⟩
  · exact HomologicalComplex.hom_ext _ _ fun n => enlargeρ_ι θ (m - 1) (qE ≫ e) n
  · have hsq : (biprod.inr ≫ factorThruImage (enlGen θ (m - 1) (qE ≫ e) (m - 1))) ≫
        image.ι (enlGen θ (m - 1) (qE ≫ e) (m - 1)) = qE ≫ e := by
      rw [Category.assoc, image.fac, enlGen_inr, enlTau_self]
    have : StrongEpi qE := strongEpi_of_epi qE
    exact ⟨(CommSq.mk hsq).lift, (CommSq.mk hsq).fac_right⟩
  · have hepi : Epi (finAddDesc P r rE ≫ biprod.map q (𝟙 (⨁ fun _ : Fin rE => P)) ≫
        factorThruImage (enlGen θ (m - 1) (qE ≫ e) (m - 1))) := by
      have := epi_finAddDesc P r rE
      infer_instance
    exact ⟨_, hepi⟩

end CochainComplex

end
