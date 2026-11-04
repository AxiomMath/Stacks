module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso

/-!
# Weibel's acyclic assembly lemma for double complexes bounded above

Let `A` be an abelian category and let `Z` be a double complex of `A` indexed by `ℤ × ℤ`, with
cochain conventions in both directions, which is *bounded above*: it vanishes in first degrees
`> a` and in second degrees `> b`. Such a `Z` has, in each total degree, only finitely many
nonzero terms, and this module proves the criterion of [Stacks, Tag 0133] for it: a morphism
`f : Z ⟶ Z'` of double complexes bounded above which is a quasi-isomorphism on every column
induces a quasi-isomorphism `Tot(Z) ⟶ Tot(Z')`.

Double complexes of this shape are what a projective resolution evaluated on a cosimplicial
object produces: both the resolution degree and the Moore degree are bounded above and
unbounded below.

## Main results

* `StacksDraft.TotalComplexQuasiIso.hasTotal_of_upperBound`: a double complex bounded above has
  a total complex, the coproducts defining it being finite.
* `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_columnBounds`: the criterion for a
  double complex with only finitely many nonzero columns.
* `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound`: **[Stacks, Tag 0133] for
  double complexes bounded above**, the hypothesis being on the columns.
* `StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_upperBound_flip`: the same with the
  hypothesis on the rows.

## Implementation notes

`StacksDraft.TotalComplexQuasiIso.quasiIso_total_map` is the same statement for double complexes
*bounded below*, where the induction deleting the bottom column terminates because the total
complex vanishes in low degrees. For a double complex bounded above that induction has no base
case, and the route taken here is different: with finitely many columns the induction on their
number terminates with the zero double complex, and the general case reduces to that one because
only the columns `p ≥ n - 1 - b` contribute to `H^n(Tot(Z))`, so that the inclusion of the stupid
truncation `Z^{≥ n - 1 - b} ⟶ Z` is invertible in the three total degrees which compute `H^n`.

The inductive step consumes the deletion of the bottom column exactly as the bounded below proof
does — `bottomSES`, `totalBottomSES_shortExact`, `totalBottomSESMap` and two out of three for
quasi-isomorphisms in the middle — none of which needs a bound in the second degree; what a bound
in the second degree supplies here is instead the existence of the total complexes.

## References

* [Stacks, Tag 0133]
-/

@[expose] public noncomputable section

open CategoryTheory Limits HomologicalComplex ComplexShape

namespace StacksDraft.TotalComplexQuasiIso

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-! ### Two elementary criteria -/

/-- A morphism of cochain complexes which is invertible in the degrees `n - 1`, `n` and `n + 1`
induces an isomorphism on homology in degree `n`. -/
lemma isIso_homologyMap_of_isIso_f {K L : CochainComplex A ℤ} (φ : K ⟶ L) (n : ℤ)
    (h₁ : IsIso (φ.f (n - 1))) (h₂ : IsIso (φ.f n)) (h₃ : IsIso (φ.f (n + 1))) :
    IsIso (HomologicalComplex.homologyMap φ n) := by
  rw [← quasiIsoAt_iff_isIso_homologyMap,
    quasiIsoAt_iff' φ (n - 1) n (n + 1) (by simp) (by simp)]
  have : IsIso ((HomologicalComplex.shortComplexFunctor' A (up ℤ) (n - 1) n (n + 1)).map φ) :=
    @ShortComplex.isIso_of_isIso _ _ _ _ _ _ h₁ h₂ h₃
  infer_instance

/-- A term of a double complex in a vanishing column vanishes. -/
private lemma isZero_X_X_of_isZero_X (Z : HomologicalComplex₂ A (up ℤ) (up ℤ)) {p : ℤ}
    (h : IsZero (Z.X p)) (q : ℤ) : IsZero ((Z.X p).X q) :=
  Functor.map_isZero (HomologicalComplex.eval A (up ℤ) q) h

/-- A morphism of double complexes which is invertible on every term of total degree `n` is
invertible on the total complexes in degree `n`. -/
lemma isIso_total_map_f {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (φ : Z ⟶ Z')
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)] (n : ℤ)
    (h : ∀ p q, p + q = n → IsIso ((φ.f p).f q)) :
    IsIso ((HomologicalComplex₂.total.map φ (up ℤ)).f n) := by
  refine ⟨Z'.totalDesc (fun p q hpq =>
    have := h p q hpq
    inv ((φ.f p).f q) ≫ Z.ιTotal (up ℤ) p q n hpq), ?_, ?_⟩
  · refine HomologicalComplex₂.total.hom_ext (up ℤ) (fun p q hpq => ?_)
    have := h p q hpq
    simp only [Category.comp_id, HomologicalComplex₂.ιTotal_map_assoc,
      HomologicalComplex₂.ι_totalDesc, IsIso.hom_inv_id_assoc]
  · refine HomologicalComplex₂.total.hom_ext (up ℤ) (fun p q hpq => ?_)
    have := h p q hpq
    simp only [Category.comp_id, HomologicalComplex₂.ι_totalDesc_assoc, Category.assoc,
      HomologicalComplex₂.ιTotal_map, IsIso.inv_hom_id_assoc]

/-! ### Existence of the total complex -/

/-- A double complex with only finitely many nonzero columns has a total complex: in each total
degree the coproduct defining it has finitely many nonzero terms. -/
lemma hasTotal_of_columnBounds (Z : HomologicalComplex₂ A (up ℤ) (up ℤ)) (a b : ℤ)
    (hZ : ∀ p, p < a ∨ b < p → IsZero (Z.X p)) :
    Z.HasTotal (up ℤ) := by
  apply HomologicalComplex₂.hasTotal_of_finite
  intro n
  refine Set.Finite.subset ((Set.finite_Icc a b).image (fun p => (p, n - p))) ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hpq' : p + q = n := hpq
  have hab : a ≤ p ∧ p ≤ b := by
    by_contra hc
    exact hz (isZero_X_X_of_isZero_X Z (hZ p (by omega)) q)
  exact ⟨p, hab, by simp [show n - p = q by omega]⟩

/-- **The total complex of a double complex bounded above exists**: a nonzero term `Z^{p, q}` of
total degree `n` has `n - b ≤ p ≤ a`, so the coproducts defining the total complex are finite. -/
lemma hasTotal_of_upperBound (Z : HomologicalComplex₂ A (up ℤ) (up ℤ)) (a b : ℤ)
    (hZp : ∀ p, a < p → IsZero (Z.X p)) (hZq : ∀ p q, b < q → IsZero ((Z.X p).X q)) :
    Z.HasTotal (up ℤ) := by
  apply HomologicalComplex₂.hasTotal_of_finite
  intro n
  refine Set.Finite.subset ((Set.finite_Icc (n - b) a).image (fun p => (p, n - p))) ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hpq' : p + q = n := hpq
  have h₁ : p ≤ a := by
    by_contra hc
    exact hz (isZero_X_X_of_isZero_X Z (hZp p (by omega)) q)
  have h₂ : n - b ≤ p := by
    by_contra hc
    exact hz (hZq p q (by omega))
  exact ⟨p, ⟨h₂, h₁⟩, by simp [show n - p = q by omega]⟩

/-! ### Finitely many columns -/

/-- A morphism between double complexes all of whose columns vanish is a quasi-isomorphism on
total complexes: both total complexes are zero. -/
lemma quasiIso_total_map_of_isZero {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z')
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)]
    (hZ : ∀ p, IsZero (Z.X p)) (hZ' : ∀ p, IsZero (Z'.X p)) :
    QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) := by
  have hcomp : ∀ n, IsIso ((HomologicalComplex₂.total.map f (up ℤ)).f n) := fun n =>
    isIso_of_isZero_of_isZero _
      (HomologicalComplex₂.isZero_total_X_of_isZero Z (up ℤ) n (fun p q _ =>
        isZero_X_X_of_isZero_X Z (hZ p) q))
      (HomologicalComplex₂.isZero_total_X_of_isZero Z' (up ℤ) n (fun p q _ =>
        isZero_X_X_of_isZero_X Z' (hZ' p) q))
  have : IsIso (HomologicalComplex₂.total.map f (up ℤ)) :=
    HomologicalComplex.Hom.isIso_of_components _
  infer_instance

/-- **[Stacks, Tag 0133] for double complexes with finitely many nonzero columns**: a morphism
which is a quasi-isomorphism on every column is one on total complexes. The natural number `k`
bounds the number of columns. -/
lemma quasiIso_total_map_of_columnBounds (k : ℕ)
    {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z') (a b : ℤ)
    (hk : b + 1 - a ≤ (k : ℤ))
    (hZ : ∀ p, p < a ∨ b < p → IsZero (Z.X p))
    (hZ' : ∀ p, p < a ∨ b < p → IsZero (Z'.X p))
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)]
    (hf : ∀ p, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) := by
  induction k generalizing Z Z' a b with
  | zero =>
    have hab : b < a := by push_cast at hk; omega
    exact quasiIso_total_map_of_isZero f (fun p => hZ p (by omega)) (fun p => hZ' p (by omega))
  | succ k ih =>
    by_cases hab : b < a
    · exact quasiIso_total_map_of_isZero f (fun p => hZ p (by omega)) (fun p => hZ' p (by omega))
    · have hZa : IsZero (Z.X (a - 1)) := hZ (a - 1) (Or.inl (by omega))
      have hZ'a : IsZero (Z'.X (a - 1)) := hZ' (a - 1) (Or.inl (by omega))
      have hker : ∀ (W : HomologicalComplex₂ A (up ℤ) (up ℤ))
          (hW : ∀ p, p < a ∨ b < p → IsZero (W.X p)) (hWa : IsZero (W.X (a - 1))) (p : ℤ),
          p < a + 1 ∨ b < p → IsZero ((kernel (bottomProj W a hWa)).X p) := by
        rintro W hW hWa p (hp | hp)
        · exact isZero_bottomTrunc_X a hWa (fun p hp => hW p (Or.inl hp)) p hp
        · exact isZero_kernel_bottomProj_X W a hWa p (hW p (Or.inr hp))
      have _ := hasTotal_of_columnBounds (kernel (bottomProj Z a hZa)) (a + 1) b (hker Z hZ hZa)
      have _ := hasTotal_of_columnBounds (kernel (bottomProj Z' a hZ'a)) (a + 1) b
        (hker Z' hZ' hZ'a)
      have _ := hasTotal_singleColumn (Z.X a) a
      have _ := hasTotal_singleColumn (Z'.X a) a
      have h₁ : QuasiIso (totalBottomSESMap f a hZa hZ'a).τ₁ := by
        rw [totalBottomSESMap_τ₁]
        exact ih (bottomTruncMap f a hZa hZ'a) (a + 1) b (by push_cast at hk ⊢; omega)
          (hker Z hZ hZa) (hker Z' hZ' hZ'a) (quasiIso_bottomTruncMap_f f a hZa hZ'a hf)
      have h₃ : QuasiIso (totalBottomSESMap f a hZa hZ'a).τ₃ := by
        rw [totalBottomSESMap_τ₃]
        have := hf a
        exact quasiIso_total_map_singleColumn (f.f a) a
      have hmid := quasiIso_τ₂ (totalBottomSESMap f a hZa hZ'a)
        (totalBottomSES_shortExact Z a hZa) (totalBottomSES_shortExact Z' a hZ'a)
      rw [totalBottomSESMap_τ₂] at hmid
      exact hmid

/-! ### Bounded above -/

/-- Only the columns `p ≥ m - b` contribute to the total degree `m` of a double complex
vanishing in second degrees `> b`, so there the inclusion of the stupid truncation in first
degrees `≥ c` is invertible as soon as `c ≤ m - b`. -/
lemma isIso_total_map_ιStupidTrunc_f
    (W : HomologicalComplex₂ A (up ℤ) (up ℤ)) (b c m : ℤ)
    (hWq : ∀ p q, b < q → IsZero ((W.X p).X q)) (hcm : c ≤ m - b)
    [HomologicalComplex₂.HasTotal W (up ℤ)]
    [HomologicalComplex₂.HasTotal (W.stupidTrunc (ComplexShape.embeddingUpIntGE c)) (up ℤ)] :
    IsIso ((HomologicalComplex₂.total.map
      (W.ιStupidTrunc (ComplexShape.embeddingUpIntGE c)) (up ℤ)).f m) := by
  refine isIso_total_map_f _ m (fun p q hpq => ?_)
  by_cases hp : c ≤ p
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, (ComplexShape.embeddingUpIntGE c).f i = p :=
      ⟨(p - c).toNat, show c + ((p - c).toNat : ℤ) = p by omega⟩
    have := HomologicalComplex.isIso_ιStupidTrunc_f W (ComplexShape.embeddingUpIntGE c) hi
    infer_instance
  · exact isIso_of_isZero_of_isZero _
      (isZero_X_X_of_isZero_X _
        (HomologicalComplex.isZero_stupidTrunc_X W _ p
          ((ComplexShape.notMem_range_embeddingUpIntGE_iff c p).2 (by omega))) q)
      (hWq p q (by omega))

/-- The stupid truncation in first degrees `≥ c` of a double complex vanishing in first degrees
`> a` vanishes outside the columns `c ≤ p ≤ a`. -/
lemma isZero_stupidTrunc_embeddingUpIntGE_X (W : HomologicalComplex₂ A (up ℤ) (up ℤ)) (a c : ℤ)
    (hW : ∀ p, a < p → IsZero (W.X p)) (p : ℤ) (hp : p < c ∨ a < p) :
    IsZero ((W.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X p) := by
  rcases hp with hp | hp
  · exact HomologicalComplex.isZero_stupidTrunc_X _ _ _
      ((ComplexShape.notMem_range_embeddingUpIntGE_iff c p).2 hp)
  · by_cases hq : ∃ i, (ComplexShape.embeddingUpIntGE c).f i = p
    · obtain ⟨i, hi⟩ := hq
      exact (hW p hp).of_iso (W.stupidTruncXIso _ hi)
    · exact HomologicalComplex.isZero_stupidTrunc_X _ _ _ (by simpa using hq)

/-- The stupid truncation in first degrees `≥ c` of a morphism of double complexes which is a
quasi-isomorphism on every column is again a quasi-isomorphism on every column. -/
lemma quasiIso_stupidTruncMap_f {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z') (c : ℤ)
    (hf : ∀ p, QuasiIso (f.f p)) (p : ℤ) :
    QuasiIso ((HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE c)).f p) := by
  by_cases hq : ∃ i, (ComplexShape.embeddingUpIntGE c).f i = p
  · obtain ⟨i, hi⟩ := hq
    have key : (HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE c)).f p =
        (Z.stupidTruncXIso _ hi).hom ≫ f.f p ≫ (Z'.stupidTruncXIso _ hi).inv := by
      rw [← Category.assoc,
        ← HomologicalComplex.stupidTruncMap_stupidTruncXIso_hom f
          (ComplexShape.embeddingUpIntGE c) hi, Category.assoc, Iso.hom_inv_id,
        Category.comp_id]
    rw [key]
    have := hf p
    infer_instance
  · have hz : ∀ W : HomologicalComplex₂ A (up ℤ) (up ℤ),
        IsZero ((W.stupidTrunc (ComplexShape.embeddingUpIntGE c)).X p) := fun W =>
      HomologicalComplex.isZero_stupidTrunc_X _ _ _ (by simpa using hq)
    have := isIso_of_isZero_of_isZero
      ((HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE c)).f p) (hz Z) (hz Z')
    infer_instance

/-- For a double complex vanishing in second degrees `> b`, the inclusion of the stupid
truncation in first degrees `≥ c` induces an isomorphism on `H^n` of total complexes as soon as
`c ≤ n - 1 - b`. -/
lemma isIso_homologyMap_total_map_ιStupidTrunc
    (W : HomologicalComplex₂ A (up ℤ) (up ℤ)) (b c n : ℤ)
    (hWq : ∀ p q, b < q → IsZero ((W.X p).X q)) (hcn : c ≤ n - 1 - b)
    [HomologicalComplex₂.HasTotal W (up ℤ)]
    [HomologicalComplex₂.HasTotal (W.stupidTrunc (ComplexShape.embeddingUpIntGE c)) (up ℤ)] :
    IsIso (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (W.ιStupidTrunc (ComplexShape.embeddingUpIntGE c)) (up ℤ)) n) :=
  isIso_homologyMap_of_isIso_f _ n
    (isIso_total_map_ιStupidTrunc_f W b c (n - 1) hWq (by omega))
    (isIso_total_map_ιStupidTrunc_f W b c n hWq (by omega))
    (isIso_total_map_ιStupidTrunc_f W b c (n + 1) hWq (by omega))

/-- **[Stacks, Tag 0133] for double complexes bounded above**: a morphism of double complexes
vanishing in first degrees `> a` and in second degrees `> b` which is a quasi-isomorphism on
every column is a quasi-isomorphism on total complexes. -/
lemma quasiIso_total_map_of_upperBound
    {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z') (a b : ℤ)
    (hZp : ∀ p, a < p → IsZero (Z.X p)) (hZq : ∀ p q, b < q → IsZero ((Z.X p).X q))
    (hZ'p : ∀ p, a < p → IsZero (Z'.X p)) (hZ'q : ∀ p q, b < q → IsZero ((Z'.X p).X q))
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)]
    (hf : ∀ p, QuasiIso (f.f p)) :
    QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain ⟨c, hc⟩ : ∃ c : ℤ, c = n - 1 - b := ⟨_, rfl⟩
  have hT := hasTotal_of_columnBounds (Z.stupidTrunc (ComplexShape.embeddingUpIntGE c)) c a
    (isZero_stupidTrunc_embeddingUpIntGE_X Z a c hZp)
  have hT' := hasTotal_of_columnBounds (Z'.stupidTrunc (ComplexShape.embeddingUpIntGE c)) c a
    (isZero_stupidTrunc_embeddingUpIntGE_X Z' a c hZ'p)
  have hqcn : IsIso (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE c)) (up ℤ)) n) := by
    have hqc := quasiIso_total_map_of_columnBounds (a + 1 - c).toNat
      (HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE c)) c a (by omega)
      (isZero_stupidTrunc_embeddingUpIntGE_X Z a c hZp)
      (isZero_stupidTrunc_embeddingUpIntGE_X Z' a c hZ'p) (quasiIso_stupidTruncMap_f f c hf)
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    rw [quasiIso_iff] at hqc
    exact hqc n
  have hsq : HomologicalComplex₂.total.map
        (HomologicalComplex.stupidTruncMap f (ComplexShape.embeddingUpIntGE c)) (up ℤ) ≫
      HomologicalComplex₂.total.map
        (Z'.ιStupidTrunc (ComplexShape.embeddingUpIntGE c)) (up ℤ) =
    HomologicalComplex₂.total.map (Z.ιStupidTrunc (ComplexShape.embeddingUpIntGE c)) (up ℤ) ≫
      HomologicalComplex₂.total.map f (up ℤ) := by
    rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp,
      HomologicalComplex.stupidTruncMap_ιStupidTrunc]
  have hιZ := isIso_homologyMap_total_map_ιStupidTrunc Z b c n hZq (by omega)
  have hιZ' := isIso_homologyMap_total_map_ιStupidTrunc Z' b c n hZ'q (by omega)
  have hcomp : IsIso (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
        (Z.ιStupidTrunc (ComplexShape.embeddingUpIntGE c)) (up ℤ)) n ≫
      HomologicalComplex.homologyMap (HomologicalComplex₂.total.map f (up ℤ)) n) := by
    rw [← HomologicalComplex.homologyMap_comp, ← hsq, HomologicalComplex.homologyMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap
    (HomologicalComplex₂.total.map
      (Z.ιStupidTrunc (ComplexShape.embeddingUpIntGE c)) (up ℤ)) n) _

/-! ### The statement on the rows -/

/-- The image of a morphism of double complexes under the flip. -/
abbrev flipHom {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z') : Z.flip ⟶ Z'.flip :=
  (HomologicalComplex₂.flipFunctor A (up ℤ) (up ℤ)).map f

/-- The identification of the total complex of a double complex with that of its flip is natural
in the double complex. -/
lemma totalFlipIso_naturality {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z')
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)] :
    HomologicalComplex₂.total.map (flipHom f) (up ℤ) ≫ (Z'.totalFlipIso (up ℤ)).hom =
      (Z.totalFlipIso (up ℤ)).hom ≫ HomologicalComplex₂.total.map f (up ℤ) := by
  ext n p q h
  simp only [HomologicalComplex.comp_f, HomologicalComplex₂.ιTotal_map_assoc,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom,
    HomologicalComplex₂.ιTotal_totalFlipIso_f_hom_assoc,
    Units.smul_def, HomologicalComplex₂.flipFunctor_map_f_f]
  rw (transparency := .default) [Preadditive.zsmul_comp, HomologicalComplex₂.ιTotal_map,
    Preadditive.comp_zsmul]
  rfl

/-- **[Stacks, Tag 0133] for double complexes bounded above, on the rows**: a morphism of double
complexes vanishing in first degrees `> a` and in second degrees `> b` which is a
quasi-isomorphism on every row is a quasi-isomorphism on total complexes. -/
lemma quasiIso_total_map_of_upperBound_flip
    {Z Z' : HomologicalComplex₂ A (up ℤ) (up ℤ)} (f : Z ⟶ Z') (a b : ℤ)
    (hZ : ∀ p q, a < p ∨ b < q → IsZero ((Z.X p).X q))
    (hZ' : ∀ p q, a < p ∨ b < q → IsZero ((Z'.X p).X q))
    [Z.HasTotal (up ℤ)] [Z'.HasTotal (up ℤ)]
    (hf : ∀ q, QuasiIso ((flipHom f).f q)) :
    QuasiIso (HomologicalComplex₂.total.map f (up ℤ)) := by
  have hcol : ∀ (W : HomologicalComplex₂ A (up ℤ) (up ℤ)),
      (∀ p q, a < p ∨ b < q → IsZero ((W.X p).X q)) → ∀ q, b < q → IsZero (W.flip.X q) := by
    intro W hW q hq
    refine (IsZero.iff_id_eq_zero _).2 ?_
    ext p
    exact (hW p q (Or.inr hq)).eq_of_src _ _
  have _ := (Z.flip_hasTotal_iff (up ℤ)).2 ‹_›
  have _ := (Z'.flip_hasTotal_iff (up ℤ)).2 ‹_›
  have hflip : QuasiIso (HomologicalComplex₂.total.map (flipHom f) (up ℤ)) :=
    quasiIso_total_map_of_upperBound (flipHom f) b a (hcol Z hZ)
      (fun q p hp => hZ p q (Or.inl hp)) (hcol Z' hZ')
      (fun q p hp => hZ' p q (Or.inl hp)) hf
  have : QuasiIso ((Z.totalFlipIso (up ℤ)).hom ≫
      HomologicalComplex₂.total.map f (up ℤ)) := by
    rw [← totalFlipIso_naturality]
    infer_instance
  exact quasiIso_of_comp_left (Z.totalFlipIso (up ℤ)).hom _

end StacksDraft.TotalComplexQuasiIso

end
