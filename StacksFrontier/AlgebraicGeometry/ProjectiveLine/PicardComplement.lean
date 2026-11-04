module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PicardGroup.OpenUFD
public import StacksFrontier.AlgebraicGeometry.ProjectiveChart.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveLine.ResidueDegree

/-!
# The Picard group of the projective line with a closed point removed

Let `k` be a field, let `f ∈ k[T₀, T₁]` be a homogeneous form and let `X = D₊(f)` be the
complement of its vanishing locus in `ℙ¹_k = Proj k[T₀, T₁]`. When a linear form `T₀ - c T₁`
divides `f` the open `X` sits inside `D₊(T₀ - c T₁)`, which is an affine line over `k`, so
`Pic(X) = 0` by [Stacks, Tag 0BDA]. This is clause (6) of [Stacks, Tag 0CDP]: extending `k` to a
field `k'` into which the residue field `κ(t)` of the closed point `t = V₊(f)` embeds over `k`
produces a `k'`-rational point of the vanishing locus, hence such a linear factor over `k'`, and
the Picard group of the base change dies.

The base change `X_{k'}` of `X = D₊(f)` is the open `D₊(f')` of `ℙ¹_{k'} = Proj k'[T₀, T₁]`,
where `f'` is `f` with its coefficients pushed along `k → k'`. The residue field `κ(t)` of the
closed point `t = V₊(f)` is the residue field of the maximal ideal `(F)` of the chart ring `k[X]`
cut out by the dehomogenization `F` of `f`.

## Main definitions

* `Stacks.ProjectiveLine.shear` and `Stacks.ProjectiveLine.gradedShear`: the shear
  `T₀ ↦ T₀ + c T₁` of `k[T₀, T₁]`, and the same map read as a graded ring homomorphism.
* `Stacks.ProjectiveLine.linearForm`: the linear form `T₀ - c T₁`.
* `Stacks.ProjectiveLine.awayShearEquiv`: the shear transports the degree-zero localization at
  `g` to the degree-zero localization at the sheared form.
* `Stacks.ProjectiveLine.basicOpenLinearFormIsoSpec`: **the complement of a rational point of
  `ℙ¹_k` is an affine line.**
* `Stacks.ProjectiveLine.basicOpenXIsoSpec`: the same for the coordinate point `V₊(Tᵢ)`, whose
  complement is the standard chart `D₊(Tᵢ)`.

## Main results

* `Stacks.ProjectiveLine.subsingleton_picardGroup_basicOpen_of_linearForm_dvd`: **the Picard
  group of `D₊(g)` is trivial when a linear form divides `g`.**
* `Stacks.ProjectiveLine.subsingleton_picardGroup_basicOpen_of_isHomogeneous_one`: the Picard
  group of `ℙ¹_k` with a `k`-rational point removed is trivial, which is the computation
  `Pic(X) = ℤ/dℤ` of Tag 0CDP in the case `d = 1`.
* `Stacks.ProjectiveLine.subsingleton_picardGroup_basicOpen_map_of_residueFieldAlgHom`:
  **clause (6) of Tag 0CDP** — the Picard group of the base change of `ℙ¹_k ∖ {t}` to a field
  `k'` admitting a `k`-embedding of `κ(t)` is trivial.
* `Stacks.ProjectiveLine.subsingleton_picardGroup_basicOpen_of_X_dvd`: the Picard group of
  `D₊(g)` is trivial when a homogeneous coordinate divides `g`.
* `Stacks.ProjectiveLine.subsingleton_picardGroup_basicOpen_map_of_X_one_dvd`: **clause (6) at
  the point at infinity** `t = V₊(T₁)` — with no hypothesis on the field extension, because
  `κ(t) = k` there.
* `Stacks.ProjectiveLine.not_X_one_dvd_of_isPrime_span_dehomogenize` and
  `Stacks.ProjectiveLine.subsingleton_picardGroup_basicOpen_map_of_residueFieldAlgHom_of_isPrime`:
  **clause (6) with the hypothesis `t ≠ V₊(T₁)` removed from the statement**, that hypothesis
  being implied by the chart presentation of `κ(t)`.

## References

* [Stacks Project, Tag 0CDP](https://stacks.math.columbia.edu/tag/0CDP)
* [Stacks Project, Tag 0BDA](https://stacks.math.columbia.edu/tag/0BDA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.SheafOfModules

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.ProjectiveLine

universe u

variable {k : Type u} [Field k]

/-! ### Shearing the homogeneous coordinates -/

/-- **The shear** of `k[T₀, T₁]`: the `k`-algebra map sending `T₀` to `T₀ + c T₁` and fixing
`T₁`. It is an automorphism, with inverse the shear at `-c`. -/
def shear (c : k) : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1, MvPolynomial.X 1]

/-- The shear sends `T₀` to `T₀ + c T₁`. -/
@[simp]
theorem shear_X_zero (c : k) :
    shear c (MvPolynomial.X 0) = MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1 := by
  simp [shear]

/-- The shear fixes `T₁`. -/
@[simp]
theorem shear_X_one (c : k) : shear c (MvPolynomial.X 1) = MvPolynomial.X 1 := by
  simp [shear]

/-- The shear at `-c` is a left inverse of the shear at `c`. -/
theorem shear_comp_shear (c : k) :
    (shear (-c)).comp (shear c) = AlgHom.id k (MvPolynomial (Fin 2) k) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp

/-- The shear at `-c` undoes the shear at `c`. -/
theorem shear_shear (c : k) (g : MvPolynomial (Fin 2) k) : shear (-c) (shear c g) = g := by
  simpa using AlgHom.congr_fun (shear_comp_shear c) g

/-- The shear at `c` undoes the shear at `-c`. -/
theorem shear_neg_shear (c : k) (g : MvPolynomial (Fin 2) k) : shear c (shear (-c) g) = g := by
  simpa using shear_shear (-c) g

/-- The shear preserves the total-degree grading. -/
theorem isHomogeneous_shear (c : k) {n : ℕ} {g : MvPolynomial (Fin 2) k}
    (hg : g.IsHomogeneous n) : (shear c g).IsHomogeneous n := by
  have h1 : ∀ i, (![MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1,
      MvPolynomial.X (1 : Fin 2)] i).IsHomogeneous 1 := by
    intro i
    fin_cases i
    · exact (MvPolynomial.isHomogeneous_X k (0 : Fin 2)).add
        (MvPolynomial.isHomogeneous_C_mul_X c (1 : Fin 2))
    · exact MvPolynomial.isHomogeneous_X k (1 : Fin 2)
  have h2 := hg.aeval ![MvPolynomial.X 0 + MvPolynomial.C c * MvPolynomial.X 1,
    MvPolynomial.X (1 : Fin 2)] h1
  rwa [one_mul] at h2

/-- The shear as a graded ring homomorphism of `k[T₀, T₁]`. -/
def gradedShear (c : k) : grading k →+*ᵍ grading k where
  __ := (shear c).toRingHom
  map_mem hx := (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (isHomogeneous_shear c ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hx))

/-- The graded shear agrees with the shear. -/
@[simp]
theorem gradedShear_apply (c : k) (g : MvPolynomial (Fin 2) k) :
    gradedShear c g = shear c g := rfl

/-! ### Transport of the degree-zero localization along a shear -/

/-- If the shear sends `g` to `h`, it sends the powers of `g` into the powers of `h`. -/
theorem powers_le_comap_gradedShear (c : k) {g h : MvPolynomial (Fin 2) k}
    (hgh : shear c g = h) :
    Submonoid.powers g ≤ (Submonoid.powers h).comap (gradedShear c) := by
  rintro x ⟨n, rfl⟩
  exact ⟨n, by rw [gradedShear_apply, map_pow, hgh]⟩

/-- Two shears that undo one another induce mutually inverse maps on degree-zero
localizations. -/
theorem map_gradedShear_map_gradedShear (c c' : k)
    (hcc : ∀ y : MvPolynomial (Fin 2) k, shear c' (shear c y) = y)
    {g h : MvPolynomial (Fin 2) k}
    (h₁ : Submonoid.powers g ≤ (Submonoid.powers h).comap (gradedShear c))
    (h₂ : Submonoid.powers h ≤ (Submonoid.powers g).comap (gradedShear c'))
    (x : HomogeneousLocalization.Away (grading k) g) :
    HomogeneousLocalization.map (gradedShear c') h₂
        (HomogeneousLocalization.map (gradedShear c) h₁ x) = x := by
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective x
  refine HomogeneousLocalization.val_injective _ ?_
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
  congr 1
  · exact hcc _
  · exact Subtype.ext (hcc _)

/-- **The shear transports the ring of functions on a standard open**: the degree-zero
localization at `g` is carried isomorphically to the degree-zero localization at the sheared
form. -/
def awayShearEquiv (c : k) {g h : MvPolynomial (Fin 2) k} (hgh : shear c g = h) :
    HomogeneousLocalization.Away (grading k) g ≃+*
      HomogeneousLocalization.Away (grading k) h :=
  have h₁ : Submonoid.powers g ≤ (Submonoid.powers h).comap (gradedShear c) :=
    powers_le_comap_gradedShear c hgh
  have h₂ : Submonoid.powers h ≤ (Submonoid.powers g).comap (gradedShear (-c)) :=
    powers_le_comap_gradedShear (-c) (by rw [← hgh, shear_shear])
  { toFun := HomogeneousLocalization.map (gradedShear c) h₁
    invFun := HomogeneousLocalization.map (gradedShear (-c)) h₂
    left_inv := map_gradedShear_map_gradedShear c (-c) (shear_shear c) h₁ h₂
    right_inv := map_gradedShear_map_gradedShear (-c) c (shear_neg_shear c) h₂ h₁
    map_mul' := (HomogeneousLocalization.map (gradedShear c) h₁).map_mul
    map_add' := (HomogeneousLocalization.map (gradedShear c) h₁).map_add }

/-! ### The complement of a rational point is an affine line -/

/-- **The linear form `T₀ - c T₁`**, whose vanishing locus is the rational point of `ℙ¹_k` with
coordinate `c` in the standard chart `D₊(T₁)`. -/
def linearForm (c : k) : MvPolynomial (Fin 2) k :=
  MvPolynomial.X 0 - MvPolynomial.C c * MvPolynomial.X 1

/-- The shear at `-c` sends `T₀` to the linear form `T₀ - c T₁`. -/
theorem shear_neg_X_zero (c : k) : shear (-c) (MvPolynomial.X 0) = linearForm c := by
  rw [shear_X_zero, linearForm, map_neg, neg_mul, ← sub_eq_add_neg]

/-- The linear form `T₀ - c T₁` is homogeneous of degree one. -/
theorem isHomogeneous_linearForm (c : k) : (linearForm c).IsHomogeneous 1 :=
  (MvPolynomial.isHomogeneous_X k (0 : Fin 2)).sub
    (MvPolynomial.isHomogeneous_C_mul_X c (1 : Fin 2))

/-- The degree-one homogenization of `X - c` is the linear form `T₀ - c T₁`. -/
theorem homogenize_X_sub_C (c : k) :
    (Polynomial.X - Polynomial.C c).homogenize 1 = linearForm c := by
  rw [Polynomial.homogenize_sub, Polynomial.homogenize_X one_ne_zero, Polynomial.homogenize_C]
  simp [linearForm]

/-- The ring of functions on the complement of the rational point with coordinate `c` is a
polynomial ring in one variable over `k`. -/
def polynomialAwayLinearFormEquiv (c : k) :
    MvPolynomial (Fin 1) k ≃+* HomogeneousLocalization.Away (grading k) (linearForm c) :=
  (Stacks.ProjectiveChart.chartRingEquiv k (0 : Fin (1 + 1))).trans
    (awayShearEquiv (-c) (shear_neg_X_zero c))

/-- **The complement of a rational point of `ℙ¹_k` is an affine line**: the standard open
`D₊(T₀ - c T₁)` is the spectrum of a polynomial ring in one variable over `k`. -/
def basicOpenLinearFormIsoSpec (c : k) :
    (Proj.basicOpen (grading k) (linearForm c)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (Fin 1) k)) :=
  (Proj.basicOpenIsoSpec (grading k) (linearForm c)
      (mem_grading (isHomogeneous_linearForm c)) Nat.one_pos).trans
    (Scheme.Spec.mapIso (polynomialAwayLinearFormEquiv c).toCommRingCatIso.op)

/-! ### Triviality of the Picard group -/

/-- If `D₊(a)` is an affine space over `k`, then the Picard group of `D₊(a * q)` is trivial. -/
private theorem subsingleton_picardGroup_basicOpen_mul_of_iso {a : MvPolynomial (Fin 2) k}
    (e : (Proj.basicOpen (grading k) a).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (Fin 1) k))) (q : MvPolynomial (Fin 2) k) :
    Subsingleton (PicardGroup (Proj.basicOpen (grading k) (a * q)).toScheme.presheaf
      (Proj.basicOpen (grading k) (a * q)).toScheme.ringCatSheaf.2) := by
  have : UniqueFactorizationMonoid (MvPolynomial (Fin 1) k) :=
    MvPolynomial.uniqueFactorizationMonoid (Fin 1)
  have hle : Proj.basicOpen (grading k) (a * q) ≤ Proj.basicOpen (grading k) a := by
    rw [Proj.basicOpen_mul]
    exact inf_le_left
  set U := Proj.basicOpen (grading k) a
  set V := Proj.basicOpen (grading k) (a * q)
  have hWim : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V :=
    (U.ι.image_preimage_eq_opensRange_inf V).trans (by
      simp only [Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hle)
  refine Stacks.PicardGroup.subsingleton_of_iso
    (U.ι.isoImage (U.ι ⁻¹ᵁ V) ≪≫ (Proj (grading k)).isoOfEq hWim) ?_
  refine Stacks.PicardGroup.subsingleton_of_iso
    (Scheme.Hom.preimageIso e.symm.hom (U.ι ⁻¹ᵁ V)) ?_
  exact Stacks.PicardUFD.subsingleton_picardGroup_open_spectrum
    (MvPolynomial (Fin 1) k) _

/-- **The Picard group of `D₊(g)` is trivial when a linear form divides `g`.** -/
theorem subsingleton_picardGroup_basicOpen_of_linearForm_dvd (c : k)
    {g : MvPolynomial (Fin 2) k} (hdvd : linearForm c ∣ g) :
    Subsingleton (PicardGroup (Proj.basicOpen (grading k) g).toScheme.presheaf
      (Proj.basicOpen (grading k) g).toScheme.ringCatSheaf.2) := by
  obtain ⟨q, rfl⟩ := hdvd
  exact subsingleton_picardGroup_basicOpen_mul_of_iso (basicOpenLinearFormIsoSpec c) q

/-- A linear factor of a polynomial gives a linear factor of its homogenization. -/
private theorem linearForm_dvd_of_dvd_homogenize {F : Polynomial k} {c : k} {d : ℕ}
    {f : MvPolynomial (Fin 2) k}
    (hdvd : Polynomial.X - Polynomial.C c ∣ F) (hd : F.natDegree = d) (hF : F.homogenize d = f) :
    linearForm c ∣ f := by
  have h := Polynomial.homogenize_dvd hdvd
  rwa [Polynomial.natDegree_X_sub_C, homogenize_X_sub_C, hd, hF] at h

/-- A root of the dehomogenization of a form not divisible by `T₁` gives a linear factor of the
form. -/
theorem linearForm_dvd_of_isRoot {d : ℕ} {f : MvPolynomial (Fin 2) k} (hf : f.IsHomogeneous d)
    (hX : ¬ MvPolynomial.X (1 : Fin 2) ∣ f) {c : k} (hc : (dehomogenize k f).IsRoot c) :
    linearForm c ∣ f := by
  exact linearForm_dvd_of_dvd_homogenize (Polynomial.dvd_iff_isRoot.mpr hc)
    (natDegree_dehomogenize_eq_of_not_X_one_dvd hf hX) (homogenize_dehomogenize hf)

/-- **The Picard group of `ℙ¹_k` with a `k`-rational point removed is trivial**: the standard
open of a homogeneous form of degree one not divisible by `T₁` has trivial Picard group. This is
the computation `Pic(X) = ℤ/dℤ` of [Stacks, Tag 0CDP] in the case `d = 1`. -/
theorem subsingleton_picardGroup_basicOpen_of_isHomogeneous_one
    {f : MvPolynomial (Fin 2) k} (hf : f.IsHomogeneous 1)
    (hX : ¬ MvPolynomial.X (1 : Fin 2) ∣ f) :
    Subsingleton (PicardGroup (Proj.basicOpen (grading k) f).toScheme.presheaf
      (Proj.basicOpen (grading k) f).toScheme.ringCatSheaf.2) := by
  have hF1 : (dehomogenize k f).natDegree = 1 :=
    natDegree_dehomogenize_eq_of_not_X_one_dvd hf hX
  have hne : dehomogenize k f ≠ 0 := fun h0 => by simp [h0] at hF1
  have hdeg : (dehomogenize k f).degree = 1 := by
    rw [Polynomial.degree_eq_natDegree hne, hF1]
    simp
  obtain ⟨c, hc⟩ := Polynomial.exists_root_of_degree_eq_one hdeg
  exact subsingleton_picardGroup_basicOpen_of_linearForm_dvd c
    (linearForm_dvd_of_isRoot hf hX hc)

/-- **The Picard group of `ℙ¹_k ∖ {t}` dies over a field embedding `κ(t)`.** Let `t = V₊(f)` be
the closed point of `ℙ¹_k` cut out by a homogeneous irreducible form `f` not divisible by `T₁`,
and let `X = ℙ¹_k ∖ {t}`. If a field `k'` admits a `k`-embedding of the residue field `κ(t)`,
then `Pic(X_{k'}) = 0`. -/
@[stacks 0CDP "clause (6): after enlarging `k` to a field `k'` admitting a `k`-embedding \
`κ(t) → k'`, the Picard group of the base change of `X = ℙ¹_k ∖ {t}` is trivial"]
theorem subsingleton_picardGroup_basicOpen_map_of_residueFieldAlgHom
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] {d : ℕ}
    {f : MvPolynomial (Fin 2) k} (hf : f.IsHomogeneous d) (hirr : Irreducible f)
    (hX : ¬ MvPolynomial.X (1 : Fin 2) ∣ f)
    [(Ideal.span {dehomogenize k f}).IsPrime]
    (ψ : (Ideal.span {dehomogenize k f}).ResidueField →ₐ[k] k') :
    Subsingleton (PicardGroup
      (Proj.basicOpen (grading k') (MvPolynomial.map (algebraMap k k') f)).toScheme.presheaf
      (Proj.basicOpen (grading k')
        (MvPolynomial.map (algebraMap k k') f)).toScheme.ringCatSheaf.2) := by
  have : (Ideal.span {dehomogenize k f}).IsMaximal :=
    isMaximal_span_dehomogenize hf hirr hX
  set F := dehomogenize k f with hFdef
  set χ : Polynomial k →ₐ[k] k' :=
    (ψ.comp (residueFieldAlgEquivQuotient k (Polynomial k) (Ideal.span {F})).toAlgHom).comp
      (Ideal.Quotient.mkₐ k (Ideal.span {F})) with hχ
  have hroot : Polynomial.aeval (χ Polynomial.X) F = 0 := by
    rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left_apply, hχ]
    simp
  have hdvdF : (Polynomial.X - Polynomial.C (χ Polynomial.X)) ∣
      F.map (algebraMap k k') := by
    rwa [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_map,
      ← Polynomial.aeval_def]
  have hmapdeg : (F.map (algebraMap k k')).natDegree = d := by
    rw [Polynomial.natDegree_map_eq_of_injective (algebraMap k k').injective,
      natDegree_dehomogenize_eq_of_not_X_one_dvd hf hX]
  have hhom : (F.map (algebraMap k k')).homogenize d =
      MvPolynomial.map (algebraMap k k') f := by
    rw [Polynomial.homogenize_map, hFdef, homogenize_dehomogenize hf]
  have hdvd := linearForm_dvd_of_dvd_homogenize hdvdF hmapdeg hhom
  exact subsingleton_picardGroup_basicOpen_of_linearForm_dvd _ hdvd

/-! ### The point at infinity

The closed point `V₊(T₁)` of `ℙ¹_k` is `k`-rational, and its complement `D₊(T₁)` is an affine line
over `k`. -/

/-- **The complement of the coordinate point `V₊(Tᵢ)` of `ℙ¹_k` is an affine line**: the standard
chart `D₊(Tᵢ)` is the spectrum of a polynomial ring in one variable over `k`. -/
@[ega "II 7.4.14"]
def basicOpenXIsoSpec (k : Type u) [Field k] (i : Fin 2) :
    (Proj.basicOpen (grading k) (MvPolynomial.X i)).toScheme ≅
      Spec (CommRingCat.of (MvPolynomial (Fin 1) k)) :=
  (Proj.basicOpenIsoSpec (grading k) (MvPolynomial.X i)
      (mem_grading (MvPolynomial.isHomogeneous_X k i)) Nat.one_pos).trans
    (Scheme.Spec.mapIso (Stacks.ProjectiveChart.chartRingEquiv k i).toCommRingCatIso.op)

/-- **The Picard group of `D₊(g)` is trivial when a homogeneous coordinate divides `g`.** -/
theorem subsingleton_picardGroup_basicOpen_of_X_dvd (i : Fin 2)
    {g : MvPolynomial (Fin 2) k} (hdvd : MvPolynomial.X i ∣ g) :
    Subsingleton (PicardGroup (Proj.basicOpen (grading k) g).toScheme.presheaf
      (Proj.basicOpen (grading k) g).toScheme.ringCatSheaf.2) := by
  obtain ⟨q, rfl⟩ := hdvd
  exact subsingleton_picardGroup_basicOpen_mul_of_iso (basicOpenXIsoSpec k i) q

/-- **The Picard group of `ℙ¹_k ∖ {V₊(T₁)}` dies over every field extension.** If `T₁` divides
`f`, then the Picard group of the base change of `D₊(f)` to any field extension `k'` of `k` is
trivial. -/
@[stacks 0CDP "clause (6) at the point at infinity `t = V₊(T₁)`, i.e. for `T₁ ∣ f`: the Picard \
group of the base change of `X = ℙ¹_k ∖ {t}` to an arbitrary field extension `k'` is trivial, \
with no hypothesis on `k'`"]
theorem subsingleton_picardGroup_basicOpen_map_of_X_one_dvd
    {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {f : MvPolynomial (Fin 2) k} (hdvd : MvPolynomial.X (1 : Fin 2) ∣ f) :
    Subsingleton (PicardGroup
      (Proj.basicOpen (grading k') (MvPolynomial.map (algebraMap k k') f)).toScheme.presheaf
      (Proj.basicOpen (grading k')
        (MvPolynomial.map (algebraMap k k') f)).toScheme.ringCatSheaf.2) := by
  obtain ⟨q, rfl⟩ := hdvd
  refine subsingleton_picardGroup_basicOpen_of_X_dvd (1 : Fin 2)
    ⟨MvPolynomial.map (algebraMap k k') q, ?_⟩
  simp

/-- If `f` is irreducible and the ideal generated by its dehomogenization is prime, then `T₁`
does not divide `f`. -/
theorem not_X_one_dvd_of_isPrime_span_dehomogenize {k : Type u} [Field k]
    {f : MvPolynomial (Fin 2) k} (hirr : Irreducible f)
    [h : (Ideal.span {dehomogenize k f}).IsPrime] :
    ¬ MvPolynomial.X (1 : Fin 2) ∣ f := by
  rintro ⟨q, hq⟩
  have hu : IsUnit q := (hirr.isUnit_or_isUnit hq).resolve_left MvPolynomial.X_prime.not_isUnit
  have hunit : IsUnit (dehomogenize k f) := by
    rw [hq, map_mul, dehomogenize_X_one, one_mul]
    exact hu.map (dehomogenize k)
  exact h.ne_top (Ideal.span_singleton_eq_top.mpr hunit)

/-- **The Picard group of `ℙ¹_k ∖ {t}` dies over a field embedding `κ(t)`.** Let `t = V₊(f)` be
the closed point of `ℙ¹_k` cut out by a homogeneous irreducible form `f`, with `κ(t)` the residue
field of the prime ideal generated by the dehomogenization of `f`, and let `X = ℙ¹_k ∖ {t}`. If a
field `k'` admits a `k`-embedding of `κ(t)`, then `Pic(X_{k'}) = 0`. -/
@[stacks 0CDP "clause (6) with the extra hypothesis `t ≠ V₊(T₁)` removed from the statement: \
for a closed point `t` of `ℙ¹_k` presented in the standard chart, a `k`-embedding `κ(t) → k'` \
makes the Picard group of the base change of `X = ℙ¹_k ∖ {t}` trivial"]
theorem subsingleton_picardGroup_basicOpen_map_of_residueFieldAlgHom_of_isPrime
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] {d : ℕ}
    {f : MvPolynomial (Fin 2) k} (hf : f.IsHomogeneous d) (hirr : Irreducible f)
    [(Ideal.span {dehomogenize k f}).IsPrime]
    (ψ : (Ideal.span {dehomogenize k f}).ResidueField →ₐ[k] k') :
    Subsingleton (PicardGroup
      (Proj.basicOpen (grading k') (MvPolynomial.map (algebraMap k k') f)).toScheme.presheaf
      (Proj.basicOpen (grading k')
        (MvPolynomial.map (algebraMap k k') f)).toScheme.ringCatSheaf.2) :=
  subsingleton_picardGroup_basicOpen_map_of_residueFieldAlgHom hf hirr
    (not_X_one_dvd_of_isPrime_span_dehomogenize hirr) ψ

end Stacks.ProjectiveLine

end
