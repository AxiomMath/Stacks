module

public import StacksFrontier.RingTheory.MvPolynomial.BasisQuotientUniversal
public import StacksFrontier.RingTheory.Module.LocallyFree.SpanningFamily
public import StacksFrontier.RingTheory.Module.LocallyFree.Field
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Module

/-!
# Where prescribed polynomials form a basis of a finite locally free quotient

Let `A` be an `R`-algebra and `J ⊂ A[x_i; i ∈ ι]` an ideal whose quotient is a finite locally
free `A`-module of rank `d`. For polynomials `f₁, …, f_d` over `R` this file proves the three
algebraic facts behind the source's proof of [Stacks, Tag 0B99] that the subfunctors `F_W` of the
Hilbert functor of an affine space are open and cover it:

* the basis property is stable under base change
  (`Stacks.Hilbert.BasisQuotient.IsBasisIdeal.map`);
* if it holds after base change to some `B` at a prime `q`, it holds on a neighbourhood
  `D(g)` of the prime of `A` below `q` (`exists_isBasisIdeal_away`);
* every prime of `A` has a neighbourhood on which some `d` monomials have the basis property
  (`exists_isBasisIdeal_away_monomial`).

## References

* [Stacks Project, Tag 0B99](https://stacks.math.columbia.edu/tag/0B99)
-/

@[expose] public noncomputable section

open MvPolynomial TensorProduct Module

universe u

/-- A finite locally free module is finite. -/
theorem Module.IsFiniteLocallyFreeOfRank.moduleFinite {A : Type u} [CommRing A] {M : Type u}
    [AddCommGroup M] [Module A M] {d : ℕ} (h : Module.IsFiniteLocallyFreeOfRank A M d) :
    Module.Finite A M := by
  obtain ⟨ι, f, hspan, hbasis⟩ := h
  refine Module.Finite.of_localizationSpan (Set.range f) hspan ?_
  rintro ⟨g, ⟨i, rfl⟩⟩
  exact Module.Finite.of_basis (hbasis i).some

namespace Stacks.Hilbert.BasisQuotient

variable {R : Type*} [CommRing R] {ι : Type u} {d : ℕ} (f : Fin d → MvPolynomial ι R)

/-- **The basis property is stable under base change.** -/
theorem IsBasisIdeal.map {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    {J : Ideal (MvPolynomial ι A)} (hJ : IsBasisIdeal f J) (ψ : A →ₐ[R] B) :
    IsBasisIdeal f (J.map (MvPolynomial.map (ψ : A →+* B))) := by
  have h := equiv_comp f ((equiv f).symm ⟨J, hJ⟩) ψ
  rw [Equiv.apply_symm_apply] at h
  rw [← h]
  exact (equiv f (ψ.comp ((equiv f).symm ⟨J, hJ⟩))).2

section BaseChange

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (J : Ideal (MvPolynomial ι A))

/-- Evaluating the base change of `p` to `B` at the elements `1 ⊗ x_i` of `B ⊗_A (A[x_i] / J)`
gives `1 ⊗ p`. -/
theorem aeval_tmul_map (p : MvPolynomial ι A) :
    aeval (R := B) (fun i ↦ (1 : B) ⊗ₜ[A] Ideal.Quotient.mk J (X i))
      (MvPolynomial.map (algebraMap A B) p) = (1 : B) ⊗ₜ[A] Ideal.Quotient.mk J p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, aeval_C, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one,
      algebraMap_smul, smul_tmul, Algebra.smul_def, mul_one]
    rfl
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, tmul_add]
  | mul_X p i hp =>
    rw [_root_.map_mul, _root_.map_mul, hp, map_X, aeval_X, _root_.map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The comparison map `B[x_i] / J B[x_i] → B ⊗_A (A[x_i] / J)`. -/
def quotientBaseChange :
    (MvPolynomial ι B ⧸ J.map (MvPolynomial.map (algebraMap A B))) →ₐ[B]
      B ⊗[A] (MvPolynomial ι A ⧸ J) :=
  Ideal.Quotient.liftₐ _ (aeval fun i ↦ (1 : B) ⊗ₜ[A] Ideal.Quotient.mk J (X i)) (by
    have hle : J.map (MvPolynomial.map (algebraMap A B)) ≤
        RingHom.ker (aeval (R := B) fun i ↦ (1 : B) ⊗ₜ[A] Ideal.Quotient.mk J (X i)) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      rw [Ideal.mem_comap, RingHom.mem_ker, aeval_tmul_map,
        (Ideal.Quotient.eq_zero_iff_mem).mpr hp, tmul_zero]
    exact fun a ha ↦ hle ha)

/-- `quotientBaseChange` sends the class of the base change of `p` to `1 ⊗ p`. -/
theorem quotientBaseChange_mk_map (p : MvPolynomial ι A) :
    quotientBaseChange J (Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap A B) p)) =
      (1 : B) ⊗ₜ[A] Ideal.Quotient.mk J p :=
  aeval_tmul_map J p

/-- The comparison map `B[x_i] / J B[x_i] → B ⊗_A (A[x_i] / J)` is surjective. -/
theorem quotientBaseChange_surjective : Function.Surjective (quotientBaseChange (B := B) J) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b q =>
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨b • Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap A B) p), ?_⟩
    rw [map_smul, quotientBaseChange_mk_map, smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add _ _ _⟩

/-- A family spanning a module is sent to a spanning family by a surjective linear map. -/
private theorem span_range_comp_eq_top_of_surjective {B N P κ : Type*} [CommRing B]
    [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P] (σ : N →ₗ[B] P)
    (hσ : Function.Surjective σ) (v : κ → N) (hv : Submodule.span B (Set.range v) = ⊤) :
    Submodule.span B (Set.range (σ ∘ v)) = ⊤ := by
  rw [Set.range_comp, ← Submodule.map_span, hv, Submodule.map_top, LinearMap.range_eq_top.mpr hσ]

/-- The classes of the monomials `x^α` generate `B[x_i] / I` as a `B`-module. -/
private theorem span_range_mk_monomial_eq_top (I : Ideal (MvPolynomial ι B)) :
    Submodule.span B (Set.range fun α ↦ Ideal.Quotient.mk I (monomial α (1 : B))) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [show monomial α c = c • monomial α (1 : B) by rw [smul_monomial, smul_eq_mul, mul_one],
      ← Ideal.Quotient.mkₐ_eq_mk B, map_smul, Ideal.Quotient.mkₐ_eq_mk]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, rfl⟩)
  | add p q hp hq =>
    rw [map_add]
    exact Submodule.add_mem _ hp hq

/-- If the classes of the base changes of a family `v` generate `B[x_i] / J B[x_i]`, then the
elements `1 ⊗ v k` generate `B ⊗_A (A[x_i] / J)`. -/
private theorem span_tmul_eq_top_of_span_mk_map_eq_top {κ : Type*} (v : κ → MvPolynomial ι A)
    (h : Submodule.span B (Set.range fun k ↦ Ideal.Quotient.mk
      (J.map (MvPolynomial.map (algebraMap A B))) (MvPolynomial.map (algebraMap A B) (v k))) = ⊤) :
    Submodule.span B (Set.range fun k ↦ (1 : B) ⊗ₜ[A] Ideal.Quotient.mk J (v k)) = ⊤ := by
  rw [← span_range_comp_eq_top_of_surjective (quotientBaseChange (B := B) J).toLinearMap
    (quotientBaseChange_surjective J) _ h]
  congr 2
  funext k
  exact (quotientBaseChange_mk_map J (v k)).symm

/-- The elements `1 ⊗ x^α` generate `B ⊗_A (A[x_i] / J)`. -/
private theorem span_range_tmul_mk_monomial_eq_top :
    Submodule.span B (Set.range fun α ↦ (1 : B) ⊗ₜ[A] Ideal.Quotient.mk J (monomial α 1)) = ⊤ :=
  span_tmul_eq_top_of_span_mk_map_eq_top J _ (by
    simpa only [map_monomial, map_one] using span_range_mk_monomial_eq_top _)

end BaseChange

/-- A spanning family in a vector space of dimension `d` has a spanning subfamily indexed by
`Fin d`. -/
private theorem _root_.Submodule.exists_fin_span_range_comp_eq_top {K P X : Type*} [Field K]
    [AddCommGroup P] [Module K P] [Module.Finite K P] {d : ℕ} (hd : finrank K P = d)
    (v : X → P) (hv : Submodule.span K (Set.range v) = ⊤) :
    ∃ α : Fin d → X, Submodule.span K (Set.range (v ∘ α)) = ⊤ := by
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range v)
  have hb : Submodule.span K b = ⊤ := hbspan.trans hv
  let bas : Module.Basis b K P := Module.Basis.mk hbli (by
    rw [Subtype.range_coe_subtype, Set.ofPred_mem_eq, hb])
  have : Finite b := hbli.finite_of_isNoetherian
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = d := by
    rw [← Nat.card_eq_fintype_card, ← finrank_eq_nat_card_basis bas, hd]
  let e : Fin d ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose α hα using fun l ↦ hbsub (e l).2
  refine ⟨α, ?_⟩
  rw [show v ∘ α = Subtype.val ∘ e from funext hα, EquivLike.range_comp, Subtype.range_coe, hb]

section Locus

variable {A : Type u} [CommRing A] [Algebra R A] (J : Ideal (MvPolynomial ι A))

/-- The images of the `f l` in the quotient by `J`. -/
abbrev vec (l : Fin d) : MvPolynomial ι A ⧸ J := Ideal.Quotient.mk J (fA f A l)

/-- For an `A`-algebra `B` in a scalar tower over `R`, `fA f B l` is the image of `fA f A l`
under the coefficient map `A → B`. -/
theorem fA_eq_map {B : Type u} [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    (l : Fin d) : fA f B l = MvPolynomial.map (algebraMap A B) (fA f A l) := by
  rw [fA, fA, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq]

/-- In a quotient of `B[x_i]`, the class of the base change of `a • p` is the image of `a` in `B`
times the class of the base change of `p`. -/
theorem mk_map_smul {B : Type u} [CommRing B] [Algebra A B] (J' : Ideal (MvPolynomial ι B))
    (a : A) (p : MvPolynomial ι A) :
    Ideal.Quotient.mk J' (MvPolynomial.map (algebraMap A B) (a • p)) =
      algebraMap A B a • Ideal.Quotient.mk J' (MvPolynomial.map (algebraMap A B) p) := by
  rw [smul_eq_C_mul, _root_.map_mul, map_C, _root_.map_mul, Algebra.smul_def,
    ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq]

/-- If the images of the `f l` generate `(A[x_i] / J)_g`, then the class in
`A_g[x_i] / J A_g[x_i]` of the base change of any `P` lies in the span of the images of the
`f l`. -/
private theorem mk_map_mem_span_away_of_surjective (g : A)
    (h : Function.Surjective (LocalizedModule.map (Submonoid.powers g)
      (Fintype.linearCombination A (vec f J)))) (P : MvPolynomial ι A) :
    Ideal.Quotient.mk (J.map (MvPolynomial.map (algebraMap A (Localization.Away g))))
        (MvPolynomial.map (algebraMap A (Localization.Away g)) P) ∈
      Submodule.span (Localization.Away g) (Set.range fun l ↦ Ideal.Quotient.mk
        (J.map (MvPolynomial.map (algebraMap A (Localization.Away g))))
          (fA f (Localization.Away g) l)) := by
  set Ag := Localization.Away g
  set J' := J.map (MvPolynomial.map (algebraMap A Ag))
  set N := Submodule.span Ag (Set.range fun l ↦ Ideal.Quotient.mk J' (fA f Ag l))
  obtain ⟨y, hy⟩ := h (LocalizedModule.mk (Ideal.Quotient.mk J P) 1)
  induction y using LocalizedModule.induction_on with
  | h c s =>
    rw [LocalizedModule.map_mk] at hy
    obtain ⟨w, hw⟩ := LocalizedModule.mk_eq.mp hy
    let D : MvPolynomial ι A := ∑ l, c l • fA f A l
    have hD : Fintype.linearCombination A (vec f J) c = Ideal.Quotient.mk J D := by
      simp only [Fintype.linearCombination_apply, D, map_sum, vec]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [← Ideal.Quotient.mkₐ_eq_mk A, map_smul]
    have hmem : (w : A) • D - ((w : A) * (s : A)) • P ∈ J := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero,
        ← Ideal.Quotient.mkₐ_eq_mk A, map_smul, map_smul, Ideal.Quotient.mkₐ_eq_mk, ← hD]
      have hw' : (w : A) • (1 : A) • Fintype.linearCombination A (vec f J) c =
          (w : A) • (s : A) • Ideal.Quotient.mk J P := hw
      rwa [one_smul, smul_smul] at hw'
    have hmem' : Ideal.Quotient.mk J' (MvPolynomial.map (algebraMap A Ag)
        ((w : A) • D - ((w : A) * (s : A)) • P)) = 0 :=
      (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_map_of_mem _ hmem)
    rw [map_sub, map_sub, mk_map_smul, mk_map_smul, sub_eq_zero] at hmem'
    have hDN : Ideal.Quotient.mk J' (MvPolynomial.map (algebraMap A Ag) D) ∈ N := by
      simp only [D, map_sum, mk_map_smul]
      refine Submodule.sum_mem _ fun l _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, ?_⟩)
      exact congrArg (Ideal.Quotient.mk J') (fA_eq_map (A := A) (B := Ag) f l)
    have key : algebraMap A Ag ((w : A) * (s : A)) •
        Ideal.Quotient.mk J' (MvPolynomial.map (algebraMap A Ag) P) ∈ N := by
      rw [← hmem']
      exact Submodule.smul_mem _ _ hDN
    exact (Submodule.smul_mem_iff_of_isUnit N
      (IsLocalization.map_units Ag (⟨_, mul_mem w.2 s.2⟩ : Submonoid.powers g))).mp key

/-- If the images of the `f l` generate `(A[x_i] / J)_g`, they generate
`A_g[x_i] / J A_g[x_i]`. -/
theorem span_eq_top_away_of_surjective (g : A)
    (h : Function.Surjective (LocalizedModule.map (Submonoid.powers g)
      (Fintype.linearCombination A (vec f J)))) :
    Submodule.span (Localization.Away g) (Set.range fun l ↦ Ideal.Quotient.mk
      (J.map (MvPolynomial.map (algebraMap A (Localization.Away g))))
        (fA f (Localization.Away g) l)) = ⊤ := by
  rw [eq_top_iff, ← span_range_mk_monomial_eq_top
    (J.map (MvPolynomial.map (algebraMap A (Localization.Away g)))), Submodule.span_le]
  rintro _ ⟨α, rfl⟩
  simpa only [SetLike.mem_coe, map_monomial, map_one] using
    mk_map_mem_span_away_of_surjective f J g h (monomial α 1)

/-- A spanning family of `d` elements of a module surjecting onto a finite locally free module of
rank `d` is linearly independent. -/
theorem _root_.LinearIndependent.of_span_eq_top_of_surjective {B : Type u} [CommRing B]
    {N P : Type u} [AddCommGroup N] [Module B N] [AddCommGroup P] [Module B P]
    (σ : N →ₗ[B] P) (hσ : Function.Surjective σ) (hP : Module.IsFiniteLocallyFreeOfRank B P d)
    (v : Fin d → N) (hv : Submodule.span B (Set.range v) = ⊤) : LinearIndependent B v :=
  LinearIndependent.of_comp σ (hP.linearIndependent_of_span_eq_top _
    (span_range_comp_eq_top_of_surjective σ hσ v hv))

variable {f J}

/-- **Spanning implies basis.** If `A[x_i] / J` is finite locally free of rank `d` and, after base
change to `B`, the images of the `f l` generate, they form a basis. -/
theorem isBasisIdeal_map_of_span_eq_top {B : Type u} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (hM : Module.IsFiniteLocallyFreeOfRank A (MvPolynomial ι A ⧸ J) d)
    (hspan : Submodule.span B (Set.range fun l ↦ Ideal.Quotient.mk
      (J.map (MvPolynomial.map (algebraMap A B))) (fA f B l)) = ⊤) :
    IsBasisIdeal f (J.map (MvPolynomial.map (algebraMap A B))) := by
  have := hM.moduleFinite
  exact ⟨LinearIndependent.of_span_eq_top_of_surjective (quotientBaseChange J).toLinearMap
    (quotientBaseChange_surjective J) (hM.baseChange B) _ hspan, hspan.ge⟩

/-- If the images of the `f l` generate `B[x_i] / J B[x_i]`, then the elements `1 ⊗ f l` generate
`B ⊗_A (A[x_i] / J)`. -/
theorem span_tmul_eq_top_of_span_eq_top {B : Type u} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B]
    (hspan : Submodule.span B (Set.range fun l ↦ Ideal.Quotient.mk
      (J.map (MvPolynomial.map (algebraMap A B))) (fA f B l)) = ⊤) :
    Submodule.span B (Set.range fun l ↦ (1 : B) ⊗ₜ[A] vec f J l) = ⊤ := by
  simp only [fA_eq_map (A := A) (B := B) f] at hspan
  exact span_tmul_eq_top_of_span_mk_map_eq_top J (fA f A) hspan

/-- **The basis property spreads out from a point.** If `A[x_i] / J` is finite locally free of
rank `d` and the `f l` give a basis after base change to `B`, then they give a basis over `A_g`
for some `g` outside the prime of `A` below a given prime `q` of `B`. -/
theorem exists_isBasisIdeal_away {B : Type u} [CommRing B] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] (hM : Module.IsFiniteLocallyFreeOfRank A (MvPolynomial ι A ⧸ J) d)
    (q : Ideal B) [q.IsPrime] (hB : IsBasisIdeal f (J.map (MvPolynomial.map (algebraMap A B)))) :
    ∃ g ∉ q.comap (algebraMap A B),
      IsBasisIdeal f (J.map (MvPolynomial.map (algebraMap A (Localization.Away g)))) := by
  have := hM.moduleFinite
  obtain ⟨g, hg, hsurj⟩ := Module.exists_away_surjective_linearCombination_of_baseChange
    (vec f J) q (span_tmul_eq_top_of_span_eq_top (top_le_iff.mp hB.2))
  exact ⟨g, hg, isBasisIdeal_map_of_span_eq_top hM (span_eq_top_away_of_surjective f J g hsurj)⟩

/-- **Every point has a neighbourhood with a monomial basis.** If `A[x_i] / J` is finite locally
free of rank `d`, every prime `p` of `A` has a basic neighbourhood `D(g)` over which the images of
some `d` monomials form a basis. -/
theorem exists_isBasisIdeal_away_monomial
    (hM : Module.IsFiniteLocallyFreeOfRank A (MvPolynomial ι A ⧸ J) d) (p : Ideal A) [p.IsPrime] :
    ∃ (α : Fin d → (ι →₀ ℕ)) (g : A), g ∉ p ∧
      IsBasisIdeal (fun l ↦ (monomial (α l) 1 : MvPolynomial ι R))
        (J.map (MvPolynomial.map (algebraMap A (Localization.Away g)))) := by
  classical
  have := hM.moduleFinite
  let κ := p.ResidueField
  obtain ⟨hfin, hrank⟩ := IsFiniteLocallyFreeOfRank.finite_and_finrank_eq (hM.baseChange κ)
  obtain ⟨α, hα⟩ := Submodule.exists_fin_span_range_comp_eq_top hrank _
    (span_range_tmul_mk_monomial_eq_top (B := κ) J)
  let fm : Fin d → MvPolynomial ι R := fun l ↦ monomial (α l) 1
  have hspan : Submodule.span κ (Set.range fun l ↦ (1 : κ) ⊗ₜ[A] vec fm J l) = ⊤ := by
    rw [← hα]
    congr 2
    funext l
    simp only [vec, fA, fm, Function.comp_apply, map_monomial, map_one]
  obtain ⟨g, hg, hsurj⟩ :=
    Module.exists_away_surjective_linearCombination_of_baseChange (vec fm J) (⊥ : Ideal κ) hspan
  rw [← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField] at hg
  exact ⟨α, g, hg, isBasisIdeal_map_of_span_eq_top hM (span_eq_top_away_of_surjective fm J g hsurj)⟩

end Locus

end Stacks.Hilbert.BasisQuotient

end
