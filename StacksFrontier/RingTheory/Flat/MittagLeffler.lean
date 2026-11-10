module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.RingTheory.Module.Kaplansky
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Universal injectivity from injectivity modulo the maximal ideal

Let `(R, 𝔪)` be a local ring and let `u : M → N` be a map of `R`-modules with `M` projective and
`N` flat. Stacks 05FQ says that if the reduction `ū : M/𝔪M → N/𝔪N` is injective, then `u` is
universally injective. This is the universal-injectivity input to the Mittag-Leffler conclusion
of Stacks 05U7, which deduces it from Stacks 0AS7 applied to a filtered colimit presentation.

## Main results

* `Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal`: Stacks 05FQ, with
  the source's reduction `M/𝔪M → N/𝔪N` written as the canonical map between the two quotients.
* `Module.Flat.rTensor_injective_of_projective_of_mem_maximalIdeal_smul_top`: the same statement
  with that map's injectivity spelled out as a membership condition.

## Implementation notes

The source's reduction `M/𝔪M → N/𝔪N` is the canonical `Submodule.mapQ` of `u` between the
quotients by `𝔪 • ⊤`, exactly as in Stacks 0AS5 and 046Y. Its injectivity is equivalent to
`u x ∈ 𝔪 • ⊤ → x ∈ 𝔪 • ⊤`, and that membership form is the hypothesis taken here: it is what
every step of the argument uses, and it avoids carrying the `Submodule.mapQ` well-definedness
proof `Submodule.smul_top_le_comap_smul_top` through the induction.
`Submodule.injective_mapQ_smul_top_iff` records the equivalence with the map form, and
`Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal` is the source's
statement with the map form as its hypothesis.

The proof is not the source's. The source writes `N` as a filtered colimit of finite free modules
by Lazard's theorem (Stacks 058G), factors `u` through a member of the system, and checks that the
resulting map of finite free modules is a split injection. Here Stacks 0AS5 first reduces
universal injectivity to the single test module `R/I` for `I` an ideal, after which the equational
criterion for flatness (Stacks 00HK, in Mathlib's form
`Module.Flat.exists_factorization_of_apply_eq_zero_of_free`) produces the factorization through a
finite free module directly, at the one element where it is needed. This needs neither Lazard's
theorem nor any colimit of modules.

Two universe conventions are inherited. `Module.Flat.rTensor_injective_iff_injective_mapQ_smul_top`
(Stacks 0AS5) puts `M` and `N` in a single universe `v` with `Small.{v} R`, which is what makes its
left-hand side -- test modules ranging over `Type v` -- the source's notion of universal
injectivity; the final statement therefore does the same, as do the companion statements
Stacks 05CJ,
05CM and 058K. The intermediate lemmas, which do not use Stacks 0AS5, keep all universes
independent.

## References

* [Stacks Project, Tag 05FQ](https://stacks.math.columbia.edu/tag/05FQ)
-/

@[expose] public section

universe u v w w'

open IsLocalRing

/-- Every basis coordinate of an element of `I • ⊤` lies in `I`. -/
private theorem Module.Basis.repr_mem_of_mem_ideal_smul_top {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] {ι : Type w} (b : Module.Basis ι R M) (I : Ideal R) {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : ∀ i, b.repr x i ∈ I := by
  refine Submodule.smul_induction_on (p := fun y ↦ ∀ i, b.repr y i ∈ I) hx
    (fun r hr n _ i ↦ ?_) (fun y z hy hz i ↦ ?_)
  · simpa using I.mul_mem_right _ hr
  · simpa using I.add_mem (hy i) (hz i)

/-- In a free module, membership in `I • ⊤` is membership of every basis coordinate in `I`. -/
private theorem Module.Basis.mem_ideal_smul_top_iff {R : Type u} [CommRing R] {M : Type v}
    [AddCommGroup M] [Module R M] {ι : Type w} (b : Module.Basis ι R M) (I : Ideal R) (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ ∀ i, b.repr x i ∈ I := by
  refine ⟨b.repr_mem_of_mem_ideal_smul_top I, fun hx ↦ ?_⟩
  rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hx i) Submodule.mem_top

/-- In a free module over a local ring, membership in `𝔪 • ⊤` is vanishing of every basis
coordinate in the residue field. -/
private theorem Module.Basis.mem_maximalIdeal_smul_top_iff {R : Type u} [CommRing R]
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M] {ι : Type w}
    (b : Module.Basis ι R M) (x : M) :
    x ∈ maximalIdeal R • (⊤ : Submodule R M) ↔ ∀ i, residue R (b.repr x i) = 0 := by
  simp only [b.mem_ideal_smul_top_iff, residue_eq_zero_iff]

/-- Injectivity of the reduction `M/IM → N/IN` of a linear map is the statement that `f x ∈ I • ⊤`
forces `x ∈ I • ⊤`. This is the form of the hypothesis used throughout. -/
public theorem Submodule.injective_mapQ_smul_top_iff {R : Type u} [CommRing R] {M : Type v}
    {N : Type w} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (I : Ideal R) :
    Function.Injective ((I • (⊤ : Submodule R M)).mapQ (I • (⊤ : Submodule R N)) f
        (Submodule.smul_top_le_comap_smul_top I f)) ↔
      ∀ x : M, f x ∈ I • (⊤ : Submodule R N) → x ∈ I • (⊤ : Submodule R M) := by
  refine ⟨fun h x hx ↦ ?_, fun h a₁ a₂ ha ↦ ?_⟩
  · simpa [Submodule.Quotient.mk_eq_zero] using
      h (a₁ := Submodule.Quotient.mk x) (a₂ := 0) (by simpa [Submodule.mapQ_apply] using hx)
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a₁
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ a₂
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq] at ha
    rw [Submodule.Quotient.eq]
    exact h _ (by simpa using ha)

/-- An endomorphism of a finite free module over a local ring which is the identity modulo the
maximal ideal is a unit: its determinant is `1` modulo the maximal ideal, hence a unit. -/
private theorem isUnit_of_sub_id_mem_maximalIdeal_smul_top {R : Type u} [CommRing R]
    [IsLocalRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (γ : M →ₗ[R] M)
    (hγ : ∀ x : M, γ x - x ∈ maximalIdeal R • (⊤ : Submodule R M)) : IsUnit γ := by
  classical
  set b := Module.Free.chooseBasis R M
  have hmap : (LinearMap.toMatrix b b γ).map (residue R) = 1 := by
    ext i j
    have := (b.mem_maximalIdeal_smul_top_iff _).1 (hγ (b j)) i
    rw [map_sub, Finsupp.sub_apply, map_sub, sub_eq_zero] at this
    simpa [Matrix.map_apply, LinearMap.toMatrix_apply, Matrix.one_apply, Matrix.diagonal_apply,
      b.repr_self, Finsupp.single_apply, eq_comm] using this
  have hdet : residue R (LinearMap.det γ) = 1 := by
    rw [← LinearMap.det_toMatrix b γ, RingHom.map_det]
    change ((LinearMap.toMatrix b b γ).map (residue R)).det = 1
    rw [hmap, Matrix.det_one]
  refine (LinearMap.isUnit_iff_isUnit_det γ).2 (notMem_maximalIdeal.mp fun hcon ↦ ?_)
  exact one_ne_zero (α := ResidueField R)
    (hdet.symm.trans (residue_eq_zero_iff _ |>.mpr hcon))

/-- A map of finite free modules over a local ring which is injective modulo the maximal ideal is
a split injection. Over the residue field the reduced map has a left inverse; lifting that left
inverse and composing gives an endomorphism of the source which is the identity modulo the
maximal ideal, hence invertible. -/
@[sga "3 VIIB 1.3.2" "special case"]
private theorem exists_comp_eq_id_of_mem_maximalIdeal_smul_top {R : Type u} [CommRing R]
    [IsLocalRing R] {M : Type v} {P : Type w} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    (β : M →ₗ[R] P)
    (hβ : ∀ x : M, β x ∈ maximalIdeal R • (⊤ : Submodule R P) →
      x ∈ maximalIdeal R • (⊤ : Submodule R M)) :
    ∃ ρ : P →ₗ[R] M, ρ ∘ₗ β = LinearMap.id := by
  classical
  set bM := Module.Free.chooseBasis R M
  set bP := Module.Free.chooseBasis R P
  set B := LinearMap.toMatrix bM bP β with hB
  set q := residue R with hq
  set Bbar := B.map q with hBbar
  -- The reduced matrix is injective over the residue field.
  have hker : LinearMap.ker (Matrix.toLin' Bbar) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    choose d hd using fun i ↦ residue_surjective (R := R) (c i)
    set x := bM.repr.symm (Finsupp.equivFunOnFinite.symm d) with hx
    have hrepr : ∀ i, bM.repr x i = d i := by
      intro i
      rw [hx, LinearEquiv.apply_symm_apply]
      simp
    have hmem : β x ∈ maximalIdeal R • (⊤ : Submodule R P) := by
      rw [bP.mem_maximalIdeal_smul_top_iff]
      intro j
      have hBx : ∀ j, Matrix.mulVec B d j = bP.repr (β x) j := by
        intro j
        have hrw := LinearMap.toMatrix_mulVec_repr bM bP β x
        rw [hB, ← congrFun hrw j]
        congr 1
        funext i
        exact (hrepr i).symm
      have hzero : Matrix.mulVec Bbar c j = 0 := by
        rw [← Matrix.toLin'_apply, hc]; rfl
      rw [← hBx j, RingHom.map_mulVec q B d j]
      refine .trans ?_ hzero
      rw [hBbar]
      congr 1
      funext i
      exact hd i
    have hall := (bM.mem_maximalIdeal_smul_top_iff _).1 (hβ x hmem)
    funext i
    rw [← hd i]
    simpa [hrepr i] using hall i
  -- Over the residue field it therefore has a left inverse.
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Bbar) hker
  set Abar := LinearMap.toMatrix' L with hAbar
  have hAB : Abar * Bbar = 1 := by
    rw [hAbar, ← LinearMap.toMatrix'_toLin' Bbar, ← LinearMap.toMatrix'_comp, hL,
      LinearMap.toMatrix'_id]
  -- Lift the left inverse entrywise.
  choose A hA using fun p : _ × _ ↦ residue_surjective (R := R) (Abar p.1 p.2)
  set A' : Matrix (Module.Free.ChooseBasisIndex R M) (Module.Free.ChooseBasisIndex R P) R :=
    Matrix.of fun i j ↦ A (i, j)
  have hA'map : A'.map q = Abar := Matrix.ext fun i j ↦ hA (i, j)
  have hmul : (A' * B).map q = 1 := by
    rw [Matrix.map_mul, hA'map, ← hBbar, hAB]
  -- The composite endomorphism is the identity modulo the maximal ideal, hence invertible.
  set γ := Matrix.toLin bM bM (A' * B) with hγ
  have hγid : ∀ x : M, γ x - x ∈ maximalIdeal R • (⊤ : Submodule R M) := by
    intro x
    rw [bM.mem_maximalIdeal_smul_top_iff]
    intro i
    rw [← hq, map_sub, Finsupp.sub_apply, map_sub, sub_eq_zero]
    have h1 : bM.repr (γ x) = Matrix.mulVec (A' * B) (bM.repr x) := by
      rw [hγ, Matrix.repr_toLin]
    rw [h1, RingHom.map_mulVec q (A' * B) (bM.repr x) i, hmul]
    simp
  obtain ⟨γu, hγu⟩ := isUnit_of_sub_id_mem_maximalIdeal_smul_top γ hγid
  refine ⟨(↑γu⁻¹ : M →ₗ[R] M) ∘ₗ Matrix.toLin bP bM A', ?_⟩
  have hcomp : (Matrix.toLin bP bM A') ∘ₗ β = γ := by
    rw [hγ, Matrix.toLin_mul (v₂ := bP), hB, Matrix.toLin_toMatrix]
  rw [LinearMap.comp_assoc, hcomp, ← hγu]
  exact γu.inv_mul

/-- The case of Stacks 05FQ in which the source is finite free: for `I` an ideal, if `f x` lies in
`I • ⊤` then so does `x`.

The equational criterion for flatness factors `f` through a finite free module in a way that kills
the chosen expression of `f x` as an `I`-combination, and the factoring map is a split injection
because it too is injective modulo the maximal ideal. -/
private theorem mem_ideal_smul_top_of_free_of_finite {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Flat R N] (f : M →ₗ[R] N)
    (hf : ∀ x : M, f x ∈ maximalIdeal R • (⊤ : Submodule R N) →
      x ∈ maximalIdeal R • (⊤ : Submodule R M))
    {I : Ideal R} {x : M} (hx : f x ∈ I • (⊤ : Submodule R N)) :
    x ∈ I • (⊤ : Submodule R M) := by
  classical
  -- Write `f x` as an `I`-linear combination of finitely many elements of `N`.
  rw [show (⊤ : Submodule R N) = Submodule.span R (Set.range (id : N → N)) by
    simp, Submodule.mem_ideal_smul_span_iff_exists_sum] at hx
  obtain ⟨a, ha, hsum⟩ := hx
  set T := a.support
  -- An auxiliary finite free module carrying the combination.
  set W := M × ({t // t ∈ T} → R)
  set g : ({t // t ∈ T} → R) →ₗ[R] N :=
    Fintype.linearCombination R (fun t : {t // t ∈ T} ↦ (t : N)) with hg
  set φ : W →ₗ[R] N := f ∘ₗ LinearMap.fst R M _ - g ∘ₗ LinearMap.snd R M _ with hφ
  set c : {t // t ∈ T} → R := fun t ↦ a t with hc
  have hφξ : φ (x, c) = 0 := by
    have hgc : g c = a.sum fun n r ↦ r • id n := by
      rw [hg, Fintype.linearCombination_apply, Finsupp.sum]
      exact Finset.sum_coe_sort T fun n ↦ a n • id n
    rw [hφ]
    change f x - g c = 0
    rw [hgc, hsum, sub_self]
  -- Factor through a finite free module.
  obtain ⟨k, α, ψ, hfac, hαξ⟩ :=
    Module.Flat.exists_factorization_of_apply_eq_zero_of_free (R := R) (M := N) hφξ
  set β := α ∘ₗ LinearMap.inl R M ({t // t ∈ T} → R) with hβdef
  have hψβ : ∀ m : M, ψ (β m) = f m := by
    intro m
    have h1 : φ (m, 0) = f m := by
      rw [hφ]
      change f m - g 0 = f m
      rw [map_zero, sub_zero]
    have h2 : ψ (α (m, 0)) = φ (m, 0) := by rw [hfac]; rfl
    rw [hβdef]
    change ψ (α (m, 0)) = f m
    rw [h2, h1]
  -- The factoring map is injective modulo the maximal ideal.
  have hβ : ∀ m : M, β m ∈ maximalIdeal R • (⊤ : Submodule R (Fin k →₀ R)) →
      m ∈ maximalIdeal R • (⊤ : Submodule R M) := by
    intro m hm
    refine hf m ?_
    have := Submodule.smul_top_le_comap_smul_top _ ψ hm
    rwa [Submodule.mem_comap, hψβ m] at this
  obtain ⟨ρ, hρ⟩ := exists_comp_eq_id_of_mem_maximalIdeal_smul_top β hβ
  -- The factorization kills the combination, so `β x` lies in `I • ⊤`.
  have hcI : c ∈ I • (⊤ : Submodule R ({t // t ∈ T} → R)) := by
    rw [(Pi.basisFun R {t // t ∈ T}).mem_ideal_smul_top_iff]
    intro t
    simpa [hc] using ha t
  have hβx : β x ∈ I • (⊤ : Submodule R (Fin k →₀ R)) := by
    have hsplit : (x, c) = LinearMap.inl R M ({t // t ∈ T} → R) x +
        LinearMap.inr R M ({t // t ∈ T} → R) c := by simp
    have : β x = -α (LinearMap.inr R M ({t // t ∈ T} → R) c) := by
      rw [hβdef, LinearMap.comp_apply, eq_neg_iff_add_eq_zero, ← map_add, ← hsplit]
      exact hαξ
    rw [this]
    exact Submodule.neg_mem _
      (Submodule.smul_top_le_comap_smul_top I α
        (Submodule.smul_top_le_comap_smul_top I (LinearMap.inr R M _) hcI))
  have hxρ : ρ (β x) = x := LinearMap.congr_fun hρ x
  rw [← hxρ]
  exact Submodule.smul_top_le_comap_smul_top I ρ hβx

/-- **Stacks 05FQ.** Let `(R, 𝔪)` be a local ring and let `u : M →ₗ[R] N` be a map of `R`-modules
with `M` projective and `N` flat. If the reduction `M/𝔪M → N/𝔪N` is injective -- that is, if
`u x ∈ 𝔪 • ⊤` forces `x ∈ 𝔪 • ⊤` -- then `u` is universally injective, i.e. `u ⊗ id_Q` is
injective for every `R`-module `Q`. -/
@[stacks 05FQ "the hypothesis spells out injectivity of `M/𝔪M → N/𝔪N` as
`u x ∈ 𝔪 • ⊤ → x ∈ 𝔪 • ⊤`, the form `Submodule.injective_mapQ_smul_top_iff` shows it to be
equivalent to; the conclusion spells out universal injectivity, which `Mathlib` has no name for,
as in Stacks 0AS5, 05CJ and 05CM."]
public theorem Module.Flat.rTensor_injective_of_projective_of_mem_maximalIdeal_smul_top
    {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R] {M N : Type v} [AddCommGroup M]
    [Module R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Flat R N]
    (u : M →ₗ[R] N)
    (hu : ∀ x : M, u x ∈ maximalIdeal R • (⊤ : Submodule R N) →
      x ∈ maximalIdeal R • (⊤ : Submodule R M)) :
    ∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (u.rTensor Q) := by
  classical
  have : Module.Free R M := Module.free_of_projective_of_isLocalRing
  refine (Module.Flat.rTensor_injective_iff_injective_mapQ_smul_top u).mpr fun I _ ↦ ?_
  rw [Submodule.injective_mapQ_smul_top_iff]
  intro x hx
  -- Restrict to the finite free submodule spanned by the basis vectors occurring in `x`.
  set b := Module.Free.chooseBasis R M
  set T := (b.repr x).support with hT
  set e : ({t // t ∈ T} → R) →ₗ[R] M :=
    Fintype.linearCombination R (fun t : {t // t ∈ T} ↦ b (t : Module.Free.ChooseBasisIndex R M))
    with he
  set π : M →ₗ[R] ({t // t ∈ T} → R) :=
    LinearMap.pi (fun t : {t // t ∈ T} ↦ b.coord (t : Module.Free.ChooseBasisIndex R M)) with hπ
  have hπe : ∀ d, π (e d) = d := by
    intro d
    funext t
    rw [hπ, LinearMap.pi_apply, he, Fintype.linearCombination_apply, Module.Basis.coord_apply,
      map_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single t]
    · simp
    · intro t' _ hne
      have hne' : (t' : Module.Free.ChooseBasisIndex R M) ≠ t := fun h ↦ hne (Subtype.ext h)
      simp [hne']
    · simp
  have hex : e (π x) = x := by
    have h1 : e (π x) = ∑ t : {t // t ∈ T}, b.repr x (t : Module.Free.ChooseBasisIndex R M) •
        b (t : Module.Free.ChooseBasisIndex R M) := by
      rw [he, Fintype.linearCombination_apply]
      simp only [hπ, LinearMap.pi_apply, Module.Basis.coord_apply]
    have h2 : ∑ i ∈ T, b.repr x i • b i = x := by
      conv_rhs => rw [← b.linearCombination_repr x]
      rw [Finsupp.linearCombination_apply, Finsupp.sum, hT]
    rw [h1, Finset.sum_coe_sort T fun i ↦ b.repr x i • b i, h2]
  -- Transfer the hypothesis and conclusion along `e` and `π`.
  have hu₀ : ∀ d : ({t // t ∈ T} → R), (u ∘ₗ e) d ∈ maximalIdeal R • (⊤ : Submodule R N) →
      d ∈ maximalIdeal R • (⊤ : Submodule R ({t // t ∈ T} → R)) := by
    intro d hd
    simpa [hπe d] using Submodule.smul_top_le_comap_smul_top _ π (hu (e d) hd)
  have hx₀ : (u ∘ₗ e) (π x) ∈ I • (⊤ : Submodule R N) := by
    simpa [LinearMap.comp_apply, hex] using hx
  rw [← hex]
  exact Submodule.smul_top_le_comap_smul_top I e
    (mem_ideal_smul_top_of_free_of_finite (u ∘ₗ e) hu₀ hx₀)

/-- **Stacks 05FQ.** Let `(R, 𝔪)` be a local ring and let `u : M →ₗ[R] N` be a map of `R`-modules
with `M` projective and `N` flat. If the induced map `M/𝔪M → N/𝔪N` is injective, then `u` is
universally injective, i.e. `u ⊗ id_Q` is injective for every `R`-module `Q`. -/
@[stacks 05FQ "`M/𝔪M` is `M ⧸ 𝔪 • ⊤` and the reduction of `u` is `Submodule.mapQ` along `u`, as in
Stacks 0AS5 and 046Y; the conclusion spells out universal injectivity, which `Mathlib` has no
name for."]
public theorem Module.Flat.rTensor_injective_of_projective_of_injective_mapQ_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R] {M N : Type v} [AddCommGroup M]
    [Module R M] [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Flat R N]
    (u : M →ₗ[R] N)
    (hu : Function.Injective ((maximalIdeal R • (⊤ : Submodule R M)).mapQ
      (maximalIdeal R • (⊤ : Submodule R N)) u
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal R) u))) :
    ∀ (Q : Type v) [AddCommGroup Q] [Module R Q], Function.Injective (u.rTensor Q) :=
  Module.Flat.rTensor_injective_of_projective_of_mem_maximalIdeal_smul_top u
    ((Submodule.injective_mapQ_smul_top_iff u (maximalIdeal R)).mp hu)

end
