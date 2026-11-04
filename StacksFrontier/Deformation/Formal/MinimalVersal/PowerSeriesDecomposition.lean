module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.MvPowerSeries.Evaluation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Completed.PowerSeries
public import StacksFrontier.Deformation.Formal.MinimalVersal.BaseRetraction
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.FormalObject.Completion
public import StacksFrontier.RingTheory.MvPowerSeries.CotangentSpace

/-!
# The base of a versal formal object is a power series ring over a smallest descent

Let `ξ` be a versal formal object of a category cofibered in groupoids over `𝒞_Λ`, lying over
`R = ξ.base`, and let `ξ' → ξ` be a smallest descent of it in the sense of Stacks 06T2, lying
over `R' = ξ'.base`. Then

    R ≅ R'[[x_1, …, x_r]]

as `Λ`-algebras, compatibly with the inclusion `R' → R`. This is the first half of Stacks
06T3; the second half, that `ξ'` is again versal, is
`Deformation.isVersal_smallestDescent`.

The argument runs as follows. By `Deformation.exists_ideal_prodAddEquiv_of_smallestDescent`
the inclusion `R' → R` admits a retraction, so `R` is the additive direct sum of `R'` and an
ideal `I`. Choosing elements `x_1, …, x_r` of `I` whose residues form a basis of the
finite-dimensional `κ`-vector space `I / 𝔪_R I` gives a `Λ`-algebra map
`R'[[x_1, …, x_r]] → R` sending `x_i` to `x_i`; it is surjective because it is surjective on
cotangent spaces (`Deformation.surjective_of_mvPowerSeriesEval`), and its kernel lies in the
square of the maximal ideal because the `x_i` are independent modulo `𝔪_R I`. Versality then
produces, for every `n`, a lift of the `n`-th adic truncation of `R` through the truncation of
that map, which forces the truncation to be injective as well. The power-series criterion of
Stacks 06SG upgrades those truncated bijections to a bijection.

## Main definitions

* `Deformation.mvPowerSeriesEval`: evaluation of a power series over one object of the
  completed base category at elements of the maximal ideal of another, along a morphism.

## Main results

* `Deformation.exists_mvPowerSeries_algEquiv_of_smallestDescent`: **Stacks 06T3**, the base of
  a versal formal object is a power series algebra over the base of a smallest descent of it,
  compatibly with the descended-base inclusion.

## Implementation notes

The compatibility clause is what makes the conclusion a statement *over* `R'` rather than an
abstract ring isomorphism; the images of the formal variables are the elements `x_1, …, x_r` of
the source statement.

Evaluation is Mathlib's `MvPowerSeries.eval₂Hom`, which needs the coefficient and target rings
topologised and the substituted elements topologically nilpotent. Both rings here are complete
local, so the maximal-ideal-adic topology registered by `WithIdeal` is complete and Hausdorff,
and an element of the maximal ideal is topologically nilpotent for it. Continuity of the
coefficient map is `RingHom.continuous_adic_of_isLocalHom`.

The injectivity of the truncated maps is obtained from a lift rather than from a direct
computation: the lift supplies a section of the truncation of `R`, and a surjective
endomorphism-like map whose kernel is killed by the nilpotence of the truncated maximal ideal
is injective.

## References

* [Stacks Project, Tag 06T2](https://stacks.math.columbia.edu/tag/06T2)
* [Stacks Project, Tag 06T3](https://stacks.math.columbia.edu/tag/06T3)
* [Stacks Project, Tag 06SG](https://stacks.math.columbia.edu/tag/06SG)
-/

@[expose] public section

open CategoryTheory IsLocalRing PowerSeries

namespace Deformation

universe u v w uF vF

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Evaluation of a power series over `R'` at elements of the maximal ideal of `R`, with
coefficients transported along a morphism `f : R' ⟶ R` of the completed base category. Both
rings carry their maximal-ideal-adic topologies, for which they are complete and Hausdorff, so
the defining sum converges. -/
public noncomputable def mvPowerSeriesEval
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} {r : ℕ} (f : R' ⟶ R)
    (x : Fin r → R) (hx : ∀ i, x i ∈ maximalIdeal R) :
    MvPowerSeries (Fin r) R' →+* R := by
  letI : WithIdeal R' := ⟨maximalIdeal R'⟩
  letI : WithIdeal R := ⟨maximalIdeal R⟩
  have hR' : IsAdic (maximalIdeal R') := rfl
  have hR : IsAdic (maximalIdeal R) := rfl
  letI : CompleteSpace R' := (hR'.isAdicComplete_iff).1 R'.completeLocal.isComplete |>.1
  letI : T2Space R' := (hR'.isAdicComplete_iff).1 R'.completeLocal.isComplete |>.2
  letI : CompleteSpace R := (hR.isAdicComplete_iff).1 R.completeLocal.isComplete |>.1
  letI : T2Space R := (hR.isAdicComplete_iff).1 R.completeLocal.isComplete |>.2
  letI : IsLocalHom f.hom.toRingHom := f.isLocal
  have hcont : Continuous (f.hom.toRingHom : R' →+* R) :=
    RingHom.continuous_adic_of_isLocalHom f.hom.toRingHom
  have hEval : MvPowerSeries.HasEval x := by
    refine ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hx i), ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot
  exact MvPowerSeries.eval₂Hom hcont hEval

/-- Evaluation sends a constant to the image of its coefficient. -/
public theorem mvPowerSeriesEval_C
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} {r : ℕ} (f : R' ⟶ R)
    (x : Fin r → R) (hx : ∀ i, x i ∈ maximalIdeal R) (a : R') :
    mvPowerSeriesEval f x hx (MvPowerSeries.C a) = f.hom a := by
  simp [mvPowerSeriesEval, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]

/-- Evaluation sends the `i`-th variable to the `i`-th chosen element. -/
public theorem mvPowerSeriesEval_X
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} {r : ℕ} (f : R' ⟶ R)
    (x : Fin r → R) (hx : ∀ i, x i ∈ maximalIdeal R) (i : Fin r) :
    mvPowerSeriesEval f x hx (MvPowerSeries.X i) = x i := by
  simp [mvPowerSeriesEval, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]

/-- Evaluation carries a power series with constant coefficient in the maximal ideal into the
maximal ideal: every term of the defining sum lies there, and the maximal ideal is closed. -/
public theorem mvPowerSeriesEval_mem_maximalIdeal
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} {r : ℕ} (f : R' ⟶ R)
    (x : Fin r → R) (hx : ∀ i, x i ∈ maximalIdeal R)
    (s : MvPowerSeries (Fin r) R')
    (hs : MvPowerSeries.constantCoeff s ∈ maximalIdeal R') :
    mvPowerSeriesEval f x hx s ∈ maximalIdeal R := by
  classical
  let _ : WithIdeal R' := ⟨maximalIdeal R'⟩
  let _ : WithIdeal R := ⟨maximalIdeal R⟩
  have hR' : IsAdic (maximalIdeal R') := rfl
  have hR : IsAdic (maximalIdeal R) := rfl
  let _ : CompleteSpace R' := (hR'.isAdicComplete_iff).1 R'.completeLocal.isComplete |>.1
  let _ : T2Space R' := (hR'.isAdicComplete_iff).1 R'.completeLocal.isComplete |>.2
  let _ : CompleteSpace R := (hR.isAdicComplete_iff).1 R.completeLocal.isComplete |>.1
  let _ : T2Space R := (hR.isAdicComplete_iff).1 R.completeLocal.isComplete |>.2
  have : IsLocalHom f.hom.toRingHom := f.isLocal
  have hcont : Continuous (f.hom.toRingHom : R' →+* R) :=
    RingHom.continuous_adic_of_isLocalHom f.hom.toRingHom
  have hEval : MvPowerSeries.HasEval x := by
    refine ⟨fun i => WithIdeal.isTopologicallyNilpotent_of_mem (hx i), ?_⟩
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot
  have hmopen : IsOpen (maximalIdeal R : Set R) :=
    AddSubgroup.isOpen_of_mem_nhds (maximalIdeal R).toAddSubgroup (by
      rw [hR.hasBasis_nhds_zero.mem_iff]
      exact ⟨1, trivial, by simp⟩)
  have hterm : ∀ d : (Fin r →₀ ℕ),
      f.hom (MvPowerSeries.coeff d s) * d.prod (fun j n => x j ^ n) ∈ maximalIdeal R := by
    intro d
    by_cases hd : d = 0
    · subst d
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff, hs] using
        (show f.hom (MvPowerSeries.constantCoeff s) ∈ maximalIdeal R from
          (mem_maximalIdeal _).2 (fun hu => hs (f.isLocal.map_nonunit _ hu)))
    · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
      have hdi : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have hxpow : x i ^ d i ∈ maximalIdeal R :=
        (Ideal.pow_le_self (by omega)) (Ideal.pow_mem_pow (hx i) (d i))
      have hprod : d.prod (fun j n => x j ^ n) ∈ maximalIdeal R := by
        show (∏ j ∈ d.support, x j ^ d j) ∈ maximalIdeal R
        exact Ideal.prod_mem _ (Finsupp.mem_support_iff.mpr hdi) hxpow
      exact Ideal.mul_mem_left _ _ hprod
  rw [show mvPowerSeriesEval f x hx s = MvPowerSeries.eval₂ f.hom.toRingHom x s by
    simp [mvPowerSeriesEval, MvPowerSeries.coe_eval₂Hom],
    MvPowerSeries.eval₂_eq_tsum hcont hEval s]
  exact tsum_mem (AddSubgroup.isClosed_of_isOpen (maximalIdeal R).toAddSubgroup hmopen) hterm

end

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An ideal of a Noetherian local ring admits finitely many elements whose residues form a
basis of the finite-dimensional residue-field vector space `I / 𝔪 I`: they span `I` modulo
`𝔪 I`, and a combination of them lying in `𝔪 I` has all coefficients in `𝔪`. -/
private theorem exists_fin_basis_mod_maximalIdeal_mul
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) :
    ∃ (r : ℕ) (x : Fin r → I),
      (∀ y : I, ∃ a : Fin r → R, y.1 - ∑ i, a i * (x i).1 ∈ maximalIdeal R * I) ∧
      (∀ a : Fin r → R,
        (∑ i, a i * (x i).1 ∈ maximalIdeal R * I) → ∀ i, a i ∈ maximalIdeal R) := by
  classical
  let m : Ideal R := maximalIdeal R
  let κ := ResidueField R
  let Q := I ⧸ (m • (⊤ : Submodule R I))
  let π : I →ₗ[R] I ⧸ (m • (⊤ : Submodule R I)) := Submodule.mkQ (m • (⊤ : Submodule R I))
  have hfinQ : Module.Finite R (I ⧸ (m • (⊤ : Submodule R I))) :=
    Module.Finite.of_surjective π (Submodule.mkQ_surjective _)
  let _ : Module κ Q := by
    show Module (R ⧸ maximalIdeal R) Q
    infer_instance
  have : IsScalarTower R κ Q := by
    show IsScalarTower R (R ⧸ maximalIdeal R) Q
    infer_instance
  have : Module.Finite κ Q := Module.Finite.of_restrictScalars_finite R κ Q
  have : Module.Free κ Q := Module.Free.of_basis (Module.Basis.ofVectorSpace κ Q)
  let b : Module.Basis (Fin (Module.finrank κ Q)) κ Q := Module.finBasis κ Q
  choose x hx using
    (fun i => Submodule.mkQ_surjective _ (b i) : ∀ i, ∃ y : I, π y = b i)
  have hsmul (a : R) (z : I) : residue R a • π z = π (a • z) := by
    show (algebraMap R κ a) • π z = a • π z
    exact IsScalarTower.algebraMap_smul κ a (π z)
  have hπsum (a : Fin (Module.finrank κ Q) → R) :
      π (∑ i, a i • x i) = ∑ i, residue R (a i) • b i := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← hsmul, hx]
  have hmap : Submodule.map I.subtype (m • (⊤ : Submodule R I)) = (m * I : Ideal R) := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype, smul_eq_mul]
  refine ⟨Module.finrank κ Q, x, ?_, ?_⟩
  · intro y
    choose c hc using fun i => residue_surjective (b.repr (π y) i)
    have hsumQ : π (∑ i, c i • x i) = π y := by
      rw [hπsum]
      apply b.repr.injective
      ext i
      simp [hc]
    let z : I := y - ∑ i, c i • x i
    have hq : π z = 0 := by rw [map_sub, hsumQ, sub_self]
    have hmem : z ∈ m • (⊤ : Submodule R I) := (Submodule.Quotient.mk_eq_zero _).1 hq
    refine ⟨c, ?_⟩
    simpa [hmap, z, Submodule.coe_sum, Submodule.coe_smul] using
      (Submodule.mem_map_of_mem hmem :
        (z : R) ∈ Submodule.map I.subtype (m • (⊤ : Submodule R I)))
  · intro a hsum i
    let z : I := ∑ j, a j • x j
    have hmem : z ∈ m • (⊤ : Submodule R I) := by
      have hmem' : (z : R) ∈ Submodule.map I.subtype (m • (⊤ : Submodule R I)) := by
        rw [hmap]
        simpa [z, m, Submodule.coe_sum, Submodule.coe_smul] using hsum
      obtain ⟨z', hz', heq⟩ := Submodule.mem_map.1 hmem'
      have hz'' : z' = (∑ j, a j • x j : I) := Subtype.ext heq
      simpa [hz''] using hz'
    have hlin : ∑ j, residue R (a j) • b j = 0 := by
      rw [← hπsum a]
      exact (Submodule.Quotient.mk_eq_zero _).2 hmem
    exact (Ideal.Quotient.eq_zero_iff_mem).1
      ((Fintype.linearIndependent_iff.mp b.linearIndependent) (fun j => residue R (a j)) hlin i)

/-- The kernel of a power-series map sending the variables to elements of `I` whose residues
are independent modulo `𝔪_R I` lies in the square of the maximal ideal: a kernel element has
constant coefficient zero by uniqueness of the additive decomposition, and its linear
coefficients are then forced into the maximal ideal by the independence. -/
private theorem ker_mvPowerSeriesEval_le_maximalIdeal_sq
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R' ⟶ R) (I : Ideal R)
    (hdecomp : ∀ z : R, ∃! q : R' × I, z = f.hom q.1 + q.2.1)
    {r : ℕ} (x : Fin r → I)
    (hindep : ∀ a : Fin r → R,
      (∑ i, a i * (x i).1 ∈ maximalIdeal R * I) → ∀ i, a i ∈ maximalIdeal R)
    (F : MvPowerSeries (Fin r) R' →+* R) [IsLocalHom F]
    (hC : ∀ a, F (MvPowerSeries.C a) = f.hom a)
    (hX : ∀ i, F (MvPowerSeries.X i) = (x i).1) :
    RingHom.ker F ≤ maximalIdeal (MvPowerSeries (Fin r) R') ^ 2 := by
  classical
  intro s hs
  have hFs : F s = 0 := hs
  obtain ⟨g, _, hg⟩ :=
    Stacks.MvPowerSeries.RegularParameters.exists_sum_X_mul_of_constantCoeff_eq_zero
      (s - MvPowerSeries.C (MvPowerSeries.constantCoeff s)) (by simp)
  have heq : s = MvPowerSeries.C (MvPowerSeries.constantCoeff s) +
      ∑ i, MvPowerSeries.X i * g i := by rw [← hg]; ring
  have hsumI : ∑ i, (x i).1 * F (g i) ∈ I :=
    Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_right _ _ (x i).2)
  have hrel : f.hom (MvPowerSeries.constantCoeff s) + ∑ i, (x i).1 * F (g i) = 0 := by
    have he := congrArg F heq
    simpa only [hFs, map_add, map_sum, map_mul, hC, hX] using he.symm
  obtain ⟨_, _, hu⟩ := hdecomp 0
  have hc : MvPowerSeries.constantCoeff s = 0 :=
    congrArg Prod.fst
      ((hu (MvPowerSeries.constantCoeff s, ⟨_, hsumI⟩) hrel.symm).trans
        (hu (0, 0) (by simp)).symm)
  have hz : ∑ i, F (g i) * (x i).1 = 0 := by
    simpa [hc, mul_comm] using hrel
  have hgm : ∀ i, g i ∈ maximalIdeal (MvPowerSeries (Fin r) R') := by
    intro i
    rw [← maximalIdeal_comap F]
    exact hindep (fun i => F (g i)) (hz ▸ (maximalIdeal R * I).zero_mem) i
  rw [heq, hc, map_zero, zero_add, pow_two]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul
    ((mem_maximalIdeal_mvPowerSeries_iff _).2 (by simp)) (hgm i)

end

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- Versality lifts an Artinian point of the base of `ξ` through a surjection, given a
compatible point of the base of a formal object mapping to `ξ`: push both formal objects
forward to their points, use the universal property of the pushforward of the source to get a
morphism over the surjection, and lift it by the criterion of Stacks 06HS. -/
private theorem exists_artinian_base_lift
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (hξ : IsVersal hp ξ)
    {η : FormalObject p} (j : η ⟶ ξ)
    {B A : ArtinianLocalAlgCat.{u, v, w} Λ k} (f : B ⟶ A) (hf : Function.Surjective f.hom)
    (α : ξ.base ⟶ artinianToComplete.obj A) (β : η.base ⟶ artinianToComplete.obj B)
    (hcomm : j.base ≫ α = β ≫ artinianToComplete.map f) :
    ∃ t : ξ.base ⟶ artinianToComplete.obj B, t ≫ artinianToComplete.map f = α := by
  classical
  let P := FormalObject.projection (p := p)
  have hP := formalObjectProjection_isCofiberedInGroupoids p hp
  obtain ⟨X, iX, hiX⟩ := exists_pushforward hP α ξ rfl
  obtain ⟨Y, iY, hiY⟩ := exists_pushforward hP β η rfl
  have hb' : P.IsStronglyCocartesian β iY :=
    isStronglyCocartesian_of_isCofiberedInGroupoids hP β iY hiY
  have hj : P.IsHomLift j.base j := IsHomLift.map P j
  have hja : P.IsHomLift (β ≫ artinianToComplete.map f) (j ≫ iX) := by
    rw [← hcomm]
    infer_instance
  obtain ⟨g, ⟨hg, _⟩, _⟩ := Functor.IsStronglyCocartesian.universal_property P β iY
    (artinianToComplete.map f) (β ≫ artinianToComplete.map f) rfl (j ≫ iX)
  obtain ⟨b, hbg⟩ := (isVersal_iff_lifts_artinian hp ξ).1 hξ f hf g hg iX
  have eY : Y.base = artinianToComplete.obj B := IsHomLift.codomain_eq P β iY
  have eX : X.base = artinianToComplete.obj A := IsHomLift.codomain_eq P α iX
  refine ⟨b.base ≫ eqToHom eY, ?_⟩
  have hgf : g.base ≫ eqToHom eX = eqToHom eY ≫ artinianToComplete.map f := by
    simpa [P, FormalObject.projection] using (congrArg (fun z => eqToHom eY ≫ z)
      (IsHomLift.fac P (artinianToComplete.map f) g)).symm
  rw [Category.assoc, ← hgf, ← Category.assoc,
    show b.base ≫ g.base = iX.base from congrArg FormalObject.Hom.base hbg]
  simpa [P, FormalObject.projection] using (IsHomLift.fac P α iX).symm

/-- A surjective morphism of complete local algebras stays surjective on adic truncations. -/
private theorem adicTruncation_map_surjective
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (hf : Function.Surjective f.hom) (n : ℕ) :
    Function.Surjective (AdicTruncation.map f n).hom := by
  intro b
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

/-- A local homomorphism of local rings carries each power of the maximal ideal into the
same power of the maximal ideal. -/
private theorem map_maximalIdeal_pow_le {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (g : A →+* B) [IsLocalHom g] (m : ℕ) :
    Ideal.map g (maximalIdeal A ^ m) ≤ maximalIdeal B ^ m := by
  rw [Ideal.map_pow]
  exact Ideal.pow_right_mono (map_maximalIdeal_le g) m

/-- For `n ≥ 1`, the adic truncation of a surjection whose kernel lies in the square of the
maximal ideal again has kernel in the square of the maximal ideal. -/
private theorem ker_adicTruncation_map_le_maximalIdeal_sq
    {S R : CompleteLocalAlgCat.{u, v, w} Λ k} (φ : S ⟶ R)
    (hφ : Function.Surjective φ.hom)
    (hker : RingHom.ker φ.hom ≤ maximalIdeal S ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    RingHom.ker (artinianToComplete.map (AdicTruncation.map φ n)).hom ≤
      maximalIdeal (artinianToComplete.obj (AdicTruncation.obj S n)) ^ 2 := by
  let π : S ⟶ artinianToComplete.obj (AdicTruncation.obj S n) := quotientProjection S n
  have : IsLocalHom φ.hom.toRingHom := φ.isLocal
  have : IsLocalHom π.hom.toRingHom := π.isLocal
  have hsq : (maximalIdeal R ^ 2).comap φ.hom = maximalIdeal S ^ 2 := by
    rw [← map_maximalIdeal_of_surjective φ.hom.toRingHom hφ, ← Ideal.map_pow]
    show Ideal.comap φ.hom (Ideal.map φ.hom (maximalIdeal S ^ 2)) = _
    rw [Ideal.comap_map_of_surjective' φ.hom hφ, sup_eq_left.mpr hker]
  intro b hb
  obtain ⟨s, rfl⟩ := (Ideal.Quotient.mk_surjective : Function.Surjective π.hom) b
  have hs : φ.hom s ∈ maximalIdeal R ^ (n + 1) :=
    Ideal.Quotient.eq_zero_iff_mem.mp
      (show (quotientProjection R n).hom (φ.hom s) = 0 from hb)
  have hs₂ : s ∈ maximalIdeal S ^ 2 := by
    rw [← hsq]
    exact Ideal.pow_le_pow_right (by omega : 2 ≤ n + 1) hs
  exact map_maximalIdeal_pow_le π.hom.toRingHom 2
    (Ideal.mem_map_of_mem _ hs₂)

/-- A surjection of complete local algebras whose kernel lies in the square of the maximal
ideal becomes injective on every positive adic truncation as soon as the truncation of the
target admits a section over the truncation of the map: the section is surjective because it
is surjective on cotangent spaces, and the truncated maximal ideal is nilpotent. -/
private theorem adicTruncation_map_injective_of_lift
    {S R : CompleteLocalAlgCat.{u, v, w} Λ k} (φ : S ⟶ R)
    (hφ : Function.Surjective φ.hom)
    (hker : RingHom.ker φ.hom ≤ maximalIdeal S ^ 2)
    (n : ℕ) (hn : 1 ≤ n)
    (t : R ⟶ artinianToComplete.obj (AdicTruncation.obj S n))
    (ht : t ≫ artinianToComplete.map (AdicTruncation.map φ n) = quotientProjection R n) :
    Function.Injective (AdicTruncation.map φ n).hom := by
  let B := artinianToComplete.obj (AdicTruncation.obj S n)
  let q : B ⟶ artinianToComplete.obj (AdicTruncation.obj R n) :=
    artinianToComplete.map (AdicTruncation.map φ n)
  let π : S ⟶ B := quotientProjection S n
  have : IsLocalHom φ.hom.toRingHom := φ.isLocal
  have : IsLocalHom π.hom.toRingHom := π.isLocal
  have : IsLocalHom t.hom.toRingHom := t.isLocal
  have hπsurj : Function.Surjective π.hom := Ideal.Quotient.mk_surjective
  have hπ (s : S) : q.hom (π.hom s) = (quotientProjection R n).hom (φ.hom s) := rfl
  have ht' (a : R) : q.hom (t.hom a) = (quotientProjection R n).hom a :=
    congrArg (fun g => g.hom a) ht
  have htmax : maximalIdeal R ≤ (maximalIdeal B).comap t.hom :=
    (maximalIdeal_comap t.hom.toRingHom).ge
  have htcot : Function.Surjective
      (Ideal.mapCotangent (maximalIdeal R) (maximalIdeal B) t.hom htmax) := by
    intro y
    obtain ⟨b, rfl⟩ := (maximalIdeal B).toCotangent_surjective y
    obtain ⟨s, hs⟩ := hπsurj b
    have hsm : s ∈ maximalIdeal S := by
      rw [← maximalIdeal_comap π.hom.toRingHom]
      show π.hom s ∈ maximalIdeal B
      rw [hs]
      exact b.2
    have hφsm : φ.hom s ∈ maximalIdeal R := (maximalIdeal_comap φ.hom.toRingHom).ge hsm
    refine ⟨(maximalIdeal R).toCotangent ⟨φ.hom s, hφsm⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent]
    apply (maximalIdeal B).toCotangent_eq.mpr
    apply ker_adicTruncation_map_le_maximalIdeal_sq φ hφ hker n hn
    show q.hom (t.hom (φ.hom s) - b.1) = 0
    rw [map_sub, ht', ← hs, hπ, sub_self]
  have htsurj : Function.Surjective t.hom :=
    (surjective_iff_surjective_cotangentSpaceMap t).2 htcot
  have hnil : maximalIdeal B ^ (n + 1) = ⊥ := by
    rw [← map_maximalIdeal_of_surjective π.hom.toRingHom hπsurj, ← Ideal.map_pow]
    refine le_antisymm ?_ bot_le
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hs
  refine (RingHom.injective_iff_ker_eq_bot _).2 (le_antisymm ?_ bot_le)
  intro b hb
  obtain ⟨a, rfl⟩ := htsurj b
  have ha : a ∈ maximalIdeal R ^ (n + 1) :=
    Ideal.Quotient.eq_zero_iff_mem.mp ((ht' a).symm.trans hb)
  have htmem : t.hom a ∈ maximalIdeal B ^ (n + 1) :=
    map_maximalIdeal_pow_le t.hom.toRingHom _ (Ideal.mem_map_of_mem _ ha)
  simpa [hnil] using htmem

/-- A power-series map compatible with constants and preserving maximal ideals induces, on
residue fields, the map read off from the constant coefficient. -/
private theorem residueEquiv_residue_mvPowerSeries
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} {r : ℕ} (f : R' ⟶ R)
    (F : MvPowerSeries (Fin r) R' →+* R)
    (hFmax : ∀ s ∈ maximalIdeal (MvPowerSeries (Fin r) R'), F s ∈ maximalIdeal R)
    (hF_C : ∀ a, F (MvPowerSeries.C a) = f.hom a) (s : MvPowerSeries (Fin r) R') :
    R.residueEquiv (residue R (F s)) =
      R'.residueEquiv (residue R' (MvPowerSeries.constantCoeff s)) := by
  have htail : s - MvPowerSeries.C (MvPowerSeries.constantCoeff s) ∈
      maximalIdeal (MvPowerSeries (Fin r) R') := by
    rw [mem_maximalIdeal_mvPowerSeries_iff]
    simp
  have hres : residue R (F s) =
      residue R (F (MvPowerSeries.C (MvPowerSeries.constantCoeff s))) := by
    refine sub_eq_zero.mp ?_
    rw [← map_sub, residue_eq_zero_iff]
    simpa only [map_sub] using hFmax _ htail
  rw [hres, hF_C]
  exact f.residue_comm (MvPowerSeries.constantCoeff s)

/-- Versality makes every positive adic truncation of a surjection from a power series algebra
over a smallest descent, with kernel in the square of the maximal ideal and restricting to the
descended-base inclusion on constants, bijective. -/
private theorem adicTruncation_map_bijective_of_isVersal
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (hξ : IsVersal hp ξ)
    (d : SmallestDescent ξ) {r : ℕ} (φ : mvPowerSeriesObject d.object.base r ⟶ ξ.base)
    (hsurj : Function.Surjective φ.hom)
    (hker : RingHom.ker φ.hom ≤ maximalIdeal (mvPowerSeriesObject d.object.base r) ^ 2)
    (hφ : mvPowerSeriesCoeffMap d.object.base r ≫ φ = d.inclusion.base)
    (n : ℕ) (hn : 1 ≤ n) : Function.Bijective (AdicTruncation.map φ n).hom := by
  obtain ⟨t, ht⟩ := exists_artinian_base_lift hp ξ hξ d.inclusion
    (AdicTruncation.map φ n) (adicTruncation_map_surjective φ hsurj n)
    (quotientProjection ξ.base n)
    (mvPowerSeriesCoeffMap d.object.base r ≫
      quotientProjection (mvPowerSeriesObject d.object.base r) n) (by
      rw [Category.assoc, quotientProjection_naturality, ← Category.assoc, hφ])
  exact ⟨adicTruncation_map_injective_of_lift φ hsurj hker n hn t ht,
    adicTruncation_map_surjective φ hsurj n⟩

/-- A map from a power series algebra that is bijective on every positive adic truncation
admits, from level two on, local retractions of its truncations compatible with `Λ`. -/
private theorem exists_quotient_retract_of_bijective
    {R' R : CompleteLocalAlgCat.{u, v, w} Λ k} {r : ℕ} (φ : mvPowerSeriesObject R' r ⟶ R)
    (F : MvPowerSeries (Fin r) R' →+* R) [IsLocalHom F] (hφ : ∀ s, φ.hom s = F s)
    (hquot : ∀ n, 1 ≤ n → Function.Bijective (AdicTruncation.map φ n).hom) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Ideal.map F (maximalIdeal (MvPowerSeries (Fin r) R') ^ n) ≤ maximalIdeal R ^ n ∧
        ∃ h : (R ⧸ maximalIdeal R ^ n) →+*
            (MvPowerSeries (Fin r) R' ⧸ maximalIdeal (MvPowerSeries (Fin r) R') ^ n),
          IsLocalHom h ∧
          (∀ s : MvPowerSeries (Fin r) R',
            h (Ideal.Quotient.mk (maximalIdeal R ^ n) (F s)) =
              Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin r) R') ^ n) s) ∧
          (∀ a : Λ,
            h (Ideal.Quotient.mk (maximalIdeal R ^ n) (algebraMap Λ R a)) =
              Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin r) R') ^ n)
                (MvPowerSeries.C (algebraMap Λ R' a))) := by
  refine ⟨2, fun n hn => ?_⟩
  cases n with
  | zero => omega
  | succ n =>
    refine ⟨map_maximalIdeal_pow_le F _, ?_⟩
    let e := AlgEquiv.ofBijective (AdicTruncation.map φ n).hom (hquot n (by omega))
    refine ⟨e.symm.toRingHom, ⟨fun a ha => ?_⟩,
      fun s => ?_, fun a => ?_⟩
    · have hu := ha.map e.toRingHom
      change IsUnit (e (e.symm a)) at hu
      exact e.apply_symm_apply a ▸ hu
    · rw [← hφ s]
      exact e.symm_apply_apply (Ideal.Quotient.mk _ s)
    · show e.symm (algebraMap Λ (AdicTruncation.obj R n) a) = _
      rw [e.symm.commutes]
      simp only [AdicTruncation.obj, AdicTruncation.ideal]
      dsimp [mvPowerSeriesObject]
      rw [← MvPowerSeries.algebraMap_apply]
      have : (maximalIdeal (MvPowerSeries (Fin r) R') ^ (n + 1)).IsTwoSided :=
        ⟨fun b hb => mul_comm b _ ▸
          (maximalIdeal (MvPowerSeries (Fin r) R') ^ (n + 1)).smul_mem b hb⟩
      exact (Ideal.Quotient.mk_algebraMap Λ
        (maximalIdeal (MvPowerSeries (Fin r) R') ^ (n + 1)) a).symm

/-- **Stacks Project, Tag 06T3.** The base of a versal formal object is a power series algebra
over the base of a smallest descent of it, compatibly with the descended-base inclusion: the
isomorphism carries a constant to the image of its coefficient. -/
@[stacks 06T3 "power series decomposition", sga "7 VI 2.10" "smallest descent case"]
public theorem exists_mvPowerSeries_algEquiv_of_smallestDescent
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p) (hξ : IsVersal hp ξ)
    (d : SmallestDescent ξ) :
    ∃ r : ℕ, ∃ e : MvPowerSeries (Fin r) d.object.base ≃ₐ[Λ] ξ.base,
      ∀ a : d.object.base, e (MvPowerSeries.C a) = d.inclusion.base.hom a := by
  classical
  let f := d.inclusion.base
  obtain ⟨I, addEquiv, haddEquiv⟩ :=
    exists_ideal_prodAddEquiv_of_smallestDescent hp ξ hξ d
  have hdecomp : ∀ z : ξ.base, ∃! q : d.object.base × I, z = f.hom q.1 + q.2.1 := fun z =>
    ⟨addEquiv.symm z, (addEquiv.apply_symm_apply z).symm.trans (haddEquiv _ _),
      fun q' hq' => addEquiv.injective
        ((haddEquiv q'.1 q'.2).trans (hq'.symm.trans (addEquiv.apply_symm_apply z).symm))⟩
  obtain ⟨r, x, hspan, hindep⟩ := exists_fin_basis_mod_maximalIdeal_mul I
  have hI : I ≤ maximalIdeal ξ.base :=
    ideal_le_maximalIdeal_of_prodDecomposition f I hdecomp
  let xR : Fin r → ξ.base := fun i => (x i).1
  have hx : ∀ i, xR i ∈ maximalIdeal ξ.base := fun i => hI (x i).2
  let F : MvPowerSeries (Fin r) d.object.base →+* ξ.base := mvPowerSeriesEval f xR hx
  have hF_C : ∀ a : d.object.base, F (MvPowerSeries.C a) = f.hom a :=
    mvPowerSeriesEval_C f xR hx
  have hF_X : ∀ i : Fin r, F (MvPowerSeries.X i) = xR i := mvPowerSeriesEval_X f xR hx
  have hFmax : ∀ s ∈ maximalIdeal (MvPowerSeries (Fin r) d.object.base),
      F s ∈ maximalIdeal ξ.base := fun s hs =>
    mvPowerSeriesEval_mem_maximalIdeal f xR hx s ((mem_maximalIdeal_mvPowerSeries_iff s).1 hs)
  have hFlocal : IsLocalHom F := ⟨fun s hu => by_contra fun hs =>
    (mem_maximalIdeal _).mp (hFmax s ((mem_maximalIdeal _).2 hs)) hu⟩
  have hsurj : Function.Surjective F :=
    surjective_of_mvPowerSeriesEval f I hdecomp x hspan F hFmax hF_C hF_X
  have hker : RingHom.ker F ≤ maximalIdeal (MvPowerSeries (Fin r) d.object.base) ^ 2 :=
    ker_mvPowerSeriesEval_le_maximalIdeal_sq f I hdecomp x hindep F hF_C hF_X
  let G : MvPowerSeries (Fin r) d.object.base →ₐ[Λ] ξ.base :=
    { toRingHom := F
      commutes' := by
        intro a
        show F (algebraMap Λ (MvPowerSeries (Fin r) d.object.base) a) = algebraMap Λ ξ.base a
        rw [MvPowerSeries.algebraMap_apply, hF_C]
        exact f.hom.commutes a }
  let φ : mvPowerSeriesObject d.object.base r ⟶ ξ.base :=
    { hom := G
      isLocal := hFlocal
      residue_comm := fun s => (residueEquiv_residue_mvPowerSeries f F hFmax hF_C s).trans rfl }
  have hφ : mvPowerSeriesCoeffMap d.object.base r ≫ φ = f := by
    apply CompleteLocalAlgCat.Hom.ext
    ext a
    exact hF_C a
  exact ⟨r, AlgEquiv.ofBijective G
    (mvPowerSeries_bijective_of_eventually_quotient_retract f I hdecomp x hspan hindep F
      hF_C hF_X (exists_quotient_retract_of_bijective φ F (fun _ => rfl)
        (adicTruncation_map_bijective_of_isVersal hp ξ hξ d φ hsurj hker hφ))), hF_C⟩

end

end Deformation

end
