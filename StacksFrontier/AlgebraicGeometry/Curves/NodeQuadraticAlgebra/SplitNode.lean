module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Curves.MulticrossNormalization
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.MaximalIdeals
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra

/-!
# Split nodes

Let `A` be a nodal local algebra over a field `k`, with residue field `κ`, and let
`κ' = Stacks.Curves.quadraticAlgebra A` be the separable `κ`-algebra of degree two attached to
it. The node is *split* when `κ'` is `κ × κ` rather than a separable quadratic field extension.
This file shows that splitness is detected equally by the quadratic relation, by the
normalization, and by the number of branches.

## Main results

* `Stacks.Curves.isSplitNode_tfae` — the equivalent conditions for a node to be split.
* `Stacks.Curves.nonempty_algEquiv_prod_iff_encard_maximalSpectrum_eq_two` — a
  two-dimensional algebra over a field is the square of the field exactly when it has two
  maximal ideals.
* `Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_iff_encard_maximalSpectrum_eq_two` —
  the quadratic algebra of a node splits exactly when the normalization has two maximal ideals.
* `Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_iff_exists_cotangent_coordinates` —
  the quadratic algebra of a node splits exactly when the quadratic relation can be written
  `x y` in suitable cotangent coordinates.
* `Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_iff_numberOfBranches_eq_two` — the
  quadratic algebra of a node splits exactly when the node has two branches.
* `Stacks.Curves.numberOfBranches_eq_encard_maximalSpectrum_integralClosure` — the branches of
  a reduced Noetherian local ring are the maximal ideals of its normalization.

## References

* [Stacks Project, Tag 0CBU](https://stacks.math.columbia.edu/tag/0CBU)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u v

namespace Stacks.Curves

/-! ### Two-dimensional algebras over a field with two maximal ideals -/

/-- An algebra map between finite algebras of equal dimension over a field is injective exactly
when it is surjective. -/
private theorem algHom_injective_iff_surjective_of_finrank_eq (K : Type*) [Field K]
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [Module.Finite K A] [Module.Finite K B] (φ : A →ₐ[K] B)
    (hdim : Module.finrank K A = Module.finrank K B) :
    Function.Injective φ ↔ Function.Surjective φ :=
  LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := φ.toLinearMap)

/-- Maximal spectra of isomorphic rings have the same cardinality. -/
private theorem encard_maximalSpectrum_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Set.encard (Set.univ : Set (MaximalSpectrum R)) =
      Set.encard (Set.univ : Set (MaximalSpectrum S)) := by
  rw [Set.encard_univ, Set.encard_univ]
  exact ENat.card_congr (maximalSpectrumCongr e)

/-- **An algebra of dimension one over a field is the field.** -/
theorem nonempty_algEquiv_self_of_finrank_eq_one (K : Type u) [Field K] (L : Type v)
    [CommRing L] [Nontrivial L] [Algebra K L] [Module.Finite K L]
    (hrank : Module.finrank K L = 1) : Nonempty (L ≃ₐ[K] K) := by
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hdim : Module.finrank K K = Module.finrank K L := by
    rw [hrank, Module.finrank_self]
  have hsurj : Function.Surjective (Algebra.ofId K L) :=
    (algHom_injective_iff_surjective_of_finrank_eq K _ hdim).mp hinj
  exact ⟨(AlgEquiv.ofBijective (Algebra.ofId K L) ⟨hinj, hsurj⟩).symm⟩

/-- **The square of a field has at least two maximal ideals**, the kernels of its two
projections. -/
theorem one_lt_encard_maximalSpectrum_prod (K : Type u) [Field K] :
    1 < Set.encard (Set.univ : Set (MaximalSpectrum (K × K))) := by
  have hmax (f : K × K →+* K) (hf : Function.Surjective f) : (RingHom.ker f).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _
      ((RingHom.quotientKerEquivOfSurjective hf).toMulEquiv.isField (Field.toIsField K))
  have hfst := hmax (RingHom.fst K K) fun x ↦ ⟨(x, 0), rfl⟩
  have hsnd := hmax (RingHom.snd K K) fun x ↦ ⟨(0, x), rfl⟩
  rw [Set.one_lt_encard_iff_nontrivial]
  refine ⟨⟨_, hfst⟩, Set.mem_univ _, ⟨_, hsnd⟩, Set.mem_univ _, fun h ↦ ?_⟩
  have h' : RingHom.ker (RingHom.fst K K) = RingHom.ker (RingHom.snd K K) :=
    congrArg MaximalSpectrum.asIdeal h
  have hmem : ((1 : K), (0 : K)) ∈ RingHom.ker (RingHom.snd K K) := by
    simp [RingHom.mem_ker]
  rw [← h', RingHom.mem_ker] at hmem
  simp at hmem

/-- **A two-dimensional algebra over a field with two maximal ideals is the square of the
field.** -/
theorem nonempty_algEquiv_prod_of_encard_maximalSpectrum_eq_two (K : Type u) [Field K]
    (T : Type v) [CommRing T] [Algebra K T] [Module.Finite K T]
    (hrank : Module.finrank K T = 2)
    (hcard : Set.encard (Set.univ : Set (MaximalSpectrum T)) = 2) :
    Nonempty (T ≃ₐ[K] (K × K)) := by
  classical
  obtain ⟨m, n, hmn, -⟩ := Set.encard_eq_two.mp hcard
  have hm : m.asIdeal.IsMaximal := m.isMaximal
  have hn : n.asIdeal.IsMaximal := n.isMaximal
  have hsup : m.asIdeal ⊔ n.asIdeal = ⊤ :=
    Ideal.isCoprime_iff_sup_eq.mp (MaximalSpectrum.isCoprime_of_ne hmn)
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    Submodule.mem_sup.mp (hsup ▸ Submodule.mem_top (x := (1 : T)))
  have : Nontrivial (T ⧸ m.asIdeal) := (Ideal.Quotient.field m.asIdeal).toNontrivial
  have : Nontrivial (T ⧸ n.asIdeal) := (Ideal.Quotient.field n.asIdeal).toNontrivial
  have : Module.Finite K (T ⧸ m.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  have : Module.Finite K (T ⧸ n.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K n.asIdeal).toLinearMap
      Ideal.Quotient.mk_surjective
  set φ : T →ₐ[K] ((T ⧸ m.asIdeal) × (T ⧸ n.asIdeal)) :=
    (Ideal.Quotient.mkₐ K m.asIdeal).prod (Ideal.Quotient.mkₐ K n.asIdeal) with hφdef
  have hsurj : Function.Surjective φ := by
    rintro ⟨z, w⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective w
    have key (I : Ideal T) (p q a b : T) (hp : p ∈ I) (hpq : p + q = 1) :
        Ideal.Quotient.mk I (a * q + b * p) = Ideal.Quotient.mk I a := by
      refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
      have h1 : a * q + b * p - a = (b - a) * p := by linear_combination a * hpq
      rw [h1]
      exact Ideal.mul_mem_left _ _ hp
    exact ⟨a * q + b * p, Prod.ext (key _ p q a b hp hpq) (by
      rw [add_comm]
      exact key _ q p b a hq (by rw [add_comm]; exact hpq))⟩
  have hle : Module.finrank K ((T ⧸ m.asIdeal) × (T ⧸ n.asIdeal)) ≤ Module.finrank K T :=
    LinearMap.finrank_le_finrank_of_surjective (f := φ.toLinearMap) hsurj
  have hsum : Module.finrank K ((T ⧸ m.asIdeal) × (T ⧸ n.asIdeal)) =
      Module.finrank K (T ⧸ m.asIdeal) + Module.finrank K (T ⧸ n.asIdeal) :=
    Module.finrank_prod
  have hmpos : 0 < Module.finrank K (T ⧸ m.asIdeal) := Module.finrank_pos
  have hnpos : 0 < Module.finrank K (T ⧸ n.asIdeal) := Module.finrank_pos
  have hmone : Module.finrank K (T ⧸ m.asIdeal) = 1 := by omega
  have hnone : Module.finrank K (T ⧸ n.asIdeal) = 1 := by omega
  have hdim : Module.finrank K T = Module.finrank K ((T ⧸ m.asIdeal) × (T ⧸ n.asIdeal)) := by
    rw [hsum, hmone, hnone, hrank]
  have hinj : Function.Injective φ :=
    (algHom_injective_iff_surjective_of_finrank_eq K φ hdim).mpr hsurj
  obtain ⟨em⟩ := nonempty_algEquiv_self_of_finrank_eq_one K (T ⧸ m.asIdeal) hmone
  obtain ⟨en⟩ := nonempty_algEquiv_self_of_finrank_eq_one K (T ⧸ n.asIdeal) hnone
  exact ⟨(AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩).trans (AlgEquiv.prodCongr em en)⟩

/-- **The square of a field has exactly two maximal ideals**, so a two-dimensional algebra
isomorphic to it has two. -/
theorem encard_maximalSpectrum_eq_two_of_nonempty_algEquiv_prod (K : Type u) [Field K]
    (T : Type v) [CommRing T] [Algebra K T] [Module.Finite K T]
    (hrank : Module.finrank K T = 2) (e : T ≃ₐ[K] (K × K)) :
    Set.encard (Set.univ : Set (MaximalSpectrum T)) = 2 := by
  have hcongr := encard_maximalSpectrum_eq_of_ringEquiv e.toRingEquiv
  rcases encard_maximalSpectrum_eq_one_or_two_of_finrank_eq_two K T hrank with h | h
  · rw [hcongr] at h
    exact absurd h (by simpa using (one_lt_encard_maximalSpectrum_prod K).ne')
  · exact h

/-- **A two-dimensional algebra over a field is the square of the field exactly when it has two
maximal ideals.** -/
theorem nonempty_algEquiv_prod_iff_encard_maximalSpectrum_eq_two (K : Type u) [Field K]
    (T : Type v) [CommRing T] [Algebra K T] [Module.Finite K T]
    (hrank : Module.finrank K T = 2) :
    Nonempty (T ≃ₐ[K] (K × K)) ↔ Set.encard (Set.univ : Set (MaximalSpectrum T)) = 2 :=
  ⟨fun ⟨e⟩ ↦ encard_maximalSpectrum_eq_two_of_nonempty_algEquiv_prod K T hrank e,
    nonempty_algEquiv_prod_of_encard_maximalSpectrum_eq_two K T hrank⟩

/-! ### The quadratic algebra of a quadratic polynomial with a root -/

/-- **A nondegenerate quadratic polynomial with a root in the base field presents the square of
the field.** -/
theorem nonempty_adjoinRoot_algEquiv_prod_of_isRoot (K : Type u) [Field K] (a b c : K)
    (ha : a ≠ 0) (hdisc : 4 * a * c - b ^ 2 ≠ 0) (r : K) (hr : a * r ^ 2 + b * r + c = 0) :
    Nonempty (AdjoinRoot (C a * X ^ 2 + C b * X + C c) ≃ₐ[K] (K × K)) := by
  set f : K[X] := C a * X ^ 2 + C b * X + C c with hfdef
  have hdeg : f.natDegree = 2 := by
    rw [hfdef]
    compute_degree!
  have hf : f ≠ 0 := fun h0 ↦ by simp [h0] at hdeg
  set s : K := -(b + a * r) / a with hsdef
  have has : a * s = -(b + a * r) := by
    rw [hsdef]
    field_simp
  have hs : a * s ^ 2 + b * s + c = 0 := by
    have h2 : a * (a * s ^ 2 + b * s + c) = (a * s) ^ 2 + b * (a * s) + a * c := by ring
    rw [has] at h2
    have h3 : a * (a * s ^ 2 + b * s + c) = 0 := by
      rw [h2]
      linear_combination a * hr
    exact mul_left_cancel₀ ha (h3.trans (mul_zero a).symm)
  have hd : a * (r - s) = 2 * a * r + b := by
    rw [mul_sub, has]
    ring
  have hdne : r - s ≠ 0 := by
    intro h0
    have h1 : (2 * a * r + b) ^ 2 = b ^ 2 - 4 * a * c := by
      linear_combination (4 * a) * hr
    rw [← hd, h0, mul_zero] at h1
    exact hdisc (by linear_combination h1)
  have hroot : Polynomial.eval₂ ((Algebra.ofId K (K × K)) : K →+* (K × K)) (r, s) f = 0 := by
    rw [hfdef]
    refine Prod.ext ?_ ?_ <;>
      simp only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X_pow, eval₂_X, Prod.fst_add, Prod.snd_add,
        Prod.fst_mul, Prod.snd_mul, Prod.fst_zero, Prod.snd_zero, Prod.pow_fst, Prod.pow_snd]
    · simpa using hr
    · simpa using hs
  set φ : AdjoinRoot f →ₐ[K] (K × K) :=
    AdjoinRoot.liftAlgHom f (Algebra.ofId K (K × K)) (r, s) hroot with hφdef
  have hφroot : φ (AdjoinRoot.root f) = (r, s) := by
    rw [hφdef]
    exact AdjoinRoot.liftAlgHom_root _ _ _ _
  have hφC : ∀ z : K, φ (algebraMap K (AdjoinRoot f) z) = (z, z) := fun z ↦ by
    rw [AlgHom.commutes]
    rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨u, v⟩
    refine ⟨algebraMap K (AdjoinRoot f) (u - (u - v) / (r - s) * r) +
      algebraMap K (AdjoinRoot f) ((u - v) / (r - s)) * AdjoinRoot.root f, ?_⟩
    have key : (u - v) / (r - s) * (r - s) = u - v := by field_simp
    rw [map_add, map_mul, hφroot, hφC, hφC, Prod.mk_add_mk, Prod.mk_mul_mk, Prod.mk.injEq]
    exact ⟨by ring, by linear_combination -key⟩
  have : Module.Finite K (AdjoinRoot f) := (AdjoinRoot.powerBasis hf).finite
  have hrankA : Module.finrank K (AdjoinRoot f) = 2 := by
    rw [PowerBasis.finrank (AdjoinRoot.powerBasis hf), AdjoinRoot.powerBasis_dim hf, hdeg]
  have hrankP : Module.finrank K (K × K) = 2 := by
    rw [Module.finrank_prod, Module.finrank_self]
  have hdim : Module.finrank K (AdjoinRoot f) = Module.finrank K (K × K) := by
    rw [hrankA, hrankP]
  have hinj : Function.Injective φ :=
    (algHom_injective_iff_surjective_of_finrank_eq K φ hdim).mpr hsurj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

/-- **A quadratic algebra isomorphic to the square of the base field has a root in the base
field**, namely the image of the generator under the first projection. -/
theorem exists_isRoot_of_nonempty_adjoinRoot_algEquiv_prod (K : Type u) [Field K] (a b c : K)
    (e : AdjoinRoot (C a * X ^ 2 + C b * X + C c) ≃ₐ[K] (K × K)) :
    ∃ r : K, a * r ^ 2 + b * r + c = 0 := by
  have h := AdjoinRoot.aeval_algHom_eq_zero (C a * X ^ 2 + C b * X + C c)
    ((AlgHom.fst K K K).comp e.toAlgHom)
  exact ⟨(AlgHom.fst K K K).comp e.toAlgHom (AdjoinRoot.root (C a * X ^ 2 + C b * X + C c)),
    by simpa using h⟩

/-! ### Splitness and the maximal ideals of the normalization -/

/-- **The quadratic algebra of a node splits exactly when the normalization has two maximal
ideals.** -/
theorem nonempty_quadraticAlgebra_algEquiv_prod_iff_encard_maximalSpectrum_eq_two
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) :
    Nonempty (quadraticAlgebra A ≃ₐ[ResidueField A] (ResidueField A × ResidueField A)) ↔
      Set.encard
        (Set.univ : Set (MaximalSpectrum ↥(integralClosure A (FractionRing A)))) = 2 := by
  have : Module.Finite (ResidueField A) (quadraticAlgebra A) :=
    finite_quadraticAlgebra_of_isNodalAlgebra k A hA
  have hrank := finrank_quadraticAlgebra_of_isNodalAlgebra k A hA
  have hquot : Set.encard
      (Set.univ : Set (MaximalSpectrum ↥(integralClosure A (FractionRing A)))) =
      Set.encard (Set.univ : Set (MaximalSpectrum (quadraticAlgebra A))) :=
    encard_maximalSpectrum_quotient
      ((maximalIdeal A).map (algebraMap A ↥(integralClosure A (FractionRing A))))
      fun m ↦ by
        have := m.isMaximal
        exact map_maximalIdeal_le_of_isMaximal m.asIdeal
  rw [hquot]
  exact nonempty_algEquiv_prod_iff_encard_maximalSpectrum_eq_two (ResidueField A)
    (quadraticAlgebra A) hrank

/-! ### Splitness and the quadratic relation -/

/-- **The quadratic form of a split node is isotropic.** -/
theorem exists_isotropic_of_nonempty_quadraticAlgebra_algEquiv_prod
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A)
    (x y : maximalIdeal A)
    (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
    (hx : e ⟨0⟩ = (maximalIdeal A).toCotangent x)
    (hy : e ⟨1⟩ = (maximalIdeal A).toCotangent y)
    (a b c : A) (hdisc : residue A (4 * a * c - b ^ 2) ≠ 0)
    (hrel : a * (x : A) ^ 2 + b * (x : A) * (y : A) + c * (y : A) ^ 2 ∈ (maximalIdeal A) ^ 3)
    (hsplit : Nonempty (quadraticAlgebra A ≃ₐ[ResidueField A]
      (ResidueField A × ResidueField A))) :
    ∃ u v : ResidueField A, (u ≠ 0 ∨ v ≠ 0) ∧
      residue A a * u ^ 2 + residue A b * u * v + residue A c * v ^ 2 = 0 := by
  obtain ⟨e₀⟩ := hsplit
  by_cases ha : residue A a = 0
  · exact ⟨1, 0, Or.inl one_ne_zero, by simp [ha]⟩
  obtain ⟨e₁⟩ := quadraticAlgebra_equiv_adjoinRoot k A hA x y e hx hy a b c ha hdisc hrel
  obtain ⟨r, hr⟩ := exists_isRoot_of_nonempty_adjoinRoot_algEquiv_prod (ResidueField A)
    (residue A a) (residue A b) (residue A c) (e₁.symm.trans e₀)
  exact ⟨r, 1, Or.inr one_ne_zero, by simpa using hr⟩

/-- **A node whose quadratic form is isotropic has cotangent coordinates in which the relation
reads `x y`.** -/
theorem exists_cotangent_coordinates_of_isotropic
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A)
    (x y : maximalIdeal A)
    (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
    (hx : e ⟨0⟩ = (maximalIdeal A).toCotangent x)
    (hy : e ⟨1⟩ = (maximalIdeal A).toCotangent y)
    (a b c : A) (hdisc : residue A (4 * a * c - b ^ 2) ≠ 0)
    (hrel : a * (x : A) ^ 2 + b * (x : A) * (y : A) + c * (y : A) ^ 2 ∈ (maximalIdeal A) ^ 3)
    (hiso : ∃ u v : ResidueField A, (u ≠ 0 ∨ v ≠ 0) ∧
      residue A a * u ^ 2 + residue A b * u * v + residue A c * v ^ 2 = 0) :
    ∃ (x' y' : maximalIdeal A)
      (e' : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A)),
      e' ⟨0⟩ = (maximalIdeal A).toCotangent x' ∧
        e' ⟨1⟩ = (maximalIdeal A).toCotangent y' ∧
        (x' : A) * (y' : A) ∈ (maximalIdeal A) ^ 3 := by
  have hdisc' : 4 * residue A a * residue A c - residue A b ^ 2 ≠ 0 := by
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using hdisc
  obtain ⟨α, β, γ, δ, hdet, hαγ, hbb, hβδ⟩ :=
    exists_linearFactorization_of_isotropic (residue A a) (residue A b) (residue A c)
      hdisc' hiso
  obtain ⟨P, hP⟩ := residue_surjective (R := A) α
  obtain ⟨Q, hQ⟩ := residue_surjective (R := A) β
  obtain ⟨R, hR⟩ := residue_surjective (R := A) γ
  obtain ⟨S, hS⟩ := residue_surjective (R := A) δ
  set u : A := P * (x : A) + Q * (y : A) with hudef
  set w : A := R * (x : A) + S * (y : A) with hwdef
  have hlin (P Q : A) : P * (x : A) + Q * (y : A) ∈ maximalIdeal A :=
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ x.2) (Ideal.mul_mem_left _ _ y.2)
  have hum : u ∈ maximalIdeal A := hlin P Q
  have hwm : w ∈ maximalIdeal A := hlin R S
  have hc1 : a - P * R ∈ maximalIdeal A := by
    refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
    rw [map_sub, map_mul, hP, hR, hαγ, sub_self]
  have hc2 : b - (P * S + Q * R) ∈ maximalIdeal A := by
    refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
    rw [map_sub, map_add, map_mul, map_mul, hP, hQ, hR, hS, hbb, sub_self]
  have hc3 : c - Q * S ∈ maximalIdeal A := by
    refine (IsLocalRing.residue_eq_zero_iff _).mp ?_
    rw [map_sub, map_mul, hQ, hS, hβδ, sub_self]
  have hmul : u * w ∈ (maximalIdeal A) ^ 3 := by
    have h := nodalQuadratic_coeff_change_mod_cube (maximalIdeal A) (x : A) (y : A)
      a b c (P * R) (P * S + Q * R) (Q * S) x.2 y.2 hc1 hc2 hc3 hrel
    have heq : P * R * (x : A) ^ 2 + (P * S + Q * R) * (x : A) * (y : A) +
        Q * S * (y : A) ^ 2 = u * w := by
      rw [hudef, hwdef]
      ring
    rw [← heq]
    exact h
  have hD : IsUnit (P * S - Q * R) := by
    refine (IsLocalRing.residue_ne_zero_iff_isUnit _).mp ?_
    rw [map_sub, map_mul, map_mul, hP, hQ, hR, hS]
    exact hdet
  have hspanxy : maximalIdeal A = Ideal.span {(x : A), (y : A)} :=
    maximalIdeal_eq_span_of_cotangent_basis x y e hx hy
  have hspan : Ideal.span {u, w} = maximalIdeal A := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      rintro z (rfl | rfl)
      exacts [hum, hwm]
    · have hu : u ∈ Ideal.span {u, w} := Ideal.subset_span (Set.mem_insert _ _)
      have hw : w ∈ Ideal.span {u, w} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      have hxmem : (x : A) ∈ Ideal.span {u, w} := by
        refine (Ideal.unit_mul_mem_iff_mem _ hD).mp ?_
        have heq : (P * S - Q * R) * (x : A) = S * u - Q * w := by
          rw [hudef, hwdef]
          ring
        rw [heq]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hu) (Ideal.mul_mem_left _ _ hw)
      have hymem : (y : A) ∈ Ideal.span {u, w} := by
        refine (Ideal.unit_mul_mem_iff_mem _ hD).mp ?_
        have heq : (P * S - Q * R) * (y : A) = P * w - R * u := by
          rw [hudef, hwdef]
          ring
        rw [heq]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hw) (Ideal.mul_mem_left _ _ hu)
      rw [hspanxy, Ideal.span_le]
      rintro z (rfl | rfl)
      exacts [hxmem, hymem]
  have hfin : Module.finrank (ResidueField A) (CotangentSpace A) = 2 :=
    finrank_cotangentSpace_eq_two_of_hasNodalQuadraticRelation hA.2.2
  obtain ⟨e', he₀, he₁⟩ :=
    exists_cotangent_basis_of_pair_generators_and_finrank_two A ⟨u, hum⟩ ⟨w, hwm⟩ hspan hfin
  exact ⟨⟨u, hum⟩, ⟨w, hwm⟩, e', he₀, he₁, hmul⟩

/-- **A node whose quadratic relation reads `x y` in some cotangent coordinates is split.** -/
theorem nonempty_quadraticAlgebra_algEquiv_prod_of_cotangent_coordinates
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A)
    (x y : maximalIdeal A)
    (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
    (hx : e ⟨0⟩ = (maximalIdeal A).toCotangent x)
    (hy : e ⟨1⟩ = (maximalIdeal A).toCotangent y)
    (hxy : (x : A) * (y : A) ∈ (maximalIdeal A) ^ 3) :
    Nonempty (quadraticAlgebra A ≃ₐ[ResidueField A] (ResidueField A × ResidueField A)) := by
  classical
  let t : CotangentSpace A ≃ₗ[ResidueField A] CotangentSpace A :=
    LinearEquiv.transvection (f := e.coord ⟨1⟩) (v := -e ⟨0⟩) (by simp)
  let e' := e.map t
  have hx' : e' ⟨0⟩ = (maximalIdeal A).toCotangent x := by
    change t (e ⟨0⟩) = _
    simpa [t, LinearMap.transvection.apply] using hx
  have hy' : e' ⟨1⟩ = (maximalIdeal A).toCotangent (y - x) := by
    change t (e ⟨1⟩) = _
    rw [map_sub, ← hx, ← hy]
    simp [t, LinearMap.transvection.apply, sub_eq_add_neg]
  have ha : residue A (1 : A) ≠ 0 := by simp
  have hdisc : residue A (4 * (1 : A) * 0 - 1 ^ 2) ≠ 0 := by simp
  have hrel : (1 : A) * (x : A) ^ 2 + 1 * (x : A) * ((y - x : maximalIdeal A) : A) +
      0 * (((y - x : maximalIdeal A) : A)) ^ 2 ∈ (maximalIdeal A) ^ 3 := by
    have h : (1 : A) * (x : A) ^ 2 + 1 * (x : A) * ((y - x : maximalIdeal A) : A) +
        0 * (((y - x : maximalIdeal A) : A)) ^ 2 = (x : A) * (y : A) := by
      rw [Submodule.coe_sub]
      ring
    rw [h]
    exact hxy
  have hdisc' : 4 * residue A (1 : A) * residue A (0 : A) - residue A (1 : A) ^ 2 ≠ 0 := by
    norm_num
  have hroot : residue A (1 : A) * (0 : ResidueField A) ^ 2 +
      residue A (1 : A) * 0 + residue A (0 : A) = 0 := by
    simp
  obtain ⟨e₁⟩ :=
    quadraticAlgebra_equiv_adjoinRoot k A hA x (y - x) e' hx' hy' 1 1 0 ha hdisc hrel
  obtain ⟨e₂⟩ := nonempty_adjoinRoot_algEquiv_prod_of_isRoot (ResidueField A)
    (residue A (1 : A)) (residue A (1 : A)) (residue A (0 : A)) ha hdisc' 0 hroot
  exact ⟨e₁.trans e₂⟩

/-- **The quadratic algebra of a node splits exactly when the quadratic relation of Stacks Tag
0C49 can be written `x y`**, that is, exactly when the cotangent space has a basis whose lifts
multiply into `𝔪³`. -/
theorem nonempty_quadraticAlgebra_algEquiv_prod_iff_exists_cotangent_coordinates
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) :
    Nonempty (quadraticAlgebra A ≃ₐ[ResidueField A] (ResidueField A × ResidueField A)) ↔
      ∃ (x y : maximalIdeal A)
        (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A)),
        e ⟨0⟩ = (maximalIdeal A).toCotangent x ∧
          e ⟨1⟩ = (maximalIdeal A).toCotangent y ∧
          (x : A) * (y : A) ∈ (maximalIdeal A) ^ 3 := by
  refine ⟨fun hsplit ↦ ?_, fun ⟨x, y, e, hx, hy, hxy⟩ ↦
    nonempty_quadraticAlgebra_algEquiv_prod_of_cotangent_coordinates k A hA x y e hx hy hxy⟩
  obtain ⟨x, y, e, a, b, c, hx, hy, -, hdisc, hrel⟩ := exists_nodalQuadraticRelation_nonzero k A hA
  exact exists_cotangent_coordinates_of_isotropic k A hA x y e hx hy a b c hdisc hrel
    (exists_isotropic_of_nonempty_quadraticAlgebra_algEquiv_prod k A hA x y e hx hy a b c
      hdisc hrel hsplit)

/-! ### Splitness and the number of branches -/

/-- **The maximal ideals of a ring, as a set of ideals, are counted by its maximal spectrum.** -/
theorem encard_setOf_isMaximal (R : Type v) [CommRing R] :
    Set.encard {I : Ideal R | I.IsMaximal} =
      Set.encard (Set.univ : Set (MaximalSpectrum R)) := by
  have himg : {I : Ideal R | I.IsMaximal} =
      MaximalSpectrum.asIdeal '' (Set.univ : Set (MaximalSpectrum R)) := by
    ext I
    exact ⟨fun hI ↦ ⟨⟨I, hI⟩, Set.mem_univ _, rfl⟩, by rintro ⟨m, -, rfl⟩; exact m.isMaximal⟩
  rw [himg, Function.Injective.encard_image (fun a b h ↦ MaximalSpectrum.ext h) _]

/-- **The branches of a reduced Noetherian local ring are counted by the maximal ideals of its
normalization.** In particular the count does not depend on the chosen henselization. -/
theorem numberOfBranches_eq_encard_maximalSpectrum_integralClosure
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (Ah : Type v) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (ResidueField A) Ah] :
    numberOfBranches A Ah =
      Set.encard (Set.univ : Set (MaximalSpectrum ↥(integralClosure A (FractionRing A)))) := by
  classical
  have hfinite : (minimalPrimes A).Finite := minimalPrimes.finite_of_isNoetherianRing A
  have hchar := numberOfBranches_characterizations A Ah
    (strictHenselizationData A).carrier (SeparableClosure (ResidueField A))
  have hbr : numberOfBranches A Ah =
      Set.encard {I : Ideal ↥(integralClosure A (FractionRing (A ⧸ nilradical A))) |
        I.IsMaximal} := (hchar.2.2.2 hfinite).1
  have hnil : nilradical A = ⊥ := nilradical_eq_bot_iff.mpr inferInstance
  have hker : RingHom.ker (AlgHom.id A A) = (⊥ : Ideal A) := by
    ext x
    simp
  let eBase : (A ⧸ nilradical A) ≃ₐ[A] A :=
    (Ideal.quotientEquivAlgOfEq A hnil).trans
      ((Ideal.quotientEquivAlgOfEq A hker.symm).trans
        (Ideal.quotientKerAlgEquivOfSurjective (f := AlgHom.id A A) fun x ↦ ⟨x, by simp⟩))
  let eFrac : FractionRing (A ⧸ nilradical A) ≃ₐ[A] FractionRing A :=
    IsFractionRing.algEquivOfAlgEquiv eBase
  let eClosure : ↥(integralClosure A (FractionRing (A ⧸ nilradical A))) ≃ₐ[A]
      ↥(integralClosure A (FractionRing A)) := eFrac.mapIntegralClosure
  rw [hbr, encard_setOf_isMaximal, encard_maximalSpectrum_eq_of_ringEquiv eClosure.toRingEquiv]

/-- **The branches of a reduced Noetherian local ring, counted against the fixed henselization,
are the maximal ideals of its normalization.** -/
theorem numberOfBranchesOfLocalRing_eq_encard_maximalSpectrum_integralClosure
    (A : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A] :
    numberOfBranchesOfLocalRing A =
      Set.encard (Set.univ : Set (MaximalSpectrum ↥(integralClosure A (FractionRing A)))) :=
  numberOfBranches_eq_encard_maximalSpectrum_integralClosure A (henselizationData A).carrier

/-- **The quadratic algebra of a node splits exactly when the node has two branches.** -/
theorem nonempty_quadraticAlgebra_algEquiv_prod_iff_numberOfBranches_eq_two
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) :
    Nonempty (quadraticAlgebra A ≃ₐ[ResidueField A] (ResidueField A × ResidueField A)) ↔
      numberOfBranchesOfLocalRing A = 2 := by
  have : IsReduced A := hA.2.1
  rw [numberOfBranchesOfLocalRing_eq_encard_maximalSpectrum_integralClosure A]
  exact nonempty_quadraticAlgebra_algEquiv_prod_iff_encard_maximalSpectrum_eq_two k A hA

/-! ### The equivalent conditions of a split node -/

/-- Let `A` be a nodal local algebra over a field `k`, with residue field `κ`, and let
`κ' = Stacks.Curves.quadraticAlgebra A` be the associated separable `κ`-algebra of degree two.
Then the following are equivalent: `κ'` is `κ × κ`; the nondegenerate quadratic form of Stacks
Tag 0C49 can be chosen to be `x y`; `A` has two branches; the integral closure of `A` in its
total ring of fractions has two maximal ideals.

The completion condition (5) is
`Stacks.Curves.nonempty_algEquiv_adicCompletion_quotient_X_mul_X_iff_numberOfBranches_eq_two`, and
the closing assertion of the remark, on the fibre of the normalization of a locally Noetherian
`k`-scheme, is `Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_iff_normalizationFiber`. -/
@[stacks 0CBU "conditions (1)-(4)"]
public theorem isSplitNode_tfae
    (k : Type u) (A : Type v) [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra k A] (hA : IsNodalAlgebra k A) :
    List.TFAE [
      Nonempty (quadraticAlgebra A ≃ₐ[ResidueField A] (ResidueField A × ResidueField A)),
      ∃ (x y : maximalIdeal A)
        (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A)),
        e ⟨0⟩ = (maximalIdeal A).toCotangent x ∧
          e ⟨1⟩ = (maximalIdeal A).toCotangent y ∧
          (x : A) * (y : A) ∈ (maximalIdeal A) ^ 3,
      numberOfBranchesOfLocalRing A = 2,
      Set.encard
        (Set.univ : Set (MaximalSpectrum ↥(integralClosure A (FractionRing A)))) = 2] := by
  tfae_have 1 ↔ 2 :=
    nonempty_quadraticAlgebra_algEquiv_prod_iff_exists_cotangent_coordinates k A hA
  tfae_have 1 ↔ 3 := nonempty_quadraticAlgebra_algEquiv_prod_iff_numberOfBranches_eq_two k A hA
  tfae_have 1 ↔ 4 :=
    nonempty_quadraticAlgebra_algEquiv_prod_iff_encard_maximalSpectrum_eq_two k A hA
  tfae_finish

end Stacks.Curves

end
