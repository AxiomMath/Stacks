module

public import Mathlib
public import StacksFrontier.Homology.Perfect.BettiSemicontinuity
public import StacksFrontier.RingTheory.Spectrum.Prime.MatrixRankLocus

/-!
# Constructibility of the level sets of the derived-fibre Betti numbers

Let `R` be a commutative ring and let `K` be a pseudo-coherent object of the derived category
`D(R)`.  For a prime `p` of `R` the `i`-th derived-fibre Betti number of `K` at `p` is
`dim_{κ(p)} H^i(K ⊗ᴸ_R κ(p))`, the function `StacksDraft.Perfect.fibreBetti`.  This module proves
that its level sets are constructible subsets of `PrimeSpectrum R`: this is the affine,
module-theoretic case of part (3) of [Stacks, Tag 0BDI].

## Main results

* `StacksDraft.Perfect.finrank_shortComplex_homology_add` and
  `StacksDraft.Perfect.finrank_homology_add`: for a complex of vector spaces, the dimension of
  the cohomology in degree `i` together with the ranks of the two adjacent differentials add up
  to the dimension of the term in degree `i`.
* `StacksDraft.Perfect.finrank_range_extendScalars_map`: the rank of a map of finite free modules
  after extension of scalars along `φ` is the rank of the entrywise image under `φ` of its
  matrix.
* `StacksDraft.Perfect.exists_matrix_fibreBetti_add_rank_add_rank_eq`: the derived-fibre Betti
  numbers of a pseudo-coherent object are `b - r₂ - r₁` for the ranks `r₁`, `r₂` at `p` of two
  fixed matrices over `R`.
* `StacksDraft.Perfect.isConstructible_fibreBetti_preimage`: **the affine case of part (3) of
  [Stacks, Tag 0BDI].**

## Implementation notes

The argument is the one of the source.  Pseudo-coherence gives a bounded-above representative `F`
with finite free terms, and base change along `R → κ(p)` computes the derived fibre degreewise
(`StacksDraft.Perfect.finrank_homologyFunctor_totalDerived_Q_obj`), so the Betti number at `p` is
the dimension of the cohomology of
`κ(p)^a → κ(p)^b → κ(p)^c`, that is `b - rank d^i - rank d^{i-1}`.  The two ranks are the ranks of
the entrywise images of two fixed matrices over `R`, whose level sets are constructible by
`StacksDraft.MinorRank.isConstructible_rank_eq`, and a level set of the Betti number is the
finite union of the intersections of a pair of them.

This is where constructibility, as opposed to the openness that part (2) gives, comes from: the
rank locus is the complement of the zero locus of the *finitely generated* ideal of minors, hence
retrocompact.

The matrix of the base-changed differential is the entrywise image of the matrix of the
differential: that is `finrank_range_extendScalars_map`, proved by comparing the two maps on the
base-changed basis `Algebra.TensorProduct.basis`.  The `Module R S` instance that
`ModuleCat.extendScalars` uses is `Module.compHom`, which is identified with the one coming from
`RingHom.toAlgebra` before the bases are formed.

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### The dimension of the cohomology of a complex of vector spaces -/

/-- **The dimension count for the homology of a short complex of vector spaces.**  For a short
complex `X₁ → X₂ → X₃` of vector spaces with `X₂` finite-dimensional, the dimension of the
homology, the rank of the second map and the rank of the first map add up to the dimension of
`X₂`.

The homology is `ker g ⧸ im f` by `CategoryTheory.ShortComplex.moduleCatHomologyIso`, so its
dimension is `dim (ker g) - dim (im f)`, and `dim (ker g) = dim X₂ - dim (im g)`. -/
theorem finrank_shortComplex_homology_add {k : Type u} [Field k]
    (S : ShortComplex (ModuleCat.{v} k)) [FiniteDimensional k S.X₂] :
    Module.finrank k S.homology + Module.finrank k (LinearMap.range S.g.hom) +
      Module.finrank k (LinearMap.range S.f.hom) = Module.finrank k S.X₂ := by
  have hle : LinearMap.range S.f.hom ≤ LinearMap.ker S.g.hom :=
    LinearMap.range_le_ker_iff.2 (ModuleCat.hom_ext_iff.1 S.zero)
  have h1 : Module.finrank k S.homology =
      Module.finrank k ((LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles) :=
    S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  have h2 : Module.finrank k (LinearMap.range S.moduleCatToCycles) =
      Module.finrank k (LinearMap.range S.f.hom) := by
    have hrange : LinearMap.range S.moduleCatToCycles =
        Submodule.comap (LinearMap.ker S.g.hom).subtype (LinearMap.range S.f.hom) :=
      LinearMap.range_codRestrict _ _ _
    rw [hrange]
    exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)
  have h4 := LinearMap.finrank_range_add_finrank_ker S.g.hom
  omega

/-- **The dimension count for the cohomology of a cochain complex of vector spaces.**  For a
cochain complex `C` of vector spaces whose term in degree `i` is finite-dimensional, the dimension
of `H^i(C)`, the rank of `d^i` and the rank of `d^{i-1}` add up to the dimension of `C^i`. -/
theorem finrank_homology_add {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{v} k) ℤ) (i : ℤ) [FiniteDimensional k (C.X i)] :
    Module.finrank k (C.homology i) +
        Module.finrank k (LinearMap.range (C.d i (i + 1)).hom) +
      Module.finrank k (LinearMap.range (C.d (i - 1) i).hom) = Module.finrank k (C.X i) := by
  have hprev : (ComplexShape.up ℤ).prev i = i - 1 := by simp
  have hnext : (ComplexShape.up ℤ).next i = i + 1 := by simp
  have h1 : Module.finrank k (C.homology i) =
      Module.finrank k ((C.sc' (i - 1) i (i + 1)).homology) :=
    (C.homologyIsoSc' (i - 1) i (i + 1) hprev hnext).toLinearEquiv.finrank_eq
  have : FiniteDimensional k ((C.sc' (i - 1) i (i + 1)).X₂) :=
    inferInstanceAs (FiniteDimensional k (C.X i))
  rw [h1]
  exact finrank_shortComplex_homology_add (C.sc' (i - 1) i (i + 1))

/-! ### The rank of a base-changed map is the rank of the base-changed matrix -/

/-- The `Module R S` structure of `φ.toAlgebra` is the restriction of scalars `Module.compHom`. -/
private theorem module_eq_compHom {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) :
    @Algebra.toModule R S _ _ φ.toAlgebra = Module.compHom S φ :=
  Module.ext' _ _ fun _ _ => rfl

/-- **Extension of scalars reads off the entrywise image of the matrix.**  For a homomorphism
`φ : R → S` and a map `d : M ⟶ N` of `R`-modules with chosen finite bases, the rank of the map
obtained from `d` by extension of scalars along `φ` is the rank of the entrywise image under `φ`
of the matrix of `d`: in the base-changed bases the two maps are the same. -/
theorem finrank_range_extendScalars_map {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M N : ModuleCat.{u} R} {m n : ℕ}
    (bM : Module.Basis (Fin n) R M) (bN : Module.Basis (Fin m) R N) (d : M ⟶ N) :
    Module.finrank S
        (LinearMap.range ((ModuleCat.extendScalars.{u, u, u} φ).map d).hom) =
      ((LinearMap.toMatrix bM bN d.hom).map φ).rank := by
  let : Algebra R S := φ.toAlgebra
  cases module_eq_compHom φ
  let bM' : Module.Basis (Fin n) S ((ModuleCat.extendScalars.{u, u, u} φ).obj M) :=
    Algebra.TensorProduct.basis S bM
  let bN' : Module.Basis (Fin m) S ((ModuleCat.extendScalars.{u, u, u} φ).obj N) :=
    Algebra.TensorProduct.basis S bN
  have hbM' : ∀ j, bM' j = (1 : S) ⊗ₜ[R] bM j := fun j =>
    Algebra.TensorProduct.basis_apply bM j
  have hbN' : ∀ l, bN' l = (1 : S) ⊗ₜ[R] bN l := fun l =>
    Algebra.TensorProduct.basis_apply bN l
  have hmap : ((ModuleCat.extendScalars.{u, u, u} φ).map d).hom =
      Matrix.toLin bM' bN' ((LinearMap.toMatrix bM bN d.hom).map φ) := by
    refine bM'.ext fun j => ?_
    rw [Matrix.toLin_self, hbM' j]
    have hdj : d.hom (bM j) =
        ∑ l : Fin m, (LinearMap.toMatrix bM bN d.hom) l j • bN l := by
      conv_lhs => rw [← Matrix.toLin_toMatrix bM bN d.hom]
      rw [Matrix.toLin_self]
    change (1 : S) ⊗ₜ[R] d.hom (bM j) = _
    rw [hdj, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hbN' l, TensorProduct.tmul_smul, Matrix.map_apply]
    change ((LinearMap.toMatrix bM bN d.hom) l j • (1 : S)) ⊗ₜ[R] bN l = _
    congr 1
  rw [hmap, Matrix.rank_eq_finrank_range_toLin _ bN' bM']

/-- Extension of scalars takes a finite module to a finite module. -/
theorem finite_extendScalars {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    (P : ModuleCat.{u} R) (hP : Module.Finite R P) :
    Module.Finite S ((ModuleCat.extendScalars.{u, u, u} φ).obj P) := by
  let : Module.Finite R P := hP
  let : Algebra R S := φ.toAlgebra
  cases module_eq_compHom φ
  exact Module.Finite.base_change R S P

/-- Extension of scalars does not change the rank of a free module. -/
theorem finrank_extendScalars {R S : Type u} [CommRing R] [CommRing S] [Nontrivial R]
    [Nontrivial S] (φ : R →+* S) (P : ModuleCat.{u} R) (hP : Module.Free R P) :
    Module.finrank S ((ModuleCat.extendScalars.{u, u, u} φ).obj P) = Module.finrank R P := by
  let : Module.Free R P := hP
  let : Algebra R S := φ.toAlgebra
  exact Module.finrank_baseChange

/-! ### The derived-fibre Betti numbers through the rank of two matrices -/

/-- **The derived-fibre Betti numbers of a pseudo-coherent object are read off from two matrices
over `R`.**  Let `K` be a pseudo-coherent object of `D(R)` and let `i` be an integer.  There are
natural numbers `a`, `b`, `c` and matrices `A₁` of size `b × a` and `A₂` of size `c × b` over `R`
such that for every prime `p`

`β_i(p) + rank_{κ(p)} A₂ + rank_{κ(p)} A₁ = b`.

Pseudo-coherence gives a bounded-above representative `F` with finite free terms; `a`, `b`, `c`
are the ranks of `F^{i-1}`, `F^i`, `F^{i+1}`, and `A₁`, `A₂` are the matrices of the
differentials `d^{i-1}` and `d^i` in chosen bases.  Base change along `R → κ(p)` computes the
derived fibre degreewise, and over the field `κ(p)` the dimension of `H^i`, the rank of `d^i` and
the rank of `d^{i-1}` add up to `dim F^i ⊗ κ(p) = b`. -/
theorem exists_matrix_fibreBetti_add_rank_add_rank_eq {R : Type u} [CommRing R] [Nontrivial R]
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ) :
    ∃ (a b c : ℕ) (A₁ : Matrix (Fin b) (Fin a) R) (A₂ : Matrix (Fin c) (Fin b) R),
      ∀ p : PrimeSpectrum R,
        fibreBetti.{u, u} K i p +
            (A₂.map (algebraMap R p.asIdeal.ResidueField)).rank +
          (A₁.map (algebraMap R p.asIdeal.ResidueField)).rank = b := by
  obtain ⟨F, hF, ⟨eF⟩⟩ := hK
  obtain ⟨bd, hbd⟩ := hF.upperBound
  let := hbd
  have hFfin : ∀ j : ℤ, Module.Finite R (F.X j) := fun j => (hF.finiteFree j).1
  let := hFfin
  have hFfree : ∀ j : ℤ, Module.Free R (F.X j) := fun j => (hF.finiteFree j).2
  let := hFfree
  have hFproj : ∀ j : ℤ, Projective (F.X j) := fun j =>
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (F.X j))
  let := hFproj
  refine ⟨Module.finrank R (F.X (i - 1)), Module.finrank R (F.X i),
    Module.finrank R (F.X (i + 1)),
    LinearMap.toMatrix (Module.finBasis R (F.X (i - 1))) (Module.finBasis R (F.X i))
      (F.d (i - 1) i).hom,
    LinearMap.toMatrix (Module.finBasis R (F.X i)) (Module.finBasis R (F.X (i + 1)))
      (F.d i (i + 1)).hom, fun p => ?_⟩
  set ψ : R →+* p.asIdeal.ResidueField := algebraMap R p.asIdeal.ResidueField
  set Pκ := ((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj F
  -- the derived fibre at `p` is computed degreewise by the representative
  have hbetti : fibreBetti.{u, u} K i p =
      Module.finrank p.asIdeal.ResidueField (Pκ.homology i) := by
    change Module.finrank p.asIdeal.ResidueField
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.asIdeal.ResidueField) i).obj
        ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          ψ).functor.obj K)) = _
    rw [finrank_homologyFunctor_eq_of_iso
      ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        ψ).functor.mapIso eF.symm) i]
    exact finrank_homologyFunctor_totalDerived_Q_obj.{u, u} ψ F bd i
  -- the term in degree `i` has the rank of `F^i`
  have : Module.Finite p.asIdeal.ResidueField (Pκ.X i) :=
    finite_extendScalars ψ (F.X i) (hFfin i)
  have hXi : Module.finrank p.asIdeal.ResidueField (Pκ.X i) = Module.finrank R (F.X i) :=
    finrank_extendScalars ψ (F.X i) (hFfree i)
  -- the ranks of the two differentials are the ranks of the base-changed matrices
  have hd : ∀ j k : ℤ, Module.finrank p.asIdeal.ResidueField (LinearMap.range (Pκ.d j k).hom) =
      ((LinearMap.toMatrix (Module.finBasis R (F.X j)) (Module.finBasis R (F.X k))
        (F.d j k).hom).map ψ).rank := fun j k =>
    finrank_range_extendScalars_map ψ _ _ (F.d j k)
  have hsum := finrank_homology_add Pκ i
  have := hd (i - 1) i
  have := hd i (i + 1)
  omega

/-! ### Constructibility of the level sets -/

/-- **The affine case of part (3) of [Stacks, Tag 0BDI].**  For a pseudo-coherent object `K` of
`D(R)` and integers `i`, `n`, the locus of primes `p` at which the `i`-th derived-fibre Betti
number of `K` equals `n` is a constructible subset of `PrimeSpectrum R`.

By `exists_matrix_fibreBetti_add_rank_add_rank_eq` the Betti number is `b - r₂ - r₁` for the
ranks `r₁`, `r₂` at `p` of two fixed matrices over `R`, so the level set is the finite union, over
the pairs `(r₂, r₁)` with `n + r₂ + r₁ = b`, of the intersections of two rank loci, and each rank
locus is constructible by `StacksDraft.MinorRank.isConstructible_rank_eq`. -/
theorem isConstructible_fibreBetti_preimage {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ) (n : ℕ) :
    IsConstructible (fibreBetti.{u, u} K i ⁻¹' {n}) := by
  classical
  by_cases hR : Nontrivial R
  · obtain ⟨a, b, c, A₁, A₂, hAB⟩ := exists_matrix_fibreBetti_add_rank_add_rank_eq K hK i
    set T : Finset (ℕ × ℕ) :=
      ((Finset.range (b + 1)) ×ˢ (Finset.range (b + 1))).filter
        (fun q => n + q.1 + q.2 = b) with hT
    have hset : fibreBetti.{u, u} K i ⁻¹' {n} = ⋃ q ∈ (T : Set (ℕ × ℕ)),
        ({p : PrimeSpectrum R |
            (A₂.map (algebraMap R p.asIdeal.ResidueField)).rank = q.1} ∩
          {p : PrimeSpectrum R |
            (A₁.map (algebraMap R p.asIdeal.ResidueField)).rank = q.2}) := by
      ext p
      have hp := hAB p
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_ofPred_eq, hT, Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
        Finset.mem_range, exists_prop]
      constructor
      · intro hn
        exact ⟨((A₂.map (algebraMap R p.asIdeal.ResidueField)).rank,
          (A₁.map (algebraMap R p.asIdeal.ResidueField)).rank),
          ⟨⟨by omega, by omega⟩, by omega⟩, rfl, rfl⟩
      · rintro ⟨q, ⟨-, hq⟩, h1, h2⟩
        omega
    rw [hset]
    exact Topology.IsConstructible.biUnion (Finset.finite_toSet _) fun q _ =>
      (StacksDraft.MinorRank.isConstructible_rank_eq A₂ q.1).inter
        (StacksDraft.MinorRank.isConstructible_rank_eq A₁ q.2)
  · -- the zero ring has no primes, so every subset of its spectrum is constructible
    rw [not_nontrivial_iff_subsingleton] at hR
    have : IsEmpty (PrimeSpectrum R) :=
      ⟨fun p => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
        (Subsingleton.elim (1 : R) 0 ▸ p.asIdeal.zero_mem))⟩
    rw [Set.eq_empty_of_isEmpty (fibreBetti.{u, u} K i ⁻¹' {n})]
    exact Topology.IsConstructible.empty

end StacksDraft.Perfect

end
