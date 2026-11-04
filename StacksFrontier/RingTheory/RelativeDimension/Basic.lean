module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksFrontier.RingTheory.RelativeDimension.Defs
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# Basic properties of the relative dimension

Let `R → S` be a ring map and let `𝔮` be a prime of `S` lying over `𝔭`. The relative dimension
`dim_𝔮(S/R)` is the dimension at `𝔮` of the fibre of `Spec(S) → Spec(R)` over `𝔭`. This file
computes it on the fibre ring `κ(𝔭) ⊗_R S`, shows that it is unchanged by principal localization,
and computes the relative dimension of an algebra all of whose fibres have the same dimension.

## Main results

* `Algebra.relativeDimensionAt_eq_localKrullDim`: `dim_𝔮(S/R)` is the local dimension of
  `Spec(κ(𝔭) ⊗_R S)` at the prime corresponding to `𝔮`.
* `Algebra.relativeDimensionAt_comap_eq`: the relative dimension is unchanged by passing to a
  principal localization `S_g`.
* `Algebra.relativeDimension_eq_of_forall_topologicalKrullDim_fiber`: an algebra all of whose
  fibres have dimension `d` has relative dimension `d`.
-/

@[expose] public section

open Algebra.TensorProduct

/-- A prime `𝔔` of the fibre `κ(𝔭) ⊗_R S` corresponds to a prime `𝔮` of `S` over `𝔭` under
`PrimeSpectrum.preimageHomeomorphFiber` exactly when `𝔔 ∩ S = 𝔮`. -/
private theorem preimageHomeomorphFiber_eq_iff_comap_includeRight_eq {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] {p : PrimeSpectrum R}
    (x : ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) (Q : PrimeSpectrum (p.asIdeal.Fiber S)) :
    PrimeSpectrum.preimageHomeomorphFiber R S p x = Q ↔
      Q.asIdeal.comap (includeRight : S →ₐ[R] p.asIdeal.Fiber S) = x.1.asIdeal := by
  rw [eq_comm, ← (PrimeSpectrum.preimageHomeomorphFiber R S p).symm_apply_eq, Subtype.ext_iff,
    PrimeSpectrum.ext_iff]
  rfl

/-- For a prime `𝔮` of `S` over `𝔭` and the prime `𝔔` of `κ(𝔭) ⊗_R S` with `𝔔 ∩ S = 𝔮`,
`dim_𝔮(S/R)` is the local dimension of `Spec(κ(𝔭) ⊗_R S)` at `𝔔`. -/
theorem Algebra.relativeDimensionAt_eq_localKrullDim {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] (p : Ideal R) [p.IsPrime] (hp : q.under R = p)
    (Q : Ideal (p.Fiber S)) [Q.IsPrime] (hQ : Q.comap (includeRight : S →ₐ[R] p.Fiber S) = q) :
    Algebra.relativeDimensionAt R q =
      TopologicalSpace.localKrullDim (PrimeSpectrum (p.Fiber S)) ⟨Q, ‹_›⟩ := by
  subst hp
  set e := PrimeSpectrum.preimageHomeomorphFiber R S
    (PrimeSpectrum.comap (algebraMap R S) ⟨q, ‹_›⟩)
  have he : e ⟨⟨q, ‹_›⟩, rfl⟩ = ⟨Q, ‹_›⟩ :=
    (preimageHomeomorphFiber_eq_iff_comap_includeRight_eq _ _).2 hQ
  rw [Algebra.relativeDimensionAt, topologicalKrullDimAt_eq_of_homeomorph e, he,
    TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  rfl

/-- For a localization `S_g` of `S` away from `g` and a prime `𝔔` of `S_g`,
`dim_{𝔔 ∩ S}(S/R) = dim_𝔔(S_g/R)`. -/
theorem Algebra.relativeDimensionAt_comap_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (g : S) (Sg : Type*) [CommRing Sg] [Algebra S Sg] [IsLocalization.Away g Sg]
    [Algebra R Sg] [IsScalarTower R S Sg] (Q : Ideal Sg) [Q.IsPrime] :
    Algebra.relativeDimensionAt R (Q.comap (algebraMap S Sg)) =
      Algebra.relativeDimensionAt R Q := by
  have hoe : Topology.IsOpenEmbedding (PrimeSpectrum.comap (algebraMap S Sg)) :=
    PrimeSpectrum.localization_away_isOpenEmbedding Sg g
  set x : PrimeSpectrum Sg := ⟨Q, ‹_›⟩
  set F := PrimeSpectrum.comap (algebraMap R S) ⁻¹'
    {PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S Sg) x)}
  have hcomp : PrimeSpectrum.comap (algebraMap R Sg) =
      PrimeSpectrum.comap (algebraMap R S) ∘ PrimeSpectrum.comap (algebraMap S Sg) := by
    rw [IsScalarTower.algebraMap_eq R S Sg, PrimeSpectrum.comap_comp]
  have hB : PrimeSpectrum.comap (algebraMap S Sg) ⁻¹' F =
      PrimeSpectrum.comap (algebraMap R Sg) ⁻¹' {PrimeSpectrum.comap (algebraMap R Sg) x} := by
    rw [hcomp, Set.preimage_comp]
    rfl
  calc Algebra.relativeDimensionAt R (Q.comap (algebraMap S Sg))
      = topologicalKrullDimAt F (F.restrictPreimage (PrimeSpectrum.comap (algebraMap S Sg))
          ⟨x, rfl⟩) := rfl
    _ = topologicalKrullDimAt (PrimeSpectrum.comap (algebraMap S Sg) ⁻¹' F) ⟨x, rfl⟩ :=
        (hoe.restrictPreimage F).topologicalKrullDimAt_eq _
    _ = Algebra.relativeDimensionAt R Q :=
        topologicalKrullDimAt_eq_of_homeomorph (Homeomorph.setCongr hB) _

/-- The relative dimension at a prime depends only on the prime. -/
theorem Algebra.relativeDimensionAt_congr {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I J : Ideal S} [I.IsPrime] [J.IsPrime] (h : I = J) :
    Algebra.relativeDimensionAt R I = Algebra.relativeDimensionAt R J := by
  subst h
  rfl

/-! ### Primes of the fibre -/

/-- Every prime `𝔮` of `S` over `𝔭` is `𝔔 ∩ S` for a prime `𝔔` of the fibre `κ(𝔭) ⊗_R S`. -/
theorem Ideal.Fiber.exists_comap_includeRight_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] (p : Ideal R) [p.IsPrime] (hp : q.under R = p) :
    ∃ Q : Ideal (p.Fiber S), Q.IsPrime ∧ Q.comap (includeRight : S →ₐ[R] p.Fiber S) = q := by
  subst hp
  set e := PrimeSpectrum.preimageHomeomorphFiber R S
    (PrimeSpectrum.comap (algebraMap R S) ⟨q, ‹_›⟩)
  exact ⟨_, (e ⟨⟨q, ‹_›⟩, rfl⟩).isPrime,
    (preimageHomeomorphFiber_eq_iff_comap_includeRight_eq ⟨⟨q, ‹_›⟩, rfl⟩ _).1 rfl⟩

/-- If the ideal `J ⊆ S` generates the unit ideal of the fibre `κ(𝔭) ⊗_R S`, then some element of
`J` becomes a unit in the fibre. -/
theorem Ideal.Fiber.exists_mem_isUnit_includeRight_of_one_mem_map {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsPrime] (J : Ideal S)
    (h1 : (1 : p.Fiber S) ∈ J.map (includeRight : S →ₐ[R] p.Fiber S)) :
    ∃ g ∈ J, IsUnit (includeRight (R := R) (A := p.ResidueField) g) := by
  classical
  rw [Ideal.map, Ideal.span, Submodule.mem_span_set'] at h1
  obtain ⟨n, c, j, hcj⟩ := h1
  choose a ha haj using fun i ↦ (j i).2
  choose r hr s hs using fun i ↦ Ideal.Fiber.exists_smul_eq_one_tmul p (c i)
  set g : S := ∑ i, algebraMap R S (∏ k ∈ Finset.univ.erase i, r k) * s i * a i
  refine ⟨g, Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (ha i), ?_⟩
  have hrκ : IsUnit (algebraMap R p.ResidueField (∏ k, r k)) := by
    rw [isUnit_iff_ne_zero, Ne, Ideal.algebraMap_residueField_eq_zero]
    exact fun hmem ↦ (Ideal.IsPrime.prod_mem_iff (p := p) (s := Finset.univ)).1 hmem |>.elim
      fun i ⟨_, hi⟩ ↦ hr i hi
  have hg : includeRight (R := R) (A := p.ResidueField) g =
      algebraMap p.ResidueField (p.Fiber S) (algebraMap R p.ResidueField (∏ k, r k)) := by
    rw [← IsScalarTower.algebraMap_apply, ← mul_one (algebraMap R (p.Fiber S) _),
      ← Algebra.smul_def, ← hcj, Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    symm
    calc (∏ k, r k) • (c i • (j i : p.Fiber S))
        = (∏ k ∈ Finset.univ.erase i, r k) • ((r i • c i) * (j i : p.Fiber S)) := by
          rw [← Finset.mul_prod_erase Finset.univ r (Finset.mem_univ i), mul_comm, mul_smul,
            smul_eq_mul, smul_mul_assoc]
      _ = (∏ k ∈ Finset.univ.erase i, r k) • ((1 ⊗ₜ[R] s i) * includeRight (a i)) := by
          rw [hs, haj]
      _ = includeRight (R := R) (A := p.ResidueField)
            (algebraMap R S (∏ k ∈ Finset.univ.erase i, r k) * s i * a i) := by
          rw [includeRight_apply, includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
            one_mul, ← TensorProduct.tmul_smul, Algebra.smul_def, mul_assoc]
  rw [hg]
  exact hrκ.map _

/-! ### The relative dimension of an algebra all of whose fibres have one dimension -/

/-- The relative dimension at a prime `q` lying over `p` is the dimension at `q` of the fibre
over `p`. -/
private lemma Algebra.relativeDimensionAt_eq_topologicalKrullDimAt_fiber {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (p : PrimeSpectrum R) (q : PrimeSpectrum S)
    (hq : PrimeSpectrum.comap (algebraMap R S) q = p) :
    Algebra.relativeDimensionAt R q.asIdeal =
      topologicalKrullDimAt ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) ⟨q, hq⟩ := by
  subst hq
  rfl

/-- If the base has a prime and every fibre of `Spec(S) → Spec(R)` has dimension `d`, then the
relative dimension of `S` over `R` is `d`. The converse fails, by
`Algebra.not_forall_relativeDimension_eq_topologicalKrullDim_fiber`. -/
theorem Algebra.relativeDimension_eq_of_forall_topologicalKrullDim_fiber {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] [Nonempty (PrimeSpectrum R)] (d : WithBot ℕ∞)
    (h : ∀ p : PrimeSpectrum R,
      topologicalKrullDim ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}) = d) :
    Algebra.relativeDimension R S = d := by
  refine le_antisymm (iSup_le fun q => ?_) ?_
  · rw [Algebra.relativeDimensionAt_eq_topologicalKrullDimAt_fiber
      (PrimeSpectrum.comap (algebraMap R S) q) q rfl, ← h]
    exact topologicalKrullDimAt_le_topologicalKrullDim _
  · obtain ⟨p₀⟩ := ‹Nonempty (PrimeSpectrum R)›
    rw [← h p₀, TopologicalSpace.topologicalKrullDim_eq_iSup_localKrullDim]
    refine iSup_le fun w => ?_
    rw [← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
      ← Algebra.relativeDimensionAt_eq_topologicalKrullDimAt_fiber p₀ w.1 w.2]
    exact le_iSup (fun q : PrimeSpectrum S => Algebra.relativeDimensionAt R q.asIdeal) w.1

end
