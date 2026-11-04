module

public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
import all StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.RingTheory.Henselian.Colimit
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.ExistenceData

/-!
# Strict henselization commutes with filtered colimits of local rings

Let `(R_i, f_{ij})` be a directed system of local rings along local homomorphisms, with colimit
`R = colim R_i`, and let `R_i → R_i^{sh}` be strict henselizations together with ring maps
`R_i^{sh} → R_j^{sh}` over the `f_{ij}` forming a directed system. Then `colim R_i^{sh}` is a
strict henselization of `R`, with respect to any separable algebraic closure of the residue field
of `R` (Travaux de Gabber, Exposé XVIII-A, last remark of §2, where it identifies the strict
henselization of a valuation ring at a point of the Zariski–Riemann space with the colimit of the
strict henselizations of the local rings of the models at the centers).

The four properties of Stacks 04GP are checked one by one on `T = colim R_i^{sh}` over
`S = colim R_i`:

* `T` is a strictly henselian local ring and `S → T` is local: Stacks 04GI
  (`part1_isLocalRing`, `part2_henselian`, `part3_strictlyHenselian`), the transition maps of the
  strict henselizations being local because `𝔪_{R_i} R_i^{sh}` is the maximal ideal of `R_i^{sh}`;
* `T` is ind-étale over `S`: by the factorization criterion of Stacks 07C3, a map `C → T` from a
  finitely presented `S`-algebra descends, generators, relations and all, to a map
  `C_k → R_k^{sh}` from a finitely presented `R_k`-algebra at a finite stage `k`; it factors
  through an étale `R_k`-algebra `E_k` because `R_k^{sh}` is ind-étale over `R_k`, so `C → T`
  factors through the étale `S`-algebra `S ⊗_{R_k} E_k`;
* `𝔪_T = 𝔪_S T`, because `𝔪_T` is the union of the images of the `𝔪_{R_i^{sh}} = 𝔪_{R_i} R_i^{sh}`;
* the residue field of `T` is a separable algebraic closure of that of `S`: it is separably closed
  by 04GI, and separable algebraic because every element comes from some `κ(R_i^{sh}) = κ_i^{sep}`,
  where it is a root of a separable polynomial over `κ(R_i)` whose image over `κ(S)` it still
  annihilates.

## Main results

* `Stacks.StrictHenselization.DirectLimit.indEtale_directLimit`: a directed colimit of ind-étale
  algebras over a directed colimit of bases is ind-étale over the colimit base.
* `Stacks.StrictHenselization.DirectLimit.isStrictHenselization_directLimit`: **the colimit of the
  strict henselizations is a strict henselization of the colimit.**
* `Stacks.StrictHenselization.DirectLimit.subringDirectLimitEquiv`: a directed union of subrings is
  their direct limit.

## Implementation notes

The algebra structure of `colim R_i^{sh}` over `colim R_i` is taken as an instance together with
the condition `halg` that the structure maps `R_i^{sh} → colim R_i^{sh}` are compatible with it;
`Ring.DirectLimit.map` provides one. The local-ring instances on the two colimits are taken as
instance arguments: they are `Prop`s, provided by `part1_isLocalRing`, so any two agree.

The factorization criterion of Stacks 07C3 is `StacksDraft.ind_etale_iff_factorization`, which
is private to `StacksFrontier.RingTheory.Etale.IndEtaleUniverse`, hence the `import all`.

No compatibility between the chosen separable closures `κ_i^{sep}` is needed: the separable
closure of the colimit is an arbitrary one, `κ`, and the identification of the residue field of
`colim R_i^{sh}` with it is the unique-up-to-isomorphism one of `IsSepClosure.equiv`.

## References

* [StacksProject 04GI](https://stacks.math.columbia.edu/tag/04GI)
* [StacksProject 04GP](https://stacks.math.columbia.edu/tag/04GP)
* [StacksProject 07C3](https://stacks.math.columbia.edu/tag/07C3)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing
open scoped TensorProduct

universe u w

namespace Stacks.StrictHenselization.DirectLimit

section Generic

variable {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {G : ι → Type u} [∀ i, CommRing (G i)] (g : ∀ i j, i ≤ j → G i →+* G j)

/-- Every element of a directed colimit comes from every sufficiently large stage. -/
theorem exists_of_forall_le (z : colimitRing G g) :
    ∃ i, ∀ j, i ≤ j → ∃ x, colimitOf G g j x = z := by
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
  exact ⟨i, fun j hij => ⟨g i j hij x, Ring.DirectLimit.of_f hij x⟩⟩

/-- Every polynomial over a directed colimit has its coefficients in every sufficiently large
stage. -/
theorem exists_mvPolynomial_forall_le {σ : Type*} (p : MvPolynomial σ (colimitRing G g)) :
    ∃ i, ∀ j, i ≤ j → p ∈ Set.range (MvPolynomial.map (colimitOf G g j)) := by
  classical
  choose idx hidx using fun c : colimitRing G g => exists_of_forall_le g c
  obtain ⟨i, hi⟩ := Finset.exists_le (p.coeffs.image idx)
  refine ⟨i, fun j hij => MvPolynomial.mem_range_map_iff_coeffs_subset.mpr ?_⟩
  intro c hc
  exact hidx c j ((hi _ (Finset.mem_image_of_mem _ (Finset.mem_coe.mp hc))).trans hij)

variable [DirectedSystem G fun i j h => g i j h]

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] in
/-- The transition maps of a directed system compose. -/
theorem map_map {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (x : G i) :
    g j k hjk (g i j hij x) = g i k (hij.trans hjk) x :=
  DirectedSystem.map_map (f := fun i j h => g i j h) hij hjk x

/-- Finitely many elements of a stage that vanish in the colimit vanish at one later stage. -/
theorem exists_le_forall_eq_zero {J : Type*} [Finite J] {i : ι} (x : J → G i)
    (hx : ∀ t, colimitOf G g i (x t) = 0) :
    ∃ k, ∃ hik : i ≤ k, ∀ t, g i k hik (x t) = 0 := by
  classical
  have := Fintype.ofFinite J
  choose j hij hj using fun t => Ring.DirectLimit.of.zero_exact (hx t)
  obtain ⟨k, hk⟩ := Finset.exists_le (insert i (Finset.univ.image j))
  have hik : i ≤ k := hk i (Finset.mem_insert_self _ _)
  refine ⟨k, hik, fun t => ?_⟩
  have hjk : j t ≤ k := hk _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (by simp)))
  rw [← map_map g (hij t) hjk, hj t, map_zero]

end Generic

section IndEtale

variable {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {R : ι → Type u} [∀ i, CommRing (R i)] (f : ∀ i j, i ≤ j → R i →+* R j)
  {Rsh : ι → Type u} [∀ i, CommRing (Rsh i)] [∀ i, Algebra (R i) (Rsh i)]
  (fsh : ∀ i j, i ≤ j → Rsh i →+* Rsh j) [DirectedSystem Rsh fun i j h => fsh i j h]

/-- **A directed colimit of ind-étale algebras is ind-étale over the colimit of the bases.** Let
`(R_i)` and `(Rsh_i)` be directed systems, with `Rsh_i` an ind-étale `R_i`-algebra and the
transition maps compatible with the structure maps. Then `colim Rsh_i` is ind-étale over
`colim R_i`, for an algebra structure making the maps `Rsh_i → colim Rsh_i` compatible with the
maps `R_i → colim R_i`. -/
theorem indEtale_directLimit
    (hcomm : ∀ i j (hij : i ≤ j) x,
      fsh i j hij (algebraMap (R i) (Rsh i) x) = algebraMap (R j) (Rsh j) (f i j hij x))
    [Algebra (colimitRing R f) (colimitRing Rsh fsh)]
    (halg : ∀ i x, algebraMap (colimitRing R f) (colimitRing Rsh fsh) (colimitOf R f i x) =
      colimitOf Rsh fsh i (algebraMap (R i) (Rsh i) x))
    (hind : ∀ i, (CommAlgCat.etale (R i)).ind.{u} (CommAlgCat.of (R i) (Rsh i))) :
    (CommAlgCat.etale (colimitRing R f)).ind.{max w u}
      (CommAlgCat.of (colimitRing R f) (colimitRing Rsh fsh)) := by
  classical
  rw [StacksDraft.ind_etale_iff_factorization]
  intro C _ _ _ φ
  obtain ⟨n, π, hπ, s, hs⟩ := Algebra.FinitePresentation.out (R := colimitRing R f) (A := C)
  -- descend the relations and the images of the generators to a common stage `i₀`
  choose ig hig using fun g : s => exists_mvPolynomial_forall_le f g.1
  choose iy hiy using fun t : Fin n => exists_of_forall_le fsh (φ (π (MvPolynomial.X t)))
  obtain ⟨i₀, hi₀⟩ := Finset.exists_le (Finset.univ.image ig ∪ Finset.univ.image iy)
  choose G hG using fun g : s => hig g i₀ (hi₀ _ (by simp))
  choose b hb using fun t : Fin n => hiy t i₀ (hi₀ _ (by simp))
  -- `φ ∘ π` is evaluation at the images of the generators
  have hev : ∀ p, MvPolynomial.aeval (fun t => φ (π (MvPolynomial.X t))) p = φ (π p) :=
    fun p => (AlgHom.congr_fun (MvPolynomial.aeval_unique (φ.comp π)) p).symm
  have hcompat : (colimitOf Rsh fsh i₀).comp (algebraMap (R i₀) (Rsh i₀)) =
      (algebraMap (colimitRing R f) (colimitRing Rsh fsh)).comp (colimitOf R f i₀) :=
    RingHom.ext fun x => (halg i₀ x).symm
  -- the relations hold at the stage `i₀` after passing to the colimit
  have hzero : ∀ g : s, colimitOf Rsh fsh i₀ (MvPolynomial.aeval b (G g)) = 0 := by
    intro g
    have hg : π g.1 = 0 := by
      have hmem : g.1 ∈ RingHom.ker π.toRingHom := hs ▸ Submodule.subset_span g.2
      exact hmem
    rw [MvPolynomial.map_aeval, MvPolynomial.coe_eval₂Hom, hcompat]
    simp only [hb]
    rw [← MvPolynomial.eval₂_map, hG g, ← MvPolynomial.aeval_def, hev, hg, map_zero]
  -- so they hold at a later stage `k`
  obtain ⟨k, hk, hk0⟩ := exists_le_forall_eq_zero fsh (fun g : s => MvPolynomial.aeval b (G g))
    hzero
  let G' : s → MvPolynomial (Fin n) (R k) := fun g => MvPolynomial.map (f i₀ k hk) (G g)
  let b' : Fin n → Rsh k := fun t => fsh i₀ k hk (b t)
  have hG' : ∀ g, MvPolynomial.aeval b' (G' g) = 0 := by
    intro g
    have hc : (algebraMap (R k) (Rsh k)).comp (f i₀ k hk) =
        (fsh i₀ k hk).comp (algebraMap (R i₀) (Rsh i₀)) :=
      RingHom.ext fun x => (hcomm i₀ k hk x).symm
    rw [← hk0 g, MvPolynomial.map_aeval, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, hc]
    rfl
  -- the finitely presented `R_k`-algebra `C_k` and its map to `Rsh_k`
  let I : Ideal (MvPolynomial (Fin n) (R k)) := Ideal.span (Set.range G')
  have : Algebra.FinitePresentation (R k) (MvPolynomial (Fin n) (R k) ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range G'))
  have hIker : I ≤ RingHom.ker (MvPolynomial.aeval (R := R k) b') :=
    Ideal.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact RingHom.mem_ker.mpr (hG' g))
  let uk : (MvPolynomial (Fin n) (R k) ⧸ I) →ₐ[R k] Rsh k :=
    Ideal.Quotient.liftₐ I (MvPolynomial.aeval b') fun a ha => RingHom.mem_ker.mp (hIker ha)
  obtain ⟨E, _, _, hEt, gk, hk', hgh⟩ := StacksDraft.ind_etale_iff_factorization.mp (hind k) _ uk
  -- the étale `S`-algebra `S ⊗_{R_k} E`
  let : Algebra (R k) (colimitRing R f) := (colimitOf R f k).toAlgebra
  let : Algebra (R k) (colimitRing Rsh fsh) :=
    ((algebraMap (colimitRing R f) (colimitRing Rsh fsh)).comp (colimitOf R f k)).toAlgebra
  have : IsScalarTower (R k) (colimitRing R f) (colimitRing Rsh fsh) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let δ : E →ₐ[R k] colimitRing Rsh fsh :=
    { toRingHom := (colimitOf Rsh fsh k).comp hk'.toRingHom
      commutes' := fun r => by
        change colimitOf Rsh fsh k (hk' (algebraMap (R k) E r)) =
          algebraMap (colimitRing R f) (colimitRing Rsh fsh) (colimitOf R f k r)
        rw [hk'.commutes, halg] }
  let γ : colimitRing R f ⊗[R k] E →ₐ[colimitRing R f] colimitRing Rsh fsh :=
    AlgHom.liftEquiv (R k) (colimitRing R f) E (colimitRing Rsh fsh) δ
  let ψ : MvPolynomial (Fin n) (R k) →ₐ[R k] colimitRing R f ⊗[R k] E :=
    Algebra.TensorProduct.includeRight.comp (gk.comp (Ideal.Quotient.mkₐ (R k) I))
  let β : MvPolynomial (Fin n) (colimitRing R f) →ₐ[colimitRing R f]
      colimitRing R f ⊗[R k] E :=
    MvPolynomial.aeval fun t => ψ (MvPolynomial.X t)
  have hβψ : ∀ P, β (MvPolynomial.map (colimitOf R f k) P) = ψ P := by
    intro P
    change MvPolynomial.aeval _ (MvPolynomial.map (algebraMap (R k) (colimitRing R f)) P) = _
    rw [MvPolynomial.aeval_map_algebraMap]
    exact (AlgHom.congr_fun (MvPolynomial.aeval_unique ψ) P).symm
  have hβ : ∀ a ∈ RingHom.ker π, β a = 0 := by
    have hle : RingHom.ker π ≤ RingHom.ker β := by
      change RingHom.ker π.toRingHom ≤ _
      rw [← hs]
      refine Submodule.span_le.mpr ?_
      intro g hg
      refine RingHom.mem_ker.mpr ?_
      have hgG : g = MvPolynomial.map (colimitOf R f k) (G' ⟨g, hg⟩) := by
        have hof : (colimitOf R f k).comp (f i₀ k hk) = colimitOf R f i₀ :=
          RingHom.ext fun x => Ring.DirectLimit.of_f hk x
        rw [MvPolynomial.map_map, hof, hG ⟨g, hg⟩]
      rw [hgG, hβψ]
      change Algebra.TensorProduct.includeRight (gk (Ideal.Quotient.mk I (G' ⟨g, hg⟩))) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self _)), map_zero,
        map_zero]
    exact fun a ha => RingHom.mem_ker.mp (hle ha)
  let α : C →ₐ[colimitRing R f] colimitRing R f ⊗[R k] E :=
    (Ideal.Quotient.liftₐ (RingHom.ker π) β hβ).comp
      (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toAlgHom
  have hαπ : ∀ p, α (π p) = β p := by
    intro p
    change Ideal.Quotient.liftₐ (RingHom.ker π) β hβ
      ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm (π p)) = β p
    rw [← Ideal.quotientKerAlgEquivOfSurjective_mk hπ p, AlgEquiv.symm_apply_apply]
    rfl
  refine ⟨colimitRing R f ⊗[R k] E, inferInstance, inferInstance, inferInstance, α, γ,
    (AlgHom.cancel_right hπ).mp (MvPolynomial.algHom_ext fun t => ?_)⟩
  simp only [AlgHom.comp_apply]
  rw [hαπ, ← hb t]
  change γ (MvPolynomial.aeval (fun t => ψ (MvPolynomial.X t)) (MvPolynomial.X t)) = _
  rw [MvPolynomial.aeval_X]
  change γ (Algebra.TensorProduct.includeRight
    (gk (Ideal.Quotient.mkₐ (R k) I (MvPolynomial.X t)))) = _
  rw [Algebra.TensorProduct.includeRight_apply, AlgHom.liftEquiv_tmul, one_smul]
  change colimitOf Rsh fsh k (hk' (gk (Ideal.Quotient.mkₐ (R k) I (MvPolynomial.X t)))) = _
  rw [← AlgHom.comp_apply hk' gk, hgh]
  change colimitOf Rsh fsh k (MvPolynomial.aeval b' (MvPolynomial.X t)) = _
  rw [MvPolynomial.aeval_X]
  exact Ring.DirectLimit.of_f hk (b t)

end IndEtale

section StrictHenselization

variable {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {R : ι → Type u} [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)]
  (f : ∀ i j, i ≤ j → R i →+* R j) [DirectedSystem R fun i j h => f i j h]
  {Rsh : ι → Type u} [∀ i, CommRing (Rsh i)] [∀ i, IsLocalRing (Rsh i)]
  [∀ i, Algebra (R i) (Rsh i)]
  (fsh : ∀ i j, i ≤ j → Rsh i →+* Rsh j) [DirectedSystem Rsh fun i j h => fsh i j h]
  {κsep : ι → Type*} [∀ i, Field (κsep i)]
  [∀ i, Algebra (maximalIdeal (R i)).ResidueField (κsep i)]
  [∀ i, IsSepClosure (maximalIdeal (R i)).ResidueField (κsep i)]

/-- The two models of the residue field of a local ring are separably closed simultaneously. -/
private theorem isSepClosed_residueField_iff {A : Type*} [CommRing A] [IsLocalRing A] :
    IsSepClosed (ResidueField A) ↔ IsSepClosed (maximalIdeal A).ResidueField := by
  let e := AlgEquiv.ofBijective (Algebra.ofId (ResidueField A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))
  exact ⟨fun _ => IsSepClosed.of_ringEquiv e.symm.toRingEquiv,
    fun _ => IsSepClosed.of_ringEquiv e.toRingEquiv⟩

omit [IsDirected ι (· ≤ ·)] [Nonempty ι] [DirectedSystem R fun i j h => f i j h]
  [DirectedSystem Rsh fun i j h => fsh i j h] in
/-- **Maps of strict henselizations over local maps are local.** If `R_i → R_j` is local and the
ring map `R_i^{sh} → R_j^{sh}` lies over it, then it is local: it carries
`𝔪_{R_i^{sh}} = 𝔪_{R_i} R_i^{sh}` into `𝔪_{R_j} R_j^{sh} = 𝔪_{R_j^{sh}}`. -/
theorem isLocalHom_transition (hf : ∀ i j h, IsLocalHom (f i j h))
    (hsh : ∀ i, IsStrictHenselization (R i) (κsep i) (Rsh i))
    (hcomm : ∀ i j (hij : i ≤ j) x,
      fsh i j hij (algebraMap (R i) (Rsh i) x) = algebraMap (R j) (Rsh j) (f i j hij x))
    (i j : ι) (hij : i ≤ j) : IsLocalHom (fsh i j hij) := by
  have := hf i j hij
  refine ((local_hom_TFAE (fsh i j hij)).out 3 1).mp ?_
  have hc : (fsh i j hij).comp (algebraMap (R i) (Rsh i)) =
      (algebraMap (R j) (Rsh j)).comp (f i j hij) :=
    RingHom.ext (hcomm i j hij)
  rw [← (hsh i).maximalIdeal_map, Ideal.map_map, hc, ← Ideal.map_map,
    ← (hsh j).maximalIdeal_map]
  exact Ideal.map_mono (map_maximalIdeal_le (f i j hij))

/-- **Strict henselization commutes with directed colimits of local rings along local maps.**
Let `(R_i, f_{ij})` be a directed system of local rings along local homomorphisms, let
`R_i → R_i^{sh}` be a strict henselization of `R_i` (with respect to some separable algebraic
closure `κ_i^{sep}` of its residue field) and let `R_i^{sh} → R_j^{sh}` be ring maps over the
`f_{ij}` forming a directed system. Equip `colim R_i^{sh}` with an algebra structure over
`colim R_i` compatible with the structure maps (`halg`). Then `colim R_i^{sh}` is a strict
henselization of `colim R_i`, with respect to any separable algebraic closure `κ` of the residue
field of `colim R_i`. -/
theorem isStrictHenselization_directLimit (hf : ∀ i j h, IsLocalHom (f i j h))
    (hsh : ∀ i, IsStrictHenselization (R i) (κsep i) (Rsh i))
    (hcomm : ∀ i j (hij : i ≤ j) x,
      fsh i j hij (algebraMap (R i) (Rsh i) x) = algebraMap (R j) (Rsh j) (f i j hij x))
    [Algebra (colimitRing R f) (colimitRing Rsh fsh)]
    (halg : ∀ i x, algebraMap (colimitRing R f) (colimitRing Rsh fsh) (colimitOf R f i x) =
      colimitOf Rsh fsh i (algebraMap (R i) (Rsh i) x))
    [IsLocalRing (colimitRing R f)] [IsLocalRing (colimitRing Rsh fsh)]
    (κ : Type*) [Field κ] [Algebra (maximalIdeal (colimitRing R f)).ResidueField κ]
    [IsSepClosure (maximalIdeal (colimitRing R f)).ResidueField κ] :
    Nonempty (IsStrictHenselization (colimitRing R f) κ (colimitRing Rsh fsh)) := by
  classical
  have hfsh := isLocalHom_transition f fsh hf hsh hcomm
  have hofR : ∀ i, IsLocalHom (colimitOf R f i) := part1_of_isLocalHom R f hf
  have hofT : ∀ i, IsLocalHom (colimitOf Rsh fsh i) := part1_of_isLocalHom Rsh fsh hfsh
  have hcompat : ∀ i, (colimitOf Rsh fsh i).comp (algebraMap (R i) (Rsh i)) =
      (algebraMap (colimitRing R f) (colimitRing Rsh fsh)).comp (colimitOf R f i) :=
    fun i => RingHom.ext fun x => (halg i x).symm
  -- the structure map is local
  have hloc : IsLocalHom (algebraMap (colimitRing R f) (colimitRing Rsh fsh)) := by
    refine ⟨fun x hx => ?_⟩
    obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of x
    rw [halg] at hx
    have := hofT i
    have := (hsh i).isLocalHom
    have h1 : IsUnit (algebraMap (R i) (Rsh i) a) := IsUnit.of_map (colimitOf Rsh fsh i) _ hx
    exact (IsUnit.of_map (algebraMap (R i) (Rsh i)) a h1).map (colimitOf R f i)
  -- strictly henselian (Stacks 04GI)
  have hhens : HenselianLocalRing (colimitRing Rsh fsh) :=
    part2_henselian Rsh fsh hfsh fun i => (hsh i).henselian
  have hsepT : IsSepClosed (maximalIdeal (colimitRing Rsh fsh)).ResidueField := by
    have hsepi : ∀ i, IsSepClosed (ResidueField (Rsh i)) := fun i =>
      isSepClosed_residueField_iff.mpr (hsh i).sepClosed
    exact isSepClosed_residueField_iff.mp
      (part3_strictlyHenselian Rsh fsh hfsh (fun i => (hsh i).henselian) hsepi).2
  -- ind-étale
  have hind := StacksDraft.indEtale_iff.mpr (indEtale_directLimit f fsh hcomm halg fun i =>
    StacksDraft.indEtale_iff.mp (hsh i).isFilteredColimitEtale)
  -- the maximal ideal is generated by the image of the maximal ideal
  have hmax : (maximalIdeal (colimitRing R f)).map
      (algebraMap (colimitRing R f) (colimitRing Rsh fsh)) =
        maximalIdeal (colimitRing Rsh fsh) := by
    refine le_antisymm (map_maximalIdeal_le _) fun z hz => ?_
    obtain ⟨i, x, rfl, hx⟩ := (part1_mem_maximalIdeal Rsh fsh hfsh z).mp hz
    rw [← (hsh i).maximalIdeal_map] at hx
    have h1 : colimitOf Rsh fsh i x ∈
        ((maximalIdeal (R i)).map (algebraMap (R i) (Rsh i))).map (colimitOf Rsh fsh i) :=
      Ideal.mem_map_of_mem _ hx
    rw [Ideal.map_map, hcompat i, ← Ideal.map_map] at h1
    have := hofR i
    exact Ideal.map_mono (map_maximalIdeal_le (colimitOf R f i)) h1
  -- the residue field is a separable algebraic closure of that of the base
  let κ₀ := (maximalIdeal (colimitRing Rsh fsh)).ResidueField
  let : Algebra (maximalIdeal (colimitRing R f)).ResidueField κ₀ :=
    (Ideal.ResidueField.map (maximalIdeal (colimitRing R f)) (maximalIdeal (colimitRing Rsh fsh))
      (algebraMap (colimitRing R f) (colimitRing Rsh fsh))
      (maximalIdeal_comap _).symm).toAlgebra
  have hsepar : Algebra.IsSeparable (maximalIdeal (colimitRing R f)).ResidueField κ₀ := by
    refine ⟨fun y => ?_⟩
    obtain ⟨t, rfl⟩ :=
      Ideal.algebraMap_residueField_surjective (maximalIdeal (colimitRing Rsh fsh)) y
    obtain ⟨i, b, rfl⟩ := Ring.DirectLimit.exists_of t
    have := hofR i
    have := hofT i
    have := (hsh i).isLocalHom
    let e := (hsh i).residueFieldEquiv
    let z := e.symm (algebraMap (Rsh i) (maximalIdeal (Rsh i)).ResidueField b)
    have hz : IsSeparable (maximalIdeal (R i)).ResidueField z :=
      Algebra.IsSeparable.isSeparable _ z
    obtain ⟨P, hP⟩ := Polynomial.map_surjective
      (f := algebraMap (R i) (maximalIdeal (R i)).ResidueField)
      (Ideal.algebraMap_residueField_surjective (maximalIdeal (R i)))
      (minpoly (maximalIdeal (R i)).ResidueField z)
    -- `P(b)` lies in the maximal ideal of `Rsh i`
    have hsq : (algebraMap (Rsh i) (maximalIdeal (Rsh i)).ResidueField).comp
          (algebraMap (R i) (Rsh i)) =
        (e : κsep i →+* _).comp ((algebraMap _ (κsep i)).comp
          (algebraMap (R i) (maximalIdeal (R i)).ResidueField)) := by
      rw [← RingHom.comp_assoc, (hsh i).residueFieldEquiv_comp]
      exact RingHom.ext fun r => (Ideal.ResidueField.map_algebraMap _ _ _ _ r).symm
    have he : algebraMap (Rsh i) (maximalIdeal (Rsh i)).ResidueField b =
        (e : κsep i →+* _) z :=
      (e.apply_symm_apply _).symm
    have hPb : P.eval₂ (algebraMap (R i) (Rsh i)) b ∈ maximalIdeal (Rsh i) := by
      rw [← Ideal.algebraMap_residueField_eq_zero, Polynomial.hom_eval₂, hsq, he,
        ← Polynomial.hom_eval₂, ← Polynomial.eval₂_map, hP, ← Polynomial.aeval_def,
        minpoly.aeval, map_zero]
    -- so its image in the residue field of the colimit vanishes
    have hTzero : algebraMap (colimitRing Rsh fsh) κ₀
        (colimitOf Rsh fsh i (P.eval₂ (algebraMap (R i) (Rsh i)) b)) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr
        (map_nonunit (colimitOf Rsh fsh i) _ hPb)
    let φi := Ideal.ResidueField.map (maximalIdeal (R i)) (maximalIdeal (colimitRing R f))
      (colimitOf R f i) (maximalIdeal_comap _).symm
    have hφ : (algebraMap (colimitRing R f) (maximalIdeal (colimitRing R f)).ResidueField).comp
          (colimitOf R f i) =
        φi.comp (algebraMap (R i) (maximalIdeal (R i)).ResidueField) :=
      RingHom.ext fun r => (Ideal.ResidueField.map_algebraMap _ _ _ _ r).symm
    let Q := P.map ((algebraMap (colimitRing R f)
      (maximalIdeal (colimitRing R f)).ResidueField).comp (colimitOf R f i))
    have hQsep : Q.Separable := by
      change (P.map _).Separable
      rw [hφ, ← Polynomial.map_map, hP]
      exact Polynomial.Separable.map hz
    have hsq2 : (algebraMap (maximalIdeal (colimitRing R f)).ResidueField κ₀).comp
          ((algebraMap (colimitRing R f) (maximalIdeal (colimitRing R f)).ResidueField).comp
            (colimitOf R f i)) =
        (algebraMap (colimitRing Rsh fsh) κ₀).comp
          ((colimitOf Rsh fsh i).comp (algebraMap (R i) (Rsh i))) := by
      refine RingHom.ext fun r => ?_
      change Ideal.ResidueField.map _ _ (algebraMap (colimitRing R f) (colimitRing Rsh fsh)) _
        (algebraMap (colimitRing R f) _ (colimitOf R f i r)) =
          algebraMap (colimitRing Rsh fsh) κ₀ (colimitOf Rsh fsh i (algebraMap (R i) (Rsh i) r))
      rw [Ideal.ResidueField.map_algebraMap, halg]
    have hQroot : Polynomial.aeval
        (algebraMap (colimitRing Rsh fsh) κ₀ (colimitOf Rsh fsh i b)) Q = 0 := by
      rw [Polynomial.aeval_def, Polynomial.eval₂_map, hsq2,
        ← Polynomial.hom_eval₂ (p := P) (f := (colimitOf Rsh fsh i).comp
          (algebraMap (R i) (Rsh i))) (g := algebraMap (colimitRing Rsh fsh) κ₀),
        ← Polynomial.hom_eval₂ (p := P) (f := algebraMap (R i) (Rsh i))
          (g := colimitOf Rsh fsh i), hTzero]
    exact Polynomial.Separable.of_dvd hQsep (minpoly.dvd _ _ hQroot)
  have : IsSepClosure (maximalIdeal (colimitRing R f)).ResidueField κ₀ := ⟨hsepT, hsepar⟩
  let H : IsStrictHenselization (colimitRing R f) κ₀ (colimitRing Rsh fsh) :=
    { isLocalHom := hloc
      henselian := hhens
      sepClosed := hsepT
      isFilteredColimitEtale := hind
      maximalIdeal_map := hmax
      residueFieldEquiv := RingEquiv.refl _
      residueFieldEquiv_comp := rfl }
  exact ⟨H.reindex (IsSepClosure.equiv _ κ κ₀)⟩

end StrictHenselization

section Subrings

variable {V : Type u} [CommRing V] {ι : Type w} [Preorder ι] (A : ι → Subring V)
  (hA : Monotone A)

/-- The inclusions `A_i ⊆ A_j` of a monotone family of subrings, as a directed system. -/
def subringInclusion (i j : ι) (hij : i ≤ j) : A i →+* A j :=
  Subring.inclusion (hA hij)

/-- The inclusions of a monotone family of subrings form a directed system. -/
theorem directedSystem_subringInclusion :
    DirectedSystem (fun i => A i) fun i j h => subringInclusion A hA i j h :=
  ⟨fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-- The inclusions of a monotone family of subrings commute with the inclusions into `V`. -/
theorem subtype_subringInclusion (i j : ι) (hij : i ≤ j) (x : A i) :
    (A j).subtype (subringInclusion A hA i j hij x) = (A i).subtype x :=
  rfl

/-- **A directed union of subrings is their direct limit.** If the monotone family `A_i` of
subrings of `V` exhausts `V` over a directed index, the direct limit of the `A_i` along the
inclusions is `V`. -/
def subringDirectLimitEquiv [IsDirected ι (· ≤ ·)] [Nonempty ι] (hsup : ⨆ i, A i = ⊤) :
    colimitRing (fun i => A i) (subringInclusion A hA) ≃+* V :=
  have := directedSystem_subringInclusion A hA
  RingEquiv.ofBijective
    (Ring.DirectLimit.lift (fun i => A i) (fun i j h => subringInclusion A hA i j h) V
      (fun i => (A i).subtype) (subtype_subringInclusion A hA))
    ⟨by
      apply Ring.DirectLimit.lift_injective
      exact fun i => Subtype.val_injective,
    fun x => by
      have hx : x ∈ ⨆ i, A i := hsup ▸ Subring.mem_top x
      obtain ⟨i, hi⟩ := (Subring.mem_iSup_of_directed hA.directed_le).mp hx
      exact ⟨colimitOf (fun i => A i) (subringInclusion A hA) i ⟨x, hi⟩,
        Ring.DirectLimit.lift_of _ _ _ _ _⟩⟩

/-- The identification of the direct limit of a directed union of subrings with the union sends
the class of `x ∈ A_i` to `x`. -/
theorem subringDirectLimitEquiv_of [IsDirected ι (· ≤ ·)] [Nonempty ι] (hsup : ⨆ i, A i = ⊤)
    (i : ι) (x : A i) :
    subringDirectLimitEquiv A hA hsup (colimitOf (fun i => A i) (subringInclusion A hA) i x) =
      x :=
  Ring.DirectLimit.lift_of V (fun i => (A i).subtype) (subtype_subringInclusion A hA) i x

end Subrings

end Stacks.StrictHenselization.DirectLimit

end
