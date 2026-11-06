module

public import Mathlib.RingTheory.Localization.Away.Lemmas
public import StacksFrontier.RingTheory.CohenMacaulay.Locus
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterionEssFP
public import StacksFrontier.RingTheory.Flat.OpenFlatLocus
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.RelativeDimension.FlatLocalExtension
public import StacksFrontier.RingTheory.RelativeDimension.QuasiFinite
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.RingTheory.Depth.RingEquiv
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop

/-!
# Openness of Cohen–Macaulay loci

Let `R → S` be a flat ring map of finite presentation. For a prime `𝔮` of `S` lying over
`𝔭 = R ∩ 𝔮` the *fibre ring* at `𝔮` is `S_𝔮/𝔭S_𝔮 = S_𝔮 ⊗_R κ(𝔭)`, the local ring at `𝔮` of the
fibre of `Spec S → Spec R` through `𝔮`. This file shows that the set of primes at which the
fibre ring is Cohen–Macaulay is open, and deduces the openness of the Cohen–Macaulay locus of a
finite type algebra over a field and the splitting of a flat, finitely presented ring map with
Cohen–Macaulay fibres according to the dimension of its fibres.

The key statement is Lemma 00RH: for every `d ≥ 0` the set `W_d` of primes `𝔮` at which the fibre
ring is Cohen–Macaulay and `dim_𝔮(S/R) = d` is open. Given `𝔮 ∈ W_d`, after replacing `S` by a
principal localization `S_g`, `g ∉ 𝔮`, there is a quasi-finite map of `R`-algebras
`R[t_1, …, t_d] → S` (Lemma 00QE). For a prime `𝔯` of `S` with `𝔭 = R ∩ 𝔯` and
`𝔯' = R[t_1, …, t_d] ∩ 𝔯`, Lemma 00RE applied to the fibre over `κ(𝔭)` says that
`R[t]_{𝔯'}/𝔭R[t]_{𝔯'} → S_𝔯/𝔭S_𝔯` is flat if and only if `𝔯 ∈ W_d`; the critère de platitude par
fibres (Lemma 00R7) together with flatness of `S` over `R` upgrades flatness of this map to
flatness of `S_𝔯` over `R[t_1, …, t_d]`, and conversely flatness of `S_𝔯` gives flatness of the
fibre map by base change. So `W_d` is, near `𝔮`, the flat locus of `R[t_1, …, t_d] → S`, which
is open by Theorem 00RC.

Over a field `k` the fibre ring at `𝔮` is `S_𝔮` itself, so the Cohen–Macaulay locus of a finite
type `k`-algebra is the union of the `W_d` (Lemma 00RF). It contains every minimal prime, whose
local ring has dimension zero, and is therefore dense (Lemma 00RG). In the relative setting the
union `W` of the `W_d` is open, and it is dense in every fibre because it contains every point
which is minimal in its fibre (Lemma 00RI). Finally, if all fibre rings are Cohen–Macaulay then
the `W_d` form a partition of the quasi-compact space `Spec S` into open, hence clopen, pieces,
finitely many of them nonempty, and the corresponding idempotents split `S` as a product
(Lemma 00RL).

## Main results

* `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq`: Stacks 00RH,
  the set of primes with Cohen–Macaulay fibre ring and relative dimension `d` is open.
* `PrimeSpectrum.isOpen_setOf_isMaximalCohenMacaulay_localization`: Stacks 00RF, the
  Cohen–Macaulay locus of a finite type algebra over a field is open.
* `PrimeSpectrum.isOpen_and_dense_setOf_isMaximalCohenMacaulay_localization`: Stacks 00RG, it is
  moreover dense.
* `Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber`: Stacks 00RI, the set of
  primes with Cohen–Macaulay fibre ring is open and dense in every fibre.
* `Algebra.exists_algEquiv_pi_of_isMaximalCohenMacaulay_fiber`: Stacks 00RL, a flat ring map of
  finite presentation with Cohen–Macaulay fibres is a finite product of such maps with
  equidimensional fibres.
* `Module.isMaximalCohenMacaulay_self_of_ringKrullDim_eq_zero`: a local ring of dimension zero
  is Cohen–Macaulay.

## Implementation notes

*The fibre ring* at `𝔮` is spelled as in Lemma 00RK, as the localization
`Localization.AtPrime (𝔮.map (Ideal.Quotient.mk ((𝔮.under R).map (algebraMap R S))))` of `S/𝔭S`
at the image of `𝔮`, and Cohen–Macaulayness of a Noetherian local ring `A` (Definition 00N8) is
`Module.IsMaximalCohenMacaulay A A`. The relative dimension `dim_𝔮(S/R)` is
`Algebra.relativeDimensionAt R 𝔮` (Definition 00QD).

*Lemma 00RH.* The two local rings of the argument are presented concretely: the local ring
`S_𝔯/𝔭S_𝔯` is shown to be the localization of the fibre `κ(𝔭) ⊗_R S` at the point corresponding
to `𝔯`, which makes it the local ring to which Lemma 00RE applies over the field `κ(𝔭)`, for the
polynomial ring `κ(𝔭)[t_1, …, t_d] = κ(𝔭) ⊗_R R[t_1, …, t_d]` acting through the fibre of
`R[t_1, …, t_d]`; and `R[t]_{𝔯'}/𝔭R[t]_{𝔯'}` is in the same way a localization of
`κ(𝔭)[t_1, …, t_d]`, so that the two flatness conditions of the source agree. The fibre modules
in Lemma 00R7 are the quotients `M/(𝔪B)M`; they are identified with the ring quotients above.
The ring maps `R_𝔭 → R[t]_{𝔯'}` and `R_𝔭 → S_𝔯` are essentially of finite presentation because
the target is a localization of `R_𝔭 ⊗_R R[t]` respectively `R_𝔭 ⊗_R S`.

*Lemma 00RF.* The source's proof is the argument of Lemma 00RH over a field, and it is recovered here as the case `R = k` of Lemma 00RH, the fibre
ring over a field being the local ring itself.

*Lemma 00RI.* The source proves density by applying Lemma 00RG to the fibre, whose Cohen–Macaulay
locus is the intersection of `W` with the fibre. The proof of Lemma 00RG is that the locus
contains the minimal primes; the same argument is made directly in the fibre: a point of the
fibre over `𝔭` specializes from a minimal prime over `𝔭S`, which lies in the same fibre and at
which the fibre ring has dimension zero. Density is density in the fibre with its subspace
topology.

*Lemma 00RL.* A fibre of `R → S_d` is equidimensional of dimension `d` exactly when the relative
dimension `dim_𝔮(S_d/R)` equals `d` at every prime `𝔮` of `S_d`: over a field the local dimension
at a point is the largest dimension of an irreducible component through it (Lemma 00OT), and the
local dimension at the generic point of a component is the dimension of that component. The
conclusion is stated in this form, which is the form in which the source's proof produces it,
through the sets `W_d` of Lemma 00RH. The product is indexed by `d = 0, …, n` and the factors are
the quotients `S_d = S/(1 - e_d)` by the idempotents `e_d` cutting out the clopen sets `W_d`;
these are the principal localizations `S_{e_d}`. The passage from the finite clopen partition of
`Spec S` to the product decomposition — Lemma 00EM for a partition into finitely many pieces — is
made through the complete orthogonal family of idempotents it determines
(`PrimeSpectrum.isClopen_iff`, `CompleteOrthogonalIdempotents.bijective_pi`). The factors are
taken in the universe of `S`.

## References

* [StacksProject 00RF](https://stacks.math.columbia.edu/tag/00RF), Lemma 10.130.3
* [StacksProject 00RG](https://stacks.math.columbia.edu/tag/00RG), Lemma 10.130.4
* [StacksProject 00RH](https://stacks.math.columbia.edu/tag/00RH), Lemma 10.130.5
* [StacksProject 00RI](https://stacks.math.columbia.edu/tag/00RI), Lemma 10.130.6
* [StacksProject 00RL](https://stacks.math.columbia.edu/tag/00RL), Lemma 10.130.9
-/

@[expose] public section

open IsLocalRing Algebra.TensorProduct TensorProduct

universe u v

/-- Cohen–Macaulayness of a local ring is invariant under ring isomorphisms. -/
theorem Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv {A B : Type*} [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) :
    Module.IsMaximalCohenMacaulay A A ↔ Module.IsMaximalCohenMacaulay B B := by
  rw [Module.IsMaximalCohenMacaulay, Module.IsMaximalCohenMacaulay,
    ← IsLocalRing.map_maximalIdeal_of_surjective (e : A →+* B) e.surjective,
    ← Module.depth_eq_of_ringEquiv e, ← ringKrullDim_eq_of_ringEquiv e]

/-- The fibre ring `S_𝔮/𝔭S_𝔮` computed from any model `Y` of `S_𝔮`. -/
noncomputable def fiberRingEquiv (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] (Y : Type*) [CommRing Y] [Algebra S Y]
    [IsLocalization.AtPrime Y q] [Algebra R Y] [IsScalarTower R S Y] :
    (Y ⧸ (q.under R).map (algebraMap R Y)) ≃+*
      Localization.AtPrime (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))) := by
  set I := (q.under R).map (algebraMap R S)
  have : (q.map (Ideal.Quotient.mk I)).LiesOver q :=
    ⟨.trans (by simp [I, ← RingHom.ker_eq_comap_bot, Ideal.map_comap_le])
      (Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective _).symm⟩
  have hsub := Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
    (q.map (Ideal.Quotient.mk I)) q Ideal.Quotient.mk_surjective
  refine (Ideal.quotEquivOfEq (R := Y) (J := I.map (algebraMap S Y))
    (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq])).trans ?_
  have : IsLocalization (q.map (Ideal.Quotient.mk I)).primeCompl
      (Y ⧸ I.map (algebraMap S Y)) := hsub ▸ inferInstance
  exact (IsLocalization.algEquiv (q.map (Ideal.Quotient.mk I)).primeCompl _
    (Localization.AtPrime (q.map (Ideal.Quotient.mk I)))).toRingEquiv

/-- Cohen–Macaulayness of the fibre ring is local on `Spec S`. -/
private theorem isMaximalCohenMacaulay_fiberRing_comap_iff (R : Type*) {S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (M : Submonoid S) (T : Type*) [CommRing T] [Algebra S T]
    [IsLocalization M T] [Algebra R T] [IsScalarTower R S T] (q : Ideal T) [q.IsPrime] :
    Module.IsMaximalCohenMacaulay
        (Localization.AtPrime ((q.comap (algebraMap S T)).map (Ideal.Quotient.mk
          (((q.comap (algebraMap S T)).under R).map (algebraMap R S)))))
        (Localization.AtPrime ((q.comap (algebraMap S T)).map (Ideal.Quotient.mk
          (((q.comap (algebraMap S T)).under R).map (algebraMap R S))))) ↔
      Module.IsMaximalCohenMacaulay
        (Localization.AtPrime (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T)))))
        (Localization.AtPrime (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R T))))) := by
  have : IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap S T)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M _ q
  have hunder : (q.comap (algebraMap S T)).under R = q.under R := by
    rw [Ideal.under, Ideal.under, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  have e₁ := fiberRingEquiv R (q.comap (algebraMap S T)) (Localization.AtPrime q)
  have e₂ := fiberRingEquiv R q (Localization.AtPrime q)
  have e₃ : (Localization.AtPrime q ⧸ ((q.comap (algebraMap S T)).under R).map
      (algebraMap R (Localization.AtPrime q))) ≃+*
      (Localization.AtPrime q ⧸ (q.under R).map (algebraMap R (Localization.AtPrime q))) :=
    Ideal.quotEquivOfEq (by rw [hunder])
  have : IsLocalRing (Localization.AtPrime q ⧸ (q.under R).map
      (algebraMap R (Localization.AtPrime q))) := e₂.symm.isLocalRing
  have : IsLocalRing (Localization.AtPrime q ⧸ ((q.comap (algebraMap S T)).under R).map
      (algebraMap R (Localization.AtPrime q))) := e₁.symm.isLocalRing
  rw [← Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv e₁,
    ← Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv e₂,
    Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv e₃]

/-- For a ring map of finite type the relative dimension at a prime is a natural number. -/
theorem Algebra.exists_relativeDimensionAt_eq_natCast (R : Type*) {S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (q : Ideal S) [q.IsPrime] :
    ∃ n : ℕ, Algebra.relativeDimensionAt R q = n := by
  obtain ⟨Q, hQ, hQq⟩ := Ideal.Fiber.exists_comap_includeRight_eq q (q.under R) rfl
  rw [Algebra.relativeDimensionAt_eq_localKrullDim q (q.under R) rfl Q hQq,
    ← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim]
  obtain ⟨⟨U, hxU, _, hEq⟩, -⟩ := topologicalKrullDimAt_isLeast _
    (⟨Q, hQ⟩ : PrimeSpectrum ((q.under R).Fiber S))
  have h0 : 0 ≤ topologicalKrullDimAt (PrimeSpectrum ((q.under R).Fiber S)) ⟨Q, hQ⟩ := by
    rw [hEq, topologicalKrullDim]
    have : Nonempty (TopologicalSpace.IrreducibleCloseds ↥U) :=
      ⟨⟨closure {⟨_, hxU⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_nonneg
  have hle : topologicalKrullDimAt (PrimeSpectrum ((q.under R).Fiber S)) ⟨Q, hQ⟩ ≤
      ringKrullDim ((q.under R).Fiber S) := by
    rw [topologicalKrullDimAt, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact iInf_le_of_le ⟨Set.univ, Set.mem_univ _, isOpen_univ⟩
      (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ _).isHomeomorph).le
  have hne := ne_top_of_le_ne_top (ringKrullDim_ne_top_of_finiteType
    (κ := (q.under R).ResidueField)) hle
  generalize topologicalKrullDimAt (PrimeSpectrum ((q.under R).Fiber S)) ⟨Q, hQ⟩ = a at h0 hne
  induction a with
  | bot => exact absurd h0 (by simp)
  | coe a =>
    induction a with
    | top => exact absurd rfl hne
    | coe n => exact ⟨n, rfl⟩

section FiberLocalization

variable {R X : Type*} [CommRing R] [CommRing X] [Algebra R X] (p : Ideal R) [p.IsPrime]
  (r : Ideal X) [r.IsPrime] [r.LiesOver p] (J : Ideal (Localization.AtPrime r))

/-- The residue field `κ(𝔭)` maps to `X_𝔯/𝔭X_𝔯`. -/
noncomputable def residueFieldToQuotient
    (hJ : J = p.map (algebraMap R (Localization.AtPrime r))) :
    p.ResidueField →ₐ[R] Localization.AtPrime r ⧸ J :=
  Ideal.ResidueField.liftₐ p (Algebra.ofId R _)
    (fun a ha ↦ by
      rw [RingHom.mem_ker, Algebra.ofId_apply,
        IsScalarTower.algebraMap_apply R (Localization.AtPrime r) (Localization.AtPrime r ⧸ J),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, hJ]
      exact Ideal.mem_map_of_mem _ ha)
    (fun a ha ↦ by
      have hr : algebraMap R X a ∉ r := by
        rwa [← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def r p]
      have hu : IsUnit (algebraMap R (Localization.AtPrime r) a) := by
        rw [IsScalarTower.algebraMap_apply R X]
        exact IsLocalization.map_units _ (⟨_, hr⟩ : r.primeCompl)
      change IsUnit (Algebra.ofId R _ a)
      rw [Algebra.ofId_apply,
        IsScalarTower.algebraMap_apply R (Localization.AtPrime r) (Localization.AtPrime r ⧸ J)]
      exact hu.map _)

/-- The canonical map from the fibre `κ(𝔭) ⊗_R X` to `X_𝔯/𝔭X_𝔯`. -/
noncomputable def fiberToQuotient
    (hJ : J = p.map (algebraMap R (Localization.AtPrime r))) :
    p.Fiber X →ₐ[R] Localization.AtPrime r ⧸ J :=
  Algebra.TensorProduct.lift (residueFieldToQuotient p r J hJ)
    ((IsScalarTower.toAlgHom R (Localization.AtPrime r) (Localization.AtPrime r ⧸ J)).comp
      (IsScalarTower.toAlgHom R X (Localization.AtPrime r))) fun _ _ ↦ Commute.all _ _

/-- The map `κ(𝔭) ⊗_R X → X_𝔯/𝔭X_𝔯` sends `1 ⊗ x` to the class of `x`. -/
theorem fiberToQuotient_tmul (hJ : J = p.map (algebraMap R (Localization.AtPrime r)))
    (x : X) :
    fiberToQuotient p r J hJ (1 ⊗ₜ x) = Ideal.Quotient.mk J (algebraMap X _ x) := by
  simp [fiberToQuotient]

/-- The ideal `𝔭X` dies in the fibre `κ(𝔭) ⊗_R X`. -/
theorem includeRight_eq_zero_of_mem (x : X) (hx : x ∈ p.map (algebraMap R X)) :
    (includeRight : X →ₐ[R] p.Fiber X) x = 0 := by
  have : p.map (algebraMap R X) ≤ RingHom.ker (includeRight : X →ₐ[R] p.Fiber X).toRingHom := by
    refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker]
    show includeRight (algebraMap R X a) = 0
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R p.ResidueField,
      Ideal.algebraMap_residueField_eq_zero.mpr ha, map_zero]
  exact this hx

/-- **The local ring of the fibre.** `X_𝔯/𝔭X_𝔯` is the localization of the fibre `κ(𝔭) ⊗_R X` at
the prime `𝔓` corresponding to `𝔯`. -/
theorem isLocalization_fiberToQuotient
    (hJ : J = p.map (algebraMap R (Localization.AtPrime r)))
    (P : Ideal (p.Fiber X)) [P.IsPrime]
    (hP : P.comap (includeRight : X →ₐ[R] p.Fiber X).toRingHom = r) :
    letI := (fiberToQuotient p r J hJ).toRingHom.toAlgebra
    IsLocalization.AtPrime (Localization.AtPrime r ⧸ J) P := by
  let := (fiberToQuotient p r J hJ).toRingHom.toAlgebra
  set φ := fiberToQuotient p r J hJ
  have hφ : ∀ x : X, algebraMap (p.Fiber X) (Localization.AtPrime r ⧸ J) (1 ⊗ₜ x) =
      Ideal.Quotient.mk J (algebraMap X _ x) := fiberToQuotient_tmul p r J hJ
  have hJle : J ≤ maximalIdeal (Localization.AtPrime r) := by
    rw [hJ, Ideal.map_le_iff_le_comap]
    intro a ha
    rwa [Ideal.mem_comap, IsScalarTower.algebraMap_apply R X,
      IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime r) r,
      ← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def r p]
  have : Nontrivial (Localization.AtPrime r ⧸ J) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJle)
  have : IsLocalRing (Localization.AtPrime r ⧸ J) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  -- the prime of the fibre cut out by the maximal ideal of `X_𝔯/𝔭X_𝔯` is `𝔓`
  have hmax : (maximalIdeal (Localization.AtPrime r ⧸ J)).comap (algebraMap _ _) = P := by
    have : ((maximalIdeal (Localization.AtPrime r ⧸ J)).comap
        (algebraMap (p.Fiber X) (Localization.AtPrime r ⧸ J))).IsPrime := Ideal.comap_isPrime _ _
    refine congrArg PrimeSpectrum.asIdeal ((PrimeSpectrum.preimageEquivFiber R X
      (⟨p, ‹_›⟩ : PrimeSpectrum R)).symm.injective (a₁ := ⟨_, this⟩) (a₂ := ⟨P, ‹_›⟩)
      (Subtype.ext (PrimeSpectrum.ext ?_)))
    show Ideal.comap _ _ = Ideal.comap _ _
    rw [hP]
    ext x
    rw [Ideal.mem_comap, Ideal.mem_comap]
    show algebraMap (p.Fiber X) _ (1 ⊗ₜ x) ∈ _ ↔ _
    rw [hφ, ← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime r) r x]
    have hmk : maximalIdeal (Localization.AtPrime r ⧸ J) =
        (maximalIdeal (Localization.AtPrime r)).map (Ideal.Quotient.mk J) :=
      (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
    rw [hmk, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    refine ⟨fun ⟨y, hy, hyx⟩ ↦ ?_, fun h ↦ ⟨_, h, rfl⟩⟩
    rw [Ideal.Quotient.eq] at hyx
    have := (maximalIdeal (Localization.AtPrime r)).sub_mem hy (hJle hyx)
    rwa [sub_sub_cancel] at this
  rw [IsLocalization.AtPrime, isLocalization_iff]
  refine ⟨fun y ↦ ?_, fun z ↦ ?_, fun {a b} hab ↦ ?_⟩
  · have hy : (y : p.Fiber X) ∉ (maximalIdeal (Localization.AtPrime r ⧸ J)).comap
        (algebraMap _ _) := by rw [hmax]; exact y.2
    rw [Ideal.mem_comap] at hy
    exact IsLocalRing.notMem_maximalIdeal.mp hy
  · obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective r.primeCompl w
    have hs : (1 ⊗ₜ[R] (s : X) : p.Fiber X) ∈ P.primeCompl := by
      show (includeRight : X →ₐ[R] p.Fiber X).toRingHom (s : X) ∉ P
      rw [← Ideal.mem_comap (f := (includeRight : X →ₐ[R] p.Fiber X).toRingHom), hP]
      exact s.2
    refine ⟨⟨1 ⊗ₜ x, ⟨_, hs⟩⟩, ?_⟩
    simp only [hφ, ← map_mul, IsLocalization.mk'_spec]
  · obtain ⟨u, hu, t, ht⟩ := Ideal.Fiber.exists_smul_eq_one_tmul p (a - b)
    have h0 : Ideal.Quotient.mk J (algebraMap X (Localization.AtPrime r) t) = 0 := by
      rw [← hφ, ← ht, Algebra.smul_def, map_mul, map_sub, hab, sub_self, mul_zero]
    rw [Ideal.Quotient.eq_zero_iff_mem, hJ,
      IsScalarTower.algebraMap_eq R X (Localization.AtPrime r),
      ← Ideal.map_map, IsLocalization.algebraMap_mem_map_algebraMap_iff r.primeCompl] at h0
    obtain ⟨v, hv, hvt⟩ := h0
    have hvP : (1 ⊗ₜ[R] v : p.Fiber X) ∉ P := by
      show (includeRight : X →ₐ[R] p.Fiber X).toRingHom v ∉ P
      rw [← Ideal.mem_comap (f := (includeRight : X →ₐ[R] p.Fiber X).toRingHom), hP]
      exact hv
    have huP : algebraMap R (p.Fiber X) u ∉ P := by
      intro h
      apply (inferInstance : P.IsPrime).ne_top
      refine Ideal.eq_top_of_isUnit_mem _ h ?_
      rw [IsScalarTower.algebraMap_apply R p.ResidueField]
      refine IsUnit.map _ (isUnit_iff_ne_zero.mpr ?_)
      rwa [Ne, Ideal.algebraMap_residueField_eq_zero]
    refine ⟨⟨(1 ⊗ₜ v) * algebraMap R (p.Fiber X) u,
      (inferInstance : P.IsPrime).mul_notMem hvP huP⟩, ?_⟩
    rw [← sub_eq_zero, ← mul_sub, mul_assoc, ← Algebra.smul_def, ht]
    show (includeRight : X →ₐ[R] p.Fiber X) v * includeRight t = 0
    rw [← map_mul]
    exact includeRight_eq_zero_of_mem p _ hvt

end FiberLocalization

/-- For a finitely presented `R`-algebra `X` and a prime `𝔯` of `X` over `𝔭`, the local ring map
`R_𝔭 → X_𝔯` is essentially of finite presentation: `X_𝔯` is a localization of `R_𝔭 ⊗_R X`. -/
@[ega "IV 1.3.10" "partial"]
theorem essentiallyOfFinitePresentation_localRingHom {R X : Type*} [CommRing R] [CommRing X]
    [Algebra R X] [Algebra.FinitePresentation R X] (p : Ideal R) [p.IsPrime] (r : Ideal X)
    [r.IsPrime] [r.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p r
    (algebraMap (Localization.AtPrime p)
      (Localization.AtPrime r)).EssentiallyOfFinitePresentation := by
  let := Localization.AtPrime.algebraOfLiesOver p r
  let : Algebra X (Localization.AtPrime p ⊗[R] X) := Algebra.TensorProduct.rightAlgebra
  let f : Localization.AtPrime p ⊗[R] X →ₐ[Localization.AtPrime p] Localization.AtPrime r :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) (IsScalarTower.toAlgHom R X _)
      fun _ _ ↦ .all _ _
  let : Algebra (Localization.AtPrime p ⊗[R] X) (Localization.AtPrime r) := f.toRingHom.toAlgebra
  have : IsScalarTower (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] X)
      (Localization.AtPrime r) := .of_algebraMap_eq fun c ↦ (f.commutes c).symm
  have : IsScalarTower X (Localization.AtPrime p ⊗[R] X) (Localization.AtPrime r) :=
    .of_algebraMap_eq fun x ↦ by
      show _ = f (1 ⊗ₜ x)
      simp [f]
  have hle : Algebra.algebraMapSubmonoid X p.primeCompl ≤ r.primeCompl := by
    rintro _ ⟨a, ha, rfl⟩
    show algebraMap R X a ∉ r
    rwa [← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def r p]
  have := IsLocalization.isLocalization_of_submonoid_le (Localization.AtPrime p ⊗[R] X)
    (Localization.AtPrime r) _ _ hle
  exact ⟨Localization.AtPrime p ⊗[R] X, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, _, this⟩

set_option backward.isDefEq.respectTransparency false in
/-- The two spellings `M/IM` of the base change of a `B`-algebra `M` to `B/I` have the same
flatness over `B/I`. -/
theorem flat_quotient_smul_top_iff {B M : Type*} [CommRing B] [CommRing M] [Algebra B M]
    (IB : Ideal B) (IM : Ideal M) (h : IB.map (algebraMap B M) = IM)
    [Algebra (B ⧸ IB) (M ⧸ IM)] [IsScalarTower B (B ⧸ IB) (M ⧸ IM)] :
    Module.Flat (B ⧸ IB) (M ⧸ (IB • (⊤ : Submodule B M))) ↔ Module.Flat (B ⧸ IB) (M ⧸ IM) := by
  have hsmul : IB • (⊤ : Submodule B M) = IM.restrictScalars B := by
    rw [Ideal.smul_top_eq_map, h]
  exact Module.Flat.equiv_iff (LinearEquiv.extendScalarsOfSurjective
    (fun y ↦ Ideal.Quotient.mk_surjective y)
    ((Submodule.quotEquivOfEq _ _ hsmul).trans (Submodule.Quotient.restrictScalarsEquiv B IM)))

-- needed: as for `flat_quotient_smul_top_iff`
set_option backward.isDefEq.respectTransparency false in
/-- The base change `M/IM` of a flat `B`-module is flat over `B/I`. -/
theorem flat_quotient_smul_top {B M : Type*} [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Flat B M] (IB : Ideal B) :
    Module.Flat (B ⧸ IB) (M ⧸ (IB • (⊤ : Submodule B M))) :=
  Module.Flat.of_linearEquiv (LinearEquiv.extendScalarsOfSurjective
    (fun y ↦ Ideal.Quotient.mk_surjective y) (TensorProduct.quotTensorEquivQuotSMul M IB)).symm

section Core

open Localization.AtPrime

variable {R T : Type*} [CommRing R] [CommRing T] [Algebra R T] {σ : Type*} [Finite σ]
  [Algebra (MvPolynomial σ R) T] [IsScalarTower R (MvPolynomial σ R) T]

/-- **The core of Stacks 00RH.** Let `R → T` be flat of finite presentation and let
`R[t_1, …, t_d] → T` be a quasi-finite map of `R`-algebras. For a prime `𝔯` of `T`, the local
ring `T_𝔯` is flat over `R[t_1, …, t_d]` if and only if the fibre ring `T_𝔯/𝔭T_𝔯` is
Cohen–Macaulay and `dim_𝔯(T/R) = d`. -/
theorem flat_localization_iff [Module.Flat R T] [Algebra.FinitePresentation R T]
    [Algebra.QuasiFinite (MvPolynomial σ R) T] (r : Ideal T) [r.IsPrime] :
    Module.Flat (MvPolynomial σ R) (Localization.AtPrime r) ↔
      Module.IsMaximalCohenMacaulay
          (Localization.AtPrime (r.map (Ideal.Quotient.mk ((r.under R).map (algebraMap R T)))))
          (Localization.AtPrime (r.map (Ideal.Quotient.mk ((r.under R).map (algebraMap R T))))) ∧
        Algebra.relativeDimensionAt R r = Nat.card σ := by
  classical
  set p := r.under R with hp
  set r' := r.under (MvPolynomial σ R) with hr'
  have : r.LiesOver p := ⟨rfl⟩
  have : r.LiesOver r' := ⟨rfl⟩
  have hr'p : r'.under R = p := by rw [hr', Ideal.under_under]
  have : r'.LiesOver p := ⟨hr'p.symm⟩
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime r') := algebraOfLiesOver p r'
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime r) := algebraOfLiesOver p r
  let : Algebra (Localization.AtPrime r') (Localization.AtPrime r) := algebraOfLiesOver r' r
  set 𝔪 := maximalIdeal (Localization.AtPrime p) with h𝔪def
  set IB := 𝔪.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime r')) with hIBdef
  set IM := 𝔪.map (algebraMap (Localization.AtPrime p) (Localization.AtPrime r)) with hIMdef
  have h𝔪 : 𝔪 = p.map (algebraMap R (Localization.AtPrime p)) :=
    (IsLocalization.AtPrime.map_eq_maximalIdeal p _).symm
  have hIM : IM = p.map (algebraMap R (Localization.AtPrime r)) := by
    rw [hIMdef, h𝔪, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hIB : IB = p.map (algebraMap R (Localization.AtPrime r')) := by
    rw [hIBdef, h𝔪, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  obtain ⟨PT, hPT, hPTr⟩ := Ideal.Fiber.exists_comap_includeRight_eq r p rfl
  obtain ⟨PA, hPA, hPAr⟩ := Ideal.Fiber.exists_comap_includeRight_eq r' p hr'p
  -- the fibre rings as localizations of the fibres
  let : Algebra (p.Fiber T) (Localization.AtPrime r ⧸ IM) :=
    (fiberToQuotient p r IM hIM).toRingHom.toAlgebra
  have : IsLocalization.AtPrime (Localization.AtPrime r ⧸ IM) PT :=
    isLocalization_fiberToQuotient p r IM hIM PT hPTr
  let : Algebra (p.Fiber (MvPolynomial σ R)) (Localization.AtPrime r' ⧸ IB) :=
    (fiberToQuotient p r' IB hIB).toRingHom.toAlgebra
  have : IsLocalization.AtPrime (Localization.AtPrime r' ⧸ IB) PA :=
    isLocalization_fiberToQuotient p r' IB hIB PA hPAr
  have : IsLocalRing (Localization.AtPrime r ⧸ IM) := IsLocalization.AtPrime.isLocalRing _ PT
  -- the polynomial ring over `κ(𝔭)` and its maps
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := σ) R p.ResidueField
  let ψ : p.Fiber (MvPolynomial σ R) →ₐ[p.ResidueField] p.Fiber T :=
    Algebra.TensorProduct.map (AlgHom.id _ _) (IsScalarTower.toAlgHom R (MvPolynomial σ R) T)
  let : Algebra (MvPolynomial σ p.ResidueField) (p.Fiber T) :=
    (ψ.comp e.symm.toAlgHom).toRingHom.toAlgebra
  have : IsScalarTower p.ResidueField (MvPolynomial σ p.ResidueField) (p.Fiber T) :=
    .of_algebraMap_eq fun c ↦ ((ψ.comp e.symm.toAlgHom).commutes c).symm
  let : Algebra (MvPolynomial σ p.ResidueField) (Localization.AtPrime r ⧸ IM) :=
    ((algebraMap (p.Fiber T) _).comp (algebraMap (MvPolynomial σ p.ResidueField) _)).toAlgebra
  have : IsScalarTower (MvPolynomial σ p.ResidueField) (p.Fiber T)
      (Localization.AtPrime r ⧸ IM) := .of_algebraMap_eq' rfl
  -- quasi-finiteness of the fibre over `κ(𝔭)[t_1, …, t_d]`
  let : Algebra (MvPolynomial σ R) (MvPolynomial σ p.ResidueField) :=
    MvPolynomial.algebraMvPolynomial
  let : Algebra (MvPolynomial σ R) (p.Fiber T) :=
    ((algebraMap (MvPolynomial σ p.ResidueField) (p.Fiber T)).comp
      (algebraMap (MvPolynomial σ R) (MvPolynomial σ p.ResidueField))).toAlgebra
  have : IsScalarTower (MvPolynomial σ R) (MvPolynomial σ p.ResidueField) (p.Fiber T) :=
    .of_algebraMap_eq' rfl
  have he : ∀ a : MvPolynomial σ R,
      e.symm (algebraMap (MvPolynomial σ R) (MvPolynomial σ p.ResidueField) a) = 1 ⊗ₜ a := by
    intro a
    rw [MvPolynomial.algebraMap_def, MvPolynomial.algebraTensorAlgEquiv_symm_map]
  have hψ : ∀ a : MvPolynomial σ R, algebraMap (MvPolynomial σ R) (p.Fiber T) a =
      1 ⊗ₜ algebraMap (MvPolynomial σ R) T a := by
    intro a
    show ψ (e.symm (algebraMap (MvPolynomial σ R) (MvPolynomial σ p.ResidueField) a)) = _
    rw [he]
    simp [ψ]
  let g : T →ₐ[MvPolynomial σ R] p.Fiber T :=
    { (includeRight : T →ₐ[R] p.Fiber T) with commutes' := fun a ↦ (hψ a).symm }
  let F : MvPolynomial σ p.ResidueField ⊗[MvPolynomial σ R] T →ₐ[MvPolynomial σ p.ResidueField]
      p.Fiber T := Algebra.TensorProduct.lift (Algebra.ofId _ _) g fun _ _ ↦ .all _ _
  have hF : Function.Surjective F := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul c t =>
      refine ⟨MvPolynomial.C c ⊗ₜ t, ?_⟩
      rw [Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
      show (algebraMap p.ResidueField p.ResidueField c) ⊗ₜ[R] (1 : T) * (1 ⊗ₜ t) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, Algebra.algebraMap_self,
        RingHom.id_apply]
    | add x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact ⟨a + b, map_add F a b⟩
  have : Algebra.QuasiFinite (MvPolynomial σ p.ResidueField) (p.Fiber T) :=
    .of_surjective_algHom F hF
  -- Stacks 00RE for the fibre
  have hRE := Module.Flat.atPrime_iff_isMaximalCohenMacaulay_and_relativeDimensionAt_eq
    (k := p.ResidueField) (S := p.Fiber T) (σ := σ) PT (Localization.AtPrime r ⧸ IM)
  have hCM : Module.IsMaximalCohenMacaulay (Localization.AtPrime r ⧸ IM)
      (Localization.AtPrime r ⧸ IM) ↔ Module.IsMaximalCohenMacaulay
          (Localization.AtPrime (r.map (Ideal.Quotient.mk ((r.under R).map (algebraMap R T)))))
          (Localization.AtPrime (r.map (Ideal.Quotient.mk ((r.under R).map (algebraMap R T))))) :=
    Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv
      ((Ideal.quotEquivOfEq hIM).trans (fiberRingEquiv R r (Localization.AtPrime r)))
  have hdim : Algebra.relativeDimensionAt p.ResidueField PT = Algebra.relativeDimensionAt R r := by
    rw [relativeDimensionAt_eq_localKrullDim_of_field,
      Algebra.relativeDimensionAt_eq_localKrullDim r p rfl PT hPTr]
  rw [← hCM, ← hdim, ← hRE]
  -- `B_𝔪 = R[t]_{𝔯'}/𝔭R[t]_{𝔯'}` is a localization of `κ(𝔭)[t_1, …, t_d]`
  let : Algebra (MvPolynomial σ p.ResidueField) (Localization.AtPrime r' ⧸ IB) :=
    RingHom.toAlgebra (R := MvPolynomial σ p.ResidueField) (S := Localization.AtPrime r' ⧸ IB)
      ((algebraMap (p.Fiber (MvPolynomial σ R)) (Localization.AtPrime r' ⧸ IB)).comp
        e.toRingEquiv.symm.toRingHom)
  have hlocK : IsLocalization (PA.primeCompl.map e.toRingEquiv) (Localization.AtPrime r' ⧸ IB) :=
    IsLocalization.isLocalization_of_base_ringEquiv PA.primeCompl _ e.toRingEquiv
  have hIBM : IB ≤ IM.comap (algebraMap (Localization.AtPrime r') (Localization.AtPrime r)) :=
    Ideal.map_le_iff_le_comap.mpr (by
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]; exact Ideal.le_comap_map)
  let : Algebra (Localization.AtPrime r' ⧸ IB) (Localization.AtPrime r ⧸ IM) :=
    Ideal.Quotient.algebraQuotientOfLEComap hIBM
  have htowerK : IsScalarTower (MvPolynomial σ p.ResidueField) (Localization.AtPrime r' ⧸ IB)
      (Localization.AtPrime r ⧸ IM) := by
    refine .of_algebraMap_eq fun k ↦ ?_
    obtain ⟨x, rfl⟩ := e.surjective k
    show fiberToQuotient p r IM hIM (ψ (e.symm (e x))) =
      Ideal.quotientMap IM _ hIBM (fiberToQuotient p r' IB hIB (e.toRingEquiv.symm (e x)))
    show fiberToQuotient p r IM hIM (ψ (e.symm (e x))) =
      Ideal.quotientMap IM _ hIBM (fiberToQuotient p r' IB hIB (e.symm (e x)))
    rw [e.symm_apply_apply]
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c a =>
      have hca : (c ⊗ₜ[R] a : p.Fiber (MvPolynomial σ R)) =
          algebraMap p.ResidueField _ c * (1 ⊗ₜ a) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          mul_one, one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      rw [hca, map_mul, map_mul, map_mul, map_mul, AlgHom.commutes]
      congr 1
      · have h1 : ((fiberToQuotient p r IM hIM).toRingHom.comp
            (algebraMap p.ResidueField (p.Fiber T))) =
            (Ideal.quotientMap IM _ hIBM).comp ((fiberToQuotient p r' IB hIB).toRingHom.comp
              (algebraMap p.ResidueField (p.Fiber (MvPolynomial σ R)))) := by
          ext a
          simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
            ← IsScalarTower.algebraMap_apply, AlgHom.commutes, Ideal.quotientMap_algebraMap]
          rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime r)
              (Localization.AtPrime r ⧸ IM)]
          rfl
        exact congr($h1 c)
      · simp only [ψ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, fiberToQuotient_tmul]
        rw [Ideal.quotientMap_mk, IsScalarTower.coe_toAlgHom',
          ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hKB : Module.Flat (MvPolynomial σ p.ResidueField) (Localization.AtPrime r ⧸ IM) ↔
      Module.Flat (Localization.AtPrime r' ⧸ IB) (Localization.AtPrime r ⧸ IM) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime r' ⧸ IB)
      (PA.primeCompl.map e.toRingEquiv) (Localization.AtPrime r ⧸ IM)).symm
  have hAB : Module.Flat (MvPolynomial σ R) (Localization.AtPrime r) ↔
      Module.Flat (Localization.AtPrime r') (Localization.AtPrime r) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime r') r'.primeCompl
      (Localization.AtPrime r)).symm
  have : IsScalarTower (Localization.AtPrime r') (Localization.AtPrime r' ⧸ IB)
      (Localization.AtPrime r ⧸ IM) := by
    refine ⟨fun b x y ↦ ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    show Ideal.quotientMap IM _ hIBM (Ideal.Quotient.mk IB (b • x)) * Ideal.Quotient.mk IM y =
      b • (Ideal.Quotient.mk IM (algebraMap _ _ x) * Ideal.Quotient.mk IM y)
    rw [Ideal.quotientMap_mk, ← map_mul, ← map_mul, smul_eq_mul]
    show _ = Ideal.Quotient.mk IM (b • (algebraMap _ _ x * y))
    rw [Algebra.smul_def, map_mul, map_mul, map_mul, map_mul, mul_assoc, map_mul]
  have hIBIM : IB.map (algebraMap (Localization.AtPrime r') (Localization.AtPrime r)) = IM := by
    rw [hIBdef, hIMdef, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [hAB, hKB, ← flat_quotient_smul_top_iff IB IM hIBIM]
  refine ⟨fun _ ↦ flat_quotient_smul_top IB, fun hflat ↦ ?_⟩
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime r')) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have : IsLocalHom (algebraMap (Localization.AtPrime r') (Localization.AtPrime r)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have : Module.Flat R (Localization.AtPrime r) := Module.Flat.trans R T _
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime r) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).mpr this
  exact (Module.flat_algebra_and_flat_of_flat_quotient_maximalIdeal
    (R := Localization.AtPrime p) (S := Localization.AtPrime r')
    (S' := Localization.AtPrime r) (M := Localization.AtPrime r)
    (essentiallyOfFinitePresentation_localRingHom p r')
    (essentiallyOfFinitePresentation_localRingHom p r)).2

end Core

/-- A local ring of dimension zero is Cohen–Macaulay. -/
theorem Module.isMaximalCohenMacaulay_self_of_ringKrullDim_eq_zero {A : Type*} [CommRing A]
    [IsLocalRing A]
    (h : ringKrullDim A = 0) : Module.IsMaximalCohenMacaulay A A := by
  have hI : maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ := by
    rw [smul_eq_mul, Ideal.mul_top]; exact (maximalIdeal.isMaximal A).ne_top
  have hle := Module.depth_le_supportDim A (maximalIdeal A) A hI
  rw [Module.supportDim_self_eq_ringKrullDim, h] at hle
  rw [Module.IsMaximalCohenMacaulay, h]
  exact le_antisymm hle (by simp)

/-- The local ring of a ring at a minimal prime is Cohen–Macaulay. -/
private theorem isMaximalCohenMacaulay_localization_of_mem_minimalPrimes {S : Type*} [CommRing S]
    (q : Ideal S) [q.IsPrime] (hq : q ∈ minimalPrimes S) :
    Module.IsMaximalCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q) := by
  refine Module.isMaximalCohenMacaulay_self_of_ringKrullDim_eq_zero ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, Ideal.height_eq_zero_iff.mpr hq]
  rfl

/-- The fibre ring at a prime which is minimal in its fibre is Cohen–Macaulay. -/
private theorem isMaximalCohenMacaulay_fiberRing_of_mem_minimalPrimes (R : Type*) {S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime]
    (hq : q ∈ ((q.under R).map (algebraMap R S)).minimalPrimes) :
    Module.IsMaximalCohenMacaulay
      (Localization.AtPrime (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))))
      (Localization.AtPrime (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S))))) := by
  set I := (q.under R).map (algebraMap R S)
  rw [Ideal.minimalPrimes_eq_comap] at hq
  obtain ⟨m, hm, hmq⟩ := hq
  have hmap : q.map (Ideal.Quotient.mk I) = m := by
    rw [← hmq, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have : q.map (Ideal.Quotient.mk I) ∈ minimalPrimes (S ⧸ I) := hmap ▸ hm
  exact isMaximalCohenMacaulay_localization_of_mem_minimalPrimes _ this

/-- **Stacks 00RH.** Let `R → S` be flat of finite presentation and let `d ≥ 0`. The set of
primes `𝔮` of `S` such that, with `𝔭 = R ∩ 𝔮`, the fibre ring `S_𝔮/𝔭S_𝔮` is Cohen–Macaulay and
`dim_𝔮(S/R) = d` is open in `Spec S`. The fibre ring is spelled as the localization of `S/𝔭S` at
the image of `𝔮`. -/
@[stacks 00RH "The fibre ring `S_𝔮/𝔭S_𝔮` is `Localization.AtPrime` of the image of `𝔮` in
`S/𝔭S`, `𝔭 = 𝔮.under R`, as in 00RK; Cohen-Macaulayness of a local ring (Definition 00N8) is
`Module.IsMaximalCohenMacaulay A A`, and `dim_𝔮(S/R)` is `Algebra.relativeDimensionAt R 𝔮`.",
  ega "IV 12.1.7" "(iii)"]
theorem Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S] (d : ℕ) :
    IsOpen {q : PrimeSpectrum S |
      Module.IsMaximalCohenMacaulay
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S)))))
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S))))) ∧
        Algebra.relativeDimensionAt R q.asIdeal = d} := by
  rw [isOpen_iff_forall_mem_open]
  rintro q ⟨hCM, hdim⟩
  -- Lemma 00QE: after localizing, `S` is quasi-finite over `R[t_1, …, t_d]`
  obtain ⟨Q, hQ, hQq⟩ := Ideal.Fiber.exists_comap_includeRight_eq q.asIdeal (q.asIdeal.under R) rfl
  have hQE : _root_.relativeDimensionAt R S (q.asIdeal.under R) ⟨Q, hQ⟩ =
      ((d : ℕ∞) : WithBot ℕ∞) := by
    rw [_root_.relativeDimensionAt, krullDimAt_eq_topologicalKrullDimAt,
      TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim,
      ← Algebra.relativeDimensionAt_eq_localKrullDim q.asIdeal _ rfl Q hQq, hdim]
    rfl
  obtain ⟨g, hg, φ, hφ, -, hqf⟩ := quasiFinite_over_polynomial_of_relativeDimension R S q
    (q.asIdeal.under R) ⟨Q, hQ⟩ (PrimeSpectrum.ext hQq) d hQE
  let : Algebra (MvPolynomial (Fin d) R) (Localization.Away g) := φ.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin d) R) (Localization.Away g) :=
    .of_algebraMap_eq fun a ↦ (congr($hφ a)).symm
  have : Algebra.QuasiFinite (MvPolynomial (Fin d) R) (Localization.Away g) := hqf
  have : Module.Flat R (Localization.Away g) := Module.Flat.trans R S _
  have : Algebra.FinitePresentation R (Localization.Away g) :=
    Algebra.FinitePresentation.trans R S _
  have : Algebra.FinitePresentation (MvPolynomial (Fin d) R) (Localization.Away g) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ _
  -- the flat locus of `R[t_1, …, t_d] → S_g` is open (Theorem 00RC)
  set U := {r : PrimeSpectrum (Localization.Away g) |
    Module.Flat (MvPolynomial (Fin d) R) (Localization.AtPrime r.asIdeal)}
  have hU : IsOpen U := by
    convert Module.isOpen_setOf_flat_localizedModule_atPrime (R := MvPolynomial (Fin d) R)
      (S := Localization.Away g) (M := Localization.Away g) using 1
  have hemb := PrimeSpectrum.localization_away_isOpenEmbedding (Localization.Away g) g
  obtain ⟨qT, rfl⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rwa [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]
  have key : ∀ r : PrimeSpectrum (Localization.Away g), r ∈ U ↔
      Module.IsMaximalCohenMacaulay
          (Localization.AtPrime ((PrimeSpectrum.comap (algebraMap S _) r).asIdeal.map
            (Ideal.Quotient.mk (((PrimeSpectrum.comap (algebraMap S _) r).asIdeal.under R).map
              (algebraMap R S)))))
          (Localization.AtPrime ((PrimeSpectrum.comap (algebraMap S _) r).asIdeal.map
            (Ideal.Quotient.mk (((PrimeSpectrum.comap (algebraMap S _) r).asIdeal.under R).map
              (algebraMap R S))))) ∧
        Algebra.relativeDimensionAt R (PrimeSpectrum.comap (algebraMap S _) r).asIdeal = d := by
    intro r
    rw [Set.mem_ofPred_eq, flat_localization_iff, Nat.card_fin]
    have hrel := Algebra.relativeDimensionAt_comap_eq (R := R) g (Localization.Away g) r.asIdeal
    exact and_congr (isMaximalCohenMacaulay_fiberRing_comap_iff R (Submonoid.powers g) _
      r.asIdeal).symm ⟨fun h ↦ hrel.trans h, fun h ↦ hrel.symm.trans h⟩
  exact ⟨PrimeSpectrum.comap (algebraMap S (Localization.Away g)) '' U,
    fun x ⟨r, hr, hrx⟩ ↦ hrx ▸ (key r).mp hr, hemb.isOpenMap _ hU,
    ⟨qT, (key qT).mpr ⟨hCM, hdim⟩, rfl⟩⟩

/-- For `R → S` flat of finite presentation, the set of primes with Cohen–Macaulay fibre ring is
open. -/
private theorem isOpen_setOf_isMaximalCohenMacaulay_fiber (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.Flat R S] [Algebra.FinitePresentation R S] :
    IsOpen {q : PrimeSpectrum S |
      Module.IsMaximalCohenMacaulay
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S)))))
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S)))))} := by
  convert isOpen_iUnion fun d : ℕ ↦
    Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq R S d using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  exact ⟨fun h ↦ (Algebra.exists_relativeDimensionAt_eq_natCast R q.asIdeal).imp
    fun d hd ↦ ⟨h, hd⟩,
    fun ⟨_, h, _⟩ ↦ h⟩

/-- Over a field the fibre ring at `𝔮` is the local ring `S_𝔮`. -/
private theorem isMaximalCohenMacaulay_fiberRing_iff_of_field (k : Type*)
    {S : Type*} [Field k] [CommRing S] [Algebra k S] (q : Ideal S) [q.IsPrime] :
    Module.IsMaximalCohenMacaulay
        (Localization.AtPrime (q.map (Ideal.Quotient.mk ((q.under k).map (algebraMap k S)))))
        (Localization.AtPrime (q.map (Ideal.Quotient.mk ((q.under k).map (algebraMap k S))))) ↔
      Module.IsMaximalCohenMacaulay (Localization.AtPrime q) (Localization.AtPrime q) := by
  have hbot : (q.under k).map (algebraMap k (Localization.AtPrime q)) = ⊥ := by
    rw [Ideal.eq_bot_of_prime (q.under k), Ideal.map_bot]
  have e := (fiberRingEquiv k q (Localization.AtPrime q)).symm.trans
    ((Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot _))
  exact Module.isMaximalCohenMacaulay_self_iff_of_ringEquiv e

/-- **Stacks 00RF.** Let `S` be a finite type algebra over a field `k`. The set of primes `𝔮` of
`S` such that the local ring `S_𝔮` is Cohen–Macaulay is open in `Spec S`. -/
@[stacks 00RF "Cohen-Macaulayness of the local ring `S_𝔮` (Definition 00N8) is
`Module.IsMaximalCohenMacaulay` of `Localization.AtPrime 𝔮` over itself. The proof is the case
`R = k` of Lemma 00RH; see the module docstring.",
  ega "IV 6.11.3" "affine over field, F=O_X",
  ega "IV 12.1.7" "(iii), over a field"]
theorem PrimeSpectrum.isOpen_setOf_isMaximalCohenMacaulay_localization (k S : Type*) [Field k]
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S] :
    IsOpen {q : PrimeSpectrum S |
      Module.IsMaximalCohenMacaulay (Localization.AtPrime q.asIdeal)
        (Localization.AtPrime q.asIdeal)} := by
  have : Algebra.FinitePresentation k S := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  convert isOpen_setOf_isMaximalCohenMacaulay_fiber k S using 1
  ext q
  exact (isMaximalCohenMacaulay_fiberRing_iff_of_field k q.asIdeal).symm

/-- A set of primes containing every minimal prime is dense: every prime specializes from a
minimal prime below it. -/
private theorem dense_of_minimalPrimes_subset {S : Type*} [CommRing S]
    {W : Set (PrimeSpectrum S)} (hW : ∀ q : PrimeSpectrum S, q.asIdeal ∈ minimalPrimes S → q ∈ W) :
    Dense W := by
  intro x
  obtain ⟨m, hm, hmx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
  have : m.IsPrime := hm.1.1
  have hsp : (⟨m, this⟩ : PrimeSpectrum S) ⤳ x := (PrimeSpectrum.le_iff_specializes _ _).mp hmx
  exact closure_mono (Set.singleton_subset_iff.mpr (hW ⟨m, this⟩ hm))
    (specializes_iff_mem_closure.mp hsp)

/-- **Stacks 00RG.** Let `S` be a finite type algebra over a field `k`. The set of primes `𝔮` of
`S` at which `S_𝔮` is Cohen–Macaulay is a dense open subset of `Spec S`: it is open by Lemma 00RF
and contains every minimal prime, where the local ring has dimension zero. -/
@[stacks 00RG "Cohen-Macaulayness of `S_𝔮` is `Module.IsMaximalCohenMacaulay` of
`Localization.AtPrime 𝔮` over itself; \"dense open\" is the conjunction of `IsOpen` and
`Dense`.", ega "IV 6.11.3" "affine over field, F=O_X", ega "IV 12.1.7" "(iii), over a field"]
theorem PrimeSpectrum.isOpen_and_dense_setOf_isMaximalCohenMacaulay_localization (k S : Type*)
    [Field k] [CommRing S] [Algebra k S] [Algebra.FiniteType k S] :
    IsOpen {q : PrimeSpectrum S |
        Module.IsMaximalCohenMacaulay (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)} ∧
      Dense {q : PrimeSpectrum S |
        Module.IsMaximalCohenMacaulay (Localization.AtPrime q.asIdeal)
          (Localization.AtPrime q.asIdeal)} :=
  ⟨isOpen_setOf_isMaximalCohenMacaulay_localization k S,
    dense_of_minimalPrimes_subset fun q hq ↦
      isMaximalCohenMacaulay_localization_of_mem_minimalPrimes q.asIdeal hq⟩

/-- **Stacks 00RI.** Let `R → S` be flat of finite presentation. The set `W` of primes `𝔮` of `S`
at which the fibre ring `S_𝔮 ⊗_R κ(𝔭)`, `𝔭 = R ∩ 𝔮`, is Cohen–Macaulay is open in `Spec S`, and
for every prime `𝔭` of `R` its trace on the fibre `Spec S ×_{Spec R} {𝔭}` of `Spec S → Spec R` is
dense in that fibre. -/
@[stacks 00RI "The fibre ring is `Localization.AtPrime` of the image of `𝔮` in `S/𝔭S`, as in
00RH and 00RK. The fibre over `𝔭` is the subspace `comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S`
and density is for its subspace topology; openness is asserted in all of `Spec S`, which implies
openness in each fibre. See the module docstring.",
  sga "4 XVIII 2.3" "affine case",
  ega "IV 12.1.1" "(vi), affine, F=O_X", ega "IV 12.1.7" "(iii), affine flat"]
theorem Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    [Algebra.FinitePresentation R S] :
    IsOpen {q : PrimeSpectrum S |
      Module.IsMaximalCohenMacaulay
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S)))))
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S)))))} ∧
    ∀ p : PrimeSpectrum R,
      Dense ((↑) ⁻¹' {q : PrimeSpectrum S |
        Module.IsMaximalCohenMacaulay
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S)))))
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S)))))} :
        Set (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p})) := by
  refine ⟨?_, fun p x ↦ ?_⟩
  · exact isOpen_setOf_isMaximalCohenMacaulay_fiber R S
  · -- a point of the fibre specializes from a minimal point of the fibre, which lies in the set
    have hx : x.1.asIdeal.under R = p.asIdeal := congrArg PrimeSpectrum.asIdeal x.2
    obtain ⟨m, hm, hmx⟩ := Ideal.exists_minimalPrimes_le
      (I := p.asIdeal.map (algebraMap R S)) (J := x.1.asIdeal)
      (by rw [Ideal.map_le_iff_le_comap, ← hx])
    have : m.IsPrime := hm.1.1
    have hmp : m.under R = p.asIdeal := le_antisymm
      (hx ▸ Ideal.comap_mono hmx) (Ideal.map_le_iff_le_comap.mp hm.1.2)
    let m' : PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p} := ⟨⟨m, this⟩, PrimeSpectrum.ext hmp⟩
    have hsp : m' ⤳ x := by
      rw [← Topology.IsInducing.subtypeVal.specializes_iff]
      exact (PrimeSpectrum.le_iff_specializes _ _).mp hmx
    refine closure_mono (Set.singleton_subset_iff.mpr ?_) (specializes_iff_mem_closure.mp hsp)
    show Module.IsMaximalCohenMacaulay _ _
    exact isMaximalCohenMacaulay_fiberRing_of_mem_minimalPrimes R m (by rwa [hmp])

/-- **Stacks 00RL.** Let `R → S` be flat, of finite presentation and with Cohen–Macaulay fibres,
that is with every fibre ring `S_𝔮/𝔭S_𝔮` Cohen–Macaulay. Then `S ≅ S_0 × ⋯ × S_n` as
`R`-algebras, where each `S_d` is flat, of finite presentation and with Cohen–Macaulay fibres
over `R`, and all fibres of `R → S_d` are equidimensional of dimension `d`: the relative
dimension `dim_𝔮(S_d/R)` is `d` at every prime `𝔮` of `S_d`. -/
@[stacks 00RL "The fibre ring is `Localization.AtPrime` of the image of `𝔮` in `S/𝔭S`, as in
00RH. \"All fibres equidimensional of dimension `d`\" is `Algebra.relativeDimensionAt R 𝔮 = d`
at every prime `𝔮` of `S_d`, which is equivalent over a field by Lemma 00OT. The factors are
indexed by `Fin (n + 1)` and live in the universe of `S`. See the module docstring."]
theorem Algebra.exists_algEquiv_pi_of_isMaximalCohenMacaulay_fiber (R : Type u) (S : Type v)
    [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra.FinitePresentation R S]
    (hCM : ∀ q : PrimeSpectrum S,
      Module.IsMaximalCohenMacaulay
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S)))))
          (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
            ((q.asIdeal.under R).map (algebraMap R S)))))) :
    ∃ (n : ℕ) (S' : Fin (n + 1) → Type v) (_ : ∀ d, CommRing (S' d)) (_ : ∀ d, Algebra R (S' d)),
      Nonempty (S ≃ₐ[R] Π d, S' d) ∧ ∀ d, Module.Flat R (S' d) ∧
        Algebra.FinitePresentation R (S' d) ∧
        (∀ q : PrimeSpectrum (S' d),
          Module.IsMaximalCohenMacaulay
            (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
              ((q.asIdeal.under R).map (algebraMap R (S' d))))))
            (Localization.AtPrime (q.asIdeal.map (Ideal.Quotient.mk
              ((q.asIdeal.under R).map (algebraMap R (S' d))))))) ∧
        ∀ q : PrimeSpectrum (S' d), Algebra.relativeDimensionAt R q.asIdeal = (d : ℕ) := by
  classical
  set W : ℕ → Set (PrimeSpectrum S) := fun d ↦ {q | Algebra.relativeDimensionAt R q.asIdeal = d}
    with hWdef
  -- on the Cohen–Macaulay locus, `W d` is the open set of Lemma 00RH
  have hWo : ∀ d, IsOpen (W d) := fun d ↦ by
    convert Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_relativeDimensionAt_eq R S d
      using 1
    ext q
    exact ⟨fun h ↦ ⟨hCM q, h⟩, fun h ↦ h.2⟩
  have hWcover : ∀ q, ∃ d, q ∈ W d := fun q ↦
    Algebra.exists_relativeDimensionAt_eq_natCast R q.asIdeal
  have hWdisj : ∀ d d', d ≠ d' → Disjoint (W d) (W d') := fun d d' hdd' ↦
    Set.disjoint_left.mpr fun q (hq : _ = _) (hq' : _ = _) ↦
      hdd' (by exact_mod_cast hq.symm.trans hq')
  -- finitely many of them are nonempty
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun q _ ↦ Set.mem_iUnion.mpr (hWcover q))
  set n := t.sup _root_.id
  have hWempty : ∀ d, n < d → W d = ∅ := fun d hd ↦ by
    refine Set.eq_empty_of_forall_notMem fun q hq ↦ ?_
    obtain ⟨d', hd't, hq'⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ q))
    have : d' ≤ n := Finset.le_sup (f := _root_.id) hd't
    exact Set.disjoint_left.mp (hWdisj d d' (by omega)) hq hq'
  have hclopen : ∀ d, IsClopen (W d) := fun d ↦ by
    refine ⟨?_, hWo d⟩
    rw [← isOpen_compl_iff]
    convert isOpen_iUnion fun d' : {d' : ℕ // d' ≠ d} ↦ hWo d' using 1
    ext q
    simp only [Set.mem_compl_iff, Set.mem_iUnion]
    obtain ⟨d', hd'⟩ := hWcover q
    refine ⟨fun hq ↦ ⟨⟨d', fun h ↦ hq (h ▸ hd')⟩, hd'⟩, fun ⟨d'', hq⟩ hq' ↦ ?_⟩
    exact Set.disjoint_left.mp (hWdisj d d''.1 (Ne.symm d''.2)) hq' hq
  choose e he heW using fun d : Fin (n + 1) ↦ PrimeSpectrum.isClopen_iff.mp (hclopen d)
  have hcoi : CompleteOrthogonalIdempotents e := by
    have hortho : Pairwise fun d d' ↦ e d * e d' = 0 := fun d d' hdd' ↦ by
      refine ((he d).mul (he d')).eq_zero_of_isNilpotent ?_
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff, PrimeSpectrum.basicOpen_mul]
      ext1
      simp only [TopologicalSpace.Opens.coe_inf, ← heW, TopologicalSpace.Opens.coe_bot]
      exact (hWdisj d d' (fun h ↦ hdd' (Fin.ext h))).eq_bot
    refine ⟨⟨he, hortho⟩, ?_⟩
    have hidem : IsIdempotentElem (1 - ∑ d, e d) :=
      (OrthogonalIdempotents.isIdempotentElem_sum ⟨he, hortho⟩).one_sub
    rw [eq_comm, ← sub_eq_zero]
    refine hidem.eq_zero_of_isNilpotent ?_
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff, eq_bot_iff]
    intro q hq
    obtain ⟨d', hd'⟩ := hWcover q
    have hd'n : d' < n + 1 := by
      by_contra h
      rw [hWempty d' (by omega)] at hd'
      exact hd'
    have hq' : q ∈ (PrimeSpectrum.basicOpen (e ⟨d', hd'n⟩) : Set _) := heW ⟨d', hd'n⟩ ▸ hd'
    have h0 : (1 - ∑ d, e d) * e ⟨d', hd'n⟩ = 0 := by
      rw [sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single ⟨d', hd'n⟩
        (fun b _ hb ↦ hortho hb) (by simp), (he _).eq, sub_self]
    exact (q.isPrime.mem_or_mem_of_mul_eq_zero h0).elim hq hq' |>.elim
  refine ⟨n, fun d ↦ S ⧸ Ideal.span {1 - e d}, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    ⟨AlgEquiv.ofBijective (AlgHom.pi fun d ↦ Ideal.Quotient.mkₐ R _) hcoi.bijective_pi⟩,
    fun d ↦ ?_⟩
  have : IsLocalization.Away (e d) (S ⧸ Ideal.span {1 - e d}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem (he d)
  have : Module.Flat S (S ⧸ Ideal.span {1 - e d}) :=
    IsLocalization.flat _ (Submonoid.powers (e d))
  have : Algebra.FinitePresentation S (S ⧸ Ideal.span {1 - e d}) :=
    IsLocalization.Away.finitePresentation (e d)
  refine ⟨Module.Flat.trans R S _, Algebra.FinitePresentation.trans R S _, fun q ↦ ?_, fun q ↦ ?_⟩
  · exact (isMaximalCohenMacaulay_fiberRing_comap_iff R (Submonoid.powers (e d)) _ q.asIdeal).mp
      (hCM (PrimeSpectrum.comap (algebraMap S _) q))
  · rw [← Algebra.relativeDimensionAt_comap_eq (e d) (S ⧸ Ideal.span {1 - e d}) q.asIdeal]
    have hq : PrimeSpectrum.comap (algebraMap S (S ⧸ Ideal.span {1 - e d})) q ∈ W d := by
      rw [heW d, ← PrimeSpectrum.localization_away_comap_range (S ⧸ Ideal.span {1 - e d}) (e d)]
      exact ⟨q, rfl⟩
    exact hq
end
