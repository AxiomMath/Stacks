module

public import StacksFrontier.Algebra.Homology.ProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import Mathlib.RingTheory.DualNumber

/-!
# The residue field of the dual numbers has infinite projective dimension

For a field `k`, let `R = k[ε]` be the ring of dual numbers and let `M = R/(ε)`. The module `M`
is represented in the derived category by the periodic free resolution whose differentials are
multiplication by `ε`, but its projective dimension is infinite.

## Main definitions

There are no new definitions.

## Main results

* `StacksDraft.ProjectiveDimension.dualNumber_quotient_eps_periodic_resolution_infinite_dimension`
  gives the periodic resolution of `R/(ε)` and asserts that its projective dimension is infinite.

## Implementation notes

The displayed rightward complex in the source is represented cohomologically in nonpositive
degrees. Its term in degree `-n` is free of rank one, and its differential from degree `-(n+1)`
to degree `-n` is multiplication by `ε`. Infinite projective dimension is expressed by
`projectiveDimension M = ⊤`.

Infinite projective dimension is established here by the private dimension-shifting chain
ending in `residue_projectiveDimension_eq_top`: the short exact sequence
`0 → R/(ε) → R → R/(ε) → 0` has projective middle term, so
`HasProjectiveDimensionLT M (n + 2) ↔ HasProjectiveDimensionLT M (n + 1)`, and `M` is not
projective, so no finite bound holds.

That chain deliberately duplicates the mathematics of
`StacksFrontier.Algebra.Homology.ProjectiveDimension`'s `DualNumberInfiniteProjDim.main_theorem`,
which runs the same argument. The duplication is not an oversight: `main_theorem` is stated for
`k : Type`, and discharging the first conjunct from it would force this tag's statement down to
`Type 0`, weakening it relative to the source. A faithful `Type u` statement takes priority over
avoiding the duplication. The `DualNumberInfiniteProjDim` development is universe-polymorphic in
substance — only its top-level `variable (k : Type)` binder pins it — so the two can be collapsed
by generalising that binder to `Type u` and deleting the private helpers below.

## References

* [Stacks Project, Tag 0A5Q](https://stacks.math.columbia.edu/tag/0A5Q)
-/

open CategoryTheory Limits

namespace StacksDraft.ProjectiveDimension

universe w u

private lemma mul_eps_eq_zero_iff (k : Type u) [Field k] (r : DualNumber k) :
    r * DualNumber.eps = 0 ↔
      r ∈ Ideal.span {(DualNumber.eps : DualNumber k)} := by
  rw [Ideal.mem_span_singleton']
  constructor
  · intro h
    have hfst : r.fst = 0 := by
      simpa [TrivSqZeroExt.snd_mul, DualNumber.snd_eps, DualNumber.fst_eps] using
        congrArg TrivSqZeroExt.snd h
    refine ⟨TrivSqZeroExt.inl r.snd, ?_⟩
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, hfst]
    · simp [TrivSqZeroExt.snd_mul, DualNumber.snd_eps, DualNumber.fst_eps]
  · rintro ⟨s, rfl⟩
    simp [mul_assoc, DualNumber.eps_mul_eps]

private abbrev epsMul (k : Type u) [Field k] :
    DualNumber k →ₗ[DualNumber k] DualNumber k :=
  LinearMap.mulLeft (DualNumber k) DualNumber.eps

private lemma ofHom_epsMul_comp (k : Type u) [Field k] :
    ModuleCat.ofHom (epsMul k) ≫ ModuleCat.ofHom (epsMul k) = 0 := by
  apply ModuleCat.hom_ext
  change (epsMul k).comp (epsMul k) = 0
  apply LinearMap.ext
  intro x
  apply TrivSqZeroExt.ext <;>
    simp [epsMul, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul,
      DualNumber.fst_eps, DualNumber.snd_eps]

private noncomputable def periodicChainComplex (k : Type u) [Field k] :
    ChainComplex (ModuleCat.{u} (DualNumber k)) ℕ :=
  ChainComplex.of
    (fun _ ↦ ModuleCat.of (DualNumber k) (DualNumber k))
    (fun _ ↦ ModuleCat.ofHom (epsMul k))
    (fun _ ↦ ofHom_epsMul_comp k)

private lemma periodicChainComplex_d (k : Type u) [Field k] (n : ℕ) :
    (periodicChainComplex k).d (n + 1) n =
      ModuleCat.ofHom (epsMul k) := by
  simp [periodicChainComplex]

/-- Multiples of `ε` vanish in the quotient `R/(ε)`. -/
private lemma mkQ_eps_mul (k : Type u) [Field k] (x : DualNumber k) :
    (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ (DualNumber.eps * x) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right x _ (Ideal.mem_span_singleton_self _)

private noncomputable def periodicAugmentation (k : Type u) [Field k] :
    periodicChainComplex k ⟶
      (ChainComplex.single₀ (ModuleCat.{u} (DualNumber k))).obj
        (ModuleCat.of (DualNumber k)
          (DualNumber k ⧸ Ideal.span {(DualNumber.eps : DualNumber k)})) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨ModuleCat.ofHom (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ, by
      rw [periodicChainComplex_d]
      apply ModuleCat.hom_ext
      change (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ.comp (epsMul k) = 0
      exact LinearMap.ext (mkQ_eps_mul k)⟩

private lemma augmentation_exact (k : Type u) [Field k] :
    Function.Exact
      (epsMul k)
      (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ := by
  intro r
  constructor
  · intro h
    change Submodule.Quotient.mk r = 0 at h
    rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at h
    obtain ⟨s, rfl⟩ := h
    exact ⟨s, by simp [epsMul, mul_comm]⟩
  · rintro ⟨s, rfl⟩
    exact mkQ_eps_mul k s

private lemma periodic_exact (k : Type u) [Field k] :
    Function.Exact (epsMul k) (epsMul k) := fun r ↦ by
  have : epsMul k r = 0 ↔ (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ r = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← mul_eps_eq_zero_iff, epsMul,
      LinearMap.mulLeft_apply, mul_comm]
  exact this.trans (augmentation_exact k r)

private noncomputable def periodicProjectiveResolution (k : Type u) [Field k] :
    ProjectiveResolution
      (ModuleCat.of (DualNumber k)
        (DualNumber k ⧸ Ideal.span {(DualNumber.eps : DualNumber k)})) where
  complex := periodicChainComplex k
  projective _ := ModuleCat.projective_of_free
    (Module.Free.chooseBasis (DualNumber k) (DualNumber k))
  π := periodicAugmentation k
  quasiIso := ⟨fun n ↦ by
    cases n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · change (ShortComplex.mk (ModuleCat.ofHom (epsMul k))
              (ModuleCat.ofHom (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ) _).Exact ∧
              Epi (ModuleCat.ofHom (Ideal.span
                {(DualNumber.eps : DualNumber k)}).mkQ)
          exact ⟨
            (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
              (augmentation_exact k),
            (ModuleCat.epi_iff_surjective _).2 (Submodule.Quotient.mk_surjective _)⟩
        all_goals rfl
    | succ n =>
        rw [quasiIsoAt_iff_exactAt']
        · rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
          dsimp [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
            periodicChainComplex]
          rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
          simpa [ChainComplex.of.d] using periodic_exact k
        · apply ChainComplex.exactAt_succ_single_obj⟩

private abbrev Residue (k : Type u) [Field k] :=
  DualNumber k ⧸ Ideal.span {(DualNumber.eps : DualNumber k)}

private noncomputable def residueObj (k : Type u) [Field k] :
    ModuleCat (DualNumber k) := ModuleCat.of (DualNumber k) (Residue k)

private instance residue_nontrivial (k : Type u) [Field k] : Nontrivial (Residue k) := by
  apply (Ideal.Quotient.nontrivial_iff).2
  rw [Ideal.ne_top_iff_one]
  intro h
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨a, ha⟩ := h
  simpa [TrivSqZeroExt.fst_mul, DualNumber.fst_eps] using congrArg TrivSqZeroExt.fst ha

private lemma eps_mem_residue_annihilator (k : Type u) [Field k] :
    (DualNumber.eps : DualNumber k) ∈
      Module.annihilator (DualNumber k) (Residue k) := by
  rw [Module.mem_annihilator]
  intro m
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  exact mkQ_eps_mul k x

private lemma residueObj_not_projective (k : Type u) [Field k] :
    ¬ Projective (residueObj k) := by
  intro hproj
  have hMproj : Module.Projective (DualNumber k) (Residue k) :=
    (IsProjective.iff_projective (Residue k)).2 hproj
  have : Module.Flat (DualNumber k) (Residue k) := Module.Flat.of_projective
  have : Module.Free (DualNumber k) (Residue k) := Module.free_of_flat_of_isLocalRing
  have : FaithfulSMul (DualNumber k) (Residue k) :=
    @Module.Free.instFaithfulSMulOfNontrivial
      (DualNumber k) (Residue k) _ _ _ _ _
  have hann : Module.annihilator (DualNumber k) (Residue k) = ⊥ :=
    (Module.annihilator_eq_bot).2 inferInstance
  have h := eps_mem_residue_annihilator k
  rw [hann, Ideal.mem_bot] at h
  simpa [DualNumber.snd_eps] using congrArg TrivSqZeroExt.snd h

private noncomputable def residueToDual (k : Type u) [Field k] :
    Residue k →ₗ[DualNumber k] DualNumber k :=
  Submodule.liftQ _
    (LinearMap.toSpanSingleton (DualNumber k) (DualNumber k) DualNumber.eps) (by
    rw [Ideal.span_le]
    rintro x rfl
    simp [DualNumber.eps_mul_eps])

private lemma residueToDual_mk (k : Type u) [Field k] (x : DualNumber k) :
    residueToDual k (Submodule.Quotient.mk x) = x * DualNumber.eps := by
  rw [residueToDual, Submodule.liftQ_apply]
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

private noncomputable def periodicShortComplex (k : Type u) [Field k] :
    ShortComplex (ModuleCat (DualNumber k)) :=
  ShortComplex.mk
    (ModuleCat.ofHom (residueToDual k))
    (ModuleCat.ofHom (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (r * DualNumber.eps) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Ideal.mul_mem_left _ r (Ideal.mem_span_singleton_self _))

private lemma periodicShortComplex_shortExact (k : Type u) [Field k] :
    (periodicShortComplex k).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (residueToDual k)
      (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, residueToDual,
      Submodule.range_liftQ, LinearMap.range_toSpanSingleton]
  · change Function.Injective (residueToDual k)
    intro x y h
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [residueToDual_mk] at h
    change Submodule.Quotient.mk r = Submodule.Quotient.mk s
    rw [Submodule.Quotient.eq, ← mul_eps_eq_zero_iff k]
    simpa [sub_mul] using sub_eq_zero.mpr h
  · change Function.Surjective
      (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ
    exact Submodule.Quotient.mk_surjective _

private lemma residue_projectiveDimension_eq_top (k : Type u) [Field k] :
    projectiveDimension (residueObj k) = ⊤ := by
  have hperiodic (n : ℕ) :
      HasProjectiveDimensionLT (residueObj k) (n + 2) ↔
        HasProjectiveDimensionLT (residueObj k) (n + 1) := by
    have key := (periodicShortComplex_shortExact k).hasProjectiveDimensionLT_X₃_iff n
      (ModuleCat.projective_of_free (Module.Free.chooseBasis (DualNumber k) (DualNumber k)))
    exact key
  have hnot : ∀ n : ℕ, ¬ HasProjectiveDimensionLT (residueObj k) (n + 1) := by
    intro n
    induction n with
    | zero =>
        intro h
        exact residueObj_not_projective k
          (CategoryTheory.instProjectiveOfHasProjectiveDimensionLTOfNatNat (residueObj k))
    | succ n ih => exact fun h ↦ ih ((hperiodic n).1 h)
  by_contra h
  obtain ⟨n, hn⟩ := (projectiveDimension_ne_top_iff (residueObj k)).1 h
  exact hnot n hn

/-- **Stacks 0A5Q.** For the ring `R = k[ε]` of dual numbers over a field and `M = R/(ε)`, the
module `M` is represented by the periodic free complex with all differentials multiplication by
`ε`, but `M` has infinite projective dimension. -/
@[stacks 0A5Q]
public theorem dualNumber_quotient_eps_periodic_resolution_infinite_dimension
    (k : Type u) [Field k]
    [HasDerivedCategory.{w} (ModuleCat.{u} (DualNumber k))] :
    let R := DualNumber k
    let ε : R := DualNumber.eps
    let M := ModuleCat.of R (R ⧸ Ideal.span {ε})
    projectiveDimension M = ⊤ ∧
      ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
        Nonempty
          (DerivedCategory.Q.obj P ≅
            (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ∧
          (∀ i : ℤ, 0 < i → IsZero (P.X i)) ∧
          ∃ e : ∀ n : ℕ, P.X (-(n : ℤ)) ≅ ModuleCat.of R R,
            ∀ n : ℕ,
              P.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (e n).hom =
                (e (n + 1)).hom ≫
                  ModuleCat.ofHom (LinearMap.mulLeft R ε) := by
  dsimp
  refine ⟨residue_projectiveDimension_eq_top k, ?_⟩
  let Q := periodicProjectiveResolution k
  refine ⟨Q.cochainComplex, ⟨asIso (DerivedCategory.Q.map Q.π')⟩,
    fun i hi ↦ CochainComplex.isZero_of_isStrictlyLE _ 0 i hi, ?_⟩
  let e : ∀ n : ℕ,
      Q.cochainComplex.X (-(n : ℤ)) ≅
        ModuleCat.of (DualNumber k) (DualNumber k) :=
    fun n ↦ Q.cochainComplexXIso (-(n : ℤ)) n ≪≫
      eqToIso (by dsimp [Q, periodicProjectiveResolution, periodicChainComplex])
  refine ⟨e, fun n ↦ ?_⟩
  rw [Q.cochainComplex_d_assoc (-(↑n + 1)) (-(n : ℤ)) (n + 1) n
    (by omega) rfl]
  dsimp [e]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  dsimp [Q, periodicProjectiveResolution]
  rw [periodicChainComplex_d]
  rfl

end StacksDraft.ProjectiveDimension
