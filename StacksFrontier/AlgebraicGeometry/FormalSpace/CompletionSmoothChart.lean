module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionStageLifting
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmoothOverFormalSpectrum
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothAtSpec
public import StacksFrontier.RingTheory.Smooth.AdicStageSmoothLocus
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientSurjection

/-!
# Smoothness near a point of the lifting property, over an affine target

Let `S` be a scheme contained in a big fppf site `B`, let `V = Spec R` be a Noetherian affine
scheme of the site, locally of finite type over `S`, let `Z ⊆ |V|` be closed and let
`G : V_{/Z} ⟶ Spf C₀` be a morphism to the formal spectrum of a Noetherian adic ring which is
representable by algebraic spaces. If `G` has the lifting property at a closed point `v`
(`AlgebraicGeometry.FormalSpace.LiftsAtCompletion`), then there is `f ∈ R` with `v ∈ D(f)` such
that `G` restricted to the completion of `D(f)` is smooth. This is the affine case of the proof of
Stacks 0GI9.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isPullback_stage_pow`: the base change of `G` over the
  quotient stage `Spec (C₀/bⁿ⁺¹)` is `Spec (R^∧/bⁿ⁺¹R^∧)`.

## References

* [Stacks Project, Tag 0GI9](https://stacks.math.columbia.edu/tag/0GI9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] instTopologicalSpaceAdicCompletion'

/-- The adic completion of a Noetherian ring is a topological ring. -/
local instance instIsTopologicalRingAdicCompletion'' {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) : IsTopologicalRing (AdicCompletion I A) :=
  adicCompletion_isTopologicalRing I

/-- The adic completion of a Noetherian ring carries a linear topology. -/
local instance instIsLinearTopologyAdicCompletion'' {A : Type u} [CommRing A]
    [IsNoetherianRing A] (I : Ideal A) :
    IsLinearTopology (AdicCompletion I A) (AdicCompletion I A) :=
  adicCompletion_isLinearTopology I

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (hR : B.Contains (Spec (.of R)))
  (s : Spec (.of R) ⟶ S) (I : Ideal R)
  {C₀ : Type u} [CommRing C₀] [TopologicalSpace C₀] [IsTopologicalRing C₀]
  [IsLinearTopology C₀ C₀]

/-- **The base change over a power of an ideal of definition.** For `Spf φ`, `φ : C₀ → R^∧` taut,
and `b` an ideal defining the topology of `C₀`, the base change of `Spf φ` over the quotient stage
`Spec (C₀/bⁿ⁺¹)` is the quotient stage `Spec (R^∧/bⁿ⁺¹R^∧)`: the closure of `bⁿ⁺¹R^∧` is
`bⁿ⁺¹R^∧` itself, `R^∧` being Noetherian and complete. -/
theorem exists_isPullback_stage_pow (hC₀ : TopologicalRing.IsWeaklyAdmissible C₀)
    (E : QuotientSystem B S hS C₀)
    (φ : ContinuousHom E (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing))
    (hwA : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I R))
    (htaut : RingHom.IsTaut φ.toRingHom) {b : Ideal C₀} (hb : _root_.IsAdic b) (n : ℕ) :
    ∃ (hw : TopologicalRing.IsWeakIdealOfDefinition ((b ^ (n + 1)).map φ.toRingHom))
      (hJK : b ^ (n + 1) ≤ Ideal.comap φ.toRingHom ((b ^ (n + 1)).map φ.toRingHom)),
      IsPullback
        (colimit.ι (formalSpectrumDiagram
          (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing))
          (OrderDual.toDual ⟨_, hw⟩))
        ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          ((BigAffineFppf.inclusion B S hS).map (φ.stageMap
            ⟨b ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hb n.succ_ne_zero⟩ ⟨_, hw⟩ hJK)))
        (formalSpectrumMap hC₀ φ)
        (colimit.ι (formalSpectrumDiagram E) (OrderDual.toDual
          ⟨b ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hb n.succ_ne_zero⟩)) := by
  obtain ⟨⟨K, hKw⟩, hK, hJK, hsq⟩ := isPullback_formalSpectrumMap_stage_of_isTaut B S hS hC₀ hwA E
    (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing) φ htaut
    ⟨b ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hb n.succ_ne_zero⟩
  obtain rfl : K = (b ^ (n + 1)).map φ.toRingHom := hK.trans (adicCompletion_closure_eq I _)
  exact ⟨hKw, hJK, hsq⟩

/-- **The prime of the completion over a point of `V(I)`.** For a prime `p ⊇ I` of `R` there is a
prime `q` of `R^∧` lying over `p` which contains every topologically nilpotent element. -/
theorem exists_prime_adicCompletion (p : Ideal R) [p.IsPrime] (hp : I ≤ p) :
    ∃ q : Ideal (AdicCompletion I R), q.IsPrime ∧
      q.comap (algebraMap R (AdicCompletion I R)) = p ∧
      ∀ t : AdicCompletion I R, IsTopologicallyNilpotent t → t ∈ q := by
  let e := (AdicCompletion.evalₐ I 1).toRingHom
  have hp1 : RingHom.ker (Ideal.Quotient.mk (I ^ 1)) ≤ p := by
    rwa [Ideal.mk_ker, pow_one]
  have := Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk (I ^ 1))
    Ideal.Quotient.mk_surjective hp1
  refine ⟨(p.map (Ideal.Quotient.mk (I ^ 1))).comap e, Ideal.comap_isPrime _ _, ?_, ?_⟩
  · have he : e.comp (algebraMap R (AdicCompletion I R)) = Ideal.Quotient.mk (I ^ 1) := by
      ext x
      show AdicCompletion.evalₐ I 1 (algebraMap R (AdicCompletion I R) x) = _
      rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
      rfl
    rw [Ideal.comap_comap, he, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot]
    exact sup_eq_left.mpr hp1
  · intro t ht
    let : TopologicalSpace R := I.adicTopology
    have hnhds : ((I ^ 1 • (⊤ : Submodule R (AdicCompletion I R)) : Submodule R _) :
        Set (AdicCompletion I R)) ∈ nhds (0 : AdicCompletion I R) :=
      (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis
        (AdicCompletion I R))).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_of_mem ⟨1, rfl⟩
    obtain ⟨m, hm⟩ := (ht.eventually hnhds).exists
    have hker : e (t ^ m) = 0 := by
      have h1 : AdicCompletion.eval I R 1 (t ^ m) = 0 := by
        rwa [← LinearMap.mem_ker,
          ← AdicCompletion.pow_smul_top_eq_ker_eval I.fg_of_isNoetherianRing]
      have h2 := AdicCompletion.factor_evalₐ_eq_eval I (t ^ m) (n := 1) (by simp)
      rw [h1] at h2
      show AdicCompletion.evalₐ I 1 (t ^ m) = 0
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I 1 (t ^ m))
      rw [← ha] at h2 ⊢
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at h2
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simpa using h2
    have hmem : t ^ m ∈ (p.map (Ideal.Quotient.mk (I ^ 1))).comap e := by
      rw [Ideal.mem_comap, hker]
      exact zero_mem _
    exact (Ideal.comap_isPrime _ _).mem_of_pow_mem m hmem

omit [IsTopologicalRing C₀] [IsLinearTopology C₀ C₀] in
/-- The stage maps of a continuous homomorphism into the adic quotient system of `R` are locally
of finite type, `Spec R ⟶ S` being so. -/
theorem locallyOfFiniteType_quotientMap_stage [LocallyOfFiniteType s] (E : QuotientSystem B S hS C₀)
    (φ : ContinuousHom E (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing))
    (J : {J : Ideal C₀ // TopologicalRing.IsWeakIdealOfDefinition J})
    (K : {K : Ideal (AdicCompletion I R) // TopologicalRing.IsWeakIdealOfDefinition K})
    (hJK : J.1 ≤ Ideal.comap φ.toRingHom K.1) :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ.toRingHom hJK))) := by
  let ρ : R →+* AdicCompletion I R ⧸ K.1 :=
    (Ideal.Quotient.mk K.1).comp (algebraMap R (AdicCompletion I R))
  let q := Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 φ.toRingHom hJK))
  have hover : q ≫ E.overS J = Spec.map (CommRingCat.ofHom ρ) ≫ s := φ.overS J K hJK
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom ρ) ≫ s) := by
    have : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom ρ)) :=
      AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
        (adicCompletion_quotient_surjective I I.fg_of_isNoetherianRing ⟨K.1, K.2.1⟩)
    infer_instance
  have : LocallyOfFiniteType (q ≫ E.overS J) := by
    rw [hover]
    infer_instance
  exact locallyOfFiniteType_of_comp q (E.overS J)

omit [IsNoetherianRing R] in
/-- The image in `R^∧/𝔨` of a prime `q ⊇ 𝔨` of `R^∧` lies over `q ∩ R`. -/
theorem specMap_quotient_map_eq {K : Ideal (AdicCompletion I R)} (q : Ideal (AdicCompletion I R))
    (hK : K ≤ q) (hq' : (q.map (Ideal.Quotient.mk K)).IsPrime) (v : PrimeSpectrum R)
    (hqv : q.comap (algebraMap R (AdicCompletion I R)) = v.asIdeal) :
    Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk K).comp (algebraMap R (AdicCompletion I R))))
      (⟨q.map (Ideal.Quotient.mk K), hq'⟩ : PrimeSpectrum _) = v := by
  apply PrimeSpectrum.ext
  show Ideal.comap ((Ideal.Quotient.mk K).comp (algebraMap R (AdicCompletion I R)))
    (q.map (Ideal.Quotient.mk K)) = _
  rw [← Ideal.comap_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hK, hqv]

/-- An element of `R^∧` has a representative `f₀ ∈ R` modulo an open ideal `K`, so that `f` and
`f₀` lie in the same ideals containing `K`. -/
private theorem exists_forall_mem_iff_of_isOpen {K : Ideal (AdicCompletion I R)}
    (hK : IsOpen (K : Set (AdicCompletion I R))) (f : AdicCompletion I R) :
    ∃ f₀ : R, ∀ Q : Ideal (AdicCompletion I R), K ≤ Q →
      (f ∈ Q ↔ algebraMap R (AdicCompletion I R) f₀ ∈ Q) := by
  obtain ⟨f₀, hf₀⟩ := adicCompletion_quotient_surjective I I.fg_of_isNoetherianRing ⟨K, hK⟩
    (Ideal.Quotient.mk _ f)
  have h : f - algebraMap R (AdicCompletion I R) f₀ ∈ K := by
    rw [← Ideal.Quotient.eq]
    exact hf₀.symm
  exact ⟨f₀, fun Q hKQ => ⟨fun hf => by simpa using Q.sub_mem hf (hKQ h),
    fun hf => by simpa using Q.add_mem (hKQ h) hf⟩⟩

/-- The pullback to `A` of a prime of `A/bⁿ⁺¹A` contains the image of `b`. -/
private theorem map_le_comap_of_pow_succ {A C : Type*} [CommRing A] [CommRing C]
    (g : C →+* A) (b : Ideal C) (n : ℕ) (x : PrimeSpectrum (A ⧸ (b ^ (n + 1)).map g)) :
    b.map g ≤ x.asIdeal.comap (Ideal.Quotient.mk ((b ^ (n + 1)).map g)) := by
  have : (x.asIdeal.comap (Ideal.Quotient.mk ((b ^ (n + 1)).map g))).IsPrime :=
    Ideal.comap_isPrime _ _
  intro y hy
  refine this.mem_of_pow_mem (n + 1) ?_
  show Ideal.Quotient.mk _ (y ^ (n + 1)) ∈ x.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (show y ^ (n + 1) ∈ (b ^ (n + 1)).map g by
    rw [Ideal.map_pow]
    exact Ideal.pow_mem_pow hy _)]
  exact zero_mem _

/-- **A common smooth neighbourhood of all the stages (affine case).** If `G = Spf φ` has the
lifting property at a closed point `v` of `V(I)`, there is `f₀ ∈ R` with `f₀ ∉ v` such that every
stage map `Spec (R^∧/bⁿ⁺¹R^∧) ⟶ Spec (C₀/bⁿ⁺¹)` is smooth at every point lying over a point of
`D(f₀)`. The stage maps are smooth over `v` by the lifting criterion, and the key step
`Algebra.exists_notMem_forall_smoothAt_quotient_pow` spreads this out. -/
theorem exists_notMem_forall_smoothAt_stage [LocallyOfFiniteType s] [IsNoetherianRing C₀]
    (hC₀ : TopologicalRing.IsWeaklyAdmissible C₀) (E : QuotientSystem B S hS C₀)
    (G : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s))
      (zeroLocusPoints B S hS hR s I) ⟶ formalSpectrum E)
    (φ : ContinuousHom E (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing))
    (hφ : formalSpectrumMap hC₀ φ =
      completionComparison B S hS hR s I
        (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing)
        (quotientSystemCompatible_adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing) ≫
        G)
    (hwA : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I R))
    (htaut : RingHom.IsTaut φ.toRingHom) {b : Ideal C₀} (hb : _root_.IsAdic b)
    (v : PrimeSpectrum R) (hvI : I ≤ v.asIdeal)
    (hlift : LiftsAtCompletion B S hS (affineOver B S hS hR s) (zeroLocusPoints B S hS hR s I)
      (formalSpectrum E) G v) :
    ∃ f₀ : R, f₀ ∉ v.asIdeal ∧ ∀ (n : ℕ)
      (x : PrimeSpectrum (AdicCompletion I R ⧸ (b ^ (n + 1)).map φ.toRingHom)),
      f₀ ∉ (PrimeSpectrum.comap ((Ideal.Quotient.mk _).comp
        (algebraMap R (AdicCompletion I R))) x).asIdeal →
      InfinitesimalLifting.SmoothAt (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap ((b ^ (n + 1)).map φ.toRingHom) φ.toRingHom Ideal.le_comap_map))) x := by
  classical
  let : Algebra C₀ (AdicCompletion I R) := φ.toRingHom.toAlgebra
  have : IsNoetherianRing (AdicCompletion I R) := Stacks.AdicCompletion.NoetherianRing.solution I
  obtain ⟨q, hqp, hqv, hqn⟩ := exists_prime_adicCompletion I v.asIdeal hvI
  obtain ⟨hw₀, -, -⟩ := exists_isPullback_stage_pow B S hS hR s I hC₀ E φ hwA htaut hb 0
  -- the hypotheses of the key step
  have hq : b.map (algebraMap C₀ (AdicCompletion I R)) ≤ q := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hqn _ (hw₀.2 _ (Ideal.mem_map_of_mem _ (by simpa using hx)))
  have hstage : ∀ n : ℕ, LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap ((b ^ (n + 1)).map φ.toRingHom) φ.toRingHom Ideal.le_comap_map))) :=
    fun n => locallyOfFiniteType_quotientMap_stage B S hS hR s I E φ
      ⟨b ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hb n.succ_ne_zero⟩
      ⟨_, (exists_isPullback_stage_pow B S hS hR s I hC₀ E φ hwA htaut hb n).1⟩ _
  have hft : ∀ n : ℕ, Algebra.FiniteType (C₀ ⧸ b ^ (n + 1))
      (AdicCompletion I R ⧸ (b ^ (n + 1)).map (algebraMap C₀ (AdicCompletion I R))) := fun n =>
    RingHom.finiteType_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp (hstage n))
  have hsm : ∀ n : ℕ, have := Algebra.isPrime_map_quotient (Algebra.map_pow_succ_le hq n)
      Algebra.SmoothAt (C₀ ⧸ b ^ (n + 1))
        (AdicCompletion I R ⧸ (b ^ (n + 1)).map (algebraMap C₀ (AdicCompletion I R)))
        (q.map (Ideal.Quotient.mk ((b ^ (n + 1)).map (algebraMap C₀ (AdicCompletion I R))))) := by
    intro n
    have := Algebra.isPrime_map_quotient (Algebra.map_pow_succ_le hq n)
    obtain ⟨hw, hJK, hsq⟩ := exists_isPullback_stage_pow B S hS hR s I hC₀ E φ hwA htaut hb n
    have hx := specMap_quotient_map_eq I q (Algebra.map_pow_succ_le hq n) inferInstance v hqv
    have h2 := smoothAt_stageMap_of_liftsAtCompletion B S hS hR s I hC₀ E G φ hφ
      ⟨b ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hb n.succ_ne_zero⟩ ⟨_, hw⟩ hJK hsq v
      hlift _ hx
    exact (InfinitesimalLifting.smoothAt_specMap_iff
      (R := C₀ ⧸ b ^ (n + 1))
      (A := AdicCompletion I R ⧸ (b ^ (n + 1)).map (algebraMap C₀ (AdicCompletion I R))) _).mp h2
  obtain ⟨f, hfq, hf⟩ := Algebra.exists_notMem_forall_smoothAt_quotient_pow b q hq hft hsm
  -- a representative of `f` modulo `b R^∧`
  obtain ⟨f₀, hf₀⟩ := exists_forall_mem_iff_of_isOpen I hw₀.1 f
  have hdiffQ : ∀ Q : Ideal (AdicCompletion I R), b.map (algebraMap C₀ (AdicCompletion I R)) ≤ Q →
      (f ∈ Q ↔ algebraMap R (AdicCompletion I R) f₀ ∈ Q) := fun Q hbQ =>
    hf₀ Q (by rw [zero_add, pow_one]; exact hbQ)
  refine ⟨f₀, fun h => hfq ((hdiffQ q hq).mpr ?_), ?_⟩
  · rwa [← Ideal.mem_comap, hqv]
  · intro n x hx
    let Q : Ideal (AdicCompletion I R) :=
      x.asIdeal.comap (Ideal.Quotient.mk ((b ^ (n + 1)).map φ.toRingHom))
    have : Q.IsPrime := Ideal.comap_isPrime _ _
    have hbQ : b.map (algebraMap C₀ (AdicCompletion I R)) ≤ Q :=
      map_le_comap_of_pow_succ φ.toRingHom b n x
    have hfQ : f ∉ Q := fun h => hx ((hdiffQ Q hbQ).mp h)
    have hxQ : Q.map (Ideal.Quotient.mk ((b ^ (n + 1)).map (algebraMap C₀ (AdicCompletion I R)))) =
        x.asIdeal := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
    refine (InfinitesimalLifting.smoothAt_specMap_iff (R := C₀ ⧸ b ^ (n + 1))
      (A := AdicCompletion I R ⧸ (b ^ (n + 1)).map (algebraMap C₀ (AdicCompletion I R))) x).mpr ?_
    convert hf n Q hbQ hfQ using 2
    exact hxQ.symm

omit [IsLinearTopology C₀ C₀] in
/-- An open ideal of `C₀` contains a power `bⁿ⁺¹` of an ideal of definition `b`. -/
theorem exists_pow_succ_le_of_isAdic {b : Ideal C₀} (hb : _root_.IsAdic b)
    (J : { J : Ideal C₀ // TopologicalRing.IsWeakIdealOfDefinition J }) :
    ∃ n : ℕ, b ^ (n + 1) ≤ J.1 := by
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hb).2 J.1 (J.2.1.mem_nhds J.1.zero_mem)
  exact ⟨n, (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn⟩

/-- Precomposing a pullback square with an isomorphism into the base gives a pullback square. -/
private theorem isPullback_comp_of_isIso {C : Type*} [Category C] {P X Y Z W : C} {a : P ⟶ X}
    {b : P ⟶ Z} {c : Z ⟶ W} {G : Y ⟶ W} (e : X ⟶ Y) [IsIso e] (h : IsPullback a b (e ≫ G) c) :
    IsPullback (a ≫ e) b G c :=
  IsPullback.of_iso h (Iso.refl _) (asIso e) (Iso.refl _) (Iso.refl _)
    (Category.id_comp _).symm ((Category.comp_id _).trans (Category.id_comp _).symm)
    (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- **Smoothness of the stages gives the lifting property (affine case).** If every stage map
`Spec (R^∧/bⁿ⁺¹R^∧) ⟶ Spec (C₀/bⁿ⁺¹)` is smooth at every point over `u`, then `G = Spf φ` has the
lifting property at `u`: a section of `Spf C₀` over an Artinian `Spec D'` factors through a stage
(Tag 0AIA), hence through some `Spec (C₀/bⁿ⁺¹)`, and the base change over it is the stage map. -/
theorem liftsAtCompletion_of_forall_smoothAt_stage [LocallyOfFiniteType s] [IsNoetherianRing C₀]
    (hC₀ : TopologicalRing.IsWeaklyAdmissible C₀) (E : QuotientSystem B S hS C₀)
    (G : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s))
      (zeroLocusPoints B S hS hR s I) ⟶ formalSpectrum E)
    (φ : ContinuousHom E (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing))
    (hφ : formalSpectrumMap hC₀ φ =
      completionComparison B S hS hR s I
        (adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing)
        (quotientSystemCompatible_adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing) ≫
        G)
    (hwA : TopologicalRing.IsWeaklyAdmissible (AdicCompletion I R))
    (htaut : RingHom.IsTaut φ.toRingHom) {b : Ideal C₀} (hb : _root_.IsAdic b)
    (u : PrimeSpectrum R)
    (hsm : ∀ (n : ℕ) (x : PrimeSpectrum (AdicCompletion I R ⧸ (b ^ (n + 1)).map φ.toRingHom)),
      PrimeSpectrum.comap ((Ideal.Quotient.mk _).comp (algebraMap R (AdicCompletion I R))) x = u →
      InfinitesimalLifting.SmoothAt (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap ((b ^ (n + 1)).map φ.toRingHom) φ.toRingHom Ideal.le_comap_map))) x) :
    LiftsAtCompletion B S hS (affineOver B S hS hR s) (zeroLocusPoints B S hS hR s I)
      (formalSpectrum E) G u := by
  classical
  intro D' D φ' hφ' hloc hD hD' t α hα hpt _ ha z hz
  have := hloc
  let 𝒥 := BigFppfOver.topology B S hS
  let sY := Sheaf.sheafifiedYoneda 𝒥
  let incl := BigAffineFppf.inclusion B S hS
  -- the section `z` factors through a stage `Spec (C₀/bⁿ⁺¹)`
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj (affineOver B S hS hD' t)) :=
    inferInstanceAs (CompactSpace (Spec (.of D')))
  obtain ⟨I₀, p, hp⟩ := exists_factorsThroughStage_of_compactSpace hC₀.1 E
    (affineOver B S hS hD' t) inferInstance ((Sheaf.sectionEquiv 𝒥).symm z)
  obtain ⟨n, hn⟩ := exists_pow_succ_le_of_isAdic hb I₀
  let J : { J : Ideal C₀ // TopologicalRing.IsWeakIdealOfDefinition J } :=
    ⟨b ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hb n.succ_ne_zero⟩
  have hJI : OrderDual.toDual I₀ ⟶ OrderDual.toDual J := homOfLE hn
  let tY : affineOver B S hS hD' t ⟶ incl.obj (E.stage J) := p ≫ incl.map (E.diagram.map hJI)
  have hzt : z = Sheaf.sectionEquiv 𝒥 (sY.map tY ≫
      colimit.ι (formalSpectrumDiagram E) (OrderDual.toDual J)) := by
    have hw := colimit.w (formalSpectrumDiagram E) hJI
    have e : sY.map tY ≫ colimit.ι (formalSpectrumDiagram E) (OrderDual.toDual J) =
        (Sheaf.sectionEquiv 𝒥).symm z := by
      refine ((congrArg (· ≫ _) (sY.map_comp _ _)).trans (Category.assoc _ _ _)).trans ?_
      exact (congrArg (sY.map p ≫ ·) hw).trans hp
    rw [e]
    exact (Equiv.apply_symm_apply (Sheaf.sectionEquiv 𝒥) z).symm
  -- the base change of `G` over that stage
  obtain ⟨hw, hJK, hsq⟩ := exists_isPullback_stage_pow B S hS hR s I hC₀ E φ hwA htaut hb n
  let Dq := adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing
  let hDq := quotientSystemCompatible_adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing
  let cmp := completionComparison B S hS hR s I Dq hDq
  let K : { K : Ideal (AdicCompletion I R) // TopologicalRing.IsWeakIdealOfDefinition K } := ⟨_, hw⟩
  have hcmp : IsIso cmp := isIso_completionComparison_adicQuotientSystem B S hS hR s I
    I.fg_of_isNoetherianRing
  let ι : sY.obj (incl.obj (Dq.stage K)) ⟶ Space.completionSheaf B S hS
      (yoneda.obj (affineOver B S hS hR s)) (zeroLocusPoints B S hS hR s I) :=
    colimit.ι (formalSpectrumDiagram Dq) (OrderDual.toDual K) ≫ cmp
  have hpb : IsPullback ι (sY.map (incl.map (φ.stageMap J K hJK))) G
      (colimit.ι (formalSpectrumDiagram E) (OrderDual.toDual J)) := by
    rw [hφ] at hsq
    exact isPullback_comp_of_isIso cmp hsq
  have : AlgebraicGeometry.IsLocallyNoetherian
      ((BigFppfOver.toScheme B S hS).obj (incl.obj (E.stage J))) :=
    inferInstanceAs (AlgebraicGeometry.IsLocallyNoetherian (Spec (.of (C₀ ⧸ J.1))))
  have : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (incl.map (φ.stageMap J K hJK))) :=
    locallyOfFiniteType_quotientMap_stage B S hS hR s I E φ J K hJK
  exact exists_lift_of_isPullback_of_smoothAt B S hS (c := quotientStageToAffine B S hS hR s I Dq
    hDq K) hpb (fun αs => exists_presheafSection_eq_stage B S hS hR s I K αs) u
    (fun x hx => hsm n x hx) φ' hφ' hD hD' t α hα hpt ha z hz tY hzt

omit [IsNoetherianRing R] in
/-- The points of a quotient stage `Spec (R^∧/K)` lie over `V(I)`: the image of `I` in the discrete
quotient `R^∧/K` is nilpotent. -/
theorem le_asIdeal_comap_of_isOpen (K : Ideal (AdicCompletion I R))
    (hK : IsOpen (K : Set (AdicCompletion I R))) (x : PrimeSpectrum (AdicCompletion I R ⧸ K)) :
    I ≤ (PrimeSpectrum.comap ((Ideal.Quotient.mk K).comp
      (algebraMap R (AdicCompletion I R))) x).asIdeal := by
  let : TopologicalSpace R := I.adicTopology
  obtain ⟨-, ⟨n, rfl⟩, hn⟩ :=
    (I.ringFilterBasis.moduleFilterBasis (I.adic_module_basis
      (AdicCompletion I R))).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff.mp
      (hK.mem_nhds K.zero_mem)
  intro i hi
  show Ideal.Quotient.mk K (algebraMap R (AdicCompletion I R) i) ∈ x.asIdeal
  apply x.isPrime.mem_of_pow_mem n
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem.mpr]
  · exact zero_mem _
  · apply hn
    show algebraMap R (AdicCompletion I R) (i ^ n) ∈
      I ^ n • (⊤ : Submodule R (AdicCompletion I R))
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow hi n) Submodule.mem_top

/-- **The lifting property everywhere gives smoothness (affine case).** If `G : V_{/V(I)} ⟶ Spf C₀`
is representable by algebraic spaces and has the lifting property at every point of
`V(I) ⊆ Spec R`, then `G` is smooth. -/
theorem hasPropertyULift_isSmoothULift_of_forall_liftsAtCompletion [LocallyOfFiniteType s]
    [IsNoetherianRing C₀] (hC₀ : TopologicalRing.IsAdic C₀) (E : QuotientSystem B S hS C₀)
    {Z : Set (Space.points B S hS (yoneda.obj (affineOver B S hS hR s)))}
    (hZ : Z = zeroLocusPoints B S hS hR s I)
    (G : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s)) Z ⟶ formalSpectrum E)
    (hG : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G.hom)
    (hlift : ∀ u : PrimeSpectrum R, I ≤ u.asIdeal →
      LiftsAtCompletion B S hS (affineOver B S hS hR s) Z (formalSpectrum E) G u) :
    Space.HasPropertyULift.{u + 1} B S hS (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom)
      G.hom hG := by
  classical
  subst hZ
  obtain ⟨b, -, hb⟩ := hC₀.1
  obtain ⟨φ, htaut, hwA, hφ⟩ := exists_continuousHom_completionComparison B S hS hR s I hC₀ E G hG
  refine hasPropertyULift_isSmoothULift_of_stage_pullbacks B S hS hC₀.isWeaklyAdmissible E G hG ?_
  intro J
  obtain ⟨n, hn⟩ := exists_pow_succ_le_of_isAdic hb J
  obtain ⟨hw, hJK, hsq⟩ := exists_isPullback_stage_pow B S hS hR s I hC₀.isWeaklyAdmissible E φ hwA
    htaut hb n
  let 𝒥 := BigFppfOver.topology B S hS
  let sY := Sheaf.sheafifiedYoneda 𝒥
  let incl := BigAffineFppf.inclusion B S hS
  let J' : { J : Ideal C₀ // TopologicalRing.IsWeakIdealOfDefinition J } :=
    ⟨b ^ (n + 1), isWeakIdealOfDefinition_pow_of_isAdic hb n.succ_ne_zero⟩
  let Dq := adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing
  let hDq := quotientSystemCompatible_adicQuotientSystem B S hS hR s I I.fg_of_isNoetherianRing
  let cmp := completionComparison B S hS hR s I Dq hDq
  let K : { K : Ideal (AdicCompletion I R) // TopologicalRing.IsWeakIdealOfDefinition K } := ⟨_, hw⟩
  have hcmp : IsIso cmp := isIso_completionComparison_adicQuotientSystem B S hS hR s I
    I.fg_of_isNoetherianRing
  have hpb : IsPullback (colimit.ι (formalSpectrumDiagram Dq) (OrderDual.toDual K) ≫ cmp)
      (sY.map (incl.map (φ.stageMap J' K hJK))) G
      (formalSpectrumInclusion E (OrderDual.toDual J')) := by
    rw [hφ] at hsq
    exact isPullback_comp_of_isIso cmp hsq
  refine ⟨J', hn, _, incl.map (φ.stageMap J' K hJK), _, hpb, ?_⟩
  apply InfinitesimalLifting.smooth_of_forall_smoothAt
  intro x
  exact smoothAt_stageMap_of_liftsAtCompletion B S hS hR s I hC₀.isWeaklyAdmissible E G φ hφ J' K
    hJK hsq _ (hlift _ (le_asIdeal_comap_of_isOpen I K.1 hw.1 x)) x rfl

omit [IsNoetherianRing R] in
/-- The preimage of `V(I)` under the map of represented presheaves induced by `R → R'` is
`V(IR')`. -/
private theorem preimage_zeroLocusPoints_affineOverHom {R' : Type u} [CommRing R']
    [Algebra R R'] (hR' : B.Contains (Spec (.of R'))) :
    Space.pointsMap B S hS
        (yoneda.obj (affineOver B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ s)))
        (yoneda.map (affineOverHom B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ s)
          (V := affineOver B S hS hR s) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) rfl)) ⁻¹'
      zeroLocusPoints B S hS hR s I =
      zeroLocusPoints B S hS hR' _ (I.map (algebraMap R R')) := by
  rw [zeroLocusPoints_eq_preimage_pointsToScheme, zeroLocusPoints_eq_preimage_pointsToScheme]
  ext x
  show Space.pointsToScheme B S hS (affineOver B S hS hR s)
      (Space.pointsMap B S hS
        (yoneda.obj (affineOver B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ s)))
        (yoneda.map (affineOverHom B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ s)
          (V := affineOver B S hS hR s) (Spec.map (CommRingCat.ofHom (algebraMap R R'))) rfl)) x)
      ∈ PrimeSpectrum.zeroLocus (I : Set R) ↔
    Space.pointsToScheme B S hS
        (affineOver B S hS hR' (Spec.map (CommRingCat.ofHom (algebraMap R R')) ≫ s)) x ∈
      PrimeSpectrum.zeroLocus (I.map (algebraMap R R') : Set R')
  rw [Space.pointsToScheme_pointsMap]
  show I ≤ Ideal.comap (algebraMap R R') _ ↔ I.map (algebraMap R R') ≤ _
  exact Ideal.map_le_iff_le_comap.symm

/-- **Smoothness near a point of the lifting property (affine case).** Let
`G : V_{/V(I)} ⟶ Spf C₀`, for `V = Spec R` and `C₀` a Noetherian adic ring, be representable by
algebraic spaces with the lifting property at a point `v ∈ V(I)`. Then there is an open
neighbourhood `D(f₀)` of `v` such that `G` restricted to the completion of `D(f₀)` is smooth: the
stage maps are smooth over `D(f₀)` (`exists_notMem_forall_smoothAt_stage`), so `G` has the lifting
property at every point of `D(f₀)`, hence so has its restriction, which is therefore smooth. -/
theorem exists_isOpenImmersion_smooth_of_liftsAtCompletion_affine [LocallyOfFiniteType s]
    [IsNoetherianRing C₀] (hC₀ : TopologicalRing.IsAdic C₀) (E : QuotientSystem B S hS C₀)
    (G : Space.completionSheaf B S hS (yoneda.obj (affineOver B S hS hR s))
      (zeroLocusPoints B S hS hR s I) ⟶ formalSpectrum E)
    (hG : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS G.hom)
    (v : PrimeSpectrum R)
    (hlift : I ≤ v.asIdeal → LiftsAtCompletion B S hS (affineOver B S hS hR s)
      (zeroLocusPoints B S hS hR s I) (formalSpectrum E) G v) :
    ∃ (U : BigFppfOver B S hS) (j : U ⟶ affineOver B S hS hR s),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      v ∈ Set.range ((BigFppfOver.toScheme B S hS).map j) ∧
      ∃ hrep, Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ a ↦ Space.IsSmoothULift.{u + 1} B S hS a.hom)
        (Space.completionSheafMap B S hS (yoneda.map j) (zeroLocusPoints B S hS hR s I) ≫ G).hom
        hrep := by
  classical
  obtain ⟨b, -, hb⟩ := hC₀.1
  obtain ⟨φ, htaut, hwA, hφ⟩ := exists_continuousHom_completionComparison B S hS hR s I hC₀ E G hG
  obtain ⟨f₀, hf₀v, hliftD⟩ : ∃ f₀ : R, f₀ ∉ v.asIdeal ∧ ∀ u : PrimeSpectrum R, f₀ ∉ u.asIdeal →
      I ≤ u.asIdeal → LiftsAtCompletion B S hS (affineOver B S hS hR s)
        (zeroLocusPoints B S hS hR s I) (formalSpectrum E) G u := by
    by_cases hvI : I ≤ v.asIdeal
    · obtain ⟨f₀, hf₀v, hf₀⟩ := exists_notMem_forall_smoothAt_stage B S hS hR s I
        hC₀.isWeaklyAdmissible E G φ hφ hwA htaut hb v hvI (hlift hvI)
      exact ⟨f₀, hf₀v, fun u hu _ => liftsAtCompletion_of_forall_smoothAt_stage B S hS hR s I
        hC₀.isWeaklyAdmissible E G φ hφ hwA htaut hb u
        (fun n x hx => hf₀ n x (by rwa [hx]))⟩
    · obtain ⟨f₀, hf₀I, hf₀v⟩ := Set.not_subset.mp hvI
      exact ⟨f₀, hf₀v, fun u hu hIu => absurd (hIu hf₀I) hu⟩
  let Rf := Localization.Away f₀
  have : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers f₀) Rf
    inferInstance
  let ι : Spec (.of Rf) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R Rf))
  have : IsOpenImmersion ι := Scheme.isOpenImmersion_SpecMap_localizationAway (R := .of R) f₀
  have hRf : B.Contains (Spec (.of Rf)) :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact ι) hR
  let s' := ι ≫ s
  let j : affineOver B S hS hRf s' ⟶ affineOver B S hS hR s :=
    affineOverHom B S hS hRf s' (V := affineOver B S hS hR s) ι rfl
  have : IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) :=
    inferInstanceAs (IsOpenImmersion ι)
  let I' := I.map (algebraMap R Rf)
  have hT' : Space.pointsMap B S hS (yoneda.obj (affineOver B S hS hRf s')) (yoneda.map j) ⁻¹'
      zeroLocusPoints B S hS hR s I = zeroLocusPoints B S hS hRf s' I' :=
    preimage_zeroLocusPoints_affineOverHom B S hS hR s I hRf
  have hrep := Space.isRepresentableByAlgebraicSpacesULift_comp B S hS _ _
    (Space.isRepresentableByAlgebraicSpacesULift_completionMap B S hS
      (isAlgebraicSpace_yoneda B S hS _) (isAlgebraicSpace_yoneda B S hS _) (yoneda.map j)
      (zeroLocusPoints B S hS hR s I)) hG
  refine ⟨_, j, inferInstance, ?_, hrep, ?_⟩
  · obtain ⟨w, hw⟩ : v ∈ Set.range (PrimeSpectrum.comap (algebraMap R Rf)) := by
      rwa [PrimeSpectrum.localization_away_comap_range Rf f₀]
    exact ⟨w, hw⟩
  · refine hasPropertyULift_isSmoothULift_of_forall_liftsAtCompletion B S hS hRf s' I' hC₀ E hT' _
      hrep (fun u hIu => liftsAtCompletion_comp_completionSheafMap B S hS j _ _ G u
        (hliftD _ ?_ ?_))
    · intro h
      have h' : algebraMap R Rf f₀ ∈ u.asIdeal := h
      exact u.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h'
        (IsLocalization.Away.algebraMap_isUnit f₀))
    · intro i hi
      exact hIu (Ideal.mem_map_of_mem _ hi)

end AlgebraicGeometry.FormalSpace
