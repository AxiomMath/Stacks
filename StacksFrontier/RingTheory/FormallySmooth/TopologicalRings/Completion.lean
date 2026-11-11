module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.Nonarchimedean.Completion
public import Mathlib.Topology.Algebra.UniformRing
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.FormallySmooth.AdicLifting
public import StacksFrontier.RingTheory.FormallySmooth.BaseChange
public import StacksFrontier.RingTheory.FormallySmooth.Topological
public import StacksFrontier.Topology.Algebra.AdicTopology.Continuous
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings.AdicCriterion
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings.AdicCompletionComparison

@[expose] public section

/-!
# Formally smooth maps of topological rings: adic completion

Stacks Project, Chapter 15 "More on Algebra". The tags treated here are

07ED.

## Tag 07ED — Formal smoothness and adic completion

For a continuous homomorphism between rings with finitely generated adic ideals,
formal smoothness is unchanged by completing the target or by completing both
the source and target.

### Main results

* `isFormallySmooth_iff_adicCompletion`: formal smoothness is equivalent
  for a map, its map to the completed target, and the induced map on completions.

### Implementation notes

The completions are uniform completions of the rings equipped with their adic
topologies. On each completed ring, formal smoothness is evaluated using the
adic topology defined by the extension of the original ideal. The maps to and
between completions are the canonical maps induced by the original continuous
ring homomorphism. The exported `uniformCompletionRingEquiv` identifies this
model with `AdicCompletion`, compatibly with the canonical ring maps.

### References

* Stacks Project, Tag 07ED.

-/

/-! ### Stacks Tag 07ED -/

section

@[expose] public section

open scoped Topology Uniformity

open Filter Set Function

open UniformSpace

namespace Stacks.FormallySmooth.TopologicalRings

/-- A ring homomorphism from `R` with the `I`-adic topology to a discrete ring is continuous
if and only if its kernel contains a power of `I`. -/
public theorem continuous_ringHom_to_discrete_iff
    {R A : Type*} [CommRing R] (I : Ideal R)
    [CommRing A] [TopologicalSpace A] [DiscreteTopology A] (f : R →+* A) :
    @Continuous R A I.adicTopology _ f ↔ ∃ n : ℕ, I ^ n ≤ RingHom.ker f := by
  let : TopologicalSpace R := I.adicTopology
  constructor
  · intro hf
    have hker : (RingHom.ker f : Set R) ∈ nhds (0 : R) := by
      change f ⁻¹' {0} ∈ nhds (0 : R)
      exact hf.continuousAt.preimage_mem_nhds (by simp)
    simpa [SetLike.coe_subset_coe] using I.hasBasis_nhds_zero_adic.mem_iff.mp hker
  · rintro ⟨n, hn⟩
    apply continuous_of_continuousAt_zero f
    rw [continuousAt_def, map_zero]
    intro s hs
    have hzero : (0 : A) ∈ s := mem_of_mem_nhds hs
    refine I.hasBasis_nhds_zero_adic.mem_iff.mpr ⟨n, trivial, ?_⟩
    intro x hx
    simpa [show f x = 0 from hn hx] using hzero

/-- A ring homomorphism is continuous for the `I`-adic and `J`-adic topologies if and only if
the preimage of every power of `J` contains a power of `I`. -/
public theorem continuous_ringHom_adic_iff
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    (f : R →+* S) :
    @Continuous R S I.adicTopology J.adicTopology f ↔
      ∀ n : ℕ, ∃ k : ℕ, I ^ k ≤ (J ^ n).comap f := by
  let : TopologicalSpace R := I.adicTopology
  let : TopologicalSpace S := J.adicTopology
  constructor
  · intro h
    have ht := (I.hasBasis_nhds_zero_adic.tendsto_iff
      J.hasBasis_nhds_zero_adic).mp (by simpa [ContinuousAt] using h.continuousAt (x := 0))
    intro n
    obtain ⟨k, -, hk⟩ := ht n trivial
    exact ⟨k, hk⟩
  · intro h
    apply continuous_of_continuousAt_zero f
    rw [ContinuousAt, map_zero]
    apply (I.hasBasis_nhds_zero_adic.tendsto_iff J.hasBasis_nhds_zero_adic).mpr
    intro n _
    obtain ⟨k, hk⟩ := h n
    exact ⟨k, trivial, hk⟩

end Stacks.FormallySmooth.TopologicalRings

open Stacks.FormallySmooth.TopologicalRings

/-- The extension of a continuous ring map to the completion restricts to it on the ring. -/
private theorem extensionHom_comp_coeRingHom
    {R A : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T0Space A] (f : R →+* A) (hf : Continuous f) :
    (Completion.extensionHom f hf).comp Completion.coeRingHom = f :=
  RingHom.ext (Completion.extensionHom_coe f hf)

private theorem continuous_extensionHom_adic
    {R A : Type*} [CommRing R] (I : Ideal R)
    [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [DiscreteTopology A] [CompleteSpace A] [T0Space A] :
    letI : WithIdeal R := ⟨I⟩
    ∀ (f : R →+* A) (hf : Continuous f),
    let Ihat : Ideal (Completion R) := I.map Completion.coeRingHom
    @Continuous (Completion R) A Ihat.adicTopology _
      (Completion.extensionHom f hf) := by
  let : WithIdeal R := ⟨I⟩
  intro f hf
  let Ihat : Ideal (Completion R) := I.map Completion.coeRingHom
  obtain ⟨k, hk⟩ := (continuous_ringHom_to_discrete_iff I f).mp hf
  apply (continuous_ringHom_to_discrete_iff Ihat (Completion.extensionHom f hf)).mpr
  refine ⟨k, ?_⟩
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
  intro x hx
  change Completion.extensionHom f hf x = 0
  rw [Completion.extensionHom_coe]
  exact hk hx

private theorem completion_sub_coe_mem_adic_pow
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG) :
    letI : WithIdeal R := ⟨I⟩
    ∀ (x : Completion R) (n : ℕ),
      ∃ r : R, x - Completion.coeRingHom r ∈
        (I.map Completion.coeRingHom) ^ n := by
  let : WithIdeal R := ⟨I⟩
  let e := AdicCompletionBridge.adicCompletionRingEquiv I (by rfl : IsAdic I)
  have her (r : R) : e (Completion.coeRingHom r) = AdicCompletion.of I R r := by
    change e (↑r : Completion R) = AdicCompletion.of I R r
    exact AdicCompletionBridge.adicCompletionRingEquiv_coe I (by rfl : IsAdic I) r
  have he : e.toRingHom.comp Completion.coeRingHom =
      (algebraMap R (AdicCompletion I R)) :=
    RingHom.ext fun r => (her r).trans (AdicCompletion.algebraMap_apply I r).symm
  intro x n
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective (I ^ n • (⊤ : Submodule R R))
    ((e x).val n)
  refine ⟨r, ?_⟩
  have hker : e x - AdicCompletion.of I R r ∈
      (AdicCompletion.eval I R n).ker := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero, AdicCompletion.eval_of]
    exact hr.symm
  have hsmul : e x - AdicCompletion.of I R r ∈
      I ^ n • (⊤ : Submodule R (AdicCompletion I R)) := by
    rwa [AdicCompletion.pow_smul_top_eq_ker_eval hI]
  have hmap : e x - AdicCompletion.of I R r ∈
      Ideal.map (algebraMap R (AdicCompletion I R)) (I ^ n) := by
    rwa [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map]
  have hmap' : e (x - Completion.coeRingHom r) ∈
      Ideal.map e.toRingHom ((I.map Completion.coeRingHom) ^ n) := by
    rwa [map_sub, her, ← Ideal.map_pow, Ideal.map_map, he]
  obtain ⟨y, hy, hye⟩ := (Ideal.mem_map_of_equiv e _).mp hmap'
  exact (show x - Completion.coeRingHom r = y from e.injective hye.symm) ▸ hy

/-- The canonical completion map is continuous for the extended ideal topology. -/
theorem continuous_coeRingHom_adic
    {R : Type*} [CommRing R] (I : Ideal R) :
    letI : WithIdeal R := ⟨I⟩
    @Continuous R (Completion R) I.adicTopology
      (I.map Completion.coeRingHom).adicTopology Completion.coeRingHom := by
  let : WithIdeal R := ⟨I⟩
  refine (continuous_ringHom_adic_iff I (I.map Completion.coeRingHom)
    Completion.coeRingHom).mpr fun n => ⟨n, fun r hr => ?_⟩
  change Completion.coeRingHom r ∈ (I.map Completion.coeRingHom) ^ n
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem Completion.coeRingHom hr

private theorem ringHom_ext_adic_completion
    {R A : Type*} [CommRing R] [CommRing A]
    [TopologicalSpace A] [DiscreteTopology A]
    (I : Ideal R) (hI : I.FG) :
    letI : WithIdeal R := ⟨I⟩
    ∀ (g h : Completion R →+* A),
      @Continuous (Completion R) A
        (I.map Completion.coeRingHom).adicTopology _ g →
      @Continuous (Completion R) A
        (I.map Completion.coeRingHom).adicTopology _ h →
      g.comp Completion.coeRingHom = h.comp Completion.coeRingHom →
      g = h := by
  let : WithIdeal R := ⟨I⟩
  intro g h hg hh hcomp
  refine RingHom.ext fun x => ?_
  obtain ⟨k, hk⟩ := (continuous_ringHom_to_discrete_iff
    (I.map Completion.coeRingHom) g).mp hg
  obtain ⟨l, hl⟩ := (continuous_ringHom_to_discrete_iff
    (I.map Completion.coeRingHom) h).mp hh
  obtain ⟨r, hr⟩ := completion_sub_coe_mem_adic_pow I hI x (max k l)
  have hg0 : g (x - Completion.coeRingHom r) = 0 :=
    hk ((Ideal.pow_le_pow_right (le_max_left k l)) hr)
  have hh0 : h (x - Completion.coeRingHom r) = 0 :=
    hl ((Ideal.pow_le_pow_right (le_max_right k l)) hr)
  have hgr : g x = g (Completion.coeRingHom r) := sub_eq_zero.mp (by rwa [← map_sub])
  have hhr : h x = h (Completion.coeRingHom r) := sub_eq_zero.mp (by rwa [← map_sub])
  rw [hgr, hhr]
  exact DFunLike.congr_fun hcomp r

/-- The induced completion map is continuous for the extended ideal topologies. -/
theorem continuous_mapRingHom_adic
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : @Continuous R S I.adicTopology J.adicTopology f) :
    letI : WithIdeal R := ⟨I⟩
    letI : WithIdeal S := ⟨J⟩
    @Continuous (Completion R) (Completion S)
      (I.map Completion.coeRingHom).adicTopology
      (J.map Completion.coeRingHom).adicTopology
      (Completion.mapRingHom f hf) := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨J⟩
  let Ihat : Ideal (Completion R) := I.map Completion.coeRingHom
  let Jhat : Ideal (Completion S) := J.map Completion.coeRingHom
  let fhat : Completion R →+* Completion S := Completion.mapRingHom f hf
  have hfactor : fhat.comp Completion.coeRingHom =
      Completion.coeRingHom.comp f := RingHom.ext (Completion.mapRingHom_coe hf)
  apply (continuous_ringHom_adic_iff Ihat Jhat fhat).mpr
  intro n
  obtain ⟨k, hk⟩ := (continuous_ringHom_adic_iff I J f).mp hf n
  refine ⟨k, (Ideal.map_le_iff_le_comap).mp ?_⟩
  calc
    Ideal.map fhat (Ihat ^ k) =
        Ideal.map (fhat.comp Completion.coeRingHom) (I ^ k) := by
          rw [← Ideal.map_pow, Ideal.map_map]
    _ = Ideal.map (Completion.coeRingHom.comp f) (I ^ k) := by rw [hfactor]
    _ = Ideal.map Completion.coeRingHom (Ideal.map f (I ^ k)) := by
          rw [Ideal.map_map]
    _ ≤ Ideal.map Completion.coeRingHom (J ^ n) :=
          Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr hk)
    _ = Jhat ^ n := Ideal.map_pow Completion.coeRingHom J n

/-- The induced homomorphism between algebraic adic completions of a continuous ring map,
obtained by transporting `UniformSpace.Completion.mapRingHom` along
`uniformCompletionRingEquiv`. -/
noncomputable def uniformAdicCompletionMap {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : @Continuous R S I.adicTopology J.adicTopology f) :
    AdicCompletion I R →+* AdicCompletion J S := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨J⟩
  exact (uniformCompletionRingEquiv J).toRingHom.comp
    ((Completion.mapRingHom f hf).comp (uniformCompletionRingEquiv I).symm.toRingHom)

/-- Naturality of the comparison between uniform and algebraic completions. -/
theorem uniformCompletionRingEquiv_comp_mapRingHom
    {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : @Continuous R S I.adicTopology J.adicTopology f) :
    letI : WithIdeal R := ⟨I⟩
    letI : WithIdeal S := ⟨J⟩
    (uniformCompletionRingEquiv J).toRingHom.comp (Completion.mapRingHom f hf) =
      (uniformAdicCompletionMap I J f hf).comp (uniformCompletionRingEquiv I).toRingHom := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨J⟩
  ext x
  simp [uniformAdicCompletionMap]

/-- The algebraic completion map extends the original ring homomorphism. -/
@[simp]
theorem uniformAdicCompletionMap_comp_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : @Continuous R S I.adicTopology J.adicTopology f) :
    (uniformAdicCompletionMap I J f hf).comp (algebraMap R (AdicCompletion I R)) =
      (algebraMap S (AdicCompletion J S)).comp f := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨J⟩
  rw [← uniformCompletionRingEquiv_comp_coeRingHom I,
    ← RingHom.comp_assoc, ← uniformCompletionRingEquiv_comp_mapRingHom]
  refine RingHom.ext fun r => ?_
  change uniformCompletionRingEquiv J
    ((Completion.mapRingHom f hf) (↑r : Completion R)) =
      algebraMap S (AdicCompletion J S) (f r)
  rw [Completion.mapRingHom_coe]
  exact uniformCompletionRingEquiv_coe J (f r)

/-- A local homomorphism induces a local homomorphism on maximal ideal completions. -/
theorem isLocalHom_mapRingHom {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S]
    (hR : (IsLocalRing.maximalIdeal R).FG) (hS : (IsLocalRing.maximalIdeal S).FG)
    (f : R →+* S) [IsLocalHom f]
    (hf : @Continuous R S (IsLocalRing.maximalIdeal R).adicTopology
      (IsLocalRing.maximalIdeal S).adicTopology f) :
    letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
    letI : WithIdeal S := ⟨IsLocalRing.maximalIdeal S⟩
    IsLocalHom (Completion.mapRingHom f hf) := by
  let : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  let : WithIdeal S := ⟨IsLocalRing.maximalIdeal S⟩
  let := isLocalRing_uniformCompletion hR
  let := isLocalRing_uniformCompletion hS
  apply ((IsLocalRing.local_hom_TFAE (Completion.mapRingHom f hf)).out 3 1).mp
  rw [maximalIdeal_uniformCompletion_eq_map hR, maximalIdeal_uniformCompletion_eq_map hS,
    Ideal.map_map]
  have hfactor : (Completion.mapRingHom f hf).comp Completion.coeRingHom =
      Completion.coeRingHom.comp f := RingHom.ext (Completion.mapRingHom_coe hf)
  rw [hfactor, ← Ideal.map_map]
  exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le f)

private theorem discrete_ideal_quotient
    {A : Type*} [CommRing A] [TopologicalSpace A] [DiscreteTopology A]
    (K : Ideal A) : DiscreteTopology (A ⧸ K) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  simpa only [Set.image_singleton] using
    (QuotientRing.isOpenQuotientMap_mk K).isOpenMap
      ({a} : Set A) (isOpen_discrete _)

private theorem formallySmoothTop_target_completion_iff.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (hJ : J.FG) (f : R →+* S)
    (_hf : @Continuous R S I.adicTopology J.adicTopology f) :
    letI : WithIdeal R := ⟨I⟩
    letI : WithIdeal S := ⟨J⟩
    let Jhat : Ideal (Completion S) := J.map Completion.coeRingHom
    letI : TopologicalSpace (Completion S) := Jhat.adicTopology
    letI : IsTopologicalRing (Completion S) := Jhat.nonarchimedean.toIsTopologicalRing
    RingHom.FormallySmoothTop.{u} f ↔
      RingHom.FormallySmoothTop.{u} (Completion.coeRingHom.comp f) := by
  let : WithIdeal R := ⟨I⟩
  let : WithIdeal S := ⟨J⟩
  let Jhat : Ideal (Completion S) := J.map Completion.coeRingHom
  let : TopologicalSpace (Completion S) := Jhat.adicTopology
  let : IsTopologicalRing (Completion S) := Jhat.nonarchimedean.toIsTopologicalRing
  have hcoe : Continuous (Completion.coeRingHom : S →+* Completion S) :=
    continuous_coeRingHom_adic J
  constructor
  · intro hs A _ _ _ K hK fa hfa gbar hgbar hcomm
    have hbar : Continuous (gbar.comp Completion.coeRingHom) := hgbar.comp hcoe
    have hcomm' : (gbar.comp Completion.coeRingHom).comp f =
        (Ideal.Quotient.mk K).comp fa := by
      simpa only [RingHom.comp_assoc] using hcomm
    obtain ⟨g, hg, hgf, hπg⟩ := hs A K hK fa hfa
      (gbar.comp Completion.coeRingHom) hbar hcomm'
    let : DiscreteTopology (A ⧸ K) := discrete_ideal_quotient K
    rcases @DiscreteTopology.eq_bot A _ _ with rfl
    let : UniformSpace A := ⊥
    let gext : Completion S →+* A := Completion.extensionHom g hg
    have hgext : Continuous gext := continuous_extensionHom_adic J g hg
    refine ⟨gext, hgext, ?_, ?_⟩
    · rw [← RingHom.comp_assoc, extensionHom_comp_coeRingHom]
      exact hgf
    · apply ringHom_ext_adic_completion J hJ
      · exact (continuous_of_discreteTopology :
          Continuous (Ideal.Quotient.mk K : A →+* A ⧸ K)).comp hgext
      · exact hgbar
      · rw [RingHom.comp_assoc, extensionHom_comp_coeRingHom]
        exact hπg
  · intro hs A _ _ _ K hK fa hfa gbar hgbar hcomm
    let : DiscreteTopology (A ⧸ K) := discrete_ideal_quotient K
    let : UniformSpace (A ⧸ K) := ⊥
    have hgbar' : @Continuous S (A ⧸ K) _
        (⊥ : UniformSpace (A ⧸ K)).toTopologicalSpace gbar := by
      rw [UniformSpace.toTopologicalSpace_bot, ← (@DiscreteTopology.eq_bot (A ⧸ K)
        (topologicalRingQuotientTopology K) (discrete_ideal_quotient K))]
      exact hgbar
    let barext : Completion S →+* A ⧸ K := Completion.extensionHom gbar hgbar'
    have hbarext' : @Continuous (Completion S) (A ⧸ K) Jhat.adicTopology
        (⊥ : UniformSpace (A ⧸ K)).toTopologicalSpace barext :=
      continuous_extensionHom_adic J gbar hgbar'
    have hbarext : Continuous barext := by
      change @Continuous (Completion S) (A ⧸ K) Jhat.adicTopology
        (topologicalRingQuotientTopology K) barext
      rw [@DiscreteTopology.eq_bot (A ⧸ K)
        (topologicalRingQuotientTopology K) (discrete_ideal_quotient K)]
      exact hbarext'
    have hcomm' : barext.comp (Completion.coeRingHom.comp f) =
        (Ideal.Quotient.mk K).comp fa := by
      rw [← RingHom.comp_assoc, extensionHom_comp_coeRingHom]
      exact hcomm
    obtain ⟨g, hg, hgf, hπg⟩ := hs A K hK fa hfa barext hbarext hcomm'
    refine ⟨g.comp Completion.coeRingHom, hg.comp hcoe, ?_, ?_⟩
    · simpa only [RingHom.comp_assoc] using hgf
    · rw [← RingHom.comp_assoc, hπg, extensionHom_comp_coeRingHom]

private theorem formallySmoothTop_source_completion_iff.{u, v, w}
    {R : Type v} {T : Type w} [CommRing R] [CommRing T]
    [TopologicalSpace T] [IsTopologicalRing T]
    (I : Ideal R) (hI : I.FG) :
    letI : WithIdeal R := ⟨I⟩
    let Ihat : Ideal (Completion R) := I.map Completion.coeRingHom
    letI : TopologicalSpace (Completion R) := Ihat.adicTopology
    letI : IsTopologicalRing (Completion R) := Ihat.nonarchimedean.toIsTopologicalRing
    ∀ (F : Completion R →+* T), Continuous F →
      (RingHom.FormallySmoothTop.{u} (F.comp Completion.coeRingHom) ↔
        RingHom.FormallySmoothTop.{u} F) := by
  let : WithIdeal R := ⟨I⟩
  let Ihat : Ideal (Completion R) := I.map Completion.coeRingHom
  let : TopologicalSpace (Completion R) := Ihat.adicTopology
  let : IsTopologicalRing (Completion R) := Ihat.nonarchimedean.toIsTopologicalRing
  change ∀ (F : Completion R →+* T), Continuous F →
    (RingHom.FormallySmoothTop.{u} (F.comp Completion.coeRingHom) ↔ RingHom.FormallySmoothTop.{u} F)
  intro F hF
  have hcoe : Continuous (Completion.coeRingHom : R →+* Completion R) :=
    continuous_coeRingHom_adic I
  constructor
  · intro hs A _ _ _ K hK fa hfa gbar hgbar hcomm
    have hfa' : Continuous (fa.comp Completion.coeRingHom) := hfa.comp hcoe
    have hcomm' : gbar.comp (F.comp Completion.coeRingHom) =
        (Ideal.Quotient.mk K).comp (fa.comp Completion.coeRingHom) := by
      simpa only [RingHom.comp_assoc] using congrArg
        (fun q : Completion R →+* A ⧸ K => q.comp Completion.coeRingHom) hcomm
    obtain ⟨g, hg, hgf, hπg⟩ := hs A K hK
      (fa.comp Completion.coeRingHom) hfa' gbar hgbar hcomm'
    let : DiscreteTopology (A ⧸ K) := discrete_ideal_quotient K
    refine ⟨g, hg, ?_, hπg⟩
    exact ringHom_ext_adic_completion I hI (g.comp F) fa (hg.comp hF) hfa
      (by simpa only [RingHom.comp_assoc] using hgf)
  · intro hs A _ _ _ K hK fa hfa gbar hgbar hcomm
    let : DiscreteTopology (A ⧸ K) := discrete_ideal_quotient K
    rcases @DiscreteTopology.eq_bot A _ _ with rfl
    let : UniformSpace A := ⊥
    let faext : Completion R →+* A := Completion.extensionHom fa hfa
    have hfaext : Continuous faext := continuous_extensionHom_adic I fa hfa
    have hcomm' : gbar.comp F = (Ideal.Quotient.mk K).comp faext := by
      apply ringHom_ext_adic_completion I hI
      · exact hgbar.comp hF
      · exact (continuous_of_discreteTopology :
          Continuous (Ideal.Quotient.mk K : A →+* A ⧸ K)).comp hfaext
      · rw [RingHom.comp_assoc, RingHom.comp_assoc, extensionHom_comp_coeRingHom]
        exact hcomm
    obtain ⟨g, hg, hgf, hπg⟩ := hs A K hK faext hfaext gbar hgbar hcomm'
    refine ⟨g, hg, ?_, hπg⟩
    rw [← RingHom.comp_assoc, hgf, extensionHom_comp_coeRingHom]

/-- Formal smoothness of a continuous homomorphism of adic rings is unchanged
by completing the target, or by completing both source and target.

The hypotheses are exactly those of Stacks 07ED: rings `R` and `S` with
finitely generated ideals `m` and `n`, endowed with the `m`-adic and `n`-adic
topologies, and a continuous ring homomorphism `f : R →+* S`. The completions
carry the adic topologies of the extended ideals `m R^∧` and `n S^∧`; since `m`
and `n` are finitely generated, these are the `m`-adic and `n`-adic topologies
of the completions (Stacks 05GG). -/
@[stacks 07ED,
  ega "0 19.3.6" "adic top., f.g. ideals",
  ega "0 19.9.4" "a) <=> b) <=> c)",
  ega "IV 17.5.3" "d) ⇔ d')"]
public theorem isFormallySmooth_iff_adicCompletion.{u, v, w}
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (m : Ideal R) (n : Ideal S) (hm : m.FG) (hn : n.FG) (f : R →+* S)
    (hf : @Continuous R S m.adicTopology n.adicTopology f) :
    letI : WithIdeal R := ⟨m⟩
    letI : WithIdeal S := ⟨n⟩
    let mhat : Ideal (Completion R) := m.map Completion.coeRingHom
    let nhat : Ideal (Completion S) := n.map Completion.coeRingHom
    let fhat : Completion R →+* Completion S := Completion.mapRingHom f hf
    let toShat : R →+* Completion S := Completion.coeRingHom.comp f
    letI : TopologicalSpace (Completion R) := mhat.adicTopology
    letI : IsTopologicalRing (Completion R) := mhat.nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology (Completion R) (Completion R) := mhat.isLinearTopology
    letI : TopologicalSpace (Completion S) := nhat.adicTopology
    letI : IsTopologicalRing (Completion S) := nhat.nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology (Completion S) (Completion S) := nhat.isLinearTopology
    (IsFormallySmooth.{u} f ↔ IsFormallySmooth.{u} toShat) ∧
      (IsFormallySmooth.{u} toShat ↔ IsFormallySmooth.{u} fhat) := by
  let : WithIdeal R := ⟨m⟩
  let : WithIdeal S := ⟨n⟩
  let mhat : Ideal (Completion R) := m.map Completion.coeRingHom
  let nhat : Ideal (Completion S) := n.map Completion.coeRingHom
  let fhat : Completion R →+* Completion S := Completion.mapRingHom f hf
  let toShat : R →+* Completion S := Completion.coeRingHom.comp f
  let : TopologicalSpace (Completion R) := mhat.adicTopology
  let : IsTopologicalRing (Completion R) := mhat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (Completion R) (Completion R) := mhat.isLinearTopology
  let : TopologicalSpace (Completion S) := nhat.adicTopology
  let : IsTopologicalRing (Completion S) := nhat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology (Completion S) (Completion S) := nhat.isLinearTopology
  have hto : Continuous toShat := (continuous_coeRingHom_adic n).comp hf
  have hfhat : Continuous fhat := continuous_mapRingHom_adic m n f hf
  have hfactor : fhat.comp Completion.coeRingHom = toShat :=
    RingHom.ext (Completion.mapRingHom_coe hf)
  have htarget : RingHom.FormallySmoothTop.{u} f ↔ RingHom.FormallySmoothTop.{u} toShat :=
    formallySmoothTop_target_completion_iff m n hn f hf
  have hsource : RingHom.FormallySmoothTop.{u} toShat ↔ RingHom.FormallySmoothTop.{u} fhat := by
    simpa only [hfactor] using
      (formallySmoothTop_source_completion_iff m hm fhat hfhat :
        RingHom.FormallySmoothTop.{u} (fhat.comp Completion.coeRingHom) ↔
          RingHom.FormallySmoothTop.{u} fhat)
  change (Continuous f ∧ RingHom.FormallySmoothTop.{u} f ↔
      Continuous toShat ∧ RingHom.FormallySmoothTop.{u} toShat) ∧
    (Continuous toShat ∧ RingHom.FormallySmoothTop.{u} toShat ↔
      Continuous fhat ∧ RingHom.FormallySmoothTop.{u} fhat)
  exact ⟨⟨fun h => ⟨hto, htarget.mp h.2⟩, fun h => ⟨hf, htarget.mpr h.2⟩⟩,
    ⟨fun h => ⟨hfhat, hsource.mp h.2⟩, fun h => ⟨hto, hsource.mpr h.2⟩⟩⟩

open UniformSpace


end
