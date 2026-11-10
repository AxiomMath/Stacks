module

public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.AdicCompletion.Basic
public import StacksFrontier.RingTheory.AdicCompletion.KerEval
public import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Adic topologies and ideals of definition

Basic facts about adic topologies, ideals of definition and the topological nilradical which the
rig-geometry development uses throughout: an ideal defining the topology is an ideal of
definition, its elements are topologically nilpotent, and its radical is the topological
nilradical.  We also record that an adic completion along a finitely generated ideal is
weakly admissible
and that a quotient of a localization away from an element is again such a localization.
-/

@[expose] public section

namespace Rig

/-- An ideal defining the topology of a topological ring is an ideal of definition. -/
lemma isIdealOfDefinition_of_isAdic {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {I : Ideal R} (hI : IsAdic I) :
    TopologicalRing.IsIdealOfDefinition I := by
  obtain ⟨hopen, hcofinal⟩ := isAdic_iff.mp hI
  exact ⟨by simpa using hopen 1, hcofinal⟩

/-- Elements of an ideal of definition are topologically nilpotent. -/
@[ega "0 7.1.4" "(ii)"]
lemma isTopologicallyNilpotent_of_mem_isIdealOfDefinition {R : Type*} [CommRing R]
    [TopologicalSpace R] {I : Ideal R} (hI : TopologicalRing.IsIdealOfDefinition I) {x : R}
    (hx : x ∈ I) : IsTopologicallyNilpotent x := by
  change Filter.Tendsto (x ^ ·) Filter.atTop (nhds 0)
  refine Filter.tendsto_def.2 fun U hU => ?_
  obtain ⟨n, hn⟩ := hI.2 U hU
  exact Filter.eventually_atTop.2
    ⟨n, fun m hm => hn (Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow hx m))⟩

/-- An ideal of definition is contained in the topological nilradical. -/
lemma isIdealOfDefinition_le_topologicalNilradical {A : Type*} [CommRing A] [TopologicalSpace A]
    [IsLinearTopology A A] (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I) :
    I ≤ topologicalNilradical A := fun _ hx =>
  IsTopologicallyNilpotent.mem_topologicalNilradical_iff.mpr
    (isTopologicallyNilpotent_of_mem_isIdealOfDefinition hI hx)

/-- The topological nilradical is contained in the radical of an ideal of definition. -/
lemma topologicalNilradical_le_radical_of_isIdealOfDefinition {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsLinearTopology A A] (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I) : topologicalNilradical A ≤ I.radical := by
  intro x hx
  rw [IsTopologicallyNilpotent.mem_topologicalNilradical_iff] at hx
  obtain ⟨n, hn⟩ := hx.exists_pow_mem_of_mem_nhds (hI.1.mem_nhds I.zero_mem)
  exact Ideal.mem_radical_iff.mpr ⟨n, hn⟩

/-- An ideal of definition of a linearly topologized ring has the topological nilradical as its
radical. -/
@[ega "0 7.1.3" "(ii)"]
lemma radical_eq_topologicalNilradical_of_isIdealOfDefinition {A : Type*} [CommRing A]
    [TopologicalSpace A] [IsLinearTopology A A] (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I) : I.radical = topologicalNilradical A :=
  le_antisymm
    (TopologicalRing.topologicalNilradical_isRadical.radical_le_iff.mpr
      (isIdealOfDefinition_le_topologicalNilradical I hI))
    (topologicalNilradical_le_radical_of_isIdealOfDefinition I hI)

/-- An ideal defining the topology of a linearly topologized ring has the topological nilradical
as its radical. -/
lemma radical_eq_topologicalNilradical_of_isAdic {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] (K : Ideal R) (hK : IsAdic K) :
    K.radical = topologicalNilradical R :=
  radical_eq_topologicalNilradical_of_isIdealOfDefinition K (isIdealOfDefinition_of_isAdic hK)

/-- In a Noetherian linearly topologized ring whose topology is adic, the topological nilradical
is itself an ideal of definition. -/
lemma isIdealOfDefinition_topologicalNilradical_of_isAdic {R : Type*} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R] [IsNoetherianRing R]
    (I : Ideal R) (hI : IsAdic I) :
    TopologicalRing.IsIdealOfDefinition (topologicalNilradical R) := by
  have hIdef := isIdealOfDefinition_of_isAdic hI
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (topologicalNilradical_le_radical_of_isIdealOfDefinition I hIdef)
    (IsNoetherian.noetherian (topologicalNilradical R))
  refine ⟨Ideal.isOpen_of_isOpen_subideal
    (isIdealOfDefinition_le_topologicalNilradical I hIdef) hIdef.1, fun U hU => ?_⟩
  obtain ⟨m, hm⟩ := hIdef.2 U hU
  exact ⟨n * m, fun x hx => hm ((pow_mul (topologicalNilradical R) n m ▸
    Ideal.pow_right_mono hn m) hx)⟩

/-- The adic completion along a finitely generated ideal is weakly admissible for the topology
defined by the extension of that ideal. -/
lemma isWeaklyAdmissible_adicCompletion {R : Type*} [CommRing R] (I : Ideal R) (hIfg : I.FG) :
    letI C := AdicCompletion I R
    letI I_hat := I.map (algebraMap R C)
    letI : TopologicalSpace C := I_hat.adicTopology
    letI : IsTopologicalRing C := I_hat.nonarchimedean.toIsTopologicalRing
    letI : IsLinearTopology C C := I_hat.isLinearTopology
    TopologicalRing.IsWeaklyAdmissible C := by
  let C := AdicCompletion I R
  let I_hat := I.map (algebraMap R C)
  let : TopologicalSpace C := I_hat.adicTopology
  let : IsTopologicalRing C := I_hat.nonarchimedean.toIsTopologicalRing
  let : IsLinearTopology C C := I_hat.isLinearTopology
  exact TopologicalRing.isWeaklyAdmissible_of_isAdic rfl
    ((IsAdicComplete.map_algebraMap_iff I C).mpr (AdicCompletion.isAdicComplete hIfg))

/-- The quotient of a localization away from `f` by the extension of an ideal `I` is the
localization of `R ⧸ I` away from the image of `f`. -/
lemma isLocalization_away_quotient {R : Type*} [CommRing R] (I : Ideal R) (f : R) :
    letI L := Localization.Away f
    letI Iₗ := I.map (algebraMap R L)
    letI Q := L ⧸ Iₗ
    letI i : R ⧸ I →+* Q := Ideal.quotientMap Iₗ (algebraMap R L)
      (fun _ hx => Ideal.mem_map_of_mem (algebraMap R L) hx)
    letI : Algebra (R ⧸ I) Q := i.toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk I f) Q := by
  classical
  let L := Localization.Away f
  let Iₗ := I.map (algebraMap R L)
  let Q := L ⧸ Iₗ
  let i : R ⧸ I →+* Q := Ideal.quotientMap Iₗ (algebraMap R L)
    (fun _ hx => Ideal.mem_map_of_mem (algebraMap R L) hx)
  let : Algebra (R ⧸ I) Q := i.toAlgebra
  simpa only [IsLocalization.Away, ← Submonoid.map_powers] using
    (IsLocalization.of_surjective (Submonoid.powers f) L
      (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      (Ideal.Quotient.mk Iₗ) Ideal.Quotient.mk_surjective rfl
      (by rw [Ideal.mk_ker, Ideal.mk_ker]) :
        IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) (Submonoid.powers f)) Q)

/-- A ring homomorphism taking a power of `I` into `J` is continuous for the adic topologies. -/
lemma continuous_adic_of_map_le {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R)
    (J : Ideal S) (f : R →+* S) (h : I.map f ≤ J) :
    @Continuous R S I.adicTopology J.adicTopology f :=
  (_root_.RingHom.continuous_adic_iff f I J).mpr
    ⟨1, le_rfl, fun x hx => h (Ideal.mem_map_of_mem f (by simpa using hx))⟩

/-- A quotient of an `I`-adically complete Noetherian ring is adically complete for the extended
ideal. -/
lemma isAdicComplete_quotient {R : Type*} [CommRing R] [IsNoetherianRing R] (J : Ideal R)
    [IsAdicComplete J R] (b : Ideal R) :
    IsAdicComplete (J.map (Ideal.Quotient.mk b)) (R ⧸ b) :=
  (IsAdicComplete.map_algebraMap_iff (S := R ⧸ b) J (R ⧸ b)).mpr
    (isAdicComplete_of_iInf_smul_eq_bot J
      (IsHausdorff.of_le_jacobson J (R ⧸ b) (IsAdicComplete.le_jacobson_bot J)).iInf_pow_smul)

namespace RingHom

/-- An adic ring homomorphism is continuous. -/
theorem continuous_of_isAdic {A B : Type*} [CommRing A] [CommRing B] [TopologicalSpace A]
    [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B] (f : A →+* B)
    (hf : _root_.RingHom.IsAdic f) : Continuous f := by
  obtain ⟨I, hI, hIf⟩ := hf
  rw [hI, hIf]
  exact continuous_adic_of_map_le I (I.map f) f le_rfl

end RingHom

end Rig
