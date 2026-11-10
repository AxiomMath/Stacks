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

@[expose] public section

/-!
# Uniform and algebraic adic completions

Preparation for Stacks Tag 07ED (formal smoothness and adic completion), treated in
`StacksFrontier.RingTheory.FormallySmooth.TopologicalRings.Completion`.

For a ring `R` with its `I`-adic topology, the uniform completion `UniformSpace.Completion R`
is identified with the algebraic adic completion `AdicCompletion I R`, compatibly with the
canonical maps from `R`, and the standard properties of `AdicCompletion` are transported to
the uniform model.

## Main definitions

* `AdicCompletionBridge.adicCompletionRingEquiv`: the ring isomorphism
  `Completion R ≃+* AdicCompletion I R` for an adic uniform ring.
* `AdicCompletionBridge.adicCompletionRingHomeomorph`: the same comparison as a homeomorphism.
* `uniformCompletionRingEquiv`: the canonical ring equivalence between the uniform and
  algebraic adic completions.

## Main results

* `isNoetherianRing_uniformCompletion`, `isLocalRing_uniformCompletion`,
  `isAdicComplete_uniformCompletion`, `faithfullyFlat_coeRingHom`: properties of the uniform
  adic completion obtained through the comparison.

## Implementation notes

`AdicCompletion I R` is given the uniformity of a subtype of the product of the discrete
quotients `R ⧸ I ^ n`; it is then an `AbstractCompletion` of `R`, and the comparison is the
one between two abstract completions.

## References

* Stacks Project, Tag 07ED.
-/

/-! ### Stacks Tag 07ED -/

section

@[expose] public section

universe u_bridge

open scoped Topology Uniformity

open Filter Set Function

namespace AdicCompletionBridge

variable {R : Type u_bridge} [CommRing R] (I : Ideal R)

/-! ### The key submodule identity -/

/-- For a ring `R` as a module over itself: `I^n • ⊤ = I^n`. -/
private theorem ideal_smul_top_eq_self (n : ℕ) :
    (I ^ n • (⊤ : Submodule R R) : Submodule R R) = ↑(I ^ n) := by
  rw [Ideal.smul_eq_mul, Ideal.mul_top]

/-! ### Discrete topology on quotients -/

/-- Discrete topology on `R ⧸ (I^n • ⊤)`. -/
noncomputable local instance quotientDiscreteTopology (n : ℕ) :
    TopologicalSpace (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⊥

/-- Discrete uniform space on `R ⧸ (I^n • ⊤)`. -/
noncomputable local instance quotientDiscreteUniformSpace (n : ℕ) :
    UniformSpace (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⊥

/-- The topology on `R ⧸ (I^n • ⊤)` is discrete. -/
local instance quotientDiscrete (n : ℕ) :
    DiscreteTopology (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⟨rfl⟩

/-- The uniformity on `R ⧸ (I^n • ⊤)` is discrete. -/
local instance quotientDiscreteUnif (n : ℕ) :
    DiscreteUniformity (R ⧸ (I ^ n • (⊤ : Submodule R R))) := ⟨rfl⟩

/-! ### Coordinate entourages -/

/-- `{(f,g) | f n = g n}` is a Pi-uniformity entourage (discrete factors). -/
private theorem pi_coord_mem_uniformity (n : ℕ) :
    {p : (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) ×
         (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) |
      p.1 n = p.2 n} ∈
      𝓤 (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) := by
  rw [Pi.uniformity]
  exact Filter.mem_iInf_of_mem n
    ⟨{p | p.1 = p.2}, Filter.mem_principal_self _, fun ⟨_, _⟩ h => h⟩

/-- `{(x,y) | eval n x = eval n y}` is in the subtype uniformity of AdicCompletion. -/
private theorem eval_entourage_mem [UniformSpace R] (n : ℕ) :
    {p : AdicCompletion I R × AdicCompletion I R |
      AdicCompletion.eval I R n p.1 =
        AdicCompletion.eval I R n p.2} ∈
      @uniformity (AdicCompletion I R) instUniformSpaceSubtype :=
  Filter.mem_comap.mpr ⟨{p | p.1 n = p.2 n}, pi_coord_mem_uniformity I n,
    fun ⟨_, _⟩ h => h⟩

/-- Two images of `AdicCompletion.of` agree at level `n` iff the difference lies in `I ^ n`. -/
private theorem of_val_eq_iff (a b : R) (n : ℕ) :
    (AdicCompletion.of I R a).val n = (AdicCompletion.of I R b).val n ↔
      b - a ∈ (I ^ n : Ideal R) := by
  change AdicCompletion.eval I R n (AdicCompletion.of I R a) =
    AdicCompletion.eval I R n (AdicCompletion.of I R b) ↔ _
  rw [AdicCompletion.eval_of, AdicCompletion.eval_of, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq,
    ideal_smul_top_eq_self, ← neg_sub, neg_mem_iff]

/-- Every entourage of `AdicCompletion I R` contains the pairs agreeing up to some level. -/
private theorem exists_forall_val_eq_mem_uniformity
    {E : Set (AdicCompletion I R × AdicCompletion I R)}
    (hE : E ∈ @uniformity (AdicCompletion I R) instUniformSpaceSubtype) :
    ∃ N : ℕ, ∀ x y : AdicCompletion I R, (∀ i ≤ N, x.val i = y.val i) → (x, y) ∈ E := by
  obtain ⟨W, hW, hWE⟩ := Filter.mem_comap.mp hE
  rw [Pi.uniformity, Filter.mem_iInf] at hW
  obtain ⟨S, hSfin, V_fn, hV_mem, hW_eq⟩ := hW
  refine ⟨hSfin.toFinset.sup id, fun x y hxy => hWE ?_⟩
  rw [hW_eq]
  refine Set.mem_iInter.mpr fun ⟨i, hi⟩ => ?_
  obtain ⟨D, hD, hDV⟩ := Filter.mem_comap.mp (hV_mem ⟨i, hi⟩)
  apply hDV
  change (x.val i, y.val i) ∈ D
  rw [hxy i (Finset.le_sup (f := id) (hSfin.mem_toFinset.mpr hi))]
  exact refl_mem_uniformity hD

/-! ### Topology and uniformity on AdicCompletion via subtype of product -/

section Instances

variable [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]

/-- The uniform structure on `AdicCompletion I R`: the subtype uniformity
from the product `∀ n, R ⧸ (I^n • ⊤)` with discrete factors. -/
noncomputable local instance adicCompletionUniformSpace :
    UniformSpace (AdicCompletion I R) :=
  instUniformSpaceSubtype

/-- `AdicCompletion I R` is T₀ because elements agreeing at all levels are equal. -/
local instance adicCompletionT0 : @T0Space (AdicCompletion I R)
    (adicCompletionUniformSpace I).toTopologicalSpace := by
  constructor
  intro ⟨f, hf⟩ ⟨g, hg⟩ hinsep
  ext n
  have hpi : @Inseparable _ Pi.topologicalSpace
      (⟨f, hf⟩ : AdicCompletion I R).val (⟨g, hg⟩ : AdicCompletion I R).val :=
    Inseparable.map hinsep continuous_subtype_val
  rw [@inseparable_pi] at hpi
  exact (hpi n).eq

/-- The set underlying `AdicCompletion I R` inside the product type. -/
def adicCompletionSet :
    Set (∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R))) :=
  {f | ∀ {m n : ℕ} (hmn : m ≤ n),
    (AdicCompletion.transitionMap I R hmn) (f n) = f m}

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R] in
private theorem adicCompletionSet_isClosed : IsClosed (adicCompletionSet I) := by
  unfold adicCompletionSet
  have : {g : ∀ k, R ⧸ (I ^ k • (⊤ : Submodule R R)) |
      ∀ {m n : ℕ} (hmn : m ≤ n),
        (AdicCompletion.transitionMap I R hmn) (g n) = g m} =
    ⋂ (p : ℕ × ℕ) (_ : p.1 ≤ p.2),
      {g | (AdicCompletion.transitionMap I R ‹p.1 ≤ p.2›) (g p.2) = g p.1} := by
    ext g; simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact ⟨fun h p hp => h hp, fun h m n hmn => h ⟨m, n⟩ hmn⟩
  rw [this]
  exact isClosed_iInter fun ⟨m, n⟩ => isClosed_iInter fun hmn =>
    isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply n))
      (continuous_apply m)

/-- `AdicCompletion I R` is complete: it's a closed subtype of the complete
product `∀ n, R ⧸ (I^n • ⊤)` (product of discrete = complete). -/
local instance adicCompletionComplete : @CompleteSpace (AdicCompletion I R)
    (adicCompletionUniformSpace I) :=
  (adicCompletionSet_isClosed I).completeSpace_coe
section Bridge

omit [IsTopologicalRing R] in
/-- `AdicCompletion.of I R` is uniform inducing for the I-adic uniformity
on `R` and the subtype uniformity on `AdicCompletion I R`. -/
theorem of_isUniformInducing (hadic : IsAdic I) :
    @IsUniformInducing R (AdicCompletion I R) _ (adicCompletionUniformSpace I)
      (AdicCompletion.of I R) := by
  constructor
  have hbasis_nhds : (𝓝 (0 : R)).HasBasis (fun (_ : ℕ) => True)
      (fun n => ((I ^ n : Ideal R) : Set R)) := by
    have h : @nhds R _ 0 = @nhds R I.adicTopology 0 := by rw [hadic]
    rw [h]; convert Ideal.hasBasis_nhds_adic I (0 : R) using 1
    funext n; simp [zero_add, Set.image_id']
  have hbasis_unif := hbasis_nhds.uniformity_of_nhds_zero
  have hbasis_comap : (Filter.comap (fun x =>
      ((AdicCompletion.of I R) x.1, (AdicCompletion.of I R) x.2))
      (𝓤 (AdicCompletion I R))).HasBasis (fun (_ : ℕ) => True)
      (fun n => {x : R × R | x.2 - x.1 ∈ (I ^ n : Ideal R)}) := by
    constructor; intro U; constructor
    · intro hU
      obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
      obtain ⟨N, hN⟩ := exists_forall_val_eq_mem_uniformity I hV
      exact ⟨N, trivial, fun ⟨a, b⟩ hab => hVU (hN _ _ fun i hi =>
        (of_val_eq_iff I a b i).mpr (Ideal.pow_le_pow_right hi hab))⟩
    · rintro ⟨n, -, hn⟩
      apply Filter.mem_comap.mpr
      refine ⟨{p | AdicCompletion.eval I R n p.1 =
        AdicCompletion.eval I R n p.2}, eval_entourage_mem I n, ?_⟩
      intro ⟨a, b⟩ hab
      exact hn ((of_val_eq_iff I a b n).mp hab)
  exact hbasis_unif.eq_of_same_basis hbasis_comap |>.symm

omit [IsUniformAddGroup R] [IsTopologicalRing R] in
/-- `AdicCompletion.of I R` has dense range in the subtype topology. -/
theorem of_denseRange (_hadic : IsAdic I) :
    @DenseRange (AdicCompletion I R) (adicCompletionUniformSpace I).toTopologicalSpace
      R (AdicCompletion.of I R) := by
  intro x
  choose r hr using fun n => Submodule.Quotient.mk_surjective (I ^ n • ⊤) (x.val n)
  have htendsto : Filter.Tendsto (fun n => AdicCompletion.of I R (r n))
      Filter.atTop (@nhds _ (adicCompletionUniformSpace I).toTopologicalSpace x) := by
    rw [Filter.Tendsto, Filter.map_le_iff_le_comap, Filter.le_def]
    intro U hU
    rw [Filter.mem_comap] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    rw [@nhds_eq_comap_uniformity _ (adicCompletionUniformSpace I)] at hV
    obtain ⟨E, hE, hEV⟩ := Filter.mem_comap.mp hV
    obtain ⟨N, hN⟩ := exists_forall_val_eq_mem_uniformity I hE
    refine Filter.mem_atTop_sets.mpr ⟨N, fun m hm => hVU (hEV (hN _ _ fun i hi => ?_))⟩
    have hle_m : i ≤ m := le_trans hi hm
    have heval : (AdicCompletion.of I R (r m)).val i = x.val i := by
      have h1 := (AdicCompletion.of I R (r m)).property hle_m
      have h2 := x.property hle_m
      change AdicCompletion.eval I R i (AdicCompletion.of I R (r m)) = x.val i
      rw [show AdicCompletion.eval I R i (AdicCompletion.of I R (r m)) =
        (AdicCompletion.transitionMap I R hle_m)
          (AdicCompletion.eval I R m (AdicCompletion.of I R (r m))) from h1.symm,
        AdicCompletion.eval_of]
      change (AdicCompletion.transitionMap I R hle_m) (Submodule.Quotient.mk (r m)) = x.val i
      rw [hr m, h2]
    exact heval.symm
  exact mem_closure_of_tendsto htendsto
    (Filter.Eventually.of_forall fun n => Set.mem_range.mpr ⟨r n, rfl⟩)

/-- `AdicCompletion I R` with subtype uniformity as an `AbstractCompletion`. -/
noncomputable def adicAbstractCompletion (hadic : IsAdic I) : AbstractCompletion R where
  space := AdicCompletion I R
  coe := AdicCompletion.of I R
  uniformStruct := adicCompletionUniformSpace I
  complete := adicCompletionComplete I
  separation := adicCompletionT0 I
  isUniformInducing := of_isUniformInducing I hadic
  dense := of_denseRange I hadic

/-- Forward comparison: `Completion R → AdicCompletion I R`. -/
noncomputable def adicCompletionEquiv (hadic : IsAdic I) :
    UniformSpace.Completion R → AdicCompletion I R :=
  (UniformSpace.Completion.cPkg (α := R)).compare (adicAbstractCompletion I hadic)

/-- Backward comparison: `AdicCompletion I R → Completion R`. -/
noncomputable def adicCompletionEquivInv (hadic : IsAdic I) :
    AdicCompletion I R → UniformSpace.Completion R :=
  (adicAbstractCompletion I hadic).compare (UniformSpace.Completion.cPkg (α := R))

/-- The ring isomorphism `Completion R ≃+* AdicCompletion I R`. -/
noncomputable def adicCompletionRingEquiv (hadic : IsAdic I) :
    UniformSpace.Completion R ≃+* AdicCompletion I R := by
  let e := adicCompletionEquiv I hadic
  let e_inv := adicCompletionEquivInv I hadic
  have : T2Space (AdicCompletion I R) := inferInstance
  have : CompleteSpace (AdicCompletion I R) := adicCompletionComplete I
  have : ContinuousMul (AdicCompletion I R) := ⟨by
    apply Continuous.subtype_mk; apply continuous_pi; intro n
    change Continuous fun p : AdicCompletion I R × AdicCompletion I R =>
      p.1.val n * p.2.val n
    exact ((continuous_apply n).comp (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd))⟩
  have : ContinuousAdd (AdicCompletion I R) := ⟨by
    apply Continuous.subtype_mk; apply continuous_pi; intro n
    change Continuous fun p : AdicCompletion I R × AdicCompletion I R =>
      p.1.val n + p.2.val n
    exact ((continuous_apply n).comp (continuous_subtype_val.comp continuous_fst)).add
      ((continuous_apply n).comp (continuous_subtype_val.comp continuous_snd))⟩
  have he_cont : Continuous e := @UniformSpace.Completion.continuous_extension
    R _ (AdicCompletion I R) (adicCompletionUniformSpace I)
    (f := AdicCompletion.of I R) (adicCompletionComplete I)
  have he_coe : ∀ a : R, e (↑a) = AdicCompletion.of I R a := fun a =>
    AbstractCompletion.compare_coe
      UniformSpace.Completion.cPkg (adicAbstractCompletion I hadic) a
  exact {
    toFun := e
    invFun := e_inv
    left_inv := fun x => congr_fun (AbstractCompletion.inverse_compare
      (adicAbstractCompletion I hadic) UniformSpace.Completion.cPkg) x
    right_inv := fun x => congr_fun (AbstractCompletion.inverse_compare
      UniformSpace.Completion.cPkg (adicAbstractCompletion I hadic)) x
    map_mul' := fun x y => by
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq (he_cont.comp continuous_mul)
          ((he_cont.comp continuous_fst).mul (he_cont.comp continuous_snd))
      · intro a b
        rw [← UniformSpace.Completion.coe_mul, he_coe, he_coe, he_coe]
        exact map_mul (algebraMap R (AdicCompletion I R)) a b
    map_add' := fun x y => by
      refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
      · exact isClosed_eq (he_cont.comp continuous_add)
          ((he_cont.comp continuous_fst).add (he_cont.comp continuous_snd))
      · intro a b
        rw [show (↑a : UniformSpace.Completion R) + ↑b = ↑(a + b) from
          (map_add UniformSpace.Completion.coeRingHom a b).symm,
          he_coe, he_coe, he_coe, map_add (AdicCompletion.of I R)]
  }

/-- **The comparison `Completion R ≃+* AdicCompletion I R` is uniformly continuous.**  Both the
comparison and its inverse are `AbstractCompletion.compare` maps between two abstract
completions of `R`, and those are uniformly continuous. -/
theorem uniformContinuous_adicCompletionRingEquiv (hadic : IsAdic I) :
    @UniformContinuous (UniformSpace.Completion R) (AdicCompletion I R) _
      (adicCompletionUniformSpace I) (adicCompletionRingEquiv I hadic) :=
  (UniformSpace.Completion.cPkg (α := R)).uniformContinuous_compare
    (adicAbstractCompletion I hadic)

/-- The inverse comparison `AdicCompletion I R → Completion R` is uniformly continuous. -/
theorem uniformContinuous_adicCompletionRingEquiv_symm (hadic : IsAdic I) :
    @UniformContinuous (AdicCompletion I R) (UniformSpace.Completion R)
      (adicCompletionUniformSpace I) _ (adicCompletionRingEquiv I hadic).symm :=
  (adicAbstractCompletion I hadic).uniformContinuous_compare
    (UniformSpace.Completion.cPkg (α := R))

/-- The comparison `Completion R ≃+* AdicCompletion I R` is continuous. -/
theorem continuous_adicCompletionRingEquiv (hadic : IsAdic I) :
    @Continuous (UniformSpace.Completion R) (AdicCompletion I R) _
      (adicCompletionUniformSpace I).toTopologicalSpace (adicCompletionRingEquiv I hadic) :=
  (uniformContinuous_adicCompletionRingEquiv I hadic).continuous

/-- The inverse comparison `AdicCompletion I R → Completion R` is continuous. -/
theorem continuous_adicCompletionRingEquiv_symm (hadic : IsAdic I) :
    @Continuous (AdicCompletion I R) (UniformSpace.Completion R)
      (adicCompletionUniformSpace I).toTopologicalSpace _
      (adicCompletionRingEquiv I hadic).symm :=
  (uniformContinuous_adicCompletionRingEquiv_symm I hadic).continuous

/-- **The comparison between the uniform and the algebraic adic completion is a
homeomorphism.**  This is the bundled form of `continuous_adicCompletionRingEquiv` and
`continuous_adicCompletionRingEquiv_symm`. -/
noncomputable def adicCompletionRingHomeomorph (hadic : IsAdic I) :
    @Homeomorph (UniformSpace.Completion R) (AdicCompletion I R) _
      (adicCompletionUniformSpace I).toTopologicalSpace where
  toEquiv := (adicCompletionRingEquiv I hadic).toEquiv
  continuous_toFun := continuous_adicCompletionRingEquiv I hadic
  continuous_invFun := continuous_adicCompletionRingEquiv_symm I hadic


end Bridge
end Instances
end AdicCompletionBridge

namespace AdicCompletionBridge
/-- The comparison `adicCompletionRingEquiv` sends the image of `a` in the uniform completion
to its image `AdicCompletion.of I' R' a`. -/
theorem adicCompletionRingEquiv_coe {R' : Type*} [CommRing R'] [UniformSpace R']
    [IsTopologicalRing R'] [IsUniformAddGroup R'] (I' : Ideal R') (hadic : IsAdic I')
    (a : R') :
    adicCompletionRingEquiv I' hadic (↑a) = AdicCompletion.of I' R' a :=
  AbstractCompletion.compare_coe UniformSpace.Completion.cPkg
    (adicAbstractCompletion I' hadic) a
end AdicCompletionBridge

open UniformSpace

/-- The canonical ring equivalence between the uniform and algebraic adic completions. -/
noncomputable def uniformCompletionRingEquiv {R : Type*} [CommRing R] (I : Ideal R) :
    letI : WithIdeal R := ⟨I⟩
    Completion R ≃+* AdicCompletion I R := by
  let : WithIdeal R := ⟨I⟩
  exact AdicCompletionBridge.adicCompletionRingEquiv I (by rfl)

/-- The comparison identifies the canonical maps from the original ring. -/
@[simp]
theorem uniformCompletionRingEquiv_coe {R : Type*} [CommRing R] (I : Ideal R) (r : R) :
    letI : WithIdeal R := ⟨I⟩
    uniformCompletionRingEquiv I (Completion.coeRingHom r) =
      algebraMap R (AdicCompletion I R) r := by
  let : WithIdeal R := ⟨I⟩
  exact (AdicCompletionBridge.adicCompletionRingEquiv_coe I (by rfl) r).trans
    (AdicCompletion.algebraMap_apply I r).symm

/-- Compatibility of the comparison with the canonical completion homomorphism. -/
@[simp]
theorem uniformCompletionRingEquiv_comp_coeRingHom {R : Type*} [CommRing R]
    (I : Ideal R) :
    letI : WithIdeal R := ⟨I⟩
    (uniformCompletionRingEquiv I).toRingHom.comp Completion.coeRingHom =
      algebraMap R (AdicCompletion I R) := by
  let : WithIdeal R := ⟨I⟩
  exact RingHom.ext (uniformCompletionRingEquiv_coe I)

/-- The comparison identifies the extended ideals in the two completion models. -/
theorem uniformCompletionRingEquiv_map_ideal {R : Type*} [CommRing R] (I : Ideal R) :
    letI : WithIdeal R := ⟨I⟩
    (I.map Completion.coeRingHom).map (uniformCompletionRingEquiv I) =
      I.map (algebraMap R (AdicCompletion I R)) := by
  let : WithIdeal R := ⟨I⟩
  change (I.map Completion.coeRingHom).map (uniformCompletionRingEquiv I).toRingHom = _
  rw [Ideal.map_map, uniformCompletionRingEquiv_comp_coeRingHom]

/-- A uniform adic completion of a Noetherian ring is Noetherian (Tag 0316). -/
theorem isNoetherianRing_uniformCompletion {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) :
    letI : WithIdeal R := ⟨I⟩
    IsNoetherianRing (Completion R) := by
  let : WithIdeal R := ⟨I⟩
  exact isNoetherianRing_of_ringEquiv (AdicCompletion I R)
    (uniformCompletionRingEquiv I).symm

/-- The completion at a finitely generated maximal ideal is a local ring. -/
theorem isLocalRing_uniformCompletion {R : Type*} [CommRing R] [IsLocalRing R]
    (hI : (IsLocalRing.maximalIdeal R).FG) :
    letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
    IsLocalRing (Completion R) := by
  let : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  let := AdicCompletion.isLocalRing_of_fg hI
  exact (uniformCompletionRingEquiv (IsLocalRing.maximalIdeal R)).symm.isLocalRing

/-- Completion of a local ring at its finitely generated maximal ideal is a local map. -/
theorem isLocalHom_coeRingHom {R : Type*} [CommRing R] [IsLocalRing R]
    (hI : (IsLocalRing.maximalIdeal R).FG) :
    letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
    IsLocalHom (Completion.coeRingHom : R →+* Completion R) := by
  let : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  let := AdicCompletion.isLocalRing_of_fg hI
  let := AdicCompletion.algebraMap_isLocalHom_of_fg hI
  have : IsLocalHom
      ((uniformCompletionRingEquiv (IsLocalRing.maximalIdeal R)).toRingHom.comp
        Completion.coeRingHom) := by
    rw [uniformCompletionRingEquiv_comp_coeRingHom]
    infer_instance
  exact isLocalHom_of_comp Completion.coeRingHom
    (uniformCompletionRingEquiv (IsLocalRing.maximalIdeal R)).toRingHom

/-- The maximal ideal of the completion is the extended maximal ideal. -/
theorem maximalIdeal_uniformCompletion_eq_map {R : Type*} [CommRing R] [IsLocalRing R]
    (hI : (IsLocalRing.maximalIdeal R).FG) :
    letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
    letI := isLocalRing_uniformCompletion hI
    IsLocalRing.maximalIdeal (Completion R) =
      (IsLocalRing.maximalIdeal R).map Completion.coeRingHom := by
  let : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  let := isLocalRing_uniformCompletion hI
  let := AdicCompletion.isLocalRing_of_fg hI
  let e := uniformCompletionRingEquiv (IsLocalRing.maximalIdeal R)
  have h : (IsLocalRing.maximalIdeal (Completion R)).map e =
      ((IsLocalRing.maximalIdeal R).map Completion.coeRingHom).map e := by
    rw [IsLocalRing.map_ringEquiv_maximalIdeal, uniformCompletionRingEquiv_map_ideal]
    exact AdicCompletion.maximalIdeal_eq_map_of_fg hI
  ext x
  have hx := congrArg (fun J : Ideal (AdicCompletion (IsLocalRing.maximalIdeal R) R) =>
    e x ∈ J) h
  simpa only [Ideal.apply_mem_of_equiv_iff] using Eq.to_iff hx

/-- For a finitely generated ideal the uniform completion is adically complete (Tag 05GG). -/
theorem isAdicComplete_uniformCompletion {R : Type*} [CommRing R] (I : Ideal R)
    (hI : I.FG) :
    letI : WithIdeal R := ⟨I⟩
    IsAdicComplete (I.map Completion.coeRingHom) (Completion R) := by
  let : WithIdeal R := ⟨I⟩
  apply (IsAdicComplete.congr_ringEquiv (I.map Completion.coeRingHom)
    (uniformCompletionRingEquiv I)).mp
  rw [uniformCompletionRingEquiv_map_ideal]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete hI)

/-- Completion at a finitely generated maximal ideal is complete for its own maximal ideal. -/
theorem isAdicComplete_maximalIdeal_uniformCompletion {R : Type*} [CommRing R]
    [IsLocalRing R] (hI : (IsLocalRing.maximalIdeal R).FG) :
    letI : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
    letI := isLocalRing_uniformCompletion hI
    IsAdicComplete (IsLocalRing.maximalIdeal (Completion R)) (Completion R) := by
  let : WithIdeal R := ⟨IsLocalRing.maximalIdeal R⟩
  let := isLocalRing_uniformCompletion hI
  rw [maximalIdeal_uniformCompletion_eq_map hI]
  exact isAdicComplete_uniformCompletion _ hI

/-- Uniform completion along an ideal in the Jacobson radical is faithfully flat (Tag 00MC). -/
theorem faithfullyFlat_coeRingHom {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) :
    letI : WithIdeal R := ⟨I⟩
    (Completion.coeRingHom : R →+* Completion R).FaithfullyFlat := by
  let : WithIdeal R := ⟨I⟩
  have h := RingHom.FaithfullyFlat.stableUnderComposition
    (algebraMap R (AdicCompletion I R)) (uniformCompletionRingEquiv I).symm.toRingHom
    (RingHom.faithfullyFlat_algebraMap_iff.mpr
      (AdicCompletion.faithfullyFlat_of_le_ringJacobson I hI))
    (RingHom.FaithfullyFlat.of_bijective (uniformCompletionRingEquiv I).symm.bijective)
  have he : (uniformCompletionRingEquiv I).symm.toRingHom.comp
      (algebraMap R (AdicCompletion I R)) = Completion.coeRingHom := by
    ext r
    exact (uniformCompletionRingEquiv I).injective (by simp)
  rwa [he] at h
