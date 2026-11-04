module

public import StacksFrontier.RingTheory.DiscreteValuationRing.EppSharedFactorSync.FactorSolutions

/-!
# The shared wild extension, the layer descent and the package step

The wild and carried cases over one produced orbit extension, the layer descent instantiated on
intermediate fields, and Tag 09ES's composition at the shape a layer descent's step needs.
-/

@[expose] public section

open scoped TensorProduct

namespace Stacks.EppTheorem

universe uA uB uK uL

/-! ### The wild case, mixed with the carried case, over one orbit extension -/

section SharedWild

open IsDiscreteValuationRing

variable (A : Type uA) (B : Type uB) (K : Type uK) (L : Type uL) (K₁ R : Type uK)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [HenselianLocalRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra A K₁] [Algebra B L]
    [Algebra K L] [Algebra K K₁]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [IsDiscreteValuationRing.IsExtension A B] [IsFractionRing B L]
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra A R] [Algebra.IsIntegral A R] [IsDiscreteValuationRing.IsExtension A R]
    [Algebra R K₁] [IsFractionRing R K₁] [IsScalarTower A R K₁]
    {nf : ℕ} (E : Fin nf → Type (max uL uK))
    [∀ i, Field (E i)] [∀ i, Algebra K (E i)] [∀ i, Algebra L (E i)]
    [∀ i, Algebra K₁ (E i)] [∀ i, Module.Finite L (E i)]

include A B K L K₁ R in
/-- **A mixed conjugate family over one orbit extension: wild factors solved, carried factors
checked against the same extension.**

Each factor is either *wild* — `Wild i`, carrying a prepared Artin--Schreier Laurent presentation
with a **nonempty** wild set, in one common uniformizer `pi` of `R` — or already weakly unramified
over `R`.  The choice is per factor and any mixture is allowed.  One finite `K₂ / K₁` is produced
and it discharges `FactorSolutions` for the whole family.

**Why the branch is internal, and not two theorems.**  A real family is mixed.  Solving the wild
factors over one extension and the carried factors over another, then reconciling the two, is the
amalgamation the all-factor route forbids: weak solutions do not survive arbitrary finite
enlargement of the base, and a common overfield of totally ramified extensions is not reachable
from either by the etale square along which they do ascend.  So the disjunction is resolved
**inside** the `forall i`.  `K₂` is produced once, from the wild sub-family, and the carried
factors are *checked* against that same `K₂` — never given one of their own.

**What makes the carried branch available.**  The engine returns `IsGalois K₁ K₂` and `IsTotallyRamifiedWithRespectTo R K₁ K₂`, and this
statement **exposes both**.  That is not decoration: `IsGalois` gives separability and, with
total ramification, these are exactly the inputs of
`IsDiscreteValuationRing.exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified`, the
engine of `factorSolutions_of_isWeaklyUnramified`, which is what discharges a carried factor here.
Without them in the conclusion a caller could not obtain these inputs and the carried case would
be unreachable; exposing them is what makes the mixed statement true.

**Only `K₂` is shared.**  Each wild factor keeps its own pole order, wild set, depths, maximising
position and rings.  The extension's depth and rank are selected **once from the whole prepared
family, before any per-factor proof** — not "before any factor's coefficients are read", which is
false: those parameters are computed from
the prepared data `pole`, `J` and `depth`, which are exactly the coefficients' classification.
What is true, and is what matters, is that they are fixed for the family before any individual
factor is solved, so no factor influences the extension the others get.

**The gap this does not cover, and why it cannot be patched by a second construction.**  A factor
that is genuinely ramified but has an *empty* wild set — every Laurent coefficient in
`perfectCore (kappa_{Bi i}) p` — is in neither branch.  It is Epp's constant-numerator case, and it
needs the base residue field.  It must be folded into **this same construction**, because building
a separate extension for those factors and combining is precisely the forbidden amalgamation; the
mixed shape here is what such a fold would have to extend. -/
theorem exists_sharedExtension_factorSolutions_of_prepared_wild_or_isWeaklyUnramified
    (p : ℕ) (hp : p.Prime) [CharP K₁ p]
    (Wild : Fin nf → Prop)
    (Bi Li : Fin nf → Type (max uL uK))
    [∀ i, CommRing (Bi i)] [∀ i, IsDomain (Bi i)]
    [∀ i, IsDiscreteValuationRing (Bi i)] [∀ i, Field (Li i)]
    [∀ i, Algebra R (Bi i)] [∀ i, Algebra (Bi i) (Li i)] [∀ i, Algebra R (Li i)]
    [∀ i, Algebra K₁ (Li i)] [∀ i, Algebra (Li i) (E i)]
    [∀ i, Algebra (Bi i) (E i)]
    [∀ i, IsScalarTower R (Bi i) (Li i)] [∀ i, IsScalarTower R K₁ (Li i)]
    [∀ i, IsScalarTower K₁ (Li i) (E i)] [∀ i, IsScalarTower (Bi i) (Li i) (E i)]
    [∀ i, IsDiscreteValuationRing.IsExtension R (Bi i)]
    [∀ i, IsFractionRing (Bi i) (Li i)]
    (decomp : ReducedTensorTower.Reduction (L ⊗[K] K₁) ≃ₐ[K] ∀ i, E i)
    (hleft : ∀ i (l : L), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] K₁) l)) i =
      algebraMap L (E i) l)
    (hright : ∀ i (x : K₁), decomp (Ideal.Quotient.mk _
        ((Algebra.TensorProduct.includeRight : K₁ →ₐ[K] L ⊗[K] K₁) x)) i =
      algebraMap K₁ (E i) x)
    (pi : R) (hpi : Irreducible pi)
    (hweakBi : ∀ i, IsDiscreteValuationRing.IsWeaklyUnramified R (Bi i))
    (xi : ∀ i, Li i) (zz : ∀ i, E i)
    (hz : ∀ i, Wild i → zz i ^ p - zz i = algebraMap (Li i) (E i) (xi i))
    (hgen : ∀ i, Wild i → Algebra.adjoin (Li i) {zz i} = ⊤)
    (pole : Fin nf → ℕ) (hpole : ∀ i, Wild i → 0 < pole i)
    (lift : ∀ i, IsLocalRing.ResidueField (Bi i) → Bi i)
    (hlift : ∀ i, Wild i → ∀ x, IsLocalRing.residue (Bi i) (lift i x) = x)
    (liftMod : ∀ i, IsLocalRing.ResidueField (Bi i) →+*
      Bi i ⧸ (IsLocalRing.maximalIdeal (Bi i)) ^ (pole i))
    (hliftMod : ∀ i, Wild i → ∀ x,
      Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (Bi i)) ^ (pole i)) (lift i x) = liftMod i x)
    (coeff : ∀ i, ℕ → IsLocalRing.ResidueField (Bi i)) (bb : ∀ i, Bi i)
    (hexp : ∀ i, Wild i → xi i = (∑ k ∈ Finset.range (pole i),
        algebraMap (Bi i) (Li i) (lift i (coeff i k)) *
          (algebraMap (Bi i) (Li i) (algebraMap R (Bi i) pi))⁻¹ ^ (pole i - k)) +
      algebraMap (Bi i) (Li i) (bb i))
    (J : Fin nf → Finset ℕ) (hJ : ∀ i, Wild i → (J i).Nonempty)
    (hJn : ∀ i, Wild i → ∀ k ∈ J i, k < pole i)
    (depth : Fin nf → ℕ → ℕ)
    (wildRoot : ∀ i, ℕ → IsLocalRing.ResidueField (Bi i))
    (hwildPow : ∀ i, Wild i → ∀ k ∈ J i, wildRoot i k ^ (p ^ depth i k) = coeff i k)
    (hwildTerminal : ∀ i, Wild i → ∀ k ∈ J i,
      ¬∃ y : IsLocalRing.ResidueField (Bi i), wildRoot i k = y ^ p)
    (htame : ∀ i, Wild i → ∀ k ∈ Finset.range (pole i), k ∉ J i →
      ∀ m : ℕ, ∃ y : IsLocalRing.ResidueField (Bi i), y ^ (p ^ m) = coeff i k)
    (hsep : ∀ i, Wild i → ∀ k ∈ J i, ∀ k' ∈ J i, k ≠ k' →
      ∀ r : ℕ, pole i - k' ≠ (pole i - k) * p ^ r) :
    letI : ∀ i, Algebra B (E i) := fun i =>
      ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
    letI : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra A (E i) := fun i =>
      ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
    letI : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, Algebra R (E i) := fun i =>
      ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
    letI : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
    letI : ∀ i, FaithfulSMul R (E i) := fun i =>
      (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
        ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
    letI : ∀ i, IsScalarTower A R (E i) := fun i =>
      IsScalarTower.of_algebraMap_eq fun a =>
        (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
          (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
    letI : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
      isDiscreteValuationRing_integralClosure_factor B L (E i)
    letI : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
      algebraIntegralClosureBase A B R (E i)
    letI : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
      isExtension_base_integralClosure_factor A B R L (E i)
    (instAlg : ∀ i, Algebra (Bi i) (integralClosure B (E i))) →
    letI := instAlg
    (∀ i, IsDiscreteValuationRing.IsExtension (Bi i) (integralClosure B (E i))) →
    (∀ i, IsScalarTower R (Bi i) (integralClosure B (E i))) →
    (∀ i, IsScalarTower (Bi i) (integralClosure B (E i)) (E i)) →
    (∀ i, Wild i ∨ IsDiscreteValuationRing.IsWeaklyUnramified R (integralClosure B (E i))) →
    ∃ (K₂ : Type uK) (_ : Field K₂) (_ : Algebra K₁ K₂) (_ : Algebra R K₂)
      (_ : IsScalarTower R K₁ K₂) (_ : Module.Finite K₁ K₂) (_ : IsGalois K₁ K₂),
      IsDiscreteValuationRing.IsTotallyRamifiedWithRespectTo R K₁ K₂ ∧
        FactorSolutions A B K L K₁ K₂ R E decomp hleft hright := by
  let : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, IsScalarTower B L (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  let : ∀ i, IsScalarTower A B (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, Algebra R (E i) := fun i =>
    ((algebraMap K₁ (E i)).comp (algebraMap R K₁)).toAlgebra
  let : ∀ i, IsScalarTower R K₁ (E i) := fun _ => IsScalarTower.of_algebraMap_eq' rfl
  let : ∀ i, FaithfulSMul R (E i) := fun i =>
    (faithfulSMul_iff_algebraMap_injective R (E i)).mpr
      ((algebraMap K₁ (E i)).injective.comp (IsFractionRing.injective R K₁))
  let : ∀ i, IsScalarTower A R (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a =>
      (algebraMap_reducedFactor_base_eq_of_tower A B K L K₁ E decomp hleft hright i a).trans
        (congrArg (algebraMap K₁ (E i)) (IsScalarTower.algebraMap_apply A R K₁ a))
  let : ∀ i, IsDiscreteValuationRing (integralClosure B (E i)) := fun i =>
    isDiscreteValuationRing_integralClosure_factor B L (E i)
  let : ∀ i, Algebra R (integralClosure B (E i)) := fun i =>
    algebraIntegralClosureBase A B R (E i)
  let : ∀ i, IsDiscreteValuationRing.IsExtension R (integralClosure B (E i)) := fun i =>
    isExtension_base_integralClosure_factor A B R L (E i)
  let : ∀ i, IsFractionRing (integralClosure B (E i)) (E i) := fun i =>
    isFractionRing_integralClosure_factor B L (E i)
  let : ∀ i, IsScalarTower R (integralClosure B (E i)) (E i) := fun i =>
    isScalarTower_base_integralClosure_factor A B R (E i)
  intro instAlg instExt instTowerL instTowerU hcase
  let : ∀ i, Algebra (Bi i) (integralClosure B (E i)) := instAlg
  let : ∀ i, IsDiscreteValuationRing.IsExtension (Bi i) (integralClosure B (E i)) := instExt
  let : ∀ i, IsScalarTower R (Bi i) (integralClosure B (E i)) := instTowerL
  let : ∀ i, IsScalarTower (Bi i) (integralClosure B (E i)) (E i) := instTowerU
  obtain ⟨ K₂, hK₂field, hK₂alg, hK₂algR, hK₂tower, hK₂fin, hK₂gal, htot, rank, hdeg, hsol ⟩ :=
    exists_shared_orbitExtension_forall_isWeakSolution_of_prepared_wild_laurent
      R K₁ (fun i : {i : Fin nf // Wild i} => Bi i.1)
      (fun i : {i : Fin nf // Wild i} => integralClosure B (E i.1))
      (fun i : {i : Fin nf // Wild i} => Li i.1) (fun i : {i : Fin nf // Wild i} => E i.1)
      p hp (fun i => hweakBi i.1) pi hpi (fun i => xi i.1) (fun i => zz i.1)
      (fun i => hz i.1 i.2) (fun i => hgen i.1 i.2)
      (fun i => pole i.1) (fun i => hpole i.1 i.2)
      (fun i => lift i.1) (fun i => hlift i.1 i.2)
      (fun i => liftMod i.1) (fun i => hliftMod i.1 i.2)
      (fun i => coeff i.1) (fun i => bb i.1) (fun i => hexp i.1 i.2)
      (fun i => J i.1) (fun i => hJ i.1 i.2) (fun i => hJn i.1 i.2)
      (fun i => depth i.1) (fun i => wildRoot i.1)
      (fun i => hwildPow i.1 i.2) (fun i => hwildTerminal i.1 i.2)
      (fun i => htame i.1 i.2) (fun i => hsep i.1 i.2)
  let := hK₂field
  let := hK₂alg
  let := hK₂algR
  let := hK₂tower
  let := hK₂fin
  let := hK₂gal
  refine ⟨ K₂, hK₂field, hK₂alg, hK₂algR, hK₂tower, hK₂fin, hK₂gal, htot, fun i => ?_ ⟩
  rcases hcase i with hw | hu
  · exact hsol ⟨ i, hw ⟩
  · exact IsDiscreteValuationRing.exists_isWeakSolution_of_isWeaklyUnramified_of_totallyRamified
      R (integralClosure B (E i)) K₁ (E i) K₂ hu htot

end SharedWild

universe u

/-! ### The layer descent, instantiated on intermediate fields

`solves_of_prescribed` in `EppKuhlmannCompleteCase.lean` is a skeleton: `mu`, `R`, `deg` and
`Terminal` are opaque, and its `hsplit` is a hypothesis.  This section instantiates it at the
ring-theoretic level, which means choosing those four and **proving** `hsplit` from the field
theory rather than assuming it.

The choice is `mu := IntermediateField K L`, `deg E := Module.finrank E L`, and
`Terminal E := Module.finrank E L ≤ 1`.

The one design point worth recording is what happened to `R`.  The abstract lemma has resources
ranging over a type `R`, and the ring-theoretic resource is a field extension `K₂ / K₁` — a type
together with instances, which is not an element of a type, so a literal instantiation would need
an ambient field and `IntermediateField` resources.  None of that is necessary, because the
resource is **prescribed**: it is fixed before the descent starts, so it can live in the ambient
context and be baked into `Solves`, and `R` collapses to a single point.  That is not a trick to
avoid the difficulty; it is what "prescribed" means, stated formally.  A version with `R` a genuine
type of resources would be strictly weaker to use, because a caller would have to produce resources
as *elements*, which is exactly the choice the route forbids.

So `Solves : IntermediateField K L → Prop` is an arbitrary predicate here, and the consumer
instantiates it as "this layer has a weak solution over the prescribed `K₂`".  Its two obligations
are then the ones the route already names: `hterminal`, discharged by the shared degree-`p` family
solver, and `hstep`, discharged by Tag 09ES
(`IsDiscreteValuationRing.weakSolutions_and_solutions_go_down_and_compose`).

Note what is *not* assumed: there is no hypothesis combining two resources.  `hstep` reduces a
layer to one shorter layer against the same ambient `K₂`, so the amalgamation never arises — the
same reason the abstract version needs no `hmerge`. -/

section LayerDescent

/-- Strong induction on `finrank E L`: if every non-terminal `P`-layer has a strictly smaller
`P`-layer whose solution gives its own, then `Solves` holds on all `P`-layers. -/
private theorem solves_of_finrank_descent
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (Solves P : IntermediateField K L → Prop)
    (hterminal : ∀ E : IntermediateField K L, Module.finrank E L ≤ 1 → Solves E)
    (hP : ∀ E : IntermediateField K L, P E → 1 < Module.finrank E L →
      ∃ F : IntermediateField K L, P F ∧ Module.finrank F L < Module.finrank E L ∧
        (Solves F → Solves E))
    (E : IntermediateField K L) (hE : P E) : Solves E := by
  suffices ∀ k, ∀ E : IntermediateField K L, P E → Module.finrank E L = k → Solves E from
    this _ E hE rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro E hE hk
    by_cases h1 : k ≤ 1
    · exact hterminal E (hk ▸ h1)
    obtain ⟨F, hF, hlt, hsolve⟩ := hP E hE (by omega)
    exact hsolve (ih _ (hk ▸ hlt) F hF rfl)

/-- **The layer descent on intermediate fields, Galois case.**

Any property of intermediate fields that holds on the terminal layers and descends along
prime-degree cyclic steps holds on every layer, for a finite solvable Galois `L / K`.

`hstep` receives more than the bare step: the prime degree, the cyclicity of the step's Galois
group, and the strict decrease.  All three are free —
`exists_intermediateField_prime_finrank_of_isSolvable` returns them — and the degree-`p` solver
downstream wants the first two.

The Galois and solvability hypotheses are threaded through the induction rather than assumed for
every intermediate field, because the splitting lemma re-supplies them for the layer it produces.
So they are required only of the layer the descent starts at. -/
theorem solves_intermediateField_of_prescribed
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (Solves : IntermediateField K L → Prop)
    (hterminal : ∀ E : IntermediateField K L, Module.finrank E L ≤ 1 → Solves E)
    (hstep : ∀ (E : IntermediateField K L) (F : IntermediateField E L),
      (Module.finrank E F).Prime → IsCyclic (F ≃ₐ[E] F) →
      Module.finrank (F.restrictScalars K) L < Module.finrank E L →
      Solves (F.restrictScalars K) → Solves E)
    (E : IntermediateField K L) (hgal : IsGalois E L)
    (hsolv : Group.IsSolvable (L ≃ₐ[E] L)) : Solves E := by
  refine solves_of_finrank_descent Solves (fun E => IsGalois E L ∧ Group.IsSolvable (L ≃ₐ[E] L))
    hterminal (fun E ⟨_, _⟩ hlt => ?_) E ⟨hgal, hsolv⟩
  obtain ⟨F, -, hprime, hcyc, hdec, hFgal, hFsolv⟩ :=
    IsDiscreteValuationRing.exists_intermediateField_prime_finrank_of_isSolvable E L hlt
  exact ⟨F.restrictScalars K, ⟨hFgal, hFsolv⟩, hdec, hstep E F hprime hcyc hdec⟩

/-- **The family form: one prescribed resource serves every member.**

This is the conclusion shape the all-factor route consumes.  The existential over resources is not
here at all — it belongs to whatever constructs the resource, and `Solves` already speaks about
that one resource, which is the whole point of the prescribed formulation. -/
theorem forall_solves_intermediateField_of_prescribed
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (Solves : IntermediateField K L → Prop)
    (hterminal : ∀ E : IntermediateField K L, Module.finrank E L ≤ 1 → Solves E)
    (hstep : ∀ (E : IntermediateField K L) (F : IntermediateField E L),
      (Module.finrank E F).Prime → IsCyclic (F ≃ₐ[E] F) →
      Module.finrank (F.restrictScalars K) L < Module.finrank E L →
      Solves (F.restrictScalars K) → Solves E)
    {ι : Sort*} (f : ι → IntermediateField K L)
    (hgal : ∀ i, IsGalois (f i) L)
    (hsolv : ∀ i, Group.IsSolvable (L ≃ₐ[f i] L)) : ∀ i, Solves (f i) :=
  fun i => solves_intermediateField_of_prescribed Solves hterminal hstep (f i) (hgal i) (hsolv i)

/-- **The layer descent on intermediate fields, purely inseparable case.**

The companion to `solves_intermediateField_of_prescribed`.  A layer induction has to handle both
kinds of step, and in the purely inseparable case the splitting datum is an element rather than a
subgroup: `exists_intermediateField_finrank_eq_of_isPurelyInseparable` produces a `y` whose `p`-th
power is already in the base, so the layer it cuts out is the degree-`p` radical extension the
prime-degree solver expects, and `hstep` receives that `y` together with `y ^ p ∈ range`.

`1 < p` is a hypothesis rather than derived from `ExpChar`, because `ExpChar K 1` is the
characteristic-zero case, where a purely inseparable extension is trivial and the descent is
vacuous — the terminal branch already covers it.  A caller in residue characteristic `p > 0` has
`1 < p` immediately. -/
theorem solves_intermediateField_of_prescribed_isPurelyInseparable
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : ℕ) (hp : 1 < p)
    (Solves : IntermediateField K L → Prop)
    (hterminal : ∀ E : IntermediateField K L, Module.finrank E L ≤ 1 → Solves E)
    (hstep : ∀ (E : IntermediateField K L) (y : L), y ^ p ∈ (algebraMap E L).range →
      Module.finrank E (IntermediateField.adjoin E {y}) = p →
      Module.finrank ((IntermediateField.adjoin E {y}).restrictScalars K) L <
        Module.finrank E L →
      Solves ((IntermediateField.adjoin E {y}).restrictScalars K) → Solves E)
    (E : IntermediateField K L) (hpi : IsPurelyInseparable E L)
    (hexp : ExpChar E p) : Solves E := by
  refine solves_of_finrank_descent Solves (fun E => IsPurelyInseparable E L ∧ ExpChar E p)
    hterminal (fun E ⟨_, _⟩ hlt => ?_) E ⟨hpi, hexp⟩
  have hbot : (⊥ : IntermediateField E L) ≠ ⊤ := by
    intro h
    rw [IntermediateField.bot_eq_top_iff_finrank_eq_one] at h
    omega
  obtain ⟨y, hyp, hydeg⟩ :=
    IsDiscreteValuationRing.exists_intermediateField_finrank_eq_of_isPurelyInseparable
      E L p hbot
  set F := IntermediateField.adjoin E {y} with hF
  have hmul : Module.finrank E F * Module.finrank F L = Module.finrank E L :=
    Module.finrank_mul_finrank E F L
  have hdec : Module.finrank F L < Module.finrank E L := by
    rw [← hmul, hydeg]
    exact (Nat.lt_mul_iff_one_lt_left Module.finrank_pos).mpr hp
  exact ⟨F.restrictScalars K, ⟨IsPurelyInseparable.tower_top E F L,
    expChar_of_injective_algebraMap (algebraMap E F).injective p⟩, hdec,
    hstep E y hyp hydeg hdec⟩

end LayerDescent

/-! ### Tag 09ES's composition at the shape a layer descent's step needs -/

section PackageStep

open IsDiscreteValuationRing

universe uC uM uK₁ uE uL₁ uA₁ uB₁ uM₁ uA₂ uC₁ uN₁ uB₂ uC₂

/-- **The conjugate-factor family, with every carrier collapsed to one universe.**

`IsDiscreteValuationRing.finiteFieldFactors_compatible` produces the factor family of a package in
`Type (max uL uD₁)`, where `uD₁` is the package's `L₁` universe.  That is the concrete form of the
carrier problem: a descent step built from it lands its output in a universe larger than its
input's, so an induction whose members must all inhabit one universe cannot iterate it.

Collapsing every carrier of the package to a single `u` fixes this, because `max u u` normalises to
`u`: the factors then live in `Type u` alongside the input, and the step is universe-closed. That
is the whole content of "reconciling the eight carriers", and the reason it is *available* is that
the package's own construction puts `L₁`, `A₁` and `B₁` in `max` of the input universes, so
demanding `.{u,u,u,u,u,u,u,u}` is satisfiable rather than a restriction imposed from outside.

This wrapper is therefore thin on purpose — it fixes universes and changes nothing else. Its value
is that `forall_solves_of_family_descent`, which quantifies over index types in one fixed `Type u`,
can consume it. -/
theorem exists_finiteFieldFactors_of_package
    (A B K L K₁ : Type u)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁]
    (D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L K₁) :
    letI := D.commRingL₁
    letI := D.algebraLL₁
    letI := D.algebraK₁L₁
    ∃ (n : ℕ) (E : Fin n → Type u)
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra L (E i))
      (_ : ∀ i, Algebra K₁ (E i)) (_ : ∀ i, Algebra B (E i))
      (_ : ∀ i, Algebra A (E i))
      (_ : ∀ i, IsScalarTower B L (E i))
      (_ : ∀ i, IsScalarTower A B (E i))
      (_ : ∀ i, IsScalarTower A K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i)),
      0 < n ∧ ∃ e : D.L₁ ≃ₐ[L] ∀ i, E i,
        ∀ (i : Fin n) (x : K₁), e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x :=
  IsDiscreteValuationRing.finiteFieldFactors_compatible A B K L K₁ D

/-- The field factors of a separable base change are finite and separable, with all compatibility
structures retained. -/
theorem exists_finiteSeparableFieldFactors_of_package
    (A B K L K₁ : Type u)
    [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B]
    [Field K] [Field L] [Field K₁]
    [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L]
    [Algebra K L] [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsFractionRing A K] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L] [IsScalarTower A K K₁]
    [Module.Finite K K₁] [Algebra.IsSeparable K K₁]
    (D : IntegralClosureBaseChange.{u, u, u, u, u, u, u, u} A B K L K₁) :
    letI := D.commRingL₁
    letI := D.algebraLL₁
    letI := D.algebraK₁L₁
    ∃ (n : ℕ) (E : Fin n → Type u)
      (_ : ∀ i, Field (E i)) (_ : ∀ i, Algebra L (E i))
      (_ : ∀ i, Algebra K₁ (E i)) (_ : ∀ i, Algebra B (E i))
      (_ : ∀ i, Algebra A (E i))
      (_ : ∀ i, IsScalarTower B L (E i))
      (_ : ∀ i, IsScalarTower A B (E i))
      (_ : ∀ i, IsScalarTower A K₁ (E i))
      (_ : ∀ i, Module.Finite L (E i))
      (_ : ∀ i, Algebra.IsSeparable L (E i)),
      0 < n ∧ ∃ e : D.L₁ ≃ₐ[L] ∀ i, E i,
        ∀ (i : Fin n) (x : K₁), e (algebraMap K₁ D.L₁ x) i = algebraMap K₁ (E i) x := by
  let := D.commRingL₁
  let := D.commRingA₁
  let := D.commRingB₁
  let := D.algebraKL₁
  let := D.algebraLL₁
  let := D.algebraK₁L₁
  let := D.algebraBL₁
  let := D.algebraAA₁
  let := D.algebraA₁K₁
  let := D.algebraBB₁
  let := D.algebraB₁L₁
  let := D.algebraAB₁
  let := D.algebraA₁B₁
  let := D.isScalarTowerKLL₁
  let := D.isScalarTowerKK₁L₁
  let := D.isScalarTowerBLL₁
  let := D.isScalarTowerAA₁K₁
  let := D.isScalarTowerBB₁L₁
  let := D.isScalarTowerABB₁
  let := D.isScalarTowerAA₁B₁
  let := D.isIntegralClosureA₁
  let := D.isIntegralClosureB₁
  let eA := IsIntegralClosure.equiv A D.A₁ K₁ (integralClosure A K₁)
  let eB := IsIntegralClosure.equiv B D.B₁ D.L₁ (integralClosure B D.L₁)
  have hall := integralClosures_after_finite_fraction_field_extension
    A B K L K₁ D.L₁ D.A₁ D.B₁ D.eL₁ eA eB D.eL₁_left D.eL₁_right
    (fun x => IsIntegralClosure.algebraMap_equiv B D.B₁ D.L₁
      (integralClosure B D.L₁) x)
    (fun x => by
      rw [← IsScalarTower.algebraMap_apply K L D.L₁,
        ← IsScalarTower.algebraMap_apply K K₁ D.L₁])
    (fun x => by
      rw [show (eA x : K₁) = algebraMap D.A₁ K₁ x from
        IsIntegralClosure.algebraMap_equiv A D.A₁ K₁ (integralClosure A K₁) x]
      exact D.ringSquare x)
  rcases hall with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsep, _, _⟩
  obtain ⟨n, E, hE, hLE, hfin, hsepE, hn, ⟨e⟩⟩ := (hsep inferInstance).2.1
  let := hE
  let := hLE
  let : ∀ i, Algebra K₁ (E i) := fun i =>
    (((Pi.evalAlgHom L E i).toRingHom.comp e.toRingHom).comp
      (algebraMap K₁ D.L₁)).toAlgebra
  let : ∀ i, Algebra B (E i) := fun i =>
    ((algebraMap L (E i)).comp (algebraMap B L)).toAlgebra
  let : ∀ i, Algebra A (E i) := fun i =>
    ((algebraMap B (E i)).comp (algebraMap A B)).toAlgebra
  let hBLE : ∀ i, IsScalarTower B L (E i) := fun _ =>
    IsScalarTower.of_algebraMap_eq' rfl
  let hABE : ∀ i, IsScalarTower A B (E i) := fun _ =>
    IsScalarTower.of_algebraMap_eq' rfl
  let hAK₁E : ∀ i, IsScalarTower A K₁ (E i) := fun i =>
    IsScalarTower.of_algebraMap_eq fun a => by
      show algebraMap L (E i) (algebraMap B L (algebraMap A B a)) =
        e (algebraMap K₁ D.L₁ (algebraMap A K₁ a)) i
      rw [← IsScalarTower.algebraMap_apply A B L]
      have hs : algebraMap K₁ D.L₁ (algebraMap A K₁ a) =
          algebraMap L D.L₁ (algebraMap A L a) := by
        rw [IsScalarTower.algebraMap_apply A K K₁,
          IsScalarTower.algebraMap_apply A K L,
          ← IsScalarTower.algebraMap_apply K K₁ D.L₁,
          ← IsScalarTower.algebraMap_apply K L D.L₁]
      rw [hs, e.commutes]
      rfl
  exact ⟨n, E, hE, hLE, inferInstance, inferInstance, inferInstance,
    hBLE, hABE, hAK₁E, hfin, hsepE, hn, e, fun _ _ => rfl⟩

/-- **The package-level step: a solved lower layer plus a solved upper layer over every factor give
a solved whole, all over the one prescribed base change.**

This is the weak-solution half of Tag 09ES's composition
(`IsDiscreteValuationRing.weakSolutions_and_solutions_go_down_and_compose`) extracted as a direct
implication, which is the form a layer descent's step can actually consume: inside 09ES it sits as
one component of a conjunction nested under a universally quantified factor family, and a caller
holding exactly the two solutions cannot apply it without reconstructing that whole shape.

There is no new mathematics here and none is claimed — this is a projection. Its value is
applicability.

Two things the statement records that are easy to get wrong.

The factors appear **only in the hypotheses**. Each `DBC i` is a weak solution for the upper layer
base-changed by the factor `E i`, not by `K₁`, while the conclusion is about `DAC`, base-changed by
`K₁`. So per-factor solutions are never transported to the shared base: the composition consumes
them where they live. That is the re-entry architecture, and a statement that tried to move them to
`K₁` first would be asking for a map that does not generally exist.

The two `letI`s are load-bearing and their position is forced. `DAB.L₁` has no `CommRing` or
`Algebra L` instance until `DAB.commRingL₁` and `DAB.algebraLL₁` are introduced, and the factor
equivalence `e` mentions both; since `e` is a hypothesis, the instances must precede it in the
telescope, which is why `e`, `DBC` and the two solution hypotheses are stated after them in the
conclusion rather than as ordinary arguments.

Universes are left polymorphic in all seventeen. That costs nothing because this step constructs no
package — universe reconciliation is a problem for building an `IntegralClosureBaseChange`, not for
stating a `Prop` about ones handed in. -/
theorem isWeakSolution_of_prime_layer_of_forall_factor
    (A : Type uA) (B : Type uB) (C : Type uC)
    (K : Type uK) (L : Type uL) (M : Type uM) (K₁ : Type uK₁)
    [CommRing A] [CommRing B] [CommRing C]
    [IsDomain A] [IsDomain B] [IsDomain C]
    [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [IsDiscreteValuationRing C]
    [Field K] [Field L] [Field M] [Field K₁]
    [Algebra A B] [Algebra B C] [Algebra A C]
    [Algebra A K] [Algebra A L] [Algebra A M]
    [Algebra B L] [Algebra B M] [Algebra C M]
    [Algebra K L] [Algebra K M] [Algebra L M]
    [Algebra K K₁] [Algebra A K₁]
    [IsExtension A B] [IsExtension B C] [IsExtension A C]
    [IsFractionRing A K] [IsFractionRing B L] [IsFractionRing C M]
    [IsScalarTower A B C] [IsScalarTower A B L] [IsScalarTower A B M]
    [IsScalarTower B C M] [IsScalarTower A C M]
    [IsScalarTower A K L] [IsScalarTower A K M] [IsScalarTower K L M]
    [IsScalarTower B L M] [IsScalarTower A K K₁] [Module.Finite K K₁]
    (DAB : IntegralClosureBaseChange.{uA, uB, uK, uL, uK₁, uL₁, uA₁, uB₁} A B K L K₁)
    (DAC : IntegralClosureBaseChange.{uA, uC, uK, uM, uK₁, uM₁, uA₂, uC₁} A C K M K₁)
    (n : ℕ) (E : Fin n → Type uE)
    [∀ i, Field (E i)] [∀ i, Algebra L (E i)] [∀ i, Algebra B (E i)]
    [∀ i, IsScalarTower B L (E i)] [∀ i, Module.Finite L (E i)]
    (hn : 0 < n) :
    letI := DAB.commRingL₁
    letI := DAB.algebraLL₁
    ∀ (_e : DAB.L₁ ≃ₐ[L] ∀ i, E i)
      (DBC : ∀ i, IntegralClosureBaseChange.{uB, uC, uL, uM, uE, uN₁, uB₂, uC₂} B C L M (E i)),
      DAB.IsWeakSolution → (∀ i, (DBC i).IsWeakSolution) → DAC.IsWeakSolution := by
  let := DAB.commRingL₁
  let := DAB.algebraLL₁
  intro e DBC hAB hBC
  exact ((IsDiscreteValuationRing.weakSolutions_and_solutions_go_down_and_compose
    A B C K L M K₁ DAB DAC).2 n E hn ⟨e⟩ DBC).1 ⟨hAB, hBC⟩

end PackageStep

end Stacks.EppTheorem

end
