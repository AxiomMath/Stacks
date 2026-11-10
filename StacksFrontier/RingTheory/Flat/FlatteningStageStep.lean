module

public import StacksFrontier.RingTheory.Flat.FlatteningStageTransfer
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.RingTheory.Flat.FlatteningBridge
public import StacksFrontier.RingTheory.Flat.FlatteningClosedFibre
public import StacksFrontier.RingTheory.Flat.DevissageProjectiveStages
public import Mathlib.LinearAlgebra.Isomorphisms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The induction step of the local flattening theorem

The proof of Stacks Tag 05PG runs along a complete dévissage of the module, one stage at a time,
from the last stage down. At a stage the data are a flat and projective `A`-algebra `B` with
geometrically integral fibres, a prime `Q` of `B` over the closed point of the local ring `A`, a
finite `B`-module `M` and a map `α : B^(⊕ r) → M` which is an isomorphism over the generic point
of the closed fibre; the induction hypothesis is that the flatness condition at `Q` for the
cokernel of `α` is corepresented by an ideal `J ⊆ A`. This file proves that the condition for
`M` is then corepresented as well (`Module.exists_ideal_isFlatAtPrimesAbove_iff_of_cokernel`).

The argument is the source's. Over a local `A`-algebra `R`, Stacks Tag 05I3 applied to
`B ⊗_A R` shows that flatness of `M` at a prime over the closed point gives flatness of the
cokernel there and injectivity of `α ⊗ R` (`Module.flat_cokernel_and_injective_of_flat`); so the
condition for `M` forces the condition for the cokernel, hence the vanishing of `J`. Given the
vanishing of `J`, the condition is equivalent to injectivity of `α ⊗ R`, which is cut out by an
ideal: the source invokes Stacks Tag 05PF for the image of `α`; here the ideal is written down
directly as `J` together with the coordinates, in a splitting of the projective `A`-module
`B^(⊕ r)`, of the elements whose image lies in `J M`. That this ideal suffices is a Tor argument
(`Module.mem_smul_top_of_flat_quotient_cokernel`): modulo `J` the cokernel is flat at `Q`, so the
image of `B^(⊕ r)` meets `I M` in `I`-multiples.

## Main results

* `Module.flat_cokernel_and_injective_of_flat`: Stacks Tag 05I3 over a local `A`-algebra.
* `Module.mem_smul_top_of_flat_quotient_cokernel`: the Tor argument.
* `Module.exists_ideal_isFlatAtPrimesAbove_iff_of_cokernel`: the induction step.

## References

* [Stacks Project, Tag 05I3](https://stacks.math.columbia.edu/tag/05I3)
* [Stacks Project, Tag 05PF](https://stacks.math.columbia.edu/tag/05PF)
* [Stacks Project, Tag 05PG](https://stacks.math.columbia.edu/tag/05PG)
-/

@[expose] public section

open IsLocalRing

open scoped TensorProduct

universe u v w x y

namespace Module

/-- **A submodule with flat cokernel meets `𝔞 X` in `𝔞 Y`.** Let `0 → Y → X → Z → 0` be exact with
`Z` flat over `T`. If the image of `y ∈ Y` lies in `𝔞 X` for an ideal `𝔞` of `T`, then `y ∈ 𝔞 Y`:
the sequence stays exact on the left after tensoring with `T ⧸ 𝔞`. -/
theorem mem_smul_top_of_flat_cokernel {T : Type u} [CommRing T] (𝔞 : Ideal T) {Y X Z : Type*}
    [AddCommGroup Y] [AddCommGroup X] [AddCommGroup Z] [Module T Y] [Module T X] [Module T Z]
    [Module.Flat T Z] (i : Y →ₗ[T] X) (π : X →ₗ[T] Z) (hi : Function.Injective i)
    (hπ : Function.Surjective π) (hex : Function.Exact i π) (y : Y)
    (hy : i y ∈ 𝔞 • (⊤ : Submodule T X)) : y ∈ 𝔞 • (⊤ : Submodule T Y) := by
  have hinj := LinearMap.lTensor_injective_of_exact_of_flat π hπ i hi hex (T ⧸ 𝔞)
  have h0 : i.lTensor (T ⧸ 𝔞) ((1 : T ⧸ 𝔞) ⊗ₜ[T] y) = 0 := by
    rw [LinearMap.lTensor_tmul]
    apply (TensorProduct.quotTensorEquivQuotSMul X 𝔞).injective
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hy
  have h1 : (1 : T ⧸ 𝔞) ⊗ₜ[T] y = 0 := hinj (h0.trans (map_zero _).symm)
  have h2 := congrArg (TensorProduct.quotTensorEquivQuotSMul Y 𝔞) h1
  rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, map_zero] at h2
  exact (Submodule.Quotient.mk_eq_zero _).mp h2

/-- Reducing a right exact sequence modulo `K` keeps it exact: if `α` and `π` are exact with `π`
surjective then so are the induced maps `P ⧸ K P → M ⧸ K M → C ⧸ K C`. -/
theorem exact_mapQ_smul_top {A : Type u} [CommRing A] (K : Ideal A) {P M C : Type*}
    [AddCommGroup P] [AddCommGroup M] [AddCommGroup C] [Module A P] [Module A M] [Module A C]
    (α : P →ₗ[A] M) (π : M →ₗ[A] C) (hπ : Function.Surjective π) (hex : Function.Exact α π) :
    Function.Exact (Submodule.mapQ _ _ α (Submodule.smul_top_le_comap_smul_top K α))
      (Submodule.mapQ _ _ π (Submodule.smul_top_le_comap_smul_top K π)) := by
  intro y
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Submodule.mapQ_apply, Set.mem_range]
  constructor
  · intro h
    have hm : π m ∈ K • (⊤ : Submodule A C) := (Submodule.Quotient.mk_eq_zero _).mp h
    have hmap : (K • (⊤ : Submodule A M)).map π = K • (⊤ : Submodule A C) := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hπ]
    rw [← hmap] at hm
    obtain ⟨m₀, hm₀, hπm₀⟩ := hm
    obtain ⟨p, hp⟩ := (hex (m - m₀)).mp (by rw [map_sub, hπm₀, sub_self])
    refine ⟨Submodule.Quotient.mk p, ?_⟩
    rw [Submodule.mapQ_apply, hp, Submodule.Quotient.eq, sub_sub_cancel_left]
    exact neg_mem hm₀
  · rintro ⟨z, hz⟩
    obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rw [Submodule.mapQ_apply] at hz
    have h'' := Submodule.smul_top_le_comap_smul_top K π ((Submodule.Quotient.eq _).mp hz)
    rw [Submodule.mem_comap, map_sub, hex.apply_apply_eq_zero, zero_sub] at h''
    exact (Submodule.Quotient.mk_eq_zero _).mpr (by simpa using neg_mem h'')

/-- Reducing a surjection modulo `K` keeps it surjective: `M ⧸ K M → C ⧸ K C` is onto. -/
private theorem surjective_mapQ_smul_top {A : Type u} [CommRing A] (K : Ideal A) {M C : Type*}
    [AddCommGroup M] [AddCommGroup C] [Module A M] [Module A C] (π : M →ₗ[A] C)
    (hπ : Function.Surjective π) :
    Function.Surjective (Submodule.mapQ _ _ π (Submodule.smul_top_le_comap_smul_top K π)) := by
  intro z
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨m, rfl⟩ := hπ c
  exact ⟨Submodule.Quotient.mk m, rfl⟩

/-- **The Tor argument of the induction step.** Let `P → M → C → 0` be exact, let `J ≤ I` be
ideals of `A` and suppose that `C ⧸ J C` is flat over `A ⧸ J`. If every element of `P` whose image
lies in `J M` lies in `I P`, then every element whose image lies in `I M` lies in `I P`.

Writing `X = M ⧸ J M`, the kernel `Y` of `X → C ⧸ J C` is the image of `P`, and flatness of the
cokernel gives `Y ∩ Ī X = Ī Y` for `Ī = I (A ⧸ J)` (`Module.mem_smul_top_of_flat_cokernel`); an
element of `Ī Y` is the image of an element of `I P`. -/
theorem mem_smul_top_of_flat_quotient_cokernel {A : Type u} [CommRing A] {J I : Ideal A}
    {P M C : Type*} [AddCommGroup P] [AddCommGroup M] [AddCommGroup C] [Module A P]
    [Module A M] [Module A C] (α : P →ₗ[A] M) (π : M →ₗ[A] C) (hπ : Function.Surjective π)
    (hex : Function.Exact α π) (hflat : Module.Flat (A ⧸ J) (C ⧸ (J • ⊤ : Submodule A C)))
    (h2 : ∀ x, α x ∈ J • (⊤ : Submodule A M) → x ∈ I • (⊤ : Submodule A P))
    (x : P) (hx : α x ∈ I • (⊤ : Submodule A M)) : x ∈ I • (⊤ : Submodule A P) := by
  set αq := Submodule.mapQ _ _ α (Submodule.smul_top_le_comap_smul_top J α)
  set πq := Submodule.mapQ _ _ π (Submodule.smul_top_le_comap_smul_top J π)
  have hexq : Function.Exact αq πq := exact_mapQ_smul_top J α π hπ hex
  let πT : (M ⧸ (J • ⊤ : Submodule A M)) →ₗ[A ⧸ J] (C ⧸ (J • ⊤ : Submodule A C)) :=
    πq.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  have hπT : Function.Surjective πT := surjective_mapQ_smul_top _ π hπ
  let Ibar : Ideal (A ⧸ J) := I.map (Ideal.Quotient.mk J)
  -- the image of `α x` in `M ⧸ J M` lies in the kernel of `πT`
  have hker : αq (Submodule.Quotient.mk x) ∈ LinearMap.ker πT :=
    LinearMap.mem_ker.mpr ((hexq _).mpr ⟨_, rfl⟩)
  have hIbar : ((⟨αq (Submodule.Quotient.mk x), hker⟩ : LinearMap.ker πT) :
      M ⧸ (J • ⊤ : Submodule A M)) ∈ Ibar • (⊤ : Submodule (A ⧸ J) _) := by
    change Submodule.Quotient.mk (α x) ∈ _
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha m _
      rw [Submodule.Quotient.mk_smul, ← algebraMap_smul (A ⧸ J) a]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) Submodule.mem_top
    · intro m m' hm hm'
      rw [Submodule.Quotient.mk_add]
      exact add_mem hm hm'
  have hmem := Module.mem_smul_top_of_flat_cokernel Ibar (LinearMap.ker πT).subtype πT
    (Submodule.injective_subtype _) hπT (LinearMap.exact_subtype_ker_map πT)
    ⟨αq (Submodule.Quotient.mk x), hker⟩ hIbar
  -- an element of `Ī Y` is the image of an element of `I P`
  have hlift : ∀ y ∈ Ibar • (⊤ : Submodule (A ⧸ J) (LinearMap.ker πT)),
      ∃ p ∈ I • (⊤ : Submodule A P), (y : M ⧸ (J • ⊤ : Submodule A M)) =
        αq (Submodule.Quotient.mk p) := by
    intro y hy
    refine Submodule.smul_induction_on hy ?_ ?_
    · intro b hb y' _
      obtain ⟨a, ha, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hb
      obtain ⟨z, hz⟩ :=
        (hexq (y' : M ⧸ (J • ⊤ : Submodule A M))).mp (LinearMap.mem_ker.mp y'.2)
      obtain ⟨p₁, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      refine ⟨a • p₁, Submodule.smul_mem_smul ha Submodule.mem_top, ?_⟩
      rw [Submodule.coe_smul, ← hz, Submodule.Quotient.mk_smul, map_smul,
        ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    · rintro y₁ y₂ ⟨p₁, hp₁, h₁⟩ ⟨p₂, hp₂, h₂⟩
      exact ⟨p₁ + p₂, add_mem hp₁ hp₂, by
        rw [Submodule.coe_add, h₁, h₂, Submodule.Quotient.mk_add, map_add]⟩
  obtain ⟨p, hp, hxp⟩ := hlift _ hmem
  have hJ : α (x - p) ∈ J • (⊤ : Submodule A M) := by
    have := (Submodule.Quotient.eq _).mp hxp
    rwa [map_sub]
  simpa using add_mem (h2 _ hJ) hp


/-- **Flatness of an extension modulo `I`.** Let `P → M → C → 0` be exact and suppose that the
induced map `P ⧸ I P → M ⧸ I M` is injective. If `P ⧸ I P` and `C ⧸ I C` are flat over `A ⧸ I`
then so is `M ⧸ I M`. -/
theorem flat_quotient_smul_top_of_exact {A : Type u} [CommRing A] (I : Ideal A) {P M C : Type*}
    [AddCommGroup P] [AddCommGroup M] [AddCommGroup C] [Module A P] [Module A M] [Module A C]
    (α : P →ₗ[A] M) (π : M →ₗ[A] C) (hπ : Function.Surjective π) (hex : Function.Exact α π)
    (hinj : ∀ x, α x ∈ I • (⊤ : Submodule A M) → x ∈ I • (⊤ : Submodule A P))
    [Module.Flat (A ⧸ I) (P ⧸ (I • ⊤ : Submodule A P))]
    [Module.Flat (A ⧸ I) (C ⧸ (I • ⊤ : Submodule A C))] :
    Module.Flat (A ⧸ I) (M ⧸ (I • ⊤ : Submodule A M)) := by
  have hmk : Function.Surjective (algebraMap A (A ⧸ I)) := Ideal.Quotient.mk_surjective
  set αq := Submodule.mapQ _ _ α (Submodule.smul_top_le_comap_smul_top I α)
  set πq := Submodule.mapQ _ _ π (Submodule.smul_top_le_comap_smul_top I π)
  have hexq : Function.Exact αq πq := exact_mapQ_smul_top I α π hπ hex
  let αT := αq.extendScalarsOfSurjective hmk
  let πT := πq.extendScalarsOfSurjective hmk
  have hαT : Function.Injective αT := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact (Submodule.Quotient.mk_eq_zero _).mpr
      (hinj x ((Submodule.Quotient.mk_eq_zero _).mp hz))
  have hπT : Function.Surjective πT := surjective_mapQ_smul_top _ π hπ
  exact flat_of_flat_of_flat αT πT hαT hexq hπT


/-- **The flatness condition over a quotient of the base.** For a proper ideal `J` of the local
ring `A` and a prime `Q` of `B` over the closed point, the condition
`Module.IsFlatAtPrimesAbove` over `A ⧸ J` is flatness over `A ⧸ J` of `X_Q ⧸ J X_Q`. -/
theorem isFlatAtPrimesAbove_quotient_iff {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v}
    [CommRing B] [Algebra A B] {Q : Ideal B} [Q.IsPrime]
    (hQ : Q.comap (algebraMap A B) = maximalIdeal A) {X : Type w} [AddCommGroup X] [Module B X]
    [Module A X] [IsScalarTower A B X] (J : Ideal A) [Nontrivial (A ⧸ J)] :
    letI : IsLocalRing (A ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
    IsFlatAtPrimesAbove A B Q X (A ⧸ J) ↔ Module.Flat (A ⧸ J)
      (LocalizedModule Q.primeCompl X ⧸
        (J • ⊤ : Submodule A (LocalizedModule Q.primeCompl X))) := by
  let : IsLocalRing (A ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have hJ : J ≠ ⊤ := Ideal.Quotient.nontrivial_iff.mp ‹_›
  rw [isFlatAtPrimesAbove_iff_conditionOn Q hQ]
  set S := flatAtPointSituationAtPrime A B Q hQ X
  have h1 : S.ConditionOn (A ⧸ J) ↔ S.Flattens J := by
    unfold FlatAtPointSituation.Flattens FlatAtPointSituation.ConditionOn
    rw [FlatAtPointSituation.maximalIdeal_quotient hJ]
  rw [h1, S.flattens_iff_flat_quotient J]
  have hinst : FlatAtPointSituation.moduleAM S =
      (inferInstance : Module A (LocalizedModule Q.primeCompl X)) :=
    Module.compHom_algebraMap_eq _
  rw [hinst]

/-- **The cokernel of a base change is the base change of the cokernel.** For a map `α : P → N`
of `A`-modules and an `A`-algebra `A'`, right exactness of the tensor product identifies the
quotient of `A' ⊗_A N` by the image of `A' ⊗_A α` with `A' ⊗_A (N ⧸ Im α)`. -/
@[ega "0 7.3.1" "more general"]
noncomputable def _root_.LinearMap.quotRangeBaseChangeEquiv {A : Type u} [CommRing A]
    (A' : Type v) [CommRing A'] [Algebra A A'] {P : Type w} [AddCommGroup P] [Module A P]
    {N : Type x} [AddCommGroup N] [Module A N] (α : P →ₗ[A] N) :
    ((A' ⊗[A] N) ⧸ LinearMap.range (α.baseChange A')) ≃ₗ[A']
      A' ⊗[A] (N ⧸ LinearMap.range α) := by
  have hsurj : Function.Surjective ((LinearMap.range α).mkQ.baseChange A') := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact LinearMap.lTensor_surjective A' (Submodule.mkQ_surjective _)
  have hex : Function.Exact (α.baseChange A') ((LinearMap.range α).mkQ.baseChange A') := by
    rw [LinearMap.baseChange_eq_lTensor, LinearMap.baseChange_eq_lTensor]
    exact _root_.lTensor_exact A' α.exact_map_mkQ_range (Submodule.mkQ_surjective _)
  exact (Submodule.quotEquivOfEq _ _ hex.linearMap_ker_eq.symm).trans
    (((LinearMap.range α).mkQ.baseChange A').quotKerEquivOfSurjective hsurj)

/-- **The commutativity of the tensor product, as an equivalence over the right factor.** For
the `R`-algebra structure `Algebra.TensorProduct.rightAlgebra` on `B ⊗[A] R`, the swap is
`R`-linear onto `R ⊗[A] B` with its standard structure. -/
noncomputable def tensorCommRight (A : Type u) (B : Type v) (R : Type y) [CommRing A]
    [CommRing B] [CommRing R] [Algebra A B] [Algebra A R] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    (B ⊗[A] R) ≃ₗ[R] R ⊗[A] B :=
  letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  AddEquiv.toLinearEquiv (TensorProduct.comm A B R).toAddEquiv fun r x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul b s =>
        change (TensorProduct.comm A B R) ((1 ⊗ₜ[A] r) * (b ⊗ₜ[A] s)) =
          r • (TensorProduct.comm A B R) (b ⊗ₜ[A] s)
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/-- The submodule `J X` generated by an ideal of `A` is stable under the action of an
`A`-algebra `B` acting compatibly on `X`. -/
theorem smul_mem_ideal_smul_top {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {X : Type w} [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X] (J : Ideal A)
    (b : B) {z : X} (hz : z ∈ (J • ⊤ : Submodule A X)) : b • z ∈ (J • ⊤ : Submodule A X) := by
  refine Submodule.smul_induction_on hz (fun a ha m _ ↦ ?_) (fun m m' hm hm' ↦ ?_)
  · rw [← algebraMap_smul B a m, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [smul_add]
    exact add_mem hm hm'

/-- An element `m / t` of a localization lies in `J X_T` only if some `t' • m` lies in `J X`. -/
theorem exists_smul_mem_of_mk_mem_ideal_smul_top {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] {X : Type w} [AddCommGroup X] [Module A X] [Module B X]
    [IsScalarTower A B X] (T : Submonoid B) (J : Ideal A) (m : X) (t : T)
    (h : LocalizedModule.mk m t ∈ (J • ⊤ : Submodule A (LocalizedModule T X))) :
    ∃ t' : T, (t' : B) • m ∈ (J • ⊤ : Submodule A X) := by
  have key : ∀ z ∈ (J • ⊤ : Submodule A (LocalizedModule T X)),
      ∃ m₀ ∈ (J • ⊤ : Submodule A X), ∃ t₀ : T, z = LocalizedModule.mk m₀ t₀ := by
    intro z hz
    refine Submodule.smul_induction_on hz (fun a ha z _ ↦ ?_) ?_
    · induction z using LocalizedModule.induction_on with
      | h m₁ t₁ =>
        refine ⟨a • m₁, Submodule.smul_mem_smul ha Submodule.mem_top, t₁, ?_⟩
        rw [← algebraMap_smul B a, LocalizedModule.smul'_mk, algebraMap_smul]
    · rintro z₁ z₂ ⟨m₁, hm₁, t₁, rfl⟩ ⟨m₂, hm₂, t₂, rfl⟩
      exact ⟨t₂ • m₁ + t₁ • m₂, add_mem (smul_mem_ideal_smul_top J (t₂ : B) hm₁)
        (smul_mem_ideal_smul_top J (t₁ : B) hm₂), t₁ * t₂, LocalizedModule.mk_add_mk⟩
  obtain ⟨m₀, hm₀, t₀, heq⟩ := key _ h
  obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp heq
  refine ⟨u * t₀, ?_⟩
  rw [Submonoid.coe_mul, ← smul_smul]
  change u • t₀ • m ∈ _
  rw [hu]
  exact smul_mem_ideal_smul_top J _ (smul_mem_ideal_smul_top J _ hm₀)

/-- If `z ∈ I X` then `z / t ∈ I X_T`. -/
theorem mk_mem_ideal_smul_top {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {X : Type w} [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
    (T : Submonoid B) (I : Ideal A) {z : X} (hz : z ∈ (I • ⊤ : Submodule A X)) (t : T) :
    LocalizedModule.mk z t ∈ (I • ⊤ : Submodule A (LocalizedModule T X)) := by
  let φ : X →ₗ[A] LocalizedModule T X :=
    { toFun := fun z ↦ LocalizedModule.mk z t
      map_add' := fun z z' ↦ by
        rw [LocalizedModule.mk_add_mk, ← smul_add, LocalizedModule.mk_cancel_common_left]
      map_smul' := fun a z ↦ by
        rw [RingHom.id_apply, ← algebraMap_smul B a z, ← LocalizedModule.smul'_mk,
          algebraMap_smul] }
  exact Submodule.smul_top_le_comap_smul_top I φ hz

section Step

variable {A : Type u} [CommRing A] [IsLocalRing A] {B : Type u} [CommRing B] [Algebra A B]
  [Module.Flat A B] [Module.Projective A B]
  [AlgebraicGeometry.GeometricallyIntegral
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B)))]
  [(Algebra.closedFiberIdeal A B).IsPrime]
  {M : Type w} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
  [Module.Finite B M] {r : ℕ} (α : (Fin r →₀ B) →ₗ[B] M)
  (hα : Function.Bijective (α.baseChange (Algebra.closedFiberIdeal A B).ResidueField))

omit [Module A M] [IsScalarTower A B M] in
include hα in
/-- **Stacks Tag 05I3 over a local `A`-algebra, at one prime.** Let `B` be flat and projective
over `A` with geometrically integral fibres and let `α : B^(⊕ r) → M` be an isomorphism over the
generic point of the closed fibre. For a local `A`-algebra `R` and a prime `𝔮` of `B ⊗[A] R`
over the closed point of `R`, flatness over `R` of the base change of `M` at `𝔮` forces flatness
of the base change of `Coker(α)` at `𝔮` and injectivity of the base change of `α`. -/
theorem flat_cokernel_and_injective_of_flat (R : Type max u y) [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsLocalHom (algebraMap A R)] :
    letI : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    ∀ (𝔮 : Ideal (B ⊗[A] R)) (_ : 𝔮.IsPrime),
      Ideal.map (algebraMap R (B ⊗[A] R)) (maximalIdeal R) ≤ 𝔮 →
      Module.Flat R (LocalizedModule 𝔮.primeCompl ((B ⊗[A] R) ⊗[B] M)) →
        Module.Flat R (LocalizedModule 𝔮.primeCompl
          ((B ⊗[A] R) ⊗[B] (M ⧸ LinearMap.range α))) ∧
        Function.Injective (α.baseChange (B ⊗[A] R)) := by
  let : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
  intro 𝔮 h𝔮 hle hflat
  have : Module.Flat R (B ⊗[A] R) := Module.Flat.of_linearEquiv (tensorCommRight A B R)
  have : Module.Projective R (B ⊗[A] R) :=
    Module.Projective.of_equiv (tensorCommRight A B R).symm
  have hprime := closedFiberIdeal_tensorProduct_isPrime (A := A) (B := B) R
  have hq : 𝔮.comap (algebraMap R (B ⊗[A] R)) = maximalIdeal R :=
    ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_isPrime _ 𝔮).ne_top
      (Ideal.map_le_iff_le_comap.mp hle)).symm
  let e := TensorProduct.finsuppScalarRight B (B ⊗[A] R) (B ⊗[A] R) (Fin r)
  let α' : (Fin r →₀ B ⊗[A] R) →ₗ[B ⊗[A] R] (B ⊗[A] R) ⊗[B] M :=
    α.baseChange (B ⊗[A] R) ∘ₗ e.symm.toLinearMap
  have hα' : Function.Bijective
      (α'.baseChange (Algebra.closedFiberIdeal R (B ⊗[A] R)).ResidueField) := by
    rw [LinearMap.baseChange_comp]
    exact (bijective_baseChange_closedFiber_tensorProduct hprime α hα).comp
      (e.symm.baseChange _ _ _ _).bijective
  have hrange : LinearMap.range α' = LinearMap.range (α.baseChange (B ⊗[A] R)) :=
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr e.symm.surjective)
  refine ⟨?_, ?_⟩
  · have h := flat_localizedModule_coker_of_flat_localizedModule_of_projective_finsupp
      R (B ⊗[A] R) 𝔮 hq ((B ⊗[A] R) ⊗[B] M) r α' hα' hflat
    rw [hrange] at h
    exact (flat_localizedModule_congr 𝔮.primeCompl
      (LinearMap.quotRangeBaseChangeEquiv (B ⊗[A] R) α)).mp h
  · have h := injective_of_flat_localizedModule_of_projective_finsupp
      R (B ⊗[A] R) 𝔮 hq ((B ⊗[A] R) ⊗[B] M) r α' hα' hflat
    have : ⇑(α.baseChange (B ⊗[A] R)) = α' ∘ e := by
      funext x
      simp [α']
    rw [this]
    exact h.comp e.injective

include hα in
/-- **The induction step of the source's proof of Stacks Tag 05PG.** Let `B` be flat and
projective over the local ring `A` with geometrically integral fibres, let `Q` be a prime of `B`
over the closed point and let `α : B^(⊕ r) → M` be an isomorphism over the generic point of the
closed fibre. If the flatness condition at `Q` for the cokernel of `α` is corepresented by an ideal
`J` of `A`, then the flatness condition at `Q` for `M` is corepresented by an ideal of `A`.

Over a local `A`-algebra `R`, Stacks Tag 05I3 turns flatness of `M` into flatness of the cokernel
and injectivity of `α ⊗ R` (`Module.flat_cokernel_and_injective_of_flat`); injectivity kills the
coefficients, under a splitting of `B^(⊕ r)` over `A`, of every element whose image lies in `J M`.
Conversely, once `J` and those coefficients die, the cokernel of `α` is flat modulo `J` at `Q`,
so the image of `B^(⊕ r)` meets `I M` in `I`-multiples
(`Module.mem_smul_top_of_flat_quotient_cokernel`) and `M` is flat modulo `I` at `Q` as an
extension of flat modules. -/
theorem exists_ideal_isFlatAtPrimesAbove_iff_of_cokernel {Q : Ideal B} [Q.IsPrime]
    (hQ : Q.comap (algebraMap A B) = maximalIdeal A) (J : Ideal A)
    (hJ : ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra A R]
      [IsLocalHom (algebraMap A R)],
      IsFlatAtPrimesAbove A B Q (M ⧸ LinearMap.range α) R ↔ Ideal.map (algebraMap A R) J = ⊥) :
    ∃ I : Ideal A, ∀ (R : Type max u x) [CommRing R] [IsLocalRing R] [Algebra A R]
      [IsLocalHom (algebraMap A R)],
      IsFlatAtPrimesAbove A B Q M R ↔ Ideal.map (algebraMap A R) I = ⊥ := by
  classical
  have hPproj : Module.Projective A (Fin r →₀ B) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp A).symm
  obtain ⟨s, hs⟩ := Module.projective_def.mp hPproj
  let G : Set A := {a | ∃ x : Fin r →₀ B, α x ∈ (J • ⊤ : Submodule A M) ∧ ∃ e, a = s x e}
  let I : Ideal A := J ⊔ Ideal.span G
  have h2 : ∀ x : Fin r →₀ B, α x ∈ (J • ⊤ : Submodule A M) →
      x ∈ (I • ⊤ : Submodule A (Fin r →₀ B)) := by
    intro x hx
    rw [← hs x, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun e _ ↦ Submodule.smul_mem_smul ?_ Submodule.mem_top
    exact Ideal.mem_sup_right (Ideal.subset_span ⟨x, hx, e, rfl⟩)
  refine ⟨I, fun R _ _ _ _ ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
  · -- the condition kills `I`
    let : Algebra R (B ⊗[A] R) := Algebra.TensorProduct.rightAlgebra
    have hcoker : IsFlatAtPrimesAbove A B Q (M ⧸ LinearMap.range α) R :=
      fun 𝔮 h𝔮 hle hcomap ↦ (flat_cokernel_and_injective_of_flat α hα R 𝔮 h𝔮 hle
        (h 𝔮 h𝔮 hle hcomap)).1
    have hJR := (hJ R).mp hcoker
    obtain ⟨𝔮₀, h𝔮₀, hle₀, hcomap₀⟩ := exists_isPrime_closedFiber_comap_eq Q hQ R
    have hinj := (flat_cokernel_and_injective_of_flat α hα R 𝔮₀ h𝔮₀ hle₀
      (h 𝔮₀ h𝔮₀ hle₀ hcomap₀)).2
    have hz : ∀ j ∈ J, (algebraMap A B j) • (1 : B ⊗[A] R) = 0 := by
      intro j hj
      have hj0 : algebraMap A R j = 0 :=
        RingHom.mem_ker.mp ((Ideal.map_eq_bot_iff_le_ker _).mp hJR hj)
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', algebraMap_smul,
        TensorProduct.smul_tmul, Algebra.smul_def, mul_one, hj0, TensorProduct.tmul_zero]
    rw [Ideal.map_eq_bot_iff_le_ker]
    refine sup_le ((Ideal.map_eq_bot_iff_le_ker _).mp hJR) (Ideal.span_le.mpr ?_)
    rintro _ ⟨x, hx, e, rfl⟩
    have h1 : (1 : B ⊗[A] R) ⊗ₜ[B] α x = 0 := by
      refine Submodule.smul_induction_on hx (fun j hj m _ ↦ ?_) (fun m m' hm hm' ↦ ?_)
      · rw [← algebraMap_smul B j m, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
          hz j hj, TensorProduct.zero_tmul]
      · rw [TensorProduct.tmul_add, hm, hm', add_zero]
    have h0 : (1 : B ⊗[A] R) ⊗ₜ[B] x = 0 := by
      apply hinj
      rw [LinearMap.baseChange_tmul, h1, map_zero]
    have h3 := congrArg (Algebra.IsPushout.cancelBaseChange A R B (B ⊗[A] R) (Fin r →₀ B)) h0
    rw [Algebra.IsPushout.cancelBaseChange_tmul, map_zero] at h3
    have h4 := congrArg (fun t ↦ TensorProduct.finsuppScalarRight A A R (Fin r →₀ B)
      (s.lTensor R t) e) h3
    simp only [LinearMap.lTensor_tmul, TensorProduct.finsuppScalarRight_apply_tmul_apply,
      map_zero, Finsupp.coe_zero, Pi.zero_apply] at h4
    rwa [SetLike.mem_coe, RingHom.mem_ker, Algebra.algebraMap_eq_smul_one]
  · -- the vanishing of `I` forces the condition
    have hI : I ≠ ⊤ := by
      intro htop
      rw [htop, Ideal.map_top] at h
      have h1 : (1 : R) ∈ (⊥ : Ideal R) := h ▸ Submodule.mem_top
      exact one_ne_zero ((Submodule.mem_bot R).mp h1)
    have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
    have : Nontrivial (A ⧸ J) :=
      Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top hI le_sup_left)
    let : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
    let : IsLocalRing (A ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap A (A ⧸ I)) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (algebraMap A (A ⧸ J)) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hker : I ≤ RingHom.ker (algebraMap A R) := (Ideal.map_eq_bot_iff_le_ker _).mp h
    let : Algebra (A ⧸ I) R :=
      (Ideal.Quotient.lift I (algebraMap A R) fun a ha ↦ hker ha).toAlgebra
    have : IsScalarTower A (A ⧸ I) R := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : IsLocalHom (algebraMap (A ⧸ I) R) := by
      refine ⟨fun a ha ↦ ?_⟩
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
      exact (IsLocalHom.map_nonunit (f := algebraMap A R) b ha).map (Ideal.Quotient.mk I)
    refine IsFlatAtPrimesAbove.of_isLocalHom (R := A ⧸ I) hQ R ?_
    rw [isFlatAtPrimesAbove_quotient_iff hQ I]
    -- flatness of the cokernel modulo `I` and modulo `J`
    have hcok : ∀ K : Ideal A, J ≤ K → (hK : Nontrivial (A ⧸ K)) →
        Module.Flat (A ⧸ K) (LocalizedModule Q.primeCompl (M ⧸ LinearMap.range α) ⧸
          (K • ⊤ : Submodule A (LocalizedModule Q.primeCompl (M ⧸ LinearMap.range α)))) := by
      intro K hJK hK
      let : IsLocalRing (A ⧸ K) := .of_surjective' _ Ideal.Quotient.mk_surjective
      have : IsLocalHom (algebraMap A (A ⧸ K)) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      rw [← isFlatAtPrimesAbove_quotient_iff hQ K,
        ← isFlatAtPrimesAbove_ulift_iff.{u, u, w, u, max u x} hQ, hJ]
      rw [Ideal.map_eq_bot_iff_le_ker, ULift.ker_algebraMap, Ideal.Quotient.algebraMap_eq,
        Ideal.mk_ker]
      exact hJK
    have hcokI := hcok I le_sup_left inferInstance
    have hcokJ := hcok J le_rfl inferInstance
    -- flatness of the localized free module modulo `I`
    have : Module.Flat A (LocalizedModule Q.primeCompl (Fin r →₀ B)) :=
      Flat.localizedModule_of_isScalarTower (R := A) (A := B) Q.primeCompl
    have : Module.Flat (A ⧸ I) (LocalizedModule Q.primeCompl (Fin r →₀ B) ⧸
        (I • ⊤ : Submodule A (LocalizedModule Q.primeCompl (Fin r →₀ B)))) :=
      Module.Flat.of_linearEquiv (TensorProduct.quotTensorEquivQuotSMulₐ _ I).symm
    let α' := (LocalizedModule.map Q.primeCompl α).restrictScalars A
    let π' := (LocalizedModule.map Q.primeCompl (LinearMap.range α).mkQ).restrictScalars A
    have hπ' : Function.Surjective π' :=
      LocalizedModule.map_surjective _ _ (Submodule.mkQ_surjective _)
    have hex' : Function.Exact α' π' :=
      LocalizedModule.map_exact Q.primeCompl α _ α.exact_map_mkQ_range
    have h2' : ∀ y, α' y ∈ (J • ⊤ : Submodule A _) → y ∈ (I • ⊤ : Submodule A _) := by
      intro y hy
      induction y using LocalizedModule.induction_on with
      | h x t =>
        have hy' : LocalizedModule.mk (α x) t ∈
            (J • ⊤ : Submodule A (LocalizedModule Q.primeCompl M)) := by
          simpa [α', LocalizedModule.map_mk] using hy
        obtain ⟨t', ht'⟩ := exists_smul_mem_of_mk_mem_ideal_smul_top Q.primeCompl J _ t hy'
        rw [← map_smul] at ht'
        rw [← LocalizedModule.mk_cancel_common_left t' t x]
        exact mk_mem_ideal_smul_top Q.primeCompl I (h2 _ ht') _
    exact flat_quotient_smul_top_of_exact I α' π' hπ' hex'
      (mem_smul_top_of_flat_quotient_cokernel α' π' hπ' hex' hcokJ h2')

end Step

end Module

end
