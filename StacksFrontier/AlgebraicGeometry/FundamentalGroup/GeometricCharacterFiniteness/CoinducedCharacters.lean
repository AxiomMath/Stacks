module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.FiniteTypeCoinduction
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedCohomologyDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationSheafConstant
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricCharacterFiniteness.CocycleClass
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricCharacterFiniteness.ShapiroCocycle
public import Mathlib.Topology.Instances.ZMod

/-!
# Characters of `φ⁻¹(H)` are bounded by `H¹(G, Coind_H 𝔽_ℓ)`

Let `φ : G → Γ` be a continuous homomorphism of compact groups, `H` an open normal subgroup of
`Γ` and `P = Coind_H 𝔽_ℓ` the module of functions `Γ ⧸ H → 𝔽_ℓ`, restricted to `G` along `φ`. A
continuous character `χ : φ⁻¹(H) → 𝔽_ℓ` gives the Shapiro cocycle
(`Stacks.GroupCohomology.shapiroCocycle`), whose class in `H¹(G, P)` determines `χ`: two cocycles
with the same class differ by a coboundary, and coboundaries vanish on `φ⁻¹(H)`, which acts
trivially on `P`. So there are at most `#H¹(G, P)` continuous characters of `φ⁻¹(H)`.

Characters of an open subgroup `V` of a compact group are determined by their restriction to an
open subgroup `N ≤ V` and their values on representatives of the finitely many cosets of `N` in
`V`, which reduces the finiteness for `V` to that for `N`.

## Main results

* `Stacks.GroupCohomology.finite_continuous_monoidHom_comap_of_finite` — finitely many continuous
  characters of `φ⁻¹(H)` when `H¹(G, Coind_H 𝔽_ℓ)` is finite.
* `Stacks.GroupCohomology.finite_continuous_monoidHom_of_le` — the reduction from `V` to an open
  subgroup `N ≤ V`.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.ContinuousCohomology

universe w

namespace Stacks.GroupCohomology

section Reduction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {M : Type*} [Group M] [Finite M] [TopologicalSpace M]

/-- **Finitely many characters on `N` give finitely many on `V ⊇ N`**, for `N` an open subgroup of
a compact group and `M` finite: a homomorphism on `V` is determined by its restriction to `N` and
its values on representatives of `V ⧸ N`. -/
theorem finite_continuous_monoidHom_of_le {N V : Subgroup G} (hNV : N ≤ V)
    (hN : IsOpen (N : Set G)) (hfin : Finite {χ : N →* M // Continuous χ}) :
    Finite {χ : V →* M // Continuous χ} := by
  have : Finite (G ⧸ N) := N.quotient_finite_of_isOpen hN
  have : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : Finite (V ⧸ N.subgroupOf V) := inferInstance
  let res : {χ : V →* M // Continuous χ} → {χ : N →* M // Continuous χ} := fun χ ↦
    ⟨χ.1.comp (Subgroup.inclusion hNV), χ.2.comp (continuous_inclusion hNV)⟩
  refine Finite.of_injective (fun χ ↦ (res χ, fun q : V ⧸ N.subgroupOf V ↦ χ.1 q.out)) ?_
  rintro χ ψ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : ∀ n : N, χ.1 (Subgroup.inclusion hNV n) = ψ.1 (Subgroup.inclusion hNV n) :=
    fun n ↦ congrArg (fun ρ : {χ : N →* M // Continuous χ} ↦ ρ.1 n) h1
  refine Subtype.ext (MonoidHom.ext fun v ↦ ?_)
  obtain ⟨q, hqv⟩ : ∃ q : V ⧸ N.subgroupOf V, q = v := ⟨_, rfl⟩
  have hq : q.out⁻¹ * v ∈ N.subgroupOf V := QuotientGroup.eq.1 ((QuotientGroup.out_eq' q).trans hqv)
  obtain ⟨n, hn⟩ : ∃ n : N, v = q.out * Subgroup.inclusion hNV n :=
    ⟨⟨_, hq⟩, by ext; simp⟩
  rw [hn, map_mul, map_mul, congrFun h2 q, h1' n]

end Reduction

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The coefficient module `𝔽_ℓ`, at the universe `w`. -/
abbrev zmodCoefficient : ObjectProperty.FullSubcategory (ModuleCat.isFG.{w} (ZMod ℓ)) :=
  ⟨ModuleCat.of (ZMod ℓ) (ULift.{w} (ZMod ℓ)), Module.Finite.of_finite⟩

variable {G Γ : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (φ : G →ₜ* Γ)
  (H : OpenSubgroup Γ) [H.toSubgroup.Normal]

/-- The permutation module `Coind_H 𝔽_ℓ` of functions `Γ ⧸ H → 𝔽_ℓ`, restricted to `G`. -/
abbrev coinducedZModRes : Stacks.Injectives.ContinuousModule.{0, w, w} (ZMod ℓ) G :=
  (finiteTypeContinuousModuleToRes (ZMod ℓ) φ).obj ((finiteTypeContinuousModuleCoind (ZMod ℓ) H).obj
    ((finiteTypeContinuousModuleTrivial (ZMod ℓ) Γ).obj (zmodCoefficient.{w} ℓ)))

omit [IsTopologicalGroup G] [CompactSpace G] [H.toSubgroup.Normal] in
/-- The action of `G` on `Coind_H 𝔽_ℓ`: `(g • F)(x) = F(φ(g)⁻¹ • x)`. -/
lemma rep_coinducedZModRes_apply (g : G) (F : Γ ⧸ (H : Subgroup Γ) → ULift.{w} (ZMod ℓ))
    (x : Γ ⧸ (H : Subgroup Γ)) :
    rep (ZMod ℓ) G (coinducedZModRes ℓ φ H) g F x = F ((φ g)⁻¹ • x) :=
  rfl

/-- A multiplicative character read additively. -/
def charToAdd {N : Type*} [Group N] (χ : N →* Multiplicative (ZMod ℓ)) (n : N) : ZMod ℓ :=
  Multiplicative.toAdd (χ n)

lemma charToAdd_mul {N : Type*} [Group N] (χ : N →* Multiplicative (ZMod ℓ)) (a b : N) :
    charToAdd ℓ χ (a * b) = charToAdd ℓ χ a + charToAdd ℓ χ b :=
  (congrArg Multiplicative.toAdd (map_mul χ a b)).trans (toAdd_mul _ _)

/-- The Shapiro cocycle of a continuous character of `φ⁻¹(H)`, with values in `Coind_H 𝔽_ℓ`. -/
def shapiroCocycles₁ (χ : (H : Subgroup Γ).comap φ.toMonoidHom →* Multiplicative (ZMod ℓ))
    (hχ : Continuous χ) : cocycles₁ (ZMod ℓ) G (coinducedZModRes ℓ φ H) := by
  refine ⟨fun g x ↦ ULift.up (shapiroCocycle φ.toMonoidHom H (charToAdd ℓ χ) g x), ?_, ?_⟩
  · intro g h
    funext x
    exact congrArg ULift.up (shapiroCocycle_mul φ.toMonoidHom H _ (charToAdd_mul ℓ χ) g h x)
  · have hN : IsOpen (((H : Subgroup Γ).comap φ.toMonoidHom : Subgroup G) : Set G) :=
      H.isOpen.preimage φ.continuous
    have hker : IsOpen {g : G | ∃ h : g ∈ (H : Subgroup Γ).comap φ.toMonoidHom,
        charToAdd ℓ χ ⟨g, h⟩ = 0} := by
      have h1 : IsOpen (χ ⁻¹' {1}) := (isOpen_discrete _).preimage hχ
      convert hN.isOpenMap_subtype_val _ h1 using 1
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h, h0⟩
        refine ⟨⟨g, h⟩, ?_, rfl⟩
        rw [← ofAdd_toAdd (χ _)]
        exact (congrArg Multiplicative.ofAdd h0).trans ofAdd_zero
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n.2, show Multiplicative.toAdd (χ n) = 0 by rw [hn, toAdd_one]⟩
    exact (isLocallyConstant_shapiroCocycle φ.toMonoidHom H _
      (charToAdd_mul ℓ χ) hker).comp (fun F x ↦ ULift.up (F x))

omit [CompactSpace G] in
/-- The Shapiro cocycle recovers the character at the trivial coset. -/
lemma shapiroCocycles₁_apply_one
    (χ : (H : Subgroup Γ).comap φ.toMonoidHom →* Multiplicative (ZMod ℓ))
    (hχ : Continuous χ) (n : (H : Subgroup Γ).comap φ.toMonoidHom) :
    (shapiroCocycles₁ ℓ φ H χ hχ).1 n ((1 : Γ) : Γ ⧸ (H : Subgroup Γ)) =
      ULift.up (charToAdd ℓ χ n) :=
  congrArg ULift.up (shapiroCocycle_apply_one φ.toMonoidHom H (charToAdd ℓ χ) n.2)

omit [CompactSpace G] in
/-- **Finitely many continuous characters of `φ⁻¹(H)`** with values in `𝔽_ℓ`, as soon as
`H¹(G, Coind_H 𝔽_ℓ)` is finite: a character is determined by the class of its Shapiro
cocycle. -/
theorem finite_continuous_monoidHom_comap_of_finite
    (hfin : Finite (((invariantsDelta.{0, w, w} (ZMod ℓ) (G := G)).functor 1).obj
      (coinducedZModRes ℓ φ H))) :
    Finite {χ : (H : Subgroup Γ).comap φ.toMonoidHom →* Multiplicative (ZMod ℓ) //
      Continuous χ} := by
  refine Finite.of_injective
    (fun χ ↦ cocycleClass.{0, w, w} (coinducedZModRes ℓ φ H) (shapiroCocycles₁ ℓ φ H χ.1 χ.2))
    fun χ ψ hχψ ↦ ?_
  obtain ⟨F, hF⟩ := exists_eq_sub_of_cocycleClass_eq.{0, w, w} _ _ _ hχψ
  refine Subtype.ext (MonoidHom.ext fun n ↦ ?_)
  have h := congrFun (hF n) ((1 : Γ) : Γ ⧸ (H : Subgroup Γ))
  have htriv : rep (ZMod ℓ) G (coinducedZModRes ℓ φ H) n F = F :=
    comp_smul_eq_of_mem φ.toMonoidHom H F n.2
  rw [htriv, sub_self] at h
  have h' := sub_eq_zero.1
    (h : (shapiroCocycles₁ ℓ φ H χ.1 χ.2).1 n ((1 : Γ) : Γ ⧸ (H : Subgroup Γ)) -
      (shapiroCocycles₁ ℓ φ H ψ.1 ψ.2).1 n ((1 : Γ) : Γ ⧸ (H : Subgroup Γ)) = 0)
  rw [shapiroCocycles₁_apply_one, shapiroCocycles₁_apply_one] at h'
  exact Multiplicative.toAdd.injective (congrArg ULift.down h')

end Stacks.GroupCohomology
