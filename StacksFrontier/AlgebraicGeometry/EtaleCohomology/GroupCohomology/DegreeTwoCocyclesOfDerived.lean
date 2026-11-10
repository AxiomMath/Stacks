module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.CoinducedCochainAcyclic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.TorsionDerivedVanishing

/-!
# From `H ²(G, M) = 0` to the vanishing of locally constant `2`-cocycles

Let `G` be a profinite group and `M` a discrete `G`-module. The group `H ²(G, M)` of
`Stacks.continuousGroupCohomology` is a right derived functor of invariants. This file proves the
direction of the comparison with cochains that needs an acyclic resolution: **if `H ²(G, M) = 0`
then every locally constant `2`-cocycle with values in `M` is the coboundary of a locally
constant `1`-cochain.** The converse is
`Stacks.GroupCohomology.isZero_continuousGroupCohomology_two_of_vanishesTwo`.

## Main results

* `Stacks.GroupCohomology.epi_map_g_of_isZero_continuousGroupCohomology_one`: invariants are right
  exact on a short exact sequence whose kernel has vanishing `H ¹`.
* `Stacks.GroupCohomology.vanishesOne_of_isZero_continuousGroupCohomology_one`: `H ¹(G, M) = 0`
  gives the cochain-level statement in degree one.
* `Stacks.GroupCohomology.vanishesTwo_of_isZero_continuousGroupCohomology_two`: **`H ²(G, M) = 0`
  gives the cochain-level statement in degree two.**

## Implementation notes

The acyclic object is the module `I(M)` of locally constant functions `G → M` with `G` acting by
right translation, into which `M` embeds by `m ↦ (x ↦ x • m)`
(`Stacks.GroupCohomology.orbitMap`). It has no locally constant cocycles but coboundaries in
degrees one and two by explicit formulas (`Stacks.GroupCohomology.vanishesOne_lcFun`,
`Stacks.GroupCohomology.vanishesTwo_lcFun`), so `H ¹(G, I(M)) = 0` by the degree-one criterion.
For `0 → M → I(M) → Q → 0` the long exact sequence gives `H ¹(G, Q) = 0` from `H ²(G, M) = 0`.
Degree one is then read on cochains by embedding `Q` in turn into `I(Q)`: `H ¹(G, Q) = 0` says
that invariants lift along `I(Q) → I(Q)/Q`, which is what the cochain argument needs. Finally a
`2`-cocycle of `M` trivializes in `I(M)` and the trivializing cochain is corrected using the
degree-one statement for `Q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.ContinuousCohomology

universe u v

namespace Stacks.GroupCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The underlying additive map of a morphism of discrete `G`-modules. -/
abbrev homAdd {X Y : ContinuousGModule.{u, max u v} G} (f : X ⟶ Y) :
    X.obj.obj.V →+ Y.obj.obj.V :=
  (f.hom.hom.hom.hom : X.obj.obj.V →ₗ[ℤ] Y.obj.obj.V).toAddMonoidHom

omit [IsTopologicalGroup G] in
/-- The underlying additive map of a morphism of discrete `G`-modules is `G`-equivariant. -/
lemma homAdd_smul {X Y : ContinuousGModule.{u, max u v} G} (f : X ⟶ Y) (g : G)
    (x : X.obj.obj.V) :
    letI := carrierAction X
    letI := carrierAction Y
    homAdd f (g • x) = g • homAdd f x :=
  ConcreteCategory.congr_hom (f.hom.hom.comm g) x

omit [IsTopologicalGroup G] in
/-- The underlying maps of a short exact sequence of discrete `G`-modules form a short exact
sequence of abelian groups. -/
lemma shortExact_underlying {S : ShortComplex (ContinuousGModule.{u, max u v} G)}
    (hS : S.ShortExact) :
    Function.Injective (homAdd S.f) ∧ Function.Surjective (homAdd S.g) ∧
      (∀ m, homAdd S.g (homAdd S.f m) = 0) ∧
      (∀ m, homAdd S.g m = 0 → ∃ m₁, homAdd S.f m₁ = m) := by
  have hSu := hS.map_of_exact (continuousGModuleUnderlying.{u, max u v} G)
  exact ⟨hSu.moduleCat_injective_f, hSu.moduleCat_surjective_g,
    fun m ↦ ShortComplex.moduleCat_zero_apply
      (S.map (continuousGModuleUnderlying.{u, max u v} G)) m,
    (ShortComplex.moduleCat_exact_iff _).mp hSu.exact⟩

attribute [local instance] HasDerivedCategory.standard

/-- The cohomological δ-functor of the right derived functors of invariants, i.e. of continuous
group cohomology `H ⁿ(G, -)`. -/
abbrev cohomologyDelta : CategoryTheory.DeltaFunctor (ContinuousGModule.{u, max u v} G)
    AddCommGrpCat.{max u v} :=
  Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor
    (continuousGModuleInvariants.{u, max u v} G)
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure _)
    (Stacks.DerivedIndexing.canonicalδ _) (fun _ _ ↦ rfl)

/-- **Invariants are right exact on a short exact sequence whose kernel has `H ¹ = 0`**: the long
exact sequence `M₂ ᴳ → M₃ ᴳ → H ¹(G, M₁)` of continuous group cohomology. -/
theorem epi_map_g_of_isZero_continuousGroupCohomology_one
    {S : ShortComplex (ContinuousGModule.{u, max u v} G)} (hS : S.ShortExact)
    (h : IsZero (continuousGroupCohomology.{u, v} G 1 S.X₁)) :
    Epi ((continuousGModuleInvariants.{u, max u v} G).map S.g) := by
  have : PreservesFiniteLimits (continuousGModuleInvariants.{u, max u v} G) :=
    preservesFiniteLimits_invariants G
  have : Epi (((continuousGModuleInvariants.{u, max u v} G).rightDerivedPlus 0).map S.g) :=
    ((cohomologyDelta.{u, v} (G := G)).exact_δ₁ hS 0).epi_f (h.eq_of_tgt _ _)
  rw [← NatIso.naturality_2
    (rightDerivedPlusZeroIso (continuousGModuleInvariants.{u, max u v} G)) S.g]
  infer_instance

/-- The invariant-lifting statement read off from `H ¹` of the kernel. -/
theorem exists_invariant_lift_of_isZero_continuousGroupCohomology_one
    {S : ShortComplex (ContinuousGModule.{u, max u v} G)} (hS : S.ShortExact)
    (h : IsZero (continuousGroupCohomology.{u, v} G 1 S.X₁))
    (y : S.X₃.obj.obj.V) (hy : ∀ g : G, (S.X₃.obj.obj.ρ g).asHom.hom y = y) :
    ∃ x : S.X₂.obj.obj.V, (∀ g : G, (S.X₂.obj.obj.ρ g).asHom.hom x = x) ∧ homAdd S.g x = y := by
  have := epi_map_g_of_isZero_continuousGroupCohomology_one hS h
  obtain ⟨x, hx⟩ := (AddCommGrpCat.epi_iff_surjective _).1 this ⟨y, fun g ↦ hy g⟩
  exact ⟨x.1, fun g ↦ x.2 g, congrArg Subtype.val hx⟩

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The embedding of a discrete `G`-module into the module of locally constant functions
`G → M`, `m ↦ (x ↦ x • m)`, and its cokernel, as a short exact sequence. -/
abbrev coinducedSeq (N : ContinuousGModule.{u, max u v} G) :
    ShortComplex (ContinuousGModule.{u, max u v} G) :=
  ShortComplex.mk (orbitMap N (AddMonoidHom.id N.obj.obj.V))
    (cokernel.π (orbitMap N (AddMonoidHom.id N.obj.obj.V)))
    (cokernel.condition (orbitMap N (AddMonoidHom.id N.obj.obj.V)))

/-- The sequence `coinducedSeq N` is short exact. -/
lemma shortExact_coinducedSeq (N : ContinuousGModule.{u, max u v} G) :
    (coinducedSeq N).ShortExact := by
  have := mono_orbitMap N (AddMonoidHom.id _) Function.injective_id
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel _
      (cokernelIsCokernel (orbitMap N (AddMonoidHom.id N.obj.obj.V)))) inferInstance inferInstance

/-- The module of locally constant functions has no `1`-cocycles but coboundaries, for the
action of its underlying discrete `G`-module. -/
lemma vanishesOne_locallyConstantGModule (B : Type (max u v)) [AddCommGroup B] :
    letI := carrierAction (locallyConstantGModule G B)
    VanishesOne G (locallyConstantGModule G B).obj.obj.V :=
  vanishesOne_lcFun

/-- The module of locally constant functions has no `2`-cocycles but coboundaries, for the
action of its underlying discrete `G`-module. -/
lemma vanishesTwo_locallyConstantGModule (B : Type (max u v)) [AddCommGroup B] :
    letI := carrierAction (locallyConstantGModule G B)
    VanishesTwo G (locallyConstantGModule G B).obj.obj.V :=
  vanishesTwo_lcFun

/-- `H ¹(G, I) = 0` for the module `I` of locally constant functions. -/
lemma isZero_continuousGroupCohomology_one_locallyConstantGModule (B : Type (max u v))
    [AddCommGroup B] :
    IsZero (continuousGroupCohomology.{u, v} G 1 (locallyConstantGModule G B)) := by
  refine isZero_continuousGroupCohomology_one_of_forall_isCoboundary _ fun c hc hcoc ↦ ?_
  obtain ⟨x, hx⟩ := vanishesOne_locallyConstantGModule B c hc hcoc
  exact ⟨x, fun g ↦ congrFun hx g⟩

/-- **`H ¹(G, M) = 0` gives the vanishing of locally constant `1`-cocycles.** -/
theorem vanishesOne_of_isZero_continuousGroupCohomology_one (N : ContinuousGModule.{u, max u v} G)
    (h : IsZero (continuousGroupCohomology.{u, v} G 1 N)) :
    letI := carrierAction N
    VanishesOne G N.obj.obj.V := by
  let S := coinducedSeq N
  have hS : S.ShortExact := shortExact_coinducedSeq N
  obtain ⟨hi, -, hpi, hex⟩ := shortExact_underlying hS
  let := carrierAction S.X₁
  let := carrierAction S.X₂
  let := carrierAction S.X₃
  exact vanishesOne_of_exists_invariant_lift (homAdd S.f) (homAdd S.g) (homAdd_smul S.f)
    (homAdd_smul S.g) hi hpi hex (vanishesOne_locallyConstantGModule _)
    (fun y hy ↦ exists_invariant_lift_of_isZero_continuousGroupCohomology_one hS h y hy)

/-- **`H ²(G, M) = 0` gives the vanishing of locally constant `2`-cocycles**: for a profinite
group `G` and a discrete `G`-module `M` with `H ²(G, M) = 0`, every locally constant `2`-cocycle
`G × G → M` is the coboundary of a locally constant `1`-cochain. -/
theorem vanishesTwo_of_isZero_continuousGroupCohomology_two (M : ContinuousGModule.{u, max u v} G)
    (h : IsZero (continuousGroupCohomology.{u, v} G 2 M)) :
    letI := carrierAction M
    VanishesTwo G M.obj.obj.V := by
  let S := coinducedSeq M
  have hS : S.ShortExact := shortExact_coinducedSeq M
  have hI : IsZero (continuousGroupCohomology.{u, v} G 1 S.X₂) :=
    isZero_continuousGroupCohomology_one_locallyConstantGModule _
  have hQ : IsZero (continuousGroupCohomology.{u, v} G 1 S.X₃) :=
    ((cohomologyDelta.{u, v} (G := G)).exact_δ₁ hS 1).isZero_X₂ (hI.eq_of_src _ _)
      (h.eq_of_tgt _ _)
  obtain ⟨hi, hp, hpi, hex⟩ := shortExact_underlying hS
  let := carrierAction S.X₁
  let := carrierAction S.X₂
  let := carrierAction S.X₃
  exact vanishesTwo_of_vanishesOne_quotient (homAdd S.f) (homAdd S.g) (homAdd_smul S.f)
    (homAdd_smul S.g) hi hp hpi hex (hasOpenStabilizers_carrier S.X₂)
    (vanishesTwo_locallyConstantGModule _)
    (vanishesOne_of_isZero_continuousGroupCohomology_one S.X₃ hQ)

end Stacks.GroupCohomology

end
