module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.DegreeTwoCocycles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.LocallyConstantGModule
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.TorsionCochainVanishing

/-!
# Vanishing of the continuous cohomology of a torsion module above degree one

For a profinite group `G` satisfying `Stacks.GroupCohomology.HasPrimeBase` and a torsion discrete
`G`-module `M`, the continuous cohomology groups `H ^q(G, M)` of Stacks 04JR vanish for every
`q ≥ 2`.

## Main definitions

* `Stacks.GroupCohomology.carrierAction`: the action of `G` on the carrier of a discrete
  `G`-module, written as a scalar multiplication.

## Main results

* `Stacks.GroupCohomology.isZero_continuousGroupCohomology_two_of_vanishesTwo`: if every locally
  constant `2`-cocycle with values in the carrier is a coboundary, then `H ²(G, M) = 0`.
* `Stacks.GroupCohomology.isZero_continuousGroupCohomology_of_torsion`: **the vanishing in every
  degree `q ≥ 2`.**

## Implementation notes

Degree two is the comparison
`Stacks.GroupCohomology.isZero_continuousGroupCohomology_two_of_forall_isCoboundary`, whose
hypothesis is exactly `Stacks.GroupCohomology.VanishesTwo` written with the action of the module
spelled out, so the cochain statement
`Stacks.GroupCohomology.vanishesTwo_of_isTorsion` discharges it.

Higher degrees are dimension shifting, which needs a *torsion* injective object to shift along:
the module of locally constant functions `G → A` is injective when `A` is divisible
(`Stacks.GroupCohomology.injective_locallyConstantGModule`) and torsion when `A` is
(`Stacks.GroupCohomology.exists_nsmul_eq_zero_lcFun`), and a torsion abelian group embeds in a
torsion divisible one (`Stacks.GroupCohomology.toTorsionHull`). The cokernel of such an embedding
is torsion because the underlying map of an epimorphism of discrete modules is surjective, so the
induction hypothesis applies to it, and
`Stacks.GroupCohomology.isZero_rightDerivedPlus_succ_of_injective` steps the degree up.

## References

* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8): part (2).
* [Stacks Project, Tag 04JR](https://stacks.math.columbia.edu/tag/04JR): the cohomology groups.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits groupCohomology Stacks.ContinuousCohomology

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.GroupCohomology

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The action of `G` on the carrier of a discrete `G`-module**, written as a scalar
multiplication. -/
@[instance_reducible]
def carrierAction (M : ContinuousGModule.{u, v} G) : DistribMulAction G M.obj.obj.V where
  smul g m := (M.obj.obj.ρ g).asHom.hom m
  one_smul m := by
    change (M.obj.obj.ρ 1).asHom.hom m = m
    rw [map_one]
    rfl
  mul_smul g h m := by
    change (M.obj.obj.ρ (g * h)).asHom.hom m =
      (M.obj.obj.ρ g).asHom.hom ((M.obj.obj.ρ h).asHom.hom m)
    rw [map_mul]
    rfl
  smul_zero g := map_zero _
  smul_add g m n := map_add _ _ _

omit [IsTopologicalGroup G] in
/-- Under `carrierAction M`, `g • m` is the action of `ρ g` on `m`. -/
lemma carrierAction_smul (M : ContinuousGModule.{u, v} G) (g : G) (m : M.obj.obj.V) :
    letI := carrierAction M
    g • m = (M.obj.obj.ρ g).asHom.hom m := rfl

omit [IsTopologicalGroup G] in
/-- The carrier of a discrete `G`-module has open stabilizers. -/
theorem hasOpenStabilizers_carrier (M : ContinuousGModule.{u, v} G) :
    letI := carrierAction M
    HasOpenStabilizers G M.obj.obj.V :=
  fun m ↦ isOpen_stabilizer ℤ G M m

/-- If the carrier of a discrete `G`-module `M` satisfies `VanishesTwo`, then the derived-functor
group `H ²(G, M)` vanishes. -/
theorem isZero_continuousGroupCohomology_two_of_vanishesTwo (M : ContinuousGModule.{u, max u v} G)
    (hM : letI := carrierAction M; VanishesTwo G M.obj.obj.V) :
    IsZero (continuousGroupCohomology.{u, v} G 2 M) :=
  isZero_continuousGroupCohomology_two_of_forall_isCoboundary M (fun d hdlc hdcoc ↦ by
    obtain ⟨x, hxlc, hx⟩ := hM d hdlc hdcoc
    exact ⟨x, hxlc, fun g₁ g₂ ↦ congrFun hx (g₁, g₂)⟩)

/-- For a profinite group `G` with `HasPrimeBase G`, `H ^q(G, M)` vanishes for every `q ≥ 2` and
every torsion discrete `G`-module `M`. -/
theorem isZero_continuousGroupCohomology_of_torsion [CompactSpace G]
    [TotallyDisconnectedSpace G] (hbase : HasPrimeBase G) :
    ∀ (q : ℕ), 2 ≤ q → ∀ M : ContinuousGModule.{u, max u v} G,
      (∀ m : M.obj.obj.V, ∃ n : ℕ, 0 < n ∧ n • m = 0) →
      IsZero (continuousGroupCohomology.{u, v} G q M) := by
  intro q
  induction q with
  | zero => intro hq; omega
  | succ n ih =>
      intro hq M hM
      rcases Nat.lt_or_ge n 2 with hn | hn
      · have hn1 : n = 1 := by omega
        subst hn1
        refine isZero_continuousGroupCohomology_two_of_vanishesTwo M ?_
        let := carrierAction M
        exact vanishesTwo_of_isTorsion hbase (hasOpenStabilizers_carrier M) hM
      · have htor : IsAddTorsion M.obj.obj.V := fun m ↦ isOfFinAddOrder_iff_nsmul_eq_zero.2 (hM m)
        set A : Type (max u v) := ↥(torsionHull M.obj.obj.V) with hAdef
        have hAtor : ∀ a : A, ∃ k : ℕ, 0 < k ∧ k • a = 0 := fun a ↦
          isOfFinAddOrder_iff_nsmul_eq_zero.1 (isAddTorsion_torsionHull M.obj.obj.V a)
        set J : ContinuousGModule.{u, max u v} G := locallyConstantGModule G A with hJdef
        set f : M ⟶ J := orbitMap M (toTorsionHull M.obj.obj.V htor) with hfdef
        have : Mono f := mono_orbitMap M _ (injective_toTorsionHull M.obj.obj.V htor)
        have : Injective J := injective_locallyConstantGModule G A
        set S : ShortComplex (ContinuousGModule.{u, max u v} G) :=
          ShortComplex.mk f (cokernel.π f) (cokernel.condition f) with hSdef
        have hS : S.ShortExact := ShortComplex.ShortExact.mk'
          (ShortComplex.exact_of_g_is_cokernel S (cokernelIsCokernel f)) inferInstance
          inferInstance
        have hQtor : ∀ m : S.X₃.obj.obj.V, ∃ k : ℕ, 0 < k ∧ k • m = 0 := by
          intro m
          have hSu : (S.map (continuousGModuleUnderlying.{u, max u v} G)).ShortExact :=
            hS.map_of_exact _
          have hgsurj : Function.Surjective ((cokernel.π f).hom.hom.hom.hom :
              J.obj.obj.V →ₗ[ℤ] S.X₃.obj.obj.V) := hSu.moduleCat_surjective_g
          obtain ⟨z, hz⟩ := hgsurj m
          obtain ⟨k, hk, hkz⟩ := exists_nsmul_eq_zero_lcFun hAtor z
          refine ⟨k, hk, ?_⟩
          have hz0 : (k • z : J.obj.obj.V) = 0 := hkz
          rw [← hz, ← map_nsmul, hz0, map_zero]
        exact isZero_rightDerivedPlus_succ_of_injective
          (continuousGModuleInvariants.{u, max u v} G) hS inferInstance n (ih (by omega) S.X₃ hQtor)

end Stacks.GroupCohomology

end
