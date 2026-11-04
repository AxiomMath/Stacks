module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.CoinducedEffacement
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ModuleBaseChange
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleCofinality
public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Cohomology of a subgroup is effaced by coinduction from the big group

Let `φ : G → Γ` be a continuous homomorphism of compact groups which is a topological embedding,
`R` a ring and `M` a continuous discrete `R`-`Γ`-module. Every class of positive degree in
`Hⁿ⁺¹(G, M)` (`M` restricted to `G` along `φ`) dies in `Hⁿ⁺¹(G, Coind_U M)` for some open normal
subgroup `U` of `Γ`, where `Coind_U M` is the `Γ`-module of functions `Γ ⧸ U → M`
(`Stacks.ContinuousCohomology.coind`), restricted to `G`.

## Main definitions

* `Stacks.ContinuousCohomology.coindRestrictMap`: the map `Coind_V M → Coind_U M`, `f ↦ f ∘ s`,
  for a `G`-equivariant map `s : Γ ⧸ U → G ⧸ V`.

## Main results

* `Stacks.ContinuousCohomology.coindUnit_comp_coindRestrictMap`: `f ↦ f ∘ s` carries the
  constant functions to the constant functions.
* `Stacks.ContinuousCohomology.exists_map_res_coindUnit_eq_zero`: every class of
  `Hⁿ⁺¹(G, res M)` dies in `Hⁿ⁺¹(G, res Coind_U M)` for some open normal subgroup `U` of `Γ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe u v w

namespace Stacks.ContinuousCohomology

variable (R : Type u) [Ring R] {G Γ : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] (φ : G →ₜ* Γ)

/-- **Composition with an equivariant map of coset spaces.** For open subgroups `V ≤ G`, `U ≤ Γ`
and a map `s : Γ ⧸ U → G ⧸ V` equivariant for `G` acting on `Γ ⧸ U` through `φ`, the map
`f ↦ f ∘ s` from `Coind_V (res M)` to `res (Coind_U M)`, a map of `G`-modules. -/
def coindRestrictMap (V : OpenSubgroup G) (U : OpenSubgroup Γ)
    (s : Γ ⧸ (U : Subgroup Γ) → G ⧸ (V : Subgroup G))
    (hs : ∀ (g : G) (x : Γ ⧸ (U : Subgroup Γ)), s (φ g • x) = g • s x)
    (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R Γ) :
    (coind.{u, v, w} R V).obj ((continuousModuleRes.{u, v, max u v w} R φ).obj M) ⟶
      (continuousModuleRes.{u, v, max u v w} R φ).obj ((coind.{u, v, w} R U).obj M) :=
  (Stacks.GroupCohomology.homEquiv R G _ _).symm
    ⟨LinearMap.funLeft R _ s, fun g f ↦ by
      funext x
      change (M.obj.obj.ρ (φ g)).hom (f (g⁻¹ • s x)) =
        (M.obj.obj.ρ (φ g)).hom (f (s ((φ g)⁻¹ • x)))
      rw [← map_inv, hs]⟩

/-- `f ↦ f ∘ s` carries the constant functions to the constant functions. -/
theorem coindUnit_comp_coindRestrictMap (V : OpenSubgroup G) (U : OpenSubgroup Γ)
    (s : Γ ⧸ (U : Subgroup Γ) → G ⧸ (V : Subgroup G))
    (hs : ∀ (g : G) (x : Γ ⧸ (U : Subgroup Γ)), s (φ g • x) = g • s x)
    (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R Γ) :
    coindUnit.{u, v, w} R V ((continuousModuleRes.{u, v, max u v w} R φ).obj M) ≫
        coindRestrictMap R φ V U s hs M =
      (continuousModuleRes.{u, v, max u v w} R φ).map (coindUnit.{u, v, w} R U M) := by
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply Action.hom_ext
  apply ModuleCat.hom_ext; rfl

attribute [local instance] HasDerivedCategory.standard

variable [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace Γ]

/-- **The cohomology of `G` with coefficients in a `Γ`-module is effaced by coinduction from an
open normal subgroup of `Γ`**, for `φ : G → Γ` a topological embedding of profinite groups: every
class of `Hⁿ⁺¹(G, res M)` dies in `Hⁿ⁺¹(G, res Coind_U M)` for some open normal `U ≤ Γ`. -/
theorem exists_map_res_coindUnit_eq_zero (hφ : Topology.IsInducing φ) (n : ℕ)
    (M : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R Γ)
    (c : ((invariantsDelta.{u, v, w} R (G := G)).functor (n + 1)).obj
      ((continuousModuleRes.{u, v, max u v w} R φ).obj M)) :
    ∃ U : OpenNormalSubgroup Γ, ((invariantsDelta.{u, v, w} R (G := G)).functor (n + 1)).map
      ((continuousModuleRes.{u, v, max u v w} R φ).map
        (coindUnit.{u, v, w} R U.toOpenSubgroup M)) c = 0 := by
  obtain ⟨V, hV⟩ := exists_map_coindUnit_eq_zero.{u, v, w} R n _ c
  obtain ⟨V', hV'⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one V.isOpen V.one_mem
  obtain ⟨O, hO, hpre⟩ := hφ.isOpen_iff.1 V'.isOpen
  have h1O : (1 : Γ) ∈ O := by
    simpa using (show (1 : G) ∈ φ ⁻¹' O by rw [hpre]; exact V'.one_mem)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hO h1O
  refine ⟨U, ?_⟩
  let : MulAction G (Γ ⧸ (U.toOpenSubgroup : Subgroup Γ)) :=
    MulAction.compHom _ φ.toMonoidHom
  have hfix : ∀ (g : G) (a : Γ ⧸ (U.toOpenSubgroup : Subgroup Γ)), g • a = a →
      ∀ y : G ⧸ (V : Subgroup G), g • y = y := by
    intro g a ha y
    induction a using QuotientGroup.induction_on with
    | H γ =>
      have hga : φ g • (γ : Γ ⧸ (U.toOpenSubgroup : Subgroup Γ)) = γ := ha
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul] at hga
      have hmem : (φ g)⁻¹ ∈ (U : Subgroup Γ) := by
        simpa [mul_assoc] using (U.isNormal' : (U : Subgroup Γ).Normal).conj_mem _ hga γ
      have hgV' : g ∈ (V' : Subgroup G) := by
        have : g⁻¹ ∈ φ ⁻¹' O := by
          change φ g⁻¹ ∈ O
          rw [map_inv]
          exact hU hmem
        rw [hpre] at this
        simpa using this
      induction y using QuotientGroup.induction_on with
      | H h =>
        rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
        apply hV'
        have h2 : h⁻¹ * (g⁻¹ * h) ∈ (V' : Subgroup G) := by
          simpa [mul_assoc] using (V'.isNormal' : (V' : Subgroup G).Normal).conj_mem _
            ((V' : Subgroup G).inv_mem hgV') h⁻¹
        rwa [mul_inv_rev, mul_assoc]
  obtain ⟨s, hs⟩ := MulAction.exists_smul_equivariant_of_forall_smul_eq
    (A := Γ ⧸ (U.toOpenSubgroup : Subgroup Γ)) (Y := G ⧸ (V : Subgroup G))
    ((1 : G) : G ⧸ (V : Subgroup G)) hfix
  rw [← coindUnit_comp_coindRestrictMap R φ V U.toOpenSubgroup s hs M, Functor.map_comp,
    ConcreteCategory.comp_apply, hV, map_zero]

end Stacks.ContinuousCohomology

end
