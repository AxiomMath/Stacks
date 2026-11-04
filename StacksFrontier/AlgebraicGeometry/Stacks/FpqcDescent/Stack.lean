module

public import StacksFrontier.AlgebraicGeometry.Stacks.FpqcDescent.ChartEffective
public import StacksFrontier.AlgebraicGeometry.Quot.QuotFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.CoveringRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.FinerTopologies
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionAffine
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafConditionDisjointUnion
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafConditionSmallEtale

/-!
# Algebraic stacks with quasi-affine diagonal satisfy fpqc descent

This file proves **Stacks 0GRH**: an algebraic stack `𝒳` over `S` whose diagonal is quasi-affine
is a stack for the fpqc topology of the big fppf site over `S`.

## Main results

* `AlgebraicGeometry.Stack.effectiveSieve_mem_topology`: for a descent datum relative to an fpqc
  covering sieve, the sieve of arrows along which it becomes effective is an fppf covering sieve.
* `AlgebraicGeometry.Stack.isStack_fpqc_of_isQuasiAffineHom_diagonal`: **Stacks 0GRH**.

## Implementation notes

The proof is the one of the source. The morphism presheaves of `𝒳` are fpqc sheaves by
`AlgebraicGeometry.Stack.isMorSheaf_fpqc_of_isAlgebraicStack`, so a descent datum relative to an
fpqc covering is effective as soon as it is effective fppf locally
(`CategoryTheory.Functor.SieveDescentDatum.isEffective_of_effectiveSieve_mem`), `𝒳` being an
fppf stack. That it is effective fppf locally is proved by refining the covering Zariski locally
to a single surjective flat morphism of affine schemes (the finite disjoint union of a finite
affine refinement), which lies in the effective sieve because `𝒳` is an fppf stack, and then by
the geometric step `AlgebraicGeometry.Stack.exists_smooth_surjective_isEffective_pullback`,
applied to the datum glued from the effective objects, which provides a smooth surjective
morphism in the effective sieve.

## References

* [Stacks Project, Tag 0GRH](https://stacks.math.columbia.edu/tag/0GRH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- The big fppf topology over `S` is coarser than the fpqc topology. -/
alias bigFppfOver_topology_le_fpqc :=
  AlgebraicGeometry.Space.bigFppfOver_topology_le_fpqcTopology

/-- An algebraic stack has effective descent for the big fppf topology. -/
private theorem hasEffectiveDescent_of_isAlgebraicStack
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    [𝒳.val.p.IsFibered] (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val) :
    HasEffectiveDescent 𝒳.val.p (BigFppfOver.topology B S hS) := by
  obtain ⟨-, ⟨hstack, -⟩, -⟩ := h𝒳
  exact hstack.hasEffectiveDescent

/-- **The effective sieve of an fpqc descent datum is an fppf covering.** -/
theorem effectiveSieve_mem_topology
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) [𝒳.val.p.IsFibered]
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hΔ : IsQuasiAffineHom B S hS (diagonal.{u, u, u} B S hS 𝒳))
    {U : BigFppfOver B S hS} {R : Sieve U}
    (hR : R ∈ (Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck U)
    (D : SieveDescentDatum 𝒳.val.p R) :
    D.effectiveSieve ∈ BigFppfOver.topology B S hS U := by
  set F := BigFppfOver.toScheme B S hS with hF
  have hp := 𝒳.isFiberedInGroupoids
  have hmor := fun V (x y : 𝒳.val.p.Fiber V) =>
    isMorSheaf_fpqc_of_isAlgebraicStack B S hS 𝒳 h𝒳 V x y
  have hJ := hasEffectiveDescent_of_isAlgebraicStack h𝒳
  have hRE : R ≤ D.effectiveSieve := D.le_effectiveSieve hJ
  obtain ⟨Pres, hPres, hle⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨Jt, Y, u, m, W, w, hYaff, -, hZar, hWaff, hwflat, hWfpqc, hfac⟩ :=
    BigFppfOver.exists_zariski_affine_flat_refinement Pres hPres
  have hZ : Sieve.generate (Presieve.ofArrows Y u) ∈ BigFppfOver.topology B S hS U := by
    refine BigFppfOver.sieve_generate_ofArrows_mem_topology Y u ?_
    rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hZar
    exact Scheme.zariskiPrecoverage_le_fppfPrecoverage _ hZar
  refine (BigFppfOver.topology B S hS).transitive hZ _ (fun V h hh => ?_)
  obtain ⟨Z, k, _, ⟨j⟩, rfl⟩ := hh
  rw [Sieve.pullback_comp]
  refine (BigFppfOver.topology B S hS).pullback_stable k ?_
  -- over `Y j`: the disjoint union of the finite affine refinement
  have hc : IsColimit (Cofan.mk (∐ W j) (Sigma.ι (W j))) := coproductIsCoproduct (W j)
  obtain ⟨e, he⟩ := BigFppfOver.exists_iso_sigma_of_isColimit_cofan (W j) hc
  set q := Cofan.IsColimit.desc hc (w j) with hq
  have hqdesc : F.map q = e.inv ≫ Sigma.desc fun i ↦ F.map (w j i) := by
    rw [← Category.id_comp (F.map q), ← e.inv_hom_id, Category.assoc]
    congr 1
    refine Sigma.hom_ext _ _ fun i ↦ ?_
    rw [← Category.assoc, he i, Sigma.ι_desc, ← Functor.map_comp]
    exact congrArg F.map (Cofan.IsColimit.fac hc (w j) i)
  have hWaff' (i : Fin (m j)) : IsAffine (F.obj (W j i)) := hWaff j i
  have hTaff : IsAffine (F.obj (Cofan.mk (∐ W j) (Sigma.ι (W j))).pt) := IsAffine.of_isIso e.inv
  have hflat : Flat (F.map q) := by
    have : Flat (Sigma.desc fun i ↦ F.map (w j i)) := by
      have hw (i : Fin (m j)) : Flat (F.map (w j i)) := hwflat j i
      infer_instance
    rw [hqdesc]
    infer_instance
  have hmem := hWfpqc j
  rw [Precoverage.mem_comap_iff, Presieve.map_ofArrows] at hmem
  obtain ⟨-, hfl⟩ := hmem
  obtain ⟨hjs, -⟩ := (Scheme.ofArrows_mem_precoverage_iff _).mp hfl
  have hsurj : Surjective (F.map q) := by
    have : Surjective (Sigma.desc fun i ↦ F.map (w j i)) := by
      refine ⟨fun y ↦ ?_⟩
      obtain ⟨i, z, hzy⟩ := hjs y
      refine ⟨Sigma.ι (fun i ↦ F.obj (W j i)) i z, ?_⟩
      rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
      exact hzy
    rw [hqdesc]
    infer_instance
  have hYaff' := hYaff j
  have hqc : QuasiCompact (F.map q) := inferInstance
  -- the disjoint union lies in the effective sieve, `𝒳` being an fppf stack
  have hqE : D.effectiveSieve (q ≫ u j) := by
    refine D.effectiveSieve_of_isEffective_pullback _ (hJ _ ?_ (D.pullback (q ≫ u j)))
    refine (BigFppfOver.topology B S hS).superset_covering ?_
      (BigFppfOver.sieve_generate_ofArrows_mem_topology (W j) (Sigma.ι (W j))
        (BigFppfOver.ofArrows_cofan_inj_mem_fppfPrecoverage (W j) hc))
    rw [Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    show R.arrows (Sigma.ι (W j) i ≫ q ≫ u j)
    obtain ⟨T, f, hf, v, hv⟩ := hfac j i
    have hι : Sigma.ι (W j) i ≫ q = w j i := Cofan.IsColimit.fac hc (w j) i
    rw [← Category.assoc, hι, hv]
    exact R.downward_closed (hle _ _ hf) v
  -- the geometric step, for the datum glued from the effective objects
  obtain ⟨W₀, w₀, hsm, hsu, heff⟩ := exists_smooth_surjective_isEffective_pullback 𝒳 h𝒳 hΔ
    (D.coarseGlueDatum hp hmor hR) (u j) (f := q) hqE
  obtain ⟨a, ⟨A⟩⟩ := (D.coarseGlueDatum hp hmor hR).effectiveSieve_of_isEffective_pullback _ heff
  have hw₀ : D.effectiveSieve (w₀ ≫ u j) :=
    ⟨a, D.nonempty_effectiveAlong_of_coarseGlueDatum hp hmor hR hRE A⟩
  -- a smooth surjective morphism generates an fppf covering sieve
  refine (BigFppfOver.topology B S hS).superset_covering ?_
    (BigFppfOver.sieve_generate_ofArrows_mem_topology (fun _ : PUnit.{1} => W₀) (fun _ => w₀) ?_)
  · rw [Sieve.generate_le_iff]
    rintro _ _ ⟨⟩
    exact hw₀
  · rw [Presieve.ofArrows_pUnit]
    have := hsm
    have := hsu
    exact (F.map w₀).singleton_mem_fppfPrecoverage

/-- **Stacks 0GRH.** An algebraic stack `𝒳` over `S` with quasi-affine diagonal satisfies descent
for fpqc coverings: it is a stack for the fpqc topology of the big fppf site over `S`. -/
@[stacks 0GRH]
theorem isStack_fpqc_of_isQuasiAffineHom_diagonal
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳.val)
    (hΔ : IsQuasiAffineHom B S hS (diagonal.{u, u, u} B S hS 𝒳)) :
    𝒳.val.p.IsStack
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) := by
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have hp := 𝒳.isFiberedInGroupoids
  have hmor := fun V (x y : 𝒳.val.p.Fiber V) =>
    isMorSheaf_fpqc_of_isAlgebraicStack B S hS 𝒳 h𝒳 V x y
  have hJ := hasEffectiveDescent_of_isAlgebraicStack h𝒳
  refine ⟨inferInstance, hmor, fun U R hR D => ?_⟩
  exact D.isEffective_of_effectiveSieve_mem hp hmor hR bigFppfOver_topology_le_fpqc hJ
    (effectiveSieve_mem_topology 𝒳 h𝒳 hΔ hR D)

end AlgebraicGeometry.Stack

end
