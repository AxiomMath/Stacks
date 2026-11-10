module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.Defs

/-!
# `Proj S` over `Spec S₀`: separatedness, the structure morphism, the valuative criterion

Let `S = ⨁_{d ≥ 0} 𝒜 d` be a graded ring and `Proj 𝒜` its homogeneous spectrum as a scheme.

* `Proj 𝒜` is separated: this is Mathlib's instance `Scheme.IsSeparated (Proj 𝒜)`, which
  carries [Stacks, Tag 01MC].
* The canonical morphism `Proj.toSpecZero 𝒜 : Proj 𝒜 ⟶ Spec 𝒜₀` is, on underlying points, the map
  `𝔭 ↦ 𝔭 ∩ 𝒜₀`: the inclusion of the homogeneous spectrum into `Spec S` followed by the map
  `Spec S → Spec 𝒜₀` induced by `𝒜₀ ⊆ S`.
* If `S` is a finitely generated `𝒜₀`-algebra, `Proj 𝒜 ⟶ Spec 𝒜₀` satisfies both the existence
  and the uniqueness parts of the valuative criterion.

## Main results

* `Stacks.AlgebraicGeometry.ProjToSpecZero.toSpecZero_base_eq` — the structure morphism
  `Proj 𝒜 ⟶ Spec 𝒜₀` is `𝔭 ↦ 𝔭 ∩ 𝒜₀` on points.
* `Stacks.AlgebraicGeometry.ProjToSpecZero.valuativeCriterion_toSpecZero` — the valuative
  criterion for `Proj 𝒜 ⟶ Spec 𝒜₀` when `S` is of finite type over `𝒜₀`.

## References

* [Stacks Project, Tag 01MC](https://stacks.math.columbia.edu/tag/01MC)
* [Stacks Project, Tag 01ME](https://stacks.math.columbia.edu/tag/01ME)
* [Stacks Project, Tag 01MF](https://stacks.math.columbia.edu/tag/01MF)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Stacks.AlgebraicGeometry.ProjToSpecZero

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- Every point of `Proj 𝒜` lies in the standard open `D₊(1) = Proj 𝒜`. -/
theorem mem_basicOpen_one (x : AlgebraicGeometry.Proj 𝒜) : x ∈ Proj.basicOpen 𝒜 1 := by
  rw [Proj.basicOpen_one]
  trivial

/-- The structure morphism `Proj 𝒜 ⟶ Spec 𝒜₀` sends the homogeneous prime `𝔭` to `𝔭 ∩ 𝒜₀`. -/
theorem toSpecZero_apply (x : AlgebraicGeometry.Proj 𝒜) :
    Proj.toSpecZero 𝒜 x =
      PrimeSpectrum.comap (algebraMap (𝒜 0) A) (_root_.Proj.toSpec 𝒜 x) := by
  have key : Scheme.forgetToLocallyRingedSpace.map (Proj.basicOpenToSpec 𝒜 1) =
      ProjectiveSpectrum.Proj.toSpec 𝒜 1 := by
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [Category.assoc, ← Spec.map_comp]
    rfl
  have hz : ((AlgebraicGeometry.Proj 𝒜).isoOfEq (Proj.basicOpen_one 𝒜)).inv
      ((AlgebraicGeometry.Proj 𝒜).topIso.inv x) = ⟨x, mem_basicOpen_one 𝒜 x⟩ := by
    apply Subtype.ext
    change (Proj.basicOpen 𝒜 1).ι (((AlgebraicGeometry.Proj 𝒜).isoOfEq
      (Proj.basicOpen_one 𝒜)).inv ((AlgebraicGeometry.Proj 𝒜).topIso.inv x)) = x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Scheme.isoOfEq_inv_ι,
      Scheme.toIso_inv_ι]
    rfl
  have hb : Proj.basicOpenToSpec 𝒜 1 ⟨x, mem_basicOpen_one 𝒜 x⟩ =
      (ProjectiveSpectrum.Proj.toSpec 𝒜 1).base ⟨x, mem_basicOpen_one 𝒜 x⟩ := by
    rw [← key]
    rfl
  simp only [Proj.toSpecZero, Scheme.Hom.comp_apply]
  rw [hz, hb]
  refine PrimeSpectrum.ext (Ideal.ext fun a => ?_)
  change fromZeroRingHom 𝒜 (Submonoid.powers 1) a ∈
      ((ProjectiveSpectrum.Proj.toSpec 𝒜 1).base ⟨x, mem_basicOpen_one 𝒜 x⟩).asIdeal ↔
    (a : A) ∈ x.asHomogeneousIdeal
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply 𝒜 ⟨x, mem_basicOpen_one 𝒜 x⟩
    ⟨0, a, ⟨1, SetLike.one_mem_graded 𝒜⟩, Submonoid.one_mem _⟩

/-- **The canonical morphism `Proj 𝒜 ⟶ Spec 𝒜₀`** is `Proj.toSpecZero 𝒜`, glued from the ring
maps `𝒜₀ → S_(f)` on the standard opens. On underlying topological spaces it is the map of the
homogeneous spectrum: the inclusion `Proj 𝒜 ⊆ Spec S` followed by `Spec S → Spec 𝒜₀` induced by
`𝒜₀ ⊆ S`, i.e. `𝔭 ↦ 𝔭 ∩ 𝒜₀`. -/
@[stacks 01ME "the canonical morphism Proj S → Spec S₀, equal on points to 𝔭 ↦ 𝔭 ∩ S₀"]
theorem toSpecZero_base_eq :
    ⇑(Proj.toSpecZero 𝒜) =
      PrimeSpectrum.comap (algebraMap (𝒜 0) A) ∘ _root_.Proj.toSpec 𝒜 :=
  funext (toSpecZero_apply 𝒜)

/-- **The valuative criterion for `Proj 𝒜 ⟶ Spec 𝒜₀`.** If `S` is finitely generated as an
`𝒜₀`-algebra, then for every valuation ring `O` with fraction field `K` and every commutative
square `Spec K ⟶ Proj 𝒜`, `Spec O ⟶ Spec 𝒜₀`, there exists a lift `Spec O ⟶ Proj 𝒜`
(existence) and it is unique (uniqueness, from separatedness). -/
@[stacks 01MF "existence and uniqueness parts of the valuative criterion for Proj S → Spec S₀"]
theorem valuativeCriterion_toSpecZero [Algebra.FiniteType (𝒜 0) A] :
    ValuativeCriterion (Proj.toSpecZero 𝒜) :=
  ValuativeCriterion.iff.mpr
    ⟨Proj.valuativeCriterion_existence 𝒜, IsSeparated.valuativeCriterion _⟩

end Stacks.AlgebraicGeometry.ProjToSpecZero

end
