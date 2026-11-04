module

public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety
public import StacksCore.Tactic.StacksAttribute

/-!
# The projective transformation attached to an endomorphism

An endomorphism `g` of a vector space `V` induces a graded homomorphism `Sym g` of the
symmetric algebra, hence a morphism of projective spaces defined on the open

`𝐏(V) ⊇ U(g) --r_g--> 𝐏(V)`,

where `U(g)` is the complement of the linear subspace cut out by the image of `g`, that is of
`𝐏(Coker g) ⊆ 𝐏(V)`, and the image of `r_g` is the linear subspace cut out by the kernel of
`g`, that is `𝐏(Im g) ⊆ 𝐏(V)`. On the closed point cut out by a nonzero functional `f` the
morphism is `f ↦ f ∘ g`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.endDomain`: the open `U(g)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection`: the morphism `r_g`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.coe_endDomain`: `U(g)` is the complement of the
  linear subspace cut out by `LinearMap.range g`, namely of `𝐏(Coker g)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_eq_linearFunctionalPoint`: on the
  point cut out by a functional `f`, the morphism `r_g` gives the point cut out by `f ∘ g`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_endProjection_subset` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.exists_endProjection_eq`: the image of `r_g` lies
  in the linear subspace cut out by `LinearMap.ker g`, namely in `𝐏(Im g)`, and over an
  algebraically closed field every closed point of that subspace is attained.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.endDomain_smul` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.endProjection_smul_apply`: the open and the
  morphism depend only on the class of `g` up to a unit scalar.

## Implementation notes

`U(g)` is `Stacks.AlgebraicGeometry.ProjShared.mapDomain` and `r_g` is
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` of the graded homomorphism
`SymPow.gradedSymAlgMap g`, exactly as the linear projection
`AlgebraicGeometry.ProjectiveSpaceOfModule.projection` away from a linear subspace is built
from the inclusion of a submodule. For an invertible `g` the open is all of `𝐏(V)` and `r_g` is
the action of `g` by a scheme automorphism, which is
`AlgebraicGeometry.ProjectiveSpaceOfModule.mapDomain_eq_top` together with
`AlgebraicGeometry.ProjectiveSpaceOfModule.mapDomain_ι_comp_map`.

Relative to the parameter space `𝐏 = 𝐏(End(V)ᵛ)` and the rational map
`𝐏 × 𝐏(V) ⊇ U(ψ) → 𝐏 × 𝐏(V)` attached to `ψ : V ⊗ 𝒪_𝐏 → V ⊗ 𝒪_𝐏(1)`, `endDomain` is the fibre
of `U(ψ)` and `endProjection` the fibre of `r_ψ` over the point `[g]` of `𝐏`.

## References

* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u v

variable (k : Type u) (V : Type v) [Field k] [AddCommGroup V] [Module k V]

/-- The open `U(g)` on which the projective transformation attached to an endomorphism `g` of
`V` is defined: the domain of definition of the morphism of projective spectra induced by
`Sym g`. -/
@[stacks 0B2W "the open U(ψ) over the point [g] of the parameter space, i.e. U(g)"]
public abbrev endDomain (g : V →ₗ[k] V) : (projectiveSpaceOfModule k V).Opens :=
  mapDomain (fun n => SymPow.symmetricPower n k V) (fun n => SymPow.symmetricPower n k V)
    (SymPow.gradedSymAlgMap g)

/-- The projective transformation `r_g : 𝐏(V) ⊇ U(g) → 𝐏(V)` attached to an endomorphism `g`
of `V`: the morphism of projective spectra induced by `Sym g` on its domain of definition. -/
@[stacks 0B2W "the morphism r_ψ over the point [g] of the parameter space, i.e. r_g"]
public def endProjection (g : V →ₗ[k] V) :
    (endDomain k V g).toScheme ⟶ projectiveSpaceOfModule k V :=
  mapHom _ _ (SymPow.gradedSymAlgMap g)

/-- The image under `Sym g` of a positive-degree symmetric power of `V` lands in the homogeneous
prime of any point at which every degree-one form in the image of `g` vanishes. -/
private theorem symAlgMap_mem_of_range_le (g : V →ₗ[k] V) (q : projectiveSpaceOfModule k V)
    (h : LinearMap.range g ≤ pointSubmodule k V q) (d : ℕ) (hd : 0 < d)
    (x : SymmetricAlgebra k V) (hx : x ∈ SymPow.symmetricPower d k V) :
    SymPow.symAlgMap g x ∈ q.asHomogeneousIdeal.toIdeal := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  rw [SymPow.symmetricPower, pow_succ'] at hx
  refine Submodule.mul_induction_on hx ?_ fun a b ha hb => by rw [map_add]; exact add_mem ha hb
  rintro a ⟨v, rfl⟩ b _
  rw [_root_.map_mul, SymPow.symAlgMap_ι]
  exact q.asHomogeneousIdeal.toIdeal.mul_mem_right _
    ((mem_pointSubmodule_iff k V q (g v)).mp (h ⟨v, rfl⟩))

/-- A point of `𝐏(V)` lies outside `U(g)` exactly when it lies on the
linear subspace cut out by the image of `g`, that is on `𝐏(Coker g) ⊆ 𝐏(V)`. -/
@[stacks 0B2W "the complement of U(g) is the image of the closed immersion 𝐏(Coker g) → 𝐏(V)"]
public theorem notMem_endDomain_iff (g : V →ₗ[k] V) (q : projectiveSpaceOfModule k V) :
    q ∉ endDomain k V g ↔ q ∈ linearSubspace k V (LinearMap.range g) := by
  rw [mem_linearSubspace_iff]
  constructor
  · intro h v hv
    obtain ⟨w, rfl⟩ := hv
    rw [mem_pointSubmodule_iff]
    by_contra hmem
    refine h ((mem_mapDomain_iff _ _ _ q).mpr
      ⟨1, SymmetricAlgebra.ι k V w, Nat.one_pos, by simp, ?_⟩)
    simpa [SymPow.gradedSymAlgMap_apply, SymPow.symAlgMap_ι] using hmem
  · intro h hq
    obtain ⟨d, x, hd, hx, hxq⟩ := (mem_mapDomain_iff _ _ _ q).mp hq
    exact hxq (symAlgMap_mem_of_range_le k V g q h d hd x hx)

/-- The domain of definition of `r_g` is the complement of the linear subspace cut out by the
image of `g`. -/
public theorem coe_endDomain (g : V →ₗ[k] V) :
    (endDomain k V g : Set (projectiveSpaceOfModule k V)) =
      (linearSubspace k V (LinearMap.range g))ᶜ := by
  ext q
  rw [Set.mem_compl_iff, ← notMem_endDomain_iff k V g q, not_not]
  exact Iff.rfl

/-- A positive-degree homogeneous element of `Sym V` lies in the
homogeneous prime of the image of a point under `r_g` exactly when its image under `Sym g` lies
in the homogeneous prime of that point. -/
public theorem mem_endProjection_iff (g : V →ₗ[k] V) (y : (endDomain k V g).toScheme)
    {d : ℕ} (hd : 0 < d) {x : SymmetricAlgebra k V} (hx : x ∈ SymPow.symmetricPower d k V) :
    x ∈ (endProjection k V g y).asHomogeneousIdeal ↔
      SymPow.symAlgMap g x ∈
        (y.val : projectiveSpaceOfModule k V).asHomogeneousIdeal := by
  unfold endProjection
  have hpre := mapHom_preimage_basicOpen (fun n => SymPow.symmetricPower n k V)
    (fun n => SymPow.symmetricPower n k V) (SymPow.gradedSymAlgMap g) x d hx hd
  have h : y ∈ mapHom (fun n => SymPow.symmetricPower n k V)
        (fun n => SymPow.symmetricPower n k V) (SymPow.gradedSymAlgMap g) ⁻¹ᵁ
        Proj.basicOpen (fun n => SymPow.symmetricPower n k V) x ↔
      y ∈ (mapDomain (fun n => SymPow.symmetricPower n k V)
        (fun n => SymPow.symmetricPower n k V) (SymPow.gradedSymAlgMap g)).ι ⁻¹ᵁ
        Proj.basicOpen (fun n => SymPow.symmetricPower n k V)
          (SymPow.gradedSymAlgMap g x) := by rw [hpre]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, Proj.mem_basicOpen,
    Proj.mem_basicOpen] at h
  exact not_iff_not.mp h

/-- The morphism `r_g` sends the point cut out by a functional `f` on `V` to the point cut out by
`f ∘ g`. -/
@[stacks 0B2W "the value of r_g on a closed point, namely f ↦ f ∘ g"]
public theorem endProjection_eq_linearFunctionalPoint (g : V →ₗ[k] V)
    (y : (endDomain k V g).toScheme) (f : Module.Dual k V) (hf : f ≠ 0) (hfg : f ∘ₗ g ≠ 0)
    (hy : (y.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f hf) :
    endProjection k V g y = linearFunctionalPoint k V (f ∘ₗ g) hfg := by
  refine eq_of_forall_homogeneous_mem_iff k V fun d hd x hx => ?_
  rw [mem_endProjection_iff k V g y hd hx, hy, linearFunctionalPoint_mem k V f hf,
    linearFunctionalPoint_mem k V (f ∘ₗ g) hfg, SymPow.symAlgMap_comp_apply]

/-- Every point in the image of `r_g` lies on the linear subspace cut out by the kernel of `g`,
which is the image of `𝐏(Im g) → 𝐏(V)`. -/
@[stacks 0B2W "the image of r_g is contained in the image of 𝐏(Im g) → 𝐏(V)"]
public theorem range_endProjection_subset (g : V →ₗ[k] V) :
    Set.range (endProjection k V g).base ⊆ linearSubspace k V (LinearMap.ker g) := by
  rintro _ ⟨y, rfl⟩
  rw [mem_linearSubspace_iff]
  intro u hu
  rw [mem_pointSubmodule_iff]
  have h1 : SymmetricAlgebra.ι k V u ∈ SymPow.symmetricPower 1 k V := by simp
  rw [show (endProjection k V g).base y = endProjection k V g y from rfl,
    mem_endProjection_iff k V g y Nat.one_pos h1, SymPow.symAlgMap_ι,
    LinearMap.mem_ker.mp hu, map_zero]
  exact zero_mem _

/-- The point cut out by a functional depends only on the functional. -/
private theorem linearFunctionalPoint_congr {f f' : Module.Dual k V} (hf : f ≠ 0) (hf' : f' ≠ 0)
    (h : f = f') : linearFunctionalPoint k V f hf = linearFunctionalPoint k V f' hf' := by
  subst h
  rfl

/-- Equal functionals cut out the same point, whatever the witnesses of their non-vanishing. -/
public alias linearFunctionalPoint_eq_of_eq := linearFunctionalPoint_congr

/-- Over an algebraically closed field
every closed point of the linear subspace cut out by the kernel of `g` — that is, of the image
of `𝐏(Im g) → 𝐏(V)` — is the image under `r_g` of a point of `U(g)`. -/
@[stacks 0B2W "the image of r_g is the image of 𝐏(Im g) → 𝐏(V), on closed points"]
public theorem exists_endProjection_eq [IsAlgClosed k] [Module.Finite k V] (g : V →ₗ[k] V)
    (q : projectiveSpaceOfModule k V)
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k V)))
    (hmem : q ∈ linearSubspace k V (LinearMap.ker g)) :
    ∃ y : (endDomain k V g).toScheme, endProjection k V g y = q := by
  obtain ⟨f, hf, rfl⟩ := exists_eq_linearFunctionalPoint k V q hq
  rw [mem_linearSubspace_iff, pointSubmodule_linearFunctionalPoint] at hmem
  obtain ⟨f', hf'⟩ : ∃ f' : Module.Dual k V, f' ∘ₗ g = f := by
    have hmemann : f ∈ (LinearMap.ker g).dualAnnihilator :=
      (Submodule.mem_dualAnnihilator _).mpr fun w hw => LinearMap.mem_ker.mp (hmem hw)
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmemann
    exact hmemann
  have hf'g : f' ∘ₗ g ≠ 0 := hf' ▸ hf
  have hf'0 : f' ≠ 0 := by
    rintro rfl
    exact hf'g (LinearMap.zero_comp g)
  have hmemdom : (linearFunctionalPoint k V f' hf'0) ∈
      (endDomain k V g : Set (projectiveSpaceOfModule k V)) := by
    rw [coe_endDomain, Set.mem_compl_iff, mem_linearSubspace_iff,
      pointSubmodule_linearFunctionalPoint]
    intro hle
    refine hf'g (LinearMap.ext fun v => ?_)
    simpa using LinearMap.mem_ker.mp (hle ⟨v, rfl⟩)
  obtain ⟨y, hyv⟩ : ∃ y : (endDomain k V g).toScheme,
      (y.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f' hf'0 :=
    ⟨⟨_, hmemdom⟩, rfl⟩
  refine ⟨y, ?_⟩
  rw [endProjection_eq_linearFunctionalPoint k V g y f' hf'0 hf'g hyv]
  exact linearFunctionalPoint_congr k V hf'g hf hf'

/-- The image of a unit multiple of a linear map is the image of that map. -/
private theorem range_units_smul (c : kˣ) (g : V →ₗ[k] V) :
    LinearMap.range ((c : k) • g) = LinearMap.range g := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    exact ⟨(c : k) • v, by simp⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨((c⁻¹ : kˣ) : k) • v, by simp [smul_smul]⟩

/-- A unit multiple of `g` has the same domain of definition `U(g)`. -/
@[stacks 0B2W "U(g) depends only on the point [g] of the parameter space"]
public theorem endDomain_smul (c : kˣ) (g : V →ₗ[k] V) :
    endDomain k V ((c : k) • g) = endDomain k V g :=
  TopologicalSpace.Opens.ext (by
    rw [coe_endDomain, coe_endDomain, range_units_smul])

/-- A unit multiple of `g` induces the same morphism `r_g` on the points cut out by linear
functionals. -/
@[stacks 0B2W "r_g depends only on the point [g] of the parameter space, on closed points"]
public theorem endProjection_smul_apply (c : kˣ) (g : V →ₗ[k] V)
    (y : (endDomain k V ((c : k) • g)).toScheme) (y' : (endDomain k V g).toScheme)
    (f : Module.Dual k V) (hf : f ≠ 0) (hfg : f ∘ₗ g ≠ 0)
    (hy : (y.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f hf)
    (hy' : (y'.val : projectiveSpaceOfModule k V) = linearFunctionalPoint k V f hf) :
    endProjection k V ((c : k) • g) y = endProjection k V g y' := by
  have hsm : f ∘ₗ ((c : k) • g) = c • (f ∘ₗ g) := by
    ext v
    simp [Units.smul_def]
  have hcsm : (c • (f ∘ₗ g) : Module.Dual k V) ≠ 0 := (smul_ne_zero_iff_ne c).mpr hfg
  have hcfg : f ∘ₗ ((c : k) • g) ≠ 0 := hsm ▸ hcsm
  rw [endProjection_eq_linearFunctionalPoint k V _ y f hf hcfg hy,
    endProjection_eq_linearFunctionalPoint k V g y' f hf hfg hy',
    linearFunctionalPoint_congr k V hcfg hcsm hsm]
  exact linearFunctionalPoint_units_smul k V c (f ∘ₗ g) hfg hcsm

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
