module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Topology.Algebra.AdicLimitTopology

/-!
# The limit topology on a categorical limit of modules

`StacksFrontier/Topology/Algebra/AdicLimitTopology.lean` compares the limit topology on the inverse
limit of a tower of modules with the `I`-adic topology, for the inverse limit realised as the
submodule `Stacks.AdicLimit.towerLimit` of compatible sequences. Inverse systems of modules
arising from sheaves are functors `ℕᵒᵖ ⥤ ModuleCat R`, and their limits are categorical limits.
This file transports the comparison to that setting: the categorical limit is linearly
isomorphic to the module of compatible sequences, by the projections in one direction and by the
universal property in the other.

## Main results

* `Stacks.AdicLimit.ker_limit_π_le_pow_smul` — successive approximation by a fixed finite family
  of elements of `I` places the kernel of the projection to the term of index `c + k` inside
  `IᵏM`, for `M` the limit of a tower in `ModuleCat R`.
* `Stacks.AdicLimit.iInf_induced_limit_eq_adicModuleTopology` — consequently the limit topology
  on `M` is the `I`-adic topology, as soon as the `n`-th term is killed by `Iⁿ⁺¹`.

## References

* [Stacks Project, Tag 0GYM](https://stacks.math.columbia.edu/tag/0GYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.AdicLimit

variable {R : Type u} [CommRing R] (G : ℕᵒᵖ ⥤ ModuleCat.{v} R) [HasLimit G]

/-- The terms of a tower in `ModuleCat R`, as types. -/
abbrev towerTerm (n : ℕ) : Type v := ↑(G.obj (op n))

/-- The successive transition maps of a tower in `ModuleCat R`, as linear maps. -/
abbrev towerTransition (n : ℕ) : G.obj (op (n + 1)) →ₗ[R] G.obj (op n) :=
  (G.map (homOfLE (Nat.le_succ n)).op).hom

/-- The categorical limit of a tower of modules, mapped to the module of compatible sequences by
its projections. -/
def limitToTowerLimit :
    ↑(limit G) →ₗ[R] towerLimit (towerTerm G) (towerTransition G) :=
  LinearMap.codRestrict _ (LinearMap.pi fun n => (limit.π G (op n)).hom) fun x n =>
    congrArg (fun g => ModuleCat.Hom.hom g x) (limit.w G (homOfLE (Nat.le_succ n)).op)

/-- The projection from the module of compatible sequences to a term of the tower. -/
def towerLimitProjHom (n : ℕ) :
    ((Functor.const ℕᵒᵖ).obj (ModuleCat.of R
      (towerLimit (towerTerm G) (towerTransition G)))).obj (op n) ⟶ G.obj (op n) :=
  ModuleCat.ofHom (towerLimit.proj (towerTerm G) (towerTransition G) n)

/-- The module of compatible sequences, as a cone over the tower. -/
def towerLimitCone : Cone G where
  pt := ModuleCat.of R (towerLimit (towerTerm G) (towerTransition G))
  π := NatTrans.ofOpSequence (towerLimitProjHom G) fun n => by
      ext z
      change z.1 n = (towerTransition G n) (z.1 (n + 1))
      exact (z.2 n).symm

/-- The map from compatible sequences to the categorical limit given by the universal property,
followed by the projection to the term of index `n`, is the `n`-th coordinate. -/
theorem limit_π_lift_towerLimitCone (z : towerLimit (towerTerm G)
    (towerTransition G)) (n : ℕ) :
    (limit.π G (op n)).hom ((limit.lift G (towerLimitCone G)).hom z) = z.1 n :=
  ConcreteCategory.congr_hom (limit.lift_π (towerLimitCone G) (op n)) z

/-- The map from compatible sequences to the categorical limit given by the universal property is
a left inverse of `Stacks.AdicLimit.limitToTowerLimit`. -/
theorem lift_towerLimitCone_limitToTowerLimit (x : ↑(limit G)) :
    (limit.lift G (towerLimitCone G)).hom (limitToTowerLimit G x) = x := by
  have h : ModuleCat.ofHom ((limit.lift G (towerLimitCone G)).hom.comp (limitToTowerLimit G)) =
      𝟙 (limit G) := by
    refine limit.hom_ext fun j => ?_
    obtain ⟨n⟩ := j
    ext y
    exact limit_π_lift_towerLimitCone G _ n
  exact ConcreteCategory.congr_hom h x

/-- **Successive approximation bounds the kernels of the projections of a limit of modules.**
If, beyond `c`, every element of `M = lim Gₙ` dying in `G_(n+1)` is congruent modulo the kernel
of the projection to `G_(n+2)` to a combination `∑ aᵢ yᵢ` of elements dying in `Gₙ`, with all
`aᵢ ∈ I`, then `Ker(M → G_(c+k)) ⊆ IᵏM`. -/
theorem ker_limit_π_le_pow_smul (I : Ideal R) {ι : Type w} [Fintype ι] (a : ι → R)
    (ha : ∀ i, a i ∈ I) (c : ℕ)
    (happrox : ∀ n, c ≤ n → ∀ x : ↑(limit G), (limit.π G (op (n + 1))).hom x = 0 →
      ∃ y : ι → ↑(limit G), (∀ i, (limit.π G (op n)).hom (y i) = 0) ∧
        (limit.π G (op (n + 2))).hom (x - ∑ i, a i • y i) = 0)
    (k : ℕ) :
    LinearMap.ker (limit.π G (op (c + k))).hom ≤
      I ^ k • (⊤ : Submodule R ↑(limit G)) := by
  let Φ := limitToTowerLimit G
  let Ψ : towerLimit (towerTerm G) (towerTransition G) →ₗ[R] ↑(limit G) :=
    (limit.lift G (towerLimitCone G)).hom
  have hΦ (x : ↑(limit G)) (n : ℕ) : (Φ x).1 n = (limit.π G (op n)).hom x := rfl
  have hΨ (z : towerLimit (towerTerm G) (towerTransition G)) (n : ℕ) :
      (limit.π G (op n)).hom (Ψ z) = z.1 n := limit_π_lift_towerLimitCone G z n
  have hΦΨ (z) : Φ (Ψ z) = z := Subtype.ext (funext fun n => (hΦ _ n).trans (hΨ z n))
  have hΨΦ (x) : Ψ (Φ x) = x := lift_towerLimitCone_limitToTowerLimit G x
  have hker (n : ℕ) (z : towerLimit (towerTerm G) (towerTransition G)) :
      z ∈ LinearMap.ker (towerLimit.proj (towerTerm G) (towerTransition G) n) ↔ z.1 n = 0 :=
    Iff.rfl
  have happrox' : ∀ n, c ≤ n → ∀ z, z ∈ LinearMap.ker
      (towerLimit.proj (towerTerm G) (towerTransition G) (n + 1)) →
      ∃ y : ι → towerLimit (towerTerm G) (towerTransition G),
        (∀ i, y i ∈ LinearMap.ker (towerLimit.proj (towerTerm G) (towerTransition G) n)) ∧
        z - ∑ i, a i • y i ∈
          LinearMap.ker (towerLimit.proj (towerTerm G) (towerTransition G) (n + 2)) := by
    intro n hn z hz
    rw [hker] at hz
    obtain ⟨y, hy, hxy⟩ := happrox n hn (Ψ z) ((hΨ z (n + 1)).trans hz)
    refine ⟨fun i => Φ (y i), fun i => (hker n _).mpr ((hΦ _ n).trans (hy i)), ?_⟩
    have he : z - ∑ i, a i • Φ (y i) = Φ (Ψ z - ∑ i, a i • y i) := by
      rw [map_sub, map_sum, hΦΨ]
      simp only [map_smul]
    rw [he, hker, hΦ]
    exact hxy
  intro x hx
  have hx' : Φ x ∈ LinearMap.ker (towerLimit.proj (towerTerm G) (towerTransition G) (c + k)) :=
    (hker _ _).mpr ((hΦ x _).trans hx)
  have hmem : Φ x ∈ I ^ k • (⊤ : Submodule R (towerLimit (towerTerm G) (towerTransition G))) :=
    proj_ker_le_pow_smul (D := towerTerm G) (towerTransition G) I (ι := ι) a ha c happrox' k hx'
  have hmap : Ψ (Φ x) ∈
      (I ^ k • (⊤ : Submodule R (towerLimit (towerTerm G) (towerTransition G)))).map Ψ :=
    Submodule.mem_map_of_mem hmem
  rw [Submodule.map_smul'', hΨΦ] at hmap
  exact Submodule.smul_mono le_rfl le_top hmap




/-- **The limit topology on a limit of modules is the adic topology** when the `n`-th term of the
tower is killed by `Iⁿ⁺¹` and the successive approximation of
`Stacks.AdicLimit.ker_limit_π_le_pow_smul` holds. -/
theorem iInf_induced_limit_eq_adicModuleTopology (I : Ideal R)
    (hann : ∀ n, I ^ (n + 1) • (⊤ : Submodule R (G.obj (op n))) = ⊥)
    {ι : Type w} [Fintype ι] (a : ι → R) (ha : ∀ i, a i ∈ I) (c : ℕ)
    (happrox : ∀ n, c ≤ n → ∀ x : ↑(limit G), (limit.π G (op (n + 1))).hom x = 0 →
      ∃ y : ι → ↑(limit G), (∀ i, (limit.π G (op n)).hom (y i) = 0) ∧
        (limit.π G (op (n + 2))).hom (x - ∑ i, a i • y i) = 0) :
    (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : ↑(limit G) => (limit.π G (op n)).hom x) ⊥) =
        I.adicModuleTopology ↑(limit G) := by
  refine iInf_induced_eq_adicModuleTopology I (fun n => (limit.π G (op n)).hom) ?_ ?_ ?_
  · intro i j hij x hx
    have hw := limit.w G (homOfLE hij).op
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hw, ModuleCat.hom_comp]
    simp only [LinearMap.coe_comp, Function.comp_apply, hx, map_zero]
  · refine fun n => ⟨n + 1, Submodule.smul_le.mpr fun r hr x _ => ?_⟩
    rw [LinearMap.mem_ker, map_smul]
    have h := Submodule.smul_mem_smul hr (Submodule.mem_top (x := (limit.π G (op n)).hom x))
    rw [hann n] at h
    exact (Submodule.mem_bot R).mp h
  · exact fun k => ⟨c + k, ker_limit_π_le_pow_smul G I a ha c happrox k⟩

end Stacks.AdicLimit

end
