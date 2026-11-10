module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.CoinducedEffacement

/-!
# Degree-one classes with trivial coefficients come from homomorphisms

Let `G` be a compact topological group, `R` a ring and `A` a continuous discrete
`R`-`G`-module on which `G` acts trivially. Every class `z ∈ H¹(G, A)` (the right derived functor
of invariants, `Stacks.ContinuousCohomology.invariantsDelta`) gives a homomorphism `c : G → A`
with open kernel such that `m • c = 0` forces `m • z = 0`. In particular, for `A = ℤ/N` a class of
order `N` gives a surjection `G → ℤ/N` with open kernel.

## Main results

* `Stacks.ContinuousCohomology.exists_hom_of_trivial_of_degreeOne` — the homomorphism.
* `Stacks.ContinuousCohomology.exists_surjective_hom_of_trivial_of_degreeOne` — a class of maximal
  order gives a surjective homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Stacks.ContinuousCohomology

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [Ring R] {G : Type v} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G]

/-- **A degree-one class with trivial coefficients comes from a homomorphism.** For `A` a
continuous discrete `R`-`G`-module with trivial action and `z ∈ H¹(G, A)` there is a map
`c : G → A`, additive in the group law of `G`, with open kernel, such that `m • z = 0` as soon as
`m • c = 0`. -/
theorem exists_hom_of_trivial_of_degreeOne
    (A : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G)
    (hA : ∀ (g : G) (a : A.obj.obj.V), (A.obj.obj.ρ g).asHom.hom a = a)
    (z : ((invariantsDelta.{u, v, w} R (G := G)).functor 1).obj A) :
    ∃ c : G → A.obj.obj.V, (∀ g h, c (g * h) = c g + c h) ∧ IsOpen {g | c g = 0} ∧
      ∀ m : ℕ, (∀ g, m • c g = 0) → m • z = 0 := by
  classical
  obtain ⟨V, hV⟩ := exists_map_coindUnit_eq_zero.{u, v, w} R 0 A z
  have hequiv : ∀ {X Y : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G} (φ : X ⟶ Y)
      (g : G) (x : X.obj.obj.V),
      φ.hom.hom.hom.hom ((X.obj.obj.ρ g).asHom.hom x) =
        (Y.obj.obj.ρ g).asHom.hom (φ.hom.hom.hom.hom x) :=
    fun φ g x ↦ ConcreteCategory.congr_hom (φ.hom.hom.comm g) x
  let S := monoSeq R (coindUnit.{u, v, w} R V A)
  have hS : S.ShortExact := shortExact_monoSeq R _
  obtain ⟨q, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
    ((invariantsDelta.{u, v, w} R (G := G)).exact_δ₂ hS 0) z hV
  have hmul : ∀ (a b : G) (y : S.X₂.obj.obj.V),
      (S.X₂.obj.obj.ρ (a * b)).asHom.hom y =
        (S.X₂.obj.obj.ρ a).asHom.hom ((S.X₂.obj.obj.ρ b).asHom.hom y) := by
    intro a b y; rw [map_mul]; rfl
  let e0 : (invariantsDelta.{u, v, w} R (G := G)).functor 0 ≅
      continuousModuleRingInvariants.{u, v, max u v w} R G :=
    eqToIso (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives_functor _ 0) ≪≫
      (continuousModuleRingInvariants.{u, v, max u v w} R G).rightDerivedZeroIsoSelf
  let q0 := e0.hom.app _ q
  obtain ⟨f, hf⟩ := (epi_iff_surjective R S.g).1 hS.epi_g q0.1
  let ι := (coindUnit.{u, v, w} R V A).hom.hom.hom.hom
  have hι : Function.Injective ι := (mono_iff_injective R _).1 inferInstance
  have hgf : ∀ g : G, S.g.hom.hom.hom.hom ((S.X₂.obj.obj.ρ g).asHom.hom f - f) = 0 := by
    intro g
    rw [map_sub, hequiv, show S.g.hom.hom.hom.hom f = q0.1 from hf]
    exact sub_eq_zero.2 (q0.2 g)
  have hex := (exact_iff_underlying R S).1 hS.exact
  choose c hc using fun g : G ↦ hex _ (hgf g)
  have hcι : ∀ g, ι (c g) = (S.X₂.obj.obj.ρ g).asHom.hom f - f := hc
  have hfix : ∀ (g : G) (a : A.obj.obj.V), (S.X₂.obj.obj.ρ g).asHom.hom (ι a) = ι a := by
    intro g a
    rw [← hequiv (coindUnit.{u, v, w} R V A), hA]
  refine ⟨c, fun g h ↦ hι ?_, ?_, fun m hm ↦ ?_⟩
  · rw [map_add, hcι, hcι, hcι, hmul]
    have := hfix g (c h)
    rw [hcι, map_sub, sub_eq_iff_eq_add] at this
    rw [this]
    abel
  · have : {g | c g = 0} = {g | (S.X₂.obj.obj.ρ g).asHom.hom f = f} := by
      ext g
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← sub_eq_zero (a := (S.X₂.obj.obj.ρ g).asHom.hom f),
        ← hcι, map_eq_zero_iff ι hι]
    rw [this]
    exact Stacks.GroupCohomology.isOpen_stabilizer R G _ f
  · have hinv : ∀ g : G, (S.X₂.obj.obj.ρ g).asHom.hom (m • f) = m • f := by
      intro g
      have h0 : m • ((S.X₂.obj.obj.ρ g).asHom.hom f - f) = 0 := by
        rw [← hcι, ← map_nsmul, hm g, map_zero]
      rw [map_nsmul]
      rw [nsmul_sub, sub_eq_zero] at h0
      exact h0
    let f0 : (continuousModuleRingInvariants.{u, v, max u v w} R G).obj S.X₂ := ⟨m • f, hinv⟩
    have hmap : (continuousModuleRingInvariants.{u, v, max u v w} R G).map S.g f0 = m • q0 := by
      apply Subtype.ext
      change S.g.hom.hom.hom.hom (m • f) = m • q0.1
      rw [map_nsmul, show S.g.hom.hom.hom.hom f = q0.1 from hf]
    have hq : m • q =
        ((invariantsDelta.{u, v, w} R (G := G)).functor 0).map S.g (e0.inv.app _ f0) := by
      have n1 := ConcreteCategory.congr_hom (e0.inv.naturality S.g) f0
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at n1
      rw [← n1, hmap, map_nsmul]
      congr 1
      change q = (e0.hom ≫ e0.inv).app _ q
      rw [e0.hom_inv_id]
      rfl
    rw [← map_nsmul, hq, ← ConcreteCategory.comp_apply,
      (invariantsDelta.{u, v, w} R (G := G)).map_g_δ hS 0]
    rfl

/-- **A degree-one class of maximal order gives a surjection.** If `A` (trivial action) has `N`
elements and `z ∈ H¹(G, A)` is killed by `m` only when `N ∣ m`, then there is a surjective map
`c : G → A`, additive in the group law of `G`, with open kernel. -/
theorem exists_surjective_hom_of_trivial_of_degreeOne
    (A : Stacks.Injectives.ContinuousModule.{u, v, max u v w} R G) [Finite A.obj.obj.V]
    (hA : ∀ (g : G) (a : A.obj.obj.V), (A.obj.obj.ρ g).asHom.hom a = a)
    (z : ((invariantsDelta.{u, v, w} R (G := G)).functor 1).obj A)
    (hz : ∀ m : ℕ, m • z = 0 → Nat.card A.obj.obj.V ∣ m) :
    ∃ c : G → A.obj.obj.V, (∀ g h, c (g * h) = c g + c h) ∧ IsOpen {g | c g = 0} ∧
      Function.Surjective c := by
  classical
  obtain ⟨c, hc, hopen, htors⟩ := exists_hom_of_trivial_of_degreeOne.{u, v, w} R A hA z
  have h0 : c 1 = 0 := by simpa using hc 1 1
  let H : AddSubgroup A.obj.obj.V :=
    { carrier := Set.range c
      zero_mem' := ⟨1, h0⟩
      add_mem' := fun {a b} ⟨g, hg⟩ ⟨h, hh⟩ ↦ ⟨g * h, by rw [hc, hg, hh]⟩
      neg_mem' := fun {a} ⟨g, hg⟩ ↦ ⟨g⁻¹, by
        have h1 := hc g⁻¹ g
        rw [inv_mul_cancel, h0] at h1
        rw [← hg]
        exact eq_neg_of_add_eq_zero_left h1.symm⟩ }
  have hkill : ∀ g, Nat.card H • c g = 0 := fun g ↦ by
    have := card_nsmul_eq_zero' (G := H) (x := ⟨c g, g, rfl⟩)
    exact congrArg Subtype.val this
  have hdvd := hz _ (htors _ hkill)
  have hle : Nat.card H ≤ Nat.card A.obj.obj.V := AddSubgroup.card_le_of_le le_top |>.trans
    (by rw [AddSubgroup.card_top])
  have hpos : 0 < Nat.card H := Nat.card_pos
  have heq : Nat.card H = Nat.card A.obj.obj.V :=
    le_antisymm hle (Nat.le_of_dvd hpos hdvd)
  have htop : H = ⊤ := AddSubgroup.eq_top_of_card_eq H heq
  exact ⟨c, hc, hopen, fun a ↦ (htop ▸ AddSubgroup.mem_top a : a ∈ H)⟩

end Stacks.ContinuousCohomology

end
