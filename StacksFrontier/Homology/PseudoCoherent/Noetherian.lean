module

public import Mathlib.RingTheory.Filtration
public import StacksFrontier.Homology.PseudoCoherent.Ext
public import StacksCore.Tactic.StacksAttribute

/-!
# Detecting nonzero cohomology of a pseudo-coherent complex modulo an ideal

Let `K` be a pseudo-coherent object of the derived category of modules over a Noetherian ring.
If one of its cohomology modules remains nonzero after reduction modulo an ideal, then
that cohomology class is detected by a morphism from `K` to a finite module annihilated by a
power of the ideal.

## Main results

* `StacksDraft.PseudoCoherence.exists_finite_module_detecting_homology_mod_ideal`: the finite
  module and the morphism detecting the given cohomology.

## Implementation notes

The shifted module `E[-i]` in the source is represented by the single complex with `E` in
degree `i`. Nonvanishing on cohomology is stated after the canonical identification of the
degree-`i` cohomology of this single complex with `E`.

## References

* [Stacks Project, Tag 0A7D](https://stacks.math.columbia.edu/tag/0A7D)
-/

open CategoryTheory

namespace StacksDraft.PseudoCoherence

universe u v

attribute [local instance] HasDerivedCategory.standard

private lemma exists_pow_smul_top_inf_range_le_smul
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {H M : Type v} [AddCommGroup H] [Module A H] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (m : Ideal A) (g : H →ₗ[A] M) :
    ∃ n : ℕ, m ^ n • (⊤ : Submodule A M) ⊓ LinearMap.range g ≤ m • LinearMap.range g := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul m (LinearMap.range g)
  refine ⟨k + 1, ?_⟩
  rw [hk (k + 1) (Nat.le_succ k), Nat.add_sub_cancel_left, pow_one]
  exact Submodule.smul_mono le_rfl inf_le_right

private lemma quotient_comp_ne_zero
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {H M : Type v} [AddCommGroup H] [Module A H] [AddCommGroup M] [Module A M]
    [Module.Finite A M] (m : Ideal A) (g : H →ₗ[A] M) (hg : Function.Injective g)
    (hi : Nontrivial (H ⧸ (m • (⊤ : Submodule A H)))) :
    ∃ n : ℕ, (Submodule.mkQ (m ^ n • (⊤ : Submodule A M))).comp g ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_pow_smul_top_inf_range_le_smul m g
  refine ⟨n, fun hzero ↦ ?_⟩
  have htop : m • (⊤ : Submodule A H) = ⊤ := top_unique fun x _ ↦ by
    have hxker : g x ∈ m ^ n • (⊤ : Submodule A M) := by
      rw [← Submodule.ker_mkQ (m ^ n • (⊤ : Submodule A M)), LinearMap.mem_ker]
      exact LinearMap.congr_fun hzero x
    have hxrange : g x ∈ LinearMap.range g := ⟨x, rfl⟩
    have hx : g x ∈ m • LinearMap.range g := hn ⟨hxker, hxrange⟩
    rw [← Submodule.map_top g, ← Submodule.map_smul''] at hx
    obtain ⟨y, hy, hgy⟩ := hx
    simpa [hg hgy] using hy
  have : Subsingleton (H ⧸ (m • (⊤ : Submodule A H))) :=
    Submodule.Quotient.subsingleton_iff.mpr htop
  exact not_nontrivial (H ⧸ (m • (⊤ : Submodule A H))) hi

/-- **Stacks 0A7D.** If degree-`i` cohomology of a pseudo-coherent complex over a Noetherian
ring is nonzero modulo an ideal, it is detected by a map to a finite module annihilated by a
power of that ideal, placed in degree `i`. -/
@[stacks 0A7D]
public theorem exists_finite_module_detecting_homology_mod_ideal
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsPseudoCoherent K)
    (m : Ideal A) (i : ℤ)
    (hi : Nontrivial
      (((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K) ⧸
        (m • (⊤ : Submodule A
          ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K))))) :
    ∃ (E : ModuleCat.{v} A), Module.Finite A E ∧
      (∃ n : ℕ, m ^ n • (⊤ : Submodule A E) = ⊥) ∧
      ∃ f : K ⟶ (DerivedCategory.singleFunctor (ModuleCat.{v} A) i).obj E,
        (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map f ≫
          (DerivedCategory.singleFunctorCompHomologyFunctorIso
            (ModuleCat.{v} A) i).hom.app E ≠ 0 := by
  obtain ⟨M, hM, f, hf⟩ :=
    exists_finitelyPresented_module_mono_homology K hK i
  let g : (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K ⟶ M :=
    (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map f ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) i).hom.app M
  let : Module.FinitePresentation A M := hM
  have hg : Function.Injective g := (ModuleCat.mono_iff_injective g).mp hf
  obtain ⟨n, hn⟩ := quotient_comp_ne_zero m g.hom hg hi
  let N : Submodule A M := m ^ n • ⊤
  let E : ModuleCat.{v} A := ModuleCat.of A (M ⧸ N)
  let q : M ⟶ E := ModuleCat.ofHom (Submodule.mkQ N)
  refine ⟨E, inferInstance, ⟨n, ?_⟩, f ≫ (DerivedCategory.singleFunctor
    (ModuleCat.{v} A) i).map q, ?_⟩
  · change m ^ n • (⊤ : Submodule A (M ⧸ N)) = ⊥
    calc
      m ^ n • (⊤ : Submodule A (M ⧸ N)) =
          (m ^ n • (⊤ : Submodule A M)).map (Submodule.mkQ N) := by
            rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
      _ = ⊥ := by
        rw [Submodule.eq_bot_iff]
        rintro z ⟨x, hx, rfl⟩
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        simpa [N] using hx
  · rw [Functor.map_comp, Category.assoc]
    change (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map f ≫
      (((DerivedCategory.singleFunctor (ModuleCat.{v} A) i) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map q ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso
          (ModuleCat.{v} A) i).hom.app E) ≠ 0
    rw [(DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{v} A) i).hom.naturality q, Functor.id_map]
    change g ≫ q ≠ 0
    intro h
    apply hn
    ext x
    have hx := congrArg (fun k : _ ⟶ E ↦ k.hom x) h
    rw [ModuleCat.hom_comp] at hx
    change q.hom (g.hom x) = 0
    simpa [q, N] using hx

end StacksDraft.PseudoCoherence
