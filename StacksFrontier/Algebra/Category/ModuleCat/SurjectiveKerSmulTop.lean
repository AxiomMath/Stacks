module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Surjective maps with kernel `I • ⊤`, transported

Two facts about the property "surjective with kernel `I • M`" of a linear map, used to read a
statement about a map of modules through isomorphisms and restriction of scalars:

* it is invariant under isomorphisms of the source and the target
  (`ModuleCat.surjective_and_ker_eq_of_comm`);
* for a ring map `ρ : R →+* S`, an `S`-module `N` and an ideal `I` of `R`, the submodule `I • N`
  of `N` read as an `R`-module has the same elements as the submodule `(I S) • N` of the `S`-module
  `N` (`ModuleCat.mem_smul_top_restrictScalars_iff`).
-/

@[expose] public section

open CategoryTheory

universe v u u'

namespace ModuleCat

/-- **Surjectivity and kernel `I • ⊤` along a commutative square of isomorphisms.** -/
theorem surjective_and_ker_eq_of_comm {R : Type u} [CommRing R] {A A' B B' : ModuleCat.{v} R}
    (f : A ⟶ B) (f' : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B') (w : f ≫ eB.hom = eA.hom ≫ f')
    (I : Ideal R) (hs : Function.Surjective f') (hk : LinearMap.ker f'.hom = I • ⊤) :
    Function.Surjective f ∧ LinearMap.ker f.hom = I • ⊤ := by
  have hf : f = eA.hom ≫ f' ≫ eB.inv := by
    rw [← Category.assoc, ← w, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  constructor
  · rw [hf]
    exact (eB.toLinearEquiv.symm.surjective.comp hs).comp eA.toLinearEquiv.surjective
  · have key : (I • (⊤ : Submodule R A')).comap eA.toLinearEquiv.toLinearMap = I • ⊤ := by
      rw [Submodule.comap_equiv_eq_map_symm, Submodule.map_smul'', Submodule.map_top,
        LinearEquiv.range]
    ext x
    rw [LinearMap.mem_ker, ← key, Submodule.mem_comap, ← hk, LinearMap.mem_ker]
    show f x = 0 ↔ f' (eA.hom x) = 0
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · have := congrArg eB.hom hx
      rwa [map_zero, ← ConcreteCategory.comp_apply, w, ConcreteCategory.comp_apply] at this
    · rw [hf, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hx, map_zero]

/-- **Surjectivity and kernel `I • ⊤` after an isomorphism of the target.** -/
theorem surjective_and_ker_eq_comp_iso {R : Type u} [CommRing R] {A B C : ModuleCat.{v} R}
    (f : A ⟶ B) (e : B ≅ C) (I : Ideal R) (hs : Function.Surjective f)
    (hk : LinearMap.ker f.hom = I • ⊤) :
    Function.Surjective (f ≫ e.hom) ∧ LinearMap.ker (f ≫ e.hom).hom = I • ⊤ :=
  surjective_and_ker_eq_of_comm (f ≫ e.hom) f (Iso.refl A) e.symm
    (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]) I hs hk

/-- **`I • N` read over `R` is `(I S) • N`**, for a ring map `ρ : R →+* S`, an `S`-module `N` and
an ideal `I` of `R`. -/
theorem mem_smul_top_restrictScalars_iff {R : Type u} {S : Type u'} [CommRing R] [CommRing S]
    (ρ : R →+* S) (N : ModuleCat.{v} S) (I : Ideal R) (x : N) :
    x ∈ (I • ⊤ : Submodule R ((restrictScalars ρ).obj N)) ↔ x ∈ (I.map ρ • ⊤ : Submodule S N) := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · exact Submodule.smul_induction_on (p := fun y : (restrictScalars ρ).obj N =>
      (show N from y) ∈ (I.map ρ • ⊤ : Submodule S N)) hx
      (fun r hr n _ => Submodule.smul_mem_smul (Ideal.mem_map_of_mem ρ hr) Submodule.mem_top)
      (fun _ _ ha hb => Submodule.add_mem _ ha hb)
  · let P : Set N := fun y => (show (restrictScalars ρ).obj N from y) ∈
      (I • ⊤ : Submodule R ((restrictScalars ρ).obj N))
    have hPadd : ∀ a b : N, a ∈ P → b ∈ P → a + b ∈ P := fun a b ha hb =>
      Submodule.add_mem (I • ⊤ : Submodule R ((restrictScalars ρ).obj N)) ha hb
    show x ∈ P
    refine Submodule.smul_induction_on (p := fun y : N => y ∈ P) hx (fun s hs n _ => ?_) hPadd
    suffices h : ∀ n : N, s • n ∈ P from h n
    refine Submodule.span_induction (p := fun s _ => ∀ n : N, s • n ∈ P) ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨r, hr, rfl⟩ n
      exact Submodule.smul_mem_smul (M := (restrictScalars ρ).obj N) hr Submodule.mem_top
    · intro n
      rw [zero_smul]
      exact Submodule.zero_mem (I • ⊤ : Submodule R ((restrictScalars ρ).obj N))
    · intro a b _ _ ha hb n
      rw [add_smul]
      exact hPadd _ _ (ha n) (hb n)
    · intro t a _ ha n
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact ha (t • n)

end ModuleCat
