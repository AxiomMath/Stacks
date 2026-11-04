module

public import StacksFrontier.Algebra.Homology.TwoTermHomologyExact

/-!
# Monomorphy of a map of cohomology objects in a degree with no incoming differential

The companions of `HomologicalComplex.epi_homologyMap_of_epi_opcyclesMap` and
`HomologicalComplex.epi_opcyclesMap_of_surjective` on the other side: in a degree `j` into which
no differential enters, the cohomology object is the object of cycles, so a map of complexes
injective on cycles is a monomorphism on cohomology.

Mathlib's `HomologicalComplex.mono_homologyMap_of_mono_of_not_rel` is the same statement for a
degree that is the target of *no* arrow of the complex shape; for a cochain complex of abelian
groups in degree `j` there is always the arrow from `j - 1`, and what is available instead is the
vanishing of that one differential, which is the hypothesis below.

## Main results

* `HomologicalComplex.mono_homologyMap_of_mono_cyclesMap`: with the differential into degree `j`
  zero in both complexes, a map of cycles that is a monomorphism makes the map of cohomology one.
* `HomologicalComplex.mono_cyclesMap_of_injective`: for complexes of modules, the map of cycles
  in degree `j` is a monomorphism as soon as an element of degree `j` killed by the differential
  out of `j` and by the map is zero.
* `CochainComplex.eq_zero_of_addEquiv`: the elementwise hypothesis of the previous result,
  transported along additive equivalences of all the objects in sight.  This is the companion of
  `CochainComplex.exists_cycle_of_addEquiv`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

/-! ### Cohomology in a degree with no incoming differential -/

section Mono

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [CategoryWithHomology C]
  {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}

/-- **In a degree with no incoming differential, cohomology is cycles**: if the map of cycles
induced by a morphism of complexes is a monomorphism, so is the map of cohomology objects. -/
theorem mono_homologyMap_of_mono_cyclesMap (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i)
    (hK : K.d i j = 0) (hL : L.d i j = 0) (h : Mono (cyclesMap φ j)) :
    Mono (homologyMap φ j) := by
  have h₁ := K.isIso_homologyπ i j hi hK
  have h₂ := L.isIso_homologyπ i j hi hL
  have e : homologyMap φ j = inv (K.homologyπ j) ≫ cyclesMap φ j ≫ L.homologyπ j := by
    rw [← homologyπ_naturality, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

end Mono

/-! ### The map of cycles of a morphism of complexes of modules -/

section Modules

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{v} R) c}

/-- **The map of cycles induced by a morphism of complexes of modules is a monomorphism as soon
as it is injective on cycles**, which is what the displayed elementwise condition says: the
cycles in degree `j` are the elements killed by the differential out of `j`. -/
theorem mono_cyclesMap_of_injective (φ : K ⟶ L) (j k : ι) (hk : c.next j = k)
    (hinj : ∀ x : K.X j, K.d j k x = 0 → φ.f j x = 0 → x = 0) :
    Mono (cyclesMap φ j) := by
  subst hk
  have hi : Function.Injective (K.iCycles j) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  rw [ModuleCat.mono_iff_injective]
  intro ζ ζ' hζ
  refine hi ?_
  have hsub : K.iCycles j (ζ - ζ') = 0 := by
    have hd : K.d j (c.next j) (K.iCycles j (ζ - ζ')) = 0 :=
      congrArg (fun m : K.cycles j ⟶ K.X (c.next j) => m.hom (ζ - ζ'))
        (K.iCycles_d j (c.next j))
    have hφ : φ.f j (K.iCycles j (ζ - ζ')) = 0 := by
      have hcomm := congrArg (fun m : K.cycles j ⟶ L.X j => m.hom (ζ - ζ'))
        (cyclesMap_i φ j)
      change (L.iCycles j) (cyclesMap φ j (ζ - ζ')) = φ.f j (K.iCycles j (ζ - ζ')) at hcomm
      rw [← hcomm, map_sub, hζ, sub_self, map_zero]
    exact hinj _ hd hφ
  rw [map_sub, sub_eq_zero] at hsub
  exact hsub

end Modules

end HomologicalComplex

namespace CochainComplex

/-! ### Transport of the elementwise condition along additive equivalences -/

section Transport

variable {C₁ T₁ C₂ M₁ N₁ M₂ : Type*} [AddCommGroup C₁] [AddCommGroup T₁] [AddCommGroup C₂]
  [AddCommGroup M₁] [AddCommGroup N₁] [AddCommGroup M₂]
  {u₁ : C₁ ≃+ M₁} {u₀ : T₁ ≃+ N₁} {v₁ : C₂ ≃+ M₂}
  {dK : C₁ → T₁} {pc : C₁ → C₂} {d₁ : M₁ → N₁} {p : M₁ → M₂}

/-- The condition of `HomologicalComplex.mono_cyclesMap_of_injective`, transported along additive
equivalences of the three objects involved.  This is the companion of
`CochainComplex.exists_cycle_of_addEquiv`. -/
theorem eq_zero_of_addEquiv (hdK : ∀ z, u₀ (dK z) = d₁ (u₁ z)) (hp : ∀ z, v₁ (pc z) = p (u₁ z))
    (h : ∀ n : M₁, d₁ n = 0 → p n = 0 → n = 0)
    (m : C₁) (h1 : dK m = 0) (h2 : pc m = 0) : m = 0 := by
  refine u₁.injective ?_
  rw [map_zero]
  refine h (u₁ m) ?_ ?_
  · rw [← hdK, h1, map_zero]
  · rw [← hp, h2, map_zero]

end Transport

end CochainComplex

end
