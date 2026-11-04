module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Isomorphisms on cohomology of complexes of modules, on elements

A map `φ : K ⟶ L` of cochain complexes of `R`-modules induces an isomorphism on cohomology in
degree `n` as soon as, on elements, every cycle of `L` is cohomologous to the image of a cycle of
`K`, and every cycle of `K` whose image is a boundary is itself a boundary.

## Main results

* `HomologicalComplex.isIso_homologyMap_of_forall`: the criterion on elements for `φ` to induce an
  isomorphism on homology in degree `n`.
* `HomologicalComplex.exists_of_epi_homologyMap`: the converse on elements for an epimorphism.
* `HomologicalComplex.exists_of_mono_homologyMap`: the converse on elements for a monomorphism.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace HomologicalComplex

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{max u v} R) c}

/-- The map `(M →₀ R) ⟶ M` sending `Finsupp.single m 1` to `m` is an epimorphism. -/
theorem epi_ofHom_linearCombination_id (M : ModuleCat.{max u v} R) :
    Epi (ModuleCat.ofHom (Finsupp.linearCombination R (_root_.id : M → M))) :=
  (ModuleCat.epi_iff_surjective _).2 fun m => ⟨Finsupp.single m 1, by
    simp⟩

/-- Two morphisms out of the free module `M →₀ R` agree if they agree on every basis element
`Finsupp.single m 1`. -/
theorem ofHom_linearCombination_hom_ext (M : ModuleCat.{max u v} R) {N : ModuleCat.{max u v} R}
    {f g : ModuleCat.of R (M →₀ R) ⟶ N}
    (h : ∀ m : M, f.hom (Finsupp.single m 1) = g.hom (Finsupp.single m 1)) : f = g :=
  ModuleCat.hom_ext (Finsupp.lhom_ext' fun m => LinearMap.ext_ring (h m))

/-- **A criterion on elements for `φ` to be an isomorphism on cohomology in degree `n`.** If every
cycle of `L` is cohomologous to the image of a cycle of `K`, and every cycle of `K` whose image is
a boundary is a boundary, then `homologyMap φ n` is an isomorphism. -/
theorem isIso_homologyMap_of_forall (φ : K ⟶ L) (i n k : ι) (hi : c.prev n = i) (hk : c.next n = k)
    (hsurj : ∀ y : L.X n, L.d n k y = 0 →
      ∃ x : K.X n, K.d n k x = 0 ∧ ∃ y' : L.X i, y = φ.f n x + L.d i n y')
    (hinj : ∀ x : K.X n, K.d n k x = 0 → ∀ y : L.X i,
      φ.f n x = L.d i n y → ∃ z : K.X i, K.d i n z = x) :
    IsIso (HomologicalComplex.homologyMap φ n) := by
  have hmono : Mono (HomologicalComplex.homologyMap φ n) := by
    rw [HomologicalComplex.mono_homologyMap_iff_up_to_refinements φ i n k
      hi hk]
    intro A x₂ hx₂ y₁ hy₁
    have hz (a : A) : ∃ z : K.X i, K.d i n z = x₂ a :=
      hinj _ (by simpa using ConcreteCategory.congr_hom hx₂ a) (y₁ a)
        (by simpa using ConcreteCategory.congr_hom hy₁ a)
    refine ⟨_, _, epi_ofHom_linearCombination_id A,
      ModuleCat.ofHom (Finsupp.linearCombination R fun a => (hz a).choose), ?_⟩
    refine ofHom_linearCombination_hom_ext A fun a => ?_
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
      ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, Finsupp.linearCombination_single,
      Finsupp.linearCombination_single, one_smul, one_smul, id_eq]
    exact (hz a).choose_spec.symm
  have hepi : Epi (HomologicalComplex.homologyMap φ n) := by
    rw [HomologicalComplex.epi_homologyMap_iff_up_to_refinements φ i n k
      hi hk]
    intro A y₂ hy₂
    have hx (a : A) := hsurj (y₂ a) (by simpa using ConcreteCategory.congr_hom hy₂ a)
    refine ⟨_, _, epi_ofHom_linearCombination_id A,
      ModuleCat.ofHom (Finsupp.linearCombination R fun a => (hx a).choose), ?_,
      ModuleCat.ofHom (Finsupp.linearCombination R fun a => (hx a).choose_spec.2.choose), ?_⟩
    · refine ofHom_linearCombination_hom_ext A fun a => ?_
      simpa using (hx a).choose_spec.1
    · refine ofHom_linearCombination_hom_ext A fun a => ?_
      simpa using (hx a).choose_spec.2.choose_spec
  exact isIso_of_mono_of_epi _

/-- **Surjectivity on cohomology, on elements.** If `φ` is an epimorphism on cohomology in degree
`n`, every cycle of `L` is cohomologous to the image of a cycle of `K`. -/
theorem exists_of_epi_homologyMap (φ : K ⟶ L) (i n k : ι) (hi : c.prev n = i) (hk : c.next n = k)
    [Epi (HomologicalComplex.homologyMap φ n)] (y : L.X n) (hy : L.d n k y = 0) :
    ∃ x : K.X n, K.d n k x = 0 ∧ ∃ y' : L.X i, y = φ.f n x + L.d i n y' := by
  have h := (HomologicalComplex.epi_homologyMap_iff_up_to_refinements φ i n k
    hi hk).1 inferInstance
  obtain ⟨A', π, hπ, x₂, hx₂, y₁, hfac⟩ := h (A := ModuleCat.of R (ULift.{max u v} R))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ y ∘ₗ ULift.moduleEquiv.toLinearMap)) (by
      refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
      simp [hy])
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective π).1 hπ (ULift.up 1)
  refine ⟨x₂ a, by simpa using ConcreteCategory.congr_hom hx₂ a, y₁ a, ?_⟩
  have := ConcreteCategory.congr_hom hfac a
  simpa [ha] using this

/-- **Injectivity on cohomology, on elements.** If `φ` is a monomorphism on cohomology in degree
`n`, a cycle of `K` whose image is a boundary is a boundary. -/
theorem exists_of_mono_homologyMap (φ : K ⟶ L) (i n k : ι) (hi : c.prev n = i)
    (hk : c.next n = k) [Mono (HomologicalComplex.homologyMap φ n)] (x : K.X n)
    (hx : K.d n k x = 0) (y : L.X i) (hy : φ.f n x = L.d i n y) :
    ∃ z : K.X i, K.d i n z = x := by
  have h := (HomologicalComplex.mono_homologyMap_iff_up_to_refinements φ i n k hi hk).1
    inferInstance
  obtain ⟨A', π, hπ, x₁, hfac⟩ := h (A := ModuleCat.of R (ULift.{max u v} R))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x ∘ₗ ULift.moduleEquiv.toLinearMap)) (by
      refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
      simp [hx])
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ y ∘ₗ ULift.moduleEquiv.toLinearMap)) (by
      refine ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
      simp [hy])
  obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective π).1 hπ (ULift.up 1)
  refine ⟨x₁ a, ?_⟩
  have := ConcreteCategory.congr_hom hfac a
  simpa [ha] using this.symm

end HomologicalComplex

end
