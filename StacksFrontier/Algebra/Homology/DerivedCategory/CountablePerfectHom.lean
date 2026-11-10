module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import StacksFrontier.Algebra.Homology.DerivedCategory.CountableHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationTriangle
public import StacksFrontier.Homology.Perfect.Defs

/-!
# Morphisms out of a perfect complex into a complex with countable homology

Let `R` be a ring, `P` a perfect object of `D(R)` and `N` an object of `D(R)` all of whose
homology modules are countable. Then `Hom_{D(R)}(P, N)` is countable.

A finite projective module `Q` placed in degree `q` corepresents `Hom_R(Q, H^q(-))`, which is
countable on `N` since `Q` is finitely generated; a perfect object is built from such objects by
the distinguished triangles of the stupid filtration of a bounded complex, and countability
of `Hom(-, N)` passes from the outer vertices of a distinguished triangle to the middle one.

## Main results

* `Stacks.Homology.countable_linearMap_of_finite`: `Hom_R(Q, M)` is countable for `Q` finite and
  `M` countable.
* `Stacks.Homology.countable_hom_of_isPerfect`: `Hom_{D(R)}(P, N)` is countable.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w u

namespace Stacks.Homology

/-- **Linear maps out of a finite module into a countable module form a countable set**: such a
map is determined by its values on a finite generating family. -/
theorem countable_linearMap_of_finite {R : Type*} [Ring R] (Q M : Type*) [AddCommGroup Q]
    [Module R Q] [AddCommGroup M] [Module R M] [Module.Finite R Q] [Countable M] :
    Countable (Q →ₗ[R] M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin (R := R) (M := Q)
  exact Function.Injective.countable (f := fun φ : Q →ₗ[R] M => fun i => φ (f i))
    fun φ ψ h => LinearMap.ext_on_range hf fun i => congrFun h i

variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]

/-- **Countability of `Hom(-, N)` passes to the middle vertex of a distinguished triangle.** -/
theorem countable_hom_obj₂ (T : Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang (DerivedCategory (ModuleCat.{u} R)))
    (N : DerivedCategory (ModuleCat.{u} R))
    (h₁ : Countable (T.obj₁ ⟶ N)) (h₃ : Countable (T.obj₃ ⟶ N)) : Countable (T.obj₂ ⟶ N) := by
  classical
  let s : (T.obj₁ ⟶ N) → (T.obj₂ ⟶ N) := fun a =>
    if h : ∃ f' : T.obj₂ ⟶ N, T.mor₁ ≫ f' = a then h.choose else 0
  have hex : ∀ f : T.obj₂ ⟶ N, ∃ g : T.obj₃ ⟶ N, f = s (T.mor₁ ≫ f) + T.mor₂ ≫ g := by
    intro f
    have h : ∃ f' : T.obj₂ ⟶ N, T.mor₁ ≫ f' = T.mor₁ ≫ f := ⟨f, rfl⟩
    have hs : s (T.mor₁ ≫ f) = h.choose := dite_eq_left h
    obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ T hT (f - h.choose) (by
      rw [Preadditive.comp_sub, h.choose_spec, sub_self])
    exact ⟨g, by rw [hs, ← hg, add_sub_cancel]⟩
  refine Function.Injective.countable
    (f := fun f : T.obj₂ ⟶ N => (T.mor₁ ≫ f, (hex f).choose)) ?_
  intro f f' hff'
  simp only [Prod.mk.injEq] at hff'
  calc f = s (T.mor₁ ≫ f) + T.mor₂ ≫ (hex f).choose := (hex f).choose_spec
    _ = s (T.mor₁ ≫ f') + T.mor₂ ≫ (hex f').choose := by rw [hff'.2, hff'.1]
    _ = f' := (hex f').choose_spec.symm

/-- **Morphisms out of a perfect object of `D(R)` into an object with countable homology form a
countable set.** -/
theorem countable_hom_of_isPerfect {P : DerivedCategory (ModuleCat.{u} R)}
    (hP : StacksDraft.Perfect.IsPerfect P) {N : DerivedCategory (ModuleCat.{u} R)}
    (hN : HasCountableHomology N) : Countable (P ⟶ N) := by
  obtain ⟨K, a, b, hGE, hLE, hfin, hproj, ⟨e⟩⟩ := hP
  have hiso : ∀ {X Y : DerivedCategory (ModuleCat.{u} R)}, (X ≅ Y) →
      Countable (X ⟶ N) → Countable (Y ⟶ N) := fun e h =>
    Function.Injective.countable (f := fun g => e.hom ≫ g) fun g g' hg => by
      simpa using congrArg (e.inv ≫ ·) hg
  refine hiso e.symm
    (Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex_of_distTriang
      (fun X => Countable (X ⟶ N)) hiso (fun X hX => ?_)
      (fun T hT h₁ h₃ => countable_hom_obj₂ T hT N h₁ h₃) K ?_ fun i => ?_)
  · have : Subsingleton (X ⟶ N) := ⟨fun f g => hX.eq_of_src f g⟩
    infer_instance
  · refine (Set.finite_Icc a b).subset fun i hi => ?_
    simp only [Set.mem_ofPred_eq] at hi
    simp only [Set.mem_Icc]
    constructor <;> by_contra h
    · exact hi (CochainComplex.isZero_of_isStrictlyGE K a i (by omega))
    · exact hi (CochainComplex.isZero_of_isStrictlyLE K b i (by omega))
  · have : Projective (K.X i) := (IsProjective.iff_projective (ModuleCat.of R (K.X i))).mp (hproj i)
    have : Module.Finite R (K.X i) := hfin i
    have : Countable ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj N) := hN i
    have := countable_linearMap_of_finite (R := R) (K.X i)
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj N)
    have : Countable (K.X i ⟶ (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj N) :=
      Function.Injective.countable (f := fun g => g.hom) fun g g' h => ModuleCat.hom_ext h
    exact Function.Injective.countable
      (_root_.DerivedCategory.homologyFromSingleAddEquiv (K.X i) N i).injective

/-- A finite module over a countable ring is countable. -/
theorem countable_of_finite_of_countable_ring {R : Type*} [Ring R] [Countable R] (M : Type*)
    [AddCommGroup M] [Module R M] [Module.Finite R M] : Countable M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hs : Function.Surjective (Fintype.linearCombination R f) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hf]
  exact hs.countable

/-- **A perfect object of `D(R)` over a countable ring has countable homology**: it is a bounded
complex of finite modules, each of which is countable, and homology is a subquotient. -/
theorem hasCountableHomology_of_isPerfect [Countable R] {P : DerivedCategory (ModuleCat.{u} R)}
    (hP : StacksDraft.Perfect.IsPerfect P) : HasCountableHomology P := by
  obtain ⟨K, a, b, -, -, hfin, -, ⟨e⟩⟩ := hP
  refine HasCountableHomology.of_iso e.symm fun i => ?_
  have : Module.Finite R (K.X i) := hfin i
  have : Countable (K.X i) := countable_of_finite_of_countable_ring (R := R) (K.X i)
  have h₁ : Countable (K.cycles i) :=
    Function.Injective.countable ((ModuleCat.mono_iff_injective (K.iCycles i)).1 inferInstance)
  have h₂ : Countable (K.homology i) :=
    Function.Surjective.countable ((ModuleCat.epi_iff_surjective (K.homologyπ i)).1 inferInstance)
  exact @Function.Injective.countable _ _ h₂ _
    ((_root_.DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app
      K).toLinearEquiv.injective

end Stacks.Homology

end
