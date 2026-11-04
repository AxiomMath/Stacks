module

public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Injectivity and surjectivity of a map on cohomology, in terms of elements

For a chain map `φ : K ⟶ L` of cochain complexes of modules over a ring, injectivity and
surjectivity of `Hʲ(φ)` are the familiar statements about cocycles and coboundaries. Mathlib
states them for an arbitrary abelian category "up to refinements"; this file reads those
statements off on elements, which is the form in which they are checked on Čech complexes.

## Main results

* `HomologicalComplex.mono_homologyMap_iff_elementwise`
* `HomologicalComplex.epi_homologyMap_iff_elementwise`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace HomologicalComplex

variable {R : Type u} [CommRing R] {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c} (φ : K ⟶ L)

private lemma epi_linearCombination_id (A : ModuleCat.{u} R) :
    Epi (ModuleCat.ofHom (Finsupp.linearCombination R (fun a : A => a))) :=
  (ModuleCat.epi_iff_surjective _).2 fun a => ⟨Finsupp.single a 1, by simp⟩

/-- Precomposing `m ↦ r • m` with a map `π` sending `a` to `1` gives back `m` at `a`. -/
private lemma comp_toSpanSingleton_apply {A M : ModuleCat.{u} R} (π : A ⟶ ModuleCat.of R R)
    {a : A} (ha : π a = 1) (m : M) :
    (π ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R M m)) a = m := by
  simp [ha]

/-- **Injectivity of `Hʲ(φ)` on elements.** `Hʲ(φ)` is injective exactly when every cocycle of
`K` whose image is a coboundary of `L` is a coboundary of `K`. -/
theorem mono_homologyMap_iff_elementwise (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    Mono (homologyMap φ j) ↔
      ∀ x : K.X j, K.d j k x = 0 → ∀ y : L.X i, φ.f j x = L.d i j y →
        ∃ w : K.X i, K.d i j w = x := by
  rw [mono_homologyMap_iff_up_to_refinements φ i j k hi hk]
  constructor
  · intro h x hx y hy
    obtain ⟨A', π, hπ, x₁, hx₁⟩ := h (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x))
      (by ext; simpa using hx) (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ y))
      (by ext; simpa using hy)
    obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective π).1 hπ 1
    exact ⟨x₁ a, ((comp_toSpanSingleton_apply π ha x).symm.trans congr($hx₁ a)).symm⟩
  · intro h A x₂ hx₂ y₁ hy₁
    choose w hw using fun a : A =>
      h (x₂ a) (by simpa using congr($hx₂ a)) (y₁ a) (by simpa using congr($hy₁ a))
    refine ⟨ModuleCat.of R (A →₀ R), ModuleCat.ofHom (Finsupp.linearCombination R (fun a => a)),
      epi_linearCombination_id A,
      ModuleCat.ofHom (Finsupp.linearCombination R w), ?_⟩
    ext a
    simp [hw]

/-- **Surjectivity of `Hʲ(φ)` on elements.** `Hʲ(φ)` is surjective exactly when every cocycle
of `L` is the image of a cocycle of `K` up to a coboundary. -/
theorem epi_homologyMap_iff_elementwise (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    Epi (homologyMap φ j) ↔
      ∀ y : L.X j, L.d j k y = 0 → ∃ x : K.X j, K.d j k x = 0 ∧
        ∃ y₁ : L.X i, y = φ.f j x + L.d i j y₁ := by
  rw [epi_homologyMap_iff_up_to_refinements φ i j k hi hk]
  constructor
  · intro h y hy
    obtain ⟨A', π, hπ, x₂, hx₂, y₁, hy₁⟩ := h (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ y))
      (by ext; simpa using hy)
    obtain ⟨a, ha⟩ := (ModuleCat.epi_iff_surjective π).1 hπ 1
    refine ⟨x₂ a, by simpa using congr($hx₂ a), y₁ a, ?_⟩
    simpa using (comp_toSpanSingleton_apply π ha y).symm.trans congr($hy₁ a)
  · intro h A y₂ hy₂
    choose x hx y₁ hy₁ using fun a : A => h (y₂ a) (by simpa using congr($hy₂ a))
    refine ⟨ModuleCat.of R (A →₀ R), ModuleCat.ofHom (Finsupp.linearCombination R (fun a => a)),
      epi_linearCombination_id A,
      ModuleCat.ofHom (Finsupp.linearCombination R x), ?_,
      ModuleCat.ofHom (Finsupp.linearCombination R y₁), ?_⟩
    · ext a
      simp [hx]
    · ext a
      simp [hy₁]

end HomologicalComplex
