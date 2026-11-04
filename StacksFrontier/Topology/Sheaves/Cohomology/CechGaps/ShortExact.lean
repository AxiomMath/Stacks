module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechGaps.Decode
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Short exactness of the Čech complexes of a short exact sequence

A short complex of abelian presheaves that is short exact on every open occurring in the Čech
complexes of a family of opens gives a short exact sequence of Čech complexes: each term of a Čech
complex is a product of sections over such opens, and a product of short exact sequences of abelian
groups is short exact.

## Main results

* `Stacks.CechGaps.shortExact_piShortComplex`: a product of short exact sequences of abelian
  groups is short exact.
* `Stacks.CechGaps.shortExact_map_cechComplexFunctor`: the Čech complexes of a short complex of
  abelian presheaves form a short exact sequence of cochain complexes as soon as the short
  complex is short exact over every open occurring in those complexes.
* `Stacks.CechGaps.shortExact_map_secF`: `Γ(W, -)` takes a short exact sequence of
  `𝒪_X`-modules to a short exact sequence as soon as it is surjective on the last map.
* `Stacks.CechGaps.pi_ext`, `Stacks.CechGaps.piMap_π_apply`: the element-level API for a product
  in `AddCommGrpCat`.

## References

* [Stacks Project, Tag 01EU](https://stacks.math.columbia.edu/tag/01EU)
* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u u₂

namespace Stacks.CechGaps

section Products

variable {J : Type u} {A B : J → AddCommGrpCat.{u}}

/-- An element of a product of abelian groups is determined by its components. -/
lemma pi_ext (a b : ToType (∏ᶜ A)) (h : ∀ j, Limits.Pi.π A j a = Limits.Pi.π A j b) : a = b :=
  (Limits.Concrete.productEquiv A).injective
    (funext fun j ↦ by simpa only [Limits.Concrete.productEquiv_apply_apply] using h j)

/-- The components of `Limits.Pi.map p` applied to an element. -/
lemma piMap_π_apply (p : ∀ j, A j ⟶ B j) (a : ToType (∏ᶜ A)) (j : J) :
    Limits.Pi.π B j (Limits.Pi.map p a) = p j (Limits.Pi.π A j a) :=
  (ConcreteCategory.comp_apply _ _ a).symm.trans
    (congrArg (fun h : (∏ᶜ A) ⟶ B j ↦ ConcreteCategory.hom h a) (Limits.Pi.map_π p j) |>.trans
      (ConcreteCategory.comp_apply _ _ a))

variable (T : J → ShortComplex AddCommGrpCat.{u})

/-- The three products of a family of short complexes of abelian groups do form a short
complex. -/
lemma piShortComplex_zero :
    (Limits.Pi.map fun j ↦ (T j).f) ≫ (Limits.Pi.map fun j ↦ (T j).g) = 0 :=
  Limits.Pi.hom_ext _ _ fun j ↦ by
    rw [Limits.zero_comp, Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc,
      (T j).zero, Limits.comp_zero]

/-- The product of the short complexes `T j`, formed with `Limits.Pi.map`. -/
noncomputable abbrev piShortComplex : ShortComplex AddCommGrpCat.{u} :=
  ShortComplex.mk _ _ (piShortComplex_zero T)

/-- An element of a product is in the image of `Limits.Pi.map p` if it is so componentwise. -/
private theorem exists_piMap_eq (p : ∀ j, A j ⟶ B j) (c : ToType (∏ᶜ B))
    (h : ∀ j, ∃ a, p j a = Limits.Pi.π B j c) : ∃ a, Limits.Pi.map p a = c := by
  choose a ha using h
  refine ⟨(Limits.Concrete.productEquiv A).symm a, pi_ext _ _ fun j ↦ ?_⟩
  rw [piMap_π_apply, Limits.Concrete.productEquiv_symm_apply_π]
  exact ha j

/-- A product of short exact sequences of abelian groups is short exact. -/
theorem shortExact_piShortComplex (h : ∀ j, (T j).ShortExact) : (piShortComplex T).ShortExact where
  mono_f := by
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    refine pi_ext _ _ fun j ↦ ?_
    refine (AddCommGrpCat.mono_iff_injective _).1 (h j).mono_f ?_
    rw [← piMap_π_apply (fun j ↦ (T j).f), ← piMap_π_apply (fun j ↦ (T j).f)]
    exact congrArg _ hab
  epi_g := by
    rw [AddCommGrpCat.epi_iff_surjective]
    exact fun c ↦ exists_piMap_eq _ c fun j ↦
      (AddCommGrpCat.epi_iff_surjective _).1 (h j).epi_g _
  exact := by
    rw [ShortComplex.ab_exact_iff]
    intro b hb
    have hb' : Limits.Pi.map (fun j ↦ (T j).g) b = 0 := hb
    exact exists_piMap_eq _ b fun j ↦ ((ShortComplex.ab_exact_iff (T j)).1 (h j).exact) _
      (by rw [← piMap_π_apply (fun j ↦ (T j).g), hb', map_zero])

end Products

section Cech

variable {X : Type u} [TopologicalSpace X] {ι : Type u} (U : ι → Opens X)

/-- The Čech complexes of a short complex of abelian presheaves form a short exact sequence of
cochain complexes as soon as the short complex is short exact on every open that occurs in the
Čech complexes. -/
@[ega "III 1.2.5" "partial"]
theorem shortExact_map_cechComplexFunctor
    (S : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}))
    (h : ∀ (n : ℕ) (x : Fin (n + 1) → ι),
      (S.map ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (∏ᶜ (U ∘ x))))).ShortExact) :
    (S.map (cechComplexFunctor U)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    shortExact_piShortComplex
      (fun x : Fin (n + 1) → ι ↦
        S.map ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (∏ᶜ (U ∘ x)))))
      (h n)

end Cech

section Modules

open Stacks.CohomologyVanishing

variable {X : Type u} [TopologicalSpace X]
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u₂})

/-- Sections over an open take a short exact sequence of `𝒪_X`-modules to a short exact sequence
as soon as they are surjective on the last map. -/
theorem shortExact_map_secF (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (W : Opens X) (hepi : Epi ((secF R W).map S.g)) : (S.map (secF R W)).ShortExact :=
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono (secF R W)).1
    inferInstance S hS
  { mono_f := h.2, epi_g := hepi, exact := h.1 }

end Modules

end Stacks.CechGaps
