module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible

/-!
# Exactness of sheaves of modules is tested on enough objects

Let `(C, J)` be a site, `R` a sheaf of rings on it and `P` a class of objects of `C` such that
every object has a covering by objects of `P` (the site *has enough `P` objects*,
[Stacks, Tag 090L] (3)). A morphism of sheaves of `R`-modules which is surjective on sections over
every object of `P` is an epimorphism, and a short complex of sheaves of `R`-modules which is exact
with epimorphic second map on sections over every object of `P` is exact with epimorphic second
map.

This is the site-theoretic form of
`AlgebraicGeometry.Scheme.exact_and_epi_of_isAffineOpen`, where the affine opens of a scheme play
the rôle of `P`.

## Main results

* `Stacks.SheafOfModules.EpiMono.epi_of_surjective_of_hasEnoughObjects`: a morphism of sheaves
  of modules which is surjective on sections over every object of `P` is an epimorphism.
* `Stacks.SheafOfModules.EpiMono.exact_and_epi_of_hasEnoughObjects`: a short complex of sheaves of
  modules which is exact with epimorphic second map on sections over every object of `P` is exact
  with epimorphic second map.

## References

* [Stacks Project, Tag 090L](https://stacks.math.columbia.edu/tag/090L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u' t

namespace Stacks.SheafOfModules.EpiMono

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- If every object is covered by objects of `P`, a morphism of sheaves of modules which is
surjective on sections over every object of `P` is an epimorphism. -/
theorem epi_of_surjective_of_hasEnoughObjects (P : ObjectProperty C) (hP : J.HasEnoughObjects P)
    {M N : SheafOfModules.{t} R} (f : M ⟶ N)
    (hf : ∀ U : C, P U → Function.Surjective (f.val.app (op U))) : Epi f := by
  refine epi_of_isLocallySurjective _ ⟨fun {U} s => ?_⟩
  obtain ⟨I, Ui, g, hcov, hPi⟩ := hP U
  refine J.superset_covering ?_ hcov
  rintro V _ ⟨W, a, b, ⟨i⟩, rfl⟩
  refine Sieve.downward_closed _ ?_ a
  exact hf (Ui i) (hPi i) (N.val.map (g i).op s)

variable [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- Over an object `U`, if the short complex of sections of `T` is exact, then the map from the
first term of `T` to its cycles is surjective on sections. -/
theorem surjective_map_toCycles (T : ShortComplex (SheafOfModules.{t} R)) (U : C)
    (h : (T.map (SheafOfModules.evaluation R (op U) ⋙
      forget₂ _ AddCommGrpCat.{t})).Exact) :
    Function.Surjective ((SheafOfModules.evaluation R (op U) ⋙
      forget₂ _ AddCommGrpCat.{t}).map T.toCycles) := by
  set Φ := SheafOfModules.evaluation R (op U) ⋙ forget₂ _ AddCommGrpCat.{t}
  have hinj : Function.Injective (Φ.map T.iCycles) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  intro y
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).1 h (Φ.map T.iCycles y) (by
    change (Φ.map T.iCycles ≫ Φ.map T.g) y = 0
    rw [← Φ.map_comp, T.iCycles_g, Φ.map_zero]
    rfl)
  refine ⟨x, hinj ?_⟩
  change (Φ.map T.toCycles ≫ Φ.map T.iCycles) x = _
  rwa [← Φ.map_comp, T.toCycles_i]

/-- If every object is covered by objects of `P`, a short complex of sheaves of modules which is
exact with epimorphic second map on sections over every object of `P` is exact with epimorphic
second map. -/
theorem exact_and_epi_of_hasEnoughObjects (P : ObjectProperty C) (hP : J.HasEnoughObjects P)
    (T : ShortComplex (SheafOfModules.{t} R))
    (h : ∀ U : C, P U →
      (T.map (SheafOfModules.evaluation R (op U) ⋙ forget₂ _ AddCommGrpCat.{t})).Exact ∧
        Epi (T.map (SheafOfModules.evaluation R (op U) ⋙ forget₂ _ AddCommGrpCat.{t})).g) :
    T.Exact ∧ Epi T.g := by
  refine ⟨?_, epi_of_surjective_of_hasEnoughObjects P hP _ fun U hU => ?_⟩
  · rw [T.exact_iff_epi_toCycles]
    exact epi_of_surjective_of_hasEnoughObjects P hP _ fun U hU =>
      surjective_map_toCycles T U (h U hU).1
  · exact (AddCommGrpCat.epi_iff_surjective _).1 (h U hU).2

end Stacks.SheafOfModules.EpiMono

end
