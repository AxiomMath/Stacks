module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative

/-!
# Exactness of sheaves of modules on a scheme is tested on affine opens

Let `X` be a scheme.  A short complex `T` of `𝒪_X`-modules is exact with epimorphic second map as
soon as, for every affine open `U` of `X`, the short complex of abelian groups of sections over
`U` is: the affine opens form a basis of the topology of `X`, and both conditions are local
surjectivity statements.

## Main results

* `AlgebraicGeometry.Scheme.epi_of_surjective_of_isAffineOpen`: a morphism of `𝒪_X`-modules
  which is surjective on sections over every affine open is an epimorphism.
* `AlgebraicGeometry.Scheme.exact_and_epi_of_isAffineOpen`: a short complex of `𝒪_X`-modules
  which is exact with epimorphic second map on sections over every affine open is exact with
  epimorphic second map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- **A morphism of `𝒪_X`-modules which is surjective on sections over every affine open is an
epimorphism**: it is locally surjective, the affine opens being a basis of the topology. -/
theorem epi_of_surjective_of_isAffineOpen {M N : SheafOfModules.{u} X.ringCatSheaf}
    (f : M ⟶ N) (hf : ∀ U : X.Opens, IsAffineOpen U → Function.Surjective (f.val.app (op U))) :
    Epi f := by
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {U} s => ?_⟩
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
  obtain ⟨t, ht⟩ := hf V hV (N.val.map (homOfLE hVU).op s)
  exact ⟨V, homOfLE hVU, ⟨t, ht⟩, hxV⟩

/-- Over an open `U`, if the short complex of sections of `T` is exact, then the map from the
first term of `T` to its cycles is surjective on sections: a section of the cycles is a section
of the second term killed by the second map, hence comes from the first term, and the inclusion
of the cycles stays injective on sections. -/
private theorem surjective_map_toCycles (T : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (U : X.Opens)
    (h : (T.map (SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
      forget₂ _ AddCommGrpCat.{u})).Exact) :
    Function.Surjective ((SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
      forget₂ _ AddCommGrpCat.{u}).map T.toCycles) := by
  set Φ := SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙ forget₂ _ AddCommGrpCat.{u}
  have hinj : Function.Injective (Φ.map T.iCycles) :=
    (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  intro y
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).1 h (Φ.map T.iCycles y) (by
    show (Φ.map T.iCycles ≫ Φ.map T.g) y = 0
    rw [← Φ.map_comp, T.iCycles_g, Φ.map_zero]
    rfl)
  refine ⟨x, hinj ?_⟩
  show (Φ.map T.toCycles ≫ Φ.map T.iCycles) x = _
  rw [← Φ.map_comp, T.toCycles_i]
  exact hx

/-- **A short complex of `𝒪_X`-modules which is exact with epimorphic second map on sections over
every affine open is exact with epimorphic second map.**  Both the second map and the map from the
first term to the cycles are then surjective on sections over every affine open, hence
epimorphisms. -/
theorem exact_and_epi_of_isAffineOpen (T : ShortComplex (SheafOfModules.{u} X.ringCatSheaf))
    (h : ∀ U : X.Opens, IsAffineOpen U →
      (T.map (SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
        forget₂ _ AddCommGrpCat.{u})).Exact ∧
        Epi (T.map (SheafOfModules.evaluation X.ringCatSheaf (op U) ⋙
          forget₂ _ AddCommGrpCat.{u})).g) :
    T.Exact ∧ Epi T.g := by
  refine ⟨?_, epi_of_surjective_of_isAffineOpen _ fun U hU => ?_⟩
  · rw [T.exact_iff_epi_toCycles]
    exact epi_of_surjective_of_isAffineOpen _ fun U hU => surjective_map_toCycles T U (h U hU).1
  · exact (AddCommGrpCat.epi_iff_surjective _).1 (h U hU).2

end AlgebraicGeometry.Scheme

end
