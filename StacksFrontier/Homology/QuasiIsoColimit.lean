module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import StacksFrontier.Homology.HomologyColimit

/-!
# Quasi-isomorphisms and colimits

In an abelian category whose colimits of shape `J` are exact, a colimit of quasi-isomorphisms is
a quasi-isomorphism. This is the morphism-property form of
`Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor`: a quasi-isomorphism is a map
inducing an isomorphism on homology in every degree, the homology functors commute with the
colimit, and isomorphisms are stable under colimits of any shape.

## Main results

* `Stacks.HomologyColimit.isStableUnderColimitsOfShape_quasiIso`: the quasi-isomorphisms are
  stable under colimits of a shape whose colimits are exact.
* `Stacks.HomologyColimit.quasiIso_colimMap`: a natural transformation of `J`-shaped diagrams of
  complexes all of whose components are quasi-isomorphisms induces a quasi-isomorphism on the
  colimits.
* `Stacks.HomologyColimit.quasiIso_isStableUnderFilteredColimits`: in a Grothendieck abelian
  category, the quasi-isomorphisms are stable under all filtered colimits.

## Implementation notes

The proof of the first result is the whole content: everything else is a repackaging. Given
colimit cocones `c₁`, `c₂` on diagrams `X₁`, `X₂` of complexes and a compatible map
`φ : c₁.pt ⟶ c₂.pt` over a natural transformation `f : X₁ ⟶ X₂` with quasi-isomorphic
components, applying the degree-`i` homology functor `Φ` turns `c₁` and `c₂` into colimit cocones
(`CategoryTheory.Limits.isColimitOfPreserves`, which is where exactness of the colimits enters)
and turns `f` into a natural transformation with isomorphic components. So `Φ.map φ` is the map
induced on the colimits by an isomorphism of diagrams, and
`CategoryTheory.MorphismProperty.IsStableUnderColimitsOfShape.isomorphisms` applies.

No filteredness is needed for the first two results: only `HasExactColimitsOfShape`, which for a
non-filtered shape is a strong assumption but is not used here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v

namespace Stacks.HomologyColimit

variable {A : Type v} [Category.{w} A] [Abelian A]

/-- **The quasi-isomorphisms are stable under colimits of a shape whose colimits are exact.**
A map between the vertices of colimit cocones which is compatible with a natural transformation
of quasi-isomorphisms is a quasi-isomorphism. -/
lemma isStableUnderColimitsOfShape_quasiIso {J : Type*} [Category J]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] {ι : Type*} (c : ComplexShape ι) :
    (HomologicalComplex.quasiIso A c).IsStableUnderColimitsOfShape J where
  condition X₁ X₂ c₁ c₂ h₁ h₂ f hf φ hφ := by
    rw [HomologicalComplex.mem_quasiIso_iff, quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have := preservesColimitsOfShape_homologyFunctor (A := A) (J := J) c i
    set Φ := HomologicalComplex.homologyFunctor A c i with hΦ
    have hiso : ∀ j, IsIso ((Functor.whiskerRight f Φ).app j) := fun j => by
      have : QuasiIso (f.app j) := hf j
      exact (quasiIsoAt_iff_isIso_homologyMap (f.app j) i).mp inferInstance
    exact (MorphismProperty.IsStableUnderColimitsOfShape.isomorphisms A J).condition
      (X₁ ⋙ Φ) (X₂ ⋙ Φ) (Φ.mapCocone c₁) (Φ.mapCocone c₂)
      (isColimitOfPreserves Φ h₁) (isColimitOfPreserves Φ h₂)
      (Functor.whiskerRight f Φ) hiso (Φ.map φ)
      (fun j => by
        change Φ.map (c₁.ι.app j) ≫ Φ.map φ = Φ.map (f.app j) ≫ Φ.map (c₂.ι.app j)
        rw [← Φ.map_comp, ← Φ.map_comp, hφ j])

/-- **A colimit of quasi-isomorphisms is a quasi-isomorphism**, in the form of the map induced on
the chosen colimits by a natural transformation of diagrams of complexes. -/
lemma quasiIso_colimMap {J : Type*} [Category J] [HasColimitsOfShape J A]
    [HasExactColimitsOfShape J A] {ι : Type*} {c : ComplexShape ι}
    {X₁ X₂ : J ⥤ HomologicalComplex A c} (f : X₁ ⟶ X₂) (hf : ∀ j, QuasiIso (f.app j)) :
    QuasiIso (colimMap f) :=
  have := isStableUnderColimitsOfShape_quasiIso (A := A) (J := J) c
  MorphismProperty.colimMap (W := HomologicalComplex.quasiIso A c) f fun j => hf j

/-- **In a Grothendieck abelian category the quasi-isomorphisms are stable under filtered
colimits.** -/
instance quasiIso_isStableUnderFilteredColimits [IsGrothendieckAbelian.{w} A]
    {ι : Type*} (c : ComplexShape ι) :
    MorphismProperty.IsStableUnderFilteredColimits.{w, w}
      (HomologicalComplex.quasiIso A c) where
  isStableUnderColimitsOfShape _ _ _ := isStableUnderColimitsOfShape_quasiIso c

end Stacks.HomologyColimit

end
