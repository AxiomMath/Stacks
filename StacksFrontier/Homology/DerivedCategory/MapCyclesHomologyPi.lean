module

public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# An exact functor, the cycles of a complex, and the projection onto homology

For a functor `F` preserving the left homology of a short complex `S`, the comparison
`CategoryTheory.ShortComplex.mapCyclesIso` of cycles is compatible with the projection
`CategoryTheory.ShortComplex.homologyπ` of the cycles onto the homology. This is also stated for
`HomologicalComplex.cycles` under an exact functor.

## Main results

* `StacksDraft.DerivedCategoryHomology.mapCyclesIso_hom_map_homologyπ`:
  `(S.mapCyclesIso F).hom ≫ F.map S.homologyπ = (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom`.
* `StacksDraft.DerivedCategoryHomology.mapHomologicalComplexCyclesIso`: the cycles comparison of
  a complex, `((F.mapHomologicalComplex c).obj K).cycles i ≅ F.obj (K.cycles i)`.
* `StacksDraft.DerivedCategoryHomology.mapHomologicalComplexCyclesIso_hom_map_homologyπ`: the
  same square on a complex, against
  `StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso`.

## Implementation notes

The proof works at the left homology data `S.homologyData.left` rather than through
`CategoryTheory.ShortComplex.LeftHomologyData.mapCyclesIso_eq`, which is stated with
`backward.isDefEq.respectTransparency` turned off and leaves goals that are not type-correct at
`implicit` transparency after rewriting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.DerivedCategoryHomology

section ShortComplexes

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]

/-- For `S` a short complex with homology and `F` a functor preserving its left homology, the
square
`(S.mapCyclesIso F).hom ≫ F.map S.homologyπ = (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom`
commutes. -/
theorem mapCyclesIso_hom_map_homologyπ (S : ShortComplex C) (F : C ⥤ D)
    [F.PreservesZeroMorphisms] [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).hom ≫ F.map S.homologyπ =
      (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom := by
  have : Mono (F.map S.homologyData.left.i) :=
    inferInstanceAs (Mono ((S.homologyData.left.map F).i))
  have hA : (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.homologyData.left.map F).cyclesIso.hom ≫ F.map S.homologyData.left.π :=
    ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom (S.map F)
      (S.homologyData.left.map F)
  have hB : S.homologyData.left.cyclesIso.hom ≫ S.homologyData.left.π = S.homologyπ :=
    (ShortComplex.LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom
      S.homologyData.left).symm
  have hC : (S.mapCyclesIso F).hom ≫ F.map S.homologyData.left.cyclesIso.hom =
      (S.homologyData.left.map F).cyclesIso.hom := by
    refine (cancel_mono (F.map S.homologyData.left.i)).mp ?_
    rw [Category.assoc, ← Functor.map_comp,
      ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i,
      ShortComplex.mapCyclesIso_hom_iCycles]
    exact (ShortComplex.LeftHomologyData.cyclesIso_hom_comp_i
      (S.homologyData.left.map F)).symm
  have hD : (S.mapCyclesIso F).hom ≫ F.map S.homologyπ =
      ((S.mapCyclesIso F).hom ≫ F.map S.homologyData.left.cyclesIso.hom) ≫
        F.map S.homologyData.left.π := by
    rw [Category.assoc, ← Functor.map_comp]
    exact congrArg (fun z => (S.mapCyclesIso F).hom ≫ F.map z) hB.symm
  exact hD.trans ((congrArg (· ≫ F.map S.homologyData.left.π) hC).trans hA.symm)

end ShortComplexes

section Complexes

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) (i : ι)

/-- The isomorphism `((F.mapHomologicalComplex c).obj K).cycles i ≅ F.obj (K.cycles i)` for an
exact functor `F`. -/
noncomputable def mapHomologicalComplexCyclesIso :
    ((F.mapHomologicalComplex c).obj K).cycles i ≅ F.obj (K.cycles i) :=
  (K.sc i).mapCyclesIso F

/-- The cycles comparison `mapHomologicalComplexCyclesIso` of an exact functor is compatible
with the projection onto homology and the homology comparison
`StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso`. -/
theorem mapHomologicalComplexCyclesIso_hom_map_homologyπ :
    (mapHomologicalComplexCyclesIso F K i).hom ≫ F.map (K.homologyπ i) =
      ((F.mapHomologicalComplex c).obj K).homologyπ i ≫
        ((mapHomologicalComplexHomologyIso F c i).app K).hom :=
  mapCyclesIso_hom_map_homologyπ (K.sc i) F

end Complexes

end StacksDraft.DerivedCategoryHomology

end
