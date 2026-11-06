module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMapFunctoriality

/-!
# The descent of an invertible comparison of a square of additive functors

Let

```
A --G'--> C
|F        |F'
v         v
B --G-->  D
```

be a square of additive functors between abelian categories and let `τ : F ⋙ G ⟶ G' ⋙ F'` be a
comparison between the two composites.  `Stacks.Cohomology.BaseChange.derived` descends `τ` to
the bounded below derived categories.  **Invertibility of `τ` alone does not make the descent
invertible**: the descent compares `RG ∘ RF` with `RF' ∘ RG'`, and the right derived functor of a
composite is not the composite of the right derived functors unless the inner functor is
sufficiently exact.  What this file proves is that invertibility of `τ` *together with*
preservation of injective objects by the top horizontal functor `G'` does suffice.

The hypothesis is what makes `RG' ⋙ RF'` a right derived functor of `G' ⋙ F'`, by Grothendieck's
composition criterion: at a bounded below complex `K` of injective objects, `G'K` is again a
complex of injective objects, hence right acyclic for `F'`, so both derived-functor units
occurring in `Stacks.Cohomology.BaseChange.onHomotopy` are invertible there, and so are the two
remaining factors — the comparison `e` and `τ` applied degreewise.  Two right derived functors of
isomorphic functors are isomorphic, which is
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc`.

The intended instance is the base-change comparison of a square whose horizontal morphisms are
open immersions into the base: there the comparison is invertible for every module, and
restriction to an open subspace preserves injectives.

## Main results

* `Stacks.Cohomology.BaseChange.isIso_mapPlus`: the degreewise image of an invertible
  comparison is invertible.
* `Stacks.Cohomology.BaseChange.isRightDerivedFunctor_onHomotopy`: granted the two hypotheses,
  `RG' ⋙ RF'` is a right derived functor of the degreewise comparison.
* `Stacks.Cohomology.BaseChange.isIso_derived`: **the descent of an invertible comparison is
  invertible** when the top horizontal functor preserves injective objects.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

section Invertibility

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]

omit [EnoughInjectives A] in
/-- **The degreewise image of an invertible comparison is invertible.**  Applying a natural
transformation degreewise on the bounded below homotopy category is functorial, so it takes the
inverse of `τ` to an inverse of its image. -/
theorem isIso_mapPlus {E H : A ⥤ D} [E.Additive] [H.Additive] (τ : E ⟶ H) [IsIso τ] :
    IsIso (mapPlus τ) :=
  ⟨mapPlus (inv τ), by rw [← mapPlus_comp, IsIso.hom_inv_id, mapPlus_id],
    by rw [← mapPlus_comp, IsIso.inv_hom_id, mapPlus_id]⟩

omit [EnoughInjectives A] in
/-- The unit of `RF'` is invertible at the degreewise image under `G'` of a bounded below complex
of injective objects: `G'` preserves injectives, so the terms of that image are injective, hence
right acyclic for `F'`. -/
private theorem isIso_unit_mapHomotopyCategoryPlus [G'.PreservesInjectiveObjects]
    (M : HomotopyCategory.Plus A) (hM : ∀ n : ℤ, Injective (M.obj.as.X n)) :
    IsIso (F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj M)) := by
  refine Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic _ _ fun n => ?_
  have := hM n
  exact (show F'.rightAcyclic (G'.obj (M.obj.as.X n)) from
    Functor.rightAcyclic_of_injective F' (G'.obj (M.obj.as.X n)))

/-- **`RG' ⋙ RF'` is a right derived functor of the degreewise comparison** when `τ` is
invertible and `G'` preserves injective objects.  At a bounded below complex `K` of injective
objects all four factors of `Stacks.Cohomology.BaseChange.onHomotopy` are invertible: the
comparison `e`, the degreewise image of `τ`, the unit of `RF'` at `G'K` — a complex of injective
objects, hence right acyclic for `F'` — and the unit of `RG'` at `K`. -/
theorem isRightDerivedFunctor_onHomotopy (τ : F ⋙ G ⟶ G' ⋙ F') [IsIso τ]
    [G'.PreservesInjectiveObjects]
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus) :
    (G'.rightDerivedFunctorPlus ⋙ F'.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (onHomotopy F F' G G' τ e) (HomotopyCategory.Plus.quasiIso A) := by
  have := isIso_mapPlus τ
  refine (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
    fun K => ?_
  rw [onHomotopy_app]
  set X := (HomotopyCategory.Plus.localizerMorphism A).functor.obj K
  have : IsIso (e.inv.app (F.mapHomotopyCategoryPlus.obj X)) := NatIso.isIso_app_of_isIso _ _
  have : IsIso ((mapPlus τ).app X) := NatIso.isIso_app_of_isIso _ _
  have := isIso_unit_mapHomotopyCategoryPlus F' G' X
    (fun n => (inferInstance :
      Injective (((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj K).obj.as.X n)))
  have : IsIso (G'.rightDerivedFunctorPlusUnith.app X) :=
    inferInstanceAs (IsIso (G'.rightDerivedFunctorPlusUnith.app
      ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj K)))
  have : IsIso (DerivedCategory.Plus.Qh.map ((mapPlus τ).app X)) := inferInstance
  have : IsIso (F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app X)) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ ‹_›
    (@IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› (@IsIso.comp_isIso _ _ _ _ _ _ _ ‹_› ‹_›))

/-- **The descent of an invertible comparison is invertible** as soon as the top horizontal
functor preserves injective objects.  Both `RF ⋙ RG` and `RG' ⋙ RF'` are then right derived
functors of the same functor on the bounded below homotopy category, and the descent is the
comparison between them. -/
theorem isIso_derived (τ : F ⋙ G ⟶ G' ⋙ F') [IsIso τ] [G'.PreservesInjectiveObjects]
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus) :
    IsIso (derived F F' G G' τ e) := by
  have htarget := isRightDerivedFunctor_onHomotopy F F' G G' τ e
  let hRF : (F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (Functor.whiskerRight F.rightDerivedFunctorPlusUnith G.rightDerivedFunctorPlus ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso A) :=
    (HomotopyCategory.Plus.localizerMorphism_derives _).isRightDerivedFunctor_of_isIso _
      (fun K ↦ by dsimp; infer_instance)
  unfold derived
  exact (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc _ _ _ _ _).1 htarget

end Invertibility

end Stacks.Cohomology.BaseChange

end
