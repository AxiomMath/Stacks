module

public import StacksFrontier.Topology.Simplicial.AugmentationFibrePartTwo

/-!
# The higher direct images along an augmentation, as fibre cohomology

**[Stacks, Tag 0D84].** Let `X` be a simplicial topological space, let `a : X ⟶ Y` be an
augmentation and let `F` be an abelian sheaf on `X_Zar`.  Then `Rⁿa_*F` is the sheaf associated
to the presheaf

`V ↦ Hⁿ((X ×_Y V)_Zar, F|_{(X ×_Y V)_Zar})`.

The sheafification half is
`Stacks.Topology.Simplicial.higherDirectImage_iso_sheafify_augmentationCohomologyPresheaf`;
this file supplies the identification of the values of that presheaf with the cohomology of the
fibre, which is what the two parts of the source proof are for:

* part (1), that restriction to `(X ×_Y V)_Zar` carries injective abelian sheaves to injective
  abelian sheaves, so that an injective resolution of `F` restricts to one of `F|`
  (`Stacks.Topology.Simplicial.fibreRestrictionAb_preservesInjectiveObjects`);
* part (2), that the sections of `a_*F` over `V` are the global sections of `F|`
  (`Stacks.Topology.Simplicial.augmentationFibreSections_iso_fibreRestrictedSections`).

Together they say that the `n`-th right derived functor of `F ↦ (a_*F)(V)` is
`Hⁿ((X ×_Y V)_Zar, F|)`.

## Main results

* `Stacks.Topology.Simplicial.augmentationCohomologyPresheaf_obj_iso_fibreCohomology`: **the
  value over `V` of the cohomology presheaf of the augmentation is `Hⁿ((X ×_Y V)_Zar, F|)`.**
* `Stacks.Topology.Simplicial.higherDirectImage_iso_sheafify_fibreCohomology`: **Stacks 0D84**,
  the two halves together.

## References

* [Stacks Project, Tag 0D84](https://stacks.math.columbia.edu/tag/0D84)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Topology.Simplicial

variable (X : SimplicialObject TopCat.{u}) (Y : TopCat.{u})
  (a : X ⟶ (SimplicialObject.const TopCat).obj Y)

section Pointwise

variable (V : Opens Y)

/-- **Stacks 0D84.** The value over an open `V` of the target of the cohomology presheaf of an
augmentation is the cohomology `Hⁿ((X ×_Y V)_Zar, F|)` of the restriction of `F` to the total
site of the fibre `X ×_Y V`.

This is the displayed rule of the statement.  Three steps: the value of the cohomology presheaf
over `V` is the `n`-th right derived functor of the sections of the direct image over `V`
(exactness of evaluation); those sections are the global sections of the restriction to the
fibre, which is part (2) of the source proof; and the derived functors of the global sections of
the restriction are the cohomology of the fibre, because restriction is exact and carries
injectives to injectives, which is part (1) of the source proof. -/
@[stacks 0D84 "the values of the displayed presheaf are the cohomology of the fibre"]
theorem augmentationCohomologyPresheaf_obj_iso_fibreCohomology (n : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    Nonempty (((augmentationCohomologyPresheaf X Y a n).obj F).obj (op V) ≅
      (fibreCohomology X Y a V n).obj ((fibreRestrictionAb X Y a V).obj F)) := by
  obtain ⟨e⟩ := augmentationCohomologyPresheaf_evaluation_iso X Y a n F V
  exact ⟨e ≪≫ (ModuleSheafCohomology.rightDerivedIso
      (augmentationFibreSections_iso_fibreRestrictedSections X Y a V) n).app F ≪≫
    fibreRestrictedSections_rightDerived_iso X Y a V n F⟩

end Pointwise

/-- **Stacks 0D84.** Let `X` be a simplicial space, let `a : X ⟶ Y` be an augmentation and let
`F` be an abelian sheaf on `X_Zar`.  Then `Rⁿa_*F` is the sheaf associated to the presheaf whose
value over an open `V` of `Y` is `Hⁿ((X ×_Y V)_Zar, F|_{(X ×_Y V)_Zar})`. -/
@[stacks 0D84]
theorem higherDirectImage_iso_sheafify_fibreCohomology (n : ℕ)
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u}) :
    Nonempty (((augmentationPushforwardAb X Y a).rightDerived n).obj F ≅
        (presheafToSheaf (Opens.grothendieckTopology Y) Ab.{u}).obj
          ((augmentationCohomologyPresheaf X Y a n).obj F)) ∧
      ∀ V : Opens Y,
        Nonempty (((augmentationCohomologyPresheaf X Y a n).obj F).obj (op V) ≅
          (fibreCohomology X Y a V n).obj ((fibreRestrictionAb X Y a V).obj F)) :=
  ⟨higherDirectImage_iso_sheafify_augmentationCohomologyPresheaf X Y a n F,
    fun V => augmentationCohomologyPresheaf_obj_iso_fibreCohomology X Y a V n F⟩

end Stacks.Topology.Simplicial

end
