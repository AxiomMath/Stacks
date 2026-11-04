module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# Base change for the direct image along a closed immersion, with module coefficients

For a commutative square
```
Z' --g'--> Z
|i'        |i
X' --g---> X
```
with `i` a closed immersion and `i'` a closed immersion whose open complement maps into the open
complement of `i`, the base change map `g^{-1} i_* ⟶ i'_* g'^{-1}` of sheaves of `Λ`-modules on the
small étale sites is an isomorphism.  This is the case of a closed immersion of
[Stacks, Tag 0959], at module coefficients and on Mathlib's small étale site.

The proof checks invertibility after the inverse images to `Z'` and to its open complement `U'`,
which jointly reflect isomorphisms: over `U'` both sides vanish, and over `Z'` the base change
map is, up to the counits of `i^{-1} ⊣ i_*` and `i'^{-1} ⊣ i'_*` (invertible as both direct images
are fully faithful), the comparison of the two composites around the square.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleBaseChange`: the base change map `g^{-1} f_* ⟶ f'_* g'^{-1}`
  of sheaves of modules for a commutative square.

## Main results

* `Stacks.EtaleCohomology.isIso_etaleModuleBaseChange_of_isClosedImmersion`.

## References

* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [Ring Λ] {Z Z' X X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (g : X' ⟶ X)
  (g' : Z' ⟶ Z) (w : i' ≫ g = g' ≫ i)

/-- **The base change map `g^{-1} i_* ⟶ i'_* g'^{-1}`** of sheaves of `Λ`-modules for a commutative
square `i' ≫ g = g' ≫ i`: the mate of the comparison `g^{-1} ⋙ i'^{-1} ≅ i^{-1} ⋙ g'^{-1}`. -/
def etaleModuleBaseChange :
    etaleModuleDirectImage.{u, r} Λ i ⋙ etaleModuleInverseImage.{u, r} Λ g ⟶
      etaleModuleInverseImage.{u, r} Λ g' ⋙ etaleModuleDirectImage.{u, r} Λ i' :=
  Stacks.CategoryTheory.BaseChange.twoSquare (etaleModuleInverseImageAdj.{u, r} Λ i)
    (etaleModuleInverseImageAdj.{u, r} Λ i') (etaleModuleInverseImageCompIso.{u, r} Λ i' g).symm
    ((etaleModuleInverseImageCompIso.{u, r} Λ g' i).symm ≪≫
      eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w.symm))

/-- The comparison `i^{-1} ⋙ g'^{-1} ≅ (i' ≫ g)^{-1}` of the base change square. -/
abbrev etaleModuleBaseChangeComparison :
    etaleModuleInverseImage.{u, r} Λ i ⋙ etaleModuleInverseImage.{u, r} Λ g' ≅
      etaleModuleInverseImage.{u, r} Λ (i' ≫ g) :=
  (etaleModuleInverseImageCompIso.{u, r} Λ g' i).symm ≪≫
    eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) w.symm)

/-- After the inverse image along `i'`, the base change map followed by the counit of
`i'^{-1} ⊣ i'_*` is the comparison of the two composites followed by `g'^{-1}` of the counit of
`i^{-1} ⊣ i_*`. -/
lemma inverseImage_map_etaleModuleBaseChange_comp_counit (M : EtaleModules.{u, r} Λ Z) :
    (etaleModuleInverseImage.{u, r} Λ i').map ((etaleModuleBaseChange Λ i i' g g' w).app M) ≫
        (etaleModuleInverseImageAdj.{u, r} Λ i').counit.app
          ((etaleModuleInverseImage.{u, r} Λ g').obj M) =
      (etaleModuleInverseImageCompIso.{u, r} Λ i' g).inv.app
          ((etaleModuleDirectImage.{u, r} Λ i).obj M) ≫
        (etaleModuleBaseChangeComparison Λ i i' g g' w).inv.app
          ((etaleModuleDirectImage.{u, r} Λ i).obj M) ≫
        (etaleModuleInverseImage.{u, r} Λ g').map
          ((etaleModuleInverseImageAdj.{u, r} Λ i).counit.app M) :=
  (Adjunction.homEquiv_counit _ _ _ _).symm.trans
    (Stacks.CategoryTheory.BaseChange.homEquiv_symm_map
      (etaleModuleInverseImageAdj.{u, r} Λ i) (etaleModuleInverseImageAdj.{u, r} Λ i')
      (etaleModuleInverseImageCompIso.{u, r} Λ i' g).symm
      (etaleModuleBaseChangeComparison Λ i i' g g' w) M)

private lemma isIso_of_isZero_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C] {A B : C}
    (f : A ⟶ B) (hA : IsZero A) (hB : IsZero B) : IsIso f :=
  ⟨0, hA.eq_of_src _ _, hB.eq_of_src _ _⟩

/-- The inverse image to an open complement of a closed immersion kills its direct images. -/
lemma isZero_etaleModuleInverseImage_directImage {U : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ) (M : EtaleModules.{u, r} Λ Z) :
    IsZero ((etaleModuleInverseImage.{u, r} Λ j).obj ((etaleModuleDirectImage.{u, r} Λ i).obj M)) :=
  (isZero_etaleModuleRestriction_etaleModuleDirectImage Λ i j hij M).of_iso
    ((etaleModuleInverseImageRestrictionIso.{u, r} Λ j).app _)

/-- **Base change for a closed immersion, module coefficients ([Stacks, Tag 0959]).**  Let
`i' ≫ g = g' ≫ i` with `i`, `i'` closed immersions, and let `j : U ⟶ X`, `j' : U' ⟶ X'` be étale
morphisms onto their open complements with `j' ≫ g` factoring through `j`.  Then the base change
map `g^{-1} i_* M ⟶ i'_* g'^{-1} M` is an isomorphism. -/
theorem isIso_etaleModuleBaseChange_of_isClosedImmersion [IsClosedImmersion i]
    [IsClosedImmersion i'] {U U' : Scheme.{u}} (j : U ⟶ X) (j' : U' ⟶ X') [Etale j] [Etale j']
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (hij' : Set.range j'.base = (Set.range i'.base)ᶜ) (h : U' ⟶ U) (hh : j' ≫ g = h ≫ j)
    (M : EtaleModules.{u, r} Λ Z) :
    IsIso ((etaleModuleBaseChange Λ i i' g g' w).app M) := by
  have hi' : IsIso ((etaleModuleInverseImage.{u, r} Λ i').map
      ((etaleModuleBaseChange Λ i i' g g' w).app M)) := by
    have := (etaleModuleDirectImageFullyFaithful.{u, r} Λ i).full
    have := (etaleModuleDirectImageFullyFaithful.{u, r} Λ i).faithful
    have := (etaleModuleDirectImageFullyFaithful.{u, r} Λ i').full
    have := (etaleModuleDirectImageFullyFaithful.{u, r} Λ i').faithful
    have : IsIso ((etaleModuleInverseImage.{u, r} Λ i').map
        ((etaleModuleBaseChange Λ i i' g g' w).app M) ≫
        (etaleModuleInverseImageAdj.{u, r} Λ i').counit.app
          ((etaleModuleInverseImage.{u, r} Λ g').obj M)) := by
      rw [inverseImage_map_etaleModuleBaseChange_comp_counit Λ i i' g g' w M]
      infer_instance
    exact IsIso.of_isIso_comp_right _ ((etaleModuleInverseImageAdj.{u, r} Λ i').counit.app _)
  have hj' : IsIso ((etaleModuleInverseImage.{u, r} Λ j').map
      ((etaleModuleBaseChange Λ i i' g g' w).app M)) := by
    refine isIso_of_isZero_of_isZero _ ?_
      (isZero_etaleModuleInverseImage_directImage Λ i' j' hij' _)
    refine (((etaleModuleInverseImage.{u, r} Λ h).map_isZero
      (isZero_etaleModuleInverseImage_directImage Λ i j hij M)).of_iso ?_)
    exact ((etaleModuleInverseImageCompIso.{u, r} Λ j' g).symm ≪≫
      eqToIso (congrArg (fun m => etaleModuleInverseImage.{u, r} Λ m) hh) ≪≫
        etaleModuleInverseImageCompIso.{u, r} Λ h j).app _
  exact isIso_of_isIso_etaleModuleInverseImage Λ i' j' hij' _

end Stacks.EtaleCohomology

end
