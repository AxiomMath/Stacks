module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsExceptionalComparison
public import StacksFrontier.AlgebraicGeometry.Cohomology.DerivedPushforwardAffineBaseHomology

/-!
# The comparison `Rb_*F ⟶ i_*Rp_*G` attached to a restriction along a closed immersion

Let `b : L ⟶ X`, `j : P ⟶ L`, `p : P ⟶ Z` and `i : Z ⟶ X` be morphisms of schemes with
`j ≫ b = p ≫ i` and `j` a closed immersion, and let `r : F ⟶ j_*G` be a morphism of
`𝒪_L`-modules. The canonical map

`Rb_*F ⟶ Rb_*(j_*G) ⟶ Rb_*Rj_*G ≅ R(j ≫ b)_*G = R(p ≫ i)_*G ≅ Ri_*Rp_*G`

in `D(𝒪_X)` is the recipe of both `Stacks.DeRham.blowupFormsRestrictionDerivedComparison` (clause
(3) of [Stacks, Tag 0FUU]) and `Stacks.DeRham.CoordinateCone.coneFormsDerivedComparison` (clause
(3) of [Stacks, Tag 0FUR]), with `r` the restriction of forms. Everything after `Rb_*r` is
invertible, because `j_* ⟶ Rj_*` is invertible along a closed immersion and the remaining maps are
the comparisons of [Stacks, Tag 0D5T]. This file records the consequence: the map is invertible on
a cohomology sheaf as soon as `Rb_*r` is.

## Main definitions

* `Stacks.DeRham.formsRestrictionComplexMap`: `r` placed in degree `0`, as a map into the direct
  image of `G` placed in degree `0`.
* `Stacks.DeRham.formsDerivedComparisonOf`: the map above, in an arbitrary model of each derived
  category.

## Main results

* `Stacks.DeRham.isIso_homology_formsDerivedComparisonOf_of_isIso`: it is invertible on `H^q` as
  soon as `Rb_*r` is.
* `Stacks.DeRham.isIso_homology_formsDerivedComparisonOf_of_isIso_rightDerived`: for `X` affine,
  `b` quasi-compact and quasi-separated and `F`, `j_*G` quasi-coherent, it is invertible on `H^q`
  as soon as `H^q(L, r)` is.

## References

* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.BlowupTriangle

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham

variable {L X P Z : Scheme.{u}}
  [HasDerivedCategory (ModuleSheaves X.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves L.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves Z.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves P.toRingedSpace)]
  (b : L ⟶ X) (j : P ⟶ L) (p : P ⟶ Z) (i : Z ⟶ X)
  (w : j.toLRSHom.toShHom ≫ b.toLRSHom.toShHom = p.toLRSHom.toShHom ≫ i.toLRSHom.toShHom)
  {F : L.Modules} (G : P.Modules) (r : F ⟶ (Scheme.Modules.pushforward j).obj G)

/-- `r : F ⟶ j_*G` placed in degree `0`, followed by the identification `(j_*G)[0] = j_*(G[0])`:
a morphism of complexes `F[0] ⟶ j_*(G[0])`. -/
def formsRestrictionComplexMap :
    singleComplex F ⟶ ((modulePushforward j.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (singleComplex G) :=
  (HomologicalComplex.single (ModuleSheaves L.toRingedSpace) (ComplexShape.up ℤ) 0).map r ≫
    (HomologicalComplex.singleMapHomologicalComplex (modulePushforward j.toLRSHom.toShHom)
      (ComplexShape.up ℤ) 0).inv.app G

/-- **The comparison `Rb_*F ⟶ i_*Rp_*G` attached to `r : F ⟶ j_*G`**: `Rb_*` of `r` followed by
the comparison `j_* ⟶ Rj_*`, then the comparisons `Rb_*Rj_* ≅ R(j ≫ b)_* = R(p ≫ i)_* ≅ Ri_*Rp_*`
of [Stacks, Tag 0D5T]. -/
def formsDerivedComparisonOf :
    (derivedPushforward b.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (singleComplex F)) ⟶
      (derivedPushforward i.toLRSHom.toShHom).obj
        ((derivedPushforward p.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (singleComplex G))) :=
  (derivedPushforward b.toLRSHom.toShHom).map
      (DerivedCategory.Q.map (formsRestrictionComplexMap j G r) ≫
        unit j.toLRSHom.toShHom (singleComplex G)) ≫
    (compIso j.toLRSHom.toShHom b.toLRSHom.toShHom).inv.app _ ≫
    eqToHom (congrArg (fun g => (derivedPushforward g).obj
      (DerivedCategory.Q.obj (singleComplex G))) w) ≫
    (compIso p.toLRSHom.toShHom i.toLRSHom.toShHom).hom.app _

/-- **The comparison is invertible on `H^q` as soon as `Rb_*r` is**, for `j` a closed immersion:
every factor after `Rb_*r` is an isomorphism.

The complexes in degree `0` occurring in `formsRestrictionComplexMap` carry the zero morphisms of
two definitionally equal instances, so `Q` of that composite is only definitionally a composite in
the source of `Q`; the split is `Functor.map_comp` read through unification, and the factors are
assembled with `IsIso.comp_isIso'` rather than by instance search. -/
theorem isIso_homology_formsDerivedComparisonOf_of_isIso [IsClosedImmersion j] (q : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((derivedPushforward b.toLRSHom.toShHom).map (DerivedCategory.Q.map
        ((HomologicalComplex.single (ModuleSheaves L.toRingedSpace) (ComplexShape.up ℤ) 0).map
          r))))) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map (formsDerivedComparisonOf b j p i w G r)) := by
  have hu := isIso_unit_of_isClosedEmbedding j.toLRSHom.toShHom j.isClosedEmbedding
    (singleComplex G)
  let Φ := DerivedCategory.Q ⋙ derivedPushforward b.toLRSHom.toShHom ⋙
    DerivedCategory.homologyFunctor _ q
  let A := (HomologicalComplex.single (ModuleSheaves L.toRingedSpace) (ComplexShape.up ℤ) 0).map r
  let B := (HomologicalComplex.singleMapHomologicalComplex (modulePushforward j.toLRSHom.toShHom)
    (ComplexShape.up ℤ) 0).inv.app G
  have hA : IsIso (Φ.map A) := h
  have hB : IsIso (Φ.map B) := (Φ.mapIso ((HomologicalComplex.singleMapHomologicalComplex
    (modulePushforward j.toLRSHom.toShHom) (ComplexShape.up ℤ) 0).app G).symm).isIso_hom
  have hAB := (congrArg (fun f => IsIso f) (Φ.map_comp A B)).mpr (IsIso.comp_isIso' hA hB)
  simp only [formsDerivedComparisonOf, Functor.map_comp]
  exact IsIso.comp_isIso' (IsIso.comp_isIso' hAB inferInstance) inferInstance

/-- **The comparison is invertible on `H^q` as soon as `H^q(L, r)` is**, for `j` a closed
immersion, `b` quasi-compact and quasi-separated, `X` affine and `F`, `j_*G` quasi-coherent: then
`H^q(Rb_*r)` is invertible by
`Stacks.Cohomology.AffineBase.isIso_homology_derivedPushforward_map_single_of_isIso`. -/
theorem isIso_homology_formsDerivedComparisonOf_of_isIso_rightDerived [IsClosedImmersion j]
    [QuasiCompact b] [QuasiSeparated b] [IsAffine X] [F.IsQuasicoherent]
    [((Scheme.Modules.pushforward j).obj G).IsQuasicoherent] (q : ℕ)
    (h : IsIso (((Stacks.Cohomology.sectionsFunctor L ⊤).rightDerived q).map r)) :
    IsIso ((DerivedCategory.homologyFunctor _ (q : ℤ)).map
      (formsDerivedComparisonOf b j p i w G r)) :=
  isIso_homology_formsDerivedComparisonOf_of_isIso b j p i w G r q
    (Stacks.Cohomology.AffineBase.isIso_homology_derivedPushforward_map_single_of_isIso b r q h)

end Stacks.DeRham

end
