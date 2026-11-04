module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoextendScalarsKInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentExtClass
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseTowerSheafification
public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionBaseChange
public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionHomology
public import StacksFrontier.Deformation.ToposThickening.CotangentObstructionNaiveSquare

/-!
# Maps out of the first vertex of the fundamental triangle of a quotient into `G[1]`

Let `g : A' ⟶ A` be a locally surjective homomorphism of sheaves of commutative rings on a site,
with kernel `I`, let `h : A ⟶ O` be a further homomorphism and `G` a sheaf of `O`-modules. The
first vertex `L_{A/A'} ⊗_A O` of the fundamental triangle of `A' ⟶ A ⟶ O` (Tag 08SZ) lies in
degrees `≤ -1` with `H^{-1} = (I/I²) ⊗_A O`, so maps from it to `G[1]` are the `A`-linear maps
`I/I² ⟶ G`. This file constructs that identification.

## Main definitions

* `Deformation.ToposThickening.CotangentObstruction.baseExtEquiv`: maps
  `L_{A/A'} ⊗_A O ⟶ G[1]` in the derived category are `A`-linear maps `I/I² ⟶ G`.

## Main results

* `Deformation.ToposThickening.CotangentObstruction.homologyMap_towerCotangentNaive_homologyToX`:
  the first morphism of the fundamental triangle on `H^{-1}`, read in the naive cotangent complex
  of the presentation by `P₀`.
* `Deformation.ToposThickening.CotangentObstruction.baseExtEquiv_Q_map_towerNaiveMap_comp`: the map
  `I/I² ⟶ G` attached to a map out of `NL_{O/A'}` through the first morphism of the triangle.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u v w

namespace Deformation.ToposThickening.CotangentObstruction

open CategoryTheory.Sheaf

/-! ### The comparison `L ⟶ NL` in degree `-1` -/

section Comparison


variable {C' : Type u} [Category.{v} C'] {J' : GrothendieckTopology C'}
  {B D : Sheaf J' CommRingCat.{max u v w}} (f : B ⟶ D)

/-- The inverse of the degree `-1` identification of the canonical conormal sequence, followed by
the `eqToHom` into the naive cotangent complex, is the identity. -/
private theorem doubleXIso₀_inv_comp_eqToHom :
    (HomologicalComplex.doubleXIso₀
      (Stacks.SheafOfModules.canonicalConormalSequence.{v, u, max u v w, u} J' B D f).f
        ComplexShape.upIntRelNegOneZero).inv ≫
      eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{v, u, max u v w, u}
        J' B D f) = 𝟙 _ :=
  (eqToHom_trans (dite_eq_left rfl).symm _).trans (eqToHom_refl _ _)

/-- In degree `-1` the comparison `L_{D/B} ⟶ NL_{D/B}` into the naive cotangent complex of the
canonical presentation is the comparison into the naive cotangent complex of the presentation by
`P₀`, read through `P₀ ≅ B[D]`. -/
theorem canonicalNaiveComparison_f_negOne_comp_doubleXIso₀ :
    (canonicalNaiveComparison.{u, v, w} J' f).f (-1) ≫
        eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{v, u, max u v w, u}
          J' B D f) =
      (cotangentComplex_degreeIso.{u, v, w} J' f 1).hom ≫ naiveComparisonNegOne J' f ≫
        (naiveConormalIso J' f).hom := by
  rw [canonicalNaiveComparison, HomologicalComplex.comp_f, naiveComparison_f_negOne,
    naiveCotangentComplexIsoCanonical, HomologicalComplex.doubleIsoOfIso_hom,
    HomologicalComplex.doubleMap_f₀]
  have key : ∀ {P Q R S T U : targetModules.{u, v, w} J' D} (a : P ⟶ Q) (b : Q ⟶ R)
      (x : R ⟶ S) (x' : S ⟶ R) (c : R ⟶ T) (y : T ⟶ U) (y' : U ⟶ T),
      x ≫ x' = 𝟙 _ → y ≫ y' = 𝟙 _ → (((a ≫ b) ≫ x) ≫ x' ≫ c ≫ y) ≫ y' = a ≫ b ≫ c := by
    intro _ _ _ _ _ _ a b x x' c y y' hx hy
    simp only [Category.assoc, reassoc_of% hx, hy, Category.comp_id]
  exact key _ _ _ _ _ _ _ (Iso.inv_hom_id _) (doubleXIso₀_inv_comp_eqToHom.{u, v, w} f)

/-- In degree `-1` the identification of the naive cotangent complexes of the presentations by
`P₀` and by `B[D]` is the identification of their conormal sheaves along `P₀ ≅ B[D]`. -/
theorem naiveCotangentComplexIsoCanonical_hom_f_negOne :
    (naiveCotangentComplexIsoCanonical.{u, v, w} J' f).hom.f (-1) ≫
        eqToHom (Stacks.SheafOfModules.naiveCotangentComplex_X_negOne.{v, u, max u v w, u}
          J' B D f) =
      (naiveCotangentComplexXNegOneIso.{u, v, w} J' f).hom ≫ (naiveConormalIso J' f).hom := by
  rw [naiveCotangentComplexIsoCanonical, HomologicalComplex.doubleIsoOfIso_hom,
    HomologicalComplex.doubleMap_f₀]
  have key : ∀ {P Q R S : targetModules.{u, v, w} J' D} (a : P ⟶ Q) (c : Q ⟶ R) (x : R ⟶ S)
      (y : S ⟶ R), x ≫ y = 𝟙 _ → (a ≫ c ≫ x) ≫ y = a ≫ c := by
    intro _ _ _ _ a c x y hxy
    rw [Category.assoc, Category.assoc, hxy, Category.comp_id]
  exact key _ _ _ _ (doubleXIso₀_inv_comp_eqToHom.{u, v, w} f)

/-- The degree `-1` comparison `L_{D/B} ⟶ I/I²`, restricted to the cycles of `L_{D/B}`, is killed
by the conormal map of the presentation by `P₀`. -/
theorem iCycles_comp_naiveComparisonNegOne_comp_f :
    (cotangentComplex.{u, v, w} J' f).iCycles (-1) ≫
        (cotangentComplex_degreeIso.{u, v, w} J' f 1).hom ≫ naiveComparisonNegOne J' f ≫
          (naiveSequence J' f).f = 0 := by
  have hcomm := (naiveComparison.{u, v, w} J' f).comm (-1) 0
  rw [naiveComparison_f_negOne] at hcomm
  have hd : (naiveCotangentComplex.{u, v, w} J' f).d (-1) 0 =
      (naiveCotangentComplexXNegOneIso.{u, v, w} J' f).hom ≫ (naiveSequence J' f).f ≫
        (naiveCotangentComplexXZeroIso.{u, v, w} J' f).inv :=
    HomologicalComplex.double_d _ _ (by decide)
  rw [hd] at hcomm
  have key : (cotangentComplex_degreeIso.{u, v, w} J' f 1).hom ≫ naiveComparisonNegOne J' f ≫
      (naiveSequence J' f).f = (cotangentComplex.{u, v, w} J' f).d (-1) 0 ≫
        (naiveComparison.{u, v, w} J' f).f 0 ≫
          (naiveCotangentComplexXZeroIso.{u, v, w} J' f).hom := by
    rw [← reassoc_of% hcomm]
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [key, HomologicalComplex.iCycles_d_assoc, zero_comp]

/-- The base map `B ⟶ P₀` of the standard resolution followed by its augmentation is `f`. -/
theorem resolutionBase_comp_resolutionAugmentation :
    resolutionBase.{u, v, w} J' f (op ⦋0⦌) ≫ resolutionAugmentation J' f (op ⦋0⦌) = f :=
  Under.w ((standardResolution.{v, u, w} J' f).hom.app (op ⦋0⦌))

variable [Presheaf.IsLocallySurjective J' f.hom]
  [J'.WEqualsLocallyBijective CommRingCat.{max u v w}]

/-- **`H^{-1}(L_{D/B}) = I/I²` on cycles.** A cycle of `L_{D/B}` in degree `-1`, read in the
conormal sheaf of `P₀ ⟶ D` through `H^{-1}(L_{D/B}) = I/I²` and the base map `B ⟶ P₀`, is its
image under the comparison `L_{D/B} ⟶ NL_{D/B}`. -/
theorem homologyπ_conormalIso_hom_conormalSheafMapOfFac :
    (cotangentComplex.{u, v, w} J' f).homologyπ (-1) ≫
        (cotangentComplexHomologyNegOneIsoConormal.{u, v, w} J' f).hom ≫
          Stacks.Sites.Conormal.conormalSheafMapOfFac.{v, u, max u v w, u} J' D B
            (resolutionTerm.{u, v, w} J' f (op ⦋0⦌)) f (resolutionAugmentation J' f (op ⦋0⦌))
            (resolutionBase.{u, v, w} J' f (op ⦋0⦌))
            (resolutionBase_comp_resolutionAugmentation f) =
      (cotangentComplex.{u, v, w} J' f).iCycles (-1) ≫
        (cotangentComplex_degreeIso.{u, v, w} J' f 1).hom ≫ naiveComparisonNegOne J' f := by
  have gen :=
    Stacks.SheafOfModules.naiveCotangentHomologyNegOneIsoConormal_hom_conormalSheafMapOfFac.{v,
    u, max u v w, u} J' B D f _ (resolutionBase.{u, v, w} J' f (op ⦋0⦌))
    (resolutionAugmentation J' f (op ⦋0⦌)) (resolutionBase_comp_resolutionAugmentation f)
    (resolutionZeroIsoFreeAlgebra J' f)
    (resolutionZeroIsoFreeAlgebra_hom_comp_canonicalPresentation J' f)
    (resolutionBase_comp_resolutionZeroIsoFreeAlgebra_hom J' f)
  have hS := canonicalNaiveComparison_f_negOne_comp_doubleXIso₀.{u, v, w} (J' := J') f
  refine (Iso.cancel_iso_hom_right _ _ (naiveConormalIso J' f)).1 ?_
  refine Eq.trans ?_ (congrArg ((cotangentComplex.{u, v, w} J' f).iCycles (-1) ≫ ·) hS)
  refine Eq.trans ?_ (HomologicalComplex.homologyπ_homologyMap_homologyToX_assoc _ _
    (Stacks.SheafOfModules.naiveCotangentComplex_d_prev_negOne.{v, u, max u v w, u} J' B D f) _)
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  exact ((Category.assoc _ _ _).trans (Category.assoc _ _ _)).trans (congrArg (_ ≫ ·) gen)

end Comparison

/-! ### Restriction of scalars is exact -/

section Exactness

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {B B' : Sheaf J CommRingCat.{max u v w}} (b : B ⟶ B')

/-- Restriction of scalars along a map of sheaves of commutative rings preserves finite limits:
it commutes with the forgetful functors to sheaves of abelian groups. -/
instance preservesFiniteLimits_squareRestrict :
    PreservesFiniteLimits (squareRestrict.{u, v, w} J b) :=
  preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- Restriction of scalars along a map of sheaves of commutative rings preserves finite
colimits: it commutes with the forgetful functors to sheaves of abelian groups. -/
instance preservesFiniteColimits_squareRestrict :
    PreservesFiniteColimits (squareRestrict.{u, v, w} J b) :=
  haveI : PreservesFiniteColimits (squareRestrict.{u, v, w} J b ⋙
      SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf B)) :=
    Stacks.SheafOfModules.instPreservesFiniteColimitsToSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf B')
  preservesFiniteColimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf B))

/-- The comparison of `H^{-1}` with restriction of scalars is compatible with the inclusions of
`H^{-1}` into the terms in degree `-1`, for a complex with no differential into degree `-1`. -/
@[reassoc]
theorem homologyMapIso_hom_map_homologyToX (K : CochainComplex (targetModules.{u, v, w} J B') ℤ)
    (hK : K.d ((ComplexShape.up ℤ).prev (-1)) (-1) = 0)
    (hRK : (((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).d
      ((ComplexShape.up ℤ).prev (-1)) (-1) = 0) :
    (ShortComplex.homologyMapIsoOfLeftHomologyData (squareRestrict.{u, v, w} J b)
        (K.sc (-1)).leftHomologyData).hom ≫
      (squareRestrict.{u, v, w} J b).map (K.homologyToX (-1) hK) =
    (((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homologyToX
      (-1) hRK := by
  refine (cancel_epi ((((squareRestrict.{u, v, w} J b).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K).homologyπ (-1))).1 ?_
  have e1 := ShortComplex.homologyπ_comp_homologyMapIsoOfLeftHomologyData_hom_assoc
    (squareRestrict.{u, v, w} J b) (K.sc (-1)).leftHomologyData
    ((squareRestrict.{u, v, w} J b).map (K.homologyToX (-1) hK))
  have e2 : (squareRestrict.{u, v, w} J b).map (K.homologyπ (-1)) ≫
      (squareRestrict.{u, v, w} J b).map (K.homologyToX (-1) hK) =
      (squareRestrict.{u, v, w} J b).map (K.iCycles (-1)) := by
    rw [← Functor.map_comp, HomologicalComplex.homologyπ_homologyToX]
  exact e1.trans ((congrArg _ e2).trans
    ((ShortComplex.cyclesMapIsoOfLeftHomologyData_hom_comp_map_iCycles _ _).trans
      (HomologicalComplex.homologyπ_homologyToX
        (((squareRestrict.{u, v, w} J b).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
        (-1) hRK).symm))

end Exactness

/-! ### The first morphism of the fundamental triangle in degree `-1` -/

section Tower

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A' A O : Sheaf J CommRingCat.{max u v w}} (g : A' ⟶ A) (h : A ⟶ O)

/-- The map of standard resolutions attached to the square `(𝟙 A', h)` from `g` to `g ≫ h`. -/
noncomputable abbrev towerSquare : ResolutionSquareMap.{u, v, w} J g (g ≫ h) (𝟙 A') h :=
  towerBaseChangeSquare.{u, v, w} J g h

/-- The map of conormal sheaves of the degree-zero presentations along the tower square. -/
noncomputable abbrev towerZeroConormal :=
  Stacks.Sites.Conormal.conormalSheafMapOfSquare.{v, u, max u v w, u} J
    (resolutionTerm.{u, v, w} J g (op ⦋0⦌)) (resolutionTerm.{u, v, w} J (g ≫ h) (op ⦋0⦌)) A O
    (resolutionAugmentation J g (op ⦋0⦌)) (resolutionAugmentation J (g ≫ h) (op ⦋0⦌))
    ((towerSquare g h).resolution (op ⦋0⦌)) h
    ((towerSquare g h).resolution_augmentation (op ⦋0⦌))

/-- **The first morphism of the fundamental triangle, followed by the comparison with the naive
cotangent complex, in degree `-1`.** Its transpose along extension of scalars, followed by the
comparison `L_{O/A'} ⟶ NL_{O/A'}` of the presentation by `P₀`, is in degree `-1` the comparison
of `L_{A/A'}` followed by the map of conormal sheaves of the degree-zero presentations. -/
theorem towerCotangentNaive_f_negOne :
    (squareCotangentComplexMap (towerSquare g h) ≫
        ((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (naiveComparison.{u, v, w} J (g ≫ h))).f (-1) ≫
      (squareRestrict.{u, v, w} J h).map (naiveCotangentComplexXNegOneIso.{u, v, w} J (g ≫ h)).hom =
    ((cotangentComplex_degreeIso.{u, v, w} J g 1).hom ≫ naiveComparisonNegOne J g) ≫
      towerZeroConormal g h := by
  have hu : (squareCotangentComplexMap (towerSquare g h)).f (-1) =
      (cotangentComplex_degreeIso.{u, v, w} J g 1).hom ≫
        squareCotangentTermMap (towerSquare g h) (op ⦋1⦌) ≫
          (squareRestrict.{u, v, w} J h).map
            (cotangentComplex_degreeIso.{u, v, w} J (g ≫ h) 1).inv :=
    squareCotangentComplexMap_f _ 1
  have hs := squareCotangentTermMap_comp_naiveComparisonNegOne (towerSquare g h)
  rw [HomologicalComplex.comp_f, Category.assoc]
  change _ ≫ (squareRestrict.{u, v, w} J h).map _ ≫ (squareRestrict.{u, v, w} J h).map _ = _
  rw [← Functor.map_comp, naiveComparison_f_negOne, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, hu, Category.assoc, Category.assoc, Functor.map_comp,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (congrArg _ hs).trans (Category.assoc _ _ _).symm

/-- The naive cotangent complex of `P₀ ⟶ O`, with scalars restricted to `A`, has no
differential into degree `-1`. -/
theorem restrictedNaive_d_prev_negOne :
    (((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{u, v, w} J (g ≫ h))).d ((ComplexShape.up ℤ).prev (-1)) (-1) =
      0 := by
  rw [Functor.mapHomologicalComplex_obj_d,
    (naiveCotangentComplex_isZero_X.{u, v, w} J (g ≫ h) _ (by simp) (by simp)).eq_of_src
      ((naiveCotangentComplex.{u, v, w} J (g ≫ h)).d _ _) 0, Functor.map_zero]

variable [Presheaf.IsLocallySurjective J g.hom] [J.WEqualsLocallyBijective CommRingCat.{max u v w}]

/-- **The first morphism of the fundamental triangle on `H^{-1}`.** Its transpose along extension
of scalars, followed by the comparison with the naive cotangent complex of the presentation by
`P₀`, sends a class of `H^{-1}(L_{A/A'}) = I/I²` to the class in the conormal sheaf of
`P₀ ⟶ O` of its image under the base map `A' ⟶ P₀` of `g` and the map of standard resolutions. -/
theorem homologyMap_towerCotangentNaive_homologyToX :
    HomologicalComplex.homologyMap (squareCotangentComplexMap (towerSquare g h) ≫
        ((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (naiveComparison.{u, v, w} J (g ≫ h))) (-1) ≫
      (((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (naiveCotangentComplex.{u, v, w} J (g ≫ h))).homologyToX (-1)
          (restrictedNaive_d_prev_negOne g h) ≫
        (squareRestrict.{u, v, w} J h).map
          (naiveCotangentComplexXNegOneIso.{u, v, w} J (g ≫ h)).hom =
    ((cotangentComplexHomologyNegOneIsoConormal.{u, v, w} J g).hom ≫
        Stacks.Sites.Conormal.conormalSheafMapOfFac.{v, u, max u v w, u} J A A'
          (resolutionTerm.{u, v, w} J g (op ⦋0⦌)) g (resolutionAugmentation J g (op ⦋0⦌))
          (resolutionBase.{u, v, w} J g (op ⦋0⦌))
          (resolutionBase_comp_resolutionAugmentation g)) ≫
      towerZeroConormal g h := by
  refine (cancel_epi ((cotangentComplex.{u, v, w} J g).homologyπ (-1))).1 ?_
  refine (HomologicalComplex.homologyπ_homologyMap_homologyToX_assoc _ _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (towerCotangentNaive_f_negOne g h)).trans ?_
  refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
  exact congrArg (· ≫ towerZeroConormal g h)
    (homologyπ_conormalIso_hom_conormalSheafMapOfFac g).symm

end Tower

section Main

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  {A' A O : Sheaf J CommRingCat.{max u v w}} (g : A' ⟶ A) (h : A ⟶ O)
  [Presheaf.IsLocallySurjective J g.hom]
  [HasDerivedCategory (targetModules.{u, v, w} J O)] (G : targetModules.{u, v, w} J O)

/-- The degreewise base change `L_{A/A'} ⊗_A O`, as the image of the cotangent complex under
extension of scalars. -/
noncomputable abbrev baseChangedComplex : CochainComplex (targetModules.{u, v, w} J O) ℤ :=
  ((towerExtendScalars.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (cotangentComplex.{u, v, w} J g)

/-- The degreewise base change `L_{A/A'} ⊗_A O` lies in degrees `≤ -1` in the derived
category. -/
instance isLE_Q_obj_baseChangedComplex :
    (DerivedCategory.Q.obj (baseChangedComplex J g h)).IsLE (-1) :=
  haveI := isLE_Q_obj_baseChangedCotangentComplex.{u, v, w} J g h
  (DerivedCategory.TStructure.t.isLE_of_iso
    (DerivedCategory.Q.mapIso (towerExtendScalarsCotangentComplexIso.{u, v, w} J g h)).symm (-1))

/-- **Maps `L_{A/A'} ⊗_A O ⟶ G[1]` are the `A`-linear maps `I/I² ⟶ G`.** The map on `H^{-1}`
(Stacks 06XS), through `H^{-1}(L_{A/A'} ⊗_A O) = H^{-1}(L_{A/A'}) ⊗_A O`, transposed along
extension of scalars, and read through `H^{-1}(L_{A/A'}) = I/I²`. -/
noncomputable def baseExtEquiv :
    (DerivedCategory.Q.obj (baseChangedComplex J g h) ⟶
        ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧) ≃
      (Stacks.Sites.Conormal.conormalSheaf.{v, u, max u v w, u} J A' A g ⟶
        (squareRestrict.{u, v, w} J h).obj G) :=
  (Equiv.ofBijective _ (DerivedCategory.bijective_negOneHomologyMap _ G)).trans
    ((((extendScalarsCotangentHomologyNegOneIso.{u, v, w} J g h).homCongr (Iso.refl G)).trans
      ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _)).trans
        ((cotangentComplexHomologyNegOneIsoConormal.{u, v, w} J g).homCongr (Iso.refl _)))

/-- The first morphism of the fundamental triangle of `A' ⟶ A ⟶ O`, read on the degreewise base
change and followed by the comparison with the naive cotangent complex of the presentation of `O`
by `P₀`. -/
noncomputable abbrev towerNaiveMap :
    baseChangedComplex J g h ⟶ naiveCotangentComplex.{u, v, w} J (g ≫ h) :=
  (towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom ≫
    towerCotangentBaseChange.{u, v, w} J g h ≫ naiveComparison.{u, v, w} J (g ≫ h)

omit [J.WEqualsLocallyBijective CommRingCat] [Presheaf.IsLocallySurjective J g.hom]
  [HasDerivedCategory (targetModules J O)] in
/-- In each degree the first morphism of the fundamental triangle, read on the degreewise base
change, is the transpose of the map of base-changed differentials along the tower square. -/
theorem towerExtendScalarsCotangentComplexIso_hom_f_comp (j : ℤ) :
    (towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom.f j ≫
        (towerCotangentBaseChange.{u, v, w} J g h).f j =
      ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _).symm
        ((squareCotangentComplexMap (towerSquare g h)).f j) :=
  (Category.assoc _ _ _).trans (towerCotangentBaseChange_f_eq_homEquiv_symm.{u, v, w} J g h j)

/-- The transpose of `towerNaiveMap` in degree `-1`. -/
theorem homEquiv_towerNaiveMap_f (j : ℤ) :
    (towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _ ((towerNaiveMap J g h).f j) =
      (squareCotangentComplexMap (towerSquare g h) ≫
        ((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (naiveComparison.{u, v, w} J (g ≫ h))).f j := by
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
    towerExtendScalarsCotangentComplexIso_hom_f_comp, Adjunction.homEquiv_naturality_right,
    Equiv.apply_symm_apply]
  rfl

/-- **The class of a map out of `NL_{O/A'}` restricted to the base ideal, in the derived
category.** For `φ : NL_{O/A'} ⟶ G[1]`, the map `I/I² ⟶ G` attached to the composite of the
first morphism of the fundamental triangle with `L_{O/A'} ⟶ NL_{O/A'}` and `φ` is the map induced
on `H^{-1}` by the transpose of that first morphism, followed by the map `φ` induces on
`H^{-1}`. -/
theorem baseExtEquiv_Q_map_towerNaiveMap_comp
    (φ : DerivedCategory.Q.obj (naiveCotangentComplex.{u, v, w} J (g ≫ h)) ⟶
      ((DerivedCategory.singleFunctor _ 0).obj G)⟦(1 : ℤ)⟧) :
    baseExtEquiv J g h G (DerivedCategory.Q.map (towerNaiveMap J g h) ≫ φ) =
      (cotangentComplexHomologyNegOneIsoConormal.{u, v, w} J g).inv ≫
        HomologicalComplex.homologyMap (squareCotangentComplexMap (towerSquare g h) ≫
          ((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (naiveComparison.{u, v, w} J (g ≫ h))) (-1) ≫
          (ShortComplex.homologyMapIsoOfLeftHomologyData (squareRestrict.{u, v, w} J h)
            ((naiveCotangentComplex.{u, v, w} J (g ≫ h)).sc (-1)).leftHomologyData).hom ≫
            (squareRestrict.{u, v, w} J h).map
              (DerivedCategory.negOneHomologyMap _ G φ) := by
  have key := ShortComplex.homEquiv_homologyMapIso_inv_comp_homologyMap
    (towerExtendScalars.{u, v, w} J h) (cotangentNegOneData.{u, v, w} J g)
    (towerExtendRestrictAdjunction.{u, v, w} J h)
    ((naiveCotangentComplex.{u, v, w} J (g ≫ h)).sc (-1)).leftHomologyData
    ((HomologicalComplex.shortComplexFunctor _ _ (-1)).map (towerNaiveMap J g h))
    ((HomologicalComplex.shortComplexFunctor _ _ (-1)).map
      (squareCotangentComplexMap (towerSquare g h) ≫
        ((squareRestrict.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (naiveComparison.{u, v, w} J (g ≫ h))))
    (homEquiv_towerNaiveMap_f J g h (-1)).symm
  change (cotangentComplexHomologyNegOneIsoConormal.{u, v, w} J g).inv ≫
      (towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _
        ((extendScalarsCotangentHomologyNegOneIso.{u, v, w} J g h).inv ≫
          DerivedCategory.negOneHomologyMap _ G (DerivedCategory.Q.map (towerNaiveMap J g h) ≫ φ) ≫
            (Iso.refl G).hom) ≫ (Iso.refl _).hom = _
  have e1 : (extendScalarsCotangentHomologyNegOneIso.{u, v, w} J g h).inv ≫
      DerivedCategory.negOneHomologyMap _ G (DerivedCategory.Q.map (towerNaiveMap J g h) ≫ φ) ≫
        (Iso.refl G).hom =
      ((extendScalarsCotangentHomologyNegOneIso.{u, v, w} J g h).inv ≫
        HomologicalComplex.homologyMap (towerNaiveMap J g h) (-1)) ≫
          DerivedCategory.negOneHomologyMap _ G φ := by
    have aux : ∀ {X Y Z W : targetModules.{u, v, w} J O} (a : X ⟶ Y) (b : Y ⟶ W) (c : Y ⟶ Z)
        (d : Z ⟶ W), b = c ≫ d → a ≫ b ≫ 𝟙 W = (a ≫ c) ≫ d := by
      intro _ _ _ _ a b c d hb
      rw [hb, Category.comp_id, Category.assoc]
    exact aux _ _ _ _ (DerivedCategory.negOneHomologyMap_Q_map_comp _ G φ)
  refine congrArg (_ ≫ ·) ((Category.comp_id _).trans ?_)
  refine (congrArg ((towerExtendRestrictAdjunction.{u, v, w} J h).homEquiv _ _) e1).trans ?_
  refine (Adjunction.homEquiv_naturality_right _ _ _).trans ?_
  exact (congrArg (· ≫ _) key).trans (Category.assoc _ _ _)

end Main


end Deformation.ToposThickening.CotangentObstruction

end
