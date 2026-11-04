module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceRationalPoint
public import StacksFrontier.AlgebraicGeometry.Curves.Models.InseparableModel.ComponentGenus
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.DegreeOneFromPoints
public import StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.SectionPoint
public import
  StacksFrontier.AlgebraicGeometry.Curves.ProjectiveLineCriterion.SmoothGeometricallyIntegral
public import StacksFrontier.AlgebraicGeometry.HProjectiveProper.Basic
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothProjectiveVariety
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The projective line satisfies the conditions characterizing it

Let `k` be a field and let `f : X ⟶ Spec k` be isomorphic over `k` to the projective line
`𝐏¹_k ⟶ Spec k`. This file proves the implication "(1) ⟹ (2), …, (8)" of [Stacks, Tag 0C6U],
whose verification the source omits: `X` is proper, smooth, a curve, geometrically irreducible
and geometrically integral over `k`, `H⁰(X, 𝒪_X) = k`, `X` has genus `0` and `H¹(X, 𝒪_X) = 0`,
`X` is Gorenstein, `X` has an invertible module of degree `1` (hence of odd degree), and `X` has a
closed point with normal local ring and residue field `k`. The degree-one module is produced from
a rational point rather than as `𝒪(1)`.

The argument: `𝐏¹_k` is proper, smooth and a curve, and has a section; so `X` has the same
properties, and the image of the section is a normal rational closed point
(`AlgebraicGeometry.ProjectiveLineCriterion.normalRationalPoint_of_section`). Such a point forces
`H⁰(X, 𝒪_X) = k` and gives `𝒪_X(x)` of degree `1`
(`AlgebraicGeometry.ProjectiveLineCriterion.isIso_globalSections_of_gcd`,
`AlgebraicGeometry.ProjectiveLineCriterion.exists_invertibleCurveDegree_eq_one_of_gcd`).
Geometric irreducibility and integrality follow from `H⁰ = k` for the proper, smooth, hence
geometrically normal, `X` ([Stacks, Tag 0FD3]); smoothness gives regularity, hence the Gorenstein
property ([Stacks, Tag 0DWG]); the genus is read off the polynomial model
`Proj k[T₀, T₁]` through `Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison`.

## Main results

All in the namespace `AlgebraicGeometry.ProjectiveLineCriterion`:

* `isProper_of_iso_projectiveLine` and the companion statements for each property listed above.
* `exists_section_of_iso_projectiveLine`
* `exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine`

## References

* [Stacks Project, Tag 0C6U](https://stacks.math.columbia.edu/tag/0C6U)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
* [Stacks Project, Tag 0DWG](https://stacks.math.columbia.edu/tag/0DWG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveLineCriterion

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (e : Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)))

/-- The isomorphism of schemes underlying an isomorphism over `k` with `𝐏¹_k`. -/
def isoOfIsoProjectiveLine : X ≅ projectiveSpaceOver 1 (Spec (.of k)) :=
  (Over.forget _).mapIso e

/-- The isomorphism with `𝐏¹_k` lies over `Spec k`. -/
theorem isoOfIsoProjectiveLine_hom_comp :
    (isoOfIsoProjectiveLine e).hom ≫ (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)) = f :=
  Over.w e.hom

include e

/-- A scheme isomorphic over `k` to `𝐏¹_k` is proper over `k`. -/
theorem isProper_of_iso_projectiveLine : IsProper f := by
  rw [← isoOfIsoProjectiveLine_hom_comp e]; infer_instance

/-- A scheme isomorphic over `k` to `𝐏¹_k` is smooth over `k`. -/
theorem smooth_of_iso_projectiveLine : Smooth f := by
  rw [← isoOfIsoProjectiveLine_hom_comp e]; infer_instance

/-- A scheme isomorphic to `𝐏¹_k` has dimension one. -/
theorem topologicalKrullDim_of_iso_projectiveLine : topologicalKrullDim X = 1 := by
  have := isCurve_projectiveSpaceOver_one k
  exact (IsHomeomorph.topologicalKrullDim_eq _
      (isoOfIsoProjectiveLine e).hom.homeomorph.isHomeomorph).trans
    (IsCurve.topologicalKrullDim_eq_one
      (f := projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k)))

/-- A scheme isomorphic over `k` to `𝐏¹_k` is a curve over `k`. -/
theorem isCurve_of_iso_projectiveLine : IsCurve k f := by
  have := isCurve_projectiveSpaceOver_one k
  have : IsIntegral (projectiveSpaceOver 1 (Spec (.of k))) := inferInstance
  have : Nonempty X := ⟨(isoOfIsoProjectiveLine e).inv (Nonempty.some inferInstance)⟩
  have : IsIntegral X := isIntegral_of_isOpenImmersion (isoOfIsoProjectiveLine e).hom
  have := isProper_of_iso_projectiveLine e
  have : IsVariety k f := IsVariety.mk
  exact (isCurve_iff k f).mpr ⟨inferInstance, topologicalKrullDim_of_iso_projectiveLine e⟩

/-- **A scheme isomorphic over `k` to `𝐏¹_k` has a section over `k`.** -/
theorem exists_section_of_iso_projectiveLine : ∃ s : Spec (.of k) ⟶ X, s ≫ f = 𝟙 _ := by
  obtain ⟨s, hs⟩ := exists_section_projectiveSpaceOver (Spec (.of k)) 1
  refine ⟨s ≫ (isoOfIsoProjectiveLine e).inv, ?_⟩
  calc (s ≫ (isoOfIsoProjectiveLine e).inv) ≫ f
      = (s ≫ (isoOfIsoProjectiveLine e).inv) ≫ ((isoOfIsoProjectiveLine e).hom ≫
          (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) := by
        rw [isoOfIsoProjectiveLine_hom_comp e]
    _ = 𝟙 _ := by rw [Category.assoc, Iso.inv_hom_id_assoc, hs]

/-- **A scheme isomorphic over `k` to `𝐏¹_k` has a closed point with normal local ring and
residue field `k`**, so it satisfies the point condition of item (8) of [Stacks, Tag 0C6U]. -/
theorem exists_normalPoints_gcd_eq_one_of_iso_projectiveLine :
    ∃ (n : ℕ) (x : Fin n → X), (∀ i, IsClosed ({x i} : Set X)) ∧
      (∀ i, IsNormalRing (X.presheaf.stalk (x i))) ∧
      Finset.univ.gcd (fun i => letI : Algebra k (X.residueField (x i)) :=
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (x i)).hom.toAlgebra
        Module.finrank k (X.residueField (x i))) = 1 := by
  have := isProper_of_iso_projectiveLine e
  have := smooth_of_iso_projectiveLine e
  obtain ⟨s, hs⟩ := exists_section_of_iso_projectiveLine e
  exact exists_normalPoints_gcd_eq_one_of_section f s hs

/-- **A scheme isomorphic over `k` to `𝐏¹_k` has a rational closed point with normal local
ring.** -/
theorem exists_normalRationalPoint_of_iso_projectiveLine :
    ∃ x : X, IsClosed ({x} : Set X) ∧ IsNormalRing (X.presheaf.stalk x) ∧
      letI : Algebra k (X.residueField x) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Module.finrank k (X.residueField x) = 1 := by
  have := isProper_of_iso_projectiveLine e
  have := smooth_of_iso_projectiveLine e
  obtain ⟨s, hs⟩ := exists_section_of_iso_projectiveLine e
  obtain ⟨p⟩ : Nonempty (Spec (.of k)) := inferInstance
  exact ⟨s p, normalRationalPoint_of_section f s hs p⟩

omit e in
/-- **A scheme isomorphic over `k` to `𝐏¹_k` has `H⁰(X, 𝒪_X) = k`**: the global functions form a
field contained in the residue field `k` of a rational point. -/
theorem isIso_globalSections_of_iso_projectiveLine
    (e : Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) := by
  have := isProper_of_iso_projectiveLine e
  have := isCurve_of_iso_projectiveLine e
  obtain ⟨n, x, -, -, hgcd⟩ := exists_normalPoints_gcd_eq_one_of_iso_projectiveLine e
  exact isIso_globalSections_of_gcd f x hgcd

/-- **A scheme isomorphic over `k` to `𝐏¹_k` is geometrically irreducible over `k`**
([Stacks, Tag 0FD3], `X` being proper and smooth with `H⁰(X, 𝒪_X) = k`). -/
theorem geometricallyIrreducible_of_iso_projectiveLine : GeometricallyIrreducible f := by
  have := isProper_of_iso_projectiveLine e
  have := smooth_of_iso_projectiveLine e
  have := isIso_globalSections_of_iso_projectiveLine e
  exact geometricallyIrreducible_of_smooth_of_isIso f

/-- **A scheme isomorphic over `k` to `𝐏¹_k` is geometrically integral over `k`**
([Stacks, Tag 0FD3]). -/
@[ega "II 7.4.14" "more general"]
theorem geometricallyIntegral_of_iso_projectiveLine : GeometricallyIntegral f := by
  have := isProper_of_iso_projectiveLine e
  have := smooth_of_iso_projectiveLine e
  have := isIso_globalSections_of_iso_projectiveLine e
  exact geometricallyIntegral_of_smooth_of_isIso f

/-- **A scheme isomorphic over `k` to `𝐏¹_k` is Gorenstein**: it is smooth over `k`, hence
regular ([Stacks, Tag 056S]), and regular schemes are Gorenstein ([Stacks, Tag 0DWG]). -/
theorem isGorenstein_of_iso_projectiveLine : IsGorenstein X := by
  have := smooth_of_iso_projectiveLine e
  exact isGorenstein_of_smooth f

/-- **A scheme isomorphic over `k` to `𝐏¹_k` has genus zero**, read off the polynomial model
`Proj k[T₀, T₁]`. -/
theorem genus_of_iso_projectiveLine : genus f = 0 :=
  Stacks.Curves.genus_eq_zero_of_iso_projectiveLine
    (isoOfIsoProjectiveLine e ≪≫
      (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 1).iso) f

omit e in
/-- **A scheme isomorphic over `k` to `𝐏¹_k` has `H¹(X, 𝒪_X) = 0`.** -/
theorem isZero_cohomologyOverField_one_of_iso_projectiveLine
    (e : Over.mk f ≅ Over.mk (projectiveSpaceOver 1 (Spec (.of k)) ↘ Spec (.of k))) :
    IsZero (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) := by
  have := isProper_of_iso_projectiveLine e
  exact (genus_eq_zero_iff_isZero f).mp (genus_of_iso_projectiveLine e)

/-- **A scheme isomorphic over `k` to `𝐏¹_k` has an invertible module of degree `1`**, the
invertible module `𝒪_X(x)` of a rational point. -/
theorem exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine
    (hdim : topologicalKrullDim X ≤ 1) :
    letI := isProper_of_iso_projectiveLine e
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      invertibleCurveDegree k f hdim L = 1 := by
  let := isProper_of_iso_projectiveLine e
  have := isCurve_of_iso_projectiveLine e
  obtain ⟨n, x, hx, hnorm, hgcd⟩ := exists_normalPoints_gcd_eq_one_of_iso_projectiveLine e
  exact exists_invertibleCurveDegree_eq_one_of_gcd f hdim x hx hnorm hgcd

/-- **A scheme isomorphic over `k` to `𝐏¹_k` has an invertible module of odd degree.** -/
theorem exists_invertibleCurveDegree_odd_of_iso_projectiveLine
    (hdim : topologicalKrullDim X ≤ 1) :
    letI := isProper_of_iso_projectiveLine e
    ∃ (L : X.Modules) (_ : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L),
      Odd (invertibleCurveDegree k f hdim L) := by
  let := isProper_of_iso_projectiveLine e
  obtain ⟨L, hL, h⟩ := exists_invertibleCurveDegree_eq_one_of_iso_projectiveLine e hdim
  exact ⟨L, hL, h ▸ odd_one⟩

end AlgebraicGeometry.ProjectiveLineCriterion

end
