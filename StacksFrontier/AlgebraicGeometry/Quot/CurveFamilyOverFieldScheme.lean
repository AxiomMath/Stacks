module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyTotalScheme
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceTowerHypotheses
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionOneSchematicLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionLocalRings
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedAffineBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionSemicontinuity
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison

/-!
# The total space of a family of curves over a field is a scheme

Let `F` be a family of curves (Stacks 0D4Z) over the spectrum of a field `K`. Its total space is
an algebraic space, separated and of finite type over `Spec K`, hence absolutely separated and
locally Noetherian, and of dimension at most one at each of its points, because over a field the
relative dimension of the structure morphism is the dimension of the total space. By Stacks 0ADD
every point has an open neighbourhood which is a scheme, so the total space is a scheme
(Stacks 03JH; `AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`).

Being a scheme, the total space is a proper scheme `X` of dimension at most one over the field,
and the family is isomorphic to the family `AlgebraicGeometry.curveFamilyOfScheme` of `X`.

## Main results

* `AlgebraicGeometry.CurveFamily.dimensionAtPoint_total_le_one_of_base_eq`: the total space of a
  family of curves over the spectrum of a field has dimension at most one at each of its points.
* `AlgebraicGeometry.CurveFamily.exists_iso_curveFamilyOfScheme_of_base_eq`: a family of curves
  over the spectrum of a field `K` is isomorphic to the family of a proper scheme of dimension at
  most one over `K`.

## References

* [Stacks Project, Tag 0ADD](https://stacks.math.columbia.edu/tag/0ADD)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- **An isomorphism of families of curves** from isomorphisms of the base schemes and of the
total spaces compatible with the structure morphisms: a commutative square whose horizontal sides
are isomorphisms is cartesian. -/
def isoMk {F G : CurveFamily B hZ} (β : F.base ≅ G.base) (ε : F.total ≅ G.total)
    (w : ε.hom ≫ G.toBase = F.toBase ≫ schemeSpaceMap β.hom) : F ≅ G where
  hom :=
    { baseMap := β.hom
      totalMap := ε.hom
      cartesian := by
        have : IsIso (schemeSpaceMap β.hom) :=
          (inferInstance : IsIso ((schemeSpaceFunctor B integerBase hZ).mapIso β).hom)
        exact IsPullback.of_horiz_isIso ⟨w⟩ }
  inv :=
    { baseMap := β.inv
      totalMap := ε.inv
      cartesian := by
        have : IsIso (schemeSpaceMap β.inv) :=
          (inferInstance : IsIso ((schemeSpaceFunctor B integerBase hZ).mapIso β).inv)
        refine IsPullback.of_horiz_isIso ⟨?_⟩
        rw [Iso.inv_comp_eq, ← Category.assoc, w, Category.assoc, ← schemeSpaceMap_comp,
          β.hom_inv_id, show schemeSpaceMap (𝟙 F.base) = 𝟙 _ from
            (schemeSpaceFunctor B integerBase hZ).map_id _, Category.comp_id] }
  hom_inv_id := CurveFamily.Hom.ext β.hom_inv_id ε.hom_inv_id
  inv_hom_id := CurveFamily.Hom.ext β.inv_hom_id ε.inv_hom_id

/-- **The dimension of the total space of a family of curves over a field is at most one** at
each of its points: over the spectrum of a field the relative dimension of the structure morphism
at a point is the dimension of the total space there. -/
theorem dimensionAtPoint_total_le_one_of_base_eq {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (F : CurveFamily B hZ)
    (hF : F.base = integerSiteObject B hZ hK) (x : Space.points B integerBase hZ F.total.obj) :
    Space.dimensionAtPoint B integerBase hZ F.total.obj F.total.property x ≤ 1 := by
  cases F with
  | mk base total toBase _ _ _ hrel => ?_
  change base = _ at hF
  subst hF
  let p : Space.FieldValuedPoint B integerBase hZ (yoneda.obj (integerSiteObject B hZ hK)) :=
    ⟨K, hK, specULiftZIsTerminal.from _, 𝟙 _⟩
  obtain ⟨e, he, hx⟩ := hrel x
  have h := (Space.relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B integerBase hZ
    total.property p toBase.hom x e).1 hx
  change Space.dimensionAtPoint B integerBase hZ total.obj total.property x ≤ 1
  rw [h]
  exact_mod_cast he

/-- **A family of curves over a field is the family of a proper curve.** If the base of a family
of curves is the spectrum of a field `K`, its total space is a scheme `X`
(`AlgebraicGeometry.CurveFamily.isRepresentable_total_of_base_eq`), proper over `K` because the
structure morphism is, and of dimension at most one because the relative dimension over a field is
the dimension; the family is isomorphic to the family `AlgebraicGeometry.curveFamilyOfScheme` of
`X ⟶ Spec K`. -/
theorem exists_iso_curveFamilyOfScheme_of_base_eq {K : Type u} [Field K]
    (hK : B.Contains (Spec (.of K))) (F : CurveFamily B hZ)
    (hF : F.base = integerSiteObject B hZ hK) :
    ∃ (X : Over (Spec (.of K))) (_ : IsProper X.hom) (hdim : topologicalKrullDim X.left ≤ 1),
      Nonempty (F ≅ curveFamilyOfScheme X B hZ hK hdim) := by
  have hrep := F.isRepresentable_total_of_base_eq (K := K)
    (congrArg (BigFppfOver.toScheme B integerBase hZ).obj hF)
  have hdimF := dimensionAtPoint_total_le_one_of_base_eq hK F hF
  cases F with
  | mk base total toBase hflat hproper hfp hrel => ?_
  change base = _ at hF
  subst hF
  obtain ⟨T, ⟨e⟩⟩ : ∃ T : BigFppfOver B integerBase hZ, Nonempty (total ≅ schemeSpace T) :=
    ⟨total.1.reprX, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso total.1.reprW.symm⟩⟩
  obtain ⟨⟨T, hT⟩, ⟨⟨⟩⟩, tHom⟩ := T
  obtain rfl : tHom = ObjectProperty.homMk (specULiftZIsTerminal.from _) :=
    ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _)
  replace e : total ≅ schemeSpace (integerSiteObject B hZ hT) := e
  obtain ⟨g, hg⟩ : ∃ g : integerSiteObject B hZ hT ⟶ integerSiteObject B hZ hK,
      schemeSpaceMap g = e.inv ≫ toBase :=
    ⟨(schemeSpaceFunctorFullyFaithful _ _).preimage _,
      (schemeSpaceFunctorFullyFaithful _ _).map_preimage _⟩
  let X : Over (Spec (.of K)) := Over.mk ((BigFppfOver.toScheme B integerBase hZ).map g)
  have hXp : IsProper X.hom := by
    have h₁ : Space.IsProper B integerBase hZ (yoneda.map g) := by
      have : IsIso e.inv.hom := inferInstanceAs (IsIso ((ObjectProperty.ι _).map e.inv))
      rw [show yoneda.map g = e.inv.hom ≫ toBase.hom from congrArg (fun φ => φ.hom) hg]
      exact Space.isProper_comp B integerBase hZ (isAlgebraicSpace_yoneda B integerBase hZ _)
        total.property (isAlgebraicSpace_yoneda B integerBase hZ _) e.inv.hom toBase.hom
        (Space.isProper_of_isIso B integerBase hZ e.inv.hom) hproper
    have : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B integerBase hZ)).IsStableUnderBaseChange :=
      ⟨fun hsq hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @_root_.AlgebraicGeometry.IsProper)
        (hsq.map (BigFppfOver.toScheme B integerBase hZ)) hg⟩
    exact (MorphismProperty.relative_map_iff (F := yoneda)
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsProper.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B integerBase hZ))).mp
      ((Space.presheaf_isProper_iff B integerBase hZ (yoneda.map g)
        (isAlgebraicSpace_yoneda B integerBase hZ _) (isAlgebraicSpace_yoneda B integerBase hZ _)
        (Functor.relativelyRepresentable.map yoneda g)).mp h₁)
  have hdim : topologicalKrullDim X.left ≤ 1 := by
    change topologicalKrullDim
      ((BigFppfOver.toScheme B integerBase hZ).obj (integerSiteObject B hZ hT)) ≤ 1
    rw [← Space.dimension_yoneda_eq_topologicalKrullDim B integerBase hZ,
      ← Space.dimension_eq_of_iso B integerBase hZ total.property
        (isAlgebraicSpace_yoneda B integerBase hZ _) ((ObjectProperty.ι _).mapIso e)]
    exact iSup_le hdimF
  refine ⟨X, hXp, hdim, ⟨isoMk (Iso.refl _) e ?_⟩⟩
  change e.hom ≫ schemeSpaceMap (integerSiteMap B hZ hT hK
      ((BigFppfOver.toScheme B integerBase hZ).map g)) =
    toBase ≫ schemeSpaceMap (𝟙 (integerSiteObject B hZ hK))
  rw [integerSiteMap_toScheme_map, hg, Iso.hom_inv_id_assoc,
    show schemeSpaceMap (𝟙 (integerSiteObject B hZ hK)) = 𝟙 _ from
      (schemeSpaceFunctor B integerBase hZ).map_id _, Category.comp_id]

end AlgebraicGeometry.CurveFamily

end
