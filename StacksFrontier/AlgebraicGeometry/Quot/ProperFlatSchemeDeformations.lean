module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceOfScheme
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.Artin.Predeformation.Factorization

/-!
# Scheme deformations give deformations in `Spaces'_{fp, flat, proper}`

Let `k` be a field with `Spec k` in a big fppf site `B`, and let `f : X ⟶ Spec k` be a flat,
proper morphism of finite presentation, giving the point `x₀` of the stack
`𝒳 = Spaces'_{fp, flat, proper}` over the big fppf site of `Spec k`. A deformation of the scheme
`X` over an object `A` of `𝒞_k` (Stacks 0DY7) is a flat scheme `X'` over `Spec A` with a cartesian
square identifying its fibre over the closed point with `X`. Then `X' ⟶ Spec A` is proper and of
finite presentation as well (the special fibre is a thickening of finite order, Stacks 06AG), so
`X'`, viewed as an algebraic space, is an object of `𝒳` over `Spec A`, and the cartesian square
is a morphism `x₀ ⟶ X'` of `𝒳` over the closed point `Spec k ⟶ Spec A`: a deformation of `x₀` in
the predeformation category `𝓕_{𝒳,k,x₀}` (Stacks 07T2).

## Main definitions

* `AlgebraicGeometry.ProperFlatSpaceOfScheme.siteObjOfDeformation`: the total space of a scheme
  deformation as an object of the site over `Spec k`.
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.specialSiteHom`: the special-fibre immersion as a
  morphism of the site.
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.toDeformationObject`: the deformation of the point
  `x₀` attached to a scheme deformation of `X`.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceOfScheme.isPullback_specialSiteHom`: the special-fibre square
  of a scheme deformation is cartesian in the site.
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.total_point_toDeformationObject` and
  `AlgebraicGeometry.ProperFlatSpaceOfScheme.arrow_toDeformationObject`: the total space and the
  arrow of `toDeformationObject P` are those represented by `P`.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 07T2](https://stacks.math.columbia.edu/tag/07T2)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Deformation Deformation.Examples

universe u

namespace Deformation.Examples.SchemeDeformationCategory

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k] {X : Over (Spec (.of k))}

/-- The special-fibre immersion of a scheme deformation is a closed immersion. -/
instance isClosedImmersion_specialMap (P : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    IsClosedImmersion P.specialMap :=
  deformationSpecialMap_isClosedImmersion P

end Deformation.Examples.SchemeDeformationCategory

namespace AlgebraicGeometry.ProperFlatSpaceOfScheme

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
  (P : SchemeDeformationCategory (Λ := k) (k := k) (Over.mk f))

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- The structure morphism of a scheme deformation of `X` is proper. -/
theorem isProper_toBase : IsProper P.toBase :=
  haveI : IsProper (Over.mk f).hom := ‹IsProper f›
  P.isProper_toBase

omit [Flat f] [LocallyOfFinitePresentation f] in
include hk in
/-- The big fppf site contains the total space of a scheme deformation of `X`. -/
theorem contains_scheme : B.Contains P.scheme :=
  haveI : IsProper (Over.mk f).hom := ‹IsProper f›
  P.contains_scheme B hk

/-- The base `Spec A` of a scheme deformation of `X`, as an object of the site over `Spec k`, in
the form used by the predeformation category (`Deformation.Artin.algebraOver`). -/
abbrev baseObjOfDeformation : BigFppfOver B (Spec (.of k)) hk :=
  Deformation.Artin.algebraOver P.base B (Spec (.of k)) hk
    (Spec.map (CommRingCat.ofHom (algebraMap k P.base)) ≫ 𝟙 (Spec (.of k)))
    (contains_baseSpec B hk P.base)

/-- The total space of a scheme deformation of `X`, as an object of the site over `Spec k`,
through `P.toBase ≫ Spec (k → A)`. -/
abbrev siteObjOfDeformation : BigFppfOver B (Spec (.of k)) hk :=
  Over.mk (ObjectProperty.homMk (P.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.base))) :
    B.obj (contains_scheme B k hk f P) ⟶ B.obj hk)

/-- The structure morphism of a scheme deformation of `X`, as a morphism of the site. -/
def toBaseObjOfDeformation : siteObjOfDeformation B k hk f P ⟶ baseObjOfDeformation B k hk f P :=
  Over.homMk (ObjectProperty.homMk P.toBase) (by
    apply ObjectProperty.hom_ext
    change P.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.base)) ≫ 𝟙 (Spec (.of k)) =
      P.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.base))
    rw [Category.comp_id])

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- The underlying morphism of schemes of `toBaseObjOfDeformation P` is `P.toBase`. -/
@[simp]
theorem toScheme_map_toBaseObjOfDeformation :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (toBaseObjOfDeformation B k hk f P) =
      P.toBase :=
  rfl

omit [IsProper f] [Flat f] [LocallyOfFinitePresentation f] in
/-- The residue identity `Spec k ⟶ Spec A ⟶ Spec k` of an object of `𝒞_k`. -/
theorem residueSpecMap_comp_specMap_algebraMap :
    residueSpecMap P.base ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.base)) =
      Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Deformation.Artin.residueMap_comp_algebraMap_artinianLocalAlg]

/-- The closed point `Spec k ⟶ Spec A` of the base of a scheme deformation, as a morphism of the
site. -/
def baseSiteHom : baseObj B k hk ⟶ baseObjOfDeformation B k hk f P :=
  Over.homMk (ObjectProperty.homMk (residueSpecMap P.base)) (by
    apply ObjectProperty.hom_ext
    change residueSpecMap P.base ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.base)) ≫
      𝟙 (Spec (.of k)) = Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 (Spec (.of k))
    rw [← Category.assoc, residueSpecMap_comp_specMap_algebraMap])

omit [IsProper f] [Flat f] [LocallyOfFinitePresentation f] in
/-- The underlying morphism of schemes of `baseSiteHom P` is the closed point. -/
@[simp]
theorem toScheme_map_baseSiteHom :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (baseSiteHom B k hk f P) =
      residueSpecMap P.base :=
  rfl

/-- The special-fibre immersion `X ⟶ X'` of a scheme deformation, as a morphism of the site. -/
def specialSiteHom : siteObj B k hk f ⟶ siteObjOfDeformation B k hk f P :=
  Over.homMk (ObjectProperty.homMk P.specialMap) (by
    apply ObjectProperty.hom_ext
    change P.specialMap ≫ P.toBase ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.base)) = f
    rw [← Category.assoc, P.specialCartesian.w]
    change (f ≫ residueSpecMap P.base) ≫ _ = f
    rw [Category.assoc, residueSpecMap_comp_specMap_algebraMap, Algebra.algebraMap_self,
      CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])

/-- The underlying morphism of schemes of `specialSiteHom P` is `P.specialMap`. -/
@[simp]
theorem toScheme_map_specialSiteHom :
    (BigFppfOver.toScheme B (Spec (.of k)) hk).map (specialSiteHom B k hk f P) = P.specialMap :=
  rfl

/-- **The special-fibre square of a scheme deformation is cartesian in the site.** -/
theorem isPullback_specialSiteHom :
    IsPullback (specialSiteHom B k hk f P) (toBaseObj B k hk f)
      (toBaseObjOfDeformation B k hk f P) (baseSiteHom B k hk f P) :=
  FiniteFreeAlgebra.isPullback_of_isPullback_toScheme P.specialCartesian

/-- The total space of a scheme deformation of `X`, as an object of `Spaces'_{fp, flat, proper}`
over `Spec A`. -/
def pointOfDeformation : CartesianProperFlatSpaces B (Spec (.of k)) hk :=
  haveI := isProper_toBase k f P
  haveI : LocallyOfFinitePresentation (Over.mk f).hom := ‹LocallyOfFinitePresentation f›
  haveI := P.locallyOfFinitePresentation_toBase
  haveI := P.flat
  CartesianProperFlatSpaces.mk' (baseObjOfDeformation B k hk f P)
    (yoneda.obj (siteObjOfDeformation B k hk f P)) (isAlgebraicSpace_yoneda B _ hk _)
    (yoneda.map (toBaseObjOfDeformation B k hk f P))
    (Space.isFinitePresentation_yoneda_map B _ hk _ (by
      change FinitePresentation P.toBase
      exact ⟨inferInstance, inferInstance, inferInstance⟩))
    (Space.isFlat_yoneda_map B _ hk _ (by change Flat P.toBase; infer_instance))
    ((Space.isProper_yoneda_map_iff B _ hk _).2 (by change IsProper P.toBase; infer_instance))

/-- The morphism `x₀ ⟶ X'` of `Spaces'_{fp, flat, proper}` given by the special-fibre square of a
scheme deformation. -/
def arrowOfDeformation : point B k hk f ⟶ pointOfDeformation B k hk f P :=
  CartesianProperFlatSpaces.homOfIsPullback (x := point B k hk f)
    (y := pointOfDeformation B k hk f P) (yoneda.map (specialSiteHom B k hk f P))
    (baseSiteHom B k hk f P) ((isPullback_specialSiteHom B k hk f P).map yoneda)

/-- **A scheme deformation of `X` is a deformation of the point `x₀` of
`Spaces'_{fp, flat, proper}`**: an object of the predeformation category `𝓕_{𝒳,k,x₀}` over the
same object of `𝒞_k`. -/
def toDeformationObject :
    Deformation.Artin.DeformationObject (𝟙 (Spec (.of k)))
      (cartesianProperFlatProjection B (Spec (.of k)) hk ⋙ Over.post B.inclusion)
      (point B k hk f) (projection_point B k hk f) where
  algebra := P.base
  point := pointOfDeformation B k hk f P
  arrow := arrowOfDeformation B k hk f P
  base := rfl
  arrow_base := rfl

/-- The algebra of `toDeformationObject P` is the base of `P`. -/
@[simp]
theorem algebra_toDeformationObject : (toDeformationObject B k hk f P).algebra = P.base :=
  rfl

/-- The total space of `toDeformationObject P` is the presheaf represented by the total space
of `P`. -/
theorem total_point_toDeformationObject :
    (toDeformationObject B k hk f P).point.total = yoneda.obj (siteObjOfDeformation B k hk f P) :=
  rfl

/-- The base of `toDeformationObject P` is `Spec A`. -/
theorem base_point_toDeformationObject :
    (toDeformationObject B k hk f P).point.base = baseObjOfDeformation B k hk f P :=
  rfl

/-- The structure morphism of `toDeformationObject P` is represented by that of `P`. -/
theorem toBase_point_toDeformationObject :
    (toDeformationObject B k hk f P).point.toBase =
      yoneda.map (toBaseObjOfDeformation B k hk f P) :=
  rfl

/-- The map of total spaces of the arrow of `toDeformationObject P` is represented by the
special-fibre immersion of `P`. -/
theorem arrow_toDeformationObject :
    (toDeformationObject B k hk f P).arrow.hom.hom.left.hom =
      yoneda.map (specialSiteHom B k hk f P) :=
  rfl

/-- The map of bases of the arrow of `toDeformationObject P` is the closed point of `Spec A`. -/
theorem arrow_right_toDeformationObject :
    (toDeformationObject B k hk f P).arrow.hom.hom.right = baseSiteHom B k hk f P :=
  rfl

end AlgebraicGeometry.ProperFlatSpaceOfScheme

end
