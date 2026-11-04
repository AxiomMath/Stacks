module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeFpqcDescentSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.StalkwiseSlicePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleStructureSheafPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSlicePointsOfFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectJacobsonDescent

/-!
# Stacks 0DL2: locally finite Tor dimension descends along fpqc coverings

Let `{g_i : Y_i ⟶ Y}` be an fpqc covering of algebraic spaces over `S`, let `f : X ⟶ Y` be a
morphism of algebraic spaces, and let `X_i = Y_i ×_Y X` with projections `f_i : X_i ⟶ Y_i` and
`g'_i : X_i ⟶ X`.  This file proves the second assertion of Stacks 0DL2: an object `E` of `D(𝒪_X)`
locally has finite Tor dimension as an object of `D(f⁻¹𝒪_Y)` if and only if every `L(g'_i)^*E`
locally has finite Tor dimension as an object of `D(f_i⁻¹𝒪_{Y_i})`.  The first assertion, for a
fixed interval `[a, b]`, is
`AlgebraicGeometry.Space.hasTorAmplitude_derivedScalarRestriction_iff_forall_of_isFpqcCovering`.

## Main results

* `locallyHasFiniteTorDimension_derivedScalarRestriction_pullback_of_cartesian`:
  the pullback half, for any cartesian square with flat lower edge.
* `locallyHasFiniteTorDimension_derivedScalarRestriction_of_forall_pullback`:
  the descent half.
* `locallyHasFiniteTorDimension_derivedScalarRestriction_iff_forall_of_isFpqcCovering`:
  Stacks 0DL2 for locally finite Tor dimension.

## Implementation notes

Both halves are reduced to derived stalks at geometric points.  On a slice of the small étale
site, Tor amplitude of a restriction is tested on the derived stalks at the geometric points
lifting to the chart (Stacks 0DJJ on the slice, through Stacks 04H2); at a geometric point the
amplitude moves across a cartesian square with flat lower edge in both directions
(`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_derivedModuleFiber_pullback_of_cartesian` and
`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_derivedModuleFiber_of_pullback_of_cartesian`).

The pullback half needs no topology: a chart of `X_i` on which `L(g'_i)^*E` is tested is covered
by its fibre products with charts of `X` on which `E` has finite Tor dimension.

The descent half is the "elementary topology" of the source.  The images of étale charts are
open, but the members of an fpqc covering are only flat, so a chart of `X_i` does not have open
image in `X`.  Instead, for an affine chart `U` of `X` the base change of the covering is refined
by finitely many affines `T_j` mapping to the `X_i`; each `T_j` is quasi-compact, so finitely many
charts of the `X_i`, base changed to `T_j`, cover it, and their bounds combine to one interval.
The geometric points of these base changes then give a family of geometric points of `X`, with
lifts to `U` meeting every point of `U`, at which the derived stalks of `E` are bounded; such a
family is conservative on the slice over `U`
(`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePointOver_of_family`), although it
is not the family of all geometric points.

As for the first assertion, the statement is proved for arbitrary cartesian squares presenting the
`X_i` and for every object of `D(𝒪_X)`, without the quasi-coherence hypothesis of the source, and
Tor amplitude on each slice is measured against the canonical derived tensor product.

## References

* [Stacks Project, Tag 0DL2](https://stacks.math.columbia.edu/tag/0DL2)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude

namespace AlgebraicGeometry.Space

universe u v

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Transfer

-- The standard model is forced: `HasTorAmplitudeCanonical`, `smallEtaleDerivedModulePullback` and
-- `RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff` are stated only for it.
attribute [local instance 10000] HasDerivedCategory.standard

variable {X' X Y' Y : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y)

/-- **Stacks 0DKD (1) at a geometric point, for an object of `D(𝒪_X)`.**  For a cartesian square
with flat lower edge `g`, if the derived stalk at `g'(x̄')` of `E` read in `D(f⁻¹𝒪_Y)` has Tor
amplitude in `[a, b]`, then so does the derived stalk at `x̄'` of `L(g')^*E` read in
`D(f'⁻¹𝒪_{Y'})`. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_pullback_of_cartesian
    (hpb : IsPullback g' f' f g) (hg : IsFlat B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (x' : GeometricPoint B S hS X'.1)
    (a b : ℤ)
    (h : HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2).presheafFiber
        (A := CommRingCat.{u})).obj (inverseImageRingedSite B S hS f).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
        (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
      a b) :
    HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X'.1 x' X'.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f').O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
        (inverseImageRingedSite B S hS f').O).obj ((derivedScalarRestriction B S hS f').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E))) a b := by
  have hg' : IsFlat B S hS g'.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb.flip hg
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have h₀ := AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
      (inverseImageRingedSite B S hS f).O).mapIso
      ((derivedScalarRestriction B S hS f).mapIso e.symm)) a b h
  have h₁ := (hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_pullback_iff B S hS
    g' hg' f' x' K a b).2
    (hasTorAmplitudeCanonical_geometricStalk_baseChange B S hS g' f' f g hpb hg x' _ a b
      ((hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_iff B S hS f
        (geometricPointMap g'.hom x') K a b).1 h₀))
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
      (inverseImageRingedSite B S hS f').O).mapIso
      ((derivedScalarRestriction B S hS f').mapIso
        ((smallEtaleDerivedModulePullback B S hS g').mapIso e))) a b h₁

/-- **The descent half of Stacks 0DL2 at a geometric point, for an object of `D(𝒪_X)`.**  For a
cartesian square with flat lower edge `g`, if the derived stalk at `x̄'` of `L(g')^*E` read in
`D(f'⁻¹𝒪_{Y'})` has Tor amplitude in `[a, b]`, then so does the derived stalk at `g'(x̄')` of `E`
read in `D(f⁻¹𝒪_Y)`. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_of_pullback_of_cartesian
    (hpb : IsPullback g' f' f g) (hg : IsFlat B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (x' : GeometricPoint B S hS X'.1)
    (a b : ℤ)
    (h : HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X'.1 x' X'.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f').O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
        (inverseImageRingedSite B S hS f').O).obj ((derivedScalarRestriction B S hS f').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E))) a b) :
    HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2).presheafFiber
        (A := CommRingCat.{u})).obj (inverseImageRingedSite B S hS f).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
        (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
      a b := by
  have hg' : IsFlat B S hS g'.hom :=
    (isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb.flip hg
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  have h₀ := AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X'.1 x' X'.2)
      (inverseImageRingedSite B S hS f').O).mapIso
      ((derivedScalarRestriction B S hS f').mapIso
        ((smallEtaleDerivedModulePullback B S hS g').mapIso e.symm))) a b h
  have h₁ := (hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_iff B S hS f
    (geometricPointMap g'.hom x') K a b).2
    (hasTorAmplitudeCanonical_geometricStalk_of_baseChange B S hS g' f' f g hpb hg x' _ a b
      ((hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_pullback_iff B S hS
        g' hg' f' x' K a b).1 h₀))
  exact AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 (geometricPointMap g'.hom x') X.2)
      (inverseImageRingedSite B S hS f).O).mapIso
      ((derivedScalarRestriction B S hS f).mapIso e)) a b h₁

end Transfer

section Slices

-- The standard model is forced: `HasTorAmplitudeCanonical`, `smallEtaleDerivedModulePullback` and
-- `RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff` are stated only for it.
attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.DerivedTensorProduct.sliceLocallySmall

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)

/-- Sheafification of abelian presheaves on a slice of `(X_étale, f⁻¹𝒪_Y)`, from the small étale
site of `X`; it has to be preferred to Mathlib's universe-generic construction, which does not
apply to a site whose objects lie one universe above its morphisms. -/
@[local instance high]
theorem inverseImageSlice_hasSheafify (V : (inverseImageRingedSite B S hS f).C) :
    HasSheafify ((inverseImageRingedSite B S hS f).over V).J AddCommGrpCat.{u} :=
  smallEtaleRingedSite_hasSheafify_over_addCommGrpCat B S hS X.1 X.2 V

/-- The sheafification adjunction on a slice of `(X_étale, f⁻¹𝒪_Y)`, read off
`inverseImageSlice_hasSheafify`. -/
@[local instance high]
theorem inverseImageSlice_isRightAdjoint (V : (inverseImageRingedSite B S hS f).C) :
    (sheafToPresheaf ((inverseImageRingedSite B S hS f).over V).J
      AddCommGrpCat.{u}).IsRightAdjoint :=
  (smallEtaleRingedSite_hasSheafify_over_addCommGrpCat B S hS X.1 X.2 V).isRightAdjoint

/-- On a slice `V` of `(X_étale, f⁻¹𝒪_Y)`, a Tor-amplitude bound on `E|_V` bounds the derived stalk
of `E` at every geometric point of `X` lifting to `V` (Stacks 0DJJ (1) on the slice, and
Stacks 04H2). -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_of_derivedRestriction
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (V : (inverseImageRingedSite B S hS f).C)
    (x : GeometricPoint B S hS X.1) (p : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V) (a b : ℤ)
    (h : Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over V))
      ((RingedSite.derivedRestriction (inverseImageRingedSite B S hS f) V).obj
        ((derivedScalarRestriction B S hS f).obj E)) a b) :
    HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
      a b :=
  (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
    (Z := inverseImageRingedSite B S hS f)
    (etaleSitePoint B S hS X.1 x X.2 : (inverseImageRingedSite B S hS f).J.Point.{u}) p _ a b).1
    (hasTorAmplitudeCanonical_derivedModuleFiber.{u + 1, u, u, u + 1} _ _ a b h
      ((etaleSitePoint B S hS X.1 x X.2 : (inverseImageRingedSite B S hS f).J.Point.{u}).over p))

/-- On a slice `V` of `(X_étale, f⁻¹𝒪_Y)`, if the derived stalk of `E` at every geometric point of
`X` lifting to `V` has Tor amplitude in `[a, b]`, then so does `E|_V` (Stacks 0DJJ (2) on the
slice, tested on the lifts of the geometric points, and Stacks 04H2). -/
theorem hasTorAmplitude_derivedRestriction_of_forall_derivedModuleFiber
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (V : (inverseImageRingedSite B S hS f).C)
    (a b : ℤ)
    (h : ∀ (x : GeometricPoint B S hS X.1) (_ : (etaleSitePoint B S hS X.1 x X.2).fiber.obj V),
      HasTorAmplitudeCanonical
        (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
          (inverseImageRingedSite B S hS f).O.obj)
        ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
          (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
        a b) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over V))
      ((RingedSite.derivedRestriction (inverseImageRingedSite B S hS f) V).obj
        ((derivedScalarRestriction B S hS f).obj E)) a b :=
  hasTorAmplitude_of_forall_derivedModuleFiber_family.{u + 1, u, u, u + 1} _ _ a b
    (fun ψ : Σ x : GeometricPoint B S hS X.1, (etaleSitePoint B S hS X.1 x X.2).fiber.obj V =>
      ((etaleSitePoint B S hS X.1 ψ.1 X.2 : (inverseImageRingedSite B S hS f).J.Point.{u}).over
        ψ.2 : ((inverseImageRingedSite B S hS f).over V).J.Point.{u}))
    (isConservativeFamilyOfPoints_etaleSitePointOver B S hS X.2 V)
    (fun ψ => (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
      (Z := inverseImageRingedSite B S hS f)
      (etaleSitePoint B S hS X.1 ψ.1 X.2 : (inverseImageRingedSite B S hS f).J.Point.{u}) ψ.2
        _ a b).2 (h ψ.1 ψ.2))

/-- On a slice `V` of `(X_étale, f⁻¹𝒪_Y)`, a Tor-amplitude bound on the derived stalks of `E` at a
family of geometric points with lifts to `V` covering the points of `V` bounds `E|_V` (Stacks 0DJJ
(2) on the slice, tested on a conservative family, and Stacks 04H2). -/
theorem hasTorAmplitude_derivedRestriction_of_derivedModuleFiber_family
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (V : (inverseImageRingedSite B S hS f).C)
    (a b : ℤ) {t : Type*}
    (ψ : t → Σ x : GeometricPoint B S hS X.1, (etaleSitePoint B S hS X.1 x X.2).fiber.obj V)
    (hψ : ∀ v : (BigFppfOver.toScheme B S hS).obj V.obj.left, ∃ k,
      ∃ ζ : (BigFppfOver.toScheme B S hS).obj (ψ k).1.val.siteObject,
        (BigFppfOver.toScheme B S hS).map (ψ k).2.1 ζ = v)
    (h : ∀ k, HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X.1 (ψ k).1 X.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 (ψ k).1 X.2)
        (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E)) a b) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over V))
      ((RingedSite.derivedRestriction (inverseImageRingedSite B S hS f) V).obj
        ((derivedScalarRestriction B S hS f).obj E)) a b :=
  hasTorAmplitude_of_forall_derivedModuleFiber_family.{u + 1, u, u, u + 1} _ _ a b
    (fun k => ((etaleSitePoint B S hS X.1 (ψ k).1 X.2 :
      (inverseImageRingedSite B S hS f).J.Point.{u}).over (ψ k).2 :
        ((inverseImageRingedSite B S hS f).over V).J.Point.{u}))
    (isConservativeFamilyOfPoints_etaleSitePointOver_of_family B S hS X.2 V ψ hψ)
    (fun k => (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
      (Z := inverseImageRingedSite B S hS f)
      (etaleSitePoint B S hS X.1 (ψ k).1 X.2 : (inverseImageRingedSite B S hS f).J.Point.{u})
        (ψ k).2 _ a b).2 (h k))

/-- If `E` locally has finite Tor dimension over `f⁻¹𝒪_Y`, every geometric point `x` of `X` lifts to
a slice `V` on which `E|_V` has some Tor amplitude bound `[a, b]`. -/
private theorem exists_lift_hasTorAmplitude_derivedRestriction
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over U))
      ((derivedScalarRestriction B S hS f).obj E))
    (x : GeometricPoint B S hS X.1) :
    ∃ (V : (inverseImageRingedSite B S hS f).C) (_ : GeometricFiber B S hS X.1 x V) (a b : ℤ),
      Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
          ((inverseImageRingedSite B S hS f).over V))
        ((RingedSite.derivedRestriction (inverseImageRingedSite B S hS f) V).obj
          ((derivedScalarRestriction B S hS f).obj E)) a b := by
  have := isCofiltered_smallEtaleNeighborhood B S hS X.1 X.2 x
  obtain ⟨N⟩ : Nonempty (SmallEtaleNeighborhood x) := IsCofiltered.nonempty
  obtain ⟨S₀, hS₀, htor⟩ := hE N.chart
  obtain ⟨V₁, k₁, hk₁, y₁, -⟩ := (etaleSitePoint B S hS X.1 x X.2).jointly_surjective _ hS₀
    (⟨N.point, N.point_comp⟩ : GeometricFiber B S hS X.1 x N.chart)
  obtain ⟨V₂, p₁, k₂, hk₂, -⟩ := hk₁
  obtain ⟨a, b, hab⟩ := htor k₂ hk₂
  exact ⟨V₂, (etaleSitePoint B S hS X.1 x X.2).fiber.map p₁ y₁, a, b, hab⟩

end Slices

section Charts

variable {X' X : AlgebraicSpaces B S hS} (m : X'.1 ⟶ X.1) (V : SmallEtale B S hS X'.1)
  (V' : SmallEtale B S hS X.1)

/-- The étale chart `V ×_X V'` of `X'`, for an étale chart `V` of `X'`, an étale chart `V'` of `X`
and a morphism `m : X' ⟶ X`: the base change of `V' ⟶ X` along `V ⟶ X' ⟶ X`, mapping to `X'`
through `V`. -/
noncomputable def chartFiberProduct : SmallEtale B S hS X'.1 :=
  ⟨CostructuredArrow.mk (yoneda.map ((V'.property.rep).snd (V.obj.hom ≫ m)) ≫ V.obj.hom),
    have := isMultiplicative_presheaf_etale B S hS
    MorphismProperty.comp_mem _ _ _
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        ((V'.property.rep).isPullback (V.obj.hom ≫ m)) V'.property) V.property⟩

/-- The projection of `V ×_X V'` to `V`. -/
noncomputable def chartFiberProductFst : chartFiberProduct B S hS m V V' ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk ((V'.property.rep).snd (V.obj.hom ≫ m)) rfl)

/-- A lift of a geometric point `y'` of `X'` to `V ×_X V'` gives a lift of its image `m(y')` to
`V'`. -/
noncomputable def chartFiberProductLiftSnd (y' : GeometricPoint B S hS X'.1)
    (r : GeometricFiber B S hS X'.1 y' (chartFiberProduct B S hS m V V')) :
    GeometricFiber B S hS X.1 (geometricPointMap m y') V' := by
  refine ⟨r.1 ≫ (V'.property.rep).fst' (V.obj.hom ≫ m), ?_⟩
  have hw := congrFun (congrArg (fun η => η.app (Opposite.op y'.val.siteObject))
    ((V'.property.rep).w (V.obj.hom ≫ m))) r.1
  rw [← (V'.property.rep).map_fst'] at hw
  exact hw.trans (congrArg (m.app (Opposite.op y'.val.siteObject)) r.2)

/-- The compatibility condition for lifting a pair of lifts to `V ×_X V'`. -/
theorem chartFiberProductLift_cond (x' : GeometricPoint B S hS X'.1)
    (q : GeometricFiber B S hS X'.1 x' V)
    (y : GeometricFiber B S hS X.1 (geometricPointMap m x') V') :
    yoneda.map y.1 ≫ V'.obj.hom = yoneda.map q.1 ≫ (V.obj.hom ≫ m) :=
  yonedaEquiv.injective <| y.2.trans (congrArg (m.app (Opposite.op x'.val.siteObject)) q.2.symm)

/-- Compatible lifts of a geometric point `x'` of `X'` to `V` and of `m(x')` to `V'` give a lift of
`x'` to `V ×_X V'`. -/
noncomputable def chartFiberProductLift (x' : GeometricPoint B S hS X'.1)
    (q : GeometricFiber B S hS X'.1 x' V)
    (y : GeometricFiber B S hS X.1 (geometricPointMap m x') V') :
    GeometricFiber B S hS X'.1 x' (chartFiberProduct B S hS m V V') :=
  ⟨(V'.property.rep).lift' y.1 q.1 (chartFiberProductLift_cond B S hS m V V' x' q y),
    (congrArg (V.obj.hom.app (Opposite.op x'.val.siteObject))
      ((V'.property.rep).lift'_snd y.1 q.1 (chartFiberProductLift_cond B S hS m V V' x' q y))).trans
      q.2⟩

/-- The lift of `chartFiberProductLift` lies over the given lift to `V`. -/
theorem chartFiberProductLift_comp_snd (x' : GeometricPoint B S hS X'.1)
    (q : GeometricFiber B S hS X'.1 x' V)
    (y : GeometricFiber B S hS X.1 (geometricPointMap m x') V') :
    (chartFiberProductLift B S hS m V V' x' q y).1 ≫
      (V'.property.rep).snd (V.obj.hom ≫ m) = q.1 :=
  (V'.property.rep).lift'_snd _ _ _

end Charts

section LocallyFinite

-- The standard model is forced: `HasTorAmplitudeCanonical`, `smallEtaleDerivedModulePullback` and
-- `RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff` are stated only for it.
attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.DerivedTensorProduct.sliceLocallySmall
attribute [local instance high] inverseImageSlice_hasSheafify inverseImageSlice_isRightAdjoint

variable {X' X Y' Y : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
  (g : Y' ⟶ Y)

/-- **Stacks 0DL2, locally finite Tor dimension, pullback half.**  For a cartesian square with
flat lower edge `g`, if `E` locally has finite Tor dimension as an object of `D(f⁻¹𝒪_Y)` then
`L(g')^*E` locally has finite Tor dimension as an object of `D(f'⁻¹𝒪_{Y'})`. -/
theorem locallyHasFiniteTorDimension_derivedScalarRestriction_pullback_of_cartesian
    (hpb : IsPullback g' f' f g) (hg : IsFlat B S hS g.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over U))
      ((derivedScalarRestriction B S hS f).obj E)) :
    LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f').over U))
      ((derivedScalarRestriction B S hS f').obj
        ((smallEtaleDerivedModulePullback B S hS g').obj E)) := by
  intro V
  refine ⟨fun W _ =>
      Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f').over W))
      ((RingedSite.derivedRestriction (inverseImageRingedSite B S hS f') W).obj
        ((derivedScalarRestriction B S hS f').obj
          ((smallEtaleDerivedModulePullback B S hS g').obj E))), ?_, fun W _ hW => hW⟩
  apply smallEtale_sieve_of_pointwise_covering B S hS X'.1 V
  intro z
  obtain ⟨x', q, z', hz⟩ := exists_geo_lift_at_chart_point B S hS X'.1 V z
  obtain ⟨V₂, y, a, b, hab⟩ :=
    exists_lift_hasTorAmplitude_derivedRestriction B S hS f E hE (geometricPointMap g'.hom x')
  refine ⟨chartFiberProduct B S hS g'.hom V V₂, chartFiberProductFst B S hS g'.hom V V₂,
    Sieve.le_generate _ _ _ ?_, ?_⟩
  · exact ⟨a, b, hasTorAmplitude_derivedRestriction_of_forall_derivedModuleFiber B S hS f' _ _ a b
      fun y' r => hasTorAmplitudeCanonical_derivedModuleFiber_pullback_of_cartesian B S hS g' f' f
        g hpb hg E y' a b (hasTorAmplitudeCanonical_derivedModuleFiber_of_derivedRestriction B S hS
          f E V₂ (geometricPointMap g'.hom y') (chartFiberProductLiftSnd B S hS g'.hom V V₂ y' r)
          a b hab)⟩
  · refine ⟨(BigFppfOver.toScheme B S hS).map
      (chartFiberProductLift B S hS g'.hom V V₂ x' q y).1 z', ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp]
    show (BigFppfOver.toScheme B S hS).map ((chartFiberProductLift B S hS g'.hom V V₂ x' q y).1 ≫
      (V₂.property.rep).snd (V.obj.hom ≫ g'.hom)) z' = z
    exact (congrArg (fun t => (BigFppfOver.toScheme B S hS).map t z')
      (chartFiberProductLift_comp_snd B S hS g'.hom V V₂ x' q y)).trans hz

end LocallyFinite

section Descent

-- The standard model is forced: `HasTorAmplitudeCanonical`, `smallEtaleDerivedModulePullback` and
-- `RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff` are stated only for it.
attribute [local instance 10000] HasDerivedCategory.standard

open Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.DerivedTensorProduct.sliceLocallySmall
attribute [local instance high] inverseImageSlice_hasSheafify inverseImageSlice_isRightAdjoint

/-- A Tor amplitude bound `[a i, b i]` weakens to the interval `[-∑ |a|, ∑ |b|]` over any finite
index set containing `i`. -/
private theorem hasTorAmplitudeCanonical_mono_sum {ι : Type*} {s : Finset ι} {i : ι}
    (hi : i ∈ s) (a b : ι → ℤ) {T : Type u} [CommRing T] {K : DerivedCategory (ModuleCat.{u} T)}
    (h : HasTorAmplitudeCanonical T K (a i) (b i)) :
    HasTorAmplitudeCanonical T K (-(∑ j ∈ s, |a j|)) (∑ j ∈ s, |b j|) :=
  Scheme.Hom.hasTorAmplitudeCanonical_mono
    ((neg_le_neg (Finset.single_le_sum (f := fun j => |a j|) (fun _ _ => abs_nonneg _) hi)).trans
      (neg_abs_le _))
    ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |b j|) (fun _ _ => abs_nonneg _) hi))
    h

section Bounds

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
  (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))

/-- **Locally finite Tor dimension bounds the derived stalks near a point.**  If `E` locally has
finite Tor dimension over `f⁻¹𝒪_Y`, then for every morphism `β : T ⟶ X` from an object of the big
fppf site and every point `t` of `T` there are an interval `[a, b]` and an open neighbourhood `O`
of `t` such that every point of `O` is hit by a geometric point of `T` at whose image in `X` the
derived stalk of `E` has Tor amplitude in `[a, b]`.  The neighbourhood is the image in `T` of the
base change of an étale chart of `X` on which `E` has finite Tor dimension. -/
theorem exists_isOpen_forall_hasTorAmplitudeCanonical_derivedModuleFiber
    (hE : LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over U))
      ((derivedScalarRestriction B S hS f).obj E))
    (T : BigFppfOver B S hS) (β : yoneda.obj T ⟶ X.1) (t : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (a b : ℤ) (O : Set ((BigFppfOver.toScheme B S hS).obj T)), IsOpen O ∧ t ∈ O ∧
      ∀ t' ∈ O, ∃ (x : GeometricPoint B S hS X.1) (ξ : x.val.siteObject ⟶ T),
        β.app (Opposite.op x.val.siteObject) ξ = x.val.value ∧
          (∃ ζ : (BigFppfOver.toScheme B S hS).obj x.val.siteObject,
            (BigFppfOver.toScheme B S hS).map ξ ζ = t') ∧
          HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
          a b := by
  obtain ⟨x, ξ, hξ, z', hz'⟩ := exists_geometricPoint_hom_of_point B S hS T β t
  obtain ⟨V₂, y, a, b, hab⟩ := exists_lift_hasTorAmplitude_derivedRestriction B S hS f E hE x
  let hr := V₂.property.rep
  have hEt : Etale ((BigFppfOver.toScheme B S hS).map (hr.snd β)) :=
    V₂.property.2 β (hr.fst β) (hr.snd β) (hr.isPullback β)
  have hopen : IsOpenMap ((BigFppfOver.toScheme B S hS).map (hr.snd β)).base := by
    have : AlgebraicGeometry.UniversallyOpen ((BigFppfOver.toScheme B S hS).map (hr.snd β)) :=
      AlgebraicGeometry.UniversallyOpen.of_flat _
    exact ((BigFppfOver.toScheme B S hS).map (hr.snd β)).isOpenMap
  refine ⟨a, b, Set.range ((BigFppfOver.toScheme B S hS).map (hr.snd β)).base,
    hopen.isOpen_range, ?_, ?_⟩
  · have hcompat : yoneda.map y.1 ≫ V₂.obj.hom = yoneda.map ξ ≫ β :=
      yonedaEquiv.injective (y.2.trans hξ.symm)
    refine ⟨(BigFppfOver.toScheme B S hS).map (hr.lift (yoneda.map y.1) ξ hcompat) z', ?_⟩
    show ((BigFppfOver.toScheme B S hS).map (hr.snd β))
      ((BigFppfOver.toScheme B S hS).map (hr.lift (yoneda.map y.1) ξ hcompat) z') = t
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hr.lift_snd]
    exact hz'
  · rintro t' ⟨c, rfl⟩
    obtain ⟨x', ξ', hξ', ζ, hζ⟩ := exists_geometricPoint_hom_of_point B S hS (hr.pullback β)
      (yoneda.map (hr.snd β) ≫ β) c
    refine ⟨x', ξ' ≫ hr.snd β, hξ', ⟨ζ, ?_⟩, ?_⟩
    · rw [Functor.map_comp, Scheme.Hom.comp_apply, hζ]
    · refine hasTorAmplitudeCanonical_derivedModuleFiber_of_derivedRestriction B S hS f E V₂ x'
        ⟨ξ' ≫ hr.fst' β, ?_⟩ a b hab
      have hw := congrFun (congrArg (fun η => η.app (Opposite.op x'.val.siteObject))
        (hr.w β)) ξ'
      rw [← hr.map_fst'] at hw
      exact hw.trans hξ'

/-- **Locally finite Tor dimension bounds the derived stalks over a quasi-compact object.**  If `E`
locally has finite Tor dimension over `f⁻¹𝒪_Y` and `β : T ⟶ X` is a morphism from an object of
the big fppf site whose underlying scheme is quasi-compact, then a single interval `[a, b]` works
at every point of `T`: finitely many of the neighbourhoods of
`exists_isOpen_forall_hasTorAmplitudeCanonical_derivedModuleFiber` cover `T`. -/
theorem exists_forall_hasTorAmplitudeCanonical_derivedModuleFiber_of_compactSpace
    (hE : LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over U))
      ((derivedScalarRestriction B S hS f).obj E))
    (T : BigFppfOver B S hS) (β : yoneda.obj T ⟶ X.1)
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj T)] :
    ∃ a b : ℤ, ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ (x : GeometricPoint B S hS X.1) (ξ : x.val.siteObject ⟶ T),
        β.app (Opposite.op x.val.siteObject) ξ = x.val.value ∧
          (∃ ζ : (BigFppfOver.toScheme B S hS).obj x.val.siteObject,
            (BigFppfOver.toScheme B S hS).map ξ ζ = t) ∧
          HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS X.1 x X.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS f).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS X.1 x X.2)
        (inverseImageRingedSite B S hS f).O).obj ((derivedScalarRestriction B S hS f).obj E))
          a b := by
  classical
  choose a b O hO hmem hgood using
    exists_isOpen_forall_hasTorAmplitudeCanonical_derivedModuleFiber B S hS f E hE T β
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun t _ => Set.mem_iUnion.2 ⟨t, hmem t⟩)
  refine ⟨-(∑ t ∈ s, |a t|), ∑ t ∈ s, |b t|, fun t' => ?_⟩
  obtain ⟨t, ht, ht'⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ t'))
  obtain ⟨x, ξ, hξ, hz, hP⟩ := hgood t t' ht'
  exact ⟨x, ξ, hξ, hz, hasTorAmplitudeCanonical_mono_sum ht a b hP⟩

end Bounds

variable {I : Type v} {Y : AlgebraicSpaces B S hS} {Yi : I → AlgebraicSpaces B S hS}
  (g : ∀ i, Yi i ⟶ Y) (hg : IsFpqcCovering B S hS fun i => (g i).hom)
  {X : AlgebraicSpaces B S hS} (f : X ⟶ Y) {Xi : I → AlgebraicSpaces B S hS}
  (f' : ∀ i, Xi i ⟶ Yi i) (g' : ∀ i, Xi i ⟶ X) (hpb : ∀ i, IsPullback (g' i) (f' i) f (g i))

include hg hpb in
/-- **The descent half of Stacks 0DL2 for locally finite Tor dimension, on an affine chart.**  If
every `L(g'_i)^*E` locally has finite Tor dimension over `f_i⁻¹𝒪_{Y_i}`, then `E` restricted to an
étale chart `U` of `X` with affine underlying scheme has finite Tor dimension over `f⁻¹𝒪_Y`.  The
base change of the covering to `U` is refined by finitely many affines `T_j ⟶ X_{i_j}`; each is
quasi-compact, so carries a single bound on the derived stalks of `L(g'_{i_j})^*E`, and these
descend to the derived stalks of `E` at the image geometric points, which meet every point of
`U`. -/
theorem exists_hasTorAmplitude_derivedRestriction_of_isAffine
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ i, LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS (f' i)).over U))
      ((derivedScalarRestriction B S hS (f' i)).obj
        ((smallEtaleDerivedModulePullback B S hS (g' i)).obj E)))
    (U : (inverseImageRingedSite B S hS f).C)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left)) :
    ∃ a b : ℤ, Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over U))
      ((RingedSite.derivedRestriction (inverseImageRingedSite B S hS f) U).obj
        ((derivedScalarRestriction B S hS f).obj E)) a b := by
  classical
  have hg' := isFpqcCovering_of_isPullback B S hS g hg f f' g' hpb
  let T₀ : BigAffineFppf B S hS := ⟨U.obj.left, hU⟩
  obtain ⟨𝒰, hfin, hfpqc, hfac⟩ := hg'.2 T₀ U.obj.hom
  choose i α hα using hfac
  have hcpt : ∀ j, CompactSpace ((BigFppfOver.toScheme B S hS).obj
      ((BigAffineFppf.inclusion B S hS).obj (𝒰.X j))) := fun j => by
    have : IsAffine ((BigFppfOver.toScheme B S hS).obj
        ((BigAffineFppf.inclusion B S hS).obj (𝒰.X j))) := (𝒰.X j).property
    infer_instance
  choose a b hgood using fun j =>
    exists_forall_hasTorAmplitudeCanonical_derivedModuleFiber_of_compactSpace B S hS (f' (i j))
      ((smallEtaleDerivedModulePullback B S hS (g' (i j))).obj E) (hE (i j))
      ((BigAffineFppf.inclusion B S hS).obj (𝒰.X j)) (α j)
  have := Fintype.ofFinite 𝒰.I₀
  refine ⟨-(∑ j, |a j|), ∑ j, |b j|, ?_⟩
  let ψ : (Σ j : 𝒰.I₀, Σ x : GeometricPoint B S hS (Xi (i j)).1,
      {ξ : x.val.siteObject ⟶ (BigAffineFppf.inclusion B S hS).obj (𝒰.X j) //
        (α j).app (Opposite.op x.val.siteObject) ξ = x.val.value ∧
          HasTorAmplitudeCanonical
          (((etaleSitePoint B S hS (Xi (i j)).1 x (Xi (i j)).2).presheafFiber
            (A := CommRingCat.{u})).obj
            (inverseImageRingedSite B S hS (f' (i j))).O.obj)
          ((Stacks.derivedModuleFiber (etaleSitePoint B S hS (Xi (i j)).1 x (Xi (i j)).2)
            (inverseImageRingedSite B S hS (f' (i j))).O).obj
              ((derivedScalarRestriction B S hS (f' (i j))).obj
                ((smallEtaleDerivedModulePullback B S hS (g' (i j))).obj E))) (a j) (b j)}) →
      Σ x : GeometricPoint B S hS X.1, (etaleSitePoint B S hS X.1 x X.2).fiber.obj U :=
    fun k => ⟨geometricPointMap (g' (i k.1)).hom k.2.1,
      ⟨k.2.2.1 ≫ (BigAffineFppf.inclusion B S hS).map (𝒰.f k.1),
        (congrFun (congrArg (fun η => η.app (Opposite.op k.2.1.val.siteObject)) (hα k.1))
          k.2.2.1).symm.trans (congrArg ((g' (i k.1)).hom.app _) k.2.2.2.1)⟩⟩
  refine hasTorAmplitude_derivedRestriction_of_derivedModuleFiber_family B S hS f E U _ _ ψ
    ?_ ?_
  · intro v
    have hmap : Presieve.map (BigAffineFppf.toScheme B S hS) 𝒰.presieve₀ =
        Presieve.ofArrows (fun j => (BigAffineFppf.toScheme B S hS).obj (𝒰.X j))
          (fun j => (BigAffineFppf.toScheme B S hS).map (𝒰.f j)) := by
      simp [PreZeroHypercover.presieve₀]
    change Presieve.map (BigAffineFppf.toScheme B S hS) 𝒰.presieve₀ ∈
        Scheme.qcPrecoverage _ ∧
      Presieve.map (BigAffineFppf.toScheme B S hS) 𝒰.presieve₀ ∈
        Scheme.precoverage @Flat _ at hfpqc
    rw [hmap] at hfpqc
    obtain ⟨j, w, hw⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 hfpqc.2).1 v
    obtain ⟨x, ξ, hξ, ⟨ζ, hζ⟩, hP⟩ := hgood j w
    refine ⟨⟨j, x, ξ, hξ, hP⟩, ζ, ?_⟩
    show (BigFppfOver.toScheme B S hS).map
      (ξ ≫ (BigAffineFppf.inclusion B S hS).map (𝒰.f j)) ζ = v
    rwa [Functor.map_comp, Scheme.Hom.comp_apply, hζ]
  · rintro ⟨j, x, ξ, hξ, hP⟩
    exact hasTorAmplitudeCanonical_mono_sum (Finset.mem_univ j) a b
      (hasTorAmplitudeCanonical_derivedModuleFiber_of_pullback_of_cartesian B S hS (g' (i j))
        (f' (i j)) f (g (i j)) (hpb (i j)) (hg.1 (i j)) E x (a j) (b j) hP)

include hg hpb in
/-- **The descent half of Stacks 0DL2 for locally finite Tor dimension.**  If every `L(g'_i)^*E`
locally has finite Tor dimension over `f_i⁻¹𝒪_{Y_i}`, then `E` locally has finite Tor dimension
over `f⁻¹𝒪_Y`: every étale chart of `X` is covered by charts with affine underlying scheme, on
which `exists_hasTorAmplitude_derivedRestriction_of_isAffine` applies. -/
theorem locallyHasFiniteTorDimension_derivedScalarRestriction_of_forall_pullback
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : ∀ i, LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS (f' i)).over U))
      ((derivedScalarRestriction B S hS (f' i)).obj
        ((smallEtaleDerivedModulePullback B S hS (g' i)).obj E))) :
    LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over U))
      ((derivedScalarRestriction B S hS f).obj E) := by
  intro U
  obtain ⟨J, Yj, aj, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS X.1 U
  refine ⟨Presieve.ofArrows Yj aj, hcov, ?_⟩
  rintro V _ ⟨j⟩
  exact exists_hasTorAmplitude_derivedRestriction_of_isAffine B S hS g hg f f' g' hpb E hE (Yj j)
    (haff j)

include hg hpb in
/-- **Stacks 0DL2**, locally finite Tor dimension. -/
@[stacks 0DL2 "locally finite tor dimension"]
theorem locallyHasFiniteTorDimension_derivedScalarRestriction_iff_forall_of_isFpqcCovering
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS f).over U))
      ((derivedScalarRestriction B S hS f).obj E) ↔
      ∀ i, LocallyHasFiniteTorDimension.{u + 1, u, u, u + 1}
      (fun U => Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS (f' i)).over U))
      ((derivedScalarRestriction B S hS (f' i)).obj
        ((smallEtaleDerivedModulePullback B S hS (g' i)).obj E)) :=
  ⟨fun h i => locallyHasFiniteTorDimension_derivedScalarRestriction_pullback_of_cartesian B S hS
      (g' i) (f' i) f (g i) (hpb i) (hg.1 i) E h,
    locallyHasFiniteTorDimension_derivedScalarRestriction_of_forall_pullback B S hS g hg f f' g'
      hpb E⟩

end Descent

end AlgebraicGeometry.Space

end
