module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCartesianPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeFpqcDescentLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.PresheafOrder

/-!
# Relative perfectness ascends along a finite-order thickening of the base (Stacks 0DL4)

Consider a cartesian square of algebraic spaces
```
X --i--> X'
|f       |f'
v        v
Y --j--> Y'
```
with `f'` flat and locally of finite presentation and `j` a finite-order thickening.  Stacks 0DL4
says that an object `E'` of `D(𝒪_{X'})` whose derived pullback `Li^*E'` is `Y`-perfect is
`Y'`-perfect.  Relative perfectness (Stacks 0DKN) is pseudo-coherence together with locally finite
Tor dimension over `f'⁻¹𝒪_{Y'}`.

The source proves pseudo-coherence by Stacks 0DL3 and reduces the Tor clause to schemes by Stacks
0DKQ and Stacks 0DJY.  Here the Tor clause is proved directly, at the geometric stalks, with no
use of Stacks 0DKQ; only pseudo-coherence is taken from Stacks 0DL3, which enters as the explicit
hypothesis `h0DL3`.

## Main results

* `AlgebraicGeometry.Space.hasTorAmplitudeCanonical_derivedModuleFiber_of_pull_of_isNilpotent`:
  the transfer of a Tor bound from the derived stalk of `Lφ^*E` to that of `E`.
* `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_of_pull_of_isNilpotent`: the Tor clause
  of relative perfectness ascends along a thickening of the base.
* `AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening`:
  Stacks 0DL4, granted Stacks 0DL3.
* `Space.isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening_subfunctor`:
  the same, granted Stacks 0DL3 with the thickening given as a finite-order thickening subspace
  (Stacks 05ZK, part (3)).
* `AlgebraicGeometry.Space.ComplexesSituation.isRelativelyPerfect_of_isFiniteOrderThickening`:
  the `h0DL4` binder of the consumers of the stack of complexes, granted Stacks 0DL3.

## Implementation notes

The Tor clause is checked on étale charts with affine underlying scheme.  Over such a chart `U'` of
`X'`, the base change `X ×_{X'} U'` is affine, hence quasi-compact, and carries one bound on the
derived stalks of `Li^*E'`
(`exists_forall_hasTorAmplitudeCanonical_derivedModuleFiber_of_compactSpace` of Stacks 0DL2); the
bound ascends to the derived stalks of `E'` at the image geometric points, which meet every point
of `U'`.  This is the "elementary topology" of Stacks 0DL2, and it replaces the reduction to
schemes of the source.

## References

* [Stacks Project, Tag 0DL4](https://stacks.math.columbia.edu/tag/0DL4)
* [Stacks Project, Tag 0DL3](https://stacks.math.columbia.edu/tag/0DL3)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 0DL2](https://stacks.math.columbia.edu/tag/0DL2)
* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open StacksDraft.TorAmplitude

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

-- The standard model is forced: `HasTorAmplitudeCanonical`, `Stacks.derivedModuleFiber` and the
-- stalkwise criteria of
-- `StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeTorAmplitudeFpqcDescentLocal`
-- are stated only for it, and a plain-priority pin loses to the global instances.
attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The Tor amplitude of the derived stalk, read over the base, is invariant under isomorphism. -/
private theorem hasTorAmplitudeCanonical_derivedModuleFiber_of_iso
    {A C : AlgebraicSpaces B S hS} (g : A ⟶ C) (x : GeometricPoint B S hS A.1)
    {E F : derivedModules B S hS A} (e : E ≅ F) (a b : ℤ)
    (h : HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS A.1 x A.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS g).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS A.1 x A.2)
        (inverseImageRingedSite B S hS g).O).obj ((derivedScalarRestriction B S hS g).obj E))
      a b) :
    HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS A.1 x A.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS g).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS A.1 x A.2)
        (inverseImageRingedSite B S hS g).O).obj ((derivedScalarRestriction B S hS g).obj F))
      a b :=
  AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
    ((Stacks.derivedModuleFiber (etaleSitePoint B S hS A.1 x A.2)
      (inverseImageRingedSite B S hS g).O).mapIso ((derivedScalarRestriction B S hS g).mapIso e))
    a b h

/-- **The transfer at a geometric point, for a K-flat complex.**  The case of
`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_derivedModuleFiber_of_pull_of_isNilpotent` in
which `E` is presented by a K-flat complex `K` with K-flat stalk at `φ(z̄)`: the derived pullback
of `K` is its degreewise pullback, whose stalk at `z̄` is the extension of scalars of the stalk of
`K` (Stacks 05V5). -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_of_pull_of_kFlat
    {Z W V U : AlgebraicSpaces B S hS}
    {φ : Z ⟶ W} {p : Z ⟶ V} {q : W ⟶ U} {h : V ⟶ U} (hpb : IsPullback φ p q h)
    (hφ : IsClosedImmersion B S hS φ.hom) (hq : IsFlat B S hS q.hom)
    (K : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ)
    (hKflat : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS W)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))
    (x : GeometricPoint B S hS Z.1)
    (hstalk : CochainComplex.KFlat.{u, u}
      (((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x) W.2)
        (smallEtaleRingedTopos B S hS W).O).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))
    (hsurj : Function.Surjective (stalkStructureMap B S hS h (geometricPointMap p.hom x)).hom)
    (hnil : IsNilpotent (RingHom.ker (stalkStructureMap B S hS h (geometricPointMap p.hom x)).hom))
    (a b : ℤ)
    (hE : HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS Z.1 x Z.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS p).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS Z.1 x Z.2)
        (inverseImageRingedSite B S hS p).O).obj ((derivedScalarRestriction B S hS p).obj
          (((smallEtaleDerivedPullbackData B S hS).pull φ).obj (DerivedCategory.Q.obj K)))) a b) :
    HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x) W.2).presheafFiber
        (A := CommRingCat.{u})).obj (inverseImageRingedSite B S hS q).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x) W.2)
        (inverseImageRingedSite B S hS q).O).obj
          ((derivedScalarRestriction B S hS q).obj (DerivedCategory.Q.obj K))) a b := by
  let K' : CochainComplex (Modules.{u, u} B S hS Z.1 Z.2) ℤ :=
    ((smallEtaleRingedToposHom B S hS φ).toModulesHom.pullbackModules.mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
  have h₁ := hasTorAmplitudeCanonical_derivedModuleFiber_of_iso p x
    (derivedPullbackObjIsoOfIsKFlat B S hS φ K hKflat) a b hE
  have h₂ := (hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_iff B S hS p x K'
    a b).1 h₁
  have hβ : Stacks.Sheaves.StalkPullback.stalkRingMap
      (smallEtaleRingedToposHom B S hS φ).toModulesHom
      (etaleSitePoint B S hS Z.1 x Z.2)
      (etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x) W.2)
      (smallEtaleInverseImageFiberIso B S hS φ x) = (stalkStructureMap B S hS φ x).hom :=
    (stalkRingMap_toModulesHom_eq B S hS φ x).trans
      (stalkStructureMap_hom_eq_smallEtaleStalkPullbackRingMap B S hS φ x).symm
  have e₂ := DerivedCategory.Q.mapIso ((CochainComplex.restrictScalars
    (stalkStructureMap B S hS p x).hom).mapIso (stalkComplexPullbackIso B S hS φ x K))
  rw [hβ] at e₂
  have h₃ := AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e₂ a b h₂
  have h₄ := hasTorAmplitudeCanonical_geometricStalk_of_baseChange_of_isNilpotent B S hS φ p q h
    hpb hq hφ x hsurj hnil _ hstalk a b h₃
  exact (hasTorAmplitudeCanonical_derivedModuleFiber_scalarRestriction_iff B S hS q
    (geometricPointMap φ.hom x) K a b).2 h₄

/-- **Relative Tor amplitude ascends along a base thickening, at a geometric point.**
Let `φ : Z ⟶ W`, `p : Z ⟶ V`, `q : W ⟶ U`, `h : V ⟶ U` be a cartesian square of algebraic spaces
with `q` flat and `φ` a closed immersion, and let `z̄` be a geometric point of `Z` at whose image
in `V` the homomorphism of stalk rings of `h` is surjective with nilpotent kernel.  If the derived
stalk at `z̄` of `Lφ^*E`, read in `D(p⁻¹𝒪_V)`, has Tor amplitude in `[a, b]`, then so has the
derived stalk at `φ(z̄)` of `E`, read in `D(q⁻¹𝒪_U)`.

`E` is represented by a K-flat complex `K` with K-flat stalks; the stalk of `Lφ^*E` at `z̄` is the
extension of scalars of the stalk of `K` at `φ(z̄)` (Stacks 05V5), and the bound is transferred
along the square of stalk rings by
`AlgebraicGeometry.Space.hasTorAmplitudeCanonical_geometricStalk_of_baseChange_of_isNilpotent`. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_of_pull_of_isNilpotent
    {Z W V U : AlgebraicSpaces B S hS}
    {φ : Z ⟶ W} {p : Z ⟶ V} {q : W ⟶ U} {h : V ⟶ U} (hpb : IsPullback φ p q h)
    (hφ : IsClosedImmersion B S hS φ.hom) (hq : IsFlat B S hS q.hom)
    (E : derivedModules B S hS W) (x : GeometricPoint B S hS Z.1)
    (hsurj : Function.Surjective (stalkStructureMap B S hS h (geometricPointMap p.hom x)).hom)
    (hnil : IsNilpotent (RingHom.ker (stalkStructureMap B S hS h (geometricPointMap p.hom x)).hom))
    (a b : ℤ)
    (hE : HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS Z.1 x Z.2).presheafFiber (A := CommRingCat.{u})).obj
        (inverseImageRingedSite B S hS p).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS Z.1 x Z.2)
        (inverseImageRingedSite B S hS p).O).obj ((derivedScalarRestriction B S hS p).obj
          (((smallEtaleDerivedPullbackData B S hS).pull φ).obj E))) a b) :
    HasTorAmplitudeCanonical
      (((etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x) W.2).presheafFiber
        (A := CommRingCat.{u})).obj (inverseImageRingedSite B S hS q).O.obj)
      ((Stacks.derivedModuleFiber (etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x) W.2)
        (inverseImageRingedSite B S hS q).O).obj ((derivedScalarRestriction B S hS q).obj E))
      a b := by
  -- a K-flat representative of `E` which is a sequential colimit of bounded above flat complexes
  let K₀ : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ :=
    DerivedCategory.Q.objPreimage E
  have := Stacks.SheafOfModules.KFlatResolution.hasColimitsOfShape_nat_ofSize
    (smallEtaleRingedTopos B S hS W).O
  obtain ⟨Dn, α, hLE, hflat, hqis, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_resolution_colimit_ofSize
      (smallEtaleRingedTopos B S hS W).O K₀
  have hDn : HasColimit Dn := inferInstance
  let K : CochainComplex (Modules.{u, u} B S hS W.1 W.2) ℤ := (Arrow.mk α).left
  let α' : K ⟶ K₀ := α
  have hQα : IsIso (DerivedCategory.Q.map α') := by
    rwa [DerivedCategory.isIso_Q_map_iff_quasiIso]
  let eK : DerivedCategory.Q.obj K ≅ E :=
    asIso (DerivedCategory.Q.map α') ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have := Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize
    (smallEtaleRingedTopos B S hS W).O
  have hKflat : Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.IsKFlat
      (Y := smallEtaleRingedTopos B S hS W)
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) :=
    ⟨Stacks.SheafOfModules.KFlatResolution.kFlat_colimit_of_isStrictlyLE_of_isFlat_ofSize
      _ Dn hLE hflat,
      Stacks.SheafOfModules.KFlatResolution.isFlat_colimit_X_ofSize _ Dn hflat⟩
  have hDn' : HasColimit (show ℕ ⥤ CochainComplex (SheafOfModules.{u}
      (Stacks.commRingSheafToRingSheaf.{u, u + 1, u}
        (smallEtaleRingedTopos B S hS W).O)) ℤ from Dn) := hDn
  have hstalk : CochainComplex.KFlat.{u, u}
      (((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x) W.2)
        (smallEtaleRingedTopos B S hS W).O).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
    Stacks.kFlat_mapHomologicalComplex_sheafModuleFiber_colimit
      (etaleSitePoint B S hS W.1 (geometricPointMap φ.hom x) W.2)
      (smallEtaleRingedTopos B S hS W).O _ hLE hflat
  have hE' := hasTorAmplitudeCanonical_derivedModuleFiber_of_iso p x
    (((smallEtaleDerivedPullbackData B S hS).pull φ).mapIso eK.symm) a b hE
  exact hasTorAmplitudeCanonical_derivedModuleFiber_of_iso q _ eK a b
    (hasTorAmplitudeCanonical_derivedModuleFiber_of_pull_of_kFlat hpb hφ hq K hKflat x hstalk
      hsurj hnil a b hE')

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **Relative Tor amplitude ascends along a thickening of the base, on an affine chart.**  In the
situation of `hasTorAmplitudeCanonical_derivedModuleFiber_of_pull_of_isNilpotent`, suppose
moreover that every base change of `φ` to a scheme is surjective and that the stalk maps of `h`
are surjective with nilpotent kernel at every geometric point.  If `Lφ^*E` locally has
finite Tor dimension over `p⁻¹𝒪_V`, then `E` restricted to an étale chart `U'` of `W` with affine
underlying scheme has finite Tor dimension over `q⁻¹𝒪_U`.

The base change `T = Z ×_W U'` is a closed subscheme of the affine scheme `U'`, so it is
quasi-compact and carries one bound on the derived stalks of `Lφ^*E` at the geometric points of
`Z` through `T`; the bound ascends to the derived stalks of `E` at their images in `W`, which lift
to `U'` and meet every point of `U'`, `T ⟶ U'` being surjective. -/
theorem exists_hasTorAmplitude_derivedRestriction_of_pull_of_isAffine
    {Z W V U : AlgebraicSpaces B S hS}
    {φ : Z ⟶ W} {p : Z ⟶ V} {q : W ⟶ U} {h : V ⟶ U} (hpb : IsPullback φ p q h)
    (hφ : IsClosedImmersion B S hS φ.hom)
    (hφs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ.hom)
    (hq : IsFlat B S hS q.hom)
    (hstalk : ∀ y : GeometricPoint B S hS V.1,
      Function.Surjective (stalkStructureMap B S hS h y).hom ∧
        IsNilpotent (RingHom.ker (stalkStructureMap B S hS h y).hom))
    (E : derivedModules B S hS W)
    (hE : LocallyHasFiniteTorDimension (canonicalSliceDerivedTensorProduct B S hS p)
      ((derivedScalarRestriction B S hS p).obj
        (((smallEtaleDerivedPullbackData B S hS).pull φ).obj E)))
    (U' : (inverseImageRingedSite B S hS q).C)
    (hU' : IsAffine ((BigFppfOver.toScheme B S hS).obj U'.obj.left)) :
    ∃ a b : ℤ, Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.{u + 1, u, u, u + 1}
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        ((inverseImageRingedSite B S hS q).over U'))
      ((RingedSite.derivedRestriction (inverseImageRingedSite B S hS q) U').obj
        ((derivedScalarRestriction B S hS q).obj E)) a b := by
  classical
  let hr := hφ.rep
  let T := hr.pullback U'.obj.hom
  let β := hr.fst U'.obj.hom
  let sn := hr.snd U'.obj.hom
  have : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map sn) :=
    hφ.property_snd U'.obj.hom
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T) :=
    (AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigFppfOver.toScheme B S hS).map sn)).1
  obtain ⟨a, b, hgood⟩ :=
    exists_forall_hasTorAmplitudeCanonical_derivedModuleFiber_of_compactSpace B S hS p _ hE T β
  have hsurjsn : Function.Surjective ((BigFppfOver.toScheme B S hS).map sn).base :=
    (hφs.property_snd U'.obj.hom).surj
  refine ⟨a, b, ?_⟩
  let ψ : (Σ x : GeometricPoint B S hS Z.1,
      {ξ : x.val.siteObject ⟶ T // β.app (Opposite.op x.val.siteObject) ξ = x.val.value ∧
        HasTorAmplitudeCanonical
          (((etaleSitePoint B S hS Z.1 x Z.2).presheafFiber (A := CommRingCat.{u})).obj
            (inverseImageRingedSite B S hS p).O.obj)
          ((Stacks.derivedModuleFiber (etaleSitePoint B S hS Z.1 x Z.2)
            (inverseImageRingedSite B S hS p).O).obj ((derivedScalarRestriction B S hS p).obj
              (((smallEtaleDerivedPullbackData B S hS).pull φ).obj E))) a b}) →
      Σ x : GeometricPoint B S hS W.1, (etaleSitePoint B S hS W.1 x W.2).fiber.obj U' :=
    fun k => ⟨geometricPointMap φ.hom k.1,
      ⟨k.2.1 ≫ sn,
        (congrFun (congrArg (fun η => η.app (Opposite.op k.1.val.siteObject))
          (hr.w U'.obj.hom)) k.2.1).symm.trans (congrArg (φ.hom.app _) k.2.2.1)⟩⟩
  refine hasTorAmplitude_derivedRestriction_of_derivedModuleFiber_family B S hS q E U' a b ψ ?_ ?_
  · intro v
    obtain ⟨t, ht⟩ := hsurjsn v
    obtain ⟨x, ξ, hξ, ⟨ζ, hζ⟩, hP⟩ := hgood t
    refine ⟨⟨x, ξ, hξ, hP⟩, ζ, ?_⟩
    show (BigFppfOver.toScheme B S hS).map (ξ ≫ sn) ζ = v
    rwa [Functor.map_comp, Scheme.Hom.comp_apply, hζ]
  · rintro ⟨x, ξ, hξ, hP⟩
    exact hasTorAmplitudeCanonical_derivedModuleFiber_of_pull_of_isNilpotent hpb hφ hq E x
      (hstalk _).1 (hstalk _).2 a b hP

open Stacks.SheafOfModules.DerivedTensorProduct in
/-- **The Tor clause of relative perfectness ascends along a thickening of the base.**  Let
`φ : Z ⟶ W`, `p : Z ⟶ V`, `q : W ⟶ U`, `h : V ⟶ U` be a cartesian square of algebraic spaces
with `q` flat, `φ` a closed immersion all of whose base changes to schemes are surjective, and `h`
inducing at every geometric point of `V` a surjection of stalk rings with nilpotent kernel.  If
`Lφ^*E`, read over `p⁻¹𝒪_V`, locally has finite Tor dimension, then so has `E`, read over
`q⁻¹𝒪_U`.  This is the Tor half of Stacks 0DL4: every étale chart of `W` is covered by charts with
affine underlying scheme, on which
`AlgebraicGeometry.Space.exists_hasTorAmplitude_derivedRestriction_of_pull_of_isAffine` applies. -/
theorem locallyHasFiniteTorDimension_of_pull_of_isNilpotent
    {Z W V U : AlgebraicSpaces B S hS}
    {φ : Z ⟶ W} {p : Z ⟶ V} {q : W ⟶ U} {h : V ⟶ U} (hpb : IsPullback φ p q h)
    (hφ : IsClosedImmersion B S hS φ.hom)
    (hφs : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ.hom)
    (hq : IsFlat B S hS q.hom)
    (hstalk : ∀ y : GeometricPoint B S hS V.1,
      Function.Surjective (stalkStructureMap B S hS h y).hom ∧
        IsNilpotent (RingHom.ker (stalkStructureMap B S hS h y).hom))
    (E : derivedModules B S hS W)
    (hE : LocallyHasFiniteTorDimension (canonicalSliceDerivedTensorProduct B S hS p)
      ((derivedScalarRestriction B S hS p).obj
        (((smallEtaleDerivedPullbackData B S hS).pull φ).obj E))) :
    LocallyHasFiniteTorDimension (canonicalSliceDerivedTensorProduct B S hS q)
      ((derivedScalarRestriction B S hS q).obj E) := by
  intro U'
  obtain ⟨J, Yj, aj, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS W.1 U'
  refine ⟨Presieve.ofArrows Yj aj, hcov, ?_⟩
  rintro V' _ ⟨j⟩
  exact exists_hasTorAmplitude_derivedRestriction_of_pull_of_isAffine hpb hφ hφs hq hstalk E hE
    (Yj j) (haff j)

/-- **Stacks 0DL4, granted Stacks 0DL3.**  Consider a cartesian square
```
X --i--> X'
|f       |f'
v        v
Y --j--> Y'
```
of algebraic spaces over `S` with `f'` flat and locally of finite presentation and `j` a
finite-order thickening, every base change of `j` to a scheme being an `n`th-order thickening of
schemes.  Let `E' ∈ D(𝒪_{X'})`.  If `E = Li^*E'` is `Y`-perfect, then `E'` is `Y'`-perfect.

The hypothesis `h0DL3` is **Stacks 0DL3** (not yet proved here): pseudo-coherence
ascends along a finite-order thickening of algebraic spaces.  It gives the pseudo-coherence clause,
`i` being a finite-order thickening as a base change of `j`.  The Tor clause is proved here,
without Stacks 0DKQ: at a geometric point the square of stalk rings is a pushout along a
surjection with nilpotent kernel, so the nilpotent dévissage of Stacks 0H75 lifts the Tor bound
(`AlgebraicGeometry.Space.locallyHasFiniteTorDimension_of_pull_of_isNilpotent`).  The flatness
and finite presentation of `f` are those of `f'`, by base change. -/
theorem isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening
    (h0DL3 : ∀ {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X') (n : ℕ),
      (MorphismProperty.inverseImage (thickOrder.{u} n)
        (BigFppfOver.toScheme B S hS)).presheaf i.hom →
      ∀ K' : derivedModules B S hS X',
        (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
          (((smallEtaleDerivedPullbackData B S hS).pull i).obj K') →
        (smallEtaleRingedSite B S hS X'.1 X'.2).IsPseudoCoherent K')
    {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    (hpb : IsPullback i f f' j) {n : ℕ}
    (hj : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf j.hom)
    (hflat : IsFlat B S hS f'.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f'.hom)
    (E' : derivedModules B S hS X')
    (hE : IsPerfectRelativeToCanonical B S hS f
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb hflat)
      ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hpb
        hlfp)
      (((smallEtaleDerivedPullbackData B S hS).pull i).obj E')) :
    IsPerfectRelativeToCanonical B S hS f' hflat hlfp E' := by
  have hi : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf i.hom :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (AlgebraicSpaces.isPullback_hom B S hS hpb.flip) hj
  exact ⟨h0DL3 i n hi E' hE.1,
    locallyHasFiniteTorDimension_of_pull_of_isNilpotent hpb
      (isClosedImmersion_of_presheaf_thickOrder B S hS hi)
      (presheaf_surjective_of_presheaf_thickOrder B S hS hi) hflat
      (fun y => surjective_and_isNilpotent_ker_stalkStructureMap B S hS j hj y) E' hE.2⟩

/-- **Stacks 0DL4, granted Stacks 0DL3 in the subspace form of Stacks 05ZK.**  The statement of
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening`, with
the hypothesis `h0DL3` read for a thickening presented as a finite-order thickening subspace
`G ⊆ X'` (Stacks 05ZK, part (3)) together with an isomorphism `X ≅ G` through which `i : X ⟶ X'`
is the inclusion of `G`.

The hypothesis `h0DL3` is **Stacks 0DL3** (not yet proved here), in the thickening
shape of its statement.  A morphism all of whose base changes to schemes are
`n`th-order thickenings has a finite-order thickening as its range, and is identified with its
inclusion
(`AlgebraicGeometry.Space.presheaf_thickOrder_iff_isThickeningHom_and_isNthOrderThickening`). -/
theorem isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening_subfunctor
    (h0DL3 : ∀ (X' : AlgebraicSpaces B S hS) (G : Subfunctor X'.1),
      IsFiniteOrderThickening B S hS X' G →
      ∀ (X : AlgebraicSpaces B S hS) (e : X.1 ≅ G.toFunctor) (i : X ⟶ X'), e.hom ≫ G.ι = i.hom →
      ∀ K' : derivedModules B S hS X',
        (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
          (((smallEtaleDerivedPullbackData B S hS).pull i).obj K') →
        (smallEtaleRingedSite B S hS X'.1 X'.2).IsPseudoCoherent K')
    {X X' Y Y' : AlgebraicSpaces B S hS} {i : X ⟶ X'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {j : Y ⟶ Y'}
    (hpb : IsPullback i f f' j) {n : ℕ}
    (hj : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf j.hom)
    (hflat : IsFlat B S hS f'.hom) (hlfp : IsLocallyOfFinitePresentation B S hS f'.hom)
    (E' : derivedModules B S hS X')
    (hE : IsPerfectRelativeToCanonical B S hS f
      ((isFlat_isStableUnderBaseChange B S hS).of_isPullback hpb hflat)
      ((isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hpb
        hlfp)
      (((smallEtaleDerivedPullbackData B S hS).pull i).obj E')) :
    IsPerfectRelativeToCanonical B S hS f' hflat hlfp E' := by
  refine isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening
    (fun {Z Z'} k m hk K' hK => ?_) hpb hj hflat hlfp E' hE
  obtain ⟨hth, hm⟩ :=
    (presheaf_thickOrder_iff_isThickeningHom_and_isNthOrderThickening B S hS k m).1 hk
  have := hth.1
  exact h0DL3 Z' (Subfunctor.range k.hom) ⟨m, hm⟩ Z (asIso (Subfunctor.toRange k.hom)) k
    (Subfunctor.toRange_ι k.hom) K' hK

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

/-- **Stacks 0DL4 in the situation of Stacks 0DLE, granted Stacks 0DL3.**  For a finite-order
thickening `T ⟶ T'` of test schemes over `Y`, an object `E'` of `D(𝒪_{X_{T'}})` whose derived
restriction to `X_T` is isomorphic to a `T`-perfect object is `T'`-perfect.

This is the `h0DL4` binder of
`AlgebraicGeometry.Space.ComplexesSituation.isAlgebraicStack_complexes_of_held'` and of the files
`StacksFrontier/AlgebraicGeometry/Quot/ComplexesStackPushout*.lean`, discharged from
`h0DL3` — **Stacks 0DL3** (not yet proved here) — by
`AlgebraicGeometry.Space.isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening` at the
cartesian square defining `X_T`.  `T`-perfectness is invariant under isomorphism (Stacks 0DKR). -/
theorem isRelativelyPerfect_of_isFiniteOrderThickening
    (h0DL3 : ∀ {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X') (n : ℕ),
      (MorphismProperty.inverseImage (thickOrder.{u} n)
        (BigFppfOver.toScheme B S hS)).presheaf i.hom →
      ∀ K' : derivedModules B S hS X',
        (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent
          (((smallEtaleDerivedPullbackData B S hS).pull i).obj K') →
        (smallEtaleRingedSite B S hS X'.1 X'.2).IsPseudoCoherent K')
    {T T' : SchemesOver D.Y} (h : T ⟶ T')
    (hfin : Stacks.Thickenings.IsFiniteOrderThickening ((BigFppfOver.toScheme B S hS).map h.left))
    (E' : derivedModules B S hS (D.space T')) (E : derivedModules B S hS (D.space T))
    (e : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)).obj E' ≅ E)
    (hE : D.IsRelativelyPerfect T E) : D.IsRelativelyPerfect T' E' := by
  obtain ⟨hci, n, hn⟩ := hfin
  have : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun sq hq => MorphismProperty.of_isPullback (P := thickOrder.{u} n)
      (sq.map (BigFppfOver.toScheme B S hS)) hq⟩
  have hj : (MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS)).presheaf ((schemeSpaceFunctor B S hS).map h.left).hom :=
    MorphismProperty.relative_map (show MorphismProperty.inverseImage (thickOrder.{u} n)
      (BigFppfOver.toScheme B S hS) h.left from ⟨hci, hn⟩)
  exact isPerfectRelativeToCanonical_of_pull_of_isFiniteOrderThickening h0DL3
    (isPullback_baseChangeMap D.f h) hj (D.projection_isFlat T')
    (D.projection_isLocallyOfFinitePresentation T') E'
    ((isClosedUnderIsomorphisms_isPerfectRelativeToCanonical B S hS (D.projection T)
      (D.projection_isFlat T) (D.projection_isLocallyOfFinitePresentation T)).of_iso e.symm hE)

end ComplexesSituation

end AlgebraicGeometry.Space

end
