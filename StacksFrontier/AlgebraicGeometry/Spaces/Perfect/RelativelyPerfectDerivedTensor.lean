module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfect
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectOfPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RestrictionToASliceGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.RestrictionOfEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.StrictlyPerfectTensorRestrictScalars
public import StacksCore.Tactic.StacksAttribute

/-!
# Tensoring a relatively perfect object with a perfect object

Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is flat
and locally of finite presentation. A perfect object of `D(𝒪_X)` is `Y`-perfect, and if
`K, M ∈ D(𝒪_X)` with `K` perfect and `M` `Y`-perfect (Stacks 0DKN), then `K ⊗^𝐋_{𝒪_X} M` is
`Y`-perfect. This is Stacks 0DKS.

The first assertion is `AlgebraicGeometry.Space.isRelativelyPerfect_of_isPerfect`; this file
proves the second. Its pseudo-coherence clause is Stacks 09J9 (2) on the small étale site, and its
Tor clause is the dévissage of Stacks 08FL over the objects of the small étale site on which `K`
is represented by a strictly perfect complex.

## Main results

* `AlgebraicGeometry.RingedSite.exists_strictlyPerfect_model_restrictAlong_general`: a strictly
  perfect model of the restriction of a complex to `V` restricts along an arrow `W ⟶ V`.
* `AlgebraicGeometry.Space.locallyHasFiniteTorDimension_derivedScalarRestriction_tensor`: the
  Tor clause of `K ⊗^𝐋 M`.
* `AlgebraicGeometry.Space.isRelativelyPerfect_derivedTensor`: the second assertion of
  Stacks 0DKS.
* `AlgebraicGeometry.Space.isRelativelyPerfect_of_isPerfect_and_derivedTensor`: both
  assertions, which is Stacks 0DKS.

## Implementation notes

The source reduces to schemes by Stacks 0DKQ and applies Stacks 0DI4; the argument here stays on
the small étale site. The derived tensor product `K ⊗^𝐋_{𝒪_X} M` is that of an arbitrary derived
tensor product datum `TX` of Stacks 06YU on the small étale site, the canonical one
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` included. The derived categories of the
slices of the small étale site are instance arguments at the hom universe of `D(𝒪_X)`.

## References

* [Stacks Project, Tag 0DKS](https://stacks.math.columbia.edu/tag/0DKS)
* [Stacks Project, Tag 0DI4](https://stacks.math.columbia.edu/tag/0DI4)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 09J9](https://stacks.math.columbia.edu/tag/09J9)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d e

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

-- This instance reaches sheafification of abelian sheaves on a slice of the small étale site
-- through an assignment of universes that the kernel rejects.
attribute [-instance] Stacks.ConstantSheaf.hasWeakSheafify_addCommGrp_of_univLE

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] overMapLimits overMapColimits

/-- **A strictly perfect model restricts along an arrow of the site.** If the restriction of a
complex `E` to `V` receives a quasi-isomorphism from a strictly perfect complex `P`, then for
every arrow `g : W ⟶ V` the restriction of `E` to `W` receives one from the restriction of `P`
along `g`, which is strictly perfect. -/
theorem exists_strictlyPerfect_model_restrictAlong_general
    {E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {V W : X.C} (g : W ⟶ V)
    (h : ∃ P : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
        ∃ q : P ⟶ X.restrictComplex E V, QuasiIso q) :
    ∃ P : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
        ∃ q : P ⟶ X.restrictComplex E W, QuasiIso q := by
  obtain ⟨P, hP, q, hq⟩ := h
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  have : (SheafOfModules.overMap.{w} R g).PreservesHomology := Functor.preservesHomologyOfExact _
  let HC := (SheafOfModules.overMap.{w} R g).mapHomologicalComplex (ComplexShape.up ℤ)
  let c := Stacks.SheafOfModules.restrictComplexAlongOverIsoGeneral R g E
  have : QuasiIso (HC.map q) := HomologicalComplex.quasiIso_map_of_preservesHomology q _
  have : QuasiIso c.hom := quasiIso_of_isIso c.hom
  exact ⟨HC.obj P, Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general R g hP,
    HC.map q ≫ c.hom, inferInstance⟩

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules.DerivedTensorProduct

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    [HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
    [HasDerivedCategory.{e} (RingedSite.Modules.{u + 1, u, u} (inverseImageRingedSite B S hS f))]

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable
    [∀ U : (inverseImageRingedSite B S hS f).C,
      HasDerivedCategory.{e}
        (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U))]
    [∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      HasDerivedCategory.{d}
        (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U))]

attribute [local instance] essentiallySmall_inverseImageRingedSite

/-- The derived category of the modules on a slice of `(X_étale, f⁻¹𝒪_Y)`, at the spelling in
which restriction to the slice produces them. -/
local instance inverseImageSliceHasDerivedCategory (W : (inverseImageRingedSite B S hS f).C) :
    HasDerivedCategory.{e} (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        (inverseImageRingedSite B S hS f).O).over W)) :=
  inferInstanceAs (HasDerivedCategory.{e}
    (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over W)))

/-- The derived category of the modules on a slice of `X_étale`, at the spelling in which
restriction to the slice produces them. -/
local instance smallEtaleSliceHasDerivedCategory (W : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    HasDerivedCategory.{d} (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O).over W)) :=
  inferInstanceAs (HasDerivedCategory.{d}
    (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over W)))

/-- The map `f⁻¹𝒪_Y|_W ⟶ 𝒪_X|_W` of structure sheaves on the slice of the small étale site of `X`
over `W`: the restriction of `AlgebraicGeometry.Space.inverseImageStructureMap`. -/
abbrev inverseImageStructureMapOver (W : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O).over W ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over W :=
  ((smallEtaleRingedSite B S hS X.1 X.2).J.overPullback RingCat.{u} W).map
    (inverseImageStructureMap B S hS f)

/-- **Reading over `f⁻¹𝒪_Y` commutes with restriction to a slice.** For an object `E` of
`D(𝒪_X)` and an object `W` of the small étale site of `X`, the restriction to `W` of `E` read
over `f⁻¹𝒪_Y` is the restriction of `E` to `W`, read over `f⁻¹𝒪_Y|_W`. -/
def derivedRestrictionScalarRestrictionIso (W : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :
    (SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O)
            W).mapDerivedCategory.obj ((derivedScalarRestriction B S hS f).obj E) ≅
      (SheafOfModules.restrictScalars.{u}
          (inverseImageStructureMapOver B S hS f W)).mapDerivedCategory.obj
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
            W).mapDerivedCategory.obj E) :=
  (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O)
        W).mapDerivedCategory.mapIso ((derivedScalarRestriction B S hS f).mapIso
          (DerivedCategory.Q.objObjPreimageIso E).symm) ≪≫
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O)
        W).mapDerivedCategory.mapIso ((derivedScalarRestrictionFactors B S hS f).app
          (DerivedCategory.Q.objPreimage E)) ≪≫
    (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (inverseImageRingedSite B S hS f).O)
        W).mapDerivedCategoryFactors.app
      (((scalarRestriction B S hS f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (DerivedCategory.Q.objPreimage E)) ≪≫
    ((SheafOfModules.restrictScalars.{u}
      (inverseImageStructureMapOver B S hS f W)).mapDerivedCategoryFactors.app
        (((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
            W).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (DerivedCategory.Q.objPreimage E))).symm ≪≫
    (SheafOfModules.restrictScalars.{u}
      (inverseImageStructureMapOver B S hS f W)).mapDerivedCategory.mapIso
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
            W).mapDerivedCategoryFactors.app (DerivedCategory.Q.objPreimage E)).symm ≪≫
    (SheafOfModules.restrictScalars.{u}
      (inverseImageStructureMapOver B S hS f W)).mapDerivedCategory.mapIso
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
            W).mapDerivedCategory.mapIso (DerivedCategory.Q.objObjPreimageIso E))

/-- **The Tor clause of `K ⊗^𝐋 M` over one object carrying the local data.** Let `W` be an object
of the small étale site of `X` over which the restriction of a complex `Kc` representing `K`
receives a quasi-isomorphism from a strictly perfect complex `P`, and over which `M`, read over
`f⁻¹𝒪_Y`, has Tor amplitude in `[c, e']`. Then `K ⊗^𝐋 M`, read over `f⁻¹𝒪_Y`, has finite Tor
dimension over `W`: its Tor amplitude lies in `[c + p, e' + q]` when the nonzero terms of `P`
lie in degrees `[p, q]` (Stacks 08FL). -/
theorem hasFiniteTorDimension_derivedRestriction_tensor_of_model
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (TX : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, d}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (Kc : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (eK : DerivedCategory.Q.obj Kc ≅ K)
    (W : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (P : CochainComplex (SheafOfModules.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over W)) ℤ)
    (hP : IsStrictlyPerfect
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over W) P)
    (α : P ⟶ (smallEtaleRingedSite B S hS X.1 X.2).restrictComplex Kc W) (hα : QuasiIso α)
    (c e' : ℤ)
    (hM : HasTorAmplitude.{u + 1, u, u, e} (T W)
      ((RingedSite.derivedRestriction.{u + 1, u, u, e} (inverseImageRingedSite B S hS f) W).obj
        ((derivedScalarRestriction B S hS f).obj M)) c e') :
    HasFiniteTorDimension.{u + 1, u, u, e} (T W)
      ((RingedSite.derivedRestriction.{u + 1, u, u, e} (inverseImageRingedSite B S hS f) W).obj
        ((derivedScalarRestriction B S hS f).obj ((TX.tensor.obj K).obj M))) := by
  obtain ⟨q, hq⟩ := hP.bounded.bddAbove
  obtain ⟨p, hp⟩ := hP.bounded.bddBelow
  obtain ⟨eT⟩ := nonempty_derivedTensor_restriction_iso_general
    (smallEtaleRingedSite B S hS X.1 X.2) TX W
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      ((smallEtaleRingedSite B S hS X.1 X.2).over W)) K M
  have hN : HasTorAmplitude.{u + 1, u, u, e} (T W)
      ((SheafOfModules.restrictScalars.{u}
        (inverseImageStructureMapOver B S hS f W)).mapDerivedCategory.obj
          ((SheafOfModules.overFunctor.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
              W).mapDerivedCategory.obj M)) c e' :=
    hM.of_iso (derivedRestrictionScalarRestrictionIso B S hS f W M)
  have : IsIso (DerivedCategory.Q.map α) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := α)).2 hα
  have eKW : DerivedCategory.Q.obj P ≅ (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        W).mapDerivedCategory.obj K :=
    asIso (DerivedCategory.Q.map α) ≪≫ ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        W).mapDerivedCategoryFactors.app Kc).symm ≪≫
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
          W).mapDerivedCategory.mapIso eK
  have h := hasTorAmplitude_restrictScalars_tensor_of_isStrictlyPerfect
    (O₁ := ((inverseImageRingedSite B S hS f).over W).O)
    (O₂ := ((smallEtaleRingedSite B S hS X.1 X.2).over W).O)
    (inverseImageStructureMapOver B S hS f W) (T W)
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct
      ((smallEtaleRingedSite B S hS X.1 X.2).over W)) _ c e' hN P hP p q
    (fun i hi => ⟨hp hi, hq hi⟩)
  exact ⟨c + p, e' + q, h.of_iso ((SheafOfModules.restrictScalars.{u}
    (inverseImageStructureMapOver B S hS f W)).mapDerivedCategory.mapIso
      (((Stacks.SheafOfModules.canonicalDerivedTensorProduct
        ((smallEtaleRingedSite B S hS X.1 X.2).over W)).tensor.mapIso eKW).app _ ≪≫ eT.symm) ≪≫
      (derivedRestrictionScalarRestrictionIso B S hS f W _).symm)⟩

/-- **The Tor clause of the second assertion of Stacks 0DKS.** If `K` is perfect and `M`, read
over `f⁻¹𝒪_Y`, locally has finite Tor dimension, then so does `K ⊗^𝐋_{𝒪_X} M`, for every
derived tensor product `TX` on the small étale site of `X` and every family `T` of derived
tensor products on the slices of `(X_étale, f⁻¹𝒪_Y)`. -/
theorem locallyHasFiniteTorDimension_derivedScalarRestriction_tensor
    (T : ∀ U : (inverseImageRingedSite B S hS f).C,
      Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, e}
        ((inverseImageRingedSite B S hS f).over U))
    (TX : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, d}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K)
    (hM : LocallyHasFiniteTorDimension.{u + 1, u, u, e} T
      ((derivedScalarRestriction B S hS f).obj M)) :
    LocallyHasFiniteTorDimension.{u + 1, u, u, e} T
      ((derivedScalarRestriction B S hS f).obj ((TX.tensor.obj K).obj M)) := by
  have hres : FiniteTorDimensionRestricts.{u + 1, u, u, e} T :=
    OfEssentiallySmall.finiteTorDimensionRestricts (inverseImageRingedSite B S hS f) T
  obtain ⟨Kc, hKc, ⟨eK⟩⟩ := hK
  intro U
  obtain ⟨S₁, hS₁, hd₁⟩ := hKc U
  obtain ⟨S₂, hS₂, hd₂⟩ := hM U
  refine ⟨(Sieve.generate S₁ ⊓ Sieve.generate S₂).arrows, by
    simpa using (smallEtaleRingedSite B S hS X.1 X.2).J.intersection_covering hS₁ hS₂,
    fun {W} h hh => ?_⟩
  obtain ⟨⟨Y₁, p₁, q₁, hq₁, -⟩, ⟨Y₂, p₂, q₂, hq₂, -⟩⟩ := hh
  obtain ⟨c, e', hce⟩ := hres p₂ _ (hd₂ q₂ hq₂)
  obtain ⟨P, hP, α, hα⟩ := RingedSite.exists_strictlyPerfect_model_restrictAlong_general
    (smallEtaleRingedSite B S hS X.1 X.2) p₁ (hd₁ q₁ hq₁)
  exact hasFiniteTorDimension_derivedRestriction_tensor_of_model B S hS f T TX K M Kc eK W P hP
    α hα c e' hce

/-- **Stacks 0DKS, the second assertion.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over
`S` which is flat and locally of finite presentation, and let `K, M ∈ D(𝒪_X)`. If `K` is perfect
and `M` is `Y`-perfect, then `K ⊗^𝐋_{𝒪_X} M` is `Y`-perfect, for every derived tensor product
`TX` of Stacks 06YU on the small étale site of `X`. -/
theorem isRelativelyPerfect_derivedTensor
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (TX : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, d}
      (smallEtaleRingedSite B S hS X.1 X.2))
    (K M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hK : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K)
    (hM : IsRelativelyPerfect B S hS f hflat hlfp M) :
    IsRelativelyPerfect B S hS f hflat hlfp ((TX.tensor.obj K).obj M) :=
  ⟨isPseudoCoherent_tensor_general (smallEtaleRingedSite B S hS X.1 X.2) TX
      (fun W => Stacks.SheafOfModules.canonicalDerivedTensorProduct
        ((smallEtaleRingedSite B S hS X.1 X.2).over W)) K M
      (RingedSite.isPseudoCoherent_of_isPerfect_general _ hK) hM.1,
    locallyHasFiniteTorDimension_derivedScalarRestriction_tensor B S hS f _ TX K M hK hM.2⟩

/-- **Stacks 0DKS.** Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is flat and locally of finite presentation.

1. A perfect object of `D(𝒪_X)` is `Y`-perfect.
2. If `K, M ∈ D(𝒪_X)`, then `K ⊗^𝐋_{𝒪_X} M` is `Y`-perfect if `K` is perfect and `M` is
   `Y`-perfect.

`Y`-perfectness is Stacks 0DKN, `AlgebraicGeometry.Space.IsRelativelyPerfect`. The derived tensor
product is any derived tensor product datum `TX` of Stacks 06YU on the small étale site of `X`,
for instance the canonical one. The first assertion is
`AlgebraicGeometry.Space.isRelativelyPerfect_of_isPerfect`, the second
`AlgebraicGeometry.Space.isRelativelyPerfect_derivedTensor`. -/
@[stacks 0DKS]
theorem isRelativelyPerfect_of_isPerfect_and_derivedTensor
    (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom)
    (TX : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, d}
      (smallEtaleRingedSite B S hS X.1 X.2)) :
    (∀ E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
        (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E →
          IsRelativelyPerfect B S hS f hflat hlfp E) ∧
      ∀ K M : DerivedCategory (Modules.{u, u} B S hS X.1 X.2),
        (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K →
          IsRelativelyPerfect B S hS f hflat hlfp M →
            IsRelativelyPerfect B S hS f hflat hlfp ((TX.tensor.obj K).obj M) :=
  ⟨fun E hE => isRelativelyPerfect_of_isPerfect B S hS f hflat hlfp E hE,
    fun K M hK hM => isRelativelyPerfect_derivedTensor B S hS f hflat hlfp TX K M hK hM⟩

end AlgebraicGeometry.Space

end
