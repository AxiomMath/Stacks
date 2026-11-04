module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackStalkReflection
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGeometricFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.ComplexesWithSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.CompositeChartData

/-!
# Geometric points and fibres for the stalkwise proof of Stacks 0AF0

The source checks the invertibility of the comparison maps of formal glueing "on stalks at
geometric points".  This file collects the three general facts that check rests on.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_fiber`: a map of `𝒪_X`-modules is invertible as soon as
  it is invertible on the fibre at every geometric point, the fibre being
  `Stacks.sheafModuleFiberOfCommRing`, the one Stacks 05V5 is stated for.
* `AlgebraicGeometry.Space.faithfullyFlat_smallEtaleStalkPullbackRingMap_of_isFlatAt` and
  `AlgebraicGeometry.Space.isIso_fiber_of_isIso_fiber_modulePullback`: along a morphism flat at
  the image of a geometric point the homomorphism of stalk rings is faithfully flat, so a map
  of modules whose pullback is invertible on the fibre at that point is invertible on the fibre
  at the image point.  This is the pointwise refinement of
  `AlgebraicGeometry.Space.mono_moduleStalk_map_modulePullback_iff_of_isFlat`, which asks for
  flatness everywhere.
* `AlgebraicGeometry.Space.exists_geometricPoint_openComplement_or_closed`: a geometric point of
  an algebraic space lifts either to the open complement of a closed subspace or to the closed
  subspace itself.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 03MK](https://stacks.math.columbia.edu/tag/03MK)
* [Stacks Project, Tag 05VN](https://stacks.math.columbia.edu/tag/05VN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The fibre at a geometric point of an `𝒪_X`-module, as a module over the stalk of the
structure sheaf: the functor Stacks 05V5 is stated for. -/
abbrev moduleFiber (X : AlgebraicSpaces B S hS) (x : GeometricPoint B S hS X.1) :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      ModuleCat.{u} (((etaleSitePoint B S hS X.1 x X.2).presheafFiber
        (A := CommRingCat.{u})).obj (smallEtaleRingedTopos B S hS X).O.obj) :=
  Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O

/-- **Fibres at geometric points detect isomorphisms of `𝒪_X`-modules.** -/
theorem isIso_of_isIso_fiber (X : AlgebraicSpaces B S hS) {M N : Modules.{u, u} B S hS X.1 X.2}
    (φ : M ⟶ N) (h : ∀ x, IsIso ((moduleFiber B S hS X x).map φ)) : IsIso φ :=
  isIso_of_isIso_geometricModuleStalk B S hS X.1 X.2 (structureRingSheafOfSite B S hS X.1 X.2) φ
    fun x => isIso_sheafModuleFiber_map_of_isIso_moduleStalkFunctor_map B S hS x φ (h x)

variable {B S hS} {X X' : AlgebraicSpaces B S hS}

/-- **Stacks 03MK at a point, for the stalk rings of the small étale ringed topoi.**  The
homomorphism `(𝒪_X)_{φ ∘ x̄} ⟶ (𝒪_{X'})_{x̄}` of structure-sheaf stalks along which Stacks 05V5
extends scalars is faithfully flat as soon as `φ` is flat at the image of `x̄`. -/
theorem faithfullyFlat_smallEtaleStalkPullbackRingMap_of_isFlatAt (φ : X' ⟶ X)
    (x : GeometricPoint B S hS X'.1) (hφ : IsFlatAt B S hS φ.hom x.image) :
    (smallEtaleStalkPullbackRingMap B S hS φ x).FaithfullyFlat := by
  have hcomp : ((pointStalkRingEquiv B S hS X' x).toRingHom.comp
      (smallEtaleStalkPullbackRingMap B S hS φ x)).FaithfullyFlat := by
    rw [pointStalkRingEquiv_comp_smallEtaleStalkPullbackRingMap B S hS φ x]
    exact RingHom.FaithfullyFlat.comp
      (RingHom.FaithfullyFlat.of_bijective
        (pointStalkRingEquiv B S hS X (geometricPointMap φ.hom x)).bijective)
      (faithfullyFlat_etaleLocalRingMap_of_isFlatAt B S hS X'.2 X.2 φ.hom x hφ)
  have heq : (pointStalkRingEquiv B S hS X' x).symm.toRingHom.comp
        ((pointStalkRingEquiv B S hS X' x).toRingHom.comp
          (smallEtaleStalkPullbackRingMap B S hS φ x)) =
      smallEtaleStalkPullbackRingMap B S hS φ x :=
    RingHom.ext fun z => (pointStalkRingEquiv B S hS X' x).symm_apply_apply _
  rw [← heq]
  exact RingHom.FaithfullyFlat.comp hcomp
    (RingHom.FaithfullyFlat.of_bijective (pointStalkRingEquiv B S hS X' x).symm.bijective)

/-- **A map of modules whose pullback is invertible on the fibre at a point of flatness is
invertible on the fibre at the image point.**  By Stacks 05V5 the first fibre map is the base
change of the second along the homomorphism of stalk rings, which is faithfully flat. -/
theorem isIso_fiber_of_isIso_fiber_modulePullback (φ : X' ⟶ X) (x : GeometricPoint B S hS X'.1)
    (hφ : IsFlatAt B S hS φ.hom x.image) {M N : Modules.{u, u} B S hS X.1 X.2} (v : M ⟶ N)
    (h : IsIso ((moduleFiber B S hS X' x).map ((modulePullback B S hS φ).map v))) :
    IsIso ((moduleFiber B S hS X (geometricPointMap φ.hom x)).map v) := by
  have hff := faithfullyFlat_smallEtaleStalkPullbackRingMap_of_isFlatAt φ x hφ
  have e := modulePullbackFiberIso B S hS φ x
  have hm : Mono ((moduleFiber B S hS X (geometricPointMap φ.hom x)).map v) :=
    (ModuleCat.mono_extendScalars_map_iff_of_faithfullyFlat hff _).1
      ((mono_iff_mono_of_comm_sq (e.app M) (e.app N) (e.hom.naturality v)).1
        (@IsIso.mono_of_iso _ _ _ _ _ h))
  have he : Epi ((moduleFiber B S hS X (geometricPointMap φ.hom x)).map v) :=
    (ModuleCat.epi_extendScalars_map_iff_of_faithfullyFlat hff _).1
      ((epi_iff_epi_of_comm_sq (e.app M) (e.app N) (e.hom.naturality v)).1
        (@IsIso.epi_of_iso _ _ _ _ _ h))
  exact isIso_of_mono_of_epi _

/-- An étale morphism is flat at every point. -/
theorem isFlatAt_of_isEtale (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (x : points B S hS X'.1) : IsFlatAt B S hS φ.hom x :=
  isFlatAt_of_isFlat B S hS φ.hom (isFlat_of_isEtale B S hS hφ) x

variable (B S hS) in
/-- **A geometric point lifts to the open complement of a closed subspace, or to the closed
subspace.** -/
theorem exists_geometricPoint_openComplement_or_closed {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (Z : Subfunctor F) (hZ : IsClosedSubspace B S hS Z)
    (P : Subfunctor F) (hP : P = openComplement B S hS Z) (x : GeometricPoint B S hS F) :
    (∃ u : GeometricPoint B S hS P.toFunctor, geometricPointMap P.ι u = x) ∨
      ∃ z : GeometricPoint B S hS Z.toFunctor, geometricPointMap Z.ι z = x := by
  subst hP
  by_cases h : x.image ∈ Set.range (pointsMap B S hS Z.toFunctor Z.ι)
  · right
    obtain ⟨z, hz⟩ := exists_geometricPoint_map_eq_of_mem_range B S hS
      (X := ⟨F, hF⟩) (Z := ⟨Z.toFunctor, hZ.1⟩) (ObjectProperty.homMk Z.ι) hZ.2 x h
    exact ⟨z, hz⟩
  · left
    have hU := isOpenSubspace_openComplement B S hS hF Z hZ
    rw [← Set.mem_compl_iff, ← range_pointsMap_ι_openComplement] at h
    obtain ⟨u₀, hu₀⟩ := h
    obtain ⟨u, -, hu⟩ := exists_geometricPoint_lift_of_isEtale B S hS hU.1 hF
      (openComplement B S hS Z).ι (isEtale_of_isOpenImmersion B S hS hU.2) x u₀ hu₀
    exact ⟨u, Subtype.ext hu⟩

end AlgebraicGeometry.Space

end
