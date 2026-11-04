module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RepresentedZariskiTorAmplitude
public import StacksFrontier.AlgebraicGeometry.Spaces.RelocalizeChartRestriction

/-!
# Locally finite relative Tor dimension across `ε : X_étale ⟶ X_Zar` (Stacks 0DK7 (2))

Tor amplitude of `ε^*E` over `h⁻¹𝒪` on a slice of the small étale site of `yoneda.obj T` is read
at the points of the scheme in the image of the slice, and part (2) of Stacks 0DK7 follows from
part (1) by covering arguments.
-/

@[expose] public noncomputable section

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

open CategoryTheory CategoryTheory.Limits Opposite StacksDraft.TorAmplitude

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (g : T ⟶ T')

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

/-- **Tor amplitude on a slice of the small étale site, read at the geometric points lifting to
it.** -/
theorem hasTorAmplitude_derivedRestriction_iff_forall_relativeStalk
    (V : (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).C)
    (TV : Stacks.SheafOfModules.DerivedTensorProduct
      ((inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).over V))
    (F : RingedSite.DerivedModules (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)))
    (a b : ℤ) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude TV
        ((RingedSite.derivedRestriction
          (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)) V).obj F) a b ↔
      ∀ (x : GeometricPoint B S hS (yoneda.obj T))
        (_ : (etaleSitePoint B S hS (yoneda.obj T) x
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T)).fiber.obj V),
        HasTorAmplitudeCanonical (relativeStalkRing (representedSpaceMap B S hS g) x)
          ((Stacks.derivedModuleFiber
            (etaleSitePoint B S hS (yoneda.obj T) x
              (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T))
            (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).O).obj F) a b := by
  refine ⟨fun h x p => ?_, fun h => ?_⟩
  · exact (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_derivedRestriction_iff
      (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)) _ p F a b).1
      (Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeCanonical_derivedModuleFiber
        _ _ a b h _)
  · have hcons := isConservativeFamilyOfPoints_etaleSitePointOver B S hS
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS T) V
    refine
      Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_forall_derivedModuleFiber_family
      TV _ a b _ hcons (fun ψ => ?_)
    exact (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_derivedRestriction_iff
      (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)) _ ψ.2 F a b).2 (h ψ.1 ψ.2)

/-- **Tor amplitude on a slice, read on the scheme.**  On the slice over an étale chart `V` of
`yoneda.obj T`, `ε^*E` read over `h⁻¹𝒪` has Tor amplitude in `[a, b]` exactly when `E_z` has Tor
amplitude in `[a, b]` over `𝒪_{Y, g₀ z}` at every point `z` of `X` in the image of `V`. -/
theorem hasTorAmplitude_derivedRestriction_representedZariski_iff
    (V : (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).C)
    (TV : Stacks.SheafOfModules.DerivedTensorProduct
      ((inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).over V))
    (E : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules)
    (a b : ℤ) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude TV
        ((RingedSite.derivedRestriction
          (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)) V).obj
          ((derivedScalarRestriction B S hS (representedSpaceMap B S hS g)).obj
            ((representedZariskiDerivedPullback B S hS T).obj E))) a b ↔
      ∀ v : chartScheme V, Scheme.Hom.HasTorAmplitudeAtPoint ((BigFppfOver.toScheme B S hS).map g)
        E ((representedChartSchemeMap V).base v) a b := by
  rw [hasTorAmplitude_derivedRestriction_iff_forall_relativeStalk]
  refine ⟨fun h v => ?_, fun h x p => ?_⟩
  · obtain ⟨x, p, hp⟩ := exists_geometricFiber_chartPoint_eq V v
    have hx := (hasTorAmplitudeCanonical_relativeStalk_representedZariski_iff' g x E a b).1 (h x p)
    rwa [representedPoint_eq_of_geometricFiber x p, hp] at hx
  · refine (hasTorAmplitudeCanonical_relativeStalk_representedZariski_iff' g x E a b).2 ?_
    rw [representedPoint_eq_of_geometricFiber x p]
    exact h _

/-- The structure morphism of an étale chart of `yoneda.obj T` is étale on schemes. -/
theorem etale_representedChartSchemeMap (V : SmallEtale B S hS (yoneda.obj T)) :
    Etale (representedChartSchemeMap V) :=
  etale_of_comp_etale_chart B S hS V.property (idEtaleChart B S hS T).property
    (by change yoneda.map (yoneda.preimage V.obj.hom) ≫ 𝟙 _ = V.obj.hom
        rw [Category.comp_id, Functor.map_preimage])

/-- The structure morphism of a Zariski open of an étale chart is the inclusion followed by the
structure morphism of the chart. -/
theorem representedChartSchemeMap_chartOpens (W : SmallEtale B S hS (yoneda.obj T))
    (O : (chartScheme W).Opens) :
    representedChartSchemeMap ((chartOpens B S hS W).obj O) =
      O.ι ≫ representedChartSchemeMap W := by
  have h : representedChartMap ((chartOpens B S hS W).obj O) =
      chartOpenOverι B S hS W O ≫ representedChartMap W := by
    apply yoneda.map_injective
    refine (Functor.map_preimage _ _).trans ?_
    exact (congrArg (yoneda.map (chartOpenOverι B S hS W O) ≫ ·)
      (Functor.map_preimage yoneda W.obj.hom).symm).trans
      (yoneda.map_comp (chartOpenOverι B S hS W O) (representedChartMap W)).symm
  exact (congrArg (BigFppfOver.toScheme B S hS).map h).trans
    ((BigFppfOver.toScheme B S hS).map_comp _ _)

/-- The structure morphism of a chart over the identity chart is the underlying morphism of
schemes of the morphism of charts. -/
theorem representedChartSchemeMap_eq_of_hom {V : SmallEtale B S hS (yoneda.obj T)}
    (k : V ⟶ idEtaleChart B S hS T) :
    representedChartSchemeMap V =
      (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS (yoneda.obj T)).map k) := by
  have h : representedChartMap V = (SmallEtale.toOver B S hS (yoneda.obj T)).map k := by
    apply yoneda.map_injective
    rw [Functor.map_preimage]
    have hw := CostructuredArrow.w k.hom
    change yoneda.map k.hom.left ≫ 𝟙 _ = V.obj.hom at hw
    rw [Category.comp_id] at hw
    exact hw.symm
  exact congrArg (BigFppfOver.toScheme B S hS).map h

/-- **Stacks 0DK7, part (2).**  Let `g₀ : X ⟶ Y` be the morphism of schemes underlying a
morphism `g` of the big fppf site and `E ∈ D(𝒪_X)`.  Then `E` read in `D(g₀⁻¹𝒪_Y)` locally has
finite Tor dimension if and only if `ε^*E` read in `D(g_{small}⁻¹𝒪_{Y_étale})` locally has
finite Tor dimension, for any family of derived tensor products on the slices.

As in part (1), `g_{small}⁻¹𝒪_{Y_étale}` is the inverse image of the structure sheaf of
`yoneda.obj T'` on the small étale site of `yoneda.obj T`, which is that of `X` by Stacks 04M0.
Both conditions are read at the points: an open cover of `X` with a Tor-amplitude interval on
each member gives the étale covers by the charts mapping into the members, and an étale cover of
the identity chart gives the open cover of `X` by the images of its members. -/
@[stacks 0DK7 "part (2)"]
theorem locallyHasFiniteTorDimension_derivedScalarRestriction_iff_representedZariskiDerivedPullback
    (Tfam : ∀ U : (inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).C,
      Stacks.SheafOfModules.DerivedTensorProduct
        ((inverseImageRingedSite B S hS (representedSpaceMap B S hS g)).over U))
    (E : DerivedCategory (representedSchemeRepresentedZariskiRingedToposHom B S hS T).Modules) :
    Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension
        (RingedSpace.inverseImage
          (representedSchemeRepresentedZariskiRingedToposHom B S hS T').toRingedSpace
          ((BigFppfOver.toScheme B S hS).map g).base)
        ((Scheme.Hom.derivedScalarRestriction ((BigFppfOver.toScheme B S hS).map g)).obj E) ↔
      Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension Tfam
        ((derivedScalarRestriction B S hS (representedSpaceMap B S hS g)).obj
          ((representedZariskiDerivedPullback B S hS T).obj E)) := by
  open Scheme.Hom in
  rw [locallyHasFiniteTorDimension_derivedScalarRestriction_iff_cover_hasTorAmplitudeAtPoint]
  refine ⟨fun ⟨I, U, hU, hb⟩ W => ?_, fun h => ?_⟩
  · choose a b hab using hb
    let R : Presieve W := fun V _ => ∃ i, ∀ v : chartScheme V,
      (representedChartSchemeMap V).base v ∈ U i
    refine ⟨R, ?_, fun V k ⟨i, hi⟩ => ⟨a i, b i,
      (hasTorAmplitude_derivedRestriction_representedZariski_iff g V (Tfam V) E _ _).2
        fun v => hab i _ (hi v)⟩⟩
    refine (SmallEtale.mem_topology_iff_exists_mem_range B S hS (yoneda.obj T) _).2 fun z => ?_
    have hz : (representedChartSchemeMap W).base z ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    let O : (chartScheme W).Opens := (representedChartSchemeMap W) ⁻¹ᵁ U i
    refine ⟨(chartOpens B S hS W).obj O, chartOpensι W O,
      Sieve.le_generate R _ _ ⟨i, fun v => ?_⟩, ⟨⟨z, hi⟩, rfl⟩⟩
    have hv := congrArg (fun φ => φ.base v) (representedChartSchemeMap_chartOpens (T := T) W O)
    exact (congrArg (· ∈ U i) hv).mpr v.2
  · obtain ⟨R, hR, hfin⟩ := h (idEtaleChart B S hS T)
    have hcov := (SmallEtale.mem_topology_iff_exists_mem_range B S hS (yoneda.obj T) _).1 hR
    have key : ∀ y : representedSchemeRepresentedZariskiRingedToposHom B S hS T,
        ∃ (V : SmallEtale B S hS (yoneda.obj T)) (a b : ℤ),
          y ∈ Set.range (representedChartSchemeMap V).base ∧
          ∀ v : chartScheme V, Scheme.Hom.HasTorAmplitudeAtPoint
            ((BigFppfOver.toScheme B S hS).map g) E ((representedChartSchemeMap V).base v) a b := by
      intro y
      obtain ⟨V, k, ⟨V', l, k', hk', rfl⟩, ⟨z, hz⟩⟩ := hcov y
      obtain ⟨a, b, hab⟩ := hfin k' hk'
      refine ⟨V', a, b, ⟨((BigFppfOver.toScheme B S hS).map
        ((SmallEtale.toOver B S hS (yoneda.obj T)).map l)).base z, ?_⟩,
        (hasTorAmplitude_derivedRestriction_representedZariski_iff g V' (Tfam V') E a b).1 hab⟩
      rw [representedChartSchemeMap_eq_of_hom k', ← hz]
      exact (congrArg (fun φ => φ.base z) ((BigFppfOver.toScheme B S hS).map_comp _ _ ▸
        congrArg (BigFppfOver.toScheme B S hS).map
          ((SmallEtale.toOver B S hS (yoneda.obj T)).map_comp l k'))).symm
    choose V a b hy hb using key
    have hopen : ∀ y, IsOpen (Set.range (representedChartSchemeMap (V y)).base) := fun y =>
      have := etale_representedChartSchemeMap (V y)
      (representedChartSchemeMap (V y)).isOpenMap.isOpen_range
    refine ⟨representedSchemeRepresentedZariskiRingedToposHom B S hS T, fun y => ⟨_, hopen y⟩, ?_,
      fun y => ⟨a y, b y, ?_⟩⟩
    · exact top_unique fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hy y⟩
    · rintro _ ⟨v, rfl⟩
      exact hb y v

end AlgebraicGeometry.Space

end
