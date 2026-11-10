module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ProperValuativeLifting
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenInCoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.CoherentSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricModuleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkInvertible
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleFiniteTypeQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedInvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse

/-!
# A map of invertible modules which is an isomorphism on the closed fibre

Let `f : X ⟶ Y` be a universally closed morphism of algebraic spaces and let `Y₀ ⟶ Y` be a
morphism whose image meets every nonempty closed subset of `|Y|`; the model case is the closed
point `Spec κ ⟶ Spec R` of a local ring. Let `X₀ = X ×_Y Y₀` be the fibre. A map `u : M ⟶ N` of
quasi-coherent `𝒪_X`-modules with `N` of finite type is surjective as soon as its restriction to
`X₀` is: the support of `Coker u` is closed, its image in `|Y|` is closed because `f` is closed,
and that image misses the image of `|Y₀|` because formation of the support commutes with
pullback; so the image is empty. If `M` and `N` are invertible, a surjection `M ⟶ N` is an
isomorphism, since on each geometric stalk it is a surjective linear map between free modules
of rank one over the étale local ring.

This is the last step of the proof of Stacks 0DNJ: a section `s : 𝒪_{X_R} ⟶ L` of an invertible
module over a valuation ring `R` whose restriction to the closed fibre is an isomorphism
trivializes `L`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_epi_of_isInvertibleModule`: an epimorphism between
  invertible modules on an algebraic space is an isomorphism.
* `AlgebraicGeometry.Space.epi_of_epi_modulePullback_of_isPullback`: a map of quasi-coherent
  modules with target of finite type which is surjective on the fibre over a morphism meeting
  every nonempty closed set is surjective, for a universally closed morphism.
* `AlgebraicGeometry.Space.isIso_of_isIso_modulePullback_of_isPullback`: the same for an
  isomorphism of invertible modules.
* `AlgebraicGeometry.Space.exists_pointsMap_yoneda_mem_of_isClosed`: a morphism of schemes
  meeting every nonempty closed set does so on the points of the represented presheaves.
* `AlgebraicGeometry.Space.isIso_of_isIso_modulePullback_closedPoint`: the case of the closed
  point of the spectrum of a local ring.

## Implementation notes

Surjectivity of a map of modules is emptiness of the support of its cokernel
(`AlgebraicGeometry.Space.supportOfSheaf_eq_empty_iff_isZero`); the cokernel is quasi-coherent
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_cokernel_unconditional`) and of finite type, so
its support is closed (Stacks 07TZ part (1)) and pulls back to the support of its pullback
(Stacks 07TZ part (3), `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq`). The
pullback functor is a left adjoint, so it carries the cokernel of `u` to the cokernel of its
pullback. Points of the fibre product are lifted with Stacks 03H4,
`AlgebraicGeometry.Space.exists_points_of_isPullback`.

## References

* [Stacks Project, Tag 0DNJ](https://stacks.math.columbia.edu/tag/0DNJ)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section EpiIso

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- **An epimorphism between invertible modules is an isomorphism.** On every geometric stalk
the map is a surjective linear map between free modules of rank one over the étale local ring,
hence injective (a surjective endomorphism of a finite module is injective); a map of modules
injective on all geometric stalks is a monomorphism, and a monomorphism which is an epimorphism
is an isomorphism. -/
theorem isIso_of_epi_of_isInvertibleModule {Z : AlgebraicSpaces B S hS}
    {M L : Modules.{u, u} B S hS Z.1 Z.2} (hM : IsInvertibleModule Z M)
    (hL : IsInvertibleModule Z L) (φ : M ⟶ L) [Epi φ] : IsIso φ := by
  have hmono : Mono φ := by
    refine (mono_iff_injective_geometricModuleStalkMap B S hS Z φ).mpr fun x => ?_
    obtain ⟨eM⟩ := nonempty_linearEquiv_geometricModuleStalk_of_isInvertibleModule B S hS Z x M hM
    obtain ⟨eL⟩ := nonempty_linearEquiv_geometricModuleStalk_of_isInvertibleModule B S hS Z x L hL
    let ψ : geometricModuleStalk B S hS Z x M →ₗ[etaleLocalRing B S hS Z.1 x]
        geometricModuleStalk B S hS Z x L :=
      { toFun := geometricModuleStalkMap B S hS Z x φ
        map_add' := map_add _
        map_smul' := geometricModuleStalkMap_smul B S hS Z x φ }
    let e := eL.toLinearMap ∘ₗ ψ ∘ₗ eM.symm.toLinearMap
    have hinj : Function.Injective e := OrzechProperty.injective_of_surjective_endomorphism e
      (eL.surjective.comp
        (((epi_iff_surjective_geometricModuleStalkMap B S hS Z φ).mp inferInstance x).comp
          eM.symm.surjective))
    intro a b hab
    apply eM.injective
    apply hinj
    change eL (ψ (eM.symm (eM a))) = eL (ψ (eM.symm (eM b)))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact congrArg eL hab
  exact isIso_of_mono_of_epi φ

end EpiIso

/-- **Surjectivity on a fibre meeting every closed set propagates.** Let `f : X ⟶ Y` be
universally closed, let `i : Y₀ ⟶ Y` be a morphism whose image meets every nonempty closed
subset of `|Y|`, and let `X₀ = X ×_Y Y₀` with projection `j : X₀ ⟶ X`. A map `u : M ⟶ N` of
quasi-coherent `𝒪_X`-modules, `N` of finite type, whose pullback to `X₀` is an epimorphism is an
epimorphism. -/
theorem epi_of_epi_modulePullback_of_isPullback {X Y X₀ Y₀ : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : UniversallyClosed B S hS f.hom) (i : Y₀ ⟶ Y) (f₀ : X₀ ⟶ Y₀)
    (j : X₀ ⟶ X) (sq : IsPullback j.hom f₀.hom f.hom i.hom)
    (hi : ∀ W : Set (points B S hS Y.1), IsClosed W → W.Nonempty →
      ∃ y₀, pointsMap B S hS Y₀.1 i.hom y₀ ∈ W)
    {M N : Modules.{u, u} B S hS X.1 X.2} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (hNft : SheafOfModules.IsFiniteTypeOnSite N) (u : M ⟶ N)
    (hu : Epi ((modulePullback B S hS j).map u)) : Epi u := by
  set Q : Modules.{u, u} B S hS X.1 X.2 := cokernel u
  have hQqc : Q.IsQuasicoherentOnSite :=
    @isQuasicoherentOnSite_cokernel_unconditional B S hS X.1 X.2 M N hM hN u
  have hQft := isFiniteTypeOnSite_cokernel_of_isFiniteTypeOnSite B S hS X.1 X.2 u hNft
  have hZ := isClosed_supportOfSheaf_of_epi B S hS X.1 X.2 (cokernel.π u) hNft
  have hadj := modulePullbackAdjunction B S hS j
  have := hadj.isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (modulePullback B S hS j) :=
    hadj.leftAdjoint_preservesColimits
  have hQ0 : IsZero ((modulePullback B S hS j).obj Q) :=
    ((Preadditive.epi_iff_isZero_cokernel _).mp hu).of_iso
      (PreservesCokernel.iso (modulePullback B S hS j) u)
  have hpre : pointsMap B S hS X₀.1 j.hom ⁻¹'
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj Q) = ∅ := by
    rwa [← supportOfSheaf_modulePullback_eq B S hS j Q hQqc hQft,
      supportOfSheaf_eq_empty_iff_isZero]
  have hW := isClosed_of_universallyClosed B S hS Y.2 f.hom hf _ hZ
  have hWempty : pointsMap B S hS X.1 f.hom ''
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj Q) = ∅ := by
    by_contra hne
    obtain ⟨y₀, x, hxZ, hx⟩ := hi _ hW (Set.nonempty_iff_ne_empty.2 hne)
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B S hS sq x y₀ hx
    exact (Set.eq_empty_iff_forall_notMem.1 hpre w) (by rwa [Set.mem_preimage, hw])
  rw [Preadditive.epi_iff_isZero_cokernel]
  exact (supportOfSheaf_eq_empty_iff_isZero B S hS X Q).mp (Set.image_eq_empty.1 hWempty)

/-- **A map of invertible modules which is an isomorphism on a fibre meeting every closed set
is an isomorphism.** In the situation of
`AlgebraicGeometry.Space.epi_of_epi_modulePullback_of_isPullback`, a map `s : M ⟶ L` of
invertible `𝒪_X`-modules whose pullback to `X₀` is an isomorphism is an isomorphism. -/
theorem isIso_of_isIso_modulePullback_of_isPullback {X Y X₀ Y₀ : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : UniversallyClosed B S hS f.hom) (i : Y₀ ⟶ Y) (f₀ : X₀ ⟶ Y₀)
    (j : X₀ ⟶ X) (sq : IsPullback j.hom f₀.hom f.hom i.hom)
    (hi : ∀ W : Set (points B S hS Y.1), IsClosed W → W.Nonempty →
      ∃ y₀, pointsMap B S hS Y₀.1 i.hom y₀ ∈ W)
    {M L : Modules.{u, u} B S hS X.1 X.2} (hM : IsInvertibleModule X M)
    (hL : IsInvertibleModule X L) (s : M ⟶ L)
    (hs : IsIso ((modulePullback B S hS j).map s)) : IsIso s := by
  have : L.IsFinitePresentationOnSite := isFinitePresentationOnSite_of_isInvertibleModule L hL
  have : Epi s := epi_of_epi_modulePullback_of_isPullback f hf i f₀ j sq hi
    (isQuasicoherentOnSite_of_isInvertibleModule X M hM)
    (isQuasicoherentOnSite_of_isInvertibleModule X L hL) inferInstance s
    (@IsIso.epi_of_iso _ _ _ _ _ hs)
  exact isIso_of_epi_of_isInvertibleModule hM hL s

/-- A morphism of the site whose underlying morphism of schemes meets every nonempty closed
subset of its target meets, on points of the represented presheaves, every nonempty closed set
of points: the points of a represented presheaf are those of the representing scheme, with its
topology. -/
theorem exists_pointsMap_yoneda_mem_of_isClosed {U V : BigFppfOver B S hS} (h : V ⟶ U)
    (hh : ∀ W : Set ((BigFppfOver.toScheme B S hS).obj U), IsClosed W → W.Nonempty →
      ∃ v, (BigFppfOver.toScheme B S hS).map h v ∈ W)
    (W : Set (points B S hS (yoneda.obj U))) (hW : IsClosed W) (hne : W.Nonempty) :
    ∃ y₀, pointsMap B S hS (yoneda.obj V) (yoneda.map h) y₀ ∈ W := by
  rw [isClosed_pointTopology_yoneda_iff_isClosed_image] at hW
  obtain ⟨v, w, hwW, hw⟩ := hh _ hW (hne.image _)
  obtain ⟨y₀, rfl⟩ := surjective_pointsToScheme B S hS V v
  refine ⟨y₀, ?_⟩
  have heq : pointsToScheme B S hS U (pointsMap B S hS (yoneda.obj V) (yoneda.map h) y₀) =
      pointsToScheme B S hS U w := by
    rw [pointsToScheme_pointsMap_yoneda, hw]
  rwa [injective_pointsToScheme B S hS U heq]

/-- **A map of invertible modules over a local ring which is an isomorphism on the closed fibre
is an isomorphism.** Let `R` be a local ring whose spectrum lies in the site, let
`f : X ⟶ Spec R` be universally closed, and let `X₀ = X ×_{Spec R} Spec κ` be the closed fibre,
`κ` the residue field. A map `s : M ⟶ L` of invertible `𝒪_X`-modules whose pullback to `X₀` is
an isomorphism is an isomorphism. -/
theorem isIso_of_isIso_modulePullback_closedPoint (R : Type u) [CommRing R] [IsLocalRing R]
    (ring_mem : B.Contains (Spec (.of R)))
    (field_mem : B.Contains (Spec (.of (IsLocalRing.ResidueField R))))
    (base : Spec (.of R) ⟶ S) {X X₀ : AlgebraicSpaces B S hS}
    (f : X ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS ring_mem base))
    (hf : UniversallyClosed B S hS f.hom)
    (f₀ : X₀ ⟶ (schemeSpaceFunctor B S hS).obj (siteObject B S hS field_mem
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) ≫ base)))
    (j : X₀ ⟶ X)
    (sq : IsPullback j.hom f₀.hom f.hom ((schemeSpaceFunctor B S hS).map
      (specSiteObjectMap (IsLocalRing.residue R) ring_mem field_mem base)).hom)
    {M L : Modules.{u, u} B S hS X.1 X.2} (hM : IsInvertibleModule X M)
    (hL : IsInvertibleModule X L) (s : M ⟶ L)
    (hs : IsIso ((modulePullback B S hS j).map s)) : IsIso s := by
  refine isIso_of_isIso_modulePullback_of_isPullback f hf _ f₀ j sq ?_ hM hL s hs
  refine exists_pointsMap_yoneda_mem_of_isClosed _ fun W hW ⟨w, hw⟩ => ?_
  refine ⟨IsLocalRing.closedPoint (IsLocalRing.ResidueField R), ?_⟩
  change Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) _ ∈ W
  have : IsLocalHom (CommRingCat.ofHom (IsLocalRing.residue R)).hom :=
    inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
  rw [Spec_closedPoint]
  exact (IsLocalRing.specializes_closedPoint (R := R) w).mem_closed hW hw

end AlgebraicGeometry.Space

end
