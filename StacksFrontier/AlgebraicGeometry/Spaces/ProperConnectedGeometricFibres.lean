module

public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreInducing
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperConnectedFibresOverAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase

/-!
# Connected geometric fibres of a proper morphism with `f_* 𝒪_X = 𝒪_Y`

Let `f : X ⟶ Y` be a proper surjective morphism of algebraic spaces over `S` with `Y` locally
Noetherian and `𝒪_Y ⟶ f_* 𝒪_X` an isomorphism.  Then every geometric fibre of `f` is
connected.  This is the connectedness assertion of the Stein factorization, Stacks 0A1B,
clause (1), for the first factor `f'`, which is proper, surjective and has `f'_* 𝒪_X = 𝒪_{Y'}`.

By Stacks 0A1A
(`AlgebraicGeometry.Space.connectedSpace_geometricFiber_iff_forall_scheme_etaleNeighborhood`) it
suffices to show that for every étale neighbourhood of the geometric point by a scheme `W`
of the site, the fibre of the base change `X_W ⟶ W` over the residue field point is connected.
That fibre is the set-theoretic fibre over a point of `W` (Stacks 0AC8), which is nonempty by
surjectivity and preconnected by
`AlgebraicGeometry.Space.isPreconnected_fibre_of_isProper_of_isIso_fSharp'`, the base change
being proper with `f_* 𝒪 = 𝒪` by flat base change.

## Main results

* `AlgebraicGeometry.Space.connectedPullback_of_isProper_of_isIso_fSharp`: the statement above.

## References

* [Stacks Project, Tag 0A1B](https://stacks.math.columbia.edu/tag/0A1B)
* [Stacks Project, Tag 0A1A](https://stacks.math.columbia.edu/tag/0A1A)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The geometric fibres of a proper surjective morphism with `f_* 𝒪_X = 𝒪_Y` over a locally
Noetherian base are connected.** -/
theorem connectedPullback_of_isProper_of_isIso_fSharp {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom) (hfs : IsSurjective B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    [IsIso (smallEtaleRingedToposHom B S hS f).fSharp] (y : GeometricPoint B S hS Y.1) :
    ConnectedPullback B S hS f.hom (yonedaEquiv.symm y.val.value) := by
  refine (connectedSpace_geometricFiber_iff_forall_scheme_etaleNeighborhood B S hS X.property
    Y.property f.hom y).2 fun U W e => ?_
  let r := representedResidueFieldPointInNeighborhood B S hS U W e
  -- the étale morphism from the scheme `W` and the point of `W`
  let a : yoneda.obj W ⟶ Y.obj := e.inv ≫ U.toBase
  have ha : IsEtale B S hS a := by
    intro T φ hφ
    exact U.etale_toBase T (φ ≫ e.inv) (MorphismProperty.RespectsIso.postcomp _ e.inv φ hφ)
  let q : FieldValuedPoint B S hS (yoneda.obj W) := FieldValuedPoint.map B S hS U.space e.hom r
  have hq : yonedaEquiv.symm q.value = yonedaEquiv.symm r.value ≫ e.hom :=
    (yonedaEquiv_symm_naturality_right _ e.hom _).symm
  have hka : yonedaEquiv.symm q.value ≫ a = yonedaEquiv.symm r.value ≫ U.toBase := by
    rw [hq]
    exact (Category.assoc _ _ _).trans
      (congrArg (yonedaEquiv.symm r.value ≫ ·) (e.hom_inv_id_assoc U.toBase))
  obtain ⟨hrqc, hrmono⟩ := representedResidueFieldPointInNeighborhood_qc_mono B S hS U W e
  have hqmono : Mono (yonedaEquiv.symm q.value) := by
    have := hrmono
    have h : Mono (yonedaEquiv.symm r.value ≫ e.hom) :=
      @mono_comp _ _ _ _ _ _ hrmono _ (IsIso.mono_of_iso _)
    exact hq ▸ h
  have hqqc : IsQuasiCompact B S hS (yonedaEquiv.symm q.value) := by
    rw [hq]
    exact (isQuasiCompact_comp_isIso_iff B S hS _ e.hom).2 hrqc
  -- the base change of `f` to `W`
  let aS : schemeSpace W ⟶ Y := ObjectProperty.homMk a
  let sq := IsPullback.of_hasPullback f aS
  let j := pullback.fst f aS
  let g := pullback.snd f aS
  have sqP : IsPullback j.hom g.hom f.hom a := sq.map (ObjectProperty.ι _)
  have : IsIso (smallEtaleRingedToposHom B S hS g).fSharp :=
    isIso_fSharp_of_isPullback_of_isFlat sq hf.2.1.2 (isQuasiSeparated_of_isSeparated B S hS hf.1)
      (isFlat_of_isEtale B S hS ha)
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) :=
    isLocallyNoetherian_chartScheme B S hS Y hY ⟨CostructuredArrow.mk a,
      presheaf_etale_of_isEtale B S hS ha⟩
  -- the fibre over `q` is connected
  let w := pointsToScheme B S hS W (q.class B S hS (yoneda.obj W))
  have hset : setFibre B S hS g.hom q = {x : points B S hS (pullback f aS).obj |
      pointsToScheme B S hS W (pointsMap B S hS _ g.hom x) = w} := by
    ext x
    exact ⟨congrArg (pointsToScheme B S hS W), (injective_pointsToScheme B S hS W ·)⟩
  have hpre := isPreconnected_fibre_of_isProper_of_isIso_fSharp' g
    ((isProper_isStableUnderBaseChange B S hS).of_isPullback sq hf) w
  rw [← hset] at hpre
  have hconn : ConnectedSpace (setFibre B S hS g.hom q) :=
    isConnected_iff_connectedSpace.mp ⟨isSurjective_of_isPullback B S hS sq hfs _, hpre⟩
  have hfib : ConnectedPullback B S hS g.hom (yonedaEquiv.symm q.value) :=
    (homeomorphSetFibre B S hS (pullback f aS).property (schemeSpace W).property g.hom q
      hqmono hqqc).symm.surjective.connectedSpace (Homeomorph.continuous _)
  -- transport along the pasting of the two cartesian squares
  have big : IsPullback (pullback.fst g.hom (yonedaEquiv.symm q.value) ≫ j.hom)
      (pullback.snd g.hom (yonedaEquiv.symm q.value)) f.hom
      (yonedaEquiv.symm q.value ≫ a) :=
    (IsPullback.of_hasPullback g.hom (yonedaEquiv.symm q.value)).paste_horiz sqP
  rw [← hka]
  exact connectedSpace_of_presheafIso B S hS big.isoPullback hfib

end AlgebraicGeometry.Space

end
