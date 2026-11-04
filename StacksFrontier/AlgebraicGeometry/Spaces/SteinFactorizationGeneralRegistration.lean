module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointsDescendStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibreInducing
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricFibreConnected
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinConnectedFibreCore
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationStructureSheafIso

/-!
# Stein factorization of a proper morphism of algebraic spaces, general case

This file proves **Stacks 0A1C**: for a proper morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the factorization `X ⟶ Y' ⟶ Y` through the normalization `Y'` of `Y` in `X`
(Stacks 0822, `AlgebraicGeometry.Space.normalizationInQcqs`) has the five properties of the
source: `f'` is proper with connected geometric fibres, `π : Y' ⟶ Y` is integral,
`f'_*𝒪_X = 𝒪_{Y'}`, `Y' = \underline{Spec}_Y(f_*𝒪_X)`, and `Y'` is the normalization of `Y`
in `X`.

## Main results

* `AlgebraicGeometry.Space.connectedPullback_of_isProper_of_isIso_fSharp_unconditional`: a proper,
  surjective morphism `g : X ⟶ Y` of algebraic spaces with `g_*𝒪_X = 𝒪_Y` has connected
  geometric fibres, with no Noetherian hypothesis on `Y` (the base's
  `AlgebraicGeometry.Space.connectedPullback_of_isProper_of_isIso_fSharp` assumes `Y` locally
  Noetherian).
* `AlgebraicGeometry.Space.steinFactorization_general_complete`: **Stacks 0A1C**, all five clauses.

## Implementation notes

All clauses except the connectedness of the geometric fibres are in
`StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationStructureSheafIso` (clause (3)),
`StacksFrontier.AlgebraicGeometry.Spaces.SteinFactorizationGeneral` (properness of `f'`; that file's
`AlgebraicGeometry.Space.steinFactorization_general` registers clauses (1)-properness, (2), (4)
and (5)) and in the base (clause (2) and (5): Stacks 0823; clause (4): Stacks 0A0Q).

For the connectedness, Stacks 0A1A
(`AlgebraicGeometry.Space.connectedSpace_geometricFiber_iff_forall_scheme_etaleNeighborhood`)
reduces it to the connectedness of the fibre over the residue field point of every
scheme-valued étale neighbourhood `W` of the geometric point.  The base change `g : X_W ⟶ W`
is proper, and every clopen set of points of `X_W ×_W T`, for `T ⟶ W` étale, is a clopen set of
points of `X ×_{Y'} T`, hence by `f'_*𝒪_X = 𝒪_{Y'}` the preimage of a set of points of `T`
(`AlgebraicGeometry.Space.exists_eq_preimage_of_isClopen_of_isIso_fSharp`).  So the
set-theoretic fibre of `g` over the point of `W` is preconnected
(`AlgebraicGeometry.Space.isPreconnected_fibre_of_forall_isClopen_eq_preimage`), and nonempty
because `f'` is surjective (Stacks 0A19).  The fibre over the residue field point is
homeomorphic to the set-theoretic fibre by Stacks 0AC8
(`AlgebraicGeometry.Space.homeomorphSetFibre`).

The source proves the connectedness through absolute Noetherian approximation (Stacks 0A0X)
and the Noetherian case (Stacks 0A1B, via the theorem on formal functions 08B1); neither is
available for algebraic spaces in this library, and the argument above replaces them with
Chow's lemma for algebraic spaces and the case of schemes, see
`StacksFrontier.AlgebraicGeometry.Spaces.SteinConnectedFibreCore`.

## References

* [Stacks Project, Tag 0A1C](https://stacks.math.columbia.edu/tag/0A1C)
* [Stacks Project, Tag 0A19](https://stacks.math.columbia.edu/tag/0A19)
* [Stacks Project, Tag 0A1A](https://stacks.math.columbia.edu/tag/0A1A)
* [Stacks Project, Tag 0AC8](https://stacks.math.columbia.edu/tag/0AC8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS}

/-- Clopen sets of points of the base changes of `g = pullback.snd f t` along étale morphisms
descend, when `f_*𝒪_X = 𝒪_Y` and `t : h_W ⟶ Y` is étale. -/
theorem forall_isClopen_eq_preimage_pullback_snd (f : X ⟶ Y)
    (hf : IsIso (smallEtaleRingedToposHom B S hS f).fSharp) {W : BigFppfOver B S hS}
    (t : yoneda.obj W ⟶ Y.1) (ht : IsEtale B S hS t) (T : BigFppfOver B S hS) (τ : T ⟶ W)
    (hτ : Etale ((BigFppfOver.toScheme B S hS).map τ))
    (A : Set (points B S hS (pullback (pullback.snd f.hom t) (yoneda.map τ))))
    (hA : IsClopen A) :
    ∃ D : Set ((BigFppfOver.toScheme B S hS).obj T), ∀ x, x ∈ A ↔
      pointsToScheme B S hS T (pointsMap B S hS _
        (pullback.snd (pullback.snd f.hom t) (yoneda.map τ)) x) ∈ D := by
  let V : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk (yoneda.map τ ≫ t),
    presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS (etale_yoneda B S hS τ hτ) ht)⟩
  have sq : IsPullback (chartBaseChange B S hS f V).1.hom.hom
      (chartBaseChangeProjection B S hS f V).hom f.hom (yoneda.map τ ≫ t) :=
    (isPullback_chartBaseChangeProjection B S hS f V).flip
  let Φ : pullback (pullback.snd f.hom t) (yoneda.map τ) ≅
      (chartBaseChangeSpace B S hS f V).obj :=
    pullbackLeftPullbackSndIso f.hom t (yoneda.map τ) ≪≫ sq.isoPullback.symm
  have hΦ : Φ.hom ≫ (chartBaseChangeProjection B S hS f V).hom =
      pullback.snd (pullback.snd f.hom t) (yoneda.map τ) :=
    (Category.assoc _ _ _).trans ((congrArg
      ((pullbackLeftPullbackSndIso f.hom t (yoneda.map τ)).hom ≫ ·)
        sq.isoPullback_inv_snd).trans (pullbackLeftPullbackSndIso_hom_snd _ _ _))
  set h := pointsHomeomorphOfIso B S hS Φ
  obtain ⟨D, hD⟩ := exists_eq_preimage_of_isClopen_of_isIso_fSharp f hf V (h.symm ⁻¹' A)
    (hA.preimage h.symm.continuous)
  refine ⟨D, fun x => ?_⟩
  have h1 := hD (h x)
  rw [Set.mem_preimage, Homeomorph.symm_apply_apply] at h1
  rw [h1, pointsHomeomorphOfIso_apply]
  have E : pointsMap B S hS _ (chartBaseChangeProjection B S hS f V).hom
      (pointsMap B S hS _ Φ.hom x) =
        pointsMap B S hS _ (pullback.snd (pullback.snd f.hom t) (yoneda.map τ)) x :=
    (pointsMap_comp_apply B S hS Φ.hom _ x).symm.trans
      (congrArg (fun m => pointsMap B S hS _ m x) hΦ)
  exact Iff.of_eq (congrArg (fun z => pointsToScheme B S hS T z ∈ D) E)

/-- **A proper surjective morphism `g` with `g_*𝒪_X = 𝒪_Y` has connected geometric fibres.**
Let `g : X ⟶ Y` be a proper morphism of algebraic spaces over `S`, surjective on points, whose
structure map `𝒪_Y ⟶ g_*𝒪_X` is an isomorphism.  Then the fibre of `g` over every geometric
point of `Y` is connected. -/
theorem connectedPullback_of_isProper_of_isIso_fSharp_unconditional (f : X ⟶ Y)
    (hfP : IsProper B S hS f.hom) (hfS : IsSurjective B S hS f.hom)
    (hf : IsIso (smallEtaleRingedToposHom B S hS f).fSharp)
    (y : GeometricPoint B S hS Y.1) :
    ConnectedPullback B S hS f.hom (yonedaEquiv.symm y.val.value) := by
  refine (connectedSpace_geometricFiber_iff_forall_scheme_etaleNeighborhood B S hS X.2 Y.2
    f.hom y).2 fun U W e => ?_
  set t : yoneda.obj W ⟶ Y.1 := e.inv ≫ U.toBase
  have ht : IsEtale B S hS t := isEtale_comp B S hS (isEtale_of_isIso B S hS e.inv) U.etale_toBase
  have hYW := isAlgebraicSpace_yoneda B S hS W
  set XW := pullback f.hom t
  set g := pullback.snd f.hom t
  have sqW : IsPullback (pullback.fst f.hom t) g f.hom t := IsPullback.of_hasPullback _ _
  have hXW : IsAlgebraicSpace B S hS XW := isAlgebraicSpace_pullback B S hS f.hom t X.2 hYW Y.2
  have hg : IsProper B S hS g := isProper_of_isPullback B S hS hXW X.2 hYW Y.2 sqW hfP
  set w := schemePoint B S hS W (FieldValuedPoint.map B S hS U.space e.hom (liftedPoint U))
  set p := schemeResidueFieldPoint B S hS W w
  -- the set-theoretic fibre over `w`
  have hpw : pointsToScheme B S hS W (p.class B S hS (yoneda.obj W)) = w := by
    rw [pointsToScheme_class]
    exact Scheme.fromSpecResidueField_apply w _
  have hZ : setFibre B S hS g p =
      {x | pointsToScheme B S hS W (pointsMap B S hS XW g x) = w} := by
    ext x
    show pointsMap B S hS XW g x = p.class B S hS (yoneda.obj W) ↔ _
    refine ⟨fun h => ?_, fun h => injective_pointsToScheme B S hS W (h.trans hpw.symm)⟩
    show pointsToScheme B S hS W (pointsMap B S hS XW g x) = w
    rw [h]
    exact hpw
  have hpre := isPreconnected_fibre_of_forall_isClopen_eq_preimage hXW g hg
    (fun T τ hτ A hA => forall_isClopen_eq_preimage_pullback_snd f hf t ht T τ hτ A hA) w
  have hne : (setFibre B S hS g p).Nonempty := by
    obtain ⟨x, hx⟩ := surjective_pointsMap_of_isPullback B S hS sqW hfS
      (p.class B S hS (yoneda.obj W))
    exact ⟨x, hx⟩
  rw [← hZ] at hpre
  have hconn : ConnectedSpace (setFibre B S hS g p) :=
    isConnected_iff_connectedSpace.mp ⟨hne, hpre⟩
  have hfib : ConnectedPullback B S hS g (yonedaEquiv.symm p.value) :=
    (homeomorphSetFibre B S hS hXW hYW g p (mono_schemeResidueFieldPoint B S hS W w)
      (quasiCompact_schemeResidueFieldPoint B S hS W w)).connectedSpace_iff.mpr hconn
  have hcomp := connectedSpace_of_presheafIso B S hS
    (pullbackLeftPullbackSndIso f.hom t (yonedaEquiv.symm p.value)) hfib
  have hval : yonedaEquiv.symm (representedResidueFieldPointInNeighborhood B S hS U W e).value ≫
      U.toBase = yonedaEquiv.symm p.value ≫ t := by
    refine (congrArg (· ≫ U.toBase) ?_).trans (Category.assoc _ _ _)
    exact (yonedaEquiv_symm_naturality_right _ e.inv p.value).symm
  rw [hval]
  exact hcomp

/-- **Stacks 0A1C (Stein factorization; general case).**  Let `f : X ⟶ Y` be a proper morphism
of algebraic spaces over a scheme `S`.  Let `π : Y' ⟶ Y` be the normalization of `Y` in `X`
(Stacks 0822, `AlgebraicGeometry.Space.normalizationInQcqs`, which needs `f` quasi-compact and
quasi-separated, as a proper morphism is) and `f' : X ⟶ Y'` the canonical morphism, so that
`f = π ∘ f'`.  Then:

1. `f'` is proper with connected geometric fibres: for every geometric point `ȳ` of `Y'` the
   fibre `X ×_{Y'} ȳ` has connected point space;
2. `π : Y' ⟶ Y` is integral;
3. `f'_*𝒪_X = 𝒪_{Y'}`: the structure map `𝒪_{Y'} ⟶ f'_*𝒪_X` of Stacks 03G8 is an isomorphism;
4. `Y' = \underline{Spec}_Y(f_*𝒪_X)`: `π` is affine and the map `π_*𝒪_{Y'} ⟶ f_*𝒪_X` of
   `𝒪_Y`-algebras induced by `f'` is an isomorphism;
5. `Y'` is the normalization of `Y` in `X`: the factorization has the two properties of
   Stacks 0823 which characterize it.

The conclusion also records the factorization `f = π ∘ f'` itself.  No hypothesis beyond
properness of `f` is used. -/
@[stacks 0A1C "all five clauses, for the factorization X ⟶ Y' ⟶ Y through the normalization \
of Y in X (0822): f' proper with connected geometric fibres, π integral, f'_*O_X = O_{Y'} as the \
invertibility of the structure map, Y' = Spec_Y(f_*O_X) as π affine with π_*O_{Y'} ≅ f_*O_X, \
and the 0823 characterization of the normalization"]
theorem steinFactorization_general_complete (f : X ⟶ Y) (hf : IsProper B S hS f.hom) :
    let hfqc := isQuasiCompact_of_universallyClosed B S hS X.2 Y.2 f.hom hf.2.2
    let hfqs := isQuasiSeparated_of_isSeparated B S hS hf.1
    toNormalizationInQcqs f hfqc hfqs ≫ normalizationInQcqsHom B S hS f hfqc hfqs = f ∧
      (IsProper B S hS (toNormalizationInQcqs f hfqc hfqs).hom ∧
        ∀ y : GeometricPoint B S hS (normalizationInQcqs B S hS f hfqc hfqs).1,
          ConnectedPullback B S hS (toNormalizationInQcqs f hfqc hfqs).hom
            (yonedaEquiv.symm y.val.value)) ∧
      IsIntegralHom B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom ∧
      IsIso (smallEtaleRingedToposHom B S hS (toNormalizationInQcqs f hfqc hfqs)).fSharp ∧
      (IsAffineHom B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom ∧
        IsIso (pushforwardAlgebraMap B S hS (toNormalizationInQcqsOver f hfqc hfqs))) ∧
      IsRelativeNormalization B S hS f.hom (normalizationInQcqsHom B S hS f hfqc hfqs).hom
        (toNormalizationInQcqs f hfqc hfqs).hom := by
  intro hfqc hfqs
  have hrel := isRelativeNormalization_normalizationInQcqs f hfqc hfqs
  have hsharp := isIso_fSharp_toNormalizationInQcqs f hfqc hfqs hf.2.2
  have hP := isProper_toNormalizationInQcqs B S hS f hfqc hfqs hf
  have hsurj : IsSurjective B S hS (toNormalizationInQcqs f hfqc hfqs).hom :=
    isSurjective_of_isRelativeNormalization B S hS hrel X.2
      (normalizationInQcqs B S hS f hfqc hfqs).2
      (isQuasiCompact_toNormalizationInQcqs B S hS f hfqc hfqs)
      (universallyClosed_toNormalizationInQcqs B S hS f hfqc hfqs hf.2.2)
  exact ⟨toNormalizationInQcqs_comp f hfqc hfqs,
    ⟨hP, connectedPullback_of_isProper_of_isIso_fSharp_unconditional _ hP hsurj hsharp⟩,
    isIntegralHom_normalizationInQcqsHom f hfqc hfqs, hsharp,
    ⟨isAffineHom_normalizationInQcqsHom B S hS f hfqc hfqs,
      isIso_pushforwardAlgebraMap_toNormalizationInQcqsOver_of_universallyClosed f hfqc hfqs
        hf.2.2⟩,
    hrel⟩

end AlgebraicGeometry.Space

end
