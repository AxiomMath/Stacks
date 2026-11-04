module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.IsomorphismFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsOfPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeOfIntegralBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedCodimensionZero
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecFiniteCover
public import StacksFrontier.CategoryTheory.PullbackCancelMono
public import StacksFrontier.RingTheory.Etale.FlatEtaleSelfTensorModel

/-!
# Flat monomorphisms of algebraic spaces are representable

Let `f : X ⟶ Y` be a flat monomorphism of algebraic spaces over a scheme `S`. Then `f` is
representable by schemes: for every scheme `T` of the site with a morphism `T ⟶ Y`, the fibre
product `X ×_Y T` is a scheme. This is **Stacks 0B8A**, a result of David Rydh.

The fibre product `X ×_Y T` is again an algebraic space with a flat monomorphism to `T`, so it
suffices to show that an algebraic space `X` with a flat monomorphism `f : X ⟶ h_T` to an object
of the site is a scheme, that is, that every point of `X` lies in the schematic locus of
Stacks 03JH. After shrinking `T` to an affine open neighbourhood `Spec B` of the image of the
point, and `X` to a quasi-compact open neighbourhood of it, `X` has an affine étale surjective
chart `U = Spec C ⟶ X`. Since `f` is a monomorphism, `U ×_X U = U ×_T U = Spec (C ⊗_B C)`, so
`B → C` is flat and `C → C ⊗_B C` is étale. The commutative algebra of
`Algebra.exists_etale_bijective_map` then provides `g ∈ B` not in the prime under the point, a
`B_g`-algebra `D` étale over `B_g` with surjective spectrum map, and a map
`ψ : D → C_g` with `C ⊗_B D ≅ C ⊗_B C_g`. Geometrically: over the étale cover `V = Spec D` of
`T' = Spec B_g`, the base change `X ×_T V` of `X` receives the morphism `Spec C_g ⟶ X ×_T V`
induced by `ψ`, and its base change along the surjective étale chart `U ×_T V ⟶ X ×_T V` is
the isomorphism `Spec (C ⊗_B C_g) ⟶ Spec (C ⊗_B D)`. By fpqc descent of isomorphisms
(Stacks 041Y) it is an isomorphism, so `X ×_T V` is affine, and by the descent of affineness
along étale covers (Stacks 03WG) `X ×_T T'` is affine. It is an open subspace of `X` containing
the point, which is therefore in the schematic locus.

## Main results

* `AlgebraicGeometry.Space.isAffineSpace_pullback_of_isIso_chart`: the descent step above, for
  a monomorphism from an algebraic space with a surjective étale chart.
* `AlgebraicGeometry.Space.flat_and_etale_tensor_of_chart`: the ring maps of a flat
  monomorphism read on an affine étale chart.
* `AlgebraicGeometry.Space.exists_isAffineSpace_pullback_of_isFlat_of_mono`: a flat
  monomorphism to an affine object of the site is affine over an affine open neighbourhood of
  the image of every point of a chart.
* `AlgebraicGeometry.Space.range_pointsMap_subset_schematicLocus_of_isOpenImmersion` and
  `AlgebraicGeometry.Space.mem_range_pointsMap_schematicLocus_of_isOpenImmersion`: open
  immersions and the schematic locus.
* `AlgebraicGeometry.Space.isRepresentable_of_isFlat_of_mono`: an algebraic space with a flat
  monomorphism to an object of the site is a scheme.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_isFlat_of_mono`: **Stacks 0B8A**.

## Implementation notes

The source reduces to a local base through Limits of Spaces, Stacks 0B80, whose proof rests on
the descent of affineness along limits of Stacks 07SQ, and then concludes with the
generalization lifting of Decent Spaces, Stacks 0B7W, and fpqc descent. The argument here takes
the place of that reduction for the case at hand: since `X ×_T Spec B_p ≅ Spec B_p` is affine,
the presentation that Stacks 07SQ descends to a stage can be taken over the base ring `B`
itself, and the comparison isomorphism of the 07SQ argument becomes the bijectivity of
`C ⊗_B D → C ⊗_B C_g`, which is spread out from `p` by commutative algebra. No limit of
algebraic spaces is formed.

## References

* [Stacks Project, Tag 0B8A](https://stacks.math.columbia.edu/tag/0B8A)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 041Y](https://stacks.math.columbia.edu/tag/041Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A base change of a monomorphism, made affine by an étale chart.**

Let `f : X ⟶ h_T` be a monomorphism from an algebraic space, `a : h_U ⟶ X` a surjective étale
chart and `π : U ⟶ T` the induced morphism. Let `ι : T' ⟶ T` be a morphism from an affine
object, `v : V ⟶ T'` a surjective étale morphism from an affine object, and `ψ : U' ⟶ V` a
morphism from an affine object which lies over `j : U' ⟶ U` in the sense that
`j ≫ π = ψ ≫ v ≫ ι`. If the morphism `U ×_T U' ⟶ U ×_T V` induced by `ψ` is an isomorphism, then
the base change `X ×_T T'` is an affine algebraic space. -/
theorem isAffineSpace_pullback_of_isIso_chart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {T U T' V U' W R : BigFppfOver B S hS}
    (f : X ⟶ yoneda.obj T) [Mono f] (a : yoneda.obj U ⟶ X)
    (has : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hae : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (π : U ⟶ T) (hπ : yoneda.map π = a ≫ f) (ι : T' ⟶ T)
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')) (v : V ⟶ T')
    (hve : Etale ((BigFppfOver.toScheme B S hS).map v))
    (hvs : Surjective ((BigFppfOver.toScheme B S hS).map v))
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (j : U' ⟶ U) (ψ : U' ⟶ V) (hjψ : j ≫ π = ψ ≫ v ≫ ι)
    (hU' : IsAffine ((BigFppfOver.toScheme B S hS).obj U'))
    (wU : W ⟶ U) (wV : W ⟶ V)
    (hW : IsPullback ((BigFppfOver.toScheme B S hS).map wU) ((BigFppfOver.toScheme B S hS).map wV)
      ((BigFppfOver.toScheme B S hS).map π) ((BigFppfOver.toScheme B S hS).map (v ≫ ι)))
    (rU : R ⟶ U) (rG : R ⟶ U')
    (hR : IsPullback ((BigFppfOver.toScheme B S hS).map rU) ((BigFppfOver.toScheme B S hS).map rG)
      ((BigFppfOver.toScheme B S hS).map π) ((BigFppfOver.toScheme B S hS).map (j ≫ π)))
    (θ : R ⟶ W) (hθ : IsIso ((BigFppfOver.toScheme B S hS).map θ)) (hθU : θ ≫ wU = rU)
    (hθV : θ ≫ wV = rG ≫ ψ) :
    IsAffineSpace B S hS (pullback f (yoneda.map ι)) := by
  have hWp : IsPullback (yoneda.map wU) (yoneda.map wV) (a ≫ f) (yoneda.map (v ≫ ι)) := by
    rw [← hπ]
    exact (FiniteFreeAlgebra.isPullback_of_isPullback_toScheme hW).map yoneda
  have hRp : IsPullback (yoneda.map rU) (yoneda.map rG) a (yoneda.map j ≫ a) := by
    have h := (FiniteFreeAlgebra.isPullback_of_isPullback_toScheme hR).map yoneda
    rw [yoneda.map_comp, hπ, ← Category.assoc] at h
    exact isPullback_of_comp_mono f h
  -- `X' = X ×_T T'` and `Q = X' ×_{T'} V = X ×_T V`
  let X' := pullback f (yoneda.map ι)
  let f' : X' ⟶ yoneda.obj T' := pullback.snd f (yoneda.map ι)
  let Q := pullback f' (yoneda.map v)
  let fstQ : Q ⟶ X := pullback.fst f' (yoneda.map v) ≫ pullback.fst f (yoneda.map ι)
  let sndQ : Q ⟶ yoneda.obj V := pullback.snd f' (yoneda.map v)
  have hQ : IsPullback fstQ sndQ f (yoneda.map (v ≫ ι)) := by
    rw [yoneda.map_comp]
    exact (IsPullback.of_hasPullback f' (yoneda.map v)).paste_horiz
      (IsPullback.of_hasPullback f (yoneda.map ι))
  let φ : yoneda.obj U' ⟶ Q := hQ.lift (yoneda.map j ≫ a) (yoneda.map ψ) (by
    rw [Category.assoc, ← hπ, ← yoneda.map_comp, hjψ, yoneda.map_comp])
  let w : yoneda.obj W ⟶ Q := hQ.lift (yoneda.map wU ≫ a) (yoneda.map wV)
    (by rw [Category.assoc, hWp.w])
  have hwfst : w ≫ fstQ = yoneda.map wU ≫ a := hQ.lift_fst _ _ _
  have hwsnd : w ≫ sndQ = yoneda.map wV := hQ.lift_snd _ _ _
  have hφfst : φ ≫ fstQ = yoneda.map j ≫ a := hQ.lift_fst _ _ _
  have hφsnd : φ ≫ sndQ = yoneda.map ψ := hQ.lift_snd _ _ _
  -- the right-hand square: `W = U ×_X Q`
  have hright : IsPullback (yoneda.map wU) w a fstQ := by
    refine IsPullback.of_bot ?_ hwfst.symm hQ
    rw [hwsnd]
    exact hWp
  -- the left-hand square: the base change of `φ` along `w` is `θ`
  have hleft : IsPullback (yoneda.map θ) (yoneda.map rG) w φ := by
    refine IsPullback.of_right ?_ ?_ hright
    · rw [← yoneda.map_comp, hθU, hφfst]
      exact hRp
    · apply hQ.hom_ext
      · rw [Category.assoc, Category.assoc, hwfst, hφfst, ← Category.assoc, ← yoneda.map_comp, hθU,
          hRp.w]
      · rw [Category.assoc, Category.assoc, hwsnd, hφsnd, ← yoneda.map_comp, ← yoneda.map_comp,
          hθV]
  -- the algebraic spaces involved
  have hX' : IsAlgebraicSpace B S hS X' :=
    isAlgebraicSpace_pullback B S hS f (yoneda.map ι) hX (isAlgebraicSpace_yoneda B S hS T')
      (isAlgebraicSpace_yoneda B S hS T)
  have hQalg : IsAlgebraicSpace B S hS Q :=
    isAlgebraicSpace_pullback B S hS f' (yoneda.map v) hX' (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS T')
  -- `w` is a surjective étale chart of `Q`, being a base change of `a`
  have hwe : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w := presheaf_of_isPullback B S hS hright hae
  have hws : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf w := presheaf_of_isPullback B S hS hright has
  -- `φ` is an isomorphism, by fpqc descent of isomorphisms along `w`
  have hθ' : IsIso (yoneda.map θ) := by
    have : IsIso θ := isIso_of_reflects_iso θ (BigFppfOver.toScheme B S hS)
    infer_instance
  let Uₐ : AlgebraicSpaces B S hS := ⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩
  let Wₐ : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let Rₐ : AlgebraicSpaces B S hS := ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩
  let Qₐ : AlgebraicSpaces B S hS := ⟨Q, hQalg⟩
  let φₐ : Uₐ ⟶ Qₐ := ObjectProperty.homMk φ
  let wₐ : Wₐ ⟶ Qₐ := ObjectProperty.homMk w
  have hφ : IsIso φ := by
    have hmem : Presieve.ofArrows (fun _ : PUnit.{u + 1} ↦ Wₐ) (fun _ ↦ wₐ) ∈
        (Topology.precoverage.{u, u} .fpqc B S hS) Qₐ :=
      ⟨PUnit.{u + 1}, fun _ ↦ Wₐ, fun _ ↦ wₐ, rfl, hQalg, fun _ ↦ Wₐ.property,
        isFpqcCovering_of_isEtaleCovering B S hS _ _
          ⟨hQalg, fun _ ↦ Wₐ.property, fun _ ↦ isEtale_of_presheaf_etale B S hS hwe,
            Set.eq_univ_iff_forall.2 fun x ↦ Set.mem_iUnion.2
              ⟨PUnit.unit, isSurjective_of_presheafSurjective B S hS w hws x⟩⟩⟩
    let _ := isomorphisms_isLocalAtTarget_fpqc.{u, u} B S hS
    have : IsIso φₐ := by
      refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
        (P := MorphismProperty.isomorphisms _) hmem ?_
      rintro _ _ _ ⟨⟩
      have hsq : IsPullback (ObjectProperty.homMk (yoneda.map rG) : Rₐ ⟶ Uₐ)
          (ObjectProperty.homMk (yoneda.map θ) : Rₐ ⟶ Wₐ) φₐ wₐ :=
        IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hleft.w.symm) hleft.flip
      have : IsIso (ObjectProperty.homMk (yoneda.map θ) : Rₐ ⟶ Wₐ) :=
        (ObjectProperty.isIso_hom_iff _).1 hθ'
      exact IsIso.of_isIso_fac_left hsq.isoPullback_hom_snd
    exact (ObjectProperty.isIso_hom_iff φₐ).2 this
  -- hence `X' ⟶ h_{T'}` is affine, by descent along the chart `v` (Stacks 03WG)
  have haffQ : IsAffineHom B S hS sndQ := by
    have : sndQ = inv φ ≫ yoneda.map ψ := by rw [← hφsnd, IsIso.inv_hom_id_assoc]
    rw [this]
    have := hU'
    have := hV
    exact isAffineHom_iso_comp (inv φ) (isAffineHom_yoneda_map B S hS ψ)
  have haff : IsAffineHom B S hS f' := by
    refine ((isAffineHom_tfae_of_isAlgebraicSpace B S hS f' hX'
      (isAlgebraicSpace_yoneda B S hS T')).out 4 2).1 ?_
    refine ⟨V, yoneda.map v, ?_, ?_, haffQ⟩
    · exact isSurjective_yoneda_map B S hS v hvs
    · exact isEtale_of_presheaf_etale B S hS ((presheaf_yoneda_map_etale_iff B S hS v).2 hve)
  exact haff.isAffineSpace_source (isAffineSpace_yoneda B S hS T' hT')

open TensorProduct in
/-- **The ring maps of a flat monomorphism read on an affine étale chart.** Let `f : X ⟶ h_T`
be a flat monomorphism from an algebraic space and `a : h_U ⟶ X` an étale chart, with
`U ≅ Spec C` and `T ≅ Spec B` compatibly with `π : U ⟶ T`. Then `B → C` is flat and the first
inclusion `C → C ⊗_B C` is étale: `Spec (C ⊗_B C) = U ×_T U` is `U ×_X U`, an étale chart of
`U`. -/
theorem flat_and_etale_tensor_of_chart {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T U : BigFppfOver B S hS} (f : X ⟶ yoneda.obj T) [Mono f] (hf : IsFlat B S hS f)
    (a : yoneda.obj U ⟶ X)
    (hae : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (π : U ⟶ T) (hπ : yoneda.map π = a ≫ f) (Bt Ct : Type u) [CommRing Bt] [CommRing Ct]
    [Algebra Bt Ct] (eT : (BigFppfOver.toScheme B S hS).obj T ≅ Spec (.of Bt))
    (eU : (BigFppfOver.toScheme B S hS).obj U ≅ Spec (.of Ct))
    (hcomm : eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Bt Ct)) =
      (BigFppfOver.toScheme B S hS).map π ≫ eT.hom) :
    Module.Flat Bt Ct ∧ Algebra.Etale Ct (Ct ⊗[Bt] Ct) := by
  have hspec : Spec.map (CommRingCat.ofHom (algebraMap Bt Ct)) =
      eU.inv ≫ (BigFppfOver.toScheme B S hS).map π ≫ eT.hom := by
    rw [← hcomm, Iso.inv_hom_id_assoc]
  constructor
  · -- flatness, from the chart square of `f` over the identity of `h_T`
    have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj T)) := by
      rw [← yoneda.map_id]
      exact (presheaf_yoneda_map_etale_iff B S hS (𝟙 T)).2 (by
        simpa using (inferInstance : Etale (𝟙 ((BigFppfOver.toScheme B S hS).obj T))))
    have hflat : Flat ((BigFppfOver.toScheme B S hS).map π) :=
      hf U T a (𝟙 _) π hae hid (by rw [hπ, Category.comp_id])
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap Bt Ct))) := by
      rw [hspec]
      infer_instance
    rw [Flat.SpecMap_iff] at this
    exact RingHom.flat_algebraMap_iff.1 this
  · -- étaleness of the first projection of `U ×_T U`
    have hK := IsPullback.of_hasPullback π π
    have hKp : IsPullback (yoneda.map (pullback.fst π π)) (yoneda.map (pullback.snd π π)) a a := by
      have h := hK.map yoneda
      rw [hπ] at h
      exact isPullback_of_comp_mono f h
    have hfst : Etale ((BigFppfOver.toScheme B S hS).map (pullback.fst π π)) :=
      (presheaf_yoneda_map_etale_iff B S hS _).1 (presheaf_of_isPullback B S hS hKp.flip hae)
    have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      preservesLimitsOfShape_walkingCospan_toScheme B S hS
    have hKs := hK.map (BigFppfOver.toScheme B S hS)
    have hT := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct Bt Ct Ct)
    have hT' : IsPullback (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom (R := Bt) (A := Ct) (B := Ct))) ≫ eU.inv)
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := Bt) (A := Ct)
          (B := Ct)).toRingHom) ≫ eU.inv)
        ((BigFppfOver.toScheme B S hS).map π) ((BigFppfOver.toScheme B S hS).map π) := by
      refine IsPullback.of_iso hT (Iso.refl _) eU.symm eU.symm eT.symm ?_ ?_ ?_ ?_
      · simp
      · simp
      · simp [hspec]
      · simp [hspec]
    let e := hKs.isoIsPullback _ _ hT'
    have he : e.hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom (R := Bt) (A := Ct) (B := Ct))) ≫ eU.inv =
        (BigFppfOver.toScheme B S hS).map (pullback.fst π π) :=
      hKs.isoIsPullback_hom_fst _ _ hT'
    have : Etale (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := Bt) (A := Ct) (B := Ct)))) := by
      have : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := Bt) (A := Ct) (B := Ct))) =
          e.inv ≫ (BigFppfOver.toScheme B S hS).map (pullback.fst π π) ≫ eU.hom := by
        rw [← he]
        simp
      rw [this]
      infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @Etale)] at this
    exact RingHom.etale_algebraMap.1 this

/-- A morphism of the site between two objects over a third, given by a morphism of the
underlying schemes over the scheme underlying the third. -/
private noncomputable def homOfComp {P Q T : BigFppfOver B S hS} (p : P ⟶ T) (q : Q ⟶ T)
    (v : (BigFppfOver.toScheme B S hS).obj P ⟶ (BigFppfOver.toScheme B S hS).obj Q)
    (hv : v ≫ (BigFppfOver.toScheme B S hS).map q = (BigFppfOver.toScheme B S hS).map p) :
    P ⟶ Q :=
  BigFppfOver.homOfCompEq B S hS v (by
    have hp : B.inclusion.map p.left ≫ B.inclusion.map T.hom = B.inclusion.map P.hom := by
      rw [← Functor.map_comp, Over.w p]
    have hq : B.inclusion.map q.left ≫ B.inclusion.map T.hom = B.inclusion.map Q.hom := by
      rw [← Functor.map_comp, Over.w q]
    rw [← hp, ← hq, ← Category.assoc]
    exact congrArg (· ≫ B.inclusion.map T.hom) hv)

private theorem toScheme_map_homOfComp {P Q T : BigFppfOver B S hS} (p : P ⟶ T) (q : Q ⟶ T)
    (v : (BigFppfOver.toScheme B S hS).obj P ⟶ (BigFppfOver.toScheme B S hS).obj Q)
    (hv : v ≫ (BigFppfOver.toScheme B S hS).map q = (BigFppfOver.toScheme B S hS).map p) :
    (BigFppfOver.toScheme B S hS).map (homOfComp B S hS p q v hv) = v :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS _ _

private theorem homOfComp_comp {P Q T : BigFppfOver B S hS} (p : P ⟶ T) (q : Q ⟶ T)
    (v : (BigFppfOver.toScheme B S hS).obj P ⟶ (BigFppfOver.toScheme B S hS).obj Q)
    (hv : v ≫ (BigFppfOver.toScheme B S hS).map q = (BigFppfOver.toScheme B S hS).map p) :
    homOfComp B S hS p q v hv ≫ q = p :=
  BigFppfOver.map_toScheme_injective B S hS (by
    show (BigFppfOver.toScheme B S hS).map (homOfComp B S hS p q v hv ≫ q) = _
    rw [Functor.map_comp, toScheme_map_homOfComp, hv])

open TensorProduct in
/-- **A flat monomorphism to an affine object is affine near every point of a chart.** Let
`f : X ⟶ h_T` be a flat monomorphism from an algebraic space to an affine object of the site, and
let `a : h_U ⟶ X` be a surjective étale chart with `U` affine. For every point `u` of `U` there
is an open immersion `ι : T' ⟶ T` from an affine object, through whose image the image of `u`
passes, such that `X ×_T T'` is an affine algebraic space. -/
theorem exists_isAffineSpace_pullback_of_isFlat_of_mono {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {T U : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    (f : X ⟶ yoneda.obj T) [Mono f] (hf : IsFlat B S hS f) (a : yoneda.obj U ⟶ X)
    (has : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hae : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (y₀ : (BigFppfOver.toScheme B S hS).obj U) :
    ∃ (T' : BigFppfOver B S hS) (ι : T' ⟶ T),
      AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι) ∧
      IsAffineSpace B S hS (pullback f (yoneda.map ι)) ∧
      (BigFppfOver.toScheme B S hS).map (yoneda.preimage (a ≫ f)) y₀ ∈
        Set.range ((BigFppfOver.toScheme B S hS).map ι) := by
  classical
  let Ts := (BigFppfOver.toScheme B S hS).obj T
  let Us := (BigFppfOver.toScheme B S hS).obj U
  let π : U ⟶ T := yoneda.preimage (a ≫ f)
  have hπ : yoneda.map π = a ≫ f := yoneda.map_preimage _
  let πs := (BigFppfOver.toScheme B S hS).map π
  -- the rings
  let Bt : Type u := Γ(Ts, ⊤)
  let Ct : Type u := Γ(Us, ⊤)
  let : Algebra Bt Ct := πs.appTop.hom.toAlgebra
  let eT : Ts ≅ Spec (.of Bt) := Ts.isoSpec
  let eU : Us ≅ Spec (.of Ct) := Us.isoSpec
  have hcomm : eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Bt Ct)) = πs ≫ eT.hom :=
    Scheme.isoSpec_hom_naturality πs
  obtain ⟨hflat, het⟩ := flat_and_etale_tensor_of_chart B S hS f hf a hae π hπ Bt Ct eT eU hcomm
  -- the prime of `C` at `u`, and the local structure there
  let u₀ : PrimeSpectrum Ct := eU.hom y₀
  obtain ⟨g, hg, D, _, _, hEt, hSurj, ψr, hbij⟩ :=
    Algebra.exists_etale_bijective_map (u₀.asIdeal.comap (algebraMap Bt Ct)) u₀.asIdeal rfl
  let Bg := Localization.Away g
  let Cg := Localization (Algebra.algebraMapSubmonoid Ct (Submonoid.powers g))
  let Dg := Localization (Algebra.algebraMapSubmonoid D (Submonoid.powers g))
  -- the schemes involved belong to the site
  have hsite : ∀ (Z : BigFppfOver B S hS) (E : Type u) [CommRing E]
      (e : (BigFppfOver.toScheme B S hS).obj Z ≅ Spec (.of E)), B.Contains (Spec (.of E)) := by
    intro Z E _ e
    show (Spec (.of E)).size < B.cutoff
    rw [← Scheme.size_congr e]
    exact Z.left.2
  have hT₀ : B.Contains (Spec (.of Bt)) := hsite T Bt eT
  have hU₀ : B.Contains (Spec (.of Ct)) := hsite U Ct eU
  have hT' : B.Contains (Spec (.of Bg)) :=
    B.contains_of_isOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Bt Bg))) hT₀
  have hU' : B.Contains (Spec (.of Cg)) := by
    have : IsLocalization.Away (algebraMap Bt Ct g) Cg := by
      unfold IsLocalization.Away
      rw [← Algebra.algebraMapSubmonoid_powers]
      infer_instance
    have : AlgebraicGeometry.IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (algebraMap Ct Cg))) :=
      IsOpenImmersion.of_isLocalization (algebraMap Bt Ct g)
    exact B.contains_of_isOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap Ct Cg))) hU₀
  have hvEt : Etale (Spec.map (CommRingCat.ofHom (algebraMap Bg Dg))) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 (RingHom.etale_algebraMap.2 hEt)
  have hV : B.Contains (Spec (.of Dg)) :=
    B.contains_of_locallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap Bg Dg))) hT'
  have hDt : B.Contains (Spec (.of Dg)) := hV
  have htensor : ∀ (E : Type u) [CommRing E] [Algebra Bt E], B.Contains (Spec (.of E)) →
      B.Contains (Spec (.of (Ct ⊗[Bt] E))) := by
    intro E _ _ hE
    show (Spec (.of (Ct ⊗[Bt] E))).size < B.cutoff
    rw [← Scheme.size_congr (pullbackSpecIso Bt Ct E)]
    exact Scheme.size_pullback_lt _ _ hU₀ hE
  have hW : B.Contains (Spec (.of (Ct ⊗[Bt] Dg))) := htensor Dg hV
  have hR : B.Contains (Spec (.of (Ct ⊗[Bt] Cg))) := htensor Cg hU'
  -- the objects of the site
  let T' := BigFppfOver.siteObjectOver B S hS T hT'
    (Spec.map (CommRingCat.ofHom (algebraMap Bt Bg)) ≫ eT.inv)
  let ι : T' ⟶ T := BigFppfOver.siteMapOver B S hS T hT' _
  let V := BigFppfOver.siteObjectOver B S hS T' hV (Spec.map (CommRingCat.ofHom (algebraMap Bg Dg)))
  let v : V ⟶ T' := BigFppfOver.siteMapOver B S hS T' hV _
  let U' := BigFppfOver.siteObjectOver B S hS U hU'
    (Spec.map (CommRingCat.ofHom (algebraMap Ct Cg)) ≫ eU.inv)
  let j : U' ⟶ U := BigFppfOver.siteMapOver B S hS U hU' _
  let W := BigFppfOver.siteObjectOver B S hS U hW
    (Spec.map (CommRingCat.ofHom (algebraMap Ct (Ct ⊗[Bt] Dg))) ≫ eU.inv)
  let wU : W ⟶ U := BigFppfOver.siteMapOver B S hS U hW _
  let R := BigFppfOver.siteObjectOver B S hS U hR
    (Spec.map (CommRingCat.ofHom (algebraMap Ct (Ct ⊗[Bt] Cg))) ≫ eU.inv)
  let rU : R ⟶ U := BigFppfOver.siteMapOver B S hS U hR _
  have hπs : eU.inv ≫ πs = Spec.map (CommRingCat.ofHom (algebraMap Bt Ct)) ≫ eT.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hcomm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  -- the ring identities
  have hSpecT : ∀ (A M N : Type u) [CommRing A] [CommRing M] [CommRing N] [Algebra A M]
      [Algebra M N] [Algebra A N] [IsScalarTower A M N],
      Spec.map (CommRingCat.ofHom (algebraMap M N)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A M)) =
        Spec.map (CommRingCat.ofHom (algebraMap A N)) := by
    intros
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hψr : CommRingCat.ofHom (algebraMap Bt Dg) ≫ CommRingCat.ofHom ψr.toRingHom =
      CommRingCat.ofHom (algebraMap Bt Cg) := by
    rw [← CommRingCat.ofHom_comp]
    congr 1
    rw [IsScalarTower.algebraMap_eq Bt Bg Dg, IsScalarTower.algebraMap_eq Bt Bg Cg,
      ← RingHom.comp_assoc]
    congr 1
    exact ψr.comp_algebraMap
  have hvι : (BigFppfOver.toScheme B S hS).map (v ≫ ι) =
      Spec.map (CommRingCat.ofHom (algebraMap Bt Dg)) ≫ eT.inv := by
    show Spec.map (CommRingCat.ofHom (algebraMap Bg Dg)) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Bt Bg)) ≫ eT.inv) = _
    rw [← Category.assoc, hSpecT]
  have hπE : ∀ (E : Type u) [CommRing E] [Algebra Bt E] [Algebra Ct E] [IsScalarTower Bt Ct E],
      (Spec.map (CommRingCat.ofHom (algebraMap Ct E)) ≫ eU.inv) ≫ πs =
        Spec.map (CommRingCat.ofHom (algebraMap Bt E)) ≫ eT.inv := by
    intros
    rw [Category.assoc, hπs, ← Category.assoc, hSpecT]
  have hjπ : (BigFppfOver.toScheme B S hS).map (j ≫ π) =
      Spec.map (CommRingCat.ofHom (algebraMap Bt Cg)) ≫ eT.inv := hπE Cg
  have hwπ : (BigFppfOver.toScheme B S hS).map (wU ≫ π) =
      Spec.map (CommRingCat.ofHom (algebraMap Bt (Ct ⊗[Bt] Dg))) ≫ eT.inv := hπE _
  have hrπ : (BigFppfOver.toScheme B S hS).map (rU ≫ π) =
      Spec.map (CommRingCat.ofHom (algebraMap Bt (Ct ⊗[Bt] Cg))) ≫ eT.inv := hπE _
  -- the morphisms of the site
  have eψ : Spec.map (CommRingCat.ofHom ψr.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Bt Dg)) ≫ eT.inv) =
      Spec.map (CommRingCat.ofHom (algebraMap Bt Cg)) ≫ eT.inv := by
    rw [← Category.assoc, ← Spec.map_comp, hψr]
  let ψ : U' ⟶ V := homOfComp B S hS (j ≫ π) (v ≫ ι)
    (Spec.map (CommRingCat.ofHom ψr.toRingHom)) (by rw [hvι, hjπ]; exact eψ)
  have eincR : ∀ (E : Type u) [CommRing E] [Algebra Bt E],
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight (R := Bt) (A := Ct) (B := E)).toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap Bt E)) ≫ eT.inv) =
      Spec.map (CommRingCat.ofHom (algebraMap Bt (Ct ⊗[Bt] E))) ≫ eT.inv := by
    intro E _ _
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact Algebra.TensorProduct.includeRight.comp_algebraMap
  let incRD : Dg →ₐ[Bt] Ct ⊗[Bt] Dg := Algebra.TensorProduct.includeRight
  let incRC : Cg →ₐ[Bt] Ct ⊗[Bt] Cg := Algebra.TensorProduct.includeRight
  let wV : W ⟶ V := homOfComp B S hS (wU ≫ π) (v ≫ ι)
    (Spec.map (CommRingCat.ofHom incRD.toRingHom)) (by rw [hvι, hwπ]; exact eincR Dg)
  let rG : R ⟶ U' := homOfComp B S hS (rU ≫ π) (j ≫ π)
    (Spec.map (CommRingCat.ofHom incRC.toRingHom)) (by rw [hjπ, hrπ]; exact eincR Cg)
  let Θ : Ct ⊗[Bt] Dg →ₐ[Bt] Ct ⊗[Bt] Cg :=
    Algebra.TensorProduct.map (AlgHom.id Bt Ct) (ψr.restrictScalars Bt)
  have eθ : Spec.map (CommRingCat.ofHom Θ.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (algebraMap Ct (Ct ⊗[Bt] Dg))) ≫ eU.inv) =
      Spec.map (CommRingCat.ofHom (algebraMap Ct (Ct ⊗[Bt] Cg))) ≫ eU.inv := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext x
    simp [Θ]
  let θ : R ⟶ W := homOfComp B S hS rU wU (Spec.map (CommRingCat.ofHom Θ.toRingHom)) eθ
  have hψs : (BigFppfOver.toScheme B S hS).map ψ = Spec.map (CommRingCat.ofHom ψr.toRingHom) :=
    toScheme_map_homOfComp B S hS _ _ _ _
  have hwVs : (BigFppfOver.toScheme B S hS).map wV =
      Spec.map (CommRingCat.ofHom incRD.toRingHom) := toScheme_map_homOfComp B S hS _ _ _ _
  have hrGs : (BigFppfOver.toScheme B S hS).map rG =
      Spec.map (CommRingCat.ofHom incRC.toRingHom) := toScheme_map_homOfComp B S hS _ _ _ _
  have hθs : (BigFppfOver.toScheme B S hS).map θ =
      Spec.map (CommRingCat.ofHom Θ.toRingHom) := toScheme_map_homOfComp B S hS _ _ _ _
  -- the two cartesian squares
  have hsq : ∀ (E : Type u) [CommRing E] [Algebra Bt E],
      IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Ct (Ct ⊗[Bt] E))) ≫ eU.inv)
        (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight (R := Bt) (A := Ct) (B := E)).toRingHom))
        πs (Spec.map (CommRingCat.ofHom (algebraMap Bt E)) ≫ eT.inv) := by
    intro E _ _
    have hT := isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_tensorProduct Bt Ct E)
    refine IsPullback.of_iso hT (Iso.refl _) eU.symm (Iso.refl _) eT.symm ?_ ?_ ?_ ?_
    · exact (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact hπs.symm
    · exact (Category.id_comp _).symm
  have hWsq : IsPullback ((BigFppfOver.toScheme B S hS).map wU)
      ((BigFppfOver.toScheme B S hS).map wV) πs ((BigFppfOver.toScheme B S hS).map (v ≫ ι)) := by
    rw [hvι, hwVs]
    exact hsq Dg
  have hRsq : IsPullback ((BigFppfOver.toScheme B S hS).map rU)
      ((BigFppfOver.toScheme B S hS).map rG) πs ((BigFppfOver.toScheme B S hS).map (j ≫ π)) := by
    rw [hjπ, hrGs]
    exact hsq Cg
  have hθiso : IsIso ((BigFppfOver.toScheme B S hS).map θ) := by
    have : IsIso (CommRingCat.ofHom Θ.toRingHom) :=
      (RingEquiv.ofBijective Θ hbij).toCommRingCatIso.isIso_hom
    rw [hθs]
    exact inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom Θ.toRingHom)))
  have hθV : θ ≫ wV = rG ≫ ψ := by
    apply BigFppfOver.map_toScheme_injective B S hS
    show (BigFppfOver.toScheme B S hS).map (θ ≫ wV) = (BigFppfOver.toScheme B S hS).map (rG ≫ ψ)
    rw [Functor.map_comp, Functor.map_comp, hθs, hwVs, hrGs, hψs]
    have e : Spec.map (CommRingCat.ofHom Θ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom incRD.toRingHom) =
        Spec.map (CommRingCat.ofHom incRC.toRingHom) ≫
          Spec.map (CommRingCat.ofHom ψr.toRingHom) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
    exact e
  have hvs : Surjective ((BigFppfOver.toScheme B S hS).map v) := ⟨hSurj⟩
  have key := isAffineSpace_pullback_of_isIso_chart B S hS hX f a has hae π hπ ι
    (inferInstance : IsAffine (Spec (.of Bg))) v hvEt hvs (inferInstance : IsAffine (Spec (.of Dg)))
    j ψ (homOfComp_comp B S hS _ _ _ _).symm (inferInstance : IsAffine (Spec (.of Cg)))
    wU wV hWsq rU rG hRsq θ hθiso (homOfComp_comp B S hS _ _ _ _) hθV
  have hιs : (BigFppfOver.toScheme B S hS).map ι =
      Spec.map (CommRingCat.ofHom (algebraMap Bt Bg)) ≫ eT.inv := rfl
  have hoi : AlgebraicGeometry.IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap Bt Bg)) ≫ eT.inv) := by
    have := IsOpenImmersion.of_isLocalization (S := Bg) g
    infer_instance
  refine ⟨T', ι, hoi, key, ?_⟩
  · have hmem : PrimeSpectrum.comap (algebraMap Bt Ct) u₀ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Bt Bg)) := by
      rw [PrimeSpectrum.localization_away_comap_range Bg g]
      exact hg
    obtain ⟨y, hy⟩ := hmem
    refine ⟨y, ?_⟩
    have hπs' : πs = eU.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Bt Ct)) ≫ eT.inv := by
      rw [← hπs, Iso.hom_inv_id_assoc]
    show (Spec.map (CommRingCat.ofHom (algebraMap Bt Bg)) ≫ eT.inv) y = πs y₀
    rw [hπs']
    simp only [Scheme.Hom.comp_apply]
    exact congrArg eT.inv hy

/-- **The image of a representable open subspace lies in the schematic locus.** If
`j : O ⟶ X` is an open immersion into an algebraic space and `O` is represented by an object of
the site, then every point of `X` in the image of `j` lies in the schematic locus of `X`. -/
theorem range_pointsMap_subset_schematicLocus_of_isOpenImmersion
    {O X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    [O.IsRepresentable] (j : O ⟶ X) (hj : IsOpenImmersion B S hS j) :
    Set.range (pointsMap B S hS O j) ⊆
      Set.range (pointsMap B S hS (schematicLocus B S hS X).toFunctor
        (schematicLocus B S hS X).ι) := by
  classical
  set Q := MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))
  set χ := O.reprW.hom ≫ j with hχ
  have hχopen : IsOpenImmersion B S hS χ :=
    MorphismProperty.RespectsIso.precomp Q O.reprW.hom _ hj
  have hχetale : (MorphismProperty.inverseImage (@Etale.{u})
      (BigFppfOver.toScheme B S hS)).presheaf χ :=
    presheaf_etale_of_isOpenImmersion B S hS hχopen
  obtain ⟨K, ψ, hKopen, hψχ, hψsurj, -, hKimage⟩ :=
    exists_isOpenSubspace_etaleImage B S hS hX O.reprX χ hχetale
  have hψopen : IsOpenImmersion B S hS ψ :=
    isOpenImmersion_of_comp_mono B S hS ψ K.ι (by rwa [hψχ])
  have hψiso : IsIso ψ :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS ψ hψopen hψsurj
  have hKrep : K.toFunctor.IsRepresentable := Functor.IsRepresentable.mk' (asIso ψ)
  have hsurjε : Function.Surjective (pointsMap B S hS (yoneda.obj O.reprX) O.reprW.hom) := by
    intro z
    refine ⟨pointsMap B S hS O O.reprW.inv z, ?_⟩
    have := congrFun (pointsMap_comp B S hS O O.reprW.inv O.reprW.hom) z
    simp only [Iso.inv_hom_id, Function.comp_apply] at this
    rw [← this]
    simp [pointsMap_id]
  have hrange : Set.range (pointsMap B S hS O j) =
      Set.range (pointsMap B S hS K.toFunctor K.ι) := by
    rw [hKimage, hχ, pointsMap_comp, Set.range_comp, hsurjε.range_eq, Set.image_univ]
  rw [hrange]
  exact range_pointsMap_ι_le_schematicLocus B S hS K hKopen hKrep

/-- An open immersion of algebraic spaces carries the schematic locus of its source into that of
its target. -/
theorem mem_range_pointsMap_schematicLocus_of_isOpenImmersion
    {O X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hO : IsAlgebraicSpace B S hS O) (j : O ⟶ X) (hj : IsOpenImmersion B S hS j)
    {o : points B S hS O}
    (ho : o ∈ Set.range (pointsMap B S hS (schematicLocus B S hS O).toFunctor
      (schematicLocus B S hS O).ι)) :
    pointsMap B S hS O j o ∈ Set.range (pointsMap B S hS (schematicLocus B S hS X).toFunctor
      (schematicLocus B S hS X).ι) := by
  obtain ⟨hGopen, hGrep⟩ :=
    isOpenSubspace_and_isRepresentable_schematicLocus_of_isAlgebraicSpace B S hS hO
  have hk : IsOpenImmersion B S hS ((schematicLocus B S hS O).ι ≫ j) := by
    have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).IsMultiplicative := inferInstance
    exact MorphismProperty.comp_mem _ _ _ hGopen.2 hj
  obtain ⟨g, rfl⟩ := ho
  refine range_pointsMap_subset_schematicLocus_of_isOpenImmersion B S hS hX _ hk ⟨g, ?_⟩
  rw [pointsMap_comp, Function.comp_apply]

attribute [local instance] pointTopology in
/-- **An algebraic space with a flat monomorphism to an object of the site is a scheme.** -/
theorem isRepresentable_of_isFlat_of_mono {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {T : BigFppfOver B S hS} (f : X ⟶ yoneda.obj T) [Mono f]
    (hf : IsFlat B S hS f) : X.IsRepresentable := by
  classical
  refine isRepresentable_of_surjective_pointsMap_schematicLocus B S hS hX fun x => ?_
  -- an affine open neighbourhood of the image of `x`
  set t := schemePointsHomeomorph B S hS T (pointsMap B S hS X f x) with ht
  obtain ⟨Uo, hUo, htUo, -⟩ := exists_isAffineOpen_mem_and_subset (x := t) (U := ⊤) trivial
  let T₁ := openSiteObject B S hS T Uo
  let ι₁ : T₁ ⟶ T := openSiteObjectHom B S hS T Uo
  have hι₁ : (BigFppfOver.toScheme B S hS).map ι₁ = Uo.ι := map_openSiteObjectHom B S hS T Uo
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₁) := hUo
  -- the base change `X₁ = X ×_T T₁`, an open subspace of `X`
  let X₁ := pullback f (yoneda.map ι₁)
  let f₁ : X₁ ⟶ yoneda.obj T₁ := pullback.snd f (yoneda.map ι₁)
  let j₁ : X₁ ⟶ X := pullback.fst f (yoneda.map ι₁)
  have hpb₁ := IsPullback.of_hasPullback f (yoneda.map ι₁)
  have hX₁ : IsAlgebraicSpace B S hS X₁ :=
    isAlgebraicSpace_pullback B S hS f (yoneda.map ι₁) hX (isAlgebraicSpace_yoneda B S hS T₁)
      (isAlgebraicSpace_yoneda B S hS T)
  have hι₁open : IsOpenImmersion B S hS (yoneda.map ι₁) := by
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ι₁).2 ?_
    show AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map ι₁)
    rw [hι₁]
    exact (inferInstance : AlgebraicGeometry.IsOpenImmersion Uo.ι)
  have hj₁ : IsOpenImmersion B S hS j₁ := presheaf_of_isPullback B S hS hpb₁.flip hι₁open
  have hf₁ : IsFlat B S hS f₁ :=
    isFlat_of_isPullback_of_isAlgebraicSpace B S hS hpb₁.flip hX
      (isAlgebraicSpace_yoneda B S hS T) hf
  -- a point of `X₁` over `x`
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : (BigFppfOver.toScheme B S hS).obj T₁,
      (BigFppfOver.toScheme B S hS).map ι₁ t₁ = t := by
    rw [hι₁]
    have : t ∈ Set.range Uo.ι := by rw [Scheme.Opens.range_ι]; exact htUo
    exact this
  obtain ⟨x₁, -, hx₁⟩ := exists_point_of_isPullback_presheaf B S hS hpb₁.flip
    ((schemePointsHomeomorph B S hS T₁).symm t₁) x (by
      rw [schemePointsHomeomorph_symm_naturality, ht₁, ht, Homeomorph.symm_apply_apply])
  -- a quasi-compact open neighbourhood of `x₁` and an affine chart of it
  obtain ⟨W, hW, hWqc, w, hw⟩ :=
    exists_isOpenSubspace_isQuasiCompactSpace_pointsMap_eq B S hS hX₁ x₁
  obtain ⟨U, a, hU, has, hae⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hW.1).1 hWqc
  have hae' := (isEtale_iff_presheaf_of_yoneda B S hS a).1 hae
  let fW : W.toFunctor ⟶ yoneda.obj T₁ := W.ι ≫ f₁
  have hWet := presheaf_etale_of_isOpenImmersion B S hS hW.2
  have hfW : IsFlat B S hS fW := by
    intro U' V' a' b h ha' hb hcomm
    have := isMultiplicative_presheaf_etale B S hS
    exact hf₁ U' V' (a' ≫ W.ι) b h (MorphismProperty.comp_mem _ _ _ ha' hWet) hb
      (by rw [hcomm, Category.assoc])
  have : Mono fW := mono_comp _ _
  -- the scheme point of the chart over `w`
  obtain ⟨u', hu'⟩ := isSurjective_of_presheafSurjective B S hS a has w
  obtain ⟨T', ι, hι, haff, hmem⟩ := exists_isAffineSpace_pullback_of_isFlat_of_mono B S hS hW.1
    fW hfW a has hae' (schemePointsHomeomorph B S hS U u')
  -- the base change `W ×_{T₁} T'`, a representable open subspace of `W` containing `w`
  let O := pullback fW (yoneda.map ι)
  have hpbO := IsPullback.of_hasPullback fW (yoneda.map ι)
  have hιopen : IsOpenImmersion B S hS (yoneda.map ι) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ ι).2 hι
  have hjO : IsOpenImmersion B S hS (pullback.fst fW (yoneda.map ι)) :=
    presheaf_of_isPullback B S hS hpbO.flip hιopen
  obtain ⟨T'', -, ⟨eO⟩⟩ := haff
  have : O.IsRepresentable := Functor.IsRepresentable.mk' eO.symm
  obtain ⟨y', hy'⟩ := hmem
  have hπ' : yoneda.map (yoneda.preimage (a ≫ fW)) = a ≫ fW := yoneda.map_preimage _
  obtain ⟨o, -, ho⟩ := exists_point_of_isPullback_presheaf B S hS hpbO.flip
    ((schemePointsHomeomorph B S hS T').symm y') w (by
      rw [schemePointsHomeomorph_symm_naturality, hy', ← hu', ← pointsMap_comp_apply, ← hπ',
        ← schemePointsHomeomorph_symm_naturality, Homeomorph.symm_apply_apply,
        Functor.preimage_map])
  have hwmem := range_pointsMap_subset_schematicLocus_of_isOpenImmersion B S hS hW.1 _ hjO ⟨o, ho⟩
  have hx₁mem := mem_range_pointsMap_schematicLocus_of_isOpenSubspace B S hS hX₁ hW hwmem
  rw [hw] at hx₁mem
  have := mem_range_pointsMap_schematicLocus_of_isOpenImmersion B S hS hX hX₁ j₁ hj₁ hx₁mem
  rwa [hx₁] at this

/-- **Stacks 0B8A** (David Rydh). A flat monomorphism of algebraic spaces is representable by
schemes. -/
@[stacks 0B8A]
theorem relativelyRepresentable_of_isFlat_of_mono {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) [Mono f]
    (hf : IsFlat B S hS f) : yoneda.relativelyRepresentable f := by
  intro T g
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    isAlgebraicSpace_pullback B S hS g f (isAlgebraicSpace_yoneda B S hS T) hX hY
  have hflat : IsFlat B S hS (pullback.fst g f) :=
    isFlat_of_isPullback_of_isAlgebraicSpace B S hS (IsPullback.of_hasPullback g f) hX hY hf
  have := isRepresentable_of_isFlat_of_mono B S hS hP (pullback.fst g f) hflat
  let e := (pullback g f).reprW
  refine ⟨(pullback g f).reprX, yoneda.preimage (e.hom ≫ pullback.fst g f),
    e.hom ≫ pullback.snd g f, ?_⟩
  rw [yoneda.map_preimage]
  exact (IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e (by simp) (by simp)).flip

end AlgebraicGeometry.Space

end
