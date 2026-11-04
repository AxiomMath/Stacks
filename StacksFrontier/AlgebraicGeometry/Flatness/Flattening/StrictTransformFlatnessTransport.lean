module

public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Flat
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.LocallyPrincipalComplementAffine
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.SupportedSectionsFlatPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.EtaleBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.PullbackFlatness
public import StacksFrontier.AlgebraicGeometry.StrictTransform.CompositionBlowUp
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Quasicoherent

/-!
# Moving flatness of a strict transform around

This file collects the ways in which flatness of the strict transform of a quasi-coherent module
over the blowup of the base is transported: along an isomorphism of the module, along an
enlargement of the centre by a second factor, and along an étale localization of the base
together with a flat localization of the source.

The last of these is the mechanism by which the étale-local flattening statement
[Stacks, Tag 0814] is checked pointwise. It rests on the fact that the strict transform commutes
with flat pullback, which is `Stacks.SupportedQuotient` of
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/SupportedSectionsFlatPullback.lean`: the open
complement of the exceptional preimage has affine inclusion because the exceptional ideal is an
effective Cartier divisor ([Stacks, Tag 07ZT]).

## Main results

* `AlgebraicGeometry.isFlatOver_strictTransformSheaf_of_isFlatOver`: a module flat over the base
  has flat strict transform, for any centre. This is [Stacks, Tag 080F] part (2) plus
  [Stacks, Tag 01U8].
* `AlgebraicGeometry.isFlatOver_strictTransformSheaf_mul`: if the strict transform in `I` is flat
  then so is the strict transform in `I * J`, for every second centre `J`. This is the
  combination of [Stacks, Tag 080A] and [Stacks, Tag 080I] with the previous item.
* `AlgebraicGeometry.exists_isFlatOverAt_strictTransformSheaf_iff_of_etale`: for an étale base
  change `e` and a compatible flat source change `j`, the strict transform of `j^* F` in `I·𝒪`
  *is* the pullback of the strict transform of `F` in `I` along the induced morphism `k` of base
  changes; in particular flatness of one at a point is flatness of the other at its image.
  This is [Stacks, Tag 0805] plus [Stacks, Tag 05B9] plus [Stacks, Tag 02JZ].
* `AlgebraicGeometry.isFlatOver_strictTransformSheaf_restrict`: the case of an open immersion of
  the base, which is the instance of the previous item used to shrink the base.
* `AlgebraicGeometry.exists_isOpenImmersion_strictTransformSheaf_iso_restrict`: **forming the
  strict transform commutes with restricting the base to an open.** The morphism of base changes
  is then an open immersion, and the strict transform upstairs is the restriction of the strict
  transform downstairs along it.

## Implementation notes

The strict transform used is `Stacks.StrictTransform.sheaf` at `b = AlgebraicGeometry.blowUpToBase`
and `E = AlgebraicGeometry.exceptionalIdeal`, which is the vocabulary [Stacks, Tag 080F] and
[Stacks, Tag 080I] are stated in. The parallel construction `Stacks.Blowup.strictTransformSheaf`
is hard-wired to the other model of the blowup and is not used here.

The support identity that [Stacks, Tag 080I] consumes for the composite centre `I * J` is
`AlgebraicGeometry.supportSet_mul_eq_union_image_comap`, which lives with the rest of the
composite-centre material in
`StacksFrontier/AlgebraicGeometry/Blowup/CompositeCentre.lean`.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 01U8](https://stacks.math.columbia.edu/tag/01U8)
* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
* [Stacks Project, Tag 05B9](https://stacks.math.columbia.edu/tag/05B9)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### Flat modules have flat strict transform -/

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
private instance isQuasicoherent_pullback_obj {Y Z : Scheme.{u}} (g : Y ⟶ Z) (F : Z.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
    g.toLRSHom.toShHom F ‹F.IsQuasicoherent›

/-- **A module flat over the base has flat strict transform.** The strict transform of a module
flat over `S` is its pullback to the base change ([Stacks, Tag 080F] part (2)), and flatness is
stable under that base change ([Stacks, Tag 01U8]). -/
theorem isFlatOver_strictTransformSheaf_of_isFlatOver (f : X ⟶ S) (I : S.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (hF : IsFlatOver f.toLRSHom.toShHom F) :
    IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) := by
  have hiso : IsIso (Stacks.StrictTransform.π f (blowUpToBase I) (exceptionalIdeal I) F) :=
    isIso_strictTransformSheaf_quotient_of_flat_at_exceptional f I F fun x _ ↦ hF x
  let Fm : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) := F
  have : Fm.IsQuasicoherent := ‹F.IsQuasicoherent›
  exact fun x ↦ isFlatOverAt_of_moduleIso _ (@asIso _ _ _ _ _ hiso) x
    (modulePullback_isFlatOver (IsPullback.of_hasPullback f (blowUpToBase I)) Fm hF x)

/-! ### Transport along isomorphisms -/

/-- Flatness of a module over a base is unchanged by isomorphisms of both schemes and of the
module: an isomorphism of the base is étale, so [Stacks, Tag 05B9] applies, and an isomorphism of
the source is flat and surjective, so [Stacks, Tag 02JZ] applies. -/
theorem isFlatOver_iff_of_schemeIsos {X T X' T' : Scheme.{u}} (g : X ⟶ T) (g' : X' ⟶ T')
    (eX : X ≅ X') (eT : T ≅ T') (hcomm : g ≫ eT.hom = eX.hom ≫ g')
    (G : X.Modules) (G' : X'.Modules) [G.IsQuasicoherent] [G'.IsQuasicoherent]
    (eG : G ≅ (Scheme.Modules.pullback eX.hom).obj G') :
    IsFlatOver g.toLRSHom.toShHom G ↔ IsFlatOver g'.toLRSHom.toShHom G' := by
  have hModule : IsFlatOver (g ≫ eT.hom).toLRSHom.toShHom G ↔
      IsFlatOver (g ≫ eT.hom).toLRSHom.toShHom ((Scheme.Modules.pullback eX.hom).obj G') :=
    forall_congr' fun x ↦ isFlatOverAt_iff_of_moduleIso (g ≫ eT.hom).toLRSHom.toShHom eG x
  have hcomm' : IsFlatOver (eX.hom ≫ g').toLRSHom.toShHom
        ((Scheme.Modules.pullback eX.hom).obj G') ↔
      IsFlatOver (g ≫ eT.hom).toLRSHom.toShHom
        ((Scheme.Modules.pullback eX.hom).obj G') := by rw [hcomm]
  exact (isFlatOver_comp_iff_of_etale g eT.hom G).symm.trans (hModule.trans
    (hcomm'.symm.trans (isFlatOver_iff_modulePullback_isFlatOver eX.hom g' G').symm))

/-- Flatness of the strict transform depends on the module only up to isomorphism. -/
theorem isFlatOver_strictTransformSheaf_of_iso (f : X ⟶ S) (I : S.IdealSheafData)
    {F G : X.Modules} (e : F ≅ G)
    (h : IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) :
    IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) G) :=
  fun x ↦ isFlatOverAt_of_moduleIso _
    (Stacks.SupportedQuotient.supportedSectionsCokernelIso
      (Stacks.StrictTransform.exceptionalPreimage f (blowUpToBase I) (exceptionalIdeal I))
      ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).mapIso e)) x (h x)

/-! ### Enlarging the centre -/

/-- Flatness of the strict transform transports along an isomorphism of the two-step blowup with
a one-step blowup in a centre with the right support. The first strict transform being flat over
the first blowup, the second strict transform of it is its pullback ([Stacks, Tag 080F] part (2)),
hence flat over the two-step blowup ([Stacks, Tag 01U8]); and [Stacks, Tag 080I] identifies that
iterated strict transform with the one-step strict transform in the third centre. -/
theorem isFlatOver_strictTransformSheaf_transport_comp (f : X ⟶ S) (I K : S.IdealSheafData)
    (J : (blowUp I).IdealSheafData)
    (hK : K.supportSet = I.supportSet ∪ (blowUpToBase I).base '' J.supportSet)
    (e : Over.mk (blowUpToBase J ≫ blowUpToBase I) ≅ Over.mk (blowUpToBase K))
    (F : X.Modules) [F.IsQuasicoherent]
    (hflat : IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) :
    IsFlatOver (pullback.snd f (blowUpToBase K)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase K) (exceptionalIdeal K) F) := by
  set f₁ : Stacks.StrictTransform.baseChange f (blowUpToBase I) ⟶ blowUp I :=
    pullback.snd f (blowUpToBase I)
  set QI := Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F
  have : QI.IsQuasicoherent := inferInstance
  have : (Stacks.StrictTransform.sheaf f₁ (blowUpToBase J)
      (exceptionalIdeal J) QI).IsQuasicoherent := inferInstance
  have : (Stacks.StrictTransform.sheaf f (blowUpToBase K)
      (exceptionalIdeal K) F).IsQuasicoherent := inferInstance
  obtain ⟨g, -, hq, eQ, -⟩ :=
    Stacks.StrictTransform.strictTransformSheaf_comp_blowUp f I K J hK e F
  exact (isFlatOver_iff_of_schemeIsos (pullback.snd f₁ (blowUpToBase J))
    (pullback.snd f (blowUpToBase K)) g ((Over.forget S).mapIso e) hq.symm
    (Stacks.StrictTransform.sheaf f₁ (blowUpToBase J) (exceptionalIdeal J) QI)
    (Stacks.StrictTransform.sheaf f (blowUpToBase K) (exceptionalIdeal K) F) eQ.symm).mp
    (isFlatOver_strictTransformSheaf_of_isFlatOver f₁ J QI hflat)

/-- **Enlarging the centre preserves flatness of the strict transform.** If the strict transform
of `F` in the centre `I` is flat over the blowup of `S` in `I`, then for every second centre `J`
the strict transform of `F` in `I * J` is flat over the blowup of `S` in `I * J`. -/
theorem isFlatOver_strictTransformSheaf_mul (f : X ⟶ S) (I J : S.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent]
    (hflat : IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) :
    IsFlatOver (pullback.snd f (blowUpToBase (I * J))).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase (I * J)) (exceptionalIdeal (I * J)) F) :=
  isFlatOver_strictTransformSheaf_transport_comp f I (I * J) (J.comap (blowUpToBase I))
    (supportSet_mul_eq_union_image_comap I J) (blowUpMulIso I J) F hflat

/-! ### Étale localization of the base -/

/-- The inclusion of the inverse image of an open with affine inclusion has affine inclusion. -/
theorem isAffineHom_preimage_ι {Y T : Scheme.{u}} (g : Y ⟶ T) (V : T.Opens) [IsAffineHom V.ι] :
    IsAffineHom (g ⁻¹ᵁ V).ι :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (isPullback_morphismRestrict g V)
    inferInstance

/-- For a morphism `k` of base changes lying over a morphism `b` of blowups compatible with `e`,
the inverse image under `k` of the exceptional preimage downstairs is the exceptional preimage
upstairs. -/
theorem preimage_compl_exceptionalComplement_eq_of_comp_snd {Y T : Scheme.{u}} (f : X ⟶ S)
    (f' : Y ⟶ T) (e : T ⟶ S) (I : S.IdealSheafData) (b : blowUp (I.comap e) ⟶ blowUp I)
    (hb : blowUpToBase (I.comap e) ≫ e = b ≫ blowUpToBase I)
    (k : Stacks.StrictTransform.baseChange f' (blowUpToBase (I.comap e)) ⟶
      Stacks.StrictTransform.baseChange f (blowUpToBase I))
    (hkq : k ≫ pullback.snd f (blowUpToBase I) = pullback.snd f' (blowUpToBase (I.comap e)) ≫ b) :
    k.base ⁻¹' ((Stacks.StrictTransform.exceptionalComplement f (blowUpToBase I)
        (exceptionalIdeal I) : Set (Stacks.StrictTransform.baseChange f (blowUpToBase I))))ᶜ =
      Stacks.StrictTransform.exceptionalPreimage f' (blowUpToBase (I.comap e))
        (exceptionalIdeal (I.comap e)) := by
  rw [← Stacks.StrictTransform.exceptionalPreimage_eq_compl]
  change k.base ⁻¹' ((pullback.snd f (blowUpToBase I)).base ⁻¹'
      ((I.comap (blowUpToBase I)).support : Set (blowUp I))) =
    (pullback.snd f' (blowUpToBase (I.comap e))).base ⁻¹'
      (((I.comap e).comap (blowUpToBase (I.comap e))).support : Set (blowUp (I.comap e)))
  simp only [Scheme.IdealSheafData.support_comap]
  refine Set.ext fun y ↦ ?_
  have h₁ : pullback.snd f (blowUpToBase I) (k y) =
      b (pullback.snd f' (blowUpToBase (I.comap e)) y) := congrArg (fun a ↦ a y) hkq
  have h₂ : e (blowUpToBase (I.comap e) (pullback.snd f' (blowUpToBase (I.comap e)) y)) =
      blowUpToBase I (b (pullback.snd f' (blowUpToBase (I.comap e)) y)) :=
    congrArg (fun a ↦ a (pullback.snd f' (blowUpToBase (I.comap e)) y)) hb
  change blowUpToBase I (pullback.snd f (blowUpToBase I) (k y)) ∈ I.support ↔
    e (blowUpToBase (I.comap e) (pullback.snd f' (blowUpToBase (I.comap e)) y)) ∈ I.support
  rw [h₁, h₂]

/-- For a flat morphism `k` of base changes lying over the source change `j` and a morphism `b`
of blowups compatible with `e`, the pullback along `k` of the strict transform of `F` in `I` is
the strict transform of `j^* F` in `I·𝒪_T`. -/
theorem nonempty_pullback_strictTransformSheaf_iso_of_flat {Y T : Scheme.{u}} (f : X ⟶ S)
    (f' : Y ⟶ T) (e : T ⟶ S) (j : Y ⟶ X) (I : S.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (b : blowUp (I.comap e) ⟶ blowUp I)
    (hb : blowUpToBase (I.comap e) ≫ e = b ≫ blowUpToBase I)
    (k : Stacks.StrictTransform.baseChange f' (blowUpToBase (I.comap e)) ⟶
      Stacks.StrictTransform.baseChange f (blowUpToBase I)) [Flat k]
    (hkp : k ≫ pullback.fst f (blowUpToBase I) = pullback.fst f' (blowUpToBase (I.comap e)) ≫ j)
    (hkq : k ≫ pullback.snd f (blowUpToBase I) = pullback.snd f' (blowUpToBase (I.comap e)) ≫ b) :
    Nonempty ((Scheme.Modules.pullback k).obj
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) ≅
      Stacks.StrictTransform.sheaf f' (blowUpToBase (I.comap e))
        (exceptionalIdeal (I.comap e)) ((Scheme.Modules.pullback j).obj F)) := by
  have : IsAffineHom (Scheme.Opens.ι (exceptionalIdeal I).support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal I)
  have : IsAffineHom (Stacks.StrictTransform.exceptionalComplement f (blowUpToBase I)
      (exceptionalIdeal I)).ι :=
    isAffineHom_preimage_ι (pullback.snd f (blowUpToBase I)) (exceptionalIdeal I).support.compl
  refine ⟨?_⟩
  change (Scheme.Modules.pullback k).obj (cokernel (supportedSectionsι
      (Stacks.StrictTransform.exceptionalPreimage f (blowUpToBase I) (exceptionalIdeal I))
      ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F))) ≅ _
  rw [Stacks.StrictTransform.exceptionalPreimage_eq_compl f (blowUpToBase I) (exceptionalIdeal I)]
  refine Stacks.SupportedQuotient.flatPullbackSupportedSectionsCokernelIso k
    (Stacks.StrictTransform.exceptionalComplement f (blowUpToBase I) (exceptionalIdeal I))
    ((Scheme.Modules.pullback (pullback.fst f (blowUpToBase I))).obj F) ≪≫ ?_
  rw [preimage_compl_exceptionalComplement_eq_of_comp_snd f f' e I b hb k hkq]
  exact Stacks.SupportedQuotient.supportedSectionsCokernelIso _
    ((Scheme.Modules.pullbackComp k _).app F ≪≫ (Scheme.Modules.pullbackCongr hkp).app F ≪≫
      ((Scheme.Modules.pullbackComp _ j).app F).symm)

/-- **The strict transform and an étale localization of the base.** Let `e : T ⟶ S` be étale, let
`j : Y ⟶ X` be flat, and let `j ≫ f = f' ≫ e`. Then the base change of the blowup of `S` in `I`
along `e` is the blowup of `T` in `I·𝒪_T` ([Stacks, Tag 0805]), and there is a canonical morphism
`k` from the upstairs base change to the downstairs one making a cartesian square with `j`, such
that

* the strict transform of `j^* F` in `I·𝒪_T` is the pullback along `k` of the strict transform of
  `F` in `I`, and
* consequently flatness of the strict transform of `j^* F` in `I·𝒪_T` at a point `y` is exactly
  flatness of the strict transform of `F` in `I` at `k(y)`.

The identification of the two strict transforms is
`Stacks.SupportedQuotient.flatPullbackSupportedSectionsCokernelIso`; the passage between the two
bases is [Stacks, Tag 05B9] and the passage between the two sources is [Stacks, Tag 02JZ]. -/
theorem exists_isFlatOverAt_strictTransformSheaf_iff_and_iso_of_etale {Y T : Scheme.{u}}
    (f : X ⟶ S) (f' : Y ⟶ T) (e : T ⟶ S) (j : Y ⟶ X) [Etale e] [Flat j] (hcomm : j ≫ f = f' ≫ e)
    (I : S.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] :
    ∃ k : Stacks.StrictTransform.baseChange f' (blowUpToBase (I.comap e)) ⟶
        Stacks.StrictTransform.baseChange f (blowUpToBase I),
      IsPullback (pullback.fst f' (blowUpToBase (I.comap e))) k j
        (pullback.fst f (blowUpToBase I)) ∧
      Nonempty ((Scheme.Modules.pullback k).obj
          (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) ≅
        Stacks.StrictTransform.sheaf f' (blowUpToBase (I.comap e))
          (exceptionalIdeal (I.comap e)) ((Scheme.Modules.pullback j).obj F)) ∧
      ∀ y : Stacks.StrictTransform.baseChange f' (blowUpToBase (I.comap e)),
        IsFlatOverAt (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
            (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) (k y) ↔
          IsFlatOverAt (pullback.snd f' (blowUpToBase (I.comap e))).toLRSHom.toShHom
            (Stacks.StrictTransform.sheaf f' (blowUpToBase (I.comap e))
              (exceptionalIdeal (I.comap e))
              ((Scheme.Modules.pullback j).obj F)) y := by
  set bI := blowUpToBase I
  set bJ := blowUpToBase (I.comap e)
  set p := pullback.fst f bI
  set q := pullback.snd f bI
  set p' := pullback.fst f' bJ
  set q' := pullback.snd f' bJ
  obtain ⟨b, hb⟩ := exists_isPullback_blowUpToBase_comap e I
  have hkcomm : (p' ≫ j) ≫ f = (q' ≫ b) ≫ bI := by
    calc (p' ≫ j) ≫ f = (p' ≫ f') ≫ e := by rw [Category.assoc, hcomm, Category.assoc]
      _ = (q' ≫ bJ) ≫ e := by rw [pullback.condition]
      _ = (q' ≫ b) ≫ bI := by rw [Category.assoc, hb.w, Category.assoc]
  set k := pullback.lift (p' ≫ j) (q' ≫ b) hkcomm
  have hkp : k ≫ p = p' ≫ j := pullback.lift_fst _ _ _
  have hkq : k ≫ q = q' ≫ b := pullback.lift_snd _ _ _
  have hout : IsPullback p' (k ≫ q) (j ≫ f) bI := by
    rw [hkq, hcomm]
    exact (IsPullback.of_hasPullback f' bJ).paste_vert hb
  have hkpb : IsPullback p' k j p := hout.of_bot hkp.symm (IsPullback.of_hasPullback f bI)
  have : Flat k := MorphismProperty.of_isPullback (P := @Flat) hkpb inferInstance
  have : Etale b := MorphismProperty.of_isPullback (P := @Etale) hb inferInstance
  obtain ⟨eQ⟩ := nonempty_pullback_strictTransformSheaf_iso_of_flat f f' e j I F b hb.w k hkp hkq
  have : (Stacks.StrictTransform.sheaf f' bJ (exceptionalIdeal (I.comap e))
      ((Scheme.Modules.pullback j).obj F)).IsQuasicoherent := inferInstance
  refine ⟨k, hkpb, ⟨eQ⟩, fun y ↦ ?_⟩
  have h₃ : IsFlatOverAt (k ≫ q).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f' bJ (exceptionalIdeal (I.comap e))
          ((Scheme.Modules.pullback j).obj F)) y ↔
      IsFlatOverAt q'.toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f' bJ (exceptionalIdeal (I.comap e))
          ((Scheme.Modules.pullback j).obj F)) y := by
    rw [hkq]
    exact isFlatOverAt_comp_iff_of_etale q' b _ y
  exact (isFlatOverAt_iff_modulePullback_isFlatOverAt k q
      (Stacks.StrictTransform.sheaf f bI (exceptionalIdeal I) F) y (Flat.stalkMap k y)).trans
    ((isFlatOverAt_iff_of_moduleIso (k ≫ q).toLRSHom.toShHom eQ y).trans h₃)

/-- Let `j : Y ⟶ X` be flat and `e : T ⟶ S` étale, with `j ≫ f = f' ≫ e`. There is a morphism
`k` from the base change of `f'` along the blowup of `T` in `I·𝒪_T` to the base change of `f`
along the blowup of `S` in `I`, making a cartesian square with `j`, such that the strict
transform of `j^* F` in `I·𝒪_T` is flat at a point `y` if and only if the strict transform of `F`
in `I` is flat at `k(y)`. -/
theorem exists_isFlatOverAt_strictTransformSheaf_iff_of_etale {Y T : Scheme.{u}} (f : X ⟶ S)
    (f' : Y ⟶ T) (e : T ⟶ S) (j : Y ⟶ X) [Etale e] [Flat j] (hcomm : j ≫ f = f' ≫ e)
    (I : S.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] :
    ∃ k : Stacks.StrictTransform.baseChange f' (blowUpToBase (I.comap e)) ⟶
        Stacks.StrictTransform.baseChange f (blowUpToBase I),
      IsPullback (pullback.fst f' (blowUpToBase (I.comap e))) k j
        (pullback.fst f (blowUpToBase I)) ∧
      ∀ y : Stacks.StrictTransform.baseChange f' (blowUpToBase (I.comap e)),
        IsFlatOverAt (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
            (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) (k y) ↔
          IsFlatOverAt (pullback.snd f' (blowUpToBase (I.comap e))).toLRSHom.toShHom
            (Stacks.StrictTransform.sheaf f' (blowUpToBase (I.comap e))
              (exceptionalIdeal (I.comap e))
              ((Scheme.Modules.pullback j).obj F)) y :=
  (exists_isFlatOverAt_strictTransformSheaf_iff_and_iso_of_etale f f' e j hcomm I F).imp
    fun _ h ↦ ⟨h.1, h.2.2⟩

/-- **Shrinking the base.** If the strict transform of `F` in `I` is flat over the blowup of `S`
in `I`, then over an open `V ⊆ S` the strict transform of the restricted module in the restricted
centre is flat over the blowup of `V` in that centre. This is the instance of
`AlgebraicGeometry.exists_isFlatOverAt_strictTransformSheaf_iff_of_etale` at the open immersion
`V.ι`. -/
theorem isFlatOver_strictTransformSheaf_restrict (f : X ⟶ S) (I : S.IdealSheafData)
    (F : X.Modules) [F.IsQuasicoherent] (V : S.Opens)
    (h : IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F)) :
    IsFlatOver (pullback.snd (f ∣_ V) (blowUpToBase (I.comap V.ι))).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf (f ∣_ V) (blowUpToBase (I.comap V.ι))
        (exceptionalIdeal (I.comap V.ι))
        ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F)) := by
  obtain ⟨k, -, -, hk⟩ := exists_isFlatOverAt_strictTransformSheaf_iff_and_iso_of_etale f
    (f ∣_ V) V.ι (f ⁻¹ᵁ V).ι (morphismRestrict_ι f V).symm I F
  exact fun y ↦ (hk y).mp (h (k y))

/-- **Forming the strict transform commutes with restricting the base to an open.** For `V ⊆ S`
an open, the morphism `k` from the base change over the blowup of `V` in the restricted centre to
the base change over the blowup of `S` in `I` is an open immersion, and the strict transform of
the restricted module in the restricted centre is the restriction along `k` of the strict
transform of `F` in `I`.

This is `AlgebraicGeometry.exists_isFlatOverAt_strictTransformSheaf_iff_of_etale` at the open
immersion `V.ι`, whose source change is the open immersion `(f ⁻¹ᵁ V).ι`; `k` is a base change of
the latter, so it is an open immersion too. -/
theorem exists_isOpenImmersion_strictTransformSheaf_iso_restrict (f : X ⟶ S)
    (I : S.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] (V : S.Opens) :
    ∃ k : Stacks.StrictTransform.baseChange (f ∣_ V) (blowUpToBase (I.comap V.ι)) ⟶
        Stacks.StrictTransform.baseChange f (blowUpToBase I),
      IsOpenImmersion k ∧
      IsPullback (pullback.fst (f ∣_ V) (blowUpToBase (I.comap V.ι))) k (f ⁻¹ᵁ V).ι
        (pullback.fst f (blowUpToBase I)) ∧
      Nonempty ((Scheme.Modules.pullback k).obj
          (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) ≅
        Stacks.StrictTransform.sheaf (f ∣_ V) (blowUpToBase (I.comap V.ι))
          (exceptionalIdeal (I.comap V.ι))
          ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj F)) := by
  obtain ⟨k, hk, hiso, -⟩ := exists_isFlatOverAt_strictTransformSheaf_iff_and_iso_of_etale f
    (f ∣_ V) V.ι (f ⁻¹ᵁ V).ι (morphismRestrict_ι f V).symm I F
  exact ⟨k, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hk inferInstance, hk, hiso⟩

end AlgebraicGeometry

end
