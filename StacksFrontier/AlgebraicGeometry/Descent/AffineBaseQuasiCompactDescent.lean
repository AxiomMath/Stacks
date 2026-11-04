module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineSourceEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.PointSetCoverLocallySurjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Effective descent along surjective étale morphisms over an affine base

Effective descent along the surjective étale morphisms of the big fppf site of `S` reduces, for
descent data whose base object and whose covering object are affine, to the third and fourth
steps of Stacks 02W8. The input that makes this work is that the fibre product of a chart with
itself, for a chart presented as a base change of a quasi-compact morphism of the site, is an
object of the site with quasi-compact first projection.

## Main results

* `AlgebraicGeometry.Space.exists_isPullback_self_of_quasiCompact`: the fibre product of a chart
  with itself, for a chart presented as a base change of a quasi-compact morphism of the site, is
  an object of the site with quasi-compact first projection.
* `AlgebraicGeometry.Space.presheaf_pullback_snd_of_zariskiCover_of_mk_lt_cutoff`: the glueing step
  of Stacks 02W8 at a single descent datum.
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_representable_of_affineBase`:
  **steps 1, 2 and 5 of Stacks 02W8 composed.** Effective descent along the surjective étale
  morphisms of the site follows from the third and fourth steps alone, for data whose base object
  and whose covering object are affine.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
* [Stacks Project, Tag 021U](https://stacks.math.columbia.edu/tag/021U)
* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
-/


@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The fibre product of the chart with itself -/

/-- **The fibre product of a chart with itself, when the covering morphism is quasi-compact.**
Let `g : yoneda.obj U ⟶ X ×[Y] yoneda.obj a` present `yoneda.obj U` as a base change of
`yoneda.map q` along the projection, for a quasi-compact morphism `q : c ⟶ a` of the big fppf site
of `S`. Then the fibre product of `g` with itself is representable by an object of the site, and
its first projection is quasi-compact. -/
theorem exists_isPullback_self_of_quasiCompact
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {a c : BigFppfOver B S hS}
    {h : yoneda.obj a ⟶ Y} {q : c ⟶ a}
    (hq : QuasiCompact ((BigFppfOver.toScheme B S hS).map q))
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ pullback f h}
    {ρ : yoneda.obj U ⟶ yoneda.obj c}
    (sqg : IsPullback g ρ (pullback.snd f h) (yoneda.map q)) :
    ∃ (D : BigFppfOver B S hS) (π₁ π₂ : D ⟶ U),
      IsPullback (yoneda.map π₁) (yoneda.map π₂) g g ∧
        QuasiCompact ((BigFppfOver.toScheme B S hS).map π₁) := by
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hmapρ : yoneda.map (yoneda.preimage ρ) = ρ := Functor.map_preimage _ _
  have sqsite : IsPullback (pullback.fst (yoneda.preimage ρ ≫ q) q)
      (pullback.snd (yoneda.preimage ρ ≫ q) q) (yoneda.preimage ρ ≫ q) q :=
    IsPullback.of_hasPullback _ _
  have sqY := sqsite.map (yoneda (C := BigFppfOver B S hS))
  have hleg : g ≫ pullback.snd f h = yoneda.map (yoneda.preimage ρ ≫ q) := by
    rw [sqg.w, Functor.map_comp, hmapρ]
  rw [← hleg] at sqY
  have hw : (yoneda.map (pullback.fst (yoneda.preimage ρ ≫ q) q) ≫ g) ≫ pullback.snd f h =
      yoneda.map (pullback.snd (yoneda.preimage ρ ≫ q) q) ≫ yoneda.map q := by
    rw [Category.assoc, sqY.w]
  refine ⟨_, pullback.fst (yoneda.preimage ρ ≫ q) q,
    yoneda.preimage (sqg.lift (yoneda.map (pullback.fst (yoneda.preimage ρ ≫ q) q) ≫ g)
      (yoneda.map (pullback.snd (yoneda.preimage ρ ≫ q) q)) hw), ?_, ?_⟩
  · rw [Functor.map_preimage]
    exact IsPullback.of_bot' sqY sqg
  · exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (sqsite.map (BigFppfOver.toScheme B S hS)).flip hq

/-! ### The glueing step at one datum -/

/-- **The glueing step of Stacks 02W8 at a single datum.** Given a descent datum along a
surjective étale morphism of the big fppf site of `S` and a Zariski covering of the descended
sheaf `X ×[Y] yoneda.obj a` by representable open subfunctors indexed by a type of cardinality
below the site's cutoff, the projection `X ×[Y] yoneda.obj a ⟶ yoneda.obj a` is representable
with `P`. -/
theorem presheaf_pullback_snd_of_zariskiCover_of_mk_lt_cutoff
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hY : Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y)
    {a c : BigFppfOver B S hS} (h : yoneda.obj a ⟶ Y) (q : c ⟶ a)
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : A ⟶ X) (r : A ⟶ yoneda.obj c)
    (sq : IsPullback m r f (yoneda.map q ≫ h))
    (hr : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r)
    {ι : Type u} (hι : #ι < B.cutoff) (W : ι → BigFppfOver B S hS)
    (k : ∀ i, yoneda.obj (W i) ⟶ pullback f h) (hk : ∀ i, IsOpenImmersion B S hS (k i))
    (hksurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) (Sigma.desc k)) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f h) := by
  obtain ⟨μ, hμ, hbound⟩ := exists_size_bound_of_descentDatum f h q hqs hqe m r sq hr.rep
  have hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (pullback f h) :=
    BigFppfOver.isSheaf_pullback_yoneda_obj f h hX hY
  have hrep : yoneda.relativelyRepresentable (pullback.snd f h) :=
    relativelyRepresentable_pullback_snd f h
      (isRepresentable_of_zariskiCover_of_size_le B S hS hF hι hμ W
        (fun i => hbound (W i) (k i) (hk i)) k hk hksurj)
  exact presheaf_of_surjectiveEtaleChart_of_descendsAlong hrep
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe)
    (sq.of_right' (IsPullback.of_hasPullback f h)) hr

/-! ### Steps 1, 2 and 5 of Stacks 02W8 composed -/

/-- **Steps 1, 2 and 5 of Stacks 02W8 composed.** Effective descent along the surjective étale
morphisms of the big fppf site of `S` holds for a property `P` as soon as the following holds, for
every descent datum whose base object `a` and whose covering object `c` have affine underlying
schemes. For every object `U` of the site presenting `yoneda.obj U` as a base change of
`yoneda.map q` along the projection `X ×[Y] yoneda.obj a ⟶ yoneda.obj a`, every affine open `T` of
`U`, and the object `b` of the site with an open immersion to `U` whose image is the saturation of
`T` — which is quasi-compact and Cartesian over the open subfunctor cut out by the image of `T` —
that open subfunctor is representable. -/
@[sga "3 X 5.4" "special case"]
theorem isEffectiveDescentAlongSurjectiveEtale_of_representable_of_affineBase
    {P : MorphismProperty Scheme.{u}}
    [P.RespectsIso] [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)]
    (H : ∀ ⦃X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (f : X ⟶ Y),
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) X →
      Presheaf.IsSheaf (BigFppfOver.topology B S hS) Y →
      ∀ ⦃a c : BigFppfOver B S hS⦄ (h : yoneda.obj a ⟶ Y) (q : c ⟶ a),
        IsAffine ((BigFppfOver.toScheme B S hS).obj a) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj c) →
        Surjective ((BigFppfOver.toScheme B S hS).map q) →
        Etale ((BigFppfOver.toScheme B S hS).map q) →
        QuasiCompact ((BigFppfOver.toScheme B S hS).map q) →
        ∀ ⦃A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (m : A ⟶ X) (r : A ⟶ yoneda.obj c),
          IsPullback m r f (yoneda.map q ≫ h) →
          (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r →
          ∀ (U : BigFppfOver B S hS) (g : yoneda.obj U ⟶ pullback f h)
            (ρ : yoneda.obj U ⟶ yoneda.obj c),
            IsPullback g ρ (pullback.snd f h) (yoneda.map q) →
            ∀ (T : ((BigFppfOver.toScheme B S hS).obj U).affineOpens)
              (b : BigFppfOver B S hS) (i : b ⟶ U)
              (k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS (pullback f h)
                (pointsMap B S hS (yoneda.obj U) g ''
                  (pointsToScheme B S hS U ⁻¹'
                    (T : Set _)))).toFunctor),
              _root_.AlgebraicGeometry.IsOpenImmersion
                ((BigFppfOver.toScheme B S hS).map i) →
              Set.range ((BigFppfOver.toScheme B S hS).map i) =
                pointsToScheme B S hS U ''
                  (pointsMap B S hS (yoneda.obj U) g ⁻¹'
                    (pointsMap B S hS (yoneda.obj U) g ''
                      (pointsToScheme B S hS U ⁻¹'
                        (T : Set _)))) →
              IsCompact (pointsToScheme B S hS U ''
                (pointsMap B S hS (yoneda.obj U) g ⁻¹'
                  (pointsMap B S hS (yoneda.obj U) g ''
                    (pointsToScheme B S hS U ⁻¹'
                      (T : Set _))))) →
              IsPullback k (yoneda.map i)
                (openSubspaceOfPoints B S hS (pullback f h)
                  (pointsMap B S hS (yoneda.obj U) g ''
                    (pointsToScheme B S hS U ⁻¹'
                      (T : Set _)))).ι g →
                (openSubspaceOfPoints B S hS (pullback f h)
                  (pointsMap B S hS (yoneda.obj U) g ''
                    (pointsToScheme B S hS U ⁻¹'
                      (T : Set _)))).toFunctor.IsRepresentable) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS P := by
  refine isEffectiveDescentAlongSurjectiveEtale_of_affineBase_affineSource ?_
  intro X Y f hX hY a c h q ha hc hqs hqe hqqc A m r sq hr
  have _ : A.IsRepresentable :=
    Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable r hr.rep
  have sq₂ := sq.of_right' (IsPullback.of_hasPullback f h)
  obtain ⟨g, sq₃⟩ : ∃ g, IsPullback g (A.reprW.hom ≫ r) (pullback.snd f h) (yoneda.map q) :=
    ⟨A.reprW.hom ≫ (IsPullback.of_hasPullback f h).lift m (r ≫ yoneda.map q)
        (by rw [sq.w, Category.assoc]),
      sq₂.of_iso' A.reprW (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp)
        (by simp)⟩
  obtain ⟨D, π₁, π₂, sqD, hπ₁⟩ := exists_isPullback_self_of_quasiCompact hqqc sq₃
  have hg := presheafIsOpenMap_of_isPullback_of_etale B S hS sq₃ hqe
  have hrepT : ∀ T : ((BigFppfOver.toScheme B S hS).obj A.reprX).affineOpens,
      (openSubspaceOfPoints B S hS (pullback f h)
        (pointsMap B S hS (yoneda.obj A.reprX) g ''
          (pointsToScheme B S hS A.reprX ⁻¹' (T : Set _)))).toFunctor.IsRepresentable := by
    intro T
    obtain ⟨b, i, kb, hi, hirange, hsqb⟩ :=
      exists_isPullback_ι_openSubspaceOfPoints_image B S hS _ hg T.1.isOpen
    exact H f hX hY h q ha hc hqs hqe hqqc m r sq hr A.reprX g (A.reprW.hom ≫ r) sq₃ T b i kb hi
      hirange (isCompact_preimage_image_pointsMap B S hS _ sqD hπ₁ T.1.isOpen T.2.isCompact) hsqb
  obtain ⟨ι, hι, W, k, hk, hksurj⟩ := exists_zariskiCover_affineOpens_of_chart B S hS _ hg
    (surjective_pointsMap_of_isPullback_of_surjective B S hS sq₃ hqs) hrepT
  exact presheaf_pullback_snd_of_zariskiCover_of_mk_lt_cutoff f hX hY h q hqs hqe m r sq hr
    hι W k hk hksurj

end AlgebraicGeometry.Space

end
