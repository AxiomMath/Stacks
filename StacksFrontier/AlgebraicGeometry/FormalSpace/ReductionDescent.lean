module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleQuotientPresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionExistence

/-!
# The reduction inclusion is a representable thickening

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` with atlas `{X_i ⟶ X}` by affine formal algebraic spaces, and let `ι : R ⟶ X` be a
monomorphism of fppf sheaves whose base change along each `X_i` is a representable thickening.
Then `ι` is itself a representable thickening.

## Main results

* `AlgebraicGeometry.FormalSpace.isEffectiveDescentAlongSurjectiveEtale_isThickening`:
  effective descent along a surjective étale morphism of the big fppf site holds for thickenings.
* `AlgebraicGeometry.FormalSpace.isRepresentableThickening_of_isPullback_etale_cover`: the
  descent statement.

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

/-- A property respecting isomorphisms which holds for the second leg of a pullback square holds
for the second projection of the chosen pullback. -/
private theorem pullback_snd_of_isPullback {C : Type*} [Category C] {P : MorphismProperty C}
    [P.RespectsIso] {A X Y Z : C} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f g] (h : IsPullback fst snd f g) (hs : P snd) : P (pullback.snd f g) := by
  rw [← (Iso.inv_comp_eq _).2 h.isoPullback_hom_snd.symm]
  exact MorphismProperty.RespectsIso.precomp _ h.isoPullback.inv snd hs

namespace Stacks.Thickenings

universe u

/-- Thickenings of schemes descend along a surjective flat morphism of finite presentation. -/
private instance isThickening_descendsAlong_surjective_inf_flat_inf_lfp :
    MorphismProperty.DescendsAlong (@IsThickening : MorphismProperty AlgebraicGeometry.Scheme.{u})
      (@AlgebraicGeometry.Surjective ⊓ @AlgebraicGeometry.Flat ⊓
        @AlgebraicGeometry.LocallyOfFinitePresentation) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have _ : MorphismProperty.IsLocalAtTarget
        (@IsThickening : MorphismProperty AlgebraicGeometry.Scheme.{u})
        AlgebraicGeometry.Scheme.fppfPrecoverage :=
      MorphismProperty.IsLocalAtTarget.of_le
        AlgebraicGeometry.Scheme.fppfPrecoverage_le_fpqcPrecoverage
    have hmem : Presieve.singleton f ∈ AlgebraicGeometry.Scheme.fppfPrecoverage Z := by
      rw [AlgebraicGeometry.Scheme.fppfPrecoverage]
      exact (AlgebraicGeometry.Scheme.singleton_mem_precoverage_iff _ f).2
        ⟨hf.1.1.surj, hf.1.2, hf.2⟩
    refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hmem ?_
    rintro U gg _ ⟨⟩
    exact pullback_snd_of_isPullback h.flip hfst

end Stacks.Thickenings

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### De-universe-lifting a subobject of a universe-lifted presheaf -/

section DownRange

variable {C : Type*} [Category.{u} C]

/-- The subfunctor of `F₀` whose sections over `T` are those which, lifted one universe up, lie
in the image of a monomorphism `m : Z ⟶ F₀ ⋙ uliftFunctor`. -/
def downRangeSubfunctor {F₀ : Cᵒᵖ ⥤ Type u} {Z : Cᵒᵖ ⥤ Type (u + 1)}
    (m : Z ⟶ F₀ ⋙ uliftFunctor.{u + 1}) : Subfunctor F₀ where
  obj T := {x | ∃ z, m.app T z = ULift.up x}
  map {T T'} h := by
    rintro x ⟨z, hz⟩
    refine ⟨Z.map h z, ?_⟩
    rw [NatTrans.naturality_apply m h z, hz]
    rfl

/-- The universe lift of `AlgebraicGeometry.FormalSpace.downRangeSubfunctor m` is isomorphic to
the source of the monomorphism `m`. -/
noncomputable def downRangeSubfunctorIso {F₀ : Cᵒᵖ ⥤ Type u} {Z : Cᵒᵖ ⥤ Type (u + 1)}
    (m : Z ⟶ F₀ ⋙ uliftFunctor.{u + 1}) [Mono m] :
    Z ≅ (downRangeSubfunctor m).toFunctor ⋙ uliftFunctor.{u + 1} := by
  have hinj (T : Cᵒᵖ) : Function.Injective (m.app T) :=
    (mono_iff_injective (m.app T)).1 ((NatTrans.mono_iff_mono_app m).1 inferInstance T)
  let α : Z ⟶ (downRangeSubfunctor m).toFunctor ⋙ uliftFunctor.{u + 1} :=
    { app T := ↾fun z ↦ ULift.up ⟨(m.app T z).down, ⟨z, rfl⟩⟩
      naturality T T' h := by
        ext z
        apply ULift.ext
        apply Subtype.ext
        change (m.app T' (Z.map h z)).down = _
        rw [NatTrans.naturality_apply m h z]
        rfl }
  have happ (T : Cᵒᵖ) : IsIso (α.app T) := (isIso_iff_bijective _).2
    ⟨fun z z' h ↦ hinj T (ULift.ext (congrArg (fun y ↦ (ULift.down y).1) h)),
      fun ⟨⟨x, z, hz⟩⟩ ↦ ⟨z, ULift.ext (Subtype.ext (congrArg ULift.down hz))⟩⟩
  have _ : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- The comparison isomorphism is compatible with the two inclusions. -/
theorem downRangeSubfunctorIso_hom_comp {F₀ : Cᵒᵖ ⥤ Type u} {Z : Cᵒᵖ ⥤ Type (u + 1)}
    (m : Z ⟶ F₀ ⋙ uliftFunctor.{u + 1}) [Mono m] :
    (downRangeSubfunctorIso m).hom ≫
      Functor.whiskerRight (downRangeSubfunctor m).ι uliftFunctor.{u + 1} = m := by
  ext T z
  rfl

end DownRange

/-- If `Z` is a sheaf, then the subfunctor `AlgebraicGeometry.FormalSpace.downRangeSubfunctor m`
cut out by a monomorphism `m : Z ⟶ F₀ ⋙ uliftFunctor` is a sheaf. -/
theorem isSheaf_downRangeSubfunctor {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C) {F₀ : Cᵒᵖ ⥤ Type u} {Z : Cᵒᵖ ⥤ Type (u + 1)}
    (m : Z ⟶ F₀ ⋙ uliftFunctor.{u + 1}) [Mono m] (hZ : Presheaf.IsSheaf J Z) :
    Presheaf.IsSheaf J (downRangeSubfunctor m).toFunctor := by
  have h : Presheaf.IsSheaf J ((downRangeSubfunctor m).toFunctor ⋙ uliftFunctor.{u + 1}) :=
    (Presheaf.isSheaf_of_iso_iff (downRangeSubfunctorIso m)).1 hZ
  rw [isSheaf_iff_isSheaf_of_type] at h
  rwa [isSheaf_iff_isSheaf_of_type, ← Presieve.isSheaf_comp_uliftFunctor_iff]

/-- If `fst, snd` is a pullback of `f` and `𝟙 Y ≫ g`, it is a pullback of `f` and `g`. -/
private theorem isPullback_of_id_comp {C : Type*} [Category C] {P X Y Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f (𝟙 Y ≫ g)) : IsPullback fst snd f g := by
  rwa [Category.id_comp] at h

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Effective descent for thickenings -/

/-- Effective descent along a surjective étale morphism of the big fppf site of `S` holds for the
thickenings. -/
@[stacks 02W8 "effective descent along a surjective étale chart of the site, for thickenings"]
theorem isEffectiveDescentAlongSurjectiveEtale_isThickening :
    Space.IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) := by
  refine Space.isEffectiveDescentAlongSurjectiveEtale_of_le
    (Space.isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_locallyQuasiFinite_inf_lft
      B S hS) ?_
  intro V W q hq
  have _ : _root_.AlgebraicGeometry.IsClosedImmersion q := hq.1
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

/-! ### Descent of the representable-thickening property -/

/-- Let `X` be a formal algebraic space over `S` with atlas `{X_i ⟶ X}` by affine formal
algebraic spaces and let `ι : R ⟶ X` be a monomorphism of fppf sheaves whose base change along
each `X_i` is a representable thickening. Then `ι` is a representable thickening. -/
theorem isRepresentableThickening_of_isPullback_etale_cover
    [HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS)]
    {X R : FppfSheaf B S hS} (ι : R ⟶ X) (hmono : Mono ι) {I : Type (u + 1)}
    (Xi Ri : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X) (k : ∀ i, Ri i ⟶ R)
    (j : ∀ i, Ri i ⟶ Xi i) (hsq : ∀ i, IsPullback (k i) (j i) ι (f i))
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom) (f i).hom hfi)
    (hcover : Sheaf.IsLocallySurjective (Limits.Sigma.desc f))
    (hj : ∀ i, Space.IsRepresentableThickeningULift.{u + 1} B S hS (j i).hom) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom := by
  classical
  let Hs := BigFppfOver.toScheme B S hS
  let Q := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) Hs
  let Pf := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let Wf : ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ⥤ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
    (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}
  have _ : Q.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  apply MorphismProperty.relative.of_exists
  intro a g₀
  let ga : FppfSheaf B S hS := ⟨(uliftYoneda.{u + 1}).obj a,
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS a).isSheaf⟩
  let g : ga ⟶ X := ⟨g₀⟩
  let m : (pullback ι g).obj ⟶ yoneda.obj a ⋙ uliftFunctor.{u + 1} :=
    Pf.map (pullback.snd ι g)
  have hZP : IsPullback (Pf.map (pullback.fst ι g)) m ι.hom g₀ :=
    (IsPullback.of_hasPullback ι g).map Pf
  have hmonoP : Mono (Pf.map ι) := by
    have _ := hmono
    infer_instance
  have hmm : Mono m :=
    MorphismProperty.of_isPullback (P := MorphismProperty.monomorphisms _) hZP hmonoP
  let G₀ := (downRangeSubfunctor m).toFunctor
  let f₀ : G₀ ⟶ yoneda.obj a := (downRangeSubfunctor m).ι
  let eZ : (pullback ι g).obj ≅ Wf.obj G₀ := downRangeSubfunctorIso m
  have heZ : eZ.hom ≫ Wf.map f₀ = m := downRangeSubfunctorIso_hom_comp m
  obtain ⟨W, V, w, p, v, hwsurj, hwet, hpthick, hvpb⟩ :=
    exists_etale_atlas_of_pullback_thickening B S hS ι Xi Ri f k j hsq hf hcover hj a g₀
  have hvw : v ≫ ι.hom =
      ((uliftYoneda.{u + 1}).map p ≫ (uliftYoneda.{u + 1}).map w) ≫ g₀ :=
    hvpb.w.trans (Category.assoc _ _ _).symm
  let v' : Wf.obj (yoneda.obj V) ⟶ (pullback ι g).obj :=
    hZP.lift v ((uliftYoneda.{u + 1}).map p ≫ (uliftYoneda.{u + 1}).map w) hvw
  have hv'fst : v' ≫ Pf.map (pullback.fst ι g) = v := hZP.lift_fst _ _ _
  have hv'snd : v' ≫ m =
      (uliftYoneda.{u + 1}).map p ≫ (uliftYoneda.{u + 1}).map w := hZP.lift_snd _ _ _
  have hv' : IsPullback v' ((uliftYoneda.{u + 1}).map p) m ((uliftYoneda.{u + 1}).map w) := by
    refine IsPullback.of_right ?_ hv'snd hZP
    rwa [hv'fst]
  have hbig : IsPullback (v' ≫ eZ.hom) ((uliftYoneda.{u + 1}).map p) (Wf.map f₀)
      ((uliftYoneda.{u + 1}).map w) := by
    exact hv'.of_iso (Iso.refl _) eZ (Iso.refl _) (Iso.refl _)
      (Category.id_comp (v' ≫ eZ.hom)).symm
      ((Category.comp_id _).trans (Category.id_comp _).symm) ((Category.comp_id _).trans heZ.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  obtain ⟨i₀, hi₀⟩ := Wf.map_surjective
    (show Wf.obj (yoneda.obj V) ⟶ Wf.obj G₀ from v' ≫ eZ.hom)
  have hsmall : IsPullback i₀ (yoneda.map p) f₀ (yoneda.map w) := by
    have hb : IsPullback (Wf.map i₀) (Wf.map (yoneda.map p)) (Wf.map f₀)
        (Wf.map (yoneda.map w)) := by
      rwa [hi₀]
    refine hb.of_map Wf ?_
    apply Wf.map_injective
    simpa only [Functor.map_comp] using hb.w
  have hqsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) Hs)) (yoneda.map w) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ w).2 hwsurj
  have hqetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) Hs)) (yoneda.map w) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ w).2 hwet
  have hV : Q.presheaf (pullback.snd f₀ (yoneda.map w)) := by
    have hpres : Q.presheaf (yoneda.map p) :=
      MorphismProperty.relative_map (F := yoneda) hpthick
    exact pullback_snd_of_isPullback hsmall hpres
  have h03I2 := Space.isAlgebraicSpace_and_presheaf_of_surjectiveEtaleChart_of_descent
    (P := (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}))
    (isEffectiveDescentAlongSurjectiveEtale_isThickening B S hS)
    (isSheaf_downRangeSubfunctor (BigFppfOver.topology B S hS) m (pullback ι g).property)
    (isAlgebraicSpace_yoneda B S hS a) hqsurj hqetale hV
  have hmQ : Q.relative uliftYoneda.{u + 1} m := by
    have _ : (Q.relative uliftYoneda.{u + 1}).RespectsIso :=
      (MorphismProperty.relative_isStableUnderBaseChange
        (F := uliftYoneda.{u + 1}) Q).respectsIso
    have h1 : Q.relative uliftYoneda.{u + 1} (Wf.map f₀) :=
      Space.relative_ulift_of_presheaf Q f₀ h03I2.2
    have h2 : Q.relative uliftYoneda.{u + 1} (eZ.hom ≫ Wf.map f₀) :=
      MorphismProperty.RespectsIso.precomp _ eZ.hom (Wf.map f₀) h1
    rwa [heZ] at h2
  have hpaste : IsPullback
      (hmQ.rep.fst (𝟙 ((uliftYoneda.{u + 1}).obj a)) ≫ Pf.map (pullback.fst ι g))
      ((uliftYoneda.{u + 1}).map (hmQ.rep.snd (𝟙 ((uliftYoneda.{u + 1}).obj a))))
      ι.hom g₀ :=
    isPullback_of_id_comp
      ((hmQ.rep.isPullback (𝟙 ((uliftYoneda.{u + 1}).obj a))).paste_horiz hZP)
  exact ⟨hmQ.rep.pullback (𝟙 ((uliftYoneda.{u + 1}).obj a)),
    hmQ.rep.fst (𝟙 ((uliftYoneda.{u + 1}).obj a)) ≫ Pf.map (pullback.fst ι g),
    hmQ.rep.snd (𝟙 ((uliftYoneda.{u + 1}).obj a)), hpaste,
    hmQ.property_snd (𝟙 ((uliftYoneda.{u + 1}).obj a))⟩

end AlgebraicGeometry.FormalSpace

end
