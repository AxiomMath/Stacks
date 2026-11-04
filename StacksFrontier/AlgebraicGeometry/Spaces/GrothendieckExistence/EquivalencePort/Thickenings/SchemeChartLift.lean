module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactQuasiSeparatedPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Thickenings.SpacesEtaleEquivalenceGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHomTfaeComplete
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.Pushouts.ThickeningAffineAtlasOfChartLift

namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573

/-!
# Lifting étale scheme charts along a thickening of algebraic spaces

Let `j : Z ⟶ Q` be a thickening of algebraic spaces over `S` and let `U` be a scheme étale over
`Z`. By Stacks 05ZH there is an algebraic space `W` étale over `Q` with `W ×_Q Z ≅ U`; the
morphism `U ⟶ W` is a base change of `j`, hence a thickening, and so `W` is a scheme as soon as
the ambient space of a thickening whose closed subspace is a scheme is itself a scheme, which is
Stacks 05ZR. This file proves that implication
(`AlgebraicGeometry.schemeChartLiftProperty_of_thickeningRepresentable`): the lift of
étale scheme charts used by the proofs of Stacks 07VX and Stacks 07WN.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

open _root_.AlgebraicGeometry.Space.C1573
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étale scheme charts lift along thickenings of algebraic spaces: for a thickening
`j : Z ⟶ Q` and a scheme `U` étale over `Z`, there is a scheme `U'` étale over `Q` with
`U = U' ×_Q Z`. This is Stacks 05ZH together with Stacks 05ZR. -/
def C1573.SchemeChartLiftProperty : Prop :=
  ∀ {Z Q : AlgebraicSpaces B S hS} (j : Z ⟶ Q), IsThickeningHom B S hS j →
    ∀ (U : BigFppfOver B S hS) (m : yoneda.obj U ⟶ Z.1), IsEtale B S hS m →
      ∃ (U' : BigFppfOver B S hS) (m' : yoneda.obj U' ⟶ Q.1) (k : U ⟶ U'),
        IsEtale B S hS m' ∧ IsPullback (yoneda.map k) m m' j.hom

/-! ### The base change of a thickening of schemes to an algebraic space -/

/-- A morphism of algebraic spaces cartesian over a thickening of schemes of the site is a
thickening. -/
theorem C1573.isThickeningHom_of_isPullback_yoneda {Z Q : AlgebraicSpaces B S hS}
    {X X' : BigFppfOver B S hS} (j : Z ⟶ Q) (π : Z.1 ⟶ yoneda.obj X) (ρ : Q.1 ⟶ yoneda.obj X')
    (i : X ⟶ X')
    (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i))
    (h : IsPullback j.hom π ρ (yoneda.map i)) : IsThickeningHom B S hS j := by
  have hth := FormalSpace.isThickeningHom_yonedaSpace_map B S hS i hi
  rw [isThickeningHom_iff_isClosedImmersion_and_isSurjective] at hth ⊢
  have h' : IsPullback (ObjectProperty.homMk π : Z ⟶ (schemeSpaceFunctor B S hS).obj X) j
      ((schemeSpaceFunctor B S hS).map i) (ObjectProperty.homMk ρ) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) h.flip
  exact ⟨isClosedImmersion_of_isPullback B S hS h' hth.1,
    isSurjective_of_isPullback B S hS h' hth.2⟩

/-- An étale morphism of algebraic spaces stays étale after base change, for a cartesian square
of presheaves. -/
theorem C1573.isEtale_of_isPullback_presheaf {P X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z)
    {p : P ⟶ X} {f' : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y} (h : IsPullback p f' f g)
    (hf : IsEtale B S hS f) : IsEtale B S hS f' :=
  isEtale_of_isPullback B S hS (X' := ⟨P, hP⟩) (X := ⟨X, hX⟩) (Z := ⟨Z, hZ⟩) (Y := ⟨Y, hY⟩)
    (ObjectProperty.homMk p) (ObjectProperty.homMk f') (ObjectProperty.homMk f)
    (ObjectProperty.homMk g) (IsPullback.of_map_of_faithful (ObjectProperty.ι _) h) hf

/-- A pushout of schemes of the site has the universal property of a pushout in the site. -/
theorem C1573.exists_desc_of_isPushout_toScheme {U U' V P W : BigFppfOver B S hS} {k : U ⟶ U'}
    {g : U ⟶ V} {u₁ : U' ⟶ P} {u₂ : V ⟶ P}
    (hP : IsPushout ((BigFppfOver.toScheme B S hS).map k) ((BigFppfOver.toScheme B S hS).map g)
      ((BigFppfOver.toScheme B S hS).map u₁) ((BigFppfOver.toScheme B S hS).map u₂))
    (s' : U' ⟶ W) (s : V ⟶ W) (h : k ≫ s' = g ≫ s) :
    ∃ cP : P ⟶ W, u₁ ≫ cP = s' ∧ u₂ ≫ cP = s := by
  set Φ := BigFppfOver.toScheme B S hS
  have hw : Φ.map k ≫ Φ.map s' = Φ.map g ≫ Φ.map s := by rw [← Φ.map_comp, ← Φ.map_comp, h]
  set φ : Φ.obj P ⟶ Φ.obj W := hP.desc (Φ.map s') (Φ.map s) hw with hφ
  have hφS : φ ≫ B.inclusion.map W.hom = B.inclusion.map P.hom := by
    refine hP.hom_ext ?_ ?_ <;> rw [← Category.assoc, hφ] <;>
      simp only [IsPushout.inl_desc, IsPushout.inr_desc] <;>
      erw [← B.inclusion.map_comp, ← B.inclusion.map_comp, Over.w, Over.w]
  let cP : P ⟶ W := Over.homMk (B.inclusion.preimage φ) (by
    apply B.inclusion.map_injective
    rwa [Functor.map_comp, B.inclusion.map_preimage])
  have hcP : Φ.map cP = φ := B.inclusion.map_preimage φ
  exact ⟨cP, Φ.map_injective (by rw [Φ.map_comp, hcP, hφ, hP.inl_desc]),
    Φ.map_injective (by rw [Φ.map_comp, hcP, hφ, hP.inr_desc])⟩

/-- A base change of a thickening of algebraic spaces is a thickening. -/
theorem C1573.isThickeningHom_fst_of_isPullback {W X Z Y : AlgebraicSpaces B S hS} {p : W ⟶ X}
    {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y} (h : IsPullback p q f g)
    (hg : IsThickeningHom B S hS g) : IsThickeningHom B S hS p := by
  rw [isThickeningHom_iff_isClosedImmersion_and_isSurjective] at hg ⊢
  exact ⟨isClosedImmersion_of_isPullback B S hS h.flip hg.1,
    isSurjective_of_isPullback B S hS h.flip hg.2⟩

/-- Representability of the ambient space of a thickening whose closed subspace is a scheme:
the conclusion of Stacks 05ZR, in the morphism form. -/
def C1573.ThickeningRepresentableProperty : Prop :=
  ∀ {X X' : AlgebraicSpaces B S hS} (i : X ⟶ X'), IsThickeningHom B S hS i →
    X.1.IsRepresentable → X'.1.IsRepresentable

/-- **Étale scheme charts lift along thickenings**, from Stacks 05ZH and Stacks 05ZR. -/
theorem C1573.schemeChartLiftProperty_of_thickeningRepresentable
    (hrep : ThickeningRepresentableProperty B S hS) : SchemeChartLiftProperty B S hS := by
  intro Z Q j hj U m hm
  have : (spacesBaseChange B S hS j).functor.IsEquivalence :=
    isEquivalence_spacesBaseChange_of_isThickeningHom B S hS j hj
  let Uo : SpacesEtale B S hS Z :=
    ⟨Over.mk (ObjectProperty.homMk m : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
      AlgebraicSpaces B S hS) ⟶ Z), hm⟩
  obtain ⟨Wo, ⟨eW⟩⟩ := Functor.EssSurj.mem_essImage (F := (spacesBaseChange B S hS j).functor)
    Uo
  set bc := (spacesBaseChange B S hS j).functor.obj Wo
  have hpb := (spacesBaseChange B S hS j).isPullback Wo
  set pr := (spacesBaseChange B S hS j).projection.app Wo
  have hthW : IsThickeningHom B S hS pr := isThickeningHom_fst_of_isPullback B S hS hpb hj
  let eU : bc.1.left ≅
      (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) :=
    (Over.forget Z).mapIso ((ObjectProperty.ι _).mapIso eW)
  have hbcrep : bc.1.left.1.IsRepresentable :=
    Functor.IsRepresentable.mk' ((ObjectProperty.ι _).mapIso eU).symm
  have hWrep : Wo.1.left.1.IsRepresentable := hrep pr hthW hbcrep
  set U' := Wo.1.left.1.reprX
  let φ : yoneda.obj U' ≅ Wo.1.left.1 := Wo.1.left.1.reprW
  refine ⟨U', φ.hom ≫ Wo.1.hom.hom, yoneda.preimage (eU.inv.hom ≫ pr.hom ≫ φ.inv), ?_, ?_⟩
  · exact isEtale_comp B S hS (isEtale_of_isIso B S hS φ.hom) Wo.2
  · rw [yoneda.map_preimage]
    have hm' : eU.hom.hom ≫ m = bc.1.hom.hom :=
      congrArg (·.hom) (Over.w eW.hom.hom : eW.hom.hom.left ≫ Uo.1.hom = bc.1.hom)
    refine IsPullback.of_iso (AlgebraicSpaces.isPullback_hom B S hS hpb)
      ((ObjectProperty.ι _).mapIso eU) φ.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · show pr.hom ≫ φ.inv = eU.hom.hom ≫ eU.inv.hom ≫ pr.hom ≫ φ.inv
      rw [← Category.assoc eU.hom.hom, ← InducedCategory.comp_hom, eU.hom_inv_id]
      rfl
    · show bc.1.hom.hom ≫ 𝟙 _ = eU.hom.hom ≫ m
      rw [Category.comp_id, hm']
    · show Wo.1.hom.hom ≫ 𝟙 _ = φ.inv ≫ φ.hom ≫ Wo.1.hom.hom
      simp
    · simp

/-! ### Compatible charts of a thickening-and-affine span -/

/-- **Every thickening-and-affine span of algebraic spaces has a compatible pair of étale scheme
charts**, once étale scheme charts lift along thickenings: a surjective étale chart `V` of `Y`
restricts to the scheme `V ×_Y X`, the morphism `X ⟶ Y` being affine, and that chart lifts across
`X ⟶ X'`. -/
theorem C1573.hasThickeningAffineAtlases_of_schemeChartLift
    (hlift : SchemeChartLiftProperty B S hS) :
    HasThickeningAffineAtlases B S hS := by
  refine hasThickeningAffineAtlases_of_forall_chartLift B S hS ?_
  intro X X' Y i f hi hf
  obtain ⟨V, q, hqS, hqE⟩ := Y.property.exists_atlas
  have hr := presheaf_isAffineHom_of_isAffineHom_of_isAlgebraicSpace B S hS X.property
    Y.property hf
  let U := hr.1.pullback q
  let p := hr.1.fst q
  let g := hr.1.snd q
  have hpbf : IsPullback p (yoneda.map g) f.hom q := hr.1.isPullback q
  have hpE : IsEtale B S hS p :=
    isEtale_of_isPullback_presheaf B S hS (isAlgebraicSpace_yoneda B S hS U)
      (isAlgebraicSpace_yoneda B S hS V) Y.property X.property hpbf.flip
      ((isEtale_iff_presheaf_of_yoneda B S hS q).2 hqE)
  obtain ⟨U', p', k, hp'E, hpbi⟩ := hlift i hi U p hpE
  exact ⟨U, U', V, q, p, p', k, g, hqS, hqE, (isEtale_iff_presheaf_of_yoneda B S hS p').1 hp'E,
    hpbf, hpbi⟩

end AlgebraicGeometry.Space

end
