module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Constructible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.SmallWeaklyContractible
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleJacobsonQuotient
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ExactPushforward

/-!
# Exactness of direct image along a closed immersion with retrocompact complement

For a closed immersion of schemes whose open complement is retrocompact, direct image of abelian
sheaves on the small pro-étale sites is exact.

Exactness is tested on the affine objects of the small pro-étale site of the target whose rings of
global sections are w-contractible, which cover every object. The base change of such an object
along the closed immersion is a closed subscheme of it, so affine, and its ring of global sections
is a quotient `R ⧸ I` of a w-contractible ring `R` whose zero locus has quasi-compact open
complement, because that complement is the preimage of the complement of the image of the closed
immersion. A quotient of this shape is again w-contractible, and over a w-contractible object a
locally surjective morphism of sheaves is surjective on sections, while direct image evaluates on
an object of the source site at its base change.

## Main results

* `AlgebraicGeometry.ProEtale.SmallProetale.isWContractibleObject_baseChange_of_isRetrocompact`:
  base change of an affine object with w-contractible global sections along a closed immersion
  with retrocompact open complement is again one.
* `AlgebraicGeometry.ProEtale.exact_smallProetalePushforward_of_isRetrocompact_compl_range`:
  direct image of abelian sheaves is exact.

## Implementation notes

Abelian sheaves are taken in `AddCommGrpCat.{u + 1}`: the small pro-étale site of a scheme in a
chosen big pro-étale site has its objects one universe above its morphisms, and sheafification of
abelian presheaves on it needs colimits of that larger size.

The complement of the image of the closed immersion is taken in the underlying topological space
of the target scheme, and is retrocompact exactly when it is quasi-compact, the underlying space
of a scheme being quasi-separated locally. Quasi-compactness of the complement of the base-changed
closed immersion is read off on `Spec` of the ring of global sections of the affine object, using
that a closed immersion into an affine scheme is the one cut out by an ideal.

## References

* [Stacks Project, Tag 09BM](https://stacks.math.columbia.edu/tag/09BM)
* [Stacks Project, Tag 00F6](https://stacks.math.columbia.edu/tag/00F6)
* [Stacks Project, Tag 0986](https://stacks.math.columbia.edu/tag/0986)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe u

namespace AlgebraicGeometry.ProEtale

/-- The preimage of a retrocompact open subset along a morphism of schemes is retrocompact: an
open subset is retrocompact exactly when its inclusion is a spectral map, which for an open
immersion of schemes is quasi-compactness of that immersion, and quasi-compactness of a morphism
is stable under base change. -/
private theorem isRetrocompact_preimage_of_isOpen {X Y : Scheme.{u}} (f : X ⟶ Y) {s : Set Y}
    (hs : IsOpen s) (hc : IsRetrocompact s) : IsRetrocompact (f ⁻¹' s) :=
  IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr
    (quasiCompact_iff_isSpectralMap.mp
      (MorphismProperty.of_isPullback (P := @QuasiCompact)
        (isPullback_morphismRestrict f ⟨s, hs⟩)
        (quasiCompact_iff_isSpectralMap.mpr
          (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hc))))

/-- A closed immersion `p : P ⟶ W` into an affine scheme whose image has compact complement is
cut out by an ideal `I` of `Γ(W, ⊤)` whose zero locus has compact complement. -/
private theorem exists_ideal_isCompact_compl_zeroLocus_of_isClosedImmersion
    {P W : Scheme.{u}} [IsAffine W] (p : P ⟶ W) [IsClosedImmersion p]
    (hc : IsCompact (Set.range p.base)ᶜ) :
    ∃ (I : Ideal Γ(W, ⊤)) (_ : P ≅ Spec (CommRingCat.of (Γ(W, ⊤) ⧸ I))),
      IsCompact (PrimeSpectrum.zeroLocus (I : Set Γ(W, ⊤)))ᶜ := by
  let eW : ↥W ≃ₜ ↥(Spec Γ(W, ⊤)) := TopCat.homeoOfIso (Scheme.forgetToTop.mapIso W.isoSpec)
  obtain ⟨I, eP, hfac⟩ :=
    (IsClosedImmersion.Spec_iff (f := p ≫ W.isoSpec.hom)).mp inferInstance
  refine ⟨I, eP, ?_⟩
  have hrq : Set.range (p ≫ W.isoSpec.hom).base =
      (PrimeSpectrum.zeroLocus (I : Set ↥Γ(W, ⊤)) : Set ↥(Spec Γ(W, ⊤))) := by
    rw [hfac, Scheme.Hom.comp_base]
    change Set.range ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base ∘
      eP.hom.base) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr (by
      have _ : IsIso eP.hom.base := Scheme.forgetToTop.map_isIso eP.hom
      exact ((TopCat.isIso_iff_isHomeomorph _).mp inferInstance).surjective),
      Set.image_univ]
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
    rw [_root_.range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective]
    simp [Ideal.mk_ker]
  have himage : Set.range (p ≫ W.isoSpec.hom).base = eW '' Set.range p.base := by
    rw [Scheme.Hom.comp_base]
    change Set.range (eW ∘ p.base) = _
    rw [Set.range_comp]
  have h : IsCompact (eW '' ((Set.range p.base)ᶜ)) := hc.image eW.continuous
  rwa [Homeomorph.image_compl, ← himage, hrq] at h

/-- **The w-contractible objects of the small pro-étale site are preserved by base change along a
closed immersion with retrocompact open complement.**

Let `U` be an affine object of the small pro-étale site of `X` with w-contractible ring of global
sections `R`. The base change of `U` along `i` is the closed subscheme of `U` cut out by an ideal
`I` of `R`, whose zero locus is the preimage in `U` of the image of `i`; the complement of that
preimage is quasi-compact because the complement of the image of `i` is retrocompact. So `R ⧸ I`
is a quotient of a w-contractible ring with quasi-compact open complement of its zero locus, and
is therefore w-contractible. -/
theorem SmallProetale.isWContractibleObject_baseChange_of_isRetrocompact
    (B : BigProetaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
    [IsClosedImmersion (B.inclusion.map i)]
    (hi : IsRetrocompact ((Set.range (B.inclusion.map i).base)ᶜ))
    (U : SmallProetale B X.obj X.property)
    (hU : SmallProetale.IsWContractibleObject B X.obj X.property U) :
    SmallProetale.IsWContractibleObject B Z.obj Z.property
      ((smallProetaleBaseChange B Z X i).obj U) := by
  obtain ⟨haff, hwc⟩ := hU
  have haffW : IsAffine (B.inclusion.obj U.obj.left) := haff
  have hpb : IsPullback (B.inclusion.map (pullback.fst U.obj.hom i))
      (B.inclusion.map (pullback.snd U.obj.hom i))
      (B.inclusion.map U.obj.hom) (B.inclusion.map i) :=
    (IsPullback.of_hasPullback U.obj.hom i).map B.inclusion
  have hci : IsClosedImmersion (B.inclusion.map (pullback.fst U.obj.hom i)) :=
    MorphismProperty.of_isPullback hpb.flip inferInstance
  have haffP : IsAffine (B.inclusion.obj (pullback U.obj.hom i)) :=
    isAffine_of_isAffineHom (B.inclusion.map (pullback.fst U.obj.hom i))
  refine ⟨haffP, ?_⟩
  change IsWContractible.{u, u} Γ(B.inclusion.obj (pullback U.obj.hom i), ⊤)
  set W : Scheme.{u} := B.inclusion.obj U.obj.left
  set P : Scheme.{u} := B.inclusion.obj (pullback U.obj.hom i)
  set p : P ⟶ W := B.inclusion.map (pullback.fst U.obj.hom i) with hp
  have hcpt : IsCompact ((Set.range p.base)ᶜ) := by
    refine IsRetrocompact.isCompact ?_
    have hr := Scheme.image_preimage_eq_of_isPullback hpb.flip Set.univ
    simp only [Set.preimage_univ, Set.image_univ] at hr
    rw [hp, hr, ← Set.preimage_compl]
    exact isRetrocompact_preimage_of_isOpen (B.inclusion.map U.obj.hom)
      (IsClosedImmersion.isClosedEmbedding (B.inclusion.map i)).isClosed_range.isOpen_compl hi
  obtain ⟨I, eP, hcptI⟩ := exists_ideal_isCompact_compl_zeroLocus_of_isClosedImmersion p hcpt
  have hwcW : IsWContractible.{u, u} ↥Γ(W, ⊤) := hwc
  exact isWContractible_of_ringEquiv
    ((Scheme.ΓSpecIso (CommRingCat.of (↥Γ(W, ⊤) ⧸ I))).symm ≪≫
      Scheme.Γ.mapIso eP.op).commRingCatIsoToRingEquiv.symm
    (isWContractible_quotient_of_isCompact_compl_zeroLocus _ hwcW I hcptI)

/-- **Stacks 09BM.** Let `i : Z → X` be a closed immersion of schemes whose open complement is
retrocompact. Then direct image of abelian sheaves along the induced morphism of small pro-étale
sites is exact. -/
@[stacks 09BM]
theorem exact_smallProetalePushforward_of_isRetrocompact_compl_range
    (B : BigProetaleSite.{u}) {Z X : B.Scheme} (i : Z ⟶ X)
    [IsClosedImmersion (B.inclusion.map i)]
    (hi : IsRetrocompact ((Set.range (B.inclusion.map i).base)ᶜ)) :
    exactFunctor
      (Sheaf (SmallProetale.topology B Z.obj Z.property) AddCommGrpCat.{u + 1})
      (Sheaf (SmallProetale.topology B X.obj X.property) AddCommGrpCat.{u + 1})
      ((smallProetaleBaseChange B Z X i).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (SmallProetale.topology B X.obj X.property)
        (SmallProetale.topology B Z.obj Z.property)) := by
  have _ : (smallProetaleBaseChange B Z X i).IsContinuous
      (SmallProetale.topology B X.obj X.property)
      (SmallProetale.topology B Z.obj Z.property) :=
    (smallProetaleBaseChange_isMorphismOfSites B Z X i).toIsContinuous
  refine Stacks.WeaklyContractible.exact_sheafPushforwardContinuous _ _ _
    (SmallProetale.IsWContractibleObject B X.obj X.property)
    (SmallProetale.hasEnoughObjects_isWContractible B X) ?_
  intro U hU F G φ hφ
  obtain ⟨haff, hwc⟩ :=
    SmallProetale.isWContractibleObject_baseChange_of_isRetrocompact B i hi U hU
  have := haff
  exact SmallProetale.surjective_sections_of_isWContractible B Z.obj Z.property _ hwc F G φ hφ

end AlgebraicGeometry.ProEtale

end
