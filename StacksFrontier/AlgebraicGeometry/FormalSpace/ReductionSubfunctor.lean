module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceOfAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlasRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
import all StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
import all StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionComparison
import all StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionCountablyIndexed
import all StacksFrontier.AlgebraicGeometry.FormalSpace.MonomorphismClosedImmersion
import all StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas

/-!
# The reduction subfunctor of a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an fppf sheaf over `S` with an
atlas `fᵢ : Xᵢ ⟶ X` of morphisms representable by algebraic spaces and étale, and let
`rᵢ : Rᵢ ⟶ Xᵢ` be reductions of its members. This file cuts the candidate reduction `X_red`
out of `X` as a subfunctor and proves its properties: `Rᵢ = X_red ×_X Xᵢ`, and the inclusion
`X_red ⟶ X` is a closed immersion and a representable thickening. Together with the reduced
atlas of `exists_reduced_atlas_of_reducedAffineCharts` this is a second construction of the
reduction of a formal algebraic space (Stacks 0AIN), registered at
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.reductionSubfunctor`: for an atlas `fᵢ : Xᵢ ⟶ X` and reductions
  `rᵢ : Rᵢ ⟶ Xᵢ` of its members, the subfunctor of `X` of the sections all of whose lifts to the
  `Xᵢ` lie in the `Rᵢ`.
* `AlgebraicGeometry.FormalSpace.reductionSheaf` and
  `AlgebraicGeometry.FormalSpace.reductionSheafι`: that subfunctor as an fppf sheaf, and its
  inclusion into `X`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isReduction_yonedaSheaf_of_isAffineFormalAlgebraicSpace`:
  the affine case of Stacks 0AIN, with the reduction represented by a reduced affine object of
  the site.
* `AlgebraicGeometry.FormalSpace.IsReduction.isClosedImmersion`: the inclusion of a reduction is
  a closed immersion.
* `AlgebraicGeometry.FormalSpace.isPullback_reductionSheaf`: `Rᵢ = X_red ×_X Xᵢ`.
* `AlgebraicGeometry.FormalSpace.isClosedImmersion_reductionSheafι` and
  `AlgebraicGeometry.FormalSpace.isRepresentableThickeningULift_reductionSheafι`: the inclusion
  `X_red ⟶ X` is a closed immersion and a representable thickening.
* `AlgebraicGeometry.FormalSpace.exists_reduced_atlas_of_reducedAffineCharts`: a sheaf with an
  étale family of reduced affine charts has a reduced surjective étale scheme atlas.

## Implementation notes

The source glues the reductions `X_{i,red}` of the members of an atlas along the étale
equivalence relation `X_{i,red} ×_X X_j`. Here `X_red` is instead cut out inside `X` as a
subfunctor, which avoids forming a quotient. The key fact is the one of the source: an algebraic
space étale over a reduced algebraic space is reduced (Stacks 0GB3, through
`AlgebraicGeometry.Space.hasEtaleLocalPropertyULift_isReduced_of_isSmoothULift`), so the
projection `R ×_X X_j ⟶ X_j` factors through `X_{j,red}` for every reduced `R` mapping to `X`
(`AlgebraicGeometry.FormalSpace.exists_comp_eq_of_isReduction_of_etale`); and therefore
`X_{i,red} = X_red ×_X Xᵢ`. The closed immersion property is descent along the atlas
(Stacks 0GHY, `AlgebraicGeometry.FormalSpace.isClosedImmersion_of_locallySurjectiveFamily`).

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0GB3](https://stacks.math.columbia.edu/tag/0GB3)
* [Stacks Project, Tag 0GHY](https://stacks.math.columbia.edu/tag/0GHY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The sheaf represented by a reduced object of the site is étale locally reduced. -/
theorem hasEtaleLocalPropertyULift_isReduced_yonedaSheaf {K : BigFppfOver B S hS}
    (hK : IsReduced ((BigFppfOver.toScheme B S hS).obj K)) :
    Space.HasEtaleLocalPropertyULift.{u + 1} B S hS (yonedaSheaf B S hS K).obj
      (fun T : Scheme.{u} ↦ IsReduced T) :=
  ⟨K, 𝟙 _, hasSchemePropertyULift_of_isoSource B S hS _
      (fun _ _ g hg ↦ by have := hg; infer_instance) (Iso.refl _),
    hasSchemePropertyULift_of_isoSource B S hS _
      (fun _ _ g hg ↦ by have := hg; infer_instance) (Iso.refl _), hK⟩

/-- **Stacks 0AIN for an affine formal algebraic space, with the reduction represented.** An
affine formal algebraic space `X` over `S` has a reduction `h_T ⟶ X` whose source is the sheaf
represented by an affine reduced object `T` of the site. -/
theorem exists_isReduction_yonedaSheaf_of_isAffineFormalAlgebraicSpace
    (X : FppfSheaf B S hS) (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    ∃ (T : BigFppfOver B S hS) (i : yonedaSheaf B S hS T ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) ∧
      IsReduced ((BigFppfOver.toScheme B S hS).obj T) ∧ IsReduction B S hS X _ i := by
  classical
  obtain ⟨I, pre, hne, hdir, D, hD, ⟨e⟩⟩ := hX.2
  let _ : Preorder I := pre
  let _ : Nonempty I := hne
  let _ : IsDirected I (· ≤ ·) := hdir
  let JT := BigFppfOver.topology B S hS
  have _ : JT.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := Sheaf.sheafifiedYoneda JT
  let P := MorphismProperty.inverseImage
    (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have _ : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage _ _
  have _ : P.IsStableUnderComposition :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : PreservesLimitsOfShape WalkingCospan F := by
    dsimp [F, Sheaf.sheafifiedYoneda]
    infer_instance
  let i₀ : I := Classical.arbitrary I
  let T₀ : BigFppfOver B S hS := (BigAffineFppf.inclusion B S hS).obj (D.obj i₀)
  have hstage : MorphismProperty.relative F P
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i₀ ≫ e.symm.hom) :=
    isThickening_colimitι B S hS D hD X e.symm i₀
  let Tred : BigFppfOver B S hS := siteReduction B S hS T₀
  let r : F.obj Tred ⟶ X :=
    F.map (siteReductionMap B S hS T₀) ≫
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ F) i₀ ≫ e.symm.hom)
  have hr : MorphismProperty.relative F P r :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.relative_map
        (isThickening_toScheme_map_siteReductionMap B S hS T₀)) hstage
  have hrU : Space.IsRepresentableThickeningULift.{u + 1} B S hS r.hom :=
    relative_uliftYoneda_of_sheafifiedYoneda B S hS P hr
  let r' : yonedaSheaf B S hS Tred ⟶ X := (yonedaSheafIsoSheafifiedYoneda B S hS Tred).hom ≫ r
  have hrU' : Space.IsRepresentableThickeningULift.{u + 1} B S hS r'.hom :=
    MorphismProperty.RespectsIso.precomp (P.relative (uliftYoneda.{u + 1}))
      ((sheafToPresheaf JT (Type (u + 1))).mapIso
        (yonedaSheafIsoSheafifiedYoneda B S hS Tred)).hom r.hom hrU
  have hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) := (D.obj i₀).property
  have _ : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
    (siteReductionMap B S hS T₀)) := (isThickening_toScheme_map_siteReductionMap B S hS T₀).1
  exact ⟨Tred, r', isAffine_of_isAffineHom
      ((BigFppfOver.toScheme B S hS).map (siteReductionMap B S hS T₀)),
    isReduced_toScheme_obj_siteReduction B S hS T₀,
    isReduction_of_isRepresentableThickening B S hS r'
      (Space.isAlgebraicSpaceULift_uliftYoneda B S hS Tred)
      (hasEtaleLocalPropertyULift_isReduced_yonedaSheaf B S hS
        (isReduced_toScheme_obj_siteReduction B S hS T₀)) hrU'⟩

/-- A morphism `y : P ⟶ Y` whose composite with an étale morphism `g : Y ⟶ X`, representable by
algebraic spaces, factors through a morphism `v : V ⟶ X` out of a reduced algebraic space, factors
through any reduction `R ⟶ Y`: the base change `V ×_X Y` is étale over `V`, hence reduced, so its
projection to `Y` factors through `R`. -/
theorem exists_comp_eq_of_isReduction_of_etale {X V Y R : FppfSheaf B S hS}
    (hValg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS V.obj)
    (hVred : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS V.obj
      (fun T : Scheme.{u} ↦ IsReduced T))
    (v : V ⟶ X) (g : Y ⟶ X)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (hget : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) g.hom hg)
    {r : R ⟶ Y} (hr : IsReduction B S hS Y R r)
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : P ⟶ V.obj) (y : P ⟶ Y.obj)
    (h : a ≫ v.hom = y ≫ g.hom) :
    ∃ z : P ⟶ R.obj, z ≫ r.hom = y := by
  have sqh : IsPullback (pullback.fst v g).hom (pullback.snd v g).hom v.hom g.hom :=
    (IsPullback.of_hasPullback v g).map
      (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
  have hQalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback v g).obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS sqh.isoPullback.symm
      (Space.isAlgebraicSpaceULift_pullback_of_isRepresentableULift B S hS g.hom v.hom hg
        hValg)
  have hfstEt : ∀ (U : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj U ⟶ V.obj),
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ (pullback.fst v g).hom) :=
    isEtaleULift_pullback_fst_of_isPullback B S hS sqh.flip hget
  have hsmooth : Space.IsSmoothULift.{u + 1} B S hS (pullback.fst v g).hom :=
    Space.holdsOnEveryEtaleChartULift_of_forall_pullback_fst B S hS
      (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
      AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget hQalg hValg _
      (fun U ξ ↦ holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS _
        (fun k hk ↦ by have := hk; infer_instance) _ (hfstEt U ξ))
  have hQred := Space.hasEtaleLocalPropertyULift_isReduced_of_isSmoothULift B S hS hQalg hValg
    _ hsmooth hVred
  obtain ⟨m, hm, -⟩ := hr.universal (pullback v g) hQalg hQred (pullback.snd v g)
  have hm' : m.hom ≫ r.hom = (pullback.snd v g).hom := congrArg (fun k ↦ k.hom) hm
  exact ⟨sqh.lift a y h ≫ m.hom, by rw [Category.assoc, hm', sqh.lift_snd]⟩

/-- The section form of
`AlgebraicGeometry.FormalSpace.exists_comp_eq_of_isReduction_of_etale`. -/
theorem exists_app_eq_of_isReduction_of_etale {X V Y R : FppfSheaf B S hS}
    (hValg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS V.obj)
    (hVred : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS V.obj
      (fun T : Scheme.{u} ↦ IsReduced T))
    (v : V ⟶ X) (g : Y ⟶ X)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (hget : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) g.hom hg)
    {r : R ⟶ Y} (hr : IsReduction B S hS Y R r) {T : BigFppfOver B S hS}
    (a : V.obj.obj (op T)) (y : Y.obj.obj (op T))
    (h : v.hom.app (op T) a = g.hom.app (op T) y) :
    ∃ z : R.obj.obj (op T), r.hom.app (op T) z = y := by
  obtain ⟨z, hz⟩ := exists_comp_eq_of_isReduction_of_etale B S hS hValg hVred v g hg hget hr
    (uliftYonedaEquiv.{u + 1}.symm a) (uliftYonedaEquiv.{u + 1}.symm y) (by
      rw [uliftYonedaEquiv_symm_comp, uliftYonedaEquiv_symm_comp, h])
  refine ⟨uliftYonedaEquiv.{u + 1} z, ?_⟩
  rw [← uliftYonedaEquiv_comp, hz, Equiv.apply_symm_apply]

section

variable {B S hS}

/-- The inclusion of a reduction is a closed immersion. -/
theorem IsReduction.isClosedImmersion {Y Yr : FppfSheaf B S hS} {i : Yr ⟶ Y}
    (h : IsReduction B S hS Y Yr i) : IsClosedImmersion B S hS i := by
  have hle : MorphismProperty.inverseImage
      (@Stacks.Thickenings.IsThickening.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤ MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) := fun _ _ _ hg ↦ hg.1
  have hp := MorphismProperty.relative_monotone (F := uliftYoneda.{u + 1}) hle i.hom
    h.isRepresentableThickening
  exact isClosedImmersion_of_relative B S hS i hp

end

/-- Étale morphisms of the site, read through `BigFppfOver.toScheme`, form a multiplicative
class. -/
theorem isMultiplicative_inverseImage_etale :
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsMultiplicative where
  id_mem V := by
    change Etale (𝟙 V.left.obj)
    infer_instance
  comp_mem a b ha hb := by
    change Etale (a.left.hom ≫ b.left.hom)
    have : Etale a.left.hom := ha
    have : Etale b.left.hom := hb
    infer_instance

/-- Étale morphisms of the site, read through `BigFppfOver.toScheme`, respect isomorphisms. -/
theorem respectsIso_inverseImage_etale :
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
  have : MorphismProperty.RespectsIso (@Etale.{u}) := .mk _
    (fun e f hf => by have := hf; infer_instance)
    (fun e f hf => by have := hf; infer_instance)
  MorphismProperty.RespectsIso.inverseImage _ _

attribute [local instance] AlgebraicGeometry.Space.schemeCutoff_hasPullbacks in
/-- A morphism of fppf sheaves out of a representable sheaf which is representable by algebraic
spaces and étale is étale relative to the Yoneda embedding. -/
theorem relative_etale_of_isEtaleULift_of_schemeSource {Z Z' : FppfSheaf B S hS} (g : Z' ⟶ Z)
    (T : BigFppfOver B S hS) (e : (uliftYoneda.{u + 1}).obj T ≅ Z'.obj)
    (hg : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS g.hom)
    (het : Space.HasPropertyULift.{u + 1} B S hS
      (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) g.hom hg) :
    (MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{u + 1}) g.hom := by
  classical
  let C := BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  let P : MorphismProperty C :=
    MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have : P.RespectsIso := respectsIso_inverseImage_etale B S hS
  have : P.IsMultiplicative := isMultiplicative_inverseImage_etale B S hS
  have hrel : Y.relativelyRepresentable (e.hom ≫ g.hom) :=
    (Y.relativelyRepresentable).comp_mem _ _ (Functor.relativelyRepresentable.of_isIso Y e.hom)
      (AlgebraicGeometry.Space.relativelyRepresentableULift_of_isEtale_of_schemeSource
        B S hS g.hom T e hg het)
  exact (P.relative Y).cancel_left_of_respectsIso e.hom g.hom |>.mp
    (relative_of_representable_source_pullback_test Y P g.hom e hrel het)

attribute [local instance] AlgebraicGeometry.Space.schemeCutoff_hasPullbacks in
/-- If the family `gᵢ : Zᵢ ⟶ Z` induces a locally surjective `∐ Zᵢ ⟶ Z`, and each `Zᵢ` is
represented by `Tᵢ` with `h_{Tᵢ} ⟶ Z` representable, then for every `t : h_U ⟶ Z` the base
changes `h_{Tᵢ} ×_Z h_U ⟶ h_U` jointly cover the points of `U`. -/
theorem exists_mem_range_pullback_snd_of_isLocallySurjective {Z : FppfSheaf B S hS}
    {I : Type (u + 1)} (Zi : I → FppfSheaf B S hS) (g : ∀ i, Zi i ⟶ Z)
    (T : I → BigFppfOver B S hS) (e : ∀ i, (uliftYoneda.{u + 1}).obj (T i) ≅ (Zi i).obj)
    (hrep : ∀ i, (uliftYoneda.{u + 1}).relativelyRepresentable ((e i).hom ≫ (g i).hom))
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc g))
    (U : BigFppfOver B S hS) (t' : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj) (x : U.left.obj) :
    ∃ i, x ∈ Set.range ((hrep i).snd t').left.hom := by
  classical
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (Type (u + 1))) :=
    Sheaf.instHasColimitsOfSize
  have hmem := family_imageSieve_mem J Zi Z g hcover U (uliftYonedaEquiv t')
  rw [GrothendieckTopology.mem_over_iff] at hmem
  obtain ⟨E, hE, hER⟩ := Space.exists_covering_refining_sieve B hmem
  have hEF := B.isFppfCovering_of_isCovering hE
  rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
    PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
  obtain ⟨j, y, hy⟩ := hEF.1 x
  let T' : C := Over.mk (E.f j ≫ U.hom)
  let b : T' ⟶ U := Over.homMk (E.f j)
  have hb := (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨j⟩)
  change (⨆ i, Presheaf.imageSieve (g i).hom (uliftYonedaEquiv t')) b at hb
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
  obtain ⟨_, ⟨i, rfl⟩, z, hz⟩ := hb
  let m : Y.obj T' ⟶ (Zi i).obj := uliftYonedaEquiv.symm z
  have hw : (m ≫ (e i).inv) ≫ (e i).hom ≫ (g i).hom = Y.map b ≫ t' := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} t' b.op)
  let a : T' ⟶ (hrep i).pullback t' := Y.preimage
    (((hrep i).isPullback t').lift (m ≫ (e i).inv) (Y.map b) hw)
  have hab : a ≫ (hrep i).snd t' = b :=
    Y.map_injective (by simpa [a] using ((hrep i).isPullback t').lift_snd _ _ _)
  refine ⟨i, a.left.hom y, ?_⟩
  rwa [← Scheme.Hom.comp_apply, ← show (a ≫ (hrep i).snd t').left.hom =
    a.left.hom ≫ ((hrep i).snd t').left.hom from rfl, hab]

/-- If the members `pₓ : Vₓ ⟶ U` of an étale cover of the source of a locally surjective
`t : h_U ⟶ Z` factor through `q : h_W ⟶ Z`, then `q` is locally surjective. -/
theorem isLocallySurjective_of_comp_eq_etaleCover {Z : FppfSheaf B S hS} {ι : Type u}
    {U W : BigFppfOver B S hS} (t : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj)
    (ht : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) t)
    (q : (uliftYoneda.{u + 1}).obj W ⟶ Z.obj) (V : ι → BigFppfOver B S hS) (p : ∀ x, V x ⟶ U)
    (hp : ∀ x, Etale (p x).left.hom) (hcov : ∀ y : U.left.obj, ∃ x, y ∈ Set.range (p x).left.hom)
    (a : ∀ x, V x ⟶ W)
    (ha : ∀ x, (uliftYoneda.{u + 1}).map (a x) ≫ q = (uliftYoneda.{u + 1}).map (p x) ≫ t) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) q := by
  let J := BigFppfOver.topology B S hS
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  have hsmall : Presheaf.IsLocallySurjective J (Sigma.desc fun x ↦ Y.map (p x)) :=
    (GrothendieckTopology.ofArrows_mem_iff_isLocallySurjective_sigmaDesc_uliftYoneda_map
      J p).mp (fppf_ofArrows_mem B S hS V p (fun x => by have := hp x; infer_instance)
        (fun x => by have := hp x; infer_instance) hcov)
  let a' : ∐ (fun x ↦ Y.obj (V x)) ⟶ Y.obj W := Sigma.desc fun x ↦ Y.map (a x)
  have hafac : a' ≫ q = (Sigma.desc fun x ↦ Y.map (p x)) ≫ t :=
    Sigma.hom_ext _ _ fun x ↦ by simpa only [a', Sigma.ι_comp_desc_assoc] using ha x
  have : Presheaf.IsLocallySurjective J (a' ≫ q) := by
    rw [hafac]
    infer_instance
  exact Presheaf.isLocallySurjective_of_isLocallySurjective J a' q

/-- An object of the site covered by open immersions from reduced objects is reduced. -/
theorem isReduced_toScheme_of_openImmersions {ι : Type u} {W : BigFppfOver B S hS}
    (V : ι → BigFppfOver B S hS) (k : ∀ i, V i ⟶ W)
    (hk : ∀ i, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (k i)))
    (hcov : ∀ w : (BigFppfOver.toScheme B S hS).obj W,
      ∃ i, w ∈ Set.range ((BigFppfOver.toScheme B S hS).map (k i)))
    (hV : ∀ i, IsReduced ((BigFppfOver.toScheme B S hS).obj (V i))) :
    IsReduced ((BigFppfOver.toScheme B S hS).obj W) := by
  let 𝒰 : ((BigFppfOver.toScheme B S hS).obj W).OpenCover :=
    Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) ι
      (fun i ↦ (BigFppfOver.toScheme B S hS).obj (V i))
      (fun i ↦ (BigFppfOver.toScheme B S hS).map (k i))
      hcov hk
  have _ : ∀ i, IsReduced (𝒰.X i) := hV
  exact IsReduced.of_openCover _ 𝒰

attribute [local instance] AlgebraicGeometry.Space.schemeCutoff_hasPullbacks in
/-- **A reduced scheme atlas from reduced affine charts.** Let `gᵢ : Zᵢ ⟶ Z` be a family of
morphisms of fppf sheaves, each representable by algebraic spaces and étale, inducing a
surjection `∐ Zᵢ ⟶ Z`, where each `Zᵢ` is represented by a reduced affine object `Tᵢ` of the
site, and let `h_U ⟶ Z` be a surjection from a representable sheaf. Then `Z` has a surjective
étale scheme atlas, representable by objects of the site, whose source is reduced: the
coproduct of one `Tᵢ` for each point of `U`, as in the proof of observation (2) of Stacks 0AIS.
-/
theorem exists_reduced_atlas_of_reducedAffineCharts {Z : FppfSheaf B S hS}
    {I : Type (u + 1)} (Zi : I → FppfSheaf B S hS) (g : ∀ i, Zi i ⟶ Z)
    (T : I → BigFppfOver B S hS) (e : ∀ i, (uliftYoneda.{u + 1}).obj (T i) ≅ (Zi i).obj)
    (hTaff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (T i)))
    (hTred : ∀ i, IsReduced ((BigFppfOver.toScheme B S hS).obj (T i)))
    (hg : ∀ i, ∃ hgi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (g i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (g i).hom hgi)
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc g))
    (U : BigFppfOver B S hS) (t' : (uliftYoneda.{u + 1}).obj U ⟶ Z.obj)
    (ht' : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) t') :
    ∃ (W : BigFppfOver B S hS) (q : (uliftYoneda.{u + 1}).obj W ⟶ Z.obj),
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).relative
          (uliftYoneda.{u + 1}) q ∧
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).relative
          (uliftYoneda.{u + 1}) q ∧
      IsReduced ((BigFppfOver.toScheme B S hS).obj W) := by
  classical
  let C := BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  let P : MorphismProperty C :=
    MorphismProperty.inverseImage (@Etale : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)
  have : P.RespectsIso := respectsIso_inverseImage_etale B S hS
  have : P.IsMultiplicative := isMultiplicative_inverseImage_etale B S hS
  let gi (i : I) : Y.obj (T i) ⟶ Z.obj := (e i).hom ≫ (g i).hom
  have hgi (i : I) : P.relative Y (gi i) := by
    obtain ⟨hrep, het⟩ := hg i
    exact (P.relative Y).comp_mem _ _ ((P.relative Y).of_isIso _)
      (relative_etale_of_isEtaleULift_of_schemeSource B S hS (g i) (T i) (e i) hrep het)
  have hsize (i : I) : (T i).left.obj.size ≤ U.left.obj.size := by
    have : IsAffine (T i).left.obj := hTaff i
    exact affineChart_size_le' B S hS U (T i) t' ht' (gi i)
      (MorphismProperty.relative_monotone (MorphismProperty.monotone_inverseImage _
        fun _ _ _ hg ↦ by have := hg; infer_instance) _ (hgi i))
  let pi (i : I) : (hgi i).rep.pullback t' ⟶ U := (hgi i).rep.snd t'
  let ri (i : I) : (hgi i).rep.pullback t' ⟶ T i := Y.preimage ((hgi i).rep.fst t')
  have hpi (i : I) : Etale (pi i).left.hom := (hgi i).property_snd t'
  have hfac (i : I) : Y.map (ri i) ≫ gi i = Y.map (pi i) ≫ t' := by
    rw [Y.map_preimage]
    exact ((hgi i).rep.isPullback t').w
  have hpoint (x : U.left.obj) : ∃ i, x ∈ Set.range (pi i).left.hom :=
    exists_mem_range_pullback_snd_of_isLocallySurjective B S hS Zi g T e
      (fun i ↦ (hgi i).rep) hcover U t' x
  choose idx hidx using hpoint
  obtain ⟨W, k, q, hkq, hk, hkcov, hqrep⟩ :=
    exists_chart_of_size_le B S hS (fun x : U.left.obj => T (idx x))
      (fun x => gi (idx x)) (fun x => (hgi (idx x)).rep)
      (B.cutoff_isStrongPrelimit U.left.property) (Scheme.mk_le_two_pow_size U.left.obj)
      (fun x => (hsize (idx x)).trans (Cardinal.cantor _).le)
  have hqet : P.relative Y q := etale_of_openCover B S hS _ k hk hkcov q hqrep
    (fun x => (hkq x).symm ▸ hgi (idx x))
  have hqsurj : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) q :=
    isLocallySurjective_of_comp_eq_etaleCover B S hS t' ht' q _ (fun x ↦ pi (idx x))
      (fun x ↦ hpi (idx x)) (fun x ↦ ⟨x, hidx x⟩) (fun x ↦ ri (idx x) ≫ k x) fun x ↦ by
        rw [Functor.map_comp, Category.assoc, show Y.map (k x) ≫ q = gi (idx x) from hkq x, hfac]
  exact ⟨W, q, relative_surjective_of_locallySurjective B S hS q hqrep hqsurj, hqet,
    isReduced_toScheme_of_openImmersions B S hS _ k hk hkcov fun x ↦ hTred (idx x)⟩

/-! ### The reduction cut out by an atlas -/

section Atlas

variable {B S hS} {X : FppfSheaf B S hS} {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS}
  (f : ∀ i, Xi i ⟶ X) {R : I → FppfSheaf B S hS} (r : ∀ i, R i ⟶ Xi i)

/-- The subfunctor of a formal algebraic space `X` cut out by an atlas `fᵢ : Xᵢ ⟶ X` and chosen
reductions `rᵢ : Rᵢ ⟶ Xᵢ`: a section `ξ` of `X` over `T` belongs to it when every lift of a
restriction of `ξ` to some `Xᵢ` lies in `Rᵢ`. -/
def reductionSubfunctor : Subfunctor X.obj where
  obj T := {ξ | ∀ (i : I) ⦃T' : BigFppfOver B S hS⦄ (h : T' ⟶ T.unop)
    (y : (Xi i).obj.obj (op T')), (f i).hom.app (op T') y = X.obj.map h.op ξ →
      ∃ z, (r i).hom.app (op T') z = y}
  map {T T₂} g ξ hξ i T' h y hy := hξ i (h ≫ g.unop) y (by
    rw [hy]
    simp only [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply])

variable {f r}
variable (hrep : ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom)
  (het : ∀ i, Space.HasPropertyULift.{u + 1} B S hS
    (fun _ _ k ↦ Space.IsEtaleULift.{u + 1} B S hS k.hom) (f i).hom (hrep i))
  (hr : ∀ i, IsReduction B S hS (Xi i) (R i) (r i))
include het hr

/-- Every section of `X` coming from a reduced algebraic space lies in the reduction subfunctor. -/
theorem app_mem_reductionSubfunctor {V : FppfSheaf B S hS}
    (hValg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS V.obj)
    (hVred : Space.HasEtaleLocalPropertyULift.{u + 1} B S hS V.obj
      (fun T : Scheme.{u} ↦ IsReduced T))
    (v : V ⟶ X) {T : BigFppfOver B S hS} (a : V.obj.obj (op T)) :
    v.hom.app (op T) a ∈ (reductionSubfunctor f r).obj (op T) := by
  intro i T' h y hy
  exact exists_app_eq_of_isReduction_of_etale B S hS hValg hVred v (f i) (hrep i) (het i) (hr i)
    (V.obj.map h.op a) y ((NatTrans.naturality_apply v.hom h.op a).trans hy.symm)

/-- A section of `Xᵢ` maps into the reduction subfunctor exactly when it lies in `Rᵢ`. -/
theorem app_mem_reductionSubfunctor_iff (i : I) {T : BigFppfOver B S hS}
    (y : (Xi i).obj.obj (op T)) :
    (f i).hom.app (op T) y ∈ (reductionSubfunctor f r).obj (op T) ↔
      ∃ z, (r i).hom.app (op T) z = y := by
  refine ⟨fun hy ↦ hy i (𝟙 T) y (by simp), ?_⟩
  rintro ⟨z, rfl⟩
  exact app_mem_reductionSubfunctor hrep het hr (hr i).algebraic (hr i).reduced (r i ≫ f i) z

omit het in
/-- The reduction subfunctor is an fppf sheaf. -/
theorem isSheaf_reductionSubfunctor :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) (reductionSubfunctor f r).toFunctor := by
  let J := BigFppfOver.topology B S hS
  refine ((reductionSubfunctor f r).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type J X.obj).1 X.property)).2 fun U s hs i T' h y hy ↦ ?_
  have _ : Mono (r i).hom := mono_of_isRepresentableThickeningULift B S hS
    (hr i).isRepresentableThickening
  have hRange : Presieve.IsSheaf J (Subfunctor.range (r i).hom).toFunctor :=
    Presieve.isSheaf_iso J (asIso (Subfunctor.toRange (r i).hom))
      ((isSheaf_iff_isSheaf_of_type J (R i).obj).1 (R i).property)
  refine ((Subfunctor.range (r i).hom).isSheaf_iff
    ((isSheaf_iff_isSheaf_of_type J (Xi i).obj).1 (Xi i).property)).1 hRange (op T') y
    (J.superset_covering (fun V k hk ↦ ?_) (J.pullback_stable h hs))
  exact hk i (𝟙 V) ((Xi i).obj.map k.op y) (by
    rw [NatTrans.naturality_apply, hy]
    simp only [op_id, Functor.map_id_apply, op_comp, Functor.map_comp_apply])

variable (f) in
/-- The reduction subfunctor, as an fppf sheaf. -/
def reductionSheaf : FppfSheaf B S hS :=
  ⟨(reductionSubfunctor f r).toFunctor,
    (isSheaf_iff_isSheaf_of_type _ _).2 (isSheaf_reductionSubfunctor hr)⟩

variable (f) in
/-- The inclusion of the reduction sheaf into `X`. -/
def reductionSheafι : reductionSheaf f hr ⟶ X := ⟨(reductionSubfunctor f r).ι⟩

/-- The morphism `Rᵢ ⟶ X_red` through which `Rᵢ ⟶ Xᵢ ⟶ X` factors. -/
def reductionSheafLift (i : I) : R i ⟶ reductionSheaf f hr :=
  ⟨Subfunctor.lift ((r i).hom ≫ (f i).hom) (by
    rintro T _ ⟨z, rfl⟩
    exact (app_mem_reductionSubfunctor_iff hrep het hr i ((r i).hom.app T z)).2 ⟨z, rfl⟩)⟩

/-- The composite `Rᵢ ⟶ X_red ⟶ X` is `Rᵢ ⟶ Xᵢ ⟶ X`. -/
theorem reductionSheafLift_comp_ι (i : I) :
    reductionSheafLift hrep het hr i ≫ reductionSheafι f hr = r i ≫ f i := rfl

/-- `Rᵢ` is the base change of the reduction sheaf along the chart `Xᵢ ⟶ X`. -/
theorem isPullback_reductionSheaf (i : I) :
    IsPullback (r i) (reductionSheafLift hrep het hr i) (f i) (reductionSheafι f hr) := by
  let J := BigFppfOver.topology B S hS
  have _ : Mono (r i).hom := mono_of_isRepresentableThickeningULift B S hS
    (hr i).isRepresentableThickening
  have hpre : IsPullback (r i).hom (reductionSheafLift hrep het hr i).hom (f i).hom
      (reductionSheafι f hr).hom := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk (f := (f i).hom)
      (g := (reductionSheafι f hr).hom) (r i).hom (reductionSheafLift hrep het hr i).hom
      rfl) ?_
    refine evaluationJointlyReflectsLimits _ fun U ↦ ?_
    refine (PullbackCone.isLimitMapConeEquiv _ ((evaluation _ _).obj U)).symm ?_
    refine ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩).isLimit
    · rfl
    · rintro a b ⟨hab, -⟩
      exact ((NatTrans.mono_iff_mono_app (r i).hom).1 inferInstance U |>
        (mono_iff_injective _).1) hab
    · intro y x hxy
      obtain ⟨z, hz⟩ := (app_mem_reductionSubfunctor_iff hrep het hr i y).1 (by
        rw [show (f i).hom.app U y = x.1 from hxy]
        exact x.2)
      exact ⟨z, hz, Subtype.ext ((congrArg ((f i).hom.app U) hz).trans hxy)⟩
  exact IsPullback.of_map (sheafToPresheaf J (Type (u + 1)))
    ((sheafToPresheaf J (Type (u + 1))).map_injective hpre.w) hpre

/-- The inclusion of the reduction sheaf into `X` is a closed immersion, by descent along the
atlas. -/
theorem isClosedImmersion_reductionSheafι
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    IsClosedImmersion B S hS (reductionSheafι f hr) := by
  refine isClosedImmersion_of_locallySurjectiveFamily B S hS I Xi f hsurj fun i ↦ ?_
  have sq := (isPullback_reductionSheaf hrep het hr i).flip
  rw [show pullback.snd (reductionSheafι f hr) (f i) = sq.isoPullback.inv ≫ r i by
    rw [Iso.eq_inv_comp, sq.isoPullback_hom_snd]]
  exact isClosedImmersion_comp B S hS _ _ (isClosedImmersion_of_isIso B S hS _)
    (hr i).isClosedImmersion

/-- A section of `X` over a reduced object of the site lies in the reduction subfunctor. -/
theorem mem_reductionSubfunctor_of_isReduced {K : BigFppfOver B S hS}
    (hK : IsReduced ((BigFppfOver.toScheme B S hS).obj K)) (ξ : X.obj.obj (op K)) :
    ξ ∈ (reductionSubfunctor f r).obj (op K) := by
  have h := app_mem_reductionSubfunctor hrep het hr
    (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS K)
    (hasEtaleLocalPropertyULift_isReduced_yonedaSheaf B S hS hK)
    (⟨uliftYonedaEquiv.{u + 1}.symm ξ⟩ : yonedaSheaf B S hS K ⟶ X) (ULift.up (𝟙 K))
  rwa [show (⟨uliftYonedaEquiv.{u + 1}.symm ξ⟩ : yonedaSheaf B S hS K ⟶ X).hom.app (op K)
    (ULift.up (𝟙 K)) = ξ from uliftYonedaEquiv.{u + 1}.apply_symm_apply ξ] at h

/-- The inclusion of the reduction sheaf into `X` is a representable thickening. -/
theorem isRepresentableThickeningULift_reductionSheafι
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    Space.IsRepresentableThickeningULift.{u + 1} B S hS (reductionSheafι f hr).hom := by
  have hrel := relative_closedImmersionOfSite_of_isClosedImmersion B S hS _
    (isClosedImmersion_reductionSheafι hrep het hr hsurj)
  refine ⟨hrel.rep, fun a b g fst snd sq ↦ ⟨hrel.property g fst snd sq, ?_⟩⟩
  intro t
  let A := (BigFppfOver.toScheme B S hS).obj a
  let K : BigFppfOver B S hS := Over.mk ((ObjectProperty.homMk (A.fromSpecResidueField t) :
    (⟨_, B.residueField_spec_contains a.left.property t⟩ : B.Schemes) ⟶ a.left) ≫ a.hom)
  let k : K ⟶ a := Over.homMk (ObjectProperty.homMk (A.fromSpecResidueField t)) rfl
  have hKred : IsReduced ((BigFppfOver.toScheme B S hS).obj K) :=
    inferInstanceAs (IsReduced (Spec (.of (A.residueField t))))
  let ξK : X.obj.obj (op K) := X.obj.map k.op (uliftYonedaEquiv.{u + 1} g)
  let c : (uliftYoneda.{u + 1}).obj K ⟶ (reductionSheaf f hr).obj :=
    uliftYonedaEquiv.{u + 1}.symm
      (⟨ξK, mem_reductionSubfunctor_of_isReduced hrep het hr hKred ξK⟩ :
        (reductionSubfunctor f r).toFunctor.obj (op K))
  have hw : c ≫ (reductionSheafι f hr).hom = (uliftYoneda.{u + 1}).map k ≫ g := by
    apply uliftYonedaEquiv.{u + 1}.injective
    rw [uliftYonedaEquiv_comp, show uliftYonedaEquiv.{u + 1} c =
      ⟨ξK, mem_reductionSubfunctor_of_isReduced hrep het hr hKred ξK⟩ from
        Equiv.apply_symm_apply _ _]
    exact uliftYonedaEquiv_naturality g k.op
  obtain ⟨l, hl⟩ : ∃ l : K ⟶ b, l ≫ snd = k :=
    ⟨(uliftYoneda.{u + 1}).preimage (sq.lift c ((uliftYoneda.{u + 1}).map k) hw),
      (uliftYoneda.{u + 1}).map_injective (by simp)⟩
  let p : (BigFppfOver.toScheme B S hS).obj K := IsLocalRing.closedPoint (A.residueField t)
  refine ⟨(BigFppfOver.toScheme B S hS).map l p, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hl]
  exact Scheme.fromSpecResidueField_apply t _

end Atlas

end AlgebraicGeometry.FormalSpace

end
