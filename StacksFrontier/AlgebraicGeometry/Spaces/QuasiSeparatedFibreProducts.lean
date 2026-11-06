module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

/-!
# Quasi-separatedness tested on fibre products of schemes

An algebraic space over `S` is quasi-separated, in the absolute sense of Stacks 03BS part (3),
exactly when the fibre product of any two quasi-compact schemes over it is again a
quasi-compact scheme; and it is enough to test this on pairs of *affine* schemes over it.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_iff_compactSpace_pullback`: the
  equivalence of conditions (1) and (2) of Stacks 0AHR — quasi-separatedness is
  quasi-compactness of the fibre product of any two quasi-compact schemes over the space.
* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine`: the
  equivalence of conditions (1) and (3) of Stacks 0AHR — testing on affine schemes suffices.

## Implementation notes

The fibre product is not named by a construction but specified by an isomorphism from a
representable presheaf to the categorical pullback, so its quasi-compactness does not depend on
the choice of a representing object of the site. The schemes mapping to the space are objects of
the chosen big fppf site over `S`, and quasi-separatedness is the absolute condition, tested
after viewing the space over the terminal scheme along
`AlgebraicGeometry.Space.viewOverIntegers`.

The implication from quasi-separatedness is
`AlgebraicGeometry.Space.compactSpace_of_isAbsolutelyQuasiSeparated`, applied to the cartesian
square which representability of the diagonal attaches to the two charts.

The converse is the argument of the source, carried out over the terminal scheme. A test object
`T` of the site over `Spec ℤ` together with a morphism `h_T ⟶ X ⨯ X` is restricted to an affine
open `V` of the scheme underlying `T`; over that affine open the two components of the morphism
come, by `CategoryTheory.OverShriek.exists_eq_relocalizeYonedaFactorIso_comp`, from two charts
of `X` over `S` with the *same* underlying scheme, so the hypothesis applies to them and
produces a quasi-compact representing object `W` of the fibre product. The base change of the
diagonal along `V` is then cut out of `W` as the equalizer of the two projections `W ⟶ V`, which
is a closed subscheme because the diagonal of the affine scheme `V` is a closed immersion; a
closed immersion is quasi-compact, so the base change is quasi-compact, and quasi-compactness of
a morphism of schemes is tested on affine opens of the target.

## References

* [Stacks Project, Tag 0AHR](https://stacks.math.columbia.edu/tag/0AHR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Spaces

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

/-- Pullbacks of presheaves on a big fppf site over a scheme (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullback_presheaf_quasiSeparatedFibreProducts
    {T : Scheme.{u}} {hT : B.Contains T}
    {X Y Z : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- Binary products of presheaves on a big fppf site over a scheme (instance search times out
without this shortcut). -/
local instance (priority := high) hasBinaryProduct_presheaf_quasiSeparatedFibreProducts
    {T : Scheme.{u}} {hT : B.Contains T} (X Y : (BigFppfOver B T hT)ᵒᵖ ⥤ Type u) :
    HasLimit (pair X Y) :=
  HasLimitsOfShape.has_limit _

/-- The affine test condition of Stacks 0AHR, transported to the big fppf site of the terminal
scheme: if every fibre product of two affine charts of `X` over `S` is a quasi-compact scheme,
then every fibre product of two morphisms from affine objects of the site over the terminal
scheme into `X`, viewed there, is a quasi-compact scheme.

Each of the two morphisms factors, by
`CategoryTheory.OverShriek.exists_eq_relocalizeYonedaFactorIso_comp`, through the relocalization
of a chart of `X` over `S` whose underlying scheme is the one it started from, hence affine; and
the relocalization functor preserves fibre products and representable presheaves, so the
representing object supplied by the hypothesis, viewed over the terminal scheme, represents the
fibre product one started with. -/
private theorem exists_compactSpace_isoPullback_viewOverIntegers
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hqc : ∀ (U V : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X) (g : yoneda.obj V ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∃ W : BigFppfOver B S hS,
        CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
        Nonempty (yoneda.obj W ≅ pullback f g))
    (T₁ T₂ : BigFppfOver B (⊤_ Scheme.{u}) hZ)
    (hT₁ : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T₁))
    (hT₂ : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj T₂))
    (a : yoneda.obj T₁ ⟶ viewOverIntegers B S hS hZ X)
    (b : yoneda.obj T₂ ⟶ viewOverIntegers B S hS hZ X) :
    ∃ W : BigFppfOver B (⊤_ Scheme.{u}) hZ,
      CompactSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj W) ∧
      Nonempty (yoneda.obj W ≅ pullback a b) := by
  let base : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let R := OverShriek.relocalizePresheafFunctor base
  obtain ⟨ψ₁, hψ₁, σ₁, ha⟩ := OverShriek.exists_eq_relocalizeYonedaFactorIso_comp base a
  obtain ⟨ψ₂, hψ₂, σ₂, hb⟩ := OverShriek.exists_eq_relocalizeYonedaFactorIso_comp base b
  obtain ⟨W, hW, ⟨eW⟩⟩ := hqc (Over.mk ψ₁) (Over.mk ψ₂) σ₁ σ₂ hT₁ hT₂
  let eChange : pullback a b ≅ pullback (R.map σ₁) (R.map σ₂) := by
    rw [ha, hb]
    exact HasLimit.isoOfNatIso (cospanExt (OverShriek.relocalizeYonedaFactorIso base hψ₁)
      (OverShriek.relocalizeYonedaFactorIso base hψ₂) (Iso.refl _) (by simp [R]) (by simp [R]))
  exact ⟨(Over.map base).obj W, hW,
    ⟨((OverShriek.relocalizeYonedaIso base).app W).symm ≪≫ R.mapIso eW ≪≫
      PreservesPullback.iso R σ₁ σ₂ ≪≫ eChange.symm⟩⟩

/-- **Stacks 0AHR, (3) implies (1).** An algebraic space over `S` whose fibre products of pairs
of affine charts are quasi-compact schemes is quasi-separated.

The argument is the one of the source, run over the terminal scheme, where the product of two
quasi-compact schemes is again quasi-compact. Over an affine open `V` of a test object of the
site, the base change of the diagonal is the equalizer of the two projections of the fibre
product of the two components of the test morphism; the diagonal of the affine scheme `V` is a
closed immersion, so that equalizer is a closed subscheme of the quasi-compact scheme
representing the fibre product, hence quasi-compact. -/
private theorem isAbsolutelyQuasiSeparated_of_affine_pullbacks
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hqc : ∀ (U V : BigFppfOver B S hS) (f : yoneda.obj U ⟶ X) (g : yoneda.obj V ⟶ X),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      ∃ W : BigFppfOver B S hS,
        CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
        Nonempty (yoneda.obj W ≅ pullback f g)) :
    IsAbsolutelyQuasiSeparated B S hS hZ X := by
  let base : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩
  let XR := viewOverIntegers B S hS hZ X
  let Q := BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ
  have : MorphismProperty.RespectsIso (@QuasiCompact.{u}) :=
    (inferInstance : MorphismProperty.IsStableUnderBaseChange
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u})).respectsIso
  let P := MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) Q
  have : P.RespectsIso := MorphismProperty.RespectsIso.inverseImage
    (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) Q
  show P.presheaf (diag XR)
  have hXR : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ XR :=
    isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ base X hX
  let hdiag := hXR.diagonal_representable
  have : HasBinaryProducts (BigFppfOver B (⊤_ Scheme.{u}) hZ) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  have : HasEqualizers (BigFppfOver B (⊤_ Scheme.{u}) hZ) :=
    hasEqualizers_of_hasPullbacks_and_binary_products
  have : PreservesLimitsOfShape WalkingCospan Q := by
    apply comp_preservesLimitsOfShape
  have : PreservesLimit (Functor.empty.{0} (BigFppfOver B (⊤_ Scheme.{u}) hZ)) Q := by
    apply preservesTerminal_of_iso Q
    refine Q.mapIso ((terminalIsTerminal :
      IsTerminal (⊤_ BigFppfOver B (⊤_ Scheme.{u}) hZ)).uniqueUpToIso
        (Over.mkIdTerminal (X := B.obj hZ))) ≪≫ ?_
    exact Iso.refl (B.inclusion.obj (B.obj hZ))
  have : PreservesLimitsOfShape (Discrete PEmpty.{1}) Q :=
    preservesLimitsOfShape_pempty_of_preservesTerminal Q
  have : PreservesLimitsOfShape (Discrete WalkingPair) Q :=
    preservesBinaryProducts_of_preservesTerminal_and_pullbacks Q
  apply MorphismProperty.relative.of_exists
  intro T g
  have hP : P (hdiag.snd g) := by
    show QuasiCompact (Q.map (hdiag.snd g))
    rw [quasiCompact_iff_forall_isAffineOpen]
    intro V hV
    let T₀ := openSiteObject B (⊤_ Scheme.{u}) hZ T V
    let i := openSiteObjectHom B (⊤_ Scheme.{u}) hZ T V
    have hT₀aff : IsAffine (Q.obj T₀) := hV
    have hmap : Q.map i = V.ι := map_openSiteObjectHom B (⊤_ Scheme.{u}) hZ T V
    let g₀ := yoneda.map i ≫ g
    let a₀ := g₀ ≫ prod.fst
    let b₀ := g₀ ≫ prod.snd
    obtain ⟨W, hWcompact, ⟨eW⟩⟩ :=
      exists_compactSpace_isoPullback_viewOverIntegers B S hS hZ hqc T₀ T₀ hT₀aff hT₀aff a₀ b₀
    have hpair₀ : prod.lift a₀ b₀ = g₀ := by
      apply prod.hom_ext <;> simp [a₀, b₀]
    have hPastedPair : IsPullback
        (yoneda.map (pullback.fst (hdiag.snd g) i) ≫ hdiag.fst g)
        (yoneda.map (pullback.snd (hdiag.snd g) i)) (diag XR)
        (prod.lift a₀ b₀) := by
      simpa [hpair₀] using (Functor.map_isPullback yoneda
        (IsPullback.of_hasPullback (hdiag.snd g) i)).paste_horiz (hdiag.isPullback g)
    obtain ⟨w₁, hw₁⟩ := yoneda.map_surjective (eW.hom ≫ pullback.fst a₀ b₀)
    obtain ⟨w₂, hw₂⟩ := yoneda.map_surjective (eW.hom ≫ pullback.snd a₀ b₀)
    have hpb₀ : IsPullback (yoneda.map w₁) (yoneda.map w₂) a₀ b₀ :=
      IsPullback.of_iso_pullback
        ⟨by rw [hw₁, hw₂, Category.assoc, Category.assoc, pullback.condition]⟩
        eW hw₁.symm hw₂.symm
    have hE : IsPullback
        (equalizer.ι (yoneda.map w₁) (yoneda.map w₂) ≫ (yoneda.map w₁ ≫ a₀))
        (equalizer.ι (yoneda.map w₁) (yoneda.map w₂) ≫ yoneda.map w₁)
        (diag XR) (prod.lift a₀ b₀) := by
      simpa [Category.assoc] using (Limits.isPullback_equalizer_prod
        (yoneda.map w₁) (yoneda.map w₂)).paste_horiz (isPullback_diag_prodMap hpb₀)
    let eProdQ : Q.obj (T₀ ⨯ T₀) ≅ Q.obj T₀ ⨯ Q.obj T₀ := asIso (prodComparison Q T₀ T₀)
    let dSite : T₀ ⟶ T₀ ⨯ T₀ := prod.lift (𝟙 T₀) (𝟙 T₀)
    have hdSite : Q.map dSite ≫ eProdQ.hom =
        prod.lift (𝟙 (Q.obj T₀)) (𝟙 (Q.obj T₀)) := by
      apply prod.hom_ext <;>
        simp [eProdQ, Category.assoc, prodComparison_fst, prodComparison_snd,
          ← Functor.map_comp, dSite]
    have hdiagClosed : AlgebraicGeometry.IsClosedImmersion (Q.map dSite) := by
      have hdiag' : AlgebraicGeometry.IsClosedImmersion
          (prod.lift (𝟙 (Q.obj T₀)) (𝟙 (Q.obj T₀))) := by
        have : IsAffine (Q.obj T₀) := hT₀aff
        infer_instance
      let eArrow : Arrow.mk (Q.map dSite) ≅
          Arrow.mk (prod.lift (𝟙 (Q.obj T₀)) (𝟙 (Q.obj T₀))) :=
        Arrow.isoMk (Iso.refl _) eProdQ hdSite.symm
      exact (MorphismProperty.arrow_mk_iso_iff
        (P := @AlgebraicGeometry.IsClosedImmersion) eArrow).mpr hdiag'
    have hclosed : AlgebraicGeometry.IsClosedImmersion (Q.map (equalizer.ι w₁ w₂)) :=
      MorphismProperty.of_isPullback
        (Functor.map_isPullback Q (Limits.isPullback_equalizer_prod w₁ w₂)).flip hdiagClosed
    have hEcompact : CompactSpace (Q.obj (equalizer w₁ w₂)) := by
      have : CompactSpace (Q.obj W) := hWcompact
      exact QuasiCompact.compactSpace_of_compactSpace (Q.map (equalizer.ι w₁ w₂))
    have hVpbcompact : CompactSpace (Q.obj (pullback (hdiag.snd g) i)) :=
      compactSpace_of_iso (Q.mapIso (yoneda.preimageIso (hPastedPair.isoIsPullback _ _ hE ≪≫
        (PreservesEqualizer.iso yoneda w₁ w₂).symm)).symm) hEcompact
    have hschemeRep : IsPullback (Q.map (pullback.fst (hdiag.snd g) i))
        (Q.map (pullback.snd (hdiag.snd g) i)) (Q.map (hdiag.snd g)) V.ι := by
      simpa only [hmap] using
        Functor.map_isPullback Q (IsPullback.of_hasPullback (hdiag.snd g) i)
    exact isCompact_iff_compactSpace.2
      (compactSpace_of_iso (pullbackRestrictIsoRestrict (Q.map (hdiag.snd g)) V)
        (compactSpace_of_iso hschemeRep.isoPullback hVpbcompact))
  exact ⟨hdiag.pullback g, hdiag.fst g, hdiag.snd g, hdiag.isPullback g, hP⟩

/-- **Stacks 0AHR, equivalence of (1) and (2).** An algebraic space over `S` is quasi-separated
exactly when the fibre product of any two quasi-compact schemes over it is a quasi-compact
scheme. -/
@[stacks 0AHR "equivalence of (1) and (2)"]
theorem isAbsolutelyQuasiSeparated_iff_compactSpace_pullback
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    IsAbsolutelyQuasiSeparated B S hS hZ X ↔
      ∀ (U V : BigFppfOver B S hS)
        (f : yoneda.obj U ⟶ X) (g : yoneda.obj V ⟶ X),
        CompactSpace ((BigFppfOver.toScheme B S hS).obj U) →
        CompactSpace ((BigFppfOver.toScheme B S hS).obj V) →
        ∃ W : BigFppfOver B S hS,
          CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
          Nonempty (yoneda.obj W ≅ pullback f g) := by
  refine ⟨fun h U V f g hU hV => ?_, fun h => ?_⟩
  · have hrep := hX.diagonal_representable.of_diag f
    have hpb := hrep.isPullback' g
    exact ⟨hrep.pullback g,
      compactSpace_of_isAbsolutelyQuasiSeparated B S hS hZ h hpb hU hV, ⟨hpb.isoPullback⟩⟩
  · exact isAbsolutelyQuasiSeparated_of_affine_pullbacks B S hS hZ hX fun U V f g _ _ =>
      h U V f g (Scheme.compactSpace_of_isAffine _) (Scheme.compactSpace_of_isAffine _)

/-- **Stacks 0AHR, equivalence of (1) and (3).** It is enough to test quasi-compactness of the
fibre products of Stacks 0AHR on pairs of *affine* schemes over the algebraic space. -/
@[stacks 0AHR "equivalence of (1) and (3)"]
theorem isAbsolutelyQuasiSeparated_iff_compactSpace_pullback_affine
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X) :
    IsAbsolutelyQuasiSeparated B S hS hZ X ↔
      ∀ (U V : BigFppfOver B S hS)
        (f : yoneda.obj U ⟶ X) (g : yoneda.obj V ⟶ X),
        IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
        IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
        ∃ W : BigFppfOver B S hS,
          CompactSpace ((BigFppfOver.toScheme B S hS).obj W) ∧
          Nonempty (yoneda.obj W ≅ pullback f g) := by
  refine ⟨fun h U V f g hU hV => ?_,
    isAbsolutelyQuasiSeparated_of_affine_pullbacks B S hS hZ hX⟩
  exact (isAbsolutelyQuasiSeparated_iff_compactSpace_pullback B S hS hZ X hX).mp h U V f g
    (Scheme.compactSpace_of_isAffine _) (Scheme.compactSpace_of_isAffine _)

end AlgebraicGeometry.Space

end
