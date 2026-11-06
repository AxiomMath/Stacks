module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Cancellation
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFibreIdentification
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationMorphismProperties

/-!
# The general case of Stacks 05XR: the inputs available over the base

Let `Z ⟶ U` be a finite morphism of the big fppf site of a scheme `U` and let `w : W ⟶ h_Z` be an
étale morphism of presheaves on that site with `W` an algebraic space. Stacks 05XR asserts that
the space of sections of `W_T ⟶ Z_T`, `AlgebraicGeometry.Space.sectionSpace`, is an algebraic
space étale over `U`. It is proved for `w` *separated* as
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_of_isSeparated` and
`AlgebraicGeometry.Space.isEtale_sectionSpace_of_isSeparated`, and the source deduces the general
case from that case along a surjective étale chart `p : h_V ⟶ W` whose scheme `V` is separated:
the comparison morphism `AlgebraicGeometry.Space.sectionSpaceMap` of the two spaces of sections is
then surjective and étale, and the general case follows by the bootstrap.

This file supplies two inputs of that deduction.

The first is the **kernel pair of the comparison morphism**: the space of sections of
`(V ×_W V) ⟶ Z` is the fibre product of the space of sections of `h_V ⟶ h_Z` with itself over the
space of sections of `w`. That is the universal property of `V ×_W V` read on sections, with no
hypothesis at all; it is
`AlgebraicGeometry.Space.isPullback_sectionSpaceMap_self`. Both projections of `V ×_W V` over `Z`
are separated and étale, being base changes of the chart followed by the chart's own structure
morphism, so the separated case applies to the kernel pair as well: it is an algebraic space étale
over `U`, and therefore the two projections of the kernel pair are étale, by the cancellation law,
and surjective, the diagonal of the chart inducing a section of each.

The second is the permanence of **étaleness under a change of base scheme**. For
`h : W' ⟶ S` a morphism of a big fppf site, the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor h` of Stacks 03I5 part (2) carries a presheaf
on the big fppf site of `W'` to a presheaf on the big fppf site of `S`, and it carries algebraic
spaces to algebraic spaces by Stacks 03I4 part (3)
(`AlgebraicGeometry.Space.isAlgebraicSpace_relocalize`). Separatedness and surjectivity are
likewise unchanged, by `AlgebraicGeometry.Space.isSeparated_relocalize`,
`AlgebraicGeometry.Space.isSeparated_of_relocalize` and
`AlgebraicGeometry.Space.isSurjective_relocalize`. The corresponding statement for étaleness is
proved here: both sides are the every-étale-chart condition of Stacks 03MJ for étaleness of
morphisms of schemes, by Stacks 03XT condition (7)
(`AlgebraicGeometry.Space.isEtale_iff_holdsOnEveryEtaleChart`), and that condition is unchanged by
the extension (`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeMap_iff`), because a
chart of the extension is the extension of a chart with the same underlying scheme and a commuting
square of extended charts comes from a commuting square of charts.

## Main definitions

* `AlgebraicGeometry.Space.SectionsOver.pullbackLift`: the section of `(V ×_W V) ⟶ Z` determined
  by two sections of `h_V ⟶ h_Z` with the same postcomposition with the chart.

## Main results

* `AlgebraicGeometry.Space.isEtale_of_isEtale_terminal_from`: the cancellation law — a morphism
  between two algebraic spaces whose structure morphisms are étale is étale.
* `AlgebraicGeometry.Space.isEtale_relocalize_iff` and
  `AlgebraicGeometry.Space.isEtale_relocalizeToYoneda`: étaleness of a morphism of algebraic
  spaces, and of the structure morphism of an algebraic space, are unchanged by the lower-shriek
  extension to a larger base scheme.
* `AlgebraicGeometry.Space.isPullback_sectionSpaceMap_self`: the space of sections of
  `(V ×_W V) ⟶ Z` is the kernel pair of the comparison morphism.
* `AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_pullback_chart` and
  `AlgebraicGeometry.Space.isEtale_sectionSpace_pullback_chart`: that kernel pair is an algebraic
  space étale over `U`.
* `AlgebraicGeometry.Space.isEtale_sectionSpaceMap_pullback_fst`,
  `AlgebraicGeometry.Space.isEtale_sectionSpaceMap_pullback_snd`,
  `AlgebraicGeometry.Space.isSurjective_sectionSpaceMap_pullback_fst` and
  `AlgebraicGeometry.Space.isSurjective_sectionSpaceMap_pullback_snd`: the two projections of the
  kernel pair are étale and surjective.

## Implementation notes

No statement here carries the tag of Stacks 05XR: the general case of its main assertion is not
proved. What is still owed for it is the fibre of the comparison morphism at an *arbitrary*
scheme-valued point of the space of sections of `w` — the fibre is identified as a presheaf over
`h_T` by `AlgebraicGeometry.Space.isPullback_baseChangeSectionPresheaf`, and recognising it as a
space of sections formed over `T` means carrying the base change of the chart across the change of
base site, for which the étale transport above is one of the ingredients. The kernel pair computes
that fibre only over a point that lifts to the space of sections of the chart.

The structure morphism of a presheaf `F` is written here as
`CategoryTheory.Limits.terminal.from F`, which is the form the section-space results of Stacks
05XR use, whereas the chart statements of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleChartSmallerBase.lean` use
`AlgebraicGeometry.Space.toYonedaId`, the morphism to the representable presheaf of the identity
of the base. That object is terminal, so the two morphisms agree up to the unique isomorphism of
terminal objects, and étaleness is insensitive to composing with it.

## References

* [Stacks Project, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03XT](https://stacks.math.columbia.edu/tag/03XT)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The cancellation law -/

section Cancellation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of an object of the big fppf site of `S` is étale as soon as the
morphism to the terminal presheaf from its representable presheaf is. -/
theorem etale_hom_of_isEtale_terminal_from (A : BigFppfOver B S hS)
    (h : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (terminal.from (yoneda.obj A))) :
    AlgebraicGeometry.Etale (B.inclusion.map A.hom) := by
  set O : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS)) with hO
  set τ : A ⟶ O := Over.homMk A.hom (Category.comp_id _) with hτ
  have hterm : IsTerminal (yoneda.obj O) :=
    (Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _
  set e : yoneda.obj O ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    hterm.uniqueUpToIso terminalIsTerminal with he
  have hpost := MorphismProperty.RespectsIso.postcomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) e.inv (terminal.from (yoneda.obj A)) h
  rw [show terminal.from (yoneda.obj A) ≫ e.inv = yoneda.map τ from hterm.hom_ext _ _] at hpost
  exact (presheaf_yoneda_map_etale_iff B S hS τ).1 hpost

/-- **The cancellation law for étaleness of morphisms of algebraic spaces.** A morphism between
two algebraic spaces over `S` whose structure morphisms are étale is itself étale.

By Stacks 03XT condition (7) it suffices to see that the morphism of schemes between the charts
of a commuting square of étale charts is étale. Both charts have étale structure morphisms, being
composites of an étale chart with an étale structure morphism, and the square makes the morphism
between them a morphism over `S`, so the scheme-level cancellation law
`AlgebraicGeometry.etale_of_etale_over` of Stacks 02GW applies. -/
theorem isEtale_of_isEtale_terminal_from {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hFet : IsEtale B S hS (terminal.from F)) (hGet : IsEtale B S hS (terminal.from G))
    (f : F ⟶ G) : IsEtale B S hS f := by
  refine (isEtale_iff_holdsOnEveryEtaleChart B S hS hF hG f).2 ?_
  intro A C a b m ha hb _hsq
  have hA : AlgebraicGeometry.Etale (B.inclusion.map A.hom) := by
    refine etale_hom_of_isEtale_terminal_from B S hS A ?_
    rw [show terminal.from (yoneda.obj A) = a ≫ terminal.from F from terminal.hom_ext _ _]
    exact hFet A a ha
  have hC : AlgebraicGeometry.Etale (B.inclusion.map C.hom) := by
    refine etale_hom_of_isEtale_terminal_from B S hS C ?_
    rw [show terminal.from (yoneda.obj C) = b ≫ terminal.from G from terminal.hom_ext _ _]
    exact hGet C b hb
  exact etale_of_etale_over ((BigFppfOver.toScheme B S hS).map m)
    (p := B.inclusion.map A.hom) (q := B.inclusion.map C.hom)
    (by
      show B.inclusion.map m.left ≫ B.inclusion.map C.hom = B.inclusion.map A.hom
      rw [← B.inclusion.map_comp]
      exact congrArg B.inclusion.map (Over.w m))

/-- A morphism of presheaves on the big fppf site of `S` which admits a section is surjective on
the points of Stacks 03BU: the induced map on points is a retraction. -/
theorem isSurjective_of_comp_eq_id {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {q : F ⟶ G} {s : G ⟶ F} (h : s ≫ q = 𝟙 G) : IsSurjective B S hS q := by
  have h1 : Function.Surjective (pointsMap B S hS G (s ≫ q)) := by
    rw [h, pointsMap_id]
    exact Function.surjective_id
  rw [pointsMap_comp] at h1
  exact h1.of_comp

end Cancellation

/-! ### Étaleness and the lower-shriek extension -/

section Relocalize

variable (B : BigFppfSite.{u}) (W S : Scheme.{u}) (hW : B.Contains W) (hS : B.Contains S)
  (h : B.obj hW ⟶ B.obj hS)

/-- **Étaleness of a morphism of algebraic spaces is unchanged by the lower-shriek extension of
Stacks 03I5 part (2).** A morphism of algebraic spaces over `W` is étale exactly when its
extension along `h : W ⟶ S` is étale as a morphism of algebraic spaces over `S`.

Both sides are the every-étale-chart condition of Stacks 03MJ for étaleness of morphisms of
schemes, by Stacks 03XT condition (7), and that condition is unchanged by the extension. -/
theorem isEtale_relocalize_iff {F G : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B W hW F) (hG : IsAlgebraicSpace B W hW G) (k : F ⟶ G) :
    IsEtale B S hS ((OverShriek.relocalizePresheafFunctor h).map k) ↔ IsEtale B W hW k :=
  (isEtale_iff_holdsOnEveryEtaleChart B S hS
      (isAlgebraicSpace_relocalize B (B.obj hW) (B.obj hS) h F hF)
      (isAlgebraicSpace_relocalize B (B.obj hW) (B.obj hS) h G hG) _).trans
    ((holdsOnEveryEtaleChart_relocalizeMap_iff B W S hW hS h
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) k).trans
      (isEtale_iff_holdsOnEveryEtaleChart B W hW hF hG k).symm)

/-- **The structural morphism of a lower-shriek extension is étale as soon as the algebraic space
it extends is étale over its own base.** The structural morphism
`Λ_h F ⟶ h_{(W ⟶ S)}` is the extension of the structure morphism of `F`, followed by an
isomorphism, so the every-étale-chart condition for it over `S` is the every-étale-chart
condition for that structure morphism over `W`. -/
theorem isEtale_relocalizeToYoneda {F : (BigFppfOver B W hW)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B W hW F) (hFet : IsEtale B W hW (terminal.from F)) :
    IsEtale B S hS (OverShriek.relocalizeToYoneda h F) := by
  have hterm : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hW)))) :=
    (Over.mkIdTerminal (X := B.obj hW)).isTerminalObj yoneda _
  set e : ⊤_ ((BigFppfOver B W hW)ᵒᵖ ⥤ Type u) ≅ yoneda.obj (Over.mk (𝟙 (B.obj hW))) :=
    terminalIsTerminal.uniqueUpToIso hterm with he
  have hid : IsEtale B W hW (toYonedaId B W hW F) := by
    rw [show toYonedaId B W hW F = terminal.from F ≫ e.hom from hterm.hom_ext _ _]
    exact isEtale_comp B W hW hFet (isEtale_of_isIso B W hW e.hom)
  refine (isEtale_iff_holdsOnEveryEtaleChart B S hS
    (isAlgebraicSpace_relocalize B (B.obj hW) (B.obj hS) h F hF)
    (isAlgebraicSpace_yoneda B S hS (Over.mk h)) _).2 ?_
  refine (holdsOnEveryEtaleChart_relocalizeToYoneda_iff B W S hW hS h
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) F).2 ?_
  exact (isEtale_iff_holdsOnEveryEtaleChart B W hW hF
    (isAlgebraicSpace_yoneda B W hW (Over.mk (𝟙 (B.obj hW)))) _).1 hid

end Relocalize

/-! ### The kernel pair of a comparison of spaces of sections -/

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `U` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_SectionSpaceGeneralCase {B : BigFppfSite.{u}}
    {U : Scheme.{u}} {hU : B.Contains U} :
    HasPullbacks ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_SectionSpaceGeneralCase
    {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
    {X Y Z : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

section KernelPair

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
  {Z : BigFppfOver B U hU} {W W₁ : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
  {w : W ⟶ yoneda.obj Z} {w₁ : W₁ ⟶ yoneda.obj Z} {p : W₁ ⟶ W}

/-- The two projections of `W₁ ×_W W₁` agree after composition with the morphism to `h_Z`: they
agree already after composition with `p`. -/
theorem pullback_fst_comp_eq_snd_comp (hp : p ≫ w = w₁) :
    pullback.fst p p ≫ w₁ = pullback.snd p p ≫ w₁ := by
  rw [← hp, ← Category.assoc, ← Category.assoc, pullback.condition]

/-- The section of `W₁ ×_W W₁ ⟶ Z` over `T` determined by two sections of `W₁ ⟶ Z` whose
postcompositions with `p` agree. -/
noncomputable def SectionsOver.pullbackLift (_hp : p ≫ w = w₁) {T : BigFppfOver B U hU}
    (σ τ : SectionsOver B U hU Z T W₁ w₁) (h : σ.1 ≫ p = τ.1 ≫ p) :
    SectionsOver B U hU Z T (pullback p p) (pullback.snd p p ≫ w₁) :=
  ⟨pullback.lift σ.1 τ.1 h, by
    rw [← Category.assoc, pullback.lift_snd]
    exact τ.2⟩

/-- The morphism `T ⟶ W₁ ×_W W₁` underlying `SectionsOver.pullbackLift hp σ τ h` is
`pullback.lift σ.1 τ.1 h`. -/
@[simp]
theorem SectionsOver.pullbackLift_coe (hp : p ≫ w = w₁) {T : BigFppfOver B U hU}
    (σ τ : SectionsOver B U hU Z T W₁ w₁) (h : σ.1 ≫ p = τ.1 ≫ p) :
    (SectionsOver.pullbackLift hp σ τ h).1 = pullback.lift σ.1 τ.1 h :=
  rfl

/-- Taking the section of `W₁ ×_W W₁ ⟶ Z` determined by two sections commutes with restriction. -/
theorem SectionsOver.restrict_pullbackLift (hp : p ≫ w = w₁) {T T' : BigFppfOver B U hU}
    (f : T' ⟶ T) (σ τ : SectionsOver B U hU Z T W₁ w₁) (h : σ.1 ≫ p = τ.1 ≫ p)
    (h' : (SectionsOver.restrict f σ).1 ≫ p = (SectionsOver.restrict f τ).1 ≫ p) :
    SectionsOver.restrict f (SectionsOver.pullbackLift hp σ τ h) =
      SectionsOver.pullbackLift hp (SectionsOver.restrict f σ) (SectionsOver.restrict f τ) h' := by
  refine Subtype.ext ?_
  rw [SectionsOver.restrict_coe, SectionsOver.pullbackLift_coe, SectionsOver.pullbackLift_coe]
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, SectionsOver.restrict_coe]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, SectionsOver.restrict_coe]

/-- The morphism to the space of sections of `W₁ ×_W W₁ ⟶ Z` determined by two morphisms to the
space of sections of `w₁` whose postcompositions with the comparison morphism agree. -/
private noncomputable def sectionSpacePairLift (hp : p ≫ w = w₁)
    {A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (a b : A ⟶ sectionSpace B U hU Z W₁ w₁)
    (key : ∀ (T : BigFppfOver B U hU) (ξ : A.obj (op T)),
      (sectionSpaceEquiv B U hU Z T W₁ w₁ (a.app (op T) ξ)).1 ≫ p =
        (sectionSpaceEquiv B U hU Z T W₁ w₁ (b.app (op T) ξ)).1 ≫ p) :
    A ⟶ sectionSpace B U hU Z (pullback p p) (pullback.snd p p ≫ w₁) where
  app T₀ := ↾fun ξ =>
      (sectionSpaceEquiv B U hU Z T₀.unop (pullback p p) (pullback.snd p p ≫ w₁)).symm
        (SectionsOver.pullbackLift hp (sectionSpaceEquiv B U hU Z T₀.unop W₁ w₁ (a.app T₀ ξ))
          (sectionSpaceEquiv B U hU Z T₀.unop W₁ w₁ (b.app T₀ ξ)) (key T₀.unop ξ))
  naturality := by
    have hnat : ∀ (c : A ⟶ sectionSpace B U hU Z W₁ w₁) (T T' : BigFppfOver B U hU)
        (f : T' ⟶ T) (ξ : A.obj (op T)),
        sectionSpaceEquiv B U hU Z T' W₁ w₁ (c.app (op T') (A.map f.op ξ)) =
          SectionsOver.restrict f (sectionSpaceEquiv B U hU Z T W₁ w₁ (c.app (op T) ξ)) := by
      intro c T T' f ξ
      have h : c.app (op T') (A.map f.op ξ) =
          (sectionSpace B U hU Z W₁ w₁).map f.op (c.app (op T) ξ) :=
        ConcreteCategory.congr_hom (c.naturality f.op) ξ
      rw [h, sectionSpaceEquiv_restrict]
    rintro ⟨T⟩ ⟨T'⟩ f
    refine ConcreteCategory.hom_ext _ _ fun ξ => ?_
    change (sectionSpaceEquiv B U hU Z T' (pullback p p) (pullback.snd p p ≫ w₁)).symm
        (SectionsOver.pullbackLift hp
          (sectionSpaceEquiv B U hU Z T' W₁ w₁ (a.app (op T') (A.map f.unop.op ξ)))
          (sectionSpaceEquiv B U hU Z T' W₁ w₁ (b.app (op T') (A.map f.unop.op ξ)))
          (key T' (A.map f.unop.op ξ))) =
      (sectionSpace B U hU Z (pullback p p) (pullback.snd p p ≫ w₁)).map f.unop.op
        ((sectionSpaceEquiv B U hU Z T (pullback p p) (pullback.snd p p ≫ w₁)).symm
          (SectionsOver.pullbackLift hp (sectionSpaceEquiv B U hU Z T W₁ w₁ (a.app (op T) ξ))
            (sectionSpaceEquiv B U hU Z T W₁ w₁ (b.app (op T) ξ)) (key T ξ)))
    apply (sectionSpaceEquiv B U hU Z T' (pullback p p) (pullback.snd p p ≫ w₁)).injective
    have hres : (SectionsOver.restrict f.unop
          (sectionSpaceEquiv B U hU Z T W₁ w₁ (a.app (op T) ξ))).1 ≫ p =
        (SectionsOver.restrict f.unop
          (sectionSpaceEquiv B U hU Z T W₁ w₁ (b.app (op T) ξ))).1 ≫ p := by
      rw [← hnat a T T' f.unop ξ, ← hnat b T T' f.unop ξ]
      exact key T' (A.map f.unop.op ξ)
    rw [Equiv.apply_symm_apply, sectionSpaceEquiv_restrict, Equiv.apply_symm_apply,
      SectionsOver.restrict_pullbackLift hp f.unop _ _ (key T ξ) hres]
    refine Subtype.ext ?_
    rw [SectionsOver.pullbackLift_coe, SectionsOver.pullbackLift_coe]
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, pullback.lift_fst]
      exact congrArg Subtype.val (hnat a T T' f.unop ξ)
    · rw [pullback.lift_snd, pullback.lift_snd]
      exact congrArg Subtype.val (hnat b T T' f.unop ξ)

/-- The value of `AlgebraicGeometry.Space.sectionSpacePairLift` at a test object. -/
private theorem sectionSpaceEquiv_sectionSpacePairLift (hp : p ≫ w = w₁)
    {A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (a b : A ⟶ sectionSpace B U hU Z W₁ w₁)
    (key : ∀ (T : BigFppfOver B U hU) (ξ : A.obj (op T)),
      (sectionSpaceEquiv B U hU Z T W₁ w₁ (a.app (op T) ξ)).1 ≫ p =
        (sectionSpaceEquiv B U hU Z T W₁ w₁ (b.app (op T) ξ)).1 ≫ p)
    (T : BigFppfOver B U hU) (ξ : A.obj (op T)) :
    sectionSpaceEquiv B U hU Z T (pullback p p) (pullback.snd p p ≫ w₁)
        ((sectionSpacePairLift hp a b key).app (op T) ξ) =
      SectionsOver.pullbackLift hp (sectionSpaceEquiv B U hU Z T W₁ w₁ (a.app (op T) ξ))
        (sectionSpaceEquiv B U hU Z T W₁ w₁ (b.app (op T) ξ)) (key T ξ) :=
  Equiv.apply_symm_apply _ _

/-- **The space of sections of `W₁ ×_W W₁ ⟶ Z` is the kernel pair of the comparison morphism of
Stacks 05XR along `p : W₁ ⟶ W`.** A section of `(W₁ ×_W W₁)_T ⟶ Z_T` is a pair of sections of
`W₁_T ⟶ Z_T` with the same postcomposition with `p`, that is, a pair of points of the space of
sections of `w₁` over `T` with the same image in the space of sections of `w`.

No separatedness, étaleness or algebraicity hypothesis is used: the statement is the universal
property of the fibre product `W₁ ×_W W₁`, read on sections. -/
theorem isPullback_sectionSpaceMap_self (hp : p ≫ w = w₁) :
    IsPullback (sectionSpaceMap (pullback_fst_comp_eq_snd_comp hp))
      (sectionSpaceMap (rfl : pullback.snd p p ≫ w₁ = pullback.snd p p ≫ w₁))
      (sectionSpaceMap hp) (sectionSpaceMap hp) := by
  have hcomp : ∀ {X Y : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} {x : X ⟶ yoneda.obj Z}
      {y : Y ⟶ yoneda.obj Z} {g : X ⟶ Y} (hg : g ≫ y = x) {A : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
      {a b : A ⟶ sectionSpace B U hU Z X x}, a ≫ sectionSpaceMap hg = b ≫ sectionSpaceMap hg →
      ∀ (T : BigFppfOver B U hU) (ξ : A.obj (op T)),
        (sectionSpaceEquiv B U hU Z T X x (a.app (op T) ξ)).1 ≫ g =
          (sectionSpaceEquiv B U hU Z T X x (b.app (op T) ξ)).1 ≫ g := by
    intro X Y x y g hg A a b hab T ξ
    have h : (sectionSpaceMap hg).app (op T) (a.app (op T) ξ) =
        (sectionSpaceMap hg).app (op T) (b.app (op T) ξ) :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hab (op T)) ξ
    have h' := congrArg (fun t => (sectionSpaceEquiv B U hU Z T Y y t).1) h
    rwa [sectionSpaceEquiv_sectionSpaceMap, sectionSpaceEquiv_sectionSpaceMap,
      SectionsOver.pushforward_coe, SectionsOver.pushforward_coe] at h'
  refine IsPullback.mk' ?_ ?_ ?_
  · refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun s => ?_)
    obtain ⟨T⟩ := T₀
    apply (sectionSpaceEquiv B U hU Z T W w).injective
    show sectionSpaceEquiv B U hU Z T W w ((sectionSpaceMap hp).app (op T)
        ((sectionSpaceMap (pullback_fst_comp_eq_snd_comp hp)).app (op T) s)) =
      sectionSpaceEquiv B U hU Z T W w ((sectionSpaceMap hp).app (op T)
        ((sectionSpaceMap (rfl : pullback.snd p p ≫ w₁ = pullback.snd p p ≫ w₁)).app (op T) s))
    rw [sectionSpaceEquiv_sectionSpaceMap, sectionSpaceEquiv_sectionSpaceMap,
      sectionSpaceEquiv_sectionSpaceMap, sectionSpaceEquiv_sectionSpaceMap]
    refine Subtype.ext ?_
    rw [SectionsOver.pushforward_coe, SectionsOver.pushforward_coe,
      SectionsOver.pushforward_coe, SectionsOver.pushforward_coe, Category.assoc,
      Category.assoc, pullback.condition]
  · intro A φ φ' h₁ h₂
    refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun ξ => ?_)
    obtain ⟨T⟩ := T₀
    apply (sectionSpaceEquiv B U hU Z T (pullback p p) (pullback.snd p p ≫ w₁)).injective
    refine Subtype.ext (pullback.hom_ext ?_ ?_)
    · exact hcomp _ h₁ T ξ
    · exact hcomp _ h₂ T ξ
  · intro A a b hab
    have key := hcomp hp hab
    refine ⟨sectionSpacePairLift hp a b key, ?_, ?_⟩
    · refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun ξ => ?_)
      obtain ⟨T⟩ := T₀
      apply (sectionSpaceEquiv B U hU Z T W₁ w₁).injective
      show sectionSpaceEquiv B U hU Z T W₁ w₁
          ((sectionSpaceMap (pullback_fst_comp_eq_snd_comp hp)).app (op T)
            ((sectionSpacePairLift hp a b key).app (op T) ξ)) = _
      rw [sectionSpaceEquiv_sectionSpaceMap, sectionSpaceEquiv_sectionSpacePairLift]
      refine Subtype.ext ?_
      rw [SectionsOver.pushforward_coe, SectionsOver.pullbackLift_coe, pullback.lift_fst]
    · refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun ξ => ?_)
      obtain ⟨T⟩ := T₀
      apply (sectionSpaceEquiv B U hU Z T W₁ w₁).injective
      show sectionSpaceEquiv B U hU Z T W₁ w₁
          ((sectionSpaceMap (rfl : pullback.snd p p ≫ w₁ = pullback.snd p p ≫ w₁)).app (op T)
            ((sectionSpacePairLift hp a b key).app (op T) ξ)) = _
      rw [sectionSpaceEquiv_sectionSpaceMap, sectionSpaceEquiv_sectionSpacePairLift]
      refine Subtype.ext ?_
      rw [SectionsOver.pushforward_coe, SectionsOver.pullbackLift_coe, pullback.lift_snd]

end KernelPair

/-! ### The kernel pair of the comparison along a separated étale chart -/

section SeparatedChart

variable {B : BigFppfSite.{u}} {U : Scheme.{u}} {hU : B.Contains U}
  {Z V : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
  {w : W ⟶ yoneda.obj Z} {v : yoneda.obj V ⟶ yoneda.obj Z} {p : yoneda.obj V ⟶ W}

/-- **The space of sections of a chart of `W` with separated source is an algebraic space étale
over `U`.** This is Stacks 05XR for a separated `w`, read at a chart: a morphism out of the
representable presheaf of an object of the site whose scheme is separated is separated. -/
theorem isAlgebraicSpace_sectionSpace_chart
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V)) (hv : IsEtale B U hU v)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsAlgebraicSpace B U hU (sectionSpace B U hU Z (yoneda.obj V) v) :=
  isAlgebraicSpace_sectionSpace_of_isSeparated (isAlgebraicSpace_yoneda B U hU V) hv
    (isSeparated_of_scheme_isSeparated B U hU hV v) hZfin

/-- **The space of sections of a chart of `W` with separated source is étale over `U`.** -/
theorem isEtale_sectionSpace_chart
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V)) (hv : IsEtale B U hU v)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsEtale B U hU (terminal.from (sectionSpace B U hU Z (yoneda.obj V) v)) :=
  isEtale_sectionSpace_of_isSeparated (isAlgebraicSpace_yoneda B U hU V) hv
    (isSeparated_of_scheme_isSeparated B U hU hV v) hZfin

/-- The fibre product of a chart with itself is an algebraic space. -/
private theorem isAlgebraicSpace_pullback_chart_self (hW : IsAlgebraicSpace B U hU W) :
    IsAlgebraicSpace B U hU (pullback p p) :=
  isAlgebraicSpace_of_isPullback (isAlgebraicSpace_yoneda B U hU V)
    (isAlgebraicSpace_yoneda B U hU V) hW.isSheaf hW.diagonal_representable
    (IsPullback.of_hasPullback p p)

/-- The structure morphism of `V ×_W V` over `Z` is étale: it is a base change of the chart
followed by the chart's own structure morphism. -/
private theorem isEtale_pullback_chart_self (hW : IsAlgebraicSpace B U hU W)
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hw : IsEtale B U hU w) :
    IsEtale B U hU (pullback.snd p p ≫ v) :=
  isEtale_comp B U hU
    (isEtale_pullback_snd B U hU (isAlgebraicSpace_yoneda B U hU V) hW
      (isAlgebraicSpace_yoneda B U hU V) p p hpe)
    (hp ▸ isEtale_comp B U hU hpe hw)

/-- The structure morphism of `V ×_W V` over `Z` is separated: a base change of the chart,
which is separated because its source has separated scheme, followed by the chart's own
structure morphism, which is separated for the same reason. -/
private theorem isSeparated_pullback_chart_self
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V)) :
    IsSeparated B U hU (pullback.snd p p ≫ v) :=
  isSeparated_comp B U hU _ _
    (isSeparated_pullback B U hU p p (isSeparated_of_scheme_isSeparated B U hU hV p))
    (isSeparated_of_scheme_isSeparated B U hU hV v)

/-- **The space of sections of `(V ×_W V) ⟶ Z` is an algebraic space.** By
`AlgebraicGeometry.Space.isPullback_sectionSpaceMap_self` it is the kernel pair of the
comparison morphism of Stacks 05XR along the chart, and it is covered by Stacks 05XR for a
separated morphism, the two projections of `V ×_W V ⟶ V` being separated base changes of the
chart. -/
theorem isAlgebraicSpace_sectionSpace_pullback_chart (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsAlgebraicSpace B U hU
      (sectionSpace B U hU Z (pullback p p) (pullback.snd p p ≫ v)) :=
  isAlgebraicSpace_sectionSpace_of_isSeparated (isAlgebraicSpace_pullback_chart_self hW)
    (isEtale_pullback_chart_self hW hp hpe hw) (isSeparated_pullback_chart_self hV) hZfin

/-- **The space of sections of `(V ×_W V) ⟶ Z` is étale over `U`.** -/
theorem isEtale_sectionSpace_pullback_chart (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsEtale B U hU
      (terminal.from (sectionSpace B U hU Z (pullback p p) (pullback.snd p p ≫ v))) :=
  isEtale_sectionSpace_of_isSeparated (isAlgebraicSpace_pullback_chart_self hW)
    (isEtale_pullback_chart_self hW hp hpe hw) (isSeparated_pullback_chart_self hV) hZfin

/-- The diagonal of the chart is a section of both projections of `V ×_W V` over `Z`. -/
theorem diagonal_comp_snd_comp (_hp : p ≫ w = v) :
    pullback.diagonal p ≫ pullback.snd p p ≫ v = v := by
  rw [← Category.assoc, pullback.diagonal_snd, Category.id_comp]

/-- **The two projections of the kernel pair are étale**, by the cancellation law: both the
space of sections of `(V ×_W V) ⟶ Z` and the space of sections of `V ⟶ Z` are algebraic spaces
étale over `U`. -/
theorem isEtale_sectionSpaceMap_pullback_snd (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsEtale B U hU
      (sectionSpaceMap (rfl : pullback.snd p p ≫ v = pullback.snd p p ≫ v)) :=
  isEtale_of_isEtale_terminal_from B U hU
    (isAlgebraicSpace_sectionSpace_pullback_chart hW hV hp hpe hw hZfin)
    (isAlgebraicSpace_sectionSpace_chart hV (hp ▸ isEtale_comp B U hU hpe hw) hZfin)
    (isEtale_sectionSpace_pullback_chart hW hV hp hpe hw hZfin)
    (isEtale_sectionSpace_chart hV (hp ▸ isEtale_comp B U hU hpe hw) hZfin) _

/-- **The other projection of the kernel pair is étale.** -/
theorem isEtale_sectionSpaceMap_pullback_fst (hW : IsAlgebraicSpace B U hU W)
    (hV : Scheme.IsSeparated ((BigFppfOver.toScheme B U hU).obj V))
    (hp : p ≫ w = v) (hpe : IsEtale B U hU p) (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsEtale B U hU (sectionSpaceMap (pullback_fst_comp_eq_snd_comp hp)) :=
  isEtale_of_isEtale_terminal_from B U hU
    (isAlgebraicSpace_sectionSpace_pullback_chart hW hV hp hpe hw hZfin)
    (isAlgebraicSpace_sectionSpace_chart hV (hp ▸ isEtale_comp B U hU hpe hw) hZfin)
    (isEtale_sectionSpace_pullback_chart hW hV hp hpe hw hZfin)
    (isEtale_sectionSpace_chart hV (hp ▸ isEtale_comp B U hU hpe hw) hZfin) _

/-- The diagonal of the chart induces a section of the second projection of the kernel pair. -/
theorem sectionSpaceMap_diagonal_comp_snd (hp : p ≫ w = v) :
    sectionSpaceMap (diagonal_comp_snd_comp hp) ≫
        sectionSpaceMap (rfl : pullback.snd p p ≫ v = pullback.snd p p ≫ v) =
      𝟙 (sectionSpace B U hU Z (yoneda.obj V) v) := by
  refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun s => ?_)
  obtain ⟨T⟩ := T₀
  apply (sectionSpaceEquiv B U hU Z T (yoneda.obj V) v).injective
  show sectionSpaceEquiv B U hU Z T (yoneda.obj V) v
      ((sectionSpaceMap (rfl : pullback.snd p p ≫ v = pullback.snd p p ≫ v)).app (op T)
        ((sectionSpaceMap (diagonal_comp_snd_comp hp)).app (op T) s)) =
      sectionSpaceEquiv B U hU Z T (yoneda.obj V) v s
  rw [sectionSpaceEquiv_sectionSpaceMap, sectionSpaceEquiv_sectionSpaceMap]
  refine Subtype.ext ?_
  rw [SectionsOver.pushforward_coe, SectionsOver.pushforward_coe, Category.assoc,
    pullback.diagonal_snd, Category.comp_id]

/-- The diagonal of the chart induces a section of the first projection of the kernel pair. -/
theorem sectionSpaceMap_diagonal_comp_fst (hp : p ≫ w = v) :
    sectionSpaceMap (diagonal_comp_snd_comp hp) ≫
        sectionSpaceMap (pullback_fst_comp_eq_snd_comp hp) =
      𝟙 (sectionSpace B U hU Z (yoneda.obj V) v) := by
  refine NatTrans.ext (funext fun T₀ => ConcreteCategory.hom_ext _ _ fun s => ?_)
  obtain ⟨T⟩ := T₀
  apply (sectionSpaceEquiv B U hU Z T (yoneda.obj V) v).injective
  show sectionSpaceEquiv B U hU Z T (yoneda.obj V) v
      ((sectionSpaceMap (pullback_fst_comp_eq_snd_comp hp)).app (op T)
        ((sectionSpaceMap (diagonal_comp_snd_comp hp)).app (op T) s)) =
      sectionSpaceEquiv B U hU Z T (yoneda.obj V) v s
  rw [sectionSpaceEquiv_sectionSpaceMap, sectionSpaceEquiv_sectionSpaceMap]
  refine Subtype.ext ?_
  rw [SectionsOver.pushforward_coe, SectionsOver.pushforward_coe, Category.assoc,
    pullback.diagonal_fst, Category.comp_id]

/-- **The two projections of the kernel pair are surjective on points**, the diagonal of the
chart inducing a section of each. -/
theorem isSurjective_sectionSpaceMap_pullback_snd (hp : p ≫ w = v) :
    IsSurjective B U hU
      (sectionSpaceMap (rfl : pullback.snd p p ≫ v = pullback.snd p p ≫ v)) :=
  isSurjective_of_comp_eq_id B U hU (sectionSpaceMap_diagonal_comp_snd hp)

/-- **The other projection of the kernel pair is surjective on points.** -/
theorem isSurjective_sectionSpaceMap_pullback_fst (hp : p ≫ w = v) :
    IsSurjective B U hU (sectionSpaceMap (pullback_fst_comp_eq_snd_comp hp)) :=
  isSurjective_of_comp_eq_id B U hU (sectionSpaceMap_diagonal_comp_fst hp)

end SeparatedChart

end AlgebraicGeometry.Space

end
