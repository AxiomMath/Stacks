module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeModel

/-!
# The chosen affine models of the stage base changes are cartesian over the stages

Let `R` be a topological ring presenting an affine formal algebraic space `Spf R` over `S` and
let `v : V ⟶ Spf R` be a morphism from an affine formal algebraic space which is representable
by algebraic spaces and étale. `AlgebraicGeometry.FormalSpace.stageBaseChangeModel` chooses, for
every weak ideal of definition `J ⊆ R`, an affine object of the site representing

`Spec (R ⧸ J) ×_{Spf R} V`

together with its projection to the stage `Spec (R ⧸ J)`. The transition square

```
Spec (Ā_J) ⟶ Spec (Ā_K)
    ↓             ↓
Spec (R ⧸ J) ⟶ Spec (R ⧸ K)
```

over an inclusion `K ⊆ J` of weak ideals of definition is cartesian, and so is the
corresponding square of rings: `Ā_J = Ā_K ⊗_{R ⧸ K} R ⧸ J`.

## Main results

* `AlgebraicGeometry.FormalSpace.isPullback_map_stageBaseChangeModelMap`: the square of sheaves.
* `AlgebraicGeometry.FormalSpace.isPullback_stageBaseChangeModelMap_site`: the square in the
  site.
* `AlgebraicGeometry.FormalSpace.isPullback_stageBaseChangeModelMap`: the square of schemes.
* `AlgebraicGeometry.FormalSpace.isPushout_appTop_stageBaseChangeModelMap`: the pushout square
  of global sections.
* `AlgebraicGeometry.FormalSpace.isPushout_stageBaseChangeRingHom`: the pushout square of rings
  over the quotients of `R`.

## References

* [Stacks Project, Tag 0AN8](https://stacks.math.columbia.edu/tag/0AN8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

attribute [local instance] sheaf_hasColimits

/-- Transporting a commuting square through a conjugation by two isomorphisms. -/
private theorem comp_iso_conj' {C : Type*} [Category C] {A₁ P₁ A₂ P₂ T₁ T₂ : C}
    (e₁ : A₁ ≅ P₁) (e₂ : A₂ ≅ P₂) (m : P₁ ⟶ P₂) (t : T₁ ⟶ T₂) {p₁ : P₁ ⟶ T₁} {p₂ : P₂ ⟶ T₂}
    {a₁ : A₁ ⟶ T₁} {a₂ : A₂ ⟶ T₂} (h₁ : e₁.hom ≫ p₁ = a₁) (h₂ : e₂.hom ≫ p₂ = a₂)
    (hm : m ≫ p₂ = p₁ ≫ t) : (e₁.hom ≫ m ≫ e₂.inv) ≫ a₂ = a₁ ≫ t := by
  rw [← h₁, ← h₂, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, hm]

/-- Replacing two edges of a cartesian square by equal morphisms. -/
private theorem isPullback_of_eq {C : Type*} [Category C] {P X Y Z : C} {fst fst' : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g g' : Y ⟶ Z} (h : IsPullback fst snd f g) (e₁ : fst = fst')
    (e₂ : g = g') : IsPullback fst' snd f g' := e₁ ▸ e₂ ▸ h

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}
  {R : Type u} [CommRing R] [TopologicalSpace R] (D : QuotientSystem 𝔅 S hS R)
  {V : FppfSheaf 𝔅 S hS} (v : V ⟶ formalSpectrum D)
  (hY : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum D))
  (hV : IsAffineFormalAlgebraicSpace 𝔅 S hS V) (hv : IsRepresentableEtale 𝔅 S hS v)

/-- The sheafified Yoneda image of the transition morphism of the chosen affine models is the
transition of the stage base changes, conjugated by the identifications
`AlgebraicGeometry.FormalSpace.isoStageBaseChange`. -/
theorem map_stageBaseChangeModelMap {J K : WeakIdeals R} (g : J ⟶ K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (stageBaseChangeModelMap D v hY hV hv g) =
      (isoStageBaseChange D v hY hV hv J).hom ≫ (stageBaseChangeDiagram D v).map g ≫
        (isoStageBaseChange D v hY hV hv K).inv :=
  (sheafifiedYonedaFF 𝔅 S hS).map_preimage _

/-- The transition morphism of the chosen affine models is compatible with their projections to
the source of the chart. -/
theorem map_stageBaseChangeModelMap_comp_fst {J K : WeakIdeals R} (g : J ⟶ K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          (stageBaseChangeModelMap D v hY hV hv g) ≫
        (stageBaseChangeModel D v hY hV hv K).fst =
      (stageBaseChangeModel D v hY hV hv J).fst := by
  rw [map_stageBaseChangeModelMap]
  exact (comp_iso_conj' _ _ _ (𝟙 _) (isoStageBaseChange_hom_snd D v hY hV hv J)
    (isoStageBaseChange_hom_snd D v hY hV hv K)
    ((baseChangeDiagram_map_snd (colimit.cocone (formalSpectrumDiagram D)) v g).trans
      (Category.comp_id _).symm)).trans (Category.comp_id _)

/-- The transition morphism of the chosen affine models lies over the transition morphism of the
quotient stages. -/
theorem map_stageBaseChangeModelMap_comp_proj {J K : WeakIdeals R} (g : J ⟶ K) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          (stageBaseChangeModelMap D v hY hV hv g) ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          (stageBaseChangeModel D v hY hV hv K).proj =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          (stageBaseChangeModel D v hY hV hv J).proj ≫
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
          ((BigAffineFppf.inclusion 𝔅 S hS).map (D.diagram.map g)) := by
  rw [map_stageBaseChangeModelMap]
  exact comp_iso_conj' _ _ _ _ (isoStageBaseChange_hom_fst D v hY hV hv J)
    (isoStageBaseChange_hom_fst D v hY hV hv K)
    (baseChangeDiagram_map_fst (colimit.cocone (formalSpectrumDiagram D)) v g)

/-- The chosen affine models of the stage base changes are cartesian over the stages, as a square
of fppf sheaves. -/
theorem isPullback_map_stageBaseChangeModelMap {J K : WeakIdeals R} (g : J ⟶ K) :
    IsPullback
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (stageBaseChangeModelMap D v hY hV hv g))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (stageBaseChangeModel D v hY hV hv J).proj)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        (stageBaseChangeModel D v hY hV hv K).proj)
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        ((BigAffineFppf.inclusion 𝔅 S hS).map (D.diagram.map g))) := by
  have hw : (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS)).map
        ((BigAffineFppf.inclusion 𝔅 S hS).map (D.diagram.map g)) ≫
      formalSpectrumInclusion D K = formalSpectrumInclusion D J :=
    colimit.w (formalSpectrumDiagram D) g
  exact IsPullback.of_right
    (isPullback_of_eq (stageBaseChangeModel D v hY hV hv J).isPullback
      (map_stageBaseChangeModelMap_comp_fst D v hY hV hv g).symm hw.symm)
    (map_stageBaseChangeModelMap_comp_proj D v hY hV hv g)
    (stageBaseChangeModel D v hY hV hv K).isPullback

/-- The chosen affine models of the stage base changes are cartesian over the stages, as a square
of the site. -/
theorem isPullback_stageBaseChangeModelMap_site {J K : WeakIdeals R} (g : J ⟶ K) :
    IsPullback (stageBaseChangeModelMap D v hY hV hv g)
      (stageBaseChangeModel D v hY hV hv J).proj
      (stageBaseChangeModel D v hY hV hv K).proj
      ((BigAffineFppf.inclusion 𝔅 S hS).map (D.diagram.map g)) := by
  have _ := (sheafifiedYonedaFF 𝔅 S hS).full
  have _ := (sheafifiedYonedaFF 𝔅 S hS).faithful
  exact IsPullback.of_map_of_faithful (Sheaf.sheafifiedYoneda (BigFppfOver.topology 𝔅 S hS))
    (isPullback_map_stageBaseChangeModelMap D v hY hV hv g)

/-- The chosen affine models of the stage base changes are cartesian over the stages, as a square
of schemes. -/
theorem isPullback_stageBaseChangeModelMap {J K : WeakIdeals R} (g : J ⟶ K) :
    IsPullback
      ((BigFppfOver.toScheme 𝔅 S hS).map (stageBaseChangeModelMap D v hY hV hv g))
      ((BigFppfOver.toScheme 𝔅 S hS).map (stageBaseChangeModel D v hY hV hv J).proj)
      ((BigFppfOver.toScheme 𝔅 S hS).map (stageBaseChangeModel D v hY hV hv K).proj)
      ((BigAffineFppf.toScheme 𝔅 S hS).map (D.diagram.map g)) := by
  let _ := 𝔅.hasPullbacks_schemes
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.forget 𝔅 S hS) := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan 𝔅.inclusion := inferInstance
  let _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme 𝔅 S hS) :=
    comp_preservesLimitsOfShape _ _
  exact (isPullback_stageBaseChangeModelMap_site D v hY hV hv g).map
    (BigFppfOver.toScheme 𝔅 S hS)

/-- The coordinate rings of the chosen affine models base change along the stage transitions:
`Ā_J` is the pushout of `Ā_K` and `R ⧸ J` over `R ⧸ K`, i.e. `Ā_J = Ā_K ⊗_{R ⧸ K} R ⧸ J`, as a
square of global sections. -/
theorem isPushout_appTop_stageBaseChangeModelMap {J K : WeakIdeals R} (g : J ⟶ K) :
    IsPushout
      ((BigFppfOver.toScheme 𝔅 S hS).map
        (stageBaseChangeModel D v hY hV hv K).proj).appTop
      ((BigAffineFppf.toScheme 𝔅 S hS).map (D.diagram.map g)).appTop
      ((BigFppfOver.toScheme 𝔅 S hS).map (stageBaseChangeModelMap D v hY hV hv g)).appTop
      ((BigFppfOver.toScheme 𝔅 S hS).map (stageBaseChangeModel D v hY hV hv J).proj).appTop := by
  have _ := (stageBaseChangeModel D v hY hV hv K).isAffine
  have _ := isAffine_toScheme_stage D (hS := hS) J
  have _ := isAffine_toScheme_stage D (hS := hS) K
  exact isPushout_appTop_of_isPullback (isPullback_stageBaseChangeModelMap D v hY hV hv g)

/-- The coordinate rings of the chosen affine models base change along the stage transitions,
with the quotients of `R` themselves for the base: `Ā_J` is the pushout of `Ā_K` and `R ⧸ J`
over `R ⧸ K`, the two structure maps being `AlgebraicGeometry.FormalSpace.stageBaseChangeRingHom`
and the quotient transition `Ideal.Quotient.factor`. -/
theorem isPushout_stageBaseChangeRingHom {J K : WeakIdeals R} (g : J ⟶ K) :
    IsPushout (CommRingCat.ofHom (stageBaseChangeRingHom D v hY hV hv K))
      (CommRingCat.ofHom (Ideal.Quotient.factor
        (show (OrderDual.ofDual K).1 ≤ (OrderDual.ofDual J).1 from leOfHom g)))
      ((BigFppfOver.toScheme 𝔅 S hS).map
        (stageBaseChangeModelMap D v hY hV hv g)).appTop
      (CommRingCat.ofHom (stageBaseChangeRingHom D v hY hV hv J)) := by
  refine (isPushout_appTop_stageBaseChangeModelMap D v hY hV hv g).of_iso'
    (Scheme.ΓSpecIso (.of (R ⧸ (OrderDual.ofDual K).1))).symm (Iso.refl _)
    (Scheme.ΓSpecIso (.of (R ⧸ (OrderDual.ofDual J).1))).symm (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).symm
  · exact (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.factor
      (show (OrderDual.ofDual K).1 ≤ (OrderDual.ofDual J).1 from leOfHom g)))).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact (Category.comp_id _).symm

end AlgebraicGeometry.FormalSpace

end
