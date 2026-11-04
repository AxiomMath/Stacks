module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.OpenCoverGlue
public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Glue
public import StacksFrontier.AlgebraicGeometry.LimitApproxFunctor.Stage
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint

/-!
# Relative gluing along a two-member open cover

Let `S` be a scheme and let `U`, `W` be two opens with `U ⊔ W = ⊤`.  Given a scheme `A` over
`U`, a scheme `B` over `W` and an identification of their restrictions to `U ⊓ W`, there is a
scheme `X` over `S` restricting to `A` over `U` and to `B` over `W`, and it is of finite
presentation as soon as `A` and `B` are.

This is the object half of [Stacks, Tag 01LG](https://stacks.math.columbia.edu/tag/01LG) for a
cover with two members, and the gluing step of
[Stacks, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA).

## Main definitions

* `AlgebraicGeometry.glueCharts`: the glued scheme, as an object of `CategoryTheory.Over S`.

## Main results

* `AlgebraicGeometry.isPullback_gluePairInl_glueCharts` and
  `AlgebraicGeometry.isPullback_gluePairInr_glueCharts`: the two charts are the restrictions of
  the glued scheme to `U` and to `W`.
* `AlgebraicGeometry.property_glueCharts_hom`: a property local on the target holds for the
  structure morphism of the glued scheme as soon as it holds for the two charts.
* `AlgebraicGeometry.finitePresentation_glueCharts_hom`: the glued scheme is of finite
  presentation over `S`.
* `AlgebraicGeometry.exists_finitePresentation_isPullback_of_overPullbackIso`: an isomorphism
  of the chosen base changes to `U ⊓ W` of two schemes of finite presentation over `U` and over
  `W` glues to a scheme of finite presentation over `S` with cartesian squares over `U` and over
  `W`.

## References

* [Stacks Project, Tag 01LG](https://stacks.math.columbia.edu/tag/01LG)
* [Stacks Project, Tag 0BPA](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A property local on the target transfers across a cartesian square whose vertical legs
are open immersions.**  If the square
```
A' --iA--> A
 |         |
m'         m
 v         v
B' --iB--> B
```
is cartesian with `iA` and `iB` open immersions, then the restriction of `m` over the image of
`iB` has every isomorphism-invariant property that `m'` has. -/
lemma property_morphismRestrict_of_isPullback (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {A B A' B' : Scheme.{u}} {m : A ⟶ B} {iB : B' ⟶ B} [IsOpenImmersion iB]
    {iA : A' ⟶ A} {m' : A' ⟶ B'} (h : IsPullback iA m' m iB) (hm' : P m') :
    P (m ∣_ iB.opensRange) := by
  have : HasPullback m iB := h.hasPullback
  refine (MorphismProperty.arrow_mk_iso_iff P (morphismRestrictOpensRange m iB)).mpr ?_
  rwa [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso P]

section TwoChart

attribute [local implicit_reducible] CategoryTheory.MorphismProperty
  AlgebraicGeometry.AffineTargetMorphismProperty

variable {S : Scheme.{u}} {U W : S.Opens} {A B C : Scheme.{u}}
  (a : A ⟶ (U : Scheme.{u})) (b : B ⟶ (W : Scheme.{u}))
  (c : C ⟶ ((U ⊓ W : S.Opens) : Scheme.{u})) (f : C ⟶ A) (g : C ⟶ B)
  [IsOpenImmersion f] [IsOpenImmersion g]

/-- The structure morphism of the glued scheme: the morphism out of the glueing of the two
charts determined by their own structure morphisms, which agree over `U ⊓ W`. -/
noncomputable def glueChartsHom
    (hf : f ≫ a = c ≫ S.homOfLE (inf_le_left : U ⊓ W ≤ U))
    (hg : g ≫ b = c ≫ S.homOfLE (inf_le_right : U ⊓ W ≤ W)) :
    Scheme.gluePair f g ⟶ S :=
  Scheme.gluePairDesc f g (a ≫ U.ι) (b ≫ W.ι) <| by
    rw [← Category.assoc, ← Category.assoc, hf, hg, Category.assoc, Category.assoc,
      S.homOfLE_ι, S.homOfLE_ι]

variable (hf : f ≫ a = c ≫ S.homOfLE (inf_le_left : U ⊓ W ≤ U))
  (hg : g ≫ b = c ≫ S.homOfLE (inf_le_right : U ⊓ W ≤ W))

/-- Restricted to the first chart, the structure morphism of the glued scheme is the structure
morphism `a` of that chart followed by the inclusion of `U`. -/
@[reassoc (attr := simp)]
lemma gluePairInl_glueChartsHom :
    Scheme.gluePairInl f g ≫ glueChartsHom a b c f g hf hg = a ≫ U.ι :=
  Scheme.gluePairInl_desc _ _ _ _ _

/-- Restricted to the second chart, the structure morphism of the glued scheme is the structure
morphism `b` of that chart followed by the inclusion of `W`. -/
@[reassoc (attr := simp)]
lemma gluePairInr_glueChartsHom :
    Scheme.gluePairInr f g ≫ glueChartsHom a b c f g hf hg = b ≫ W.ι :=
  Scheme.gluePairInr_desc _ _ _ _ _

/-- The structure morphism of the glued scheme is the induced morphism of glueings followed by
the identification of `S` with the glueing of `U` and `W` along `U ⊓ W`. -/
lemma glueChartsHom_eq_gluePairMap_comp :
    glueChartsHom a b c f g hf hg =
      Scheme.gluePairMap c a b hf hg ≫ Scheme.gluePairOpensHom S U W :=
  Scheme.gluePair_hom_ext f g
    ((gluePairInl_glueChartsHom a b c f g hf hg).trans
      (by rw [Scheme.gluePairInl_gluePairMap_assoc, Scheme.gluePairInl_gluePairOpensHom]))
    ((gluePairInr_glueChartsHom a b c f g hf hg).trans
      (by rw [Scheme.gluePairInr_gluePairMap_assoc, Scheme.gluePairInr_gluePairOpensHom]))

/-- `U` pulls back to the first leg of the glueing. -/
lemma preimage_glueChartsHom_left
    (hgr : b ⁻¹ᵁ (S.homOfLE (inf_le_right : U ⊓ W ≤ W)).opensRange = g.opensRange) :
    glueChartsHom a b c f g hf hg ⁻¹ᵁ U = (Scheme.gluePairInl f g).opensRange := by
  rw [glueChartsHom_eq_gluePairMap_comp, Scheme.Hom.comp_preimage,
    Scheme.preimage_gluePairOpensHom_left,
    Scheme.preimage_opensRange_gluePairInl_gluePairMap c a b hf hg hgr]

/-- `W` pulls back to the second leg of the glueing. -/
lemma preimage_glueChartsHom_right
    (hfr : a ⁻¹ᵁ (S.homOfLE (inf_le_left : U ⊓ W ≤ U)).opensRange = f.opensRange) :
    glueChartsHom a b c f g hf hg ⁻¹ᵁ W = (Scheme.gluePairInr f g).opensRange := by
  rw [glueChartsHom_eq_gluePairMap_comp, Scheme.Hom.comp_preimage,
    Scheme.preimage_gluePairOpensHom_right,
    Scheme.preimage_opensRange_gluePairInr_gluePairMap c a b hf hg hfr]

/-- **The first chart is the restriction of the glued scheme to `U`.** -/
lemma isPullback_gluePairInl_glueCharts
    (hgr : b ⁻¹ᵁ (S.homOfLE (inf_le_right : U ⊓ W ≤ W)).opensRange = g.opensRange) :
    IsPullback a (Scheme.gluePairInl f g) U.ι (glueChartsHom a b c f g hf hg) :=
  IsOpenImmersion.isPullback a (Scheme.gluePairInl f g) U.ι _
    (gluePairInl_glueChartsHom a b c f g hf hg)
    ((congrArg (glueChartsHom a b c f g hf hg ⁻¹ᵁ ·) U.opensRange_ι).trans
      (preimage_glueChartsHom_left a b c f g hf hg hgr))

/-- **The second chart is the restriction of the glued scheme to `W`.** -/
lemma isPullback_gluePairInr_glueCharts
    (hfr : a ⁻¹ᵁ (S.homOfLE (inf_le_left : U ⊓ W ≤ U)).opensRange = f.opensRange) :
    IsPullback b (Scheme.gluePairInr f g) W.ι (glueChartsHom a b c f g hf hg) :=
  IsOpenImmersion.isPullback b (Scheme.gluePairInr f g) W.ι _
    (gluePairInr_glueChartsHom a b c f g hf hg)
    ((congrArg (glueChartsHom a b c f g hf hg ⁻¹ᵁ ·) W.opensRange_ι).trans
      (preimage_glueChartsHom_right a b c f g hf hg hfr))

/-- **A property local on the target holds for the glued scheme as soon as it holds for the two
charts.** -/
lemma property_glueCharts_hom (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hUW : U ⊔ W = ⊤)
    (hfr : a ⁻¹ᵁ (S.homOfLE (inf_le_left : U ⊓ W ≤ U)).opensRange = f.opensRange)
    (hgr : b ⁻¹ᵁ (S.homOfLE (inf_le_right : U ⊓ W ≤ W)).opensRange = g.opensRange)
    (ha : P a) (hb : P b) : P (glueChartsHom a b c f g hf hg) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun t : Bool ↦ cond t U.ι.opensRange W.ι.opensRange) ?_ fun t ↦ ?_
  · rwa [iSup_bool_eq, U.opensRange_ι, W.opensRange_ι]
  · cases t
    · exact property_morphismRestrict_of_isPullback P
        (isPullback_gluePairInr_glueCharts a b c f g hf hg hfr).flip hb
    · exact property_morphismRestrict_of_isPullback P
        (isPullback_gluePairInl_glueCharts a b c f g hf hg hgr).flip ha

/-- **The glued scheme is of finite presentation over `S`** as soon as both charts are. -/
lemma finitePresentation_glueCharts_hom (hUW : U ⊔ W = ⊤)
    (hfr : a ⁻¹ᵁ (S.homOfLE (inf_le_left : U ⊓ W ≤ U)).opensRange = f.opensRange)
    (hgr : b ⁻¹ᵁ (S.homOfLE (inf_le_right : U ⊓ W ≤ W)).opensRange = g.opensRange)
    (ha : FinitePresentation a) (hb : FinitePresentation b) :
    FinitePresentation (glueChartsHom a b c f g hf hg) :=
  ⟨property_glueCharts_hom a b c f g hf hg @LocallyOfFinitePresentation hUW hfr hgr ha.1 hb.1,
    property_glueCharts_hom a b c f g hf hg @QuasiCompact hUW hfr hgr ha.2.1 hb.2.1,
    property_glueCharts_hom a b c f g hf hg @QuasiSeparated hUW hfr hgr ha.2.2 hb.2.2⟩

/-- The glued scheme, as an object over `S`. -/
noncomputable def glueCharts : Over S :=
  Over.mk (glueChartsHom a b c f g hf hg)

/-- The structure morphism of `glueCharts` is `glueChartsHom`. -/
@[simp]
lemma glueCharts_hom : (glueCharts a b c f g hf hg).hom = glueChartsHom a b c f g hf hg :=
  rfl

end TwoChart

section ChosenPullback

/-- **Gluing two schemes of finite presentation along an isomorphism over the overlap.**  Two opens
covering `S`, a scheme of finite presentation over each of them, and an isomorphism of their
chosen base changes to `U ⊓ W` produce a scheme of finite presentation over `S` whose
restrictions to `U` and to `W` are the two given schemes, compatibly with the given
isomorphism. -/
theorem exists_finitePresentation_isPullback_of_overPullbackIso {S : Scheme.{u}} {U W : S.Opens}
    (hUW : U ⊔ W = ⊤) {A B : Scheme.{u}} (a : A ⟶ (U : Scheme.{u}))
    (b : B ⟶ (W : Scheme.{u})) (ha : FinitePresentation a) (hb : FinitePresentation b)
    (φ : (Over.pullback (S.homOfLE (inf_le_left : U ⊓ W ≤ U))).obj (Over.mk a) ≅
      (Over.pullback (S.homOfLE (inf_le_right : U ⊓ W ≤ W))).obj (Over.mk b)) :
    ∃ (X : Scheme.{u}) (p : X ⟶ S) (jU : A ⟶ X) (jW : B ⟶ X),
      FinitePresentation p ∧ IsPullback a jU U.ι p ∧ IsPullback b jW W.ι p ∧
        pullback.fst a (S.homOfLE (inf_le_left : U ⊓ W ≤ U)) ≫ jU =
          φ.hom.left ≫
            pullback.fst b (S.homOfLE (inf_le_right : U ⊓ W ≤ W)) ≫ jW := by
  have hiso : IsIso φ.hom.left := ((Over.forget _).mapIso φ).isIso_hom
  have hw : φ.hom.left ≫ pullback.snd b (S.homOfLE (inf_le_right : U ⊓ W ≤ W)) =
      pullback.snd a (S.homOfLE (inf_le_left : U ⊓ W ≤ U)) := Over.w φ.hom
  have hf : pullback.fst a (S.homOfLE (inf_le_left : U ⊓ W ≤ U)) ≫ a =
      pullback.snd a (S.homOfLE (inf_le_left : U ⊓ W ≤ U)) ≫
        S.homOfLE (inf_le_left : U ⊓ W ≤ U) := pullback.condition
  have hg : (φ.hom.left ≫ pullback.fst b (S.homOfLE (inf_le_right : U ⊓ W ≤ W))) ≫ b =
      pullback.snd a (S.homOfLE (inf_le_left : U ⊓ W ≤ U)) ≫
        S.homOfLE (inf_le_right : U ⊓ W ≤ W) := by
    rw [Category.assoc, pullback.condition (f := b)
      (g := S.homOfLE (inf_le_right : U ⊓ W ≤ W)), ← Category.assoc, hw]
  have hfr : a ⁻¹ᵁ (S.homOfLE (inf_le_left : U ⊓ W ≤ U)).opensRange =
      (pullback.fst a (S.homOfLE (inf_le_left : U ⊓ W ≤ U))).opensRange :=
    preimage_opensRange_of_isPullback
      (IsPullback.of_hasPullback a (S.homOfLE (inf_le_left : U ⊓ W ≤ U)))
  have hgr : b ⁻¹ᵁ (S.homOfLE (inf_le_right : U ⊓ W ≤ W)).opensRange =
      (φ.hom.left ≫ pullback.fst b (S.homOfLE (inf_le_right : U ⊓ W ≤ W))).opensRange :=
    (preimage_opensRange_of_isPullback
        (IsPullback.of_hasPullback b (S.homOfLE (inf_le_right : U ⊓ W ≤ W)))).trans
      (Scheme.Hom.opensRange_comp_of_isIso φ.hom.left
        (pullback.fst b (S.homOfLE (inf_le_right : U ⊓ W ≤ W)))).symm
  exact ⟨_, glueChartsHom a b (pullback.snd a (S.homOfLE (inf_le_left : U ⊓ W ≤ U))) _ _ hf hg,
    Scheme.gluePairInl _ _, Scheme.gluePairInr _ _,
    finitePresentation_glueCharts_hom a b _ _ _ hf hg hUW hfr hgr ha hb,
    isPullback_gluePairInl_glueCharts a b _ _ _ hf hg hgr,
    isPullback_gluePairInr_glueCharts a b _ _ _ hf hg hfr,
    (Scheme.gluePair_condition _ _).trans (Category.assoc _ _ _)⟩

end ChosenPullback

end AlgebraicGeometry

end
