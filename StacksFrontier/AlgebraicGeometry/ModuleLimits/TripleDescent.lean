module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.ReflectIso
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismGlue
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFreeUnconditional
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSquarePaste
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending an isomorphism, and a compatible triple, through a cofiltered limit

Let `S = lim Sᵢ` be the limit of a cofiltered system of quasi-compact quasi-separated schemes
with affine transition morphisms.  [Stacks, Tag 01ZR] (2) descends a *morphism* between the
pullbacks to `S` of two finitely presented modules at a stage, and
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isIso_pullback_map_of_isLimit` reflects
invertibility.  This file puts the two together, and then uses the result to descend the datum a
*cospan of limit systems* carries: a module on each of two systems together with an isomorphism
between their restrictions to a third.

That is the shape the Noetherian reduction opening the proof of [Stacks, Tag 0EXD] consumes: a
compatible triple `(ℱ, 𝒢, φ)` on the centre, the modification and the exceptional line of an
almost blowup square, to be descended to one Noetherian stage.  Nothing here is about almost
blowup squares; the two restriction maps are arbitrary morphisms of diagrams compatible with the
three limit cones.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_iso_of_pullback_iso`: **an isomorphism
  between the pullbacks to the limit of two finitely presented modules at a stage is, through the
  canonical identifications, the pullback of an isomorphism at some earlier stage.**  This is
  [Stacks, Tag 01ZR] (2) in its canonically pinned form followed by the reflection of
  isomorphisms, with the resulting change of stage absorbed by the pentagon.
* `Stacks.AlgebraicGeometry.ModuleLimits.sqIso_paste_vert`: **the vertical pasting law for the
  square comparison of iterated pullbacks**, two commuting squares sharing an edge.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_compatibleTriple`: **a compatible triple
  over the limits of a cospan of systems descends**, comparison included — the two modules to
  one stage and the comparison to a stage over it.
* `Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_compatibleTriple_single`: the same with the
  two stages merged, so that the whole triple lives over **one** stage.

## Implementation notes

The comparison of a module pulled back from a stage along one leg of the cospan with the same
module pulled back along the other route is `Stacks.AlgebraicGeometry.ModuleLimits.sqIso`, the
natural isomorphism of iterated pullback functors across a commuting square.  Both statements are
phrased with it rather than with `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` written out, so that the compatibility of the
descended comparison with the given one is a single equation between morphisms
`uc^* ℱ ⟶ um^* 𝒢` over the limit of the third system.

**Why the stage changes twice.**  Tag 01ZR (2) descends the comparison to a stage `k`; the
descended morphism need not be invertible there, and invertibility is recovered only at a further
stage `l` over `k`.  The two canonical identifications for `l ⟶ k` and `k ⟶ j` are merged into
the one for `l ⟶ j` by the pentagon
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp`, which is why the conclusion of
`exists_stage_iso_of_pullback_iso` mentions only the single transition morphism `D.map e`.  The
*modules* of a triple and its *comparison* are descended by two separate appeals, so they land on
two stages, and merging those is a second pasting — of the stage square at the later stage
against the naturality square of the diagram morphism — which is `sqIso_paste_vert`.

## References

* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

namespace Stacks.AlgebraicGeometry.ModuleLimits

/-! ### Pasting two commuting squares vertically -/

/-- `Stacks.AlgebraicGeometry.ModuleLimits.sqIso` written with
`Stacks.AlgebraicGeometry.ModuleLimits.canNatIso`: crossing a commuting square is the canonical
identification for its top-and-right route followed by the inverse of the one for its
left-and-bottom route.  Both `AlgebraicGeometry.Scheme.Modules.pullbackCongr` factors cancel, by
`pullbackCongr_rfl_hom_app` and `pullbackCongr_symm_hom_app`. -/
theorem canHom_comp_canNatIso_inv_app {A B C E : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ E)
    (w : A ⟶ C) (t : C ⟶ E) (h : u ≫ v = w ≫ t) (K : E.Modules) :
    canHom u v (u ≫ v) rfl K ≫ (canNatIso w t (u ≫ v) h.symm).inv.app K
      = (sqIso u v w t h K).hom := by
  simp [sqIso, sqNatIso, canHom, canNatIso, Scheme.Modules.pullbackCongr]

/-- **The vertical pasting law for the square comparison.**  Let

```
A --u--> B        C --t--> E
|        |        |        |
w        v        w'       v'
v        v        v        v
C --t--> E        C'--t'-> E'
```

be two commuting squares sharing the edge `t`, with `v ≫ v' = V`, `w ≫ w' = W` and
`u ≫ V = W ≫ t'` the pasted square.  Then crossing the pasted square is crossing the two squares
one after the other, up to the two canonical identifications
`Stacks.AlgebraicGeometry.ModuleLimits.canHom` merging the composed edges.

This is `Stacks.AlgebraicGeometry.ModuleLimits.canHom_paste_comp` — the pentagon pasted three
times — read through `canHom_comp_canNatIso_inv_app` at the three squares.  It is what turns the
descent of a comparison at a *later* stage into a comparison of the modules re-indexed to that
stage. -/
theorem sqIso_paste_vert {A B C E C' E' : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ E) (w : A ⟶ C)
    (t : C ⟶ E) (v' : E ⟶ E') (w' : C ⟶ C') (t' : C' ⟶ E') (V : B ⟶ E') (W : A ⟶ C')
    (h₁ : u ≫ v = w ≫ t) (h₂ : t ≫ v' = w' ≫ t') (hV : v ≫ v' = V) (hW : w ≫ w' = W)
    (h : u ≫ V = W ≫ t') (K : E'.Modules) :
    (Scheme.Modules.pullback u).map (canHom v v' V hV K) ≫ (sqIso u V W t' h K).hom
      = (sqIso u v w t h₁ ((Scheme.Modules.pullback v').obj K)).hom ≫
        (Scheme.Modules.pullback w).map (sqIso t v' w' t' h₂ K).hom ≫
          canHom w w' W hW ((Scheme.Modules.pullback t').obj K) := by
  subst hV
  subst hW
  have key := canHom_paste_comp v v' u t t' w w' (w ≫ w') h₁.symm h₂.symm h.symm rfl K
  rw [← canHom_comp_canNatIso_inv_app u v w t h₁, ← canHom_comp_canNatIso_inv_app t v' w' t' h₂,
    ← canHom_comp_canNatIso_inv_app u (v ≫ v') (w ≫ w') t' h]
  simp only [Functor.map_comp, Category.assoc]
  exact key.symm

/-! ### Descending an isomorphism -/

section ReflectDescent

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D)

/-- **An isomorphism over the limit between two modules pulled back from a stage descends to an
isomorphism at a stage.**  Let `c` be a limit cone on a cofiltered diagram `D` of quasi-compact
quasi-separated schemes with affine transition morphisms, and let `F`, `G` be modules of finite
presentation on a stage `D.obj j`.  Every isomorphism `θ` between their pullbacks to the limit is,
through the canonical identifications
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`, the pullback of an isomorphism between their
pullbacks to some stage over `j`.

This is [Stacks, Tag 01ZR] (2) in the canonically pinned form
`Stacks.AlgebraicGeometry.ModuleLimits.exists_map_of_pullback_canonical_of_isLimit'`, whose output
is only a morphism, followed by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_isIso_pullback_map_of_isLimit` to make it
invertible.  Those two steps return different stages, and the pentagon
`Stacks.AlgebraicGeometry.ModuleLimits.canHom_comp` merges the two canonical identifications into
the single one the conclusion is stated with.

This is the **universe-general** form of `AlgebraicGeometry.exists_stage_isIso_pullback_map`
(`StacksFrontier/AlgebraicGeometry/Quot/PolarizedLimitDescentHom.lean`), which states the same thing
but only for an index category whose morphism universe equals its object universe
(`[Category.{u} J]`).  That restriction rules out the index categories this file is applied to —
`CategoryTheory.Over` of an object of `(Finset A)ᵒᵖ` has objects in `Type u` and morphisms in
`Type 0` — which is why the statement is repeated here at `[Category.{v} I]` rather than reused.
Routing that declaration through this one is a repo-tier dedup. -/
@[ega "IV 8.5.2.5", ega "IV 8.5.3" "special case"]
theorem exists_stage_iso_of_pullback_iso (hc : IsLimit c)
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (j : I) (F G : (D.obj j).Modules) [F.IsFinitePresentation] [G.IsFinitePresentation]
    (θ : (Scheme.Modules.pullback (c.π.app j)).obj F ≅
      (Scheme.Modules.pullback (c.π.app j)).obj G) :
    ∃ (k : I) (e : k ⟶ j)
      (θk : (Scheme.Modules.pullback (D.map e)).obj F ≅
        (Scheme.Modules.pullback (D.map e)).obj G),
      (Scheme.Modules.pullback (c.π.app k)).map θk.hom ≫
          canHom (c.π.app k) (D.map e) (c.π.app j) (c.w e) G
        = canHom (c.π.app k) (D.map e) (c.π.app j) (c.w e) F ≫ θ.hom := by
  obtain ⟨k, e, ψ, hψ⟩ :=
    exists_map_of_pullback_canonical_of_isLimit' D c hc j F G θ.hom
  -- The descended morphism pulls back to an isomorphism, being a conjugate of `θ`.
  have hconj : (Scheme.Modules.pullback (c.π.app k)).map ψ =
      canHom (c.π.app k) (D.map e) (c.π.app j) (c.w e) F ≫ θ.hom ≫
        inv (canHom (c.π.app k) (D.map e) (c.π.app j) (c.w e) G) := by
    rw [← Category.assoc, ← hψ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hiso : IsIso ((Scheme.Modules.pullback (c.π.app k)).map ψ) := by
    rw [hconj]; infer_instance
  have hFk := isFinitePresentation_pullback (D.map e) F
  have hGk := isFinitePresentation_pullback (D.map e) G
  obtain ⟨l, g, hg⟩ := exists_isIso_pullback_map_of_isLimit D c hc k
    ((Scheme.Modules.pullback (D.map e)).obj F)
    ((Scheme.Modules.pullback (D.map e)).obj G) ψ hiso
  have hcomp : D.map g ≫ D.map e = D.map (g ≫ e) := (D.map_comp g e).symm
  refine ⟨l, g ≫ e,
    (canIso (D.map g) (D.map e) (D.map (g ≫ e)) hcomp F).symm ≪≫
      (@asIso _ _ _ _ ((Scheme.Modules.pullback (D.map g)).map ψ) hg) ≪≫
      canIso (D.map g) (D.map e) (D.map (g ≫ e)) hcomp G, ?_⟩
  -- The pentagon at `F` and at `G`, and the naturality of the canonical identification.
  have hP := canHom_comp (c.π.app l) (D.map g) (D.map e) (c.π.app k) (D.map (g ≫ e))
    (c.π.app j) (c.w g) hcomp (c.w e) (c.w (g ≫ e))
  have hN := canHom_naturality (c.π.app l) (D.map g) (c.π.app k) (c.w g) ψ
  have hinv : (canIso (D.map g) (D.map e) (D.map (g ≫ e)) hcomp F).inv ≫
      canHom (D.map g) (D.map e) (D.map (g ≫ e)) hcomp F = 𝟙 _ :=
    (canIso (D.map g) (D.map e) (D.map (g ≫ e)) hcomp F).inv_hom_id
  simp only [Iso.trans_hom, Iso.symm_hom, canIso_hom, asIso_hom, Functor.map_comp,
    Category.assoc]
  rw [hP G, reassoc_of% hN, hψ, ← reassoc_of% (hP F), ← Functor.map_comp_assoc, hinv]
  simp

end ReflectDescent

/-! ### A compatible triple over a cospan of limit systems -/

section Cospan

variable {I : Type u} [Category.{v} I] [IsCofiltered I]
  (Dc Dm De : I ⥤ Scheme.{u}) (cc : Cone Dc) (cm : Cone Dm) (ce : Cone De)
  (τc : De ⟶ Dc) (τm : De ⟶ Dm) (uc : ce.pt ⟶ cc.pt) (um : ce.pt ⟶ cm.pt)
  (hwc : ∀ i, ce.π.app i ≫ τc.app i = uc ≫ cc.π.app i)
  (hwm : ∀ i, ce.π.app i ≫ τm.app i = um ≫ cm.π.app i)

/-- **A comparison over the limit of the third system, read in the pulled-back presentation.**
Given modules `Eck`, `Emk` at a stage `k` of the two outer systems, identifications `ιc`, `ιm` of
their pullbacks to the limits with two given modules `Ec`, `Em`, and a comparison `φ` of the
restrictions of `Ec` and `Em` along `uc` and `um`, this is `φ` transported into a comparison of
the two restrictions of the stage modules pulled back to the limit.

The two transports are the square comparisons
`Stacks.AlgebraicGeometry.ModuleLimits.sqIso` of the commuting squares `hwc k` and `hwm k`: a
module at the stage `k`, restricted along the stage comparison `τc.app k` and then pulled back to
the limit, is the same as pulled back to the limit and then restricted along `uc`. -/
noncomputable def stageComparison (k : I) {Eck : (Dc.obj k).Modules} {Emk : (Dm.obj k).Modules}
    {Ec : cc.pt.Modules} {Em : cm.pt.Modules}
    (ιc : Ec ≅ (Scheme.Modules.pullback (cc.π.app k)).obj Eck)
    (ιm : Em ≅ (Scheme.Modules.pullback (cm.π.app k)).obj Emk)
    (φ : (Scheme.Modules.pullback uc).obj Ec ≅ (Scheme.Modules.pullback um).obj Em) :
    (Scheme.Modules.pullback (ce.π.app k)).obj
        ((Scheme.Modules.pullback (τc.app k)).obj Eck) ≅
      (Scheme.Modules.pullback (ce.π.app k)).obj
        ((Scheme.Modules.pullback (τm.app k)).obj Emk) :=
  (sqIso uc (cc.π.app k) (ce.π.app k) (τc.app k) (hwc k).symm Eck).symm ≪≫
    (Scheme.Modules.pullback uc).mapIso ιc.symm ≪≫ φ ≪≫
    (Scheme.Modules.pullback um).mapIso ιm ≪≫
    sqIso um (cm.π.app k) (ce.π.app k) (τm.app k) (hwm k).symm Emk

/-- **The Noetherian reduction of [Stacks, Tag 0EXD]: a compatible triple over a cospan of
cofiltered limit systems descends.**

Let `Dc`, `Dm`, `De` be cofiltered diagrams of quasi-compact quasi-separated schemes with affine
transition morphisms, let `cc`, `cm`, `ce` be limit cones on them, and let `τc : De ⟶ Dc`,
`τm : De ⟶ Dm` be morphisms of diagrams whose values are compatible with the cone legs through
two morphisms `uc`, `um` out of the limit of `De` — the hypotheses `hwc` and `hwm`.  (At the
almost blowup square of [Stacks, Example 0EVH] the three systems are the centre, the modification
and the exceptional line over the Noetherian stages, and `τc`, `τm`, `uc`, `um` are the two
projections of the exceptional line over a stage and over the base.)

A *compatible triple* over the limits is a finite locally free module `Ec` on `cc.pt`, a finite
locally free module `Em` on `cm.pt`, and an isomorphism `φ : uc^* Ec ≅ um^* Em`.  Then there is a
stage `j` carrying finite locally free modules `Ecj`, `Emj` pulling back to `Ec` and `Em`, and a
stage `k` over `j` at which the comparison `φ` — read through those identifications and the two
square comparisons, i.e. as
`Stacks.AlgebraicGeometry.ModuleLimits.stageComparison` — is itself the pullback of an
isomorphism, through the canonical identification
`Stacks.AlgebraicGeometry.ModuleLimits.canHom`.

**The stage shrinks twice, and only the comparison sees the second shrinking.**  The two modules
are put over a single stage `j` by [Stacks, Tag 0B8W] (1) at each system followed by
`CategoryTheory.IsCofiltered.min`; the comparison descends only after a further shrinking, by
`Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_iso_of_pullback_iso`.  The conclusion
therefore keeps `ε : k ⟶ j` explicit;
`Stacks.AlgebraicGeometry.ModuleLimits.exists_stage_compatibleTriple_single` merges the two
stages, by the vertical pasting law
`Stacks.AlgebraicGeometry.ModuleLimits.sqIso_paste_vert`. -/
theorem exists_stage_compatibleTriple
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Dc.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Dm.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (De.map f)]
    [∀ i : I, CompactSpace (Dc.obj i)] [∀ i : I, QuasiSeparatedSpace (Dc.obj i)]
    [∀ i : I, CompactSpace (Dm.obj i)] [∀ i : I, QuasiSeparatedSpace (Dm.obj i)]
    [∀ i : I, CompactSpace (De.obj i)] [∀ i : I, QuasiSeparatedSpace (De.obj i)]
    (hcc : IsLimit cc) (hcm : IsLimit cm) (hce : IsLimit ce)
    (Ec : cc.pt.Modules) (hEc : SheafOfModules.IsFiniteLocallyFree.{u, u, u} Ec)
    (Em : cm.pt.Modules) (hEm : SheafOfModules.IsFiniteLocallyFree.{u, u, u} Em)
    (φ : (Scheme.Modules.pullback uc).obj Ec ≅ (Scheme.Modules.pullback um).obj Em) :
    ∃ (j k : I) (ε : k ⟶ j) (Ecj : (Dc.obj j).Modules) (Emj : (Dm.obj j).Modules)
      (ιc : Ec ≅ (Scheme.Modules.pullback (cc.π.app j)).obj Ecj)
      (ιm : Em ≅ (Scheme.Modules.pullback (cm.π.app j)).obj Emj)
      (θ : (Scheme.Modules.pullback (De.map ε)).obj
            ((Scheme.Modules.pullback (τc.app j)).obj Ecj) ≅
          (Scheme.Modules.pullback (De.map ε)).obj
            ((Scheme.Modules.pullback (τm.app j)).obj Emj)),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} Ecj ∧
        SheafOfModules.IsFiniteLocallyFree.{u, u, u} Emj ∧
        (Scheme.Modules.pullback (ce.π.app k)).map θ.hom ≫
            canHom (ce.π.app k) (De.map ε) (ce.π.app j) (ce.w ε)
              ((Scheme.Modules.pullback (τm.app j)).obj Emj)
          = canHom (ce.π.app k) (De.map ε) (ce.π.app j) (ce.w ε)
              ((Scheme.Modules.pullback (τc.app j)).obj Ecj) ≫
            (stageComparison Dc Dm De cc cm ce τc τm uc um hwc hwm j ιc ιm φ).hom := by
  -- The two modules over a single stage, by [Stacks, Tag 0B8W] (1) at each system followed by
  -- cofilteredness of the index category.
  obtain ⟨j, Ecj, Emj, hEcj, hEmj, ⟨ec⟩, ⟨em⟩⟩ :
      ∃ (j : I) (Ecj : (Dc.obj j).Modules) (Emj : (Dm.obj j).Modules),
        SheafOfModules.IsFiniteLocallyFree.{u, u, u} Ecj ∧
          SheafOfModules.IsFiniteLocallyFree.{u, u, u} Emj ∧
          Nonempty (Ec ≅ (Scheme.Modules.pullback (cc.π.app j)).obj Ecj) ∧
          Nonempty (Em ≅ (Scheme.Modules.pullback (cm.π.app j)).obj Emj) := by
    obtain ⟨j₁, Ec₁, hEc₁, ⟨e₁⟩⟩ := exists_isFiniteLocallyFree_pullback_iso Dc cc hcc Ec hEc
    obtain ⟨j₂, Em₂, hEm₂, ⟨e₂⟩⟩ := exists_isFiniteLocallyFree_pullback_iso Dm cm hcm Em hEm
    obtain ⟨Ecj, hEcj, hc⟩ := exists_isFiniteLocallyFree_pullback_iso_of_hom Dc cc
      (IsCofiltered.minToLeft j₁ j₂) Ec₁ hEc₁ e₁
    obtain ⟨Emj, hEmj, hm⟩ := exists_isFiniteLocallyFree_pullback_iso_of_hom Dm cm
      (IsCofiltered.minToRight j₁ j₂) Em₂ hEm₂ e₂
    exact ⟨IsCofiltered.min j₁ j₂, Ecj, Emj, hEcj, hEmj, hc, hm⟩
  -- The two restrictions to the third system over that stage, and their finite presentation.
  have hFfp := (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme
    (τc.app j) Ecj hEcj).isFinitePresentation
  have hGfp := (AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme
    (τm.app j) Emj hEmj).isFinitePresentation
  -- The comparison, read in the pulled-back presentation, then descended.
  obtain ⟨k, ε, θ, hθ⟩ := exists_stage_iso_of_pullback_iso De ce hce j
    ((Scheme.Modules.pullback (τc.app j)).obj Ecj)
    ((Scheme.Modules.pullback (τm.app j)).obj Emj)
    (stageComparison Dc Dm De cc cm ce τc τm uc um hwc hwm j ec em φ)
  exact ⟨j, k, ε, Ecj, Emj, ec, em, θ, hEcj, hEmj, hθ⟩

/-- **The Noetherian reduction of [Stacks, Tag 0EXD], over a single stage.**  The compatible
triple of `exists_stage_compatibleTriple` re-indexed: there is *one* stage `k` carrying finite
locally free modules `Eck`, `Emk` and an isomorphism `φk` between their restrictions along the
two legs of the cospan at `k`, whose pullback to the limit is the given comparison `φ` read
through the two descent isomorphisms and the two square comparisons — that is,
`Stacks.AlgebraicGeometry.ModuleLimits.stageComparison`.

The second shrinking of the stage is absorbed by the vertical pasting law
`Stacks.AlgebraicGeometry.ModuleLimits.sqIso_paste_vert`, applied once on each side of the
cospan to the stage square at `k` pasted with the naturality square of the diagram morphism;
the two descent isomorphisms are re-indexed by
`Stacks.AlgebraicGeometry.ModuleLimits.isoPullbackMapOfIsoPullback`, whose comparison factor is
the same canonical identification the pasting law produces, so the two cancel. -/
theorem exists_stage_compatibleTriple_single
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Dc.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (Dm.map f)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (De.map f)]
    [∀ i : I, CompactSpace (Dc.obj i)] [∀ i : I, QuasiSeparatedSpace (Dc.obj i)]
    [∀ i : I, CompactSpace (Dm.obj i)] [∀ i : I, QuasiSeparatedSpace (Dm.obj i)]
    [∀ i : I, CompactSpace (De.obj i)] [∀ i : I, QuasiSeparatedSpace (De.obj i)]
    (hcc : IsLimit cc) (hcm : IsLimit cm) (hce : IsLimit ce)
    (Ec : cc.pt.Modules) (hEc : SheafOfModules.IsFiniteLocallyFree.{u, u, u} Ec)
    (Em : cm.pt.Modules) (hEm : SheafOfModules.IsFiniteLocallyFree.{u, u, u} Em)
    (φ : (Scheme.Modules.pullback uc).obj Ec ≅ (Scheme.Modules.pullback um).obj Em) :
    ∃ (k : I) (Eck : (Dc.obj k).Modules) (Emk : (Dm.obj k).Modules)
      (ιc : Ec ≅ (Scheme.Modules.pullback (cc.π.app k)).obj Eck)
      (ιm : Em ≅ (Scheme.Modules.pullback (cm.π.app k)).obj Emk)
      (φk : (Scheme.Modules.pullback (τc.app k)).obj Eck ≅
        (Scheme.Modules.pullback (τm.app k)).obj Emk),
      SheafOfModules.IsFiniteLocallyFree.{u, u, u} Eck ∧
        SheafOfModules.IsFiniteLocallyFree.{u, u, u} Emk ∧
        (stageComparison Dc Dm De cc cm ce τc τm uc um hwc hwm k ιc ιm φ).hom
          = (Scheme.Modules.pullback (ce.π.app k)).map φk.hom := by
  obtain ⟨j, k, ε, Ecj, Emj, ιcj, ιmj, θ, hEcj, hEmj, hθ⟩ :=
    exists_stage_compatibleTriple Dc Dm De cc cm ce τc τm uc um hwc hwm hcc hcm hce
      Ec hEc Em hEm φ
  -- The naturality squares of the two diagram morphisms, crossed.
  refine ⟨k, (Scheme.Modules.pullback (Dc.map ε)).obj Ecj,
    (Scheme.Modules.pullback (Dm.map ε)).obj Emj,
    isoPullbackMapOfIsoPullback Dc cc ε ιcj, isoPullbackMapOfIsoPullback Dm cm ε ιmj,
    sqIso (τc.app k) (Dc.map ε) (De.map ε) (τc.app j) (τc.naturality ε).symm Ecj ≪≫ θ ≪≫
      (sqIso (τm.app k) (Dm.map ε) (De.map ε) (τm.app j) (τm.naturality ε).symm Emj).symm,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (Dc.map ε) Ecj hEcj,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme (Dm.map ε) Emj hEmj, ?_⟩
  -- The two pastings: the stage square at `k` against the naturality square gives the stage
  -- square at `j`, with the canonical identifications of the composed cone legs on the outside.
  have hC := sqIso_paste_vert uc (cc.π.app k) (ce.π.app k) (τc.app k) (Dc.map ε) (De.map ε)
    (τc.app j) (cc.π.app j) (ce.π.app j) (hwc k).symm (τc.naturality ε).symm (cc.w ε) (ce.w ε)
    (hwc j).symm Ecj
  have hM := sqIso_paste_vert um (cm.π.app k) (ce.π.app k) (τm.app k) (Dm.map ε) (De.map ε)
    (τm.app j) (cm.π.app j) (ce.π.app j) (hwm k).symm (τm.naturality ε).symm (cm.w ε) (ce.w ε)
    (hwm j).symm Emj
  -- The two cancellations that the re-indexing creates: the naturality crossing on the
  -- modification side against its own inverse, and the canonical identification of the composed
  -- cone legs against the comparison factor of the re-indexed descent isomorphism.
  have hnM : (Scheme.Modules.pullback (ce.π.app k)).map
        (sqIso (τm.app k) (Dm.map ε) (De.map ε) (τm.app j) (τm.naturality ε).symm Emj).inv ≫
      (Scheme.Modules.pullback (ce.π.app k)).map
        (sqIso (τm.app k) (Dm.map ε) (De.map ε) (τm.app j) (τm.naturality ε).symm Emj).hom ≫
        canHom (ce.π.app k) (De.map ε) (ce.π.app j) (ce.w ε)
          ((Scheme.Modules.pullback (τm.app j)).obj Emj)
      = canHom (ce.π.app k) (De.map ε) (ce.π.app j) (ce.w ε)
          ((Scheme.Modules.pullback (τm.app j)).obj Emj) := by
    exact Iso.inv_hom_id_assoc ((Scheme.Modules.pullback _).mapIso (sqIso _ _ _ _ _ _)) _
  have hcanM : (Scheme.Modules.pullback um).map
        ((canNatIso (cm.π.app k) (Dm.map ε) (cm.π.app j) (cm.w ε)).app Emj).inv ≫
      (Scheme.Modules.pullback um).map
        (canHom (cm.π.app k) (Dm.map ε) (cm.π.app j) (cm.w ε) Emj) ≫
        (sqIso um (cm.π.app j) (ce.π.app j) (τm.app j) (hwm j).symm Emj).hom
      = (sqIso um (cm.π.app j) (ce.π.app j) (τm.app j) (hwm j).symm Emj).hom := by
    exact Iso.inv_hom_id_assoc ((Scheme.Modules.pullback _).mapIso
      ((canNatIso (cm.π.app k) (Dm.map ε) (cm.π.app j) (cm.w ε)).app Emj)) _
  -- Pre-compose with the stage square at `k` and post-compose with the modification-side
  -- crossing and the canonical identification, all isomorphisms.
  have hmono : Mono ((Scheme.Modules.pullback (ce.π.app k)).map
      (sqIso (τm.app k) (Dm.map ε) (De.map ε) (τm.app j) (τm.naturality ε).symm Emj).hom ≫
    canHom (ce.π.app k) (De.map ε) (ce.π.app j) (ce.w ε)
      ((Scheme.Modules.pullback (τm.app j)).obj Emj)) :=
    inferInstanceAs (Mono (((Scheme.Modules.pullback (ce.π.app k)).mapIso
      (sqIso (τm.app k) (Dm.map ε) (De.map ε) (τm.app j) (τm.naturality ε).symm Emj) ≪≫
      (canNatIso (ce.π.app k) (De.map ε) (ce.π.app j) (ce.w ε)).app
        ((Scheme.Modules.pullback (τm.app j)).obj Emj)).hom))
  rw [← cancel_epi (sqIso uc (cc.π.app k) (ce.π.app k) (τc.app k) (hwc k).symm
      ((Scheme.Modules.pullback (Dc.map ε)).obj Ecj)).hom,
    ← cancel_mono ((Scheme.Modules.pullback (ce.π.app k)).map
      (sqIso (τm.app k) (Dm.map ε) (De.map ε) (τm.app j) (τm.naturality ε).symm Emj).hom ≫
    canHom (ce.π.app k) (De.map ε) (ce.π.app j) (ce.w ε)
      ((Scheme.Modules.pullback (τm.app j)).obj Emj))]
  simp only [stageComparison, isoPullbackMapOfIsoPullback, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [hnM, hθ, ← reassoc_of% hC]
  simp only [stageComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc]
  have hidC : ((canNatIso (cc.π.app k) (Dc.map ε) (cc.π.app j) (cc.w ε)).app Ecj).hom
      = canHom (cc.π.app k) (Dc.map ε) (cc.π.app j) (cc.w ε) Ecj := rfl
  rw [← hM, hcanM, hidC]

end Cospan

end Stacks.AlgebraicGeometry.ModuleLimits

end
