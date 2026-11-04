module

public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic

/-!
# Two models over a limit become isomorphic at a later stage

Let `S = lim Sᵢ` be a cofiltered limit of quasi-compact, quasi-separated schemes with affine
transition morphisms, and let `Z` be a scheme over `S`.  Suppose `Z` is presented in two ways as
the base change of a scheme of finite presentation over one and the same stage `Sᵢ`.  This file
shows that the two models become isomorphic over a later stage: after replacing `Sᵢ` by some
`S_m` with `m ⟶ i` and both models by their base changes to `S_m`, there is an isomorphism of
the two models over `S_m` compatible with the two presentations of `Z`.

This is the uniqueness half of the descent of models, and the last ingredient the glueing step of
Stacks Tag 01ZM part (1) needs: it is what lets two descents of one intersection of members of a
cover be identified at a single later stage.

## Main results

* `AlgebraicGeometry.exists_iso_of_isPullback_of_isPullback`: the statement above, with both
  models and both presentations transported to the later stage as pullback squares.

## Implementation notes

The proof runs entirely in over categories, where base change is `CategoryTheory.Over.pullback`.
A presentation of `Z` as a base change of a model is repackaged as an isomorphism
`Over.mk fZ ≅ (Over.pullback (c.π.app i)).obj X` in `Over c.pt`, using
`CategoryTheory.IsPullback.isoPullback`.  Composing the two presentations gives an isomorphism of
the base changes of the two models to the limit;
`AlgebraicGeometry.exists_morphism_after_baseChange` descends it to a morphism `g` over some stage
`j`, and the descended morphism is an isomorphism after base change to the limit, hence — by
`AlgebraicGeometry.exists_isIso_baseChange_of_isIso_limitBaseChange` — already over some stage `k`.

The compatibility of the descended isomorphism with the two presentations of `Z` is obtained by
transporting the presentations along the comparison isomorphisms between iterated and direct base
change, so it becomes a formal consequence of the naturality of
`AlgebraicGeometry.overPullbackCompIso` together with the equation the descent already provides.
That the transported presentations still induce the original ones is read off from the
compatibility of each comparison isomorphism with the first pullback projections: for the
isomorphisms produced by the descent this is the hypothesis
`AlgebraicGeometry.exists_morphism_after_baseChange` returns, and for
`AlgebraicGeometry.overPullbackCompIso` it is
`AlgebraicGeometry.overPullbackCompIso_fst`.

## References

* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081E](https://stacks.math.columbia.edu/tag/081E)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An identification of a scheme `Z` over `Q` with the base change of `W` along `q : Q ⟶ T`
exhibits `Z` as a fibre product of `W` and `Q` over `T`. -/
public lemma isPullback_left_fst_of_overIso {Q T Z : Scheme.{u}} {q : Q ⟶ T} {f : Z ⟶ Q}
    (W : Over T) (E : Over.mk f ≅ (Over.pullback q).obj W) :
    IsPullback (E.hom.left ≫ pullback.fst W.hom q) f W.hom q := by
  have hw : E.hom.left ≫ pullback.snd W.hom q = f := by simpa using Over.w E.hom
  refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget Q).mapIso E) rfl hw
  rw [Category.assoc, pullback.condition, ← Category.assoc, hw]

/-- An identity comparing two presentations of `Z` as a base change, read on the first pullback
projections. -/
public lemma left_fst_comp_of_overIso_eq {Q T Z : Scheme.{u}} {q : Q ⟶ T} {f : Z ⟶ Q}
    {WA WB : Over T} (ψ : WA ≅ WB)
    (EA : Over.mk f ≅ (Over.pullback q).obj WA) (EB : Over.mk f ≅ (Over.pullback q).obj WB)
    (hkey : EA.hom ≫ (Over.pullback q).map ψ.hom = EB.hom) :
    (EA.hom.left ≫ pullback.fst WA.hom q) ≫ ψ.hom.left =
      EB.hom.left ≫ pullback.fst WB.hom q := by
  have h1 : EA.hom.left ≫ ((Over.pullback q).map ψ.hom).left = EB.hom.left := by
    simpa only [Over.comp_left] using congrArg (fun u => u.left) hkey
  rw [Category.assoc, ← overPullback_map_left_fst q ψ.hom, ← Category.assoc, h1]

/-- An isomorphism between an iterated base change and a direct base change that is compatible
with the first pullback projections has an inverse compatible with them the other way round. -/
public lemma overPullback_inv_left_comp_fst {S S' T : Scheme.{u}} {p : S ⟶ T} {q : S' ⟶ S}
    {r : S' ⟶ T} {X : Over T}
    (α : (Over.pullback q).obj ((Over.pullback p).obj X) ≅ (Over.pullback r).obj X)
    (hα : α.hom.left ≫ pullback.fst X.hom r =
      pullback.fst ((Over.pullback p).obj X).hom q ≫ pullback.fst X.hom p) :
    α.inv.left ≫ pullback.fst ((Over.pullback p).obj X).hom q ≫ pullback.fst X.hom p =
      pullback.fst X.hom r := by
  rw [← hα, ← Category.assoc, ← Over.comp_left, α.inv_hom_id]
  simp

/-- The transported presentation of `Z` over stage `k` induces the original one through the first
pullback projections. -/
private lemma transport_left_comp_fst {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    (c : Cone D) {i j k : I} (e : j ⟶ i) (h : k ⟶ j) {Z : Scheme.{u}} (fZ : Z ⟶ c.pt)
    (X : Over (D.obj i)) (E : Over.mk fZ ≅ (Over.pullback (c.π.app i)).obj X)
    (E' : (Over.pullback (c.π.app j)).obj ((Over.pullback (D.map e)).obj X) ≅
      (Over.pullback (c.π.app i)).obj X)
    (hE' : E'.hom.left ≫ pullback.fst X.hom (c.π.app i) =
      pullback.fst ((Over.pullback (D.map e)).obj X).hom (c.π.app j) ≫
        pullback.fst X.hom (D.map e)) :
    (E ≪≫ E'.symm ≪≫
        (overPullbackCompIso (D.map h) (c.π.app k) (c.π.app j) (c.w h)
          ((Over.pullback (D.map e)).obj X)).symm ≪≫
        (Over.pullback (c.π.app k)).mapIso
          (overPullbackCompIso (D.map e) (D.map h) (D.map (h ≫ e)) (D.map_comp h e).symm X)
        ).hom.left ≫ pullback.fst ((Over.pullback (D.map (h ≫ e))).obj X).hom (c.π.app k) ≫
          pullback.fst X.hom (D.map (h ≫ e)) = E.hom.left ≫ pullback.fst X.hom (c.π.app i) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.comp_left, Category.assoc]
  rw [reassoc_of% overPullback_map_left_fst (c.π.app k) (overPullbackCompIso (D.map e) (D.map h)
      (D.map (h ≫ e)) (D.map_comp h e).symm X).hom,
    overPullbackCompIso_fst (D.map e) (D.map h) (D.map (h ≫ e)) (D.map_comp h e).symm X,
    reassoc_of% overPullback_inv_left_comp_fst _
      (overPullbackCompIso_fst (D.map h) (c.π.app k) (c.π.app j) (c.w h)
        ((Over.pullback (D.map e)).obj X)),
    overPullback_inv_left_comp_fst E' hE']

/-- The over-categorical form of `AlgebraicGeometry.exists_iso_of_isPullback_of_isPullback`: two
schemes of finite presentation over a stage whose base changes to the limit are both identified
with a fixed scheme over the limit have isomorphic base changes to some later stage, by an
isomorphism compatible with the two identifications.  The identifications at the later stage
induce the given ones through the first pullback projections. -/
private lemma exists_iso_over_after_baseChange {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (XA XB : Over (D.obj i))
    (hpA : FinitePresentation XA.hom) (hpB : FinitePresentation XB.hom)
    {Z : Scheme.{u}} (fZ : Z ⟶ c.pt)
    (eA : Over.mk fZ ≅ (Over.pullback (c.π.app i)).obj XA)
    (eB : Over.mk fZ ≅ (Over.pullback (c.π.app i)).obj XB) :
    ∃ (m : I) (a : m ⟶ i)
      (ψ : (Over.pullback (D.map a)).obj XA ≅ (Over.pullback (D.map a)).obj XB)
      (EA : Over.mk fZ ≅ (Over.pullback (c.π.app m)).obj ((Over.pullback (D.map a)).obj XA))
      (EB : Over.mk fZ ≅ (Over.pullback (c.π.app m)).obj ((Over.pullback (D.map a)).obj XB)),
      EA.hom ≫ (Over.pullback (c.π.app m)).map ψ.hom = EB.hom ∧
        EA.hom.left ≫ pullback.fst ((Over.pullback (D.map a)).obj XA).hom (c.π.app m) ≫
            pullback.fst XA.hom (D.map a) =
          eA.hom.left ≫ pullback.fst XA.hom (c.π.app i) ∧
        EB.hom.left ≫ pullback.fst ((Over.pullback (D.map a)).obj XB).hom (c.π.app m) ≫
            pullback.fst XB.hom (D.map a) =
          eB.hom.left ≫ pullback.fst XB.hom (c.π.app i) := by
  have ⟨_, _, _⟩ := hpA
  have ⟨_, _, _⟩ := hpB
  obtain ⟨j, e, g, α, β, hα, hβ, hg⟩ :=
    exists_morphism_after_baseChange D c hc i XA XB hpA hpB (eA.symm ≪≫ eB).hom
  -- The descended morphism is an isomorphism after base change to the limit.
  have hbcg : (Over.pullback (c.π.app j)).map g = α.hom ≫ eA.inv ≫ eB.hom ≫ β.inv := by
    simp only [← Category.assoc, Iso.eq_comp_inv]
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using hg.symm
  have hIsoBc : IsIso ((Over.pullback (c.π.app j)).map g) := by rw [hbcg]; infer_instance
  have hIsoBcLeft : IsIso ((Over.pullback (c.π.app j)).map g).left :=
    (Over.forget c.pt).map_isIso ((Over.pullback (c.π.app j)).map g)
  -- The hypotheses of Tag 081E at the stage `j`.
  have hX' : ∀ X : Over (D.obj i), FinitePresentation X.hom →
      FinitePresentation ((Over.pullback (D.map e)).obj X).hom ∧
        CompactSpace ((Over.pullback (D.map e)).obj X).left ∧
        QuasiSeparatedSpace ((Over.pullback (D.map e)).obj X).left := fun X hX ↦ by
    have ⟨_, _, _⟩ := hX
    have hF : FinitePresentation ((Over.pullback (D.map e)).obj X).hom := by
      simp only [Over.pullback_obj_hom]
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    have ⟨_, _, _⟩ := hF
    exact ⟨hF,
      QuasiCompact.compactSpace_of_compactSpace ((Over.pullback (D.map e)).obj X).hom,
      quasiSeparatedSpace_of_quasiSeparated ((Over.pullback (D.map e)).obj X).hom⟩
  obtain ⟨hXA', _, _⟩ := hX' XA hpA
  obtain ⟨hXB', _, _⟩ := hX' XB hpB
  have ⟨_, _, _⟩ := hXA'
  have ⟨_, _, _⟩ := hXB'
  have hcomp : LocallyOfFinitePresentation
      (g.left ≫ ((Over.pullback (D.map e)).obj XB).hom) := by
    rw [Over.w g]; infer_instance
  have : LocallyOfFinitePresentation g.left :=
    locallyOfFinitePresentation_of_comp g.left ((Over.pullback (D.map e)).obj XB).hom
  obtain ⟨k, h, hkiso⟩ := exists_isIso_baseChange_of_isIso_limitBaseChange D c hc j
    ((Over.pullback (D.map e)).obj XA) ((Over.pullback (D.map e)).obj XB) g
  have hIsoG : IsIso ((Over.pullback (D.map h)).map g) :=
    have : IsIso ((Over.forget (D.obj k)).map ((Over.pullback (D.map h)).map g)) := hkiso
    isIso_of_reflects_iso _ (Over.forget (D.obj k))
  -- The comparison isomorphisms between the iterated and the direct base changes.
  have hnat := overPullbackCompIso_naturality (D.map h) (c.π.app k) (c.π.app j) (c.w h) g
  set α₂ := overPullbackCompIso (D.map h) (c.π.app k) (c.π.app j) (c.w h)
    ((Over.pullback (D.map e)).obj XA)
  set β₂ := overPullbackCompIso (D.map h) (c.π.app k) (c.π.app j) (c.w h)
    ((Over.pullback (D.map e)).obj XB)
  set γA := overPullbackCompIso (D.map e) (D.map h) (D.map (h ≫ e)) (D.map_comp h e).symm XA
  set γB := overPullbackCompIso (D.map e) (D.map h) (D.map (h ≫ e)) (D.map_comp h e).symm XB
  have hnat' : α₂.inv ≫ (Over.pullback (c.π.app k)).map ((Over.pullback (D.map h)).map g) =
      (Over.pullback (c.π.app j)).map g ≫ β₂.inv := by
    calc α₂.inv ≫ (Over.pullback (c.π.app k)).map ((Over.pullback (D.map h)).map g)
        = α₂.inv ≫ (α₂.hom ≫ (Over.pullback (c.π.app j)).map g) ≫ β₂.inv := by
          rw [hnat]; simp
      _ = (Over.pullback (c.π.app j)).map g ≫ β₂.inv := by simp
  refine ⟨k, h ≫ e, γA.symm ≪≫ asIso ((Over.pullback (D.map h)).map g) ≪≫ γB,
    eA ≪≫ α.symm ≪≫ α₂.symm ≪≫ (Over.pullback (c.π.app k)).mapIso γA,
    eB ≪≫ β.symm ≪≫ β₂.symm ≪≫ (Over.pullback (c.π.app k)).mapIso γB, ?_, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Functor.mapIso_hom, Functor.map_comp,
      Category.assoc, Iso.map_hom_inv_id_assoc]
    rw [reassoc_of% hnat', hbcg]
    simp
  · exact transport_left_comp_fst D c e h fZ XA eA α hα
  · exact transport_left_comp_fst D c e h fZ XB eB β hβ

/-- Two models over one stage of the same scheme over the limit become isomorphic over a later
stage. -/
public theorem exists_iso_of_isPullback_of_isPullback
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) {YA YB Z : Scheme.{u}} {pA : YA ⟶ D.obj i} {pB : YB ⟶ D.obj i}
    (hpA : FinitePresentation pA) (hpB : FinitePresentation pB)
    {fZ : Z ⟶ c.pt} {gA : Z ⟶ YA} {gB : Z ⟶ YB}
    (hA : IsPullback gA fZ pA (c.π.app i)) (hB : IsPullback gB fZ pB (c.π.app i)) :
    ∃ (m : I) (e : m ⟶ i) (YA' YB' : Scheme.{u}) (pA' : YA' ⟶ D.obj m) (pB' : YB' ⟶ D.obj m)
      (rA : YA' ⟶ YA) (rB : YB' ⟶ YB) (gA' : Z ⟶ YA') (gB' : Z ⟶ YB') (φ : YA' ≅ YB'),
      IsPullback rA pA' pA (D.map e) ∧ IsPullback rB pB' pB (D.map e) ∧
      IsPullback gA' fZ pA' (c.π.app m) ∧ IsPullback gB' fZ pB' (c.π.app m) ∧
      φ.hom ≫ pB' = pA' ∧ gA' ≫ φ.hom = gB' ∧ gA' ≫ rA = gA ∧ gB' ≫ rB = gB := by
  obtain ⟨m, a, ψ, EA, EB, hkey, hfA, hfB⟩ := exists_iso_over_after_baseChange D c hc i
    (Over.mk pA) (Over.mk pB) hpA hpB fZ
    (Over.isoMk hA.isoPullback (by simp))
    (Over.isoMk hB.isoPullback (by simp))
  refine ⟨m, a, _, _, _, _, pullback.fst pA (D.map a), pullback.fst pB (D.map a),
    EA.hom.left ≫ pullback.fst ((Over.pullback (D.map a)).obj (Over.mk pA)).hom (c.π.app m),
    EB.hom.left ≫ pullback.fst ((Over.pullback (D.map a)).obj (Over.mk pB)).hom (c.π.app m),
    (Over.forget (D.obj m)).mapIso ψ, IsPullback.of_hasPullback pA (D.map a),
    IsPullback.of_hasPullback pB (D.map a), isPullback_left_fst_of_overIso _ EA,
    isPullback_left_fst_of_overIso _ EB, Over.w ψ.hom,
    left_fst_comp_of_overIso_eq ψ EA EB hkey, ?_, ?_⟩
  · refine (Category.assoc _ _ _).trans (hfA.trans ?_)
    simp
  · refine (Category.assoc _ _ _).trans (hfB.trans ?_)
    simp

end AlgebraicGeometry
