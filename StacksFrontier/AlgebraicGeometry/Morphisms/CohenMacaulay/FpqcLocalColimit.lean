module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.Sites.Hypercover.Subcanonical
public import StacksCore.Tactic.StacksAttribute

/-!
# Colimits of schemes are local for fpqc coverings

A cocone of schemes is a colimit cocone if its base changes to every member of an fpqc
covering, and to every pairwise overlap, are colimit cocones.

## Main definitions

* `AlgebraicGeometry.baseChangeCocone` is the cocone obtained by pulling back every object and
  leg of a cocone along a morphism to its vertex.

## Main results

* `AlgebraicGeometry.isColimit_of_fpqc` gives the fpqc-local criterion for a cocone of schemes
  to be a colimit.

## Implementation notes

The statement is given for an arbitrary diagram of schemes: the fppf-site structure of the
source diagram is not used in this colimit criterion. A base-changed cocone has vertex the
chosen pullback of the identity of the original vertex; this is canonically isomorphic to the
covering scheme. Pulling back again along the canonical map from a pairwise overlap gives the
required overlap cocone.

## References

* [Stacks Project, Tag 0BMP](https://stacks.math.columbia.edu/tag/0BMP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- The cocone obtained by base-changing a cocone of schemes along a morphism to its vertex. -/
public noncomputable abbrev baseChangeCocone {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c : Cocone F) {W' : Scheme.{u}} (f : W' ⟶ c.pt) :
    Cocone (c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙
      Over.pullback f ⋙ Over.forget W') :=
  (Over.pullback f ⋙ Over.forget W').mapCocone c.toOver

/-- The cocone on the base-changed diagram whose vertex is the vertex of a second cocone `s`:
its leg at `j` is the first projection of the pullback followed by the leg of `s`. -/
private noncomputable def pulledTargetCocone {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c s : Cocone F) {W' : Scheme.{u}}
    (f : W' ⟶ c.pt) :
    Cocone (c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙
      Over.pullback f ⋙ Over.forget W') where
  pt := s.pt
  ι := {
    app := fun j =>
      pullback.fst ((CostructuredArrow.toOver F c.pt).obj
          (c.toCostructuredArrow.obj j)).hom f ≫
        eqToHom (CostructuredArrow.toOver_obj_left F c.pt (c.toCostructuredArrow.obj j)) ≫
          s.ι.app (c.toCostructuredArrow.obj j).left
    naturality := by
      intro j j' g
      simp only [Functor.comp_map, Over.forget_map, Over.pullback_map_left,
        pullback.lift_fst_assoc, CostructuredArrow.toOver_map_left,
        Functor.const_obj_map]
      rw [Category.assoc]
      exact congrArg (fun k =>
        pullback.fst ((CostructuredArrow.toOver F c.pt).obj
          (c.toCostructuredArrow.obj j)).hom f ≫
            eqToHom (CostructuredArrow.toOver_obj_left F c.pt
              (c.toCostructuredArrow.obj j)) ≫ k)
        (s.w (c.toCostructuredArrow.map g).left)
  }

/-- The structure map of the vertex of `c.toOver` is an isomorphism. -/
private instance isIso_toOver_pt_hom {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c : Cocone F) : IsIso c.toOver.pt.hom := by
  rw [Cocone.toOver_pt]
  exact inferInstanceAs (IsIso (𝟙 c.pt))

/-- The morphism out of a covering scheme obtained from the colimit property of the
base-changed cocone there. -/
private noncomputable def localDesc {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c s : Cocone F) {W' : Scheme.{u}}
    (f : W' ⟶ c.pt) (hc : IsColimit (baseChangeCocone c f)) : W' ⟶ s.pt := by
  exact inv (pullback.snd c.toOver.pt.hom f) ≫ hc.desc (pulledTargetCocone c s f)

/-- The legs of a base-changed cocone, expressed through the structure map of the pulled-back
object over the covering scheme. -/
private lemma baseChangeCocone_ι_app {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c : Cocone F) {W' : Scheme.{u}}
    (f : W' ⟶ c.pt) (j : J) :
    (baseChangeCocone c f).ι.app j =
      pullback.snd ((c.toCostructuredArrow ⋙ CostructuredArrow.toOver F c.pt).obj j).hom f ≫
        inv (pullback.snd c.toOver.pt.hom f) := by
  rw [← cancel_mono (pullback.snd c.toOver.pt.hom f), Category.assoc, IsIso.inv_hom_id,
    Category.comp_id]
  exact Over.w ((Over.pullback f).map (c.toOver.ι.app j))

/-- The local descent morphism factors the legs of the target cocone. -/
private lemma localDesc_fac {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c s : Cocone F) {W' : Scheme.{u}}
    (f : W' ⟶ c.pt) (hc : IsColimit (baseChangeCocone c f)) (j : J) :
    pullback.snd ((c.toCostructuredArrow ⋙ CostructuredArrow.toOver F c.pt).obj j).hom f ≫
        localDesc c s f hc =
      pullback.fst ((c.toCostructuredArrow ⋙ CostructuredArrow.toOver F c.pt).obj j).hom f ≫
        eqToHom (CostructuredArrow.toOver_obj_left F c.pt
          (c.toCostructuredArrow.obj j)) ≫ s.ι.app (c.toCostructuredArrow.obj j).left := by
  have := hc.fac (pulledTargetCocone c s f) j
  rw [baseChangeCocone_ι_app, Category.assoc] at this
  exact this

/-- Restricting the local descent morphism along a map into the covering scheme recovers the
legs of the target cocone. -/
private lemma pullback_snd_comp_localDesc {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c s : Cocone F) {W' V : Scheme.{u}}
    (f : W' ⟶ c.pt) (hc : IsColimit (baseChangeCocone c f))
    {h : V ⟶ c.pt} (g : V ⟶ W') (hg : g ≫ f = h) (k : J) :
    pullback.snd ((c.toCostructuredArrow ⋙ CostructuredArrow.toOver F c.pt).obj k).hom h ≫
        g ≫ localDesc c s f hc =
      pullback.fst ((c.toCostructuredArrow ⋙ CostructuredArrow.toOver F c.pt).obj k).hom h ≫
        eqToHom (CostructuredArrow.toOver_obj_left F c.pt (c.toCostructuredArrow.obj k)) ≫
          s.ι.app (c.toCostructuredArrow.obj k).left := by
  subst hg
  let d := (c.toCostructuredArrow ⋙ CostructuredArrow.toOver F c.pt).obj k
  let m : pullback d.hom (g ≫ f) ⟶ pullback d.hom f :=
    pullback.lift (pullback.fst d.hom (g ≫ f)) (pullback.snd d.hom (g ≫ f) ≫ g) (by
      simp only [Category.assoc]
      exact pullback.condition)
  have hmf : m ≫ pullback.fst d.hom f = pullback.fst d.hom (g ≫ f) := pullback.lift_fst _ _ _
  have hms : m ≫ pullback.snd d.hom f = pullback.snd d.hom (g ≫ f) ≫ g :=
    pullback.lift_snd _ _ _
  let leg := eqToHom (CostructuredArrow.toOver_obj_left F c.pt
    (c.toCostructuredArrow.obj k)) ≫ s.ι.app (c.toCostructuredArrow.obj k).left
  calc
    _ = (m ≫ pullback.snd d.hom f) ≫ localDesc c s f hc :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ localDesc c s f hc) hms.symm)
    _ = m ≫ (pullback.fst d.hom f ≫ leg) := by
      rw [Category.assoc, localDesc_fac c s f hc k]
    _ = pullback.fst d.hom (g ≫ f) ≫ leg := by simp only [← Category.assoc, hmf]

/-- The local descent morphisms attached to two members of a covering agree on their
overlap. -/
private lemma localDesc_compatible {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c s : Cocone F) {W₁ W₂ : Scheme.{u}}
    (f₁ : W₁ ⟶ c.pt) (f₂ : W₂ ⟶ c.pt)
    (hc₁ : IsColimit (baseChangeCocone c f₁))
    (hc₂ : IsColimit (baseChangeCocone c f₂))
    (hcov : IsColimit (baseChangeCocone c (pullback.fst f₁ f₂ ≫ f₁))) :
    pullback.fst f₁ f₂ ≫ localDesc c s f₁ hc₁ =
      pullback.snd f₁ f₂ ≫ localDesc c s f₂ hc₂ := by
  classical
  let p := pullback.fst f₁ f₂
  let q := pullback.snd f₁ f₂
  let h := p ≫ f₁
  let a := pullback.snd c.toOver.pt.hom h ≫ p ≫ localDesc c s f₁ hc₁
  let b := pullback.snd c.toOver.pt.hom h ≫ q ≫ localDesc c s f₂ hc₂
  have hab : a = b := by
    apply hcov.hom_ext
    intro k
    simp only [a, b]
    rw [baseChangeCocone_ι_app, Category.assoc, Category.assoc, IsIso.inv_hom_id_assoc,
      IsIso.inv_hom_id_assoc]
    exact (pullback_snd_comp_localDesc c s f₁ hc₁ (h := h) p rfl k).trans
      (pullback_snd_comp_localDesc c s f₂ hc₂ (h := h) q
        (pullback.condition (f := f₁) (g := f₂)).symm k).symm
  exact (cancel_epi (pullback.snd c.toOver.pt.hom h)).1
    (by simpa [a, b, Category.assoc] using hab)

/-- Any morphism factoring the legs of the target cocone restricts to the local descent
morphism on a covering scheme. -/
private lemma localDesc_eq_of_fac {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c s : Cocone F) {W' : Scheme.{u}}
    (f : W' ⟶ c.pt) (hc : IsColimit (baseChangeCocone c f))
    (m : c.pt ⟶ s.pt) (hm : ∀ j, c.ι.app j ≫ m = s.ι.app j) :
    f ≫ m = localDesc c s f hc := by
  rw [localDesc]
  refine (IsIso.eq_inv_comp _).2 (hc.hom_ext fun j => ?_)
  refine Eq.trans ?_ (hc.fac (pulledTargetCocone c s f) j).symm
  rw [baseChangeCocone_ι_app, Category.assoc, IsIso.inv_hom_id_assoc,
    ← Category.assoc, ← pullback.condition, Category.assoc]
  refine congrArg (pullback.fst _ f ≫ ·) ?_
  dsimp
  simp only [CostructuredArrow.toOver_obj_hom]
  exact hm j

/-- **Stacks Project, Tag 0BMP.** The colimit property for a cocone of schemes can be checked
on an fpqc covering of its vertex and on all pairwise overlaps. -/
@[stacks 0BMP]
public theorem isColimit_of_fpqc {J : Type v} [Category.{w} J]
    {F : J ⥤ Scheme.{u}} (c : Cocone F) {I : Type*}
    (W' : I → Scheme.{u}) (f : ∀ i, W' i ⟶ c.pt)
    (hfpqc : Presieve.ofArrows W' f ∈ Scheme.fpqcPrecoverage c.pt)
    (hlocal : ∀ i, Nonempty (IsColimit (baseChangeCocone c (f i))))
    (hoverlap : ∀ i j, Nonempty (IsColimit
      (baseChangeCocone c (pullback.fst (f i) (f j) ≫ f i)))) :
    Nonempty (IsColimit c) := by
  let E : Scheme.fpqcPrecoverage.ZeroHypercover c.pt := ⟨⟨I, W', f⟩, hfpqc⟩
  let localMap (s : Cocone F) (i : I) : W' i ⟶ s.pt :=
    localDesc c s (f i) (Classical.choice (hlocal i))
  let localAgree (s : Cocone F) (i j : I) :
      pullback.fst (f i) (f j) ≫ localMap s i =
      pullback.snd (f i) (f j) ≫ localMap s j :=
    localDesc_compatible c s (f i) (f j)
      (Classical.choice (hlocal i)) (Classical.choice (hlocal j))
      (Classical.choice (hoverlap i j))
  let glued (s : Cocone F) : c.pt ⟶ s.pt := E.glueMorphisms (localMap s) (localAgree s)
  refine ⟨{ desc := glued, fac := ?_, uniq := ?_ }⟩
  · intro s j
    let d := (c.toCostructuredArrow ⋙ CostructuredArrow.toOver F c.pt).obj j
    let e := CostructuredArrow.toOver_obj_left F c.pt (c.toCostructuredArrow.obj j)
    let E' := E.pullback₁ d.hom
    have hdesc : d.hom ≫ glued s = eqToHom e ≫ s.ι.app (c.toCostructuredArrow.obj j).left := by
      apply E'.hom_ext
      intro i
      dsimp [E', E]
      have eI : E'.I₀ = I := rfl
      let i₀ : I := eI ▸ i
      show pullback.fst d.hom (f i₀) ≫ d.hom ≫ glued s =
        pullback.fst d.hom (f i₀) ≫ eqToHom e ≫ s.ι.app (c.toCostructuredArrow.obj j).left
      calc
        _ = pullback.snd d.hom (f i₀) ≫ f i₀ ≫ glued s :=
          congrArg (fun z => z ≫ glued s) pullback.condition
        _ = pullback.snd d.hom (f i₀) ≫ localMap s i₀ :=
          congrArg (fun z => pullback.snd d.hom (f i₀) ≫ z)
            (Precoverage.ZeroHypercover.f_glueMorphisms E
              (localMap s) (localAgree s) i₀)
        _ = pullback.fst d.hom (f i₀) ≫
              (eqToHom e ≫ s.ι.app (c.toCostructuredArrow.obj j).left) :=
          localDesc_fac c s (f i₀) (Classical.choice (hlocal i₀)) j
    have hdom : c.ι.app j = eqToHom e.symm ≫ d.hom := by cat_disch
    cat_disch
  · intro s m hm
    apply E.hom_ext
    intro i
    calc
      f i ≫ m = localMap s i :=
        localDesc_eq_of_fac c s (f i) (Classical.choice (hlocal i)) m hm
      _ = f i ≫ glued s :=
        (Precoverage.ZeroHypercover.f_glueMorphisms E
          (localMap s) (localAgree s) i).symm

end AlgebraicGeometry
