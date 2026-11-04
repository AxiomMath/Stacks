module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces

/-!
# Translation in a groupoid in algebraic spaces

Let `G` be a groupoid in algebraic spaces and let `r` be a family of arrows indexed by the
object space, that is a morphism from the object space to the arrow space, whose source is an
isomorphism of the object space. Normalizing `r` so that its source becomes the identity, left
translation by the normalized family is an endomorphism of the arrow space; it is an
automorphism as soon as the target of `r` is an isomorphism too, and it carries the identity
arrow at the source of `r` to `r` itself.

When the object space is the spectrum of a field, every arrow of the groupoid over that field
is such a family, which is the situation of the source.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translationByArrow`: left translation by a
  family of arrows, normalized to have identity source.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translationByArrow_isIso`: translation is an
  automorphism of the arrow space.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.translationByArrow_identity`: translation sends
  the identity arrow at the source of `r` to `r`.

## Implementation notes

Both hypotheses on `r` are kept as `IsIso` instances rather than asking the object space to be
the spectrum of a field, so the results apply to any object space admitting such a family.

Bijectivity is proved pointwise, after evaluation at a test scheme. There the statement is
about a `Deformation.PointwiseGroupoid`: translating an arrow `x` by the arrow `a (t x)` out of
its target is, in the evaluated groupoid, postcomposition with a fixed isomorphism, transported
along the identification of the arrow set with the disjoint union over all pairs of endpoints
of the morphism sets of the groupoid. Postcomposition with an isomorphism is a bijection on
each morphism set, and the induced reindexing of endpoints is the bijection `σ` given by the
target of `r`, so the transported map is a bijection of the arrow set.

## References

* [Stacks Project, Tag 06E3](https://stacks.math.columbia.edu/tag/06E3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- Pointwise bijectivity of left translation: if `a` assigns to every object an arrow with
that object as source and `σ` as target, and `σ` is bijective, then composing an arrow `x`
with `a` at the target of `x` is a bijection of the set of arrows. -/
private theorem pointwise_translation_bijective
    {U R : Type u} {s t : R → U} {c : {p : R × R // s p.1 = t p.2} → R}
    (P : Deformation.PointwiseGroupoid s t c) (a : U → R) (σ : U → U)
    (ha : ∀ x, s (a x) = x) (hta : ∀ x, t (a x) = σ x) (hσ : Function.Bijective σ) :
    Function.Bijective (fun x => c ⟨(a (t x), x), ha (t x)⟩) := by
  classical
  let _inst : Groupoid U := P.groupoid
  let σe : U ≃ U := Equiv.ofBijective σ hσ
  have hta' (x : U) : t (a x) = σe x := by simpa [σe] using hta x
  let α (x : U) : x ⟶ σe x := (P.arrowEquiv x (σe x)).symm ⟨a x, ha x, hta' x⟩
  let forward (x : R) : R := c ⟨(a (t x), x), ha (t x)⟩
  have comp_source {x y z : U} (f g : R)
      (hf : s f = x) (htf : t f = y) (hg : s g = y) (htg : t g = z) :
      s (c ⟨(g, f), hg.trans htf.symm⟩) = x :=
    (P.source_comp g f (hg.trans htf.symm)).trans hf
  have comp_target {x y z : U} (f g : R)
      (hf : s f = x) (htf : t f = y) (hg : s g = y) (htg : t g = z) :
      t (c ⟨(g, f), hg.trans htf.symm⟩) = z :=
    (P.target_comp g f (hg.trans htf.symm)).trans htg
  have comp_hom {x y z : U} (f g : R)
      (hf : s f = x) (htf : t f = y) (hg : s g = y) (htg : t g = z) :
      (P.arrowEquiv x z).symm ⟨c ⟨(g, f), hg.trans htf.symm⟩,
        comp_source f g hf htf hg htg, comp_target f g hf htf hg htg⟩ =
        (P.arrowEquiv x y).symm ⟨f, hf, htf⟩ ≫ (P.arrowEquiv y z).symm ⟨g, hg, htg⟩ := by
    have hraw : c ⟨(g, f), hg.trans htf.symm⟩ =
        (P.arrowEquiv x z
          ((P.arrowEquiv x y).symm ⟨f, hf, htf⟩ ≫
            (P.arrowEquiv y z).symm ⟨g, hg, htg⟩)).1 := by
      simpa using (P.comp_eq
        ((P.arrowEquiv x y).symm ⟨f, hf, htf⟩)
        ((P.arrowEquiv y z).symm ⟨g, hg, htg⟩)).symm
    apply (P.arrowEquiv x z).injective
    simpa only [Equiv.apply_symm_apply] using Subtype.ext hraw
  let ArrowBundle := Σ x : U, Σ y : U, x ⟶ y
  let Endpoint := Σ _ : U, U
  let endpoint (x : R) : Endpoint := ⟨s x, t x⟩
  let Fiber (p : Endpoint) := {x : R // endpoint x = p}
  let endpointEquiv (x y : U) :
      {r : R // s r = x ∧ t r = y} ≃ Fiber (⟨x, y⟩ : Endpoint) :=
    Equiv.subtypeEquivRight fun _ =>
      ⟨fun ⟨hs, ht⟩ => Sigma.ext hs (heq_of_eq ht),
        fun h => ⟨congrArg Sigma.fst h, congrArg Sigma.snd h⟩⟩
  let arrowEquivBundle : ArrowBundle ≃ (Σ x : U, Σ y : U, Fiber (⟨x, y⟩ : Endpoint)) :=
    Equiv.sigmaCongrRight (fun x =>
      Equiv.sigmaCongrRight (fun y => (P.arrowEquiv x y).trans (endpointEquiv x y)))
  let flatten : (Σ x : U, Σ y : U, Fiber (⟨x, y⟩ : Endpoint)) ≃ (Σ p : Endpoint, Fiber p) :=
    { toFun := fun q => ⟨⟨q.1, q.2.1⟩, q.2.2⟩
      invFun := fun q => ⟨q.1.1, q.1.2, q.2⟩
      left_inv := by rintro ⟨x, y, z⟩; rfl
      right_inv := by rintro ⟨⟨x, y⟩, z⟩; rfl }
  let endpointBundle : (Σ x : U, Σ y : U, Fiber (⟨x, y⟩ : Endpoint)) ≃ R :=
    flatten.trans (Equiv.sigmaFiberEquiv endpoint)
  let e : ArrowBundle ≃ R := arrowEquivBundle.trans endpointBundle
  let pack (x : R) : ArrowBundle :=
    ⟨s x, t x, (P.arrowEquiv (s x) (t x)).symm ⟨x, rfl, rfl⟩⟩
  have hpack (x : R) : e (pack x) = x := by
    dsimp [e, endpointBundle, flatten, arrowEquivBundle, endpointEquiv, pack]
    rw [Equiv.sigmaFiberEquiv_apply]
    show (((P.arrowEquiv (s x) (t x)).trans (endpointEquiv (s x) (t x)))
      ((P.arrowEquiv (s x) (t x)).symm ⟨x, rfl, rfl⟩)).1 = x
    show (endpointEquiv (s x) (t x)
      (P.arrowEquiv (s x) (t x) ((P.arrowEquiv (s x) (t x)).symm ⟨x, rfl, rfl⟩))).1 = x
    rw [Equiv.apply_symm_apply]
    rfl
  let onBundle (q : ArrowBundle) : ArrowBundle := ⟨q.1, σe q.2.1, q.2.2 ≫ α q.2.1⟩
  let postEquiv (x y : U) : (x ⟶ y) ≃ (x ⟶ σe y) := (asIso (α y)).homToEquiv
  let eBundle : ArrowBundle ≃ ArrowBundle :=
    Equiv.sigmaCongrRight (fun x => Equiv.sigmaCongr σe (fun y => postEquiv x y))
  let translationEquiv : R ≃ R := e.symm.trans (eBundle.trans e)
  have hraw (x : R) :
      forward x =
        (P.arrowEquiv (s x) (σe (t x))
          ((P.arrowEquiv (s x) (t x)).symm ⟨x, rfl, rfl⟩ ≫ α (t x))).1 := by
    have h := congrArg (P.arrowEquiv (s x) (σe (t x)) :
      (s x ⟶ σe (t x)) → {r : R // s r = s x ∧ t r = σe (t x)})
      (comp_hom x (a (t x)) rfl rfl (ha (t x)) (hta' (t x)))
    simpa only [Equiv.apply_symm_apply] using congrArg Subtype.val h
  have htranslate_raw (x : R) : e (onBundle (pack x)) = forward x := by
    rw [hraw]
    dsimp [e, endpointBundle, flatten, arrowEquivBundle, endpointEquiv, onBundle, pack]
    rw [Equiv.sigmaFiberEquiv_apply]
    show (((P.arrowEquiv (s x) (σe (t x))).trans (endpointEquiv (s x) (σe (t x))))
      ((P.arrowEquiv (s x) (t x)).symm ⟨x, rfl, rfl⟩ ≫ α (t x))).1 =
        (P.arrowEquiv (s x) (σe (t x))
          ((P.arrowEquiv (s x) (t x)).symm ⟨x, rfl, rfl⟩ ≫ α (t x))).1
    show (endpointEquiv (s x) (σe (t x))
      (P.arrowEquiv (s x) (σe (t x))
        ((P.arrowEquiv (s x) (t x)).symm ⟨x, rfl, rfl⟩ ≫ α (t x)))).1 = _
    dsimp [endpointEquiv]
    rfl
  have hpack_inv (x : R) : pack x = e.symm x := e.eq_symm_apply.2 (hpack x)
  have htranslation (x : R) : forward x = translationEquiv x := by
    calc forward x = e (onBundle (pack x)) := (htranslate_raw x).symm
      _ = e (onBundle (e.symm x)) := congrArg (fun q => e (onBundle q)) (hpack_inv x)
      _ = translationEquiv x := rfl
  show Function.Bijective forward
  rw [funext htranslation]
  exact translationEquiv.bijective

/-- Left translation by a family of arrows indexed by the object space, normalized so that its
source is the identity on the object space: it sends an arrow `x` to the composite of `x` with
the normalized arrow out of the target of `x`. -/
noncomputable def translationByArrow (G : GroupoidInAlgebraicSpaces C S hS B)
    (r : G.objects ⟶ G.arrows) [IsIso (r ≫ G.source)] : G.arrows ⟶ G.arrows :=
  let a : G.objects ⟶ G.arrows := inv (r ≫ G.source) ≫ r
  (ObjectProperty.homMk
    (pullback.lift (G.target.hom ≫ a.hom) (𝟙 G.arrows.obj)
      (by
        change G.target.hom ≫ a.hom ≫ G.source.hom = (𝟙 G.arrows.obj) ≫ G.target.hom
        simp [a]) :
      G.arrows.obj ⟶ (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj) :
      G.arrows ⟶ AlgebraicSpaces.fiberProduct C S hS G.source G.target) ≫ G.comp

/-- The normalized arrow `inv (r ≫ source) ≫ r` has source the identity, also at test schemes. -/
private theorem normalized_source_app (G : GroupoidInAlgebraicSpaces C S hS B)
    (r : G.objects ⟶ G.arrows) [IsIso (r ≫ G.source)]
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : G.objects.obj.obj T) :
    G.source.hom.app T ((inv (r ≫ G.source) ≫ r).hom.app T x) = x :=
  congrArg (fun f : G.objects ⟶ G.objects => f.hom.app T x)
    (by simp [Category.assoc] : (inv (r ≫ G.source) ≫ r) ≫ G.source = 𝟙 G.objects)

/-- Translation evaluated at a test scheme is the composition of the evaluated groupoid: it
sends an arrow `x` to the composite of `x` with the normalized arrow out of the target of `x`. -/
private theorem translationByArrow_app (G : GroupoidInAlgebraicSpaces C S hS B)
    (r : G.objects ⟶ G.arrows) [IsIso (r ≫ G.source)]
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : G.arrows.obj.obj T) :
    (translationByArrow G r).hom.app T x =
      G.toGroupoidInFunctors.compose T
        ((inv (r ≫ G.source) ≫ r).hom.app T (G.toGroupoidInFunctors.target.app T x)) x
        (normalized_source_app G r T _) := by
  let a : G.objects ⟶ G.arrows := inv (r ≫ G.source) ≫ r
  let F := G.toGroupoidInFunctors
  let q : G.arrows.obj ⟶
      Deformation.composableArrows G.objects.obj G.arrows.obj G.source.hom G.target.hom :=
    { app := fun T => ↾ fun y => ⟨(a.hom.app T (G.target.hom.app T y), y),
        normalized_source_app G r T _⟩
      naturality := by
        intro X Y f
        ext y
        dsimp [Deformation.composableArrows]
        apply Subtype.ext
        apply Prod.ext
        · calc a.hom.app Y (G.target.hom.app Y (G.arrows.obj.map f y)) =
                  a.hom.app Y (G.objects.obj.map f (G.target.hom.app X y)) := by
                rw [G.target.hom.naturality_apply]
            _ = G.arrows.obj.map f (a.hom.app X (G.target.hom.app X y)) :=
                a.hom.naturality_apply f _
        · rfl }
  have hcomp : (G.target.hom ≫ a.hom) ≫ G.source.hom =
      (𝟙 G.arrows.obj) ≫ G.target.hom := by simp [a, Category.assoc]
  have hLift :
      (pullback.lift (G.target.hom ≫ a.hom) (𝟙 G.arrows.obj) hcomp :
          G.arrows.obj ⟶ (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj) =
        q ≫ composableToPullback G.source.hom G.target.hom := by
    apply pullback.hom_ext
    · calc pullback.lift (G.target.hom ≫ a.hom) (𝟙 G.arrows.obj) hcomp ≫
              pullback.fst G.source.hom G.target.hom = G.target.hom ≫ a.hom :=
            pullback.lift_fst _ _ _
        _ = q ≫ composableToPullback G.source.hom G.target.hom ≫
              pullback.fst G.source.hom G.target.hom := by
            rw [composableToPullback, pullback.lift_fst]
            ext T y
            simp [q]
    · calc pullback.lift (G.target.hom ≫ a.hom) (𝟙 G.arrows.obj) hcomp ≫
              pullback.snd G.source.hom G.target.hom = 𝟙 G.arrows.obj :=
            pullback.lift_snd _ _ _
        _ = q ≫ composableToPullback G.source.hom G.target.hom ≫
              pullback.snd G.source.hom G.target.hom := by
            rw [composableToPullback, pullback.lift_snd]
            ext T y
            simp [q]
  have hactual (y : G.arrows.obj.obj T) :
      (translationByArrow G r).hom.app T y = (F.comp.app T) (q.app T y) := by
    show G.comp.hom.app T
        ((pullback.lift (G.target.hom ≫ a.hom) (𝟙 G.arrows.obj) hcomp).app T y) =
      (F.comp.app T) (q.app T y)
    have h := congrArg
      (fun f : G.arrows.obj ⟶ (AlgebraicSpaces.fiberProduct C S hS G.source G.target).obj =>
        G.comp.hom.app T (f.app T y)) hLift
    change G.comp.hom.app T
        ((pullback.lift (G.target.hom ≫ a.hom) (𝟙 G.arrows.obj) hcomp).app T y) =
      G.comp.hom.app T ((q.app T ≫
        (composableToPullback G.source.hom G.target.hom).app T) y) at h
    show G.comp.hom.app T
        ((pullback.lift (G.target.hom ≫ a.hom) (𝟙 G.arrows.obj) hcomp).app T y) =
      G.comp.hom.app T ((composableToPullback G.source.hom G.target.hom).app T (q.app T y))
    simpa using h
  rw [hactual x]
  rfl

/-- **Stacks 06E3.** Translation by a family of arrows whose source and target are both
isomorphisms of the object space is an automorphism of the arrow space. -/
@[stacks 06E3 "the automorphism"]
theorem translationByArrow_isIso (G : GroupoidInAlgebraicSpaces C S hS B)
    (r : G.objects ⟶ G.arrows) [IsIso (r ≫ G.source)] [IsIso (r ≫ G.target)] :
    IsIso (translationByArrow G r) := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro T
  rw [isIso_iff_bijective]
  let a : G.objects ⟶ G.arrows := inv (r ≫ G.source) ≫ r
  let F := G.toGroupoidInFunctors
  have : IsIso (a ≫ G.target) := by
    simpa [a, Category.assoc] using
      (inferInstance : IsIso (inv (r ≫ G.source) ≫ (r ≫ G.target)))
  have hbij := pointwise_translation_bijective (F.pointwiseData T)
    (a.hom.app T) ((a ≫ G.target).hom.app T)
    (normalized_source_app G r T)
    (fun _ => rfl) ((isIso_iff_bijective ((a ≫ G.target).hom.app T)).1 inferInstance)
  have hactual (x : G.arrows.obj.obj T) :
      (translationByArrow G r).hom.app T x =
        F.compose T (a.hom.app T (F.target.app T x)) x
          (normalized_source_app G r T _) := by
    simpa [a, F] using translationByArrow_app G r T x
  have hbijComp : Function.Bijective
      (fun x => F.compose T (a.hom.app T (F.target.app T x)) x
        (normalized_source_app G r T _)) := by
    simpa [Deformation.GroupoidInFunctors.compose] using hbij
  show Function.Bijective
    (fun x : G.arrows.obj.obj T => (translationByArrow G r).hom.app T x)
  rw [funext hactual]
  exact hbijComp

/-- **Stacks 06E3.** Translation by `r` takes the identity arrow at the source of `r` to `r`
itself. -/
@[stacks 06E3 "image of the identity"]
theorem translationByArrow_identity (G : GroupoidInAlgebraicSpaces C S hS B)
    (r : G.objects ⟶ G.arrows) [IsIso (r ≫ G.source)]
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : G.toGroupoidInFunctors.Evaluation T) :
    (translationByArrow G r).hom.app T
      (G.toGroupoidInFunctors.identity T ((r ≫ G.source).hom.app T x)) = r.hom.app T x := by
  let a : G.objects ⟶ G.arrows := inv (r ≫ G.source) ≫ r
  let F := G.toGroupoidInFunctors
  let _inst : Groupoid (G.objects.obj.obj T) := G.toGroupoidInFunctors.evaluationGroupoid T
  let z := (r ≫ G.source).hom.app T x
  have ha_at : a.hom.app T z = r.hom.app T x := by
    dsimp [a, z]
    exact congrArg (r.hom.app T)
      (congrArg (fun f : G.objects ⟶ G.objects => f.hom.app T x)
        (IsIso.hom_inv_id (r ≫ G.source)))
  show (translationByArrow G r).hom.app T (F.identity T z) = r.hom.app T x
  have hmap_id := translationByArrow_app G r T (F.identity T z)
  have htarget_id : F.target.app T (F.identity T z) = z := by
    show F.target.app T ((F.evaluationArrowEquiv T z z (𝟙 z)).1) = z
    exact (F.evaluationArrowEquiv T z z (𝟙 z)).2.2
  have harg : (inv (r ≫ G.source) ≫ r).hom.app T
      (G.toGroupoidInFunctors.target.app T (F.identity T z)) = a.hom.app T z := by
    rw [htarget_id]
  have hs : G.source.hom.app T (a.hom.app T z) = z := normalized_source_app G r T z
  have hmap_id' : (translationByArrow G r).hom.app T (F.identity T z) =
      F.compose T (a.hom.app T z) (F.identity T z) (hs.trans htarget_id.symm) := by
    simpa only [harg] using hmap_id
  rw [hmap_id', ← ha_at]
  let σ := (a ≫ G.target).hom.app T z
  have ht : G.target.hom.app T (a.hom.app T z) = σ := rfl
  let f : z ⟶ σ := (F.evaluationArrowEquiv T z σ).symm ⟨a.hom.app T z, hs, ht⟩
  have hf_val : (F.evaluationArrowEquiv T z σ f).1 = a.hom.app T z :=
    congrArg Subtype.val
      (Equiv.apply_symm_apply (F.evaluationArrowEquiv T z σ) ⟨a.hom.app T z, hs, ht⟩)
  have hcomp : F.compose T (a.hom.app T z) (F.identity T z) (hs.trans htarget_id.symm) =
      (F.evaluationArrowEquiv T z σ (𝟙 z ≫ f)).1 := by
    show F.compose T (a.hom.app T z)
        (F.evaluationArrowEquiv T z z (𝟙 z)).1 (hs.trans htarget_id.symm) = _
    simpa only [hf_val] using (F.evaluationArrowEquiv_comp T (𝟙 z) f).symm
  show F.compose T (a.hom.app T z) (F.identity T z)
      (hs.trans htarget_id.symm) = a.hom.app T z
  rw [hcomp]
  exact (congrArg (fun g => (F.evaluationArrowEquiv T z σ g).1) (Category.id_comp f)).trans hf_val

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
