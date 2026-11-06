module

public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.EquivalencePort.ChowLemma.DatumBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsSmallerBase
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable

namespace CategoryTheory.OverShriek.C1573
end CategoryTheory.OverShriek.C1573
namespace CategoryTheory.OverShriek.C1573.IsLift
end CategoryTheory.OverShriek.C1573.IsLift
namespace AlgebraicGeometry.Space.C1573
end AlgebraicGeometry.Space.C1573
namespace AlgebraicGeometry.Space.C1573.ChowDatum
end AlgebraicGeometry.Space.C1573.ChowDatum

/-!
# Transporting a Chow datum from the base `Spec ℤ` to an arbitrary base

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of the big fppf site, and let
`Λ` be the relocalization along `S ⟶ Spec ℤ`, which views presheaves over `S` as presheaves over
`Spec ℤ` (Stacks 03I5). A Chow datum for `Λ f` gives a Chow datum for `f`.

A morphism `a : h_W ⟶ Λ G` from a representable presheaf carries a factorization `ψ` of the
structure morphism of `W` through `S` and a morphism `b : h_{(W, ψ)} ⟶ G`; we say that `b` lifts
`a`. Lifts are compatible with morphisms, cartesian squares, represented properties of
morphisms and density on points, which transports every part of the datum except the closed
subscheme of projective space; that one is base changed from `Spec ℤ` to `S`, and the immersion
into projective space over `Y` uses that `Λ (ℙᵏ_Y)` is `Λ Y × ℙᵏ_ℤ`.

## Main results

* `CategoryTheory.OverShriek.C1573.IsLift`: `b` lifts `a`.
* `CategoryTheory.OverShriek.C1573.IsLift.isPullback`: lifts of a cartesian square are cartesian.
* `CategoryTheory.OverShriek.C1573.IsLift.presheaf`: lifts inherit represented properties.
* `AlgebraicGeometry.Space.C1573.isPullback_relocalize_projectiveSpacePresheaf`: `Λ (ℙᵏ_Y)` is the
  product of `Λ Y` with `ℙᵏ_ℤ`.
* `AlgebraicGeometry.Space.C1573.ChowDatum.ofViewOverIntegers`: the transport of a Chow datum.

## References

* [Stacks Project, Tag 088U](https://stacks.math.columbia.edu/tag/088U)
* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe v u

namespace CategoryTheory.OverShriek

open _root_.CategoryTheory.OverShriek.C1573 _root_.CategoryTheory.Limits.C1573
  _root_.AlgebraicGeometry.C1573
variable {C : Type u} [Category.{v} C] {U V : C} (f : V ⟶ U) {G : (Over V)ᵒᵖ ⥤ Type v}

/-- A section of `Λ G` over `W`, read as a factorization `ψ` of the structure morphism of `W`
together with a section of `G` over `(W.left, ψ)`. -/
def C1573.relocalizeSec {W : Over U} (p : ((relocalizePresheafFunctor f).obj G).obj (op W)) :
    Σ ψ : W.left ⟶ V, G.obj (op (Over.mk ψ)) :=
  p.1

/-- The factorization carried by a section of `Λ G` over `W` composes with `f` to the structure
morphism of `W`. -/
theorem C1573.relocalizeSec_comp {W : Over U}
    (p : ((relocalizePresheafFunctor f).obj G).obj (op W)) :
    (relocalizeSec f p).1 ≫ f = W.hom :=
  p.2

/-- Restricting a section of `Λ G` along `m : W' ⟶ W` precomposes its factorization with
`m.left` and restricts its section of `G` accordingly. -/
theorem C1573.relocalizeSec_map {W W' : Over U} (m : W' ⟶ W)
    (p : ((relocalizePresheafFunctor f).obj G).obj (op W)) :
    relocalizeSec f (((relocalizePresheafFunctor f).obj G).map m.op p) =
      ⟨m.left ≫ (relocalizeSec f p).1,
        G.map (Over.homMk m.left rfl : Over.mk (m.left ≫ (relocalizeSec f p).1) ⟶
          Over.mk (relocalizeSec f p).1).op (relocalizeSec f p).2⟩ :=
  rfl

/-- The factorization `ψ` of the structure morphism carried by a morphism `h_W ⟶ Λ G`. -/
def C1573.liftPsi {W : Over U} (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G) :
    W.left ⟶ V :=
  (relocalizeSec f (yonedaEquiv a)).1

/-- The factorization `ψ` carried by `a : h_W ⟶ Λ G` satisfies `ψ ≫ f = W.hom`. -/
theorem C1573.liftPsi_comp {W : Over U} (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G) :
    liftPsi f a ≫ f = W.hom :=
  relocalizeSec_comp f _

/-- The object `(W.left, ψ)` of `C/V` carried by a morphism `h_W ⟶ Λ G`. -/
abbrev C1573.liftObj {W : Over U} (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G) :
    Over V :=
  Over.mk (liftPsi f a)

/-- The morphism `h_{(W.left, ψ)} ⟶ G` carried by a morphism `h_W ⟶ Λ G`. -/
def C1573.liftMap {W : Over U} (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G) :
    yoneda.obj (liftObj f a) ⟶ G :=
  yonedaEquiv.symm (relocalizeSec f (yonedaEquiv a)).2

/-- The section of `Λ h_{(W.left, ψ)}` over `W` corresponding to the identification of `h_W` with
`Λ h_{(W.left, ψ)}`. -/
private theorem yonedaEquiv_relocalizeYonedaFactorHom {W : Over U} {ψ : W.left ⟶ V}
    (h : ψ ≫ f = W.hom) :
    yonedaEquiv (relocalizeYonedaFactorHom f h) =
      (⟨⟨ψ, 𝟙 (Over.mk ψ)⟩, h⟩ :
        ((relocalizePresheafFunctor f).obj (yoneda.obj (Over.mk ψ))).obj (op W)) :=
  yonedaEquiv.apply_symm_apply _

/-- A morphism `a : h_W ⟶ Λ G` is the identification of `h_W` with `Λ h_{(W.left, ψ)}` followed
by `Λ` of the morphism `h_{(W.left, ψ)} ⟶ G` it carries. -/
theorem C1573.eq_relocalizeYonedaFactorIso_comp {W : Over U}
    (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G) :
    a = (relocalizeYonedaFactorIso f (liftPsi_comp f a)).hom ≫
      (relocalizePresheafFunctor f).map (liftMap f a) := by
  set p := yonedaEquiv a with hp
  have main : a = relocalizeYonedaFactorHom f p.2 ≫
      (relocalizePresheafFunctor f).map (yonedaEquiv.symm p.val.snd) := by
    refine yonedaEquiv.injective ?_
    have hsigma : (yonedaEquiv.symm p.val.snd).app (op (Over.mk p.val.fst))
          (𝟙 (Over.mk p.val.fst)) = p.val.snd :=
      yonedaEquiv.apply_symm_apply _
    rw [yonedaEquiv_comp, yonedaEquiv_relocalizeYonedaFactorHom, ← hp]
    exact Subtype.ext (congrArg (Sigma.mk p.val.fst) hsigma.symm)
  exact main.trans
    (congrArg (fun t => t ≫ (relocalizePresheafFunctor f).map (yonedaEquiv.symm p.val.snd))
      (relocalizeYonedaFactorIso_hom f p.2).symm)

/-- The relocalization functor is faithful: it is an equivalence onto the slice over `h_V` followed
by the forgetful functor. -/
instance C1573.faithful_relocalizePresheafFunctor : (relocalizePresheafFunctor f).Faithful := by
  have h1 : (presheafFunctorToOver (U := V) (C := C)).Faithful :=
    (presheafEquivalence (U := V)).faithful_functor
  have h2 : (Over.map (yoneda.map f : yoneda.obj V ⟶ yoneda.obj U)).Faithful :=
    ⟨fun {_ _} _ _ h => Over.OverMorphism.ext (by simpa using congrArg CommaMorphism.left h)⟩
  have h3 : (fiberFunctor (𝟙 (yoneda.obj U)) (C := C)).Faithful :=
    (presheafEquivalence (U := U)).faithful_inverse
  exact Functor.Faithful.comp _ (Over.map (yoneda.map f) ⋙ fiberFunctor (𝟙 (yoneda.obj U)))

/-- The factorization carried by `h_m ≫ a` is `m.left` followed by the factorization carried
by `a`. -/
theorem C1573.liftPsi_yoneda_map_comp {W W' : Over U} (m : W' ⟶ W)
    (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G) :
    liftPsi f (yoneda.map m ≫ a) = m.left ≫ liftPsi f a := by
  unfold liftPsi
  rw [← yonedaEquiv_naturality, relocalizeSec_map]

/-- **Naturality of the presentation of `h_W` as `Λ h_{(W.left, ψ)}`.** -/
theorem C1573.yoneda_map_comp_relocalizeYonedaFactorIso_hom {W W' : Over U} (m : W' ⟶ W)
    {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) {ψ' : W'.left ⟶ V} (h' : ψ' ≫ f = W'.hom)
    (k : Over.mk ψ' ⟶ Over.mk ψ) (hk : k.left = m.left) :
    yoneda.map m ≫ (relocalizeYonedaFactorIso f h).hom =
      (relocalizeYonedaFactorIso f h').hom ≫
        (relocalizePresheafFunctor f).map (yoneda.map k) := by
  simp only [relocalizeYonedaFactorIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Iso.app_inv, Category.assoc]
  have hn := (relocalizeYonedaIso f).inv.naturality k
  simp only [Functor.comp_map] at hn
  rw [← hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  congr 2
  ext
  simp [relocalizeFactorIso, hk]

/-- `b : h_{(W.left, ψ)} ⟶ G` *lifts* `a : h_W ⟶ Λ G`: `a` is `Λ b` read through the
identification of `h_W` with `Λ h_{(W.left, ψ)}`. -/
def C1573.IsLift {W : Over U} (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G)
    {ψ : W.left ⟶ V} (h : ψ ≫ f = W.hom) (b : yoneda.obj (Over.mk ψ) ⟶ G) : Prop :=
  (relocalizeYonedaFactorIso f h).hom ≫ (relocalizePresheafFunctor f).map b = a

/-- The morphism `h_{(W.left, ψ)} ⟶ G` carried by `a` lifts `a`. -/
theorem C1573.isLift_liftMap {W : Over U} (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G) :
    IsLift f a (liftPsi_comp f a) (liftMap f a) :=
  (eq_relocalizeYonedaFactorIso_comp f a).symm

/-- A lift exists along every factorization equal to the one `a` carries. -/
theorem C1573.exists_isLift {W : Over U} (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G)
    (ψ : W.left ⟶ V) (hψ : liftPsi f a = ψ) (h : ψ ≫ f = W.hom) :
    ∃ b : yoneda.obj (Over.mk ψ) ⟶ G, IsLift f a h b := by
  subst hψ
  exact ⟨_, isLift_liftMap f a⟩

/-- If `b` lifts `a`, then `b ≫ k` lifts `a ≫ Λ k`. -/
theorem C1573.IsLift.comp_map {G' : (Over V)ᵒᵖ ⥤ Type v} {W : Over U}
    {a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G} {ψ : W.left ⟶ V}
    {h : ψ ≫ f = W.hom} {b : yoneda.obj (Over.mk ψ) ⟶ G} (hb : IsLift f a h b) (k : G ⟶ G') :
    IsLift f (a ≫ (relocalizePresheafFunctor f).map k) h (b ≫ k) := by
  rw [IsLift, Functor.map_comp, ← Category.assoc, hb]

/-- Two lifts of `a` along the same factorization are equal. -/
theorem C1573.IsLift.unique {W : Over U} {a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G}
    {ψ : W.left ⟶ V} {h : ψ ≫ f = W.hom} {b b' : yoneda.obj (Over.mk ψ) ⟶ G}
    (hb : IsLift f a h b) (hb' : IsLift f a h b') : b = b' :=
  (relocalizePresheafFunctor f).map_injective
    ((cancel_epi (relocalizeYonedaFactorIso f h).hom).1 (hb.trans hb'.symm))

/-- The factorization carried by the composite of the identification of `h_W` with
`Λ h_{(W.left, ψ)}` and `Λ b` is `ψ`. -/
theorem C1573.liftPsi_relocalizeYonedaFactorIso_hom_comp {W : Over U} {ψ : W.left ⟶ V}
    (h : ψ ≫ f = W.hom) (b : yoneda.obj (Over.mk ψ) ⟶ G) :
    liftPsi f ((relocalizeYonedaFactorIso f h).hom ≫ (relocalizePresheafFunctor f).map b) = ψ := by
  rw [relocalizeYonedaFactorIso_hom]
  unfold liftPsi relocalizeSec
  rw [yonedaEquiv_comp, yonedaEquiv_relocalizeYonedaFactorHom]
  rfl

/-- If `b` lifts `a` along `ψ`, then `ψ` is the factorization carried by `a`. -/
theorem C1573.IsLift.liftPsi_eq {W : Over U}
    {a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G}
    {ψ : W.left ⟶ V} {h : ψ ≫ f = W.hom} {b : yoneda.obj (Over.mk ψ) ⟶ G}
    (hb : IsLift f a h b) : liftPsi f a = ψ := by
  rw [← hb]
  exact liftPsi_relocalizeYonedaFactorIso_hom_comp f h b

/-- Postcomposing with `Λ k` does not change the factorization carried by `a`. -/
theorem C1573.liftPsi_comp_map {G' : (Over V)ᵒᵖ ⥤ Type v} {W : Over U}
    (a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G) (k : G ⟶ G') :
    liftPsi f (a ≫ (relocalizePresheafFunctor f).map k) = liftPsi f a :=
  ((isLift_liftMap f a).comp_map f k).liftPsi_eq f

/-- The factorizations carried by two lifts are compatible with a morphism over `Λ G`. -/
theorem C1573.IsLift.left_comp {W₁ W₂ : Over U} {m : W₁ ⟶ W₂}
    {a₁ : yoneda.obj W₁ ⟶ (relocalizePresheafFunctor f).obj G}
    {a₂ : yoneda.obj W₂ ⟶ (relocalizePresheafFunctor f).obj G}
    {ψ₁ : W₁.left ⟶ V} {h₁ : ψ₁ ≫ f = W₁.hom} {b₁ : yoneda.obj (Over.mk ψ₁) ⟶ G}
    {ψ₂ : W₂.left ⟶ V} {h₂ : ψ₂ ≫ f = W₂.hom} {b₂ : yoneda.obj (Over.mk ψ₂) ⟶ G}
    (hb₁ : IsLift f a₁ h₁ b₁) (hb₂ : IsLift f a₂ h₂ b₂) (hm : yoneda.map m ≫ a₂ = a₁) :
    m.left ≫ ψ₂ = ψ₁ := by
  rw [← hb₁.liftPsi_eq, ← hb₂.liftPsi_eq, ← hm, liftPsi_yoneda_map_comp]

/-- **Two lifts are compatible with a morphism over `Λ G`.** -/
theorem C1573.IsLift.comm {W₁ W₂ : Over U} {m : W₁ ⟶ W₂}
    {a₁ : yoneda.obj W₁ ⟶ (relocalizePresheafFunctor f).obj G}
    {a₂ : yoneda.obj W₂ ⟶ (relocalizePresheafFunctor f).obj G}
    {ψ₁ : W₁.left ⟶ V} {h₁ : ψ₁ ≫ f = W₁.hom} {b₁ : yoneda.obj (Over.mk ψ₁) ⟶ G}
    {ψ₂ : W₂.left ⟶ V} {h₂ : ψ₂ ≫ f = W₂.hom} {b₂ : yoneda.obj (Over.mk ψ₂) ⟶ G}
    (hb₁ : IsLift f a₁ h₁ b₁) (hb₂ : IsLift f a₂ h₂ b₂) (hm : yoneda.map m ≫ a₂ = a₁)
    (k : Over.mk ψ₁ ⟶ Over.mk ψ₂) (hk : k.left = m.left) :
    yoneda.map k ≫ b₂ = b₁ := by
  apply (relocalizePresheafFunctor f).map_injective
  rw [← cancel_epi (relocalizeYonedaFactorIso f h₁).hom, Functor.map_comp, ← Category.assoc,
    ← yoneda_map_comp_relocalizeYonedaFactorIso_hom f m h₂ h₁ k hk, Category.assoc]
  rw [show _ = a₂ from hb₂, show _ = a₁ from hb₁, hm]

/-- **A cartesian square of representables over `Λ G` comes from one over `G`.** -/
theorem C1573.IsLift.isPullback {W₁ W₂ W₃ : Over U} {m₁ : W₁ ⟶ W₂} {m₂ : W₁ ⟶ W₃}
    {a₁ : yoneda.obj W₁ ⟶ (relocalizePresheafFunctor f).obj G}
    {a₂ : yoneda.obj W₂ ⟶ (relocalizePresheafFunctor f).obj G}
    {a₃ : yoneda.obj W₃ ⟶ (relocalizePresheafFunctor f).obj G}
    {ψ₁ : W₁.left ⟶ V} {h₁ : ψ₁ ≫ f = W₁.hom} {b₁ : yoneda.obj (Over.mk ψ₁) ⟶ G}
    {ψ₂ : W₂.left ⟶ V} {h₂ : ψ₂ ≫ f = W₂.hom} {b₂ : yoneda.obj (Over.mk ψ₂) ⟶ G}
    {ψ₃ : W₃.left ⟶ V} {h₃ : ψ₃ ≫ f = W₃.hom} {b₃ : yoneda.obj (Over.mk ψ₃) ⟶ G}
    (hb₁ : IsLift f a₁ h₁ b₁) (hb₂ : IsLift f a₂ h₂ b₂) (hb₃ : IsLift f a₃ h₃ b₃)
    (hm₁ : yoneda.map m₁ ≫ a₂ = a₁) (sq : IsPullback (yoneda.map m₁) (yoneda.map m₂) a₂ a₃)
    (k₁ : Over.mk ψ₁ ⟶ Over.mk ψ₂) (hk₁ : k₁.left = m₁.left)
    (k₂ : Over.mk ψ₁ ⟶ Over.mk ψ₃) (hk₂ : k₂.left = m₂.left) :
    IsPullback (yoneda.map k₁) (yoneda.map k₂) b₂ b₃ := by
  have hm₂ : yoneda.map m₂ ≫ a₃ = a₁ := sq.w.symm.trans hm₁
  have H : IsPullback ((relocalizePresheafFunctor f).map (yoneda.map k₁))
      ((relocalizePresheafFunctor f).map (yoneda.map k₂))
      ((relocalizePresheafFunctor f).map b₂) ((relocalizePresheafFunctor f).map b₃) := by
    refine sq.of_iso (relocalizeYonedaFactorIso f h₁) (relocalizeYonedaFactorIso f h₂)
      (relocalizeYonedaFactorIso f h₃) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact yoneda_map_comp_relocalizeYonedaFactorIso_hom f m₁ h₂ h₁ k₁ hk₁
    · exact yoneda_map_comp_relocalizeYonedaFactorIso_hom f m₂ h₃ h₁ k₂ hk₂
    · rw [Iso.refl_hom, Category.comp_id]; exact hb₂.symm
    · rw [Iso.refl_hom, Category.comp_id]; exact hb₃.symm
  have : ReflectsLimit (cospan b₂ b₃) (relocalizePresheafFunctor f) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact IsPullback.of_map (relocalizePresheafFunctor f)
    ((hb₁.comm f hb₂ hm₁ k₁ hk₁).trans (hb₁.comm f hb₃ hm₂ k₂ hk₂).symm) H

/-- **A property of a lift.** If `b` lifts `a` and `a` has the represented property `P₂`, then
`b` has every property `P₁` detected by `P₂` after `j = Over.map f`. -/
theorem C1573.IsLift.presheaf {P₁ : MorphismProperty (Over V)} {P₂ : MorphismProperty (Over U)}
    [P₂.RespectsIso] (hP : ∀ {a b : Over V} (k : a ⟶ b), P₂ ((Over.map f).map k) → P₁ k)
    {W : Over U} {a : yoneda.obj W ⟶ (relocalizePresheafFunctor f).obj G}
    {ψ : W.left ⟶ V} {h : ψ ≫ f = W.hom} {b : yoneda.obj (Over.mk ψ) ⟶ G}
    (hb : IsLift f a h b) (hrep : yoneda.relativelyRepresentable b)
    (ha : MorphismProperty.presheaf P₂ a) : MorphismProperty.presheaf P₁ b := by
  refine presheaf_of_presheaf_map_relocalize f hP hrep ?_
  have sq : IsPullback (relocalizeYonedaFactorIso f h).inv
      ((relocalizePresheafFunctor f).map b) a (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.comp_id, ← show _ = a from hb, Iso.inv_hom_id_assoc]⟩
  exact (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq ha

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

open CategoryTheory.OverShriek

open _root_.AlgebraicGeometry.C1573 _root_.AlgebraicGeometry.Space.C1573
  _root_.CategoryTheory.Limits.C1573 _root_.CategoryTheory.OverShriek.C1573
variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The projection `ℙᵏ_S ⟶ ℙᵏ_ℤ`, as a morphism of the site over `Spec ℤ`. -/
def C1573.projectiveSpaceSiteObjectToIntegers (k : ℕ) :
    (Over.map (integersMap B S hS hZ)).obj (projectiveSpaceSiteObject B S hS k) ⟶
      projectiveSpaceSiteObject B (⊤_ Scheme.{u}) hZ k :=
  Over.homMk (ObjectProperty.homMk (pullback.map (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse.{u} k)) (terminal.from (⊤_ Scheme.{u}))
    (terminal.from (projectiveSpaceAtUniverse.{u} k)) (terminal.from S) (𝟙 _) (𝟙 _)
    (terminal.hom_ext _ _) (terminal.hom_ext _ _)))
    (B.inclusion.map_injective (terminal.hom_ext _ _))

/-- The base change square of projective space along `S ⟶ Spec ℤ`, in the site over `Spec ℤ`. -/
theorem C1573.isPullback_projectiveSpaceSiteObjectToIntegers (k : ℕ) :
    IsPullback ((Over.map (integersMap B S hS hZ)).map
        (Over.homMk (projectiveSpaceSiteObject B S hS k).hom :
          projectiveSpaceSiteObject B S hS k ⟶ Over.mk (𝟙 (B.obj hS))))
      (projectiveSpaceSiteObjectToIntegers hZ k)
      (Over.homMk (integersMap B S hS hZ) (by simp) :
        (Over.map (integersMap B S hS hZ)).obj (Over.mk (𝟙 (B.obj hS))) ⟶
          Over.mk (𝟙 (B.obj hZ)))
      (Over.homMk (projectiveSpaceSiteObject B (⊤_ Scheme.{u}) hZ k).hom :
        projectiveSpaceSiteObject B (⊤_ Scheme.{u}) hZ k ⟶ Over.mk (𝟙 (B.obj hZ))) := by
  have _ : ReflectsLimit (cospan (Over.homMk (integersMap B S hS hZ) (by simp) :
        (Over.map (integersMap B S hS hZ)).obj (Over.mk (𝟙 (B.obj hS))) ⟶
          Over.mk (𝟙 (B.obj hZ)))
      (Over.homMk (projectiveSpaceSiteObject B (⊤_ Scheme.{u}) hZ k).hom :
        projectiveSpaceSiteObject B (⊤_ Scheme.{u}) hZ k ⟶ Over.mk (𝟙 (B.obj hZ))))
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)
    (isPullback_pullbackMap_terminal (P := projectiveSpaceAtUniverse.{u} k)
      (terminal.from S)).flip

/-- The comparison `Λ h_{ℙᵏ_S} ⟶ h_{ℙᵏ_ℤ}` of the relocalized projective space over `S` with
projective space over `Spec ℤ`. -/
def C1573.relocalizeProjectiveSpaceToIntegers (k : ℕ) :
    (relocalizePresheafFunctor (integersMap B S hS hZ)).obj
        (yoneda.obj (projectiveSpaceSiteObject B S hS k)) ⟶
      yoneda.obj (projectiveSpaceSiteObject B (⊤_ Scheme.{u}) hZ k) :=
  (relocalizeYonedaIso (integersMap B S hS hZ)).hom.app _ ≫
    yoneda.map (projectiveSpaceSiteObjectToIntegers hZ k)

/-- **Relocalized projective space over `Y` is projective space over the relocalization of
`Y`.** Viewed over `Spec ℤ`, `ℙᵏ_Y = Y ×_S ℙᵏ_S` is the product of `Λ Y` with `ℙᵏ_ℤ`. -/
theorem C1573.isPullback_relocalize_projectiveSpacePresheaf (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (k : ℕ) :
    IsPullback ((relocalizePresheafFunctor (integersMap B S hS hZ)).map
        (pullback.fst _ _ : projectiveSpacePresheaf B S hS Y k ⟶ Y))
      ((relocalizePresheafFunctor (integersMap B S hS hZ)).map
        (pullback.snd _ _ : projectiveSpacePresheaf B S hS Y k ⟶ _) ≫
          relocalizeProjectiveSpaceToIntegers hZ k)
      ((isTerminal_yoneda_obj_base B (⊤_ Scheme.{u}) hZ).from
        ((relocalizePresheafFunctor (integersMap B S hS hZ)).obj Y))
      ((isTerminal_yoneda_obj_base B (⊤_ Scheme.{u}) hZ).from
        (yoneda.obj (projectiveSpaceSiteObject B (⊤_ Scheme.{u}) hZ k))) := by
  set tS := isTerminal_yoneda_obj_base B S hS
  set g := integersMap B S hS hZ
  have h1 := isPullback_map_relocalize g
    (IsPullback.of_hasPullback (tS.from Y)
      (tS.from (yoneda.obj (projectiveSpaceSiteObject B S hS k))))
  have e2 : tS.from (yoneda.obj (projectiveSpaceSiteObject B S hS k)) =
      yoneda.map (Over.homMk (projectiveSpaceSiteObject B S hS k).hom :
        projectiveSpaceSiteObject B S hS k ⟶ Over.mk (𝟙 (B.obj hS))) := tS.hom_ext _ _
  have e3 : (relocalizePresheafFunctor g).map
        (tS.from (yoneda.obj (projectiveSpaceSiteObject B S hS k))) ≫
        (relocalizeYonedaIso g).hom.app (Over.mk (𝟙 (B.obj hS))) =
      (relocalizeYonedaIso g).hom.app _ ≫ yoneda.map ((Over.map g).map
        (Over.homMk (projectiveSpaceSiteObject B S hS k).hom :
          projectiveSpaceSiteObject B S hS k ⟶ Over.mk (𝟙 (B.obj hS)))) := by
    rw [e2]
    exact (relocalizeYonedaIso g).hom.naturality _
  have h1' := h1.of_iso (Iso.refl _) (Iso.refl _) ((relocalizeYonedaIso g).app _) (Iso.refl _)
    (by simp) (fst' := (relocalizePresheafFunctor g).map (pullback.fst _ _))
    (snd' := (relocalizePresheafFunctor g).map (pullback.snd _ _) ≫
      (relocalizeYonedaIso g).hom.app _) (by simp)
    (f' := (relocalizePresheafFunctor g).map (tS.from Y) ≫
      (relocalizeYonedaIso g).hom.app (Over.mk (𝟙 (B.obj hS)))) (by simp)
    (by rw [Iso.refl_hom, Category.comp_id, Iso.app_hom]; exact e3)
  have h2 := (isPullback_projectiveSpaceSiteObjectToIntegers hZ k (S := S) (hS := hS)).map yoneda
  have h3 := (h1'.flip.paste_horiz h2.flip).flip
  convert h3 using 1
  · simp only [relocalizeProjectiveSpaceToIntegers, Category.assoc]
    rfl
  · exact (isTerminal_yoneda_obj_base B (⊤_ Scheme.{u}) hZ).hom_ext _ _
  · exact (isTerminal_yoneda_obj_base B (⊤_ Scheme.{u}) hZ).hom_ext _ _

/-- **Density of a lift.** If `b` lifts `a : h_W ⟶ Λ X` and `a` has dense image on points, so
has `b`: reading points over `Spec ℤ` is a homeomorphism, natural in the presheaf. -/
theorem C1573.denseRange_pointsMap_of_isLift {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    {a : yoneda.obj W ⟶ (relocalizePresheafFunctor (integersMap B S hS hZ)).obj X}
    {ψ : W.left ⟶ B.obj hS} {h : ψ ≫ integersMap B S hS hZ = W.hom}
    {b : yoneda.obj (Over.mk ψ) ⟶ X} (hb : OverShriek.C1573.IsLift (integersMap B S hS hZ) a h b)
    (ha : @DenseRange _ (pointTopology B (⊤_ Scheme.{u}) hZ
        ((relocalizePresheafFunctor (integersMap B S hS hZ)).obj X)) _
      (pointsMap B (⊤_ Scheme.{u}) hZ _ a)) :
    letI := pointTopology B S hS X
    DenseRange (pointsMap B S hS _ b) := by
  let := pointTopology B (⊤_ Scheme.{u}) hZ
    ((relocalizePresheafFunctor (integersMap B S hS hZ)).obj X)
  let := pointTopology B S hS X
  set R := pointsRelocalize B S (⊤_ Scheme.{u}) hS hZ (integersMap B S hS hZ) X
  let H : points B S hS X ≃ₜ points B (⊤_ Scheme.{u}) hZ
      ((relocalizePresheafFunctor (integersMap B S hS hZ)).obj X) :=
    (Equiv.ofBijective R
      (pointsRelocalize_bijective B S (⊤_ Scheme.{u}) hS hZ _ X)).toHomeomorphOfContinuousClosed
      (continuous_pointsRelocalize B S (⊤_ Scheme.{u}) hS hZ _ X)
      (isClosedMap_pointsRelocalize B S (⊤_ Scheme.{u}) hS hZ _ X)
  have hrange : Set.range (pointsMap B (⊤_ Scheme.{u}) hZ _ a) =
      H '' Set.range (pointsMap B S hS _ b) := by
    have e1 : Set.range (pointsMap B (⊤_ Scheme.{u}) hZ _ a) =
        Set.range (pointsMap B (⊤_ Scheme.{u}) hZ _
          ((relocalizePresheafFunctor (integersMap B S hS hZ)).map b)) := by
      rw [← show _ = a from hb, pointsMap_comp]
      exact (pointsMap_surjective_of_isIso B (⊤_ Scheme.{u}) hZ _).range_comp _
    have e2 : Set.range (pointsMap B (⊤_ Scheme.{u}) hZ _
          ((relocalizePresheafFunctor (integersMap B S hS hZ)).map b)) =
        R '' Set.range (pointsMap B S hS _ b) := by
      rw [← (pointsRelocalize_surjective B S (⊤_ Scheme.{u}) hS hZ (integersMap B S hS hZ)
        (yoneda.obj (Over.mk ψ))).range_comp, ← Set.range_comp]
      congr 1
      funext x
      exact (pointsRelocalize_naturality B S (⊤_ Scheme.{u}) hS hZ _ b x).symm
    exact e1.trans e2
  have hd : Dense (H '' Set.range (pointsMap B S hS _ b)) := hrange ▸ ha
  have := hd.preimage H.isOpenMap
  rwa [H.preimage_image] at this

/-- **The relation of a lifted atlas is the relation of the atlas.** If `b` lifts a surjective
chart `a` of `Λ X` whose relation `h_V ×_{Λ X} h_V` is affine, then the relation of `b` is
affine: `Λ` carries the fibre square of `b` to a fibre square of `a`. -/
theorem C1573.isAffine_atlasRelation_of_isLift {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {V : BigFppfOver B (⊤_ Scheme.{u}) hZ}
    {a : yoneda.obj V ⟶ (relocalizePresheafFunctor (integersMap B S hS hZ)).obj X}
    (hsa : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))) a)
    [IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      (atlasRelation B (⊤_ Scheme.{u}) hZ hsa))]
    {ψ : V.left ⟶ B.obj hS} {h : ψ ≫ integersMap B S hS hZ = V.hom}
    {b : yoneda.obj (Over.mk ψ) ⟶ X} (hb : OverShriek.C1573.IsLift (integersMap B S hS hZ) a h b)
    (hsb : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) b) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hsb)) := by
  have sqS := (hsb.rep.isPullback b).map (relocalizePresheafFunctor (integersMap B S hS hZ))
  have hb' : (relocalizePresheafFunctor (integersMap B S hS hZ)).map b =
      (relocalizeYonedaFactorIso (integersMap B S hS hZ) h).inv ≫ a := by
    rw [← show _ = a from hb, Iso.inv_hom_id_assoc]
  have sq' : IsPullback
      (((relocalizeYonedaIso (integersMap B S hS hZ)).app (atlasRelation B S hS hsb)).inv ≫
        (relocalizePresheafFunctor (integersMap B S hS hZ)).map (hsb.rep.fst b) ≫
          (relocalizeYonedaFactorIso (integersMap B S hS hZ) h).inv)
      (((relocalizeYonedaIso (integersMap B S hS hZ)).app (atlasRelation B S hS hsb)).inv ≫
        (relocalizePresheafFunctor (integersMap B S hS hZ)).map (yoneda.map (hsb.rep.snd b)) ≫
          (relocalizeYonedaFactorIso (integersMap B S hS hZ) h).inv) a a :=
    sqS.of_iso ((relocalizeYonedaIso (integersMap B S hS hZ)).app (atlasRelation B S hS hsb))
      (relocalizeYonedaFactorIso (integersMap B S hS hZ) h).symm
      (relocalizeYonedaFactorIso (integersMap B S hS hZ) h).symm (Iso.refl _)
      (by simp) (by simp) (by rw [hb']; simp) (by rw [hb']; simp)
  have E := IsPullback.isoIsPullback _ _ sq' (hsa.rep.isPullback a)
  have E' := Yoneda.fullyFaithful.preimageIso E
  exact IsAffine.of_isIso ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).mapIso E').hom

variable (B S hS) in
/-- The view over `Spec ℤ` of an algebraic space over `S`, as an algebraic space. -/
abbrev C1573.viewOverIntegersSpace (X : AlgebraicSpaces B S hS) :
    AlgebraicSpaces B (⊤_ Scheme.{u}) hZ :=
  ⟨viewOverIntegers B S hS hZ X.1,
    isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ (integersMap B S hS hZ) X.1 X.2⟩

/-- **Transport of a Chow datum from `Spec ℤ` to `S`.** A Chow datum for the view over `Spec ℤ`
of a morphism `f : X ⟶ Y` of algebraic spaces over `S` gives one for `f`: the schemes of the
datum, with their factorizations through `S`, and the closed subscheme of projective space base
changed to `S`. -/
theorem C1573.ChowDatum.ofViewOverIntegers {X : AlgebraicSpaces B S hS}
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y) (f : X.1 ⟶ Y)
    (d : ChowDatum (viewOverIntegersSpace B S hS hZ X)
      ((relocalizePresheafFunctor (integersMap B S hS hZ)).map f)) :
    Nonempty (ChowDatum X f) := by
  have rep : ∀ {W : BigFppfOver B S hS} (b : yoneda.obj W ⟶ X.1),
      yoneda.relativelyRepresentable b :=
    fun b => relativelyRepresentable_of_isAlgebraicSpace B S hS X.2 b
  have lift : ∀ {W : BigFppfOver B (⊤_ Scheme.{u}) hZ}
      (a : yoneda.obj W ⟶ (relocalizePresheafFunctor (integersMap B S hS hZ)).obj X.1),
      ∃ (ψ : W.left ⟶ B.obj hS) (h : ψ ≫ integersMap B S hS hZ = W.hom)
        (b : yoneda.obj (Over.mk ψ) ⟶ X.1), OverShriek.C1573.IsLift (integersMap B S hS hZ) a h b :=
    fun a => ⟨_, _, _, isLift_liftMap _ a⟩
  obtain ⟨ψD, hD, uS, huS⟩ := lift d.u
  obtain ⟨ψV, hV, φS, hφS⟩ := lift d.φ
  obtain ⟨ψT, hT, τS, hτS⟩ := lift d.τ
  obtain ⟨ψTV, hTV, bTV, hbTV⟩ := lift (yoneda.map d.pT ≫ d.τ)
  let := MorphismProperty.RespectsIso.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)
  have hsS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φS :=
    hφS.presheaf _ (fun _ hk => hk) (rep φS) d.hs
  have heS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φS :=
    hφS.presheaf _ (fun _ hk => hk) (rep φS) d.he
  have huS' : IsOpenImmersion B S hS uS := huS.presheaf _ (fun _ hk => hk) (rep uS) d.hu
  have hdS : let := pointTopology B S hS X.1
      DenseRange (pointsMap B S hS (yoneda.obj (Over.mk ψD)) uS) :=
    denseRange_pointsMap_of_isLift hZ huS d.hdense
  have := d.affR
  have haffR : IsAffine ((BigFppfOver.toScheme B S hS).obj (atlasRelation B S hS hsS)) :=
    isAffine_atlasRelation_of_isLift hZ d.hs hφS hsS
  have hσw : yoneda.map d.σ ≫ d.τ = d.u := d.hσ.w.trans (Category.id_comp _)
  let σS : Over.mk ψD ⟶ Over.mk ψT := Over.homMk d.σ.left (huS.left_comp _ hτS hσw)
  have hσS : IsPullback (yoneda.map σS) (𝟙 _) τS uS := by
    have sq0 : IsPullback (yoneda.map d.σ) (yoneda.map (𝟙 d.D)) d.τ d.u := by
      rw [CategoryTheory.Functor.map_id]; exact d.hσ
    simpa using huS.isPullback _ hτS huS hσw sq0 σS rfl (𝟙 _) rfl
  let pTS : Over.mk ψTV ⟶ Over.mk ψT := Over.homMk d.pT.left (hbTV.left_comp _ hτS rfl)
  let tVS : Over.mk ψTV ⟶ Over.mk ψV :=
    Over.homMk d.tV.left (hbTV.left_comp _ hφS d.hsq.w.symm)
  have hsqS : IsPullback (yoneda.map pTS) (yoneda.map tVS) τS φS :=
    hbTV.isPullback _ hτS hφS rfl d.hsq pTS rfl tVS rfl
  have := d.hiC
  have := d.hcC
  have hcZ : B.Contains
      (pullback (B.inclusion.map (integersMap B S hS hZ)) (B.inclusion.map d.Z₂.hom)) :=
    Scheme.size_pullback_lt (B.inclusion.map (integersMap B S hS hZ)) (B.inclusion.map d.Z₂.hom)
      hS d.Z₂.left.property
  let Z₂S : BigFppfOver B S hS := siteObject B S hS hcZ
    (pullback.fst (B.inclusion.map (integersMap B S hS hZ)) (B.inclusion.map d.Z₂.hom))
  have hoc : B.inclusion.map ψT ≫ (B.inclusion.map (integersMap B S hS hZ)) =
      B.inclusion.map d.o.left ≫ (B.inclusion.map d.Z₂.hom) := by
    rw [← Functor.map_comp, ← Functor.map_comp, hT, Over.w d.o]
  let oS : Over.mk ψT ⟶ Z₂S :=
    Over.homMk (ObjectProperty.homMk (pullback.lift (B.inclusion.map ψT)
      (B.inclusion.map d.o.left) hoc)) (B.inclusion.map_injective (pullback.lift_fst _ _ _))
  let iS : (BigFppfOver.toScheme B S hS).obj Z₂S ⟶ projectiveSpaceOver d.m S :=
    pullback.lift
      (pullback.fst (B.inclusion.map (integersMap B S hS hZ)) (B.inclusion.map d.Z₂.hom))
      (pullback.snd (B.inclusion.map (integersMap B S hS hZ)) (B.inclusion.map d.Z₂.hom) ≫ d.i ≫
        pullback.snd _ _)
      (terminal.hom_ext _ _)
  have hiS : _root_.AlgebraicGeometry.IsClosedImmersion iS :=
    isClosedImmersion_lift_comp_snd (B.inclusion.map (integersMap B S hS hZ))
      (B.inclusion.map d.Z₂.hom) d.i d.hi
  have hiS' : iS ≫ pullback.fst _ _ = B.inclusion.map Z₂S.hom := pullback.lift_fst _ _ _
  have hVg : B.inclusion.map ψV ≫ (B.inclusion.map (integersMap B S hS hZ)) =
      B.inclusion.map d.V.hom := by
    rw [← Functor.map_comp, hV]
  let cSS : (BigFppfOver.toScheme B S hS).obj (Over.mk ψTV) ⟶
      pullback (B.inclusion.map ψV)
        (pullback.fst (B.inclusion.map (integersMap B S hS hZ)) (B.inclusion.map d.Z₂.hom)) :=
    d.cS ≫ (pullback.congrHom hVg rfl).inv ≫
      (pullbackRightPullbackFstIso (B.inclusion.map (integersMap B S hS hZ))
        (B.inclusion.map d.Z₂.hom) (B.inclusion.map ψV)).inv
  have hcS : _root_.AlgebraicGeometry.IsClosedImmersion cSS := by
    dsimp only [cSS]; infer_instance
  have hc1S : cSS ≫ pullback.fst (B.inclusion.map ψV)
      (pullback.fst (B.inclusion.map (integersMap B S hS hZ)) (B.inclusion.map d.Z₂.hom)) =
      (BigFppfOver.toScheme B S hS).map tVS := by
    simp only [cSS, Category.assoc, pullbackRightPullbackFstIso_inv_fst, pullback.congrHom_inv,
      pullback.map, pullback.lift_fst, Category.comp_id]
    exact d.hc1
  have htp : (BigFppfOver.toScheme B S hS).map tVS ≫ B.inclusion.map ψV =
      (BigFppfOver.toScheme B S hS).map pTS ≫ B.inclusion.map ψT := by
    show B.inclusion.map d.tV.left ≫ B.inclusion.map ψV =
      B.inclusion.map d.pT.left ≫ B.inclusion.map ψT
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg _ ((Over.w tVS).trans (Over.w pTS).symm)
  have hc2S : cSS ≫ pullback.snd (B.inclusion.map ψV)
      (pullback.fst (B.inclusion.map (integersMap B S hS hZ)) (B.inclusion.map d.Z₂.hom)) =
      (BigFppfOver.toScheme B S hS).map (pTS ≫ oS) := by
    apply pullback.hom_ext
    · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hc1S, htp, Functor.map_comp,
        Category.assoc]
      exact congrArg _ (pullback.lift_fst _ _ _).symm
    · simp only [cSS, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd,
        pullback.congrHom_inv, pullback.map, pullback.lift_snd, Category.comp_id]
      rw [d.hc2, Functor.map_comp, Functor.map_comp, Category.assoc]
      exact congrArg _ (pullback.lift_snd _ _ _).symm
  have hPY := isPullback_relocalize_projectiveSpacePresheaf hZ Y d.k
  set e := hPY.isoPullback with he
  have hj : liftPsi (integersMap B S hS hZ) (d.jT ≫ e.inv) = ψT := by
    rw [← liftPsi_comp_map _ (d.jT ≫ e.inv) (pullback.fst _ _), Category.assoc,
      IsPullback.isoPullback_inv_fst, d.hjTf, liftPsi_comp_map]
    exact hτS.liftPsi_eq _
  obtain ⟨jS, hjS⟩ := exists_isLift _ (d.jT ≫ e.inv) ψT hj hT
  have hPS : IsAlgebraicSpace B S hS (projectiveSpacePresheaf B S hS Y d.k) :=
    isAlgebraicSpace_pullback B S hS _ _ hY (isAlgebraicSpace_yoneda B S hS _)
      (isAlgebraicSpace_yoneda B S hS _)
  have hjT' : IsImmersion B (⊤_ Scheme.{u}) hZ (d.jT ≫ e.inv) :=
    isImmersion_of_isPullback' (IsPullback.of_horiz_isIso (fst := 𝟙 _) (g := e.hom)
      ⟨by simp⟩) d.hjT
  let : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  let := MorphismProperty.RespectsIso.inverseImage
    (@_root_.AlgebraicGeometry.IsImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)
  have hjTS : IsImmersion B S hS jS :=
    hjS.presheaf _ (fun _ hk => hk) (relativelyRepresentable_of_isAlgebraicSpace B S hS hPS jS)
      hjT'
  have hjTfS : jS ≫ pullback.fst _ _ = τS ≫ f := by
    refine (hjS.comp_map _ (pullback.fst _ _)).unique _ ?_
    rw [Category.assoc, IsPullback.isoPullback_inv_fst, d.hjTf]
    exact hτS.comp_map _ f
  exact ⟨{
    D := Over.mk ψD
    V := Over.mk ψV
    T₀ := Over.mk ψT
    TV := Over.mk ψTV
    Z₂ := Z₂S
    u := uS
    hu := huS'
    hdense := hdS
    φ := φS
    hs := hsS
    he := heS
    affV := d.affV
    affR := haffR
    noethV := d.noethV
    noethT₀ := d.noethT₀
    noethTV := d.noethTV
    noethD := d.noethD
    compactT₀ := d.compactT₀
    τ := τS
    σ := σS
    hσ := hσS
    pT := pTS
    tV := tVS
    hsq := hsqS
    o := oS
    m := d.m
    i := iS
    hiC := hiS
    hi := hiS'
    cS := cSS
    hcC := hcS
    hc1 := hc1S
    hc2 := hc2S
    M := d.M
    hMi := d.hMi
    hM := d.hM
    k := d.k
    jT := jS
    hjT := hjTS
    hjTf := hjTfS }⟩

end AlgebraicGeometry.Space

end
