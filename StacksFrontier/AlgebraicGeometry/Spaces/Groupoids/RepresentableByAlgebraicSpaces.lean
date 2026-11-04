module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic

/-!
# Morphisms representable by algebraic spaces

A morphism of presheaves on the big fppf site over a scheme is *representable by algebraic
spaces* when every base change of it along a scheme-valued point of its target is an
algebraic space.  Such a morphism transports the sheaf condition from its target to its
source, and the property is stable under base change.

## Main definitions

* `AlgebraicGeometry.Space.IsRepresentableByAlgebraicSpaces` is the property of a morphism
  of presheaves that each of its base changes along a scheme-valued point is an algebraic
  space.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_iso` transports the algebraic-space
  condition along an isomorphism of presheaves.
* `AlgebraicGeometry.Space.isSheaf_of_isRepresentableByAlgebraicSpaces`: the source of a
  transformation representable by algebraic spaces is a sheaf as soon as its target is.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpaces_of_isPullback`:
  representability by algebraic spaces is stable under base change.

## Implementation notes

A scheme-valued point of the target is a morphism out of its Yoneda presheaf, and the fibre
product with the source is the categorical pullback of presheaves; the defining property is
an abbreviation, so its universal quantifier applies without an unfolding lemma.

Base change is expressed by `CategoryTheory.IsPullback` rather than by the chosen pullback
object, so the upper-left corner of the cartesian square is arbitrary.  That makes
`AlgebraicGeometry.Space.isAlgebraicSpace_of_iso` necessary, and it is proved by
transporting each of the three fields of `AlgebraicGeometry.IsAlgebraicSpace` along the
isomorphism: the sheaf condition by `CategoryTheory.Presheaf.isSheaf_of_iso_iff`, and the
representable diagonal and the surjective étale atlas because both morphism properties
involved respect isomorphisms.

The sheaf property of the source is proved by amalgamating, over a covering, the sections of
the pullback of the target's Yoneda point along the transformation; that pullback is a sheaf
because it is an algebraic space.  Sections of a pullback of presheaves are handled through
`CategoryTheory.Limits.pullbackObjIso`, which identifies the value of the pullback presheaf
with the pullback of the values.

## References

* [Stacks Project, Tag 02YQ](https://stacks.math.columbia.edu/tag/02YQ)
* [Stacks Project, Tag 02YR](https://stacks.math.columbia.edu/tag/02YR)
* [Stacks Project, Tag 03Y0](https://stacks.math.columbia.edu/tag/03Y0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

/-- The algebraic-space condition on a presheaf over the big fppf site transports along an
isomorphism of presheaves. -/
lemma isAlgebraicSpace_of_iso (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    (hF : IsAlgebraicSpace B S hS F) : IsAlgebraicSpace B S hS G := by
  refine ⟨(Presheaf.isSheaf_of_iso_iff e).mp hF.isSheaf, ?_, ?_⟩
  · have hnat : diag F ≫ prod.map e.hom e.hom = e.hom ≫ diag G := by
      apply prod.hom_ext <;> simp
    rw [← MorphismProperty.cancel_left_of_respectsIso
      (P := yoneda.relativelyRepresentable) e.hom (diag G), ← hnat]
    exact MorphismProperty.RespectsIso.postcomp _ (prod.map e.hom e.hom) (diag F)
      hF.diagonal_representable
  · obtain ⟨U, f, hfSurjective, hfEtale⟩ := hF.exists_atlas
    exact ⟨U, f ≫ e.hom, MorphismProperty.RespectsIso.postcomp _ e.hom f hfSurjective,
      MorphismProperty.RespectsIso.postcomp _ e.hom f hfEtale⟩

/-- **Stacks Project, Tag 02YQ.** A morphism of presheaves is representable by algebraic
spaces if its pullback to every scheme over the base is an algebraic space. -/
@[stacks 02YQ, stacks 0AQ3 "the defining condition of an adic morphism"]
abbrev IsRepresentableByAlgebraicSpaces (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G) : Prop :=
  ∀ (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ G),
    IsAlgebraicSpace B S hS (pullback ξ a)

/-- The section of a pullback of presheaves of types determined by a compatible pair of
sections of the two factors. -/
noncomputable def pbSection {C : Type v} [Category.{w} C] {F G H : Cᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X)
    (h : f.app X x = g.app X y) : (pullback f g).obj X :=
  (pullbackObjIso f g X).inv
    (ConcreteCategory.hom (pullback.lift (↾fun _ : PUnit => x) (↾fun _ : PUnit => y)
      (by ext z; exact h)) PUnit.unit)

/-- The first projection of `pbSection` is the first of the two given sections. -/
private lemma pbSection_fst {C : Type v} [Category.{w} C] {F G H : Cᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X)
    (h : f.app X x = g.app X y) :
    (pullback.fst f g).app X (pbSection f g X x y h) = x := by
  show ConcreteCategory.hom ((pullbackObjIso f g X).inv ≫ (pullback.fst f g).app X)
    (ConcreteCategory.hom (pullback.lift (↾fun _ : PUnit => x) (↾fun _ : PUnit => y)
      (by ext z; exact h)) PUnit.unit) = x
  rw [pullbackObjIso_inv_comp_fst]
  exact ConcreteCategory.congr_hom (pullback.lift_fst
    (↾fun _ : PUnit => x) (↾fun _ : PUnit => y) (by ext z; exact h)) PUnit.unit

/-- The second projection of `pbSection` is the second of the two given sections. -/
lemma pbSection_snd {C : Type v} [Category.{w} C] {F G H : Cᵒᵖ ⥤ Type u}
    (f : F ⟶ H) (g : G ⟶ H) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X)
    (h : f.app X x = g.app X y) :
    (pullback.snd f g).app X (pbSection f g X x y h) = y := by
  show ConcreteCategory.hom ((pullbackObjIso f g X).inv ≫ (pullback.snd f g).app X)
    (ConcreteCategory.hom (pullback.lift (↾fun _ : PUnit => x) (↾fun _ : PUnit => y)
      (by ext z; exact h)) PUnit.unit) = y
  rw [pullbackObjIso_inv_comp_snd]
  exact ConcreteCategory.congr_hom (pullback.lift_snd
    (↾fun _ : PUnit => x) (↾fun _ : PUnit => y) (by ext z; exact h)) PUnit.unit

/-- Restricting `pbSection` along a morphism of the index category restricts the two given
sections. -/
private lemma pbSection_map {C : Type v} [Category.{w} C]
    {F G H : Cᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    {X Y : Cᵒᵖ} (q : X ⟶ Y) (x : F.obj X) (y : G.obj X)
    (h : f.app X x = g.app X y) :
    (pullback f g).map q (pbSection f g X x y h) =
      pbSection f g Y (F.map q x) (G.map q y) (by
        calc
          f.app Y (F.map q x) = H.map q (f.app X x) := f.naturality_apply q x
          _ = H.map q (g.app X y) := congrArg (H.map q) h
          _ = g.app Y (G.map q y) := (g.naturality_apply q y).symm) := by
  apply (Iso.toEquiv (pullbackObjIso f g Y)).injective
  apply Types.ext_of_isPullback (IsPullback.of_hasPullback (f.app Y) (g.app Y))
  · simp only [Iso.toEquiv_fun, ← types_comp_apply]
    rw [Category.assoc, pullbackObjIso_hom_comp_fst]
    simp only [types_comp_apply, (pullback.fst f g).naturality_apply, pbSection_fst]
  · simp only [Iso.toEquiv_fun, ← types_comp_apply]
    rw [Category.assoc, pullbackObjIso_hom_comp_snd]
    simp only [types_comp_apply, (pullback.snd f g).naturality_apply, pbSection_snd]

/-- `pbSection` depends only on the two given sections, not on the compatibility proof. -/
private lemma pbSection_ext {C : Type v} [Category.{w} C]
    {F G H : Cᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H)
    (X : Cᵒᵖ) (x₁ x₂ : F.obj X) (y₁ y₂ : G.obj X)
    (h₁ : x₁ = x₂) (h₂ : y₁ = y₂)
    (e₁ : f.app X x₁ = g.app X y₁) (e₂ : f.app X x₂ = g.app X y₂) :
    pbSection f g X x₁ y₁ e₁ = pbSection f g X x₂ y₂ e₂ := by
  subst h₁ h₂
  rfl

/-- **Stacks Project, Tag 02YR.** A transformation representable by algebraic spaces has a
sheaf as its source if its target is a sheaf. -/
@[stacks 02YR]
theorem isSheaf_of_isRepresentableByAlgebraicSpaces
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) F := by
  rw [isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) F]
  have hG0 : Presieve.IsSheaf (BigFppfOver.topology B S hS) G :=
    (isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) G).mp hG
  intro X R hR x hx
  let xG : Presieve.FamilyOfElements G R.arrows := x.map a
  have hxG : xG.Compatible := hx.map a
  have hGR : Presieve.IsSheafFor G R.arrows := hG0 R hR
  let σ : G.obj (op X) := hGR.amalgamate xG hxG
  have hσ : xG.IsAmalgamation σ := hGR.isAmalgamation hxG
  let ξ : yoneda.obj X ⟶ G := yonedaEquiv.symm σ
  let P := pullback ξ a
  have hP : Presieve.IsSheaf (BigFppfOver.topology B S hS) P :=
    (isSheaf_iff_isSheaf_of_type (BigFppfOver.topology B S hS) P).mp (ha X ξ).isSheaf
  have hfiber : ∀ {Y : BigFppfOver B S hS} (f : Y ⟶ X) (hf : R.arrows f),
      ξ.app (op Y) f = a.app (op Y) (x f hf) := fun {Y} f hf => by
    show (G.map f.op) σ = a.app (op Y) (x f hf)
    simpa [xG, Presieve.FamilyOfElements.map] using hσ f hf
  let z : Presieve.FamilyOfElements P R.arrows := fun {Y} f hf =>
    pbSection ξ a (op Y) f (x f hf) (hfiber f hf)
  have hz : z.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomp
    show (pullback ξ a).map g₁.op
        (pbSection ξ a (op Y₁) f₁ (x f₁ hf₁) (hfiber f₁ hf₁)) =
      (pullback ξ a).map g₂.op
        (pbSection ξ a (op Y₂) f₂ (x f₂ hf₂) (hfiber f₂ hf₂))
    rw [pbSection_map ξ a g₁.op f₁ (x f₁ hf₁) (hfiber f₁ hf₁),
      pbSection_map ξ a g₂.op f₂ (x f₂ hf₂) (hfiber f₂ hf₂)]
    apply pbSection_ext
    · show (yoneda.obj X).map g₁.op f₁ = (yoneda.obj X).map g₂.op f₂
      simpa using hcomp
    · exact hx g₁ g₂ hf₁ hf₂ hcomp
  have hPR : Presieve.IsSheafFor P R.arrows := hP.isSheafFor R.arrows (by simpa using hR)
  let t : P.obj (op X) := hPR.amalgamate z hz
  have ht : z.IsAmalgamation t := hPR.isAmalgamation hz
  let s : F.obj (op X) := (pullback.snd ξ a).app (op X) t
  have hs : x.IsAmalgamation s := by
    intro Y f hf
    have h := congrArg ((pullback.snd ξ a).app (op Y)) (ht f hf)
    rw [(pullback.snd ξ a).naturality_apply f.op t] at h
    simpa [z, s, pbSection_snd] using h
  refine ⟨s, hs, fun s' hs' => ?_⟩
  have hasection : a.app (op X) s' = σ := hGR.isSeparatedFor.ext fun Y f hf =>
    (a.naturality_apply f.op s').symm.trans
      ((congrArg (a.app (op Y)) (hs' f hf)).trans (hσ f hf).symm)
  have hfiber' : ξ.app (op X) (𝟙 X) = a.app (op X) s' :=
    (by simp [ξ] : ξ.app (op X) (𝟙 X) = σ).trans hasection.symm
  let t' : P.obj (op X) := pbSection ξ a (op X) (𝟙 X) s' hfiber'
  have ht' : z.IsAmalgamation t' := by
    intro Y f hf
    dsimp [t', z]
    rw [pbSection_map ξ a f.op (𝟙 X) s' hfiber']
    exact pbSection_ext ξ a (op Y) _ _ _ _ (by simp) (hs' f hf) _ _
  simpa [t', s, pbSection_snd] using
    congrArg ((pullback.snd ξ a).app (op X)) ((hPR z hz).unique ht' ht)

/-- **Stacks Project, Tag 03Y0.** A cartesian base change of a morphism representable by
algebraic spaces is representable by algebraic spaces. -/
@[stacks 03Y0]
lemma isRepresentableByAlgebraicSpaces_of_isPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G G' H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (p : H ⟶ F) (a' : H ⟶ G') (a : F ⟶ G) (g : G' ⟶ G)
    (h : IsPullback p a' a g)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a) :
    IsRepresentableByAlgebraicSpaces B S hS a' := by
  intro U ξ
  have hpaste : IsPullback (pullback.fst ξ a') (pullback.snd ξ a' ≫ p) (ξ ≫ g) a := by
    simpa using (IsPullback.paste_horiz (IsPullback.of_hasPullback ξ a').flip h).flip
  exact isAlgebraicSpace_of_iso B S hS hpaste.isoPullback.symm (ha U (ξ ≫ g))

end AlgebraicGeometry.Space

end
