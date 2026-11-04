module

public import Mathlib.RingTheory.TensorProduct.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Characterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Diagonal
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.FiniteCoproducts
public import StacksFrontier.CategoryTheory.Sites.Representable.SheafifiedYonedaSubcanonical
public import StacksFrontier.CategoryTheory.Sites.SubcanonicalSheafifiedYoneda
import all StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct

/-!
# Fibre products of affine formal algebraic spaces: the refined forms

An fppf sheaf has *charted* relative products when the fibre product over it of two represented
sheaves receives a relatively representable epimorphism from a represented sheaf. This is weaker
than having representable relative products, and it suffices for the base of a fibre product
satisfying the set-theoretic condition of Stacks 0AIS.

## Main definitions

* `HasChartedRelativeProducts`: The fibre product of two represented sheaves over the sheaf
  receives a relatively representable epimorphism from a represented sheaf.

## Main results

* `hasChartedRelativeProducts_of_hasRepresentableRelativeProducts`: Representable relative
  products are charted relative products.
* `hasRepresentableRelativeProducts_pullback`: A fibre product of fppf sheaves with representable
  relative products has representable relative products.
* `satisfiesSetTheoreticCondition_pullback_of_hasChartedRelativeProducts`: The set-theoretic
  condition holds for a fibre product of sheaves satisfying it with representable relative
  products, over a base with charted relative products.
* `satisfiesSetTheoreticCondition_pullback'`: The same over a base with representable relative
  products.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

section Comparison

variable {C : Type*} [Category C] [HasPullbacks C]

end Comparison

section RelativeProductOfPullback

variable {C : Type*} [Category C] [HasPullbacks C] {D : Type*} [Category D] [HasPullbacks D]
  (F : C ⥤ D) [PreservesLimitsOfShape WalkingCospan F]

/-- **The relative product over a fibre product.** Let `p : X ⟶ Z` and `q : Y ⟶ Z`, let `g` and
`h` be two morphisms into `X ×_Z Y` out of objects in the image of `F`, and suppose the three
relative products `a ×_X b`, `a ×_Y b` and `a ×_Z b` are computed by objects `A`, `B` and `Cc`
of the source category, with comparison morphisms `u : A ⟶ Cc` and `v : B ⟶ Cc` over `a` and
over `b`. Then `a ×_{X ×_Z Y} b` is computed by `A ×_{Cc} B`.

A morphism into `X ×_Z Y` is a pair of morphisms to `X` and to `Y` agreeing over `Z`, so a point
of `a ×_{X ×_Z Y} b` is a point of `a ×_Z b` lifted compatibly to `a ×_X b` and to `a ×_Y b`. -/
private theorem isPullback_map_pullback_of_relativeProducts
    {X Y Z : D} (p : X ⟶ Z) (q : Y ⟶ Z) {a b : C}
    (g : F.obj a ⟶ Limits.pullback p q) (h : F.obj b ⟶ Limits.pullback p q)
    {A Bb Cc : C} {αa : A ⟶ a} {αb : A ⟶ b} {βa : Bb ⟶ a} {βb : Bb ⟶ b}
    {γa : Cc ⟶ a} {γb : Cc ⟶ b}
    (sqA : IsPullback (F.map αa) (F.map αb) (g ≫ pullback.fst p q) (h ≫ pullback.fst p q))
    (sqB : IsPullback (F.map βa) (F.map βb) (g ≫ pullback.snd p q) (h ≫ pullback.snd p q))
    (sqC : IsPullback (F.map γa) (F.map γb) (g ≫ pullback.fst p q ≫ p)
      (h ≫ pullback.fst p q ≫ p))
    {u : A ⟶ Cc} {v : Bb ⟶ Cc}
    (hua : u ≫ γa = αa) (hub : u ≫ γb = αb) (hva : v ≫ γa = βa) (hvb : v ≫ γb = βb) :
    IsPullback (F.map (pullback.fst u v ≫ αa)) (F.map (pullback.fst u v ≫ αb)) g h := by
  have hcond : pullback.fst u v ≫ u = pullback.snd u v ≫ v := pullback.condition
  have heq : ∀ {t : C} {α : A ⟶ t} {β : Bb ⟶ t} {γ : Cc ⟶ t}, u ≫ γ = α → v ≫ γ = β →
      pullback.fst u v ≫ α = pullback.snd u v ≫ β := by
    rintro t _ _ γ rfl rfl
    rw [← Category.assoc, hcond, Category.assoc]
  have heqa := heq hua hva
  have heqb := heq hub hvb
  have sqc : IsPullback (F.map (pullback.fst u v)) (F.map (pullback.snd u v)) (F.map u)
      (F.map v) := (IsPullback.of_hasPullback u v).map F
  have hcomm : F.map (pullback.fst u v ≫ αa) ≫ g = F.map (pullback.fst u v ≫ αb) ≫ h := by
    refine pullback.hom_ext ?_ ?_
    · have hw := sqA.w
      simp only [Functor.map_comp, Category.assoc]
      rw [hw]
    · have hw := sqB.w
      rw [heqa, heqb]
      simp only [Functor.map_comp, Category.assoc]
      rw [hw]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hcomm (fun s => ?_) (fun s => ?_)
    (fun s => ?_) (fun s m hm₁ hm₂ => ?_))
  · refine sqc.lift (sqA.lift s.fst s.snd ?_) (sqB.lift s.fst s.snd ?_) ?_
    · have hs := s.condition
      simp only [← Category.assoc]
      rw [hs]
    · have hs := s.condition
      simp only [← Category.assoc]
      rw [hs]
    · refine sqC.hom_ext ?_ ?_
      · simp only [Category.assoc, ← F.map_comp, hua, hva, sqA.lift_fst, sqB.lift_fst]
      · simp only [Category.assoc, ← F.map_comp, hub, hvb, sqA.lift_snd, sqB.lift_snd]
  · simp only [F.map_comp, ← Category.assoc, sqc.lift_fst]
    exact sqA.lift_fst _ _ _
  · simp only [F.map_comp, ← Category.assoc, sqc.lift_fst]
    exact sqA.lift_snd _ _ _
  · refine sqc.hom_ext ?_ ?_
    · rw [sqc.lift_fst]
      refine sqA.hom_ext ?_ ?_
      · simp only [Category.assoc, ← F.map_comp, sqA.lift_fst]
        exact hm₁
      · simp only [Category.assoc, ← F.map_comp, sqA.lift_snd]
        exact hm₂
    · rw [sqc.lift_snd]
      refine sqB.hom_ext ?_ ?_
      · simp only [Category.assoc, ← F.map_comp, ← heqa, sqB.lift_fst]
        exact hm₁
      · simp only [Category.assoc, ← F.map_comp, ← heqb, sqB.lift_snd]
        exact hm₂

end RelativeProductOfPullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- An fppf sheaf `X` on the big fppf site of `S` *has charted relative products* when the fibre
product over `X` of two sheaves represented by objects of the site receives a relatively
representable epimorphism from a sheaf represented by an object of the site.

This is weaker than `AlgebraicGeometry.FormalSpace.HasRepresentableRelativeProducts`, which asks
the relative product itself to be represented by an object of the site: here the comparison
morphism is only an epimorphism, not an isomorphism. It is nonetheless all that the set-theoretic
condition of **Stacks 0AIS** needs of the base of a fibre product, which is
`satisfiesSetTheoreticCondition_pullback_of_hasChartedRelativeProducts`; and it is the condition
available for a sheaf whose diagonal is representable only by *algebraic spaces*, where such a
relative product is an algebraic space rather than a scheme. An algebraic space is not represented
by an object of the site, but it carries a surjective étale atlas by one, and its representable
diagonal makes that atlas relatively representable. -/
abbrev HasChartedRelativeProducts (X : FppfSheaf B S hS) : Prop :=
  ∀ ⦃a b : BigFppfOver B S hS⦄
    (g : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj a ⟶ X)
    (h : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj b ⟶ X),
    ∃ (c : BigFppfOver B S hS)
      (e : (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).obj c ⟶ pullback g h),
      Epi e ∧ (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).relativelyRepresentable e

/-- **Representable relative products are charted relative products.** The relative product is
then represented by an object of the site, and the comparison isomorphism onto the chosen fibre
product is an epimorphism and is relatively representable. -/
theorem hasChartedRelativeProducts_of_hasRepresentableRelativeProducts
    {X : FppfSheaf B S hS} (hX : HasRepresentableRelativeProducts B S hS X) :
    HasChartedRelativeProducts B S hS X := by
  intro a b g h
  obtain ⟨c, snd, fst, sq⟩ := hX g h
  have hiso : IsPullback fst ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map snd)
      g h := sq
  refine ⟨c, hiso.isoPullback.hom, inferInstance, ?_⟩
  exact Functor.relativelyRepresentable.of_isIso _ _

/-- **A fibre product of fppf sheaves with representable relative products over a base with
representable relative products has representable relative products.**

For two objects `a` and `b` of the site over `X ×_Z Y`, the three relative products `a ×_X b`,
`a ×_Y b` and `a ×_Z b` are represented by objects of the site, the first two map to the third,
and `a ×_{X ×_Z Y} b` is their fibre product over it — an object of the site, since the site has
fibre products. Fullness of the sheafified Yoneda embedding supplies the two comparison
morphisms as morphisms of the site and faithfulness identifies their composites. -/
theorem hasRepresentableRelativeProducts_pullback
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hX : HasRepresentableRelativeProducts B S hS X)
    (hY : HasRepresentableRelativeProducts B S hS Y)
    (hZ : HasRepresentableRelativeProducts B S hS Z) :
    HasRepresentableRelativeProducts B S hS (pullback p q) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  have : HasPullbacks (BigFppfOver B S hS) := inferInstance
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  have hpres : PreservesLimitsOfShape WalkingCospan F :=
    preservesLimitsOfShape_of_natIso (Sheaf.sheafifiedYonedaIsoUliftYoneda' J).symm
  intro a g b h
  have hcond : pullback.fst p q ≫ p = pullback.snd p q ≫ q := pullback.condition
  obtain ⟨A, αb, fstA, sqA0⟩ := hX (g ≫ pullback.fst p q) (h ≫ pullback.fst p q)
  obtain ⟨Bb, βb, fstB, sqB0⟩ := hY (g ≫ pullback.snd p q) (h ≫ pullback.snd p q)
  obtain ⟨Cc, γb, fstC, sqC0⟩ :=
    hZ (g ≫ pullback.fst p q ≫ p) (h ≫ pullback.fst p q ≫ p)
  obtain ⟨αa, hαa⟩ : ∃ αa : A ⟶ a, F.map αa = fstA := ⟨F.preimage fstA, F.map_preimage _⟩
  obtain ⟨βa, hβa⟩ : ∃ βa : Bb ⟶ a, F.map βa = fstB := ⟨F.preimage fstB, F.map_preimage _⟩
  obtain ⟨γa, hγa⟩ : ∃ γa : Cc ⟶ a, F.map γa = fstC := ⟨F.preimage fstC, F.map_preimage _⟩
  rw [← hαa] at sqA0
  rw [← hβa] at sqB0
  rw [← hγa] at sqC0
  have key : ∀ {T : BigFppfOver B S hS} (xa : T ⟶ a) (xb : T ⟶ b),
      F.map xa ≫ g ≫ pullback.fst p q ≫ p = F.map xb ≫ h ≫ pullback.fst p q ≫ p →
      ∃ w : T ⟶ Cc, w ≫ γa = xa ∧ w ≫ γb = xb := fun xa xb hw =>
    ⟨F.preimage (sqC0.lift (F.map xa) (F.map xb) hw),
      F.map_injective (by rw [F.map_comp, F.map_preimage, sqC0.lift_fst]),
      F.map_injective (by rw [F.map_comp, F.map_preimage, sqC0.lift_snd])⟩
  obtain ⟨u, hua, hub⟩ := key αa αb (by simpa only [← Category.assoc] using sqA0.w =≫ p)
  obtain ⟨v, hva, hvb⟩ := key βa βb (by simpa only [hcond, ← Category.assoc] using sqB0.w =≫ q)
  exact ⟨pullback u v, pullback.fst u v ≫ αb, F.map (pullback.fst u v ≫ αa),
    isPullback_map_pullback_of_relativeProducts F p q g h sqA0 sqB0 sqC0 hua hub hva hvb⟩

/-- **The set-theoretic condition of Stacks 0AIS holds for the fibre product of two fppf sheaves
which satisfy it and have representable relative products, over an fppf sheaf which has only
*charted* relative products.**

Only two things about each leg are used: that it satisfies the set-theoretic condition, which
supplies the represented surjection the construction starts from, and that every morphism to it
out of a represented sheaf is relatively representable, which makes the comparison morphism into
the fibre product relatively representable. Both hold for an affine formal algebraic space and for
a formal algebraic space.

Of the base, nothing is used beyond
`AlgebraicGeometry.FormalSpace.HasChartedRelativeProducts`, and that is used at a single pair of
points: the two surjections `h_{U_X} ⟶ X` and `h_{U_Y} ⟶ Y` which the set-theoretic condition on
the legs supplies, pushed into the base. The chart `h_C ⟶ h_{U_X} ×_Z h_{U_Y}` composed with the
comparison morphism `h_{U_X} ×_Z h_{U_Y} ⟶ X ×_Z Y` is the surjection onto the fibre product that
the condition asks for, both factors being epimorphisms; and its kernel pair is represented by an
object of the site because it is cut out in two representable steps, first the base change of the
comparison morphism — relatively representable by the hypotheses on the legs alone — along the
chart, and then the base change of the chart itself along that. The relative product
`h_{U_X} ×_Z h_{U_Y}` never has to be an object of the site. -/
theorem satisfiesSetTheoreticCondition_pullback_of_hasChartedRelativeProducts
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZchart : HasChartedRelativeProducts B S hS Z)
    (hXset : SatisfiesSetTheoreticCondition B S hS X)
    (hXrep : HasRepresentableRelativeProducts B S hS X)
    (hYset : SatisfiesSetTheoreticCondition B S hS Y)
    (hYrep : HasRepresentableRelativeProducts B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS (pullback p q) := by
  classical
  let J := BigFppfOver.topology B S hS
  let F := Sheaf.sheafifiedYoneda J
  let G := sheafToPresheaf J (Type (u + 1))
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have : F.Full := (Sheaf.fullyFaithfulSheafifiedYoneda J).full
  have : F.Faithful := (Sheaf.fullyFaithfulSheafifiedYoneda J).faithful
  let eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  have chart : ∀ W : FppfSheaf B S hS, SatisfiesSetTheoreticCondition B S hS W →
      ∃ (U : BigFppfOver B S hS) (f : F.obj U ⟶ W), Epi f := by
    intro W hW
    obtain ⟨U, -, hU, -, hUrep, -, f, hf, -⟩ := hW
    let e : hU ≅ F.obj U := (Functor.FullyFaithful.ofFullyFaithful G).preimageIso
      (Classical.choice hUrep ≪≫ (G.mapIso (eG.app U)).symm)
    exact ⟨U, e.inv ≫ f, inferInstance⟩
  obtain ⟨UX, fX', hfX'⟩ := chart X hXset
  obtain ⟨UY, fY', hfY'⟩ := chart Y hYset
  obtain ⟨C, c, hcepi, hcrep⟩ := hZchart (fX' ≫ p) (fY' ≫ q)
  obtain ⟨V, c₁, c₂, k₁, k₂, sq₁, sq₂, -, -⟩ :=
    exists_pullback_comparison p q fX' fY'
      (IsPullback.of_hasPullback (fX' ≫ p) (fY' ≫ q))
  have hk₁ : Epi k₁ := epi_of_isPullback B S hS sq₁ hfY'
  have hk₂ : Epi k₂ := epi_of_isPullback B S hS sq₂ hfX'
  have hmrep : F.relativelyRepresentable (k₁ ≫ k₂) :=
    MorphismProperty.comp_mem _ _ _
      (MorphismProperty.of_isPullback sq₁ (hYrep fY'))
      (MorphismProperty.of_isPullback sq₂ (hXrep fX'))
  have hepi : Epi (c ≫ k₁ ≫ k₂) := inferInstance
  have sqR := (hcrep.isPullback (hmrep.fst (c ≫ k₁ ≫ k₂))).paste_vert
    (hmrep.isPullback (c ≫ k₁ ≫ k₂))
  exact ⟨C, hcrep.pullback (hmrep.fst (c ≫ k₁ ≫ k₂)), F.obj C,
    F.obj (hcrep.pullback (hmrep.fst (c ≫ k₁ ≫ k₂))),
    ⟨G.mapIso (eG.app C)⟩, ⟨G.mapIso (eG.app _)⟩,
    c ≫ k₁ ≫ k₂, hepi, sqR.isoPullback.hom, inferInstance⟩

/-- The set-theoretic condition of **Stacks 0AIS** holds for the fibre product of two fppf
sheaves which satisfy it and have representable relative products, over an fppf sheaf with
representable relative products.

This is the special case of `satisfiesSetTheoreticCondition_pullback_of_hasChartedRelativeProducts`
in which the relative products of the base are represented by objects of the site rather than
merely charted by them. -/
theorem satisfiesSetTheoreticCondition_pullback'
    {X Y Z : FppfSheaf B S hS} (p : X ⟶ Z) (q : Y ⟶ Z)
    (hZrep : HasRepresentableRelativeProducts B S hS Z)
    (hXset : SatisfiesSetTheoreticCondition B S hS X)
    (hXrep : HasRepresentableRelativeProducts B S hS X)
    (hYset : SatisfiesSetTheoreticCondition B S hS Y)
    (hYrep : HasRepresentableRelativeProducts B S hS Y) :
    SatisfiesSetTheoreticCondition B S hS (pullback p q) :=
  satisfiesSetTheoreticCondition_pullback_of_hasChartedRelativeProducts B S hS p q
    (hasChartedRelativeProducts_of_hasRepresentableRelativeProducts B S hS hZrep)
    hXset hXrep hYset hYrep

end AlgebraicGeometry.FormalSpace

end
