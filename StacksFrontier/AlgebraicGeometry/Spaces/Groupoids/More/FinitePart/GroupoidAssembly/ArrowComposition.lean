module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.GroupoidComposition

/-!
# Composition of sections of the arrow space of a groupoid in algebraic spaces

This is the first of the three parts of the proof that the finite part of a groupoid in
algebraic spaces is a groupoid (Stacks 04RU, clause (3)); the other two are
`TargetIdentities.lean` and `SectionGroupoid.lean`, in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidAssembly/`.
For a groupoid in algebraic spaces `(U, R, s, t, c, e, i)` over `B`, this part records the
identities of the composition `c` which the finite part needs, read on sections of the arrow
space and on morphisms into the arrow space, and then the elementary identities of the
structure morphisms `(U', Z_univ, s', t', c', e', i')` of the finite part, built in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidStructure.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/GroupoidComposition.lean`.

## Main definitions

* `AlgebraicGeometry.Space.composeMor`: the composite of two composable morphisms into the
  arrow space of a groupoid in algebraic spaces, as a morphism into the arrow space.

## Main results

* `AlgebraicGeometry.Space.compose_assoc_app`,
  `AlgebraicGeometry.Space.compose_identity_right_app` and
  `AlgebraicGeometry.Space.compose_self_inverseArrow_app`: associativity
  `c(c(a, b), d) = c(a, c(b, d))`, the right unit law `c(z, e(s(z))) = z` and the cancellation
  `c(z, i(z)) = e(t(z))` for the composition of a groupoid in algebraic spaces, read on
  sections of the arrow space; `AlgebraicGeometry.Space.composeMor_assoc` and
  `AlgebraicGeometry.Space.composeMor_unit_right` are the first two read on morphisms.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.untwistAmbient_snd_composeMor`: the second
  component of an untwisted section of an ambient fibre product is a `composeMor`.

## Implementation notes

No hypothesis beyond the groupoid itself, and for the elementary identities the data of a
`AlgebraicGeometry.Space.FinitePartUniversalOpen G`, is carried by any declaration here.

`compose_congr'` is the version of the public `AlgebraicGeometry.Space.compose_congr` for a
general groupoid in functors, and `compose_assoc`, `compose_identity_right` and
`compose_self_inverseArrow` are new: the twisting module proves the two *other* cancellation
laws and the *left* unit law, not these.

Comparisons of composites are never made by rewriting inside a composite of two arrows, whose
third argument is a proof the type of the term depends on; `AlgebraicGeometry.Space.compose_congr`
and `composeMor_congr` replace such rewriting.

`AlgebraicGeometry.Space.composeMor` exists so that associativity can be used as an identity
between *morphisms* rather than only between sections: the second component of an untwisted
section of an ambient fibre product is literally such a composite, by
`untwistAmbient_snd_composeMor`, and the cocycle argument of `TargetIdentities.lean` is then
morphism algebra. Its arguments are ordered as in `Deformation.GroupoidInFunctors.compose`, so
`composeMor G α β h` is "`α` after `β`"; `composeMor_comp_source` reads off the source of the
second entry and `composeMor_comp_target` the target of the first.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry.Space

/-! ### Arrows of an evaluated groupoid -/

/-- The composite of two sections of the arrow functor depends only on those two sections. -/
private theorem compose_congr' {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (a b a' b' : H.arrows.obj T)
    (h : H.source.app T a = H.target.app T b)
    (h' : H.source.app T a' = H.target.app T b')
    (ha : a = a') (hb : b = b') :
    H.compose T a b h = H.compose T a' b' h' := by
  subst ha
  subst hb
  rfl

/-- **Associativity of the composition of a groupoid in functors**, read on sections of the
arrow functor. -/
private theorem compose_assoc {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D)
    (a b d : H.arrows.obj T)
    (hab : H.source.app T a = H.target.app T b)
    (hbd : H.source.app T b = H.target.app T d)
    (h₁ : H.source.app T (H.compose T a b hab) = H.target.app T d)
    (h₂ : H.source.app T a = H.target.app T (H.compose T b d hbd)) :
    H.compose T (H.compose T a b hab) d h₁ = H.compose T a (H.compose T b d hbd) h₂ := by
  have hab' : H.compose T a b hab =
      (H.evaluationArrowEquiv T (H.target.app T d) (H.target.app T a)
        (evalMor H T b (H.target.app T d) (H.target.app T b) hbd rfl ≫
          evalMor H T a (H.target.app T b) (H.target.app T a) hab rfl)).1 :=
    compose_eq_evalMor H T a b hbd rfl hab rfl hab
  have hs1 := ((H.pointwiseData T).source_comp a b hab).trans hbd
  have ht1 := (H.pointwiseData T).target_comp a b hab
  have hbd' : H.compose T b d hbd =
      (H.evaluationArrowEquiv T (H.source.app T d) (H.target.app T b)
        (evalMor H T d (H.source.app T d) (H.target.app T d) rfl rfl ≫
          evalMor H T b (H.target.app T d) (H.target.app T b) hbd rfl)).1 :=
    compose_eq_evalMor H T b d rfl rfl hbd rfl hbd
  have hs2 := (H.pointwiseData T).source_comp b d hbd
  have ht2 := (H.pointwiseData T).target_comp b d hbd
  have hL : H.compose T (H.compose T a b hab) d h₁ =
      (H.evaluationArrowEquiv T (H.source.app T d) (H.target.app T a)
        (evalMor H T d (H.source.app T d) (H.target.app T d) rfl rfl ≫
          (evalMor H T b (H.target.app T d) (H.target.app T b) hbd rfl ≫
            evalMor H T a (H.target.app T b) (H.target.app T a) hab rfl))).1 := by
    rw [compose_eq_evalMor H T (H.compose T a b hab) d rfl rfl hs1 ht1 h₁]
    exact congrArg (fun m => (H.evaluationArrowEquiv T (H.source.app T d)
      (H.target.app T a)
      (evalMor H T d (H.source.app T d) (H.target.app T d) rfl rfl ≫ m)).1)
      (evalMor_eq H T (H.compose T a b hab) (H.target.app T d) (H.target.app T a)
        hs1 ht1 _ hab')
  have hR : H.compose T a (H.compose T b d hbd) h₂ =
      (H.evaluationArrowEquiv T (H.source.app T d) (H.target.app T a)
        ((evalMor H T d (H.source.app T d) (H.target.app T d) rfl rfl ≫
            evalMor H T b (H.target.app T d) (H.target.app T b) hbd rfl) ≫
          evalMor H T a (H.target.app T b) (H.target.app T a) hab rfl)).1 := by
    rw [compose_eq_evalMor H T a (H.compose T b d hbd) hs2 ht2 hab rfl h₂]
    exact congrArg (fun m => (H.evaluationArrowEquiv T (H.source.app T d)
      (H.target.app T a)
      (m ≫ evalMor H T a (H.target.app T b) (H.target.app T a) hab rfl)).1)
      (evalMor_eq H T (H.compose T b d hbd) (H.source.app T d) (H.target.app T b)
        hs2 ht2 _ hbd')
  rw [hL, hR]
  exact congrArg (fun m => (H.evaluationArrowEquiv T (H.source.app T d)
    (H.target.app T a) m).1)
    (Category.assoc (evalMor H T d (H.source.app T d) (H.target.app T d) rfl rfl)
      (evalMor H T b (H.target.app T d) (H.target.app T b) hbd rfl)
      (evalMor H T a (H.target.app T b) (H.target.app T a) hab rfl)).symm

/-- Composing a section of the arrow functor with the identity arrow at its source returns
that section. -/
private theorem compose_identity_right {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D) (a : H.arrows.obj T)
    (h : H.source.app T a = H.target.app T (H.identity T (H.source.app T a))) :
    H.compose T a (H.identity T (H.source.app T a)) h = a := by
  have hid : H.identity T (H.source.app T a) =
      (H.evaluationArrowEquiv T (H.source.app T a) (H.source.app T a) (𝟙 _)).1 := rfl
  have hids : H.source.app T (H.identity T (H.source.app T a)) = H.source.app T a := by
    rw [hid]
    exact (H.evaluationArrowEquiv T (H.source.app T a) (H.source.app T a) (𝟙 _)).2.1
  rw [compose_eq_evalMor H T a (H.identity T (H.source.app T a)) hids h.symm rfl rfl h,
    evalMor_eq H T (H.identity T (H.source.app T a)) (H.source.app T a)
      (H.source.app T a) hids h.symm (𝟙 _) hid, Category.id_comp]
  exact evalMor_val H T a (H.source.app T a) (H.target.app T a) rfl rfl

/-- Composing a section of the arrow functor with its inverse returns the identity arrow at
its target. -/
private theorem compose_self_inverseArrow {D : Type v} [Category.{w} D]
    (H : Deformation.GroupoidInFunctors.{v, w, u} D) (T : D) (a : H.arrows.obj T)
    (h : H.source.app T a = H.target.app T (Deformation.inverseArrow H T a)) :
    H.compose T a (Deformation.inverseArrow H T a) h =
      H.identity T (H.target.app T a) := by
  let _ := H.evaluationGroupoid T
  set x : H.Evaluation T := H.source.app T a with hx
  set y : H.Evaluation T := H.target.app T a with hy
  set f₀ : x ⟶ y := (H.evaluationArrowEquiv T x y).symm ⟨a, rfl, rfl⟩ with hf₀
  have hval : (H.evaluationArrowEquiv T x y f₀).1 = a :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  have hinv : (H.evaluationArrowEquiv T y x (Groupoid.inv f₀)).1 =
      Deformation.inverseArrow H T a := rfl
  have hcomp := H.evaluationArrowEquiv_comp T (Groupoid.inv f₀) f₀
  rw [Groupoid.inv_comp, H.evaluationArrowEquiv_id] at hcomp
  exact (compose_congr' H T _ _ _ _ h _ hval.symm hinv.symm).trans hcomp.symm

/-! ### Composition of sections of the arrow space as a morphism -/

section Composition

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B)

/-- The composite of two composable morphisms into the arrow space, as a morphism into the
arrow space: the composition of the groupoid applied to the pair they form. -/
public def composeMor {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (α β : X ⟶ G.arrows.obj) (h : α ≫ G.source.hom = β ≫ G.target.hom) :
    X ⟶ G.arrows.obj :=
  pullback.lift α β h ≫ G.comp.hom

/-- The composite morphism, read on a section, is the composite of the two sections. -/
public theorem composeMor_app {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (α β : X ⟶ G.arrows.obj) (h : α ≫ G.source.hom = β ≫ G.target.hom)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : X.obj V)
    (hx : G.source.hom.app V (α.app V x) = G.target.hom.app V (β.app V x)) :
    (composeMor G α β h).app V x =
      G.toGroupoidInFunctors.compose V (α.app V x) (β.app V x) hx := by
  have hfst : (pullback.fst G.source.hom G.target.hom).app V
      ((pullback.lift α β h).app V x) = α.app V x :=
    congrArg (fun k => k.app V x) (pullback.lift_fst α β h)
  have hsnd : (pullback.snd G.source.hom G.target.hom).app V
      ((pullback.lift α β h).app V x) = β.app V x :=
    congrArg (fun k => k.app V x) (pullback.lift_snd α β h)
  have hcond := pullback_condition_app G.source.hom G.target.hom V
    ((pullback.lift α β h).app V x)
  show G.comp.hom.app V ((pullback.lift α β h).app V x) = _
  rw [comp_hom_app G V _ hcond]
  exact compose_congr G V _ _ _ _ hcond hx hfst hsnd

/-- The composite morphism depends only on the two morphisms composed. -/
public theorem composeMor_congr {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (α β α' β' : X ⟶ G.arrows.obj)
    (h : α ≫ G.source.hom = β ≫ G.target.hom)
    (h' : α' ≫ G.source.hom = β' ≫ G.target.hom)
    (ha : α = α') (hb : β = β') :
    composeMor G α β h = composeMor G α' β' h' := by
  subst ha
  subst hb
  rfl

/-- Precomposing a composite is the composite of the precompositions. -/
public theorem comp_composeMor {X X' : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (g : X' ⟶ X) (α β : X ⟶ G.arrows.obj)
    (h : α ≫ G.source.hom = β ≫ G.target.hom)
    (h' : (g ≫ α) ≫ G.source.hom = (g ≫ β) ≫ G.target.hom) :
    g ≫ composeMor G α β h = composeMor G (g ≫ α) (g ≫ β) h' := by
  have hl : pullback.lift (g ≫ α) (g ≫ β) h' = g ≫ pullback.lift α β h := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst]
    · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd]
  exact (Category.assoc g (pullback.lift α β h) G.comp.hom).symm.trans
    (congrArg (fun m => m ≫ G.comp.hom) hl.symm)

/-- The source of a composite is the source of its second entry. -/
public theorem composeMor_comp_source
    {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (α β : X ⟶ G.arrows.obj) (h : α ≫ G.source.hom = β ≫ G.target.hom) :
    composeMor G α β h ≫ G.source.hom = β ≫ G.source.hom := by
  ext V x
  have hx : G.source.hom.app V (α.app V x) = G.target.hom.app V (β.app V x) :=
    congrArg (fun k => k.app V x) h
  show G.source.hom.app V ((composeMor G α β h).app V x) =
    G.source.hom.app V (β.app V x)
  rw [composeMor_app G α β h V x hx]
  exact source_comp_hom_app G V _ _ hx

/-- The target of a composite is the target of its first entry. -/
public theorem composeMor_comp_target
    {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (α β : X ⟶ G.arrows.obj) (h : α ≫ G.source.hom = β ≫ G.target.hom) :
    composeMor G α β h ≫ G.target.hom = α ≫ G.target.hom := by
  ext V x
  have hx : G.source.hom.app V (α.app V x) = G.target.hom.app V (β.app V x) :=
    congrArg (fun k => k.app V x) h
  show G.target.hom.app V ((composeMor G α β h).app V x) =
    G.target.hom.app V (α.app V x)
  rw [composeMor_app G α β h V x hx]
  exact target_comp_hom_app G V _ _ hx

/-- **Associativity of the composition**, read on morphisms into the arrow space. -/
public theorem composeMor_assoc {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (α β δ : X ⟶ G.arrows.obj)
    (h₁ : α ≫ G.source.hom = β ≫ G.target.hom)
    (h₂ : β ≫ G.source.hom = δ ≫ G.target.hom)
    (h₃ : composeMor G α β h₁ ≫ G.source.hom = δ ≫ G.target.hom)
    (h₄ : α ≫ G.source.hom = composeMor G β δ h₂ ≫ G.target.hom) :
    composeMor G (composeMor G α β h₁) δ h₃ =
      composeMor G α (composeMor G β δ h₂) h₄ := by
  ext V x
  have e₁ : G.source.hom.app V (α.app V x) = G.target.hom.app V (β.app V x) :=
    congrArg (fun k => k.app V x) h₁
  have e₂ : G.source.hom.app V (β.app V x) = G.target.hom.app V (δ.app V x) :=
    congrArg (fun k => k.app V x) h₂
  have e₃ : G.source.hom.app V ((composeMor G α β h₁).app V x) =
      G.target.hom.app V (δ.app V x) := congrArg (fun k => k.app V x) h₃
  have e₄ : G.source.hom.app V (α.app V x) =
      G.target.hom.app V ((composeMor G β δ h₂).app V x) :=
    congrArg (fun k => k.app V x) h₄
  have hA : (composeMor G α β h₁).app V x =
      G.toGroupoidInFunctors.compose V (α.app V x) (β.app V x) e₁ :=
    composeMor_app G α β h₁ V x e₁
  have hB : (composeMor G β δ h₂).app V x =
      G.toGroupoidInFunctors.compose V (β.app V x) (δ.app V x) e₂ :=
    composeMor_app G β δ h₂ V x e₂
  have f₃ : G.source.hom.app V
      (G.toGroupoidInFunctors.compose V (α.app V x) (β.app V x) e₁) =
      G.target.hom.app V (δ.app V x) := by rw [← hA]; exact e₃
  have f₄ : G.source.hom.app V (α.app V x) =
      G.target.hom.app V
        (G.toGroupoidInFunctors.compose V (β.app V x) (δ.app V x) e₂) := by
    rw [← hB]; exact e₄
  show (composeMor G (composeMor G α β h₁) δ h₃).app V x =
    (composeMor G α (composeMor G β δ h₂) h₄).app V x
  exact ((composeMor_app G _ _ h₃ V x e₃).trans
    ((compose_congr G V _ _ _ _ e₃ f₃ hA rfl).trans
      ((compose_assoc G.toGroupoidInFunctors V (α.app V x) (β.app V x) (δ.app V x)
          e₁ e₂ f₃ f₄).trans
        (compose_congr G V _ _ _ _ f₄ e₄ rfl hB.symm)))).trans
    (composeMor_app G _ _ h₄ V x e₄).symm

/-- Composing a morphism into the arrow space with the unit at its source returns it. -/
public theorem composeMor_unit_right (e : G.objects ⟶ G.arrows)
    (he : ∀ T x, e.hom.app T x = G.toGroupoidInFunctors.identity T x)
    {X : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (α : X ⟶ G.arrows.obj)
    (h : α ≫ G.source.hom = (α ≫ G.source.hom ≫ e.hom) ≫ G.target.hom) :
    composeMor G α (α ≫ G.source.hom ≫ e.hom) h = α := by
  ext V x
  have hx : G.source.hom.app V (α.app V x) =
      G.target.hom.app V ((α ≫ G.source.hom ≫ e.hom).app V x) :=
    congrArg (fun k => k.app V x) h
  have hval : (α ≫ G.source.hom ≫ e.hom).app V x =
      G.toGroupoidInFunctors.identity V (G.source.hom.app V (α.app V x)) :=
    he V (G.source.hom.app V (α.app V x))
  have hx' : G.source.hom.app V (α.app V x) =
      G.target.hom.app V
        (G.toGroupoidInFunctors.identity V (G.source.hom.app V (α.app V x))) := by
    rw [← hval]; exact hx
  show (composeMor G α (α ≫ G.source.hom ≫ e.hom) h).app V x = α.app V x
  rw [composeMor_app G _ _ h V x hx]
  exact (compose_congr G V _ _ _ _ hx hx' rfl hval).trans
    (compose_identity_right G.toGroupoidInFunctors V (α.app V x) hx')

/-- The source of an identity arrow is the point it sits at. -/
public theorem source_identity_app (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (y : G.objects.obj.obj T) :
    G.source.hom.app T (G.toGroupoidInFunctors.identity T y) = y := by
  let _ : Groupoid (G.objects.obj.obj T) := G.toGroupoidInFunctors.evaluationGroupoid T
  exact (G.toGroupoidInFunctors.evaluationArrowEquiv T y y (𝟙 y)).2.1

/-- The target of an identity arrow is the point it sits at. -/
public theorem target_identity_app (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (y : G.objects.obj.obj T) :
    G.target.hom.app T (G.toGroupoidInFunctors.identity T y) = y := by
  let _ : Groupoid (G.objects.obj.obj T) := G.toGroupoidInFunctors.evaluationGroupoid T
  exact (G.toGroupoidInFunctors.evaluationArrowEquiv T y y (𝟙 y)).2.2

/-- The target of the unit arrow at a point of the object space is that point. -/
public theorem identity_comp_target (e : G.objects ⟶ G.arrows)
    (he : ∀ T x, e.hom.app T x = G.toGroupoidInFunctors.identity T x) :
    e.hom ≫ G.target.hom = 𝟙 G.objects.obj := by
  ext T x
  show G.target.hom.app T (e.hom.app T x) = x
  rw [he T x]
  exact target_identity_app G T x

/-- Composing a section of the arrow space with its inverse returns the unit at its target. -/
public theorem compose_self_inverseArrow_app
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : G.arrows.obj.obj T)
    (h : G.source.hom.app T a =
      G.target.hom.app T (Deformation.inverseArrow G.toGroupoidInFunctors T a)) :
    G.toGroupoidInFunctors.compose T a
        (Deformation.inverseArrow G.toGroupoidInFunctors T a) h =
      G.toGroupoidInFunctors.identity T (G.target.hom.app T a) :=
  compose_self_inverseArrow G.toGroupoidInFunctors T a h

/-- **Associativity of the composition**, read on sections of the arrow space. -/
public theorem compose_assoc_app
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a b d : G.arrows.obj.obj T)
    (hab : G.source.hom.app T a = G.target.hom.app T b)
    (hbd : G.source.hom.app T b = G.target.hom.app T d)
    (h₁ : G.source.hom.app T (G.toGroupoidInFunctors.compose T a b hab) =
      G.target.hom.app T d)
    (h₂ : G.source.hom.app T a =
      G.target.hom.app T (G.toGroupoidInFunctors.compose T b d hbd)) :
    G.toGroupoidInFunctors.compose T (G.toGroupoidInFunctors.compose T a b hab) d h₁ =
      G.toGroupoidInFunctors.compose T a (G.toGroupoidInFunctors.compose T b d hbd) h₂ :=
  compose_assoc G.toGroupoidInFunctors T a b d hab hbd h₁ h₂

/-- Composing a section of the arrow space with the identity at its source returns it. -/
public theorem compose_identity_right_app
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : G.arrows.obj.obj T)
    (h : G.source.hom.app T a =
      G.target.hom.app T
        (G.toGroupoidInFunctors.identity T (G.source.hom.app T a))) :
    G.toGroupoidInFunctors.compose T a
      (G.toGroupoidInFunctors.identity T (G.source.hom.app T a)) h = a :=
  compose_identity_right G.toGroupoidInFunctors T a h

variable {T : AlgebraicGeometry.AlgebraicSpaces C S hS}

/-- The untwisting pair followed by the composition is the composite morphism of the second
projection with the fixed arrow along the first. -/
public theorem untwistPair_comp_eq_composeMor (z : T ⟶ G.arrows) (a : T ⟶ G.objects)
    (ha : z ≫ G.target = a)
    (hc : pullback.snd a.hom G.source.hom ≫ G.source.hom =
      (pullback.fst a.hom G.source.hom ≫ z.hom) ≫ G.target.hom) :
    untwistPair G z a ha ≫ G.comp.hom =
      composeMor G (pullback.snd a.hom G.source.hom)
        (pullback.fst a.hom G.source.hom ≫ z.hom) hc := rfl

end Composition

namespace FinitePartUniversalOpen

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  {G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B}

/-! ### Elementary identities of the structure morphisms -/

/-- The base of the twisted pair, read on underlying presheaves. -/
public theorem targetPair_toBase_hom (F : FinitePartUniversalOpen G) :
    F.targetPair.toBase.hom = F.arrowMap.hom ≫ G.target.hom :=
  congrArg (fun z : F.arrows ⟶ G.objects => z.hom) F.targetPair_toBase

/-- The source square of the morphism of groupoids, read on underlying presheaves. -/
public theorem arrowMap_comp_source_hom (F : FinitePartUniversalOpen G) :
    F.arrowMap.hom ≫ G.source.hom = F.source.hom ≫ F.objectProjection.hom :=
  congrArg (fun z : F.arrows ⟶ G.objects => z.hom) F.arrowMap_comp_source

/-- The target square of the morphism of groupoids, read on underlying presheaves. -/
public theorem arrowMap_comp_target_hom (F : FinitePartUniversalOpen G) :
    F.arrowMap.hom ≫ G.target.hom = F.target.hom ≫ F.objectProjection.hom :=
  congrArg (fun z : F.arrows ⟶ G.objects => z.hom) F.arrowMap_comp_target

/-- The base of the universal pair is the projection on objects, read on underlying
presheaves. -/
public theorem universalOpen_toBase_hom (F : FinitePartUniversalOpen G) :
    F.universalOpen.toBase.hom = F.objectProjection.hom :=
  congrArg (fun z : F.objects ⟶ G.objects => z.hom) F.universalOpen_base

/-- The unit of the given groupoid is a section of its target as well as of its source. -/
public theorem unit_comp_target (F : FinitePartUniversalOpen G) :
    F.unit.hom ≫ G.target.hom = 𝟙 G.objects.obj :=
  identity_comp_target G F.unit F.unit_identity

/-- The two components of a section of the ambient fibre product of the twisted pair are
composable in the given groupoid. -/
public theorem targetPair_ambient_condition (F : FinitePartUniversalOpen G) :
    pullback.snd F.targetPair.toBase.hom G.source.hom ≫ G.source.hom =
      (pullback.fst F.targetPair.toBase.hom G.source.hom ≫ F.arrowMap.hom) ≫
        G.target.hom := by
  rw [Category.assoc, ← F.targetPair_toBase_hom]
  exact pullback.condition.symm

/-- Untwisting, read on the second component, is composition with the tautological arrow. -/
public theorem untwistAmbient_snd_composeMor (F : FinitePartUniversalOpen G) :
    F.untwistAmbient ≫
        pullback.snd (F.source ≫ F.universalOpen.toBase).hom G.source.hom =
      composeMor G (pullback.snd F.targetPair.toBase.hom G.source.hom)
        (pullback.fst F.targetPair.toBase.hom G.source.hom ≫ F.arrowMap.hom)
        F.targetPair_ambient_condition :=
  F.untwistAmbient_snd.trans
    (untwistPair_comp_eq_composeMor G F.arrowMap F.targetPair.toBase
      F.targetPair_toBase.symm F.targetPair_ambient_condition)

/-- The second component of a section of the ambient fibre product of the twisted pair is
composable with the arrow of its first component. -/
public theorem targetPair_ambient_cond (F : FinitePartUniversalOpen G)
    {Amb : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (φ : Amb ⟶ F.arrows.obj) (ψ : Amb ⟶ G.arrows.obj)
    (hM : φ ≫ F.targetPair.toBase.hom = ψ ≫ G.source.hom) :
    ψ ≫ G.source.hom = (φ ≫ F.arrowMap.hom) ≫ G.target.hom := by
  rw [← hM, F.targetPair_toBase_hom, Category.assoc]

/-- The untwist of a section of the ambient fibre product of the twisted pair is a section of
the ambient fibre product of the base change of the universal pair along the source. -/
public theorem untwist_base_condition (F : FinitePartUniversalOpen G)
    {Amb : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (φ : Amb ⟶ F.arrows.obj) (ψ : Amb ⟶ G.arrows.obj)
    (hc : ψ ≫ G.source.hom = (φ ≫ F.arrowMap.hom) ≫ G.target.hom) :
    (φ ≫ F.source.hom) ≫ F.universalOpen.toBase.hom =
      composeMor G ψ (φ ≫ F.arrowMap.hom) hc ≫ G.source.hom := by
  simp only [F.universalOpen_toBase_hom, composeMor_comp_source, Category.assoc,
    F.arrowMap_comp_source_hom]

/-- A section of the ambient fibre product of the twisted pair, read at the target, is a
section of the ambient fibre product of the universal pair. -/
public theorem untwist_target_condition (F : FinitePartUniversalOpen G)
    {Amb : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (φ : Amb ⟶ F.arrows.obj) (ψ : Amb ⟶ G.arrows.obj)
    (hM : φ ≫ F.targetPair.toBase.hom = ψ ≫ G.source.hom) :
    (φ ≫ F.target.hom) ≫ F.universalOpen.toBase.hom = ψ ≫ G.source.hom := by
  rw [F.universalOpen_toBase_hom, Category.assoc, ← F.arrowMap_comp_target_hom,
    ← F.targetPair_toBase_hom, hM]


end FinitePartUniversalOpen

end AlgebraicGeometry.Space

end
