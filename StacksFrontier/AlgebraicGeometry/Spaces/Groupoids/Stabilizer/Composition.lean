module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.Basic

/-!
# Composition of generalized arrows of a groupoid in algebraic spaces

A generalized arrow of a groupoid in algebraic spaces `G` over a presheaf `T` is a morphism
`T ⟶ R` to the arrow presheaf. Two such are composable when the source of the first agrees
with the target of the second, and then they have a composite, obtained from the composition
morphism of `G` through the universal property of the fibre product. This file sets up that
composition and proves that it is associative, has the identity arrows as two-sided units, and
that every generalized arrow is invertible — the groupoid laws, read on generalized points.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose`: the composite of a composable
  pair of generalized arrows.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidInverse`: the inverse morphism
  `R ⟶ R` of the arrow presheaf.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityAfterTarget` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityAfterSource`: the identity arrow at the
  target, resp. the source, of a generalized arrow.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_eq_comp`: the composite is
  computed by the composition morphism of the groupoid.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_source` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_target`: the composite has the
  source of the second arrow and the target of the first.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_assoc`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_leftIdentity`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_rightIdentity`,
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_inverseLeft` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.groupoidCompose_inverseRight`: the groupoid laws
  for generalized arrows.

## Implementation notes

`groupoidCompose_eval` is the bridge to the pointwise groupoid: the value of a composite at a
point of a test object is the composite of the two values in the evaluated groupoid. Its proof
identifies the morphism `pullback.lift f g w` into the chosen fibre product with the
composite of the evident morphism into the presheaf of composable pairs and the comparison
`AlgebraicGeometry.composableToPullback`, since the groupoid condition of **Stacks 043W** is
imposed through that comparison. Every law below is then obtained by transporting the
corresponding law of the evaluated groupoid, which is a genuine groupoid, along
`Deformation.GroupoidInFunctors.evaluationArrowEquiv`.

The unit is `AlgebraicGeometry.GroupoidInAlgebraicSpaces.identityArrow` (**Stacks 06K5**) and
the inverse is the natural transformation of `Deformation.existsUnique_inverse`, whose value at
each point is `Deformation.inverseArrow`; neither is re-derived here.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 0447](https://stacks.math.columbia.edu/tag/0447)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The unit of a groupoid in algebraic spaces, read as a morphism of presheaves, is a section
of the source. -/
theorem identityArrow_hom_comp_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    (identityArrow G).hom ≫ G.source.hom = 𝟙 G.objects.obj :=
  congrArg (fun f : G.objects ⟶ G.objects => f.hom) (identityArrow_comp_source G)

/-- The unit of a groupoid in algebraic spaces, read as a morphism of presheaves, is a section
of the target. -/
theorem identityArrow_hom_comp_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    (identityArrow G).hom ≫ G.target.hom = 𝟙 G.objects.obj :=
  congrArg (fun f : G.objects ⟶ G.objects => f.hom) (identityArrow_comp_target G)

/-- The composite of a composable pair of generalized arrows of a groupoid in algebraic
spaces. -/
noncomputable def groupoidCompose (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f g : T ⟶ G.arrows.obj)
    (w : f ≫ G.source.hom = g ≫ G.target.hom) : T ⟶ G.arrows.obj :=
  pullback.lift f g w ≫ G.comp.hom

/-- The composite of a composable pair of generalized arrows is computed by the composition
morphism of the groupoid, applied to the pair they determine. -/
theorem groupoidCompose_eq_comp (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f g : T ⟶ G.arrows.obj)
    (w : f ≫ G.source.hom = g ≫ G.target.hom) :
    groupoidCompose G f g w = pullback.lift f g w ≫ G.comp.hom := rfl

/-- The value of a composite of generalized arrows at a point of a test object is the
composite in the evaluated groupoid. -/
theorem groupoidCompose_eval (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f g : T ⟶ G.arrows.obj)
    (w : f ≫ G.source.hom = g ≫ G.target.hom)
    (V : (BigFppfOver C S hS)ᵒᵖ) (t : T.obj V) :
    (groupoidCompose G f g w).app V t =
      G.toGroupoidInFunctors.compose V (f.app V t) (g.app V t)
        (congrArg (fun k => (k.app V) t) w) := by
  let D := Deformation.composableArrows G.objects.obj G.arrows.obj
    G.source.hom G.target.hom
  let p : T ⟶ D := {
    app := fun V => ↾ fun t => ⟨(f.app V t, g.app V t),
      congrArg (fun k => (k.app V) t) w⟩
    naturality := by
      intro V W r
      ext t
      apply Subtype.ext
      apply Prod.ext
      · exact NatTrans.naturality_apply f r t
      · exact NatTrans.naturality_apply g r t }
  have hp : pullback.lift f g w = p ≫ composableToPullback G.source.hom G.target.hom := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, composableToPullback, pullback.lift_fst]
      ext V t
      rfl
    · rw [pullback.lift_snd, Category.assoc, composableToPullback, pullback.lift_snd]
      ext V t
      rfl
  exact congrArg (fun k => G.comp.hom.app V (k.app V t)) hp

/-- The composite of a composable pair of generalized arrows has the source of the second. -/
theorem groupoidCompose_source (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f g : T ⟶ G.arrows.obj)
    (w : f ≫ G.source.hom = g ≫ G.target.hom) :
    groupoidCompose G f g w ≫ G.source.hom = g ≫ G.source.hom := by
  ext V t
  change G.source.hom.app V ((groupoidCompose G f g w).app V t) =
    G.source.hom.app V (g.app V t)
  rw [groupoidCompose_eval]
  exact (G.toGroupoidInFunctors.pointwiseData V).source_comp
    (f.app V t) (g.app V t) (congrArg (fun k => (k.app V) t) w)

/-- The composite of a composable pair of generalized arrows has the target of the first. -/
theorem groupoidCompose_target (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f g : T ⟶ G.arrows.obj)
    (w : f ≫ G.source.hom = g ≫ G.target.hom) :
    groupoidCompose G f g w ≫ G.target.hom = f ≫ G.target.hom := by
  ext V t
  change G.target.hom.app V ((groupoidCompose G f g w).app V t) =
    G.target.hom.app V (f.app V t)
  rw [groupoidCompose_eval]
  exact (G.toGroupoidInFunctors.pointwiseData V).target_comp
    (f.app V t) (g.app V t) (congrArg (fun k => (k.app V) t) w)

/-- Composition of generalized arrows commutes with precomposition by a morphism of test
presheaves. -/
theorem groupoidCompose_pre (G : GroupoidInAlgebraicSpaces C S hS B)
    {T U : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (k : T ⟶ U)
    (f g : U ⟶ G.arrows.obj) (w : f ≫ G.source.hom = g ≫ G.target.hom) :
    k ≫ groupoidCompose G f g w =
      groupoidCompose G (k ≫ f) (k ≫ g) (by
        calc
          (k ≫ f) ≫ G.source.hom = k ≫ (f ≫ G.source.hom) := Category.assoc _ _ _
          _ = k ≫ (g ≫ G.target.hom) := congrArg (fun z => k ≫ z) w
          _ = (k ≫ g) ≫ G.target.hom := (Category.assoc _ _ _).symm) := by
  have w' : (k ≫ f) ≫ G.source.hom = (k ≫ g) ≫ G.target.hom := by
    rw [Category.assoc, Category.assoc, w]
  have hpair : k ≫ pullback.lift f g w = pullback.lift (k ≫ f) (k ≫ g) w' := by
    apply pullback.hom_ext
    · simp [Category.assoc]
    · simp [Category.assoc]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ G.comp.hom) hpair)

/-- Composition of generalized arrows only depends on the two arrows, not on the witness that
they are composable. -/
theorem groupoidCompose_congr (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {a a' b b' : T ⟶ G.arrows.obj}
    (w : a ≫ G.source.hom = b ≫ G.target.hom)
    (w' : a' ≫ G.source.hom = b' ≫ G.target.hom)
    (ha : a = a') (hb : b = b') :
    groupoidCompose G a b w = groupoidCompose G a' b' w' := by
  cases ha
  cases hb
  rfl

/-- The inverse morphism of the arrow presheaf of a groupoid in algebraic spaces. -/
noncomputable def groupoidInverse (G : GroupoidInAlgebraicSpaces C S hS B) :
    G.arrows.obj ⟶ G.arrows.obj :=
  (Deformation.existsUnique_inverse G.toGroupoidInFunctors).choose

/-- The value of the inverse morphism at a point of a test object is the inverse arrow of the
evaluated groupoid. -/
theorem groupoidInverse_app (G : GroupoidInAlgebraicSpaces C S hS B)
    (V : (BigFppfOver C S hS)ᵒᵖ) (a : G.arrows.obj.obj V) :
    (groupoidInverse G).app V a = Deformation.inverseArrow G.toGroupoidInFunctors V a :=
  (Deformation.existsUnique_inverse G.toGroupoidInFunctors).choose_spec.1 V a

/-- The inverse of an arrow has source the target of the arrow. -/
theorem groupoidInverse_source (G : GroupoidInAlgebraicSpaces C S hS B) :
    groupoidInverse G ≫ G.source.hom = G.target.hom := by
  ext V a
  change G.source.hom.app V ((groupoidInverse G).app V a) = G.target.hom.app V a
  rw [groupoidInverse_app]
  exact Deformation.inverseArrow_source G.toGroupoidInFunctors V a

/-- The inverse of an arrow has target the source of the arrow. -/
theorem groupoidInverse_target (G : GroupoidInAlgebraicSpaces C S hS B) :
    groupoidInverse G ≫ G.target.hom = G.source.hom := by
  ext V a
  change G.target.hom.app V ((groupoidInverse G).app V a) = G.source.hom.app V a
  rw [groupoidInverse_app]
  exact Deformation.inverseArrow_target G.toGroupoidInFunctors V a

/-- The identity arrow at the target of a generalized arrow. -/
noncomputable def identityAfterTarget (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj) : T ⟶ G.arrows.obj :=
  a ≫ G.target.hom ≫ (identityArrow G).hom

/-- The identity arrow at the source of a generalized arrow. -/
noncomputable def identityAfterSource (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj) : T ⟶ G.arrows.obj :=
  a ≫ G.source.hom ≫ (identityArrow G).hom

/-- The value of the identity at the target of a generalized arrow at a point. -/
private theorem identityAfterTarget_app (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj)
    (V : (BigFppfOver C S hS)ᵒᵖ) (t : T.obj V) :
    (identityAfterTarget G a).app V t =
      G.toGroupoidInFunctors.identity V (G.toGroupoidInFunctors.target.app V (a.app V t)) := by
  change (identityArrow G).hom.app V (G.toGroupoidInFunctors.target.app V (a.app V t)) = _
  exact identityArrow_hom_app G V _

/-- The value of the identity at the source of a generalized arrow at a point. -/
private theorem identityAfterSource_app (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj)
    (V : (BigFppfOver C S hS)ᵒᵖ) (t : T.obj V) :
    (identityAfterSource G a).app V t =
      G.toGroupoidInFunctors.identity V (G.toGroupoidInFunctors.source.app V (a.app V t)) := by
  change (identityArrow G).hom.app V (G.toGroupoidInFunctors.source.app V (a.app V t)) = _
  exact identityArrow_hom_app G V _

/-- The identity at the target of an arrow is composable after it. -/
theorem identityAfterTarget_composable (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj) :
    identityAfterTarget G a ≫ G.source.hom = a ≫ G.target.hom := by
  simp only [identityAfterTarget, Category.assoc, identityArrow_hom_comp_source,
    Category.comp_id]

/-- The identity at the source of an arrow is composable before it. -/
theorem identityAfterSource_composable (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj) :
    a ≫ G.source.hom = identityAfterSource G a ≫ G.target.hom := by
  simp only [identityAfterSource, Category.assoc, identityArrow_hom_comp_target,
    Category.comp_id]

/-- The arrow of the evaluated groupoid corresponding to an element of the arrow functor
represents that element. -/
private theorem evaluationArrowEquiv_symm_val {D : Type*} [Category D]
    (K : Deformation.GroupoidInFunctors D) (T : D) (f : K.arrows.obj T) :
    (K.evaluationArrowEquiv T (K.source.app T f) (K.target.app T f)
      ((K.evaluationArrowEquiv T _ _).symm ⟨f, rfl, rfl⟩)).1 = f :=
  congrArg Subtype.val (Equiv.apply_symm_apply (K.evaluationArrowEquiv T _ _) ⟨f, rfl, rfl⟩)

/-- The inverse morphism at a point is the inverse in the evaluated groupoid. -/
private theorem evaluationArrowEquiv_inv_val (G : GroupoidInAlgebraicSpaces C S hS B)
    (V : (BigFppfOver C S hS)ᵒᵖ) (f : G.arrows.obj.obj V) :
    letI := G.toGroupoidInFunctors.evaluationGroupoid V
    (G.toGroupoidInFunctors.evaluationArrowEquiv V (G.toGroupoidInFunctors.target.app V f)
      (G.toGroupoidInFunctors.source.app V f) (Groupoid.inv
        ((G.toGroupoidInFunctors.evaluationArrowEquiv V (G.toGroupoidInFunctors.source.app V f)
          (G.toGroupoidInFunctors.target.app V f)).symm ⟨f, rfl, rfl⟩))).1 =
      (groupoidInverse G).app V f := by
  rw [groupoidInverse_app]
  unfold Deformation.inverseArrow
  rfl

/-- Composition in a groupoid in functors is associative, read on sections of the arrow
functor. -/
private theorem groupoidInFunctors_compose_assoc {D : Type*} [Category D]
    (K : Deformation.GroupoidInFunctors D) (T : D) (a b c : K.arrows.obj T)
    (hab : K.source.app T a = K.target.app T b) (hbc : K.source.app T b = K.target.app T c)
    (h₁ : K.source.app T (K.compose T a b hab) = K.target.app T c)
    (h₂ : K.source.app T a = K.target.app T (K.compose T b c hbc)) :
    K.compose T (K.compose T a b hab) c h₁ = K.compose T a (K.compose T b c hbc) h₂ := by
  let _ : Groupoid (K.objects.obj T) := K.evaluationGroupoid T
  let qa := (K.evaluationArrowEquiv T (K.source.app T a) (K.target.app T a)).symm ⟨a, rfl, rfl⟩
  let qb := (K.evaluationArrowEquiv T (K.source.app T b) (K.source.app T a)).symm
    ⟨b, rfl, hab.symm⟩
  let qc := (K.evaluationArrowEquiv T (K.source.app T c) (K.source.app T b)).symm
    ⟨c, rfl, hbc.symm⟩
  have h := K.evaluationArrowEquiv_comp T (qc ≫ qb) qa
  rw [Category.assoc] at h
  simpa [qa, qb, qc] using h

/-- Composition of generalized arrows is associative. -/
theorem groupoidCompose_assoc (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a b c : T ⟶ G.arrows.obj)
    (wab : a ≫ G.source.hom = b ≫ G.target.hom)
    (wbc : b ≫ G.source.hom = c ≫ G.target.hom)
    (wL : groupoidCompose G a b wab ≫ G.source.hom = c ≫ G.target.hom)
    (wR : a ≫ G.source.hom = groupoidCompose G b c wbc ≫ G.target.hom) :
    groupoidCompose G (groupoidCompose G a b wab) c wL =
      groupoidCompose G a (groupoidCompose G b c wbc) wR := by
  ext V t
  change (groupoidCompose G _ c wL).app V t = (groupoidCompose G a _ wR).app V t
  simp only [groupoidCompose_eval]
  exact groupoidInFunctors_compose_assoc _ _ _ _ _ _ _ _ _

/-- The identity at the target of a generalized arrow is a left unit for composition. -/
theorem groupoidCompose_leftIdentity (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj) :
    groupoidCompose G (identityAfterTarget G a) a (identityAfterTarget_composable G a) = a := by
  ext V t
  let H := G.toGroupoidInFunctors
  let _ : Groupoid (H.objects.obj V) := H.evaluationGroupoid V
  let f := a.app V t
  let x := H.source.app V f
  let y := H.target.app V f
  let q := (H.evaluationArrowEquiv V x y).symm ⟨f, rfl, rfl⟩
  have wid : H.source.app V (H.identity V y) = H.target.app V f :=
    (H.evaluationArrowEquiv V y y (𝟙 y)).2.1
  have hid : (identityAfterTarget G a).app V t = H.identity V y := identityAfterTarget_app G a V t
  have hunit : H.compose V (H.identity V y) f wid = f := by
    have hcomp := H.evaluationArrowEquiv_comp V q (𝟙 y)
    have hq : (H.evaluationArrowEquiv V x y q).1 = f := evaluationArrowEquiv_symm_val H V f
    simpa only [Deformation.GroupoidInFunctors.identity, hq, Category.comp_id] using hcomp.symm
  have he' : (groupoidCompose G (identityAfterTarget G a) a
      (identityAfterTarget_composable G a)).app V t =
      H.compose V (H.identity V y) f wid := by
    simpa only [H, toGroupoidInFunctors, hid, f] using groupoidCompose_eval G
      (identityAfterTarget G a) a (identityAfterTarget_composable G a) V t
  exact he'.trans hunit

/-- The identity at the source of a generalized arrow is a right unit for composition. -/
theorem groupoidCompose_rightIdentity (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj) :
    groupoidCompose G a (identityAfterSource G a) (identityAfterSource_composable G a) = a := by
  ext V t
  let H := G.toGroupoidInFunctors
  let _ : Groupoid (H.objects.obj V) := H.evaluationGroupoid V
  let f := a.app V t
  let x := H.source.app V f
  let y := H.target.app V f
  let q := (H.evaluationArrowEquiv V x y).symm ⟨f, rfl, rfl⟩
  have wid : H.source.app V f = H.target.app V (H.identity V x) :=
    (H.evaluationArrowEquiv V x x (𝟙 x)).2.2.symm
  have hid : (identityAfterSource G a).app V t = H.identity V x := identityAfterSource_app G a V t
  have hunit : H.compose V f (H.identity V x) wid = f := by
    have hcomp := H.evaluationArrowEquiv_comp V (𝟙 x) q
    have hq : (H.evaluationArrowEquiv V x y q).1 = f := evaluationArrowEquiv_symm_val H V f
    simpa only [Deformation.GroupoidInFunctors.identity, hq, Category.id_comp] using hcomp.symm
  have he' : (groupoidCompose G a (identityAfterSource G a)
      (identityAfterSource_composable G a)).app V t =
      H.compose V f (H.identity V x) wid := by
    simpa only [H, toGroupoidInFunctors, hid, f] using groupoidCompose_eval G
      a (identityAfterSource G a) (identityAfterSource_composable G a) V t
  exact he'.trans hunit

/-- A generalized arrow composed after its inverse is the identity at its target. -/
theorem groupoidCompose_inverseLeft (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj) :
    groupoidCompose G a (a ≫ groupoidInverse G) (by
      calc
        a ≫ G.source.hom = a ≫ (groupoidInverse G ≫ G.target.hom) := by
          rw [groupoidInverse_target]
        _ = (a ≫ groupoidInverse G) ≫ G.target.hom := (Category.assoc _ _ _).symm) =
      identityAfterTarget G a := by
  have w : a ≫ G.source.hom = (a ≫ groupoidInverse G) ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_target]
  ext V t
  let H := G.toGroupoidInFunctors
  let _ : Groupoid (H.objects.obj V) := H.evaluationGroupoid V
  let f := a.app V t
  let x := H.source.app V f
  let y := H.target.app V f
  let q := (H.evaluationArrowEquiv V x y).symm ⟨f, rfl, rfl⟩
  let qi := Groupoid.inv q
  have wpoint : H.source.app V f = H.target.app V ((groupoidInverse G).app V f) :=
    (congrArg (fun k => (k.app V) f) (groupoidInverse_target G)).symm
  have hq : (H.evaluationArrowEquiv V x y q).1 = f := evaluationArrowEquiv_symm_val H V f
  have hi : (H.evaluationArrowEquiv V y x qi).1 = (groupoidInverse G).app V f :=
    evaluationArrowEquiv_inv_val G V f
  have hc' : H.compose V f ((groupoidInverse G).app V f) wpoint =
      (H.evaluationArrowEquiv V y y (qi ≫ q)).1 := by
    simpa only [hq, hi] using (H.evaluationArrowEquiv_comp V qi q).symm
  have hcId : (H.evaluationArrowEquiv V y y (qi ≫ q)).1 =
      (H.evaluationArrowEquiv V y y (𝟙 y)).1 :=
    congrArg (fun e => (H.evaluationArrowEquiv V y y e).1) (Groupoid.inv_comp q)
  have he' : (groupoidCompose G a (a ≫ groupoidInverse G) w).app V t =
      H.compose V f ((groupoidInverse G).app V f) wpoint := by
    simpa only [H, toGroupoidInFunctors, NatTrans.comp_app,
      ConcreteCategory.comp_apply, f] using
        groupoidCompose_eval G a (a ≫ groupoidInverse G) w V t
  exact he'.trans ((hc'.trans hcId).trans (identityAfterTarget_app G a V t).symm)

/-- The inverse of a generalized arrow composed after it is the identity at its source. -/
theorem groupoidCompose_inverseRight (G : GroupoidInAlgebraicSpaces C S hS B)
    {T : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (a : T ⟶ G.arrows.obj) :
    groupoidCompose G (a ≫ groupoidInverse G) a (by
      calc
        (a ≫ groupoidInverse G) ≫ G.source.hom =
            a ≫ (groupoidInverse G ≫ G.source.hom) := Category.assoc _ _ _
        _ = a ≫ G.target.hom := by rw [groupoidInverse_source]) =
      identityAfterSource G a := by
  have w : (a ≫ groupoidInverse G) ≫ G.source.hom = a ≫ G.target.hom := by
    rw [Category.assoc, groupoidInverse_source]
  ext V t
  let H := G.toGroupoidInFunctors
  let _ : Groupoid (H.objects.obj V) := H.evaluationGroupoid V
  let f := a.app V t
  let x := H.source.app V f
  let y := H.target.app V f
  let q := (H.evaluationArrowEquiv V x y).symm ⟨f, rfl, rfl⟩
  let qi := Groupoid.inv q
  have wpoint : H.source.app V ((groupoidInverse G).app V f) = H.target.app V f :=
    congrArg (fun k => (k.app V) f) (groupoidInverse_source G)
  have hq : (H.evaluationArrowEquiv V x y q).1 = f := evaluationArrowEquiv_symm_val H V f
  have hi : (H.evaluationArrowEquiv V y x qi).1 = (groupoidInverse G).app V f :=
    evaluationArrowEquiv_inv_val G V f
  have hc' : H.compose V ((groupoidInverse G).app V f) f wpoint =
      (H.evaluationArrowEquiv V x x (q ≫ qi)).1 := by
    simpa only [hi, hq] using (H.evaluationArrowEquiv_comp V q qi).symm
  have hcId : (H.evaluationArrowEquiv V x x (q ≫ qi)).1 =
      (H.evaluationArrowEquiv V x x (𝟙 x)).1 :=
    congrArg (fun e => (H.evaluationArrowEquiv V x x e).1) (Groupoid.comp_inv q)
  have he' : (groupoidCompose G (a ≫ groupoidInverse G) a w).app V t =
      H.compose V ((groupoidInverse G).app V f) f wpoint := by
    simpa only [H, toGroupoidInFunctors, NatTrans.comp_app,
      ConcreteCategory.comp_apply, f] using
        groupoidCompose_eval G (a ≫ groupoidInverse G) a w V t
  exact he'.trans ((hc'.trans hcId).trans (identityAfterSource_app G a V t).symm)

end AlgebraicGeometry.GroupoidInAlgebraicSpaces
