module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.WithSection

/-!
# The finite part of a groupoid in algebraic spaces

Let `(U, R, s, t, c, e, i)` be a groupoid in algebraic spaces over an algebraic space `B` over
a scheme `S`, and assume `s` and `t` are separated and locally of finite type. Writing `R_s`
for `R` seen over `U` through `s`, the finite part `U' = (R_s/U, e)_fin` is an algebraic space
étale over `U`, and inside `R ×_{s, U, g} U'` there is a universal open and closed subspace
`Z_univ` finite over `U'` which contains the base change of the unit. These two spaces carry a
groupoid structure `(U', Z_univ, s', t', c')` with a morphism of groupoids to `(U, R, s, t, c)`.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartUniversalOpen`: the two structure spaces of the finite
  part of a groupoid, with the identification of the object space with `(R_s/U, e)_fin` and of
  the arrow space with the universal finite open subspace.
* `AlgebraicGeometry.Space.FinitePartGroupoid`: those two spaces assembled into a groupoid in
  algebraic spaces over `B`, together with its morphism of groupoids to the given one.

## Main results

* `AlgebraicGeometry.Space.finitePartUniversalOpen`: **Stacks 04RU, clauses (1) and (2)**, the
  construction of those two spaces for a groupoid whose source and target are separated and
  locally of finite type.
* `AlgebraicGeometry.Space.nonempty_finitePartGroupoid`: **Stacks 04RU, clause (3)**, the
  construction of the groupoid on the finite part and of its morphism to the given groupoid.
* `AlgebraicGeometry.Space.finitePartGroupoid` and
  `AlgebraicGeometry.Space.finitePartGroupoidHom`: **Stacks 04RU**, that groupoid and that
  canonical morphism of groupoids as named constructions, with
  `AlgebraicGeometry.Space.finitePartGroupoid_arrows`,
  `AlgebraicGeometry.Space.finitePartGroupoid_source` and
  `AlgebraicGeometry.Space.finitePartGroupoidHom_mapArrows` identifying the arrow space with
  `Z_univ` and the arrow map with the projection `Z_univ ⊂ R ×_{s, U, g} U' ⟶ R`.

## Implementation notes

The object space is the section-containing open subspace `(R_s/U, e)_fin` of the finite part of
`s`, which is an algebraic space by Stacks 04QH and an open subspace by Stacks 04RR, and the
projection to `U` is étale as the composite of an open immersion with the étale projection of
Stacks 04QH. The arrow space is the open subspace of the pair of Stacks 04PC which corresponds,
under the bijection of Stacks 04PE, to the inclusion of the object space into the finite part of
`s`; it is closed by Stacks 04PH, and it contains the base change of the unit because every one
of its sections does.

The unit `e` is not a field of a groupoid in algebraic spaces here; it is the unique morphism
inducing the identity arrow at every test-scheme point, which is why it appears as a field
together with its characterisation.

The new target `t'` is obtained from the bijection of Stacks 04PE: translating a finite open
pair in the source fibre of an arrow `z` by `z` itself, which is an isomorphism of fibre
products built from the pointwise composition of Stacks 06K5, carries the universal pair over
`Z_univ` to another pair containing the unit, and the morphism it classifies lands in
`(R_s/U, e)_fin`. Composition `c'`, the identity and the inverse are likewise obtained by
lifting the pointwise operations of `R`, each lift being unique because an arrow of `Z_univ` is
determined by its source and its image in `R`.

## References

* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
* [Stacks Project, Tag 04PE](https://stacks.math.columbia.edu/tag/04PE)
* [Stacks Project, Tag 04PH](https://stacks.math.columbia.edu/tag/04PH)
* [Stacks Project, Tag 04QH](https://stacks.math.columbia.edu/tag/04QH)
* [Stacks Project, Tag 04RR](https://stacks.math.columbia.edu/tag/04RR)
* [Stacks Project, Tag 06K5](https://stacks.math.columbia.edu/tag/06K5)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space

/-- Discrete limits of presheaves on the big fppf site, given directly: instance search for
them times out under Lean v4.35.0. -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_finitePartGroupoid
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} (J : Type) :
    HasLimitsOfShape (Discrete J) ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- Pullbacks of presheaves on the big fppf site, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_finitePartGroupoid
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S} :
    HasPullbacks ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_finitePartGroupoid
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  hasPullbacks_presheaf_finitePartGroupoid.has_limit _

private noncomputable def identityArrow
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)) :
    H.objects ⟶ H.arrows := (Deformation.existsUnique_identity H).choose

private theorem identityArrow_spec
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)) :
    ∀ T x, (identityArrow H).app T x = H.identity T x :=
  (Deformation.existsUnique_identity H).choose_spec.1

private noncomputable def identitySection
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B) : G.objects ⟶ G.arrows :=
  ObjectProperty.homMk (identityArrow G.toGroupoidInFunctors)

/-- The identity arrow at `x` has source and target `x`. -/
private theorem identityArrow_source_target
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T) (x) : H.source.app T ((identityArrow H).app T x) = x ∧
      H.target.app T ((identityArrow H).app T x) = x := by
  let : Groupoid (H.objects.obj T) := H.evaluationGroupoid T
  rw [identityArrow_spec H T x]
  exact (H.evaluationArrowEquiv T x x (𝟙 x)).2

private theorem identitySection_source
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B) :
    (identitySection G).hom ≫ G.source.hom = 𝟙 G.objects.obj := by
  ext V x
  exact (identityArrow_source_target G.toGroupoidInFunctors V x).1

private theorem identitySection_spec
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B) :
    ∀ T x, (identitySection G).hom.app T x =
      G.toGroupoidInFunctors.identity T x :=
  fun T x => identityArrow_spec G.toGroupoidInFunctors T x

private theorem identitySection_target
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B) :
    (identitySection G).hom ≫ G.target.hom = 𝟙 G.objects.obj := by
  ext V x
  exact (identityArrow_source_target G.toGroupoidInFunctors V x).2

private abbrev EvalHom
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x y : H.Evaluation T) :=
  @Quiver.Hom (H.Evaluation T) (H.evaluationGroupoid T).toCategory.toQuiver x y




/-- The source and target of a composite arrow. -/
private theorem groupoidCompose_source_target
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : H.arrows.obj T)
    (h : H.source.app T a = H.target.app T b) :
    H.source.app T (H.compose T a b h) = H.source.app T b ∧
      H.target.app T (H.compose T a b h) = H.target.app T a := by
  let : Groupoid (H.Evaluation T) := H.evaluationGroupoid T
  let bHom : EvalHom H T (H.source.app T b) (H.target.app T b) :=
    (H.evaluationArrowEquiv T _ _).symm ⟨b, rfl, rfl⟩
  let aHom : EvalHom H T (H.target.app T b) (H.target.app T a) :=
    (H.evaluationArrowEquiv T _ _).symm ⟨a, h, rfl⟩
  have hmem := (H.evaluationArrowEquiv T _ _ (bHom ≫ aHom)).2
  rw [H.evaluationArrowEquiv_comp] at hmem
  simpa only [aHom, bHom, Equiv.apply_symm_apply] using hmem

private theorem groupoidCompose_source
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : H.arrows.obj T)
    (h : H.source.app T a = H.target.app T b) :
    H.source.app T (H.compose T a b h) = H.source.app T b :=
  (groupoidCompose_source_target H T a b h).1

private theorem groupoidCompose_target
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : H.arrows.obj T)
    (h : H.source.app T a = H.target.app T b) :
    H.target.app T (H.compose T a b h) = H.target.app T a :=
  (groupoidCompose_source_target H T a b h).2

private theorem groupoidCompose_identity_left
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : H.arrows.obj T)
    (hid : H.source.app T (H.identity T (H.target.app T a)) = H.target.app T a) :
    H.compose T (H.identity T (H.target.app T a)) a
      (hid.trans rfl) = a := by
  let := H.evaluationGroupoid T
  let x := H.source.app T a
  let y := H.target.app T a
  let f : EvalHom H T x y :=
    (H.evaluationArrowEquiv T x y).symm ⟨a, rfl, rfl⟩
  have h := congrArg
    (fun g : EvalHom H T x y => (H.evaluationArrowEquiv T x y g).1)
    (Category.comp_id f)
  rw [H.evaluationArrowEquiv_comp] at h
  simpa only [f, H.evaluationArrowEquiv_id, Equiv.apply_symm_apply] using h

/-- The source and target of an inverse arrow. -/
private theorem inverseArrow_source_target_functor
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : H.arrows.obj T) :
    H.source.app T (Deformation.inverseArrow H T a) = H.target.app T a ∧
      H.target.app T (Deformation.inverseArrow H T a) = H.source.app T a := by
  let := H.evaluationGroupoid T
  exact (H.evaluationArrowEquiv T (H.target.app T a) (H.source.app T a)
    (Groupoid.inv ((H.evaluationArrowEquiv T (H.source.app T a)
      (H.target.app T a)).symm ⟨a, rfl, rfl⟩))).2

private theorem inverseArrow_source_functor
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : H.arrows.obj T) :
    H.source.app T (Deformation.inverseArrow H T a) = H.target.app T a :=
  (inverseArrow_source_target_functor H T a).1

private theorem inverseArrow_target_functor
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : H.arrows.obj T) :
    H.target.app T (Deformation.inverseArrow H T a) = H.source.app T a :=
  (inverseArrow_source_target_functor H T a).2

/-- Composition with an identity arrow on the right fixes an arrow. -/
private theorem groupoidCompose_identity_right
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : H.arrows.obj T)
    (h : H.source.app T a = H.target.app T (H.identity T (H.source.app T a))) :
    H.compose T a (H.identity T (H.source.app T a)) h = a := by
  let := H.evaluationGroupoid T
  let f := (H.evaluationArrowEquiv T _ _).symm
    (⟨a, rfl, rfl⟩ : {r // H.source.app T r = H.source.app T a ∧
      H.target.app T r = H.target.app T a})
  have hi := congrArg (fun k => (H.evaluationArrowEquiv T _ _ k).val) (Category.id_comp f)
  simpa only [H.evaluationArrowEquiv_comp, H.evaluationArrowEquiv_id,
    f, Equiv.apply_symm_apply] using hi

private theorem groupoidCompose_assoc
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b c : H.arrows.obj T)
    (hab : H.source.app T a = H.target.app T b)
    (hbc : H.source.app T b = H.target.app T c)
    (h₁ : H.source.app T (H.compose T a b hab) = H.target.app T c)
    (h₂ : H.source.app T a = H.target.app T (H.compose T b c hbc)) :
    H.compose T (H.compose T a b hab) c h₁ =
      H.compose T a (H.compose T b c hbc) h₂ := by
  let := H.evaluationGroupoid T
  let fa := (H.evaluationArrowEquiv T _ _).symm
    (⟨a, hab, rfl⟩ : {r // H.source.app T r = H.target.app T b ∧
      H.target.app T r = H.target.app T a})
  let fb := (H.evaluationArrowEquiv T _ _).symm
    (⟨b, hbc, rfl⟩ : {r // H.source.app T r = H.target.app T c ∧
      H.target.app T r = H.target.app T b})
  let fc := (H.evaluationArrowEquiv T _ _).symm
    (⟨c, rfl, rfl⟩ : {r // H.source.app T r = H.source.app T c ∧
      H.target.app T r = H.target.app T c})
  have h := congrArg (fun k => (H.evaluationArrowEquiv T _ _ k).val)
    (Category.assoc fc fb fa)
  simpa only [H.evaluationArrowEquiv_comp, fa, fb, fc, Equiv.apply_symm_apply] using h.symm

private theorem groupoidCompose_inverse_left
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : H.arrows.obj T)
    (h : H.source.app T (Deformation.inverseArrow H T a) = H.target.app T a) :
    H.compose T (Deformation.inverseArrow H T a) a h =
      H.identity T (H.source.app T a) := by
  let := H.evaluationGroupoid T
  let f := (H.evaluationArrowEquiv T _ _).symm
    (⟨a, rfl, rfl⟩ : {r // H.source.app T r = H.source.app T a ∧
      H.target.app T r = H.target.app T a})
  have hi := congrArg (fun k => (H.evaluationArrowEquiv T _ _ k).val) (Groupoid.comp_inv f)
  simpa only [H.evaluationArrowEquiv_comp, H.evaluationArrowEquiv_id,
    f, Deformation.inverseArrow, Equiv.apply_symm_apply] using hi

private noncomputable def translateArrow
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : H.arrows.obj T) (hab : H.source.app T b = H.source.app T a) :
    H.arrows.obj T :=
  H.compose T b (Deformation.inverseArrow H T a)
    (hab.trans (inverseArrow_target_functor H T a).symm)

private theorem translateArrow_congr_args
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    {a a' b b' : H.arrows.obj T} (ha : a = a') (hb : b = b')
    (hab : H.source.app T b = H.source.app T a)
    (hab' : H.source.app T b' = H.source.app T a') :
    translateArrow H T a b hab = translateArrow H T a' b' hab' := by
  subst ha hb
  rfl

private theorem translateArrow_source
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : H.arrows.obj T) (hab : H.source.app T b = H.source.app T a) :
    H.source.app T (translateArrow H T a b hab) = H.target.app T a := by
  dsimp [translateArrow]
  rw [groupoidCompose_source]
  exact inverseArrow_source_functor H T a

private theorem translateArrow_target
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : H.arrows.obj T) (hab : H.source.app T b = H.source.app T a) :
    H.target.app T (translateArrow H T a b hab) = H.target.app T b := by
  dsimp [translateArrow]
  rw [groupoidCompose_target]

private theorem groupoidCompose_natural
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {T T' : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ} (f : T ⟶ T')
    (a b : H.arrows.obj T) (h : H.source.app T a = H.target.app T b)
    (h' : H.source.app T' (H.arrows.map f a) =
      H.target.app T' (H.arrows.map f b)) :
    H.arrows.map f (H.compose T a b h) =
      H.compose T' (H.arrows.map f a) (H.arrows.map f b) h' := by
  let D := Deformation.composableArrows H.objects H.arrows H.source H.target
  let p : D.obj T := ⟨(a, b), h⟩
  let p' : D.obj T' := ⟨(H.arrows.map f a, H.arrows.map f b), h'⟩
  have hpm : D.map f p = p' := Subtype.ext rfl
  have hn := NatTrans.naturality_apply H.comp f p
  rw [hpm] at hn
  simpa only [Deformation.GroupoidInFunctors.compose] using hn.symm

private theorem groupoidCompose_natural_of_eq
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {T T' : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ} (f : T ⟶ T')
    (a b : H.arrows.obj T) (a' b' : H.arrows.obj T')
    (h : H.source.app T a = H.target.app T b)
    (h' : H.source.app T' a' = H.target.app T' b')
    (ha : H.arrows.map f a = a') (hb : H.arrows.map f b = b') :
    H.arrows.map f (H.compose T a b h) = H.compose T' a' b' h' := by
  subst a'
  subst b'
  exact groupoidCompose_natural H f a b h h'

private theorem groupoidCompose_congr_second
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b b' : H.arrows.obj T) (h : H.source.app T a = H.target.app T b)
    (h' : H.source.app T a = H.target.app T b') (e : b = b') :
    H.compose T a b h = H.compose T a b' h' := by
  cases e
  rfl

private theorem groupoidCompose_congr_first
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a a' b : H.arrows.obj T) (h : H.source.app T a = H.target.app T b)
    (h' : H.source.app T a' = H.target.app T b) (e : a = a') :
    H.compose T a b h = H.compose T a' b h' := by
  cases e
  rfl


private theorem translateArrow_self
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : H.arrows.obj T) :
    translateArrow H T a a rfl = H.identity T (H.target.app T a) := by
  let := H.evaluationGroupoid T
  let x := H.source.app T a
  let y := H.target.app T a
  let f : EvalHom H T x y :=
    (H.evaluationArrowEquiv T x y).symm ⟨a, rfl, rfl⟩
  have h := congrArg
    (fun g : EvalHom H T y y => (H.evaluationArrowEquiv T y y g).1)
    (Groupoid.inv_comp f)
  show H.compose T a (Deformation.inverseArrow H T a) _ = H.identity T y
  simpa only [H.evaluationArrowEquiv_comp,
    H.evaluationArrowEquiv_id, Deformation.GroupoidInFunctors.compose,
    Deformation.inverseArrow, x, y, f, Equiv.apply_symm_apply] using h

private theorem translateArrow_cancel
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a b : H.arrows.obj T) (hab : H.source.app T b = H.source.app T a) :
    H.compose T (translateArrow H T a b hab) a
      (translateArrow_source H T a b hab) = b := by
  let := H.evaluationGroupoid T
  let x := H.source.app T a
  let y := H.target.app T a
  let z := H.target.app T b
  let f : EvalHom H T x y :=
    (H.evaluationArrowEquiv T x y).symm ⟨a, rfl, rfl⟩
  let g : EvalHom H T x z :=
    (H.evaluationArrowEquiv T x z).symm ⟨b, hab, rfl⟩
  let c := translateArrow H T a b hab
  let cHom : EvalHom H T y z :=
    (H.evaluationArrowEquiv T y z).symm
      ⟨c, translateArrow_source H T a b hab, translateArrow_target H T a b hab⟩
  have hc : cHom = Groupoid.inv f ≫ g := by
    apply (H.evaluationArrowEquiv T y z).injective
    apply Subtype.ext
    simp only [cHom, Equiv.apply_symm_apply]
    show c = (H.evaluationArrowEquiv T y z (Groupoid.inv f ≫ g)).1
    rw [H.evaluationArrowEquiv_comp]
    simp only [g, Equiv.apply_symm_apply]
    show H.compose T b (Deformation.inverseArrow H T a) _ =
      H.compose T b (H.evaluationArrowEquiv T y x (Groupoid.inv f)).1 _
    exact groupoidCompose_congr_second H T b _ _ _ _ (by rfl)
  have hfc : f ≫ cHom = g := by
    rw [hc, ← Category.assoc, Groupoid.comp_inv, Category.id_comp]
  let d := H.compose T c a (translateArrow_source H T a b hab)
  have hdsource : H.source.app T d = x := by
    dsimp [d]
    rw [groupoidCompose_source]
  have hdtarget : H.target.app T d = z := by
    dsimp [d]
    rw [groupoidCompose_target]
    exact translateArrow_target H T a b hab
  have hdc :
      (H.evaluationArrowEquiv T x z).symm ⟨d, hdsource, hdtarget⟩ = f ≫ cHom := by
    apply (H.evaluationArrowEquiv T x z).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    simpa only [cHom, f, Equiv.apply_symm_apply] using
      (H.evaluationArrowEquiv_comp T f cHom).symm
  have hcat := hdc.trans hfc
  have hval := congrArg
    (fun k : EvalHom H T x z => (H.evaluationArrowEquiv T x z k).1) hcat
  simpa only [Equiv.apply_symm_apply, g] using hval

private noncomputable def translateBackArrow
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a c : H.arrows.obj T) (hac : H.source.app T c = H.target.app T a) :
    H.arrows.obj T := H.compose T c a hac

private theorem translateBackArrow_source
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a c : H.arrows.obj T) (hac : H.source.app T c = H.target.app T a) :
    H.source.app T (translateBackArrow H T a c hac) = H.source.app T a :=
  groupoidCompose_source H T c a hac

private theorem translateBackArrow_target
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a c : H.arrows.obj T) (hac : H.source.app T c = H.target.app T a) :
    H.target.app T (translateBackArrow H T a c hac) = H.target.app T c :=
  groupoidCompose_target H T c a hac


private theorem translateArrow_back_cancel
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a c : H.arrows.obj T) (hac : H.source.app T c = H.target.app T a) :
    translateArrow H T a (translateBackArrow H T a c hac)
      (translateBackArrow_source H T a c hac) = c := by
  let := H.evaluationGroupoid T
  let x := H.source.app T a
  let y := H.target.app T a
  let z := H.target.app T c
  let f : EvalHom H T x y :=
    (H.evaluationArrowEquiv T x y).symm ⟨a, rfl, rfl⟩
  let g : EvalHom H T y z :=
    (H.evaluationArrowEquiv T y z).symm ⟨c, hac, rfl⟩
  let d := translateBackArrow H T a c hac
  let dHom : EvalHom H T x z :=
    (H.evaluationArrowEquiv T x z).symm
      ⟨d, translateBackArrow_source H T a c hac,
        translateBackArrow_target H T a c hac⟩
  have hd : dHom = f ≫ g := by
    apply (H.evaluationArrowEquiv T x z).injective
    apply Subtype.ext
    simp only [dHom, Equiv.apply_symm_apply]
    show d = (H.evaluationArrowEquiv T x z (f ≫ g)).1
    rw [H.evaluationArrowEquiv_comp]
    simp only [g, f, Equiv.apply_symm_apply]
    rfl
  have hcancel : Groupoid.inv f ≫ dHom = g := by
    rw [hd, ← Category.assoc, Groupoid.inv_comp, Category.id_comp]
  let e := translateArrow H T a d (translateBackArrow_source H T a c hac)
  have hesource : H.source.app T e = y := translateArrow_source H T a d _
  have hetarget : H.target.app T e = z := by
    dsimp [e]
    rw [translateArrow_target]
    exact translateBackArrow_target H T a c hac
  have heHom :
      (H.evaluationArrowEquiv T y z).symm ⟨e, hesource, hetarget⟩ = Groupoid.inv f ≫ dHom := by
    apply (H.evaluationArrowEquiv T y z).injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]
    show e = (H.evaluationArrowEquiv T y z (Groupoid.inv f ≫ dHom)).1
    rw [H.evaluationArrowEquiv_comp]
    simp only [dHom, Equiv.apply_symm_apply]
    dsimp [e, translateArrow]
    exact groupoidCompose_congr_second H T d _ _ _ _ (by rfl)
  have hcat := heHom.trans hcancel
  have hval := congrArg
    (fun k : EvalHom H T y z => (H.evaluationArrowEquiv T y z k).1) hcat
  simpa only [Equiv.apply_symm_apply, g] using hval

private noncomputable def fiberTranslatePair
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    pullback (z ≫ H.source) H.source ⟶
      Deformation.composableArrows H.objects H.arrows H.source H.target := by
  let inv := (Deformation.existsUnique_inverse H).choose
  let fst := pullback.fst (z ≫ H.source) H.source
  let snd := pullback.snd (z ≫ H.source) H.source
  refine {
    app T := ↾ fun p => ⟨(snd.app T p, inv.app T (z.app T (fst.app T p))), ?_⟩
    naturality := by
      intro T T' f
      ext p
      apply Subtype.ext
      dsimp [Deformation.composableArrows]
      change (snd.app T' ((pullback (z ≫ H.source) H.source).map f p),
          inv.app T' (z.app T' (fst.app T' ((pullback (z ≫ H.source) H.source).map f p)))) =
        (H.arrows.map f (snd.app T p),
          H.arrows.map f (inv.app T (z.app T (fst.app T p))))
      apply Prod.ext
      · exact NatTrans.naturality_apply snd f p
      · calc
          inv.app T' (z.app T' (fst.app T' ((pullback (z ≫ H.source)
              H.source).map f p))) =
              inv.app T' (z.app T' (A.map f (fst.app T p))) := by
            rw [NatTrans.naturality_apply fst]
          _ = inv.app T' (H.arrows.map f (z.app T (fst.app T p))) := by
            rw [NatTrans.naturality_apply z]
          _ = H.arrows.map f (inv.app T (z.app T (fst.app T p))) :=
            NatTrans.naturality_apply inv f (z.app T (fst.app T p))
  }
  · change H.source.app T (snd.app T p) =
      H.target.app T (inv.app T (z.app T (fst.app T p)))
    have hpb : fst ≫ (z ≫ H.source) = snd ≫ H.source := pullback.condition
    have hp := congrArg (fun k => k.app T p) hpb
    change H.source.app T (z.app T (fst.app T p)) = H.source.app T (snd.app T p) at hp
    calc
      H.source.app T (snd.app T p) = H.source.app T (z.app T (fst.app T p)) := hp.symm
      _ = H.target.app T (Deformation.inverseArrow H T
          (z.app T (fst.app T p))) :=
        (inverseArrow_target_functor H T (z.app T (fst.app T p))).symm
      _ = H.target.app T (inv.app T (z.app T (fst.app T p))) :=
        congrArg (H.target.app T)
          ((Deformation.existsUnique_inverse H).choose_spec.1 T
            (z.app T (fst.app T p))).symm

/-- Right translation by the inverse of an arrow sends its source fibre at the
arrow's source to its source fibre at the arrow's target: `w ↦ w ∘ z⁻¹`. -/
private noncomputable def fiberTranslate
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    pullback (z ≫ H.source) H.source ⟶ pullback (z ≫ H.target) H.source := by
  let pair := fiberTranslatePair H z
  refine pullback.lift (pullback.fst (z ≫ H.source) H.source)
    (pair ≫ H.comp) ?_
  ext T p
  change H.target.app T (z.app T ((pullback.fst (z ≫ H.source) H.source).app T p)) =
    H.source.app T ((pair ≫ H.comp).app T p)
  change _ = H.source.app T
      (H.compose T ((pullback.snd (z ≫ H.source) H.source).app T p)
        ((Deformation.existsUnique_inverse H).choose.app T
          (z.app T ((pullback.fst (z ≫ H.source) H.source).app T p))) _)
  rw [groupoidCompose_source]
  rw [(Deformation.existsUnique_inverse H).choose_spec.1 T
    (z.app T ((pullback.fst (z ≫ H.source) H.source).app T p))]
  exact (inverseArrow_source_functor H T
    (z.app T ((pullback.fst (z ≫ H.source) H.source).app T p))).symm

private noncomputable def fiberTranslateBackPair
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    pullback (z ≫ H.target) H.source ⟶
      Deformation.composableArrows H.objects H.arrows H.source H.target := by
  let fst := pullback.fst (z ≫ H.target) H.source
  let snd := pullback.snd (z ≫ H.target) H.source
  refine {
    app T := ↾ fun p => ⟨(snd.app T p, z.app T (fst.app T p)), ?_⟩
    naturality := by
      intro T T' f
      ext p
      apply Subtype.ext
      dsimp [Deformation.composableArrows]
      change (snd.app T' ((pullback (z ≫ H.target) H.source).map f p),
          z.app T' (fst.app T' ((pullback (z ≫ H.target) H.source).map f p))) =
        (H.arrows.map f (snd.app T p), H.arrows.map f (z.app T (fst.app T p)))
      apply Prod.ext
      · exact NatTrans.naturality_apply snd f p
      · calc
          z.app T' (fst.app T' ((pullback (z ≫ H.target) H.source).map f p)) =
              z.app T' (A.map f (fst.app T p)) := by
            rw [NatTrans.naturality_apply fst]
          _ = H.arrows.map f (z.app T (fst.app T p)) :=
            NatTrans.naturality_apply z f (fst.app T p)
  }
  · change H.source.app T (snd.app T p) = H.target.app T (z.app T (fst.app T p))
    have hpb : fst ≫ (z ≫ H.target) = snd ≫ H.source := pullback.condition
    have hp := congrArg (fun k => k.app T p) hpb
    change H.target.app T (z.app T (fst.app T p)) = H.source.app T (snd.app T p) at hp
    exact hp.symm

private noncomputable def fiberTranslateBack
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    pullback (z ≫ H.target) H.source ⟶ pullback (z ≫ H.source) H.source := by
  let pair := fiberTranslateBackPair H z
  refine pullback.lift (pullback.fst (z ≫ H.target) H.source)
    (pair ≫ H.comp) ?_
  ext T p
  change H.source.app T (z.app T ((pullback.fst (z ≫ H.target) H.source).app T p)) =
    H.source.app T ((pair ≫ H.comp).app T p)
  change _ = H.source.app T
      (H.compose T ((pullback.snd (z ≫ H.target) H.source).app T p)
        (z.app T ((pullback.fst (z ≫ H.target) H.source).app T p)) _)
  rw [groupoidCompose_source]

/-- `fiberTranslate` commutes with the first projections. -/
private theorem fiberTranslate_fst
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    fiberTranslate H z ≫ pullback.fst (z ≫ H.target) H.source =
      pullback.fst (z ≫ H.source) H.source :=
  pullback.lift_fst _ _ _

/-- The second projection of `fiberTranslate` is composition of the pair it builds. -/
private theorem fiberTranslate_comp_snd
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    fiberTranslate H z ≫ pullback.snd (z ≫ H.target) H.source =
      fiberTranslatePair H z ≫ H.comp :=
  pullback.lift_snd _ _ _

/-- `fiberTranslateBack` commutes with the first projections. -/
private theorem fiberTranslateBack_fst
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    fiberTranslateBack H z ≫ pullback.fst (z ≫ H.source) H.source =
      pullback.fst (z ≫ H.target) H.source :=
  pullback.lift_fst _ _ _

/-- The second projection of `fiberTranslateBack` is composition of the pair it builds. -/
private theorem fiberTranslateBack_comp_snd
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    fiberTranslateBack H z ≫ pullback.snd (z ≫ H.source) H.source =
      fiberTranslateBackPair H z ≫ H.comp :=
  pullback.lift_snd _ _ _

/-- The section of the second projection of `pullback (z ≫ H.target) H.source` given by the unit
at the target of `z`. -/
private noncomputable def unitOverTarget
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows)
    (unit : H.objects ⟶ H.arrows) (hunit : unit ≫ H.source = 𝟙 H.objects) :
    A ⟶ pullback (z ≫ H.target) H.source :=
  pullback.lift (𝟙 A) ((z ≫ H.target) ≫ unit) (by
    calc
      𝟙 A ≫ (z ≫ H.target) = z ≫ H.target := by simp
      _ = (z ≫ H.target) ≫ (unit ≫ H.source) := by rw [hunit]; simp
      _ = ((z ≫ H.target) ≫ unit) ≫ H.source := by simp [Category.assoc])

private theorem fiberTranslateBack_unit_comp
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows)
    (unit : H.objects ⟶ H.arrows)
    (hunit : unit ≫ H.source = 𝟙 H.objects)
    (hunit_spec : ∀ V x, unit.app V x = H.identity V x) :
    unitOverTarget H z unit hunit ≫ fiberTranslateBackPair H z ≫ H.comp = z := by
  let targetPair := unitOverTarget H z unit hunit
  ext T x
  have hfst : (pullback.fst (z ≫ H.target) H.source).app T (targetPair.app T x) = x := by
    have h := congrArg (fun k => k.app T) (pullback.lift_fst _ _ _ :
      targetPair ≫ pullback.fst (z ≫ H.target) H.source = 𝟙 _)
    exact congrArg (fun k => k x) h
  have hsnd : (pullback.snd (z ≫ H.target) H.source).app T (targetPair.app T x) =
      unit.app T (H.target.app T (z.app T x)) := by
    have h := congrArg (fun k => k.app T) (pullback.lift_snd _ _ _ :
      targetPair ≫ pullback.snd (z ≫ H.target) H.source = (z ≫ H.target) ≫ unit)
    simpa only [targetPair, unitOverTarget, NatTrans.comp_app, CategoryTheory.hom_comp,
      Function.comp_apply] using congrArg (fun k => k x) h
  let : Groupoid (H.objects.obj T) := H.evaluationGroupoid T
  let y := H.target.app T (z.app T x)
  have hunitSource : H.source.app T (unit.app T y) = y := by
    rw [hunit_spec]
    exact (H.evaluationArrowEquiv T y y (𝟙 y)).2.1
  have hpair : (fiberTranslateBackPair H z).app T (targetPair.app T x) =
      ⟨(unit.app T y, z.app T x), hunitSource⟩ := by
    apply Subtype.ext
    show ((pullback.snd (z ≫ H.target) H.source).app T (targetPair.app T x),
      z.app T ((pullback.fst (z ≫ H.target) H.source).app T (targetPair.app T x))) = _
    exact Prod.ext hsnd (congrArg (z.app T) hfst)
  show H.comp.app T
      ((fiberTranslateBackPair H z).app T (targetPair.app T x)) = z.app T x
  rw [hpair]
  show H.compose T (unit.app T (H.target.app T (z.app T x))) (z.app T x) _ =
    z.app T x
  calc
    H.compose T (unit.app T y) (z.app T x) _ =
        H.compose T (H.identity T y) (z.app T x) _ :=
      groupoidCompose_congr_first H T (unit.app T y) (H.identity T y) (z.app T x)
        _ _ (hunit_spec T y)
    _ = z.app T x := groupoidCompose_identity_left H T (z.app T x)
      ((H.evaluationArrowEquiv T y y (𝟙 y)).2.1)

private theorem fiberTranslate_snd
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows)
    (T : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (p : (pullback (z ≫ H.source) H.source).obj T) :
    (ConcreteCategory.hom ((pullback.snd (z ≫ H.target) H.source).app T))
        ((ConcreteCategory.hom ((fiberTranslate H z).app T)) p) =
      translateArrow H T (z.app T
        ((ConcreteCategory.hom ((pullback.fst (z ≫ H.source) H.source).app T)) p))
        ((ConcreteCategory.hom ((pullback.snd (z ≫ H.source) H.source).app T)) p)
        (by
          have hpull : pullback.fst (z ≫ H.source) H.source ≫
              (z ≫ H.source) = pullback.snd (z ≫ H.source) H.source ≫ H.source :=
            pullback.condition
          have hp := congrArg (fun k => k.app T p) hpull
          simpa only [NatTrans.comp_app, CategoryTheory.hom_comp,
            Function.comp_apply] using hp.symm)
    := by
  let fstS := pullback.fst (z ≫ H.source) H.source
  let sndS := pullback.snd (z ≫ H.source) H.source
  let sndT := pullback.snd (z ≫ H.target) H.source
  let a := z.app T ((ConcreteCategory.hom (fstS.app T)) p)
  let b := (ConcreteCategory.hom (sndS.app T)) p
  let hb : H.source.app T b = H.source.app T a := by
    have hpb : fstS ≫ (z ≫ H.source) = sndS ≫ H.source := pullback.condition
    have hp := congrArg (fun k => k.app T p) hpb
    change H.source.app T a = H.source.app T b at hp
    exact hp.symm
  have h := congrArg (fun k => k.app T p) (fiberTranslate_comp_snd H z)
  change (ConcreteCategory.hom (sndT.app T))
      ((ConcreteCategory.hom ((fiberTranslate H z).app T)) p) =
    H.comp.app T ((fiberTranslatePair H z).app T p) at h
  have hp : H.comp.app T ((fiberTranslatePair H z).app T p) =
      translateArrow H T a b hb := by
    let inv := (Deformation.existsUnique_inverse H).choose
    have hinv : inv.app T a = Deformation.inverseArrow H T a :=
      (Deformation.existsUnique_inverse H).choose_spec.1 T a
    have htargetInv : H.target.app T (inv.app T a) = H.source.app T a := by
      rw [hinv]
      exact inverseArrow_target_functor H T a
    have hcomp : H.comp.app T ((fiberTranslatePair H z).app T p) =
        H.compose T b (inv.app T a)
          (hb.trans htargetInv.symm) := by
      rfl
    rw [hcomp]
    exact groupoidCompose_congr_second H T b _ _ _ _
      hinv
  dsimp [a,b]
  exact h.trans hp

private theorem fiberTranslate_back_after_forward
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    fiberTranslate H z ≫ fiberTranslateBack H z =
      𝟙 (pullback (z ≫ H.source) H.source) := by
  apply pullback.hom_ext
  · rw [Category.assoc, fiberTranslateBack_fst, fiberTranslate_fst, Category.id_comp]
  · ext T p
    let fstS := pullback.fst (z ≫ H.source) H.source
    let sndS := pullback.snd (z ≫ H.source) H.source
    let fstT := pullback.fst (z ≫ H.target) H.source
    let sndT := pullback.snd (z ≫ H.target) H.source
    let a := z.app T (fstS.app T p)
    let b := sndS.app T p
    have hb : H.source.app T b = H.source.app T a := by
      have hpb : fstS ≫ (z ≫ H.source) = sndS ≫ H.source := pullback.condition
      exact (congrArg (fun k => k.app T p) hpb).symm
    have hfstPoint : fstT.app T ((fiberTranslate H z).app T p) = fstS.app T p :=
      congrArg (fun k => k.app T p) (fiberTranslate_fst H z)
    have htranslated : sndT.app T ((fiberTranslate H z).app T p) =
        translateArrow H T a b hb := fiberTranslate_snd H z T p
    have hout := congrArg (fun k => (k.app T) ((fiberTranslate H z).app T p))
      (fiberTranslateBack_comp_snd H z)
    have hcompose : H.comp.app T
        ((fiberTranslateBackPair H z).app T ((fiberTranslate H z).app T p)) = b := by
      dsimp [fiberTranslateBackPair, Deformation.GroupoidInFunctors.compose]
      have hpull : fstT ≫ (z ≫ H.target) = sndT ≫ H.source := pullback.condition
      have hp' := congrArg (fun k => k.app T ((fiberTranslate H z).app T p)) hpull
      change H.target.app T (z.app T (fstT.app T ((fiberTranslate H z).app T p))) =
          H.source.app T (sndT.app T ((fiberTranslate H z).app T p)) at hp'
      have hfirst : H.source.app T (sndT.app T ((fiberTranslate H z).app T p)) =
          H.target.app T (z.app T (fstT.app T ((fiberTranslate H z).app T p))) := hp'.symm
      have hsecond : H.source.app T (translateArrow H T a b hb) =
          H.target.app T (z.app T (fstT.app T ((fiberTranslate H z).app T p))) := by
        rw [translateArrow_source]
        exact (congrArg (fun v => H.target.app T (z.app T v)) hfstPoint).symm
      have hc : H.compose T (sndT.app T ((fiberTranslate H z).app T p))
          (z.app T (fstT.app T ((fiberTranslate H z).app T p))) hfirst =
          H.compose T (translateArrow H T a b hb)
            (z.app T (fstT.app T ((fiberTranslate H z).app T p))) hsecond :=
        groupoidCompose_congr_first H T _ _ _ hfirst hsecond htranslated
      have hsecond' : H.source.app T (translateArrow H T a b hb) = H.target.app T a :=
        translateArrow_source H T a b hb
      have hza : z.app T (fstT.app T ((fiberTranslate H z).app T p)) = a := by
        dsimp [a]
        exact congrArg (ConcreteCategory.hom (z.app T)) hfstPoint
      have ha : H.compose T (translateArrow H T a b hb)
          (z.app T (fstT.app T ((fiberTranslate H z).app T p))) hsecond =
          H.compose T (translateArrow H T a b hb) a hsecond' :=
        groupoidCompose_congr_second H T _ _ _ hsecond hsecond' hza
      exact hc.trans (ha.trans (translateArrow_cancel H T a b hb))
    change sndS.app T ((fiberTranslateBack H z).app T ((fiberTranslate H z).app T p)) =
      H.comp.app T
        ((fiberTranslateBackPair H z).app T ((fiberTranslate H z).app T p)) at hout
    exact hout.trans hcompose

private theorem fiberTranslate_forward_after_back
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    {A : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (z : A ⟶ H.arrows) :
    fiberTranslateBack H z ≫ fiberTranslate H z =
      𝟙 (pullback (z ≫ H.target) H.source) := by
  apply pullback.hom_ext
  · rw [Category.assoc, fiberTranslate_fst, fiberTranslateBack_fst, Category.id_comp]
  · ext T p
    simp only [NatTrans.comp_app, Category.id_comp]
    let fst := pullback.fst (z ≫ H.target) H.source
    let snd := pullback.snd (z ≫ H.target) H.source
    let fstS := pullback.fst (z ≫ H.source) H.source
    let sndS := pullback.snd (z ≫ H.source) H.source
    let x := (ConcreteCategory.hom (fst.app T)) p
    let a := (ConcreteCategory.hom (z.app T)) x
    let c := (ConcreteCategory.hom (snd.app T)) p
    have hac : H.source.app T c = H.target.app T a := by
      have hpull : fst ≫ (z ≫ H.target) = snd ≫ H.source := pullback.condition
      have hp := congrArg (fun k => k.app T p) hpull
      change H.target.app T a = H.source.app T c at hp
      exact hp.symm
    have hbackfst : (ConcreteCategory.hom (fstS.app T))
        ((ConcreteCategory.hom ((fiberTranslateBack H z).app T)) p) = x := by
      have hh := congrArg (fun k => k.app T p) (fiberTranslateBack_fst H z)
      change (ConcreteCategory.hom (fstS.app T))
          ((ConcreteCategory.hom ((fiberTranslateBack H z).app T)) p) =
        (ConcreteCategory.hom (fst.app T)) p at hh
      exact hh
    have hbacksnd : (ConcreteCategory.hom (sndS.app T))
        ((ConcreteCategory.hom ((fiberTranslateBack H z).app T)) p) =
        translateBackArrow H T a c hac := by
      have hh := congrArg (fun k => k.app T p) (fiberTranslateBack_comp_snd H z)
      change (ConcreteCategory.hom (sndS.app T))
          ((ConcreteCategory.hom ((fiberTranslateBack H z).app T)) p) =
        H.comp.app T ((fiberTranslateBackPair H z).app T p) at hh
      have hv : H.comp.app T ((fiberTranslateBackPair H z).app T p) =
          translateBackArrow H T a c hac := by
        rfl
      exact hh.trans hv
    let q := (ConcreteCategory.hom ((fiberTranslateBack H z).app T)) p
    have htranslated := fiberTranslate_snd H z T q
    have hax : z.app T ((ConcreteCategory.hom (fstS.app T)) q) = a := by
      show (ConcreteCategory.hom (z.app T))
          ((ConcreteCategory.hom (fstS.app T)) q) = a
      dsimp [a,x]
      rw [hbackfst]
    have hbc : (ConcreteCategory.hom (sndS.app T)) q =
        translateBackArrow H T a c hac := hbacksnd
    have hpoint : (ConcreteCategory.hom (snd.app T))
        ((ConcreteCategory.hom ((fiberTranslate H z).app T)) q) =
        translateArrow H T a (translateBackArrow H T a c hac)
          (translateBackArrow_source H T a c hac) := by
      dsimp [q, snd, fstS, sndS] at htranslated ⊢
      dsimp [fstS, sndS] at hax hbc
      have hargs : translateArrow H T
          (z.app T ((ConcreteCategory.hom
            ((pullback.fst (z ≫ H.source) H.source).app T)) q))
          ((ConcreteCategory.hom
            ((pullback.snd (z ≫ H.source) H.source).app T)) q)
          (by
            have hpull : pullback.fst (z ≫ H.source) H.source ≫
                (z ≫ H.source) =
                pullback.snd (z ≫ H.source) H.source ≫ H.source :=
              pullback.condition
            have hp := congrArg (fun k => k.app T q) hpull
            simpa only [NatTrans.comp_app, CategoryTheory.hom_comp,
              Function.comp_apply] using hp.symm) =
          translateArrow H T a (translateBackArrow H T a c hac)
            (translateBackArrow_source H T a c hac) := by
        apply translateArrow_congr_args
        · exact hax
        · exact hbc
      rw [hargs] at htranslated
      exact htranslated
    have htrans : translateArrow H T a (translateBackArrow H T a c hac)
        (translateBackArrow_source H T a c hac) = c :=
      translateArrow_back_cancel H T a c hac
    show (ConcreteCategory.hom (snd.app T))
        ((ConcreteCategory.hom ((fiberTranslate H z).app T))
          ((ConcreteCategory.hom ((fiberTranslateBack H z).app T)) p)) = c
    exact hpoint.trans htrans

private theorem pullback_restrict_isPullback
    {C : Type*} [Category C] {A B D E : C}
    (u : A ⟶ B) (f : B ⟶ D) (g : E ⟶ D)
    [HasPullback (u ≫ f) g] [HasPullback f g] :
    IsPullback
      (pullback.lift
        (pullback.fst (u ≫ f) g ≫ u)
        (pullback.snd (u ≫ f) g)
        (by
          rw [Category.assoc, pullback.condition]))
      (pullback.fst (u ≫ f) g)
      (pullback.fst f g) u :=
  IsPullback.of_right
    (by rw [pullback.lift_snd]; exact (IsPullback.of_hasPullback (u ≫ f) g).flip)
    (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f g).flip

private theorem pullback_congrHom_inv_fst
    {C : Type*} [Category C] {X Y Z : C} {f f' : X ⟶ Z} {g : Y ⟶ Z}
    [HasPullback f g] [HasPullback f' g] (h : f = f') :
    (pullback.congrHom h (rfl : g = g)).inv ≫ pullback.fst f g =
      pullback.fst f' g := by
  rw [pullback.congrHom_inv]
  simp only [pullback.map, pullback.lift_fst, Category.comp_id]


private theorem pullback_congrHom_inv_snd_left
    {C : Type*} [Category C] {X Y Z : C} {f f' : X ⟶ Z}
    {g : Y ⟶ Z} [HasPullback f g] [HasPullback f' g] (h : f = f') :
    (pullback.congrHom h (rfl : g = g)).inv ≫ pullback.snd f g =
      pullback.snd f' g := by
  rw [pullback.congrHom_inv]
  simp only [pullback.map, pullback.lift_snd, Category.comp_id]

private theorem translateUnitPair_back
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (hObjects : AlgebraicGeometry.IsAlgebraicSpace C S hS H.objects)
    (hArrows : AlgebraicGeometry.IsAlgebraicSpace C S hS H.arrows)
    (T : AlgebraicGeometry.AlgebraicSpaces C S hS)
    (z : T.obj ⟶ H.arrows)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS
      (ObjectProperty.homMk H.source :
        (⟨H.arrows, hArrows⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS) ⟶
        (⟨H.objects, hObjects⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS))
      T)
    (hbase : p.toBase.hom = z ≫ H.source)
    (unit : H.objects ⟶ H.arrows)
    (hunit : unit ≫ H.source = 𝟙 H.objects)
    (hunit_spec : ∀ V x, unit.app V x = H.identity V x) :
    unitOverTarget H z unit hunit ≫ fiberTranslateBack H z ≫
      (pullback.congrHom hbase (rfl : H.source = H.source)).inv =
    pullback.lift (𝟙 T.obj) z (by simpa using hbase) := by
  let eBase := pullback.congrHom hbase (rfl : H.source = H.source)
  let targetPair := unitOverTarget H z unit hunit
  let oldPair := pullback.lift (𝟙 T.obj) z (by simpa using hbase)
  apply pullback.hom_ext
  · have hbaseFst : eBase.inv ≫ pullback.fst p.toBase.hom H.source =
        pullback.fst (z ≫ H.source) H.source :=
      pullback_congrHom_inv_fst (f := p.toBase.hom) (f' := z ≫ H.source)
        (g := H.source) hbase
    calc
      (targetPair ≫ fiberTranslateBack H z ≫ eBase.inv) ≫
          pullback.fst p.toBase.hom H.source =
        targetPair ≫ fiberTranslateBack H z ≫ (eBase.inv ≫
          pullback.fst p.toBase.hom H.source) := by simp [Category.assoc]
      _ = targetPair ≫ fiberTranslateBack H z ≫
          pullback.fst (z ≫ H.source) H.source := by rw [hbaseFst]
      _ = targetPair ≫ pullback.fst (z ≫ H.target) H.source := by
        rw [fiberTranslateBack_fst]
      _ = 𝟙 T.obj := by
        dsimp [targetPair]
        exact pullback.lift_fst _ _ _
      _ = oldPair ≫ pullback.fst p.toBase.hom H.source := by
        dsimp [oldPair]
        exact (pullback.lift_fst _ _ _).symm
  · have hbaseSnd : eBase.inv ≫ pullback.snd p.toBase.hom H.source =
        pullback.snd (z ≫ H.source) H.source :=
      pullback_congrHom_inv_snd_left
        (C := ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u))
        (X := T.obj) (Y := H.arrows) (Z := H.objects)
        (f := p.toBase.hom) (f' := z ≫ H.source) (g := H.source) hbase
    have hcomp := fiberTranslateBack_unit_comp H z unit hunit hunit_spec
    calc
      (targetPair ≫ fiberTranslateBack H z ≫ eBase.inv) ≫
          pullback.snd p.toBase.hom H.source =
        targetPair ≫ fiberTranslateBack H z ≫ (eBase.inv ≫
          pullback.snd p.toBase.hom H.source) := by simp [Category.assoc]
      _ = targetPair ≫ fiberTranslateBack H z ≫
          pullback.snd (z ≫ H.source) H.source := by rw [hbaseSnd]
      _ = targetPair ≫ (fiberTranslateBack H z ≫
          pullback.snd (z ≫ H.source) H.source) := by simp
      _ = targetPair ≫ fiberTranslateBackPair H z ≫ H.comp := by
        rw [fiberTranslateBack_comp_snd]
      _ = z := hcomp
      _ = oldPair ≫ pullback.snd p.toBase.hom H.source := by
        dsimp [oldPair]
        exact (pullback.lift_snd _ _ _).symm

private lemma openSubspace_preimage
    (C : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : G ⟶ F) (Z : Subfunctor F)
    (hF : AlgebraicGeometry.IsAlgebraicSpace C S hS F)
    (hG : AlgebraicGeometry.IsAlgebraicSpace C S hS G)
    (hZ : AlgebraicGeometry.Space.IsOpenSubspace C S hS Z) :
    AlgebraicGeometry.Space.IsOpenSubspace C S hS (Z.preimage f) := by
  have hsquare := Subfunctor.isPullback_preimage f Z
  have hAlg : AlgebraicGeometry.IsAlgebraicSpace C S hS (Z.preimage f).toFunctor :=
    AlgebraicGeometry.isAlgebraicSpace_of_iso C S hS hsquare.isoPullback
      (AlgebraicGeometry.isAlgebraicSpace_pullback C S hS Z.ι f hZ.1 hG hF)
  refine ⟨hAlg, ?_⟩
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
      MorphismProperty Scheme.{u}) (AlgebraicGeometry.BigFppfOver.toScheme C S hS))
  let : Q.IsStableUnderBaseChange := MorphismProperty.relative_isStableUnderBaseChange _
  exact Q.of_isPullback hsquare hZ.2

private noncomputable def translateFiniteOpenPair
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (hObjects : AlgebraicGeometry.IsAlgebraicSpace C S hS H.objects)
    (hArrows : AlgebraicGeometry.IsAlgebraicSpace C S hS H.arrows)
    (T : AlgebraicGeometry.AlgebraicSpaces C S hS)
    (z : T.obj ⟶ H.arrows)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS
      (ObjectProperty.homMk H.source :
        (⟨H.arrows, hArrows⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS) ⟶
          (⟨H.objects, hObjects⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS))
      T)
    (hbase : p.toBase.hom = z ≫ H.source) :
    AlgebraicGeometry.Space.FiniteOpenSubspace C S hS
      (ObjectProperty.homMk H.source :
        (⟨H.arrows, hArrows⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS) ⟶
          (⟨H.objects, hObjects⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS))
      T := by
  let eBase := pullback.congrHom hbase (rfl : H.source = H.source)
  let eTranslate : pullback (z ≫ H.target) H.source ≅
      pullback (z ≫ H.source) H.source :=
    ⟨fiberTranslateBack H z, fiberTranslate H z,
      fiberTranslate_forward_after_back H z,
      fiberTranslate_back_after_forward H z⟩
  let eκ := eTranslate.trans eBase.symm
  let κ := eκ.hom
  let sourceFst := pullback.fst p.toBase.hom H.source
  let targetFst := pullback.fst (z ≫ H.target) H.source
  have hBaseInv : eBase.inv ≫ sourceFst =
      pullback.fst (z ≫ H.source) H.source :=
    pullback_congrHom_inv_fst hbase
  let hOld : AlgebraicGeometry.IsAlgebraicSpace C S hS
      (pullback p.toBase.hom H.source) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback C S hS p.toBase.hom H.source
      T.property hArrows hObjects
  let hNew : AlgebraicGeometry.IsAlgebraicSpace C S hS
      (pullback (z ≫ H.target) H.source) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback C S hS (z ≫ H.target) H.source
      T.property hArrows hObjects
  refine ⟨ObjectProperty.homMk (z ≫ H.target), p.subspace.preimage κ, ?_, ?_⟩
  · exact openSubspace_preimage C S hS κ p.subspace hOld hNew p.isOpen
  · have : IsIso κ := eκ.isIso_hom
    have hκfst : κ ≫ sourceFst = targetFst := by
      change (fiberTranslateBack H z ≫ eBase.inv) ≫ sourceFst = targetFst
      calc
        (fiberTranslateBack H z ≫ eBase.inv) ≫ sourceFst =
            fiberTranslateBack H z ≫ (eBase.inv ≫ sourceFst) :=
              Category.assoc _ _ _
        _ = fiberTranslateBack H z ≫
            pullback.fst (z ≫ H.source) H.source := by rw [hBaseInv]
        _ = targetFst := fiberTranslateBack_fst H z
    have hκ : IsPullback κ targetFst sourceFst
        (𝟙 T.obj) := by
      refine IsPullback.of_isLimit
        (c := PullbackCone.mk κ targetFst (by
          rw [Category.comp_id]
          exact hκfst)) ?_
      refine PullbackCone.IsLimit.mk hκfst (fun s => s.fst ≫ inv κ) ?_ ?_ ?_
      · intro s
        simp
      · intro s
        rw [← hκfst]
        simp [s.condition]
      · intro s m hm₁ hm₂
        apply (cancel_mono κ).mp
        simpa using hm₁
    have hpre := Subfunctor.isPullback_preimage κ p.subspace
    have hproj : IsPullback (p.subspace.fromPreimage κ)
        ((p.subspace.preimage κ).ι ≫ targetFst)
        (p.subspace.ι ≫ sourceFst) (𝟙 T.obj) := by
      convert hpre.paste_vert hκ using 1
    exact isFinite_of_isPullback C S hS hproj p.finite_projection

private theorem finiteOpenPair_containsSection
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y T : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS f T)
    (hfactor : ∀ V y,
      (pullback.lift (𝟙 T.obj) (p.toBase.hom ≫ σ.hom) (by
        calc
          𝟙 T.obj ≫ p.toBase.hom = p.toBase.hom := Category.id_comp _
          _ = (p.toBase.hom ≫ σ.hom) ≫ f.hom := by
            rw [Category.assoc, hσ, Category.comp_id])).app V y ∈
          p.subspace.obj V) :
    AlgebraicGeometry.Space.ContainsSection C S hS f σ hσ p := by
  let sectionPair := pullback.lift (𝟙 T.obj) (p.toBase.hom ≫ σ.hom) (by
    calc
      𝟙 T.obj ≫ p.toBase.hom = p.toBase.hom := Category.id_comp _
      _ = (p.toBase.hom ≫ σ.hom) ≫ f.hom := by
        rw [Category.assoc, hσ, Category.comp_id])
  have hrange : Subfunctor.range sectionPair ≤ p.subspace := by
    intro V x hx
    obtain ⟨y, rfl⟩ := hx
    exact hfactor V y
  let sectionLift : T.obj ⟶ p.subspace.toFunctor := Subfunctor.lift sectionPair hrange
  refine ⟨sectionLift, ?_⟩
  show sectionLift ≫ p.subspace.ι = sectionPair
  exact Subfunctor.lift_ι _ _

private theorem containsSection_baseChange
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (T : AlgebraicGeometry.AlgebraicSpaces C S hS)
    (U : AlgebraicGeometry.BigFppfOver C S hS)
    (g : yoneda.obj U ⟶ T.obj)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS f T)
    (q : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS f (schemeSpace U))
    (hbase : q.toBase.hom = g ≫ p.toBase.hom)
    (j : q.subspace.toFunctor ⟶ p.subspace.toFunctor)
    (hpb : IsPullback
      (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j g
      (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom))
    (hX : j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
      q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom)
    (hp : AlgebraicGeometry.Space.ContainsSection C S hS f σ hσ p) :
    AlgebraicGeometry.Space.ContainsSection C S hS f σ hσ q := by
  rcases hp with ⟨l, hl⟩
  let hmap : (schemeSpace U).obj ⟶ T.obj := by
    show yoneda.obj U ⟶ T.obj
    exact g
  have hbase' : q.toBase.hom = hmap ≫ p.toBase.hom := by
    dsimp [hmap, schemeSpace]
    exact hbase
  let sectionP := pullback.lift (𝟙 T.obj)
      (p.toBase.hom ≫ σ.hom) (by
        calc
          𝟙 _ ≫ p.toBase.hom = p.toBase.hom := Category.id_comp _
          _ = p.toBase.hom ≫ (σ.hom ≫ f.hom) := by rw [hσ]; simp
          _ = (p.toBase.hom ≫ σ.hom) ≫ f.hom := (Category.assoc _ _ _).symm)
  let sectionQ := pullback.lift (𝟙 (schemeSpace U).obj)
      (q.toBase.hom ≫ σ.hom) (by
        calc
          𝟙 _ ≫ q.toBase.hom = q.toBase.hom := Category.id_comp _
          _ = q.toBase.hom ≫ (σ.hom ≫ f.hom) := by rw [hσ]; simp
          _ = (q.toBase.hom ≫ σ.hom) ≫ f.hom := (Category.assoc _ _ _).symm)
  have hl' : l ≫ p.subspace.ι = sectionP := by simpa [sectionP] using hl
  have hfirst : 𝟙 (schemeSpace U).obj ≫ hmap =
      (hmap ≫ l) ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom := by
    calc
      𝟙 (schemeSpace U).obj ≫ hmap = hmap := by simp
      _ = hmap ≫ sectionP ≫ pullback.fst p.toBase.hom f.hom := by
        symm
        calc
          hmap ≫ sectionP ≫ pullback.fst p.toBase.hom f.hom =
              hmap ≫ (sectionP ≫ pullback.fst p.toBase.hom f.hom) := by simp
          _ = hmap ≫ 𝟙 _ := by simp [sectionP, pullback.lift_fst]
          _ = hmap := by simp
      _ = hmap ≫ (l ≫ p.subspace.ι) ≫ pullback.fst p.toBase.hom f.hom := by
        rw [← hl']
      _ = (hmap ≫ l) ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom := by
        simp [Category.assoc]
  let l' := hpb.lift (𝟙 (schemeSpace U).obj) (hmap ≫ l) hfirst
  have hl'fst : l' ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom =
      𝟙 (schemeSpace U).obj := hpb.lift_fst _ _ _
  have hl'j : l' ≫ j = hmap ≫ l := hpb.lift_snd _ _ _
  have hl'snd : l' ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom =
      q.toBase.hom ≫ σ.hom := by
    calc
      l' ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom =
          l' ≫ j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom :=
            congrArg (fun k => l' ≫ k) hX.symm
      _ = (l' ≫ j) ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom := by simp [Category.assoc]
      _ = (hmap ≫ l) ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom := by rw [hl'j]
      _ = hmap ≫ (l ≫ p.subspace.ι) ≫ pullback.snd p.toBase.hom f.hom := by simp [Category.assoc]
      _ = hmap ≫ sectionP ≫ pullback.snd p.toBase.hom f.hom := by rw [hl']
      _ = hmap ≫ (p.toBase.hom ≫ σ.hom) := by
            calc
              hmap ≫ sectionP ≫ pullback.snd p.toBase.hom f.hom =
                  hmap ≫ (sectionP ≫ pullback.snd p.toBase.hom f.hom) := by simp
              _ = hmap ≫ (p.toBase.hom ≫ σ.hom) := by simp [sectionP, pullback.lift_snd]
      _ = (hmap ≫ p.toBase.hom) ≫ σ.hom := (Category.assoc _ _ _).symm
      _ = q.toBase.hom ≫ σ.hom := congrArg (fun k => k ≫ σ.hom) hbase'.symm
  refine ⟨l', ?_⟩
  apply pullback.hom_ext
  · show l' ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom =
      sectionQ ≫ pullback.fst q.toBase.hom f.hom
    rw [hl'fst]
    simp [sectionQ, pullback.lift_fst]
  · show l' ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom =
      sectionQ ≫ pullback.snd q.toBase.hom f.hom
    rw [hl'snd]
    simp [sectionQ, pullback.lift_snd]

private theorem translateFiniteOpenPair_containsSection
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (hObjects : AlgebraicGeometry.IsAlgebraicSpace C S hS H.objects)
    (hArrows : AlgebraicGeometry.IsAlgebraicSpace C S hS H.arrows)
    (T : AlgebraicGeometry.AlgebraicSpaces C S hS)
    (z : T.obj ⟶ H.arrows)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS
      (ObjectProperty.homMk H.source :
        (⟨H.arrows, hArrows⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS) ⟶
          (⟨H.objects, hObjects⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS))
      T)
    (hbase : p.toBase.hom = z ≫ H.source)
    (unit : H.objects ⟶ H.arrows)
    (hunit : unit ≫ H.source = 𝟙 H.objects)
    (hunit_spec : ∀ V x, unit.app V x = H.identity V x)
    (w : T.obj ⟶ p.subspace.toFunctor)
    (hw : w ≫ p.subspace.ι =
      pullback.lift (𝟙 T.obj) z (by simpa using hbase)) :
    AlgebraicGeometry.Space.ContainsSection C S hS
      (ObjectProperty.homMk H.source :
        (⟨H.arrows, hArrows⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS) ⟶
          (⟨H.objects, hObjects⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS))
      (ObjectProperty.homMk unit)
      (show unit ≫ H.source = 𝟙 H.objects from hunit)
      (translateFiniteOpenPair H hObjects hArrows T z p hbase) := by
  let translated := translateFiniteOpenPair H hObjects hArrows T z p hbase
  let baseChange := pullback.congrHom hbase (rfl : H.source = H.source)
  let κ := fiberTranslateBack H z ≫ baseChange.inv
  let targetPair := unitOverTarget H z unit hunit
  have hback := translateUnitPair_back H hObjects hArrows T z p hbase
    unit hunit hunit_spec
  apply finiteOpenPair_containsSection
    (ObjectProperty.homMk H.source :
      (⟨H.arrows, hArrows⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS) ⟶
        (⟨H.objects, hObjects⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS))
    (ObjectProperty.homMk unit) hunit translated
  intro V y
  show κ.app V (targetPair.app V y) ∈ p.subspace.obj V
  have hpoint : ConcreteCategory.hom (κ.app V)
      (ConcreteCategory.hom (targetPair.app V) y) =
      ConcreteCategory.hom (p.subspace.ι.app V)
        (ConcreteCategory.hom (w.app V) y) := by
    have hleft := congrArg (fun f => f.app V y) hback
    have hright := congrArg (fun f => f.app V y) hw
    change ConcreteCategory.hom (baseChange.inv.app V)
        (ConcreteCategory.hom ((fiberTranslateBack H z).app V)
          (ConcreteCategory.hom (targetPair.app V) y)) =
      ConcreteCategory.hom
        ((pullback.lift (𝟙 T.obj) z
          (by simpa using hbase)).app V) y at hleft
    change ConcreteCategory.hom (p.subspace.ι.app V)
        (ConcreteCategory.hom (w.app V) y) =
      ConcreteCategory.hom
        ((pullback.lift (𝟙 T.obj) z
          (by simpa using hbase)).app V) y at hright
    show ConcreteCategory.hom (baseChange.inv.app V)
        (ConcreteCategory.hom ((fiberTranslateBack H z).app V)
          (ConcreteCategory.hom (targetPair.app V) y)) = _
    simpa only [κ] using hleft.trans hright.symm
  rw [hpoint]
  exact (w.app V y).property


private theorem isEtale_of_openImmersion
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {F G : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : AlgebraicGeometry.Space.IsOpenImmersion C S hS f) :
    AlgebraicGeometry.Space.IsEtale C S hS f := by
  let Popen := MorphismProperty.inverseImage
    (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme C S hS)
  let Petale := MorphismProperty.inverseImage
    (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme C S hS)
  have hle : Popen ≤ Petale := by
    intro X Y g hg
    change AlgebraicGeometry.IsOpenImmersion
      ((AlgebraicGeometry.BigFppfOver.toScheme C S hS).map g) at hg
    let : AlgebraicGeometry.IsOpenImmersion
        ((AlgebraicGeometry.BigFppfOver.toScheme C S hS).map g) := hg
    show Etale ((AlgebraicGeometry.BigFppfOver.toScheme C S hS).map g)
    infer_instance
  have hpres : Petale.presheaf f := by
    refine ⟨hf.1, ?_⟩
    intro X Y g fst snd hpull
    exact hle snd (hf.2 g fst snd hpull)
  have hcomp : Petale.IsStableUnderComposition := by
    let : MorphismProperty.IsStableUnderComposition
        (@Etale.{u} : MorphismProperty Scheme.{u}) := by
      refine ⟨?_⟩
      intro X Y Z f g hf hg
      let : Etale f := hf
      let : Etale g := hg
      exact Etale.etale_comp f g
    exact MorphismProperty.IsStableUnderComposition.inverseImage
      (F := AlgebraicGeometry.BigFppfOver.toScheme C S hS)
  let : Petale.IsStableUnderComposition := hcomp
  let : Petale.presheaf.IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition Petale
  intro X φ hφ
  exact MorphismProperty.comp_mem Petale.presheaf φ f hφ hpres

private theorem finiteOpenSubspaceEquiv_base
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y : AlgebraicGeometry.AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (T : AlgebraicGeometry.AlgebraicSpaces C S hS)
    (v : T.obj ⟶ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).toFunctor) :
    ((finiteOpenSubspaceEquiv C S hS f T).1 v).toBase.hom =
      v ≫ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).baseMap := by
  let P := AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f
  ext V x
  let g : yoneda.obj V.unop ⟶ T.obj := yonedaEquiv.symm x
  have hs := (finiteOpenSubspaceEquiv C S hS f T).2 v V.unop g
  have hb := congrArg yonedaEquiv hs.1
  rw [yonedaEquiv_comp] at hb
  have hg : yonedaEquiv g = x := Equiv.apply_symm_apply _ _
  rw [hg] at hb
  have hp := congrArg yonedaEquiv (P.baseMap_spec V.unop (v.app V x))
  exact hb.symm.trans (by simpa using hp.symm)

private theorem finiteOpenSubspaceEquiv_containsSection
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (T : AlgebraicGeometry.AlgebraicSpaces C S hS)
    (v : T.obj ⟶ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).toFunctor)
    (hp : AlgebraicGeometry.Space.ContainsSection C S hS f σ hσ
      ((finiteOpenSubspaceEquiv C S hS f T).1 v)) :
    Subfunctor.range v ≤ (finitePartWithSection C S hS f σ hσ).toSubfunctor := by
  intro V x hx
  obtain ⟨y, rfl⟩ := hx
  let g : yoneda.obj V.unop ⟶ T.obj := yonedaEquiv.symm y
  have hg : yonedaEquiv g = y := Equiv.apply_symm_apply _ _
  have hs := (finiteOpenSubspaceEquiv C S hS f T).2 v V.unop g
  rw [hg] at hs
  obtain ⟨hb, j, hj, hX⟩ := hs
  exact ((finitePartWithSection C S hS f σ hσ).mem_iff V.unop _).mpr
    (containsSection_baseChange f σ hσ T V.unop g _ _ hb j hj hX hp)

private def finitePairFiber
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y T : AlgebraicGeometry.AlgebraicSpaces C S hS} {f : X ⟶ Y}
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS f T)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : T.obj.obj V) (z : X.obj.obj V) : Prop :=
  ∃ a : p.subspace.toFunctor.obj V,
    (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom).app V a = x ∧
    (p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom).app V a = z

private theorem finitePairFiber_projection
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y T : AlgebraicGeometry.AlgebraicSpaces C S hS} {f : X ⟶ Y}
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS f T)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) {x : T.obj.obj V} {z : X.obj.obj V}
    (h : finitePairFiber p V x z) : p.toBase.hom.app V x = f.hom.app V z := by
  obtain ⟨a, hx, hz⟩ := h
  have h := congrArg (fun k => k.app V a.val)
    (pullback.condition (f := p.toBase.hom) (g := f.hom))
  change p.toBase.hom.app V
      ((p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom).app V a) =
    f.hom.app V ((p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom).app V a) at h
  rwa [hx, hz] at h

private theorem finitePairFiber_baseChange
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y T T' : AlgebraicGeometry.AlgebraicSpaces C S hS} {f : X ⟶ Y}
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS f T)
    (q : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS f T')
    (g : T'.obj ⟶ T.obj) (j : q.subspace.toFunctor ⟶ p.subspace.toFunctor)
    (hpb : IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) j g
      (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom))
    (hX : j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
      q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : T'.obj.obj V) (z : X.obj.obj V) :
    finitePairFiber q V x z ↔ finitePairFiber p V (g.app V x) z := by
  have hv := hpb.map ((evaluation _ _).obj V)
  have hs := (Types.isPullback_iff _ _ _ _).mp hv
  constructor
  · rintro ⟨a, ha, hz⟩
    refine ⟨j.app V a, ?_, ?_⟩
    · have h := congrArg (fun k => k.app V a) hpb.w
      change g.app V ((q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom).app V a) =
        (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom).app V (j.app V a) at h
      exact h.symm.trans (congrArg (g.app V) ha)
    · exact (congrArg (fun k => k.app V a) hX).trans hz
  · rintro ⟨a, ha, hz⟩
    obtain ⟨b, hb, hj⟩ := hs.2.2 x a ha.symm
    refine ⟨b, hb, ?_⟩
    have h := congrArg (fun k => k.app V b) hX
    change (p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom).app V
      (j.app V b) = _ at h
    change j.app V b = a at hj
    rw [hj] at h
    exact h.symm.trans hz

private theorem finitePairFiber_classified
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y T : AlgebraicGeometry.AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (v : T.obj ⟶ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).toFunctor)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : T.obj.obj V) (z : X.obj.obj V) :
    finitePairFiber ((finiteOpenSubspaceEquiv C S hS f T).1 v) V x z ↔
      finitePairFiber ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).sections V.unop
        (v.app V x)) V (𝟙 V.unop) z := by
  let g : yoneda.obj V.unop ⟶ T.obj := yonedaEquiv.symm x
  have hg : yonedaEquiv g = x := Equiv.apply_symm_apply _ _
  have hs := (finiteOpenSubspaceEquiv C S hS f T).2 v V.unop g
  rw [hg] at hs
  obtain ⟨_, j, hj, hX⟩ := hs
  have h := finitePairFiber_baseChange _ _ g j hj hX V (𝟙 V.unop) z
  change _ ↔ finitePairFiber _ V (yonedaEquiv g) z at h
  rw [hg] at h
  exact h.symm

private theorem finitePairFiber_classified_comp
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y T T' : AlgebraicGeometry.AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (v : T.obj ⟶ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).toFunctor)
    (w : T'.obj ⟶ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).toFunctor)
    (g : T'.obj ⟶ T.obj) (h : g ≫ v = w)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : T'.obj.obj V) (z : X.obj.obj V) :
    finitePairFiber ((finiteOpenSubspaceEquiv C S hS f T).1 v)
        V (g.app V x) z ↔
      finitePairFiber ((finiteOpenSubspaceEquiv C S hS f T').1 w) V x z := by
  rw [finitePairFiber_classified, finitePairFiber_classified]
  have hx := congrArg (fun k => k.app V x) h
  change v.app V (g.app V x) = w.app V x at hx
  rw [hx]

private theorem presheafPullback_ext
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Z) (g : Y ⟶ Z) (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    {a b : (pullback f g).obj V}
    (h₁ : (pullback.fst f g).app V a = (pullback.fst f g).app V b)
    (h₂ : (pullback.snd f g).app V a = (pullback.snd f g).app V b) : a = b :=
  ((Types.isPullback_iff _ _ _ _).mp
    ((IsPullback.of_hasPullback f g).map ((evaluation _ _).obj V))).2.1 a b ⟨h₁, h₂⟩

private theorem finitePairFiber_iff
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y T : AlgebraicGeometry.AlgebraicSpaces C S hS} {f : X ⟶ Y}
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS f T)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (a : (pullback p.toBase.hom f.hom).obj V) :
    finitePairFiber p V ((pullback.fst p.toBase.hom f.hom).app V a)
      ((pullback.snd p.toBase.hom f.hom).app V a) ↔ a ∈ p.subspace.obj V := by
  constructor
  · rintro ⟨b, hb₁, hb₂⟩
    have hb : b.val = a := presheafPullback_ext _ _ V hb₁ hb₂
    exact hb ▸ b.property
  · intro ha
    exact ⟨⟨a, ha⟩, rfl, rfl⟩

private theorem finitePair_ext
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y T : AlgebraicGeometry.AlgebraicSpaces C S hS} {f : X ⟶ Y}
    (p q : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS f T)
    (hb : p.toBase.hom = q.toBase.hom)
    (hf : ∀ V x z, finitePairFiber p V x z ↔ finitePairFiber q V x z) : p = q := by
  obtain ⟨a, P, hP, hPf⟩ := p
  obtain ⟨b, Q, hQ, hQf⟩ := q
  have hab : a = b := ObjectProperty.hom_ext _ hb
  subst b
  have hPQ : P = Q := by
    ext V r
    exact (finitePairFiber_iff ⟨a, P, hP, hPf⟩ V r).symm.trans
      ((hf V _ _).trans (finitePairFiber_iff ⟨a, Q, hQ, hQf⟩ V r))
  subst Q
  rfl

private theorem finitePairFiber_section
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y T : AlgebraicGeometry.AlgebraicSpaces C S hS} (f : X ⟶ Y)
    (v : T.obj ⟶ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).toFunctor)
    (V W : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : T.obj.obj V)
    (k : W.unop ⟶ V.unop) (z : X.obj.obj W) :
    finitePairFiber ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).sections V.unop
        (v.app V x)) W k z ↔
      finitePairFiber ((finiteOpenSubspaceEquiv C S hS f T).1 v)
        W (T.obj.map k.op x) z := by
  let g : yoneda.obj V.unop ⟶ T.obj := yonedaEquiv.symm x
  have hg : yonedaEquiv g = x := Equiv.apply_symm_apply _ _
  have hs := (finiteOpenSubspaceEquiv C S hS f T).2 v V.unop g
  rw [hg] at hs
  obtain ⟨_, j, hj, hX⟩ := hs
  exact finitePairFiber_baseChange _ _ g j hj hX W k z

private theorem finitePairFiber_translate
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (hObjects : AlgebraicGeometry.IsAlgebraicSpace C S hS H.objects)
    (hArrows : AlgebraicGeometry.IsAlgebraicSpace C S hS H.arrows)
    (T : AlgebraicGeometry.AlgebraicSpaces C S hS) (z : T.obj ⟶ H.arrows)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS
      (ObjectProperty.homMk H.source :
        (⟨H.arrows, hArrows⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS) ⟶
        (⟨H.objects, hObjects⟩ : AlgebraicGeometry.AlgebraicSpaces C S hS)) T)
    (hbase : p.toBase.hom = z ≫ H.source)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (x : T.obj.obj V) (r : H.arrows.obj V)
    (hr : H.source.app V r = H.target.app V (z.app V x)) :
    finitePairFiber (translateFiniteOpenPair H hObjects hArrows T z p hbase) V x r ↔
      finitePairFiber p V x (H.compose V r (z.app V x) hr) := by
  let q := translateFiniteOpenPair H hObjects hArrows T z p hbase
  let e := pullback.congrHom hbase (rfl : H.source = H.source)
  let κ := fiberTranslateBack H z ≫ e.inv
  obtain ⟨b, hb₁, hb₂⟩ := ((Types.isPullback_iff _ _ _ _).mp
    ((IsPullback.of_hasPullback (z ≫ H.target) H.source).map
      ((evaluation _ _).obj V))).2.2 x r hr.symm
  change (pullback.fst (z ≫ H.target) H.source).app V b = x at hb₁
  change (pullback.snd (z ≫ H.target) H.source).app V b = r at hb₂
  have hκ₁ : (pullback.fst p.toBase.hom H.source).app V (κ.app V b) = x := by
    have he : e.inv ≫ pullback.fst p.toBase.hom H.source =
        pullback.fst (z ≫ H.source) H.source := pullback_congrHom_inv_fst hbase
    have hκ : κ ≫ pullback.fst p.toBase.hom H.source =
        pullback.fst (z ≫ H.target) H.source := by
      rw [Category.assoc, he, fiberTranslateBack_fst]
    exact (congrArg (fun k => k.app V b) hκ).trans hb₁
  have hκ₂ : (pullback.snd p.toBase.hom H.source).app V (κ.app V b) =
      H.compose V r (z.app V x) hr := by
    have he : e.inv ≫ pullback.snd p.toBase.hom H.source =
        pullback.snd (z ≫ H.source) H.source := pullback_congrHom_inv_snd_left hbase
    have hκ : κ ≫ pullback.snd p.toBase.hom H.source =
        fiberTranslateBackPair H z ≫ H.comp := by
      rw [Category.assoc, he, fiberTranslateBack_comp_snd]
    apply (congrArg (fun k => k.app V b) hκ).trans
    show H.compose V ((pullback.snd (z ≫ H.target) H.source).app V b)
      (z.app V ((pullback.fst (z ≫ H.target) H.source).app V b)) _ = _
    apply congrArg (H.comp.app V)
    apply Subtype.ext
    exact Prod.ext hb₂ (congrArg (z.app V) hb₁)
  calc
    finitePairFiber q V x r ↔ b ∈ q.subspace.obj V := by
      rw [← hb₁, ← hb₂]
      exact finitePairFiber_iff q V b
    _ ↔ κ.app V b ∈ p.subspace.obj V := Iff.rfl
    _ ↔ finitePairFiber p V x (H.compose V r (z.app V x) hr) := by
      have hb : κ.app V b ∈ p.subspace.obj V ↔ finitePairFiber p V
          ((pullback.fst p.toBase.hom H.source).app V (κ.app V b))
          ((pullback.snd p.toBase.hom H.source).app V (κ.app V b)) :=
        (finitePairFiber_iff p V (κ.app V b)).symm
      rwa [hκ₁, hκ₂] at hb

private theorem groupoid_identity_of_idempotent
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ) (a : H.arrows.obj V)
    (haa : H.source.app V a = H.target.app V a)
    (ha : H.compose V a a haa = a) : a = H.identity V (H.source.app V a) := by
  let : Groupoid (H.objects.obj V) := H.evaluationGroupoid V
  let f : H.source.app V a ⟶ H.source.app V a :=
    (H.evaluationArrowEquiv V _ _).symm ⟨a, rfl, haa.symm⟩
  have hf : f ≫ f = f := by
    apply (H.evaluationArrowEquiv V _ _).injective
    apply Subtype.ext
    simpa only [H.evaluationArrowEquiv_comp, f, Equiv.apply_symm_apply] using ha
  have he : f = 𝟙 _ := (cancel_epi f).mp (hf.trans (Category.comp_id f).symm)
  simpa only [f, Equiv.apply_symm_apply, H.evaluationArrowEquiv_id] using
    congrArg (fun k => (H.evaluationArrowEquiv V _ _ k).val) he

private theorem composableToPullback_fst
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {U R : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U R s t).obj V) :
    (pullback.fst s t).app V ((composableToPullback s t).app V p) = p.val.1 :=
  by
    show ((composableToPullback s t ≫ pullback.fst s t).app V) p = _
    simp only [composableToPullback, pullback.lift_fst]
    rfl

private theorem composableToPullback_snd
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {U R : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U)
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U R s t).obj V) :
    (pullback.snd s t).app V ((composableToPullback s t).app V p) = p.val.2 :=
  by
    show ((composableToPullback s t ≫ pullback.snd s t).app V) p = _
    simp only [composableToPullback, pullback.lift_snd]
    rfl



private theorem pointwiseGroupoid_of_lifts
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    (H : Deformation.GroupoidInFunctors ((AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ))
    (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
    {O R : Type u} (s t : R → O) (g : O → H.objects.obj V) (p : R → H.arrows.obj V)
    (hs : ∀ a, H.source.app V (p a) = g (s a))
    (ht : ∀ a, H.target.app V (p a) = g (t a))
    (hinj : ∀ a b, s a = s b → p a = p b → a = b)
    (e : O → R) (es : ∀ x, s (e x) = x) (et : ∀ x, t (e x) = x)
    (ep : ∀ x, p (e x) = H.identity V (g x))
    (c : {q : R × R // s q.1 = t q.2} → R)
    (cs : ∀ q, s (c q) = s q.val.2) (ct : ∀ q, t (c q) = t q.val.1)
    (cp : ∀ q, p (c q) = H.compose V (p q.val.1) (p q.val.2)
      ((hs _).trans ((congrArg g q.property).trans (ht _).symm)))
    (i : R → R) (is : ∀ a, s (i a) = t a) (it : ∀ a, t (i a) = s a)
    (ip : ∀ a, p (i a) = Deformation.inverseArrow H V (p a)) :
    Nonempty (Deformation.PointwiseGroupoid s t c) := by
  classical
  let : Groupoid (H.objects.obj V) := H.evaluationGroupoid V
  let hom (x y : O) := {a : R // s a = x ∧ t a = y}
  let map {x y : O} (a : hom x y) : g x ⟶ g y :=
    (H.evaluationArrowEquiv V _ _).symm
      ⟨p a.val, (hs _).trans (congrArg g a.property.1),
        (ht _).trans (congrArg g a.property.2)⟩
  have map_inj {x y : O} : Function.Injective (@map x y) := by
    intro a b h
    apply Subtype.ext
    apply hinj a.val b.val (a.property.1.trans b.property.1.symm)
    have h' := congrArg (fun f => (H.evaluationArrowEquiv V _ _ f).val) h
    simpa only [map, Equiv.apply_symm_apply] using h'
  let id' (x : O) : hom x x := ⟨e x, es x, et x⟩
  let comp' {x y z : O} (a : hom x y) (b : hom y z) : hom x z :=
    ⟨c ⟨(b.val, a.val), b.property.1.trans a.property.2.symm⟩,
      (cs _).trans a.property.1, (ct _).trans b.property.2⟩
  have map_id (x : O) : map (id' x) = 𝟙 (g x) := by
    apply (H.evaluationArrowEquiv V _ _).injective
    apply Subtype.ext
    simp only [map, Equiv.apply_symm_apply, H.evaluationArrowEquiv_id]
    exact ep x
  have map_comp {x y z : O} (a : hom x y) (b : hom y z) :
      map (comp' a b) = map a ≫ map b := by
    apply (H.evaluationArrowEquiv V _ _).injective
    apply Subtype.ext
    simp only [map, Equiv.apply_symm_apply, H.evaluationArrowEquiv_comp]
    exact cp _
  let cat : Category.{u} O := {
    Hom := hom
    id := id'
    comp := comp'
    id_comp := by
      intro x y a
      apply map_inj
      rw [map_comp, map_id, Category.id_comp]
    comp_id := by
      intro x y a
      apply map_inj
      rw [map_comp, map_id, Category.comp_id]
    assoc := by
      intro x y z w a b c
      apply map_inj
      simp only [map_comp, Category.assoc]
  }
  let := cat
  let inv' {x y : O} (a : x ⟶ y) : y ⟶ x :=
    ⟨i a.val, (is _).trans a.property.2, (it _).trans a.property.1⟩
  let grp : Groupoid.{u} O := {
    __ := cat
    inv := inv'
    inv_comp := by
      intro x y a
      apply Subtype.ext
      apply hinj _ _
      · exact ((cs _).trans ((is _).trans a.property.2)).trans (es y).symm
      · show p (c _) = p (e y)
        rw [cp, ep]
        calc
          _ = H.compose V (p a.val) (Deformation.inverseArrow H V (p a.val))
              (inverseArrow_target_functor H V _).symm := by
            apply congrArg (H.comp.app V)
            apply Subtype.ext
            exact Prod.ext rfl (ip a.val)
          _ = H.identity V (H.target.app V (p a.val)) := translateArrow_self H V _
          _ = _ := congrArg (H.identity V) ((ht _).trans (congrArg g a.property.2))
    comp_inv := by
      intro x y a
      apply Subtype.ext
      apply hinj _ _
      · exact ((cs _).trans a.property.1).trans (es x).symm
      · show p (c _) = p (e x)
        rw [cp, ep]
        calc
          _ = H.compose V (Deformation.inverseArrow H V (p a.val)) (p a.val)
              (inverseArrow_source_functor H V _) := by
            apply congrArg (H.comp.app V)
            apply Subtype.ext
            exact Prod.ext (ip a.val) rfl
          _ = H.identity V (H.source.app V (p a.val)) := groupoidCompose_inverse_left H V _ _
          _ = _ := congrArg (H.identity V) ((hs _).trans (congrArg g a.property.1))
  }
  exact ⟨{ groupoid := grp, arrowEquiv := fun _ _ => Equiv.refl _, comp_eq := fun _ _ => rfl }⟩

/-- A morphism into the finite part of `f` whose sections all contain the induced section of
`f` classifies a pair which contains the induced section. -/
private theorem containsSection_of_range_le
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (f : X ⟶ Y) (σ : Y ⟶ X) (hσ : σ.hom ≫ f.hom = 𝟙 Y.obj)
    (T : AlgebraicGeometry.AlgebraicSpaces C S hS)
    (v : T.obj ⟶ (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).toFunctor)
    (hv : Subfunctor.range v ≤ (finitePartWithSection C S hS f σ hσ).toSubfunctor) :
    AlgebraicGeometry.Space.ContainsSection C S hS f σ hσ
      ((finiteOpenSubspaceEquiv C S hS f T).1 v) := by
  set pair := (finiteOpenSubspaceEquiv C S hS f T).1 v
  let iUnit : T.obj ⟶ pullback pair.toBase.hom f.hom :=
    pullback.lift (𝟙 T.obj) (pair.toBase.hom ≫ σ.hom)
      (by simp only [Category.id_comp, Category.assoc, hσ, Category.comp_id])
  have hle : Subfunctor.range iUnit ≤ pair.subspace := by
    intro V x hx
    rcases hx with ⟨x, rfl⟩
    let U := V.unop
    let g : AlgebraicGeometry.schemeSpace U ⟶ T :=
      ObjectProperty.homMk (yonedaEquiv.symm x)
    have hg : yonedaEquiv g.hom = x := Equiv.apply_symm_apply _ _
    let xg := yonedaEquiv g.hom
    let xP := v.app V xg
    let p := (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).sections U xP
    have hxP : xP ∈ (finitePartWithSection C S hS f σ hσ).toSubfunctor.obj V :=
      hv V ⟨xg, rfl⟩
    rcases ((finitePartWithSection C S hS f σ hσ).mem_iff U xP).1 hxP with ⟨w, hw⟩
    have hspec := (finiteOpenSubspaceEquiv C S hS f T).2 v U g.hom
    have hbaseV : p.toBase.hom = g.hom ≫ pair.toBase.hom := by
      show ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS f).sections U
          (v.app V (yonedaEquiv g.hom))).toBase.hom =
        g.hom ≫
          ((finiteOpenSubspaceEquiv C S hS f T).1 v).toBase.hom
      exact hspec.1
    have hspec2 : ∃ j : p.subspace.toFunctor ⟶ pair.subspace.toFunctor,
          IsPullback (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom) j g.hom
          (pair.subspace.ι ≫
            pullback.fst pair.toBase.hom f.hom) ∧
        j ≫ pair.subspace.ι ≫
            pullback.snd pair.toBase.hom f.hom =
          p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom := by
      simpa only [g] using hspec.2
    rcases hspec2 with ⟨j, hpb, hj⟩
    have hval : (w ≫ p.subspace.ι) =
        pullback.lift (𝟙 (AlgebraicGeometry.schemeSpace U).obj)
          (p.toBase.hom ≫ σ.hom) (by
            simp only [Category.id_comp, Category.assoc, Category.comp_id,
              hσ]) := hw
    have hmap : w ≫ j ≫ pair.subspace.ι = g.hom ≫ iUnit := by
      apply pullback.hom_ext
      · calc
          (w ≫ j ≫ pair.subspace.ι) ≫
              pullback.fst pair.toBase.hom f.hom =
              w ≫ (j ≫ pair.subspace.ι ≫
                pullback.fst pair.toBase.hom f.hom) := by
                  simp only [Category.assoc]
          _ = w ≫ (p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom ≫ g.hom) :=
                congrArg (fun k => w ≫ k) hpb.w.symm
          _ = (w ≫ p.subspace.ι) ≫
                pullback.fst p.toBase.hom f.hom ≫ g.hom := by
                simp only [Category.assoc]
          _ = pullback.lift (𝟙 (AlgebraicGeometry.schemeSpace U).obj)
                (p.toBase.hom ≫ σ.hom) (by
                  simp only [Category.id_comp, Category.assoc, Category.comp_id,
                    hσ]) ≫
                pullback.fst p.toBase.hom f.hom ≫ g.hom := by rw [hval]
          _ = 𝟙 (AlgebraicGeometry.schemeSpace U).obj ≫ g.hom := by
                calc
                  _ = (pullback.lift (𝟙 (AlgebraicGeometry.schemeSpace U).obj)
                      (p.toBase.hom ≫ σ.hom) (by
                        simp only [Category.id_comp, Category.assoc, Category.comp_id,
                          hσ]) ≫
                      pullback.fst p.toBase.hom f.hom) ≫ g.hom := by
                        simp only [← Category.assoc]
                  _ = 𝟙 (AlgebraicGeometry.schemeSpace U).obj ≫ g.hom := by
                        rw [pullback.lift_fst]
          _ = (g.hom ≫ iUnit) ≫
                pullback.fst pair.toBase.hom f.hom := by
                simp [iUnit, Category.assoc, pullback.lift_fst]
      · calc
          (w ≫ j ≫ pair.subspace.ι) ≫
              pullback.snd pair.toBase.hom f.hom =
              w ≫ (j ≫ pair.subspace.ι ≫
                pullback.snd pair.toBase.hom f.hom) := by
                  simp only [Category.assoc]
          _ = w ≫ (p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom) := by
                rw [hj]
          _ = (w ≫ p.subspace.ι) ≫
                pullback.snd p.toBase.hom f.hom := by
                simp only [Category.assoc]
          _ = pullback.lift (𝟙 (AlgebraicGeometry.schemeSpace U).obj)
                (p.toBase.hom ≫ σ.hom) (by
                  simp only [Category.id_comp, Category.assoc, Category.comp_id,
                    hσ]) ≫
                pullback.snd p.toBase.hom f.hom := by rw [hval]
          _ = (g.hom ≫ iUnit) ≫
                pullback.snd pair.toBase.hom f.hom := by
                simp [iUnit, hbaseV, Category.assoc, pullback.lift_snd]
    have hpoint : ((w ≫ j).app V (𝟙 U)).val = iUnit.app V x := by
      have h := congrArg (fun f => f.app V (𝟙 U)) hmap
      change ((w ≫ j).app V (𝟙 U)).val = iUnit.app V (g.hom.app V (𝟙 U)) at h
      have hg' : (ConcreteCategory.hom (g.hom.app V)) (𝟙 U) = x := by
        show yonedaEquiv g.hom = x
        exact hg
      rw [hg'] at h
      simpa only [Functor.map_id] using h
    show iUnit.app V x ∈ pair.subspace.obj V
    rw [← hpoint]
    exact ((w ≫ j).app V (𝟙 U)).property
  exact ⟨Subfunctor.lift iUnit hle, Subfunctor.lift_ι _ _⟩


/-- **Stacks 04RU, clauses (1) and (2).** The two structure spaces of the finite part of a
groupoid in algebraic spaces over `B`: the object space `U'` with its étale projection
`g : U' ⟶ U`, identified with `(R_s/U, e)_fin ⟶ U`, and the universal open and closed subspace
`Z_univ ⊂ R ×_{s, U, g} U'` finite over `U'` which contains the base change of the unit. -/
@[stacks 04RU "clauses (1) and (2) stated; not the groupoid structure"]
public structure FinitePartUniversalOpen
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B) where
  /-- The unit `e` of the given groupoid. -/
  unit : G.objects ⟶ G.arrows
  /-- The unit is a section of the source morphism. -/
  unit_source : unit.hom ≫ G.source.hom = 𝟙 G.objects.obj
  /-- The unit induces the identity arrow at every point of every test scheme. -/
  unit_identity : ∀ T x, unit.hom.app T x = G.toGroupoidInFunctors.identity T x
  /-- The new space of objects. -/
  objects : AlgebraicGeometry.AlgebraicSpaces C S hS
  /-- The projection `g : U' ⟶ U` on objects. -/
  objectProjection : objects ⟶ G.objects
  /-- The projection is étale. -/
  objectProjection_etale : AlgebraicGeometry.Space.IsEtale C S hS objectProjection.hom
  /-- The new space of objects is the finite part of the source containing the unit. -/
  objectsEquiv : objects.obj ≅
    (finitePartWithSection C S hS G.source unit unit_source).toSubfunctor.toFunctor
  /-- Under that identification the projection is the one of the finite part. -/
  objectProjection_spec : objectProjection.hom =
    objectsEquiv.hom ≫
      (finitePartWithSection C S hS G.source unit unit_source).toSubfunctor.ι ≫
      (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap
  /-- The universal finite open subspace `Z_univ ⊂ R ×_{s, U, g} U'`. -/
  universalOpen : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS G.source objects
  /-- Its ambient fibre product is taken along the projection. -/
  universalOpen_base : universalOpen.toBase = objectProjection
  /-- It is the pair classified by the inclusion of the new space of objects. -/
  universalOpen_spec :
    (finiteOpenSubspaceEquiv C S hS G.source objects).1
      (objectsEquiv.hom ≫
        (finitePartWithSection C S hS G.source unit unit_source).toSubfunctor.ι) =
      universalOpen
  /-- It contains the base change of the unit. -/
  universalOpen_containsUnit :
    AlgebraicGeometry.Space.ContainsSection C S hS G.source unit unit_source universalOpen
  /-- It is also closed in the ambient fibre product. -/
  universalOpen_closed : AlgebraicGeometry.Space.IsClosedSubspace C S hS universalOpen.subspace

/-- **Stacks 04RU, clauses (1) and (2).** For a groupoid in algebraic spaces over `B` whose
source and target are separated and locally of finite type, the object space `(R_s/U, e)_fin`
with its étale projection to `U` and the universal open and closed subspace of
`R ×_{s, U, g} U'` finite over `U'` containing the base change of the unit. -/
@[stacks 04RU "clauses (1) and (2); not the groupoid structure or its morphism"]
public noncomputable def finitePartUniversalOpen
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B)
    (hs_sep : AlgebraicGeometry.Space.IsSeparated C S hS G.source.hom)
    (_ht_sep : AlgebraicGeometry.Space.IsSeparated C S hS G.target.hom)
    (hs_lft : AlgebraicGeometry.Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (_ht_lft : AlgebraicGeometry.Space.IsLocallyOfFiniteType C S hS G.target.hom) :
    FinitePartUniversalOpen G := by
  classical
  let P := AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source
  let q := finitePartWithSection C S hS G.source
    (identitySection G) (identitySection_source G)
  have hP : AlgebraicGeometry.IsAlgebraicSpace C S hS P.toFunctor :=
    AlgebraicGeometry.Space.isAlgebraicSpace_finiteOpenSubspacePresheaf C S hS G.source
      hs_sep hs_lft
  have hqOpen : AlgebraicGeometry.Space.IsOpenSubspace C S hS q.toSubfunctor :=
    isOpenSubspace_finitePartWithSection C S hS G.source
      (identitySection G) (identitySection_source G) hP
  let objects : AlgebraicGeometry.AlgebraicSpaces C S hS :=
    ⟨q.toSubfunctor.toFunctor, hqOpen.1⟩
  let objectProjection : objects ⟶ G.objects :=
    ObjectProperty.homMk (q.toSubfunctor.ι ≫ P.baseMap)
  let universalOpen : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS G.source objects :=
    (finiteOpenSubspaceEquiv C S hS G.source objects).1 q.toSubfunctor.ι
  have hbase : universalOpen.toBase = objectProjection := by
    apply ObjectProperty.hom_ext
    exact finiteOpenSubspaceEquiv_base G.source objects q.toSubfunctor.ι
  have hObjectProjectionEtale :
      AlgebraicGeometry.Space.IsEtale C S hS objectProjection.hom := by
    change AlgebraicGeometry.Space.IsEtale C S hS (q.toSubfunctor.ι ≫ P.baseMap)
    exact AlgebraicGeometry.Space.isEtale_comp C S hS
      (isEtale_of_openImmersion q.toSubfunctor.ι hqOpen.2)
      (AlgebraicGeometry.Space.isEtale_baseMap_finiteOpenSubspacePresheaf C S hS G.source
        hs_sep hs_lft)
  exact {
    unit := identitySection G
    unit_source := identitySection_source G
    unit_identity := identitySection_spec G
    objects := objects
    objectProjection := objectProjection
    objectProjection_etale := hObjectProjectionEtale
    objectsEquiv := Iso.refl _
    objectProjection_spec := by rfl
    universalOpen := universalOpen
    universalOpen_base := hbase
    universalOpen_spec := by rfl
    universalOpen_containsUnit :=
      containsSection_of_range_le G.source (identitySection G) (identitySection_source G)
        objects q.toSubfunctor.ι (Subfunctor.range_ι _).le
    universalOpen_closed := AlgebraicGeometry.Space.FiniteOpenSubspace.isClosedSubspace
      C S hS G.source objects universalOpen hs_sep
  }

/-- **Stacks 04RU, clause (3).** The groupoid in algebraic spaces
`(U', Z_univ, s', t', c')` carried by the finite part of `(U, R, s, t, c)`, together with its
canonical morphism of groupoids to `(U, R, s, t, c)` over `B`. -/
@[stacks 04RU "clause (3), the groupoid structure on the finite part and its morphism to R"]
public structure FinitePartGroupoid
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B) where
  /-- The unit `e` of the given groupoid. -/
  unit : G.objects ⟶ G.arrows
  /-- The unit is a section of the source morphism. -/
  unit_source : unit.hom ≫ G.source.hom = 𝟙 G.objects.obj
  /-- The unit induces the identity arrow at every point of every test scheme. -/
  unit_identity : ∀ T x, unit.hom.app T x = G.toGroupoidInFunctors.identity T x
  /-- The groupoid `(U', Z_univ, s', t', c')` on the finite part. -/
  groupoid : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B
  /-- Its canonical morphism of groupoids over `B` to the given groupoid. -/
  hom : AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom groupoid G
  /-- The projection `g : U' ⟶ U` on objects. -/
  objectProjection : groupoid.objects ⟶ G.objects
  /-- The morphism of groupoids acts on objects by that projection. -/
  objectProjection_eq : objectProjection.hom = hom.toGroupoidHom.mapObjects
  /-- The projection is étale. -/
  objectProjection_etale : AlgebraicGeometry.Space.IsEtale C S hS objectProjection.hom
  /-- The new space of objects is the finite part of the source containing the unit. -/
  objectsEquiv : groupoid.objects.obj ≅
    (finitePartWithSection C S hS G.source unit unit_source).toSubfunctor.toFunctor
  /-- Under that identification the projection is the one of the finite part. -/
  objectProjection_spec : objectProjection.hom =
    objectsEquiv.hom ≫
      (finitePartWithSection C S hS G.source unit unit_source).toSubfunctor.ι ≫
      (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap
  /-- The universal finite open subspace `Z_univ ⊂ R ×_{s, U, g} U'`. -/
  universalOpen :
    AlgebraicGeometry.Space.FiniteOpenSubspace C S hS G.source groupoid.objects
  /-- Its ambient fibre product is taken along the projection. -/
  universalOpen_base : universalOpen.toBase = objectProjection
  /-- It is the pair classified by the inclusion of the new space of objects. -/
  universalOpen_spec :
    (finiteOpenSubspaceEquiv C S hS G.source groupoid.objects).1
      (objectsEquiv.hom ≫
        (finitePartWithSection C S hS G.source unit unit_source).toSubfunctor.ι) =
      universalOpen
  /-- It contains the base change of the unit. -/
  universalOpen_containsUnit :
    AlgebraicGeometry.Space.ContainsSection C S hS G.source unit unit_source universalOpen
  /-- It is also closed in the ambient fibre product. -/
  universalOpen_closed : AlgebraicGeometry.Space.IsClosedSubspace C S hS universalOpen.subspace
  /-- The new space of arrows is that universal finite open subspace. -/
  arrows_eq : groupoid.arrows.obj = universalOpen.subspace.toFunctor
  /-- The new source `s'` is the first projection of the ambient fibre product. -/
  source_eq : groupoid.source.hom =
    eqToHom arrows_eq ≫ universalOpen.subspace.ι ≫
      pullback.fst universalOpen.toBase.hom G.source.hom
  /-- The morphism of groupoids acts on arrows by the second projection. -/
  arrowProjection_eq : hom.toGroupoidHom.mapArrows =
    eqToHom arrows_eq ≫ universalOpen.subspace.ι ≫
      pullback.snd universalOpen.toBase.hom G.source.hom

/-- **Stacks 04RU, clause (3).** For a groupoid in algebraic spaces over `B` whose source and
target are separated and locally of finite type, the finite part carries a groupoid
`(U', Z_univ, s', t', c')` together with a morphism of groupoids to `(U, R, s, t, c)`. -/
@[stacks 04RU "clause (3), the groupoid structure on the finite part and its morphism to R"]
public theorem nonempty_finitePartGroupoid
    {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
    (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B)
    (hs_sep : AlgebraicGeometry.Space.IsSeparated C S hS G.source.hom)
    (_ht_sep : AlgebraicGeometry.Space.IsSeparated C S hS G.target.hom)
    (hs_lft : AlgebraicGeometry.Space.IsLocallyOfFiniteType C S hS G.source.hom)
    (_ht_lft : AlgebraicGeometry.Space.IsLocallyOfFiniteType C S hS G.target.hom) :
    Nonempty (FinitePartGroupoid G) := by
  refine ⟨?_⟩
  classical
  let P := AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source
  let q := finitePartWithSection C S hS G.source
    (identitySection G) (identitySection_source G)
  have hP : AlgebraicGeometry.IsAlgebraicSpace C S hS P.toFunctor :=
    isAlgebraicSpace_finiteOpenSubspacePresheaf C S hS G.source
      hs_sep hs_lft
  have hqOpen : AlgebraicGeometry.Space.IsOpenSubspace C S hS q.toSubfunctor :=
    isOpenSubspace_finitePartWithSection C S hS G.source
      (identitySection G) (identitySection_source G) hP
  let objects : AlgebraicGeometry.AlgebraicSpaces C S hS :=
    ⟨q.toSubfunctor.toFunctor, hqOpen.1⟩
  let objectProjection : objects ⟶ G.objects :=
    ObjectProperty.homMk (q.toSubfunctor.ι ≫ P.baseMap)
  let universalOpen : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS G.source objects :=
    (finiteOpenSubspaceEquiv C S hS G.source objects).1
      q.toSubfunctor.ι
  have hbase : universalOpen.toBase = objectProjection := by
    apply ObjectProperty.hom_ext
    exact finiteOpenSubspaceEquiv_base G.source objects q.toSubfunctor.ι
  have hObjectProjectionEtale :
      AlgebraicGeometry.Space.IsEtale C S hS objectProjection.hom := by
    show AlgebraicGeometry.Space.IsEtale C S hS (q.toSubfunctor.ι ≫ P.baseMap)
    exact AlgebraicGeometry.Space.isEtale_comp C S hS
      (isEtale_of_openImmersion q.toSubfunctor.ι hqOpen.2)
      (isEtale_baseMap_finiteOpenSubspacePresheaf C S hS G.source
        hs_sep hs_lft)
  let arrows : AlgebraicGeometry.AlgebraicSpaces C S hS :=
    ⟨universalOpen.subspace.toFunctor, universalOpen.isOpen.1⟩
  let sourceMap : arrows ⟶ objects := ObjectProperty.homMk
    (universalOpen.subspace.ι ≫ pullback.fst universalOpen.toBase.hom G.source.hom)
  let arrowProjection : arrows ⟶ G.arrows := ObjectProperty.homMk
    (universalOpen.subspace.ι ≫ pullback.snd universalOpen.toBase.hom G.source.hom)
  have hbaseHom : universalOpen.toBase.hom = objectProjection.hom :=
    congrArg (fun f => f.hom) hbase
  let sourceFiberBase : arrows ⟶ G.objects := sourceMap ≫ universalOpen.toBase
  let toSourceFiber : pullback sourceFiberBase.hom G.source.hom ⟶
      pullback universalOpen.toBase.hom G.source.hom :=
    pullback.lift
      (pullback.fst sourceFiberBase.hom G.source.hom ≫ sourceMap.hom)
      (pullback.snd sourceFiberBase.hom G.source.hom)
      (by
        calc
          (pullback.fst sourceFiberBase.hom G.source.hom ≫ sourceMap.hom) ≫
              universalOpen.toBase.hom =
              pullback.fst sourceFiberBase.hom G.source.hom ≫
                (sourceMap.hom ≫ universalOpen.toBase.hom) := by
                  rw [Category.assoc]
          _ = pullback.snd sourceFiberBase.hom G.source.hom ≫ G.source.hom :=
            pullback.condition)
  have hOldFiber : AlgebraicGeometry.IsAlgebraicSpace C S hS
      (pullback universalOpen.toBase.hom G.source.hom) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback C S hS universalOpen.toBase.hom G.source.hom
      hqOpen.1 G.arrows.property G.objects.property
  have hNewFiber : AlgebraicGeometry.IsAlgebraicSpace C S hS
      (pullback sourceFiberBase.hom G.source.hom) :=
    AlgebraicGeometry.isAlgebraicSpace_pullback C S hS sourceFiberBase.hom G.source.hom
      arrows.property G.arrows.property G.objects.property
  let sourcePair : AlgebraicGeometry.Space.FiniteOpenSubspace C S hS G.source arrows := {
    toBase := sourceFiberBase
    subspace := universalOpen.subspace.preimage toSourceFiber
    isOpen := openSubspace_preimage C S hS toSourceFiber universalOpen.subspace
      hOldFiber hNewFiber universalOpen.isOpen
    finite_projection := by
      have hpre := Subfunctor.isPullback_preimage toSourceFiber universalOpen.subspace
      have hbc : IsPullback toSourceFiber
          (pullback.fst sourceFiberBase.hom G.source.hom)
          (pullback.fst universalOpen.toBase.hom G.source.hom) sourceMap.hom := by
        dsimp [toSourceFiber, sourceFiberBase]
        exact pullback_restrict_isPullback sourceMap.hom universalOpen.toBase.hom G.source.hom
      have hproj : IsPullback (universalOpen.subspace.fromPreimage toSourceFiber)
          ((universalOpen.subspace.preimage toSourceFiber).ι ≫
            pullback.fst sourceFiberBase.hom G.source.hom)
          (universalOpen.subspace.ι ≫ pullback.fst universalOpen.toBase.hom G.source.hom)
          sourceMap.hom := by
        convert hpre.paste_vert hbc using 1
      exact isFinite_of_isPullback C S hS hproj universalOpen.finite_projection
  }
  have hsourcePairBase : sourcePair.toBase.hom = arrowProjection.hom ≫ G.source.hom := by
    show (sourceMap.hom ≫ universalOpen.toBase.hom) =
      arrowProjection.hom ≫ G.source.hom
    show (universalOpen.subspace.ι ≫
      pullback.fst universalOpen.toBase.hom G.source.hom) ≫ universalOpen.toBase.hom = _
    calc
      (universalOpen.subspace.ι ≫
          pullback.fst universalOpen.toBase.hom G.source.hom) ≫ universalOpen.toBase.hom =
          universalOpen.subspace.ι ≫
            (pullback.fst universalOpen.toBase.hom G.source.hom ≫
              universalOpen.toBase.hom) := by simp [Category.assoc, hbaseHom]
      _ = universalOpen.subspace.ι ≫
          (pullback.snd universalOpen.toBase.hom G.source.hom ≫ G.source.hom) := by
            rw [pullback.condition]
      _ = (universalOpen.subspace.ι ≫
          pullback.snd universalOpen.toBase.hom G.source.hom) ≫ G.source.hom :=
            (Category.assoc _ _ _).symm
  let sourceUnitPair : arrows.obj ⟶ pullback sourcePair.toBase.hom G.source.hom :=
    pullback.lift (𝟙 arrows.obj) arrowProjection.hom (by simpa using hsourcePairBase)
  have hsourceUnitPair : sourceUnitPair ≫ toSourceFiber = universalOpen.subspace.ι := by
    have hf : toSourceFiber ≫ pullback.fst universalOpen.toBase.hom G.source.hom =
        pullback.fst sourceFiberBase.hom G.source.hom ≫ sourceMap.hom :=
      pullback.lift_fst _ _ _
    have hg : toSourceFiber ≫ pullback.snd universalOpen.toBase.hom G.source.hom =
        pullback.snd sourceFiberBase.hom G.source.hom := pullback.lift_snd _ _ _
    have hu : sourceUnitPair ≫ pullback.fst sourceFiberBase.hom G.source.hom =
        𝟙 arrows.obj := pullback.lift_fst _ _ _
    have hv : sourceUnitPair ≫ pullback.snd sourceFiberBase.hom G.source.hom =
        arrowProjection.hom := pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · rw [Category.assoc, hf, ← Category.assoc, hu, Category.id_comp]
      rfl
    · rw [Category.assoc, hg, hv]
      rfl
  have hsourceUnitPair_mem : Subfunctor.range sourceUnitPair ≤ sourcePair.subspace := by
    intro V a ha
    obtain ⟨a, rfl⟩ := ha
    show toSourceFiber.app V (sourceUnitPair.app V a) ∈ universalOpen.subspace.obj V
    have hv := congrArg (fun f => f.app V a) hsourceUnitPair
    have hv' : ConcreteCategory.hom (toSourceFiber.app V)
          (ConcreteCategory.hom (sourceUnitPair.app V) a) =
        ConcreteCategory.hom (universalOpen.subspace.ι.app V) a := by
      simpa only [NatTrans.comp_app, CategoryTheory.hom_comp, Function.comp_apply] using hv
    rw [hv']
    exact a.property
  let sourceUnitLift : arrows.obj ⟶ sourcePair.subspace.toFunctor :=
    Subfunctor.lift sourceUnitPair hsourceUnitPair_mem
  have hsourceUnitLift : sourceUnitLift ≫ sourcePair.subspace.ι = sourceUnitPair :=
    Subfunctor.lift_ι _ _
  let H := G.toGroupoidInFunctors
  have hTranslatedSection := translateFiniteOpenPair_containsSection H
    G.objects.property G.arrows.property arrows arrowProjection.hom sourcePair
    hsourcePairBase (identitySection G).hom
    (identitySection_source G)
    (identitySection_spec G) sourceUnitLift hsourceUnitLift
  let translatedPair := translateFiniteOpenPair H G.objects.property G.arrows.property
    arrows arrowProjection.hom sourcePair hsourcePairBase
  let targetClassifier : arrows.obj ⟶ P.toFunctor :=
    (finiteOpenSubspaceEquiv C S hS G.source arrows).1.symm translatedPair
  have htargetPair :
      (finiteOpenSubspaceEquiv C S hS G.source arrows).1 targetClassifier =
        translatedPair := Equiv.apply_symm_apply _ _
  have htargetRange : Subfunctor.range targetClassifier ≤ q.toSubfunctor := by
    apply finiteOpenSubspaceEquiv_containsSection G.source (identitySection G)
      (identitySection_source G) arrows targetClassifier
    rw [htargetPair]
    exact hTranslatedSection
  let targetMap : arrows ⟶ objects :=
    ObjectProperty.homMk (Subfunctor.lift targetClassifier htargetRange)
  have htargetProjection : targetMap.hom ≫ objectProjection.hom =
      arrowProjection.hom ≫ G.target.hom := by
    show (Subfunctor.lift targetClassifier htargetRange) ≫
      (q.toSubfunctor.ι ≫ P.baseMap) = _
    rw [← Category.assoc, Subfunctor.lift_ι]
    rw [← finiteOpenSubspaceEquiv_base G.source arrows targetClassifier, htargetPair]
    rfl
  have hsourceProjection : sourceMap.hom ≫ objectProjection.hom =
      arrowProjection.hom ≫ G.source.hom := by
    rw [← hbaseHom]
    exact hsourcePairBase
  have hsourcePairFiber (V) (a : arrows.obj.obj V) (z : G.arrows.obj.obj V) :
      finitePairFiber sourcePair V a z ↔
        finitePairFiber universalOpen V (sourceMap.hom.app V a) z := by
    have hpre := Subfunctor.isPullback_preimage toSourceFiber universalOpen.subspace
    have hbc : IsPullback toSourceFiber
        (pullback.fst sourceFiberBase.hom G.source.hom)
        (pullback.fst universalOpen.toBase.hom G.source.hom) sourceMap.hom :=
      pullback_restrict_isPullback sourceMap.hom universalOpen.toBase.hom G.source.hom
    have hproj := hpre.paste_vert hbc
    exact finitePairFiber_baseChange universalOpen sourcePair sourceMap.hom
      (universalOpen.subspace.fromPreimage toSourceFiber) hproj.flip (by
        rw [Subfunctor.fromPreimage_ι_assoc]
        show _ = sourcePair.subspace.ι ≫ pullback.snd sourceFiberBase.hom G.source.hom
        rw [pullback.lift_snd]) V a z
  have htargetFiber (V) (a : arrows.obj.obj V) (z : G.arrows.obj.obj V)
      (hz : G.source.hom.app V z = G.target.hom.app V (arrowProjection.hom.app V a)) :
      finitePairFiber universalOpen V (targetMap.hom.app V a) z ↔
        finitePairFiber universalOpen V (sourceMap.hom.app V a)
          (H.compose V z (arrowProjection.hom.app V a) hz) := by
    have h := finitePairFiber_classified_comp G.source q.toSubfunctor.ι targetClassifier
      targetMap.hom (Subfunctor.lift_ι targetClassifier htargetRange) V a z
    change finitePairFiber universalOpen V (targetMap.hom.app V a) z ↔
      finitePairFiber _ V a z at h
    rw [htargetPair] at h
    exact h.trans ((finitePairFiber_translate H G.objects.property G.arrows.property
      arrows arrowProjection.hom sourcePair hsourcePairBase V a z hz).trans
      (hsourcePairFiber V a _))
  have harrowExt (V) (a b : arrows.obj.obj V)
      (hs : sourceMap.hom.app V a = sourceMap.hom.app V b)
      (hp : arrowProjection.hom.app V a = arrowProjection.hom.app V b) : a = b := by
    apply Subtype.ext
    exact presheafPullback_ext _ _ V hs hp
  have hobjectExt (V) (x y : objects.obj.obj V)
      (hb : objectProjection.hom.app V x = objectProjection.hom.app V y)
      (hf : ∀ W (k : V ⟶ W) z,
        finitePairFiber universalOpen W (objects.obj.map k x) z ↔
        finitePairFiber universalOpen W (objects.obj.map k y) z) : x = y := by
    apply Subtype.ext
    apply (P.sections V.unop).injective
    apply finitePair_ext
    · rw [← P.baseMap_spec, ← P.baseMap_spec]
      exact congrArg yonedaEquiv.symm hb
    · intro W k z
      exact (finitePairFiber_section G.source q.toSubfunctor.ι V W x k z).trans
        ((hf W k.op z).trans
          (finitePairFiber_section G.source q.toSubfunctor.ι V W y k z).symm)
  have hUniversalUnit : AlgebraicGeometry.Space.ContainsSection C S hS G.source
      (identitySection G) (identitySection_source G) universalOpen :=
    containsSection_of_range_le G.source (identitySection G) (identitySection_source G)
      objects q.toSubfunctor.ι (Subfunctor.range_ι _).le
  let unitNat : objects.obj ⟶ arrows.obj := hUniversalUnit.choose
  have hunitNat : unitNat ≫ universalOpen.subspace.ι =
      pullback.lift (𝟙 objects.obj)
        (universalOpen.toBase.hom ≫ (identitySection G).hom) (by
          simp only [Category.id_comp, Category.assoc, identitySection_source,
            Category.comp_id]) := hUniversalUnit.choose_spec
  have hunitSource : unitNat ≫ sourceMap.hom = 𝟙 objects.obj := by
    show unitNat ≫ (universalOpen.subspace.ι ≫ pullback.fst _ _) = _
    rw [← Category.assoc, hunitNat, pullback.lift_fst]
  have hunitProjection : unitNat ≫ arrowProjection.hom =
      objectProjection.hom ≫ (identitySection G).hom := by
    show unitNat ≫ (universalOpen.subspace.ι ≫ pullback.snd _ _) = _
    rw [← Category.assoc, hunitNat, pullback.lift_snd, hbaseHom]
  have hunitTargetProjection : (unitNat ≫ targetMap.hom) ≫ objectProjection.hom =
      objectProjection.hom := by
    rw [Category.assoc, htargetProjection, ← Category.assoc, hunitProjection,
      Category.assoc, identitySection_target, Category.comp_id]
  have hunitTargetPoint : ∀ (V : (AlgebraicGeometry.BigFppfOver C S hS)ᵒᵖ)
      (x : objects.obj.obj V), targetMap.hom.app V (unitNat.app V x) = x := by
    intro V x
    apply hobjectExt V (targetMap.hom.app V (unitNat.app V x)) x
      (congrArg (fun k => k.app V x) hunitTargetProjection)
    intro W k z
    rw [← NatTrans.naturality_apply targetMap.hom, ← NatTrans.naturality_apply unitNat]
    let y := objects.obj.map k x
    show finitePairFiber universalOpen W (targetMap.hom.app W (unitNat.app W y)) z ↔
      finitePairFiber universalOpen W y z
    have hbaseY : objectProjection.hom.app W (targetMap.hom.app W (unitNat.app W y)) =
        objectProjection.hom.app W y := congrArg (fun k => k.app W y) hunitTargetProjection
    by_cases hz : G.source.hom.app W z = objectProjection.hom.app W y
    · have he : arrowProjection.hom.app W (unitNat.app W y) =
          H.identity W (objectProjection.hom.app W y) :=
        (congrArg (fun k => k.app W y) hunitProjection).trans
          (identitySection_spec G W _)
      have hsz : G.source.hom.app W z =
          G.target.hom.app W (arrowProjection.hom.app W (unitNat.app W y)) := by
        rw [he]
        exact hz.trans (H.evaluationArrowEquiv W _ _ (𝟙 _)).property.2.symm
      rw [htargetFiber W _ z hsz]
      have hsy : sourceMap.hom.app W (unitNat.app W y) = y :=
        congrArg (fun k => k.app W y) hunitSource
      rw [hsy]
      have hc : H.compose W z (arrowProjection.hom.app W (unitNat.app W y)) hsz = z := by
        have he' : arrowProjection.hom.app W (unitNat.app W y) =
            H.identity W (H.source.app W z) := he.trans (congrArg (H.identity W) hz.symm)
        have hright : H.source.app W z =
            H.target.app W (H.identity W (H.source.app W z)) :=
          hsz.trans (congrArg (H.target.app W) he')
        exact (groupoidCompose_congr_second H W z _ _ hsz hright he').trans
          (groupoidCompose_identity_right H W z hright)
      rw [hc]
    · constructor <;> intro h
      · exfalso
        have hb := finitePairFiber_projection universalOpen W h
        rw [hbaseHom] at hb
        exact hz (hb.symm.trans hbaseY)
      · exfalso
        have hb := finitePairFiber_projection universalOpen W h
        rw [hbaseHom] at hb
        exact hz hb.symm
  have hunitTarget : unitNat ≫ targetMap.hom = 𝟙 objects.obj := by
    ext V x
    exact hunitTargetPoint V x
  have hcomposable (V) (a b : arrows.obj.obj V)
      (h : sourceMap.hom.app V a = targetMap.hom.app V b) :
      H.source.app V (arrowProjection.hom.app V a) =
        H.target.app V (arrowProjection.hom.app V b) :=
    (congrArg (fun k => k.app V a) hsourceProjection).symm.trans
      ((congrArg (objectProjection.hom.app V) h).trans
        (congrArg (fun k => k.app V b) htargetProjection))
  have hcompExists (V) (a b : arrows.obj.obj V)
      (h : sourceMap.hom.app V a = targetMap.hom.app V b) :
      ∃ c : arrows.obj.obj V, sourceMap.hom.app V c = sourceMap.hom.app V b ∧
        arrowProjection.hom.app V c = H.compose V
          (arrowProjection.hom.app V a) (arrowProjection.hom.app V b) (hcomposable V a b h) := by
    apply (htargetFiber V b (arrowProjection.hom.app V a) (hcomposable V a b h)).mp
    exact ⟨a, h, rfl⟩
  let composeLift V (a b : arrows.obj.obj V)
      (h : sourceMap.hom.app V a = targetMap.hom.app V b) : arrows.obj.obj V :=
    (hcompExists V a b h).choose
  have hcompSource V a b h :
      sourceMap.hom.app V (composeLift V a b h) = sourceMap.hom.app V b :=
    (hcompExists V a b h).choose_spec.1
  have hcompProjection V a b h :
      arrowProjection.hom.app V (composeLift V a b h) = H.compose V
        (arrowProjection.hom.app V a) (arrowProjection.hom.app V b) (hcomposable V a b h) :=
    (hcompExists V a b h).choose_spec.2
  have hcompTargetProjection (V) (a b c : arrows.obj.obj V)
      (hab : sourceMap.hom.app V a = targetMap.hom.app V b)
      (hc : arrowProjection.hom.app V c = H.compose V
        (arrowProjection.hom.app V a) (arrowProjection.hom.app V b) (hcomposable V a b hab)) :
      objectProjection.hom.app V (targetMap.hom.app V c) =
        objectProjection.hom.app V (targetMap.hom.app V a) := by
    calc
      _ = G.target.hom.app V (arrowProjection.hom.app V c) :=
        congrArg (fun k => k.app V c) htargetProjection
      _ = G.target.hom.app V (arrowProjection.hom.app V a) := by
        rw [hc]
        exact groupoidCompose_target H V _ _ _
      _ = _ := (congrArg (fun k => k.app V a) htargetProjection).symm
  have hcompTargetFiber (V) (a b c : arrows.obj.obj V)
      (hab : sourceMap.hom.app V a = targetMap.hom.app V b)
      (hs : sourceMap.hom.app V c = sourceMap.hom.app V b)
      (hc : arrowProjection.hom.app V c = H.compose V
        (arrowProjection.hom.app V a) (arrowProjection.hom.app V b) (hcomposable V a b hab))
      (z : G.arrows.obj.obj V) :
      finitePairFiber universalOpen V (targetMap.hom.app V c) z ↔
        finitePairFiber universalOpen V (targetMap.hom.app V a) z := by
    by_cases hz : G.source.hom.app V z = G.target.hom.app V (arrowProjection.hom.app V a)
    · have hzc : G.source.hom.app V z =
          G.target.hom.app V (arrowProjection.hom.app V c) := by
        rw [hc]
        exact hz.trans (groupoidCompose_target H V _ _ _).symm
      have hzb : H.source.app V
          (H.compose V z (arrowProjection.hom.app V a) hz) =
          H.target.app V (arrowProjection.hom.app V b) :=
        (groupoidCompose_source H V _ _ _).trans (hcomposable V a b hab)
      rw [htargetFiber V c z hzc, hs, htargetFiber V a z hz, hab,
        htargetFiber V b _ hzb]
      have he : H.compose V z (arrowProjection.hom.app V c) hzc =
          H.compose V (H.compose V z (arrowProjection.hom.app V a) hz)
            (arrowProjection.hom.app V b) hzb := by
        have hza : H.source.app V z = H.target.app V
            (H.compose V (arrowProjection.hom.app V a)
              (arrowProjection.hom.app V b) (hcomposable V a b hab)) :=
          hz.trans (groupoidCompose_target H V _ _ _).symm
        exact (groupoidCompose_congr_second H V z _ _ hzc hza hc).trans
          (groupoidCompose_assoc H V z (arrowProjection.hom.app V a)
            (arrowProjection.hom.app V b) hz (hcomposable V a b hab) hzb hza).symm
      rw [he]
    · have hbaseA : objectProjection.hom.app V (targetMap.hom.app V a) =
          G.target.hom.app V (arrowProjection.hom.app V a) :=
        congrArg (fun k => k.app V a) htargetProjection
      constructor <;> intro h <;> exfalso
      · have hb := finitePairFiber_projection universalOpen V h
        rw [hbaseHom] at hb
        exact hz (hb.symm.trans ((hcompTargetProjection V a b c hab hc).trans hbaseA))
      · have hb := finitePairFiber_projection universalOpen V h
        rw [hbaseHom] at hb
        exact hz (hb.symm.trans hbaseA)
  have hcompTarget V a b h : targetMap.hom.app V (composeLift V a b h) =
      targetMap.hom.app V a := by
    apply hobjectExt V _ _ (hcompTargetProjection V a b _ h (hcompProjection V a b h))
    intro W k z
    rw [← NatTrans.naturality_apply targetMap.hom, ← NatTrans.naturality_apply targetMap.hom]
    have hab : sourceMap.hom.app W (arrows.obj.map k a) =
        targetMap.hom.app W (arrows.obj.map k b) := by
      simpa only [NatTrans.naturality_apply] using congrArg (objects.obj.map k) h
    apply hcompTargetFiber W (arrows.obj.map k a) (arrows.obj.map k b) _ hab
    · simpa only [NatTrans.naturality_apply] using
        congrArg (objects.obj.map k) (hcompSource V a b h)
    · simp only [NatTrans.naturality_apply]
      rw [hcompProjection V a b h]
      exact groupoidCompose_natural H k _ _ _ _
  have hinverseExists (V) (a : arrows.obj.obj V) :
      ∃ b : arrows.obj.obj V, sourceMap.hom.app V b = targetMap.hom.app V a ∧
        arrowProjection.hom.app V b =
          Deformation.inverseArrow H V (arrowProjection.hom.app V a) := by
    apply (htargetFiber V a _ (inverseArrow_source_functor H V _)).mpr
    rw [groupoidCompose_inverse_left H V (arrowProjection.hom.app V a) _]
    refine ⟨unitNat.app V (sourceMap.hom.app V a),
      congrArg (fun k => k.app V (sourceMap.hom.app V a)) hunitSource, ?_⟩
    have he := congrArg (fun k => k.app V (sourceMap.hom.app V a)) hunitProjection
    exact he.trans ((identitySection_spec G V _).trans
      (congrArg (H.identity V) (congrArg (fun k => k.app V a) hsourceProjection)))
  let inverseLift V (a : arrows.obj.obj V) : arrows.obj.obj V := (hinverseExists V a).choose
  have hinverseSource V a : sourceMap.hom.app V (inverseLift V a) = targetMap.hom.app V a :=
    (hinverseExists V a).choose_spec.1
  have hinverseProjection V a : arrowProjection.hom.app V (inverseLift V a) =
      Deformation.inverseArrow H V (arrowProjection.hom.app V a) :=
    (hinverseExists V a).choose_spec.2
  have hinverseTarget V a : targetMap.hom.app V (inverseLift V a) = sourceMap.hom.app V a := by
    let b := inverseLift V a
    let h := hinverseSource V a
    have hc : composeLift V b a h = unitNat.app V (sourceMap.hom.app V a) := by
      apply harrowExt V
      · exact (hcompSource V b a h).trans
          (congrArg (fun k => k.app V (sourceMap.hom.app V a)) hunitSource).symm
      · rw [hcompProjection V b a h]
        have hba : H.source.app V (arrowProjection.hom.app V b) =
            H.target.app V (arrowProjection.hom.app V a) := hcomposable V b a h
        have hia : H.source.app V
            (Deformation.inverseArrow H V (arrowProjection.hom.app V a)) =
            H.target.app V (arrowProjection.hom.app V a) :=
          inverseArrow_source_functor H V _
        have he : H.compose V (arrowProjection.hom.app V b) (arrowProjection.hom.app V a) hba =
            H.identity V (H.source.app V (arrowProjection.hom.app V a)) :=
          (groupoidCompose_congr_first H V _ _ _ hba hia
            (hinverseProjection V a)).trans
            (groupoidCompose_inverse_left H V _ hia)
        exact he.trans (congrArg (H.identity V)
          (congrArg (fun k => k.app V a) hsourceProjection).symm) |>.trans
          ((identitySection_spec G V _).symm.trans
            (congrArg (fun k => k.app V (sourceMap.hom.app V a)) hunitProjection).symm)
    exact (hcompTarget V b a h).symm.trans
      ((congrArg (targetMap.hom.app V) hc).trans
        (congrArg (fun k => k.app V (sourceMap.hom.app V a)) hunitTarget))
  let compNat : pullback sourceMap.hom targetMap.hom ⟶ arrows.obj := {
    app V := ↾ fun p => composeLift V
      ((pullback.fst sourceMap.hom targetMap.hom).app V p)
      ((pullback.snd sourceMap.hom targetMap.hom).app V p)
      (congrArg (fun k => k.app V p)
        (pullback.condition (f := sourceMap.hom) (g := targetMap.hom)))
    naturality := by
      intro V W k
      ext p
      let pW := (pullback sourceMap.hom targetMap.hom).map k p
      have hpV : sourceMap.hom.app V ((pullback.fst sourceMap.hom targetMap.hom).app V p) =
          targetMap.hom.app V ((pullback.snd sourceMap.hom targetMap.hom).app V p) :=
        congrArg (fun f => f.app V p) (pullback.condition (f := sourceMap.hom) (g := targetMap.hom))
      have hpW : sourceMap.hom.app W ((pullback.fst sourceMap.hom targetMap.hom).app W pW) =
          targetMap.hom.app W ((pullback.snd sourceMap.hom targetMap.hom).app W pW) :=
        congrArg (fun f => f.app W pW)
          (pullback.condition (f := sourceMap.hom) (g := targetMap.hom))
      apply harrowExt W
      · show sourceMap.hom.app W (composeLift W _ _ hpW) =
          sourceMap.hom.app W (arrows.obj.map k (composeLift V _ _ hpV))
        calc
          _ = sourceMap.hom.app W ((pullback.snd sourceMap.hom targetMap.hom).app W pW) :=
            hcompSource W _ _ hpW
          _ = sourceMap.hom.app W
              (arrows.obj.map k ((pullback.snd sourceMap.hom targetMap.hom).app V p)) := by
            rw [(NatTrans.naturality_apply
              (pullback.snd sourceMap.hom targetMap.hom) k p)]
          _ = objects.obj.map k
              (sourceMap.hom.app V ((pullback.snd sourceMap.hom targetMap.hom).app V p)) :=
            NatTrans.naturality_apply sourceMap.hom k _
          _ = objects.obj.map k
              (sourceMap.hom.app V (composeLift V _ _ hpV)) :=
            congrArg (objects.obj.map k) (hcompSource V _ _ hpV).symm
          _ = _ := (NatTrans.naturality_apply sourceMap.hom k _).symm
      · show arrowProjection.hom.app W (composeLift W _ _ hpW) =
          arrowProjection.hom.app W (arrows.obj.map k (composeLift V _ _ hpV))
        let aV := (pullback.fst sourceMap.hom targetMap.hom).app V p
        let bV := (pullback.snd sourceMap.hom targetMap.hom).app V p
        let aW := (pullback.fst sourceMap.hom targetMap.hom).app W pW
        let bW := (pullback.snd sourceMap.hom targetMap.hom).app W pW
        have ha : arrows.obj.map k aV = aW :=
          (NatTrans.naturality_apply
            (pullback.fst sourceMap.hom targetMap.hom) k p).symm
        have hb : arrows.obj.map k bV = bW :=
          (NatTrans.naturality_apply
            (pullback.snd sourceMap.hom targetMap.hom) k p).symm
        have ha' : H.arrows.map k (arrowProjection.hom.app V aV) =
            arrowProjection.hom.app W aW := by
          calc
            _ = arrowProjection.hom.app W (arrows.obj.map k aV) :=
              (NatTrans.naturality_apply arrowProjection.hom k aV).symm
            _ = _ := congrArg (arrowProjection.hom.app W) ha
        have hb' : H.arrows.map k (arrowProjection.hom.app V bV) =
            arrowProjection.hom.app W bW := by
          calc
            _ = arrowProjection.hom.app W (arrows.obj.map k bV) :=
              (NatTrans.naturality_apply arrowProjection.hom k bV).symm
            _ = _ := congrArg (arrowProjection.hom.app W) hb
        show arrowProjection.hom.app W (composeLift W aW bW hpW) =
          arrowProjection.hom.app W (arrows.obj.map k (composeLift V aV bV hpV))
        have hnat := (groupoidCompose_natural_of_eq H k
          (arrowProjection.hom.app V aV) (arrowProjection.hom.app V bV)
          (arrowProjection.hom.app W aW) (arrowProjection.hom.app W bW)
          (hcomposable V aV bV hpV) (hcomposable W aW bW hpW) ha' hb').symm
        exact (hcompProjection W aW bW hpW).trans
          (hnat.trans ((congrArg (H.arrows.map k)
            (hcompProjection V aV bV hpV).symm).trans
            (NatTrans.naturality_apply arrowProjection.hom k _).symm))
  }
  have hcompNat_app (V) (a b : arrows.obj.obj V)
      (h : sourceMap.hom.app V a = targetMap.hom.app V b) :
      compNat.app V ((composableToPullback sourceMap.hom targetMap.hom).app V ⟨(a, b), h⟩) =
        composeLift V a b h := by
    show composeLift V
      ((pullback.fst sourceMap.hom targetMap.hom).app V
        ((composableToPullback sourceMap.hom targetMap.hom).app V ⟨(a, b), h⟩))
      ((pullback.snd sourceMap.hom targetMap.hom).app V
        ((composableToPullback sourceMap.hom targetMap.hom).app V ⟨(a, b), h⟩))
      (congrArg (fun k => k.app V
        ((composableToPullback sourceMap.hom targetMap.hom).app V ⟨(a, b), h⟩))
        (pullback.condition (f := sourceMap.hom) (g := targetMap.hom))) = _
    simp only [composableToPullback_fst, composableToPullback_snd]
  have hcompNatProjection : compNat ≫ arrowProjection.hom =
      pullback.map sourceMap.hom targetMap.hom G.source.hom G.target.hom
        arrowProjection.hom arrowProjection.hom objectProjection.hom
        hsourceProjection htargetProjection ≫ G.comp.hom := by
    ext V p
    show arrowProjection.hom.app V (composeLift V
      ((pullback.fst sourceMap.hom targetMap.hom).app V p)
      ((pullback.snd sourceMap.hom targetMap.hom).app V p)
      (congrArg (fun k => k.app V p)
        (pullback.condition (f := sourceMap.hom) (g := targetMap.hom)))) = _
    rw [hcompProjection V _ _ (congrArg (fun k => k.app V p)
      (pullback.condition (f := sourceMap.hom) (g := targetMap.hom)))]
    show G.comp.hom.app V
      ((composableToPullback G.source.hom G.target.hom).app V _) = _
    apply congrArg (G.comp.hom.app V)
    apply presheafPullback_ext G.source.hom G.target.hom V
    · show (pullback.fst G.source.hom G.target.hom).app V
        ((composableToPullback G.source.hom G.target.hom).app V _) =
        (pullback.fst G.source.hom G.target.hom).app V
          ((pullback.map sourceMap.hom targetMap.hom G.source.hom G.target.hom
            arrowProjection.hom arrowProjection.hom objectProjection.hom
            hsourceProjection htargetProjection).app V p)
      show ((composableToPullback G.source.hom G.target.hom ≫
        pullback.fst G.source.hom G.target.hom).app V) _ = _
      simp only [composableToPullback, pullback.lift_fst]
      show ((pullback.fst sourceMap.hom targetMap.hom ≫ arrowProjection.hom).app V) p =
        ((pullback.map sourceMap.hom targetMap.hom G.source.hom G.target.hom
            arrowProjection.hom arrowProjection.hom objectProjection.hom
            hsourceProjection htargetProjection ≫
          pullback.fst G.source.hom G.target.hom).app V) p
      simp only [pullback.map, pullback.lift_fst]
    · show (pullback.snd G.source.hom G.target.hom).app V
        ((composableToPullback G.source.hom G.target.hom).app V _) =
        (pullback.snd G.source.hom G.target.hom).app V
          ((pullback.map sourceMap.hom targetMap.hom G.source.hom G.target.hom
            arrowProjection.hom arrowProjection.hom objectProjection.hom
            hsourceProjection htargetProjection).app V p)
      show ((composableToPullback G.source.hom G.target.hom ≫
        pullback.snd G.source.hom G.target.hom).app V) _ = _
      simp only [composableToPullback, pullback.lift_snd]
      show ((pullback.snd sourceMap.hom targetMap.hom ≫ arrowProjection.hom).app V) p =
        ((pullback.map sourceMap.hom targetMap.hom G.source.hom G.target.hom
            arrowProjection.hom arrowProjection.hom objectProjection.hom
            hsourceProjection htargetProjection ≫
          pullback.snd G.source.hom G.target.hom).app V) p
      simp only [pullback.map, pullback.lift_snd]
  let groupoid : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B := {
    objects := objects
    arrows := arrows
    objectsToBase := objectProjection ≫ G.objectsToBase
    arrowsToBase := arrowProjection ≫ G.arrowsToBase
    source := sourceMap
    target := targetMap
    source_over := by
      apply ObjectProperty.hom_ext
      show sourceMap.hom ≫ (objectProjection.hom ≫ G.objectsToBase.hom) =
        arrowProjection.hom ≫ G.arrowsToBase.hom
      rw [← Category.assoc, hsourceProjection, Category.assoc]
      exact congrArg (fun k => arrowProjection.hom ≫ k)
        (congrArg (fun k => k.hom) G.source_over)
    target_over := by
      apply ObjectProperty.hom_ext
      show targetMap.hom ≫ (objectProjection.hom ≫ G.objectsToBase.hom) =
        arrowProjection.hom ≫ G.arrowsToBase.hom
      rw [← Category.assoc, htargetProjection, Category.assoc]
      exact congrArg (fun k => arrowProjection.hom ≫ k)
        (congrArg (fun k => k.hom) G.target_over)
    comp := ObjectProperty.homMk compNat
    comp_over := by
      apply ObjectProperty.hom_ext
      show compNat ≫ (arrowProjection.hom ≫ G.arrowsToBase.hom) =
        pullback.fst sourceMap.hom targetMap.hom ≫
          (arrowProjection.hom ≫ G.arrowsToBase.hom)
      have hG : G.comp.hom ≫ G.arrowsToBase.hom =
          pullback.fst G.source.hom G.target.hom ≫ G.arrowsToBase.hom :=
        congrArg (fun k => k.hom) G.comp_over
      calc
        compNat ≫ (arrowProjection.hom ≫ G.arrowsToBase.hom) =
            (compNat ≫ arrowProjection.hom) ≫ G.arrowsToBase.hom :=
          (Category.assoc _ _ _).symm
        _ = (pullback.map sourceMap.hom targetMap.hom G.source.hom G.target.hom
              arrowProjection.hom arrowProjection.hom objectProjection.hom
              hsourceProjection htargetProjection ≫ G.comp.hom) ≫
              G.arrowsToBase.hom := by rw [hcompNatProjection]
        _ = pullback.map sourceMap.hom targetMap.hom G.source.hom G.target.hom
              arrowProjection.hom arrowProjection.hom objectProjection.hom
              hsourceProjection htargetProjection ≫
              (G.comp.hom ≫ G.arrowsToBase.hom) := Category.assoc _ _ _
        _ = pullback.map sourceMap.hom targetMap.hom G.source.hom G.target.hom
              arrowProjection.hom arrowProjection.hom objectProjection.hom
              hsourceProjection htargetProjection ≫
              (pullback.fst G.source.hom G.target.hom ≫ G.arrowsToBase.hom) :=
          congrArg
            (fun f => pullback.map sourceMap.hom targetMap.hom G.source.hom G.target.hom
              arrowProjection.hom arrowProjection.hom objectProjection.hom
              hsourceProjection htargetProjection ≫ f) hG
        _ = pullback.fst sourceMap.hom targetMap.hom ≫
              (arrowProjection.hom ≫ G.arrowsToBase.hom) := by
          have hf : pullback.map sourceMap.hom targetMap.hom
              G.source.hom G.target.hom arrowProjection.hom arrowProjection.hom
              objectProjection.hom hsourceProjection htargetProjection ≫
              pullback.fst G.source.hom G.target.hom =
              pullback.fst sourceMap.hom targetMap.hom ≫ arrowProjection.hom :=
            by simp only [pullback.map, pullback.lift_fst]
          rw [← Category.assoc, hf, Category.assoc]
    pointwiseGroupoid := by
      intro T
      let c : {p : arrows.obj.obj T × arrows.obj.obj T //
          sourceMap.hom.app T p.1 = targetMap.hom.app T p.2} → arrows.obj.obj T :=
        fun p => composeLift T p.val.1 p.val.2 p.property
      have hp := pointwiseGroupoid_of_lifts H T
        (sourceMap.hom.app T) (targetMap.hom.app T)
        (objectProjection.hom.app T) (arrowProjection.hom.app T)
        (fun a => (congrArg (fun k => k.app T a) hsourceProjection).symm)
        (fun a => (congrArg (fun k => k.app T a) htargetProjection).symm)
        (harrowExt T) (unitNat.app T)
        (fun x => congrArg (fun k => k.app T x) hunitSource)
        (fun x => congrArg (fun k => k.app T x) hunitTarget)
        (fun x => (congrArg (fun k => k.app T x) hunitProjection).trans
          (identitySection_spec G T _)) c
        (fun p => hcompSource T p.val.1 p.val.2 p.property)
        (fun p => hcompTarget T p.val.1 p.val.2 p.property)
        (fun p => hcompProjection T p.val.1 p.val.2 p.property)
        (inverseLift T) (hinverseSource T) (hinverseTarget T) (hinverseProjection T)
      convert hp using 1
      congr 1
      funext p
      exact hcompNat_app T p.val.1 p.val.2 p.property
  }
  let hom : AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom groupoid G := {
    toGroupoidHom := {
      mapObjects := objectProjection.hom
      mapArrows := arrowProjection.hom
      map_source := by
        intro T a
        exact (congrArg (fun k => k.app T a) hsourceProjection).symm
      map_target := by
        intro T a
        exact (congrArg (fun k => k.app T a) htargetProjection).symm
      map_id := by
        intro T x
        let N := groupoid.toGroupoidInFunctors
        let e := N.identity T x
        let : Groupoid (N.objects.obj T) := N.evaluationGroupoid T
        have hes : N.source.app T e = x := (N.evaluationArrowEquiv T x x (𝟙 x)).property.1
        have het : N.target.app T e = x := (N.evaluationArrowEquiv T x x (𝟙 x)).property.2
        have hpb : sourceMap.hom.app T e = targetMap.hom.app T e :=
          hes.trans het.symm
        have hec : N.compose T e e (hes.trans het.symm) = e := by
          simpa only [N.evaluationArrowEquiv_comp, N.evaluationArrowEquiv_id] using
            congrArg (fun k => (N.evaluationArrowEquiv T x x k).val) (Category.id_comp (𝟙 x))
        have hm : H.compose T (arrowProjection.hom.app T e) (arrowProjection.hom.app T e)
            (hcomposable T e e (hes.trans het.symm)) =
            arrowProjection.hom.app T (N.compose T e e (hes.trans het.symm)) := by
          show _ = arrowProjection.hom.app T
            (compNat.app T
              ((composableToPullback sourceMap.hom targetMap.hom).app T
                ⟨(e, e), hes.trans het.symm⟩))
          exact (hcompProjection T e e hpb).symm.trans
            (congrArg (arrowProjection.hom.app T) (hcompNat_app T e e hpb).symm)
        have hi := groupoid_identity_of_idempotent H T (arrowProjection.hom.app T e)
          (hcomposable T e e (hes.trans het.symm))
          (hm.trans (congrArg (arrowProjection.hom.app T) hec))
        exact hi.trans (congrArg (H.identity T)
          ((congrArg (fun k => k.app T e) hsourceProjection).symm.trans
            (congrArg (objectProjection.hom.app T) hes)))
      map_comp := by
        intro T a b h
        show H.compose T (arrowProjection.hom.app T a)
            (arrowProjection.hom.app T b) _ = _
        show _ = arrowProjection.hom.app T
          (compNat.app T ((composableToPullback sourceMap.hom targetMap.hom).app T
            ⟨(a, b), h⟩))
        exact (hcompProjection T a b h).symm.trans
          (congrArg (arrowProjection.hom.app T) (hcompNat_app T a b h).symm)
    }
    mapObjects_over := by
      show (q.toSubfunctor.ι ≫ P.baseMap) ≫ G.objectsToBase.hom =
        q.toSubfunctor.ι ≫ P.baseMap ≫ G.objectsToBase.hom
      exact Category.assoc _ _ _
    mapArrows_over := by rfl
  }
  refine {
    unit := identitySection G
    unit_source := identitySection_source G
    unit_identity := identitySection_spec G
    groupoid := groupoid
    hom := hom
    objectProjection := objectProjection
    objectProjection_eq := rfl
    objectProjection_etale := hObjectProjectionEtale
    objectsEquiv := Iso.refl _
    objectProjection_spec := by rfl
    universalOpen := universalOpen
    universalOpen_base := hbase
    universalOpen_spec := by rfl
    universalOpen_containsUnit := hUniversalUnit
    universalOpen_closed := FiniteOpenSubspace.isClosedSubspace
      C S hS G.source objects universalOpen hs_sep
    arrows_eq := rfl
    source_eq := by rfl
    arrowProjection_eq := rfl
  }

section Canonical

variable {C : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicGeometry.AlgebraicSpaces C S hS}
  (G : AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B)
  (hs_sep : AlgebraicGeometry.Space.IsSeparated C S hS G.source.hom)
  (ht_sep : AlgebraicGeometry.Space.IsSeparated C S hS G.target.hom)
  (hs_lft : AlgebraicGeometry.Space.IsLocallyOfFiniteType C S hS G.source.hom)
  (ht_lft : AlgebraicGeometry.Space.IsLocallyOfFiniteType C S hS G.target.hom)

/-- The finite part of a groupoid in algebraic spaces whose source and target are separated and
locally of finite type, chosen once and for all out of `nonempty_finitePartGroupoid`. All the
named pieces of **Stacks 04RU** below are projections of this one choice, so they are pieces of a
single groupoid and a single morphism rather than of unrelated existential witnesses. -/
public noncomputable def finitePartGroupoidData : FinitePartGroupoid G :=
  (nonempty_finitePartGroupoid G hs_sep ht_sep hs_lft ht_lft).some

/-- **Stacks 04RU.** The groupoid in algebraic spaces `(U', Z_univ, s', t', c', e', i')` over `B`
carried by the finite part of `(U, R, s, t, c, e, i)`. -/
@[stacks 04RU "the groupoid (U', Z_univ, s', t', c', e', i') on the finite part"]
public noncomputable def finitePartGroupoid :
    AlgebraicGeometry.GroupoidInAlgebraicSpaces C S hS B :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).groupoid

/-- **Stacks 04RU.** The canonical morphism of groupoids in algebraic spaces over `B`
`(U', Z_univ, s', t', c', e', i') ⟶ (U, R, s, t, c, e, i)` whose existence the lemma asserts. -/
@[stacks 04RU "the canonical morphism of groupoids over B to (U, R, s, t, c, e, i)"]
public noncomputable def finitePartGroupoidHom :
    AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom
      (finitePartGroupoid G hs_sep ht_sep hs_lft ht_lft) G :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).hom

/-- The unit `e` of the given groupoid, as used to cut out the finite part. -/
public noncomputable def finitePartGroupoidUnit : G.objects ⟶ G.arrows :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).unit

/-- The unit is a section of the source morphism. -/
public theorem finitePartGroupoidUnit_source :
    (finitePartGroupoidUnit G hs_sep ht_sep hs_lft ht_lft).hom ≫ G.source.hom =
      𝟙 G.objects.obj :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).unit_source

/-- The unit induces the identity arrow at every point of every test scheme. -/
public theorem finitePartGroupoidUnit_identity (T) (x) :
    (finitePartGroupoidUnit G hs_sep ht_sep hs_lft ht_lft).hom.app T x =
      G.toGroupoidInFunctors.identity T x :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).unit_identity T x

/-- The projection `g : U' ⟶ U` on objects. -/
public noncomputable def finitePartGroupoidObjectProjection :
    (finitePartGroupoid G hs_sep ht_sep hs_lft ht_lft).objects ⟶ G.objects :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).objectProjection

/-- The canonical morphism acts on objects by the projection `g : U' ⟶ U`. -/
public theorem finitePartGroupoidHom_mapObjects :
    (finitePartGroupoidHom G hs_sep ht_sep hs_lft ht_lft).toGroupoidHom.mapObjects =
      (finitePartGroupoidObjectProjection G hs_sep ht_sep hs_lft ht_lft).hom :=
  ((finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).objectProjection_eq).symm

/-- The identification of the object space `U'` with the finite part `(R_s/U, e)_fin`. -/
public noncomputable def finitePartGroupoidObjectsEquiv :
    (finitePartGroupoid G hs_sep ht_sep hs_lft ht_lft).objects.obj ≅
      (finitePartWithSection C S hS G.source
        (finitePartGroupoidUnit G hs_sep ht_sep hs_lft ht_lft)
        (finitePartGroupoidUnit_source G hs_sep ht_sep hs_lft ht_lft)).toSubfunctor.toFunctor :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).objectsEquiv

/-- **Stacks 04RU, clause (1).** Under the identification of `U'` with `(R_s/U, e)_fin` the
projection `g : U' ⟶ U` is the projection of the finite part. -/
@[stacks 04RU "clause (1), g : U' ⟶ U is identified with (R_s/U, e)_fin ⟶ U"]
public theorem finitePartGroupoid_objectProjection_spec :
    (finitePartGroupoidObjectProjection G hs_sep ht_sep hs_lft ht_lft).hom =
      (finitePartGroupoidObjectsEquiv G hs_sep ht_sep hs_lft ht_lft).hom ≫
        (finitePartWithSection C S hS G.source
          (finitePartGroupoidUnit G hs_sep ht_sep hs_lft ht_lft)
          (finitePartGroupoidUnit_source G hs_sep ht_sep hs_lft ht_lft)).toSubfunctor.ι ≫
        (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf C S hS G.source).baseMap :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).objectProjection_spec

/-- The projection `g : U' ⟶ U` is étale. -/
public theorem finitePartGroupoid_objectProjection_etale :
    AlgebraicGeometry.Space.IsEtale C S hS
      (finitePartGroupoidObjectProjection G hs_sep ht_sep hs_lft ht_lft).hom :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).objectProjection_etale

/-- The universal finite open subspace `Z_univ ⊂ R ×_{s, U, g} U'`. -/
public noncomputable def finitePartGroupoidUniversalOpen :
    AlgebraicGeometry.Space.FiniteOpenSubspace C S hS G.source
      (finitePartGroupoid G hs_sep ht_sep hs_lft ht_lft).objects :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).universalOpen

/-- The ambient fibre product of `Z_univ` is taken along `g : U' ⟶ U`. -/
public theorem finitePartGroupoidUniversalOpen_base :
    (finitePartGroupoidUniversalOpen G hs_sep ht_sep hs_lft ht_lft).toBase =
      finitePartGroupoidObjectProjection G hs_sep ht_sep hs_lft ht_lft :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).universalOpen_base

/-- **Stacks 04RU, clause (2), universality.** `Z_univ` is the finite open subspace of
`R ×_{s, U, g} U'` classified by the inclusion of `U'` into the finite part of `s`; this is what
makes it the universal such subspace. -/
@[stacks 04RU "clause (2), Z_univ is the universal finite open subspace of R ×_{s, U, g} U'"]
public theorem finitePartGroupoidUniversalOpen_spec :
    (finiteOpenSubspaceEquiv C S hS G.source
        (finitePartGroupoid G hs_sep ht_sep hs_lft ht_lft).objects).1
      ((finitePartGroupoidObjectsEquiv G hs_sep ht_sep hs_lft ht_lft).hom ≫
        (finitePartWithSection C S hS G.source
          (finitePartGroupoidUnit G hs_sep ht_sep hs_lft ht_lft)
          (finitePartGroupoidUnit_source G hs_sep ht_sep hs_lft ht_lft)).toSubfunctor.ι) =
      finitePartGroupoidUniversalOpen G hs_sep ht_sep hs_lft ht_lft :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).universalOpen_spec

/-- **Stacks 04RU, clause (2), the unit.** `Z_univ` contains the base change of the unit `e`. -/
@[stacks 04RU "clause (2), Z_univ contains the base change of the unit e"]
public theorem finitePartGroupoidUniversalOpen_containsUnit :
    AlgebraicGeometry.Space.ContainsSection C S hS G.source
      (finitePartGroupoidUnit G hs_sep ht_sep hs_lft ht_lft)
      (finitePartGroupoidUnit_source G hs_sep ht_sep hs_lft ht_lft)
      (finitePartGroupoidUniversalOpen G hs_sep ht_sep hs_lft ht_lft) :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).universalOpen_containsUnit

/-- **Stacks 04RU, clause (2), closedness.** `Z_univ` is closed in `R ×_{s, U, g} U'` as well as
open. -/
@[stacks 04RU "clause (2), Z_univ is closed in R ×_{s, U, g} U' as well as open"]
public theorem finitePartGroupoidUniversalOpen_closed :
    AlgebraicGeometry.Space.IsClosedSubspace C S hS
      (finitePartGroupoidUniversalOpen G hs_sep ht_sep hs_lft ht_lft).subspace :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).universalOpen_closed

/-- **Stacks 04RU, clause (2), the arrow space.** The space of arrows of the groupoid on the
finite part *is* the universal finite open subspace `Z_univ`. -/
@[stacks 04RU "clause (2), the arrow space of the finite part is Z_univ"]
public theorem finitePartGroupoid_arrows :
    (finitePartGroupoid G hs_sep ht_sep hs_lft ht_lft).arrows.obj =
      (finitePartGroupoidUniversalOpen G hs_sep ht_sep hs_lft ht_lft).subspace.toFunctor :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).arrows_eq

/-- Under the identification of the arrow space with `Z_univ`, the source `s'` of the groupoid on
the finite part is the first projection of `R ×_{s, U, g} U'`. -/
public theorem finitePartGroupoid_source :
    (finitePartGroupoid G hs_sep ht_sep hs_lft ht_lft).source.hom =
      eqToHom (finitePartGroupoid_arrows G hs_sep ht_sep hs_lft ht_lft) ≫
        (finitePartGroupoidUniversalOpen G hs_sep ht_sep hs_lft ht_lft).subspace.ι ≫
        pullback.fst
          (finitePartGroupoidUniversalOpen G hs_sep ht_sep hs_lft ht_lft).toBase.hom
          G.source.hom :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).source_eq

/-- **Stacks 04RU.** Under the identification of the arrow space with `Z_univ`, the canonical
morphism of groupoids sends an arrow of the finite part to its underlying arrow of `R`, i.e. it is
the second projection of `R ×_{s, U, g} U'`. -/
@[stacks 04RU "the arrow map of the canonical morphism is Z_univ ⊂ R ×_{s, U, g} U' ⟶ R"]
public theorem finitePartGroupoidHom_mapArrows :
    (finitePartGroupoidHom G hs_sep ht_sep hs_lft ht_lft).toGroupoidHom.mapArrows =
      eqToHom (finitePartGroupoid_arrows G hs_sep ht_sep hs_lft ht_lft) ≫
        (finitePartGroupoidUniversalOpen G hs_sep ht_sep hs_lft ht_lft).subspace.ι ≫
        pullback.snd
          (finitePartGroupoidUniversalOpen G hs_sep ht_sep hs_lft ht_lft).toBase.hom
          G.source.hom :=
  (finitePartGroupoidData G hs_sep ht_sep hs_lft ht_lft).arrowProjection_eq

end Canonical

end AlgebraicGeometry.Space

end
