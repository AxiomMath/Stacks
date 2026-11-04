module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeOfRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidSchemeRealizationHom
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpacesOfComposable
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoid

/-!
# The realization of the groupoid scheme of a represented groupoid

A groupoid represented on the big fppf site — objects `U` and `R` of the site, `s, t : R ⟶ U`
and a composition law `c` making the sections over every test object a groupoid — gives both a
groupoid in algebraic spaces, `AlgebraicGeometry.Stack.representedGroupoid`, and a groupoid scheme,
`AlgebraicGeometry.Space.representedGroupoidScheme`. This file compares the realization of the
groupoid scheme (`Stacks.Groupoids.GroupoidScheme.realization`) with the groupoid in algebraic
spaces: they have the same object and arrow spaces and the same source and target, and the same
composition, so the identity maps form a morphism of groupoids in algebraic spaces between them,
whose evaluated functors are full and faithful.

## Main definitions

* `AlgebraicGeometry.Space.representedRealizationHom`: the comparison morphism.

## Main results

* `AlgebraicGeometry.Space.representedRealization_compose`: the composition of the realization is
  the given composition law.
* `AlgebraicGeometry.Space.representedRealizationHom_evaluation_full` and
  `AlgebraicGeometry.Space.representedRealizationHom_evaluation_faithful`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {U R : BigFppfOver B S hS} (s t : R ⟶ U)
  (c : Deformation.composableArrows (yoneda.obj U) (yoneda.obj R)
    (yoneda.map s) (yoneda.map t) ⟶ yoneda.obj R)
  (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map s).app T)
    ((yoneda.map t).app T) fun p => c.app T p))

/-- The object scheme of the groupoid scheme of a represented groupoid lies in the site. -/
theorem contains_representedGroupoidScheme_objects :
    B.Contains (representedGroupoidScheme s t c hG).objects.left := U.left.2

/-- The arrow scheme of the groupoid scheme of a represented groupoid lies in the site. -/
theorem contains_representedGroupoidScheme_arrows :
    B.Contains (representedGroupoidScheme s t c hG).arrows.left := R.left.2

/-- The scheme of composable pairs of the groupoid scheme of a represented groupoid lies in the
site. -/
theorem contains_representedGroupoidScheme_pullback :
    B.Contains (pullback (representedGroupoidScheme s t c hG).source
      (representedGroupoidScheme s t c hG).target).left :=
  BigFppfSite.contains_pullback_left B _ _ R.left.2 R.left.2

/-- The realization of the groupoid scheme of a represented groupoid. -/
noncomputable abbrev representedRealization :
    GroupoidInAlgebraicSpaces B S hS (Stacks.Groupoids.GroupoidScheme.realizationBase B hS) :=
  (representedGroupoidScheme s t c hG).realization B hS
    (contains_representedGroupoidScheme_objects s t c hG)
    (contains_representedGroupoidScheme_arrows s t c hG)
    (contains_representedGroupoidScheme_pullback s t c hG)

/-- **The composition of the realization of the groupoid scheme of a represented groupoid is the
given composition law.** -/
theorem representedRealization_compose (T : (BigFppfOver B S hS)ᵒᵖ)
    (a b : (yoneda.obj R).obj T) (h : (yoneda.map s).app T a = (yoneda.map t).app T b) :
    (representedRealization s t c hG).toGroupoidInFunctors.compose T a b h =
      c.app T ⟨(a, b), h⟩ := by
  let F := siteToOver B hS
  have hU := contains_representedGroupoidScheme_objects s t c hG
  have hR := contains_representedGroupoidScheme_arrows s t c hG
  apply (yonedaSchemePointEquiv B hS hR T).injective
  refine (Stacks.Groupoids.GroupoidScheme.Hom.yonedaSchemePointEquiv_realization_compose B hS
    (representedGroupoidScheme s t c hG) hU hR
    (contains_representedGroupoidScheme_pullback s t c hG) T a b h (by
      rw [← yonedaSchemePointEquiv_map B hS hR hU (representedGroupoidScheme s t c hG).source T a,
        ← yonedaSchemePointEquiv_map B hS hR hU (representedGroupoidScheme s t c hG).target T b]
      exact congrArg (yonedaSchemePointEquiv B hS hU T) h)).trans ?_
  show pullback.lift (F.map a) (F.map b) _ ≫
      ((isPullback_map_representedPairs s t).isoPullback.inv ≫ F.map (representedCompMap s t c)) =
    F.map (c.app T ⟨(a, b), h⟩)
  have hw : F.map a ≫ F.map s = F.map b ≫ F.map t := by
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map h
  let k : T.unop ⟶ representedPairs s t :=
    F.preimage (pullback.lift (F.map a) (F.map b) hw ≫
      (isPullback_map_representedPairs s t).isoPullback.inv)
  have hk : F.map k = pullback.lift (F.map a) (F.map b) hw ≫
      (isPullback_map_representedPairs s t).isoPullback.inv := F.map_preimage _
  have hfst : k ≫ representedFst s t = a := by
    apply F.map_injective
    rw [F.map_comp, hk, Category.assoc, (isPullback_map_representedPairs s t).isoPullback_inv_fst,
      pullback.lift_fst]
  have hsnd : k ≫ representedSnd s t = b := by
    apply F.map_injective
    rw [F.map_comp, hk, Category.assoc, (isPullback_map_representedPairs s t).isoPullback_inv_snd,
      pullback.lift_snd]
  rw [← Category.assoc, ← hk, ← F.map_comp, comp_representedCompMap]
  exact congrArg F.map (representedComp_congr s t c hfst hsnd _ h)

/-- The composition of the represented groupoid is the given composition law. -/
theorem representedGroupoid_compose (T : (BigFppfOver B S hS)ᵒᵖ)
    (a b : (yoneda.obj R).obj T) (h : (yoneda.map s).app T a = (yoneda.map t).app T b) :
    (Stack.representedGroupoid B S hS s t c hG).toGroupoidInFunctors.compose T a b h =
      c.app T ⟨(a, b), h⟩ :=
  AlgebraicGeometry.compose_ofComposable ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
    ⟨yoneda.obj R, isAlgebraicSpace_yoneda B S hS R⟩
    (ObjectProperty.homMk (yoneda.map s)) (ObjectProperty.homMk (yoneda.map t)) c hG T a b h

/-- **The comparison of the realization of the groupoid scheme of a represented groupoid with the
represented groupoid**: the identity maps of the common object and arrow spaces. -/
noncomputable def representedRealizationHom :
    GroupoidInAlgebraicSpaces.Hom (representedRealization s t c hG)
      (Stack.representedGroupoid B S hS s t c hG) :=
  GroupoidInAlgebraicSpaces.Hom.mk' (𝟙 (yoneda.obj U)) (𝟙 (yoneda.obj R))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun T a b h => (representedGroupoid_compose s t c hG T a b h).trans
      (representedRealization_compose s t c hG T a b h).symm)
    ((Space.baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _)
    ((Space.baseTerminal_yonedaIsTerminal B S hS).hom_ext _ _)

/-- The comparison is the identity on object spaces. -/
theorem representedRealizationHom_mapObjects :
    (representedRealizationHom s t c hG).toGroupoidHom.mapObjects = 𝟙 (yoneda.obj U) := rfl

/-- The comparison is the identity on arrow spaces. -/
theorem representedRealizationHom_mapArrows :
    (representedRealizationHom s t c hG).toGroupoidHom.mapArrows = 𝟙 (yoneda.obj R) := rfl

/-- The evaluated functors of the comparison are faithful. -/
theorem representedRealizationHom_evaluation_faithful (T : (BigFppfOver B S hS)ᵒᵖ) :
    ((representedRealizationHom s t c hG).toGroupoidHom.evaluation T).Faithful := by
  constructor
  intro x y m n hmn
  apply ((representedRealization s t c hG).toGroupoidInFunctors.evaluationArrowEquiv
    T x y).injective
  apply Subtype.ext
  have hm := congrArg (fun k =>
    ((Stack.representedGroupoid B S hS s t c hG).toGroupoidInFunctors.evaluationArrowEquiv T _ _
      k).1) hmn
  exact (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
      (representedRealizationHom s t c hG).toGroupoidHom T m).symm.trans
    (hm.trans (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
      (representedRealizationHom s t c hG).toGroupoidHom T n))

/-- The evaluated functors of the comparison are full. -/
theorem representedRealizationHom_evaluation_full (T : (BigFppfOver B S hS)ᵒᵖ) :
    ((representedRealizationHom s t c hG).toGroupoidHom.evaluation T).Full := by
  constructor
  intro x y m'
  let q := (Stack.representedGroupoid B S hS s t c hG).toGroupoidInFunctors.evaluationArrowEquiv
    T x y m'
  refine ⟨((representedRealization s t c hG).toGroupoidInFunctors.evaluationArrowEquiv T x y).symm
    ⟨q.1, q.2.1, q.2.2⟩, ?_⟩
  apply ((Stack.representedGroupoid B S hS s t c hG).toGroupoidInFunctors.evaluationArrowEquiv
    T _ _).injective
  apply Subtype.ext
  refine (Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
    (representedRealizationHom s t c hG).toGroupoidHom T _).trans ?_
  exact congrArg Subtype.val (Equiv.apply_symm_apply
    ((representedRealization s t c hG).toGroupoidInFunctors.evaluationArrowEquiv T x y)
    ⟨q.1, q.2.1, q.2.2⟩)

end AlgebraicGeometry.Space

end
