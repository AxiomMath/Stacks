module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackComparisonFibreFull
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackModuliSpace

/-!
# A quotient stack is a uniform categorical moduli space exactly when its presentation is a
uniform categorical quotient (Stacks 0DUI)

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a terminal base, let
`𝒳 = [U/R]` be its quotient stack and let `f : 𝒳 ⟶ Y` be a 1-morphism to an algebraic space, with
restriction `φ : U ⟶ Y` along the projection `π : U ⟶ [U/R]` as in Stacks 0DUH. Stacks 0DUI says
that `f` is a *uniform* categorical moduli space (Stacks 0DUG, part (2)) exactly when `φ` is a
*uniform* categorical quotient (Stacks 048L, part (2)), and the same in a full subcategory of the
algebraic spaces.

## Main definitions

* `AlgebraicGeometry.Stack.spaceAsStack` and `AlgebraicGeometry.Stack.quotientStackAsStack`: an
  algebraic space and a quotient stack as objects of the 2-category of stacks in groupoids on the
  big fppf site (Stacks 02ZK).
* `AlgebraicGeometry.Stack.situationGroupoid`: `G` read as a groupoid over `Y` along `φ`
  (Stacks 048G).
* `AlgebraicGeometry.Stack.baseChangeSituationGroupoid` and
  `AlgebraicGeometry.Stack.baseChangeSituationGroupoidOverBase`: the base change
  `(U', R', s', t', c')` of Stacks 048G, over `Y'` and read back over the terminal base.
* `AlgebraicGeometry.Stack.baseChangeSituationPreRelation` and
  `AlgebraicGeometry.Stack.baseChangeSituationQuotientMap`: the base-changed pre-relation
  `(t', s')` and the base-changed quotient map `U' ⟶ Y'`.

## Main results

* `AlgebraicGeometry.Stack.isBasedCategoricalModuliSpace_snd_of_isTwoFibreProduct` and
  `AlgebraicGeometry.Stack.isBasedCategoricalModuliSpaceIn_snd_of_isTwoFibreProduct`: the
  moduli-space property of the second projection of a 2-fibre product does not depend on the
  chosen 2-fibre product.
* `AlgebraicGeometry.Stack.eq_quotientStackToBase_situationGroupoid`: `f` is the structure arrow
  `[U/R] ⟶ Y` of Stacks 044R for `G` read over `Y`.
* `quotientStack_isUniformCategoricalModuliSpace_iff_isUniformCategoricalQuotient`:
  **Stacks 0DUI**, the uniform case, and
  `quotientStack_isUniformModuliSpaceIn_iff_isUniformQuotientIn_of_isClosedUnderLimitsOfShape`,
  the uniform case in a full subcategory closed under fibre products and containing `R` and `U`.
* `AlgebraicGeometry.Stack.prop_baseChangeSituationGroupoid_objects` and
  `AlgebraicGeometry.Stack.prop_baseChangeSituationGroupoid_arrows`: `U' = Y' ×_Y U` and
  `R' = Y' ×_Y R` lie in such a subcategory when `Y` and `Y'` do.

## Implementation notes

*No universe hypothesis.* The uniform condition is imposed at the quotient stack's own hom
universe, and not by restricting the test objects. `AlgebraicGeometry.Stack.quotientStack` is a
`CategoryTheory.BasedCategory.{u + 1, u + 1}`, so it is not an object of
`CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, over which
`AlgebraicGeometry.Stack.IsUniformCategoricalModuliSpace` of Stacks 0DUG part (2) quantifies its
2-fibre products. It is an object of the 2-category of stacks in groupoids of Stacks 02ZK,
`CategoryTheory.StackInGroupoids (BigFppfOver C S hS) (BigFppfOver.topology C S hS)`, and the
quantification runs over every 2-fibre product of the cospan in that 2-category. The moduli-space
property of the base change is the written-out
`AlgebraicGeometry.Stack.IsBasedCategoricalModuliSpace`, which
`AlgebraicGeometry.Stack.isCategoricalModuliSpace_iff_forall_basedFunctor` identifies with
`IsCategoricalModuliSpace` wherever the latter can be stated.

*The hom universe of the cospan.* The two vertical arrows of the Stacks 0DTG square have their
target in `AlgebraicGeometry.Stack.liftedFibredCategory`, the category fibred in sets of an
algebraic space with its morphisms pushed up into the universe of the ambient bicategory. So the
cospan is `f` followed by `AlgebraicGeometry.Stack.liftedFibredCategoryUp`, and the base change's
moduli-space property is read off its second projection followed by
`AlgebraicGeometry.Stack.liftedFibredCategoryDown`. Those two are mutually inverse on the nose, so
the condition is a condition on the projection itself.

*The base-changed pre-relation.* It is the pre-relation `(t', s')` cut out by the base change
`AlgebraicGeometry.Stack.baseChangeSituationGroupoid` of Stacks 048G, read in the slice of
algebraic spaces over the terminal base, where `AlgebraicGeometry.Space.IsCategoricalQuotient` of
Stacks 048J lives. It is the base change of `j = (t, s)` in the sense of Stacks 048G by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.baseChangedPreRelation_isBaseChange`. The uniform
quotient condition is written at this groupoid base change, not through
`AlgebraicGeometry.Space.IsUniformCategoricalQuotientIn`, which is stated at the other model
`AlgebraicGeometry.Space.pullbackPreRelation` of the same base change.

*The full subcategory.* It is an `ObjectProperty` of the algebraic spaces with
`ObjectProperty.IsClosedUnderLimitsOfShape WalkingCospan`, containing `R` and `U`. Both uniform
conditions in it (Stacks 0DUG part (4) and Stacks 048L part (2)) ask `Y` to lie in it and quantify
over the flat `Y' ⟶ Y` with `Y'` in it; for such `Y'` the base-changed spaces `Y' ×_Y U` and
`Y' ×_Y R` lie in it by closure under fibre products.

## References

* [Stacks Project, Tag 003O](https://stacks.math.columbia.edu/tag/003O)
* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 02ZK](https://stacks.math.columbia.edu/tag/02ZK)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
* [Stacks Project, Tag 048J](https://stacks.math.columbia.edu/tag/048J)
* [Stacks Project, Tag 048L](https://stacks.math.columbia.edu/tag/048L)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
* [Stacks Project, Tag 0DUG](https://stacks.math.columbia.edu/tag/0DUG)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
* [Stacks Project, Tag 0DUI](https://stacks.math.columbia.edu/tag/0DUI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-! ### The objects of the 2-category of stacks in groupoids -/

/-- **An algebraic space over `S`, as an object of the 2-category of stacks in groupoids on the
big fppf site** (Stacks 02ZK): its category fibred in sets of Stacks 0458, with the morphism
universe enlarged to that of the ambient bicategory. -/
abbrev spaceAsStack (X : AlgebraicSpaces C S hS) :
    StackInGroupoids.{u, u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)
      (BigFppfOver.topology C S hS) :=
  ⟨liftedFibredCategory X, isStackInGroupoids_liftedFibredCategory X⟩

/-- **The quotient stack of Stacks 044Q, as an object of the 2-category of stacks in groupoids on
the big fppf site** (Stacks 02ZK). -/
abbrev quotientStackAsStack (G : GroupoidInAlgebraicSpaces C S hS B) :
    StackInGroupoids.{u, u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)
      (BigFppfOver.topology C S hS) :=
  ⟨quotientStack G, isStackInGroupoids_quotientStack G⟩

/-! ### Transfer between two 2-fibre products of one cospan -/

section Transfer

variable {𝒳 𝒬 𝒮 : StackInGroupoids.{u, u, u + 1, u + 1, u + 1} (BigFppfOver C S hS)
    (BigFppfOver.topology C S hS)}
  {F : 𝒬 ⟶ 𝒮} {A : 𝒳 ⟶ 𝒮}

/-- The second projection of a 2-commutative square, composed with a 1-morphism into a category
fibred in sets, factors through the comparison 1-morphism of a pre-morphism of squares: the
comparison 2-morphism of Stacks 003O becomes an equality there. -/
private theorem comp_snd_eq_of_preHom {T Q : Bicategory.TwoCommSq F A}
    (N : Bicategory.TwoCommSq.PreHom T Q)
    {E : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (K : 𝒳.toBasedCategory ⥤ᵇ (fibredCategory C S hS E).val) :
    BasedFunctor.comp T.snd.hom K =
      BasedFunctor.comp N.hom.hom (BasedFunctor.comp Q.snd.hom K) :=
  comp_eq_of_basedNatTrans N.isoSnd.hom.hom K

/-- **The factorization property of the second projection of a 2-fibre product does not depend on
the chosen 2-fibre product**, against the test objects selected by any predicate `Pr`. -/
private theorem forall_existsUnique_snd_of_isTwoFibreProduct {Y : AlgebraicSpaces C S hS}
    (D : 𝒳.toBasedCategory ⥤ᵇ (fibredCategory C S hS Y.obj).val)
    {P Q : Bicategory.TwoCommSq F A}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (Pr : AlgebraicSpaces C S hS → Prop)
    (hQ' : ∀ (W : AlgebraicSpaces C S hS), Pr W →
      ∀ g : Q.pt.toBasedCategory ⥤ᵇ (fibredCategory C S hS W.obj).val,
        ∃! h : Y ⟶ W,
          BasedFunctor.comp (BasedFunctor.comp Q.snd.hom D)
            (associatedMap C S hS h.hom).1.hom = g) :
    ∀ (W : AlgebraicSpaces C S hS), Pr W →
      ∀ g : P.pt.toBasedCategory ⥤ᵇ (fibredCategory C S hS W.obj).val,
        ∃! h : Y ⟶ W,
          BasedFunctor.comp (BasedFunctor.comp P.snd.hom D)
            (associatedMap C S hS h.hom).1.hom = g := by
  classical
  intro W hW g
  obtain ⟨e, -, -⟩ := Bicategory.twoFibreProductPreHom_rel hP
    ((Bicategory.twoFibreProductPreHom hQ P).comp (Bicategory.twoFibreProductPreHom hP Q))
    (.id P)
  obtain ⟨h, hh, hu⟩ := hQ' W hW
    (BasedFunctor.comp (Bicategory.twoFibreProductPreHom hP Q).hom.hom g)
  refine ⟨h, ?_, fun h' hh' => hu h' ?_⟩
  · refine Eq.trans (comp_snd_eq_of_preHom (Bicategory.twoFibreProductPreHom hQ P)
      (BasedFunctor.comp D (associatedMap C S hS h.hom).1.hom)) ?_
    refine Eq.trans (congrArg
      (fun k : Q.pt.toBasedCategory ⥤ᵇ (fibredCategory C S hS W.obj).val =>
        BasedFunctor.comp (Bicategory.twoFibreProductPreHom hQ P).hom.hom k) hh) ?_
    exact (comp_eq_of_basedNatTrans e.hom.hom g).trans (BasedFunctor.id_comp g)
  · refine Eq.trans (comp_snd_eq_of_preHom (Bicategory.twoFibreProductPreHom hP Q)
      (BasedFunctor.comp D (associatedMap C S hS h'.hom).1.hom)) ?_
    exact congrArg
      (fun k : P.pt.toBasedCategory ⥤ᵇ (fibredCategory C S hS W.obj).val =>
        BasedFunctor.comp (Bicategory.twoFibreProductPreHom hP Q).hom.hom k) hh'

/-- **The moduli-space property of the second projection of a 2-fibre product does not depend on
the chosen 2-fibre product.** -/
theorem isBasedCategoricalModuliSpace_snd_of_isTwoFibreProduct {Y : AlgebraicSpaces C S hS}
    (D : 𝒳.toBasedCategory ⥤ᵇ (fibredCategory C S hS Y.obj).val)
    {P Q : Bicategory.TwoCommSq F A}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (hQ' : IsBasedCategoricalModuliSpace Y (BasedFunctor.comp Q.snd.hom D)) :
    IsBasedCategoricalModuliSpace Y (BasedFunctor.comp P.snd.hom D) :=
  fun W g => forall_existsUnique_snd_of_isTwoFibreProduct D hP hQ (fun _ => True)
    (fun W _ => hQ' W) W trivial g

/-- **The moduli-space property in a full subcategory of the second projection of a 2-fibre
product does not depend on the chosen 2-fibre product.** -/
theorem isBasedCategoricalModuliSpaceIn_snd_of_isTwoFibreProduct {Y : AlgebraicSpaces C S hS}
    (D : 𝒳.toBasedCategory ⥤ᵇ (fibredCategory C S hS Y.obj).val)
    {P Q : Bicategory.TwoCommSq F A}
    (hP : Bicategory.IsTwoFibreProduct P) (hQ : Bicategory.IsTwoFibreProduct Q)
    (Pr : AlgebraicSpaces C S hS → Prop)
    (hQ' : IsBasedCategoricalModuliSpaceIn Pr Y (BasedFunctor.comp Q.snd.hom D)) :
    IsBasedCategoricalModuliSpaceIn Pr Y (BasedFunctor.comp P.snd.hom D) :=
  ⟨hQ'.1, forall_existsUnique_snd_of_isTwoFibreProduct D hP hQ Pr hQ'.2⟩

end Transfer

/-! ### The base change of the situation of Stacks 0DUH -/

section Situation

variable (hB : IsTerminal B) (G : GroupoidInAlgebraicSpaces C S hS B)
  {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- **`G` read as a groupoid over `Y`** (Stacks 048G) along an invariant `φ : U ⟶ Y`. -/
abbrev situationGroupoid : GroupoidInAlgebraicSpaces C S hS Y :=
  invariantTargetGroupoid G (hB.from Y) φ (hB.hom_ext _ _) hφ

/-- **The base change `(U', R', s', t', c')` of Stacks 048G** of the situation of Stacks 0DUH
along `a : Y' ⟶ Y`, a groupoid over `Y'` with `U' = Y' ×_Y U` and `R' = Y' ×_Y R`. -/
abbrev baseChangeSituationGroupoid {Y' : AlgebraicSpaces C S hS} (a : Y' ⟶ Y) :
    GroupoidInAlgebraicSpaces C S hS Y' :=
  invariantBaseChangeGroupoid G (hB.from Y) a φ (hB.hom_ext _ _) hφ

/-- **The object space `U' = Y' ×_Y U` of the base change lies in a full subcategory closed
under fibre products** as soon as `U`, `Y` and `Y'` do. -/
theorem prop_baseChangeSituationGroupoid_objects (Pr : ObjectProperty (AlgebraicSpaces C S hS))
    [Pr.IsClosedUnderLimitsOfShape WalkingCospan] {Y' : AlgebraicSpaces C S hS} (a : Y' ⟶ Y)
    (hU : Pr G.objects) (hY : Pr Y) (hY' : Pr Y') :
    Pr (baseChangeSituationGroupoid hB G φ hφ a).objects :=
  Pr.prop_of_isLimit (Space.baseChange
      (invariantTargetGroupoid G (hB.from Y) φ (hB.hom_ext _ _) hφ) a).objects_isPullback.isLimit
    (by rintro (_ | _ | _) <;> assumption)

/-- **The arrow space `R' = Y' ×_Y R` of the base change lies in a full subcategory closed
under fibre products** as soon as `R`, `Y` and `Y'` do. -/
theorem prop_baseChangeSituationGroupoid_arrows (Pr : ObjectProperty (AlgebraicSpaces C S hS))
    [Pr.IsClosedUnderLimitsOfShape WalkingCospan] {Y' : AlgebraicSpaces C S hS} (a : Y' ⟶ Y)
    (hR : Pr G.arrows) (hY : Pr Y) (hY' : Pr Y') :
    Pr (baseChangeSituationGroupoid hB G φ hφ a).arrows :=
  Pr.prop_of_isLimit (Space.baseChange
      (invariantTargetGroupoid G (hB.from Y) φ (hB.hom_ext _ _) hφ) a).arrows_isPullback.isLimit
    (by rintro (_ | _ | _) <;> assumption)

/-- `AlgebraicGeometry.Stack.baseChangeSituationGroupoid`, read back as a groupoid over the
terminal base `B`. -/
abbrev baseChangeSituationGroupoidOverBase {Y' : AlgebraicSpaces C S hS} (a : Y' ⟶ Y) :
    GroupoidInAlgebraicSpaces C S hS B :=
  GroupoidInAlgebraicSpaces.overBase (baseChangeSituationGroupoid hB G φ hφ a) (hB.from Y')

/-- **The base-changed pre-relation `(t', s')`**, in the slice of algebraic spaces over the
terminal base. -/
abbrev baseChangeSituationPreRelation {Y' : AlgebraicSpaces C S hS} (a : Y' ⟶ Y) :
    Space.PreRelation
      (Over.mk (baseChangeSituationGroupoidOverBase hB G φ hφ a).arrowsToBase)
      (Over.mk (baseChangeSituationGroupoidOverBase hB G φ hφ a).objectsToBase) :=
  prod.lift
    (Over.homMk (baseChangeSituationGroupoidOverBase hB G φ hφ a).target
      (baseChangeSituationGroupoidOverBase hB G φ hφ a).target_over)
    (Over.homMk (baseChangeSituationGroupoidOverBase hB G φ hφ a).source
      (baseChangeSituationGroupoidOverBase hB G φ hφ a).source_over)

/-- **The base-changed quotient map `U' ⟶ Y'`**: the structure morphism of
`AlgebraicGeometry.Stack.baseChangeSituationGroupoid`, read as a morphism over the terminal
base. -/
abbrev baseChangeSituationQuotientMap {Y' : AlgebraicSpaces C S hS} (a : Y' ⟶ Y) :
    (Over.mk (baseChangeSituationGroupoidOverBase hB G φ hφ a).objectsToBase : Over B) ⟶
      Over.mk (hB.from Y') :=
  Over.homMk (baseChangeSituationGroupoid hB G φ hφ a).objectsToBase (hB.hom_ext _ _)

/-- **The structure arrow `[U'/R'] ⟶ Y'` of Stacks 044R for the base change of the situation
restricts along the projection to the base-changed quotient map.** -/
theorem baseChangeSituationQuotientMap_eq {Y' : AlgebraicSpaces C S hS} (a : Y' ⟶ Y) :
    (Over.homMk (restrictedMorphism (baseChangeSituationGroupoidOverBase hB G φ hφ a)
        (quotientStackToBase (baseChangeSituationGroupoid hB G φ hφ a))) (hB.hom_ext _ _) :
      (Over.mk (baseChangeSituationGroupoidOverBase hB G φ hφ a).objectsToBase : Over B) ⟶
        Over.mk (hB.from Y')) =
      baseChangeSituationQuotientMap hB G φ hφ a :=
  Over.OverMorphism.ext
    (restrictedMorphism_quotientStackToBase (G := baseChangeSituationGroupoid hB G φ hφ a))

/-- **The Stacks 0DTG square for the base change of the situation along `a : Y' ⟶ Y`**, a
2-commutative square over the cospan of the structure arrow `[U/R] ⟶ Y` and of `a`. -/
abbrev baseChangeSituationSquare {Y' : AlgebraicSpaces C S hS} (a : Y' ⟶ Y) :=
  baseChangeQuotientStackSquare.{u, u} G (hB.from Y) (hB.from Y') a (hB.hom_ext _ _) φ
    (hB.hom_ext _ _) hφ

/-- **Stacks 0DTG.** The square of
`AlgebraicGeometry.Stack.baseChangeSituationSquare` is a 2-fibre product, so the base change of
the situation of Stacks 0DUH is the situation of the base-changed groupoid. -/
def isTwoFibreProduct_baseChangeSituationSquare {Y' : AlgebraicSpaces C S hS} (a : Y' ⟶ Y) :
    Bicategory.IsTwoFibreProduct (baseChangeSituationSquare hB G φ hφ a) :=
  baseChangeQuotientStackSquare_isTwoFibreProduct.{u, u} G (hB.from Y) (hB.from Y') a
    (hB.hom_ext _ _) φ (hB.hom_ext _ _) hφ

end Situation

/-! ### One base change -/

section Pointwise

variable (hB : IsTerminal B) (G : GroupoidInAlgebraicSpaces C S hS B)
  {Y Y' : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)
  {F : quotientStack G ⥤ᵇ liftedFibredCategory Y}
  (hF : F = liftedQuotientStackToBase (situationGroupoid hB G φ hφ))
  (a : Y' ⟶ Y)

/-- **The factorizations through the second projection of the Stacks 0DTG square are the
factorizations through the structure arrow `[U'/R'] ⟶ Y'` of Stacks 044R.** -/
private theorem forall_existsUnique_baseChangeSituationSquare_snd
    (Pr : AlgebraicSpaces C S hS → Prop) :
    (∀ (W : AlgebraicSpaces C S hS), Pr W →
        ∀ g : (baseChangeSituationSquare hB G φ hφ a).pt.toBasedCategory ⥤ᵇ
            (fibredCategory C S hS W.obj).val,
          ∃! h : Y' ⟶ W,
            BasedFunctor.comp
              (BasedFunctor.comp (baseChangeSituationSquare hB G φ hφ a).snd.hom
                (liftedFibredCategoryDown Y'))
              (associatedMap C S hS h.hom).1.hom = g) ↔
      ∀ (W : AlgebraicSpaces C S hS), Pr W →
        ∀ g : quotientStack (baseChangeSituationGroupoid hB G φ hφ a) ⥤ᵇ
            (fibredCategory C S hS W.obj).val,
          ∃! h : Y' ⟶ W,
            BasedFunctor.comp
              (quotientStackToBase (baseChangeSituationGroupoid hB G φ hφ a))
              (associatedMap C S hS h.hom).1.hom = g :=
  Iff.rfl

include hF in
/-- **The second projection of any 2-fibre product of the cospan is the second projection of the
Stacks 0DTG square**, as far as the factorization property against any class of test objects is
concerned. -/
private theorem forall_existsUnique_snd_iff
    (P : Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom F : quotientStackAsStack G ⟶ spaceAsStack Y)
      (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap a) :
        spaceAsStack Y' ⟶ spaceAsStack Y))
    (hP : Bicategory.IsTwoFibreProduct P) (Pr : AlgebraicSpaces C S hS → Prop) :
    (∀ (W : AlgebraicSpaces C S hS), Pr W →
        ∀ g : P.pt.toBasedCategory ⥤ᵇ (fibredCategory C S hS W.obj).val,
          ∃! h : Y' ⟶ W,
            BasedFunctor.comp
              (BasedFunctor.comp P.snd.hom (liftedFibredCategoryDown Y'))
              (associatedMap C S hS h.hom).1.hom = g) ↔
      ∀ (W : AlgebraicSpaces C S hS), Pr W →
        ∀ g : (baseChangeSituationSquare hB G φ hφ a).pt.toBasedCategory ⥤ᵇ
            (fibredCategory C S hS W.obj).val,
          ∃! h : Y' ⟶ W,
            BasedFunctor.comp
              (BasedFunctor.comp (baseChangeSituationSquare hB G φ hφ a).snd.hom
                (liftedFibredCategoryDown Y'))
              (associatedMap C S hS h.hom).1.hom = g := by
  subst hF
  exact ⟨fun h => forall_existsUnique_snd_of_isTwoFibreProduct (liftedFibredCategoryDown Y')
      (isTwoFibreProduct_baseChangeSituationSquare hB G φ hφ a) hP Pr h,
    fun h => forall_existsUnique_snd_of_isTwoFibreProduct (liftedFibredCategoryDown Y') hP
      (isTwoFibreProduct_baseChangeSituationSquare hB G φ hφ a) Pr h⟩

include hF in
/-- **The base change of the situation of Stacks 0DUH along one morphism `a : Y' ⟶ Y`.** The base
change `Y' ×_Y [U/R] ⟶ Y'`, presented by any 2-fibre product of the cospan, is a categorical
moduli space exactly when the base-changed quotient map `U' ⟶ Y'` is a categorical quotient of the
base-changed pre-relation `(t', s')`. -/
theorem isBasedCategoricalModuliSpace_snd_iff_isCategoricalQuotient
    (P : Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom F : quotientStackAsStack G ⟶ spaceAsStack Y)
      (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap a) :
        spaceAsStack Y' ⟶ spaceAsStack Y))
    (hP : Bicategory.IsTwoFibreProduct P) :
    IsBasedCategoricalModuliSpace Y'
        (BasedFunctor.comp P.snd.hom (liftedFibredCategoryDown Y')) ↔
      Space.IsCategoricalQuotient (baseChangeSituationPreRelation hB G φ hφ a)
        (baseChangeSituationQuotientMap hB G φ hφ a) := by
  refine Iff.trans ?_ (Iff.trans
    (quotientStack_isCategoricalModuliSpace_iff_isCategoricalQuotient_prodLift hB
      (baseChangeSituationGroupoidOverBase hB G φ hφ a) Y'
      (quotientStackToBase (baseChangeSituationGroupoid hB G φ hφ a)))
    (iff_of_eq (congrArg
      (Space.IsCategoricalQuotient (baseChangeSituationPreRelation hB G φ hφ a))
      (baseChangeSituationQuotientMap_eq hB G φ hφ a))))
  refine Iff.trans ⟨fun h W _ => h W, fun h W => h W trivial⟩ (Iff.trans
    (Iff.trans (forall_existsUnique_snd_iff hB G φ hφ hF a P hP (fun _ => True))
      (forall_existsUnique_baseChangeSituationSquare_snd hB G φ hφ a (fun _ => True)))
    ⟨fun h W => h W trivial, fun h W _ => h W⟩)

include hF in
/-- **The base change of the situation of Stacks 0DUH along one morphism, in a full
subcategory.** -/
theorem isBasedCategoricalModuliSpaceIn_snd_iff_isCategoricalQuotientIn
    (Pr : AlgebraicSpaces C S hS → Prop)
    (hR : Pr (baseChangeSituationGroupoid hB G φ hφ a).arrows)
    (hU : Pr (baseChangeSituationGroupoid hB G φ hφ a).objects)
    (P : Bicategory.TwoCommSq
      (Bicategory.InducedBicategory.mkHom F : quotientStackAsStack G ⟶ spaceAsStack Y)
      (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap a) :
        spaceAsStack Y' ⟶ spaceAsStack Y))
    (hP : Bicategory.IsTwoFibreProduct P) :
    IsBasedCategoricalModuliSpaceIn Pr Y'
        (BasedFunctor.comp P.snd.hom (liftedFibredCategoryDown Y')) ↔
      Space.IsCategoricalQuotientIn (fun Z : Over B => Pr Z.left)
        (baseChangeSituationPreRelation hB G φ hφ a)
        (baseChangeSituationQuotientMap hB G φ hφ a) := by
  refine Iff.trans ?_ (Iff.trans
    (quotientStack_isCategoricalModuliSpaceIn_iff_isCategoricalQuotientIn hB
      (j := baseChangeSituationPreRelation hB G φ hφ a)
      (congrArg Over.Hom.left (prod.lift_fst _ _)) (congrArg Over.Hom.left (prod.lift_snd _ _))
      Pr hR hU Y' (quotientStackToBase (baseChangeSituationGroupoid hB G φ hφ a)))
    (iff_of_eq (congrArg
      (Space.IsCategoricalQuotientIn (fun Z : Over B => Pr Z.left)
        (baseChangeSituationPreRelation hB G φ hφ a))
      (baseChangeSituationQuotientMap_eq hB G φ hφ a))))
  exact and_congr_right' (Iff.trans (forall_existsUnique_snd_iff hB G φ hφ hF a P hP Pr)
    (forall_existsUnique_baseChangeSituationSquare_snd hB G φ hφ a Pr))

end Pointwise

/-! ### `f` as the structure arrow of a groupoid over `Y` -/

section Restriction

variable (hB : IsTerminal B) (G : GroupoidInAlgebraicSpaces C S hS B)
  (Y : AlgebraicSpaces C S hS)
  (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val)

/-- **`f` is the structure arrow `[U/R] ⟶ Y` of Stacks 044R for `G` read over `Y`.** -/
theorem eq_quotientStackToBase_situationGroupoid :
    f = quotientStackToBase
      (situationGroupoid hB G (restrictedMorphism G f) (restrictedMorphism_isInvariant G f)) :=
  (quotientStackHomEquivInvariant G Y).injective (Subtype.ext
    (restrictedMorphism_quotientStackToBase (G := situationGroupoid hB G (restrictedMorphism G f)
      (restrictedMorphism_isInvariant G f))).symm)

/-- **The cospan of the uniform condition is the cospan of the Stacks 0DTG square.** -/
theorem comp_liftedFibredCategoryUp_eq_liftedQuotientStackToBase :
    BasedFunctor.comp f (liftedFibredCategoryUp Y) =
      liftedQuotientStackToBase
        (situationGroupoid hB G (restrictedMorphism G f)
          (restrictedMorphism_isInvariant G f)) :=
  congrArg (fun k => BasedFunctor.comp k (liftedFibredCategoryUp Y))
    (eq_quotientStackToBase_situationGroupoid hB G Y f)

end Restriction

/-! ### The uniform equivalence at an abstract cospan -/

section ForallCospan

variable (hB : IsTerminal B) (G : GroupoidInAlgebraicSpaces C S hS B)
  {Y : AlgebraicSpaces C S hS} (φ : G.objects ⟶ Y)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)
  {F : quotientStack G ⥤ᵇ liftedFibredCategory Y}
  (hF : F = liftedQuotientStackToBase (situationGroupoid hB G φ hφ))

/-- A family over a type of data, all of whose members are equivalent to `B`, is equivalent to `B`
once one member exists. -/
private theorem forall_imp_iff_of_exists {α : Sort*} {p : α → Sort*} {A : α → Prop} {B : Prop}
    (x : α) (hx : p x) (h : ∀ y, p y → (A y ↔ B)) : (∀ y, p y → A y) ↔ B :=
  ⟨fun H => (h x hx).1 (H x hx), fun hB y hy => (h y hy).2 hB⟩

include hF in
/-- The uniform equivalence with the cospan carried as `F`. -/
private theorem forall_isBasedCategoricalModuliSpace_iff :
    (∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        ∀ P : Bicategory.TwoCommSq
            (Bicategory.InducedBicategory.mkHom F : quotientStackAsStack G ⟶ spaceAsStack Y)
            (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap a) :
              spaceAsStack Y' ⟶ spaceAsStack Y),
          Bicategory.IsTwoFibreProduct P →
            IsBasedCategoricalModuliSpace Y'
              (BasedFunctor.comp P.snd.hom (liftedFibredCategoryDown Y'))) ↔
      ∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        Space.IsCategoricalQuotient (baseChangeSituationPreRelation hB G φ hφ a)
          (baseChangeSituationQuotientMap hB G φ hφ a) := by
  subst hF
  refine forall_congr' fun Y' => forall_congr' fun a => imp_congr_right fun _ => ?_
  exact forall_imp_iff_of_exists _ (isTwoFibreProduct_baseChangeSituationSquare hB G φ hφ a)
    fun P hP => isBasedCategoricalModuliSpace_snd_iff_isCategoricalQuotient hB G φ hφ rfl a P hP

include hF in
/-- The uniform equivalence in a full subcategory, with the cospan carried as `F`. -/
private theorem forall_isBasedCategoricalModuliSpaceIn_iff
    (Pr : AlgebraicSpaces C S hS → Prop)
    (hR : ∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y),
      Pr (baseChangeSituationGroupoid hB G φ hφ a).arrows)
    (hU : ∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y),
      Pr (baseChangeSituationGroupoid hB G φ hφ a).objects) :
    (∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        ∀ P : Bicategory.TwoCommSq
            (Bicategory.InducedBicategory.mkHom F : quotientStackAsStack G ⟶ spaceAsStack Y)
            (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap a) :
              spaceAsStack Y' ⟶ spaceAsStack Y),
          Bicategory.IsTwoFibreProduct P →
            IsBasedCategoricalModuliSpaceIn Pr Y'
              (BasedFunctor.comp P.snd.hom (liftedFibredCategoryDown Y'))) ↔
      ∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        Space.IsCategoricalQuotientIn (fun Z : Over B => Pr Z.left)
          (baseChangeSituationPreRelation hB G φ hφ a)
          (baseChangeSituationQuotientMap hB G φ hφ a) := by
  subst hF
  refine forall_congr' fun Y' => forall_congr' fun a => imp_congr_right fun _ => ?_
  exact forall_imp_iff_of_exists _ (isTwoFibreProduct_baseChangeSituationSquare hB G φ hφ a)
    fun P hP => isBasedCategoricalModuliSpaceIn_snd_iff_isCategoricalQuotientIn hB G φ hφ rfl a Pr
      (hR Y' a) (hU Y' a) P hP

include hF in
/-- The uniform equivalence in a full subcategory closed under fibre products and containing `R`
and `U`, with the cospan carried as `F`. -/
private theorem isUniformIn_iff_of_isClosedUnderLimitsOfShape
    (Pr : ObjectProperty (AlgebraicSpaces C S hS)) [Pr.IsClosedUnderLimitsOfShape WalkingCospan]
    (hR : Pr G.arrows) (hU : Pr G.objects) :
    (Pr Y ∧ ∀ (Y' : AlgebraicSpaces C S hS), Pr Y' → ∀ (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        ∀ P : Bicategory.TwoCommSq
            (Bicategory.InducedBicategory.mkHom F : quotientStackAsStack G ⟶ spaceAsStack Y)
            (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap a) :
              spaceAsStack Y' ⟶ spaceAsStack Y),
          Bicategory.IsTwoFibreProduct P →
            IsBasedCategoricalModuliSpaceIn Pr Y'
              (BasedFunctor.comp P.snd.hom (liftedFibredCategoryDown Y'))) ↔
      Pr G.arrows ∧ Pr G.objects ∧ Pr Y ∧
        ∀ (Y' : AlgebraicSpaces C S hS), Pr Y' → ∀ (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
          Space.IsCategoricalQuotientIn (fun Z : Over B => Pr Z.left)
            (baseChangeSituationPreRelation hB G φ hφ a)
            (baseChangeSituationQuotientMap hB G φ hφ a) := by
  subst hF
  refine (and_congr_right fun hY => forall_congr' fun Y' => forall_congr' fun hY' =>
    forall_congr' fun a => imp_congr_right fun _ => ?_).trans
    ⟨fun h => ⟨hR, hU, h⟩, fun h => h.2.2⟩
  exact forall_imp_iff_of_exists _ (isTwoFibreProduct_baseChangeSituationSquare hB G φ hφ a)
    fun P hP => isBasedCategoricalModuliSpaceIn_snd_iff_isCategoricalQuotientIn hB G φ hφ rfl a Pr
      (prop_baseChangeSituationGroupoid_arrows hB G φ hφ Pr a hR hY hY')
      (prop_baseChangeSituationGroupoid_objects hB G φ hφ Pr a hU hY hY') P hP

end ForallCospan

/-! ### Stacks 0DUI, the uniform case -/

section Uniform

variable (hB : IsTerminal B) (G : GroupoidInAlgebraicSpaces C S hS B)
  (Y : AlgebraicSpaces C S hS)
  (f : quotientStack G ⥤ᵇ (fibredCategory C S hS Y.obj).val)

/-- Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a terminal base, let
`f : [U/R] ⟶ Y` be a 1-morphism to the category attached to an algebraic space `Y` and let
`φ : U ⟶ Y` be its restriction along the projection of Stacks 044R. Then `f` is a *uniform*
categorical moduli space exactly when `φ` is a *uniform* categorical quotient: for every flat
`a : Y' ⟶ Y`, the base change `Y' ×_Y [U/R] ⟶ Y'` of `f` is a categorical moduli space exactly when
the base-changed quotient map `U' ⟶ Y'` is a categorical quotient of the base-changed pre-relation
`(t', s')`, for `U' = Y' ×_Y U` and `R' = Y' ×_Y R`.

The base change is an arbitrary 2-fibre product of the cospan in the 2-category of stacks in
groupoids of Stacks 02ZK. -/
@[stacks 0DUI "the uniform case, for a groupoid over the terminal base as in the source"]
theorem quotientStack_isUniformCategoricalModuliSpace_iff_isUniformCategoricalQuotient :
    (∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        ∀ P : Bicategory.TwoCommSq
            (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp f (liftedFibredCategoryUp Y)) :
              quotientStackAsStack G ⟶ spaceAsStack Y)
            (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap a) :
              spaceAsStack Y' ⟶ spaceAsStack Y),
          Bicategory.IsTwoFibreProduct P →
            IsBasedCategoricalModuliSpace Y'
              (BasedFunctor.comp P.snd.hom (liftedFibredCategoryDown Y'))) ↔
      ∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        Space.IsCategoricalQuotient
          (baseChangeSituationPreRelation hB G (restrictedMorphism G f)
            (restrictedMorphism_isInvariant G f) a)
          (baseChangeSituationQuotientMap hB G (restrictedMorphism G f)
            (restrictedMorphism_isInvariant G f) a) :=
  forall_isBasedCategoricalModuliSpace_iff hB G (restrictedMorphism G f)
    (restrictedMorphism_isInvariant G f)
    (comp_liftedFibredCategoryUp_eq_liftedQuotientStackToBase hB G Y f)

/-- The uniform case in a full subcategory. With the same data as
`quotientStack_isUniformCategoricalModuliSpace_iff_isUniformCategoricalQuotient` and a full
subcategory of the algebraic spaces, selected by a predicate `Pr` on objects which contains the
object and arrow spaces of every base change of the groupoid: for every flat `a : Y' ⟶ Y`, the base
change `Y' ×_Y [U/R] ⟶ Y'` of `f` is a categorical moduli space in `Pr` exactly when the
base-changed quotient map `U' ⟶ Y'` is a categorical quotient in `Pr` of the base-changed
pre-relation `(t', s')`. -/
@[stacks 0DUI "variant: the uniform case in a full subcategory, over every flat Y' ⟶ Y and \
  with the subcategory containing every base change of R and U; the tag is \
  quotientStack_isUniformModuliSpaceIn_iff_isUniformQuotientIn_of_isClosedUnderLimitsOfShape"]
theorem quotientStack_isUniformCategoricalModuliSpaceIn_iff_isUniformCategoricalQuotientIn
    (Pr : AlgebraicSpaces C S hS → Prop)
    (hR : ∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y),
      Pr (baseChangeSituationGroupoid hB G (restrictedMorphism G f)
        (restrictedMorphism_isInvariant G f) a).arrows)
    (hU : ∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y),
      Pr (baseChangeSituationGroupoid hB G (restrictedMorphism G f)
        (restrictedMorphism_isInvariant G f) a).objects) :
    (∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        ∀ P : Bicategory.TwoCommSq
            (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp f (liftedFibredCategoryUp Y)) :
              quotientStackAsStack G ⟶ spaceAsStack Y)
            (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap a) :
              spaceAsStack Y' ⟶ spaceAsStack Y),
          Bicategory.IsTwoFibreProduct P →
            IsBasedCategoricalModuliSpaceIn Pr Y'
              (BasedFunctor.comp P.snd.hom (liftedFibredCategoryDown Y'))) ↔
      ∀ (Y' : AlgebraicSpaces C S hS) (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        Space.IsCategoricalQuotientIn (fun Z : Over B => Pr Z.left)
          (baseChangeSituationPreRelation hB G (restrictedMorphism G f)
            (restrictedMorphism_isInvariant G f) a)
          (baseChangeSituationQuotientMap hB G (restrictedMorphism G f)
            (restrictedMorphism_isInvariant G f) a) :=
  forall_isBasedCategoricalModuliSpaceIn_iff hB G (restrictedMorphism G f)
    (restrictedMorphism_isInvariant G f)
    (comp_liftedFibredCategoryUp_eq_liftedQuotientStackToBase hB G Y f) Pr hR hU

/-- Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over a terminal base,
`f : [U/R] ⟶ Y` a 1-morphism to the category attached to an algebraic space `Y`, and `φ : U ⟶ Y`
its restriction along the projection of Stacks 044R. Let `Pr` be a full subcategory of the
algebraic spaces which is closed under fibre products and contains `R` and `U`. Then `f` is a
uniform categorical moduli space in `Pr` (Stacks 0DUG, part (4)) — `Y` lies in `Pr` and for every
flat `a : Y' ⟶ Y` with `Y'` in `Pr` the base change `Y' ×_Y [U/R] ⟶ Y'` is a categorical moduli
space in `Pr` — exactly when `φ` is a uniform categorical quotient in `Pr` (Stacks 048L, part (2))
— `R`, `U` and `Y` lie in `Pr` and for every flat `a : Y' ⟶ Y` with `Y'` in `Pr` the base-changed
quotient map `U' ⟶ Y'` is the categorical quotient in `Pr` of the base-changed pre-relation
`(t', s')`, for `U' = Y' ×_Y U` and `R' = Y' ×_Y R`. -/
@[stacks 0DUI "uniform, in a full subcategory"]
theorem quotientStack_isUniformModuliSpaceIn_iff_isUniformQuotientIn_of_isClosedUnderLimitsOfShape
    (Pr : ObjectProperty (AlgebraicSpaces C S hS)) [Pr.IsClosedUnderLimitsOfShape WalkingCospan]
    (hR : Pr G.arrows) (hU : Pr G.objects) :
    (Pr Y ∧ ∀ (Y' : AlgebraicSpaces C S hS), Pr Y' → ∀ (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
        ∀ P : Bicategory.TwoCommSq
            (Bicategory.InducedBicategory.mkHom (BasedFunctor.comp f (liftedFibredCategoryUp Y)) :
              quotientStackAsStack G ⟶ spaceAsStack Y)
            (Bicategory.InducedBicategory.mkHom (liftedAssociatedMap a) :
              spaceAsStack Y' ⟶ spaceAsStack Y),
          Bicategory.IsTwoFibreProduct P →
            IsBasedCategoricalModuliSpaceIn Pr Y'
              (BasedFunctor.comp P.snd.hom (liftedFibredCategoryDown Y'))) ↔
      Pr G.arrows ∧ Pr G.objects ∧ Pr Y ∧
        ∀ (Y' : AlgebraicSpaces C S hS), Pr Y' → ∀ (a : Y' ⟶ Y), Space.IsFlat C S hS a.hom →
          Space.IsCategoricalQuotientIn (fun Z : Over B => Pr Z.left)
            (baseChangeSituationPreRelation hB G (restrictedMorphism G f)
              (restrictedMorphism_isInvariant G f) a)
            (baseChangeSituationQuotientMap hB G (restrictedMorphism G f)
              (restrictedMorphism_isInvariant G f) a) :=
  isUniformIn_iff_of_isClosedUnderLimitsOfShape hB G (restrictedMorphism G f)
    (restrictedMorphism_isInvariant G f)
    (comp_liftedFibredCategoryUp_eq_liftedQuotientStackToBase hB G Y f) Pr hR hU

end Uniform

end AlgebraicGeometry.Stack

end
