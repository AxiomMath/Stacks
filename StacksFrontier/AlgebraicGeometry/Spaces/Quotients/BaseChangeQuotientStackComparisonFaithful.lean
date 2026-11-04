module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.OpenSubgroupoidQuotientStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeGroupoidEvaluation
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.BaseChangeQuotientStackComparison

/-!
# Morphisms of the Stacks 0DTG 2-fibre product, and faithfulness of its comparison

The right-hand corner of the cospan the Stacks 0DTG square sits over is the enlarged fibred
category `𝒮_X` of an algebraic space, which is fibred in **sets**. That makes the comparison
square of a morphism of the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}` automatic, and the
`𝒮_{X'}`-component of such a morphism redundant: a morphism of the 2-fibre product is determined
by its `[U/R]`-component alone, and it can be built from a pair of components lying over one
morphism of the site with no further condition.

Consequently the comparison 1-morphism `c : [U'/R'] ⟶ [U/R] ×_{𝒮_X} 𝒮_{X'}` is **faithful** as
soon as the top arrow `[U'/R'] ⟶ [U/R]` of the square is, and the top arrow is faithful.

## Main definitions

* `AlgebraicGeometry.Stack.baseChangeTwoFibreProductHom`: a morphism of the 2-fibre product from
  its two components alone.

## Main results

* `AlgebraicGeometry.Stack.hom_eq_of_isHomLift_lifted`: in the enlarged fibred category of an
  algebraic space two morphisms with the same domain and codomain lying over one morphism of the
  site are equal.
* `AlgebraicGeometry.Stack.baseChangeTwoFibreProduct_hom_ext`: a morphism of the 2-fibre product
  is determined by its `[U/R]`-component.
* `AlgebraicGeometry.Stack.baseChangeQuotientStackComparison_map_a` and
  `AlgebraicGeometry.Stack.baseChangeQuotientStackComparison_map_b`: the two components of the
  image of a morphism under the comparison 1-morphism.
* `AlgebraicGeometry.Stack.faithful_invariantBaseChangeQuotientStackMap`: the top arrow of the
  Stacks 0DTG square is faithful.
* `AlgebraicGeometry.Stack.faithful_baseChangeQuotientStackComparison` and
  `AlgebraicGeometry.Stack.faithful_comparison`: the comparison 1-morphism is faithful as soon as
  the top arrow of the Stacks 0DTG square is, and it is faithful.

## Implementation notes

`AlgebraicGeometry.Stack.hom_eq_of_isHomLift_lifted` is stated through faithfulness of the
structure functor of the enlarged fibred category
(`AlgebraicGeometry.Stack.liftedFibredCategory_faithful`) rather than through
`CategoryTheory.Functor.IsFiberedInSets.hom_ext_of_isHomLift`: the two say the same thing here,
and the `IsFiberedInSets` instance for the enlarged fibred category is not exported, whereas
faithfulness of its structure functor is.

## References

* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 0043](https://stacks.math.columbia.edu/tag/0043)
* [Stacks Project, Tag 0DTG](https://stacks.math.columbia.edu/tag/0DTG)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- **In the enlarged fibred category of an algebraic space a morphism is determined by the
morphism of the site it lies over**, together with its domain and codomain. -/
theorem hom_eq_of_isHomLift_lifted {X : AlgebraicSpaces C S hS}
    {V U : BigFppfOver C S hS} (f : V ⟶ U) {x y : (liftedFibredCategory X).obj}
    (φ₁ φ₂ : y ⟶ x) (h₁ : (liftedFibredCategory X).p.IsHomLift f φ₁)
    (h₂ : (liftedFibredCategory X).p.IsHomLift f φ₂) : φ₁ = φ₂ := by
  let := liftedFibredCategory_faithful X
  have := h₁
  have := h₂
  refine Functor.Faithful.map_injective (F := (liftedFibredCategory X).p) ?_
  rw [IsHomLift.fac' (liftedFibredCategory X).p f φ₁,
    IsHomLift.fac' (liftedFibredCategory X).p f φ₂]

section BaseChange

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (g : X' ⟶ X)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- **A morphism of the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}` is determined by its
`[U/R]`-component.** -/
theorem baseChangeTwoFibreProduct_hom_ext
    {P Q : baseChangeTwoFibreProductObj G XtoB g φ hφB hφ} (F₁ F₂ : P ⟶ Q)
    (ha : F₁.a = F₂.a) : F₁ = F₂ := by
  refine TwoFibreProductOver.Hom.ext' ha ?_
  have hbase : F₁.hbase = F₂.hbase := by
    rw [F₁.hbase_eq, F₂.hbase_eq, ha]
  refine hom_eq_of_isHomLift_lifted F₁.hbase F₁.b F₂.b F₁.hb ?_
  exact hbase ▸ F₂.hb

/-- **A morphism of the 2-fibre product `[U/R] ×_{𝒮_X} 𝒮_{X'}` from its two components alone**,
given that they lie over one morphism of the site: no compatibility with the comparison square of
Stacks 0040 is required. -/
noncomputable def baseChangeTwoFibreProductHom
    {P Q : baseChangeTwoFibreProductObj G XtoB g φ hφB hφ} (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (base : eqToHom P.hy.symm ≫ (liftedFibredCategory X').p.map b ≫ eqToHom Q.hy
      = eqToHom P.hx.symm ≫
        (quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).p.map a ≫ eqToHom Q.hx) :
    P ⟶ Q := by
  refine TwoFibreProductOver.Hom.mk' a b base ?_
  set K := eqToHom P.hx.symm ≫
    (quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).p.map a ≫ eqToHom Q.hx with hK
  have ha : (quotientStack (invariantTargetGroupoid G XtoB φ hφB hφ)).p.IsHomLift K a :=
    IsHomLift.of_fac' _ _ a P.hx Q.hx (by rw [hK]; simp)
  have hb : (liftedFibredCategory X').p.IsHomLift K b :=
    IsHomLift.of_fac' _ _ b P.hy Q.hy (by rw [← base]; simp)
  have hFa := Functor.isHomLift_map_of_comp_eq
    (liftedQuotientStackToBase (invariantTargetGroupoid G XtoB φ hφB hφ)).w K a
  have hGb := Functor.isHomLift_map_of_comp_eq (liftedAssociatedMap g).w K b
  have hPv := P.vertical
  have hQv := Q.vertical
  have h1 : (liftedFibredCategory X).p.IsHomLift (K ≫ 𝟙 Q.base)
      ((liftedQuotientStackToBase
        (invariantTargetGroupoid G XtoB φ hφB hφ)).toFunctor.map a ≫ Q.iso.hom) :=
    inferInstance
  have h2 : (liftedFibredCategory X).p.IsHomLift (𝟙 P.base ≫ K)
      (P.iso.hom ≫ (liftedAssociatedMap g).toFunctor.map b) := inferInstance
  rw [Category.comp_id] at h1
  rw [Category.id_comp] at h2
  exact hom_eq_of_isHomLift_lifted K _ _ h1 h2

end BaseChange

section Comparison

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X X' : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (X'toB : X' ⟶ B) (g : X' ⟶ X) (hg : g ≫ XtoB = X'toB)
  (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- **The `[U/R]`-component of the image of a morphism under the comparison 1-morphism** is its
image under the top arrow of the Stacks 0DTG square. -/
theorem baseChangeQuotientStackComparison_map_a
    {z₁ z₂ : (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj}
    (ψ : z₁ ⟶ z₂) :
    ((baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).map ψ).a =
      (invariantBaseChangeQuotientStackMap (G := G) (XtoB := XtoB) (X'toB := X'toB)
        (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ)).map ψ := rfl

/-- **The `𝒮_{X'}`-component of the image of a morphism under the comparison 1-morphism** is its
image under the left arrow of the Stacks 0DTG square. -/
theorem baseChangeQuotientStackComparison_map_b
    {z₁ z₂ : (quotientStack (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).obj}
    (ψ : z₁ ⟶ z₂) :
    ((baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).map ψ).b =
      (liftedQuotientStackToBase
        (invariantBaseChangeGroupoid G XtoB g φ hφB hφ)).map ψ := rfl

/-- **The comparison 1-morphism of Stacks 0DTG is faithful as soon as the top arrow of the square
is.** -/
theorem faithful_baseChangeQuotientStackComparison
    (hfaithful : (invariantBaseChangeQuotientStackMap (G := G) (XtoB := XtoB) (X'toB := X'toB)
      (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ)).toFunctor.Faithful) :
    (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).Faithful :=
  ⟨fun h => hfaithful.map_injective (congrArg (·.a) h)⟩

/-- **The top arrow `[U'/R'] ⟶ [U/R]` of the Stacks 0DTG square is faithful.** -/
theorem faithful_invariantBaseChangeQuotientStackMap :
    (invariantBaseChangeQuotientStackMap (G := G) (XtoB := XtoB) (X'toB := X'toB)
      (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ)).toFunctor.Faithful :=
  faithful_quotientStackMap_of_evaluation_faithful
    (invariantBaseChangeGroupoidHom (G := G) (XtoB := XtoB) (X'toB := X'toB)
      (g := g) (hg := hg) (φ := φ) (hφB := hφB) (hφ := hφ))
    (evaluation_faithful_invariantBaseChangeGroupoidHom G XtoB X'toB g hg φ hφB hφ)

/-- **The comparison 1-morphism of Stacks 0DTG is faithful.** -/
theorem faithful_comparison :
    (baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ).Faithful :=
  faithful_baseChangeQuotientStackComparison.{u, w} G XtoB X'toB g hg φ hφB hφ
    (faithful_invariantBaseChangeQuotientStackMap G XtoB X'toB g hg φ hφB hφ)

end Comparison

end AlgebraicGeometry.Stack

end
