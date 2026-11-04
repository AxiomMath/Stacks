module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalOverTerminal
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects
public import StacksFrontier.CategoryTheory.Limits.FilteredColimitCat
public import StacksFrontier.CategoryTheory.Sites.Stack.Setoid
public import StacksFrontier.Deformation.Artin.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability

/-!
# Limit preserving categories fibred in groupoids have limit preserving structure morphism

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`. Being *limit
preserving* in the sense of Stacks 07XL asks that the comparison `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` be an
equivalence for every cofiltered inverse system of affine schemes with limit `T`; the structure
morphism `𝒳 ⟶ (Sch/S)_{fppf}` being *limit preserving on objects* in the sense of Stacks 06CU
asks only that every object of `𝒳` over `T` descend to a finite stage. This file proves that the
first condition implies the second, which is the implication (2) ⟹ (1) of Stacks 07XN.

The target `(Sch/S)_{fppf}` is `AlgebraicGeometry.Stack.terminalCFG`, the big fppf site of `S`
with the identity as structure functor, and the structure morphism is
`AlgebraicGeometry.Stack.toTerminalCFG` viewed as a 1-morphism of the 2-category of categories
fibred in groupoids.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving`: a limit
  preserving category fibred in groupoids over the big fppf site of `S` has limit preserving on
  objects structure morphism to `(Sch/S)_{fppf}`. Algebraicity is not used.
* `AlgebraicGeometry.Stack.isStackInSetoids_and_isLimitPreservingOnObjects_of_isLimitPreserving`:
  **Stacks 07XN**, the implication (2) ⟹ (1), the previous result with the stack-in-setoids
  clause carried along.

## Implementation notes

*What is and is not proved.* Stacks 07XN is the equivalence of (1) being a stack in setoids with
limit preserving on objects structure morphism, (2) being a stack in setoids and limit preserving,
and (3) being representable by an algebraic space locally of finite presentation, for an algebraic
stack. Only the implication (2) ⟹ (1) is proved here, and the file carries no tag asserting more. It
needs neither algebraicity nor the stack condition: it is the elementary half of the
equivalence, an equivalence of categories being in particular essentially surjective.

The implications relating (1) and (3), together with the composite (2) ⟹ (3), are
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingSetoidRepresentable`, which reads
condition (3) as representability by an algebraic space plus local finite presentation of the
structure morphism in the relative sense of Stacks 03YK and proves it from the implications of
Stacks 04SZ out of and into (1) together with Stacks 06CX. What remains unproved is every
implication *into* (2): both (1) ⟹ (2) and (3) ⟹ (2) need the colimit comparison to be an
equivalence rather than merely essentially surjective, and conditions (1) and (3) supply only
the latter.

*Index universes.* The hypothesis and the conclusion quantify over inverse systems at the same
pair of free index universes, so nothing is specialised in passing from one to the other. The
object and morphism universes of `𝒳` are pinned to those of the big fppf site, as they are for
`AlgebraicGeometry.Stack.IsAlgebraicStack`, because Stacks 06CU compares a 1-morphism's source
and target at a single pair of universes and the target here is the site itself.

*The descent datum.* Essential surjectivity of the comparison puts the given object `x` over the
limit in the image of the colimit, and an object of a filtered colimit in `Cat` comes from a
stage (`CategoryTheory.Cat.exists_stage_obj_of_colimit`), so `x` is isomorphic to a pullback of an
object `x₀` at some stage `i₀`. Stacks 06CU asks for a stage mapping to the prescribed index `i`
as well, which cofilteredness of the index category supplies, and the comparison asked for in the
target is forced: the structure functor of `(Sch/S)_{fppf}` is an identity, so a morphism of the
target lying over a given morphism of the site is determined by it, which is both why the
comparison can be written down and why the commuting square of Stacks 06CU holds automatically.

*The structure morphism.* `AlgebraicGeometry.Stack.structureMorphism` is a different rendering of
the same 1-morphism, landing in the big fppf site of the *identity* of `S` as required by Stacks
050D; `AlgebraicGeometry.Stack.terminalCFG` is the big fppf site of `S` itself, which is the
target Stacks 06CU and Stacks 07XN name.

## References

* [Stacks Project, Tag 07XN](https://stacks.math.columbia.edu/tag/07XN)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 04SZ](https://stacks.math.columbia.edu/tag/04SZ)
* [Stacks Project, Tag 06CX](https://stacks.math.columbia.edu/tag/06CX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u v w uC vC uX vX

section Descent

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {X : Type uX} [Category.{vX} X]

/-- An object over the vertex of a cone whose colimit comparison of fibre categories is
essentially surjective is isomorphic, in its fibre, to a pullback of an object at a finite
stage. -/
private theorem exists_stage_fiber_iso (p : X ⥤ 𝒞) [p.IsFibered]
    {I : Type v} [Category.{w} I] (E : I ⥤ 𝒞) (d : Cone E)
    [(Deformation.Artin.colimitComparison p E d).EssSurj]
    (x : p.Fiber d.pt) :
    ∃ (i₀ : I) (x₀ : p.Fiber (E.obj i₀)),
      Nonempty ((Functor.chosenPullbacks p).obj (d.π.app i₀) x₀ ≅ x) := by
  obtain ⟨io, a, ha⟩ := Cat.exists_stage_obj_of_colimit.{max vX uC uX vC, v, w}
    (Deformation.Artin.fiberDiagram p E)
    ((Deformation.Artin.colimitComparison p E d).objPreimage x)
  exact ⟨io.unop, _,
    ⟨((Deformation.Artin.colimitComparisonStageIso p E d io.unop).app a).symm ≪≫
      eqToIso (congrArg (Deformation.Artin.colimitComparison p E d).obj ha) ≪≫
      (Deformation.Artin.colimitComparison p E d).objObjPreimageIso x⟩⟩

/-- **Descent of objects along a cofiltered limit.** For a fibred category whose colimit
comparison of fibre categories at a cofiltered cone is essentially surjective, an object over the
vertex is, up to a vertical isomorphism, pulled back from a stage dominating any prescribed index,
compatibly with a prescribed cartesian comparison in the base read through the identity functor.

This is the datum Stacks 06CU asks of a structure morphism, in the shape in which the
limit-preservation condition of Stacks 07XL provides it. -/
private theorem exists_descent_of_essSurj (p : X ⥤ 𝒞) [p.IsFibered]
    {I : Type v} [Category.{w} I] [IsCofiltered I] (E : I ⥤ 𝒞) (d : Cone E)
    (hes : (Deformation.Artin.colimitComparison p E d).EssSurj)
    (i : I) (y : (𝟭 𝒞).Fiber (E.obj i)) (x : p.Fiber d.pt) (γ : p.obj x.1 ⟶ y.1)
    (hγ : (𝟭 𝒞).IsStronglyCartesian (d.π.app i) γ) :
    ∃ (i' : I) (j : i' ⟶ i) (x' : p.Fiber (E.obj i')) (xU : p.Fiber d.pt)
      (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1) (γ' : p.obj x'.1 ⟶ y.1),
      p.IsStronglyCartesian (d.π.app i') δ ∧
        p.IsHomLift (𝟙 d.pt) β ∧ IsIso β ∧
        (𝟭 𝒞).IsStronglyCartesian (E.map j) γ' ∧
        p.map δ ≫ γ' = p.map β ≫ γ := by
  have := hes
  obtain ⟨i₀, x₀, ⟨ex⟩⟩ := exists_stage_fiber_iso p E d x
  obtain ⟨i', j₀, j⟩ : Σ' i' : I, (i' ⟶ i₀) × (i' ⟶ i) :=
    ⟨IsCofiltered.min i₀ i, IsCofiltered.minToLeft i₀ i, IsCofiltered.minToRight i₀ i⟩
  have hlift : ∀ {a b : X} {R S : 𝒞} {g : R ⟶ S} {φ : a ⟶ b}, p.IsHomLift g φ →
      (𝟭 𝒞).IsHomLift g (p.map φ) := fun {_ _ _ _ g φ} h =>
    IsHomLift.of_fac' (𝟭 𝒞) g _ (IsHomLift.domain_eq p g φ) (IsHomLift.codomain_eq p g φ)
      (IsHomLift.fac' p g φ)
  have βf : (Functor.chosenPullbacks p).obj (d.π.app i')
      ((Functor.chosenPullbacks p).obj (E.map j₀) x₀) ≅ x :=
    ((Functor.chosenPullbacks p).objCompIso (d.π.app i') (E.map j₀) x₀).symm ≪≫
      eqToIso (congrArg (fun g => (Functor.chosenPullbacks p).obj g x₀) (d.w j₀)) ≪≫ ex
  have hγ' : (𝟭 𝒞).IsHomLift (E.map j)
      (eqToHom ((Functor.chosenPullbacks p).obj (E.map j₀) x₀).2 ≫
        E.map j ≫ eqToHom y.2.symm) :=
    IsHomLift.of_fac' (𝟭 𝒞) (E.map j) _
      ((Functor.chosenPullbacks p).obj (E.map j₀) x₀).2 y.2 rfl
  have hδ : p.IsHomLift (d.π.app i')
      ((Functor.chosenPullbacks p).map (d.π.app i')
        ((Functor.chosenPullbacks p).obj (E.map j₀) x₀)) :=
    ((Functor.chosenPullbacks p).isStronglyCartesian _ _).toIsHomLift
  have hβ : p.IsHomLift (𝟙 d.pt) (Functor.Fiber.fiberInclusion.map βf.hom) := βf.hom.2
  refine ⟨i', j, (Functor.chosenPullbacks p).obj (E.map j₀) x₀,
    (Functor.chosenPullbacks p).obj (d.π.app i')
      ((Functor.chosenPullbacks p).obj (E.map j₀) x₀),
    (Functor.chosenPullbacks p).map (d.π.app i')
      ((Functor.chosenPullbacks p).obj (E.map j₀) x₀),
    Functor.Fiber.fiberInclusion.map βf.hom,
    eqToHom ((Functor.chosenPullbacks p).obj (E.map j₀) x₀).2 ≫ E.map j ≫ eqToHom y.2.symm,
    (Functor.chosenPullbacks p).isStronglyCartesian _ _, hβ,
    ⟨Functor.Fiber.fiberInclusion.map βf.inv,
      by rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
        CategoryTheory.Functor.map_id]; rfl,
      by rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id]; rfl⟩, ?_, ?_⟩
  · have := hγ'
    exact Functor.isFiberedInGroupoids_id.isStronglyCartesian_homLift _ _
  · refine eq_of_isHomLift_id (d.π.app i) _ _ ?_ ?_
    · have hcomp : (𝟭 𝒞).IsHomLift (d.π.app i' ≫ E.map j)
          (p.map ((Functor.chosenPullbacks p).map (d.π.app i')
              ((Functor.chosenPullbacks p).obj (E.map j₀) x₀)) ≫
            (eqToHom ((Functor.chosenPullbacks p).obj (E.map j₀) x₀).2 ≫
              E.map j ≫ eqToHom y.2.symm)) :=
        have := hγ'
        have := hlift hδ
        inferInstance
      rwa [d.w j] at hcomp
    · have := hlift hβ
      have := hγ.toIsHomLift
      exact IsHomLift.comp_lift_id_left' (𝟭 𝒞) d.pt _ _ _

end Descent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **A limit preserving category fibred in groupoids has limit preserving on objects structure
morphism.** If the comparison `colim 𝒳_{Tᵢ} ⥤ 𝒳_T` is an equivalence for every cofiltered inverse
system of affine schemes over `S` with limit `T`, then every object of `𝒳` over such a limit
descends to a finite stage, which is the condition of Stacks 06CU for `𝒳 ⟶ (Sch/S)_{fppf}`.

Neither the stack condition nor algebraicity is used: an equivalence of categories is in
particular essentially surjective, and that is all that is needed. -/
theorem isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒳) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳
      (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)) := by
  have hfib : 𝒳.val.p.IsFibered := 𝒳.2.isFibered
  intro I _ _ D c hc i y x γ hγ
  have hEq : (Deformation.Artin.colimitComparison 𝒳.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c)).IsEquivalence := h𝒳 I D c hc
  exact exists_descent_of_essSurj 𝒳.val.p
    (D ⋙ BigAffineFppf.inclusion B S hS)
    ((BigAffineFppf.inclusion B S hS).mapCone c) hEq.essSurj i y x γ hγ

/-- **Stacks 07XN, the implication (2) ⟹ (1).** A category fibred in groupoids over the big fppf
site of `S` which is a stack in setoids and is limit preserving is a stack in setoids whose
structure morphism to `(Sch/S)_{fppf}` is limit preserving on objects.

The stack-in-setoids clause is common to the two conditions, and the limit-preservation clause
weakens from an equivalence of categories to essential surjectivity. The remaining implications of
Stacks 07XN are not proved here; see the implementation notes of this module. -/
@[stacks 07XN "the implication (2) ⟹ (1)"]
theorem isStackInSetoids_and_isLimitPreservingOnObjects_of_isLimitPreserving
    (h : 𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ∧
      Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒳) :
    𝒳.val.p.IsStackInSetoids (BigFppfOver.topology B S hS) ∧
      BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS 𝒳
        (terminalCFG B S hS)
        (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳)) :=
  ⟨h.1, isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B S hS 𝒳 h.2⟩

end AlgebraicGeometry.Stack

end
