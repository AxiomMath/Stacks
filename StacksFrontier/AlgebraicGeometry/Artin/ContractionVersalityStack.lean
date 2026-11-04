module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionVersalityOpen
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismRepresented
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismEveryConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteTypeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalityFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheoryGeometricReduction

/-!
# Openness of versality for Artin's contraction functor away from `Z`

In the situation of Stacks 0GH8 let `F` be Artin's contraction functor of Stacks 0GHA. This file
proves the first case of the proof of Stacks 0GIA: if `ξ = (Z, u', x̂) ∈ F(V)` is versal at a
finite type point `v₀ ∉ Z`, then `ξ` is versal at every finite type point of an open
neighbourhood of `v₀`. On `V° = V ∖ Z` the element `ξ` is the point `u' : V° ⟶ U' ⊆ X'`; its
versality at `v₀` makes `u'` smooth on a neighbourhood of `v₀` (Stacks 0DQZ, which for the
algebraic space `X'` is More on Morphisms of Spaces, Lemma 0APN as the source cites it), and a
smooth morphism is versal at every finite type point.

## Main results

* `AlgebraicGeometry.Stack.isLocallyOfFiniteType_structureMorphism_algebraicSpaceStack`: an
  algebraic space locally of finite type over `S` is, as an algebraic stack, locally of finite
  type over `S`.
* `AlgebraicGeometry.Artin.ContractionSituation.exists_isVersalAt_of_not_mem`: the first case of
  the proof of Stacks 0GIA.

## References

* [Stacks Project, Tag 0APN](https://stacks.math.columbia.edu/tag/0APN)
* [Stacks Project, Tag 0DQZ](https://stacks.math.columbia.edu/tag/0DQZ)
* [Stacks Project, Tag 0GIA](https://stacks.math.columbia.edu/tag/0GIA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

namespace Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space locally of finite type over `S` is, as an algebraic stack, locally of
finite type over `S`.** By Stacks 06FM for represented source and target the smooth-diagram test
for the structure morphism is local finite type of the induced morphism of representing
presheaves, which is the morphism to the terminal object, hence the structure morphism of the
space up to an isomorphism of the target. -/
theorem isLocallyOfFiniteType_structureMorphism_algebraicSpaceStack
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (hft : Space.IsLocallyOfFiniteType B S hS (terminal.from F)) :
    AlgebraicStacks.IsLocallyOfFiniteType B S hS
      (structureMorphism.{u, w} B S hS (algebraicSpaceStack.{u, w} B S hS F hF)) := by
  let 𝒯 := schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))
  let e : yoneda.obj (Over.mk (𝟙 (B.obj hS))) ≅ ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    ((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal
  have hT : IsAlgebraicSpace B S hS (⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :=
    isAlgebraicSpace_of_iso B S hS e.symm (isAlgebraicSpace_yoneda B S hS _)
  refine (hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (algebraicSpaceStack.{u, w} B S hS F hF).property 𝒯.property _).2 ?_
  refine (hasPropertyOnSomeSmoothDiagram_iff_represented.{u, w} B S hS _
    (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
    (algebraicSpaceStack.{u, w} B S hS F hF).property 𝒯.property F
    (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) hF (isAlgebraicSpace_yoneda B S hS _)
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (PresheafOfCategories.sliceElementsEquivalenceOver _) _).2 ?_
  refine Space.isLocallyOfFiniteType_of_comp B S hS hF (isAlgebraicSpace_yoneda B S hS _) hT _
    e.hom ?_
  have h : ∀ g : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hS))), g ≫ e.hom = terminal.from F :=
    fun _ => terminal.hom_ext _ _
  rwa [h]

end Stack

namespace Artin.ContractionSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (c : ContractionSituation B S hS)

/-- The versal situation of Stacks 0DQU attached to the algebraic space `X'` of the situation of
Stacks 0GH8: `X'` as an algebraic stack, locally of finite type over the locally Noetherian base
`S`. -/
def versalSituationX' : Stack.VersalSituation.{u, u} where
  B := B
  S := S
  hS := hS
  𝒳 := Stack.algebraicSpaceStack.{u, u} B S hS c.X' c.isAlgebraicSpace_X'
  locallyNoetherian := c.isLocallyNoetherian_base
  locallyFiniteType := Stack.isLocallyOfFiniteType_structureMorphism_algebraicSpaceStack B S hS
    c.X' c.isAlgebraicSpace_X' c.isLocallyOfFiniteType_X'

/-- A point of `V` outside `Z` lies in the open part `V°` of the triple. -/
theorem Triple.mem_openPart_of_not_mem {V : BigFppfOver B S hS} (t : Triple c V)
    (v : (BigFppfOver.toScheme B S hS).obj V)
    (hv : (Space.pointsEquivScheme B S hS V).symm v ∉ t.Z) :
    v ∈ (t.openPart : Set V.left.obj) :=
  ⟨_, hv, (Space.pointsEquivScheme B S hS V).apply_symm_apply v⟩

/-- **Stacks 0GIA, first case of the proof.** Let `ξ = (Z, u', x̂) ∈ F(V)` with `V` locally of
finite type over `S`, and let `v₀ ∉ Z` be a finite type point at which `ξ` is versal. Then there
is an open neighbourhood of `v₀` at every finite type point of which `ξ` is versal.

On `V° = V ∖ Z` versality of `ξ` is versality of the point `u'` of `X'`
(`AlgebraicGeometry.Artin.ContractionSituation.isVersalAt_openObject_iff`); by Stacks 0DQZ for
the algebraic space `X'` the point `u'` is smooth on an open neighbourhood `W` of `v₀` in `V°`,
and a smooth morphism is versal at every finite type point. -/
theorem exists_isVersalAt_of_not_mem (x : (contractionFunctor c).Elementsᵒᵖ)
    (hU : LocallyOfFiniteType
      ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x).hom)
    (v₀ : (BigFppfOver.toScheme B S hS).obj x.unop.1.unop.obj)
    (hv₀ : IsFiniteTypePoint v₀)
    (hZ : (Space.pointsEquivScheme B S hS x.unop.1.unop.obj).symm v₀ ∉
      (x.unop.2 : Triple c x.unop.1.unop.obj).Z)
    (hver : Deformation.Artin.IsVersalAt
      ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x)
      (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) v₀ x rfl) :
    ∃ W : ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x).left.Opens,
      v₀ ∈ W ∧ ∀ v ∈ W, IsFiniteTypePoint v →
        Deformation.Artin.IsVersalAt
          ((LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x)
          (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)) v x rfl := by
  let t : Triple c x.unop.1.unop.obj := x.unop.2
  let D := c.versalSituationX'
  let U := (LocallyNoetherianOver.elementsToOver B S hS (contractionFunctor c)).obj x
  let U' := ((D.𝒳.val.val.p ⋙ Over.post B.inclusion).obj t.openObject)
  let j : U'.left ⟶ U.left := ((Over.post B.inclusion).map t.openHom).left
  have : _root_.AlgebraicGeometry.IsOpenImmersion j :=
    inferInstanceAs (_root_.AlgebraicGeometry.IsOpenImmersion t.openPart.ι)
  have hjU : j ≫ U.hom = U'.hom := Over.w ((Over.post B.inclusion).map t.openHom)
  have := c.isLocallyNoetherian_base
  have hj' : LocallyOfFiniteType j := inferInstanceAs (LocallyOfFiniteType t.openPart.ι)
  have hU' : LocallyOfFiniteType U'.hom := by
    rw [← hjU]; exact @locallyOfFiniteType_comp _ _ _ j U.hom hj' hU
  have : LocallyOfFiniteType ((D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj t.openObject).hom :=
    hU'
  have hjrange : Set.range j = (t.openPart : Set x.unop.1.unop.obj.left.obj) :=
    Scheme.Opens.range_ι t.openPart
  obtain ⟨v₀', hv₀'⟩ : v₀ ∈ Set.range j := by
    rw [hjrange]; exact t.mem_openPart_of_not_mem c v₀ hZ
  have hft' : ∀ v' : U'.left, IsFiniteTypePoint (j v') →
      LocallyOfFiniteType (U'.left.fromSpecResidueField v' ≫ U'.hom) := by
    intro v' hv'
    have := (Deformation.Artin.isFiniteTypePoint_of_isOpenImmersion j v' hv').1
    infer_instance
  have hver' : Deformation.Artin.IsVersalAt U' (D.𝒳.val.val.p ⋙ Over.post B.inclusion) v₀'
      t.openObject rfl :=
    (isVersalAt_openObject_iff c x v₀').2 (hv₀' ▸ hver)
  obtain ⟨W, hW, hsm⟩ := Stack.exists_isRelativelySmooth_restrict_of_isVersalAt D t.openObject v₀'
    (Deformation.Artin.isFiniteTypePoint_of_isOpenImmersion j v₀' (hv₀' ▸ hv₀)) hver'
  refine ⟨⟨j '' (show Set U'.left from W.1), j.isOpenEmbedding.isOpenMap _ W.2⟩,
    ⟨v₀', hW, hv₀'⟩, ?_⟩
  rintro _ ⟨v', hv'W, rfl⟩ hft
  exact (isVersalAt_openObject_iff c x v').1
    (Stack.isVersalAt_of_exists_isRelativelySmooth_restrict B S hS D.𝒳.val t.openObject v'
      (hft' v' hft) ⟨W, hv'W, hsm⟩)

end Artin.ContractionSituation

end AlgebraicGeometry

end
