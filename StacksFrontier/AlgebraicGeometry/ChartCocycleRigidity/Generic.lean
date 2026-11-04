module

public import StacksFrontier.AlgebraicGeometry.NestedCocycleTail.Basic
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Chart

/-!
# A composition law for three restriction comparisons, from one endomorphism being the identity

`Stacks.AlgebraicGeometry.NestedCocycleTail.IsChartCocycle` asks, for a chain `W ⊆ W' ⊆ U` of
affine opens of a base scheme, that the comparison of the twists on the charts of `W` and `U` be
the composite of the two comparisons through the chart of `W'`, read on sections. This file
proves the **generic** half of that statement: nothing below mentions a projective spectrum, a
twisting sheaf or a graded ring, and every ingredient is a variable.

The situation is three open immersions `p₁ : Y ⟶ Z`, `p₂ : Z ⟶ X`, `p₃ : Y ⟶ X` with
`p₁ ≫ p₂ = p₃`, three sheaves of modules `M` on `X`, `N` on `Z`, `L` on `Y`, and three
comparisons identifying the restriction of each outer module with the next one in. Cancelling the
comparison of the outer pair against the composite of the two inner ones produces an
**endomorphism of `L`**, and the composition law holds, over every open and for every
inclusion of opens, exactly when that endomorphism is the identity.

That is what makes a rigidity argument applicable to the cocycle: rigidity is a statement about
endomorphism families of the twists on one projective spectrum, and `legEndo` is the family it
has to be run on.

## Main definitions

* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legPairIso`: the comparison of the two readings
  of the restriction along `p₃` — directly, and as the restriction along `p₁` of the restriction
  along `p₂`.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndo`: **the endomorphism of `L`** obtained by
  cancelling the outer comparison against the two inner ones.

## Main results

* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legPairIso_hom_val_app`: the comparison of the
  two readings is a restriction map, with the inclusion of opens supplied freely.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndo_val_app`: the action of the endomorphism
  on a section, in four factors.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.isEvalComposite_of_legEndo_eq_id`: **the
  composition law**, for every triple of opens and every triple of inclusions, from the single
  hypothesis that the endomorphism is the identity.
* `Stacks.AlgebraicGeometry.ChartCocycleRigidity.legEndo_app_hom_app`: the computation the
  converse direction needs — the endomorphism applied to the image of a section under the outer
  comparison is the composite of the two inner legs applied to that section.

## Implementation notes

Every statement is written with the morphisms, the schemes and the modules as variables, for the
reason recorded throughout this cluster: an equation written out at the concrete instance cannot
be matched against the same equation produced by instantiating a generic statement, and the
concrete instance here is a transition morphism of a relative projective spectrum, where even a
single projection is expensive. Each step is one application of
`Stacks.AlgebraicGeometry.NestedCocycleReduction.comp_val_app_of`, whose hypothesis is an
equation of *morphisms*, so no composite is ever identified underneath an `app`.

Inclusions of opens are never exhibited as composites. They are free arguments, and two
restriction maps between the same pair of opens agree by
`Stacks.AlgebraicGeometry.NestedCocycleReduction.map_val_congr`, because morphisms between opens
are unique.

The one equality of opens that has to be produced,
`p₂ ''ᵁ (p₁ ''ᵁ T) = p₃ ''ᵁ T`, cannot be obtained by rewriting with `p₁ ≫ p₂ = p₃`:
`AlgebraicGeometry.Scheme.Hom.opensFunctor` takes the open-immersion instance as an argument, so
the motive of such a rewrite does not typecheck. It is obtained by substituting the equality away
instead, which also discharges the instance by proof irrelevance.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.NestedCocycleReduction
open Stacks.AlgebraicGeometry.NestedCocycleTail

namespace Stacks.AlgebraicGeometry.ChartCocycleRigidity

universe u

variable {X Y Z : Scheme.{u}} (p₁ : Y ⟶ Z) (p₂ : Z ⟶ X) (p₃ : Y ⟶ X)
  [IsOpenImmersion p₁] [IsOpenImmersion p₂] [IsOpenImmersion p₃]

/-- **The image of an open under a composite of open immersions.** Stated separately because it
is the one equality of opens the construction below needs and it cannot be obtained by rewriting
with `p₁ ≫ p₂ = p₃`; see the module docstring. -/
public theorem image_eq_image_image (hp : p₁ ≫ p₂ = p₃) (T : Y.Opens) :
    p₂ ''ᵁ (p₁ ''ᵁ T) = p₃ ''ᵁ T := by
  subst hp
  ext y
  simp

/-- **The two readings of the restriction along the composite.** Restricting along `p₃` is
restricting along `p₂` and then along `p₁`. -/
public def legPairIso (hp : p₁ ≫ p₂ = p₃) (M : X.Modules) :
    (Scheme.Modules.restrictFunctor p₃).obj M ≅
      (Scheme.Modules.restrictFunctor p₁).obj ((Scheme.Modules.restrictFunctor p₂).obj M) :=
  ((Scheme.Modules.restrictFunctorCongr hp).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp p₁ p₂).app M

/-- **The comparison of the two readings is a restriction map.** The inclusion of opens is a free
argument: both of its factors are transports along equalities of opens, and morphisms between
opens are unique. -/
public theorem legPairIso_hom_val_app (hp : p₁ ≫ p₂ = p₃) (M : X.Modules) (T : Y.Opens)
    (k : p₂ ''ᵁ (p₁ ''ᵁ T) ⟶ p₃ ''ᵁ T)
    (x : ((Scheme.Modules.restrictFunctor p₃).obj M).val.obj (op T)) :
    (legPairIso p₁ p₂ p₃ hp M).hom.val.app (op T) x = M.val.map k.op x := by
  have h1 : ((Scheme.Modules.restrictFunctorCongr hp).inv.app M).val.app (op T) x =
      M.val.map (eqToHom (show (p₁ ≫ p₂) ''ᵁ T = p₃ ''ᵁ T by subst hp; rfl)).op x := rfl
  have h2 : ∀ y : ((Scheme.Modules.restrictFunctor (p₁ ≫ p₂)).obj M).val.obj (op T),
      ((Scheme.Modules.restrictFunctorComp p₁ p₂).hom.app M).val.app (op T) y =
        M.val.map (eqToHom (show p₂ ''ᵁ (p₁ ''ᵁ T) = (p₁ ≫ p₂) ''ᵁ T by
          ext z; simp)).op y := fun _ => rfl
  refine Eq.trans (comp_val_app_of _ _ rfl T h1) ?_
  exact (h2 _).trans (map_comp_val M _ _ k x)

variable {M : X.Modules} {N : Z.Modules} {L : Y.Modules}

/-- **The endomorphism of `L` obtained by cancelling the outer comparison against the two inner
ones.** Undo the comparison of the outer pair, read the restriction along `p₃` as an iterated
restriction, and apply the two inner comparisons in turn. -/
public def legEndo (hp : p₁ ≫ p₂ = p₃)
    (e₂ : (Scheme.Modules.restrictFunctor p₂).obj M ≅ N)
    (e₁ : (Scheme.Modules.restrictFunctor p₁).obj N ≅ L)
    (e₃ : (Scheme.Modules.restrictFunctor p₃).obj M ≅ L) : L ⟶ L :=
  e₃.inv ≫ (legPairIso p₁ p₂ p₃ hp M).hom ≫
    (Scheme.Modules.restrictFunctor p₁).map e₂.hom ≫ e₁.hom

/-- **The endomorphism on a section**, in four factors: undo the outer comparison, restrict along
the identification of the two readings, then apply the inner comparisons. -/
public theorem legEndo_val_app (hp : p₁ ≫ p₂ = p₃)
    (e₂ : (Scheme.Modules.restrictFunctor p₂).obj M ≅ N)
    (e₁ : (Scheme.Modules.restrictFunctor p₁).obj N ≅ L)
    (e₃ : (Scheme.Modules.restrictFunctor p₃).obj M ≅ L) (T : Y.Opens)
    (k : p₂ ''ᵁ (p₁ ''ᵁ T) ⟶ p₃ ''ᵁ T) (x : L.val.obj (op T)) :
    (legEndo p₁ p₂ p₃ hp e₂ e₁ e₃).val.app (op T) x =
      e₁.hom.val.app (op T) (e₂.hom.val.app (op (p₁ ''ᵁ T))
        (M.val.map k.op (e₃.inv.val.app (op T) x))) := by
  refine Eq.trans (comp_val_app_of e₃.inv
    ((legPairIso p₁ p₂ p₃ hp M).hom ≫
      (Scheme.Modules.restrictFunctor p₁).map e₂.hom ≫ e₁.hom) rfl T rfl) ?_
  refine Eq.trans (comp_val_app_of (legPairIso p₁ p₂ p₃ hp M).hom
    ((Scheme.Modules.restrictFunctor p₁).map e₂.hom ≫ e₁.hom) rfl T
    (legPairIso_hom_val_app p₁ p₂ p₃ hp M T k _)) ?_
  exact comp_val_app_of ((Scheme.Modules.restrictFunctor p₁).map e₂.hom) e₁.hom rfl T rfl

/-- **The endomorphism applied to the image of a section under the outer comparison** is the two
inner legs applied to that section. This is the computation the composition law is read off
from. -/
public theorem legEndo_app_hom_app (hp : p₁ ≫ p₂ = p₃)
    (e₂ : (Scheme.Modules.restrictFunctor p₂).obj M ≅ N)
    (e₁ : (Scheme.Modules.restrictFunctor p₁).obj N ≅ L)
    (e₃ : (Scheme.Modules.restrictFunctor p₃).obj M ≅ L) {T : Y.Opens} {T₀ : X.Opens}
    (j₃ : p₃ ''ᵁ T ⟶ T₀) (m : p₂ ''ᵁ (p₁ ''ᵁ T) ⟶ T₀) (s : M.val.obj (op T₀)) :
    (legEndo p₁ p₂ p₃ hp e₂ e₁ e₃).val.app (op T) (chartLeg p₃ e₃ j₃ s) =
      e₁.hom.val.app (op T) (e₂.hom.val.app (op (p₁ ''ᵁ T)) (M.val.map m.op s)) := by
  refine Eq.trans (legEndo_val_app p₁ p₂ p₃ hp e₂ e₁ e₃ T
    (eqToHom (image_eq_image_image p₁ p₂ p₃ hp T)) _) ?_
  refine congrArg (e₁.hom.val.app (op T)) (congrArg (e₂.hom.val.app (op (p₁ ''ᵁ T))) ?_)
  refine Eq.trans (congrArg (M.val.map (eqToHom
    (image_eq_image_image p₁ p₂ p₃ hp T)).op) ?_) (map_comp_val M _ j₃ m s)
  exact Stacks.AlgebraicGeometry.TwistRigidity.iso_inv_app_hom_app e₃ (op T) _

/-- **The composite of the two inner legs, written with the comparisons' own naturality.** The
restriction along `i₁` is moved through the inner comparison, which is what turns the two legs
into one application of each comparison over the smaller open. -/
public theorem chartLeg_comp_eq (e₂ : (Scheme.Modules.restrictFunctor p₂).obj M ≅ N)
    (e₁ : (Scheme.Modules.restrictFunctor p₁).obj N ≅ L) {T : Y.Opens} {T' : Z.Opens}
    {T₀ : X.Opens} (i₁ : p₁ ''ᵁ T ⟶ T') (j₂ : p₂ ''ᵁ T' ⟶ T₀)
    (m : p₂ ''ᵁ (p₁ ''ᵁ T) ⟶ T₀) (s : M.val.obj (op T₀)) :
    chartLeg p₁ e₁ i₁ (chartLeg p₂ e₂ j₂ s) =
      e₁.hom.val.app (op T) (e₂.hom.val.app (op (p₁ ''ᵁ T)) (M.val.map m.op s)) := by
  refine congrArg (e₁.hom.val.app (op T)) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply e₂.hom.val i₁.op _).symm ?_
  refine congrArg (e₂.hom.val.app (op (p₁ ''ᵁ T))) ?_
  exact (restrict_val_map p₂ M i₁ _).trans (map_comp_val M _ j₂ m s)

/-- **The composition law for the three comparisons on sections, from one endomorphism being the
identity.** Over every triple of opens and for every triple of inclusions: following the
comparison through the middle module by the inner comparison is the comparison of the outer
pair. -/
public theorem isEvalComposite_of_legEndo_eq_id (hp : p₁ ≫ p₂ = p₃)
    (e₂ : (Scheme.Modules.restrictFunctor p₂).obj M ≅ N)
    (e₁ : (Scheme.Modules.restrictFunctor p₁).obj N ≅ L)
    (e₃ : (Scheme.Modules.restrictFunctor p₃).obj M ≅ L)
    (hid : legEndo p₁ p₂ p₃ hp e₂ e₁ e₃ = 𝟙 L) {T : Y.Opens} {T' : Z.Opens} {T₀ : X.Opens}
    (i₁ : p₁ ''ᵁ T ⟶ T') (j₂ : p₂ ''ᵁ T' ⟶ T₀) (j₃ : p₃ ''ᵁ T ⟶ T₀) :
    IsEvalComposite (chartLeg p₂ e₂ j₂) (chartLeg p₁ e₁ i₁) (chartLeg p₃ e₃ j₃) := by
  intro s
  have hm : p₂ ''ᵁ (p₁ ''ᵁ T) ⟶ T₀ :=
    eqToHom (image_eq_image_image p₁ p₂ p₃ hp T) ≫ j₃
  refine Eq.trans (chartLeg_comp_eq p₁ p₂ e₂ e₁ i₁ j₂ hm s) ?_
  refine Eq.trans (legEndo_app_hom_app p₁ p₂ p₃ hp e₂ e₁ e₃ j₃ hm s).symm ?_
  exact congrArg (fun φ : L ⟶ L => φ.val.app (op T) (chartLeg p₃ e₃ j₃ s)) hid

end Stacks.AlgebraicGeometry.ChartCocycleRigidity

end
