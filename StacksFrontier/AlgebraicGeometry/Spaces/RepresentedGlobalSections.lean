module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspace

/-!
# The global functions on a represented algebraic space

For an algebraic space represented by an object `T` of the big fppf site, the global sections of
the structure sheaf `AlgebraicGeometry.Space.structureRingSheaf` of its small étale site are the
global regular functions on the scheme underlying `T`: a global regular function corresponds to
the global section whose value on each étale chart is its pullback.

## Main definitions

* `AlgebraicGeometry.Space.representedUnitSectionsEquiv`: the bijection
  `Γ(U_étale, 𝒪) ≃ Γ(U, ⊤)` for a represented algebraic space.
* `AlgebraicGeometry.Space.representedUnitSection`: the global section of the structure sheaf
  determined by a global regular function on the representing scheme.

## Main results

* `AlgebraicGeometry.Space.eval_representedUnitSection`: its value on an étale chart is the
  pullback of the function along the chart's structure morphism.
* `AlgebraicGeometry.Space.representedUnitSectionsEquiv_apply_eq_eval`: the forward direction is
  evaluation at the identity chart.

## Implementation notes

No descent is involved, and in particular neither the étale descent of quasi-coherence nor
**Stacks 05B2** is: the small étale site of a *represented* presheaf has a **terminal object**,
the identity chart `AlgebraicGeometry.Space.idChart`
(`AlgebraicGeometry.Space.isTerminal_idChart`, which is the Yoneda lemma), and the global
sections of a sheaf of modules on a site with a terminal object are its sections at that object
(`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal`). The value of the structure
sheaf at a chart is `Γ` of the chart's scheme on the nose — `structurePresheaf` is
`(SmallEtale.toOver ⋙ BigFppfOver.toScheme).op ⋙ Scheme.Γ` — and the scheme of the identity
chart is the scheme of the representing object, so the right hand side needs no comparison
isomorphism.

In `AlgebraicGeometry.Space.eval_representedUnitSection` the morphism of the site along which the
function is pulled back is an argument `p` with `yoneda.map p` the chart's structure morphism,
rather than `AlgebraicGeometry.Space.yonedaEquiv` of that structure morphism; it is unique by
terminality of the identity chart.

## References

* [Stacks Project, Tag 03G7](https://stacks.math.columbia.edu/tag/03G7)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 06N3](https://stacks.math.columbia.edu/tag/06N3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)
  (hT : IsAlgebraicSpace B S hS (yoneda.obj T))

/-- **The global sections of the structure sheaf of a represented algebraic space are the global
regular functions on the representing scheme**, by evaluation at the identity chart, a terminal
object of the small étale site of `yoneda.obj T`. -/
noncomputable def representedUnitSectionsEquiv :
    (SheafOfModules.unit (structureRingSheaf B S hS ⟨yoneda.obj T, hT⟩)).sections ≃
      Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal
    (SheafOfModules.unit (structureRingSheaf B S hS ⟨yoneda.obj T, hT⟩))
    (isTerminal_idChart B S hS T)

/-- The bijection of `AlgebraicGeometry.Space.representedUnitSectionsEquiv` is evaluation at the
identity chart. -/
theorem representedUnitSectionsEquiv_apply_eq_eval
    (a : (SheafOfModules.unit (structureRingSheaf B S hS ⟨yoneda.obj T, hT⟩)).sections) :
    representedUnitSectionsEquiv B S hS T hT a = a.eval (op (idChart B S hS T)) :=
  rfl

/-- **The global section of the structure sheaf of a represented algebraic space determined by a
global regular function on the representing scheme.** -/
noncomputable def representedUnitSection (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    (SheafOfModules.unit (structureRingSheaf B S hS ⟨yoneda.obj T, hT⟩)).sections :=
  (representedUnitSectionsEquiv B S hS T hT).symm s

/-- **The value of `AlgebraicGeometry.Space.representedUnitSection` on an étale chart is the
pullback of the function along the chart's structure morphism**, for any morphism `p` of the
site with `yoneda.map p` the structure morphism of the chart. -/
theorem eval_representedUnitSection (s : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (V : SmallEtale B S hS (yoneda.obj T)) (p : V.obj.left ⟶ T)
    (hp : yoneda.map p = V.obj.hom) :
    (representedUnitSection B S hS T hT s).eval (op V) =
      ((BigFppfOver.toScheme B S hS).map p).appTop.hom s := by
  have hw : yoneda.map p ≫ (idChart B S hS T).obj.hom = V.obj.hom := (Category.comp_id _).trans hp
  set m : V ⟶ idChart B S hS T := ObjectProperty.homMk (CostructuredArrow.homMk p hw)
  have hunique : (isTerminal_idChart B S hS T).from V = m :=
    (isTerminal_idChart B S hS T).hom_ext _ _
  show ((structureRingSheaf B S hS ⟨yoneda.obj T, hT⟩).obj.map
      ((isTerminal_idChart B S hS T).from V).op).hom s = _
  rw [hunique]
  rfl

end AlgebraicGeometry.Space

end
