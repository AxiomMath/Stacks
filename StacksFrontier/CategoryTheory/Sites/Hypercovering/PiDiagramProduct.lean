module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence

/-!
# A diagonal diagram composed with `lim` is the product of the family

`Stacks.CategoryTheory.Hypercovering.piDiagram F ⋙ lim` is how a product of functors is presented
to the limit-preservation lemmas:  it is the pointwise product, `a ↦ ∏ᶜ (fun i ↦ (F i).obj a)`.
This file identifies it with the product `∏ᶜ F` taken in the functor category, which is the form
`CategoryTheory.Functor.rightAcyclic_of_isoPi` consumes.

## Main results

* `Stacks.CategoryTheory.Hypercovering.discreteFunctorFlipIsoPiDiagram`:
  `(Discrete.functor F).flip ≅ piDiagram F`.
* `Stacks.CategoryTheory.Hypercovering.piDiagramCompLimIsoPi`:
  `piDiagram F ⋙ lim ≅ ∏ᶜ F`.
* `Stacks.CategoryTheory.Hypercovering.compPiDiagramIso`:
  `P ⋙ piDiagram F ≅ piDiagram (fun i ↦ P ⋙ F i)`.

## Implementation notes

The two functors `(Discrete.functor F).flip` and `piDiagram F` agree on objects and morphisms as
*descriptions* — both send `a` to the discrete diagram `i ↦ (F i).obj a` — but they are not
definitionally equal, and the component of the comparison is **not** `Iso.refl`:
`Functor.flip`'s value at `a` is a functor assembled field by field, whereas `piDiagram`'s is
literally `Discrete.functor`.  Indeed, `Iso.refl` is rejected with

```
Iso.refl ((Discrete.functor F).flip.obj a) has type
  (Discrete.functor F).flip.obj a ≅ (Discrete.functor F).flip.obj a
but is expected to have type
  (Discrete.functor F).flip.obj a ≅ (piDiagram F).obj a
```

so the component has to be built inside the discrete category, by `Discrete.natIso` applied to
`Iso.refl` at each index.  Ascribing the type of the component does not help, and neither do
explicit universes:  the mismatch is real rather than an elaboration order problem.

With the comparison in hand the identification is Mathlib's
`CategoryTheory.Limits.limitIsoFlipCompLim`, which says that a limit in a functor category is the
pointwise limit; `∏ᶜ F` is `limit (Discrete.functor F)` by definition.
-/

@[expose] public noncomputable section

universe v₁ u₁ v₂ u₂

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory.Hypercovering

variable {ι : Type*} {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **The flip of a discrete diagram of functors is the diagonal diagram of the family.**  Both
send an object `a` to the discrete diagram `i ↦ (F i).obj a`; the comparison is built inside the
discrete category, `Iso.refl` being the wrong component for the reason recorded in the module
docstring. -/
def discreteFunctorFlipIsoPiDiagram (F : ι → (C ⥤ D)) :
    (Discrete.functor F).flip ≅ piDiagram F :=
  NatIso.ofComponents
    (fun a ↦ Discrete.natIso (fun i ↦ Iso.refl ((F i.as).obj a)))
    (by intro a b f; ext ⟨i⟩; simp [piDiagram, Discrete.natTrans])

/-- **The diagonal diagram composed with `lim` is the product of the family**, the product being
taken in the functor category.  Limits in a functor category are pointwise
(`CategoryTheory.Limits.limitIsoFlipCompLim`) and `∏ᶜ F` is `limit (Discrete.functor F)`. -/
def piDiagramCompLimIsoPi [HasLimitsOfShape (Discrete ι) D] (F : ι → (C ⥤ D)) :
    piDiagram F ⋙ lim ≅ ∏ᶜ F :=
  (Functor.isoWhiskerRight (discreteFunctorFlipIsoPiDiagram F) lim).symm ≪≫
    (limitIsoFlipCompLim (Discrete.functor F)).symm

/-- **Precomposing a diagonal diagram with a functor is the diagonal diagram of the precomposed
family.**  Both send `b` to the discrete diagram `i ↦ (F i).obj (P.obj b)`, and the components
are identities. -/
def compPiDiagramIso {B : Type*} [Category* B] (P : B ⥤ C) (F : ι → (C ⥤ D)) :
    P ⋙ piDiagram F ≅ piDiagram (fun i ↦ P ⋙ F i) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by ext ⟨i⟩; simp [piDiagram])

end Stacks.CategoryTheory.Hypercovering

end
