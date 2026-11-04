module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorRetract

/-!
# A module over a factor is its tensor product with that factor

Let `R ≅ ∏_i factor i` be a sheaf of commutative rings presented as a product and let `L` be a
sheaf of modules over the factor `factor n`, read as a sheaf of `R`-modules through the `n`-th
projection (`Stacks.SheafOfModules.RingSheafProductFactor.projRing`).  Then

`factor n ⊗_R L ≅ L`

in `Mod(R)`: the projection `R ⟶ factor n` is surjective on sections, so tensoring over `R`
against the factor does nothing to a module over the factor.

The module docstring of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingSheafProductFactorRetract` records this
isomorphism as true and deliberately proves only the retract, "only one of the two composites has
to be computed", because that was all its consumer — the off-diagonal vanishing of Stacks 0FPG —
needed.  The *diagonal* terms of the same implication need the isomorphism, and the second
composite turns out to cost nothing: the two maps of the retract are the left unit constraint
conjugates of `Stacks.SheafOfModules.RingSheafProductFactor.factorProjection` and
`factorInclusion`, so the composite the retract does not compute is the right whiskering of
`factorInclusion ≫ factorProjection`, which is the identity by
`Stacks.SheafOfModules.RingSheafProductFactor.factorInclusion_comp_factorProjection`.  No section
of a tensor product is touched, and in particular the local-pure-tensor extensionality the
retract file was avoiding is not needed after all.

## Main definitions

* `Stacks.SheafOfModules.RingSheafProductFactor.presheafIsoRestrictScalars`: the isomorphism at
  the level of presheaves of modules.
* `Stacks.SheafOfModules.RingSheafProductFactor.sheafTensorIsoRestrictScalars`: the isomorphism
  for the tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` of [Stacks, Tag 01CA],
  and `tensorObjIsoRestrictScalars` at the monoidal spelling `F ⊗ G` of
  `SheafOfModules.monoidalCategorySheafTensor`.

## Implementation notes

**The statement is false for a general `R`-module**, exactly as for the retract: at `L = R` and
two nonzero factors it would say `factor n ≅ R`.  The restriction of scalars is load-bearing.

**This is not the general base change.**  What the diagonal terms of the implication
`(2) ⟹ (1)` of Stacks 0FPG ultimately need is the comparison of `A ⊗_R B` with `A ⊗_{factor n} B`
for two modules `A` and `B` over the factor — the invertibility of
`Stacks.SheafOfModules.TensorRestrictScalars.laxComparison` at the projection.  The case proved
here is `A = factor n`, which is the diagonal term of the decomposition `𝒪_X = ∏_n 𝒪_n` with
`ℋ^n = 𝒪_n`; the general case is still absent.

Nothing here is a clause of Stacks 0FPG; this is a step of the proof of its implication
`(2) ⟹ (1)`, so no declaration carries the project tag.

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, whose diagonal terms consume this isomorphism.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe v u w t

noncomputable section

namespace Stacks.SheafOfModules.RingSheafProductFactor

/-- **The one-object step**: if `f : A ⟶ 𝟙_ C` and `g : 𝟙_ C ⟶ A` compose to the identity of `A`,
then the two left unit constraint conjugates of `f` and `g` compose to the identity of `A ⊗ M`.

Stated in an arbitrary monoidal category with every object and morphism a variable, so that it
applies by `exact` at a presheaf of modules, where the goal is not type-correct at `implicit`
transparency and no rewriting tactic acts on it. -/
public theorem whiskerRight_leftUnitor_comp_of_comp_eq_id {C : Type*} [Category* C]
    [MonoidalCategory C] {A : C} (f : A ⟶ 𝟙_ C) (g : 𝟙_ C ⟶ A) (hfg : f ≫ g = 𝟙 A) (M : C) :
    (f ▷ M ≫ (λ_ M).hom) ≫ ((λ_ M).inv ≫ g ▷ M) = 𝟙 (A ⊗ M) := by
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← MonoidalCategory.comp_whiskerRight, hfg,
    MonoidalCategory.id_whiskerRight]

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {ι : Type t}
  {factor : ι → Sheaf J CommRingCat.{max u v}} {R : Sheaf J CommRingCat.{max u v}}
  (hp : ProductPresentation R factor)
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]

section Presheaf

variable [DecidableEq ι]

/-- **A module over the `n`-th factor is isomorphic to its presheaf tensor product with that
factor.**  The two maps are those of `presheafRetractRestrictScalars`: `x ↦ 1 ⊗ x` one way and
`a ⊗ x ↦ a • x` the other.  One composite is the retract's; the other is the right whiskering of
`factorInclusion ≫ factorProjection = 𝟙`, the two left unit constraints cancelling. -/
public def presheafIsoRestrictScalars (n : ι)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n))) :
    ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L).val ≅
      ((factorModule hp n).val ⊗
        ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L).val) where
  hom := (λ_ _).inv ≫ (factorProjection hp n).val ▷ _
  inv := (factorInclusion hp n).val ▷ _ ≫ (λ_ _).hom
  hom_inv_id := (presheafRetractRestrictScalars hp n L).retract
  inv_hom_id := by
    have hval : (factorInclusion hp n).val ≫ (factorProjection hp n).val =
        𝟙 (factorModule hp n).val :=
      congrArg _root_.SheafOfModules.Hom.val (factorInclusion_comp_factorProjection hp n)
    exact whiskerRight_leftUnitor_comp_of_comp_eq_id _ _ hval _

end Presheaf

variable [HasBinaryBiproducts (_root_.SheafOfModules (Tensor.ringSheaf R))] [DecidableEq ι]

/-- **A module over the `n`-th factor is isomorphic to its tensor product with that factor**, for
the tensor product sheaf `Stacks.SheafOfModules.Tensor.sheafTensor` of [Stacks, Tag 01CA].

Sheafification carries `presheafIsoRestrictScalars` to an isomorphism between the sheafification
of `L` and the tensor product sheaf, and `SheafOfModules.counitIso` identifies the former with
`L`. -/
public def sheafTensorIsoRestrictScalars (n : ι)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n))) :
    ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L) ≅
      (((Tensor.sheafTensor R).obj (factorModule hp n)).obj
        ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L)) :=
  (_root_.SheafOfModules.counitIso R
      ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L)).symm ≪≫
    ((PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf (R))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (R)).obj))).mapIso
        (presheafIsoRestrictScalars hp n L)

/-- **A module over the `n`-th factor is isomorphic to its tensor product with that factor**, at
the monoidal spelling `F ⊗ G` of `SheafOfModules.monoidalCategorySheafTensor`, whose tensor
product is `Stacks.SheafOfModules.Tensor.sheafTensor` on the nose.

This is the form the diagonal terms of the assembly of the implication `(2) ⟹ (1)` of Stacks 0FPG
consume, at `L` the unit module: it says `𝒪_n ⊗_{𝒪_X} 𝒪_n ≅ 𝒪_n`. -/
public def tensorObjIsoRestrictScalars (n : ι)
    (L : _root_.SheafOfModules.{max u v} (Tensor.ringSheaf (factor n))) :
    letI := _root_.SheafOfModules.monoidalCategorySheafTensor R
    ((_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L) ≅
      (factorModule hp n ⊗ (_root_.SheafOfModules.restrictScalars (projRing hp n)).obj L) :=
  sheafTensorIsoRestrictScalars hp n L

end Stacks.SheafOfModules.RingSheafProductFactor

end

end
