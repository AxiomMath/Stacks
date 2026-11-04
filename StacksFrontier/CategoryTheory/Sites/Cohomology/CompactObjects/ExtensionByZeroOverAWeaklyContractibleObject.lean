module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedExactFunctor
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.WeaklyContractible.CohomologyOverAWeaklyContractibleObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroIsCompact
import StacksCore.Tactic.StacksAttribute

/-! # Compactness of extension by zero from a quasi-compact weakly contractible object

Let `(C, O)` be a ringed site and let `U` be an object of `C` which is quasi-compact and weakly
contractible. Then the `O`-module `j_{U!} O_U` is a compact object of the unbounded derived
category `D(O)`.

This is Stacks 094E, and the proof is the source's: it discharges the two hypotheses of Stacks
094D. Weak contractibility of `U` makes `Γ(U, -)` exact on sheaves of modules, so all its higher
right derived functors vanish — in particular cohomology over `U` has cohomological dimension
zero. Quasi-compactness of `U` makes `Γ(U, -)` commute with direct sums, which together with
that vanishing gives the commutation for every `R ᵖ Γ(U, -)`.

## Main results

* `Stacks.Cohomology.CompactExtensionByZero.exact_evaluation_of_isWeaklyContractible`:
  **Stacks 0946 part (1) for sheaves of modules.** Evaluation of sheaves of modules at a weakly
  contractible object is exact.
* `Stacks.Cohomology.CompactExtensionByZero.preservesCoproducts_rightDerived_evaluation`:
  every `R ᵖ Γ(U, -)` on sheaves of modules commutes with direct sums, for `U` quasi-compact and
  weakly contractible.
* `isCompactObject_singleFunctor_extensionByZeroUnit_of_isWeaklyContractible`, in the same
  namespace, is **Stacks 094E**.

## Implementation notes

The two inputs from the abelian side transport to sheaves of modules through the identity

```
SheafOfModules.evaluation R (op U) ⋙ forget₂ (ModuleCat (R(U))) AddCommGrpCat
  = SheafOfModules.toSheaf R ⋙ (sheafSections J AddCommGrpCat).obj (op U)
```

which holds by `rfl`: evaluation of a sheaf of modules at `U` is, by construction, the sections
at `U` of the underlying abelian sheaf. The library's Stacks 0946 part (1) and Stacks 0935 part (2)
are stated for the right-hand side, so no comparison isomorphism is needed; `forget₂` reflects
finite colimits and colimits of discrete shape, which descends both facts from the composite to
`SheafOfModules.evaluation R (op U)` itself.

In positive degrees the commutation with direct sums is not inherited from degree zero: it holds
because the derived functor itself vanishes, by
`CategoryTheory.Functor.isZero_rightDerived_of_exact`.

The index universe of the direct sums is the universe `u` of the ringed site. Stacks 0935 part
(2) is stated for an arbitrary index type, but descending it from the underlying abelian sheaves
to sheaves of modules needs `forget₂` to *reflect* coproducts of that shape, which in turn needs
`ModuleCat.{u}` to have them; that holds only for `u`-small index types. The conclusion is
therefore `IsCompactObject.{u}`, which is the form Stacks 094E is asked for.

## References

* [Stacks Project, Tag 094E](https://stacks.math.columbia.edu/tag/094E)
* [Stacks Project, Tag 094D](https://stacks.math.columbia.edu/tag/094D)
* [Stacks Project, Tag 0946](https://stacks.math.columbia.edu/tag/0946)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.Cohomology.CompactExtensionByZero

universe u

variable (X : RingedSite.{u, u, u}) (U : X.C)

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] evaluationAdditive

/-- **Stacks 0946, part (1), for sheaves of modules.** Evaluation of sheaves of `O`-modules at a
weakly contractible object is exact.

Evaluation of a sheaf of modules at `U` is, by definition, the sections at `U` of the underlying
abelian sheaf, so the statement follows from the abelian-sheaf form of Stacks 0946 part (1) and
the right exactness of the passage to the underlying abelian sheaf, because `forget₂` reflects
finite colimits. -/
theorem exact_evaluation_of_isWeaklyContractible (hU : X.J.IsWeaklyContractible U) :
    exactFunctor (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) := by
  have hSections := Stacks.WeaklyContractible.exact_sheafSections_of_isWeaklyContractible.{u}
    X.J U hU
  have _ : PreservesFiniteColimits ((sheafSections X.J AddCommGrpCat.{u}).obj (op U)) :=
    ((exactFunctor_iff _).1 hSections).2
  have hcomp : PreservesFiniteColimits
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
        forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
          AddCommGrpCat.{u}) :=
    comp_preservesFiniteColimits
      (SheafOfModules.toSheaf.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      ((sheafSections X.J AddCommGrpCat.{u}).obj (op U))
  have _ := hcomp
  have _ : PreservesFiniteColimits
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
    preservesFiniteColimits_of_reflects_of_preserves _
      (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
        AddCommGrpCat.{u})
  have : PreservesFiniteLimits
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

/-- The higher right derived functors of evaluation at a weakly contractible object vanish. -/
private theorem isZero_rightDerived_evaluation_obj (hU : X.J.IsWeaklyContractible U) {p : ℕ}
    (hp : 0 < p) (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U)).rightDerived p).obj M) :=
  CategoryTheory.Functor.isZero_rightDerived_of_exactFunctor _
    (exact_evaluation_of_isWeaklyContractible X U hU) M p hp

/-- **The higher cohomology over a quasi-compact weakly contractible object commutes with direct
sums.** For `U` quasi-compact and weakly contractible, every `R ᵖ Γ(U, -)` on sheaves of
`O`-modules preserves coproducts indexed by an arbitrary type.

In degree zero this is Stacks 0935 part (2), transported from the underlying abelian sheaves. In
positive degrees the functor is itself zero, by exactness of `Γ(U, -)`. -/
theorem preservesCoproducts_rightDerived_evaluation
    (hU : X.J.IsQuasiCompactObject U) (hU' : X.J.IsWeaklyContractible U)
    (p : ℕ) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).rightDerived
        p) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    have hcomp : PreservesColimitsOfShape (Discrete I)
        (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U) ⋙
          forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
            AddCommGrpCat.{u}) :=
      Stacks.Sites.sheafOfModules_sections_preserves_coproducts
        X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U hU I
    have _ := hcomp
    have _ : PreservesColimitsOfShape (Discrete I)
        (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
          AddCommGrpCat.{u}) :=
      forgetToAddCommGrp_preservesCoproducts
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) I
    have _ : ReflectsColimitsOfShape (Discrete I)
        (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
          AddCommGrpCat.{u}) :=
      reflectsColimitsOfShape_of_reflectsIsomorphisms
    have _ : PreservesColimitsOfShape (Discrete I)
        (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
      preservesColimitsOfShape_of_reflects_of_preserves _
        (forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
          AddCommGrpCat.{u})
    have : PreservesFiniteLimits
        (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)) :=
      SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
    exact preservesColimitsOfShape_of_natIso
      (SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerivedZeroIsoSelf.symm
  · exact ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (op U)).rightDerived p).preservesColimitsOfShape_of_isZero
      (Functor.isZero_iff _ |>.2 (isZero_rightDerived_evaluation_obj X U hU' hp)) (Discrete I)

/-- **Stacks 094E.** Let `(C, O)` be a ringed site and let `U` be an object of `C` which is
quasi-compact and weakly contractible. Then `j_{U!} O_U`, placed in degree zero, is a compact
object of the unbounded derived category of `O`-modules.

The two hypotheses of Stacks 094D are discharged: weak contractibility makes `Γ(U, -)` exact, so
cohomology over `U` vanishes in positive degrees and in particular has finite cohomological
dimension, and together with quasi-compactness it makes every `R ᵖ Γ(U, -)` commute with direct
sums. -/
@[stacks 094E]
theorem isCompactObject_singleFunctor_extensionByZeroUnit_of_isWeaklyContractible
    (hU : X.J.IsQuasiCompactObject U) (hU' : X.J.IsWeaklyContractible U) :
    IsCompactObject.{u}
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((SheafOfModules.pullback.{u} (F := Over.forget U)
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))).obj
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)))) := by
  refine isCompactObject_singleFunctor_extensionByZeroUnit.{u, u} X U ⟨0, ?_⟩
    (preservesCoproducts_rightDerived_evaluation X U hU hU')
  intro p G hp
  exact isZero_rightDerived_evaluation_obj X U hU' (by exact_mod_cast hp) G

end Stacks.Cohomology.CompactExtensionByZero

end
