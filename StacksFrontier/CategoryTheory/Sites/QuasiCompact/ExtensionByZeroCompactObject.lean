module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Modules.ExtensionByZeroUnitSections
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero from a quasi-compact object is a compact object

Let `(C, O)` be a ringed site and `U` a quasi-compact object of `C`. The sheaf of modules
`j_{U!} O_U`, obtained by extending the structure sheaf of the slice site `C/U` by zero, is a
compact object of the category of sheaves of `O`-modules: morphisms out of it commute with
arbitrary direct sums.

The proof is the one in the source and it is a transport. Morphisms out of `j_{U!} O_U` are the
sections over `U` (Stacks 0G1V), naturally in the target, so the covariant additive
representable functor `Hom(j_{U!} O_U, -)` is isomorphic to the sections functor at `U`; and
sections over a quasi-compact object commute with direct sums (Stacks 0935). The only work is
that Stacks 0G1V gives a bijection of sets, whereas a comparison of additive functors needs it
to be a group isomorphism; `extensionByZeroUnitHomEquiv_additive` supplies that, from
additivity of the extension-by-zero adjunction.

## Main results

* `Stacks.Sites.homFromExtensionByZeroUnit_preservesCoproducts`: morphisms from the extension
  by zero of the structure sheaf on a quasi-compact slice object commute with direct sums.

## Implementation notes

Extension by zero is Mathlib's `SheafOfModules.pullback` along `Over.forget U`, taken at the
identity morphism of the restricted ring sheaf, which is how Stacks 03DI is formalized in this
repository; the structure sheaf of the slice site is `SheafOfModules.unit` of that restricted
ring sheaf. Morphisms out of an object are expressed by `preadditiveCoyoneda`, so the statement
that they commute with direct sums is preservation of colimits of discrete shape, which
includes the canonical comparison map and its naturality.

The indexing type of the direct sum lives in its own universe `w`, independent of the single
universe `u` of the ringed site: no size condition relates them, because Stacks 0935 imposes
none.

## References

* [Stacks Project, Tag 0936](https://stacks.math.columbia.edu/tag/0936)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
* [Stacks Project, Tag 0G1V](https://stacks.math.columbia.edu/tag/0G1V)
* [Stacks Project, Tag 03DI](https://stacks.math.columbia.edu/tag/03DI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites

universe u w

variable (X : AlgebraicGeometry.RingedSite.{u, u, u}) (U : X.C)

/-- Extension by zero of the structure sheaf of the slice site over `U`, as a sheaf of modules
on the ringed site. -/
private noncomputable abbrev extensionByZeroUnit :
    SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (SheafOfModules.pullback.{u} (F := Over.forget U)
    (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))).obj
      (SheafOfModules.unit (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))

/-- Restriction to a slice site is additive: it is computed on sections. -/
private lemma pushforward_over_additive :
    (SheafOfModules.pushforward.{u} (F := Over.forget U)
      (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))).Additive where
  map_add {_ _ p q} := by
    ext V z
    rfl

/-- Extension by zero is additive, being a left adjoint of an additive functor. -/
private lemma pullback_over_additive :
    (SheafOfModules.pullback.{u} (F := Over.forget U)
      (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))).Additive :=
  have := pushforward_over_additive X U
  (SheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
    (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))).left_adjoint_additive

/-- **Stacks 0G1V, additively.** The bijection of Stacks 0G1V between morphisms out of
`j_{U!} O_U` and sections over `U` is additive: the transposition step is additive because
extension by zero is a left adjoint of an additive functor, and the two remaining steps read
off a component of a morphism of sheaves of modules. -/
private lemma extensionByZeroUnitHomEquiv_additive
    (F : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (f g : extensionByZeroUnit X U ⟶ F) :
    Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U F (f + g) =
      Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U F f +
        Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U F g := by
  have := pushforward_over_additive X U
  have := pullback_over_additive X U
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let adj := SheafOfModules.pullbackPushforwardAdjunction.{u} (F := Over.forget U)
    (𝟙 (R.over U))
  change (((F.over U).unitHomEquiv
      (adj.homEquiv (SheafOfModules.unit (R.over U)) F (f + g))).val
        (op (Over.mk (𝟙 U)))) = _
  rw [adj.homAddEquiv_add (SheafOfModules.unit (R.over U)) F f g]
  rfl

/-- **Stacks 0936.** On a ringed site, morphisms out of the extension by zero of the structure
sheaf of the slice site over a quasi-compact object commute with arbitrary direct sums. -/
@[stacks 0936]
theorem homFromExtensionByZeroUnit_preservesCoproducts
    (hU : X.J.IsQuasiCompactObject U) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι)
      (preadditiveCoyoneda.obj (op
        ((SheafOfModules.pullback.{u}
          (F := Over.forget U)
          (𝟙 (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) :
            (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U) ⟶
              (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))).obj
            (SheafOfModules.unit
              (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over U))))) := by
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let H : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
    preadditiveCoyoneda.obj (op (extensionByZeroUnit X U))
  let S : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.toSheaf.{u} R ⋙ (sheafSections X.J AddCommGrpCat.{u}).obj (op U)
  let e : H ≅ S := NatIso.ofComponents
    (fun F => AddEquiv.toAddCommGrpIso
      { __ := Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv X.J R U F
        map_add' := extensionByZeroUnitHomEquiv_additive X U F })
    (fun f => AddCommGrpCat.ext fun h =>
      Stacks.Sites.ExtensionByZero.extensionByZeroUnitHomEquiv_naturality X.J R U h f)
  have : PreservesColimitsOfShape (Discrete ι) S :=
    sheafOfModules_sections_preserves_coproducts X.J R U hU ι
  exact preservesColimitsOfShape_of_natIso e.symm

end Stacks.Sites

end
