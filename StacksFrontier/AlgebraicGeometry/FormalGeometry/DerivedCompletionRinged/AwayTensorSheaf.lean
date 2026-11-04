module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwayTensorPresheaf
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery

/-!
# Inverting two global sections at once is inverting their product

Let `(𝒞, 𝒪)` be a ringed site and let `f`, `g` be global sections of `𝒪`. Then

`𝒪_f ⊗_𝒪 𝒪_g = 𝒪_{f g}`

as sheaves of `𝒪`-modules. This is the input, other than the currying isomorphism, of the
displayed identity in the proof of [Stacks, Tag 0996(3)].

## Main definitions

* `AlgebraicGeometry.RingedSite.awayTensorSheafIso`: **the identity above**.

## Implementation notes

There is nothing left to prove: the presheaf-level identity
`AlgebraicGeometry.RingedSite.awayTensorPresheafIso` is carried across sheafification by Stacks
0GMW, `PresheafOfModules.sheafificationTensorIso`, and the two tensor factors and
the result are identified with `𝒪_f`, `𝒪_g` and `𝒪_{f g}` by
`AlgebraicGeometry.RingedSite.awayModuleSheafificationIso`, the bridge of
`AwayTensorBridge.lean` which exhibits each as the sheafification of the presheaf of sectionwise
localizations at exactly the spelling 0GMW speaks.

Nothing here carries a `stacks` attribute: the identity is an input to the proof of Tag 0996(3),
not one of that tag's three clauses, and the source does not state it.

## References

* [Stacks Project, Tag 0996](https://stacks.math.columbia.edu/tag/0996)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry.SheafOfModules

universe u

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u}) [HasWeakSheafify X.J CommRingCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify X.J AddCommGrpCat.{u}]

variable (f g : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **`𝒪_f ⊗_𝒪 𝒪_g = 𝒪_{f g}`**: inverting two global sections of the structure sheaf
independently and tensoring is inverting their product. -/
def awayTensorSheafIso :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (awayModule X f)).obj (awayModule X g) ≅
      awayModule X (mulGlobalSection X f g) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).mapIso
        (awayModuleSheafificationIso X f).symm).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj _).mapIso (awayModuleSheafificationIso X
        g).symm) ≪≫
    (PresheafOfModules.sheafificationTensorIso.{u, u, u, u, u}
      X.J (Osharp := X.O) (𝟙 X.O.obj)).app
      (awayModulePresheafAlt X f, awayModulePresheafAlt X g) ≪≫
    (PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).mapIso (awayTensorPresheafIso X f g) ≪≫
    awayModuleSheafificationIso X (mulGlobalSection X f g)

end AlgebraicGeometry.RingedSite

end
