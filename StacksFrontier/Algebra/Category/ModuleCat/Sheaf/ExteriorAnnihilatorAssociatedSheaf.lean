module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAnnihilatorStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerAssociatedSheaf
public import StacksFrontier.Algebra.Module.Projective.Determinant.ExteriorPowerBaseChange

/-!
# The degreewise annihilator of the sheaf associated to a module

Let `(X, 𝒪_X)` be a ringed space, `α : R → Γ(X, 𝒪_X)` a ring homomorphism and `M` an
`R`-module, and let `ℱ_M` be construction (3) of Stacks 01BH. The degree-`n` part of the
annihilator of the degree-one elements of `⋀_R M`, `Stacks.ExteriorAnnihilator.part R M n`, is a
submodule of `⋀ⁿ_R M`, so construction (3) carries the inclusion to a morphism
`ℱ_{partₙ} ⟶ ℱ_{⋀ⁿ_R M}`; composing with the comparison
`Stacks.AssociatedSheaf.exteriorPowerIso` of `ℱ_{⋀ⁿ_R M}` with `⋀ⁿ(ℱ_M)` gives the comparison
this file constructs,

```
ℱ_{partₙ(det M)} ⟶ ⋀ⁿ(ℱ_M),
```

for an arbitrary bundle of tensor, exterior and symmetric algebras on `ℱ_M` in the sense of
Section 17.21.

## Main definitions

* `Stacks.AssociatedSheaf.annihilatorPartSource`: the submodule `partₙ` of `⋀ⁿ_R M` read as a
  module, the source of construction (3) here.
* `Stacks.AssociatedSheaf.annihilatorPartPresheafHom`: the presheaf-level comparison
  `𝒪_X(V) ⊗_R partₙ ⟶ ⋀ⁿ_{𝒪_X(V)}(𝒪_X(V) ⊗_R M)`, the sheafification of which is the
  comparison.
* `Stacks.AssociatedSheaf.annihilatorPartToExteriorPowerModel` and
  `Stacks.AssociatedSheaf.annihilatorPartToExteriorPower`: **the comparison
  `ℱ_{partₙ(det M)} ⟶ ⋀ⁿ(ℱ_M)`**, with its source in the
  `SheafOfModules.sheafifyModulePresheaf` spelling and in the `associatedSheaf` spelling
  respectively.
* `Stacks.AssociatedSheaf.annihilatorPartToExteriorPower'`: the same comparison assembled in the
  other order, as construction (3) applied to the inclusion followed by
  `Stacks.AssociatedSheaf.exteriorPowerIso`.

## Implementation notes

**Where the ring presheaf is spelled, and why the two forms are both given.** As recorded in the
implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ExteriorPowerAssociatedSheaf.lean`, construction
(3) indexes its presheaves by
`Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf X.presheaf` while the presheaf-model form
of Tag 01CG indexes them by `(CategoryTheory.Sheaf.toRingCat _ X.sheaf).obj`; the two agree, but
putting a term of each in one expression makes the unifier unfold two
`PresheafOfModules.exteriorAlgebraPiece` terms down to `TensorProduct`. So the sheafification
functor of the first leg of `annihilatorPartToExteriorPowerModel` is written `_` and solved from
the second leg, exactly as in `Stacks.AssociatedSheaf.modelExteriorPowerIsoFull`, and that
definition is left with its inferred type. The `associatedSheaf`-spelled form
`annihilatorPartToExteriorPower` crosses the two spellings once, through
`Stacks.AssociatedSheaf.modelAssociatedSheaf`, and composes with
`Stacks.AssociatedSheaf.exteriorPowerIso`, which has already made that crossing internally.

**Why the codomain of the inclusion is written at `ExteriorAlgebra.intPiece`.** The sectionwise
exterior powers are built from the `ℤ`-graded spelling, so `annihilatorPartι` gives the inclusion
of `partₙ` with codomain `Stacks.AssociatedSheaf.exteriorPowerSource`; the other spelling is
definitionally equal but makes the unifier compare two presentations of the exterior algebra.

## References

* [Stacks Project, Tag 0FJN](https://stacks.math.columbia.edu/tag/0FJN)
* [Stacks Project, Tag 0FJA](https://stacks.math.columbia.edu/tag/0FJA)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

namespace Stacks.AssociatedSheaf

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

variable (R : CommRingCat.{u}) (X : RingedSpace.{u, u}) (α : ↥R →+* X.presheaf.obj (op ⊤))
  (M : ModuleCat.{u} ↥R) (n : ℕ)

/-- The degree-`n` part of the annihilator of the degree-one elements of `⋀_R M`, read as a
module over `R`. -/
abbrev annihilatorPartSource : ModuleCat.{u} ↥R :=
  ModuleCat.of ↥R ↥(Stacks.ExteriorAnnihilator.part ↥R ↥M n)

/-- The inclusion `partₙ ⟶ ⋀ⁿ_R M`, with the codomain in the `ℤ`-graded spelling the
sectionwise exterior powers are built from. -/
abbrev annihilatorPartι : annihilatorPartSource R M n ⟶ exteriorPowerSource R M n :=
  ModuleCat.ofHom
    ((Stacks.ExteriorAnnihilator.part ↥R ↥M n).subtype :
      ↥(Stacks.ExteriorAnnihilator.part ↥R ↥M n) →ₗ[↥R]
        ↥(ExteriorAlgebra.intPiece ↥R ↥M (n : ℤ)))

/-- The presheaf-level inclusion `𝒪_X(V) ⊗_R partₙ ⟶ 𝒪_X(V) ⊗_R ⋀ⁿ_R M`. -/
abbrev annihilatorPartPresheafι :
    associatedPresheaf X α (annihilatorPartSource R M n) ⟶
      associatedPresheaf X α (exteriorPowerSource R M n) :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (globalSectionsMap X α)).map
    ((constantModuleFunctor X).map (annihilatorPartι R M n))

/-- The presheaf-level comparison `𝒪_X(V) ⊗_R partₙ ⟶ ⋀ⁿ_{𝒪_X(V)}(𝒪_X(V) ⊗_R M)`: the inclusion
base-changed to `V`, followed by the presheaf-level base-change comparison of Tag 01I8. -/
def annihilatorPartPresheafHom :
    associatedPresheaf X α (annihilatorPartSource R M n) ⟶
      PresheafOfModules.exteriorAlgebraPiece (n : ℤ) (associatedPresheaf X α M) :=
  annihilatorPartPresheafι R X α M n ≫ (specTildeExteriorPowerPresheafIso R X α M n).hom

/-- **The comparison `ℱ_{partₙ(det M)} ⟶ ⋀ⁿ(ℱ_M)`**, with the source in the
`SheafOfModules.sheafifyModulePresheaf` spelling: the sheafification of
`annihilatorPartPresheafHom`, followed by the presheaf-model form of Tag 01CG. -/
def annihilatorPartToExteriorPowerModel
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) (model R X α M)) :=
  CategoryTheory.Functor.map _ (annihilatorPartPresheafHom R X α M n) ≫
    (SheafOfModules.presheafModelExteriorPowerIso (Opens.grothendieckTopology X.carrier)
      (associatedPresheaf X α M) A (Iso.refl _) (n : ℤ)).hom

/-- **The comparison `ℱ_{partₙ(det M)} ⟶ ⋀ⁿ(ℱ_M)`.** -/
def annihilatorPartToExteriorPower
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) (associatedSheaf X α M)) :
    associatedSheaf X α (annihilatorPartSource R M n) ⟶ A.exteriorPower n :=
  (modelAssociatedSheaf R X α (annihilatorPartSource R M n)).hom ≫
    annihilatorPartToExteriorPowerModel R X α M n A

/-- **The comparison `ℱ_{partₙ(det M)} ⟶ ⋀ⁿ(ℱ_M)`, built the other way round**: construction
(3) applied to the inclusion `partₙ ⟶ ⋀ⁿ_R M`, followed by
`Stacks.AssociatedSheaf.exteriorPowerIso`. Both routes make the change of spelling of the sheaf
of rings exactly once, this one inside `exteriorPowerIso`. -/
def annihilatorPartToExteriorPower'
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) (associatedSheaf X α M)) :
    associatedSheaf X α (annihilatorPartSource R M n) ⟶ A.exteriorPower n :=
  (associatedSheafFunctor X α).map (annihilatorPartι R M n) ≫
    (exteriorPowerIso R X α M n A).hom

end Stacks.AssociatedSheaf

end
