module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksFrontier.Cotangent.PolynomialAlgebraSite
import StacksCore.Tactic.StacksAttribute

/-!
# The augmentation ideal on the site of a polynomial algebra

Let `A → B` be a ring map and work on the site `C_{B/A}` of polynomial `A`-algebras augmented to
`B`. The augmentations assemble into a map of sheaves of rings `𝒪 → B̲`, whose kernel

```
𝒥 = ker(𝒪 → B̲)
```

is a sheaf of `𝒪`-modules. Over the object `(P, α)` of `C_{B/A}` its sections are `ker(α)`, the
ideal that Stacks 08R7 calls `J`.

## Main definitions

* `CommAlgCat.polynomialStructureRingSheaf` and `CommAlgCat.polynomialConstantRingSheaf`: `𝒪`
  and `B̲`, read as sheaves of not necessarily commutative rings.
* `CommAlgCat.polynomialAugmentationRingHom`: the augmentation `𝒪 → B̲` as a map of sheaves of
  rings.
* `CommAlgCat.polynomialAugmentationModuleHom`: the augmentation `𝒪 → B̲` as a map of sheaves of
  `𝒪`-modules, `B̲` being an `𝒪`-module by restriction of scalars along the augmentation.
* `CommAlgCat.polynomialAugmentationIdeal`: the kernel `𝒥` of that map.

## References

* [Stacks Project, Tag 08R7](https://stacks.math.columbia.edu/tag/08R7)
* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CommAlgCat

universe u

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-- The tautological sheaf of rings `𝒪` on `C_{B/A}`, with commutativity forgotten. -/
abbrev polynomialStructureRingSheaf : Sheaf (polynomialTopology A B) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (polynomialStructureRingedTopos A B).O)

/-- The constant sheaf of rings `B̲` on `C_{B/A}`, with commutativity forgotten. -/
abbrev polynomialConstantRingSheaf : Sheaf (polynomialTopology A B) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (polynomialConstantRingedTopos A B).O)

/-- The augmentation `𝒪 ⟶ B̲` of Stacks 08PR, as a map of sheaves of not necessarily commutative
rings. -/
abbrev polynomialAugmentationRingHom :
    polynomialStructureRingSheaf A B ⟶ polynomialConstantRingSheaf A B :=
  (sheafCompose (polynomialTopology A B)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (polynomialAugmentation A B)

/-- The augmentation `𝒪 → B̲`, read as a map of sheaves of `𝒪`-modules: the target is `B̲` with
its `𝒪`-module structure obtained by restriction of scalars along the augmentation, and the map is
the one sending the unit section of `𝒪` to the unit section of `B̲`. -/
@[stacks 08R7 "the augmentation O → B of sheaves of O-modules"]
def polynomialAugmentationModuleHom :
    SheafOfModules.unit (polynomialStructureRingSheaf A B) ⟶
      (SheafOfModules.restrictScalars (polynomialAugmentationRingHom A B)).obj
        (SheafOfModules.unit (polynomialConstantRingSheaf A B)) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun X => (1 : (polynomialConstantRingSheaf A B).obj.obj X))
      (fun X Y f => by
        change (polynomialConstantRingSheaf A B).obj.map f 1 = 1
        exact map_one _))

/-- The augmentation ideal `𝒥 = ker(𝒪 → B̲)` on the site `C_{B/A}`, a sheaf of `𝒪`-modules. Its
inclusion `𝒥 ⊂ 𝒪` is `CategoryTheory.Limits.kernel.ι`. -/
@[stacks 08R7 "the defining ideal J = ker(O → B)"]
abbrev polynomialAugmentationIdeal :
    SheafOfModules.{u + 1} (polynomialStructureRingSheaf A B) :=
  kernel (polynomialAugmentationModuleHom A B)

end CommAlgCat

end
