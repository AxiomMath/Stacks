module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.RankOneTensorMonoid
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# The reflexive tensor powers of a coherent reflexive module

Let `X` be an integral locally Noetherian scheme and `ℱ` a coherent reflexive `𝒪_X`-module.
The *reflexive tensor powers* of `ℱ` are defined by

`ℱ^{[0]} = 𝒪_X`, `ℱ^{[n + 1]} = (ℱ ⊗_{𝒪_X} ℱ^{[n]})^{∨∨}`,

which is the recursion of [Stacks, Tag 0EBN].  They are the iterates of the hull tensor product
`AlgebraicGeometry.CoherentReflexive.tensorObj` of [Stacks, Tag 0EBH], so each `ℱ^{[n]}` is
again coherent and reflexive with no further argument, and `ℱ^{[1]} ≅ ℱ` by the unit constraint
of that tensor product.

A global section `s ∈ Γ(X, ℱ)`, viewed as a morphism `σ : 𝒪_X ⟶ ℱ`, gives the transition maps
`ℱ^{[n]} ⟶ ℱ^{[n + 1]}` of multiplication by `s`, and hence the directed system

`𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯`

whose colimit is the subject of the second assertion of [Stacks, Tag 0EBN].

## Main definitions

* `AlgebraicGeometry.CoherentReflexive.tensorObjMap`: functoriality of the hull tensor product,
  at the level of morphisms.
* `AlgebraicGeometry.CoherentReflexive.reflexivePower`: the powers `ℱ^{[n]}`.
* `AlgebraicGeometry.CoherentReflexive.reflexivePowerStep`: multiplication by a section,
  `ℱ^{[n]} ⟶ ℱ^{[n + 1]}`.
* `AlgebraicGeometry.CoherentReflexive.reflexivePowerSequence`: the directed system above, as a
  functor out of `ℕ`.
* `AlgebraicGeometry.CoherentReflexive.reflexivePowerModules`: the same system read as a functor
  into all of `X.Modules`, which is where its colimit is taken.

## Main results

* `AlgebraicGeometry.CoherentReflexive.reflexivePowerOne`: `ℱ^{[1]} ≅ ℱ`.
* `AlgebraicGeometry.CoherentReflexive.reflexivePowerStep_zero`: the first transition map is the
  section itself, under `ℱ^{[1]} ≅ ℱ`.

## Implementation notes

The powers are built on `AlgebraicGeometry.CoherentReflexive.CoherentReflexiveModules X` rather
than on `X.Modules`, so that coherence and reflexivity are carried by the objects themselves:
`tensorObj` is `(hullReflection X).obj` of the ordinary tensor product and
`hullReflection X` lands in the coherent reflexive modules by construction.  Only at the very
end, when the colimit is formed, is the system pushed into `X.Modules`, where the colimit lives;
the subcategory of coherent reflexive modules has no filtered colimits (the colimit of the
system is not coherent in general).

The recursion tensors the *new* factor on the left, `ℱ^{[n + 1]} = ℱ ⊗ ℱ^{[n]}`, which makes the
transition map multiplication by `s` in the first variable and lets it be written with the left
unit constraint `unitTensorObj` and functoriality in the first variable alone.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 0EBH](https://stacks.math.columbia.edu/tag/0EBH)
-/

@[expose] public section

open CategoryTheory
open Stacks.AlgebraicGeometry.ReflexiveHull (CoherentModules CoherentReflexiveModules inclusion)

universe u

namespace AlgebraicGeometry.CoherentReflexive

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-! ### Functoriality of the hull tensor product -/

/-- **Functoriality of the hull tensor product in both variables**, at the level of morphisms:
the reflexive hull of the functoriality of the ordinary tensor product.  This is the
morphism-level companion of `AlgebraicGeometry.CoherentReflexive.tensorObjIso`. -/
noncomputable def tensorObjMap {F F' G G' : CoherentReflexiveModules X} (f : F ⟶ F')
    (g : G ⟶ G') : tensorObj F G ⟶ tensorObj F' G' :=
  (hullReflection X).map (ObjectProperty.homMk
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
        (X := (F.obj.obj, G.obj.obj)) (Y := (F'.obj.obj, G'.obj.obj)) (f.hom.hom, g.hom.hom)))

/-! ### The reflexive powers -/

/-- The reflexive tensor powers `ℱ^{[n]}` of [Stacks, Tag 0EBN]: the structure sheaf in degree
zero, and `ℱ^{[n + 1]} = (ℱ ⊗_{𝒪_X} ℱ^{[n]})^{∨∨}` for the hull tensor product of
[Stacks, Tag 0EBH]. -/
noncomputable def reflexivePower (F : CoherentReflexiveModules X) :
    ℕ → CoherentReflexiveModules X
  | 0 => unitObj X
  | n + 1 => tensorObj F (reflexivePower F n)

/-- The zeroth reflexive power is the structure sheaf. -/
theorem reflexivePower_zero (F : CoherentReflexiveModules X) :
    reflexivePower F 0 = unitObj X := rfl

/-- The `(n + 1)`-st reflexive power is the hull tensor product of `ℱ` with the `n`-th. -/
theorem reflexivePower_succ (F : CoherentReflexiveModules X) (n : ℕ) :
    reflexivePower F (n + 1) = tensorObj F (reflexivePower F n) := rfl

/-- **The first reflexive power is the module itself**, `ℱ^{[1]} ≅ ℱ`, by the unit constraint of
the hull tensor product. -/
noncomputable def reflexivePowerOne (F : CoherentReflexiveModules X) :
    reflexivePower F 1 ≅ F :=
  tensorObjUnit F

/-- Every reflexive power is a coherent `𝒪_X`-module. -/
instance isCoherent_reflexivePower (F : CoherentReflexiveModules X) (n : ℕ) :
    _root_.SheafOfModules.IsCoherent (reflexivePower F n).obj.obj :=
  (reflexivePower F n).obj.property

/-- Every reflexive power is a reflexive `𝒪_X`-module. -/
theorem isReflexive_reflexivePower (F : CoherentReflexiveModules X) (n : ℕ) :
    Stacks.AlgebraicGeometry.ReflexiveModules.IsReflexive (reflexivePower F n).obj.obj :=
  (reflexivePower F n).property

/-! ### Multiplication by a section -/

variable (F : CoherentReflexiveModules X) (σ : unitObj X ⟶ F)

/-- **Multiplication by a section**, `ℱ^{[n]} ⟶ ℱ^{[n + 1]}`.  A section of `ℱ` is a morphism
`σ : 𝒪_X ⟶ ℱ`, and the transition map is `σ` tensored with the identity of `ℱ^{[n]}`, read
through the left unit constraint `𝒪_X ⊗ ℱ^{[n]} ≅ ℱ^{[n]}`. -/
noncomputable def reflexivePowerStep (n : ℕ) :
    reflexivePower F n ⟶ reflexivePower F (n + 1) :=
  (unitTensorObj (reflexivePower F n)).inv ≫ tensorObjMap σ (𝟙 (reflexivePower F n))

/-- The directed system `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯` of [Stacks, Tag 0EBN], as a functor out of
`ℕ`. -/
noncomputable def reflexivePowerSequence : ℕ ⥤ CoherentReflexiveModules X :=
  Functor.ofSequence (reflexivePowerStep F σ)

/-- The directed system of reflexive powers, read in `X.Modules`.  This is the shape in which
its colimit is taken: the full subcategory of coherent reflexive modules is not closed under
filtered colimits. -/
noncomputable def reflexivePowerModules : ℕ ⥤ X.Modules :=
  reflexivePowerSequence F σ ⋙ inclusion X ⋙ ObjectProperty.ι _

/-- The `n`-th term of the system in `X.Modules` is the underlying module of `ℱ^{[n]}`. -/
theorem reflexivePowerModules_obj (n : ℕ) :
    (reflexivePowerModules F σ).obj n = (reflexivePower F n).obj.obj := rfl

/-- The system starts at the structure sheaf. -/
theorem reflexivePowerModules_obj_zero :
    (reflexivePowerModules F σ).obj 0 =
      Stacks.AlgebraicGeometry.ReflexiveModules.unitModule X := rfl

end AlgebraicGeometry.CoherentReflexive

end
