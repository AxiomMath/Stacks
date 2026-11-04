module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction to a dense subsite commutes with the objectwise tensor product

Let `v : C ⥤ C'` be a functor and `O` a presheaf of commutative rings on `C'`. The tensor
product of sheaves of `O`-modules used in this development
(`Stacks.sheafTensorRight`, Stacks 03ER) is built in two steps: the *objectwise* tensor
product of the underlying presheaves of modules (`Stacks.tensorObj`,
`U ↦ M(U) ⊗_{O(U)} N(U)`), followed by sheafification. This file records that the first step
commutes with restriction along `v` **on the nose**, and nothing weaker: the restriction of
an objectwise tensor product is the objectwise tensor product of the restrictions, by `rfl`,
in both variables and on morphisms as well as objects.

This is the presheaf half of the statement that the tensor product of sheaves of modules
depends only on the ringed topos `(Sh(C'), O)` and not on the site presenting it (Stacks
03DG, method (2)); combined with `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence`
it reduces that statement to the compatibility of module sheafification with restriction to
a dense subsite. **That remaining step is not proved here.**

## Main results

* `Stacks.DenseSubsiteModules.ringPresheaf_restrict`: restricting a presheaf of commutative
  rings and then forgetting to rings is restricting the underlying presheaf of rings.
* `Stacks.DenseSubsiteModules.presheafRestrict_tensorObj`,
  `presheafRestrict_tensorRight_map`: the objectwise tensor product commutes with
  restriction, on objects and on morphisms.
* `Stacks.DenseSubsiteModules.presheafRestrict_comp_tensorRight`: the same as an equality of
  functors.
* `Stacks.DenseSubsiteModules.moduleRestriction_comp_forget`: restriction of *sheaves* of
  modules, followed by the forgetful functor to presheaves of modules, is the forgetful
  functor followed by restriction of presheaves of modules.

## Implementation notes

Every statement in this file is `rfl`, which is the point: restriction along `v` is
precomposition with `v.op`, so `(M ⊗ N)(v X)` and `M(v X) ⊗ N(v X)` are the same module over
the same ring, with the same restriction maps. The only friction is associativity of functor
composition — `v.op ⋙ (O ⋙ forget₂ CommRingCat RingCat)` against
`(v.op ⋙ O) ⋙ forget₂ CommRingCat RingCat` — which Lean's unifier will not perform while
solving for `?O` in `Stacks.ringPresheaf ?O`; `ringPresheaf_restrict` is stated so that the
spelling on the subsite is fixed before the tensor product is formed.

## References

* [Stacks Project, Tag 03DG](https://stacks.math.columbia.edu/tag/03DG), method (2)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
-/

@[expose] public section

open CategoryTheory Functor Opposite

universe w u₁ v₁ u₂ v₂

namespace Stacks.DenseSubsiteModules

variable {C : Type u₁} [Category.{v₁} C] {C' : Type u₂} [Category.{v₂} C']
  (v : C ⥤ C') (O : C'ᵒᵖ ⥤ CommRingCat.{w})

/-- Restricting a presheaf of commutative rings along `v` and then passing to rings is the same as
restricting the underlying presheaf of rings along `v`. -/
lemma ringPresheaf_restrict : v.op ⋙ Stacks.ringPresheaf O = Stacks.ringPresheaf (v.op ⋙ O) :=
  rfl

/-- Restriction of presheaves of modules along `v`, with the ring presheaf on the source site
spelled as a `Stacks.ringPresheaf`. -/
noncomputable abbrev presheafRestrict :
    PresheafOfModules.{w} (Stacks.ringPresheaf O) ⥤
      PresheafOfModules.{w} (Stacks.ringPresheaf (v.op ⋙ O)) :=
  PresheafOfModules.pushforward₀ v (Stacks.ringPresheaf O)

/-- The restriction along `v` of the objectwise tensor product `M ⊗ N` is the objectwise tensor
product of the restrictions of `M` and `N`. -/
lemma presheafRestrict_tensorObj (M N : PresheafOfModules.{w} (Stacks.ringPresheaf O)) :
    (presheafRestrict v O).obj (Stacks.tensorObj M N) =
      Stacks.tensorObj ((presheafRestrict v O).obj M) ((presheafRestrict v O).obj N) :=
  rfl

/-- The restriction along `v` of `f ⊗ N` is the tensor product of the restriction of `f` with the
restriction of `N`. -/
lemma presheafRestrict_tensorRight_map {M M' : PresheafOfModules.{w} (Stacks.ringPresheaf O)}
    (N : PresheafOfModules.{w} (Stacks.ringPresheaf O)) (f : M ⟶ M') :
    (presheafRestrict v O).map ((Stacks.tensorRight N).map f) =
      (Stacks.tensorRight ((presheafRestrict v O).obj N)).map ((presheafRestrict v O).map f) :=
  rfl

/-- Restriction along `v` followed by tensoring with the restriction of `N` equals tensoring with
`N` followed by restriction along `v`, as functors. -/
lemma presheafRestrict_comp_tensorRight (N : PresheafOfModules.{w} (Stacks.ringPresheaf O)) :
    presheafRestrict v O ⋙ Stacks.tensorRight ((presheafRestrict v O).obj N) =
      Stacks.tensorRight N ⋙ presheafRestrict v O :=
  rfl

variable (J : GrothendieckTopology C) (K : GrothendieckTopology C')

/-- Restriction of sheaves of modules along the continuous functor `v`, followed by the forgetful
functor to presheaves of modules, equals the forgetful functor followed by
`presheafRestrict v O.obj`. -/
lemma moduleRestriction_comp_forget [v.IsContinuous J K] (O : Sheaf K CommRingCat.{w})
    [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    SheafOfModules.pushforward (𝟙 ((v.sheafPushforwardContinuous RingCat.{w} J K).obj
        (Stacks.commRingSheafToRingSheaf O))) ⋙ SheafOfModules.forget.{w} _ =
      SheafOfModules.forget.{w} (Stacks.commRingSheafToRingSheaf O) ⋙
        presheafRestrict v O.obj :=
  rfl

end Stacks.DenseSubsiteModules
