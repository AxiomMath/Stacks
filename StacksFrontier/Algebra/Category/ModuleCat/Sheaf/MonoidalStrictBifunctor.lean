module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorEncodings

/-!
# The structural morphisms of the strict monoidal structure are the maps of the 0GMW bifunctor

`Stacks.SheafOfModules.Strict.monoidalCategory` is the monoidal structure on sheaves of
`𝒪`-modules whose tensor product is the tensor product sheaf of Tag 01CA on the nose, and
`Stacks.SheafOfModules.Tensor.sheafTensor` is that same tensor product read as a
bifunctor, the spelling Tag 0GMW and the comparison of Tag 03EL are stated in. The two agree on
objects by `rfl` (`Stacks.SheafOfModules.TensorEncodings.tensorSheafBifunctor_obj_eq_tensorSheaf`).
This file records that they agree on *morphisms* too: the tensor product of two morphisms and
each of the two whiskerings of the strict structure are the action of the bifunctor on the
corresponding pair.

The reason this is wanted separately from
`Stacks.SheafOfModules.Strict.tensorHom_eq_sheafifyMap`, which is the same fact with the target
spelled as a sheafification, is that a naturality square of a natural transformation *of the
bifunctor* — `Stacks.SheafOfModules.pullbackTensorIso` is the motivating example — comes out
phrased by the native component and inner maps, and a monoidal coherence is phrased by `◁` and `▷`.
These three lemmas are what turn one into the other.

## Main results

* `Stacks.SheafOfModules.Strict.tensorHom_eq_tensorSheafBifunctor_map`: `a ⊗ₘ b` is the action of
  the 0GMW bifunctor on `(a, b)`.
* `Stacks.SheafOfModules.Strict.whiskerLeft_eq_tensorSheafBifunctor_map` and
  `Stacks.SheafOfModules.Strict.whiskerRight_eq_tensorSheafBifunctor_map`: the two whiskerings are
  its action on `(𝟙, b)` and on `(a, 𝟙)`.

## Implementation notes

The strict structure is indexed by a presheaf of commutative rings together with a sheaf
condition, and the bifunctor by a sheaf of commutative rings; the statements here are written at
the second, with the first supplied by
`Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf`, and the defeq check of
`:=` crosses the boundary once per lemma. This is the discipline of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsMonoidal`: the two sheaves of rings
are equal by proof irrelevance but not syntactically, so a statement is declared at one spelling
and never left to instance search at the other.

The monoidal structure is named by a `@[instance_reducible] local instance` rather than by
`@`-application, because the three statements are about the notation `⊗ₘ`, `◁` and `▷`; it is not
exported, for the reason `Strict.monoidalCategory` is not an instance.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry

universe w v u

namespace Stacks.SheafOfModules.Strict

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  (O : Sheaf J CommRingCat.{w})

/-- The strict monoidal structure of Tag 01CA on sheaves of `O`-modules, named at the spelling
`Stacks.SheafOfModules.Tensor.ringSheaf` of the sheaf of rings so that the
notation `⊗ₘ`, `◁` and `▷` below refers to it. Deliberately **not** an instance, for the reason
`Stacks.SheafOfModules.Strict.monoidalCategory` is not one: sheaves of modules also carry the
localized structure of `Stacks.SheafOfModules.monoidalCategory`, and a client which wants this
one says so with `attribute [local instance]`. -/
@[instance_reducible]
def monoidalUnderlyingRingSheaf :
    MonoidalCategory (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  monoidalCategory O.obj (TensorEncodings.isSheaf_structureRingPresheaf O)

/-- The braiding of the strict monoidal structure of Tag 01CA on sheaves of `O`-modules, named at
the spelling `AlgebraicGeometry.SheafOfModules.underlyingRingSheafOfSite` of the sheaf of rings so
that the notation `β_` refers to it. Deliberately **not** an instance, for the reason
`Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf` is not one: a client which wants this
braiding says so with `attribute [local instance]`, having activated the monoidal structure the
same way. -/
@[instance_reducible]
def braidedUnderlyingRingSheaf :
    letI := monoidalUnderlyingRingSheaf O
    BraidedCategory (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  braidedCategory O.obj (TensorEncodings.isSheaf_structureRingPresheaf O)

attribute [local instance] monoidalUnderlyingRingSheaf

variable {F F' G G' : _root_.SheafOfModules.{w}
  (Stacks.SheafOfModules.Tensor.ringSheaf O)}

/-- **The tensor product of two morphisms in the strict monoidal structure is the action of the
tensor bifunctor of Tag 0GMW on the pair.** -/
theorem tensorHom_eq_tensorSheafBifunctor_map (a : F ⟶ F') (b : G ⟶ G') :
    a ⊗ₘ b =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map a).app G ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj F').map b :=
  (tensorHom_eq_sheafifyMap O.obj (TensorEncodings.isSheaf_structureRingPresheaf O) a b).trans
    (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map O a b).symm

/-- **Left whiskering in the strict monoidal structure is the action of the tensor bifunctor of
Tag 0GMW on `(𝟙, b)`.** -/
theorem whiskerLeft_eq_tensorSheafBifunctor_map (F : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) (b : G ⟶ G') :
    F ◁ b =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map (𝟙 F)).app G ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj F).map b :=
  (MonoidalCategory.id_tensorHom F b).symm.trans
    (tensorHom_eq_tensorSheafBifunctor_map O (𝟙 F) b)

/-- **Right whiskering in the strict monoidal structure is the action of the tensor bifunctor of
Tag 0GMW on `(a, 𝟙)`.** -/
theorem whiskerRight_eq_tensorSheafBifunctor_map (a : F ⟶ F')
    (G : _root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    a ▷ G =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).map a).app G ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj F').map (𝟙 G) :=
  (MonoidalCategory.tensorHom_id a G).symm.trans
    (tensorHom_eq_tensorSheafBifunctor_map O a (𝟙 G))

end Stacks.SheafOfModules.Strict

end
