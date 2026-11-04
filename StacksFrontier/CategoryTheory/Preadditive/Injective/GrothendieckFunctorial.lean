module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Preadditive.Injective.InjectiveObject
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Basic

import StacksCore.Tactic.StacksAttribute

/-!
# Grothendieck abelian categories have functorial injective embeddings

A Grothendieck abelian category has functorial injective embeddings in the sense of
[Stacks, Tag 0139]: there is an endofunctor `J` with injective values and a natural
monomorphism `𝟭 ⟶ J`.

## Main definitions

* `Stacks.Injectives.FunctorialEmbedding.embedding` is the endofunctor `J : C ⥤ C`.
* `Stacks.Injectives.FunctorialEmbedding.unit` is the natural monomorphism `𝟭 C ⟶ J`.
* `Stacks.Injectives.FunctorialEmbedding.injectiveEmbedding` is the same datum with `J` landing in
  `InjectiveObject C`, the shape in which [Stacks, Tag 0141] consumes it.

## Main results

* `Stacks.Injectives.FunctorialEmbedding.hasFunctorialInjectiveEmbeddings`: a Grothendieck abelian
  category
  satisfies `HasFunctorialInjectiveEmbeddings`.

## Implementation notes

Mathlib's proof that a Grothendieck abelian category has enough injectives
(`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`) is *already functorial*,
although it is not recorded as such.  It proceeds by the small object argument applied
to the inclusions of subobjects of a separator, and the small object argument is
packaged in Mathlib as `HasFunctorialFactorization`, whose underlying datum
`FunctorialFactorizationData` has as its first two fields a functor `Z : Arrow C ⥤ C`
and a *natural* transformation `i : Arrow.leftFunc ⟶ Z`.  The transfinite choices made
along the way (`IsGrothendieckAbelian.generatingMonomorphisms.largerSubobject` uses
`Exists.choose`) are confined to the proofs of the *propositions*
`generatingMonomorphisms_rlp`, `HasSmallObjectArgument` and `llp_rlp_monomorphisms`;
the data itself is choice-free apart from the single global `Nonempty.some` picking one
functorial factorization once and for all.

So the only thing missing is the functor `C ⥤ Arrow C` sending `X` to the arrow
`X ⟶ 0`, which Mathlib does not have (it has the opposite one,
`CategoryTheory.RightFreyd.rightFunctor`).  Precomposing the factorization functor with
it gives `J`, injectivity of the values is Mathlib's instance for
`monoMapFactorizationDataRlp (0 : X ⟶ 0)`, and the natural monomorphism is `i`
whiskered along it.

The injectivity instance is invoked by name rather than by `infer_instance`: nested
instance search for it exhausts the default heartbeat budget.

## References

* [Stacks Project, Tag 0139](https://stacks.math.columbia.edu/tag/0139)
* [Stacks Project, Tag 079H](https://stacks.math.columbia.edu/tag/079H)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open scoped ZeroObject

universe w v u

namespace Stacks.Injectives.FunctorialEmbedding

variable (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/-- The functor sending an object `X` to the arrow `X ⟶ 0`.  Feeding it to a functorial
factorization of monomorphisms turns the factorization into an endofunctor of `C`. -/
noncomputable def zeroArrowFunctor : C ⥤ Arrow C where
  obj X := Arrow.mk (0 : X ⟶ (0 : C))
  map f := Arrow.homMk f (𝟙 (0 : C)) (by simp)
  map_id _ := by ext <;> simp
  map_comp _ _ := by ext <;> simp

/-- Mathlib's chosen functorial factorization of a morphism in a Grothendieck abelian
category as a monomorphism followed by a morphism with the right lifting property
against all monomorphisms. -/
noncomputable abbrev factorizationData :
    FunctorialFactorizationData (monomorphisms C) (monomorphisms C).rlp :=
  functorialFactorizationData _ _

/-- The functorial injective embedding of [Stacks, Tag 0139]: an endofunctor of `C` whose
values are injective objects. -/
noncomputable def embedding : C ⥤ C := zeroArrowFunctor C ⋙ (factorizationData C).Z

/-- The values of `Stacks.Injectives.FunctorialEmbedding.embedding` are injective objects. -/
theorem injective_embedding_obj (X : C) : Injective ((embedding C).obj X) :=
  IsGrothendieckAbelian.instInjectiveZMonomorphismsRlpMonoMapFactorizationDataRlpOfNatHom
    (C := C) (X := X)

/-- The natural embedding of the identity functor into
  `Stacks.Injectives.FunctorialEmbedding.embedding`. -/
noncomputable def unit : 𝟭 C ⟶ embedding C where
  app X := (factorizationData C).i.app (Arrow.mk (0 : X ⟶ (0 : C)))
  naturality _ _ f := (factorizationData C).i.naturality ((zeroArrowFunctor C).map f)

/-- `Stacks.Injectives.FunctorialEmbedding.unit` is a monomorphism at every object. -/
theorem mono_unit_app (X : C) : Mono ((unit C).app X) := (factorizationData C).hi _

/-- **Stacks Project, Tag 079H.** A Grothendieck abelian category has functorial injective
embeddings in the sense of [Stacks, Tag 0139]. -/
@[stacks 079H "functorial form; Mathlib's enoughInjectives has the non-functorial half",
  sga "4 V 0.1.1" "enough injectives"]
theorem hasFunctorialInjectiveEmbeddings : HasFunctorialInjectiveEmbeddings C :=
  ⟨{ obj X := Arrow.mk ((unit C).app X)
     map f := Arrow.homMk f ((embedding C).map f) ((unit C).naturality f) },
    rfl, mono_unit_app C, injective_embedding_obj C⟩

/-- `Stacks.Injectives.FunctorialEmbedding.embedding` with its values regarded as objects of
  `InjectiveObject C`.
This is the shape in which [Stacks, Tag 0141] consumes the datum. -/
noncomputable def injectiveEmbedding : C ⥤ InjectiveObject C :=
  ObjectProperty.lift _ (embedding C) (injective_embedding_obj C)

/-- The natural embedding of the identity functor into
  `Stacks.Injectives.FunctorialEmbedding.injectiveEmbedding`,
read in `C` through the inclusion of the injective objects. -/
noncomputable def injectiveEmbeddingUnit :
    𝟭 C ⟶ injectiveEmbedding C ⋙ InjectiveObject.ι C :=
  unit C

/-- `Stacks.Injectives.FunctorialEmbedding.injectiveEmbeddingUnit` is a monomorphism at every
  object. -/
theorem mono_injectiveEmbeddingUnit_app (X : C) :
    Mono ((injectiveEmbeddingUnit C).app X) := mono_unit_app C X

end Stacks.Injectives.FunctorialEmbedding
