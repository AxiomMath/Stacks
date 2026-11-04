module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentSquare
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentInverseImageComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentRestriction

/-!
# The naive cotangent complex along a continuous functor

Let `F : C₀ ⥤ C` be a continuous functor of sites, let `a : A ⟶ B` be a homomorphism of sheaves of
commutative rings on `C`, and write `F_*` for restriction along `F`, which carries sheaves on `C`
to sheaves on `C₀`.  This file constructs the canonical `F_*B`-linear chain map

`NL_{F_*B/F_*A} ⟶ F_* NL_{B/A}`

of complexes of sheaves of `F_*B`-modules on `C₀`.

The canonical presentation `A[B] ⟶ B` pushes forward to a presentation of `F_*B` over `F_*A`,
and the canonical presentation `(F_*A)[F_*B] ⟶ F_*B` maps to it: on coefficients by `F_*` of
the coefficient map and on the variable `[b]` by the variable `[b]` of `A[B]`.  Sections of the
two terms of `NL_{F_*B/F_*A}` over `U₀` come, locally, from sections of the conormal module and
of the module of differentials of the presentation at `U₀`; these are sent to the corresponding
sections of the presentation of `B` at `F(U₀)`, and from there into the terms of `NL_{B/A}` over
`F(U₀)`, which are the sections of `F_* NL_{B/A}` over `U₀`.  Since `F_*` of a sheaf is a sheaf,
the universal property of sheafification on `C₀` extends this to the whole terms.

## Main definitions

* `Stacks.SheafOfModules.pushforwardFreeAlgebraMap`: the morphism `(F_*A)[F_*B] ⟶ F_*(A[B])`.
* `Stacks.SheafOfModules.pushforwardRingSheafHom`: the identification of the underlying sheaf of
  rings of `F_*B` with the restriction along `F` of the underlying sheaf of rings of `B`, along
  which sheaves of `B`-modules are pushed forward to sheaves of `F_*B`-modules.
* `Stacks.SheafOfModules.pushforwardConormalMap` and
  `Stacks.SheafOfModules.conormalPushforwardTensorMap`: the maps on the two terms.
* `Stacks.SheafOfModules.naiveCotangentComplexPushforwardMap`: the chain map
  `NL_{F_*B/F_*A} ⟶ F_* NL_{B/A}`.

## Main results

* `Stacks.SheafOfModules.pushforwardFreeAlgebraMap_comp_canonicalPresentation`: the morphism of
  free algebras is compatible with the two presentations.
* `Stacks.SheafOfModules.pushforwardConormalMap_conormalClass` and
  `Stacks.SheafOfModules.conormalPushforwardTensorMap_tensorDifferential`: the maps on local
  sections.

## Implementation notes

The two sites may live in different universes.  Both complexes are therefore taken with their
sections in the join `max w u₀ v₀ u v z` of all of them: the complex on `C₀` at the free module
universe `max u v z`, the one on `C` at `max u₀ v₀ z`.

## References

* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX), functoriality of the
  naive cotangent complex, of which this is the version across a continuous functor.
* [Stacks Project, Tag 0D0X](https://stacks.math.columbia.edu/tag/0D0X), whose canonical map is
  the adjoint of the composite of this chain map with the one of Tag 08TX.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sites.Conormal Stacks.Sites.FreeAlgebra

universe v₀ u₀ v u w z

namespace Stacks.SheafOfModules

variable {C₀ : Type u₀} [Category.{v₀} C₀] {C : Type u} [Category.{v} C]
  (J₀ : GrothendieckTopology C₀) (J : GrothendieckTopology C) (F : C₀ ⥤ C)
  [F.IsContinuous J₀ J]

/-! ### The free algebras -/

section FreeAlgebra

variable [HasWeakSheafify J₀ CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{w}]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- **The morphism `(F_*A)[F_*B] ⟶ F_*(A[B])`** of sheaves of commutative rings on `C₀`: `F_*` of
the coefficient map of `A[B]` on coefficients, and the variable `[b]` of `A[B]` on the variable
`[b]`. -/
def pushforwardFreeAlgebraMap :
    freeAlgebraSheaf J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        (underlyingPresheaf J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)) ⟶
      (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) :=
  freeAlgebraSheafDesc J₀ _ _ _
    ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)))
    (Functor.whiskerLeft F.op (freeAlgebraSheafVariable J A (underlyingPresheaf J B)))

/-- On coefficients, `(F_*A)[F_*B] ⟶ F_*(A[B])` is `F_*` of the coefficient map of `A[B]`. -/
theorem freeAlgebraSheafCoefficientMap_comp_pushforwardFreeAlgebraMap :
    freeAlgebraSheafCoefficientMap J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        (underlyingPresheaf J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)) ≫
      pushforwardFreeAlgebraMap J₀ J F A B =
    (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)) :=
  freeAlgebraSheafCoefficientMap_comp_desc J₀ _ _ _ _ _

/-- **`(F_*A)[F_*B] ⟶ F_*(A[B])` is compatible with the canonical presentations** of `F_*B` and of
`B`. -/
theorem pushforwardFreeAlgebraMap_comp_canonicalPresentation :
    pushforwardFreeAlgebraMap J₀ J F A B ≫
        (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map (canonicalPresentation J A B a) =
      canonicalPresentation J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) := by
  refine freeAlgebraSheaf_hom_ext J₀ _ _ _ ?_ ?_
  · rw [← Category.assoc, freeAlgebraSheafCoefficientMap_comp_pushforwardFreeAlgebraMap,
      ← Functor.map_comp, canonicalPresentation_comp_coefficientMap,
      canonicalPresentation_comp_coefficientMap]
  · rw [freeAlgebraSheafVariable_comp_canonicalPresentation J₀, Functor.map_comp,
      Functor.whiskerRight_comp, ← Category.assoc]
    refine (congrArg (· ≫ Functor.whiskerRight ((sheafToPresheaf J₀ CommRingCat.{w}).map
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map (canonicalPresentation J A B a)))
      (forget CommRingCat.{w})) (freeAlgebraSheafVariable_comp_desc J₀ _ _ _
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)))
        (Functor.whiskerLeft F.op
          (freeAlgebraSheafVariable J A (underlyingPresheaf J B))))).trans ?_
    ext U x
    exact congrArg (fun t : underlyingPresheaf J B ⟶ underlyingPresheaf J B ↦
      t.app (F.op.obj U) x) (freeAlgebraSheafVariable_comp_canonicalPresentation J A B a)

end FreeAlgebra

/-! ### The maps on the two terms -/

section Terms

variable [HasWeakSheafify J₀ CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{w}]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- **The underlying sheaf of rings of `F_*B` is the restriction along `F` of that of `B`**; the
identity, along which sheaves of `B`-modules are pushed forward to sheaves of `F_*B`-modules. -/
abbrev pushforwardRingSheafHom :
    Stacks.SheafOfModules.Tensor.ringSheaf
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B) ⟶
      (F.sheafPushforwardContinuous RingCat.{w} J₀ J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  𝟙 _

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The square of presheaves of commutative rings on `C₀` relating the two presentations. -/
theorem pushforwardPresentationSquare :
    (pushforwardFreeAlgebraMap J₀ J F A B).hom ≫
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map
          (canonicalPresentation J A B a)).hom =
      (canonicalPresentation J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
          ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).hom ≫ 𝟙 _ := by
  rw [Category.comp_id]
  exact hom_of_comp_eq (pushforwardFreeAlgebraMap_comp_canonicalPresentation J₀ J F A B a)

/-- The pushforward of the canonical presentation is surjective on sections, hence locally
surjective. -/
instance isLocallySurjective_pushforward_canonicalPresentation :
    Presheaf.IsLocallySurjective J₀
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map
        (canonicalPresentation J A B a)).hom := by
  refine Presheaf.isLocallySurjective_of_surjective _ _ fun U b ↦ ?_
  refine ⟨((freeAlgebraSheafVariable J A (underlyingPresheaf J B)).app (F.op.obj U) b), ?_⟩
  exact congrArg (fun t : underlyingPresheaf J B ⟶ underlyingPresheaf J B ↦
    t.app (F.op.obj U) b) (freeAlgebraSheafVariable_comp_canonicalPresentation J A B a)

/-- The canonical presentation `A[B] ⟶ B` of a map of sheaves of commutative rings on `C₀` is
locally surjective. -/
instance isLocallySurjective_canonicalPresentation₀
    (A B : Sheaf J₀ CommRingCat.{w}) (a : A ⟶ B) :
    Presheaf.IsLocallySurjective J₀ (canonicalPresentation J₀ A B a).hom :=
  canonicalPresentation_isLocallySurjective J₀ A B a

/-- **The map `I₀/I₀² ⟶ F_*(I/I²)` on the degree `-1` terms**, linear over `F_*B`: the class of a
section `f` of the kernel `I₀` of `(F_*A)[F_*B] ⟶ F_*B` over `U₀` goes to the class of its image
in the kernel `I` of `A[B] ⟶ B` over `F(U₀)`. -/
def pushforwardConormalMap :
    (canonicalConormalSequence.{v₀, u₀, w, max u v z} J₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).X₁ ⟶
      (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingSheafHom J₀ J F B)).obj
        (canonicalConormalSequence.{v, u, w, max u₀ v₀ z} J A B a).X₁ := by
  refine sheafifyLiftDesc.{v₀, u₀, w, max u v z} J₀ _ _
    (canonicalPresentation J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a))
    (conormalPresheaf (canonicalPresentation J₀ _ _
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).hom) _
    (fun X c ↦ toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
      (conormalPresheaf (canonicalPresentation J A B a).hom) (F.op.obj X)
      (conormalMapOfSquare _ _ _ _ (pushforwardPresentationSquare J₀ J F A B a) X c)) ?_ ?_ ?_
  · intro X c c'
    exact (congrArg (toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B
        (canonicalPresentation J A B a) (conormalPresheaf (canonicalPresentation J A B a).hom)
        (F.op.obj X))
      (map_add (conormalMapOfSquare _ _ _ _
        (pushforwardPresentationSquare J₀ J F A B a) X) c c')).trans
      (toAssociatedModule_add.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
        (conormalPresheaf (canonicalPresentation J A B a).hom) (F.op.obj X) _ _)
  · intro X r c
    refine (congrArg (toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B
        (canonicalPresentation J A B a) (conormalPresheaf (canonicalPresentation J A B a).hom)
        (F.op.obj X))
      (map_smulₛₗ (conormalMapOfSquare _ _ _ _
        (pushforwardPresentationSquare J₀ J F A B a) X) r c)).trans ?_
    refine (toAssociatedModule_smul.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
        (conormalPresheaf (canonicalPresentation J A B a).hom) (F.op.obj X) _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj (F.op.obj X) ↦
      s • toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
        (conormalPresheaf (canonicalPresentation J A B a).hom) (F.op.obj X)
        (conormalMapOfSquare _ _ _ _ (pushforwardPresentationSquare J₀ J F A B a) X c))
      (quotientToTarget_quotientMapOfSquare _ _ _ _
        (pushforwardPresentationSquare J₀ J F A B a) X r)
  · intro X Y f c
    exact (congrArg (toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B
        (canonicalPresentation J A B a) (conormalPresheaf (canonicalPresentation J A B a).hom)
        (F.op.obj Y))
      (conormalMapOfSquare_naturality _ _ _ _
        (pushforwardPresentationSquare J₀ J F A B a) f c)).trans
      (toAssociatedModule_map.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
        (conormalPresheaf (canonicalPresentation J A B a).hom) (F.op.map f) _)

omit [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The square of coefficient rings on `C₀` relating the two presentations. -/
theorem pushforwardCoefficientSquare :
    𝟙 ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A).obj ≫
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))).hom =
      (freeAlgebraSheafCoefficientMap J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
          (underlyingPresheaf J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B))).hom ≫
        (pushforwardFreeAlgebraMap J₀ J F A B).hom := by
  rw [Category.id_comp]
  exact (hom_of_comp_eq
    (freeAlgebraSheafCoefficientMap_comp_pushforwardFreeAlgebraMap J₀ J F A B)).symm

/-- **The map `F_*B ⊗_{(F_*A)[F_*B]} Ω ⟶ F_*(B ⊗_{A[B]} Ω)` on the degree `0` terms**, linear over
`F_*B`: `b ⊗ d f` over `U₀` goes to `b ⊗ d f'` over `F(U₀)`, where `f'` is the image of `f` in
`A[B]`. -/
def conormalPushforwardTensorMap :
    (canonicalConormalSequence.{v₀, u₀, w, max u v z} J₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).X₂ ⟶
      (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingSheafHom J₀ J F B)).obj
        (canonicalConormalSequence.{v, u, w, max u₀ v₀ z} J A B a).X₂ := by
  refine sheafifyLiftDesc.{v₀, u₀, w, max u v z} J₀ _ _
    (canonicalPresentation J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a))
    (tensorPresheaf (canonicalPresentation J₀ _ _
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).hom
      (freeAlgebraSheafCoefficientMap J₀ _ _).hom) _
    (fun X t ↦ toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
      (tensorPresheaf (canonicalPresentation J A B a).hom
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom) (F.op.obj X)
      (tensorMapOfSquareₛₗ _ _ _ _ (pushforwardPresentationSquare J₀ J F A B a) _ _ _
        (pushforwardCoefficientSquare J₀ J F A B) X t)) ?_ ?_ ?_
  · intro X t t'
    exact (congrArg (toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B
        (canonicalPresentation J A B a) (tensorPresheaf (canonicalPresentation J A B a).hom
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom) (F.op.obj X))
      (map_add (tensorMapOfSquareₛₗ _ _ _ _ (pushforwardPresentationSquare J₀ J F A B a) _ _ _
        (pushforwardCoefficientSquare J₀ J F A B) X) t t')).trans
      (toAssociatedModule_add.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
        (tensorPresheaf (canonicalPresentation J A B a).hom
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom) (F.op.obj X) _ _)
  · intro X r t
    refine (congrArg (toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B
        (canonicalPresentation J A B a) (tensorPresheaf (canonicalPresentation J A B a).hom
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom) (F.op.obj X))
      (tensorMapOfSquareₛₗ_smul _ _ _ _ (pushforwardPresentationSquare J₀ J F A B a) _ _ _
        (pushforwardCoefficientSquare J₀ J F A B) X r t)).trans ?_
    refine (toAssociatedModule_smul.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
        (tensorPresheaf (canonicalPresentation J A B a).hom
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom)
        (F.op.obj X) _ _).trans ?_
    exact congrArg (fun s : (Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj (F.op.obj X) ↦
      s • toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
        (tensorPresheaf (canonicalPresentation J A B a).hom
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom) (F.op.obj X)
        (tensorMapOfSquareₛₗ _ _ _ _ (pushforwardPresentationSquare J₀ J F A B a) _ _ _
          (pushforwardCoefficientSquare J₀ J F A B) X t))
      (quotientToTarget_quotientMapOfSquare _ _ _ _
        (pushforwardPresentationSquare J₀ J F A B a) X r)
  · intro X Y f t
    exact (congrArg (toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B
        (canonicalPresentation J A B a) (tensorPresheaf (canonicalPresentation J A B a).hom
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom) (F.op.obj Y))
      (tensorMapOfSquareₛₗ_naturality _ _ _ _ (pushforwardPresentationSquare J₀ J F A B a) _ _ _
        (pushforwardCoefficientSquare J₀ J F A B) f t)).trans
      (toAssociatedModule_map.{v, u, w, max u₀ v₀ z} J _ B (canonicalPresentation J A B a)
        (tensorPresheaf (canonicalPresentation J A B a).hom
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom) (F.op.map f) _)

/-- On the class of a local section `f` of the kernel, the degree `-1` map is the class of the
image of `f` in `A[B]`. -/
theorem pushforwardConormalMap_conormalClass (X : C₀ᵒᵖ)
    (x : kernelIdeal (canonicalPresentation J₀
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).hom X) :
    ((pushforwardConormalMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).val.app X)
        (conormalClass.{v₀, u₀, w, max u v z} J₀ _ _ _
          (freeAlgebraSheafCoefficientMap J₀ _ _) _ X x) =
      conormalClass.{v, u, w, max u₀ v₀ z} J A _ B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a) (F.op.obj X)
        ⟨(pushforwardFreeAlgebraMap J₀ J F A B).hom.app X x,
          kernelIdeal_le_comap_square _ _ _ _ (pushforwardPresentationSquare J₀ J F A B a) X
            x.2⟩ := by
  apply sheafifyLiftDesc_toAssociatedModule.{v₀, u₀, w, max u v z}

/-- On `1 ⊗ d f`, the degree `0` map is `1 ⊗ d f'` for the image `f'` of `f` in `A[B]`. -/
theorem conormalPushforwardTensorMap_tensorDifferential (X : C₀ᵒᵖ)
    (x : (freeAlgebraSheaf J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
      (underlyingPresheaf J₀ ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B))).obj.obj
        X) :
    ((conormalPushforwardTensorMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).val.app X)
        (tensorDifferential.{v₀, u₀, w, max u v z} J₀ _ _ _
          (freeAlgebraSheafCoefficientMap J₀ _ _) _ X x) =
      tensorDifferential.{v, u, w, max u₀ v₀ z} J A _ B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (canonicalPresentation J A B a) (F.op.obj X)
        ((pushforwardFreeAlgebraMap J₀ J F A B).hom.app X x) := by
  refine (sheafifyLiftDesc_toAssociatedModule.{v₀, u₀, w, max u v z} J₀ _ _ _ _ _ _ _ _ _
    X _).trans ?_
  refine congrArg (toAssociatedModule.{v, u, w, max u₀ v₀ z} J _ B
    (canonicalPresentation J A B a) (tensorPresheaf (canonicalPresentation J A B a).hom
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom) (F.op.obj X)) ?_
  refine (TensorProduct.map_tmul _ _ _ _).trans ?_
  exact congrArg₂ (fun (b : (freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj (F.op.obj X) ⧸
        kernelIdeal (canonicalPresentation J A B a).hom (F.op.obj X)) (ω : (differentialsPresheaf
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom).obj (F.op.obj X)) ↦
      b ⊗ₜ[(freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj (F.op.obj X)] ω)
    (map_one (quotientMapOfSquare _ _ _ _ (pushforwardPresentationSquare J₀ J F A B a) X).hom)
    (differentialsMapOfSquare_d _ _ _ _ (pushforwardCoefficientSquare J₀ J F A B) X x)

/-- **The maps on the two terms commute with the differentials** `I₀/I₀² ⟶ F_*B ⊗ Ω` and
`F_*(I/I² ⟶ B ⊗ Ω)`. -/
theorem pushforwardConormalMap_comm :
    (canonicalConormalSequence.{v₀, u₀, w, max u v z} J₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)).f ≫
        conormalPushforwardTensorMap.{v₀, u₀, v, u, w, z} J₀ J F A B a =
      pushforwardConormalMap.{v₀, u₀, v, u, w, z} J₀ J F A B a ≫
        (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingSheafHom J₀ J F B)).map
          (canonicalConormalSequence.{v, u, w, max u₀ v₀ z} J A B a).f := by
  apply sheafify_hom_ext.{v₀, u₀, w, max u v z} J₀ _ _ _ (conormalPresheaf _)
  intro X c
  obtain ⟨c, rfl⟩ := (kernelIdeal _ X).toCotangent_surjective c
  refine Eq.trans
    (congrArg ((conormalPushforwardTensorMap.{v₀, u₀, v, u, w, z} J₀ J F A B a).val.app X)
      (conormalSequence_f_class.{v₀, u₀, w, max u v z} J₀ _ _ _ _ _ X c)) ?_
  refine Eq.trans
    (conormalPushforwardTensorMap_tensorDifferential.{v₀, u₀, v, u, w, z} J₀ J F A B a X c) ?_
  refine Eq.symm (Eq.trans (congrArg
    ((canonicalConormalSequence.{v, u, w, max u₀ v₀ z} J A B a).f.val.app (F.op.obj X))
    (pushforwardConormalMap_conormalClass.{v₀, u₀, v, u, w, z} J₀ J F A B a X c)) ?_)
  exact conormalSequence_f_class.{v, u, w, max u₀ v₀ z} J _ _ _ _ _ (F.op.obj X) _

end Terms

/-! ### The chain map -/

section ComplexMap

variable [HasWeakSheafify J₀ CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{w}]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B)

/-- **The canonical chain map `NL_{F_*B/F_*A} ⟶ F_* NL_{B/A}`** of complexes of sheaves of
`F_*B`-modules on `C₀`, for a continuous functor `F : C₀ ⥤ C` and a homomorphism `a : A ⟶ B` of
sheaves of commutative rings on `C`: `pushforwardConormalMap` in degree `-1` and
`conormalPushforwardTensorMap` in degree `0`. -/
def naiveCotangentComplexPushforwardMap :
    naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) ⟶
      ((_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingSheafHom J₀ J F B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a) := by
  have : HasZeroObject (_root_.SheafOfModules.{max w u₀ v₀ u v z}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B))) :=
    hasZeroObject_of_hasTerminal_object
  refine HomologicalComplex.mkHomFromDouble
    (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide) (by decide)
    (pushforwardConormalMap.{v₀, u₀, v, u, w, z} J₀ J F A B a ≫
      (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
        (pushforwardRingSheafHom J₀ J F B)).map
        (eqToHom (naiveCotangentComplex_X_negOne.{v, u, w, max u₀ v₀ z} J A B a).symm))
    (conormalPushforwardTensorMap.{v₀, u₀, v, u, w, z} J₀ J F A B a ≫
      (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
        (pushforwardRingSheafHom J₀ J F B)).map
        (eqToHom (naiveCotangentComplex_X_zero.{v, u, w, max u₀ v₀ z} J A B a).symm)) ?_ ?_
  · change _ ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
        (pushforwardRingSheafHom J₀ J F B)).map
          ((naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a).d (-1) 0) = _
    rw [naiveCotangentComplex_d_negOne_zero, Category.assoc, ← Functor.map_comp,
      ← Category.assoc (eqToHom _), eqToHom_trans, eqToHom_refl, Category.id_comp,
      Functor.map_comp, ← Category.assoc, ← pushforwardConormalMap_comm, Category.assoc]
  · intro k _
    change _ ≫ (_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
        (pushforwardRingSheafHom J₀ J F B)).map
          ((naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a).d 0 k) = _
    have hz : (naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a).d 0 k = 0 := by
      have : HasZeroObject (_root_.SheafOfModules.{max w u v (max u₀ v₀ z)}
          (Stacks.SheafOfModules.Tensor.ringSheaf B)) := hasZeroObject_of_hasTerminal_object
      change (HomologicalComplex.double
        (canonicalConormalSequence.{v, u, w, max u₀ v₀ z} J A B a).f
        (show (ComplexShape.up ℤ).Rel (-1) 0 from by decide)).d 0 k = 0
      exact HomologicalComplex.double_d_eq_zero₀ _ _ 0 k (by decide)
    rw [hz, Functor.map_zero, Limits.comp_zero]

end ComplexMap

/-! ### Along a square -/

section Square

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable [HasWeakSheafify J₀ CommRingCat.{w}] [HasWeakSheafify J CommRingCat.{w}]
  [J₀.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (A₀ B₀ : Sheaf J₀ CommRingCat.{w}) (a₀ : A₀ ⟶ B₀)
  (ψ : A₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj A)
  (β : B₀ ⟶ (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).obj B)
  (hsq : a₀ ≫ β = ψ ≫ (F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a)

/-- A morphism `β : B₀ ⟶ F_*B` of sheaves of commutative rings, read as a morphism of the
underlying sheaves of rings `B₀ ⟶ F_*B`; this is the ring map along which sheaves of `B`-modules
are pushed forward to sheaves of `B₀`-modules. -/
abbrev pushforwardRingHomOfSquare :
    Stacks.SheafOfModules.Tensor.ringSheaf B₀ ⟶
      (F.sheafPushforwardContinuous RingCat.{w} J₀ J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf B) :=
  ObjectProperty.homMk (Functor.whiskerRight β.hom (forget₂ CommRingCat.{w} RingCat.{w}))

/-- Pushing forward along `F_*B = F_*B` and then restricting scalars along `β` is pushing forward
along `β`, degreewise the identity. -/
def pushforwardRestrictScalarsComplexIso
    (K : CochainComplex (_root_.SheafOfModules.{max w u₀ v₀ u v z}
      (Stacks.SheafOfModules.Tensor.ringSheaf B)) ℤ) :
    ((_root_.SheafOfModules.restrictScalars.{max w u₀ v₀ u v z}
        (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (((_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingSheafHom J₀ J F B)).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      ((_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingHomOfSquare J₀ J F B B₀ β)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) (fun _ _ _ ↦ rfl)

include hsq in
/-- **The canonical chain map `NL_{B₀/A₀} ⟶ F_* NL_{B/A}` attached to a commutative square**
`a₀ ≫ β = ψ ≫ F_*a` of sheaves of commutative rings on `C₀`, with `ψ : A₀ ⟶ F_*A` and
`β : B₀ ⟶ F_*B`: the chain map of Stacks 08TX of the square into `NL_{F_*B/F_*A}`, followed by
`Stacks.SheafOfModules.naiveCotangentComplexPushforwardMap`.  The target is read over `B₀` by
pushing forward along `β`. -/
def naiveCotangentComplexPushforwardSquareMap :
    naiveCotangentComplex.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ ⟶
      ((_root_.SheafOfModules.pushforward.{max w u₀ v₀ u v z}
          (pushforwardRingHomOfSquare J₀ J F B B₀ β)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (naiveCotangentComplex.{v, u, w, max u₀ v₀ z} J A B a) :=
  naiveCotangentComplexMapOfSquare.{v₀, u₀, w, max u v z} J₀ A₀ B₀ a₀ _ _
      ((F.sheafPushforwardContinuous CommRingCat.{w} J₀ J).map a) ψ β hsq ≫
    ((_root_.SheafOfModules.restrictScalars.{max w u₀ v₀ u v z}
        (underlyingRingHomOfSite β)).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (naiveCotangentComplexPushforwardMap.{v₀, u₀, v, u, w, z} J₀ J F A B a) ≫
    (pushforwardRestrictScalarsComplexIso.{v₀, u₀, v, u, w, z} J₀ J F B B₀ β _).hom

end Square

end Stacks.SheafOfModules

end
