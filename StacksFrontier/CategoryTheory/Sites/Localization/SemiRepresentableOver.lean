module

public import StacksFrontier.CategoryTheory.Limits.FormalCoproductLimits
public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRepresentable
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable

/-!
# Limits and colimits of semi-representable objects over a base

Let `C` be a category and let `X` be an object of `C`. The Stacks Project's category `SR(C, X)` of
*semi-representable objects over `X`* is the category `SR(C/X)` of semi-representable objects of
the slice `C/X`, that is, Mathlib's `CategoryTheory.Limits.FormalCoproduct (Over X)`, and the
functor `F : SR(C, X) ⥤ PSh(C)/h_X` sends a family `{U_i → X}` to the coproduct `∐ h_{U_i}` with
its structural map to `h_X`.

This file constructs that `F` and proves the two clauses of Tag 01G2 concerning `SR(C, X)`: it has
coproducts and `F` commutes with them, and `F` commutes with limits, in particular with the finite
limits that `SR(C, X)` has when `C` has fibre products.

## Main definitions

* `CategoryTheory.Limits.FormalCoproduct.yonedaOver`: the functor `F : SR(C, X) ⥤ PSh(C)/h_X`.

## Main results

* `CategoryTheory.Limits.FormalCoproduct.yonedaOverObjIso`: **Stacks Project, Tag 01G2** — the
  value of `F` on a family, namely `F({U_i → X}) = (∐ h_{U_i} → h_X)`, so that the two clauses
  below really are statements about the source's `F`.
* `CategoryTheory.Limits.FormalCoproduct.hasCoproducts_formalCoproductOver` and
  `CategoryTheory.Limits.FormalCoproduct.preservesColimitsOfShape_yonedaOver`: **Stacks Project,
  Tag 01G2** — `SR(C, X)` has coproducts and `F` commutes with them.
* `CategoryTheory.Limits.FormalCoproduct.preservesLimitsOfSize_yonedaOver`: **Stacks Project, Tag
  01G2** — `F : SR(C, X) ⥤ PSh(C)/h_X` commutes with limits of every shape, in particular with
  finite limits. That `SR(C, X)` does have finite limits when `C` has fibre products is
  `Stacks.CategoryTheory.Hypercovering.hasFiniteLimits_formalCoproductOver`.

## Implementation notes

`F` is built exactly as the source builds it: apply the results for `SR(D)` to the category
`D = C/X`, and use the identification `PSh(C/X) = PSh(C)/h_X`. The latter is the presheaf level
form of Tag 00Y1, available as `CategoryTheory.OverShriek.presheafEquivalence`, whose functor is
the presheaf level `j_{X!}`; so `F` is `FormalCoproduct.yoneda` for `C/X` followed by that
equivalence. On `{U_i → X}` the composite is
`V ↦ ∐_{φ : V ⟶ X} ∐_i {g : V ⟶ U_i | a_i ∘ g = φ} = ∐_i Hom_C(V, U_i)`, the coproduct of the
representables, with the map to `h_X` remembering `φ`; `yonedaOver_comp_forget` records the first
of those two equalities, the second being the definition of `j_{X!}`.

Both clauses then come for free: an equivalence preserves all limits and all colimits, and
`FormalCoproduct.yoneda` for `C/X` preserves coproducts and limits by
`StacksFrontier.CategoryTheory.Limits.FormalCoproductLimits`. Preservation of limits by `F` needs no
hypothesis on `C` whatsoever, and is proved for limits of arbitrary shape, which is stronger than
the finite limits the source's clause asks for.

Universes. `SR(C, X)` has coproducts for an index universe `w` unrelated to the universes `u`, `v`
of `C`, as for `SR(C)`. The functor `F` is different: `PSh(C)/h_X` is the slice of `v`-valued
presheaves on `C`, and `C/X` has `v`-valued homs, so `F` is defined on `FormalCoproduct.{v}`.

## References

* [Stacks Project, Tag 01G2](https://stacks.math.columbia.edu/tag/01G2)
-/

@[expose] public section

universe w' w v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.OverShriek

variable {C : Type u} [Category.{v} C] {X : C}

/-- A morphism `(V, φ) ⟶ B` of `C/X` is the same thing as a morphism `g : V ⟶ B.left` of `C` with
`g ∘ b = φ`, where `b` is the structure morphism of `B`. -/
def overHomEquivSubtype {V : C} (φ : V ⟶ X) (B : Over X) :
    (Over.mk φ ⟶ B) ≃ {g : V ⟶ B.left // g ≫ B.hom = φ} where
  toFun f := ⟨f.left, Over.w f⟩
  invFun g := Over.homMk g.1 g.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sections over `V` of `j_{X!}` of the presheaf represented by `B : C/X` are the morphisms
`V ⟶ B.left` of `C`: a section is a pair `(φ, f)` with `φ : V ⟶ X` and `f : (V, φ) ⟶ B`, and `φ`
is recovered from `f` as the composition of `f` with the structure morphism of `B`. -/
def presheafYonedaEquiv (B : Over X) (V : Cᵒᵖ) :
    (presheaf (CategoryTheory.yoneda.obj B)).obj V ≃
      (CategoryTheory.yoneda.obj B.left).obj V :=
  (Equiv.sigmaCongrRight fun φ => overHomEquivSubtype φ B).trans
    (Equiv.sigmaFiberEquiv fun g : V.unop ⟶ B.left => g ≫ B.hom)

/-- The structural map `γ : j_{X!}G ⟶ h_X` of Tag 00Y1, with its source written as the value of
the functor `presheafFunctor` rather than as the coproduct presheaf. It is `presheafToYoneda`
itself; only the spelling of the source differs, and this is the spelling in which `γ` composes
with the maps `presheafFunctor` produces, such as the comparison maps for a coproduct. -/
def presheafFunctorToYoneda (G : (Over X)ᵒᵖ ⥤ Type v) :
    presheafFunctor.obj G ⟶ CategoryTheory.yoneda.obj X :=
  presheafToYoneda G

/-- **`j_{X!}` of a representable presheaf is representable.** The presheaf level `j_{X!}` of the
presheaf on `C/X` represented by `B : C/X` is the presheaf on `C` represented by the underlying
object `B.left`; this is `presheafYonedaEquiv`, naturally in `V`. -/
def presheafYonedaIso (B : Over X) :
    presheafFunctor.obj (CategoryTheory.yoneda.obj B) ≅ CategoryTheory.yoneda.obj B.left :=
  NatIso.ofComponents (fun V => (presheafYonedaEquiv B V).toIso) fun _ => by ext p; rfl

/-- Under `presheafYonedaIso`, the structural map `γ` of `j_{X!}` of a representable presheaf of
`C/X` becomes the map of representables induced by the structure morphism of `B`. -/
lemma presheafYonedaIso_inv_comp_presheafFunctorToYoneda (B : Over X) :
    (presheafYonedaIso B).inv ≫ presheafFunctorToYoneda (CategoryTheory.yoneda.obj B) =
      CategoryTheory.yoneda.map B.hom := by
  ext V g
  rfl

/-- The same compatibility read in the other direction: the structural map `γ` of `j_{X!}` of a
representable presheaf of `C/X`, transported along `presheafYonedaIso`, is the map of
representables induced by the structure morphism of `B`. -/
lemma presheafYonedaIso_hom_comp_yoneda_map (B : Over X) :
    (presheafYonedaIso B).hom ≫ CategoryTheory.yoneda.map B.hom =
      presheafFunctorToYoneda (CategoryTheory.yoneda.obj B) := by
  ext V p
  exact Over.w p.2

/-- The structural map `γ` to `h_X` is natural in the presheaf on `C/X`. This is the triangle
compatibility that `presheafFunctorToOver` was built from. -/
lemma presheafFunctor_map_comp_presheafFunctorToYoneda {G G' : (Over X)ᵒᵖ ⥤ Type v} (η : G ⟶ G') :
    presheafFunctor.map η ≫ presheafFunctorToYoneda G' = presheafFunctorToYoneda G := by
  ext V p
  rfl

/-- **`j_{X!}` of a representable presheaf, as an object over `h_X`.** The presheaf level `j_{X!}`
sends the presheaf represented by `B : C/X` to the representable `h_{B.left}`, augmented to `h_X`
by the structure morphism of `B`. -/
def presheafFunctorToOverYonedaIso (B : Over X) :
    presheafFunctorToOver.obj (CategoryTheory.yoneda.obj B) ≅
      Over.mk (CategoryTheory.yoneda.map B.hom) :=
  Over.isoMk (presheafYonedaIso B) (presheafYonedaIso_hom_comp_yoneda_map B)

/-- The presheaf level `j_{X!}` is a left adjoint (`presheafAdjunction`), hence preserves all
colimits; in particular it takes the coproduct of a family of presheaves on `C/X` to the
coproduct of their images. -/
instance preservesColimitsOfSize_presheafFunctor :
    PreservesColimitsOfSize.{w, w'} (presheafFunctor (U := X)) :=
  presheafAdjunction.leftAdjoint_preservesColimits

end CategoryTheory.OverShriek

namespace CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] (X : C)

/-- The functor `F : SR(C, X) ⥤ PSh(C)/h_X` of Tag 01G2: a family `{U_i → X}` of objects over `X`
is sent to the coproduct `∐ h_{U_i}` of the representable presheaves, equipped with the map to
`h_X` whose component on `h_{U_i}` is induced by the structure morphism `U_i → X`.

It is built as in the source, by applying the semi-representable Yoneda embedding to the slice
category `C/X` and then transporting along the identification `PSh(C/X) = PSh(C)/h_X` of Tag
00Y1. -/
noncomputable def yonedaOver :
    FormalCoproduct.{v} (Over X) ⥤ Over (CategoryTheory.yoneda.obj X) :=
  FormalCoproduct.yoneda (C := Over X) ⋙ OverShriek.presheafFunctorToOver

/-- The presheaf underlying `F({U_i → X})` is `j_{X!}` of the coproduct `∐ h_{U_i → X}` of the
presheaves on `C/X` represented by the `U_i → X`, that is, the presheaf
`V ↦ ∐_{φ : V ⟶ X} ∐_i {g : V ⟶ U_i | a_i ∘ g = φ}`. -/
lemma yonedaOver_comp_forget :
    yonedaOver X ⋙ Over.forget (CategoryTheory.yoneda.obj X) =
      FormalCoproduct.yoneda (C := Over X) ⋙ OverShriek.presheafFunctor :=
  rfl

/-- The presheaf underlying `F({U_i → X})` is the coproduct `∐ h_{U_i}` of the representable
presheaves of the `U_i`: the presheaf level `j_{X!}` preserves the coproduct of the presheaves
represented by the `U_i → X` because it is a left adjoint, and it takes the presheaf represented
by `U_i → X` to the presheaf represented by `U_i`. -/
noncomputable def yonedaOverObjLeftIso (A : FormalCoproduct.{v} (Over X)) :
    OverShriek.presheafFunctor.obj (∐ fun i : A.I ↦ CategoryTheory.yoneda.obj (A.obj i)) ≅
      ∐ fun i : A.I ↦ CategoryTheory.yoneda.obj (A.obj i).left :=
  PreservesCoproduct.iso (OverShriek.presheafFunctor (U := X))
      (fun i : A.I ↦ CategoryTheory.yoneda.obj (A.obj i)) ≪≫
    Sigma.mapIso fun i ↦ OverShriek.presheafYonedaIso (A.obj i)

/-- Under `yonedaOverObjLeftIso`, the structural map `γ` of `j_{X!}` becomes the map to `h_X`
whose component on `h_{U_i}` is `h` of the structure morphism `U_i → X`. -/
lemma yonedaOverObjLeftIso_hom_comp_desc (A : FormalCoproduct.{v} (Over X)) :
    (yonedaOverObjLeftIso X A).hom ≫
        (Sigma.desc fun i : A.I ↦ CategoryTheory.yoneda.map (A.obj i).hom) =
      OverShriek.presheafFunctorToYoneda
        (∐ fun i : A.I ↦ CategoryTheory.yoneda.obj (A.obj i)) := by
  rw [← Iso.eq_inv_comp]
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  simp only [yonedaOverObjLeftIso, Iso.trans_inv, PreservesCoproduct.inv_hom, Category.assoc,
    Sigma.ι_desc, Sigma.ι_mapIso_inv_assoc, ι_comp_sigmaComparison_assoc,
    OverShriek.presheafFunctor_map_comp_presheafFunctorToYoneda,
    OverShriek.presheafYonedaIso_inv_comp_presheafFunctorToYoneda]

/-- **The value of `F` on a family, Stacks Project, Tag 01G2.** `F({U_i → X})` is the coproduct
`∐ h_{U_i}` of the representable presheaves of the `U_i`, equipped with the map to `h_X` whose
component on `h_{U_i}` is `h` of the structure morphism `U_i → X`. This is the source's
`F({U_i → X}) = (∐ h_{U_i} → h_X)`, and it is what makes the clauses below statements about the
source's `F`.

The proof is the source's description read backwards: `FormalCoproduct.yoneda` of `C/X` sends
`{U_i → X}` to the coproduct of the presheaves on `C/X` represented by the `U_i → X`, the
presheaf level `j_{X!}` preserves that coproduct because it is a left adjoint
(`OverShriek.presheafAdjunction`), and it takes the presheaf represented by `U_i → X` to the
presheaf represented by `U_i` over `h_X` (`OverShriek.presheafFunctorToOverYonedaIso`). -/
@[stacks 01G2 "the value of F: F({U_i → X}) is ∐ h_{U_i} augmented to h_X"]
noncomputable def yonedaOverObjIso (A : FormalCoproduct.{v} (Over X)) :
    (yonedaOver X).obj A ≅
      Over.mk (Sigma.desc fun i : A.I ↦ CategoryTheory.yoneda.map (A.obj i).hom) :=
  Over.isoMk (yonedaOverObjLeftIso X A) (yonedaOverObjLeftIso_hom_comp_desc X A)

/-- **Stacks Project, Tag 01G2**, coproducts clause for `SR(C, X)`, first half. The category
`SR(C, X)` of semi-representable objects over `X` has arbitrary coproducts, obtained by
concatenating the index types of the families. -/
@[stacks 01G2 "coproducts in SR(C, X)"]
theorem hasCoproducts_formalCoproductOver :
    HasCoproducts.{w} (FormalCoproduct.{w} (Over X)) :=
  inferInstance

/-- **Stacks Project, Tag 01G2**, coproducts clause for `SR(C, X)`, second half. The functor
`F : SR(C, X) ⥤ PSh(C)/h_X` commutes with coproducts: the semi-representable Yoneda embedding of
`C/X` does, and `j_{X!} : PSh(C/X) ⥤ PSh(C)/h_X` is an equivalence. -/
@[stacks 01G2 "F commutes with coproducts in SR(C, X)"]
theorem preservesColimitsOfShape_yonedaOver (J : Type v) :
    PreservesColimitsOfShape (Discrete J) (yonedaOver X) := by
  dsimp [yonedaOver]
  infer_instance

/-- **Stacks Project, Tag 01G2**, finite limits clause for `SR(C, X)`, second half. The functor
`F : SR(C, X) ⥤ PSh(C)/h_X` commutes with limits of every shape, with no hypothesis on `C`; this
strengthens the finite limits of the source's clause. The first half, that `SR(C, X)` has finite
limits as soon as `C` has fibre products, is
`Stacks.CategoryTheory.Hypercovering.hasFiniteLimits_formalCoproductOver`. -/
@[stacks 01G2 "F : SR(C, X) → PSh(C)/h_X commutes with finite limits"]
noncomputable instance preservesLimitsOfSize_yonedaOver :
    PreservesLimitsOfSize.{w, w'} (yonedaOver X) := by
  dsimp [yonedaOver]
  infer_instance

end CategoryTheory.Limits.FormalCoproduct

end
