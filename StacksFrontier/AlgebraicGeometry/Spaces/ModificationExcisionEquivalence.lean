module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.DependentProductSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ExcisionAlgebraicCofan
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationExcisionCounitIso
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphism

/-!
# Stacks 0BGY: base change along a separated étale morphism is an equivalence

Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over a scheme `S` and let
`T` be a closed subspace of `W` whose preimage is carried isomorphically onto `T` by `f`.
Write `W⁰` for the open complement of `T` and `V⁰ = f⁻¹W⁰`. This file completes Stacks 0BGY:
base change along `f`, from the modifications of `W` outside `W⁰` to the modifications of `V`
outside `V⁰`, is an equivalence of categories.

Faithfulness and fullness are
`AlgebraicGeometry.Space.faithful_baseChangeFunctor` and
`AlgebraicGeometry.Space.full_baseChangeFunctor`. What is proved here is essential
surjectivity, by assembling the inverse construction of the source proof.

## Main results

* `AlgebraicGeometry.Space.isModification_depProd`: the dependent product of a modification of
  `V` outside `V⁰` is a modification of `W` outside `W⁰`. This is the object part of the
  inverse functor.
* `AlgebraicGeometry.Space.essSurj_baseChangeFunctor`: **Stacks 0BGY**, essential surjectivity
  of the base-change functor.
* `AlgebraicGeometry.Space.isEquivalence_baseChangeFunctor` and
  `AlgebraicGeometry.Space.baseChangeEquivalence`: **Stacks 0BGY**, the base-change functor is
  an equivalence of categories.

## Implementation notes

Given a modification `Y ⟶ V` outside `V⁰`, the source proof builds the preimage as the functor
whose `A`-points are the pairs `(w, y)` with `w : A ⟶ W` and `y : A ×_{w,W} V ⟶ Y` over `V`.
That functor is the dependent product (Weil restriction) `Π_f Y`, built in
`StacksFrontier/CategoryTheory/DependentProduct.lean`, and the three things the proof asks of it
are proved separately and only combined here:

* it is an fppf sheaf (`AlgebraicGeometry.Space.isSheaf_depProdObj`);
* `X ×_{g,W} W⁰ = W⁰` (`AlgebraicGeometry.Space.isIso_fromPreimage_depProdπ` and
  `AlgebraicGeometry.Space.isIso_pullback_snd_depProdπ`), which is both the modification
  condition on `X` and the first leg of its algebraicity;
* `X ×_{g,W,f} V = Y` (`AlgebraicGeometry.Space.isIso_depProdCounitApp_left` and
  `AlgebraicGeometry.Space.isIso_depProdCounitApp`), which is both the second leg of its
  algebraicity and the isomorphism witnessing essential surjectivity.

Algebraicity of `X` is then the excision criterion
`AlgebraicGeometry.Space.isAlgebraicSpace_of_excisionBaseSource'`: a sheaf over `W` whose part
over `W⁰` and whose fibre product with `V` are algebraic spaces is an algebraic space, because
those two cover it by representable étale maps.

The order matters. Algebraicity of the leg `X ×_W V` is obtained by transporting it along the
counit isomorphism from `Y`, *not* from `AlgebraicGeometry.isAlgebraicSpace_pullback`: that
lemma would need `X` to be an algebraic space already, which is what is being proved. So the
counit isomorphism has to be available before algebraicity of `X`, and it is — it is proved for
an arbitrary `Over V` whose source is a sheaf, with no algebraicity hypothesis on the dependent
product.

`AlgebraicGeometry.Space.isSheaf_depProdObj` takes three sheaf conditions, on `V`, on `W` and
on `Y.left`; the one on `V` is not removable, and the counterexample is in its own module
documentation. Here all three are free: `V` and `W` are algebraic spaces and `Y` is a
modification.

## References

* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Presheaf Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {V W : AlgebraicSpaces B S hS}

/-! ### The dependent product is a modification -/

/-- A modification of `V` outside `f⁻¹W⁰` has an invertible map from the preimage of `f⁻¹W⁰`. -/
private theorem isIso_fromPreimage_modification (f : V ⟶ W) (T : Subfunctor W.obj)
    (Y : Modification B S hS ((openComplement B S hS T).preimage f.hom)) :
    IsIso (((openComplement B S hS T).preimage f.hom).fromPreimage Y.obj.hom) :=
  isIso_fromPreimage_of_isIso_pullback_snd Y.obj.hom _ Y.property.2

/-- **The dependent product of a modification is a modification**: for `f : V ⟶ W` separated
étale and `T` a closed subspace of `W` carried isomorphically onto by `f`, the dependent
product `Π_f Y` of a modification `Y` of `V` outside `f⁻¹W⁰` is a modification of `W` outside
`W⁰`.

This is the object part of the inverse functor of Stacks 0BGY. The modification condition is
the computation `X ×_{g,W} W⁰ = W⁰`; algebraicity is the excision criterion, whose two legs are
that same computation and the computation `X ×_{g,W,f} V = Y`. -/
theorem isModification_depProd (f : V ⟶ W) (hf : IsEtale B S hS f.hom)
    (hsep : IsSeparated B S hS f.hom) (T : Subfunctor W.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    (Y : Modification B S hS ((openComplement B S hS T).preimage f.hom)) :
    IsModification B S hS (openComplement B S hS T) ((depProd f.hom).obj Y.obj) := by
  have hY := isIso_fromPreimage_modification B S hS f T Y
  refine ⟨?_, isIso_pullback_snd_depProdπ B S hS f.hom (openComplement B S hS T) Y.obj
    Y.property.2⟩
  refine isAlgebraicSpace_of_excisionBaseSource' B S hS f hf hsep T hT hfT
    (isSheaf_depProdObj B S hS f.hom Y.obj V.property.isSheaf W.property.isSheaf
      Y.property.1.isSheaf)
    (depProdπ f.hom Y.obj) ?_
  rintro (_ | _)
  · -- The leg `X ×_{g,W,f} V`, which the counit identifies with `Y`.
    change IsAlgebraicSpace B S hS (pullback (depProdπ f.hom Y.obj) f.hom)
    have hiso := isIso_depProdCounitApp_left B S hS V.property W.property f.hom hf hsep T hfT
      Y.obj hY Y.property.1.isSheaf
    exact AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS (@asIso _ _ _ _ _ hiso)
      Y.property.1
  · -- The leg `X ×_{g,W} W⁰`, which rigidity identifies with the open subspace `W⁰`.
    change IsAlgebraicSpace B S hS
      ((openComplement B S hS T).preimage (depProdπ f.hom Y.obj)).toFunctor
    have : IsIso ((openComplement B S hS T).fromPreimage (depProdπ f.hom Y.obj)) :=
      isIso_fromPreimage_depProdπ B S hS f.hom (openComplement B S hS T) Y.obj hY
    exact AlgebraicGeometry.isAlgebraicSpace_of_iso B S hS
      (asIso ((openComplement B S hS T).fromPreimage (depProdπ f.hom Y.obj)))
      (isOpenSubspace_openComplement B S hS W.property T hT).1

/-! ### Essential surjectivity, and the equivalence -/

/-- **Stacks 0BGY, essential surjectivity of the base-change functor.** Let `f : V ⟶ W` be a
separated étale morphism of algebraic spaces over `S` and let `T` be a closed subspace of `W`
whose preimage is carried isomorphically onto `T`. Then every modification of `V` outside
`f⁻¹W⁰` is isomorphic to the base change of a modification of `W` outside `W⁰`, namely of the
dependent product `Π_f Y`, the isomorphism being the counit. -/
@[stacks 0BGY "the base-change functor is essentially surjective"]
theorem essSurj_baseChangeFunctor (f : V ⟶ W) (T : Subfunctor W.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    (hf : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom) :
    (baseChangeFunctor B S hS f (openComplement B S hS T)).1.EssSurj where
  mem_essImage Y := by
    have hiso := isIso_depProdCounitApp B S hS V.property W.property f.hom hf hsep T hfT
      Y.obj (isIso_fromPreimage_modification B S hS f T Y) Y.property.1.isSheaf
    exact ⟨⟨(depProd f.hom).obj Y.obj, isModification_depProd B S hS f hf hsep T hT hfT Y⟩,
      ⟨ObjectProperty.isoMk _ (@asIso _ _ _ _ _ hiso)⟩⟩

/-- **Stacks 0BGY.** Let `f : V ⟶ W` be a separated étale morphism of algebraic spaces over a
scheme `S` and let `T ⊂ W` be a closed subspace such that `f⁻¹T → T` is an isomorphism. Write
`W⁰` for the complement of `T` and `V⁰ = f⁻¹W⁰`. Then base change along `f` is an equivalence
from the category of morphisms `g : X ⟶ W` of algebraic spaces with `g⁻¹W⁰ → W⁰` an
isomorphism to the category of morphisms `h : Y ⟶ V` of algebraic spaces with `h⁻¹V⁰ → V⁰` an
isomorphism.

Faithfulness is `AlgebraicGeometry.Space.faithful_baseChangeFunctor`, fullness is
`AlgebraicGeometry.Space.full_baseChangeFunctor` and essential surjectivity is
`AlgebraicGeometry.Space.essSurj_baseChangeFunctor`. -/
@[stacks 0BGY "equivalence of categories"]
theorem isEquivalence_baseChangeFunctor (f : V ⟶ W) (T : Subfunctor W.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    (hf : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom) :
    (baseChangeFunctor B S hS f (openComplement B S hS T)).1.IsEquivalence where
  faithful := faithful_baseChangeFunctor B S hS f T hT hfT hf
  full := full_baseChangeFunctor B S hS f T hT hfT hf hsep
  essSurj := essSurj_baseChangeFunctor B S hS f T hT hfT hf hsep

/-- **Stacks 0BGY**, the equivalence of categories itself: base change along a separated étale
`f : V ⟶ W` is an equivalence from the modifications of `W` outside `W⁰` to the modifications
of `V` outside `f⁻¹W⁰`. This is `AlgebraicGeometry.Space.isEquivalence_baseChangeFunctor`
packaged as a `CategoryTheory.Equivalence`; the tag is registered there. -/
def baseChangeEquivalence (f : V ⟶ W) (T : Subfunctor W.obj)
    (hT : IsClosedSubspace B S hS T) (hfT : IsIso (T.fromPreimage f.hom))
    (hf : IsEtale B S hS f.hom) (hsep : IsSeparated B S hS f.hom) :
    Modification B S hS (openComplement B S hS T) ≌
      Modification B S hS ((openComplement B S hS T).preimage f.hom) :=
  have := isEquivalence_baseChangeFunctor B S hS f T hT hfT hf hsep
  (baseChangeFunctor B S hS f (openComplement B S hS T)).1.asEquivalence

end AlgebraicGeometry.Space

end
