module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsGenerators
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeTop
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsJoin

/-!
# Conclusion (c) of [Stacks, Tag 0EX3] from the pure-tensor agreement

Conclusion (c) of [Stacks, Tag 0EX3] says that formation of the top-degree direct image commutes
with further base change: for a top-degree base-change situation `S`, a quasi-coherent `F'` on
`X'` and a **cartesian** second square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
the canonical map `γ : h^* R^d f'_* F' ⟶ R^d f''_* (h')^* F'` is an isomorphism.

Everything the reduction of (c) needs is available, and this file performs the reduction: (c)
follows from the single identity that the Eilenberg-Watts map `ψ` of
`…TopDegreeBaseChange.baseChangeSectionsMap` agrees with `Γ(W, γ⁺)` on the pure tensors `1 ⊗ a`,
over each compatible pair of affine opens.

## Main results

* `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_of_isPullback_of_one_tmul`: **conclusion
  (c), from the bijectivity of `ψ` and the pure-tensor agreement.** Over each compatible pair of
  affine opens the two hypotheses are: `ψ` is bijective, and `ψ` agrees with `Γ(W, γ⁺)` on the
  pure tensors `1 ⊗ a`. Nothing else is assumed beyond the situation and the cartesian square.

## How the reduction goes

Two existing results compose, and nothing else is needed.

* `…TopDegreeBaseChange.bijective_app_topDirectImageBaseChangeMapPlus_of_one_tmul`
  (`BaseChangeSectionsGenerators.lean`) turns a **bijective** `Γ(Y'', W)`-linear map out of the
  base change `Γ(Y'', W) ⊗_{Γ(Y', V)} Γ(R^d f'_* F', V)` that agrees with `Γ(W, γ⁺)` on the pure
  tensors into bijectivity of `Γ(W, γ⁺)`: a map out of a base change is determined by its values
  on `1 ⊗ a`, and the comparison it is thereby identified with is an isomorphism. The map supplied
  is `…TopDegreeBaseChange.baseChangeSectionsMap`, whose binder type is syntactically the one that
  result asks for.
* the entry point of `BaseChangeTop.lean`,
  `…isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens_of_isPullback`,
  then gives (c) itself: invertibility of a morphism of sheaves of modules
  on `Y''` is local, and the compatible pairs of affine opens cover, so bijectivity of
  `Γ(W, γ⁺)` over each of them suffices. The finiteness of the twice-base-changed morphism is read
  off the square, both properties being stable under base change.

The first hypothesis is discharged, with no hypothesis left, by
`…TopDegreeBaseChange.bijective_baseChangeSectionsMap_of_affineOpens` (`HmulProjectionMain.lean`);
it is taken as a hypothesis here rather than consumed, because that file's import closure makes a
second `HasDerivedCategory` instance available, under which a freshly written
`Functor.rightDerivedPlus` elaborates at the wrong universes and is a different functor from the
one `γ⁺` is built on — so the statement of the pure-tensor agreement cannot be written in a module
that imports it. The consumer composes the two.

## Implementation notes

*The affineness of the two opens is passed in two shapes, and that is not avoidable here.*
`bijective_app_topDirectImageBaseChangeMapPlus_of_one_tmul` and the entry point of
`BaseChangeTop.lean` take `AlgebraicGeometry.IsAffineOpen` as an **argument**, because the covering
they consume produces it that way, whereas `baseChangeSectionsMap` takes
`IsAffine (V : Scheme)` as an **instance**, because the Eilenberg-Watts machinery it is built from
needs it for elaboration. The two are the same statement — `IsAffineOpen V` unfolds to
`IsAffine (V : Scheme)` — and `haveI` crosses between them; the files of those results already cross
it the other way, writing `(‹IsAffine (V : Scheme)› : IsAffineOpen V)`.

*The two hypotheses take the affineness as instance binders, and that is forced.* Writing them
with the instances supplied inside the binder by `haveI` makes the occurrence of
`baseChangeSectionsMap` in the hypothesis carry a different instance term from the occurrence at
the point of use, and identifying the two means unfolding that map — which exhausts the
elaborator's recursion budget. This is the wall `BaseChangeSectionsBijection.lean` records when it
explains why the four Eilenberg-Watts hypotheses are kept out of the argument lists: *the same map
written in two places would carry two different instance terms and the two would have to be
identified.* With instance binders the ambient instances at the point of use are the ones the
hypothesis is instantiated at, and nothing has to be reconciled.

*No `@[stacks 0EX3]` attribute is placed on the result below.* It is conclusion (c) granted two
hypotheses, not conclusion (c); by the covering-set rule the tag belongs on the statement that
carries no hypothesis beyond the situation and the cartesian square.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TensorProduct
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

variable {X'' Y'' : Scheme.{u}}

/-- **Conclusion (c) of [Stacks, Tag 0EX3], from the pure-tensor agreement.** For a top-degree
base-change situation `S`, a quasi-coherent `F'` on `X'` and a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
the canonical map `γ` of the tag is an isomorphism, as soon as over every compatible pair of
affine opens — an affine open `V` of `Y'` and an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` — the
Eilenberg-Watts map `ψ` of `…TopDegreeBaseChange.baseChangeSectionsMap` agrees with `Γ(W, γ⁺)` on
the pure tensors `1 ⊗ a`, the latter read at the pullback
`AlgebraicGeometry.Scheme.Modules.pullbackSection h (R^d f'_* F') V W` of the section `a`.

No hypothesis on `Y'`, on `Y''` or on the two base-changed morphisms is added: the finiteness of
`f''` is read off the square, and the affineness is asked of the two opens only. -/
theorem isIso_topDirectImageBaseChangeMap_of_isPullback_of_one_tmul
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (sq : IsPullback h' f'' S.f' h)
    (hbij : ∀ (V : S.Y'.Opens) (W : Y''.Opens) [IsAffine (V : Scheme)] [IsAffine (W : Scheme)]
      (hWV : W ≤ h ⁻¹ᵁ V),
      Function.Bijective (baseChangeSectionsMap S F' h' f'' h sq hWV))
    (hone : ∀ (V : S.Y'.Opens) (W : Y''.Opens) [IsAffine (V : Scheme)] [IsAffine (W : Scheme)]
      (hWV : W ≤ h ⁻¹ᵁ V)
      (a : Γ(((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F', V)),
      baseChangeSectionsMap S F' h' f'' h sq hWV
          ((1 : Γ(Y'', W)) ⊗ₜ[Γ(S.Y', V), (h.appLE V W hWV).hom] a) =
        (topDirectImageBaseChangeMapPlus S F' h' f'' h
            (toShHom_comm_of_isPullback h' f'' h sq)).val.app (op W)
          (Scheme.Modules.pullbackSection h
            (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F')
            V W hWV a)) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h
      (toShHom_comm_of_isPullback h' f'' h sq)) := by
  refine isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens_of_isPullback
    S F' h' f'' h sq fun V hV W hW hsub => ?_
  have : IsAffine (V : Scheme) := hV
  have : IsAffine (W : Scheme) := hW
  exact bijective_app_topDirectImageBaseChangeMapPlus_of_one_tmul S F' h' f'' h
    (toShHom_comm_of_isPullback h' f'' h sq) hV hW hsub
    (baseChangeSectionsMap S F' h' f'' h sq hsub)
    (hbij V W hsub) (hone V W hsub)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
