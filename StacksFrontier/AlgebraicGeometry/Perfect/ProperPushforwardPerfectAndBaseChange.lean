module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardBaseChangeCanonical
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness and base change of the direct image along a proper morphism of finite presentation

Let `f : X ⟶ S` be a proper morphism of finite presentation. [Stacks, Tag 0B91] asserts:

1. if `f` is flat and `E ∈ D(𝒪_X)` is perfect, then `Rf_*E` is a perfect object of `D(𝒪_S)` and
   its formation commutes with arbitrary base change;
2. if `𝒢` is an `𝒪_X`-module of finite presentation, flat over `S`, then `Rf_*𝒢` is a perfect
   object of `D(𝒪_S)` and its formation commutes with arbitrary base change.

Both clauses are stated together in
`ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_baseChange_of_isProper`.

"Formation commutes with arbitrary base change" is read at the canonical maps. For every
cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

in clause (1) the map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of [Stacks, Tag 08HY] is an isomorphism, and in
clause (2) the map `Lg^*Rf_*𝒢 ⟶ Rf'_*L(g')^*𝒢 ⟶ Rf'_*(g')^*𝒢`, the map of [Stacks, Tag 08HY]
followed by `Rf'_*` of the derived-to-ordinary comparison, is an isomorphism, so that the base
change of `Rf_*𝒢` is the direct image of the ordinary pullback `(g')^*𝒢`.

## Proof

The source's proof specialises [Stacks, Tag 0A1H] (clause (1) at `𝒢^• = 𝒪_X[0]`, clause (2) at
`E = 𝒪_X` and `𝒢^• = 𝒢[0]`). Clause (1) is
`ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat`, which
does exactly that. In clause (2) the perfectness is
`ProperFlatBaseChange.isPerfect_derivedPushforward_module` (again [Stacks, Tag 0A1H]), and the
invertibility of the canonical base-change map is
`ProperFlatBaseChange.isIso_derivedBaseChangeComp_singleDegree_of_isFinitePresentation`, which
checks condition (1) of [Stacks, Tag 0DJ8] stalkwise from the flatness of `𝒢` over `S` and
concludes by [Stacks, Tag 0DJ9].

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
* [Stacks Project, Tag 0DJ9](https://stacks.math.columbia.edu/tag/0DJ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedBaseChange (derivedBaseChangeMap)
open Stacks.Cohomology.DerivedPullbackTensor (derivedPullbackNatTrans pullbackComplex)

universe u

namespace AlgebraicGeometry.ProperFlatBaseChange

attribute [local instance] HasDerivedCategory.standard

/-- **[Stacks, Tag 0B91].** Let `f : X ⟶ S` be a proper morphism of schemes of finite
presentation.

1. Let `E ∈ D(𝒪_X)` be perfect and `f` flat. Then `Rf_*E` is a perfect object of `D(𝒪_S)`, and
   its formation commutes with arbitrary base change: for every cartesian square
   `X' = X ×_S S'` the canonical map `Lg^*Rf_*E ⟶ Rf'_*L(g')^*E` of [Stacks, Tag 08HY] is an
   isomorphism.
2. Let `𝒢` be an `𝒪_X`-module of finite presentation, flat over `S`. Then `Rf_*𝒢` is a perfect
   object of `D(𝒪_S)`, and its formation commutes with arbitrary base change: for every
   cartesian square the canonical map `Lg^*Rf_*𝒢 ⟶ Rf'_*L(g')^*𝒢 ⟶ Rf'_*(g')^*𝒢` (the map of
   [Stacks, Tag 08HY] followed by `Rf'_*` of the derived-to-ordinary comparison) is an
   isomorphism.

Here `𝒢` is placed in degree zero as the complex `singleDegreeComplex 𝒢`, at which the
base-change map of clause (2) is written. -/
@[stacks 0B91 "both clauses in full: for f proper of finite presentation, (1) for f flat and E \
perfect, Rf_*E is perfect and the canonical map Lg^*Rf_*E --> Rf'_*L(g')^*E of Tag 08HY is an \
isomorphism for every cartesian square; (2) for G of finite presentation and flat over S, Rf_*G \
is perfect and the canonical map Lg^*Rf_*G --> Rf'_*(g')^*G is an isomorphism for every \
cartesian square"]
theorem isPerfect_derivedPushforward_and_isIso_baseChange_of_isProper {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f) :
    (Flat f → ∀ E : DerivedCategory X.Modules, RingedSpace.IsPerfect (X := X.toRingedSpace) E →
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj E) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
            g.toLRSHom.toShHom (comp_toShHom_of_comm hsq.w) E)) ∧
    (∀ G : X.Modules, G.IsFinitePresentation → IsFlatOver f.toLRSHom.toShHom G →
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (DerivedCategory.Q.obj (singleDegreeComplex G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (derivedBaseChangeComp f g f' g' hsq.w
            (DerivedCategory.Q.obj (singleDegreeComplex G))
            (DerivedCategory.Q.obj ((pullbackComplex g'.toLRSHom.toShHom).obj
              (singleDegreeComplex G)))
            ((derivedPullbackNatTrans g'.toLRSHom.toShHom).app (singleDegreeComplex G)))) := by
  have : QuasiCompact f := hf.quasiCompact
  have : QuasiSeparated f := hf.quasiSeparated
  refine ⟨fun hflat E hE =>
    isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat f hf hproper hflat E hE,
    fun G hfp hflat => ⟨?_, fun g f' g' hsq => ?_⟩⟩
  · exact Stacks.Perfect.BoundedLocallyFreeComplexes.isPerfect_of_iso
      ((derivedPushforward f.toLRSHom.toShHom).mapIso
        ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app G))
      (isPerfect_derivedPushforward_module f hf hproper G hfp hflat)
  · have := hfp
    exact isIso_derivedBaseChangeComp_singleDegree_of_isFinitePresentation hsq G hflat

end AlgebraicGeometry.ProperFlatBaseChange

end
