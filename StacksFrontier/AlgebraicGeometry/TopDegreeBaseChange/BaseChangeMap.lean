module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossing
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap

/-!
# The canonical base-change map on the top higher direct image

[Stacks, Tag 0EX3] explains its conclusion (c) — that formation of `R^d f'_* F'` commutes with
arbitrary further base change — by first writing down the map whose invertibility is the
content. Given a second cartesian square tacked onto the given one,

```
X'' --h'--> X' --g'--> X
|           |          |
f''         f'         f
v           v          v
Y''  --h--> Y'  --g--> Y
```

the source says

> If (a) holds, then there is a canonical map `γ : h^* R^d f'_* F' ⟶ R^d f''_* (h')^* F'`.
> Namely, `γ` is the map on degree `d` cohomology sheaves induced by the composition
> `Lh^* Rf'_* F' ⟶ Rf''_* L(h')^* F' ⟶ Rf''_* (h')^* F'`.

This file constructs that `γ`. Its three factors were all already available and had never been
composed: the identification `h^* R^d f'_* F' ≅ H^d(Lh^* Rf'_* F')` supplied by (a)
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImagePullbackIso`), the derived base
change map of [Stacks, Tag 08HY]
(`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap`), and the comparison
from derived to ordinary pullback of a module placed in a single degree
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle`, in degree `0`).

The invertibility of `γ` — conclusion (c) itself — is **not** proved here. What is proved is the
reduction that the first of its three factors contributes nothing to the question: `γ` is
invertible if and only if the map on degree-`d` cohomology induced by the two-step composition
the source displays is, so the whole content of (c) lives in the derived category and the
top-degree comparison can be set aside.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageBaseChangeMap`: **the canonical
  map `γ`**.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.toShHom_comm_of_isPullback`: the second square's
  commutativity, read on sheaved spaces, which is the only thing the construction of `γ` uses
  of it.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.topDirectImageBaseChangeMap_eq`: `γ` with the
  degree-`d` cohomology functor distributed over the two-step composition, naming its two
  factors separately.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap_iff`:
  **conclusion (c) is equivalent to the invertibility of the degree-`d` cohomology of the
  displayed two-step composition.**
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_zero_eq`: in
  degree `0` the comparison from derived to ordinary pullback is the four-fold composite written
  at the scheme-level spelling of the category of modules.

## Implementation notes

*The map needs only a commutative square, not a cartesian one.* Cartesianness of the second
square is a hypothesis of conclusion (c), but the construction of `γ` uses only
`h' ≫ f' = f'' ≫ h`, because that is all [Stacks, Tag 08HY] uses. The map is therefore
constructed from the equation, and `toShHom_comm_of_isPullback` supplies it from an
`CategoryTheory.IsPullback`; nothing is lost and a consumer with a merely commutative square can
use the map.

*Why the equation is taken on sheaved spaces.*
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` is stated
for morphisms of ringed spaces, so its square must commute there. `Scheme.Hom.comp_toLRSHom`
and `LocallyRingedSpace.comp_toShHom` transport the scheme-level equation, and both are
`simp` lemmas, so the transport is one `simpa`.

*The reduction is an application, not an instance binder.* `IsIso (γ …)` is not syntactically
`IsIso (u ≫ v)` — `γ` is a `def`, hence semireducible, and instance search does not unfold it.
So the two halves of the equivalence supply the hypothesis in **argument** position,
`@CategoryTheory.IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hi`, where the elaborator
checks the expected type at default transparency. This is the directory's recorded cure for the
same wall: instance *binders* do not cross a definitional gap, *applications* do.

*The distribution over the two-step composition costs nothing here.* Distributing `H^d` over the
four-fold composite of `derivedToOrdinaryPullbackSingle` is a deterministic `isDefEq` timeout at
this spelling, which is why `TopDegreePullbackIdentity.lean` keeps that composite under one
`H^d`. The two-fold distribution below is not affected, and it is written in term mode
(`congrArg` of `Functor.map_comp`) so that no rewrite motive is formed.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction HomologicalComplex
open DerivedCategory

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X'' Y'' : Scheme.{u}}

/-- The second cartesian square, read as a commutative square of sheaved spaces. This is all
that the construction of the base-change map uses of the square. -/
theorem toShHom_comm_of_isPullback
    {S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u}}
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : IsPullback h' f'' S.f' h) :
    h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun k : X'' ⟶ S.Y' => k.toLRSHom.toShHom) sq.w

/-- **The canonical base-change map on the top higher direct image**,

> `γ : h^* R^d f'_* F' ⟶ R^d f''_* (h')^* F'`,

of [Stacks, Tag 0EX3]: the degree-`d` cohomology of the composition

> `Lh^* Rf'_* F' ⟶ Rf''_* L(h')^* F' ⟶ Rf''_* (h')^* F'`,

read through the identification `h^* R^d f'_* F' ≅ H^d(Lh^* Rf'_* F')` which conclusion (a) of
the tag supplies. The first arrow is the derived base change map of [Stacks, Tag 08HY] and the
second is derived pushforward of the comparison from derived to ordinary pullback.

The tag's conclusion (c) is that this map is an isomorphism. -/
def topDirectImageBaseChangeMap
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom) :
    (Scheme.Modules.pullback h).obj
      ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            S.f'.toLRSHom.toShHom).obj
          ((singleFunctor S.X'.Modules 0).obj F'))) ⟶
    (homologyFunctor Y''.Modules (S.d : ℤ)).obj
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          f''.toLRSHom.toShHom).obj
        ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) :=
  (topDirectImagePullbackIso S F' h).hom ≫
    (homologyFunctor Y''.Modules (S.d : ℤ)).map
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap h'.toLRSHom.toShHom
          f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
          ((singleFunctor S.X'.Modules 0).obj F') ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
            f''.toLRSHom.toShHom).map
          (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))

/-- The base-change map with the degree-`d` cohomology functor distributed over the two-step
composition the source displays, so that its two factors — the derived base change map of
[Stacks, Tag 08HY] and the derived pushforward of the derived-to-ordinary comparison — are
named separately. -/
theorem topDirectImageBaseChangeMap_eq
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom) :
    topDirectImageBaseChangeMap S F' h' f'' h sq =
      (topDirectImagePullbackIso S F' h).hom ≫
        (homologyFunctor Y''.Modules (S.d : ℤ)).map
          (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap h'.toLRSHom.toShHom
            f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
            ((singleFunctor S.X'.Modules 0).obj F')) ≫
        (homologyFunctor Y''.Modules (S.d : ℤ)).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
              f''.toLRSHom.toShHom).map
            (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0)) :=
  congrArg (fun k => (topDirectImagePullbackIso S F' h).hom ≫ k)
    ((homologyFunctor Y''.Modules (S.d : ℤ)).map_comp _ _)

/-- **Conclusion (c) of [Stacks, Tag 0EX3] is equivalent to the invertibility of the degree-`d`
cohomology of the two-step composition the source displays.** The first of the three factors of
the canonical map is an isomorphism — it is `topDirectImagePullbackIso`, which conclusion (a)
makes unconditional — so it contributes nothing to the question, and the whole content of (c)
lives in the derived category. -/
theorem isIso_topDirectImageBaseChangeMap_iff
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
    (F' : S.X'.Modules) [F'.IsQuasicoherent]
    (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
    (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
      = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom) :
    IsIso (topDirectImageBaseChangeMap S F' h' f'' h sq) ↔
      IsIso ((homologyFunctor Y''.Modules (S.d : ℤ)).map
        (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap h'.toLRSHom.toShHom
            f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
            ((singleFunctor S.X'.Modules 0).obj F') ≫
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
              f''.toLRSHom.toShHom).map
            (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))) :=
  ⟨fun hi => @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ inferInstance hi,
   fun hi => @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hi⟩

/-- **The comparison from derived to ordinary pullback in degree `0`, at the scheme-level
spelling.** `derivedToOrdinaryPullbackSingle` is stated for morphisms of ringed spaces and in an
arbitrary degree; in degree `0` and at a morphism of schemes it is, on the nose, the four-fold
composite of the derived-pullback comparison with the three identifications of the single
functors. -/
theorem derivedToOrdinaryPullbackSingle_zero_eq
    {X' : Scheme.{u}} (h' : X'' ⟶ X') (F' : X'.Modules) :
    derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0 =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
            h'.toLRSHom.toShHom).map
          ((singleFunctorIsoCompQh X'.Modules 0).hom.app F') ≫
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
            h'.toLRSHom.toShHom).app
          ((HomotopyCategory.singleFunctor X'.Modules 0).obj F') ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategorySingleFunctor (modulePullback h'.toLRSHom.toShHom) 0).hom.app
            F') ≫
        (singleFunctorIsoCompQh X''.Modules 0).inv.app ((Scheme.Modules.pullback h').obj F') :=
  rfl

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
