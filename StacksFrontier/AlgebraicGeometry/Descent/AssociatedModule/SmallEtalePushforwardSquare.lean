module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleOpenCoverQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition

/-!
# The square of Stacks 03LC (3) at `τ = étale`, and what it is reduced to

Stacks 03LC part (3) asserts, for `f : T ⟶ S` quasi-compact and quasi-separated and
`τ ∈ {Zariski, étale}`, **three** things: that `f_*` preserves quasi-coherent sheaves, that
`f_{small, *}` preserves quasi-coherent `𝒪`-modules on the small `τ`-site, and that the square

```
  QCoh(𝒪_T) ----- f_* -----> QCoh(𝒪_S)
      |                          |
   𝓕 ↦ 𝓕^a                   𝓖 ↦ 𝓖^a
      |                          |
      v                          v
  QCoh(T_τ, 𝒪) - f_{small,*} -> QCoh(S_τ, 𝒪)
```

commutes, `f_{small, *}(𝓕^a) = (f_*𝓕)^a`.  Only the first of the three is in the library:
`AlgebraicGeometry.pushforward_isQuasicoherent`.  This module does what is available for the
other two and **states precisely what is left**, which is a single statement.

The formal content is the mate square
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso`, `ε_{S,*} ∘ f_{small,*} ≅ f_* ∘
ε_{T,*}`, which holds with no hypothesis and is the right-adjoint transpose of 03LC (1).  Read at
an associated module `𝓕^a` and composed with the unit isomorphism of Stacks 0GN7 it gives

  `ε_{S,*}(f_{small,*}(𝓕^a)) ≅ f_*𝓕`,

`AlgebraicGeometry.SmallEtale.restrictModuleSmallPushforwardAssociatedModuleIso` below, again
with no hypothesis on `f`.  So *the restriction of the left-hand side of the square to the small
Zariski site of `S` is quasi-coherent* as soon as `f` is quasi-compact and quasi-separated, by
Stacks 01LC — and that is exactly the hypothesis `h` of
`AlgebraicGeometry.SmallEtale.isIso_counit`.  Feeding it there turns the counit at
`f_{small, *}(𝓕^a)` into the comparison the square asks for, *provided* the counit's other
hypothesis is met: that `f_{small, *}(𝓕^a)` is quasi-coherent on `S_étale`.

**That proviso is the whole of the gap, and it is not discharged here.**  It is the second
conjunct of 03LC (3) read at the one module that matters, and it is equivalent to the square: in
one direction `AlgebraicGeometry.SmallEtale.associatedModuleSmallPushforwardIso` below, in the
other `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_pushforward` says the
right-hand side `(f_*𝓕)^a` *is* quasi-coherent on the site, so an isomorphism with it transports
the property back.  Neither conjunct therefore follows from the other, and no formal consequence
of 03LC (1) supplies either: the source proves them by computing sections, `Γ(U, g^*f_*𝓕) =
Γ(U ×_S T, (g')^*𝓕)` for `g : U → S` étale, which is Stacks 02KH in degree `0` over an arbitrary
base — available as
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat` — fed
through the sections description of `𝓕^a` on `S_étale`,
`AlgebraicGeometry.SmallEtale.associatedModuleObjSectionsIso`.  Assembling those two into a
morphism of sheaves of modules on `S_étale` is the missing step.

## Main definitions

* `AlgebraicGeometry.SmallEtale.smallPushforward`: `f_{small, *}`, the pushforward of sheaves of
  modules along the morphism of ringed small étale sites `ε_a` of Stacks 070R (2).
* `AlgebraicGeometry.SmallEtale.restrictModuleSmallPushforwardAssociatedModuleIso`:
  **`ε_{S,*}(f_{small,*}(𝓕^a)) ≅ f_*𝓕`**, with no hypothesis on `f`.
* `AlgebraicGeometry.SmallEtale.associatedModuleSmallPushforwardIso`: **the square of
  Stacks 03LC (3) at `τ = étale`**, over quasi-coherence of `f_{small, *}(𝓕^a)` on `S_étale`.

## Main results

* `AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule_smallPushforward_associatedModule`:
  for `f` quasi-compact and quasi-separated, `ε_{S,*}(f_{small,*}(𝓕^a))` is quasi-coherent.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_pushforward`: the other
  corner of the square, `(f_*𝓕)^a`, is quasi-coherent on `S_étale`.

## Implementation notes

Nothing here is tagged `@[stacks 03LC]`.  The two unconditional statements are not any conjunct
of part (3): the first is about `ε_{S,*} ∘ f_{small,*}` and not about `f_{small,*}`, and the
second is Stacks 03DV (2) at the module `f_*𝓕`.  The conditional statement carries a conjunct of
the part as a hypothesis, and a hypothesis is part of a citation.

This module is the earlier, weaker route, kept for the reduction it records.  Part (3) at
`τ = étale` is proved outright in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePushforwardCartesian.lean`,
where `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_smallPushforward` discharges the
hypothesis this module assumes and
`AlgebraicGeometry.SmallEtale.associatedModuleSmallPushforwardIsoOfQcqs` carries the square with
no hypothesis beyond the source's own.  Those two hold the `@[stacks 03LC]` registrations.

## References

* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

/-- **`f_{small, *}`**, the pushforward of sheaves of modules along the morphism of ringed small
étale sites `ε_a : (X_étale, 𝒪_X) ⟶ (Y_étale, 𝒪_Y)` of Stacks 070R (2).  On sections it is
restriction along base change: `(f_{small, *}𝒢)(U) = 𝒢(U ×_Y X)`. -/
public abbrev smallPushforward :
    SheafOfModules.{u} (structureSheaf B X.obj X.property) ⥤
      SheafOfModules.{u} (structureSheaf B Y.obj Y.property) :=
  SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)

/-- **`ε_{Y,*}(f_{small,*}(𝓕^a)) ≅ f_*𝓕`**, for `𝓕` a quasi-coherent `𝒪_X`-module and with **no
hypothesis on `f`**: restricting the direct image along `ε_a` of the associated module of `𝓕`
back to the small Zariski site of `Y` is the ordinary direct image of `𝓕`.

Two inputs, both unconditional in `f`.  The mate square
`AlgebraicGeometry.SmallEtale.restrictModuleBaseChangeIso` — the right-adjoint transpose of
Stacks 03LC (1) — identifies `ε_{Y,*} ∘ f_{small,*}` with `f_* ∘ ε_{X,*}`; and the unit of the
associated-module adjunction of `X_étale` is an isomorphism at a quasi-coherent module by
Stacks 0GN7, so `ε_{X,*}(𝓕^a) ≅ 𝓕`. -/
public def restrictModuleSmallPushforwardAssociatedModuleIso
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    (restrictModule B Y.obj Y.property).obj
        ((smallPushforward B a).obj ((associatedModule B X.obj X.property).obj 𝓕)) ≅
      (Scheme.Modules.pushforward (schemeHom B a)).obj 𝓕 :=
  (restrictModuleBaseChangeIso B a).app ((associatedModule B X.obj X.property).obj 𝓕) ≪≫
    (Scheme.Modules.pushforward (schemeHom B a)).mapIso
      (@asIso _ _ _ _ _
        (unitIsoOnQuasicoherent B X.obj X.property ⟨𝓕, inferInstance⟩)).symm

/-- **For `f` quasi-compact and quasi-separated, `ε_{Y,*}(f_{small,*}(𝓕^a))` is quasi-coherent.**
By `AlgebraicGeometry.SmallEtale.restrictModuleSmallPushforwardAssociatedModuleIso` it is
`f_*𝓕`, which is quasi-coherent by Stacks 01LC.

This is the hypothesis `h` of `AlgebraicGeometry.SmallEtale.isIso_counit` at the module
`f_{small, *}(𝓕^a)`, and it is the only one of that lemma's two hypotheses that the library can
discharge there.  It is **not** the second conjunct of Stacks 03LC (3), which asks that
`f_{small, *}(𝓕^a)` be quasi-coherent on `Y_étale` and not that its restriction to the small
Zariski site be quasi-coherent on `Y`. -/
public theorem isQuasicoherent_restrictModule_smallPushforward_associatedModule
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    SheafOfModules.IsQuasicoherent (R := Y.obj.ringCatSheaf)
      ((restrictModule B Y.obj Y.property).obj
        ((smallPushforward B a).obj ((associatedModule B X.obj X.property).obj 𝓕))) :=
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent Y.obj.ringCatSheaf)
    (restrictModuleSmallPushforwardAssociatedModuleIso B a 𝓕).symm inferInstance

/-- **The corner `(f_*𝓕)^a` of the square of Stacks 03LC (3) is quasi-coherent on `Y_étale`.**
For `f` quasi-compact and quasi-separated `f_*𝓕` is quasi-coherent by Stacks 01LC, and the
associated module of a quasi-coherent module is quasi-coherent on the small étale site by
Stacks 03DV (2).

Together with `AlgebraicGeometry.SmallEtale.associatedModuleSmallPushforwardIso` this shows that
the second conjunct of part (3), read at the module `f_{small, *}(𝓕^a)`, is *equivalent* to the
square; so neither can be deduced from the other, and the source's sections computation is
needed for one of them.  That computation is now available, in
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_smallPushforward`, so the equivalence is no
longer the end of the line. -/
public theorem isQuasicoherentOnSite_associatedModule_pushforward
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent] :
    ((associatedModule B Y.obj Y.property).obj
      ((Scheme.Modules.pushforward (schemeHom B a)).obj 𝓕)).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B Y.obj Y.property _ inferInstance

/-- **The square of Stacks 03LC part (3) at `τ = étale`, over the second conjunct of that part
read at one module.**  For `f : X ⟶ Y` quasi-compact and quasi-separated and `𝓕` a quasi-coherent
`𝒪_X`-module,

    `(f_*𝓕)^a ≅ f_{small, *}(𝓕^a)`,

**given** `hG`, that `f_{small, *}(𝓕^a)` is quasi-coherent on `Y_étale`.

The isomorphism is the counit of the associated-module adjunction of `Y_étale` at
`f_{small, *}(𝓕^a)`, precomposed with the identification
`AlgebraicGeometry.SmallEtale.restrictModuleSmallPushforwardAssociatedModuleIso` of its
restriction with `f_*𝓕`.  `AlgebraicGeometry.SmallEtale.isIso_counit` makes that counit an
isomorphism from `hG` together with
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule_smallPushforward_associatedModule`.

**No `@[stacks 03LC]` attribute is carried**, and this declaration does not prove part (3): `hG`
is a conjunct of the part, so the statement is part (3) assuming part of itself.  `hG` is
discharged in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePushforwardCartesian.lean` by
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_smallPushforward`, and
`AlgebraicGeometry.SmallEtale.associatedModuleSmallPushforwardIsoOfQcqs` there is this
isomorphism with that hypothesis supplied; it is the declaration that carries the tag. -/
public def associatedModuleSmallPushforwardIso
    [QuasiCompact (schemeHom B a)] [QuasiSeparated (schemeHom B a)]
    (𝓕 : X.obj.Modules) [𝓕.IsQuasicoherent]
    (hG : ((smallPushforward B a).obj
      ((associatedModule B X.obj X.property).obj 𝓕)).IsQuasicoherentOnSite) :
    (associatedModule B Y.obj Y.property).obj
        ((Scheme.Modules.pushforward (schemeHom B a)).obj 𝓕) ≅
      (smallPushforward B a).obj ((associatedModule B X.obj X.property).obj 𝓕) :=
  (associatedModule B Y.obj Y.property).mapIso
      (restrictModuleSmallPushforwardAssociatedModuleIso B a 𝓕).symm ≪≫
    @asIso _ _ _ _ _ (isIso_counit B Y.obj Y.property _ hG
      (isQuasicoherent_restrictModule_smallPushforward_associatedModule B a 𝓕))

end AlgebraicGeometry.SmallEtale

end
