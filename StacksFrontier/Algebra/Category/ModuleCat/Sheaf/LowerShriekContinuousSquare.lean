module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
import StacksCore.Tactic.StacksAttribute

/-!
# Exchange of direct image and lower shriek over a square of sites with continuous rows

Let
```
  C' --v'--> C
  ↑          ↑
  u'         u
  D' --v---> D
```
be a square of functors of sites with `v ⋙ u = u' ⋙ v'`, in which `u` and `u'` are continuous —
so that they give rise to morphisms of sites `f : Sh(C) ⟶ Sh(D)` and `f' : Sh(C') ⟶ Sh(D')` with
`f_* = u^s` and `f'_* = (u')^s` (Stacks 00X0) — and in which `v` and `v'` are continuous as well
as cocontinuous, so that they give rise to morphisms of topoi `g : Sh(D') ⟶ Sh(D)` and
`g' : Sh(C') ⟶ Sh(C)` whose inverse images `g^{-1} = v^p` and `(g')^{-1} = (v')^p` are restriction
(Stacks 00XN, Stacks 00XR).

Fix sheaves of rings `O_C` on `C` and `O_D` on `D`, let `O_{C'} = (g')^{-1} O_C` and
`O_{D'} = g^{-1} O_D` — this is condition (5) of Stacks 0FN4, and it is built into the statements
below by taking those restrictions as *the* sheaves of rings on `C'` and `D'` — and let
`f^♯ : O_D ⟶ f_* O_C` make `f` a morphism of ringed topoi. Since `g^♯` and `(g')^♯` are
identities, `g^* = g^{-1}` and `(g')^* = (g')^{-1}` on modules, which is
`Stacks.SheafOfModules.inverseImage` of Stacks 0797.

This file proves the two conclusions of Stacks 0FN4 on sheaves of modules:

* `Stacks.SheafOfModules.inverseImage_comp_pushforward_eq`: `f'_* ∘ (g')^* = g^* ∘ f_*`;
* `Stacks.SheafOfModules.pullbackCompLowerShriekIso`: `g'_! ∘ (f')^{-1} ≅ f^{-1} ∘ g_!`, for the
  lower shriek of Stacks 0797 and the pullback of Stacks 03D7.

## The commutativity hypothesis

Stacks 0FN4 assumes the square of *ringed* topoi commutes. Its content beyond `v ⋙ u = u' ⋙ v'`
is that the structure map of `f'` is the one the square forces, namely `f^♯` restricted along `v`
and read through `v ⋙ u = u' ⋙ v'`; this is `Stacks.SheafOfModules.restrictStructureMap`, and the
hypothesis `hcomm` of each result below says exactly that the given `f'^♯` is it.

## Implementation notes

The first conclusion is an equality of functors, as in the source. Both composites are
`SheafOfModules.pushforward` for one of the two sides of the square — this is
`SheafOfModules.pushforwardComp`, which is `Iso.refl` — so the only content is transporting the
structure map along `v ⋙ u = u' ⋙ v'`, which is what `pushforward_eqToHom_eq` does.

The second conclusion is a natural isomorphism rather than an equality: it is obtained from the
first by uniqueness of left adjoints, which produces a canonical isomorphism and not an equality
of functors. All four left adjoints it names are the concrete ones, and all four exist outright:
`f^{-1}` and `(f')^{-1}` are `SheafOfModules.pullback` of Stacks 03D7, whose adjunction with
`SheafOfModules.pushforward` is `SheafOfModules.pullbackPushforwardAdjunction`, and `g_!`, `g'_!`
are `Stacks.SheafOfModules.lowerShriek` of Stacks 0797, whose adjunction with the inverse image is
`Stacks.SheafOfModules.lowerShriekAdjunction`. Both constructions ask for the module sections to
live in a universe that the sites, their morphisms and the sheaves of rings fit into, and for the
target topology to admit sheafification of abelian groups; those are the `UnivLE`,
`HasWeakSheafify` and `WEqualsLocallyBijective` hypotheses of the section carrying the second
conclusion, and they are all that it assumes beyond the square.

The sheaf-level statements, for sheaves with values in an arbitrary category, are Stacks 0FN2,
`CategoryTheory.Functor.sheafPushforwardContinuous_comp_eq_and_nonempty_sheafPullbackCompIso`.

## References

* [Stacks Project, Tag 0FN4](https://stacks.math.columbia.edu/tag/0FN4)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v r v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace Stacks.SheafOfModules

section Congr

variable {X : Type*} [Category X] {Y : Type*} [Category Y] (A : Type*) [Category A]
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y)

/-- Equal continuous functors of sites restrict a sheaf to the same sheaf. -/
theorem sheafPushforwardContinuous_obj_congr {w w' : X ⥤ Y} [w.IsContinuous JX JY]
    [w'.IsContinuous JX JY] (h : w = w') (G : Sheaf JY A) :
    (w.sheafPushforwardContinuous A JX JY).obj G =
      (w'.sheafPushforwardContinuous A JX JY).obj G := by
  subst h
  rfl

/-- Reading a structure map of sheaves of rings through an equality of continuous functors of
sites does not change the pushforward of sheaves of modules it induces. -/
theorem pushforward_eqToHom_eq {w w' : X ⥤ Y} [w.IsContinuous JX JY] [w'.IsContinuous JX JY]
    (h : w = w') {S : Sheaf JX RingCat.{r}} {R : Sheaf JY RingCat.{r}}
    (φ : S ⟶ (w.sheafPushforwardContinuous RingCat.{r} JX JY).obj R)
    (h' : (w.sheafPushforwardContinuous RingCat.{r} JX JY).obj R =
      (w'.sheafPushforwardContinuous RingCat.{r} JX JY).obj R) :
    _root_.SheafOfModules.pushforward.{v} (F := w') (φ ≫ eqToHom h') =
      _root_.SheafOfModules.pushforward.{v} (F := w) φ := by
  subst h
  rw [show h' = rfl from rfl, eqToHom_refl, Category.comp_id]

end Congr

section Square

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (J' : GrothendieckTopology C')
  (J : GrothendieckTopology C) (K' : GrothendieckTopology D') (K : GrothendieckTopology D)
  (u : D ⥤ C) (u' : D' ⥤ C') (v : D' ⥤ D) (v' : C' ⥤ C) [u.IsContinuous K J]
  [u'.IsContinuous K' J'] [v.IsContinuous K' K] [v.IsCocontinuous K' K] [v'.IsContinuous J' J]
  [v'.IsCocontinuous J' J] (OC : Sheaf J RingCat.{r}) (OD : Sheaf K RingCat.{r})
  (fSharp : OD ⟶ (u.sheafPushforwardContinuous RingCat.{r} K J).obj OC)

/-- The structure map that a commutative square of ringed topoi forces on `f'`: the structure map
`f^♯ : O_D ⟶ f_* O_C` of `f`, restricted along `v` and read through `v ⋙ u = u' ⋙ v'` as a map
`O_{D'} = g^{-1} O_D ⟶ f'_* O_{C'}` with `O_{C'} = (g')^{-1} O_C`. -/
def restrictStructureMap (hsq : v ⋙ u = u' ⋙ v') :
    inverseImageRing K' K v OD ⟶
      (u'.sheafPushforwardContinuous RingCat.{r} K' J').obj (inverseImageRing J' J v' OC) :=
  haveI : (v ⋙ u).IsContinuous K' J := Functor.isContinuous_comp v u K' K J
  haveI : (u' ⋙ v').IsContinuous K' J := Functor.isContinuous_comp u' v' K' J' J
  (v.sheafPushforwardContinuous RingCat.{r} K' K).map fSharp ≫
    eqToHom (sheafPushforwardContinuous_obj_congr RingCat.{r} K' J hsq OC)

variable (f'Sharp : inverseImageRing K' K v OD ⟶
  (u'.sheafPushforwardContinuous RingCat.{r} K' J').obj (inverseImageRing J' J v' OC))

/-- **Stacks 0FN4**, first conclusion. For a commutative square of ringed topoi as in the module
docstring — `u`, `u'` continuous giving `f`, `f'`, the functors `v`, `v'` continuous as well as
cocontinuous giving `g`, `g'`, `v ⋙ u = u' ⋙ v'`, and `g^{-1} O_D = O_{D'}`,
`(g')^{-1} O_C = O_{C'}` — we have `f'_* ∘ (g')^* = g^* ∘ f_*` on sheaves of modules. Both sides
are restriction along one of the two sides of the square together with restriction of scalars
along the corresponding composite structure map, and the square says those agree. -/
@[stacks 0FN4 "first conclusion: `f'_* ∘ (g')^* = g^* ∘ f_*` on sheaves of modules, for a
  commutative square of ringed topoi whose horizontal functors `u`, `u'` are continuous and whose
  vertical functors `v`, `v'` are continuous as well as cocontinuous, with
  `g^{-1} O_D = O_{D'}` and `(g')^{-1} O_C = O_{C'}`"]
theorem inverseImage_comp_pushforward_eq (hsq : v ⋙ u = u' ⋙ v')
    (hcomm : f'Sharp = restrictStructureMap J' J K' K u u' v v' OC OD fSharp hsq) :
    inverseImage.{v} J' J v' OC ⋙ _root_.SheafOfModules.pushforward.{v} f'Sharp =
      _root_.SheafOfModules.pushforward.{v} fSharp ⋙ inverseImage.{v} K' K v OD := by
  have : (v ⋙ u).IsContinuous K' J := Functor.isContinuous_comp v u K' K J
  have : (u' ⋙ v').IsContinuous K' J := Functor.isContinuous_comp u' v' K' J' J
  subst hcomm
  exact pushforward_eqToHom_eq K' J hsq _ _

section LowerShriek

variable [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{u₁, v}] [UnivLE.{v₂, v}] [UnivLE.{v₃, v}]
  [UnivLE.{u₃, v}] [UnivLE.{v₄, v}] [UnivLE.{u₄, v}]
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **Stacks 0FN4**, second conclusion. In the situation of
`Stacks.SheafOfModules.inverseImage_comp_pushforward_eq` we have
`g'_! ∘ (f')^{-1} ≅ f^{-1} ∘ g_!`, where `g_!` and `g'_!` are the lower shriek
`Stacks.SheafOfModules.lowerShriek` of Stacks 0797 and `f^{-1}`, `(f')^{-1}` are the pullbacks
`SheafOfModules.pullback` of Stacks 03D7. The composite `g'_! ∘ (f')^{-1}` is left adjoint to
`f'_* ∘ (g')^*` and `f^{-1} ∘ g_!` is left adjoint to `g^* ∘ f_*`; by the first conclusion those
two right adjoints are the same functor, so uniqueness of left adjoints identifies the two
composites.

Nothing beyond the square is assumed: the four adjunctions are
`Stacks.SheafOfModules.lowerShriekAdjunction` of Stacks 0797 and
`SheafOfModules.pullbackPushforwardAdjunction` of Stacks 03D7, which the `UnivLE`,
`HasWeakSheafify` and `WEqualsLocallyBijective` hypotheses of this section make available. -/
@[stacks 0FN4 "second conclusion: `g'_! ∘ (f')⁻¹ ≅ f⁻¹ ∘ g_!` on sheaves of modules, for a
  commutative square of ringed topoi whose horizontal functors `u`, `u'` are continuous and whose
  vertical functors `v`, `v'` are continuous as well as cocontinuous, with
  `g^{-1} O_D = O_{D'}` and `(g')^{-1} O_C = O_{C'}`; a canonical isomorphism rather than an
  equality, uniqueness of left adjoints giving no more. `g_!` and `g'_!` are the lower shriek of
  Stacks 0797 and `f⁻¹`, `(f')⁻¹` the pullback of Stacks 03D7; the existence of all four is
  proved, not assumed."]
def pullbackCompLowerShriekIso (hsq : v ⋙ u = u' ⋙ v')
    (hcomm : f'Sharp = restrictStructureMap J' J K' K u u' v v' OC OD fSharp hsq) :
    _root_.SheafOfModules.pullback.{v} f'Sharp ⋙ lowerShriek.{v} J' J v' OC ≅
      lowerShriek.{v} K' K v OD ⋙ _root_.SheafOfModules.pullback.{v} fSharp :=
  ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} f'Sharp).comp
        (lowerShriekAdjunction.{v} J' J v' OC)).leftAdjointUniq
    (((lowerShriekAdjunction.{v} K' K v OD).comp
          (_root_.SheafOfModules.pullbackPushforwardAdjunction.{v} fSharp)).ofNatIsoRight
      (eqToIso (inverseImage_comp_pushforward_eq.{v} J' J K' K u u' v v' OC OD fSharp f'Sharp hsq
        hcomm)).symm)

end LowerShriek

end Square

end Stacks.SheafOfModules

end
