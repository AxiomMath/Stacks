module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralPushforwardExact

/-!
# Higher direct images and an integral morphism of the base

Let `f : X ⟶ S` be a morphism of schemes and let `n` be an integer, as in the condition
`BC(f, n, q₀)` of [Stacks, Tag 0F02]. [Stacks, Tag 0F05] fixes `q ≥ 1`, assumes
`BC(f, n, q - 1)`, and considers the two commutative diagrams

```
X  ←--  X'  ←-π'-  X''  ←-h'-  Y                X'  ←------h------  Y
|f      |f'        |f''        |e       and     |f'                 |e
S  ←--  S'  ←-π-   S''  ←-g'-  T                S'  ←------g------  T
```

in which every square of the first is cartesian, `g'` is quasi-compact and quasi-separated,
`π` is integral, and the second diagram is the first one collapsed, so that `h = h' ≫ π'` and
`g = g' ≫ π`. For an abelian sheaf `F` on the small étale site of `T` annihilated by `n`, the
source asserts that if the base change map `(f')⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of the collapsed
diagram is an isomorphism, then so is the base change map
`(f'')⁻¹ R^q g'_* F ⟶ R^q h'_* e⁻¹ F` of the right-hand square of the first diagram.

The source proves this by identifying the first map with the image of the second under direct
image along `π'`, and then concluding because direct image along an integral morphism reflects
isomorphisms. This file formalizes that concluding step, with the two base change maps of
[Stacks, Tag 0F02] and all of the hypotheses of the source: direct image along the integral
morphism `π'` obtained from `π` by base change reflects isomorphisms, so the base change map of
the right-hand square is an isomorphism exactly when its image under that direct image is one.

The collapsed diagram is again of the kind the condition `BC(f, n, q₀)` speaks about: its square
is the horizontal pasting `sq₃.paste_horiz sq₂` of the two cartesian squares it is built from,
and its structure morphism `g' ≫ π` is quasi-compact and quasi-separated because an integral
morphism is affine, hence quasi-compact and separated.

## Main results

* `Stacks.EtaleCohomology.smallEtalePushforwardAb_reflectsIsomorphisms_of_isIntegralHom` —
  direct image of abelian sheaves along an integral morphism reflects isomorphisms, a
  consequence of [Stacks, Tag 04C2].
* `Stacks.EtaleCohomology.isIso_smallEtalePushforwardAb_map_iff_of_isIntegralHom` — a morphism
  of abelian sheaves on the small étale site is an isomorphism exactly when its direct image
  along an integral morphism is one.
* `Stacks.EtaleCohomology.quasiSeparated_comp_of_isIntegralHom` — the structure morphism
  `g' ≫ π` of the collapsed diagram is quasi-separated. That it is quasi-compact is found by
  instance search, an integral morphism being affine and hence quasi-compact.
* `Stacks.EtaleCohomology.isIso_pushforward_higherBaseChangeMapAb_app_iff` — the step the
  source's proof ends with: under all the hypotheses of the source, the base change map of the
  right-hand square is an isomorphism exactly when its image under direct image along `π'` is
  one. This carries no tag attribute: it is one step of the source's proof rather than the
  source's conclusion.

The conclusion of the source, **[Stacks, Tag 0F05]**, is
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_collapsed_of_bc`, which
supplies the three identifications listed under **What is assumed**, and in the stronger form of
an equivalence `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff_of_isIntegralHom`.

## Implementation notes

Both cartesian squares of the right-hand half of the first diagram are transcribed as
`IsPullback` hypotheses, and the leftmost one, `X' = X ×_S S'`, as a third; the collapsed
diagram is not a separate hypothesis, being the pasting of two of them. Quasi-compactness and
quasi-separatedness of `g'` and integrality of `π` are instance hypotheses, matching the
spelling of `Stacks.EtaleCohomology.BaseChangeHolds`. Annihilation of `F` by `n` is imposed on
every section, again as in `BaseChangeHolds`.

The ambient hypotheses `q ≥ 1`, `BC(f, n, q - 1)`, the leftmost cartesian square and the
annihilation of `F` are transcribed although the proofs here do not consume them: they are
hypotheses of the source statement, and the identifications assumed below are where the source
consumes them.

Integrality of `π'` is not a hypothesis: it is deduced from integrality of `π` and the
cartesian square `X'' = X' ×_{S'} S''`, integral morphisms being stable under base change.

## What is assumed

Three identifications the source cites or elides are needed to conclude from
`isIso_pushforward_higherBaseChangeMapAb_app_iff`;
`isIso_higherBaseChangeMapAb_app_of_isIso_collapsed_of_bc` supplies them.
Each is upstream of the source's conclusion — an identification of functors, or a commuting
square of morphisms — and none asserts that a base change map at index `q` is invertible, so
none is a piece of the conclusion.

* `h0EYP`, the identification `(f')⁻¹ π_* ≅ π'_* (f'')⁻¹` for the cartesian square
  `X'' = X' ×_{S'} S''`. This is [Stacks, Tag 0EYP], that direct image along an integral
  morphism commutes with base change, in the abelian small-étale setting. The tag is stated
  but not proved in this library, so the hypothesis is shaped as the natural isomorphism of
  functors it provides, and discharging it is a single term once it is proved.
* `hLerayBottom` and `hLerayTop`, the relative Leray identifications
  `R^q g_* ≅ π_* R^q g'_*` for `g = g' ≫ π` and `R^q h_* ≅ π'_* R^q h'_*` for `h = h' ≫ π'`,
  which hold because direct image along an integral morphism is exact, by
  [Stacks, Tag 04C2], so that `Rπ_* = π_*`. The relative Leray spectral sequence itself is
  [Stacks, Tag 0734] (equivalently [Stacks, Tag 01F6] on a space); this library has 0734 only
  for sheaves of modules, not for abelian sheaves on small étale sites.
* `hPaste`, compatibility of the base change maps of [Stacks, Tag 0F02] with those three
  identifications: the base change map of the collapsed diagram is the direct image along `π'`
  of the one of the right-hand square, read through them. This is the horizontal pasting of the
  derived base change comparison, which the source elides and which carries no tag;
  `StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeMap.lean` has
  `mate`, `derived` and `derived_fac`, but no pasting lemma.

## References

* [Stacks Project, Tag 0F05](https://stacks.math.columbia.edu/tag/0F05)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 04C2](https://stacks.math.columbia.edu/tag/04C2)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **Direct image of abelian sheaves along an integral morphism reflects isomorphisms.** By
[Stacks, Tag 04C2] it reflects injections and surjections, and a morphism of an abelian category
which is both is an isomorphism. -/
public theorem smallEtalePushforwardAb_reflectsIsomorphisms_of_isIntegralHom
    {X Y : Scheme.{u}} (π : X ⟶ Y) [IsIntegralHom π] :
    (smallEtalePushforwardAb π).ReflectsIsomorphisms := by
  have h := smallEtalePushforwardAb_properties_of_isIntegralHom π
  have hmono : (smallEtalePushforwardAb π).ReflectsMonomorphisms := h.2.2.2.2.1
  have hepi : (smallEtalePushforwardAb π).ReflectsEpimorphisms := h.2.2.2.2.2.1
  infer_instance

/-- A morphism of abelian sheaves on the small étale site of `X` is an isomorphism exactly when
its direct image along an integral morphism `π : X ⟶ Y` is one. One direction is functoriality,
the other is `smallEtalePushforwardAb_reflectsIsomorphisms_of_isIntegralHom`. -/
public theorem isIso_smallEtalePushforwardAb_map_iff_of_isIntegralHom {X Y : Scheme.{u}}
    (π : X ⟶ Y) [IsIntegralHom π] {F G : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : F ⟶ G) :
    IsIso ((smallEtalePushforwardAb π).map φ) ↔ IsIso φ := by
  have := smallEtalePushforwardAb_reflectsIsomorphisms_of_isIntegralHom π
  exact isIso_iff_of_reflects_iso φ (smallEtalePushforwardAb π)

/-- The composition of a quasi-separated morphism with an integral morphism is quasi-separated:
an integral morphism is affine, hence separated, hence quasi-separated. -/
@[ega "IV 1.2.2" "(ii), special case"]
public theorem quasiSeparated_comp_of_isIntegralHom {T S'' S' : Scheme.{u}} (g' : T ⟶ S'')
    (π : S'' ⟶ S') [QuasiSeparated g'] [IsIntegralHom π] : QuasiSeparated (g' ≫ π) := by
  have : IsSeparated π := IsSeparated.of_isAffineHom π
  infer_instance

/-- **The step the proof of [Stacks, Tag 0F05] ends with.** With `f : X ⟶ S` and `n` as in
[Stacks, Tag 0F02], let `q ≥ 1` and assume `BC(f, n, q - 1)`. Consider the commutative diagrams

```
X  ←--  X'  ←-π'-  X''  ←-h'-  Y                X'  ←------h------  Y
|f      |f'        |f''        |e       and     |f'                 |e
S  ←--  S'  ←-π-   S''  ←-g'-  T                S'  ←------g------  T
```

with all squares cartesian, `g'` quasi-compact and quasi-separated, `π` integral,
`h = h' ≫ π'` and `g = g' ≫ π`, and let `F` be an abelian sheaf on the small étale site of `T`
annihilated by `n`. Then the base change map `(f'')⁻¹ R^q g'_* F ⟶ R^q h'_* e⁻¹ F` of the
right-hand square is an isomorphism exactly when its direct image along `π'` is one.

This is the reduction the source's proof ends with, proved by way of
`isIso_smallEtalePushforwardAb_map_iff_of_isIntegralHom`, `π'` being integral as a base change
of `π`. It carries no tag attribute: it is one step of the source's proof, not the source's
conclusion, which is `isIso_higherBaseChangeMapAb_app_of_isIso_collapsed_of_bc`. -/
public theorem isIso_pushforward_higherBaseChangeMapAb_app_iff
    {X S X' S' X'' S'' Y T : Scheme.{u}} (f : X ⟶ S) (n : ℤ) (q : ℕ) (_hq : 1 ≤ q)
    (_hbc : BaseChangeHolds f n ((q : ℤ) - 1)) (s : S' ⟶ S) (p : X' ⟶ X) (f' : X' ⟶ S')
    (_sq₁ : IsPullback p f' f s) (π : S'' ⟶ S') (π' : X'' ⟶ X') (f'' : X'' ⟶ S'')
    (sq₂ : IsPullback π' f'' f' π) (g' : T ⟶ S'') (h' : Y ⟶ X'') (e : Y ⟶ T)
    (sq₃ : IsPullback h' e f'' g') [QuasiCompact g'] [QuasiSeparated g'] [IsIntegralHom π]
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (_hF : ∀ (U : T.Etale) (x : F.obj.obj (Opposite.op U)), n • x = 0) :
    IsIso ((smallEtalePushforwardAb π').map
        ((higherBaseChangeMapAb f'' g' h' e sq₃.w q).app F)) ↔
      IsIso ((higherBaseChangeMapAb f'' g' h' e sq₃.w q).app F) := by
  have : IsIntegralHom π' :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom) sq₂.flip inferInstance
  exact isIso_smallEtalePushforwardAb_map_iff_of_isIntegralHom π' _

end Stacks.EtaleCohomology

end
