module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InverseImageCocontinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms
import StacksCore.Tactic.StacksAttribute

/-!
# Exchange of direct image and lower shriek over a square of sites with cocontinuous columns

Let
```
  C' --v'--> C
  |          |
  u'         u
  v          v
  D' --v---> D
```
be a square of functors of sites with `u' ⋙ v = v' ⋙ u`, in which all four functors are
cocontinuous — so that they give rise to morphisms of topoi `f : Sh(C) ⟶ Sh(D)`,
`f' : Sh(C') ⟶ Sh(D')`, `g : Sh(D') ⟶ Sh(D)` and `g' : Sh(C') ⟶ Sh(C)` with `f_* = {}_su` and
`f'_* = {}_su'` (Stacks 00XO) — and in which `v` and `v'` are continuous as well as cocontinuous,
so that the inverse images `g^{-1} = v^p` and `(g')^{-1} = (v')^p` are restriction (Stacks 00XR).

Fix sheaves of rings `O_C` on `C` and `O_D` on `D` and let `O_{C'} = (g')^{-1} O_C`,
`O_{D'} = g^{-1} O_D`. This is condition (5) of Stacks 0FN3, and it is built into the statements
below by taking those restrictions as *the* sheaves of rings on `C'` and `D'`. Since `g^♯` and
`(g')^♯` are then identities, `g^* = g^{-1}` and `(g')^* = (g')^{-1}` on modules, which is
`Stacks.SheafOfModules.inverseImage` of Stacks 0797, and `g_!`, `g'_!` are the left adjoints
`Stacks.SheafOfModules.lowerShriek` of that tag.

Assume finally that for every object `V'` of `D'` the comparison functor
```
  {}^{u'}_{V'} I ⥤ {}^u_{v(V')} I,   (U', ψ) ↦ (v'(U'), v(ψ) : u(v'(U')) = v(u'(U')) ⟶ v(V')),
```
on the categories of Section 00XF is cofinal, i.e. final; this is condition (4), and it is the
hypothesis under which the two direct images exchange with the two restrictions on sheaves with
values in any category (Stacks 0FN1).

This file proves the two conclusions of Stacks 0FN3 on sheaves of modules, for the canonical
direct images of `Stacks.SheafOfModules.pushforwardCocontinuous`:

* `Stacks.SheafOfModules.inverseImageCompCocontinuousPushforwardOfIso`:
  `f'_* ∘ (g')^* ≅ g^* ∘ f_*`;
* `Stacks.SheafOfModules.lowerShriekCompLeftAdjointOfIso`:
  `g'_! ∘ (f')^{-1} ≅ f^{-1} ∘ g_!`.

Both are constructions, not mere existence statements;
`Stacks.SheafOfModules.nonempty_inverseImage_comp_cocontinuousPushforwardOf_iso` is the first of
them asserted through `Nonempty`, for consumers that need no more.

Both are also proved for an arbitrary pair of functors on sheaves of modules whose underlying
sheaves of abelian groups are the two direct images — a `CocontinuousPushforward` for `u` and for
`u'` — under the hypothesis that the sheaf-level comparison of Stacks 0FN1 is linear over
`O_{D'}`; those are the general statements
`Stacks.SheafOfModules.nonempty_inverseImage_comp_cocontinuousPushforward_iso` and
`Stacks.SheafOfModules.nonempty_lowerShriek_comp_leftAdjoint_iso`, of which the two above are the
case of the canonical direct images, where that hypothesis is a theorem.

## Main definitions

* `Stacks.SheafOfModules.CocontinuousPushforward`: a functor on sheaves of modules presenting the
  direct image along a morphism of topoi given by a cocontinuous functor of sites, that is, one
  whose underlying sheaf of abelian groups is the direct image `{}_su`.
* `Stacks.SheafOfModules.CocontinuousPushforward.of`: the canonical such functor, for a structure
  map `f^♯ : O_D ⟶ {}_su O_C` of sheaves of rings.

## Main results

* `Stacks.SheafOfModules.pushforward_comp_toSheaf` and
  `Stacks.SheafOfModules.inverseImage_comp_toSheaf`: on underlying sheaves of abelian groups,
  the pushforward of sheaves of modules along a continuous functor of sites — in particular the
  inverse image `g^* = g^{-1}` of Stacks 0797 — is restriction.
* `Stacks.SheafOfModules.toSheaf_comp_inverseImage_comp_cocontinuousPushforward` and
  `Stacks.SheafOfModules.toSheaf_comp_cocontinuousPushforward_comp_inverseImage`: the two
  composites of the first conclusion are, on underlying sheaves of abelian groups, the two
  composites of Stacks 0FN1.

## Implementation notes

`SheafOfModules.pushforward` is the direct image for a morphism of sites, that is, restriction
along a continuous functor, whereas the direct image along a cocontinuous `u` has the direct
image `{}_su` of Stacks 00XO for its underlying sheaf of abelian groups and carries the
`O_D`-action that the structure map `f^♯ : O_D ⟶ {}_su O_C` cuts out of the `{}_su O_C`-action.
That functor is `Stacks.SheafOfModules.pushforwardCocontinuous`, and `CocontinuousPushforward`
is the weaker, structural record of what the two conclusions actually use: a functor on sheaves
of modules together with the identification of its underlying sheaf of abelian groups with
`{}_su`. The general statements take such a datum for `f` and for `f'`;
`CocontinuousPushforward.of` exhibits the canonical one.

With `f_*` and `f'_*` so presented, the two composites of the first conclusion agree on
underlying sheaves of abelian groups by Stacks 0FN1 and condition (4), which is what the two
`toSheaf_comp_*` results reduce them to. What remains is that the comparison is `O_{D'}`-linear,
and that is the hypothesis `hlinear` of the two general statements: it asks that the sheaf-level
comparison of Stacks 0FN1 be the underlying map of a morphism of the two functors on sheaves of
modules. Such a morphism is then automatically invertible, the forgetful functor to sheaves of
abelian groups reflecting isomorphisms, and that is what turns the hypothesis into the first
conclusion. The two equalities of functors along which the comparison is read are quantified
over inside `hlinear`; they are the two `toSheaf_comp_*` results, and being equalities of
functors they contribute nothing beyond the statement that the comparison has the right source
and target.

For the canonical direct images `hlinear` is a theorem: the module structures of
`pushforwardCocontinuous` and the base-change transformation of right Kan extensions are both
characterised on the legs of the limit cones that compute `{}_su` and `{}_su'`, and base change
matches those legs through the comparison functor of the square
(`Stacks.SheafOfModules.ranSMul_squareComparison`). The two tagged statements are therefore the
canonical case, where nothing beyond the square, condition (4) and the structure map `f^♯` is
assumed. Condition (1), that `f_*` and `f'_*` have left adjoints, is a theorem for the canonical
direct images: `Stacks.SheafOfModules.isRightAdjoint_pushforwardCocontinuous_of_hasWeakSheafify`
exhibits the inverse image `f^* G = O_C ⊗_{f^{-1}O_D} f^{-1}G` as a left adjoint and
`Stacks.SheafOfModules.inverseImageCocontinuousAdjunction` names the adjunction, so nothing about
it is assumed either.

Both conclusions are natural isomorphisms rather than equalities of functors, as in Stacks 0FN1:
the sheaf-level comparison of that tag is a base-change isomorphism of right Kan extensions and
not an equality, and the second conclusion is obtained from the first by uniqueness of left
adjoints, which again produces an isomorphism only. For the canonical direct images both
isomorphisms are produced as data: the first is the inverse of
`Stacks.SheafOfModules.squareComparison` and the second is the comparison of two left adjoints of
one functor. The general statements, whose `hlinear` only asserts that an `O_{D'}`-linear
comparison exists, can give no more than `Nonempty`.

The existence of the left adjoints `f^{-1}` and `(f')^{-1}` of `f_*` and `f'_*` is condition (1):
a cocontinuous functor gives rise to a morphism of ringed topoi, and a morphism of ringed topoi
is the adjoint pair. For the canonical direct images it is constructed and not assumed, by
`Stacks.SheafOfModules.inverseImageCocontinuousAdjunction`: the left adjoint is
`Stacks.SheafOfModules.inverseImageCocontinuous`, the left adjoint of the direct image, and it is
isomorphic to restriction of the underlying presheaf of modules along `u`, base change along the
ring map `u^{-1}O_D ⟶ O_C` adjoint to `f^♯`, and sheafification — the functor that
`Stacks.SheafOfModules.isRightAdjoint_pushforwardCocontinuous_of_hasWeakSheafify` exhibits as a
left adjoint under exactly the hypotheses listed below. `SheafOfModules.pullback` of
Stacks 03D7 is the corresponding construction for a *continuous* functor of sites, where `f_*`
is restriction rather than a right Kan extension, and does not apply here; what replaces it is
the right-Kan-extension adjunction of
`Stacks.SheafOfModules.pushforward₀RanPushforwardAdjunction`, lifted from abelian presheaves to
presheaves of modules. The left adjoints `g_!` and `g'_!` of `g^*` and `(g')^*` are likewise
constructed: they are the concrete `Stacks.SheafOfModules.lowerShriek` of Stacks 0797. All four
are available under the `UnivLE`, `HasWeakSheafify` and `WEqualsLocallyBijective` hypotheses of
the sections that state the second conclusion, which are conditions on the sites and the
universes and not on the existence of any adjoint. The general statements
`nonempty_lowerShriek_comp_leftAdjoint_iso` and
`nonempty_inverseImage_comp_cocontinuousPushforward_iso` still take `IsRightAdjoint` hypotheses,
there being no reason for an arbitrary `CocontinuousPushforward` to have a left adjoint.

The sheaf-level statement, for sheaves with values in an arbitrary category, is Stacks 0FN1, that
is,
`nonempty_sheafPushforwardContinuousCompCocontinuousIso_and_leftAdjointCompPullbackIso_of_final`
in the namespace `CategoryTheory.Functor`.

## References

* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
-/

@[expose] public noncomputable section

open CategoryTheory

universe v r v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

namespace Stacks.SheafOfModules

section Forget

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
  {JX : GrothendieckTopology X} {JY : GrothendieckTopology Y} (w : X ⥤ Y)
  [w.IsContinuous JX JY] {S : Sheaf JX RingCat.{r}} {R : Sheaf JY RingCat.{r}}

/-- The underlying sheaf of abelian groups of `SheafOfModules.pushforward` along a continuous
functor of sites `w` is restriction along `w`: the pushforward acts on the underlying presheaf of
abelian groups by precomposition with `w.op`, and the restriction of scalars that accompanies it
leaves that presheaf alone. -/
theorem pushforward_comp_toSheaf
    (φ : S ⟶ (w.sheafPushforwardContinuous RingCat.{r} JX JY).obj R) :
    _root_.SheafOfModules.pushforward.{v} φ ⋙ _root_.SheafOfModules.toSheaf.{v} S =
      _root_.SheafOfModules.toSheaf.{v} R ⋙
        w.sheafPushforwardContinuous AddCommGrpCat.{v} JX JY :=
  rfl

/-- The underlying sheaf of abelian groups of the inverse image `g^* = g^{-1}` of sheaves of
modules along a continuous and cocontinuous functor of sites `w` is restriction along `w`. -/
theorem inverseImage_comp_toSheaf [w.IsCocontinuous JX JY] (O : Sheaf JY RingCat.{r}) :
    inverseImage.{v} JX JY w O ⋙
        _root_.SheafOfModules.toSheaf.{v} (inverseImageRing JX JY w O) =
      _root_.SheafOfModules.toSheaf.{v} O ⋙
        w.sheafPushforwardContinuous AddCommGrpCat.{v} JX JY :=
  pushforward_comp_toSheaf w (structureMap JX JY w O)

end Forget

section CocontinuousPushforward

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y) (w : X ⥤ Y)
  [w.IsCocontinuous JX JY]
  [∀ G : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension G]

/-- The **direct image of sheaves of modules** along the morphism of topoi `f` attached to a
cocontinuous functor of sites `w : X ⥤ Y` (Stacks 00XO): a functor
`f_* : Mod(O_X) ⥤ Mod(O_Y)` whose underlying sheaf of abelian groups is the direct image
`{}_sw = f_*` of the underlying sheaf of abelian groups, that is,
`CategoryTheory.Functor.sheafPushforwardCocontinuous`.

Only the underlying sheaf of abelian groups is prescribed; the `O_Y`-action on `f_* M`, which a
structure map `f^♯ : O_Y ⟶ {}_sw O_X` cuts out of the `{}_sw O_X`-action, is left
unconstrained. -/
structure CocontinuousPushforward (OX : Sheaf JX RingCat.{r}) (OY : Sheaf JY RingCat.{r}) where
  /-- The direct image on sheaves of modules. -/
  functor : _root_.SheafOfModules.{v} OX ⥤ _root_.SheafOfModules.{v} OY
  /-- Its underlying sheaf of abelian groups is the direct image `{}_sw` along `w`. -/
  toSheaf_comp : functor ⋙ _root_.SheafOfModules.toSheaf.{v} OY =
    _root_.SheafOfModules.toSheaf.{v} OX ⋙
      w.sheafPushforwardCocontinuous AddCommGrpCat.{v} JX JY

/-- The **canonical** direct image of sheaves of modules along the morphism of topoi `f` attached
to a cocontinuous functor of sites `w`, for a structure map `f^♯ : O_Y ⟶ {}_sw O_X` of sheaves of
rings: `Stacks.SheafOfModules.pushforwardCocontinuous`, whose underlying sheaf of abelian groups
is `{}_sw` on the nose and whose `O_Y`-action is the one that `f^♯` cuts out of the
`{}_sw O_X`-action. -/
def CocontinuousPushforward.of
    [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
    {OX : Sheaf JX RingCat.{r}} {OY : Sheaf JY RingCat.{r}}
    (fSharp : OY ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj OX) :
    CocontinuousPushforward.{v} JX JY w OX OY where
  functor := pushforwardCocontinuous.{v} w fSharp
  toSheaf_comp := pushforwardCocontinuous_comp_toSheaf.{v} w fSharp

/-- **The canonical direct image of sheaves of modules along a cocontinuous functor of sites has
a left adjoint**, namely its inverse image `f^* G = O_X ⊗_{f^{-1}O_Y} f^{-1}G`: this is
`Stacks.SheafOfModules.isRightAdjoint_pushforwardCocontinuous_of_hasWeakSheafify`, restated at
the projection `CocontinuousPushforward.functor` so that instance search finds it there. It is
condition (1) of Stacks 0FN3, and it is a theorem rather than a hypothesis — the hypotheses here
are on the sites and the universes only, and in particular ask nothing of the two categories of
modules, which is why the special adjoint functor theorem of
`Stacks.SheafOfModules.isRightAdjoint_pushforwardCocontinuous` does not serve. -/
instance isRightAdjoint_cocontinuousPushforwardOf
    [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
    {OX : Sheaf JX RingCat.{r}} {OY : Sheaf JY RingCat.{r}}
    (fSharp : OY ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj OX)
    [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{u₁, v}]
    [HasWeakSheafify JX AddCommGrpCat.{v}] [JX.WEqualsLocallyBijective AddCommGrpCat.{v}] :
    (CocontinuousPushforward.of.{v} JX JY w fSharp).functor.IsRightAdjoint :=
  inferInstanceAs (pushforwardCocontinuous.{v} w fSharp).IsRightAdjoint

end CocontinuousPushforward

section Square

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] (J' : GrothendieckTopology C')
  (J : GrothendieckTopology C) (K' : GrothendieckTopology D') (K : GrothendieckTopology D)
  (u' : C' ⥤ D') (u : C ⥤ D) (v' : C' ⥤ C) (v : D' ⥤ D) [u.IsCocontinuous J K]
  [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v.IsCocontinuous K' K]
  [v'.IsContinuous J' J] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{v}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{v}, u'.op.HasPointwiseRightKanExtension G]
  (OC : Sheaf J RingCat.{r}) (OD : Sheaf K RingCat.{r})

omit [v.IsCocontinuous K' K] in
/-- On underlying sheaves of abelian groups, `f'_* ∘ (g')^*` is the composite
`{}_su' ∘ (v')^p` of Stacks 0FN1: restriction along `v'` by `inverseImage_comp_toSheaf`, then
the direct image along `u'` by the defining property of a `CocontinuousPushforward`. -/
theorem toSheaf_comp_inverseImage_comp_cocontinuousPushforward
    (F' : CocontinuousPushforward.{v} J' K' u' (inverseImageRing J' J v' OC)
      (inverseImageRing K' K v OD)) :
    (inverseImage.{v} J' J v' OC ⋙ F'.functor) ⋙
        _root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD) =
      _root_.SheafOfModules.toSheaf.{v} OC ⋙
        (v'.sheafPushforwardContinuous AddCommGrpCat.{v} J' J ⋙
          u'.sheafPushforwardCocontinuous AddCommGrpCat.{v} J' K') := by
  rw [Functor.assoc, F'.toSheaf_comp, ← Functor.assoc, inverseImage_comp_toSheaf]
  rfl

/-- On underlying sheaves of abelian groups, `g^* ∘ f_*` is the composite `v^p ∘ {}_su` of
Stacks 0FN1: the direct image along `u` by the defining property of a
`CocontinuousPushforward`, then restriction along `v` by `inverseImage_comp_toSheaf`. -/
theorem toSheaf_comp_cocontinuousPushforward_comp_inverseImage
    (F : CocontinuousPushforward.{v} J K u OC OD) :
    (F.functor ⋙ inverseImage.{v} K' K v OD) ⋙
        _root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD) =
      _root_.SheafOfModules.toSheaf.{v} OC ⋙
        (u.sheafPushforwardCocontinuous AddCommGrpCat.{v} J K ⋙
          v.sheafPushforwardContinuous AddCommGrpCat.{v} K' K) := by
  rw [Functor.assoc, inverseImage_comp_toSheaf, ← Functor.assoc, F.toSheaf_comp]
  rfl

open Functor in
/-- **Stacks 0FN3**, first conclusion. For a commutative square of ringed topoi as in the module
docstring — all four functors cocontinuous giving `f`, `f'`, `g`, `g'`, the functors `v`, `v'`
continuous as well as cocontinuous, `u' ⋙ v = v' ⋙ u`, the comparison functors
`{}^{u'}_{V'} I ⥤ {}^u_{v(V')} I` all cofinal, and `g^{-1} O_D = O_{D'}`,
`(g')^{-1} O_C = O_{C'}` — we have `f'_* ∘ (g')^* ≅ g^* ∘ f_*` on sheaves of modules.

On underlying sheaves of abelian groups the two composites are the two composites of Stacks
0FN1, which cofinality makes isomorphic; the hypothesis `hlinear` is that that isomorphism is
the underlying map of a morphism of the two functors on sheaves of modules, i.e. that it is
linear over `O_{D'}`. Such a morphism is then invertible, since the forgetful functor from
sheaves of modules to sheaves of abelian groups reflects isomorphisms.

For the canonical direct images of `Stacks.SheafOfModules.pushforwardCocontinuous`, which
`Stacks.SheafOfModules.CocontinuousPushforward.of` packages as a `CocontinuousPushforward`, the
hypothesis `hlinear` is a theorem, and the tag is carried by the resulting unconditional form
`Stacks.SheafOfModules.inverseImageCompCocontinuousPushforwardOfIso`, which exhibits the
isomorphism rather than asserting that one exists. -/
theorem nonempty_inverseImage_comp_cocontinuousPushforward_iso
    (F : CocontinuousPushforward.{v} J K u OC OD)
    (F' : CocontinuousPushforward.{v} J' K' u' (inverseImageRing J' J v' OC)
      (inverseImageRing K' K v OD)) (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final)
    (hlinear : ∀ σ : v'.sheafPushforwardContinuous AddCommGrpCat.{v} J' J ⋙
          u'.sheafPushforwardCocontinuous AddCommGrpCat.{v} J' K' ≅
        u.sheafPushforwardCocontinuous AddCommGrpCat.{v} J K ⋙
          v.sheafPushforwardContinuous AddCommGrpCat.{v} K' K,
      ∀ e' : (inverseImage.{v} J' J v' OC ⋙ F'.functor) ⋙
          _root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD) =
        _root_.SheafOfModules.toSheaf.{v} OC ⋙
          (v'.sheafPushforwardContinuous AddCommGrpCat.{v} J' J ⋙
            u'.sheafPushforwardCocontinuous AddCommGrpCat.{v} J' K'),
      ∀ e : (F.functor ⋙ inverseImage.{v} K' K v OD) ⋙
          _root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD) =
        _root_.SheafOfModules.toSheaf.{v} OC ⋙
          (u.sheafPushforwardCocontinuous AddCommGrpCat.{v} J K ⋙
            v.sheafPushforwardContinuous AddCommGrpCat.{v} K' K),
      ∃ θ : inverseImage.{v} J' J v' OC ⋙ F'.functor ⟶
          F.functor ⋙ inverseImage.{v} K' K v OD,
        ∀ M, (_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD)).map (θ.app M) =
          eqToHom (Functor.congr_obj e' M) ≫
            σ.hom.app ((_root_.SheafOfModules.toSheaf.{v} OC).obj M) ≫
              eqToHom (Functor.congr_obj e M).symm) :
    Nonempty (inverseImage.{v} J' J v' OC ⋙ F'.functor ≅
      F.functor ⋙ inverseImage.{v} K' K v OD) := by
  obtain ⟨σ⟩ :=
    (nonempty_sheafPushforwardContinuousCompCocontinuousIso_and_leftAdjointCompPullbackIso_of_final
      AddCommGrpCat.{v} J' J K' K u' u v' v hsq hfinal).1
  obtain ⟨θ, hθ⟩ := hlinear σ
    (toSheaf_comp_inverseImage_comp_cocontinuousPushforward J' J K' K u' v' v OC OD F')
    (toSheaf_comp_cocontinuousPushforward_comp_inverseImage J K' K u v OC OD F)
  have : ∀ M, IsIso (θ.app M) := fun M ↦ by
    have : IsIso ((_root_.SheafOfModules.toSheaf.{v}
        (inverseImageRing K' K v OD)).map (θ.app M)) := by
      rw [hθ M]; infer_instance
    exact isIso_of_reflects_iso (θ.app M)
      (_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD))
  have : IsIso θ := NatIso.isIso_of_isIso_app θ
  exact ⟨asIso θ⟩


section LowerShriek

variable [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{u₁, v}] [UnivLE.{v₂, v}] [UnivLE.{v₃, v}]
  [UnivLE.{u₃, v}] [UnivLE.{v₄, v}]
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **Stacks 0FN3**, second conclusion. In the situation of
`Stacks.SheafOfModules.nonempty_inverseImage_comp_cocontinuousPushforward_iso`, and assuming in
addition that the two direct images `f_*` and `f'_*` of sheaves of modules have left adjoints
`f^{-1}` and `(f')^{-1}` — which is condition (1), a cocontinuous functor giving rise to a
morphism of topoi — we have `g'_! ∘ (f')^{-1} ≅ f^{-1} ∘ g_!`. The composite
`g'_! ∘ (f')^{-1}` is left adjoint to `f'_* ∘ (g')^*` and `f^{-1} ∘ g_!` is left adjoint to
`g^* ∘ f_*`; by the first conclusion those two right adjoints are isomorphic, so uniqueness of
left adjoints identifies the two composites. The left adjoints `g_!` and `g'_!` of `g^*` and
`(g')^*` are the lower shriek of Stacks 0797.

For the canonical direct images the hypothesis `hlinear` is a theorem, and the tag is carried by
the resulting form `Stacks.SheafOfModules.lowerShriekCompLeftAdjointOfIso`, which exhibits the
isomorphism rather than asserting that one exists. -/
theorem nonempty_lowerShriek_comp_leftAdjoint_iso
    (F : CocontinuousPushforward.{v} J K u OC OD)
    (F' : CocontinuousPushforward.{v} J' K' u' (inverseImageRing J' J v' OC)
      (inverseImageRing K' K v OD)) [F.functor.IsRightAdjoint] [F'.functor.IsRightAdjoint]
    (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final)
    (hlinear : ∀ σ : v'.sheafPushforwardContinuous AddCommGrpCat.{v} J' J ⋙
          u'.sheafPushforwardCocontinuous AddCommGrpCat.{v} J' K' ≅
        u.sheafPushforwardCocontinuous AddCommGrpCat.{v} J K ⋙
          v.sheafPushforwardContinuous AddCommGrpCat.{v} K' K,
      ∀ e' : (inverseImage.{v} J' J v' OC ⋙ F'.functor) ⋙
          _root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD) =
        _root_.SheafOfModules.toSheaf.{v} OC ⋙
          (v'.sheafPushforwardContinuous AddCommGrpCat.{v} J' J ⋙
            u'.sheafPushforwardCocontinuous AddCommGrpCat.{v} J' K'),
      ∀ e : (F.functor ⋙ inverseImage.{v} K' K v OD) ⋙
          _root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD) =
        _root_.SheafOfModules.toSheaf.{v} OC ⋙
          (u.sheafPushforwardCocontinuous AddCommGrpCat.{v} J K ⋙
            v.sheafPushforwardContinuous AddCommGrpCat.{v} K' K),
      ∃ θ : inverseImage.{v} J' J v' OC ⋙ F'.functor ⟶
          F.functor ⋙ inverseImage.{v} K' K v OD,
        ∀ M, (_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD)).map (θ.app M) =
          eqToHom (Functor.congr_obj e' M) ≫
            σ.hom.app ((_root_.SheafOfModules.toSheaf.{v} OC).obj M) ≫
              eqToHom (Functor.congr_obj e M).symm) :
    Nonempty (F'.functor.leftAdjoint ⋙ lowerShriek.{v} J' J v' OC ≅
      lowerShriek.{v} K' K v OD ⋙ F.functor.leftAdjoint) := by
  obtain ⟨σ⟩ : Nonempty (inverseImage.{v} J' J v' OC ⋙ F'.functor ≅
      F.functor ⋙ inverseImage.{v} K' K v OD) :=
    nonempty_inverseImage_comp_cocontinuousPushforward_iso (F := F) (F' := F') (hsq := hsq)
      (hfinal := hfinal) (hlinear := hlinear)
  exact ⟨((Adjunction.ofIsRightAdjoint F'.functor).comp
      (lowerShriekAdjunction.{v} J' J v' OC)).leftAdjointUniq
    (((lowerShriekAdjunction.{v} K' K v OD).comp
      (Adjunction.ofIsRightAdjoint F.functor)).ofNatIsoRight σ.symm)⟩


end LowerShriek

section Canonical

variable [∀ G : Cᵒᵖ ⥤ RingCat.{r}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G]


/-- **Stacks 0FN3**, first conclusion, for the canonical direct images. For a commutative square
of ringed topoi as in the module docstring — all four functors cocontinuous giving `f`, `f'`,
`g`, `g'`, the functors `v`, `v'` continuous as well as cocontinuous, `u' ⋙ v = v' ⋙ u`, the
comparison functors `{}^{u'}_{V'} I ⥤ {}^u_{v(V')} I` all cofinal, and `g^{-1} O_D = O_{D'}`,
`(g')^{-1} O_C = O_{C'}` — we have `f'_* ∘ (g')^* ≅ g^* ∘ f_*` on sheaves of modules.

The direct images of sheaves of modules are the canonical ones: `f_*` is
`Stacks.SheafOfModules.pushforwardCocontinuous` for the given structure map
`f^♯ : O_D ⟶ {}_su O_C`, and `f'_*` is the same construction for the structure map
`(f')^♯ : O_{D'} ⟶ {}_su' O_{C'}` that `f^♯` induces by restriction along `v` and base change.
For these the linearity hypothesis of
`Stacks.SheafOfModules.nonempty_inverseImage_comp_cocontinuousPushforward_iso` is a theorem,
`Stacks.SheafOfModules.ranSMul_squareComparison`, so no hypothesis beyond the square, the
cofinality and the structure map remains, and the isomorphism itself is available: it is the
inverse of `Stacks.SheafOfModules.squareComparison`. -/
@[stacks 0FN3 "first conclusion: `f'_* ∘ (g')^* ≅ g^* ∘ f_*` on sheaves of modules, for a
  commutative square of ringed topoi whose four functors `u`, `u'`, `v`, `v'` are cocontinuous,
  with `v`, `v'` continuous as well, with the comparison functors of the index categories of
  Section 00XF cofinal, and with `g^{-1} O_D = O_{D'}`, `(g')^{-1} O_C = O_{C'}`. An isomorphism
  rather than an equality, the sheaf-level comparison of Stacks 0FN1 being a base change of
  right Kan extensions. The direct images of sheaves of modules along the cocontinuous `u` and
  `u'` are the canonical ones attached to the structure map `f^♯ : O_D → {}_su O_C` of the
  morphism of ringed topoi, whose underlying sheaves of abelian groups are `{}_su`, `{}_su'`."]
def inverseImageCompCocontinuousPushforwardOfIso
    (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)
    (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final) :
    inverseImage.{v} J' J v' OC ⋙
        (CocontinuousPushforward.of.{v} J' K' u'
          (structureMapSquare (J' := J') (K' := K') fSharp hsq)).functor ≅
      (CocontinuousPushforward.of.{v} J K u fSharp).functor ⋙ inverseImage.{v} K' K v OD :=
  inverseImageCompPushforwardCocontinuousIso fSharp hsq hfinal

/-- `Stacks.SheafOfModules.inverseImageCompCocontinuousPushforwardOfIso` asserted through
`Nonempty`, for a consumer that only needs the two composites to be isomorphic. -/
theorem nonempty_inverseImage_comp_cocontinuousPushforwardOf_iso
    (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)
    (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final) :
    Nonempty (inverseImage.{v} J' J v' OC ⋙
        (CocontinuousPushforward.of.{v} J' K' u'
          (structureMapSquare (J' := J') (K' := K') fSharp hsq)).functor ≅
      (CocontinuousPushforward.of.{v} J K u fSharp).functor ⋙ inverseImage.{v} K' K v OD) :=
  ⟨inverseImageCompCocontinuousPushforwardOfIso J' J K' K u' u v' v OC OD fSharp hsq hfinal⟩


section CanonicalLowerShriek

variable [UnivLE.{r, v}] [UnivLE.{v₁, v}] [UnivLE.{u₁, v}] [UnivLE.{v₂, v}] [UnivLE.{u₂, v}]
  [UnivLE.{v₃, v}] [UnivLE.{u₃, v}] [UnivLE.{v₄, v}]
  [HasWeakSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify J' AddCommGrpCat.{v}] [J'.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify K AddCommGrpCat.{v}] [K.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- **Stacks 0FN3**, second conclusion, for the canonical direct images. In the situation of
`Stacks.SheafOfModules.inverseImageCompCocontinuousPushforwardOfIso` we have
`g'_! ∘ (f')^{-1} ≅ f^{-1} ∘ g_!`. The composite
`g'_! ∘ (f')^{-1}` is left adjoint to `f'_* ∘ (g')^*` and `f^{-1} ∘ g_!` is left adjoint to
`g^* ∘ f_*`; by the first conclusion those two right adjoints are isomorphic, so uniqueness of
left adjoints identifies the two composites. The left adjoints `g_!` and `g'_!` of `g^*` and
`(g')^*` are the concrete lower shriek of Stacks 0797, and the inverse images `f^{-1}` and
`(f')^{-1}` of the two canonical direct images along the cocontinuous `u` and `u'` — which is
condition (1) — are `Stacks.SheafOfModules.inverseImageCocontinuous`, constructed by
`Stacks.SheafOfModules.inverseImageCocontinuousAdjunction`. All four exist by the `UnivLE`,
`HasWeakSheafify` and `WEqualsLocallyBijective` hypotheses of this section. -/
@[stacks 0FN3 "second conclusion: `g'_! ∘ (f')⁻¹ ≅ f⁻¹ ∘ g_!` on sheaves of modules, for a
  commutative square of ringed topoi whose four functors `u`, `u'`, `v`, `v'` are cocontinuous,
  with `v`, `v'` continuous as well, with the comparison functors of the index categories of
  Section 00XF cofinal, and with `g^{-1} O_D = O_{D'}`, `(g')^{-1} O_C = O_{C'}`. Deduced from
  the first conclusion by uniqueness of left adjoints, so an isomorphism and not an equality.
  `g_!` and `g'_!` are the lower shriek of Stacks 0797, and `f^{-1}`, `(f')^{-1}` the inverse
  image `f^* G = O_C ⊗_{f^{-1}O_D} f^{-1}G` of
  `Stacks.SheafOfModules.inverseImageCocontinuous`: all four are constructed, none assumed, so
  the source's condition (1) — a cocontinuous functor giving rise to a morphism of ringed topoi
  — is a theorem here. The direct images along `u` and `u'` are the canonical ones attached to
  the structure map `f^♯ : O_D → {}_su O_C`."]
def lowerShriekCompLeftAdjointOfIso
    (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)
    (hsq : u' ⋙ v = v' ⋙ u)
    (hfinal : ∀ V' : D',
      (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
        (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final) :
    (CocontinuousPushforward.of.{v} J' K' u'
          (structureMapSquare (J' := J') (K' := K') fSharp hsq)).functor.leftAdjoint ⋙
        lowerShriek.{v} J' J v' OC ≅
      lowerShriek.{v} K' K v OD ⋙
        (CocontinuousPushforward.of.{v} J K u fSharp).functor.leftAdjoint :=
  ((Adjunction.ofIsRightAdjoint (CocontinuousPushforward.of.{v} J' K' u'
      (structureMapSquare (J' := J') (K' := K') fSharp hsq)).functor).comp
        (lowerShriekAdjunction.{v} J' J v' OC)).leftAdjointUniq
    (((lowerShriekAdjunction.{v} K' K v OD).comp
      (Adjunction.ofIsRightAdjoint
        (CocontinuousPushforward.of.{v} J K u fSharp).functor)).ofNatIsoRight
      (inverseImageCompCocontinuousPushforwardOfIso J' J K' K u' u v' v OC OD fSharp hsq
        hfinal).symm)


end CanonicalLowerShriek

end Canonical

end Square

end Stacks.SheafOfModules

end
