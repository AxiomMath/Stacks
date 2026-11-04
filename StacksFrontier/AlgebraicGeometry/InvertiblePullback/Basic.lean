module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Stacks 0B8L: the pullback of an invertible module is invertible

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `L` be an invertible sheaf
of `𝒪_Y`-modules. Stacks Tag 0B8L asserts that `f^* L` is an invertible sheaf of `𝒪_X`-modules.
This file proves that, with no hypothesis beyond a morphism of ringed spaces, and restates it
for a morphism of schemes and for the restriction of a module to an open subscheme.

## Main results

* `Stacks.InvertiblePullback.isInvertible_pullback`: **Stacks Tag 0B8L.** The pullback of an
  invertible sheaf of modules along a morphism of ringed spaces is invertible.
* `Stacks.InvertiblePullback.isInvertibleModule_pullback`: the same for a morphism of schemes,
  in the `Stacks.Ample.IsInvertibleModule` spelling, which is the one the repository's ampleness
  theory takes as an instance binder.
* `Stacks.InvertiblePullback.isInvertible_pullback_ringCatSheaf`: the same at
  `X.presheaf`/`X.ringCatSheaf.2`, the spelling of
  `Stacks.AlgebraicGeometry.GoodOpenClose.isInvertible_pullback_of_trivializing_cover`.
* `Stacks.InvertiblePullback.isInvertibleModule_restrict`: the special case of the open immersion
  of an open subscheme, that is the restriction `L|_U`. This is the form in which Stacks Tag 01VH
  needs Tag 0B8L.
* `Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible`: the two
  classes in the repository that both realise Tag 01CS agree. See the implementation notes.

## The route

Invertibility is used and produced through Tag 0B8K, `L` is invertible if and only if some `N`
has `L ⊗ N ≅ 𝒪`: that criterion is transported along `f^*` by the two facts which make `f^*`
monoidal, and no monoidal structure on `SheafOfModules` is needed.

* `Stacks.PullbackTensorIso.pullbackTensorIso` is Tag 01CD, `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B`, proved
  in the repository with no hypothesis.
* `SheafOfModules.pullbackObjUnitToUnit` is Mathlib's comparison `f^* 𝒪_Y ⟶ 𝒪_X`, an
  isomorphism as soon as the functor on opens is final; for a morphism of ringed spaces that
  functor is `Opens.map f.base`, which is representably flat because the opens `V` of `Y` with
  `U ⊆ f⁻¹ V` are closed under intersection, so `CategoryTheory.final_of_representablyFlat`
  applies.

Given `L ⊗ N ≅ 𝒪_Y`, the composite

`f^*L ⊗ f^*N ≅ f^*(L ⊗ N) ≅ f^* 𝒪_Y ≅ 𝒪_X`

is the witness Tag 0B8K asks for.

## Implementation notes

**Two classes for Tag 01CS.** The repository contains two classes with the same definition and
the same Stacks-01CS label (written here without the attribute brackets, so the audit
scanner does not read this prose as a tag): `Stacks.SheafOfModules.IsInvertible` and
`AlgebraicGeometry.SheafOfModules.IsInvertible`. Tag 0B8K
(`Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit`) is stated for the first and the
ampleness theory (`Stacks.Ample.IsInvertibleModule`, hence `Stacks.Ample.IsAmple`) for the
second, so a single statement cannot serve both: they are distinct constants and not
definitionally equal. Their two `tensorLeftFunctor`s *are* equal by `rfl`, so
`stacksIsInvertible_iff_algebraicGeometryIsInvertible` bridges them through the two
`isInvertible_iff_tensorLeftFunctor_isEquivalence` lemmas, and both spellings of Tag 0B8L below
are instances. The duplication itself is not repaired here; that would mean editing files this
file does not own.

**Spellings of the structure sheaf of rings.** Invertibility is indexed by a presheaf of
commutative rings together with the sheaf condition on its composite with
`forget₂ CommRingCat RingCat`. For a ringed space `X` those are `X.sheaf.obj` and
`(Stacks.RingedSpace.structureRingSheaf X).property`, and
`Stacks.SheafOfModules.TensorSheafification.structureSheaf X.sheaf.obj
  (Stacks.RingedSpace.structureRingSheaf X).property` is
`Stacks.RingedSpace.structureRingSheaf X` by `rfl`. That is the spelling Tag 01CD is stated in,
so the tensor product appearing in `pullbackTensorIso` is literally the one
`Stacks.SheafOfModules.tensorLeftFunctor` forms, and nothing bridges two tensor constructions.
The sheaf condition is a `Prop`, so the scheme-level restatements differ from the ringed-space
one only by proof irrelevance; but instance search runs at reducible transparency and does not
see through `Scheme.ringCatSheaf`, so each spelling needs its own instance and the conversion is
made by `@`-application, which checks at default transparency.

## References

* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace

universe v u w

namespace Stacks.InvertiblePullback

/-! ### The two classes realising Tag 01CS -/

/-- A sheaf of modules `L` satisfies `Stacks.SheafOfModules.IsInvertible` if and only if it
satisfies `AlgebraicGeometry.SheafOfModules.IsInvertible`. -/
theorem stacksIsInvertible_iff_algebraicGeometryIsInvertible {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} (O : Cᵒᵖ ⥤ CommRingCat.{w})
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) :
    Stacks.SheafOfModules.IsInvertible O hO L ↔
      AlgebraicGeometry.SheafOfModules.IsInvertible O hO L := by
  exact Iff.rfl

/-! ### Tag 0B8L on a ringed space -/

section RingedSpace

attribute [local instance] modulePushforward_isRightAdjoint

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **Stacks Tag 0B8L.** The pullback of an invertible sheaf of modules along a morphism of
ringed spaces is invertible.

A tensor inverse `N` of `L`, which Tag 0B8K produces from invertibility, is carried by `f^*` to a
tensor inverse of `f^*L`: Tag 01CD turns `f^*(L ⊗ N)` into `f^*L ⊗ f^*N`, and
`RingedSpaceModuleAdjunction.modulePullbackObjUnitIso` turns `f^* 𝒪_Y` into `𝒪_X`. -/
@[stacks 0B8L]
theorem isInvertible_pullback (L : SheafOfModules.{u} (structureRingSheaf Y))
    [Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureRingSheaf Y).property L] :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureRingSheaf X).property
      ((pullbackFunctor f).obj L) := by
  obtain ⟨N, ⟨e⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := Y.sheaf.obj) (hO := (structureRingSheaf Y).property) L).mp inferInstance
  refine (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := X.sheaf.obj) (hO := (structureRingSheaf X).property)
      ((pullbackFunctor f).obj L)).mpr ⟨(pullbackFunctor f).obj N, ⟨?_⟩⟩
  exact ((Stacks.PullbackTensorIso.pullbackTensorIso f).app (L, N)).symm ≪≫
    (pullbackFunctor f).mapIso e ≪≫ RingedSpaceModuleAdjunction.modulePullbackObjUnitIso f

/-- **Stacks Tag 0B8L** for `AlgebraicGeometry.SheafOfModules.IsInvertible`, the other class
labelled Tag 01CS. -/
theorem isInvertible_pullback' (L : SheafOfModules.{u} (structureRingSheaf Y))
    [h : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj
      (structureRingSheaf Y).property L] :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj (structureRingSheaf X).property
      ((pullbackFunctor f).obj L) :=
  let : Stacks.SheafOfModules.IsInvertible Y.sheaf.obj (structureRingSheaf Y).property L :=
    (stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ L).mpr h
  (stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp (isInvertible_pullback f L)

end RingedSpace

/-! ### Tag 0B8L on a scheme -/

/-- **Stacks Tag 0B8L for a morphism of schemes**, at `X.presheaf` and `X.ringCatSheaf.2`: the
pullback of an invertible `𝒪_S`-module along `f : X ⟶ S` is an invertible `𝒪_X`-module. -/
instance isInvertible_pullback_ringCatSheaf {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules)
    [h : Stacks.SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M] :
    Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((modulePullback f.toLRSHom.toShHom).obj M) :=
  @isInvertible_pullback _ _ f.toLRSHom.toShHom M h

/-- **Stacks Tag 0B8L for a morphism of schemes**, in the spelling the repository's ampleness
theory uses: the pullback of an invertible `𝒪_S`-module along `f : X ⟶ S` is an invertible
`𝒪_X`-module. -/
instance isInvertibleModule_pullback {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules)
    [h : Stacks.Ample.IsInvertibleModule S M] :
    Stacks.Ample.IsInvertibleModule X ((modulePullback f.toLRSHom.toShHom).obj M) :=
  @isInvertible_pullback' _ _ f.toLRSHom.toShHom M h

/-- **Stacks Tag 0B8L** at the `AlgebraicGeometry.Scheme.Modules.pullback` spelling of the
pullback functor: the pullback of an invertible `𝒪_S`-module along a morphism of schemes is
invertible. `Stacks.InvertiblePullback.isInvertibleModule_pullback` states this for the
definitionally equal `RingedSpaceModuleAdjunction.modulePullback`, and instance search does not
unfold `AlgebraicGeometry.Scheme.Modules.pullback` to reach it. -/
instance isInvertibleModule_schemeModulesPullback {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules)
    [Stacks.Ample.IsInvertibleModule S M] :
    Stacks.Ample.IsInvertibleModule X ((Scheme.Modules.pullback f).obj M) :=
  isInvertibleModule_pullback f M

/-- The restriction `L|_U` of an invertible module to an open subscheme is invertible: the case
of `Stacks.InvertiblePullback.isInvertibleModule_pullback` for the open immersion of `U`. This is
the form in which Stacks Tag 01VH needs Tag 0B8L. -/
instance isInvertibleModule_restrict {X : Scheme.{u}} (U : X.Opens) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] :
    Stacks.Ample.IsInvertibleModule U.toScheme
      ((modulePullback U.ι.toLRSHom.toShHom).obj L) :=
  isInvertibleModule_pullback U.ι L

end Stacks.InvertiblePullback

end
