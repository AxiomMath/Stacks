module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic

/-!
# The higher direct images of `Functor.rightDerived`, in degree zero

Let `f : X ⟶ Y` be a morphism of schemes. The higher direct images `R ⁱ f_* F` of a sheaf of
modules on `X` can be formed with Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`,
which computes `H ⁱ` of the image of an injective resolution: the module category `X.Modules` is
a Grothendieck abelian category, so it has enough injectives and hence injective resolutions.

This file establishes what holds for `R ⁱ f_*` in this indexing in degree `i = 0`, for an
arbitrary morphism of schemes and an arbitrary module. The pushforward functor is a right
adjoint, hence left exact, so `R ⁰ f_* F ≅ f_* F`; both quasi-coherence and finite type of
`R ⁰ f_* F` are therefore *equivalent* to the same property of `f_* F`, and for an affine
morphism the quasi-coherence is then available from [Stacks, Tag 02KG].

Along the way, `SheafOfModules.IsFiniteType` is shown to be stable under isomorphism, for an
arbitrary sheaf of rings on an arbitrary site.

## Main results

* `Stacks.AlgebraicGeometry.DerivedPushforward.isFiniteType_of_iso`: being of finite type is
  stable under isomorphism of sheaves of modules.
* `Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroIso`:
  `R ⁰ f_* ≅ f_*` as functors, and `pushforwardRightDerivedZeroObjIso` at an object.
* `Stacks.AlgebraicGeometry.DerivedPushforward.isQuasicoherent_rightDerived_zero_iff` and
  `isFiniteType_rightDerived_zero_iff`: quasi-coherence, resp. finite type, of `R ⁰ f_* F` is
  the same property of `f_* F`.
* `Stacks.AlgebraicGeometry.DerivedPushforward.isQuasicoherent_rightDerived_zero_of_isAffineHom`:
  for an affine morphism, `R ⁰ f_* F` is quasi-coherent when `F` is.

## Implementation notes

The degree-`0` isomorphism is `CategoryTheory.Functor.rightDerivedZeroIsoSelf`, whose hypothesis
`PreservesFiniteLimits` is found by instance search from
`AlgebraicGeometry.Scheme.Modules.instIsRightAdjointPushforward`. Nothing here is specific to
the morphism being proper.

Local generators are transported along an isomorphism `e : M ≅ N` by composing each generating
family with the restriction `SheafOfModules.Hom.over e.hom (X i)` of `e.hom` to the covering
object `X i`, which is an isomorphism and in particular an epimorphism, so that
`SheafOfModules.GeneratingSections.ofEpi` applies and keeps the index type — whence the
finiteness is literally the same.

## References

* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
-/


@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe v' u' u

namespace Stacks.AlgebraicGeometry.DerivedPushforward

/-! ### Finite type is stable under isomorphism -/

section FiniteType

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Transport the data of local generators of a sheaf of modules along an isomorphism: the
covering is unchanged, and each generating family is composed with the restriction of `e.hom`
to the corresponding covering object. -/
noncomputable def localGeneratorsDataOfIso {M N : SheafOfModules.{u} R}
    (σ : SheafOfModules.LocalGeneratorsData.{u'} M) (e : M ≅ N) :
    SheafOfModules.LocalGeneratorsData.{u'} N where
  I := σ.I
  X := σ.X
  coversTop := σ.coversTop
  generators i := (σ.generators i).ofEpi (SheafOfModules.Hom.over e.hom (σ.X i))

/-- If the local generators `σ` of `M` are of finite type, then so is their transport
`localGeneratorsDataOfIso σ e` along an isomorphism `e : M ≅ N`. -/
instance localGeneratorsDataOfIso_isFiniteType {M N : SheafOfModules.{u} R}
    (σ : SheafOfModules.LocalGeneratorsData.{u'} M) (e : M ≅ N) [h : σ.IsFiniteType] :
    (localGeneratorsDataOfIso σ e).IsFiniteType where
  isFiniteType i :=
    have := h.isFiniteType i
    inferInstanceAs ((σ.generators i).ofEpi (SheafOfModules.Hom.over e.hom (σ.X i))).IsFiniteType

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Being of finite type is stable under isomorphism.** If `M` is a sheaf of modules of finite
type and `e : M ≅ N`, then `N` is of finite type. -/
theorem isFiniteType_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) [M.IsFiniteType] :
    N.IsFiniteType where
  exists_localGeneratorsData := by
    obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
    exact ⟨localGeneratorsDataOfIso σ e, localGeneratorsDataOfIso_isFiniteType σ e⟩

omit [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Being of finite type is invariant under isomorphism.** -/
theorem isFiniteType_iff_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N) :
    M.IsFiniteType ↔ N.IsFiniteType :=
  ⟨fun _ => isFiniteType_of_iso e, fun _ => isFiniteType_of_iso e.symm⟩

end FiniteType

/-! ### The zeroth higher direct image is the pushforward -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The zeroth higher direct image is the pushforward**: `R ⁰ f_* ≅ f_*`, for the `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`. -/
noncomputable def pushforwardRightDerivedZeroIso :
    (Scheme.Modules.pushforward f).rightDerived 0 ≅ Scheme.Modules.pushforward f :=
  Functor.rightDerivedZeroIsoSelf _

variable (F : X.Modules)

/-- The value of `pushforwardRightDerivedZeroIso` at a module: `R ⁰ f_* F ≅ f_* F`. -/
noncomputable def pushforwardRightDerivedZeroObjIso :
    ((Scheme.Modules.pushforward f).rightDerived 0).obj F ≅
      (Scheme.Modules.pushforward f).obj F :=
  (pushforwardRightDerivedZeroIso f).app F

/-! ### Quasi-coherence and finite type in degree zero -/

/-- **Quasi-coherence of `R ⁰ f_* F` is quasi-coherence of `f_* F`.** -/
theorem isQuasicoherent_rightDerived_zero_iff :
    (((Scheme.Modules.pushforward f).rightDerived 0).obj F).IsQuasicoherent ↔
      ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
  ⟨fun _ => (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      (pushforwardRightDerivedZeroObjIso f F) inferInstance,
    fun _ => (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
      (pushforwardRightDerivedZeroObjIso f F).symm inferInstance⟩

/-- **Finite type of `R ⁰ f_* F` is finite type of `f_* F`.** -/
theorem isFiniteType_rightDerived_zero_iff :
    (((Scheme.Modules.pushforward f).rightDerived 0).obj F).IsFiniteType ↔
      ((Scheme.Modules.pushforward f).obj F).IsFiniteType :=
  isFiniteType_iff_of_iso.{u, u, u} (pushforwardRightDerivedZeroObjIso f F)

/-- **For an affine morphism, `R ⁰ f_* F` is quasi-coherent** when `F` is. -/
instance isQuasicoherent_rightDerived_zero_of_isAffineHom [IsAffineHom f] [F.IsQuasicoherent] :
    (((Scheme.Modules.pushforward f).rightDerived 0).obj F).IsQuasicoherent :=
  (isQuasicoherent_rightDerived_zero_iff f F).2 inferInstance

end Stacks.AlgebraicGeometry.DerivedPushforward

end
