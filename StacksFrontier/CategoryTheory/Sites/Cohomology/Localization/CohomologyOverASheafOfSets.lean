module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.ExtAlongAnExactFunctor
public import StacksFrontier.CategoryTheory.Sites.CechNerveHomology
public import StacksFrontier.CategoryTheory.Sites.PresheafOfElements
public import StacksFrontier.CategoryTheory.Sites.Topos.LocalizationShriekExact
import StacksCore.Tactic.StacksAttribute

/-! # Cohomology over a sheaf of sets

Let `(C, J)` be a small site and let `K` be a sheaf of sets on it. The site of elements of `K` is
`C/K = CostructuredArrow yoneda K`, whose objects are the pairs `(U, s)` with `s ∈ K(U)`, with the
topology restricted from `J`; its projection `j` to `C` is continuous and cocontinuous (Stacks
0791), so it induces a morphism of topoi whose inverse image `j⁻¹` is restriction of sheaves and
whose extension by zero `j_!` is the left adjoint of that restriction.

Stacks 07A0 asserts two things: that `j⁻¹` preserves injective abelian sheaves — which is
`Stacks.Sites.LocalizationShriek.preservesInjectiveObjects_sheafLocalizationInverseImage` — and
that cohomology over `K`, i.e. `Ext` out of the free abelian sheaf on `K`, is cohomology on `C/K`
with coefficients in the inverse image.

This file proves the second assertion, `cohomologyOnSheafIso`. It has two inputs. The first is
that `j⁻¹` is exact — it is a right adjoint by Stacks 0791's `j_! ⊣ j⁻¹` and a left adjoint by
`j⁻¹ ⊣ j_*`, hence additive as well — and preserves injectives; with those,
`Stacks.Cohomology.ExtComparison.extFunctorObjIsoCompOfIso` turns the adjunction into the
comparison of `Ext`-functors, which is `cohomologyOnSheafIso_of_extensionByZeroUnitIso`. The
second is the identification `j_!(ℤ_{C/K}) ≅ ℤ_K` of extension by zero of the unit coefficient
sheaf with the free abelian sheaf on `K`, which is `extensionByZeroUnitIso`: both sides
corepresent `F ↦ Hom_{PSh(C), Set}(K, F)`, by
`Stacks.Sites.Elements.elementsHomEquiv` on one side and the free-abelian-sheaf adjunction on the
other.

## Main definitions

* `Stacks.Cohomology.SheafOfSets.localizedTopology`: the topology on the site of elements of `K`.
* `Stacks.Cohomology.SheafOfSets.inverseImage`: `j⁻¹` on abelian sheaves. This is the functor the
  injectivity half of Stacks 07A0 is stated about.
* `Stacks.Cohomology.SheafOfSets.extensionByZero`: `j_!` on abelian sheaves, as the left adjoint
  of `j⁻¹`.
* `Stacks.Cohomology.SheafOfSets.freeAbelianSheafOn` and
  `Stacks.Cohomology.SheafOfSets.unitSheaf`: the free abelian sheaf `ℤ_K` on `K`, and the constant
  abelian sheaf `ℤ` on the site of elements of `K`. `Ext` out of the first is cohomology over `K`;
  `Ext` out of the second is `Sheaf.functorH`, by `functorH_eq_extFunctorObj`.

## Main results

* `Stacks.Cohomology.SheafOfSets.extensionByZeroUnitIso`: extension by zero of the unit
  coefficient sheaf is the free abelian sheaf on `K`.
* `Stacks.Cohomology.SheafOfSets.cohomologyOnSheafIso_of_extensionByZeroUnitIso`: the cohomology
  comparison, from that identification taken as a hypothesis.
* `Stacks.Cohomology.SheafOfSets.cohomologyOnSheafIso`: **Stacks 07A0, the cohomology
  comparison.**

## Implementation notes

The site is taken small. That is not a presentational choice: the comparison is proved through
right derived functors, so it needs injective resolutions in both sheaf categories, and Mathlib
provides those (through `IsGrothendieckAbelian`) only for a small — or essentially small — site.
It is however the generality of the source, where a site has a set of objects. The `Ext`-universe
is correspondingly the morphism universe of the sheaf categories rather than an arbitrary one
admitting `HasExt`; both are `u` here. A statement at an arbitrary `HasExt` universe would have to
be transported along `CategoryTheory.Abelian.Ext.chgUniv`, which Mathlib has only as an `Equiv`.

The continuity instance is the one Stacks 0791 provides, taken from
`Presheaf.IsSheaf.exists_sheafEquivalence_costructuredArrow_yoneda`, so that `inverseImage` is
literally the inverse image of the localization morphism of topoi; `Functor.IsContinuous` and
`Functor.IsCocontinuous` are `Prop`-valued classes, so this choice is definitionally the only
one.

## References

* [Stacks Project, Tag 07A0](https://stacks.math.columbia.edu/tag/07A0)
* [Stacks Project, Tag 0791](https://stacks.math.columbia.edu/tag/0791)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits CategoryTheory.Abelian
open Stacks.Cohomology.ExtComparison

namespace Stacks.Cohomology.SheafOfSets

universe u

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u}] (K : Sheaf J (Type u))

/-- The topology on the site `C/K` of elements of a sheaf of sets `K`, restricted from `J` along
the projection `j`. By Stacks 0791 its covering sieves are those whose image under `j` covers. -/
abbrev localizedTopology : GrothendieckTopology (CostructuredArrow (yoneda (C := C)) K.obj) :=
  (CostructuredArrow.proj (yoneda (C := C)) K.obj).restrictedTopology J

/-- **Stacks 0791:** the projection from the site of elements of a sheaf of sets is continuous. -/
instance isContinuous_proj_of_isSheaf :
    (CostructuredArrow.proj (yoneda (C := C)) K.obj).IsContinuous (localizedTopology J K) J :=
  (K.property.exists_sheafEquivalence_costructuredArrow_yoneda).2.2.choose

/-- **Stacks 0791:** the projection from the site of elements of a sheaf of sets is
cocontinuous. -/
instance isCocontinuous_proj_of_isSheaf :
    (CostructuredArrow.proj (yoneda (C := C)) K.obj).IsCocontinuous (localizedTopology J K) J :=
  (K.property.exists_sheafEquivalence_costructuredArrow_yoneda).2.2.choose_spec.choose

/-- The inverse image `j⁻¹` of the localization morphism of topoi attached to a sheaf of sets `K`,
on abelian sheaves: restriction of an abelian sheaf on `C` to the site of elements of `K`. -/
abbrev inverseImage : Sheaf J AddCommGrpCat.{u} ⥤
    Sheaf (localizedTopology J K) AddCommGrpCat.{u} :=
  (CostructuredArrow.proj (yoneda (C := C)) K.obj).sheafPushforwardContinuous
    AddCommGrpCat.{u} (localizedTopology J K) J

/-- Extension by zero `j_!` on abelian sheaves, the left adjoint of `inverseImage`. -/
abbrev extensionByZero : Sheaf (localizedTopology J K) AddCommGrpCat.{u} ⥤
    Sheaf J AddCommGrpCat.{u} :=
  Functor.sheafPullback (CostructuredArrow.proj (yoneda (C := C)) K.obj)
    AddCommGrpCat.{u} (localizedTopology J K) J

/-- **Stacks 0791:** extension by zero is left adjoint to the inverse image. -/
abbrev extensionByZeroAdjunction : extensionByZero J K ⊣ inverseImage J K :=
  Functor.sheafAdjunctionContinuous (CostructuredArrow.proj (yoneda (C := C)) K.obj)
    AddCommGrpCat.{u} (localizedTopology J K) J

/-- The free abelian sheaf `ℤ_K` on a sheaf of sets `K`. Cohomology over `K` is `Ext` out of it. -/
abbrev freeAbelianSheafOn : Sheaf J AddCommGrpCat.{u} :=
  (presheafToSheaf J AddCommGrpCat.{u}).obj (K.obj ⋙ AddCommGrpCat.free)

/-- The constant abelian sheaf `ℤ` on the site of elements of `K`, the unit coefficient sheaf
whose `Ext`-functors are the cohomology of that site. -/
abbrev unitSheaf : Sheaf (localizedTopology J K) AddCommGrpCat.{u} :=
  (constantSheaf (localizedTopology J K) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

section Instances

/-- The inverse image is right exact: it is a left adjoint, by `j⁻¹ ⊣ j_*`. -/
instance preservesFiniteColimits_inverseImage : PreservesFiniteColimits (inverseImage J K) :=
  have : (inverseImage J K).IsLeftAdjoint :=
    ((CostructuredArrow.proj (yoneda (C := C)) K.obj).sheafAdjunctionCocontinuous
      AddCommGrpCat.{u} (localizedTopology J K) J).isLeftAdjoint
  inferInstance

/-- The inverse image is additive: it is left exact, being a right adjoint. -/
instance additive_inverseImage : (inverseImage J K).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Extension by zero is additive, being the left adjoint of an additive functor. -/
instance additive_extensionByZero : (extensionByZero J K).Additive :=
  (extensionByZeroAdjunction J K).left_adjoint_additive

/-- **Stacks 07A0, the injectivity assertion**, recorded as an instance on `inverseImage`. -/
instance preservesInjectiveObjects_inverseImage :
    (inverseImage J K).PreservesInjectiveObjects :=
  Stacks.Sites.LocalizationShriek.preservesInjectiveObjects_sheafPushforwardContinuous K.obj J

end Instances

/-! ### Extension by zero of the unit coefficient sheaf

The remaining input of Stacks 07A0 is the identification of `j_!(ℤ)` with the free abelian sheaf
on `K`. Both objects corepresent the same functor on abelian sheaves, namely
`F ↦ Hom_{PSh(C), Set}(K, F)`: for the free abelian sheaf that is the free-abelian-sheaf
adjunction, and for `j_!(ℤ)` it is the composite of the free-abelian, sheafification and
`j_! ⊣ j⁻¹` adjunctions, followed by `Stacks.Sites.Elements.elementsHomEquiv`. -/

section ExtensionByZeroUnit

open Stacks.Sites.Elements

/-- The free abelian presheaf on the terminal presheaf of sets of the site of elements of `K` is
the constant presheaf `ℤ`. -/
def freeAbelianConstPUnitIso :
    (Presheaf.freeAbelian (C := CostructuredArrow (yoneda (C := C)) K.obj)).obj
        ((Functor.const _).obj PUnit.{u + 1}) ≅
      (Functor.const (CostructuredArrow (yoneda (C := C)) K.obj)ᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  NatIso.ofComponents (fun _ => freeObjPUnitIso) (by
    intro X Y f
    have h : (Presheaf.freeAbelian.obj
        ((Functor.const (CostructuredArrow (yoneda (C := C)) K.obj)ᵒᵖ).obj
          PUnit.{u + 1})).map f = 𝟙 _ := AddCommGrpCat.free.map_id _
    rw [h, Category.id_comp]
    simp)

/-- The unit coefficient sheaf of the site of elements of `K` is the free abelian sheaf on the
terminal presheaf of sets. -/
def unitSheafIsoFreeAbelianSheaf :
    (Presheaf.freeAbelianSheaf (localizedTopology J K)).obj
        ((Functor.const _).obj PUnit.{u + 1}) ≅ unitSheaf J K :=
  (presheafToSheaf (localizedTopology J K) AddCommGrpCat.{u}).mapIso
    (freeAbelianConstPUnitIso J K)

/-- The functor on abelian sheaves on `(C, J)` that both `j_!(ℤ)` and the free abelian sheaf on
`K` corepresent: maps of presheaves of sets from `K` to the underlying presheaf. -/
abbrev corepFunctor : Sheaf J AddCommGrpCat.{u} ⥤ Type u :=
  (sheafToPresheaf J AddCommGrpCat.{u} ⋙ Presheaf.forgetAbelian) ⋙ coyoneda.obj (op K.obj)

/-- The free abelian sheaf on `K` corepresents `corepFunctor`: this is the free-abelian-sheaf
adjunction. -/
def corepByFreeAbelianSheaf : (corepFunctor J K).CorepresentableBy (freeAbelianSheafOn J K) :=
  (Presheaf.freeAbelianSheafAdj J).corepresentableBy K.obj

/-- The composite of the free-abelian, sheafification and `j_! ⊣ j⁻¹` adjunctions. Its left
adjoint sends the terminal presheaf of sets on the site of elements of `K` to `j_!(ℤ)`. -/
def extensionByZeroFreeAdjunction :=
  Presheaf.freeAbelianAdj.comp
    ((sheafificationAdjunction (localizedTopology J K) AddCommGrpCat.{u}).comp
      (extensionByZeroAdjunction J K))

/-- `j_!(ℤ)` corepresents `corepFunctor`. The functor the composite adjunction corepresents sends
`F` to the maps from the terminal presheaf of sets on the site of elements of `K` to the
restriction of `F`, and `elementsHomEquiv` identifies those with the maps out of `K`. -/
def corepByExtensionByZeroUnit :
    (corepFunctor J K).CorepresentableBy ((extensionByZero J K).obj (unitSheaf J K)) :=
  (((extensionByZeroFreeAdjunction J K).corepresentableBy
      ((Functor.const _).obj PUnit.{u + 1})).ofIsoObj
    ((extensionByZero J K).mapIso (unitSheafIsoFreeAbelianSheaf J K)).symm).ofIso
    (NatIso.ofComponents
      (fun F => (elementsHomEquiv K.obj (Presheaf.forgetAbelian.obj F.obj)).toIso)
      (fun _ => by ext θ; rfl))

/-- **Extension by zero of the unit coefficient sheaf is the free abelian sheaf on `K`.** This is
the input Stacks 07A0's proof needs from the identification of `Sh(C/K)` with the localized topos
`Sh(C)/K`: under that identification `j_!` is the forgetful functor from `Sh(C)/K`, so `j_!` of
the terminal object is `K` itself, and taking free abelian sheaves preserves that. -/
def extensionByZeroUnitIso :
    (extensionByZero J K).obj (unitSheaf J K) ≅ freeAbelianSheafOn J K :=
  (corepByExtensionByZeroUnit J K).uniqueUpToIso (corepByFreeAbelianSheaf J K)

end ExtensionByZeroUnit

variable [HasExt.{u} (Sheaf (localizedTopology J K) AddCommGrpCat.{u})]

omit [HasSheafify J AddCommGrpCat.{u}] in
/-- Sheaf cohomology on the site of elements of `K` is `Ext` out of the constant abelian sheaf
`ℤ`: `Sheaf.functorH` and `extFunctorObj` of `unitSheaf` are the same functor. -/
lemma functorH_eq_extFunctorObj (p : ℕ) :
    Sheaf.functorH (localizedTopology J K) p = extFunctorObj (unitSheaf J K) p :=
  rfl

variable [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

/-- **Stacks 07A0, the cohomology comparison**, given the identification of `j_!` of the unit
coefficient sheaf with the free abelian sheaf on `K`. For every `p`,

  `Ext^p_{Sh(C, J)}(ℤ_K, -) ≅ j⁻¹ ⋙ H^p(C/K, -)`,

naturally in the abelian sheaf of coefficients.

The hypothesis `e` is the only remaining input of Stacks 07A0: both halves of its proof — the
exactness of `j⁻¹` and the fact that it preserves injectives — are instances here, and the
passage from them to the comparison is `extFunctorObjIsoCompOfIso`. -/
def cohomologyOnSheafIso_of_extensionByZeroUnitIso
    (e : (extensionByZero J K).obj (unitSheaf J K) ≅ freeAbelianSheafOn J K) (p : ℕ) :
    extFunctorObj (freeAbelianSheafOn J K) p ≅
      inverseImage J K ⋙ Sheaf.functorH (localizedTopology J K) p :=
  extFunctorObjIsoCompOfIso (extensionByZeroAdjunction J K) e p

/-- **Stacks 07A0, the cohomology comparison.** For a sheaf of sets `K` on a small site `(C, J)`,
cohomology over `K` — that is, `Ext` out of the free abelian sheaf on `K` — is the cohomology of
the site of elements of `K` with coefficients in the inverse image:

  `Ext^p_{Sh(C, J)}(ℤ_K, -) ≅ j⁻¹ ⋙ H^p(C/K, -)`,

naturally in the abelian sheaf of coefficients. -/
@[stacks 07A0 "the cohomology comparison"]
def cohomologyOnSheafIso (p : ℕ) :
    extFunctorObj (freeAbelianSheafOn J K) p ≅
      inverseImage J K ⋙ Sheaf.functorH (localizedTopology J K) p :=
  cohomologyOnSheafIso_of_extensionByZeroUnitIso J K (extensionByZeroUnitIso J K) p

end Stacks.Cohomology.SheafOfSets

end
