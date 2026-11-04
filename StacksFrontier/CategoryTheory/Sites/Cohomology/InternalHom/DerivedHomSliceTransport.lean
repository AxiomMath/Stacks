module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SheafHomSiteEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# Derived internal Hom along a slice followed by an equivalence of ringed sites

Let `X` and `Y` be ringed sites, `U` an object of `X` and `e : Y ≌ X/U` an equivalence of the
underlying sites with an invertible structure map `φ : 𝒪_Y ⟶ e_* 𝒪_{X/U}`. Reading a sheaf of
`𝒪_X`-modules on `Y` is restricting it to the slice at `U` and transporting it along `e`. This
file shows that the derived internal Hom commutes with this operation:

`(R𝓗om_X(K, L))|_U ≅ R𝓗om_Y(K|_U, L|_U)`.

It is Stacks 08JB for the slice at `U`
(`AlgebraicGeometry.RingedSite.derivedHomRestriction`) followed by the invariance of the derived
internal Hom under an equivalence of ringed sites
(`AlgebraicGeometry.RingedSite.siteEquivDerivedSheafHomIsoOfIso`).

## Main definitions

* `AlgebraicGeometry.RingedSite.sliceEquivTransport`: restriction to the slice followed by the
  transport along the equivalence.
* `AlgebraicGeometry.RingedSite.sliceEquivTransportDerivedSheafHomIso`: the comparison of derived
  internal Homs.

## References

* [Stacks Project, Tag 08JB](https://stacks.math.columbia.edu/tag/08JB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible]
  Stacks.SheafOfModules.Tensor.ringSheaf
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'
  PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  PresheafOfModules.presheaf
  PresheafOfModules.toPresheaf
  PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  SheafOfModules.pushforward
  SheafOfModules.overFunctor
  SheafOfModules.toSheaf
  SheafOfModules.forget

section SliceTransport

variable {X Y : RingedSite.{u, u, u}} (U : X.C) (eqv : Y.C ≌ (X.over U).C)
  [hF : eqv.functor.IsContinuous Y.J (X.over U).J] [hI : eqv.inverse.IsContinuous (X.over U).J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
    (eqv.functor.sheafPushforwardContinuous RingCat.{u} Y.J (X.over U).J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O))

/-- The transport of modules along the equivalence of ringed sites from `Y` to the slice at `U`. -/
abbrev sliceEquivPushforward :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  @SheafOfModules.pushforward.{u} _ _ _ _ Y.J (X.over U).J eqv.functor _ _ hF φ

/-- Restriction to the slice at `U`, followed by the transport along an equivalence of ringed
sites from `Y` to that slice. -/
abbrev sliceEquivTransport :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
    sliceEquivPushforward U eqv φ

/-- Restriction to the slice followed by transport along the equivalence is additive. -/
instance sliceEquivTransport_additive : (sliceEquivTransport U eqv φ).Additive :=
  haveI :
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive :=
    SheafOfModules.overFunctor_additive _ _
  haveI := pushforward_additive (X := X.over U) (Y := Y) eqv φ
  Functor.instAdditiveComp _ _

variable [hφ : IsIso φ]
  [hl : PreservesFiniteLimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]
  [hc : PreservesFiniteColimits
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)]

omit hc in
include hφ in
/-- Restriction to the slice followed by transport along the equivalence preserves finite limits
when `φ` is an isomorphism. -/
theorem sliceEquivTransport_preservesFiniteLimits :
    PreservesFiniteLimits (sliceEquivTransport U eqv φ) :=
  have := pushforward_preservesFiniteLimitsOfIso (X := X.over U) (Y := Y) eqv φ
  comp_preservesFiniteLimits _ _

omit hl in
include hφ in
/-- Restriction to the slice followed by transport along the equivalence preserves finite
colimits when `φ` is an isomorphism. -/
theorem sliceEquivTransport_preservesFiniteColimits :
    PreservesFiniteColimits (sliceEquivTransport U eqv φ) :=
  have := pushforward_preservesFiniteColimitsOfIso (X := X.over U) (Y := Y) eqv φ
  comp_preservesFiniteColimits _ _

variable [HasSheafify X.J AddCommGrpCat.{u}] [HasSheafify (X.over U).J AddCommGrpCat.{u}]

/-- **The derived internal Hom commutes with restriction to a slice followed by an equivalence
of ringed sites.** This is Stacks 08JB for the slice at `U` composed with the invariance of the
derived internal Hom under an equivalence of ringed sites. -/
def sliceEquivTransportDerivedSheafHomIso
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    haveI := sliceEquivTransport_preservesFiniteLimits U eqv φ
    haveI := sliceEquivTransport_preservesFiniteColimits U eqv φ
    (sliceEquivTransport U eqv φ).mapDerivedCategory.obj
        (((derivedSheafHomBifunctor X).obj (op K)).obj L) ≅
      ((derivedSheafHomBifunctor Y).obj
        (op ((sliceEquivTransport U eqv φ).mapDerivedCategory.obj K))).obj
          ((sliceEquivTransport U eqv φ).mapDerivedCategory.obj L) :=
  haveI := sliceEquivTransport_preservesFiniteLimits U eqv φ
  haveI := sliceEquivTransport_preservesFiniteColimits U eqv φ
  haveI := pushforward_preservesFiniteLimitsOfIso (X := X.over U) (Y := Y) eqv φ
  haveI := pushforward_preservesFiniteColimitsOfIso (X := X.over U) (Y := Y) eqv φ
  haveI :
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive :=
    SheafOfModules.overFunctor_additive _ _
  haveI := pushforward_additive (X := X.over U) (Y := Y) eqv φ
  let c := Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)
    (sliceEquivPushforward U eqv φ)
  c.app _ ≪≫
    (sliceEquivPushforward U eqv φ).mapDerivedCategory.mapIso
      ((derivedHomRestriction X U).iso K L) ≪≫
    siteEquivDerivedSheafHomIsoOfIso (X := X.over U) (Y := Y) eqv φ _ _ ≪≫
    ((derivedSheafHomBifunctor Y).mapIso (c.app K).op).app _ ≪≫
    ((derivedSheafHomBifunctor Y).obj _).mapIso (c.app L).symm

end SliceTransport

end AlgebraicGeometry.RingedSite

end
