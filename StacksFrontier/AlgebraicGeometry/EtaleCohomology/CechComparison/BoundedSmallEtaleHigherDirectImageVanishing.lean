module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleAssociatedSheafRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.SmallEtaleHigherDirectImageVanishing
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelianSheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleDenseSubsite
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedTransport

/-!
# The higher direct images of `Fᵃ` vanish on the size-bounded small étale site

Let `B` be a big étale site containing a scheme `S` and let `F` be a quasi-coherent `𝒪_S`-module.
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale` is the vanishing of the higher
direct images of `Fᵃ` along `ε : S_étale ⟶ S_Zar` of [Stacks, Tag 03DW], stated on Mathlib's
small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`.  This file carries it over to the
small étale site of [Stacks, Tag 021B] cut out of `B`, which is the site the quasi-coherent
`𝒪`-modules `AlgebraicGeometry.SmallEtale.qcohOnSite` live on.

## The argument

The inclusion of the opens of `S` into the size-bounded small étale site, followed by the
embedding of that site into Mathlib's, *is* the inclusion of the opens into Mathlib's small
étale site, so direct image along `ε` factors as direct image along the embedding followed by
direct image along the bounded `ε`.  The first factor is an equivalence of the two categories of
abelian sheaves, the two sites being dense subsites of one another's topology
(`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`), and an equivalence is exact and
carries injective objects to injective objects, so it may be pulled out of a right derived
functor on the left by `CategoryTheory.Equivalence.compRightDerivedIso`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.toEtaleSiteAbelianPushforward`: restriction of abelian sheaves
  along the embedding into Mathlib's small étale site, an equivalence.
* `AlgebraicGeometry.SmallEtale.boundedZariskiAbelianPushforward`: direct image of abelian
  sheaves from the size-bounded small étale site to the small Zariski site of `S`.
* `AlgebraicGeometry.SmallEtale.boundedSmallEtaleAssociatedSheaf`: `Fᵃ` as an abelian sheaf on
  the size-bounded small étale site, namely its restriction from Mathlib's.

## Main results

* `AlgebraicGeometry.SmallEtale.opensToSmallEtale_comp_toEtaleSite`: the two inclusions of the
  opens of `S` into a small étale site agree.
* `AlgebraicGeometry.SmallEtale.toEtaleSiteAbelianPushforward_comp`: hence so do the two
  factorisations of the direct image along `ε`.
* `AlgebraicGeometry.SmallEtale.rightDerivedBoundedZariskiAbelianPushforwardIso`: the
  comparison of the two higher direct images.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_opensToSmallEtale`: **the
  vanishing on the size-bounded small étale site.**

## Implementation notes

No `@[stacks]` attribute is attached.  [Stacks, Tag 03DW] is a single equality quantified over
`τ` ranging over five big sites together with `S_Zar` and `S_étale`; the vanishing of the higher
direct images along `ε` is one step of its proof and not a part the source delimits, which is
also why `AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale` carries none.

The abelian sheaf whose higher direct images are killed is the restriction of
`AlgebraicGeometry.smallEtaleAssociatedSheaf` and not the underlying abelian sheaf of
`AlgebraicGeometry.SmallEtale.associatedModule`.  The two agree by the sections formula
`Fᵃ(T) = Γ(T, f^*F)` of [Stacks, Tag 070S] (2), which is proved as
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso`.  The identification of the two
abelian sheaves is `AlgebraicGeometry.SmallEtale.toSheafAssociatedModuleIso` and the vanishing
read at a sheaf of modules is
`AlgebraicGeometry.SmallEtale.isZero_rightDerived_pushforward_toSheaf`, both in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleQuasicoherentExtensions.lean`,
which imports this file.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inclusion of the opens of `S` into the size-bounded small étale site, followed by the
embedding into Mathlib's small étale site, is the inclusion of the opens into Mathlib's small
étale site.**  Both carry an open `U` to the open immersion `U.ι` read as a scheme étale over
`S`; the size bound that the first inclusion records is what the embedding forgets. -/
public theorem opensToSmallEtale_comp_toEtaleSite :
    opensToSmallEtale B S hS ⋙ toEtaleSite B S hS = opensToEtale S :=
  rfl

/-- **Restriction of abelian sheaves along the embedding into Mathlib's small étale site.**  It
is an equivalence, the small étale site of [Stacks, Tag 021B] being a dense subsite of
Mathlib's. -/
public abbrev toEtaleSiteAbelianPushforward :
    Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u} ⥤
      Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  (toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u}
    (topology B S hS) (Scheme.smallEtaleTopology S)

/-- **Restriction of abelian sheaves along the embedding is an equivalence.**  This is
`AlgebraicGeometry.SmallEtale.sheafEquiv` at `AddCommGrpCat.{u}`, declared as an instance: the
comma categories whose limits the dense-subsite equivalence needs are essentially small, the
small étale category of [Stacks, Tag 021B] being so. -/
public instance isEquivalence_toEtaleSiteAbelianPushforward :
    (toEtaleSiteAbelianPushforward B S hS).IsEquivalence :=
  haveI : ∀ X : (S.Etale)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (toEtaleSite B S hS).op) AddCommGrpCat.{u} :=
    fun _ ↦ hasLimitsOfShape_of_essentiallySmall.{u} _ _
  inferInstance

/-- **The direct image `ε_*` of abelian sheaves along `ε : S_étale ⟶ S_Zar`** for the small
étale site of [Stacks, Tag 021B] cut out of `B`. -/
public abbrev boundedZariskiAbelianPushforward :
    Sheaf (topology B S hS) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ↥S) AddCommGrpCat.{u} :=
  (opensToSmallEtale B S hS).sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology ↥S) (topology B S hS)

/-- **The direct image along `ε` factors through the embedding into Mathlib's small étale
site.**  This is `AlgebraicGeometry.SmallEtale.opensToSmallEtale_comp_toEtaleSite` read through
the factorisation of a sheaf pushforward along a composite of continuous functors, which is the
identity. -/
public theorem toEtaleSiteAbelianPushforward_comp :
    toEtaleSiteAbelianPushforward B S hS ⋙ boundedZariskiAbelianPushforward B S hS =
      smallEtaleZariskiPushforward S :=
  rfl

variable (𝓕 : S.Modules) [𝓕.IsQuasicoherent]

/-- **`Fᵃ` as an abelian sheaf on the size-bounded small étale site of `S`**, namely the
restriction along the embedding of `AlgebraicGeometry.smallEtaleAssociatedSheaf`.  Its value at
an object `T ⟶ S` is `Γ(T, T.hom^* F)`. -/
public abbrev boundedSmallEtaleAssociatedSheaf : Sheaf (topology B S hS) AddCommGrpCat.{u} :=
  (toEtaleSiteAbelianPushforward B S hS).obj (smallEtaleAssociatedSheaf S 𝓕)

/-- **The higher direct images along the two spellings of `ε` agree.**  Restriction along the
embedding into Mathlib's small étale site is an equivalence, hence exact and injective
preserving, so it comes out of the right derived functor on the left. -/
public def rightDerivedBoundedZariskiAbelianPushforwardIso
    (𝓖 : Sheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u}) (p : ℕ) :
    ((smallEtaleZariskiPushforward S).rightDerived p).obj 𝓖 ≅
      ((boundedZariskiAbelianPushforward B S hS).rightDerived p).obj
        ((toEtaleSiteAbelianPushforward B S hS).obj 𝓖) :=
  ((toEtaleSiteAbelianPushforward B S hS).compRightDerivedIso
    (boundedZariskiAbelianPushforward B S hS) p).app 𝓖

/-- **The higher direct images of `Fᵃ` along `ε : S_étale ⟶ S_Zar` vanish on the size-bounded
small étale site of [Stacks, Tag 021B].**  This is
`AlgebraicGeometry.isZero_rightDerived_pushforward_opensToEtale` transported along the
equivalence of abelian sheaves between that site and Mathlib's small étale site. -/
public theorem isZero_rightDerived_pushforward_opensToSmallEtale (p : ℕ) (hp : 0 < p) :
    IsZero (((boundedZariskiAbelianPushforward B S hS).rightDerived p).obj
      (boundedSmallEtaleAssociatedSheaf B S hS 𝓕)) :=
  (isZero_rightDerived_pushforward_opensToEtale S 𝓕 p hp).of_iso
    (rightDerivedBoundedZariskiAbelianPushforwardIso B S hS _ p).symm

end AlgebraicGeometry.SmallEtale

end
