module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdjunction
public import
  StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineCohomologyVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.BigSiteModuleInjectives
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseRingedSiteHomGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.DerivedAdjunctionOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.IsLocallyRingedCriterion

/-!
# The derived adjunction of the morphism `((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`

Let `S` be a scheme and `(Sch/S)_τ` a chosen big site over `S`, for `τ` one of the five
topologies. The inclusion of the small Zariski site of `S` is a morphism of sites, and with the
identification of the sections of `𝒪_S` over an open with the functions on it, it is the morphism
of ringed sites `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` of [Stacks, Tag 070U]. This file packages it
as a morphism of ringed topoi on an arbitrary chosen big site and applies to it the derived
adjunction `Lf^* ⊣ Rf_*` of [Stacks, Tag 07A6].

## Main definitions

* `Stacks.Adequate.BigSite.commStructureSheaf`: the structure sheaf of a chosen big site, as a
  sheaf of commutative rings.
* `Stacks.Adequate.BigSite.ringedSite`: the ringed site `((Sch/S)_τ, 𝒪)`.
* `Stacks.Adequate.BigSite.zariskiRingedSiteHom`: the morphism of ringed sites of
  [Stacks, Tag 070U] on a chosen big site.
* `Stacks.Adequate.BigSite.zariskiRingedToposHom`: the associated morphism of ringed topoi.
* `Stacks.Adequate.BigSite.derivedZariskiPullback` and
  `Stacks.Adequate.BigSite.derivedZariskiPushforward`: `Lf^*` and `Rf_*`.

## Main results

* `Stacks.Adequate.BigSite.isMorphismOfSites_opensToBig`: the inclusion of the small Zariski site
  is a morphism of sites.
* `Stacks.Adequate.BigSite.derivedZariskiAdjunction`: [Stacks, Tag 07A6] for this morphism,
  `Lf^* ⊣ Rf_*` on the unbounded derived categories.

## Implementation notes

The underlying category of a chosen big site has its objects one universe above its morphisms.
The derived adjunction of [Stacks, Tag 07A6] is available for a morphism of ringed topoi at
independent universes, `Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction`; what it
asks of the source is sheafification and Grothendieck abelianness of its modules at the universe
of the sections, which hold because the site is essentially small at that universe. These are
recorded below as instances on the site of a chosen big site.

The derived categories are the standard models `CategoryTheory.HasDerivedCategory.standard`, which
is where the derived functors of [Stacks, Tag 07A6] are formed.

## References

* [Stacks Project, Tag 070U](https://stacks.math.columbia.edu/tag/070U)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-! ### The ringed site and the morphism to the small Zariski site -/

/-- The structure sheaf of a chosen big site, as a sheaf of commutative rings: the sheaf
`T/S ↦ Γ(T, 𝒪_T)`. Forgetting commutativity gives `Stacks.Adequate.BigSite.structureSheaf`. -/
def BigSite.commStructureSheaf : Sheaf B.topology CommRingCat.{u} :=
  ⟨(B.toOver ⋙ Over.forget S).op ⋙ Scheme.Γ,
    Presheaf.isSheaf_of_isSheaf_comp _ _ (forget₂ CommRingCat RingCat) B.isSheaf⟩

/-- Forgetting commutativity in the commutative structure sheaf gives the structure sheaf. -/
theorem BigSite.ringSheaf_commStructureSheaf :
    Stacks.SheafOfModules.Tensor.ringSheaf B.commStructureSheaf = B.structureSheaf := rfl

/-- The ringed site `((Sch/S)_τ, 𝒪)` of a chosen big site. -/
abbrev BigSite.ringedSite : RingedSite.{u + 1, u, u} where
  C := B.category
  J := B.topology
  O := B.commStructureSheaf

/-- **The inclusion of the small Zariski site of `S` into a chosen big site is a morphism of
sites**, for sheaves of sets in the universe of the sections of the structure sheaves: it is
continuous, and its pullback of sheaves of sets is left exact. A chosen big site carries the
topology of `τ` on the big fppf category of a big fppf site, where this is
`AlgebraicGeometry.BigFppfOver.opensToBig_isMorphismOfSites`. -/
theorem BigSite.isMorphismOfSites_opensToBig :
    IsMorphismOfSites.{u} B.opensToBig (Opens.grothendieckTopology ↥S) B.topology := by
  obtain ⟨κ, base_mem, J, isSheaf, chosen⟩ := B
  obtain ⟨P, hP, e, hJ⟩ := BigSite.exists_baseOverTopology ⟨κ, base_mem, J, isSheaf, chosen⟩
  cases e
  obtain rfl := eq_of_heq hJ
  exact BigFppfOver.opensToBig_isMorphismOfSites P S hP τ.toSiteKind

/-- The comparison of structure sheaves of commutative rings along the inclusion of the small
Zariski site: over an open `U` it is the identification of `Γ(S, U)` with the global functions
of the open subscheme `U`. Forgetting commutativity gives
`Stacks.Adequate.BigSite.zariskiStructureMap`. -/
def BigSite.zariskiCommStructureMap :
    S.zariskiRingedSite.O ⟶ (B.opensToBig.sheafPushforwardContinuous CommRingCat.{u}
      (Opens.grothendieckTopology ↥S) B.topology).obj B.commStructureSheaf where
  hom :=
    { app := fun U => (Scheme.Opens.topIso U.unop).inv
      naturality := fun _ _ h =>
        (Scheme.Opens.topIso_inv_appTop (X := S) (leOfHom h.unop)).symm }

/-- **[Stacks, Tag 070U] on a chosen big site**: the morphism of ringed sites
`f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)`. -/
def BigSite.zariskiRingedSiteHom : RingedSite.HomGeneral B.ringedSite S.zariskiRingedSite where
  u := B.opensToBig
  isMorphismOfSites := B.isMorphismOfSites_opensToBig
  fsharp := B.zariskiCommStructureMap

/-- The morphism of ringed topoi `f : (Sh((Sch/S)_τ), 𝒪) ⟶ (Sh(S_Zar), 𝒪_S)` of the morphism of
ringed sites of [Stacks, Tag 070U]. -/
abbrev BigSite.zariskiRingedToposHom :
    RingedToposHom B.ringedSite.toRingedTopos S.zariskiRingedSite.toRingedTopos :=
  B.zariskiRingedSiteHom.toRingedToposHom

/-! ### The ambient instances -/

/-- The underlying category of the ringed site of a chosen big site is essentially small at the
universe of the sections. -/
instance BigSite.essentiallySmall_ringedSite_C : EssentiallySmall.{u} B.ringedSite.C :=
  B.essentiallySmall_category

/-- The underlying category of a chosen big site is essentially small at the universe of the
sections. -/
instance BigSite.essentiallySmall_category_inst : EssentiallySmall.{u} B.category :=
  B.essentiallySmall_category

/-- Presheaves of abelian groups on a chosen big site admit sheafification. -/
instance BigSite.hasSheafify_addCommGrpCat_self :
    HasSheafify B.topology AddCommGrpCat.{u} :=
  BigSite.hasSheafify_addCommGrpCat.{u, u} B

/-- On a chosen big site, a morphism of presheaves of sets becomes an isomorphism after
sheafification exactly when it is locally bijective. -/
instance BigSite.wEqualsLocallyBijective_type :
    B.topology.WEqualsLocallyBijective (Type u) :=
  have := B.essentiallySmall_category
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Presheaves of abelian groups on the ringed site of a chosen big site admit sheafification. -/
instance BigSite.hasSheafify_ringedSite :
    HasSheafify B.ringedSite.toRingedTopos.J AddCommGrpCat.{u} :=
  BigSite.hasSheafify_addCommGrpCat.{u, u} B

/-- On the ringed site of a chosen big site, a morphism of presheaves of abelian groups becomes an
isomorphism after sheafification exactly when it is locally bijective. -/
instance BigSite.wEqualsLocallyBijective_ringedSite :
    B.ringedSite.toRingedTopos.J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  have := B.essentiallySmall_category
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-- Presheaves of sets on the ringed site of a chosen big site admit sheafification. -/
instance BigSite.hasSheafify_type_ringedSite :
    HasSheafify B.ringedSite.toRingedTopos.J (Type u) :=
  B.hasSheafify_type

/-- Presheaves of abelian groups on the small Zariski ringed site of a scheme admit
sheafification. -/
instance zariskiRingedSite_hasSheafify (X : Scheme.{u}) :
    HasSheafify X.zariskiRingedSite.toRingedTopos.J AddCommGrpCat.{u} :=
  Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax.{u, u} X

/-- On the small Zariski ringed site of a scheme, a morphism of presheaves of abelian groups
becomes an isomorphism after sheafification exactly when it is locally bijective. -/
instance zariskiRingedSite_wEqualsLocallyBijective (X : Scheme.{u}) :
    X.zariskiRingedSite.toRingedTopos.J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  inferInstanceAs ((Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u})

/-- Presheaves of sets on the small Zariski ringed site of a scheme admit sheafification. -/
instance zariskiRingedSite_hasSheafify_type (X : Scheme.{u}) :
    HasSheafify X.zariskiRingedSite.toRingedTopos.J (Type u) :=
  inferInstanceAs (HasSheafify (Opens.grothendieckTopology X) (Type u))

/-- The category of sheaves of modules over the structure sheaf of a chosen big site is
Grothendieck abelian. -/
instance BigSite.isGrothendieckAbelian_ringedSite :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)) :=
  B.isGrothendieckAbelian_sheafOfModules

/-! ### `Lf^*`, `Rf_*` and their adjunction -/

/-- `Lf^* : D(𝒪_S) ⥤ D(𝒪)`, the total left derived pullback of [Stacks, Tag 06YY] along the
morphism of [Stacks, Tag 070U]. -/
abbrev BigSite.derivedZariskiPullback :=
  @Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback B.ringedSite.toRingedTopos
    S.zariskiRingedSite.toRingedTopos _ _ _ _ _ _ _ _ _ B.zariskiRingedToposHom
    (Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
      B.zariskiRingedToposHom)

/-- `Rf_* : D(𝒪) ⥤ D(𝒪_S)`, the total right derived direct image of [Stacks, Tag 07A5] along the
morphism of [Stacks, Tag 070U]. -/
abbrev BigSite.derivedZariskiPushforward :=
  @Stacks.Cohomology.DerivedPushforward.derivedPushforward B.ringedSite.toRingedTopos
    S.zariskiRingedSite.toRingedTopos _ _ _ _ _ _ _ _ _ _ B.zariskiRingedToposHom

/-- **[Stacks, Tag 07A6] for the morphism of [Stacks, Tag 070U].** The derived pullback `Lf^*`
is left adjoint to the derived direct image `Rf_*`. -/
def BigSite.derivedZariskiAdjunction :
    B.derivedZariskiPullback ⊣ B.derivedZariskiPushforward :=
  @Stacks.Cohomology.DerivedPullbackOfToposHom.derivedAdjunction B.ringedSite.toRingedTopos
    S.zariskiRingedSite.toRingedTopos _ _ _ _ _ _ _ _ _ _ _ _ _ B.zariskiRingedToposHom

end Stacks.Adequate

end
