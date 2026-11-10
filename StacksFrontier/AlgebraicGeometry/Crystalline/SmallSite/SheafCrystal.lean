module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BigComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleComparison

/-!
# Crystals in modules on the small crystalline site, at sheaf level

Let `F` be a sheaf of `𝒪_{X/S}`-modules on the small crystalline site `Cris(X/S)` of a global
crystalline situation.  Over every object `(U, T, δ)` of `Cris(X/S)` it restricts to a module
`F_T` on the ambient scheme `T`, and that restriction is again a sheaf, because the restrictions
of `(U, T, δ)` to the opens of `T` are again objects of `Cris(X/S)` and form a continuous functor.
A morphism `f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` gives an `f`-map `F_{T'} ⟶ f_* F_T`, and
the adjunction between pullback and pushforward of *sheaves* of modules turns it into the
comparison map `c_f : f^* F_{T'} ⟶ F_T` of sheaves of `𝒪_T`-modules.  The module `F` is a
*crystal in `𝒪_{X/S}`-modules* when every one of these comparison maps is an isomorphism.  This is
part (3) of [Stacks, Tag 07IS] for `𝒞 = Cris(X/S)`; part (3) for `𝒞 = CRIS(X/S)` is
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`.

## The ring level is the big site, verbatim

The small crystalline site is a full subcategory of the big one and its structure sheaf is the
restriction of the big one, so the restriction of the structure sheaf to the ambient scheme of an
object `A` of `Cris(X/S)` is *the same presheaf of rings* as the restriction of the big structure
sheaf to the ambient scheme of the underlying object `A.obj` of `CRIS(X/S)`, and likewise for the
`f`-map of a morphism; this is `CohomologyRestriction.ringRestriction_eq` and
`CohomologyRestriction.restrictionFMap_crisRing_eq` in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite`, both of which hold by `rfl`.  Nothing at the
ring level is therefore redefined here: the sheaf of
rings `𝒪_T` and the semilinearity datum of the comparison map are taken to be the big-site
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheaf` and
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafFMap` at the underlying
object and morphism, which is also how
`Crystalline.GlobalCrystallineSituation.SmallSite.IsLocallyQuasiCoherent` is stated.  In
particular the adjunction between pullback and pushforward of sheaves of modules used below is
the big site's, with its instances.

The module level is *not* the big site's: a sheaf of modules on `Cris(X/S)` is a sheaf on the
small site and is in general not the restriction of one on `CRIS(X/S)`, so its restriction to `T`
has to be built on the small site.  That is the content of
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.moduleRestrictionSheaf`,
whose underlying presheaf of modules is the small-site
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.moduleRestriction`.

## Main definitions

Everything below lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite`, the comparison maps in its subnamespace
`CohomologyRestriction`.

* `CohomologyRestriction.moduleRestrictionSheaf` — the restriction `F_T` of a sheaf of
  `𝒪_{X/S}`-modules on `Cris(X/S)` to the ambient scheme of an object, as a sheaf of modules.
* `CohomologyRestriction.moduleFMapSheaf` — the `f`-map `F_{T'} ⟶ f_* F_T` of sheaves of modules.
* `CohomologyRestriction.moduleComparisonSheaf` — the comparison map `c_f : f^* F_{T'} ⟶ F_T` of
  sheaves of `𝒪_T`-modules, [Stacks, Tag 07IQ] on the small site at sheaf level.
* `IsSheafCrystal` — part (3) of [Stacks, Tag 07IS] for `𝒞 = Cris(X/S)`, read with the comparison
  maps of sheaves of modules.
* `restrictSheafOfModules` — the restriction to `Cris(X/S)` of a sheaf of `𝒪_{X/S}`-modules on
  `CRIS(X/S)`, the inclusion being continuous.

## Main results

* `CohomologyRestriction.ringRestriction_eq` and
  `CohomologyRestriction.restrictionFMap_crisRing_eq` — the small-site restriction of the
  structure sheaf to the ambient scheme of an object, and its `f`-map, are the big-site ones at
  the underlying object and morphism.
* `CohomologyRestriction.moduleFMapSheaf_eq_moduleComparisonSheaf` — the `f`-map is recovered from
  the comparison map by the unit of the adjunction.
* `CohomologyRestriction.moduleComparisonSheaf_restrictSheafOfModules` — the comparison map of the
  restriction to `Cris(X/S)` of a sheaf of modules on `CRIS(X/S)` is the big-site comparison map
  at the underlying morphism.
* `isSheafCrystal_restrictSheafOfModules` — the restriction to `Cris(X/S)` of a crystal on
  `CRIS(X/S)` is a crystal on `Cris(X/S)`.

## What is and is not proved

What is proved is that the sheaf-level comparison map `c_f` exists on the small crystalline site,
that it determines and is determined by the `f`-map, and that the crystal condition is inherited
by restriction from the big site to the small one.  `IsSheafCrystal` is a *definition*, part (3)
of the source's definition, and nothing is proved here about which modules satisfy it.

The crystal condition is read with the comparison maps of *sheaves* of modules, as on the big
site.  The condition read with the comparison maps of presheaves of modules — that is, with
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.moduleComparison` — is
strictly stronger, the pullback of sheaves of modules being the sheafification of the pullback of
presheaves of modules; see the correction described in the module documentation of
`StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.SheafCrystal`.
It would therefore name
a smaller class of modules than [Stacks, Tag 07IS] defines, and is not the condition stated here.

The implication from the presheaf-level to the sheaf-level condition, the small-site analogue of
`Crystalline.GlobalCrystallineSituation.Thickening.isIso_moduleComparisonSheaf`, is *not* proved.
It is not derivable from the big-site statement, which is about a sheaf of modules on `CRIS(X/S)`,
and proving it directly would be a third transcription of that argument alongside the two existing
big-site/small-site mirrors of the presheaf-level comparison map; the argument is generic in the
site and belongs in one place, which is not this file.  Nothing below needs it: the crystal
transfer along restriction is proved by the identification of the two comparison maps, not by the
presheaf-level criterion.

The restriction functor of the last section is the inverse image `i^{-1}` of the morphism of topoi
of [Stacks, Tag 07IJ] at the level of modules; it is given here as the underlying construction on
a single sheaf of modules, which is what the crystal transfer needs, and not as a functor.

## References

* [Stacks Project, Tag 07IS](https://stacks.math.columbia.edu/tag/07IS)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

namespace CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} {A B : CrystallineThickening S}

/-! ### The ring level is the big site at the underlying object -/

/-- **The restriction of the structure sheaf of `Cris(X/S)` to the ambient scheme of an object is
the restriction of the structure sheaf of `CRIS(X/S)` to the ambient scheme of the underlying
object.**  The structure sheaf of the small site is the restriction of that of the big site along
the inclusion, and the restrictions of an object of `Cris(X/S)` to the opens of its ambient scheme
are those of the underlying object; so both sides are the presheaf of rings sending an open `W` to
`Γ(W, 𝒪_W)`. -/
theorem ringRestriction_eq (A : CrystallineThickening S) :
    ringRestriction A = Thickening.ringRestriction A.obj := rfl

/-- **The `f`-map of the restricted structure presheaves of a morphism of `Cris(X/S)` is that of
the underlying morphism of `CRIS(X/S)`.**  Over an open `W` of the ambient scheme of the target
both are the structure sheaf applied to the restriction of the morphism over `W`. -/
theorem restrictionFMap_crisRing_eq (g : A ⟶ B) :
    restrictionFMap (crisRing S) g =
      Thickening.restrictionFMap (GlobalCrystallineSituation.crisRing S) g.hom := rfl

/-! ### The comparison map at sheaf level -/

/-- **Stacks Project, Tag 07IQ.**  The restriction `F_T` of a sheaf of `𝒪_{X/S}`-modules on
`Cris(X/S)` to the ambient scheme of an object, as a sheaf of modules over the restricted
structure sheaf: its sections over an open `W` are the sections of `F` over the restriction
`(U ∩ W, W, δ|_W)` of the object to `W`.  The sheaf condition holds because those restrictions are
again objects of `Cris(X/S)` and form a continuous functor.  The sheaf of rings it is a module
over is the big site's at the underlying object, that being the very same presheaf of rings by
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.ringRestriction_eq`. -/
def moduleRestrictionSheaf (M : SheafOfModules.{u} (structureSheaf S))
    (A : CrystallineThickening S) :
    SheafOfModules.{u} (Thickening.ringRestrictionSheaf A.obj) where
  val := moduleRestriction (M.val : PresheafOfModules.{u} (crisRing S)) A
  isSheaf := CrystallineThickening.isSheaf_restriction A _ M.isSheaf

/-- The underlying presheaf of modules of `moduleRestrictionSheaf M A` is the restriction
`moduleRestriction` of the underlying presheaf of modules of `M` to `A`. -/
@[simp]
theorem moduleRestrictionSheaf_val (M : SheafOfModules.{u} (structureSheaf S))
    (A : CrystallineThickening S) :
    (moduleRestrictionSheaf M A).val =
      moduleRestriction (M.val : PresheafOfModules.{u} (crisRing S)) A := rfl

variable (M : SheafOfModules.{u} (structureSheaf S))

/-- **Stacks Project, Tag 07IQ.**  The `f`-map `F_{T'} ⟶ f_* F_T` of a sheaf of `𝒪_{X/S}`-modules
on `Cris(X/S)` along a morphism `f` of `Cris(X/S)`, as a morphism of sheaves of modules: it is the
`f`-map of the underlying presheaves of modules, the pushforward of a sheaf along a continuous
functor being computed by restriction. -/
def moduleFMapSheaf (g : A ⟶ B) :
    moduleRestrictionSheaf M B ⟶
      (SheafOfModules.pushforward.{u} (Thickening.ringRestrictionSheafFMap g.hom)).obj
        (moduleRestrictionSheaf M A) :=
  ⟨moduleFMap (M.val : PresheafOfModules.{u} (crisRing S)) g⟩

/-- **Stacks Project, Tag 07IQ.**  The comparison map `c_f : f^* F_{T'} ⟶ F_T` of a morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` and a sheaf of `𝒪_{X/S}`-modules `F` on
`Cris(X/S)`, a map of sheaves of `𝒪_T`-modules obtained from the `f`-map `F_{T'} ⟶ f_* F_T` by the
adjunction between pullback and pushforward of *sheaves* of modules.  The pullback is the
sheafification of the pullback of presheaves of modules, so this map is in general not the
comparison map
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.moduleComparison` of the
underlying presheaves of modules. -/
@[stacks 07IQ "the comparison map for modules on the small crystalline site, for sheaves"]
def moduleComparisonSheaf (g : A ⟶ B) :
    (SheafOfModules.pullback.{u} (Thickening.ringRestrictionSheafFMap g.hom)).obj
        (moduleRestrictionSheaf M B) ⟶ moduleRestrictionSheaf M A :=
  ((SheafOfModules.pullbackPushforwardAdjunction.{u}
      (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv
    (moduleRestrictionSheaf M B) (moduleRestrictionSheaf M A)).symm (moduleFMapSheaf M g)

/-- The `f`-map of a sheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` is recovered from the comparison
map of sheaves of modules by the unit of the adjunction between pullback and pushforward, so the
two carry the same information. -/
theorem moduleFMapSheaf_eq_moduleComparisonSheaf (g : A ⟶ B) :
    moduleFMapSheaf M g =
      (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (Thickening.ringRestrictionSheafFMap g.hom)).homEquiv
        (moduleRestrictionSheaf M B) (moduleRestrictionSheaf M A) (moduleComparisonSheaf M g) :=
  (Equiv.apply_symm_apply _ _).symm

end CohomologyRestriction

/-- **Stacks Project, Tag 07IS, part (3) for `𝒞 = Cris(X/S)`.**  A sheaf of `𝒪_{X/S}`-modules on
the small crystalline site is a *crystal in `𝒪_{X/S}`-modules* when for every morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` the comparison map `c_f : f^* F_{T'} ⟶ F_T` of
*sheaves* of `𝒪_T`-modules is an isomorphism.

This is the sheaf-level reading of the condition, the pullback being the pullback of sheaves of
modules, that is, the sheafification of the pullback of presheaves of modules.  It is the reading
the source intends and it is weaker than the condition read with the comparison maps of presheaves
of modules.  The same clause for the big crystalline site is
`Crystalline.GlobalCrystallineSituation.IsSheafCrystal`. -/
@[stacks 07IS
  "part (3): crystal in modules on the small site Cris(X/S), with the comparison maps of sheaves"]
def IsSheafCrystal {S : GlobalCrystallineSituation.{u}}
    (M : SheafOfModules.{u} (structureSheaf S)) : Prop :=
  ∀ (A B : CrystallineThickening S) (k : A ⟶ B),
    IsIso (CohomologyRestriction.moduleComparisonSheaf M k)

/-! ### Restriction from the big site to the small site -/

variable {S : GlobalCrystallineSituation.{u}}

/-- **The restriction to `Cris(X/S)` of a sheaf of `𝒪_{X/S}`-modules on `CRIS(X/S)`**, the
inclusion `Cris(X/S) ⥤ CRIS(X/S)` being continuous: its sections over an object of the small site
are the sections of the given module over the underlying object of the big site, and it is a
module over the structure sheaf of the small site, that being the restriction of the structure
sheaf of the big site. -/
def restrictSheafOfModules (N : SheafOfModules.{u} (crystallineStructureSheaf S)) :
    SheafOfModules.{u} (structureSheaf S) where
  val := (PresheafOfModules.pushforward₀ (CrystallineThickening.ι S)
    (GlobalCrystallineSituation.crisRing S)).obj N.val
  isSheaf := (CrystallineThickening.ι S).op_comp_isSheaf_of_isSheaf _ _ _ N.isSheaf

namespace CohomologyRestriction

variable {A B : CrystallineThickening S}

/-- **The restriction to the ambient scheme of an object of `Cris(X/S)` of the restriction to
`Cris(X/S)` of a sheaf of modules on `CRIS(X/S)` is its big-site restriction to the ambient scheme
of the underlying object.**  Both are the given module evaluated on the restrictions of the
underlying object to the opens of its ambient scheme. -/
theorem moduleRestrictionSheaf_restrictSheafOfModules
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (A : CrystallineThickening S) :
    moduleRestrictionSheaf (restrictSheafOfModules N) A =
      Thickening.moduleRestrictionSheaf N A.obj := rfl

/-- **The sheaf-level comparison map of the restriction to `Cris(X/S)` of a sheaf of modules on
`CRIS(X/S)` is the big-site comparison map of the underlying morphism.**  The two `f`-maps agree,
being the given module applied to the restrictions of the underlying morphism over the opens of
the ambient scheme of its target, and the adjunction transposing them is the same one, the ring
level of the small site being that of the big site by `restrictionFMap_crisRing_eq`. -/
theorem moduleComparisonSheaf_restrictSheafOfModules
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (g : A ⟶ B) :
    moduleComparisonSheaf (restrictSheafOfModules N) g =
      Thickening.moduleComparisonSheaf N g.hom := rfl

end CohomologyRestriction

/-- **The restriction to `Cris(X/S)` of a crystal in `𝒪_{X/S}`-modules on `CRIS(X/S)` is a crystal
in `𝒪_{X/S}`-modules on `Cris(X/S)`.**  A morphism of the small site is a morphism of the big site
between the underlying objects, and the comparison maps of the restricted module are the big-site
comparison maps of those morphisms. -/
theorem isSheafCrystal_restrictSheafOfModules
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (h : GlobalCrystallineSituation.IsSheafCrystal N) :
    IsSheafCrystal (restrictSheafOfModules N) := fun A B k ↦
  (CohomologyRestriction.moduleComparisonSheaf_restrictSheafOfModules N k) ▸ h A.obj B.obj k.hom

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
