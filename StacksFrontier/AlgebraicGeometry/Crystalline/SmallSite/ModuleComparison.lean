module

public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CohomologyRestriction

/-!
# The comparison map `c_f` for modules on the small crystalline site

Fix a global crystalline situation `(p, (S, I, γ), X)`.  A presheaf of `𝒪_{X/S}`-modules `F` on
the small crystalline site `Cris(X/S)` restricts, over every object `(U, T, δ)`, to a presheaf of
`𝒪_T`-modules `F_T` on the ambient scheme `T`, by `F_T(W) = F(U ∩ W, W, δ|_W)`; and a morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` gives the `f`-map `F_{T'} ⟶ f_* F_T` of
[Stacks, Tag 07IP], equivalently, by adjunction, the `𝒪_T`-linear comparison morphism
`c_f : f^* F_{T'} ⟶ F_T` of [Stacks, Tag 07IQ].

Both already exist for the big crystalline category `CRIS(X/S)`
(`Crystalline.GlobalCrystallineSituation.Thickening.moduleFMap` and
`Thickening.moduleComparison`).  This file is the same construction on the small site, which is
what hypothesis (2) of [Stacks, Tag 07JN] is stated about: the restrictions of an object of
`Cris(X/S)` to the opens of its ambient scheme are again objects of `Cris(X/S)`, so a sheaf on
the small site restricts to `T` without reference to the big site, and the small-site
restriction is *not* the restriction of a big-site presheaf.

## Main definitions

Everything below lives in the namespace
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction`.

* `ringRestriction` — the restriction of the structure presheaf of `Cris(X/S)` to the ambient
  scheme of an object, as a presheaf of rings on that scheme.
* `moduleRestriction` — the restriction `F_T` of a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)`
  to the ambient scheme of an object, as a presheaf of modules over `ringRestriction`.
* `moduleFMap` — the `f`-map `F_{T'} ⟶ f_* F_T` of a morphism of `Cris(X/S)`, for presheaves of
  modules.
* `moduleComparison` — **the comparison morphism `c_f : f^* F_{T'} ⟶ F_T`** of a morphism of
  `Cris(X/S)`, obtained from the `f`-map by the adjunction between pullback and pushforward of
  presheaves of modules.
* `IsSurjectiveComparison` — **hypothesis (2) of [Stacks, Tag 07JN]**: for every morphism of
  `Cris(X/S)` whose map on ambient schemes is a closed immersion, the comparison morphism `c_f`
  is surjective.

## Main results

* `moduleRestriction_obj` and `moduleFMap_app` — the sections of `F_T` over an open `W` of `T`
  are the sections of `F` over the restriction of the object to `W`, and the `f`-map over `W` is
  `F` applied to the restriction of `f` over `W`.
* `moduleFMap_eq_moduleComparison` — the `f`-map is recovered from the comparison morphism by the
  unit of the adjunction, so the two carry the same information.

## Implementation notes

The comparison morphism exists on the small crystalline site and it determines, and is determined
by, the `f`-map; `IsSurjectiveComparison` is a *definition*, the predicate that [Stacks, Tag 07JN]
assumes, and nothing about which modules satisfy it is proved *here*. A crystal satisfies it, by
`Crystalline.GlobalCrystallineSituation.SmallSite.isSurjectiveComparison_of_isSheafCrystal`, and
the predicate is closed under tensor products and exterior powers, by
`isSurjectiveComparison_tensorModules` and `isSurjectiveComparison_extPowModules`. For
`F = Ω_{X/S}` the corresponding statement on the big crystalline category is [Stacks, Tag 07KM]
part (2), `Crystalline.GlobalCrystallineSituation.isLocallySurjective_moduleComparison`; it is not
transported to the small site here, the small-site restriction of the small-site `Ω_{X/S}` being
the big-site restriction of the big-site `Ω_{X/S}` only after the identification
`Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction.restriction_comp_ι`, and
the pullback functors on the two sides having then to be identified as well.

Surjectivity is local surjectivity for the Zariski topology on the ambient scheme, exactly as in
`Crystalline.GlobalCrystallineSituation.isLocallySurjective_moduleComparison`: the restriction of
a presheaf of modules to `T` is a presheaf and not a sheaf, so objectwise surjectivity is the
wrong condition and is in general false.

## References

* [Stacks Project, Tag 07IP](https://stacks.math.columbia.edu/tag/07IP)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KM](https://stacks.math.columbia.edu/tag/07KM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}}

/-- The restriction of the structure presheaf of the small crystalline site to the ambient scheme
of an object, as a presheaf of rings on that scheme: over an open `W` it is the ring of global
sections of the ambient scheme of the restriction `(U ∩ W, W, δ|_W)`. -/
abbrev ringRestriction (A : CrystallineThickening S) :
    (A.obj.thickening.target.scheme.Opens)ᵒᵖ ⥤ RingCat.{u} :=
  restriction (crisRing S) A

/-- **The restriction `F_T` of a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` to the ambient
scheme of an object**, as a presheaf of modules over the restriction of the structure presheaf:
its sections over an open `W` are the sections of `F` over the restriction of the object to `W`.
This is [Stacks, Tag 07IQ] on the small crystalline site. -/
def moduleRestriction (M : PresheafOfModules.{u} (crisRing S)) (A : CrystallineThickening S) :
    PresheafOfModules.{u} (ringRestriction A) :=
  (PresheafOfModules.pushforward₀ (CrystallineThickening.restrictOpenFunctor A)
    (crisRing S)).obj M

/-- The sections of `moduleRestriction M A` over an open `W` of the ambient scheme are the
sections of `M` over the restriction `A.restrictOpen W` of the object to `W`. -/
@[simp]
theorem moduleRestriction_obj (M : PresheafOfModules.{u} (crisRing S))
    (A : CrystallineThickening S) (W : A.obj.thickening.target.scheme.Opens) :
    (moduleRestriction M A).obj (op W) = M.obj (op (A.restrictOpen W)) := rfl

/-- **The `f`-map `F_{T'} ⟶ f_* F_T` of a presheaf of `𝒪_{X/S}`-modules along a morphism `f` of
`Cris(X/S)`**: over an open `W` of the ambient scheme of the target it is the presheaf of modules
applied to the restriction of `f` over `W`, a map semilinear over the `f`-map of the structure
presheaf. -/
def moduleFMap (M : PresheafOfModules.{u} (crisRing S)) {A B : CrystallineThickening S}
    (g : A ⟶ B) :
    moduleRestriction M B ⟶
      (PresheafOfModules.pushforward (F := Opens.map g.hom.targetHom.hom.base)
        (restrictionFMap (crisRing S) g)).obj (moduleRestriction M A) :=
  PresheafOfModules.pushforwardOfNatTrans
    (CrystallineThickening.restrictOpenFunctorMap g) (crisRing S) M

/-- Over an open `W` of the ambient scheme of the target, the `f`-map `moduleFMap M g` is `M`
applied to the restriction `CrystallineThickening.restrictOpenMap g W` of `g` over `W`. -/
@[simp]
theorem moduleFMap_app (M : PresheafOfModules.{u} (crisRing S)) {A B : CrystallineThickening S}
    (g : A ⟶ B) (W : (B.obj.thickening.target.scheme.Opens)ᵒᵖ) :
    (moduleFMap M g).app W = M.map (CrystallineThickening.restrictOpenMap g W.unop).op := rfl

/-- **The comparison morphism `c_f : f^* F_{T'} ⟶ F_T`** of a morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` and a presheaf of `𝒪_{X/S}`-modules `F`, a map of
`𝒪_T`-modules obtained from the `f`-map `F_{T'} ⟶ f_* F_T` by the adjunction between pullback and
pushforward of presheaves of modules along the `f`-map of the structure presheaf.  This is the
map whose surjectivity is hypothesis (2) of [Stacks, Tag 07JN]. -/
def moduleComparison (M : PresheafOfModules.{u} (crisRing S)) {A B : CrystallineThickening S}
    (g : A ⟶ B) :
    (PresheafOfModules.pullback (F := Opens.map g.hom.targetHom.hom.base)
        (restrictionFMap (crisRing S) g)).obj (moduleRestriction M B) ⟶ moduleRestriction M A :=
  ((PresheafOfModules.pullbackPushforwardAdjunction
    (restrictionFMap (crisRing S) g)).homEquiv (moduleRestriction M B)
      (moduleRestriction M A)).symm (moduleFMap M g)

/-- The `f`-map of a presheaf of `𝒪_{X/S}`-modules on `Cris(X/S)` is recovered from the
comparison morphism by the unit of the adjunction between pullback and pushforward of presheaves
of modules, so the two carry the same information. -/
theorem moduleFMap_eq_moduleComparison (M : PresheafOfModules.{u} (crisRing S))
    {A B : CrystallineThickening S} (g : A ⟶ B) :
    moduleFMap M g =
      ((PresheafOfModules.pullbackPushforwardAdjunction
        (restrictionFMap (crisRing S) g)).homEquiv (moduleRestriction M B)
          (moduleRestriction M A)) (moduleComparison M g) :=
  (Equiv.apply_symm_apply _ _).symm

/-- **Hypothesis (2) of [Stacks, Tag 07JN].**  A presheaf of `𝒪_{X/S}`-modules on the small
crystalline site has *surjective closed immersion comparison maps* when for every morphism
`f : (U, T, δ) ⟶ (U', T', δ')` of `Cris(X/S)` whose map `T ⟶ T'` on ambient schemes is a closed
immersion the comparison morphism `c_f : f^* F_{T'} ⟶ F_T` is surjective, that is, every section
of `F_T` is, on the members of an open covering of `T`, in the image of `c_f`. -/
def IsSurjectiveComparison (M : PresheafOfModules.{u} (crisRing S)) : Prop :=
  ∀ {A B : CrystallineThickening S} (g : A ⟶ B), IsClosedImmersion g.hom.targetHom.hom →
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology A.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (ringRestriction A)).map (moduleComparison M g))

end Crystalline.GlobalCrystallineSituation.SmallSite.CohomologyRestriction

end

end
