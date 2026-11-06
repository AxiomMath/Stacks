module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedStalkLeftAdjoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The stalk of a derived direct image, the strict henselization and the geometric fibre

Let `f : X ⟶ S` be a morphism of schemes, let `K` be an object of the unbounded derived category
`D(X_étale)` of abelian sheaves on the small étale site of `X`, and let `s` be a geometric point
of `S`. Writing `p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` for the projection, there are canonical maps

`(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`.

This file constructs both of them, together with the geometry they are attached to, the
restriction map on unbounded derived global sections which produces the second, and the unbounded
derived direct image which the first is a stalk of.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso` — the composition isomorphism for inverse
  image of abelian étale sheaves.
* `Stacks.EtaleCohomology.smallEtaleGlobalSectionsRestrictionAb` — restriction of global sections
  of an abelian étale sheaf to global sections of its inverse image, along a morphism of schemes.
* `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction` — the canonical map
  `RΓ(Z, M) ⟶ RΓ(T, c⁻¹M)` on unbounded derived categories, for a morphism of schemes
  `c : T ⟶ Z`.
* `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAb` and
  `Stacks.EtaleCohomology.smallEtaleDerivedPushforwardAbUnit` — unbounded derived direct image
  `Rf_*` of abelian sheaves on the small étale sites, and the unit of that derivation.
* `AlgebraicGeometry.strictHenselizationBaseChange` — the base change
  `X ×_S Spec(𝒪^{sh}_{S,s})` of `f` to the strict henselization at `s`, with its two projections
  `AlgebraicGeometry.strictHenselizationBaseChangeToSource` and
  `AlgebraicGeometry.strictHenselizationBaseChangeToStrictHenselization`.
* `AlgebraicGeometry.geometricFibre` — the geometric fibre `X_s`, with its two projections.
* `AlgebraicGeometry.geometricFibreToStrictHenselizationBaseChange` — the canonical morphism
  `X_s ⟶ X ×_S Spec(𝒪^{sh}_{S,s})` over `X`, induced by the canonical lift of the geometric
  point to the strict henselization.
* `AlgebraicGeometry.strictHenselizationSectionsToFibreSections` — **[Stacks, Tag 0GIX]** the
  second canonical map of the source, `RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`,
  natural in `K`.
* `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb` — the map on abelian
  sheaves `(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)` which the first map derives from.
* `AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections` — **[Stacks, Tag
  0GIX]** the first canonical map of the source,
  `(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)`, natural in `K`.

## Main results

* `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSectionsRestriction_fac_app` — on every complex
  of abelian étale sheaves the derived restriction map factors the degreewise restriction of
  sections through the unit of the derivation of global sections, which determines it.
* `AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections_fac_app` — on every
  complex of abelian étale sheaves the map from the stalk factors the map on sheaves through the
  unit of the derivation of direct image, which determines it.
* `AlgebraicGeometry.geometricFibrePullbackAbCompIso_hom`,
  `AlgebraicGeometry.geometricFibrePullbackAbCompIso_inv` and their forms at a sheaf
  `..._hom_app`, `..._inv_app` — the identification of the two iterated inverse images, written
  out. Its body is sealed, so these four equations are how consumers read it; see the
  implementation notes.

## Implementation notes

*The restriction map.* For a morphism of schemes `c : T ⟶ Z` the restriction of sections of
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb` at the terminal object of the small étale
site of `Z` is the map `Γ(Z, M) ⟶ Γ(T, c⁻¹M)` on abelian sheaves. Inverse image is exact, so it
acts on unbounded derived categories degreewise, and unbounded derived global sections on `Z` are
a total right derived functor; the map on derived categories is therefore the unique one
factoring the degreewise map through the two units, which is what
`CategoryTheory.Functor.rightDerivedDesc` produces. This is the same descent that
`AlgebraicGeometry.vanishingCyclesMap` performs out of the exact stalk functor, the difference
being that here the source of the descent is the derivation of global sections rather than the
degreewise action of an exact functor.

*The map to the fibre.* The geometric fibre maps to the base change to the strict henselization
over `X`, because the geometric point lifts canonically to the strict henselization
(`AlgebraicGeometry.geometricPointToStrictHenselization`). The second map of the source is the
restriction map along that morphism, evaluated at `p⁻¹K`; since `X_s ⟶ X ×_S Spec(𝒪^{sh}_{S,s})`
followed by `p` is the projection `X_s ⟶ X`, the composition isomorphism for inverse images
identifies the target with `RΓ(X_s, K|_{X_s})`.

*The map from the stalk.* On abelian sheaves it is not built from a base change map but from the
initiality of the strict henselization among the étale neighbourhoods of `s`, which is what makes
a base change map exist in the first place. The base change `X ×_S Spec(𝒪^{sh}_{S,s})` is a
scheme over the strict henselization, so `AlgebraicGeometry.etaleStalkToSectionsAb` — the map of
Stacks 0GJN on sheaves — carries a germ at `s` of a section of `f_*F` over an étale neighbourhood
`V` of `s` to its restriction along `X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X ×_S V`, a global section of
`p⁻¹f⁻¹f_*F`; the counit of the inverse-image/direct-image adjunction then lands it in
`Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`. No isomorphism is inverted anywhere, so no vanishing
theorem for the strictly henselian base enters.

The passage to unbounded derived categories is again `CategoryTheory.Functor.rightDerivedDesc`,
this time out of the stalk of the derived direct image. That composite is a right derived functor
of the stalk of the direct image by the Mathlib instance which postcomposes a right derived
functor with a left adjoint; so what is needed is that the derived stalk is a left adjoint, which
is `Stacks.EtaleCohomology.smallEtaleStalkAb_mapDerivedCategory_isLeftAdjoint`: the right adjoint
of the stalk is the skyscraper sheaf functor of the point, which is exact because products of
abelian groups are, so the adjunction descends to the unbounded derived categories degreewise.
The map from the stalk is therefore unconditional, as the source asserts: nothing is assumed of
`f`, of `K` or of `s`, with `K` ranging over the whole unbounded derived category and `f` an
arbitrary morphism of schemes.

*The composition isomorphism for inverse image* is not available in the library and is built here
by conjugating the composition isomorphism for direct image
(`Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso`) through the two adjunctions: left
adjoints of isomorphic right adjoints are isomorphic.

*Why the identification of the two iterated inverse images has a sealed body.*
`AlgebraicGeometry.geometricFibrePullbackAbCompIso` is that composition isomorphism followed by
`CategoryTheory.eqToIso` of a `congrArg` of `CategoryTheory.Limits.pullback.lift_fst`. Reducing
the transport makes the kernel evaluate that whole limit proof, and it does not terminate inside
the kernel's budget: a consumer identity about the composite — the comparison of the
three composition isomorphisms in front of the identification, proved by `rw` with
`CategoryTheory.Functor.mapDerivedCategoryFactorsh_inv_comp_mapDerivedCategoryCompIso_hom` —
fails with `(kernel) deterministic timeout` after 20.8 s while the body is exposed, and checks
in 0.2 s once it is sealed. So the definition carries `no_expose`, and the body is recorded here,
in the module where it is available, as the four equations listed above. Consumers rewrite with
those; nothing downstream can force a definitional comparison through the transport any more.

*The composition clause.* The source's last sentence — that the composite of the two maps is the
usual base change map `(Rf_*K)_s ⟶ RΓ(X_s, K|_{X_s})` — is
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections_comp_fibreSections`
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedStalkFibreComposition.lean`). It needs the derived comparison of the
stalk with sections on the geometric point
(`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedGeometricStalkSections.lean`), the global-sections clause of Stacks
0D6H (`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedLerayGlobalSectionsAb.lean`) and the derived base change map of
Stacks 0A2A, none of which this module imports.

*The maps are those of the source.* The source defines the two maps as global sections of the
derived base change maps of the two squares of its diagram. Those definitions, with no hypothesis
on the existence of the unbounded derived functors, and the composition clause for them, are in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DerivedStalkFibreBaseChangeMaps.lean`, each with its own Stacks 0GIX
registration; that the maps constructed here are those is
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSections_eq_baseChange` and
`AlgebraicGeometry.strictHenselizationSectionsToFibreSections_eq_baseChange`.

## References

* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 03PS](https://stacks.math.columbia.edu/tag/03PS)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The composition isomorphism for inverse image of abelian étale sheaves -/

section Comp

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- The composition isomorphism `a⁻¹ ∘ b⁻¹ ≅ (a ≫ b)⁻¹` for inverse image of abelian sheaves on
the small étale sites: the conjugate, under the inverse-image/direct-image adjunctions, of the
composition isomorphism `Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso` for direct
image. -/
def smallEtalePullbackAbCompIso :
    smallEtalePullbackAb b ⋙ smallEtalePullbackAb a ≅ smallEtalePullbackAb (a ≫ b) :=
  Adjunction.leftAdjointUniq ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a))
    (Adjunction.ofNatIsoRight (smallEtaleAdjunctionAb (a ≫ b))
      (smallEtalePushforwardAbCompIso a b).symm)

end Comp

/-! ### Restriction of global sections along a morphism of schemes -/

section Restriction

variable {Z T : Scheme.{u}} (c : T ⟶ Z)

/-- Restriction of global sections of an abelian sheaf on the small étale site of `Z` to global
sections of its inverse image on `T`, along a morphism of schemes `c : T ⟶ Z`: the restriction of
sections of `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb` at the terminal object of the
small étale site of `Z`, which is the identity object. -/
def smallEtaleGlobalSectionsRestrictionAb :
    Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1} ⟶
      smallEtalePullbackAb c ⋙ Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1} :=
  (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1} (isTerminalEtaleMkId Z)).hom ≫
    smallEtaleSectionsPullbackAb c (Scheme.Etale.mk (𝟙 Z)) c (Category.comp_id c)

variable
  [((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]

/-- The canonical map `RΓ(Z, M) ⟶ RΓ(T, c⁻¹M)` on unbounded derived categories of abelian sheaves
on the small étale sites, for a morphism of schemes `c : T ⟶ Z`, natural in `M`.

Unbounded derived global sections on `Z` are a total right derived functor of global sections, so
the restriction of sections on sheaves extends uniquely to a map of derived categories factoring
it through the units; that is the map. -/
def smallEtaleDerivedGlobalSectionsRestriction :
    smallEtaleDerivedGlobalSections Z ⟶
      smallEtaleDerivedPullbackAb c ⋙ smallEtaleDerivedGlobalSections T :=
  (smallEtaleDerivedGlobalSections Z).rightDerivedDesc (smallEtaleDerivedGlobalSectionsUnit Z)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ))
    (smallEtaleDerivedPullbackAb c ⋙ smallEtaleDerivedGlobalSections T)
    (Stacks.DerivedFunctor.exactDerivedDescUnit
      (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) (smallEtalePullbackAb c)
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) (smallEtaleDerivedGlobalSections T)
      (smallEtaleDerivedGlobalSectionsUnit T) (smallEtaleGlobalSectionsRestrictionAb c))

/-- On every complex of abelian sheaves on the small étale site of `Z`, the derived restriction
map factors the degreewise restriction of sections through the unit of the derivation of global
sections on `T`, read through the identification of the degreewise action of inverse image with
its action on derived categories.

Since derived global sections on `Z` are a right derived functor, this property determines the
map. -/
theorem smallEtaleDerivedGlobalSectionsRestriction_fac_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedGlobalSectionsUnit Z).app J ≫
        (smallEtaleDerivedGlobalSectionsRestriction c).app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) (smallEtalePullbackAb c)
          (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
          (smallEtaleGlobalSectionsRestrictionAb c)).app J) ≫
        (smallEtaleDerivedGlobalSectionsUnit T).app
            (((smallEtalePullbackAb c).mapHomotopyCategory (.up ℤ)).obj J) ≫
          (smallEtaleDerivedGlobalSections T).map
            ((smallEtalePullbackAb c).mapDerivedCategoryFactorsh.inv.app J) := by
  rw [← Stacks.DerivedFunctor.exactDerivedDescUnit_app]
  exact Functor.rightDerived_fac_app (smallEtaleDerivedGlobalSections Z)
    (smallEtaleDerivedGlobalSectionsUnit Z)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ))
    (smallEtaleDerivedPullbackAb c ⋙ smallEtaleDerivedGlobalSections T) _ J

end Restriction

/-! ### Unbounded derived direct image -/

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))]

/-- Unbounded derived direct image `Rf_*` of abelian sheaves on the small étale sites along a
morphism of schemes: the total right derived functor of direct image, on the localization of the
homotopy category of cochain complexes at the quasi-isomorphisms.

The definition takes the existence of the derivation as an instance argument. That instance is
a theorem for every morphism of schemes:
`Stacks.EtaleCohomology.hasRightDerivedFunctor_smallEtalePushforwardAb`, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleUnboundedDerivations`, proved from
K-injective resolutions in the Grothendieck abelian category of abelian étale sheaves (and likewise
`Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor` for
`Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections`). -/
abbrev smallEtaleDerivedPushforwardAb :
    smallEtaleDerivedCategory X ⥤ smallEtaleDerivedCategory Y :=
  ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))

/-- The unit of the derivation of direct image: the comparison from the degreewise direct image
of a complex to its unbounded derived direct image. -/
abbrev smallEtaleDerivedPushforwardAbUnit :
    (smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ smallEtaleDerivedPushforwardAb f :=
  ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))

end Pushforward

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The base change to the strict henselization and the geometric fibre -/

section Geometry

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)

/-- The base change `X ×_S Spec(𝒪^{sh}_{S,s})` of a morphism `f : X ⟶ S` to the strict
henselization of `S` at a geometric point `s`. -/
abbrev strictHenselizationBaseChange : Scheme.{u} :=
  pullback f (strictHenselizationToBase B S hS s)

/-- The projection `p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X`. -/
abbrev strictHenselizationBaseChangeToSource :
    strictHenselizationBaseChange B hS f s ⟶ X :=
  pullback.fst f (strictHenselizationToBase B S hS s)

/-- The projection `X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ Spec(𝒪^{sh}_{S,s})`, the base change of `f`. -/
abbrev strictHenselizationBaseChangeToStrictHenselization :
    strictHenselizationBaseChange B hS f s ⟶ strictHenselization B S hS s :=
  pullback.snd f (strictHenselizationToBase B S hS s)

/-- The geometric fibre `X_s` of a morphism `f : X ⟶ S` at a geometric point `s` of `S`. -/
abbrev geometricFibre : Scheme.{u} :=
  pullback f s.hom

/-- The projection `X_s ⟶ X` from the geometric fibre, along which an object of `D(X_étale)` is
restricted to the fibre. -/
abbrev geometricFibreToSource : geometricFibre f s ⟶ X :=
  pullback.fst f s.hom

/-- The structure morphism `X_s ⟶ s` of the geometric fibre. -/
abbrev geometricFibreToPoint : geometricFibre f s ⟶ s.source :=
  pullback.snd f s.hom

/-- The canonical morphism from the geometric fibre to the base change to the strict
henselization: the geometric point lifts canonically to the strict henselization, so the two
projections of the geometric fibre induce a morphism to the fibre product. -/
def geometricFibreToStrictHenselizationBaseChange :
    geometricFibre f s ⟶ strictHenselizationBaseChange B hS f s :=
  pullback.lift (geometricFibreToSource f s)
    (geometricFibreToPoint f s ≫ geometricPointToStrictHenselization B S hS s)
    (by
      rw [Category.assoc, geometricPointToStrictHenselization_comp]
      exact pullback.condition)

/-- The canonical morphism from the geometric fibre to the base change to the strict
henselization lies over `X`. -/
@[reassoc]
theorem geometricFibreToStrictHenselizationBaseChange_comp_toSource :
    geometricFibreToStrictHenselizationBaseChange B hS f s ≫
        strictHenselizationBaseChangeToSource B hS f s = geometricFibreToSource f s :=
  pullback.lift_fst _ _ _

/-- Inverse image along the projection `p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` followed by inverse
image along the canonical morphism `X_s ⟶ X ×_S Spec(𝒪^{sh}_{S,s})` is restriction to the
geometric fibre: the composition isomorphism for inverse images, read through the factorization
of the projection `X_s ⟶ X`. -/
@[no_expose]
def geometricFibrePullbackAbCompIso :
    smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtalePullbackAb (geometricFibreToStrictHenselizationBaseChange B hS f s) ≅
      smallEtalePullbackAb (geometricFibreToSource f s) :=
  smallEtalePullbackAbCompIso (geometricFibreToStrictHenselizationBaseChange B hS f s)
      (strictHenselizationBaseChangeToSource B hS f s) ≪≫
    eqToIso (congrArg (fun m : geometricFibre f s ⟶ X => smallEtalePullbackAb m)
      (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s))

private theorem geometricFibrePullbackAbCompIso_hom_aux :
    (geometricFibrePullbackAbCompIso B hS f s).hom =
      (smallEtalePullbackAbCompIso (geometricFibreToStrictHenselizationBaseChange B hS f s)
          (strictHenselizationBaseChangeToSource B hS f s)).hom ≫
        eqToHom (congrArg (fun m : geometricFibre f s ⟶ X => smallEtalePullbackAb m)
          (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s)) :=
  rfl

private theorem geometricFibrePullbackAbCompIso_inv_aux :
    (geometricFibrePullbackAbCompIso B hS f s).inv =
      eqToHom (congrArg (fun m : geometricFibre f s ⟶ X => smallEtalePullbackAb m)
          (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s)).symm ≫
        (smallEtalePullbackAbCompIso (geometricFibreToStrictHenselizationBaseChange B hS f s)
          (strictHenselizationBaseChangeToSource B hS f s)).inv :=
  rfl

/-- **The identification of the two iterated inverse images, written out.** It is the composition
isomorphism `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso` for inverse images followed by
the transport along the factorization
`AlgebraicGeometry.geometricFibreToStrictHenselizationBaseChange_comp_toSource` of the projection
from the geometric fibre.

This is the definition, recorded as an equation in the module where the body is available. The
body itself is sealed, because the transport is `CategoryTheory.eqToIso` of a `congrArg` of
`CategoryTheory.Limits.pullback.lift_fst`: reducing the transport forces that whole limit proof
to be evaluated, and a definitional comparison which unfolds it does not terminate inside the
kernel's budget. Consumers use this equation, and
`AlgebraicGeometry.geometricFibrePullbackAbCompIso_hom_app` at a sheaf, in place of unfolding. -/
alias geometricFibrePullbackAbCompIso_hom := geometricFibrePullbackAbCompIso_hom_aux

/-- The identification of the two iterated inverse images, read in the other direction: the
transport backwards, followed by the inverse of the composition isomorphism for inverse images. -/
alias geometricFibrePullbackAbCompIso_inv := geometricFibrePullbackAbCompIso_inv_aux

/-- The identification of the two iterated inverse images at an abelian sheaf: the composition
isomorphism for inverse images, followed by the transport of objects along the factorization of
the projection from the geometric fibre. -/
theorem geometricFibrePullbackAbCompIso_hom_app
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (geometricFibrePullbackAbCompIso B hS f s).hom.app F =
      (smallEtalePullbackAbCompIso (geometricFibreToStrictHenselizationBaseChange B hS f s)
          (strictHenselizationBaseChangeToSource B hS f s)).hom.app F ≫
        eqToHom (congrArg (fun m : geometricFibre f s ⟶ X => (smallEtalePullbackAb m).obj F)
          (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s)) := by
  rw [geometricFibrePullbackAbCompIso_hom, NatTrans.comp_app, eqToHom_app]

/-- The identification of the two iterated inverse images at an abelian sheaf, read in the other
direction. -/
theorem geometricFibrePullbackAbCompIso_inv_app
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (geometricFibrePullbackAbCompIso B hS f s).inv.app F =
      eqToHom (congrArg (fun m : geometricFibre f s ⟶ X => (smallEtalePullbackAb m).obj F)
          (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s)).symm ≫
        (smallEtalePullbackAbCompIso (geometricFibreToStrictHenselizationBaseChange B hS f s)
          (strictHenselizationBaseChangeToSource B hS f s)).inv.app F := by
  rw [geometricFibrePullbackAbCompIso_inv, NatTrans.comp_app, eqToHom_app]

end Geometry

/-! ### The map to the geometric fibre -/

section Fibre

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)
  [((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology (geometricFibre f s))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (geometricFibre f s)) Ab.{u + 1}) (.up ℤ))]

/-- **Stacks 0GIX, the map to the fibre.** The canonical map

`RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K) ⟶ RΓ(X_s, K|_{X_s})`

for an object `K` of the unbounded derived category of abelian sheaves on the small étale site of
`X`, natural in `K`, where `p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` is the projection.

It is the derived restriction map along the canonical morphism
`X_s ⟶ X ×_S Spec(𝒪^{sh}_{S,s})` over `X`, after identifying the inverse image along that
morphism of `p⁻¹K` with the restriction of `K` to the geometric fibre. -/
@[stacks 0GIX "the map to the fibre"]
def strictHenselizationSectionsToFibreSections :
    smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s) ⟶
      smallEtaleDerivedPullbackAb (geometricFibreToSource f s) ⋙
        smallEtaleDerivedGlobalSections (geometricFibre f s) :=
  Functor.whiskerLeft
      (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s))
      (smallEtaleDerivedGlobalSectionsRestriction
        (geometricFibreToStrictHenselizationBaseChange B hS f s)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((Functor.mapDerivedCategoryCompIso _ _).hom ≫
        NatTrans.mapDerivedCategory (geometricFibrePullbackAbCompIso B hS f s).hom)
      (smallEtaleDerivedGlobalSections (geometricFibre f s))

end Fibre

/-! ### The map from the stalk of the derived direct image -/

section Stalk

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)

/-- Inverse image along `f`, followed by inverse image along the projection
`p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X`, is inverse image along the structure morphism of the base
change over `S`: the composition isomorphism for inverse images, read through the commutativity
of the fibre product square. -/
def strictHenselizationBaseChangePullbackAbCompIso :
    smallEtalePullbackAb f ⋙
        smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ≅
      smallEtalePullbackAb (strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
        strictHenselizationToBase B S hS s) :=
  smallEtalePullbackAbCompIso (strictHenselizationBaseChangeToSource B hS f s) f ≪≫
    eqToIso (congrArg (fun m : strictHenselizationBaseChange B hS f s ⟶ S =>
      smallEtalePullbackAb m) pullback.condition)

/-- The map on abelian sheaves `(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`, natural in `F`.

The base change `X ×_S Spec(𝒪^{sh}_{S,s})` is a scheme over the strict henselization of `S` at
`s`, so `AlgebraicGeometry.etaleStalkToSectionsAb` carries the stalk at `s` of `f_*F` to the
global sections there of the inverse image of `f_*F` along the structure morphism to `S`; that
inverse image is `p⁻¹f⁻¹f_*F`, and the counit of the inverse-image/direct-image adjunction
carries it to `p⁻¹F`. -/
def pushforwardStalkToStrictHenselizationSectionsAb :
    smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom ⟶
      smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1} :=
  Functor.whiskerLeft (smallEtalePushforwardAb f)
      (etaleStalkToSectionsAb B S hS s
          (strictHenselizationBaseChangeToStrictHenselization B hS f s) ≫
        Functor.whiskerRight (strictHenselizationBaseChangePullbackAbCompIso B hS f s).inv
          (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
            Ab.{u + 1})) ≫
    Functor.whiskerRight
      (Functor.whiskerRight (smallEtaleAdjunctionAb f).counit
        (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s)))
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})

variable
  [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1}) (.up ℤ))]

/-- The comparison on the homotopy category of abelian sheaves on `X` induced by the map on
sheaves: apply it degreewise, pass to the derived category by the unit of the derivation of
global sections on the base change, and identify the degreewise actions of the stalk and of
inverse image with their actions on derived categories. -/
def derivedPushforwardStalkToStrictHenselizationSectionsUnit :
    (smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh ⋙
        smallEtaleDerivedStalkAb s.hom ⟶
      DerivedCategory.Qh ⋙ smallEtaleDerivedPullbackAb
          (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s) :=
  Functor.whiskerLeft ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ))
      (smallEtaleStalkAb s.hom).mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator ((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ))
      ((smallEtaleStalkAb s.hom).mapHomotopyCategory (.up ℤ)) DerivedCategory.Qh).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)) (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Stacks.DerivedFunctor.exactDerivedDescUnit
      (smallEtalePushforwardAb f ⋙ smallEtaleStalkAb s.hom)
      (smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hS f s))
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hS f s)) Ab.{u + 1})
      (smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s))
      (smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hS f s))
      (pushforwardStalkToStrictHenselizationSectionsAb B hS f s)

/-- **Stacks 0GIX, the map from the stalk.** The canonical map

`(Rf_*K)_s ⟶ RΓ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹K)`

for an object `K` of the unbounded derived category of abelian sheaves on the small étale site of
`X`, natural in `K`, where `p : X ×_S Spec(𝒪^{sh}_{S,s}) ⟶ X` is the projection.

The stalk of the derived direct image is a right derived functor of the stalk of the direct
image, the stalk functor having a right adjoint, so the map on sheaves
`AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb` extends uniquely to a map of
unbounded derived categories factoring it through the units. -/
@[stacks 0GIX "the map from the stalk"]
def derivedPushforwardStalkToStrictHenselizationSections :
    smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s.hom ⟶
      smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
        smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s) :=
  (smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s.hom).rightDerivedDesc
    (Functor.whiskerRight (smallEtaleDerivedPushforwardAbUnit f)
        (smallEtaleDerivedStalkAb s.hom) ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))
    (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
      smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s))
    (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s)

/-- On every complex of abelian sheaves on the small étale site of `X`, the canonical map from the
stalk of the derived direct image factors the comparison
`AlgebraicGeometry.derivedPushforwardStalkToStrictHenselizationSectionsUnit` — hence the map on
sheaves — through the unit of the derivation of direct image.

Since the stalk of the derived direct image is a right derived functor of the stalk of the direct
image, this property determines the map. -/
theorem derivedPushforwardStalkToStrictHenselizationSections_fac_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleDerivedStalkAb s.hom).map ((smallEtaleDerivedPushforwardAbUnit f).app J) ≫
        (derivedPushforwardStalkToStrictHenselizationSections B hS f s).app
          (DerivedCategory.Qh.obj J) =
      (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s).app J := by
  unfold derivedPushforwardStalkToStrictHenselizationSections
  simpa using Functor.rightDerived_fac_app
    (smallEtaleDerivedPushforwardAb f ⋙ smallEtaleDerivedStalkAb s.hom)
    (Functor.whiskerRight (smallEtaleDerivedPushforwardAbUnit f)
        (smallEtaleDerivedStalkAb s.hom) ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))
    (smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS f s) ⋙
      smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS f s))
    (derivedPushforwardStalkToStrictHenselizationSectionsUnit B hS f s) J

end Stalk

end AlgebraicGeometry

end
