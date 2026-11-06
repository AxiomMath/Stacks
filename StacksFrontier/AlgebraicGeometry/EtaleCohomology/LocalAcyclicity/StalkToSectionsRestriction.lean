module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.StrictHenselizationSections

/-!
# The map of Tag 0GJN is pullback of cohomology from the strict henselization

Let `x` be a geometric point of a scheme `X`, write `p : Spec 𝒪^{sh}_{X,x} ⟶ X` for the structure
morphism of the strict henselization, and let `K` be an object of the unbounded derived category
`D(X_étale)` of abelian sheaves on the small étale site of `X`. The source, just before
[Stacks, Tag 0GJN], records

`K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)`,

since `𝒪^{sh}_{X,x}` is strictly henselian, and obtains the canonical map
`α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)` by pulling back cohomology along the projection
`F_{x,t} ⟶ Spec 𝒪^{sh}_{X,x}` of a variety of vanishing cycles.

This file registers that map, `AlgebraicGeometry.stalkToVanishingCyclesFibreSections`, and its
generalization to any scheme over the strict henselization, with no hypothesis beyond the data of
the source: the unbounded derived global sections exist on every small étale site
(`Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor`), so the constructions
`AlgebraicGeometry.vanishingCyclesMap` and `AlgebraicGeometry.vanishingCyclesFibreMap` of
`LocalAcyclicity/SpecializationMap.lean` are used with that instance. It then states both steps of
the source's construction for this map.

## Main definitions

* `AlgebraicGeometry.smallEtaleDerivedStalkToSections` — **[Stacks, Tag 0GJN]** the canonical map
  `K_x ⟶ RΓ(T, K)` for a scheme `T` over the strict henselization, natural in `K`.
* `AlgebraicGeometry.stalkToVanishingCyclesFibreSections` — **[Stacks, Tag 0GJN]** the displayed
  map `α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)` at a variety of vanishing cycles.
* `AlgebraicGeometry.smallEtaleDerivedStalkIsoStrictHenselizationSections` — the identification
  `K_x ≅ RΓ(Spec 𝒪^{sh}_{X,x}, p⁻¹K)`, natural in `K`.

## Main results

* `AlgebraicGeometry.smallEtaleDerivedStalkToSections_fac_app` — on every complex, the map
  factors the degreewise map on sheaves through the unit of derived global sections.
* `AlgebraicGeometry.smallEtaleDerivedStalkToSections_eq_restriction` — for a scheme `T` over the
  strict henselization, the map `K_x ⟶ RΓ(T, K)` is that identification followed by restriction
  of derived global sections along `T ⟶ Spec 𝒪^{sh}_{X,x}`.
* `AlgebraicGeometry.stalkToVanishingCyclesFibreSections_eq_restriction` — the case of a variety
  of vanishing cycles: `α_{K,x,t}` is pullback of cohomology along
  `F_{x,t} ⟶ Spec 𝒪^{sh}_{X,x}`.

## References

* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The canonical map, with derived global sections supplied by the library

`AlgebraicGeometry.vanishingCyclesMap` and `AlgebraicGeometry.vanishingCyclesFibreMap` take the
existence of the unbounded derived global sections `RΓ(T, -)` as an instance argument. That
derivation always exists:
`Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor` provides it for every
scheme, abelian sheaves on a small étale site being a Grothendieck abelian category in which every
unbounded complex has a K-injective resolution ([Stacks, Tag 079P]). The declarations below are
those constructions with that instance found by instance search, so they carry no hypothesis
beyond the data of the source. -/

section Unconditional

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T : Scheme.{u}} (q : T ⟶ strictHenselization B X hX x)

/-- **Stacks 0GJN.** The canonical map `α_{K,x} : K_x ⟶ RΓ(T, K)` from the stalk at a geometric
point `x` of `X` of an object `K` of the unbounded derived category `D(X_étale)` of abelian
sheaves on the small étale site of `X`, to the unbounded derived global sections
`RΓ(T, K) = RΓ(T_étale, g⁻¹K)` of `K` on a scheme `T` over the strict henselization
`Spec 𝒪^{sh}_{X,x}`, with `g : T ⟶ Spec 𝒪^{sh}_{X,x} ⟶ X` the structure morphism, natural in `K`.

The derived global sections on `T` are the total right derived functor of global sections on the
whole unbounded homotopy category, which exists by
`Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor`. Since the strict
henselization is the initial étale neighbourhood of `x`, pulling back germs along
`T ⟶ Spec 𝒪^{sh}_{X,x}` gives the map `etaleStalkToSectionsAb` on abelian sheaves; the stalk
functor is exact, so the map on sheaves extends uniquely to one of derived categories.
`AlgebraicGeometry.smallEtaleDerivedStalkToSections_eq_restriction` identifies it with the
identification `K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)` followed by pulling back cohomology along
`T ⟶ Spec 𝒪^{sh}_{X,x}`. -/
@[stacks 0GJN "for an arbitrary scheme over the strict henselization"]
def smallEtaleDerivedStalkToSections :
    smallEtaleDerivedStalkAb x.hom ⟶
      smallEtaleDerivedPullbackAb (q ≫ strictHenselizationToBase B X hX x) ⋙
        smallEtaleDerivedGlobalSections T :=
  vanishingCyclesMap B X hX x q

/-- **Stacks 0GJN.** On every complex of abelian sheaves on the small étale site of `X`, the
canonical map to the derived global sections over `T` factors the degreewise map on sheaves
through the unit of the derivation of global sections, read through the identifications of the
degreewise actions of the stalk and of inverse image with their actions on derived categories.

Since the degreewise action of the stalk functor is a right derived functor of itself, this
property determines the map. -/
@[stacks 0GJN "the derived map factors the map on abelian sheaves"]
theorem smallEtaleDerivedStalkToSections_fac_app
    (J : HomotopyCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)) :
    (smallEtaleStalkAb x.hom).mapDerivedCategoryFactorsh.inv.app J ≫
        (smallEtaleDerivedStalkToSections B X hX x q).app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
          (smallEtaleStalkAb x.hom)
          (smallEtalePullbackAb
            (q ≫ strictHenselizationToBase B X hX x))
          (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
          (etaleStalkToSectionsAb B X hX x q)).app J) ≫
        (smallEtaleDerivedGlobalSectionsUnit T).app
            (((smallEtalePullbackAb
              (q ≫ strictHenselizationToBase B X hX x)).mapHomotopyCategory (.up ℤ)).obj J) ≫
          (smallEtaleDerivedGlobalSections T).map
            ((smallEtalePullbackAb
              (q ≫ strictHenselizationToBase B X hX x)).mapDerivedCategoryFactorsh.inv.app J) :=
  vanishingCyclesMap_fac_app B X hX x q J

end Unconditional

section UnconditionalVanishingCycles

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X)
  (t : GeometricPoint (strictHenselization B S hS (x.map f)))

/-- **Stacks 0GJN.** The canonical map

`α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)`

from the stalk at a geometric point `x` of `X` of an object `K` of the unbounded derived category
`D(X_étale)` of abelian sheaves on the small étale site of `X`, to the unbounded derived sections
`RΓ(F_{x,t}, K) = RΓ((F_{x,t})_étale, g⁻¹K)` of `K` on the variety of vanishing cycles
`F_{x,t} = t ×_{Spec 𝒪^{sh}_{S,f(x)}} Spec 𝒪^{sh}_{X,x}` of a morphism `f : X ⟶ S` at `x` and a
geometric point `t` of `Spec 𝒪^{sh}_{S,f(x)}`, with `g : F_{x,t} ⟶ X` the canonical morphism,
natural in `K`.

The derived global sections on `F_{x,t}` exist by
`Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_hasRightDerivedFunctor`. The stalk of `K` at
`x` is the derived sections of `K` over the strictly henselian `Spec 𝒪^{sh}_{X,x}`
(`AlgebraicGeometry.smallEtaleDerivedStalkIsoStrictHenselizationSections`), and the map is
pullback of cohomology along the projection `F_{x,t} ⟶ Spec 𝒪^{sh}_{X,x}`
(`AlgebraicGeometry.stalkToVanishingCyclesFibreSections_eq_restriction`). -/
@[stacks 0GJN]
def stalkToVanishingCyclesFibreSections :
    smallEtaleDerivedStalkAb x.hom ⟶
      smallEtaleDerivedPullbackAb (vanishingCyclesFibreToSource B hX hS f x t) ⋙
        smallEtaleDerivedGlobalSections (vanishingCyclesFibre B hX hS f x t) :=
  smallEtaleDerivedStalkToSections B X hX x
    (vanishingCyclesFibreToStrictHenselization B hX hS f x t)

/-- The displayed map of the source is the general construction for the projection of the variety
of vanishing cycles to the strict henselization at `x`. -/
theorem stalkToVanishingCyclesFibreSections_eq :
    stalkToVanishingCyclesFibreSections B hX hS f x t =
      smallEtaleDerivedStalkToSections B X hX x
        (vanishingCyclesFibreToStrictHenselization B hX hS f x t) :=
  rfl

end UnconditionalVanishingCycles

section StrictHenselization

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)

/-- **The stalk is the derived sections over the strict henselization.** For every object `K` of
the unbounded derived category of abelian sheaves on the small étale site of `X`, the canonical
map `K_x ⟶ RΓ(Spec 𝒪^{sh}_{X,x}, p⁻¹K)` is an isomorphism, natural in `K`: on sheaves it is
`F_x = Γ(Spec 𝒪^{sh}_{X,x}, p⁻¹F)`, and global sections over the strictly henselian
`Spec 𝒪^{sh}_{X,x}` are exact, so no boundedness of `K` is needed. -/
@[stacks 0GJN "`K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)`, since `𝒪^{sh}_{X,x}` is strictly henselian"]
def smallEtaleDerivedStalkIsoStrictHenselizationSections :
    smallEtaleDerivedStalkAb x.hom ≅
      smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x) ⋙
        smallEtaleDerivedGlobalSections (strictHenselization B X hX x) :=
  have : IsIso (smallEtaleDerivedStalkToSections B X hX x (𝟙 _)) :=
    isIso_vanishingCyclesMap_id B X hX x
  asIso (smallEtaleDerivedStalkToSections B X hX x (𝟙 _)) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (congrArg (fun m : strictHenselization B X hX x ⟶ X =>
        smallEtaleDerivedPullbackAb m) (Category.id_comp _)))
      (smallEtaleDerivedGlobalSections (strictHenselization B X hX x))

variable {T : Scheme.{u}}

/-- Restriction of derived global sections along `c`, read through the composition isomorphism
of inverse images, transported along an equality of the morphism to `X`. -/
private theorem restriction_eqToHom {g g' : strictHenselization B X hX x ⟶ X} (h : g = g')
    (c : T ⟶ strictHenselization B X hX x) :
    Functor.whiskerRight (eqToHom (congrArg (fun m => smallEtaleDerivedPullbackAb m) h))
          (smallEtaleDerivedGlobalSections (strictHenselization B X hX x)) ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb g')
          (smallEtaleDerivedGlobalSectionsRestriction c) ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            (Functor.mapDerivedCategoryCompIsoOfCompIso (smallEtalePullbackAbCompIso c g')).hom
            (smallEtaleDerivedGlobalSections T) =
      Functor.whiskerLeft (smallEtaleDerivedPullbackAb g)
          (smallEtaleDerivedGlobalSectionsRestriction c) ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            (Functor.mapDerivedCategoryCompIsoOfCompIso (smallEtalePullbackAbCompIso c g)).hom
            (smallEtaleDerivedGlobalSections T) ≫
          Functor.whiskerRight
            (eqToHom (congrArg (fun m => smallEtaleDerivedPullbackAb (c ≫ m)) h))
            (smallEtaleDerivedGlobalSections T) := by
  subst h
  simp

/-- The map of Tag 0GJN for two equal morphisms to the strict henselization. -/
private theorem smallEtaleDerivedStalkToSections_congr {c c' : T ⟶ strictHenselization B X hX x}
    (h : c = c') :
    smallEtaleDerivedStalkToSections B X hX x c' =
      smallEtaleDerivedStalkToSections B X hX x c ≫
        Functor.whiskerRight
          (eqToHom (congrArg (fun m => smallEtaleDerivedPullbackAb
            (m ≫ strictHenselizationToBase B X hX x)) h))
          (smallEtaleDerivedGlobalSections T) := by
  subst h
  simp

/-- **The map of Tag 0GJN is the identification of the stalk followed by pullback of
cohomology.** For a scheme `T` over the strict henselization `Spec 𝒪^{sh}_{X,x}`, with structure
morphism `c`, the canonical map `K_x ⟶ RΓ(T, K)` is the identification
`K_x ≅ RΓ(Spec 𝒪^{sh}_{X,x}, p⁻¹K)` followed by restriction of unbounded derived global sections
`RΓ(Spec 𝒪^{sh}_{X,x}, p⁻¹K) ⟶ RΓ(T, c⁻¹p⁻¹K)` along `c`, read through the composition
isomorphism `c⁻¹p⁻¹ ≅ (c ≫ p)⁻¹` of inverse images. -/
theorem smallEtaleDerivedStalkToSections_eq_restriction (c : T ⟶ strictHenselization B X hX x) :
    smallEtaleDerivedStalkToSections B X hX x c =
      (smallEtaleDerivedStalkIsoStrictHenselizationSections B X hX x).hom ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x))
          (smallEtaleDerivedGlobalSectionsRestriction c) ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            (Functor.mapDerivedCategoryCompIsoOfCompIso
              (smallEtalePullbackAbCompIso c (strictHenselizationToBase B X hX x))).hom
            (smallEtaleDerivedGlobalSections T) := by
  have key := vanishingCyclesMap_comp B X hX x (𝟙 _) c
  have hM : ∀ (m : T ⟶ X) (h : c ≫ 𝟙 _ ≫ strictHenselizationToBase B X hX x = m),
      (Functor.mapDerivedCategoryCompIsoOfCompIso
          (smallEtalePullbackAbCompIso c (𝟙 _ ≫ strictHenselizationToBase B X hX x) ≪≫
            eqToIso (congrArg (fun m : T ⟶ X => smallEtalePullbackAb m) h))).hom =
        (Functor.mapDerivedCategoryCompIsoOfCompIso
            (smallEtalePullbackAbCompIso c (𝟙 _ ≫ strictHenselizationToBase B X hX x))).hom ≫
          eqToHom (congrArg (fun m : T ⟶ X => smallEtaleDerivedPullbackAb m) h) := by
    intro m h
    subst h
    simp
  rw [smallEtaleDerivedStalkToSections_congr B X hX x (Category.comp_id c)]
  simp only [smallEtaleDerivedStalkToSections] at key ⊢
  rw [key, etaleStalkSectionsRestrictionCompIso, hM _ (Category.assoc _ _ _).symm]
  simp only [smallEtaleDerivedStalkIsoStrictHenselizationSections, smallEtaleDerivedStalkToSections,
    Iso.trans_hom, asIso_hom, Functor.isoWhiskerRight_hom, eqToIso.hom, Category.assoc]
  rw [restriction_eqToHom B X hX x (Category.id_comp (strictHenselizationToBase B X hX x)) c]
  simp only [Category.assoc, ← Functor.whiskerRight_comp, eqToHom_trans]

end StrictHenselization

section VanishingCycles

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X)
  (t : GeometricPoint (strictHenselization B S hS (x.map f)))

/-- **Stacks 0GJN: the map `α_{K,x,t}` is pullback of cohomology along
`F_{x,t} ⟶ Spec 𝒪^{sh}_{X,x}`.** The canonical map `α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)` at the
variety of vanishing cycles `F_{x,t} = t ×_{Spec 𝒪^{sh}_{S,f(x)}} Spec 𝒪^{sh}_{X,x}` is the
identification `K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)` followed by restriction of unbounded derived
global sections along the second projection `F_{x,t} ⟶ Spec 𝒪^{sh}_{X,x}`, read through the
composition isomorphism of inverse images. -/
@[stacks 0GJN "the map is obtained by pulling back cohomology along \
`F_{x,t} ⟶ Spec 𝒪^{sh}_{X,x}`, using `K_x = RΓ(Spec 𝒪^{sh}_{X,x}, K)`"]
theorem stalkToVanishingCyclesFibreSections_eq_restriction :
    stalkToVanishingCyclesFibreSections B hX hS f x t =
      (smallEtaleDerivedStalkIsoStrictHenselizationSections B X hX x).hom ≫
        Functor.whiskerLeft (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x))
          (smallEtaleDerivedGlobalSectionsRestriction
            (vanishingCyclesFibreToStrictHenselization B hX hS f x t)) ≫
        (Functor.associator _ _ _).inv ≫
          Functor.whiskerRight
            (Functor.mapDerivedCategoryCompIsoOfCompIso
              (smallEtalePullbackAbCompIso (vanishingCyclesFibreToStrictHenselization B hX hS f x t)
                (strictHenselizationToBase B X hX x))).hom
            (smallEtaleDerivedGlobalSections (vanishingCyclesFibre B hX hS f x t)) :=
  smallEtaleDerivedStalkToSections_eq_restriction B X hX x
    (vanishingCyclesFibreToStrictHenselization B hX hS f x t)

end VanishingCycles

end AlgebraicGeometry

end
