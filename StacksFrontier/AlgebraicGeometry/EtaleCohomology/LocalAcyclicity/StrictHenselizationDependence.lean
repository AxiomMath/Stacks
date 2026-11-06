module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.DerivedStalkSectionsPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedGlobalSectionsExistence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SpecializationStalkIdentifications

/-!
# The canonical map of Tag 0GJN sees only the inverse image on the strict henselization

Let `X` be a scheme, `x` a geometric point of `X`, `p : Spec 𝒪^{sh}_{X,x} ⟶ X` the structure
morphism of the strict henselization at `x`, and `T` a scheme over `Spec 𝒪^{sh}_{X,x}` with
structure morphism `q`. The canonical map of [Stacks, Tag 0GJN],

`α_{K,x} : K_x ⟶ RΓ(T, K)`,

is a transformation between two functors of `K ∈ D(X_étale)`, and this file factors *both* of them,
compatibly with `α`, through the inverse image

`P = Rp⁻¹ : D(X_étale) ⟶ D(Spec 𝒪^{sh}_{X,x})`.

The consequence drawn here is that the iso-status of `α_K` depends on `K` only through `P K`:
`AlgebraicGeometry.isIso_vanishingCyclesMap_app_iff_of_derivedPullbackIso`.

## What this needs, and what it does not

It does *not* need [Stacks, Tag 03Q9] on unbounded derived categories — that is, it does not need
`K_x ≅ RΓ(Spec 𝒪^{sh}_{X,x}, P K)` in `D(Ab)`, which would say that the higher cohomology of a
strictly henselian local scheme vanishes. What is used is the *degree-zero* statement, 03Q9 at the
identity morphism of `X`, which the library has as
`AlgebraicGeometry.etaleStalkSectionsAbIso`: the natural isomorphism

`F_x ≅ Γ(Spec 𝒪^{sh}_{X,x}, p⁻¹F)`

of abelian sheaves. Both functors flanking `α` are therefore the degreewise action of an exact
functor: the source is the degreewise stalk, and the above isomorphism exhibits
`Γ(Spec 𝒪^{sh}_{X,x}, -)` as exact as well, since the stalk at the canonical geometric point of
the strict henselization is — that is
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleGlobalSections_strictHenselization` and its
colimit counterpart. Exactness is all the descent machinery of
`Stacks.DerivedFunctor.compIso_whiskerLeft_eq_exactDerivedDesc` asks for, and it turns the
degree-zero identification into the required factorization on unbounded derived categories, with
the degreewise global sections on the strict henselization — *not* their right derived functor —
as the middle term.

So the dependence statement is strictly weaker than derived 03Q9: it is the degree-zero
identification plus the exactness it supplies, descended.

## Main definitions

* `AlgebraicGeometry.smallEtaleGlobalSectionsStrictHenselizationStalkAbIso` — global sections on
  `Spec 𝒪^{sh}_{X,x}` are the stalk at its canonical geometric point.
* `AlgebraicGeometry.strictHenselizationDerivedSectionsRestriction` — the middle term of the
  factorization: the descent to unbounded derived categories of restriction of global sections
  along `q : T ⟶ Spec 𝒪^{sh}_{X,x}`, out of the degreewise action of global sections on the
  strict henselization.

## Main results

* `AlgebraicGeometry.vanishingCyclesMap_eq_strictHenselizationDerivedSectionsRestriction` — the
  factorization of the canonical map of Tag 0GJN through the derived inverse image on the strict
  henselization.
* `AlgebraicGeometry.isIso_vanishingCyclesMap_app_iff_of_derivedPullbackIso` and
  `AlgebraicGeometry.isIso_vanishingCyclesFibreMap_app_iff_of_derivedPullbackIso` — the canonical
  map has the same iso-status at two objects of `D(X_étale)` with isomorphic inverse images on
  `Spec 𝒪^{sh}_{X,x}`.

## References

* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* [Stacks Project, Tag 0GJR](https://stacks.math.columbia.edu/tag/0GJR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-! ### Global sections on the strict henselization -/

section Exactness

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)

/-- **Global sections on the strict henselization are the stalk at its canonical geometric
point.** The identity object of the small étale site of `Spec 𝒪^{sh}_{X,x}`, with the canonical
geometric point as its lift, is an initial étale neighbourhood of that point, so the comparison
`Γ(Spec 𝒪^{sh}_{X,x}, G) ⟶ G_σ` of
`AlgebraicGeometry.smallEtaleGlobalSectionsToStalkAb` is an isomorphism. -/
def smallEtaleGlobalSectionsStrictHenselizationStalkAbIso :
    Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1} ≅
      smallEtaleStalkAb (geometricPointToStrictHenselization B X hX x) :=
  letI : IsIso (smallEtaleGlobalSectionsToStalkAb
      (geometricPointToStrictHenselization B X hX x)
      (Stacks.EtaleCohomology.pointSmallEtaleClosedPointElement
        (geometricPointToStrictHenselization B X hX x))) :=
    isIso_smallEtaleGlobalSectionsToStalkAb _ _
      (Stacks.EtaleCohomology.isInitialPointSmallEtaleClosedPointElement
        (geometricPointToStrictHenselization B X hX x)
        (geometricPointToStrictHenselization_base_default B X hX x))
  asIso (smallEtaleGlobalSectionsToStalkAb
    (geometricPointToStrictHenselization B X hX x)
    (Stacks.EtaleCohomology.pointSmallEtaleClosedPointElement
      (geometricPointToStrictHenselization B X hX x)))

/-- **Global sections of abelian sheaves on the small étale site of a strict henselization are
left exact**: they are the stalk at the canonical geometric point, which preserves finite
limits. -/
theorem preservesFiniteLimits_smallEtaleGlobalSections_strictHenselization :
    PreservesFiniteLimits
      (Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}) :=
  Limits.preservesFiniteLimits_of_natIso
    (smallEtaleGlobalSectionsStrictHenselizationStalkAbIso B X hX x).symm

/-- **Global sections of abelian sheaves on the small étale site of a strict henselization are
right exact**: they are the stalk at the canonical geometric point, which preserves finite
colimits. -/
theorem preservesFiniteColimits_smallEtaleGlobalSections_strictHenselization :
    PreservesFiniteColimits
      (Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1}) :=
  Limits.preservesFiniteColimits_of_natIso
    (smallEtaleGlobalSectionsStrictHenselizationStalkAbIso B X hX x).symm

end Exactness

attribute [local instance]
  preservesFiniteLimits_smallEtaleGlobalSections_strictHenselization
  preservesFiniteColimits_smallEtaleGlobalSections_strictHenselization

/-! ### The factorization of the canonical map -/

section Factorization

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T : Scheme.{u}} (q : T ⟶ strictHenselization B X hX x)

/-- Restriction of unbounded derived global sections along `q : T ⟶ Spec 𝒪^{sh}_{X,x}`, taken out
of the *degreewise* action of global sections on the strict henselization rather than out of their
right derived functor: global sections on a strict henselization are exact, so their degreewise
action on unbounded derived categories is a right derived functor of their action on homotopy
categories, and restriction of sections descends along it uniquely. -/
def strictHenselizationDerivedSectionsRestriction :
    (Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x))
          Ab.{u + 1}).mapDerivedCategory ⟶
      smallEtaleDerivedPullbackAb q ⋙ smallEtaleDerivedGlobalSections T :=
  Stacks.DerivedFunctor.exactDerivedDesc
    (Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1})
    (smallEtalePullbackAb q) (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
    (smallEtaleDerivedGlobalSections T) (smallEtaleDerivedGlobalSectionsUnit T)
    (smallEtaleGlobalSectionsRestrictionAb q)

/-- **The canonical map of Tag 0GJN factors through the derived inverse image on the strict
henselization.** Reading the source `K ↦ K_x` as the degreewise global sections on
`Spec 𝒪^{sh}_{X,x}` of the inverse image there — which is 03Q9 at `id_X`,
`AlgebraicGeometry.etaleStalkSectionsAbIso`, descended — and the target
`K ↦ RΓ(T, K)` through the composition isomorphism for inverse images, the canonical map becomes
restriction of sections along `q`, whiskered by the derived inverse image on the strict
henselization.

Both flanking functors are degreewise actions of exact functors, so each side is determined by
its factorization through `CategoryTheory.Functor.mapDerivedCategoryFactorsh`; the identity is
therefore the identity of the corresponding transformations of abelian sheaves, which is
`AlgebraicGeometry.etaleStalkToSectionsAb_comp_sectionsRestrictionAb` at the identity morphism of
the strict henselization. -/
theorem vanishingCyclesMap_eq_strictHenselizationDerivedSectionsRestriction
    (hq : q ≫ (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x) =
      q ≫ strictHenselizationToBase B X hX x) :
    (Functor.mapDerivedCategoryCompIsoOfCompIso (etaleStalkSectionsAbIso B X hX x).symm).inv ≫
        Functor.whiskerLeft
            (smallEtaleDerivedPullbackAb
              (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x))
            (strictHenselizationDerivedSectionsRestriction B X hX x q) ≫
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight
                (Functor.mapDerivedCategoryCompIsoOfCompIso
                  (smallEtalePullbackAbCompIso q
                      (𝟙 (strictHenselization B X hX x) ≫
                        strictHenselizationToBase B X hX x) ≪≫
                    eqToIso (congrArg (fun m : T ⟶ X => smallEtalePullbackAb m) hq))).hom
              (smallEtaleDerivedGlobalSections T) =
      vanishingCyclesMap B X hX x q := by
  have hsheaf : (etaleStalkSectionsAbIso B X hX x).symm.inv ≫
        Functor.whiskerLeft
            (smallEtalePullbackAb
              (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x))
            (smallEtaleGlobalSectionsRestrictionAb q) ≫
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight
                (smallEtalePullbackAbCompIso q
                    (𝟙 (strictHenselization B X hX x) ≫
                      strictHenselizationToBase B X hX x) ≪≫
                  eqToIso (congrArg (fun m : T ⟶ X => smallEtalePullbackAb m) hq)).hom
              (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) =
      etaleStalkToSectionsAb B X hX x q := by
    refine Eq.trans ?_ (etaleStalkToSectionsAb_comp_sectionsRestrictionAb B X hX x
      (𝟙 (strictHenselization B X hX x)) q q (Category.comp_id q))
    rw [Iso.symm_inv, etaleStalkSectionsAbIso_hom, smallEtaleSectionsRestrictionAb]
    congr 1
  refine Eq.trans (Stacks.DerivedFunctor.compIso_whiskerLeft_eq_exactDerivedDesc
    (smallEtaleStalkAb x.hom)
    (smallEtalePullbackAb (q ≫ strictHenselizationToBase B X hX x))
    (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
    (smallEtaleDerivedGlobalSections T) (smallEtaleDerivedGlobalSectionsUnit T)
    (smallEtalePullbackAb
      (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x))
    (Sheaf.Γ (smallEtaleTopology (strictHenselization B X hX x)) Ab.{u + 1})
    (smallEtalePullbackAb q) (etaleStalkSectionsAbIso B X hX x).symm
    (smallEtalePullbackAbCompIso q
        (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x) ≪≫
      eqToIso (congrArg (fun m : T ⟶ X => smallEtalePullbackAb m) hq))
    (smallEtaleGlobalSectionsRestrictionAb q)
    (strictHenselizationDerivedSectionsRestriction B X hX x q)
    (Stacks.DerivedFunctor.exactDerivedDesc_fac_app _ _ _ _ _ _)) ?_
  rw [hsheaf, vanishingCyclesMap]

end Factorization

/-! ### Dependence of the canonical map on the inverse image on the strict henselization -/

section Dependence

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (x : GeometricPoint X)
  {T : Scheme.{u}} (q : T ⟶ strictHenselization B X hX x)

/-- A morphism flanked by isomorphisms is invertible exactly when it is. -/
private theorem isIso_comp_middle_iff {A C D E : DerivedCategory Ab.{u + 1}} (i : A ⟶ C)
    (m : C ⟶ D) (j : D ⟶ E) (hi : IsIso i) (hj : IsIso j) :
    IsIso (i ≫ m ≫ j) ↔ IsIso m := by
  have := hi
  have := hj
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h
    have : IsIso (m ≫ j) := IsIso.of_isIso_comp_left i (m ≫ j)
    exact IsIso.of_isIso_comp_right m j
  · have := h
    infer_instance

/-- **The canonical map of Tag 0GJN depends only on the inverse image on the strict
henselization.** If two objects of `D(X_étale)` have isomorphic inverse images on
`Spec 𝒪^{sh}_{X,x}`, then the canonical map `α_{K,x} : K_x ⟶ RΓ(T, K)` is an isomorphism at one
of them exactly when it is at the other.

By `AlgebraicGeometry.vanishingCyclesMap_eq_strictHenselizationDerivedSectionsRestriction` the
canonical map at `K` is, up to isomorphisms at either end, the restriction of sections
`AlgebraicGeometry.strictHenselizationDerivedSectionsRestriction` evaluated at the inverse image
of `K`; and a transformation evaluated at isomorphic objects has the same iso-status at both, by
naturality. -/
theorem isIso_vanishingCyclesMap_app_iff_of_derivedPullbackIso
    (K K' : smallEtaleDerivedCategory X)
    (e : (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj K ≅
      (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj K') :
    IsIso ((vanishingCyclesMap B X hX x q).app K) ↔
      IsIso ((vanishingCyclesMap B X hX x q).app K') := by
  have hq : q ≫ (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x) =
      q ≫ strictHenselizationToBase B X hX x := by rw [Category.id_comp]
  have hfac : ∀ M : smallEtaleDerivedCategory X,
      IsIso ((vanishingCyclesMap B X hX x q).app M) ↔
        IsIso ((strictHenselizationDerivedSectionsRestriction B X hX x q).app
          ((smallEtaleDerivedPullbackAb (𝟙 (strictHenselization B X hX x) ≫
            strictHenselizationToBase B X hX x)).obj M)) := by
    intro M
    rw [← NatTrans.congr_app
      (vanishingCyclesMap_eq_strictHenselizationDerivedSectionsRestriction B X hX x q hq) M]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp]
    have : IsIso ((Functor.mapDerivedCategoryCompIsoOfCompIso
        (smallEtalePullbackAbCompIso q
            (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x) ≪≫
          eqToIso (congrArg (fun m : T ⟶ X => smallEtalePullbackAb m) hq))).hom.app M) :=
      NatIso.isIso_app_of_isIso _ _
    exact isIso_comp_middle_iff _ _ _ (NatIso.isIso_app_of_isIso _ _) inferInstance
  have hpull : smallEtaleDerivedPullbackAb
        (𝟙 (strictHenselization B X hX x) ≫ strictHenselizationToBase B X hX x) =
      smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x) :=
    congrArg (fun m : strictHenselization B X hX x ⟶ X => smallEtaleDerivedPullbackAb m)
      (Category.id_comp (strictHenselizationToBase B X hX x))
  have d := (eqToIso hpull).app K ≪≫ e ≪≫ ((eqToIso hpull).app K').symm
  rw [hfac K, hfac K']
  exact NatTrans.isIso_app_iff_of_iso
    (strictHenselizationDerivedSectionsRestriction B X hX x q) d

end Dependence

/-! ### The statement at a variety of vanishing cycles -/

section VanishingCycles

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X)
  (t : GeometricPoint (strictHenselization B S hS (x.map f)))

/-- **The canonical map at a variety of vanishing cycles depends only on the inverse image on the
strict henselization.** The displayed map `α_{K,x,t} : K_x ⟶ RΓ(F_{x,t}, K)` of Tag 0GJN is an
isomorphism at an object of `D(X_étale)` exactly when it is at any object with isomorphic inverse
image on `Spec 𝒪^{sh}_{X,x}`.

This is `AlgebraicGeometry.isIso_vanishingCyclesMap_app_iff_of_derivedPullbackIso` at the
projection of the variety of vanishing cycles to the strict henselization. -/
theorem isIso_vanishingCyclesFibreMap_app_iff_of_derivedPullbackIso
    (K K' : smallEtaleDerivedCategory X)
    (e : (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj K ≅
      (smallEtaleDerivedPullbackAb (strictHenselizationToBase B X hX x)).obj K') :
    IsIso ((vanishingCyclesFibreMap B hX hS f x t).app K) ↔
      IsIso ((vanishingCyclesFibreMap B hX hS f x t).app K') :=
  isIso_vanishingCyclesMap_app_iff_of_derivedPullbackIso B X hX x
    (vanishingCyclesFibreToStrictHenselization B hX hS f x t) K K' e

end VanishingCycles

end AlgebraicGeometry

end
