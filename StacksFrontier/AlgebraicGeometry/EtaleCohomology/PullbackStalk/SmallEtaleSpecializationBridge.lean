module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Specialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparisonNaturality
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SpecializationStalk

/-!
# Stalks and specialization maps on the two small étale sites

The library carries two small étale sites of a scheme `S` lying in a big étale site `B`: the
bounded site `AlgebraicGeometry.SmallEtale B S hS` of [Stacks, Tag 021B], on which the stalks
`AlgebraicGeometry.etaleStalk` and the specialization maps
`AlgebraicGeometry.specializationMapOnStalks` of [Stacks, Section 0GJ2] are defined, and Mathlib's
`S.Etale`, on which the abelian stalks `Stacks.EtaleCohomology.smallEtaleStalkAb` and the
specialization maps `AlgebraicGeometry.smallEtaleSpecializationStalkAb` used by
[Stacks, Tag 0GKD] are defined. This file compares them for the sheaf of sets underlying an
abelian sheaf `K` on Mathlib's site, transported to the bounded site: the stalks are in
bijection, by a bijection which sends the germ of a section to the germ of the same section, and
under these bijections the two specialization maps agree.

## Main definitions

* `Stacks.EtaleCohomology.etaleStalkTransportEquiv`: the bijection between the stalk on the
  bounded site of the transported sheaf of sets and the abelian stalk on Mathlib's site.

## Main results

* `Stacks.EtaleCohomology.etaleStalkTransportEquiv_ι`: the bijection on germs.
* `Stacks.EtaleCohomology.finite_etaleStalk_transport`: finiteness of stalks transports.
* `Stacks.EtaleCohomology.bijective_specializationMapOnStalks_transport`: bijectivity of the
  specialization map on Mathlib's site gives bijectivity on the bounded site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- The forgetful functor of abelian groups at the coefficient universe preserves the filtered
colimits indexing the stalks of the small étale sites. -/
local instance : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget AddCommGrpCat.{u + 1})

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (K : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The sheaf of sets underlying an abelian sheaf on Mathlib's small étale site. -/
abbrev forgetSheaf : Sheaf S.smallEtaleTopology (Type (u + 1)) :=
  (sheafCompose S.smallEtaleTopology (forget AddCommGrpCat.{u + 1})).obj K

/-- The sheaf of sets underlying an abelian sheaf on Mathlib's small étale site, transported to
the bounded small étale site of Stacks 021B. -/
abbrev forgetSheafTransport : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)) :=
  (SmallEtale.sheafEquiv B S hS (Type (u + 1))).inverse.obj (forgetSheaf S K)

/-- **The stalks of the two sites agree.** The stalk on the bounded site of the transported
sheaf of sets underlying `K` is in bijection with the abelian stalk of `K` on Mathlib's site. -/
def etaleStalkTransportEquiv (s : GeometricPoint S) :
    etaleStalk B S hS s (forgetSheafTransport B S hS K).obj ≃
      ToType ((smallEtaleStalkAb s.hom).obj K) :=
  let c := (SmallEtale.sheafEquiv B S hS (Type (u + 1))).counitIso.app (forgetSheaf S K)
  let e1 := (sheafFiberIsoOfAdjOfFiberIso (geometricPointSitePoint B S hS s)
    (Scheme.pointSmallEtale s.hom) (SmallEtale.toEtaleSite B S hS)
    (toEtaleSiteFiberIso B S hS s)
    (SmallEtale.sheafEquiv B S hS (Type (u + 1))).toAdjunction).app
      (forgetSheafTransport B S hS K)
  let e2 := ((Scheme.pointSmallEtale s.hom).sheafFiber (A := Type (u + 1))).mapIso c
  let e3 := ((Scheme.pointSmallEtale s.hom).presheafFiberCompIso
    (forget AddCommGrpCat.{u + 1})).app K.obj
  (e1.symm ≪≫ e2 ≪≫ e3).toEquiv

/-- **The bijection of stalks on germs**: the germ at an étale neighbourhood `(U, x)` of `s` on
the bounded site of a section `z` is sent to the germ at the corresponding étale neighbourhood
on Mathlib's site of the same section. -/
theorem etaleStalkTransportEquiv_ι (s : GeometricPoint S) (U : SmallEtale B S hS)
    (x : (geometricPointFiber B S hS s).obj U)
    (z : (forgetSheafTransport B S hS K).obj.obj (op U)) :
    etaleStalkTransportEquiv B S hS K s
        (colimit.ι ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
          (forgetSheafTransport B S hS K).obj) (op ⟨U, x⟩) z) =
      (Scheme.pointSmallEtale s.hom).toPresheafFiber ((SmallEtale.toEtaleSite B S hS).obj U)
        ((toEtaleSiteFiberIso B S hS s).inv.app U x) K.obj z := by
  have h1 := toPresheafFiber_sheafFiberIsoOfAdjOfFiberIso_inv (geometricPointSitePoint B S hS s)
    (Scheme.pointSmallEtale s.hom) (SmallEtale.toEtaleSite B S hS)
    (SmallEtale.sheafEquiv B S hS (Type (u + 1))).toAdjunction (toEtaleSiteFiberIso B S hS s)
    (forgetSheafTransport B S hS K) U x
  have h2 := (Scheme.pointSmallEtale s.hom).toPresheafFiber_naturality
    (((SmallEtale.sheafEquiv B S hS (Type (u + 1))).counitIso.app (forgetSheaf S K)).hom.hom)
    ((SmallEtale.toEtaleSite B S hS).obj U) ((toEtaleSiteFiberIso B S hS s).inv.app U x)
  have h3 := (Scheme.pointSmallEtale s.hom).toPresheafFiber_presheafFiberCompIso_hom_app
    (forget AddCommGrpCat.{u + 1}) ((SmallEtale.toEtaleSite B S hS).obj U)
    ((toEtaleSiteFiberIso B S hS s).inv.app U x) K.obj
  have htri : ((SmallEtale.sheafEquiv B S hS (Type (u + 1))).unit.app
      (forgetSheafTransport B S hS K)).hom.app (op U) ≫
      ((SmallEtale.sheafEquiv B S hS (Type (u + 1))).counit.app (forgetSheaf S K)).hom.app
        (op ((SmallEtale.toEtaleSite B S hS).obj U)) = 𝟙 _ :=
    congrArg (fun k => k.hom.app (op U))
      ((SmallEtale.sheafEquiv B S hS (Type (u + 1))).unit_inverse_comp (forgetSheaf S K))
  have k1 := ConcreteCategory.congr_hom h1 z
  have k2 := ConcreteCategory.congr_hom h2
    ((((SmallEtale.sheafEquiv B S hS (Type (u + 1))).unit.app
      (forgetSheafTransport B S hS K)).hom.app (op U)) z)
  have kt := ConcreteCategory.congr_hom htri z
  have k3 := ConcreteCategory.congr_hom h3 z
  simp only [ConcreteCategory.comp_apply] at k1 k2 kt k3
  let e2m := (Scheme.pointSmallEtale s.hom).presheafFiber.map
    (((SmallEtale.sheafEquiv B S hS (Type (u + 1))).counitIso.app (forgetSheaf S K)).hom.hom)
  let e3m := ((Scheme.pointSmallEtale s.hom).presheafFiberCompIso
    (forget AddCommGrpCat.{u + 1})).hom.app K.obj
  refine (congrArg (fun y => ConcreteCategory.hom e3m (ConcreteCategory.hom e2m y)) k1).trans ?_
  refine (congrArg (fun y => ConcreteCategory.hom e3m y) k2).trans ?_
  refine (congrArg (fun y => ConcreteCategory.hom e3m (ConcreteCategory.hom
    ((Scheme.pointSmallEtale s.hom).toPresheafFiber ((SmallEtale.toEtaleSite B S hS).obj U)
      ((toEtaleSiteFiberIso B S hS s).inv.app U x) (forgetSheaf S K).obj) y)) kt).trans ?_
  exact k3

/-- **Finiteness of stalks transports to the bounded site.** -/
theorem finite_etaleStalk_transport (s : GeometricPoint S)
    (h : Finite (ToType ((smallEtaleStalkAb s.hom).obj K))) :
    Finite (etaleStalk B S hS s (forgetSheafTransport B S hS K).obj) :=
  Finite.of_equiv _ (etaleStalkTransportEquiv B S hS K s).symm

/-- The factorization of the strict henselization through a pointed étale neighbourhood of the
bounded site is the factorization through the corresponding neighbourhood of Mathlib's site. -/
theorem strictHenselizationEtaleFactor_eq_neighborhoodLift (s : GeometricPoint S)
    (U : SmallEtale B S hS) (x : (geometricPointFiber B S hS s).obj U) :
    strictHenselizationEtaleFactor B S hS s U x =
      strictHenselizationNeighborhoodLift B S hS s ((SmallEtale.toEtaleSite B S hS).obj U)
        ((toEtaleSiteFiberIso B S hS s).inv.app U x) :=
  strictHenselizationNeighborhoodLift_eq B S hS s ((SmallEtale.toEtaleSite B S hS).obj U)
    ((toEtaleSiteFiberIso B S hS s).inv.app U x) (strictHenselizationEtaleFactor B S hS s U x)
    (strictHenselizationEtaleFactor_comp B S hS s U x)
    (geometricPointToStrictHenselization_comp_strictHenselizationEtaleFactor B S hS s U x)

/-- **The specialization maps of the two sites agree on germs.** Under the bijections of stalks
`etaleStalkTransportEquiv`, the specialization map on the bounded site attached to a geometric
point `t` of the strict henselization at `s` is the specialization map on Mathlib's site. -/
theorem etaleStalkTransportEquiv_specializationMapOnStalks (s : GeometricPoint S)
    (t : GeometricPoint (strictHenselization B S hS s))
    (a : etaleStalk B S hS s (forgetSheafTransport B S hS K).obj) :
    etaleStalkTransportEquiv B S hS K (t.map (strictHenselizationToBase B S hS s))
        (specializationMapOnStalks (GeometricSpecialization.ofPoint B S hS s t)
          (forgetSheafTransport B S hS K).obj a) =
      (smallEtaleSpecializationStalkAb B S hS s t).app K
        (etaleStalkTransportEquiv B S hS K s a) := by
  obtain ⟨⟨U, x⟩, z, rfl⟩ := Types.jointly_surjective'
    (F := (CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙
      (forgetSheafTransport B S hS K).obj) a
  refine (congrArg (etaleStalkTransportEquiv B S hS K (t.map (strictHenselizationToBase B S hS s)))
    (specializationMapOnStalks_ι (GeometricSpecialization.ofPoint B S hS s t)
      (forgetSheafTransport B S hS K).obj ⟨U, x⟩ z)).trans ?_
  refine (etaleStalkTransportEquiv_ι B S hS K _ U _ z).trans ?_
  refine Eq.trans ?_ (congrArg
    (ConcreteCategory.hom ((smallEtaleSpecializationStalkAb B S hS s t).app K))
    (etaleStalkTransportEquiv_ι B S hS K s U x z)).symm
  have hsp := ConcreteCategory.congr_hom
    (smallEtaleSpecializationStalkAb_toPresheafFiber B S hS s t K
      ((SmallEtale.toEtaleSite B S hS).obj U) ((toEtaleSiteFiberIso B S hS s).inv.app U x)) z
  refine Eq.trans ?_ hsp.symm
  have hv : (toEtaleSiteFiberIso B S hS (t.map (strictHenselizationToBase B S hS s))).inv.app U
      ((specializationFiberHom (GeometricSpecialization.ofPoint B S hS s t)).app U x) =
      specializationEtaleNeighborhoodLift B S hS s t ((SmallEtale.toEtaleSite B S hS).obj U)
        ((toEtaleSiteFiberIso B S hS s).inv.app U x) := by
    apply Over.OverMorphism.ext
    show t.hom ≫ strictHenselizationEtaleFactor B S hS s U x = t.hom ≫ _
    rw [strictHenselizationEtaleFactor_eq_neighborhoodLift]
  exact congrArg (fun v => ConcreteCategory.hom ((Scheme.pointSmallEtale
    (t.hom ≫ strictHenselizationToBase B S hS s)).toPresheafFiber
      ((SmallEtale.toEtaleSite B S hS).obj U) v K.obj) z) hv

/-- **Bijectivity of the specialization map transports to the bounded site.** If the specialization
map on Mathlib's site attached to a geometric point `t` of the strict henselization at `s` is an
isomorphism at `K`, the specialization map on the bounded site is bijective on the transported
sheaf of sets. -/
theorem bijective_specializationMapOnStalks_transport (s : GeometricPoint S)
    (t : GeometricPoint (strictHenselization B S hS s))
    (h : IsIso ((smallEtaleSpecializationStalkAb B S hS s t).app K)) :
    Function.Bijective (specializationMapOnStalks (GeometricSpecialization.ofPoint B S hS s t)
      (forgetSheafTransport B S hS K).obj) := by
  have hb : Function.Bijective ((smallEtaleSpecializationStalkAb B S hS s t).app K) :=
    ConcreteCategory.bijective_of_isIso _
  have heq : (ConcreteCategory.hom (specializationMapOnStalks
      (GeometricSpecialization.ofPoint B S hS s t) (forgetSheafTransport B S hS K).obj) :
        _ → _) =
      (etaleStalkTransportEquiv B S hS K (t.map (strictHenselizationToBase B S hS s))).symm ∘
        (smallEtaleSpecializationStalkAb B S hS s t).app K ∘
          etaleStalkTransportEquiv B S hS K s := by
    funext a
    exact (Equiv.eq_symm_apply _).2
      (etaleStalkTransportEquiv_specializationMapOnStalks B S hS K s t a)
  rw [heq]
  exact (Equiv.bijective _).comp (hb.comp (Equiv.bijective _))

/-- Every geometric specialization is the one attached to its geometric point of the strict
henselization. -/
theorem geometricSpecialization_eq_ofPoint {s : GeometricPoint S}
    (σ : GeometricSpecialization B S hS s) :
    σ = GeometricSpecialization.ofPoint B S hS s σ.point := by
  obtain ⟨⟨R, h⟩, lift, hl⟩ := σ
  show _ = (⟨⟨R, lift ≫ strictHenselizationToBase B S hS s⟩, lift, rfl⟩ :
    GeometricSpecialization B S hS s)
  congr
  all_goals first | exact hl.symm | exact proof_irrel_heq _ _

end Stacks.EtaleCohomology

end
