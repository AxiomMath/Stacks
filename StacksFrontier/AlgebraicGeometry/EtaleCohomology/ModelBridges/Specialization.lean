module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.Stalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleStalkSizeBoundedComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SpecializationStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.Specialization

/-!
# Specialization maps of étale sheaves in the two models

Let `s` be a geometric point of a scheme `S` and `t` a geometric point of the strict
henselization of `S` at `s`. The specialization map `sp : F_s ⟶ F_t` of Section 0GJ2 exists in
two forms: on stalks (Tag 040R) of presheaves on the small étale site of Tag 021B of a big étale
site containing `S` (`AlgebraicGeometry.specializationMapOnStalks`), and on stalks of abelian
sheaves on Mathlib's small étale site (`AlgebraicGeometry.smallEtaleSpecializationStalkAb`).
This file shows that the two agree under the identifications of stalks of
`AlgebraicGeometry.etaleStalkIsoSmallEtaleStalkAb` and
`Stacks.EtaleCohomology.etaleStalkForgetIsoSmallEtaleStalkAb`.

## Main results

* `AlgebraicGeometry.specializationMapOnStalks_comp_etaleStalkIsoSmallEtaleStalkAb_hom` — the
  two specialization maps of an abelian sheaf agree.
* `Stacks.EtaleCohomology.forget₂_map_specializationMapOnStalks_comp_etaleStalkForgetIso` — the
  same for the underlying abelian groups of the stalks of a sheaf of `Λ`-modules.
* `Stacks.EtaleCohomology.bijective_specializationMapOnStalks_of_isIso` — the specialization map
  of a sheaf of `Λ`-modules in the model of Tag 021B is bijective as soon as that of its
  underlying abelian sheaf on Mathlib's small étale site is invertible.

## Implementation notes

The statements for sheaves of `Λ`-modules are made with coefficients `ModuleCat.{u + 1} Λ`, `Λ` in
any universe: this is `EtaleModules.{u, r} Λ S` for `r = 0` and `r = u + 1`, and the abelian
stalks and specialization maps of Mathlib's small étale site live at `Ab.{u + 1}`.

Both specialization maps send the germ of a section over an étale neighbourhood `(U, u)` of `s`
to the germ of the same section over `U` at the lift of the specialized point obtained from the
unique morphism from the strict henselization to `(U, u)`. The two constructions of that
morphism, `AlgebraicGeometry.strictHenselizationEtaleFactor` and
`AlgebraicGeometry.strictHenselizationNeighborhoodLift`, agree by uniqueness.

## References

* [Stacks Project, Section 0GJ2](https://stacks.math.columbia.edu/tag/0GJ2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (s : GeometricPoint S)
  (t : GeometricPoint (strictHenselization B S hS s))

/-- **The two specialization maps of an abelian étale sheaf agree.** For an abelian sheaf `F`
on Mathlib's small étale site of `S`, the specialization map on stalks (Tag 040R) of its
restriction to the small étale site of Tag 021B is the specialization map on stalks of `F`, under
the identifications `AlgebraicGeometry.etaleStalkIsoSmallEtaleStalkAb` at `s` and at the
specialized point. -/
theorem specializationMapOnStalks_comp_etaleStalkIsoSmallEtaleStalkAb_hom
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    specializationMapOnStalks (GeometricSpecialization.ofPoint B S hS s t)
        (((SmallEtale.toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          (SmallEtale.topology B S hS) S.smallEtaleTopology).obj F).obj ≫
        (etaleStalkIsoSmallEtaleStalkAb B hS
          (GeometricSpecialization.ofPoint B S hS s t).target F).hom =
      (etaleStalkIsoSmallEtaleStalkAb B hS s F).hom ≫
        (smallEtaleSpecializationStalkAb B S hS s t).app F := by
  refine colimit.hom_ext fun e => ?_
  obtain ⟨@⟨U, x⟩⟩ := e
  let σ := GeometricSpecialization.ofPoint B S hS s t
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ (etaleStalkIsoSmallEtaleStalkAb B hS σ.target F).hom)
    (ι_comp_specializationMapOnStalks σ _ ⟨x⟩)).trans ?_
  refine (ι_etaleStalkIsoSmallEtaleStalkAb_hom B hS σ.target F U
    ((specializationFiberHom σ).app U x)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (fun k => k ≫ (smallEtaleSpecializationStalkAb B S hS s t).app F)
    (ι_etaleStalkIsoSmallEtaleStalkAb_hom B hS s F U x).symm)
  refine Eq.trans ?_ (smallEtaleSpecializationStalkAb_toPresheafFiber B S hS s t F _ _).symm
  have hfac : strictHenselizationEtaleFactor B S hS s U x =
      strictHenselizationNeighborhoodLift B S hS s ((SmallEtale.toEtaleSite B S hS).obj U)
        (Over.homMk x.1 x.2) :=
    strictHenselizationNeighborhoodLift_eq B S hS s ((SmallEtale.toEtaleSite B S hS).obj U)
      (Over.homMk x.1 x.2) _ (strictHenselizationEtaleFactor_comp B S hS s U x)
      (geometricPointToStrictHenselization_comp_strictHenselizationEtaleFactor B S hS s U x)
  exact congrArg (fun w => (Scheme.pointSmallEtale (t.hom ≫
    strictHenselizationToBase B S hS s)).toPresheafFiber ((SmallEtale.toEtaleSite B S hS).obj U)
      w F.obj) (Over.OverMorphism.ext (congrArg (fun r => t.hom ≫ r) hfac))

end AlgebraicGeometry

open AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

variable (Λ : Type r) [Ring Λ] (B : BigEtaleSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  (s : GeometricPoint S) (t : GeometricPoint (strictHenselization B S hS s))

/-- **The two specialization maps of a sheaf of `Λ`-modules agree on underlying abelian
groups.** For a sheaf `M` of `Λ`-modules on Mathlib's small étale site of `S`, the
specialization map on stalks (Tag 040R) of its transport to the small étale site of Tag 021B,
read on underlying abelian groups, is the specialization map on stalks of the underlying abelian
sheaf of `M`, under the identifications
`Stacks.EtaleCohomology.etaleStalkForgetIsoSmallEtaleStalkAb`
at `s` and at the specialized point. -/
theorem forget₂_map_specializationMapOnStalks_comp_etaleStalkForgetIso
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (specializationMapOnStalks (GeometricSpecialization.ofPoint B S hS s t)
          ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse.obj M).obj) ≫
        (etaleStalkForgetIsoSmallEtaleStalkAb Λ B hS
          (GeometricSpecialization.ofPoint B S hS s t).target M).hom =
      (etaleStalkForgetIsoSmallEtaleStalkAb Λ B hS s M).hom ≫
        (smallEtaleSpecializationStalkAb B S hS s t).app
          ((sheafCompose S.smallEtaleTopology
            (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M) := by
  let σ := GeometricSpecialization.ofPoint B S hS s t
  let P := ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse.obj M).obj
  let Φ := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let M' := (sheafCompose S.smallEtaleTopology Φ).obj M
  refine (isColimitOfPreserves Φ (colimit.isColimit
    ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P))).hom_ext fun e => ?_
  obtain ⟨@⟨U, x⟩⟩ := e
  show Φ.map (colimit.ι _ _) ≫ _ = Φ.map (colimit.ι _ _) ≫ _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ (etaleStalkForgetIsoSmallEtaleStalkAb Λ B hS σ.target M).hom)
    ((Φ.map_comp _ _).symm.trans (congrArg Φ.map
      (ι_comp_specializationMapOnStalks σ P ⟨x⟩)))).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ (etaleStalkIsoSmallEtaleStalkAb B hS σ.target M').hom)
    (ι_preservesColimitIso_hom Φ
      ((CategoryOfElements.π (geometricPointFiber B S hS σ.target)).op ⋙ P)
      (op ((CategoryOfElements.map (specializationFiberHom σ)).obj ⟨x⟩)))).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (fun k => k ≫ (smallEtaleSpecializationStalkAb B S hS s t).app M')
    ((Category.assoc _ _ _).symm.trans (congrArg (fun k => k ≫
      (etaleStalkIsoSmallEtaleStalkAb B hS s M').hom)
      (ι_preservesColimitIso_hom Φ
        ((CategoryOfElements.π (geometricPointFiber B S hS s)).op ⋙ P) (op ⟨x⟩)))).symm)
  have h := congrArg (fun k => colimit.ι ((CategoryOfElements.π
    (geometricPointFiber B S hS s)).op ⋙
      (((SmallEtale.toEtaleSite B S hS).sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} (SmallEtale.topology B S hS) S.smallEtaleTopology).obj M').obj)
      (op ⟨x⟩) ≫ k)
    (specializationMapOnStalks_comp_etaleStalkIsoSmallEtaleStalkAb_hom B hS s t M')
  refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _).symm))
  refine Eq.trans ?_ (congrArg (fun k => k ≫ (etaleStalkIsoSmallEtaleStalkAb B hS σ.target M').hom)
    (ι_comp_specializationMapOnStalks σ _ ⟨x⟩).symm)
  rfl

/-- The specialization map of the transport of `M` at the geometric specialization attached to
a geometric point `t` of the strict henselization is bijective as soon as the abelian one at `t`
is invertible. -/
private theorem bijective_specializationMapOnStalks_ofPoint_of_isIso
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : IsIso ((smallEtaleSpecializationStalkAb B S hS s t).app
      ((sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M))) :
    Function.Bijective (specializationMapOnStalks (GeometricSpecialization.ofPoint B S hS s t)
      ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse.obj M).obj) := by
  let f := specializationMapOnStalks (GeometricSpecialization.ofPoint B S hS s t)
    ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse.obj M).obj
  have h₁ : IsIso ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map f ≫
      (etaleStalkForgetIsoSmallEtaleStalkAb Λ B hS
        (GeometricSpecialization.ofPoint B S hS s t).target M).hom) :=
    (congrArg IsIso (forget₂_map_specializationMapOnStalks_comp_etaleStalkForgetIso
      Λ B hS s t M)).mpr (IsIso.comp_isIso' inferInstance h)
  have h₂ : IsIso ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map f) :=
    IsIso.of_isIso_comp_right _
      (etaleStalkForgetIsoSmallEtaleStalkAb Λ B hS
        (GeometricSpecialization.ofPoint B S hS s t).target M).hom
  have := isIso_of_reflects_iso f (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  exact ConcreteCategory.bijective_of_isIso f

/-- The specialization map at a geometric specialization whose image in `S` is given
separately, reduced to the case of `Stacks.EtaleCohomology.GeometricSpecialization.ofPoint`. -/
private theorem bijective_specializationMapOnStalks_mk_of_isIso
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (k : Type u) [Field k] [IsAlgClosed k]
    (lift : Spec (.of k) ⟶ strictHenselization B S hS s) (hom : Spec (.of k) ⟶ S)
    (hlift : lift ≫ strictHenselizationToBase B S hS s = hom)
    (h : IsIso ((smallEtaleSpecializationStalkAb B S hS s ⟨k, lift⟩).app
      ((sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M))) :
    Function.Bijective (specializationMapOnStalks
      (⟨⟨k, hom⟩, lift, hlift⟩ : GeometricSpecialization B S hS s)
      ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse.obj M).obj) := by
  subst hlift
  exact bijective_specializationMapOnStalks_ofPoint_of_isIso Λ B hS s ⟨k, lift⟩ M h

/-- **Bijectivity of a specialization map in the model of Tag 021B from the abelian one.** If
the specialization map on stalks of the underlying abelian sheaf of a sheaf `M` of `Λ`-modules
on Mathlib's small étale site is invertible, then the specialization map on stalks (Tag 040R) of
the transport of `M` to the small étale site of Tag 021B is bijective. -/
theorem bijective_specializationMapOnStalks_of_isIso
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (σ : GeometricSpecialization B S hS s)
    (h : IsIso ((smallEtaleSpecializationStalkAb B S hS s σ.point).app
      ((sheafCompose S.smallEtaleTopology
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj M))) :
    Function.Bijective
      (specializationMapOnStalks σ
        ((SmallEtale.sheafEquiv B S hS (ModuleCat.{u + 1} Λ)).inverse.obj M).obj) := by
  cases σ with
  | mk target lift hlift =>
    cases target with
    | mk k hom =>
      exact bijective_specializationMapOnStalks_mk_of_isIso Λ B hS s M k lift hom hlift h

end Stacks.EtaleCohomology

end
