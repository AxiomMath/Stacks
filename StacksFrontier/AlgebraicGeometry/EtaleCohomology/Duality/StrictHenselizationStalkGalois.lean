module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.LocalAcyclicity.StrictHenselizationCohomologyIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.FieldCohomologyOneKilled

/-!
# Boundary stalks of direct images from the Galois module over the strict henselization

Let `j : U ⟶ S` be quasi-compact and quasi-separated, `s̄` a geometric point of `S` and `G` a
sheaf of `Λ`-modules on `U_étale`. By Stacks 03Q9 the stalks at `s̄` of `R^q j_* G` are the
cohomology groups `H^q(U ×_S Spec 𝒪^{sh}_{S,s̄}, G)`. When `U ×_S Spec 𝒪^{sh}_{S,s̄}` is the
spectrum of a field `K` (at a boundary point of a curve, `K` is the fraction field of the strict
henselization), Stacks 03QU computes these as the continuous cohomology of the absolute Galois
group of `K` with coefficients in the Galois module `M` of `G`. Hence:

* if `c` kills every Galois invariant vector of `M`, then `c` kills the stalk of `j_* G` at `s̄`;
* if `c` times every locally constant `1`-cocycle with values in `M` is a coboundary, then `c`
  kills the stalk of `R¹j_* G` at `s̄`.

This is the sheaf-theoretic half of the computation of the boundary stalks of the levels of an
ℓ-adic sheaf on a curve (`Stacks.EtaleCohomology.LAdicSheaf.SmoothBoundaryPointInput`).

The statements go through the unbounded derived global sections of the small étale site, which
are defined in the model `HasDerivedCategory.standard`; that model is therefore a local instance
in the section `Standard`.

## Main results

* `Stacks.EtaleCohomology.nsmul_id_sheafFiber_eq_zero_of_forgetAb`.
* `Stacks.EtaleCohomology.nsmul_id_sheafFiber_rightDerived_of_strictHenselization`,
  `Stacks.EtaleCohomology.nsmul_id_sheafFiber_directImage_of_strictHenselization` — Stacks 03Q9.
* `Stacks.EtaleCohomology.homologyStrictHenselizationIsoSheafH`,
  `Stacks.EtaleCohomology.nsmul_homology_strictHenselization_zero_eq_zero`,
  `Stacks.EtaleCohomology.nsmul_homology_strictHenselization_one_eq_zero` — Stacks 03QU.
* `Stacks.EtaleCohomology.nsmul_id_sheafFiber_directImage_of_galoisInvariants`,
  `Stacks.EtaleCohomology.nsmul_id_sheafFiber_rightDerived_one_of_galoisCocycles` — the two
  combined.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- **A module stalk is killed by `c` when its underlying abelian stalk is.** For a sheaf `F` of
`Λ`-modules on the small étale site of `X` and a geometric point `s̄`, the underlying abelian
group of the stalk of `F` at `s̄` is the stalk of the underlying abelian sheaf, the forgetful
functor commuting with the filtered colimit computing the stalk. -/
theorem nsmul_id_sheafFiber_eq_zero_of_forgetAb {Λ : Type} [Ring Λ] {X : Scheme.{u}}
    (F : EtaleModules.{u, 0} Λ X) (s : GeometricPoint X) (c : ℕ)
    (h : c • 𝟙 ((smallEtaleStalkAb s.hom).obj ((etaleModuleForgetAb.{u, 0} Λ X).obj F)) = 0) :
    c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) = 0 := by
  let Φ := Scheme.pointSmallEtale s.hom
  let e := (Φ.presheafFiberCompIso (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app F.obj
  apply (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map_injective
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero]
  have h' : c • 𝟙 (Φ.presheafFiber.obj
      (F.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) = 0 := h
  have h2 : c • 𝟙 ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      (Φ.presheafFiber.obj F.obj)) = e.inv ≫ (c • 𝟙 _) ≫ e.hom := by
    simp
  show c • 𝟙 ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      (Φ.presheafFiber.obj F.obj)) = 0
  rw [h2]
  show e.inv ≫ (c • 𝟙 (Φ.presheafFiber.obj
      (F.obj ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}))) ≫ e.hom = 0
  rw [h', zero_comp, comp_zero]

section Standard

attribute [local instance] HasDerivedCategory.standard

/-- **Stalks of higher direct images of sheaves of modules, from the strict henselization**
(Stacks 03Q9). For `j : U ⟶ S` quasi-compact and quasi-separated, a geometric point `s̄` of `S`
and a sheaf `G` of `Λ`-modules on `U_étale`: if `c` kills every element of
`H^q(U ×_S Spec 𝒪^{sh}_{S,s̄}, G)`, then `c` kills the stalk at `s̄` of `R^q j_* G`. -/
theorem nsmul_id_sheafFiber_rightDerived_of_strictHenselization (B : BigEtaleSite.{u})
    {U S : Scheme.{u}} (hS : B.Contains S) (j : U ⟶ S) [QuasiCompact j] [QuasiSeparated j]
    (s : GeometricPoint S) {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ U) (q c : ℕ)
    (h : ∀ z : (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS j s)).obj
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS j s)).obj
            ((DerivedCategory.singleFunctor _ 0).obj ((etaleModuleForgetAb.{u, 0} Λ U).obj G)))),
        c • z = 0) :
    c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj G)) = 0 := by
  refine nsmul_id_sheafFiber_eq_zero_of_forgetAb _ s c ?_
  let E := (smallEtaleStalkAb s.hom).mapIso (etaleModuleForgetRightDerivedDirectImageIso Λ j G q) ≪≫
    stalkRightDerivedPushforwardIsoStrictHenselization B hS j s
      ((etaleModuleForgetAb.{u, 0} Λ U).obj G) q
  have hY : c • 𝟙 ((DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS j s)).obj
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS j s)).obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((etaleModuleForgetAb.{u, 0} Λ U).obj G))))) = 0 := by
    ext z
    simpa using h z
  have h2 : c • 𝟙 ((smallEtaleStalkAb s.hom).obj ((etaleModuleForgetAb.{u, 0} Λ S).obj
      (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived q).obj G))) =
      E.hom ≫ (c • 𝟙 _) ≫ E.inv := by
    simp
  rw [h2, hY, zero_comp, comp_zero]

/-- **The stalk of a direct image of sheaves of modules, from the strict henselization**
(Stacks 03Q9 in degree zero). If `c` kills every element of `H⁰(U ×_S Spec 𝒪^{sh}_{S,s̄}, G)`,
then `c` kills the stalk at `s̄` of `j_* G`. -/
theorem nsmul_id_sheafFiber_directImage_of_strictHenselization (B : BigEtaleSite.{u})
    {U S : Scheme.{u}} (hS : B.Contains S) (j : U ⟶ S) [QuasiCompact j] [QuasiSeparated j]
    (s : GeometricPoint S) {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ U) (c : ℕ)
    (h : ∀ z : (DerivedCategory.homologyFunctor Ab.{u + 1} ((0 : ℕ) : ℤ)).obj
        ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS j s)).obj
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS j s)).obj
            ((DerivedCategory.singleFunctor _ 0).obj ((etaleModuleForgetAb.{u, 0} Λ U).obj G)))),
        c • z = 0) :
    c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((etaleModuleDirectImage.{u, 0} Λ j).obj G)) = 0 := by
  let E := ((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).mapIso
    ((etaleModuleDirectImage.{u, 0} Λ j).rightDerivedZeroIsoSelf.app G)
  have h2 : c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((etaleModuleDirectImage.{u, 0} Λ j).obj G)) = E.inv ≫ (c • 𝟙 _) ≫ E.hom := by
    simp
  rw [h2, nsmul_id_sheafFiber_rightDerived_of_strictHenselization B hS j s G 0 c h, zero_comp,
    comp_zero]

/-- **Cohomology over the strict henselization, read on the spectrum of a field.** If
`U ×_S Spec 𝒪^{sh}_{S,s̄} ≅ Spec K`, the degree-`q` cohomology over it of the inverse image of an
abelian sheaf `F` on `U` is `H^q(Spec K, F|)`, `F|` the inverse image of `F` along
`Spec K ≅ U ×_S Spec 𝒪^{sh}_{S,s̄} ⟶ U`. -/
def homologyStrictHenselizationIsoSheafH (B : BigEtaleSite.{u}) {U S : Scheme.{u}}
    (hS : B.Contains S) (j : U ⟶ S) (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology U) Ab.{u + 1}) {K : Type u} [Field K]
    (e : strictHenselizationBaseChange B hS j s ≅ Spec (.of K)) (q : ℕ) :
    letI := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of K))
    (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).obj
        ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS j s)).obj
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS j s)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F))) ≅
      (Sheaf.functorH ((Spec (.of K) : Scheme.{u})).smallEtaleTopology q).obj
        ((smallEtalePullbackAb (e.inv ≫ strictHenselizationBaseChangeToSource B hS j s)).obj F) :=
  letI := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of K))
  haveI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse (Spec (.of K))
  homologyDerivedSectionsPullbackIsoOfIso e (a := strictHenselizationBaseChangeToSource B hS j s)
      (a' := e.inv ≫ strictHenselizationBaseChangeToSource B hS j s) (by simp)
      ((DerivedCategory.singleFunctor _ 0).obj F) (q : ℤ) ≪≫
    (DerivedCategory.homologyFunctor Ab.{u + 1} (q : ℤ)).mapIso
      ((smallEtaleDerivedGlobalSections (Spec (.of K))).mapIso
        (((smallEtalePullbackAb (e.inv ≫ strictHenselizationBaseChangeToSource B hS j s)
          ).mapDerivedCategorySingleFunctor 0).app F)) ≪≫
    Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
      (Sheaf.Γ (smallEtaleTopology (Spec (.of K))) Ab.{u + 1})
      (smallEtaleDerivedGlobalSections (Spec (.of K)))
      (smallEtaleDerivedGlobalSectionsUnit (Spec (.of K)))
      (Stacks.DerivedFunctor.exists_quasiIso_isKInjective.{u + 1, u + 2})
      ((smallEtalePullbackAb (e.inv ≫ strictHenselizationBaseChangeToSource B hS j s)).obj F) q ≪≫
    (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u, u + 1} _ q).app _

/-- **`H¹` over the strict henselization from a bound on Galois cocycles.** If
`U ×_S Spec 𝒪^{sh}_{S,s̄} ≅ Spec K` and `c` times every locally constant `1`-cocycle of the
absolute Galois group of `K` with values in the Galois module of `F|` is a coboundary, then `c`
kills `H¹(U ×_S Spec 𝒪^{sh}_{S,s̄}, F)` (Stacks 03QU). -/
theorem nsmul_homology_strictHenselization_one_eq_zero (B : BigEtaleSite.{u}) {U S : Scheme.{u}}
    (hS : B.Contains S) (j : U ⟶ S) (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology U) Ab.{u + 1}) {K : Type u} [Field K]
    (e : strictHenselizationBaseChange B hS j s ≅ Spec (.of K)) (B' : BigEtaleSite.{u})
    (hK : B'.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K))) (c : ℕ)
    (hM : let M := ((etaleContinuousGModuleEquivalence.{u, u + 1} B' K hK sbar).functor.obj
        ((smallEtaleSheafRestriction B' K hK).obj
          ((smallEtalePullbackAb (e.inv ≫ strictHenselizationBaseChangeToSource B hS j s)).obj F)));
      ∀ γ : GeometricPoint.absoluteGaloisGroup sbar → M.obj.obj.V, IsLocallyConstant γ →
        (∀ g₁ g₂, γ (g₁ * g₂) = (M.obj.obj.ρ g₁).asHom.hom (γ g₂) + γ g₁) →
        ∃ x : M.obj.obj.V, ∀ g, (M.obj.obj.ρ g).asHom.hom x - x = c • γ g)
    (z : (DerivedCategory.homologyFunctor Ab.{u + 1} ((1 : ℕ) : ℤ)).obj
        ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS j s)).obj
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS j s)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) :
    c • z = 0 := by
  let := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of K))
  let E := homologyStrictHenselizationIsoSheafH B hS j s F e 1
  have hx := nsmul_smallEtaleSheafH_one_eq_zero B' K hK sbar
    ((smallEtalePullbackAb (e.inv ≫ strictHenselizationBaseChangeToSource B hS j s)).obj F) c hM
    (E.hom z)
  have h1 : z = E.inv (E.hom z) := (ConcreteCategory.congr_hom E.hom_inv_id z).symm
  rw [h1, ← map_nsmul, show c • (ConcreteCategory.hom E.hom) z = 0 from hx, map_zero]

/-- **`H⁰` over the strict henselization from a bound on Galois invariants.** If
`U ×_S Spec 𝒪^{sh}_{S,s̄} ≅ Spec K` and `c` kills every Galois invariant vector of the Galois
module of `F|`, then `c` kills `H⁰(U ×_S Spec 𝒪^{sh}_{S,s̄}, F)` (Stacks 03QU). -/
theorem nsmul_homology_strictHenselization_zero_eq_zero (B : BigEtaleSite.{u}) {U S : Scheme.{u}}
    (hS : B.Contains S) (j : U ⟶ S) (s : GeometricPoint S)
    (F : Sheaf (smallEtaleTopology U) Ab.{u + 1}) {K : Type u} [Field K]
    (e : strictHenselizationBaseChange B hS j s ≅ Spec (.of K)) (B' : BigEtaleSite.{u})
    (hK : B'.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K))) (c : ℕ)
    (hM : let M := ((etaleContinuousGModuleEquivalence.{u, u + 1} B' K hK sbar).functor.obj
        ((smallEtaleSheafRestriction B' K hK).obj
          ((smallEtalePullbackAb (e.inv ≫ strictHenselizationBaseChangeToSource B hS j s)).obj F)));
      ∀ v : M.obj.obj.V, (∀ g, (M.obj.obj.ρ g).asHom.hom v = v) → c • v = 0)
    (z : (DerivedCategory.homologyFunctor Ab.{u + 1} ((0 : ℕ) : ℤ)).obj
        ((smallEtaleDerivedGlobalSections (strictHenselizationBaseChange B hS j s)).obj
          ((smallEtaleDerivedPullbackAb (strictHenselizationBaseChangeToSource B hS j s)).obj
            ((DerivedCategory.singleFunctor _ 0).obj F)))) :
    c • z = 0 := by
  let := hasExt_smallEtaleSheaf_objectUniverse (Spec (.of K))
  let F' := (smallEtalePullbackAb (e.inv ≫ strictHenselizationBaseChangeToSource B hS j s)).obj F
  let M := (etaleContinuousGModuleEquivalence.{u, u + 1} B' K hK sbar).functor.obj
    ((smallEtaleSheafRestriction B' K hK).obj F')
  let E := homologyStrictHenselizationIsoSheafH B hS j s F e 0
  let φ := smallEtaleSheafCohomologyAddEquivContinuousGroupCohomology B' K hK sbar F' 0
  let ψ := Stacks.GroupCohomology.invariantsIsoZerothCohomology.{u, u + 1}
    (GeometricPoint.absoluteGaloisGroup sbar) M
  have hw : ∀ w : (continuousGModuleInvariants.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar)).obj M, c • w = 0 :=
    fun w => Subtype.ext (hM w.1 fun g => w.2 g)
  let x : Sheaf.H.{u + 1, u + 1} F' 0 := E.hom z
  obtain ⟨w, hw'⟩ : ∃ w, ψ.hom w = φ x :=
    ⟨ψ.inv _, ConcreteCategory.congr_hom ψ.inv_hom_id _⟩
  let ψh : (continuousGModuleInvariants.{u, u + 1}
      (GeometricPoint.absoluteGaloisGroup sbar)).obj M →+
      continuousGroupCohomology.{u, u + 1} (GeometricPoint.absoluteGaloisGroup sbar) 0 M :=
    ConcreteCategory.hom ψ.hom
  let f := φ.symm.toAddMonoidHom.comp ψh
  have hxw : x = f w := by
    show x = φ.symm (ψ.hom w)
    rw [hw', AddEquiv.symm_apply_apply]
  have k1 : c • x = 0 := by
    rw [hxw, ← f.map_nsmul, hw w, f.map_zero]
  have h1 : z = E.inv (E.hom z) := (ConcreteCategory.congr_hom E.hom_inv_id z).symm
  rw [h1, ← map_nsmul, show c • (ConcreteCategory.hom E.hom) z = 0 from k1, map_zero]

/-- **`c` kills the Galois invariants of `G` over `K`.** For `j : U ⟶ S`, a geometric point `s̄`
of `S`, a sheaf `G` of `Λ`-modules on `U_étale` and `U ×_S Spec 𝒪^{sh}_{S,s̄} ≅ Spec K`: `c` kills
every vector of the Galois module at `t̄` of the restriction of `G` to `Spec K` fixed by the
absolute Galois group. -/
def GaloisModuleInvariantsKilledBy (B : BigEtaleSite.{u}) {U S : Scheme.{u}} (hS : B.Contains S)
    (j : U ⟶ S) (s : GeometricPoint S) {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ U)
    {K : Type u} [Field K] (e : strictHenselizationBaseChange B hS j s ≅ Spec (.of K))
    (B' : BigEtaleSite.{u}) (hK : B'.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K)))
    (c : ℕ) : Prop :=
  let M := ((etaleContinuousGModuleEquivalence.{u, u + 1} B' K hK sbar).functor.obj
    ((smallEtaleSheafRestriction B' K hK).obj
      ((smallEtalePullbackAb (e.inv ≫ strictHenselizationBaseChangeToSource B hS j s)).obj
        ((etaleModuleForgetAb.{u, 0} Λ U).obj G))))
  ∀ v : M.obj.obj.V, (∀ g, (M.obj.obj.ρ g).asHom.hom v = v) → c • v = 0

/-- **`c` bounds the Galois cocycles of `G` over `K`.** In the setting of
`Stacks.EtaleCohomology.GaloisModuleInvariantsKilledBy`: `c` times every locally constant
`1`-cocycle of the absolute Galois group of `K` with values in the Galois module of the
restriction of `G` to `Spec K` is a coboundary. -/
def GaloisModuleCocyclesKilledBy (B : BigEtaleSite.{u}) {U S : Scheme.{u}} (hS : B.Contains S)
    (j : U ⟶ S) (s : GeometricPoint S) {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ U)
    {K : Type u} [Field K] (e : strictHenselizationBaseChange B hS j s ≅ Spec (.of K))
    (B' : BigEtaleSite.{u}) (hK : B'.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K)))
    (c : ℕ) : Prop :=
  let M := ((etaleContinuousGModuleEquivalence.{u, u + 1} B' K hK sbar).functor.obj
    ((smallEtaleSheafRestriction B' K hK).obj
      ((smallEtalePullbackAb (e.inv ≫ strictHenselizationBaseChangeToSource B hS j s)).obj
        ((etaleModuleForgetAb.{u, 0} Λ U).obj G))))
  ∀ γ : GeometricPoint.absoluteGaloisGroup sbar → M.obj.obj.V, IsLocallyConstant γ →
    (∀ g₁ g₂, γ (g₁ * g₂) = (M.obj.obj.ρ g₁).asHom.hom (γ g₂) + γ g₁) →
    ∃ x : M.obj.obj.V, ∀ g, (M.obj.obj.ρ g).asHom.hom x - x = c • γ g

/-- **The stalk of `j_* G` at `s̄` from the Galois invariants over `K`.** For
`j : U ⟶ S` quasi-compact and quasi-separated, a sheaf `G` of `Λ`-modules on `U_étale` and
`U ×_S Spec 𝒪^{sh}_{S,s̄} ≅ Spec K`: if `c` kills every Galois invariant vector of the Galois
module of the restriction of `G` to `Spec K`, then `c` kills the stalk of `j_* G` at `s̄`
(Stacks 03Q9 and 03QU). -/
theorem nsmul_id_sheafFiber_directImage_of_galoisInvariants (B : BigEtaleSite.{u})
    {U S : Scheme.{u}} (hS : B.Contains S) (j : U ⟶ S) [QuasiCompact j] [QuasiSeparated j]
    (s : GeometricPoint S) {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ U) {K : Type u}
    [Field K] (e : strictHenselizationBaseChange B hS j s ≅ Spec (.of K)) (B' : BigEtaleSite.{u})
    (hK : B'.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K))) (c : ℕ)
    (hM : GaloisModuleInvariantsKilledBy B hS j s G e B' hK sbar c) :
    c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((etaleModuleDirectImage.{u, 0} Λ j).obj G)) = 0 :=
  nsmul_id_sheafFiber_directImage_of_strictHenselization B hS j s G c
    (nsmul_homology_strictHenselization_zero_eq_zero B hS j s _ e B' hK sbar c hM)

/-- **The stalk of `R¹j_* G` at `s̄` from a bound on Galois cocycles over `K`.** For
`j : U ⟶ S` quasi-compact and quasi-separated, a sheaf `G` of `Λ`-modules on `U_étale` and
`U ×_S Spec 𝒪^{sh}_{S,s̄} ≅ Spec K`: if `c` times every locally constant `1`-cocycle of the
absolute Galois group of `K` with values in the Galois module of the restriction of `G` is a
coboundary, then `c` kills the stalk of `R¹j_* G` at `s̄` (Stacks 03Q9 and 03QU). -/
theorem nsmul_id_sheafFiber_rightDerived_one_of_galoisCocycles (B : BigEtaleSite.{u})
    {U S : Scheme.{u}} (hS : B.Contains S) (j : U ⟶ S) [QuasiCompact j] [QuasiSeparated j]
    (s : GeometricPoint S) {Λ : Type} [Ring Λ] (G : EtaleModules.{u, 0} Λ U) {K : Type u}
    [Field K] (e : strictHenselizationBaseChange B hS j s ≅ Spec (.of K)) (B' : BigEtaleSite.{u})
    (hK : B'.Contains (Spec (.of K))) (sbar : GeometricPoint (Spec (.of K))) (c : ℕ)
    (hM : GaloisModuleCocyclesKilledBy B hS j s G e B' hK sbar c) :
    c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived 1).obj G)) = 0 :=
  nsmul_id_sheafFiber_rightDerived_of_strictHenselization B hS j s G 1 c
    (nsmul_homology_strictHenselization_one_eq_zero B hS j s _ e B' hK sbar c hM)

end Standard

end Stacks.EtaleCohomology

end
