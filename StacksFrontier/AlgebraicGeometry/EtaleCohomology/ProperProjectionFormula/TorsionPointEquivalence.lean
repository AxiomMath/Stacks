module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedTensorHom.ConstantRingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldSheaves
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `D(Spec(k)_étale, Λ̲)` is `D(Λ)` for a separably closed field `k`

Let `k` be a separably closed field and `Λ` a commutative ring. Global sections identify sheaves
of `Λ`-modules on the small étale site of `Spec k` with `Λ`-modules
(`Stacks.EtaleCohomology.isEquivalence_globalSections_of_isSepClosed`), hence, through
`Stacks.EtaleCohomology.etaleModulesEquivalence`, `Λ`-modules with sheaves of modules over the
constant ringed site `(Spec(k)_étale, Λ̲)`. This file records that equivalence, the induced
equivalence of unbounded derived categories, and the fact that it carries `Λ` to the structure
sheaf `Λ̲`, i.e. that the constant sheaf of rings `Λ̲` on `Spec(k)_étale` has global sections `Λ`.

## Main definitions

* `Stacks.EtaleCohomology.etalePointModuleEquivalence`: `Mod_Λ ≌ Mod(Spec(k)_étale, Λ̲)`.
* `Stacks.EtaleCohomology.etalePointDerivedEquivalence`: `D(Λ) ≌ D(Spec(k)_étale, Λ̲)`.
* `Stacks.EtaleCohomology.etalePointModuleUnitIso`: the equivalence carries `Λ` to `Λ̲`.
* `Stacks.EtaleCohomology.etalePointDerivedUnitIso`: the derived equivalence carries `Λ[0]` to the
  unit object `Λ̲[0]`.

## Main results

* `Stacks.EtaleCohomology.id_mem_of_mem_etaleSmallModelTopology_point`: the only covering sieve
  of the final object of the small étale site of `Spec k` is the maximal one.
* `Stacks.EtaleCohomology.bijective_etalePointRingMap`: the sheafification map
  `Λ ⟶ Γ(Spec(k)_étale, Λ̲)` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (k : Type u) [Field k] [IsSepClosed k]

/-- The final object `Spec k ⟶ Spec k` of the small model of the small étale site of `Spec k`. -/
abbrev etalePointFinal : AsSmall.{max (u + 1) r} (Spec (.of k)).Etale :=
  AsSmall.up.obj (Scheme.Etale.mk (𝟙 (Spec (.of k))))

/-- **Over a separably closed field the final object has only the maximal covering sieve**, on
the small model of the small étale site: a covering sieve of `Spec k` contains an étale
`V ⟶ Spec k` with a point, hence with a section, so it contains the identity. -/
theorem id_mem_of_mem_etaleSmallModelTopology_point
    {S : Sieve (etalePointFinal.{u, r} k)}
    (hS : S ∈ etaleSmallModelTopology.{u, r} (Spec (.of k)) (etalePointFinal.{u, r} k)) :
    S (𝟙 _) := by
  have : (AsSmall.down : AsSmall.{max (u + 1) r} (Spec (.of k)).Etale ⥤ _).IsCoverDense
      (Spec (.of k)).smallEtaleTopology :=
    inferInstanceAs ((AsSmall.equiv : (Spec (.of k)).Etale ≌
      AsSmall.{max (u + 1) r} (Spec (.of k)).Etale).inverse.IsCoverDense _)
  have : (AsSmall.down : AsSmall.{max (u + 1) r} (Spec (.of k)).Etale ⥤ _).IsLocallyFaithful
      (Spec (.of k)).smallEtaleTopology :=
    inferInstanceAs ((AsSmall.equiv : (Spec (.of k)).Etale ≌
      AsSmall.{max (u + 1) r} (Spec (.of k)).Etale).inverse.IsLocallyFaithful _)
  have : (AsSmall.down : AsSmall.{max (u + 1) r} (Spec (.of k)).Etale ⥤ _).IsLocallyFull
      (Spec (.of k)).smallEtaleTopology :=
    inferInstanceAs ((AsSmall.equiv : (Spec (.of k)).Etale ≌
      AsSmall.{max (u + 1) r} (Spec (.of k)).Etale).inverse.IsLocallyFull _)
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense, mem_smallEtaleTopology_iff] at hS
  obtain ⟨V, f, ⟨Z, g, h, hg, hfac⟩, x, -⟩ := hS (show Spec (.of k) from default)
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed V.hom
    (𝟙 (Spec (.of k))) x (Subsingleton.elim (α := Spec (.of k)) _ _)
  let s : Scheme.Etale.mk (𝟙 (Spec (.of k))) ⟶ V := MorphismProperty.Over.homMk l hl trivial
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of k)))) :=
    have : IsIso (Scheme.Etale.mk (𝟙 (Spec (.of k)))).hom :=
      inferInstanceAs (IsIso (𝟙 (Spec (.of k))))
    isTerminalOfIsIsoHom _
  have : (AsSmall.up.map (s ≫ h) : etalePointFinal.{u, r} k ⟶ Z) ≫ g = 𝟙 _ :=
    ULift.ext (hT.hom_ext _ _)
  rw [← this]
  exact S.downward_closed hg _

/-- The map from the constant presheaf of rings `ULift Λ` to the structure sheaf of the constant
ringed site `(Spec(k)_étale, Λ̲)`, through which `Λ` acts on its sheaves of modules. -/
abbrev etalePointRingMap :=
  Stacks.ConstantRingModules.constantRingedSiteRingMap
    (etaleSmallModelTopology.{u, r} (Spec (.of k))) (ULift.{max (u + 1) r} Λ)

/-- **The constant sheaf of rings `Λ̲` on `Spec(k)_étale` has global sections `Λ`**: the
sheafification map `Λ ⟶ Λ̲(Spec k)` is bijective, being locally injective and locally surjective
for a topology in which the final object has only the maximal covering sieve. -/
theorem bijective_etalePointRingMap :
    Function.Bijective ((etalePointRingMap.{u, r} Λ k).app (op (etalePointFinal.{u, r} k))) := by
  constructor
  · intro a b h
    simpa using id_mem_of_mem_etaleSmallModelTopology_point.{u, r} k
      (Presheaf.equalizerSieve_mem (etaleSmallModelTopology.{u, r} (Spec (.of k)))
        (etalePointRingMap.{u, r} Λ k) a b h)
  · intro s
    obtain ⟨t, ht⟩ := id_mem_of_mem_etaleSmallModelTopology_point.{u, r} k
      (Presheaf.imageSieve_mem (etaleSmallModelTopology.{u, r} (Spec (.of k)))
        (etalePointRingMap.{u, r} Λ k) s)
    exact ⟨t, by simpa using ht⟩

/-- Global sections of sheaves of `Λ`-modules on the small étale site of the spectrum of a
separably closed field is an equivalence. -/
@[sga "4 XVII 5.1.9"]
instance isEquivalence_etaleModuleGlobalSections_point :
    (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).IsEquivalence :=
  have : HasLimitsOfSize.{0, u} (ModuleCat.{max (u + 1) r} Λ) :=
    hasLimitsOfSizeShrink.{0, u, max (u + 1) r, max (u + 1) r} _
  isEquivalence_globalSections_of_isSepClosed k _

/-- **Sheaves of modules on `(Spec(k)_étale, Λ̲)` are `Λ`-modules**, for `k` separably closed:
the inverse of global sections, followed by `Stacks.EtaleCohomology.etaleModulesEquivalence`. -/
def etalePointModuleEquivalence :
    ModuleCat.{max (u + 1) r} Λ ≌ EtaleRingedModules.{u, r} Λ (Spec (.of k)) :=
  (etaleModuleGlobalSections.{u, r} Λ (Spec (.of k))).asEquivalence.symm.trans
    (etaleModulesEquivalence.{u, r} Λ (Spec (.of k)))

/-- The functor `Mod_Λ ⥤ Mod(Spec(k)_étale, Λ̲)` of `etalePointModuleEquivalence` is additive. -/
instance : (etalePointModuleEquivalence.{u, r} Λ k).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The functor `Mod(Spec(k)_étale, Λ̲) ⥤ Mod_Λ` of `etalePointModuleEquivalence` is additive. -/
instance : (etalePointModuleEquivalence.{u, r} Λ k).inverse.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The object `𝟙 : Spec k ⟶ Spec k` of the small étale site of `Spec k` is terminal. -/
def etalePointFinalIsTerminal :
    IsTerminal (Scheme.Etale.mk (𝟙 (Spec (.of k)))) :=
  have : IsIso (Scheme.Etale.mk (𝟙 (Spec (.of k)))).hom :=
    inferInstanceAs (IsIso (𝟙 (Spec (.of k))))
  isTerminalOfIsIsoHom _

/-- The sections over the final object of the sheaf of `Λ`-modules underlying the structure sheaf
`Λ̲`. -/
abbrev etalePointUnitSections : ModuleCat.{max (u + 1) r} Λ :=
  ((etaleModulesEquivalence.{u, r} Λ (Spec (.of k))).inverse.obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (etaleRingedSite.{u, r} Λ (Spec (.of k))).O))).obj.obj
    (op (Scheme.Etale.mk (𝟙 (Spec (.of k)))))

/-- The section `1` of the structure sheaf over the final object. -/
def etalePointUnitSectionsOne : etalePointUnitSections.{u, r} Λ k :=
  (1 : (Stacks.SheafOfModules.Tensor.ringSheaf
    (etaleRingedSite.{u, r} Λ (Spec (.of k))).O).obj.obj (op (etalePointFinal.{u, r} k)))

/-- For `a : Λ`, the section `a • 1` of `Λ̲` over the final object is the image of `a` under the
sheafification map `Λ ⟶ Λ̲(Spec k)`. -/
theorem smul_etalePointUnitSectionsOne (a : Λ) :
    (a • etalePointUnitSectionsOne.{u, r} Λ k : etalePointUnitSections.{u, r} Λ k) =
      (etalePointRingMap.{u, r} Λ k).app (op (etalePointFinal.{u, r} k)) (ULift.up a) := by
  show (etalePointRingMap.{u, r} Λ k).app (op (etalePointFinal.{u, r} k)) (ULift.up a) * 1 = _
  rw [mul_one]

/-- **`Λ̲(Spec k) = Λ`**, as `Λ`-modules: `a ↦ a • 1`. -/
def etalePointUnitSectionsIso :
    ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ) ≅ etalePointUnitSections.{u, r} Λ k :=
  (LinearEquiv.toModuleIso ((Shrink.linearEquiv Λ Λ).trans
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton Λ _ (etalePointUnitSectionsOne.{u, r} Λ k))
      (by
        have h : ⇑(LinearMap.toSpanSingleton Λ _ (etalePointUnitSectionsOne.{u, r} Λ k)) =
            ⇑((etalePointRingMap.{u, r} Λ k).app (op (etalePointFinal.{u, r} k))) ∘
              ULift.up :=
          funext (smul_etalePointUnitSectionsOne.{u, r} Λ k)
        rw [h]
        exact (bijective_etalePointRingMap.{u, r} Λ k).comp
          ⟨fun _ _ h => congrArg ULift.down h, fun b => ⟨b.down, rfl⟩⟩))))

/-- **The equivalence `Mod_Λ ≌ Mod(Spec(k)_étale, Λ̲)` carries `Λ` to the structure sheaf `Λ̲`.**
-/
def etalePointModuleUnitIso :
    (etalePointModuleEquivalence.{u, r} Λ k).functor.obj (ModuleCat.of Λ (Shrink.{max (u + 1) r}
        Λ)) ≅
      SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
        (etaleRingedSite.{u, r} Λ (Spec (.of k))).O) :=
  (etalePointModuleEquivalence.{u, r} Λ k).functor.mapIso
      (etalePointUnitSectionsIso.{u, r} Λ k ≪≫
        ((Sheaf.ΓNatIsoSheafSections (Spec (.of k)).smallEtaleTopology
          (ModuleCat.{max (u + 1) r} Λ) (etalePointFinalIsTerminal k)).app
            ((etaleModulesEquivalence.{u, r} Λ (Spec (.of k))).inverse.obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
                (etaleRingedSite.{u, r} Λ (Spec (.of k))).O)))).symm) ≪≫
    (etalePointModuleEquivalence.{u, r} Λ k).counitIso.app _

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **`D(Λ) ≌ D(Spec(k)_étale, Λ̲)`**, for `k` separably closed: the equivalence induced by
`Stacks.EtaleCohomology.etalePointModuleEquivalence`. -/
def etalePointDerivedEquivalence :
    DerivedCategory (ModuleCat.{max (u + 1) r} Λ) ≌
      DerivedCategory (EtaleRingedModules.{u, r} Λ (Spec (.of k))) :=
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence (etalePointModuleEquivalence.{u, r} Λ k)

/-- The functor of `Stacks.EtaleCohomology.etalePointDerivedEquivalence`: degreewise application
of the equivalence of abelian categories. -/
abbrev etalePointDerived :
    DerivedCategory (ModuleCat.{max (u + 1) r} Λ) ⥤
      DerivedCategory (EtaleRingedModules.{u, r} Λ (Spec (.of k))) :=
  (etalePointModuleEquivalence.{u, r} Λ k).functor.mapDerivedCategory

/-- The functor `etalePointDerived` is essentially surjective. -/
instance : (etalePointDerived.{u, r} Λ k).EssSurj :=
  inferInstanceAs (etalePointDerivedEquivalence.{u, r} Λ k).functor.EssSurj

/-- The functor `etalePointDerived` is an equivalence of categories. -/
instance : (etalePointDerived.{u, r} Λ k).IsEquivalence :=
  inferInstanceAs (etalePointDerivedEquivalence.{u, r} Λ k).functor.IsEquivalence

/-- **The derived equivalence carries `Λ[0]` to the unit object `Λ̲[0]`** of
`D(Spec(k)_étale, Λ̲)`. -/
def etalePointDerivedUnitIso :
    (etalePointDerived.{u, r} Λ k).obj ((DerivedCategory.singleFunctor _ 0).obj
        (ModuleCat.of Λ (Shrink.{max (u + 1) r} Λ))) ≅
      DerivedTensor.RingedSite.unitObject (etaleRingedSite.{u, r} Λ (Spec (.of k))) :=
  ((etalePointModuleEquivalence.{u, r} Λ k).functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (etalePointModuleUnitIso.{u, r} Λ k)

end Derived

end Stacks.EtaleCohomology

end
