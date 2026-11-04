module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexInduction
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantModuleSheafTensor
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.ConstantSheafLocalChainMaps
public import StacksFrontier.CategoryTheory.Sites.Modules.ConstantRingModulesCompatibility
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.MapOutOfALocallyConstantComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.Homology.Injectives.KInjective.RealizeDerivedIso
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.KInjectiveRepresentativesOnAnOpen
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactAdjunctionUnboundedSource
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally constant cohomology of finite type over a field gives a perfect object

Let `(C, O)` be a ringed site whose structure sheaf is the sheafification of the constant presheaf
of rings on a field `Λ`, through a locally bijective map `α : Λ̲ ⟶ O`, so that sheaves of
`O`-modules are sheaves of `Λ`-modules (`Stacks.ConstantRingModules.toModuleSheaf`). An object `K`
of `D(O)` whose cohomology is bounded and whose cohomology sheaves are locally constant of finite
type is a **perfect** object of `D(O)` (Stacks 08G5).

By Stacks 094G (`Stacks.ConstantSheaf.exists_cover_constantComplex_representation`), every object
of the site has a covering on whose members `K` is represented by the constant complex on a
bounded complex `P` of finitely generated `Λ`-modules. Over a field these are finite free, so the
corresponding complex of constant sheaves of `O`-modules is strictly perfect
(`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective`). Choosing
a K-injective representative `E` of `K`, its restrictions to the members of the covering stay
K-injective (Stacks 08FI), so the isomorphisms of the derived category produced by 094G are
realized by quasi-isomorphisms from the strictly perfect local models to `E|_V`
(`CochainComplex.exists_quasiIso_of_isKInjective_of_iso`).

This is the perfectness input of the duality for a smooth proper curve in the proof of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH): there `K = Rf̄_* Λ` has locally constant
cohomology sheaves of finite type and `Λ = ℤ/ℓ`.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfectComplex_of_isKInjective_of_isFiniteTypeLocallyConstant`:
  the statement for a K-injective complex.
* `AlgebraicGeometry.RingedSite.isPerfect_of_isFiniteTypeLocallyConstantModuleSheaf_homology`:
  the statement for an object of `D(O)`, in any model of the derived category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules Stacks.ConstantRingModules

universe w d

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Stacks.ConstantSheaf.overPullback_preservesFiniteLimits
  Stacks.ConstantSheaf.overPullback_preservesFiniteColimits
  Stacks.ConstantSheaf.overPullback_additive

variable (X : RingedSite.{w, w, w}) (Λ : Type w) [Field Λ]
  (α : constRing (C := X.C) Λ ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  [Presheaf.IsLocallyInjective X.J α] [Presheaf.IsLocallySurjective X.J α]

/-- **A K-injective complex with bounded, locally constant cohomology of finite type over a field
is a perfect complex.** -/
theorem isPerfectComplex_of_isKInjective_of_isFiniteTypeLocallyConstant
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    [E.IsKInjective] (a b : ℤ) [E.IsGE a] [E.IsLE b]
    (hE : ∀ n : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf X.J Λ
      ((toModuleSheaf.{w} Λ X.J α).obj (E.homology n))) :
    X.IsPerfectComplex E := by
  classical
  let : HasDerivedCategory (Sheaf X.J (ModuleCat.{w} Λ)) := HasDerivedCategory.standard _
  let : HasDerivedCategory
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
    HasDerivedCategory.standard _
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let F := toModuleSheaf.{w} Λ X.J α
  let hFadd : F.Additive := Functor.additive_of_preserves_binary_products _
  -- the object of `D(C, Λ)` attached to `E`, with its bounds and its cohomology sheaves
  let K₀ : DerivedCategory (Sheaf X.J (ModuleCat.{w} Λ)) :=
    F.mapDerivedCategory.obj (DerivedCategory.Q.obj E)
  have hK₀a : K₀.IsGE a :=
    F.isGE_obj_mapDerivedCategory (DerivedCategory.Q.obj E) a inferInstance
  have hK₀b : K₀.IsLE b :=
    F.isLE_obj_mapDerivedCategory (DerivedCategory.Q.obj E) b inferInstance
  let K : DerivedCategory.Bounded (Sheaf X.J (ModuleCat.{w} Λ)) :=
    ⟨K₀, ⟨⟨a, hK₀a⟩, ⟨b, hK₀b⟩⟩⟩
  have hK : ∀ n : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf X.J Λ
      ((DerivedCategory.homologyFunctor _ n).obj K.obj) := fun n =>
    ObjectProperty.prop_of_iso
      (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{w, w, w} X.J Λ)
      (F.mapIso ((DerivedCategory.homologyFunctorFactors _ n).app E).symm ≪≫
        ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).app
          (DerivedCategory.Q.obj E)).symm) (hE n)
  intro U
  obtain ⟨T, e, I, V, f, hcov, hloc⟩ :=
    Stacks.ConstantSheaf.exists_cover_constantComplex_representation X.J Λ U K hK
  refine ⟨Presieve.ofArrows V f, hcov, ?_⟩
  rintro W g ⟨i⟩
  obtain ⟨P, a', b', hP, hfg, ⟨eP⟩⟩ := hloc i
  let G := X.J.overPullback (ModuleCat.{w} Λ) (V i)
  let αV := overRingMap Λ X.J α (V i)
  let FV := toModuleSheaf.{w} Λ (X.J.over (V i)) αV
  let Φ := constSheafOfModules.{w} Λ (X.J.over (V i)) αV
  let : HasDerivedCategory (Sheaf (X.J.over (V i)) (ModuleCat.{w} Λ)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{w} (R.over (V i))) := HasDerivedCategory.standard _
  let hFVadd : FV.Additive := Functor.additive_of_preserves_binary_products _
  let GV := (moduleSheafEquivalence.{w} Λ (X.J.over (V i)) αV).inverse
  let hGVadd : GV.Additive := Functor.additive_of_preserves_binary_products _
  let L := (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let Ei := X.restrictComplex E (V i)
  have : Ei.IsKInjective := Stacks.Cohomology.Localization.isKInjective_over X.J R (V i) E
  -- `T|_V` is `E|_V` read as a complex of sheaves of `Λ`-modules
  let e₁ : DerivedCategory.Q.obj ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj T) ≅
      DerivedCategory.Q.obj ((FV.mapHomologicalComplex (ComplexShape.up ℤ)).obj Ei) :=
    (G.mapDerivedCategoryFactors.app T).symm ≪≫ G.mapDerivedCategory.mapIso e.symm ≪≫
      G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app E) ≪≫
      G.mapDerivedCategoryFactors.app _ ≪≫ DerivedCategory.Q.mapIso
        ((Functor.mapHomologicalComplexCompIso (toModuleSheafOverIso.{w} Λ X.J α (V i))
          (ComplexShape.up ℤ)).app E ≪≫
        ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (SheafOfModules.overFunctor.{w} R (V i) ⋙ FV)) (ComplexShape.up ℤ)).app E).symm)
  -- the constant complex is the complex of constant sheaves of modules
  let e₂ : ((constantSheaf (X.J.over (V i)) (ModuleCat.{w} Λ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj P ≅ (FV.mapHomologicalComplex (ComplexShape.up ℤ)).obj L :=
    (NatIso.mapHomologicalComplex (constantSheafModuleSheafIso.{w} Λ (X.J.over (V i)) αV)
      (ComplexShape.up ℤ)).app P ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (Φ ⋙ FV)) (ComplexShape.up ℤ)).app P).symm
  let e₃ : DerivedCategory.Q.obj ((FV.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≅
      DerivedCategory.Q.obj ((FV.mapHomologicalComplex (ComplexShape.up ℤ)).obj Ei) :=
    (DerivedCategory.Q.mapIso e₂).symm ≪≫ eP.symm ≪≫ e₁
  let unitC : ∀ A : CochainComplex (SheafOfModules.{w} (R.over (V i))) ℤ,
      A ≅ (GV.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((FV.mapHomologicalComplex (ComplexShape.up ℤ)).obj A) := fun A =>
    ((Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).app A).symm ≪≫
      (NatIso.mapHomologicalComplex (moduleSheafEquivalence.{w} Λ (X.J.over (V i)) αV).unitIso
        (ComplexShape.up ℤ)).app A ≪≫
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (FV ⋙ GV)) (ComplexShape.up ℤ)).app A).symm
  let e₄ : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj Ei :=
    DerivedCategory.Q.mapIso (unitC L) ≪≫ (GV.mapDerivedCategoryFactors.app _).symm ≪≫
      GV.mapDerivedCategory.mapIso e₃ ≪≫ GV.mapDerivedCategoryFactors.app _ ≪≫
      (DerivedCategory.Q.mapIso (unitC Ei)).symm
  obtain ⟨q, hq, -⟩ := CochainComplex.exists_quasiIso_of_isKInjective_of_iso L Ei e₄
  refine ⟨L, ?_, q, hq⟩
  exact Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex_of_finite_projective Φ
    (_root_.PresheafOfModules.sheafificationObjUnitIso αV)
    ((Set.finite_Icc a' b').subset fun n hn => by
      by_contra h
      exact hn (hP n h))
    (fun n => (ModuleCat.isFG_iff _).1 (hfg n)) (fun n =>
      have : Module.Free Λ (P.X n) := Module.Free.of_divisionRing Λ (P.X n)
      Module.Projective.of_free)

/-- **An object of `D(O)` with bounded, locally constant cohomology sheaves of finite type over a
field is perfect** (Stacks 08G5), in any model of the derived category: it is represented by a
K-injective complex, which is a perfect complex by
`AlgebraicGeometry.RingedSite.isPerfectComplex_of_isKInjective_of_isFiniteTypeLocallyConstant`. -/
@[sga "6 I 4.15" "special case"]
theorem isPerfect_of_isFiniteTypeLocallyConstantModuleSheaf_homology
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : ∀ n : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf X.J Λ
      ((toModuleSheaf.{w} Λ X.J α).obj ((DerivedCategory.homologyFunctor _ n).obj K))) :
    X.IsPerfect K := by
  obtain ⟨E, hE, ⟨eE⟩⟩ := Stacks.DerivedGlueing.exists_isKInjective_representative K
  have : E.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso eE.symm a
  have : E.IsLE b := by
    rw [← DerivedCategory.isLE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isLE_of_iso eE.symm b
  refine ⟨E, isPerfectComplex_of_isKInjective_of_isFiniteTypeLocallyConstant X Λ α E a b
    (fun n => ObjectProperty.prop_of_iso
      (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{w, w, w} X.J Λ)
      ((toModuleSheaf.{w} Λ X.J α).mapIso
        ((DerivedCategory.homologyFunctor _ n).mapIso eE.symm ≪≫
          (DerivedCategory.homologyFunctorFactors _ n).app E)) (hK n)), ⟨eE⟩⟩

end AlgebraicGeometry.RingedSite

end
