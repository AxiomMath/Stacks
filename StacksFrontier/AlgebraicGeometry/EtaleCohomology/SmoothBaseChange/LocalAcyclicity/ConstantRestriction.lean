module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StrictlyHenselianSectionsRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.LocallyConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestrictionComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocallyConstantPullback.SmallEtaleConstantSheafPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Restriction of derived sections of constant coefficients

Let `c : T ⟶ Z` be a morphism of schemes and `M` an abelian group. Restriction of global sections
of the constant sheaf `M̲` along `c` is compatible with the units `M ⟶ Γ(-, M̲)` of the constant
sheaf adjunctions: the unit on `Z` followed by restriction is the unit on `T`. On the spectrum of
a separably closed field, and on a strictly henselian local scheme, these units are invertible.
Hence restriction of derived sections of `M̲` from a strictly henselian local scheme to any
geometric point is an isomorphism.

## Main results

* `Stacks.EtaleCohomology.constantSheafAdj_unit_comp_smallEtaleGlobalSectionsRestrictionAb` —
  restriction carries the unit on `Z` to the unit on `T`.
* `Stacks.EtaleCohomology.isIso_constantSheafAdj_unit_app_of_isSepClosed`,
  `Stacks.EtaleCohomology.isIso_constantSheafAdj_unit_app_of_strictlyHenselian` — the units are
  invertible on these schemes.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction_app_of_exact` — for
  exact global sections the derived restriction map is computed degreewise.
* `isIso_smallEtaleDerivedGlobalSectionsRestriction_app_constantComplex_of_strictlyHenselian` —
  restriction of derived sections of `M̲` from a strictly henselian local scheme to a geometric
  point is an isomorphism.
* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedGlobalSectionsRestriction_comp_app_iff` and
  its companions — two out of three for derived restriction along a composite.

## References

* [Stacks Project, Tag 0GJQ](https://stacks.math.columbia.edu/tag/0GJQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable {Z T : Scheme.{u}} (c : T ⟶ Z)

/-- Restriction of global sections along `c : T ⟶ Z` carries the unit `M ⟶ Γ(Z, M̲)` of the
constant sheaf adjunction on `Z`, composed with the identification `c⁻¹M̲ ≅ M̲`, to the unit
`M ⟶ Γ(T, M̲)` of the constant sheaf adjunction on `T`. -/
theorem constantSheafAdj_unit_comp_smallEtaleGlobalSectionsRestrictionAb (M : Ab.{u + 1}) :
    (constantSheafAdj (smallEtaleTopology Z) Ab.{u + 1} (isTerminalEtaleMkId Z)).unit.app M ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Z) Ab.{u + 1}
        (isTerminalEtaleMkId Z)).inv.app _ ≫
      (smallEtaleGlobalSectionsRestrictionAb c).app
        ((constantSheaf (smallEtaleTopology Z) Ab.{u + 1}).obj M) ≫
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map
        ((smallEtalePullbackAbConstantSheafIso c).hom.app M) ≫
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
        (isTerminalEtaleMkId T)).hom.app _ =
    (constantSheafAdj (smallEtaleTopology T) Ab.{u + 1} (isTerminalEtaleMkId T)).unit.app M := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app
    (((constantSheafAdj (smallEtaleTopology Z) Ab.{u + 1} (isTerminalEtaleMkId Z)).comp
      (smallEtaleAdjunctionAb c)).ofNatIsoRight
      (Stacks.ConstantSheaf.pushforwardSectionsIsoOfTerminal (smallEtaleBaseChange c) Ab.{u + 1}
        Z.smallEtaleTopology T.smallEtaleTopology
        (((isTerminalEtaleMkId Z).isTerminalObj (smallEtaleBaseChange c)).uniqueUpToIso
          (isTerminalEtaleMkId T))))
    (constantSheafAdj (smallEtaleTopology T) Ab.{u + 1} (isTerminalEtaleMkId T)) M]
  have hℓ : smallEtaleBaseChangeLift c (Scheme.Etale.mk (𝟙 Z)) c (Category.comp_id c) =
      (((isTerminalEtaleMkId Z).isTerminalObj (smallEtaleBaseChange c)).uniqueUpToIso
        (isTerminalEtaleMkId T)).inv :=
    (isTerminalSmallEtaleBaseChangeObj c (isTerminalEtaleMkId Z)).hom_ext _ _
  have hnat := (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology Ab.{u + 1}
    (isTerminalEtaleMkId T)).hom.naturality ((smallEtalePullbackAbConstantSheafIso c).hom.app M)
  have hnat' : (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology Ab.{u + 1}
        (isTerminalEtaleMkId T)).inv.app
        ((smallEtalePullbackAb c).obj ((constantSheaf Z.smallEtaleTopology Ab.{u + 1}).obj M)) ≫
      (Sheaf.Γ T.smallEtaleTopology Ab.{u + 1}).map
        ((smallEtalePullbackAbConstantSheafIso c).hom.app M) ≫
      (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology Ab.{u + 1}
        (isTerminalEtaleMkId T)).hom.app ((constantSheaf T.smallEtaleTopology Ab.{u + 1}).obj M) =
      ((sheafSections T.smallEtaleTopology Ab.{u + 1}).obj (op (Scheme.Etale.mk (𝟙 T)))).map
        ((smallEtalePullbackAbConstantSheafIso c).hom.app M) := by
    rw [hnat]
    exact Iso.inv_hom_id_app_assoc _ _ _
  simp only [smallEtaleGlobalSectionsRestrictionAb, smallEtaleSectionsPullbackAb, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc, Category.assoc, hnat', hℓ]
  rfl

/-- **Over a separably closed field the constants are the global sections of the constant
sheaf.** -/
theorem isIso_constantSheafAdj_unit_app_of_isSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    (M : Ab.{u + 1}) :
    IsIso ((constantSheafAdj (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}
      (isTerminalEtaleMkId _)).unit.app M) := by
  have := isEquivalence_sheafSections_final_of_isSepClosed Ω Ab.{u + 1}
  have := (constantSheafAdj (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}
    (isTerminalEtaleMkId _)).isEquivalence_left_of_isEquivalence_right
  infer_instance

/-- **Restriction of global sections of a constant sheaf is invertible when the constants are the
global sections on both sides.** -/
theorem isIso_smallEtaleGlobalSectionsRestrictionAb_app_constantSheaf (M : Ab.{u + 1})
    [IsIso ((constantSheafAdj (smallEtaleTopology Z) Ab.{u + 1}
      (isTerminalEtaleMkId Z)).unit.app M)]
    [IsIso ((constantSheafAdj (smallEtaleTopology T) Ab.{u + 1}
      (isTerminalEtaleMkId T)).unit.app M)] :
    IsIso ((smallEtaleGlobalSectionsRestrictionAb c).app
      ((constantSheaf (smallEtaleTopology Z) Ab.{u + 1}).obj M)) := by
  have h : IsIso ((constantSheafAdj (smallEtaleTopology T) Ab.{u + 1}
      (isTerminalEtaleMkId T)).unit.app M) := inferInstance
  rwa [← constantSheafAdj_unit_comp_smallEtaleGlobalSectionsRestrictionAb c M,
    isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff] at h

/-- **On a strictly henselian local scheme the constants are the global sections of the constant
sheaf.** -/
theorem isIso_constantSheafAdj_unit_app_of_strictlyHenselian {R : Type u} [CommRing R]
    [StrictlyHenselianLocalRing R] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (x : Spec (.of Ω) ⟶ Spec (.of R))
    (hx : x (default : Spec (.of Ω)) = IsLocalRing.closedPoint R) (M : Ab.{u + 1}) :
    IsIso ((constantSheafAdj (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}
      (isTerminalEtaleMkId _)).unit.app M) := by
  have h := constantSheafAdj_unit_comp_smallEtaleGlobalSectionsRestrictionAb x M
  have := isIso_smallEtaleGlobalSectionsRestrictionAb_of_strictlyHenselian x hx
    ((constantSheaf (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}).obj M)
  have hΩ := isIso_constantSheafAdj_unit_app_of_isSepClosed Ω M
  rwa [← h, isIso_comp_right_iff] at hΩ

section Derived

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

/-- **The derived inverse image of constant coefficients is constant coefficients**: the
comparison of inverse image with placing a sheaf in degree zero, followed by the identification
of the inverse image of the constant sheaf on `M` with the constant sheaf on `M`. -/
def smallEtaleDerivedPullbackAbConstantComplexIso (M : Ab.{u + 1}) :
    (smallEtaleDerivedPullbackAb c).obj (smallEtaleConstantComplexAb Z M) ≅
      smallEtaleConstantComplexAb T M :=
  ((smallEtalePullbackAb c).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso ((smallEtalePullbackAbConstantSheafIso c).app M)

/-- **Restriction of derived sections for exact global sections is computed degreewise.** If
global sections on `Z` and on `T` are exact and restriction of sections along `c` is invertible
at every term of a complex `K`, then the derived restriction map
`RΓ(Z, K) ⟶ RΓ(T, c⁻¹K)` is invertible. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_app_of_exact
    [((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ))]
    [((Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]
    [PreservesFiniteColimits (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1})]
    [PreservesFiniteColimits (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})]
    (K : CochainComplex (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) ℤ)
    (hK : ∀ i, IsIso ((smallEtaleGlobalSectionsRestrictionAb c).app (K.X i))) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction c).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) := by
  have hfac := smallEtaleDerivedGlobalSectionsRestriction_fac_app c
    ((HomotopyCategory.quotient _ (.up ℤ)).obj K)
  have hZ : IsIso ((smallEtaleDerivedGlobalSectionsUnit Z).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) :=
    Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_of_exact
      (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) K
  have hT : IsIso ((smallEtaleDerivedGlobalSectionsUnit T).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj
        (((smallEtalePullbackAb c).mapHomologicalComplex (.up ℤ)).obj K))) :=
    Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_of_exact
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})
      (((smallEtalePullbackAb c).mapHomologicalComplex (.up ℤ)).obj K)
  have hdeg : IsIso ((Stacks.DerivedFunctor.mapHomotopyCategoryOfComp
      (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}) (smallEtalePullbackAb c)
      (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}) (smallEtaleGlobalSectionsRestrictionAb c)).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K)) := by
    rw [Stacks.DerivedFunctor.mapHomotopyCategoryOfComp_app]
    have : ∀ i, IsIso (((NatTrans.mapHomologicalComplex
        (smallEtaleGlobalSectionsRestrictionAb c) (.up ℤ)).app K).f i) := hK
    have : IsIso ((NatTrans.mapHomologicalComplex (smallEtaleGlobalSectionsRestrictionAb c)
        (.up ℤ)).app ((HomotopyCategory.quotient _ (.up ℤ)).obj K).as) :=
      HomologicalComplex.Hom.isIso_of_components
        ((NatTrans.mapHomologicalComplex (smallEtaleGlobalSectionsRestrictionAb c) (.up ℤ)).app K)
    exact Functor.map_isIso _ _
  have hc : IsIso ((smallEtaleDerivedGlobalSectionsUnit Z).app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≫
      (smallEtaleDerivedGlobalSectionsRestriction c).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K))) := by
    rw [hfac]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hT inferInstance)
  rwa [isIso_comp_left_iff] at hc

/-- **Restriction of derived sections of a sheaf in degree zero, for exact global sections.** If
global sections on `Z` and on `T` are exact and restriction of sections along `c` is invertible
at an abelian sheaf `F`, then so is the derived restriction map at `F` placed in degree zero. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_app_singleFunctor_of_exact
    [((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ))]
    [((Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology T) Ab.{u + 1}) (.up ℤ))]
    [PreservesFiniteColimits (Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1})]
    [PreservesFiniteColimits (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1})]
    (F : Sheaf (smallEtaleTopology Z) Ab.{u + 1})
    (hF : IsIso ((smallEtaleGlobalSectionsRestrictionAb c).app F)) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction c).app
      ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  let K := (HomologicalComplex.single (Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (.up ℤ) 0).obj F
  let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj K) ≅
      (DerivedCategory.singleFunctor _ 0).obj F :=
    ((DerivedCategory.singleFunctorIsoCompQh _ 0).app F).symm
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  refine isIso_smallEtaleDerivedGlobalSectionsRestriction_app_of_exact c K fun i => ?_
  by_cases hi : i = 0
  · subst hi
    exact (NatTrans.isIso_app_iff_of_iso _ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 F)).2 hF
  · have h0 := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 F i hi
    have ht := (Sheaf.Γ (smallEtaleTopology T) Ab.{u + 1}).map_isZero
      ((smallEtalePullbackAb c).map_isZero h0)
    exact ⟨⟨ht.to_ _, ((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1}).map_isZero h0).eq_of_src _ _,
      ht.eq_of_src _ _⟩⟩

/-- **Restriction of derived sections of constant coefficients from a strictly henselian local
scheme to any geometric point is invertible.** For `R` strictly henselian local and any morphism
`t : Spec Ω ⟶ Spec R` from the spectrum of a separably closed field, the map
`RΓ(Spec R, M̲) ⟶ RΓ(Spec Ω, t⁻¹M̲)` is an isomorphism for every abelian group `M`. -/
@[sga "4 VIII 8.6" "special case"]
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_app_constantComplex_of_strictlyHenselian
    {R : Type u} [CommRing R] [StrictlyHenselianLocalRing R] {Ω₀ : Type u} [Field Ω₀]
    [IsAlgClosed Ω₀] (x : Spec (.of Ω₀) ⟶ Spec (.of R))
    (hx : x (default : Spec (.of Ω₀)) = IsLocalRing.closedPoint R)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Spec (.of R))
    [((Sheaf.Γ (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}) (.up ℤ))]
    [((Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}) (.up ℤ))]
    (M : Ab.{u + 1}) :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction t).app
      (smallEtaleConstantComplexAb (Spec (.of R)) M)) := by
  have : ∀ F, IsIso ((smallEtaleGlobalSectionsRestrictionAb x).app F) :=
    isIso_smallEtaleGlobalSectionsRestrictionAb_of_strictlyHenselian x hx
  have : IsIso (smallEtaleGlobalSectionsRestrictionAb x) := NatIso.isIso_of_isIso_app _
  have : (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω₀))) Ab.{u + 1}).IsEquivalence :=
    isEquivalence_globalSections_of_isSepClosed Ω₀ Ab.{u + 1}
  have : (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) Ab.{u + 1}).IsEquivalence :=
    isEquivalence_globalSections_of_isSepClosed Ω Ab.{u + 1}
  have : PreservesFiniteColimits (Sheaf.Γ (smallEtaleTopology (Spec (.of R))) Ab.{u + 1}) :=
    preservesFiniteColimits_of_natIso (asIso (smallEtaleGlobalSectionsRestrictionAb x)).symm
  have := isIso_constantSheafAdj_unit_app_of_strictlyHenselian x hx M
  have := isIso_constantSheafAdj_unit_app_of_isSepClosed Ω M
  exact isIso_smallEtaleDerivedGlobalSectionsRestriction_app_singleFunctor_of_exact t _
    (isIso_smallEtaleGlobalSectionsRestrictionAb_app_constantSheaf t M)

section Comp

variable {X₀ X₁ X₂ : Scheme.{u}} (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂)
  [((Sheaf.Γ (smallEtaleTopology X₀) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology X₁) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X₁) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology X₂) Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X₂) Ab.{u + 1}) (.up ℤ))]
  (N : smallEtaleDerivedCategory X₂)

/-- Restriction of derived sections along `a ≫ b` at `N` is restriction along `b` at `N` followed
by restriction along `a` at `b⁻¹N` and the composition isomorphism of inverse images. -/
private theorem smallEtaleDerivedGlobalSectionsRestriction_comp_app :
    (smallEtaleDerivedGlobalSectionsRestriction (a ≫ b)).app N =
      (smallEtaleDerivedGlobalSectionsRestriction b).app N ≫
        (smallEtaleDerivedGlobalSectionsRestriction a).app
          ((smallEtaleDerivedPullbackAb b).obj N) ≫
        (smallEtaleDerivedGlobalSections X₀).map
          ((smallEtaleDerivedPullbackAbCompIsoQhLift (smallEtalePullbackAbCompIso a b)).hom.app
            N) := by
  rw [smallEtaleDerivedGlobalSectionsRestriction_comp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Category.id_comp]

/-- **Two out of three for restriction of derived sections along a composite**, when the second
restriction is invertible: restriction along `a ≫ b` at `N` is invertible exactly when restriction
along `a` at `b⁻¹N` is. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_comp_app_iff
    [IsIso ((smallEtaleDerivedGlobalSectionsRestriction b).app N)] :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction (a ≫ b)).app N) ↔
      IsIso ((smallEtaleDerivedGlobalSectionsRestriction a).app
        ((smallEtaleDerivedPullbackAb b).obj N)) := by
  rw [smallEtaleDerivedGlobalSectionsRestriction_comp_app, isIso_comp_left_iff,
    isIso_comp_right_iff]

/-- **Two out of three for restriction of derived sections along a composite**, recovering the
second restriction: if restriction along `a ≫ b` at `N` and along `a` at `b⁻¹N` are invertible,
so is restriction along `b` at `N`. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_app_of_comp
    [IsIso ((smallEtaleDerivedGlobalSectionsRestriction (a ≫ b)).app N)]
    [IsIso ((smallEtaleDerivedGlobalSectionsRestriction a).app
      ((smallEtaleDerivedPullbackAb b).obj N))] :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction b).app N) := by
  have h : IsIso ((smallEtaleDerivedGlobalSectionsRestriction (a ≫ b)).app N) := inferInstance
  rwa [smallEtaleDerivedGlobalSectionsRestriction_comp_app, isIso_comp_right_iff] at h

/-- **Two out of three for restriction of constant coefficients along a composite**, when the
second restriction is invertible. -/
theorem isIso_smallEtaleDerivedGlobalSectionsRestriction_comp_app_constantComplex_iff
    (M : Ab.{u + 1})
    [IsIso ((smallEtaleDerivedGlobalSectionsRestriction b).app
      (smallEtaleConstantComplexAb X₂ M))] :
    IsIso ((smallEtaleDerivedGlobalSectionsRestriction (a ≫ b)).app
        (smallEtaleConstantComplexAb X₂ M)) ↔
      IsIso ((smallEtaleDerivedGlobalSectionsRestriction a).app
        (smallEtaleConstantComplexAb X₁ M)) := by
  rw [isIso_smallEtaleDerivedGlobalSectionsRestriction_comp_app_iff]
  exact NatTrans.isIso_app_iff_of_iso _ (smallEtaleDerivedPullbackAbConstantComplexIso b M)

end Comp

end Derived

end Stacks.EtaleCohomology

end
