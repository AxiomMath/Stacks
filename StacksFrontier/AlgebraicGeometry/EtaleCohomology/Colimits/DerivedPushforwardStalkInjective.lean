module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.StrictHenselizationStalkCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveTruncationTower
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution

/-!
# The stalk of a derived direct image at a bounded below complex of injectives

Let `f : X ⟶ Y` be a morphism of schemes and `s` a geometric point of `Y`, with
`p : X ×_Y Spec 𝒪^{sh}_{Y,s} ⟶ X` the projection. This file reduces the invertibility of the
canonical map `(Rf_*G)_s ⟶ RΓ(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹G)` of Stacks 0GIX, for every abelian
sheaf `G`, to two statements about injective sheaves `I` on `X_étale`: the map on sheaves
`(f_*I)_s ⟶ Γ(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹I)` is an isomorphism, and `p⁻¹I` is acyclic for global
sections. This is the proof of Stacks 03Q9 in all degrees from its degree zero case: resolve `G`
by a bounded below complex `J` of injectives; `Rf_*` is computed on `J`, the stalk of `f_*J` is
degreewise `Γ(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹J)`, and `RΓ` is computed on the complex `p⁻¹J` of
acyclic sheaves (Leray's acyclicity lemma).

## Main results

* `Stacks.EtaleCohomology.LimitExt.isIso_derivedPushforwardStalk_single_of_injective`.

## Implementation notes

The invertibility of the comparison on the homotopy category is proved by working on the goal
produced by unfolding it (`refine` with explicit `@` applications, the map on sheaves generalized
to a variable), never by restating its factors: the restated factors carry instance arguments
found by instance search, which differ from those inside the definition, and the kernel then
unfolds the map on sheaves and times out.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace Stacks.EtaleCohomology.LimitExt

/-- A component of a composite of four natural transformations is invertible as soon as the four
components are. -/
theorem isIso_comp_app_of_isIso₄ {C D : Type*} [Category* C] [Category* D] {F₀ F₁ F₂ F₃ F₄ : C ⥤ D}
    (a : F₀ ⟶ F₁) (b : F₁ ⟶ F₂) (c : F₂ ⟶ F₃) (d : F₃ ⟶ F₄) (X : C) (ha : IsIso (a.app X))
    (hb : IsIso (b.app X)) (hc : IsIso (c.app X)) (hd : IsIso (d.app X)) :
    IsIso ((a ≫ b ≫ c ≫ d).app X) := by
  simp only [NatTrans.comp_app]
  infer_instance

section Assembly

variable (B : BigEtaleSite.{u}) {X Y : Scheme.{u}} (hY : B.Contains Y) (f : X ⟶ Y)
  (s : GeometricPoint Y)
  [((smallEtalePushforwardAb f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ))]
  [((Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hY f s))
        Ab.{u + 1}).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso
        (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hY f s)) Ab.{u + 1}) (.up ℤ))]

/-- The unit of `RΓ` on the base change to the strict henselization is invertible at the inverse
image of a bounded below complex of injective sheaves. -/
theorem isIso_derivedGlobalSectionsUnit_pullback
    (hacyc : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hY f s))
        Ab.{u + 1}).rightAcyclic
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hY f s)).obj I))
    (J : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) (n : ℤ)
    [CochainComplex.IsStrictlyGE J n]
    (hJ : ∀ k, Injective (J.X k)) :
    IsIso ((smallEtaleDerivedGlobalSectionsUnit (strictHenselizationBaseChange B hY f s)).app
      ((HomotopyCategory.quotient
        (Sheaf (smallEtaleTopology (strictHenselizationBaseChange B hY f s)) Ab.{u + 1})
        (.up ℤ)).obj
        (((smallEtalePullbackAb
          (strictHenselizationBaseChangeToSource B hY f s)).mapHomologicalComplex
          (.up ℤ)).obj J))) := by
  let Z := strictHenselizationBaseChange B hY f s
  have : EnoughInjectives (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    smallEtaleAbSheaf_enoughInjectives Z
  have : IsGrothendieckAbelian.{u + 1} (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Z
  let p := smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hY f s)
  let K := (p.mapHomologicalComplex (.up ℤ)).obj J
  have : CochainComplex.IsStrictlyGE K n :=
    (CochainComplex.isStrictlyGE_iff K n).2 fun k hk =>
      p.map_isZero ((CochainComplex.isStrictlyGE_iff J n).1 inferInstance k hk)
  obtain ⟨I, j, _, hI, _⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  have : QuasiIso ((((Sheaf.Γ (smallEtaleTopology Z) Ab.{u + 1})).mapHomologicalComplex
      (.up ℤ)).map j) :=
    Stacks.TruncationTower.quasiIso_map_of_boundedBelow_acyclic _ j ⟨n, inferInstance⟩
      ⟨n, inferInstance⟩
      (fun k => by
        exact hacyc (J.X k) (hJ k))
      (fun k => by
        have := hI k
        exact CategoryTheory.Functor.rightAcyclic_of_injective _ (I.X k))
  exact Stacks.TruncationTower.isIso_derivedUnit_of_quasiIso_map _
    (Stacks.DerivedFunctor.exists_quasiIso_isKInjective.{u + 1, u + 2})
    (smallEtaleDerivedGlobalSections Z) (smallEtaleDerivedGlobalSectionsUnit Z) j
    (CochainComplex.isKInjective_of_injective I n)

/-- The unit of `Rf_*` is invertible at a K-injective complex. -/
theorem isIso_derivedPushforwardUnit_of_isKInjective
    (J : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) (hJK : J.IsKInjective) :
    IsIso ((smallEtaleDerivedPushforwardAbUnit f).app
      ((HomotopyCategory.quotient (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)).obj J)) := by
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    smallEtaleAbSheaf_enoughInjectives X
  have : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  have : QuasiIso (((smallEtalePushforwardAb f).mapHomologicalComplex (.up ℤ)).map (𝟙 J)) := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  exact Stacks.TruncationTower.isIso_derivedUnit_of_quasiIso_map (smallEtalePushforwardAb f)
    (Stacks.DerivedFunctor.exists_quasiIso_isKInjective.{u + 1, u + 2})
    (smallEtaleDerivedPushforwardAb f) (smallEtaleDerivedPushforwardAbUnit f) (𝟙 J) hJK

/-- The comparison on the homotopy category is invertible at a bounded below complex of
injective sheaves, given degree zero on injective sheaves. -/
theorem isIso_derivedPushforwardStalkUnit_of_injective
    (hacyc : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hY f s))
        Ab.{u + 1}).rightAcyclic
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hY f s)).obj I))
    (hC : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      IsIso ((pushforwardStalkToStrictHenselizationSectionsAb B hY f s).app I))
    (J : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) (n : ℤ)
    [CochainComplex.IsStrictlyGE J n] (hJ : ∀ k, Injective (J.X k)) :
    IsIso ((derivedPushforwardStalkToStrictHenselizationSectionsUnit B hY f s).app
      ((HomotopyCategory.quotient (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)).obj J)) := by
  refine isIso_comp_app_of_isIso₄ _ _ _ _ _ (NatIso.isIso_app_of_isIso _ _)
    (NatIso.isIso_app_of_isIso _ _) (NatIso.isIso_app_of_isIso _ _) ?_
  rw [Stacks.DerivedFunctor.exactDerivedDescUnit_app]
  refine IsIso.comp_isIso' ?_ (IsIso.comp_isIso' ?_ ?_)
  · refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    rw [Stacks.DerivedFunctor.mapHomotopyCategoryOfComp, NatTrans.comp_app,
      NatTrans.mapHomotopyCategory_app]
    generalize pushforwardStalkToStrictHenselizationSectionsAb B hY f s = τ at hC ⊢
    refine IsIso.comp_isIso' ?_ inferInstance
    refine @Functor.map_isIso _ _ _ _ _ _ _ _ ?_
    refine @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ _ (fun k => ?_)
    exact hC _ (hJ k)
  · exact isIso_derivedGlobalSectionsUnit_pullback B hY f s hacyc J n hJ
  · exact Functor.map_isIso _ _

/-- **Stacks 03Q9 in all degrees, from degree zero on injective sheaves**, at a K-injective
bounded below complex of injectives. -/
theorem isIso_derivedPushforwardStalk_quotient_of_injective
    (hacyc : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hY f s))
        Ab.{u + 1}).rightAcyclic
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hY f s)).obj I))
    (hC : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      IsIso ((pushforwardStalkToStrictHenselizationSectionsAb B hY f s).app I))
    (J : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) (n : ℤ)
    [CochainComplex.IsStrictlyGE J n] (hJ : ∀ k, Injective (J.X k)) :
    IsIso ((derivedPushforwardStalkToStrictHenselizationSections B hY f s).app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (Sheaf (smallEtaleTopology X) Ab.{u + 1})
          (.up ℤ)).obj J))) := by
  have : ∀ k, Injective (J.X k) := hJ
  have := isIso_derivedPushforwardUnit_of_isKInjective f J
    (CochainComplex.isKInjective_of_injective J n)
  have hU := isIso_derivedPushforwardStalkUnit_of_injective B hY f s hacyc hC J n hJ
  rw [← derivedPushforwardStalkToStrictHenselizationSections_fac_app] at hU
  exact IsIso.of_isIso_comp_left ((smallEtaleDerivedStalkAb s.hom).map
    ((smallEtaleDerivedPushforwardAbUnit f).app
      ((HomotopyCategory.quotient (Sheaf (smallEtaleTopology X) Ab.{u + 1}) (.up ℤ)).obj J))) _

/-- **Stacks 03Q9 on `D⁺`, from degree zero and acyclicity on injective sheaves.** Under the same
two hypotheses, the canonical map `(Rf_*K)_s ⟶ RΓ(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹K)` is an
isomorphism for every bounded below `K`: resolve `K` by a bounded below complex of injectives. -/
theorem isIso_derivedPushforwardStalk_of_isGE_of_injective
    (hacyc : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hY f s))
        Ab.{u + 1}).rightAcyclic
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hY f s)).obj I))
    (hC : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      IsIso ((pushforwardStalkToStrictHenselizationSectionsAb B hY f s).app I))
    (K : DerivedCategory (Sheaf (smallEtaleTopology X) Ab.{u + 1})) (n : ℤ) [K.IsGE n] :
    IsIso ((derivedPushforwardStalkToStrictHenselizationSections B hY f s).app K) := by
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    smallEtaleAbSheaf_enoughInjectives X
  obtain ⟨L, _, ⟨eL⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K n
  obtain ⟨J, i, _, hJ, _⟩ := CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective L n
  have : IsIso (DerivedCategory.Q.map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (Sheaf (smallEtaleTopology X) Ab.{u + 1}) i).2
      inferInstance
  let e : K ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (.up ℤ)).obj J) :=
    eL ≪≫ asIso (DerivedCategory.Q.map i) ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app J
  exact (NatTrans.isIso_app_iff_of_iso _ e).2
    (isIso_derivedPushforwardStalk_quotient_of_injective B hY f s hacyc hC J n hJ)

/-- **Stacks 03Q9 in all degrees, from degree zero on injective sheaves.** If for every injective
abelian sheaf `I` on `X_étale` the map `(f_*I)_s ⟶ Γ(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹I)` is an
isomorphism and `p⁻¹I` is acyclic for global sections, then the canonical map
`(Rf_*G)_s ⟶ RΓ(X ×_Y Spec 𝒪^{sh}_{Y,s}, p⁻¹G)` is an isomorphism for every abelian sheaf `G`. -/
theorem isIso_derivedPushforwardStalk_single_of_injective
    (hacyc : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      (Sheaf.Γ (smallEtaleTopology (strictHenselizationBaseChange B hY f s))
        Ab.{u + 1}).rightAcyclic
        ((smallEtalePullbackAb (strictHenselizationBaseChangeToSource B hY f s)).obj I))
    (hC : ∀ I : Sheaf (smallEtaleTopology X) Ab.{u + 1}, Injective I →
      IsIso ((pushforwardStalkToStrictHenselizationSectionsAb B hY f s).app I))
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    IsIso ((derivedPushforwardStalkToStrictHenselizationSections B hY f s).app
      ((DerivedCategory.singleFunctor _ 0).obj G)) := by
  exact isIso_derivedPushforwardStalk_of_isGE_of_injective B hY f s hacyc hC _ 0

end Assembly

end Stacks.EtaleCohomology.LimitExt
