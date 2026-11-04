module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryTransportComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionSliceCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedHomGluing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackEtaleComp

/-!
# Gluing morphisms of `D(𝒪_X)` along étale charts, in terms of derived pullbacks

The gluing of morphisms of the derived category of an algebraic space along étale charts,
`AlgebraicGeometry.Space.existsUnique_restrictQMap_chartModules_eq`, restated through the derived
pullbacks `Lφ_A^*` along the charts and the composition isomorphisms of Stacks 0D6D.

## Main results

* `AlgebraicGeometry.Space.chartRestrictModulesIso_hom_eq`: restriction along a morphism of
  charts is the strict composition of étale restrictions followed by the transport along
  `chartMap c ≫ chartToSpace A = chartToSpace C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}

/-- The comparison `chartRestrictModulesIso c`, read after the strict composition of étale
restrictions, is the transport along `chartMap c ≫ chartToSpace A = chartToSpace C`. -/
theorem etaleModulePullbackComp_inv_comp_chartRestrictModulesIso_hom {C A : SmallEtale B S hS X.1}
    (c : C ⟶ A) :
    (etaleModulePullbackComp B S hS (chartMap B S hS X c) (chartToSpace B S hS X A)
          (isEtale_chartMap B S hS X c) (isEtale_chartToSpace B S hS X A)
          (isEtale_chartMap_comp_chartToSpace B S hS X c)).inv ≫
        (chartRestrictModulesIso B S hS c).hom =
      eqToHom (etaleModulePullback_congr B S hS _ _ (chartMap_comp_chartToSpace B S hS X c)) := by
  have hκ : ∀ W : SmallEtale B S hS (chartSpace B S hS X C).1,
      (chartPostcompIso B S hS c).inv.app W = eqToHom (Functor.congr_obj
        (smallEtalePostcomp_congr B S hS (isEtale_chartToSpace B S hS X C)
          (isEtale_chartMap_comp_chartToSpace B S hS X c)
          (chartMap_comp_chartToSpace B S hS X c).symm) W) := by
    intro W
    refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
    have key : ∀ {P Q : SmallEtale B S hS X.1} (h : P = Q),
        (eqToHom h).hom.left =
          eqToHom (congrArg (fun P : SmallEtale B S hS X.1 => P.obj.left) h) := by
      intro P Q h
      subst h
      rfl
    rw [key]
    exact (eqToHom_refl _ _).symm
  ext M W x
  have h0 := Stacks.SheafOfModules.ChartSliceTransport.restrictIso_hom_app_val_app
    (JA := SmallEtale.topology B S hS (chartSpace B S hS X A).1)
    (JC := SmallEtale.topology B S hS (chartSpace B S hS X C).1)
    (KX := SmallEtale.topology B S hS X.1)
    (hpA := smallEtalePostcomp_isContinuous B S hS _ _)
    (hpC := smallEtalePostcomp_isContinuous B S hS _ _)
    (hpc := smallEtalePostcomp_isContinuous B S hS _ _)
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
    (smallEtalePostcomp B S hS (chartToSpace B S hS X A) (isEtale_chartToSpace B S hS X A))
    (smallEtalePostcomp B S hS (chartToSpace B S hS X C) (isEtale_chartToSpace B S hS X C))
    (smallEtalePostcomp B S hS (chartMap B S hS X c) (isEtale_chartMap B S hS X c))
    (chartPostcompIso B S hS c) M W.unop x
  refine h0.trans ?_
  refine (Stacks.CategoryTheory.proj_congr (hκ W.unop)
    (fun g => ModuleCat.Hom.hom (M.val.map g.op) x)).trans ?_
  exact (eqToHom_etaleModulePullback_app_val_app B S hS
    (isEtale_chartMap_comp_chartToSpace B S hS X c) (isEtale_chartToSpace B S hS X C)
    (chartMap_comp_chartToSpace B S hS X c) M W.unop x).symm

/-- **Restriction along a morphism of charts is iterated étale restriction**: the comparison
`chartRestrictModulesIso c` is the strict composition of étale restrictions followed by the
transport along `chartMap c ≫ chartToSpace A = chartToSpace C`. -/
theorem chartRestrictModulesIso_hom_eq {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    (chartRestrictModulesIso B S hS c).hom =
      (etaleModulePullbackComp B S hS (chartMap B S hS X c) (chartToSpace B S hS X A)
          (isEtale_chartMap B S hS X c) (isEtale_chartToSpace B S hS X A)
          (isEtale_chartMap_comp_chartToSpace B S hS X c)).hom ≫
        eqToHom (etaleModulePullback_congr B S hS _ _ (chartMap_comp_chartToSpace B S hS X c)) :=
  (Iso.hom_inv_id_assoc _ _).symm.trans (congrArg (fun t => (etaleModulePullbackComp B S hS
    (chartMap B S hS X c) (chartToSpace B S hS X A) (isEtale_chartMap B S hS X c)
    (isEtale_chartToSpace B S hS X A) (isEtale_chartMap_comp_chartToSpace B S hS X c)).hom ≫ t)
    (etaleModulePullbackComp_inv_comp_chartRestrictModulesIso_hom B S hS c))

section Congr

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective
  isGrothendieckAbelian_ringedToposStructureRingSheaf

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

variable {Y Z : AlgebraicSpaces B S hS}

/-- The transport of derived pullbacks along an equality of étale morphisms, read through
`La^* ≅ D(a^*)`, is the transport of the induced functors. -/
theorem smallEtaleDerivedModulePullbackCongr_hom_app_comp_isoEtale {p q : Y ⟶ Z} (e : p = q)
    (hp : IsEtale B S hS p.hom) (hq : IsEtale B S hS q.hom)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    (smallEtaleDerivedModulePullbackCongr B S hS e).hom.app K ≫
        (smallEtaleDerivedModulePullbackIsoEtale B S hS q hq).hom.app K =
      (smallEtaleDerivedModulePullbackIsoEtale B S hS p hp).hom.app K ≫
        eqToHom (by subst e; rfl) := by
  subst e
  simp [smallEtaleDerivedModulePullbackCongr]

/-- Derived pullback along a morphism of charts `c : C ⟶ A`, after derived pullback to `A`, is
derived pullback to `C`: Stacks 0D6D followed by `chartMap c ≫ chartToSpace A = chartToSpace C`. -/
def chartDerivedPullbackIso {C A : SmallEtale B S hS X.1} (c : C ⟶ A) :
    smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A) ⋙
        smallEtaleDerivedModulePullback B S hS (chartMap B S hS X c) ≅
      smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X C) :=
  smallEtaleDerivedModulePullbackCompIso B S hS (chartMap B S hS X c) (chartToSpace B S hS X A) ≪≫
    smallEtaleDerivedModulePullbackCongr B S hS (chartMap_comp_chartToSpace B S hS X c)

/-- **Transport along a morphism of charts is derived pullback.** For a morphism of charts
`c : C ⟶ A`, the transport along `chartRestrictModulesIso c` of a morphism
`Lφ_A^*(Q P) ⟶ Lφ_A^*(Q I)`, read through `Lφ_A^* ≅ D(φ_A^*)`, is its derived pullback along
`chartMap c`, read through `chartDerivedPullbackIso c`. -/
theorem transportQMap_chartRestrictModulesIso_derivedQIso {C A : SmallEtale B S hS X.1}
    (c : C ⟶ A)
    {P I : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ}
    (β : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).obj
        (DerivedCategory.Q.obj P) ⟶
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X A)).obj
        (DerivedCategory.Q.obj I)) :
    Stacks.DerivedCategoryComparisons.transportQMap (chartRestrictModulesIso B S hS c)
        ((Stacks.DerivedCategoryComparisons.derivedQIso (chartModules B S hS X A)
            (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartToSpace B S hS X A))
            P).inv ≫ β ≫
          (Stacks.DerivedCategoryComparisons.derivedQIso (chartModules B S hS X A)
            (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartToSpace B S hS X A))
            I).hom) =
      (Stacks.DerivedCategoryComparisons.derivedQIso (chartModules B S hS X C)
          (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartToSpace B S hS X C))
          P).inv ≫
        ((chartDerivedPullbackIso B S hS c).inv.app _ ≫
          (smallEtaleDerivedModulePullback B S hS (chartMap B S hS X c)).map β ≫
            (chartDerivedPullbackIso B S hS c).hom.app _) ≫
          (Stacks.DerivedCategoryComparisons.derivedQIso (chartModules B S hS X C)
            (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartToSpace B S hS X C))
            I).hom :=
  Stacks.DerivedCategoryComparisons.transportQMap_eq_comp_derived
    (C₁ := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    (C₂ := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X A)))
    (C₃ := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS (chartSpace B S hS X C)))
    (F := chartModules B S hS X A) (G' := chartModules B S hS X C)
    (T := chartRestrictModules B S hS c)
    (hGadd := etaleModulePullback_additive B S hS _ (isEtale_chartMap_comp_chartToSpace B S hS X c))
    (hGpfl := preservesFiniteLimits_etaleModulePullback B S hS _
      (isEtale_chartMap_comp_chartToSpace B S hS X c))
    (hGpfc := preservesFiniteColimits_etaleModulePullback B S hS _
      (isEtale_chartMap_comp_chartToSpace B S hS X c))
    (etaleModulePullbackComp B S hS (chartMap B S hS X c) (chartToSpace B S hS X A)
      (isEtale_chartMap B S hS X c) (isEtale_chartToSpace B S hS X A)
      (isEtale_chartMap_comp_chartToSpace B S hS X c))
    (etaleModulePullback_congr B S hS _ _ (chartMap_comp_chartToSpace B S hS X c))
    (chartRestrictModulesIso B S hS c) (chartRestrictModulesIso_hom_eq B S hS c)
    (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartToSpace B S hS X A) :
      _ ≅ (chartModules B S hS X A).mapDerivedCategory)
    (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartMap B S hS X c) :
      _ ≅ (chartRestrictModules B S hS c).mapDerivedCategory)
    (smallEtaleDerivedModulePullbackIsoEtale B S hS _
      (isEtale_chartMap_comp_chartToSpace B S hS X c))
    (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartToSpace B S hS X C) :
      _ ≅ (chartModules B S hS X C).mapDerivedCategory)
    (smallEtaleDerivedModulePullbackCompIso B S hS (chartMap B S hS X c) (chartToSpace B S hS X A))
    (smallEtaleDerivedModulePullbackCongr B S hS (chartMap_comp_chartToSpace B S hS X c))
    (smallEtaleDerivedModulePullbackCongr_hom_app_comp_isoEtale B S hS
      (chartMap_comp_chartToSpace B S hS X c) _ _)
    (smallEtaleDerivedModulePullbackCompIso_hom_comp_isoEtale (chartMap B S hS X c)
      (chartToSpace B S hS X A) (isEtale_chartMap B S hS X c) (isEtale_chartToSpace B S hS X A)
      (isEtale_chartMap_comp_chartToSpace B S hS X c) (relativelyRepresentable_chartMap B S hS X c)
      (relativelyRepresentable_chartToSpace B S hS X A)
      (relativelyRepresentable_chartMap_comp_chartToSpace B S hS X c))
    (chartDerivedPullbackIso B S hS c) rfl β

/-- **Gluing morphisms of `D(𝒪_X)` along étale charts, through derived pullbacks.** Let `K`, `L`
be objects of `D(𝒪_X)` with `R𝓗om(K, L)` in `D^{≥ 0}`, and let `A i` be étale charts covering
`X`. A family of morphisms `β i : Lφ_{A i}^*K ⟶ Lφ_{A i}^*L` whose derived pullbacks along any
two morphisms of charts `C ⟶ A i`, `C ⟶ A j` agree (read through `Lc^* Lφ_A^* ≅ Lφ_C^*`) is the
family of derived pullbacks of a unique morphism `K ⟶ L`. -/
theorem existsUnique_smallEtaleDerivedModulePullback_map_eq
    {K L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))}
    (hKL : (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj L).IsGE 0)
    {ι : Type*} {A : ι → SmallEtale B S hS X.1} (hA : (SmallEtale.topology B S hS X.1).CoversTop A)
    (β : ∀ i, (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).obj L)
    (hβ : ∀ (C : SmallEtale B S hS X.1) (i j : ι) (c : C ⟶ A i) (c' : C ⟶ A j),
      (chartDerivedPullbackIso B S hS c).inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS (chartMap B S hS X c)).map (β i) ≫
            (chartDerivedPullbackIso B S hS c).hom.app L =
        (chartDerivedPullbackIso B S hS c').inv.app K ≫
          (smallEtaleDerivedModulePullback B S hS (chartMap B S hS X c')).map (β j) ≫
            (chartDerivedPullbackIso B S hS c').hom.app L) :
    ∃! d : K ⟶ L, ∀ i,
      (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).map d = β i := by
  obtain ⟨P, ⟨eP⟩⟩ : ∃ P, Nonempty (DerivedCategory.Q.obj P ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  obtain ⟨I, ⟨eI⟩⟩ : ∃ I, Nonempty (DerivedCategory.Q.obj I ≅ L) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso L⟩⟩
  have hPI : (((smallEtaleDerivedSheafHom B S hS X).obj (op (DerivedCategory.Q.obj P))).obj
      (DerivedCategory.Q.obj I)).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (X := ((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj L)
      (((smallEtaleDerivedSheafHom B S hS X).mapIso eP.symm.op).app (DerivedCategory.Q.obj I) ≪≫
        ((smallEtaleDerivedSheafHom B S hS X).obj (op K)).mapIso eI).symm 0
  have key : ∀ (i : ι) (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj I)
      (b : (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).obj
          (DerivedCategory.Q.obj P) ⟶
        (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).obj
          (DerivedCategory.Q.obj I)),
      Stacks.DerivedCategoryComparisons.restrictQMap (chartModules B S hS X (A i)) d =
          (Stacks.DerivedCategoryComparisons.derivedQIso (chartModules B S hS X (A i))
            (smallEtaleDerivedModulePullbackIsoEtale B S hS _
              (isEtale_chartToSpace B S hS X (A i))) P).inv ≫ b ≫
            (Stacks.DerivedCategoryComparisons.derivedQIso (chartModules B S hS X (A i))
              (smallEtaleDerivedModulePullbackIsoEtale B S hS _
                (isEtale_chartToSpace B S hS X (A i))) I).hom ↔
        (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).map d = b := by
    intro i d b
    rw [Stacks.DerivedCategoryComparisons.restrictQMap_eq_derivedQIso (chartModules B S hS X (A i))
      (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartToSpace B S hS X (A i))),
      cancel_epi, cancel_mono]
  obtain ⟨d', hd', huniq⟩ := existsUnique_restrictQMap_chartModules_eq B S hS hPI hA
    (fun i => (Stacks.DerivedCategoryComparisons.derivedQIso (chartModules B S hS X (A i))
        (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartToSpace B S hS X (A i)))
        P).inv ≫
      ((smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).map eP.hom ≫ β i ≫
        (smallEtaleDerivedModulePullback B S hS (chartToSpace B S hS X (A i))).map eI.inv) ≫
      (Stacks.DerivedCategoryComparisons.derivedQIso (chartModules B S hS X (A i))
        (smallEtaleDerivedModulePullbackIsoEtale B S hS _ (isEtale_chartToSpace B S hS X (A i)))
        I).hom)
    (fun C i j c c' => by
      rw [transportQMap_chartRestrictModulesIso_derivedQIso B S hS c,
        transportQMap_chartRestrictModulesIso_derivedQIso B S hS c',
        Stacks.DerivedCategoryComparisons.inv_app_comp_map_comp_hom_app,
        Stacks.DerivedCategoryComparisons.inv_app_comp_map_comp_hom_app, hβ C i j c c'])
  refine ⟨eP.inv ≫ d' ≫ eI.hom, fun i => ?_, fun d₂ hd₂ => ?_⟩
  · have h := (key i d' _).1 (hd' i)
    simp [h]
  · have h := huniq (eP.hom ≫ d₂ ≫ eI.inv) (fun i => (key i _ _).2 (by simp [hd₂ i]))
    rw [← h]
    simp

end Congr

end AlgebraicGeometry.Space

end
