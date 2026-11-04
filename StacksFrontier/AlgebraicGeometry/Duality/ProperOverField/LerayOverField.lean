module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationOfSubsingleton
public import StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsPushforward

/-!
# Derived global sections over the spectrum of a field

Let `k` be a field. The underlying space of `Spec k` is a point, so taking global sections of a
sheaf of `𝒪_{Spec k}`-modules is an exact functor, and `k`-linear derived global sections
`RΓ(Spec k, -) : D(𝒪_{Spec k}) ⥤ D(k)` is computed by global sections on every complex.
Consequently, for every scheme `X` over `k`, with structure morphism `f : X ⟶ Spec k`, the
`k`-linear derived global sections of `X` factor through derived direct image:
`RΓ(X, -) ≅ RΓ(Spec k, -) ∘ Rf_*`. This is the case of [Stacks, Tag 0D5W] over the spectrum
of a field, at the level of `k`-linear derived global sections.

## Main results

* `AlgebraicGeometry.isIso_derivedGlobalSectionsOverUnit_app_specField` — the unit of
  `RΓ(Spec k, -)` is invertible at every complex.
* `AlgebraicGeometry.derivedGlobalSectionsOverLerayIso` — the natural isomorphism
  `RΓ(X, -) ≅ Rf_* ⋙ RΓ(Spec k, -)`, and `AlgebraicGeometry.derivedGlobalSectionsOverLerayIso_fac`
  its compatibility with the units.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u


namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-- Global sections on `Spec k` preserve epimorphisms: the underlying space is a point. -/
instance globalSectionsOver_specField_preservesEpimorphisms :
    (globalSectionsOver (𝟙 (Spec (.of k)))).PreservesEpimorphisms := by
  have : (SheafOfModules.evaluation (Spec (.of k)).ringCatSheaf
      (op (⊤ : (Spec (.of k)).Opens))).PreservesEpimorphisms :=
    @Stacks.SheafOfModules.preservesEpimorphisms_evaluation_of_subsingleton _
      (Spec (.of k)).ringCatSheaf ⊤ ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      ⟨⟨default, trivial⟩⟩
  refine ⟨fun {M N} φ hφ => ?_⟩
  rw [ModuleCat.epi_iff_surjective]
  exact (ModuleCat.epi_iff_surjective
    ((SheafOfModules.evaluation (Spec (.of k)).ringCatSheaf (op ⊤)).map φ)).1
      (@Functor.PreservesEpimorphisms.preserves _ _ _ _ _ this M N φ hφ)

/-- Global sections on `Spec k` are exact. -/
instance globalSectionsOver_specField_preservesHomology :
    (globalSectionsOver (𝟙 (Spec (.of k)))).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels _

/-- Global sections on `Spec k` preserve finite colimits. -/
instance globalSectionsOver_specField_preservesFiniteColimits :
    PreservesFiniteColimits (globalSectionsOver (𝟙 (Spec (.of k)))) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

/-- **The unit of `RΓ(Spec k, -)` is invertible at every complex.** It is invertible at a
K-injective complex, every complex is quasi-isomorphic to one, and global sections on `Spec k`,
being exact, preserve quasi-isomorphisms. -/
theorem isIso_derivedGlobalSectionsOverUnit_app_specField
    (M : HomotopyCategory (Spec (.of k)).Modules (ComplexShape.up ℤ)) :
    IsIso ((derivedGlobalSectionsOverUnit (𝟙 (Spec (.of k)))).app M) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  obtain ⟨I, s, hI, hs⟩ := Scheme.Modules.exists_quasiIso_isKInjective (Spec (.of k)) K
  have hunitI := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    (homotopyGlobalSectionsOver (𝟙 (Spec (.of k))))
    (derivedGlobalSectionsOver (𝟙 (Spec (.of k))))
    (derivedGlobalSectionsOverUnit (𝟙 (Spec (.of k)))) I
  have hnat := (derivedGlobalSectionsOverUnit (𝟙 (Spec (.of k)))).naturality
    ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)
  have hQs : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff s).2 hs)
  have hΓs : IsIso ((homotopyGlobalSectionsOver (𝟙 (Spec (.of k)))).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ _) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
        ((HomologicalComplex.mem_quasiIso_iff _).2
          (HomologicalComplex.quasiIso_map_of_preservesHomology s
            (globalSectionsOver (𝟙 (Spec (.of k)))))))
  have hGs : IsIso ((DerivedCategory.Qh ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of k)))).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) :=
    Functor.map_isIso (derivedGlobalSectionsOver (𝟙 (Spec (.of k)))) _
  have h : IsIso ((derivedGlobalSectionsOverUnit (𝟙 (Spec (.of k)))).app
      ((HomotopyCategory.quotient _ _).obj K) ≫
        (DerivedCategory.Qh ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of k)))).map
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s)) := by
    rw [← hnat]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.Qh ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of k)))).map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))

/-- The functor induced by the exact functor of global sections on `Spec k` is a right derived
functor of global sections, its comparison map being invertible. -/
instance isRightDerivedFunctor_mapDerivedCategory_globalSectionsOver_specField :
    (globalSectionsOver (𝟙 (Spec (.of k)))).mapDerivedCategory.IsRightDerivedFunctor
      (globalSectionsOver (𝟙 (Spec (.of k)))).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (Spec (.of k)).Modules (ComplexShape.up ℤ)) :=
  Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun _ _ => inferInstance)

/-- **Derived global sections on `Spec k` are global sections.** -/
def derivedGlobalSectionsOverSpecFieldIso :
    derivedGlobalSectionsOver (𝟙 (Spec (.of k))) ≅
      (globalSectionsOver (𝟙 (Spec (.of k)))).mapDerivedCategory :=
  Functor.rightDerivedNatIso _ _ (derivedGlobalSectionsOverUnit (𝟙 (Spec (.of k))))
    (globalSectionsOver (𝟙 (Spec (.of k)))).mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso (Spec (.of k)).Modules (ComplexShape.up ℤ)) (Iso.refl _)

/-- Derived global sections on `Spec k` of a module placed in degree zero is its module of global
sections placed in degree zero. -/
def derivedGlobalSectionsOverSpecFieldSingleIso (M : (Spec (.of k)).Modules) :
    (derivedGlobalSectionsOver (𝟙 (Spec (.of k)))).obj
        ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj M) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
        ((globalSectionsOver (𝟙 (Spec (.of k)))).obj M) :=
  (derivedGlobalSectionsOverSpecFieldIso k).app _ ≪≫
    ((globalSectionsOver (𝟙 (Spec (.of k)))).mapDerivedCategorySingleFunctor 0).app M

/-- The global sections of the structure sheaf of `Spec k`, as a `k`-vector space, are `k`. -/
def globalSectionsOverSpecFieldUnitEquiv :
    ((globalSectionsOver (𝟙 (Spec (.of k)))).obj
      (SheafOfModules.unit (Spec (.of k)).ringCatSheaf) : Type u) ≃ₗ[k] k where
  toFun x := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv x
  invFun c := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm c
  map_add' x y := map_add (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv x y
  map_smul' c x := by
    change (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv
        (((Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Hom.appTop (𝟙 (Spec (.of k)))) c *
          (show Γ(Spec (.of k), ⊤) from x)) =
      c * (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv x
    rw [Scheme.Hom.id_appTop, Category.comp_id, map_mul]
    congr 1
    exact (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.apply_symm_apply c
  left_inv x := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.symm_apply_apply x
  right_inv c := (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.apply_symm_apply c

variable {k} {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The comparison `Γ(X, -) ⟶ Qh ⋙ Rf_* ⋙ RΓ(Spec k, -)` assembled from the units of
`RΓ(Spec k, -)` and of `Rf_*`. -/
def derivedGlobalSectionsOverLerayUnit :
    homotopyGlobalSectionsOver f ⟶ DerivedCategory.Qh ⋙
      (Stacks.Duality.derivedPushforward f ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of k)))) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (pushforwardGlobalSectionsOverIso f)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      (derivedGlobalSectionsOverUnit (𝟙 (Spec (.of k)))) ≫
    Functor.whiskerRight (derivedPushforwardUnit f) (derivedGlobalSectionsOver (𝟙 (Spec (.of k))))

/-- `Rf_* ⋙ RΓ(Spec k, -)` is a right derived functor of `k`-linear global sections on `X`. -/
instance isRightDerivedFunctor_derivedPushforward_comp_derivedGlobalSectionsOver :
    (Stacks.Duality.derivedPushforward f ⋙
        derivedGlobalSectionsOver (𝟙 (Spec (.of k)))).IsRightDerivedFunctor
      (derivedGlobalSectionsOverLerayUnit f)
      (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ (fun I hI => ?_)
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    (Stacks.Duality.homotopyPushforward f) (Stacks.Duality.derivedPushforward f)
    (derivedPushforwardUnit f) I
  have := isIso_derivedGlobalSectionsOverUnit_app_specField k
    (((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj I))
  dsimp only [derivedGlobalSectionsOverLerayUnit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app]
  infer_instance

/-- **Leray over the spectrum of a field.** For a scheme `f : X ⟶ Spec k` over a field, `k`-linear
derived global sections on `X` are derived global sections on `Spec k` of the derived direct image:
`RΓ(X, -) ≅ RΓ(Spec k, -) ∘ Rf_*`. -/
def derivedGlobalSectionsOverLerayIso :
    derivedGlobalSectionsOver f ≅
      Stacks.Duality.derivedPushforward f ⋙ derivedGlobalSectionsOver (𝟙 (Spec (.of k))) :=
  Functor.rightDerivedNatIso _ _ (derivedGlobalSectionsOverUnit f)
    (derivedGlobalSectionsOverLerayUnit f)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) (Iso.refl _)

/-- The Leray isomorphism is compatible with the two units. -/
@[reassoc]
theorem derivedGlobalSectionsOverLerayIso_fac
    (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (derivedGlobalSectionsOverUnit f).app K ≫
        (derivedGlobalSectionsOverLerayIso f).hom.app (DerivedCategory.Qh.obj K) =
      (derivedGlobalSectionsOverLerayUnit f).app K := by
  simp [derivedGlobalSectionsOverLerayIso]

end AlgebraicGeometry
