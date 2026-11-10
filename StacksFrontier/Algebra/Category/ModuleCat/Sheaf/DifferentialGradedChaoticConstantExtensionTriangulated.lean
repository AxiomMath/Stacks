module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticConstantDerivedAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedForgetHomotopyTriangulated
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConstantLinear
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import Mathlib.CategoryTheory.Shift.Localization
public import Mathlib.CategoryTheory.Localization.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-!
# The derived extension of scalars from a constant ring is an exact `R`-linear functor

Let `C` be a small category with the chaotic topology, `R` a commutative ring and `B` a sheaf of
differential graded algebras over the constant sheaf of rings with value `R`. Extension of
scalars `K ↦ K ⊗_R B` on the homotopy categories, `K(R) ⥤ K(B, d)`, is left adjoint to the global
sections `K(B, d) ⥤ K(R)`. Both functors commute with the translations, are triangulated and are
`R`-linear, and the same holds for the functor `F' : D(R) ⥤ D(B, d)` induced on the derived
categories when extension of scalars inverts the quasi-isomorphisms.

## Main results

* `Stacks.ChaoticSite.homotopyGlobalSections_commShift`,
  `Stacks.ChaoticSite.homotopyGlobalSections_isTriangulated` and
  `Stacks.ChaoticSite.homotopyGlobalSections_linear`: the global sections on the homotopy
  categories commute with the translations, are triangulated and are `R`-linear.
* `Stacks.ChaoticSite.homotopyExtend'_commShift`,
  `Stacks.ChaoticSite.homotopyExtend'_isTriangulated` and
  `Stacks.ChaoticSite.homotopyExtend'_linear`: so is extension of scalars on the homotopy
  categories.
* `Stacks.ChaoticSite.derivedExtend_commShift`, `Stacks.ChaoticSite.derivedExtend_isTriangulated`
  and `Stacks.ChaoticSite.derivedExtend_linear`: **the derived extension of scalars
  `F' : D(R) ⥤ D(B, d)` commutes with the translations, is triangulated and is `R`-linear.**

## References

* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK)
* [Stacks Project, Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.PresheafOfModules

universe u

namespace Stacks.ChaoticSite

open _root_.SheafOfModules _root_.SheafOfModules.DifferentialGradedModule

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [SmallCategory C] {R : Type u} [CommRing R]
  (B : _root_.SheafOfModules.DifferentialGradedAlgebra.{u, u} (constRingSheaf (C := C) R))

/-! ### The global sections on the homotopy categories -/

/-- Forgetting the action, `K(B, d) ⥤ K(Mod(O))`, over the constant sheaf of rings. -/
def constHomotopyForget :
    _root_.SheafOfModules.DifferentialGradedModule.HomotopyCategory.{u, u, u} B ⥤
    _root_.HomotopyCategory (_root_.SheafOfModules.{u} (constRingSheaf (C := C) R))
      (ComplexShape.up ℤ) :=
  homotopyForgetComplex.{u, u, u} (X := constRingedSite C R) B

/-- Forgetting the action commutes with the translations. -/
@[instance_reducible]
instance constHomotopyForget_commShift : (constHomotopyForget B).CommShift ℤ :=
  homotopyForgetComplex_commShift.{u, u, u} (X := constRingedSite C R) B

/-- Forgetting the action is triangulated. -/
instance constHomotopyForget_isTriangulated : (constHomotopyForget B).IsTriangulated :=
  homotopyForgetComplex_isTriangulated.{u, u, u} (X := constRingedSite C R) B

/-- The global sections on the homotopy categories are forgetting the action followed by the
global sections of complexes of sheaves of modules. -/
def homotopyGlobalSectionsIso :
    constHomotopyForget B ⋙
        (globalSections R).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      homotopyGlobalSections R B :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    rintro ⟨M⟩ ⟨N⟩ f
    obtain ⟨g, rfl⟩ := (DifferentialGradedModule.HomotopyCategory.quotient B).map_surjective f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- **The global sections on the homotopy categories commute with the translations.** -/
@[instance_reducible]
instance homotopyGlobalSections_commShift : (homotopyGlobalSections R B).CommShift ℤ :=
  Functor.CommShift.ofIso (homotopyGlobalSectionsIso B) ℤ

/-- The identification `homotopyGlobalSectionsIso` commutes with the translations. -/
instance homotopyGlobalSectionsIso_commShift :
    NatTrans.CommShift (homotopyGlobalSectionsIso B).hom ℤ :=
  Functor.CommShift.ofIso_compatibility (homotopyGlobalSectionsIso B) ℤ

/-- **The global sections on the homotopy categories are triangulated.** -/
instance homotopyGlobalSections_isTriangulated : (homotopyGlobalSections R B).IsTriangulated :=
  Functor.isTriangulated_of_iso (homotopyGlobalSectionsIso B)

/-! ### Extension of scalars on the homotopy categories -/

/-- **Extension of scalars on the homotopy categories commutes with the translations.** -/
@[instance_reducible]
instance homotopyExtend'_commShift : (homotopyExtend' B).CommShift ℤ :=
  (homotopyExtendAdjunction B).leftAdjointCommShift ℤ

/-- The adjunction `K(- ⊗_R B) ⊣ K(Γ)` is compatible with the translations. -/
instance homotopyExtendAdjunction_commShift : (homotopyExtendAdjunction B).CommShift ℤ :=
  (homotopyExtendAdjunction B).commShift_of_rightAdjoint ℤ

/-- **Extension of scalars on the homotopy categories is triangulated.** -/
instance homotopyExtend'_isTriangulated : (homotopyExtend' B).IsTriangulated :=
  (homotopyExtendAdjunction B).isTriangulated_leftAdjoint

/-! ### The derived extension of scalars -/

variable {B}

/-- The derived extension of scalars is the localization lift of extension of scalars on the
homotopy categories followed by the localization functor of `D(B, d)`. -/
instance derivedExtend_lifting (hB : ExtendInvertsQuasiIso B) :
    Localization.Lifting DerivedCategory.Qh
      (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (homotopyExtend' B ⋙ toDerivedCategory.{u, u, u} B) (derivedExtend hB) :=
  ⟨derivedExtendFac hB⟩

/-- **The derived extension of scalars commutes with the translations.** -/
@[instance_reducible]
instance derivedExtend_commShift (hB : ExtendInvertsQuasiIso B) :
    (derivedExtend hB).CommShift ℤ :=
  Functor.commShiftOfLocalization DerivedCategory.Qh
    (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ
    (homotopyExtend' B ⋙ toDerivedCategory.{u, u, u} B) (derivedExtend hB)

/-- The identification `derivedExtendFac` commutes with the translations. -/
instance derivedExtendFac_commShift (hB : ExtendInvertsQuasiIso B) :
    NatTrans.CommShift (derivedExtendFac hB).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization DerivedCategory.Qh
    (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ
    (homotopyExtend' B ⋙ toDerivedCategory.{u, u, u} B) (derivedExtend hB)

/-- **The derived extension of scalars is an exact functor of triangulated categories.** -/
instance derivedExtend_isTriangulated (hB : ExtendInvertsQuasiIso B) :
    (derivedExtend hB).IsTriangulated :=
  have := Localization.essSurj_mapArrow DerivedCategory.Qh
    (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
  Functor.isTriangulated_of_precomp_iso (derivedExtendFac hB)

/-! ### `R`-linearity -/

section Linear

variable (B)

/-- The limit of `r` times the identity of a presheaf of `R`-modules is `r` times the
identity. -/
theorem lim_map_smul_id (r : R) (F : Cᵒᵖ ⥤ ModuleCat.{u} R) :
    lim.map (r • 𝟙 F) = r • 𝟙 (lim.obj F) :=
  limit.hom_ext fun j => by simp [NatTrans.app_smul]

/-- The global sections of multiplication by `r ∈ R` on a sheaf of modules are multiplication by
`r`. -/
theorem globalSections_map_scalar (r : R)
    (M : _root_.SheafOfModules.{u} (constRingSheaf (C := C) R))
    (φ : M ⟶ M) (hφ : ∀ (U : Cᵒᵖ) (x : M.val.obj U), φ.val.app U x = r • x) :
    (globalSections R).map φ = r • 𝟙 _ := by
  have hs : (sectionsFunctor R).map φ = r • 𝟙 _ := by
    ext U x
    rw [NatTrans.app_smul]
    exact hφ U x
  change lim.map ((sectionsFunctor R).map φ) = r • 𝟙 (lim.obj ((sectionsFunctor R).obj M))
  rw [hs, lim_map_smul_id]

/-- The global sections of `r • f` are `r` times the global sections of `f`. -/
theorem dgGlobalSections_map_smul (r : R) {M N : DifferentialGradedModule.{u, u, u} B}
    (f : M ⟶ N) :
    (dgGlobalSections R B).map (r • f) = r • (dgGlobalSections R B).map f := by
  rw [smul_eq_scalarEnd_comp, Functor.map_comp]
  have h : (dgGlobalSections R B).map (scalarEnd r M) = r • 𝟙 _ := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    rw [HomologicalComplex.smul_f_apply, HomologicalComplex.id_f]
    exact globalSections_map_scalar r _ _ fun U x => scalarEnd_apply r M n U x
  rw [h, Linear.smul_comp, Category.id_comp]

/-- The global sections of right differential graded `B`-modules are `R`-linear. -/
instance dgGlobalSections_linear : (dgGlobalSections R B).Linear R :=
  ⟨fun f r => dgGlobalSections_map_smul B r f⟩

/-- **The global sections on the homotopy categories are `R`-linear.** -/
instance homotopyGlobalSections_linear : (homotopyGlobalSections R B).Linear R := by
  have : (DifferentialGradedModule.HomotopyCategory.quotient B ⋙
      homotopyGlobalSections R B).Linear R :=
    Functor.linear_of_iso _ (eqToIso (quotient_comp_homotopyGlobalSections R B)).symm
  have : (DifferentialGradedModule.HomotopyCategory.quotient B).EssSurj :=
    ⟨fun Z => ⟨Z.as, ⟨Iso.refl _⟩⟩⟩
  exact Functor.linear_of_full_essSurj_comp (DifferentialGradedModule.HomotopyCategory.quotient B)
    (homotopyGlobalSections R B)

/-- A left adjoint of an `R`-linear functor is `R`-linear. -/
theorem _root_.CategoryTheory.Adjunction.linear_leftAdjoint {R' : Type*} [Semiring R']
    {D₁ D₂ : Type*} [Category* D₁] [Category* D₂] [Preadditive D₁] [Preadditive D₂]
    [CategoryTheory.Linear R' D₁] [CategoryTheory.Linear R' D₂] {F : D₁ ⥤ D₂} {G : D₂ ⥤ D₁}
    (adj : F ⊣ G) [G.Linear R'] : F.Linear R' where
  map_smul {X Y} f r := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, adj.unit_naturality,
      Functor.map_smul (F := G), Linear.comp_smul, adj.unit_naturality, Linear.smul_comp]

/-- **Extension of scalars on the homotopy categories is `R`-linear.** -/
instance homotopyExtend'_linear : (homotopyExtend' B).Linear R :=
  (homotopyExtendAdjunction B).linear_leftAdjoint

variable {B}

/-- **The derived extension of scalars is `R`-linear.** -/
instance derivedExtend_linear (hB : ExtendInvertsQuasiIso B) : (derivedExtend hB).Linear R :=
  (Localization.functor_linear_iff DerivedCategory.Qh
    (_root_.HomotopyCategory.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) R
    (homotopyExtend' B ⋙ toDerivedCategory.{u, u, u} B) (derivedExtend hB)).1 inferInstance

end Linear

end Stacks.ChaoticSite

end
