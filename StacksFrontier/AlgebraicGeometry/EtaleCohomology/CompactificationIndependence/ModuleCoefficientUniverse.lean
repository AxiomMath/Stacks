module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.CoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleProperVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Proper direct images of sheaves of modules at every coefficient universe

Let `Λ` be a ring in an arbitrary universe `Type r`. This file carries consequences of proper base
change to sheaves of `Λ`-modules on small étale sites,
`Stacks.EtaleCohomology.EtaleModules.{u, r} Λ`, by forgetting the module structure to abelian
sheaves with coefficients in `AddCommGrpCat.{max (u + 1) r}`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleForgetUnivInverseImageIso`: inverse image commutes with
  forgetting the module structure.
* `Stacks.EtaleCohomology.etaleModuleForgetUnivRightDerivedDirectImageIso`: the underlying
  abelian sheaf of `R^q f_* G` is `R^q f_*` of the underlying abelian sheaf of `G`.

## Main results

* `Stacks.EtaleCohomology.isZero_etaleModuleInverseImage_directImage_of_isProper_univ` and
  `EtaleCohomology.isZero_etaleModuleInverseImage_rightDerived_directImage_of_isProper_univ`:
  for `g` proper and `c` arbitrary, `c⁻¹ g_* N = 0`, and `c⁻¹ R^p g_* N = 0` for `N` torsion,
  whenever `N` vanishes on everything lying over the image of `c`.
* `Stacks.EtaleCohomology.isZero_rightDerived_etaleModuleDirectImage_of_isProper_univ`:
  [Stacks, Tag 095U] for sheaves of `Λ`-modules.
* `Stacks.EtaleCohomology.isTorsionEtaleModule_etaleModuleExtensionByZero_obj_univ`: extension by
  zero of a torsion sheaf is torsion.
* `Stacks.EtaleCohomology.isIso_etaleModuleRefinementComparison_univ` and
  `Stacks.EtaleCohomology.isZero_rightDerived_etaleModuleDirectImage_extensionByZero_univ`: along
  a proper `g` with `j ≫ g = k`, the comparison `k_! ⟶ g_* j_!` is invertible and `j_! F` is
  acyclic for `g_*` when `F` is torsion.

## References

* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 095U](https://stacks.math.columbia.edu/tag/095U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u r

namespace Stacks.EtaleCohomology

/- `etaleModules_enoughInjectives_univZero` is stated for the coefficient ring in `Type`; instance
search would try to unify an arbitrary coefficient universe with it and fail on the universe
constraint, so it is switched off here. -/
attribute [-instance] etaleModules_enoughInjectives_univZero

variable (Λ : Type r) [Ring Λ]

/-- Sheaves of `Λ`-modules on a small étale site have enough injectives, stated at the
coefficient universe `max (u + 1) r`. -/
local instance etaleModules_enoughInjectives_moduleCoefficientUniverse (Z : Scheme.{u}) :
    EnoughInjectives (EtaleModules.{u, r} Λ Z) :=
  etaleModules_enoughInjectives.{u, r} Λ Z

/-! ### Forgetting the module structure -/

section Forget

/-- Postcomposition with the forgetful functor carries sheaves of modules to abelian sheaves. -/
local instance hasSheafCompose_forget₂_etaleModuleCoefficientUniverse (Z : Scheme.{u}) :
    Z.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{max (u + 1) r} Λ Z.smallEtaleTopology

/-- Sheafification commutes with forgetting the module structure. -/
local instance preservesSheafification_forget₂_etaleModuleCoefficientUniverse (Z : Scheme.{u}) :
    Z.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
  ModuleSheaf.preservesSheafification_forget₂.{max (u + 1) r} Λ Z.smallEtaleTopology

variable {X Y : Scheme.{u}} (t : Y ⟶ X)

/-- **Forgetting the module structure preserves the left Kan extensions defining inverse
image**, at every coefficient universe. -/
instance preservesLeftKanExtensions_forget₂_smallEtaleBaseChange_univ :
    (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}).PreservesLeftKanExtensions
      (smallEtaleBaseChange t).op := by
  intro P
  have hfil : ∀ V : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange t).op V) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange t) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) r, max (u + 1) r, u, u + 1} _
  infer_instance

/-- **Inverse image commutes with forgetting the module structure**: `t⁻¹(U M) ≅ U(t⁻¹ M)`,
for sheaves of `Λ`-modules with `Λ` in an arbitrary universe. -/
def etaleModuleForgetUnivInverseImageIso :
    etaleModuleForgetAb.{u, r} Λ X ⋙ etaleAbelianInverseImage.{u, r} t ≅
      etaleModuleInverseImage.{u, r} Λ t ⋙ etaleModuleForgetAb.{u, r} Λ Y :=
  Functor.isoWhiskerLeft _ (Functor.sheafPullbackConstruction.sheafPullbackIso
      (smallEtaleBaseChange t) AddCommGrpCat.{max (u + 1) r} X.smallEtaleTopology
      Y.smallEtaleTopology).symm ≪≫
    asIso (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange t) X.smallEtaleTopology
      Y.smallEtaleTopology
      (forget₂ (ModuleCat.{max (u + 1) r} Λ) AddCommGrpCat.{max (u + 1) r}))

variable {Λ} in
/-- A sheaf of modules whose underlying abelian sheaf is zero is zero. -/
lemma isZero_of_isZero_etaleModuleForgetUniv {Z : Scheme.{u}} {M : EtaleModules.{u, r} Λ Z}
    (h : IsZero ((etaleModuleForgetAb.{u, r} Λ Z).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact (etaleModuleForgetAb.{u, r} Λ Z).map_injective (by simpa using h.eq_of_src _ _)

attribute [local instance] HasDerivedCategory.standard in
/-- Forgetting the module structure commutes with placing a sheaf in degree zero, on bounded
below derived categories. -/
def etaleModuleForgetUnivPlusSingleIso (Z : Scheme.{u}) (G : EtaleModules.{u, r} Λ Z) :
    (etaleModuleForgetAb.{u, r} Λ Z).mapDerivedCategoryPlus.obj
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ Z) 0).obj G) ≅
      (DerivedCategory.Plus.singleFunctor
        (Sheaf Z.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}) 0).obj
        ((etaleModuleForgetAb.{u, r} Λ Z).obj G) :=
  DerivedCategory.Plus.ι.preimageIso
    (((etaleModuleForgetAb.{u, r} Λ Z).mapDerivedCategorySingleFunctor 0).app G)

attribute [local instance] HasDerivedCategory.standard in
/-- **The underlying abelian sheaf of `R^q f_* G` is `R^q f_*` of the underlying abelian sheaf
of `G`**, for a sheaf `G` of `Λ`-modules. -/
def etaleModuleForgetUnivRightDerivedDirectImageIso (f : X ⟶ Y) (G : EtaleModules.{u, r} Λ X)
    (q : ℕ) :
    (etaleModuleForgetAb.{u, r} Λ Y).obj
        (((etaleModuleDirectImage.{u, r} Λ f).rightDerived q).obj G) ≅
      ((etaleAbelianDirectImage.{u, r} f).rightDerived q).obj
        ((etaleModuleForgetAb.{u, r} Λ X).obj G) :=
  let U := etaleModuleForgetAb.{u, r} Λ Y
  let e : etaleModuleDirectImage.{u, r} Λ f ⋙ U ≅
      etaleModuleForgetAb.{u, r} Λ X ⋙ etaleAbelianDirectImage.{u, r} f :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)
  let D := Functor.rightDerivedRestrictionIso _ _ _ _ e
    (fun I _ => rightAcyclic_etaleAbelianDirectImage_etaleModuleForgetUniv_obj Λ f I)
  U.mapIso ((Stacks.DerivedIndexing.rightDerivedIso (etaleModuleDirectImage.{u, r} Λ f) q).app G) ≪≫
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso U (q : ℤ)).app
      (DerivedCategory.Plus.ι.obj _)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      (D.app ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, r} Λ X) 0).obj G)) ≪≫
    (DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).mapIso
      ((etaleAbelianDirectImage.{u, r} f).rightDerivedFunctorPlus.mapIso
        (etaleModuleForgetUnivPlusSingleIso Λ X G)) ≪≫
    ((Stacks.DerivedIndexing.rightDerivedIso (etaleAbelianDirectImage.{u, r} f) q).app
      ((etaleModuleForgetAb.{u, r} Λ X).obj G)).symm

end Forget

/-! ### Proper direct images over a locus the sheaf misses -/

section Closed

variable {A B W : Scheme.{u}} (g : A ⟶ B) [IsProper g] (c : W ⟶ B)
  (N : EtaleModules.{u, r} Λ A)
  (hN : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ A), Set.range t.base ⊆ g.base ⁻¹' Set.range c.base →
    IsZero ((etaleModuleInverseImage.{u, r} Λ t).obj N))

include hN

omit [IsProper g] in
/-- The underlying abelian sheaf of `N` vanishes on everything lying over the image of `c`. -/
lemma isZero_etaleAbelianInverseImage_forget_of_subset ⦃T : Scheme.{u}⦄ (t : T ⟶ A)
    (ht : Set.range t.base ⊆ g.base ⁻¹' Set.range c.base) :
    IsZero ((etaleAbelianInverseImage.{u, r} t).obj ((etaleModuleForgetAb.{u, r} Λ A).obj N)) :=
  ((etaleModuleForgetAb.{u, r} Λ T).map_isZero (hN t ht)).of_iso
    ((etaleModuleForgetUnivInverseImageIso Λ t).app N)

/-- **`c⁻¹ g_* N = 0`** for sheaves of `Λ`-modules, `g` proper, `c` arbitrary and `N` vanishing
on everything lying over the image of `c`. -/
theorem isZero_etaleModuleInverseImage_directImage_of_isProper_univ :
    IsZero ((etaleModuleInverseImage.{u, r} Λ c).obj
      ((etaleModuleDirectImage.{u, r} Λ g).obj N)) := by
  refine isZero_of_isZero_etaleModuleForgetUniv (IsZero.of_iso ?_
    ((etaleModuleForgetUnivInverseImageIso Λ c).app _).symm)
  exact isZero_etaleAbelianInverseImage_directImage_of_isProper_ulift.{r, u} g c _
    (isZero_etaleAbelianInverseImage_forget_of_subset Λ g c N hN)

/-- **`c⁻¹ R^p g_* N = 0` for every `p`** for sheaves of `Λ`-modules, `g` proper, `c` arbitrary
and `N` a torsion sheaf vanishing on everything lying over the image of `c`. -/
theorem isZero_etaleModuleInverseImage_rightDerived_directImage_of_isProper_univ
    (hT : IsTorsionEtaleModule.{u, r} Λ A N) (p : ℕ) :
    IsZero ((etaleModuleInverseImage.{u, r} Λ c).obj
      (((etaleModuleDirectImage.{u, r} Λ g).rightDerived p).obj N)) := by
  refine isZero_of_isZero_etaleModuleForgetUniv (IsZero.of_iso ?_
    ((etaleModuleForgetUnivInverseImageIso Λ c).app _).symm)
  refine IsZero.of_iso ?_ ((etaleAbelianInverseImage.{u, r} c).mapIso
    (etaleModuleForgetUnivRightDerivedDirectImageIso Λ g N p))
  exact isZero_etaleAbelianInverseImage_rightDerived_directImage_of_isProper_ulift.{r, u} g c _
    (isZero_etaleAbelianInverseImage_forget_of_subset Λ g c N hN) hT p

end Closed

/-! ### Stacks 095U for sheaves of modules -/

/-- **[Stacks, Tag 095U] for sheaves of `Λ`-modules**, `Λ` in an arbitrary universe. Let
`f : X ⟶ Y` be proper with all fibres of dimension `≤ n`, and let `G` be a torsion sheaf of
`Λ`-modules on `X_étale`. Then `R^q f_* G = 0` for `q > 2n`. -/
theorem isZero_rightDerived_etaleModuleDirectImage_of_isProper_univ {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] (n : ℕ) (hfib : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ n)
    (G : EtaleModules.{u, r} Λ X) (hG : IsTorsionEtaleModule.{u, r} Λ X G) (q : ℕ)
    (hq : 2 * n < q) :
    IsZero (((etaleModuleDirectImage.{u, r} Λ f).rightDerived q).obj G) :=
  isZero_of_isZero_etaleModuleForgetUniv
    ((isZero_rightDerived_etaleAbelianDirectImage_of_isProper_ulift.{r, u} f n hfib
      ((etaleModuleForgetAb.{u, r} Λ X).obj G) hG q hq).of_iso
      (etaleModuleForgetUnivRightDerivedDirectImageIso Λ f G q))

/-! ### Extension by zero of a torsion sheaf -/

/-- **Extension by zero of a torsion sheaf of modules is torsion**, for `Λ` in an arbitrary
universe. -/
theorem isTorsionEtaleModule_etaleModuleExtensionByZero_obj_univ {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (F : EtaleModules.{u, r} Λ U) (hF : IsTorsionEtaleModule.{u, r} Λ U F) :
    IsTorsionEtaleModule.{u, r} Λ X ((etaleModuleExtensionByZero.{u, r} Λ j).obj F) := by
  let G := Scheme.Etale.smallEtaleCompose j
  have hL : IsLocallyTorsionModulePresheaf X.smallEtaleTopology (G.op.leftKanExtension F.obj) :=
    isLocallyTorsionModulePresheaf_leftKanExtension X.smallEtaleTopology G
      (CoverPreserving.of_isContinuous _ _ _) F.obj hF
  have : X.smallEtaleTopology.WEqualsLocallyBijective (ModuleCat.{max (u + 1) r} Λ) :=
    wEqualsLocallyBijective_etaleModules.{u, r} Λ X
  exact IsLocallyTorsionModulePresheaf.of_isLocallySurjective _
    (X.smallEtaleTopology.W_toSheafify _).isLocallySurjective hL

/-! ### Along a refinement of compactifications -/

section Refinement

variable {X A B : Scheme.{u}} {j : X ⟶ A} {k : X ⟶ B} {g : A ⟶ B} [IsOpenImmersion j]
  [IsOpenImmersion k] (hjk : j ≫ g = k)

/-- The underlying abelian sheaf of `j_! F` vanishes away from `X`. -/
lemma isZero_etaleAbelianInverseImage_forget_extensionByZero_univ (F : EtaleModules.{u, r} Λ X)
    {T : Scheme.{u}} (t : T ⟶ A) (ht : Disjoint (Set.range t.base) (Set.range j.base)) :
    IsZero ((etaleAbelianInverseImage.{u, r} t).obj
      ((etaleModuleForgetAb.{u, r} Λ A).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F))) :=
  ((etaleModuleForgetAb.{u, r} Λ T).map_isZero
      (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ t j ht F)).of_iso
    ((etaleModuleForgetUnivInverseImageIso Λ t).app _)

include hjk in
/-- **`g_* j_! F` vanishes on the complement of `X`**, for `g` proper. -/
theorem isZero_etaleModuleInverseImage_directImage_extensionByZero_univ [IsProper g]
    (F : EtaleModules.{u, r} Λ X) :
    IsZero ((etaleModuleInverseImage.{u, r} Λ (openImmersionComplementι k)).obj
      ((etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F))) :=
  isZero_of_isZero_etaleModuleForgetUniv (IsZero.of_iso
    (isZero_etaleAbelianInverseImage_directImage_of_refinement_ulift.{r, u} hjk _
      (fun _ t ht => isZero_etaleAbelianInverseImage_forget_extensionByZero_univ Λ F t ht))
    ((etaleModuleForgetUnivInverseImageIso Λ _).app _).symm)

include hjk in
/-- **`R^q g_* (j_! F) = 0` for `q > 0`**, for `g` proper and `F` torsion. -/
theorem isZero_rightDerived_etaleModuleDirectImage_extensionByZero_univ [IsProper g]
    (F : EtaleModules.{u, r} Λ X) (hF : IsTorsionEtaleModule.{u, r} Λ X F) (p : ℕ) (hp : 0 < p) :
    IsZero (((etaleModuleDirectImage.{u, r} Λ g).rightDerived p).obj
      ((etaleModuleExtensionByZero.{u, r} Λ j).obj F)) :=
  isZero_of_isZero_etaleModuleForgetUniv
    ((isZero_rightDerived_etaleAbelianDirectImage_of_refinement_ulift hjk _
      (fun _ t ht => isZero_etaleAbelianInverseImage_forget_extensionByZero_univ Λ F t ht)
      (isTorsionEtaleModule_etaleModuleExtensionByZero_obj_univ Λ j F hF) p hp).of_iso
      (etaleModuleForgetUnivRightDerivedDirectImageIso Λ g _ p))

include hjk in
/-- **`θ_g : k_! ⟶ g_* j_!` is an isomorphism** for `g` proper, `Λ` in an arbitrary universe. -/
@[sga "4 XVII 3.3.2.1" "(iii)"]
theorem isIso_etaleModuleRefinementComparison_univ [IsProper g] :
    IsIso (etaleModuleRefinementComparison.{u, r} Λ hjk) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun F => ?_
  let G := (etaleModuleDirectImage.{u, r} Λ g).obj ((etaleModuleExtensionByZero.{u, r} Λ j).obj F)
  have e : (etaleModuleRefinementComparison Λ hjk).app F =
      (etaleModuleExtensionByZero.{u, r} Λ k).map ((refinementComparisonAdj Λ hjk).app F) ≫
        (etaleModuleExtensionByZeroAdj.{u, r} Λ k).counit.app G :=
    Adjunction.homEquiv_counit _ _ _ _
  have h₁ : IsIso ((refinementTarget Λ hjk).app F) := by
    simp only [refinementTarget, NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp]
    infer_instance
  have h₂ : IsIso ((refinementComparisonAdj Λ hjk).app F) := by
    have := isIso_refinementRestrictedInclusion Λ hjk
    simp only [refinementComparisonAdj, NatTrans.comp_app]
    infer_instance
  have hik : Set.range k.base = (Set.range (openImmersionComplementι k).base)ᶜ := by
    rw [range_openImmersionComplementι, compl_compl]
  obtain ⟨_, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ
    (openImmersionComplementι k) k hik G
  have h₃ : IsIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ k).counit.app G) :=
    hS.isIso_f_iff.2 ((etaleModuleDirectImage.{u, r} Λ (openImmersionComplementι k)).map_isZero
      (isZero_etaleModuleInverseImage_directImage_extensionByZero_univ Λ hjk F))
  rw [e]
  infer_instance

end Refinement

end Stacks.EtaleCohomology

end
