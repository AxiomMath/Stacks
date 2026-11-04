module

public import StacksFrontier.AlgebraicGeometry.CechPushforwardComplex.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechDeRhamDoubleComplex
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeSlots
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamPairSupport

/-!
# The columns of the Čech–de Rham double complex

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, `A = Γ(S, 𝒪_S)`, `p`
nilpotent in `A` and `X` separated, affine opens `U_i` of `X` with smooth lifts `L_i` and objects
`D_i` of `Cris(X/S)`, and a quasi-coherent `𝒪_{X/S}`-module `N` on `CRIS(X/S)`.  Let
`B^a(⦋n⦌) = ∏_{x : Fin (n + 1) → ι} N(D_x) ⊗ Ω^a_{D_x}` be the Čech–de Rham double complex
(`CechEnvelope.cechDeRhamDoubleComplex`).  This file proves:

* **the columns `a > 0` are acyclic** ([Stacks, Tag 07LA]): the slot projections of
  `Ω_{D_x}` (`CechEnvelope.slotProjOfIsLimit`) induce support projections on the cosimplicial
  module `B^a(⦋•⦌)` (`CechEnvelope.isZero_homology_cechDeRhamDoubleComplex_X`); hence the total
  complex of `B` has the cohomology of its column zero (`CechEnvelope.cechHomologyIsoTotal`);
* **column zero is the Čech complex of `N`**: through `N(T) ⊗ Ω^0_T = N(T)` and the
  identification of the products `D_x` in the affine objects of `Cris(X/S)` with those in
  `CRIS(X/S)`, the Moore complex of `B^0`, lifted to the universe `u + 1`, is the Čech complex
  `Č(D, N)` of `CechEnvelopeComputesCohomology.lean` (`CechEnvelope.cechDeRhamColumnZeroIso`);
* hence **the Čech–de Rham double complex computes crystalline cohomology**:
  `H^j(Tot B) ≅ H^j(CRIS(X/S), N)` as `A`-modules (`CechEnvelope.cechDeRhamHomologyIso`).

## References

* [Stacks Project, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicTopology

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite Stacks.CechSite Stacks.CechSite.FinalCover DeRhamPair

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) [S.X.IsSeparated] {ι : Type}
  {U : ι → S.X.Opens} [∀ i, IsAffine (U i)] (L : ∀ i, SmoothLift S (U i).ι)

/-! ### The products of the smooth-lift objects in `AffineCris S` -/

/-- **The inclusion `AffineCris S ⥤ CRIS(X/S)` preserves the products of the smooth-lift
objects**: they are the envelope objects, which lie in `Cris(X/S)` and have affine ambient
scheme. -/
instance preservesLimit_affineCrisι_affineObject {n : ℕ} (x : Fin (n + 1) → ι) :
    PreservesLimit (Discrete.functor fun a ↦ affineObject hp L (x a)) (AffineCris.ι S) := by
  have h₁ : PreservesLimit (Discrete.functor fun a ↦ affineObject hp L (x a))
      (ObjectProperty.ι _) :=
    preservesLimit_fullSubcategoryι_of_isLimit _ (isLimitCrisFan hp L x)
      (inferInstanceAs (IsAffine (envelopeObject hp (fun a ↦ L (x a))).thickening.target.scheme))
  have h₂ : PreservesLimit (Discrete.functor fun a ↦ crisObject hp L (x a))
      (CrystallineThickening.ι S) :=
    preservesLimit_fullSubcategoryι_of_isLimit _ (isLimitFan hp (fun a ↦ L (x a)))
      (inferInstanceAs (IsOpenImmersion (envelopeObject hp (fun a ↦ L (x a))).toX))
  have h₃ : PreservesLimit (Discrete.functor (fun a ↦ affineObject hp L (x a)) ⋙
      ObjectProperty.ι _) (CrystallineThickening.ι S) :=
    preservesLimit_of_iso_diagram (K₁ := Discrete.functor fun a ↦ crisObject hp L (x a))
      (CrystallineThickening.ι S)
      (Discrete.compNatIsoDiscrete (fun a ↦ affineObject hp L (x a)) (ObjectProperty.ι _)).symm
  exact comp_preservesLimit _ _

/-- **The product `D_x` of the smooth-lift objects in `AffineCris S` is a product in
`CRIS(X/S)`.** -/
def isLimitInterFanAffine {n : ℕ} (x : Fin (n + 1) → ι) :
    IsLimit (Fan.mk (FinalCover.inter (affineObject hp L) x).obj.obj
      (fun a ↦ (FinalCover.interπ (affineObject hp L) x a).hom.hom) :
        Fan fun a ↦ (L (x a)).object hp) :=
  (isLimitMapConeFanMkEquiv (AffineCris.ι S) _ _).1
    (isLimitOfPreserves (AffineCris.ι S) (FinalCover.isLimitInterFan (affineObject hp L) x))

/-! ### The columns -/

variable {N : SheafOfModules.{u} (crystallineStructureSheaf S)} (hN : N.IsQuasicoherentOnSite)

/-- **The support projections of the column `a` of the Čech–de Rham double complex** on the
factor `N(D_x) ⊗ Ω^a_{D_x}`: `m ⊗ ω ↦ m ⊗ (⋀^a π_Z)(ω)`, where `π_Z = ∑_{k ∈ Z} π_k` is the sum of
the slot projections of `Ω_{D_x}` over the slots in `Z`. -/
def columnSupport (a : ℕ) (n : ℕ) (x : Fin (n + 1) → ι) (Z : Set (Fin (n + 1))) :
    (bigCrystalDeRhamPresheaf hN ⋙ HomologicalComplex.eval _ _ a).obj
        (op (FinalCover.inter (affineObject hp L) x)) ⟶
      (bigCrystalDeRhamPresheaf hN ⋙ HomologicalComplex.eval _ _ a).obj
        (op (FinalCover.inter (affineObject hp L) x)) :=
  formsEndoHom Γ(S.S.scheme, ⊤) (sectionsDPRing S (FinalCover.inter (affineObject hp L) x).obj.obj)
    (bigCrystalPairConnection hN (FinalCover.inter (affineObject hp L) x))
    (crystalPairConnection_isIntegrable _ _)
    (slotSum (slotProjOfIsLimit hp (fun a ↦ L (x a)) (isLimitInterFanAffine hp L x)) Z) a

/-- The support projection of all the slots is the identity. -/
theorem columnSupport_univ (a : ℕ) (n : ℕ) (x : Fin (n + 1) → ι) :
    columnSupport hp L hN a n x Set.univ = 𝟙 _ :=
  (congrArg (fun ε ↦ formsEndoHom Γ(S.S.scheme, ⊤)
      (sectionsDPRing S (FinalCover.inter (affineObject hp L) x).obj.obj)
      (bigCrystalPairConnection hN (FinalCover.inter (affineObject hp L) x))
      (crystalPairConnection_isIntegrable _ _) ε a)
    (isSlotFamily_slotProjOfIsLimit hp (fun a ↦ L (x a))
      (isLimitInterFanAffine hp L x)).slotSum_univ).trans
    (formsEndoHom_id _ _ _ _ a)

/-- The support projection of no slot vanishes in positive degree. -/
theorem columnSupport_empty {a : ℕ} (ha : 0 < a) (n : ℕ) (x : Fin (n + 1) → ι) :
    columnSupport hp L hN a n x ∅ = 0 := by
  rw [columnSupport, slotSum_empty]
  exact formsEndoHom_zero _ _ _ _ ha

/-- **The support projections are compatible with the reindexing maps**: restriction along
`D_y ⟶ D_{y ∘ h}` carries the projection on `h⁻¹ Z` to the projection on `Z`. -/
theorem map_columnSupport (a : ℕ) {m n : ℕ} (h : Fin (m + 1) →o Fin (n + 1))
    (y : Fin (n + 1) → ι) (Z : Set (Fin (n + 1))) :
    (bigCrystalDeRhamPresheaf hN ⋙ HomologicalComplex.eval _ _ a).map
        (FinalCover.interMap (affineObject hp L) y h).op ≫ columnSupport hp L hN a n y Z =
      columnSupport hp L hN a m (y ∘ h) (h ⁻¹' Z) ≫
        (bigCrystalDeRhamPresheaf hN ⋙ HomologicalComplex.eval _ _ a).map
          (FinalCover.interMap (affineObject hp L) y h).op := by
  have hε := fun ω ↦ (slotSum_oneFormsMap hp (fun a ↦ L (y a)) (isLimitInterFanAffine hp L y) h
    (isLimitInterFanAffine hp L (y ∘ h)) (FinalCover.interMap (affineObject hp L) y h).hom.hom
    (fun j ↦ congrArg (fun k ↦ k.hom.hom)
      (FinalCover.interMap_comp_interπ (affineObject hp L) y h j))
    Z ω).symm
  exact (deRhamMap_f_formsEndoHom
    (sectionsDPRingMap (FinalCover.interMap (affineObject hp L) y h).hom.hom)
    (isDPMorphism_sectionsDPRingMap _)
    (crystalPairRestrict (F := restrictSheafOfModules N)
      (FinalCover.interMap (affineObject hp L) y h))
    (bigCrystalPairConnection hN _) (crystalPairConnection_isIntegrable _ _)
    (bigCrystalPairConnection hN _) (crystalPairConnection_isIntegrable _ _)
    (crystalPairConnection_isHorizontal _ (FinalCover.interMap (affineObject hp L) y h))
    hε a).symm

/-- **The columns of the Čech–de Rham double complex are acyclic away from degree zero**
([Stacks, Tag 07LA]): for `a > 0` the Čech complex of the presheaf `T ↦ N(T) ⊗ Ω^a_T` along the
smooth-lift objects is acyclic, the support projections `columnSupport` making its cosimplicial
module one with support projections. -/
theorem isZero_homology_cechDeRhamDoubleComplex_X {a : ℕ} (ha : 0 < a) (j : ℕ) :
    IsZero (((alternatingCofaceMapComplex (ModuleCat.{u} Γ(S.S.scheme, ⊤))).obj
      ((cechDeRhamDoubleComplex hp L N hN).X a)).homology j) :=
  isZero_homology_of_supportProjections (affineObject hp L)
    (bigCrystalDeRhamPresheaf hN ⋙ HomologicalComplex.eval _ _ a) (columnSupport hp L hN a)
    (columnSupport_univ hp L hN a) (columnSupport_empty hp L hN ha)
    (map_columnSupport hp L hN a) j

/-- **The Čech–de Rham double complex has the cohomology of its column zero.** -/
def cechHomologyIsoTotal (j : ℕ) :
    (((Crystalline.CosimplicialDoubleComplex.functor (ModuleCat.{u} Γ(S.S.scheme, ⊤))).obj
        (cechDeRhamDoubleComplex hp L N hN)).total (ComplexShape.up ℤ)).homology (j : ℤ) ≅
      ((alternatingCofaceMapComplex _).obj ((cechDeRhamDoubleComplex hp L N hN).X 0)).homology j :=
  Crystalline.CosimplicialDoubleComplex.totalHomologyIsoColumnZero _
    (fun _ ha j ↦ isZero_homology_cechDeRhamDoubleComplex_X hp L hN ha j) j

/-! ### Column zero -/

section ColumnZero

/-- Lifting the module universe preserves products indexed by types in `Type`. -/
theorem preservesLimitsOfShape_uliftFunctor (R : Type u) [Ring R] (J : Type) :
    PreservesLimitsOfShape (Discrete J) (ModuleCat.uliftFunctor.{u + 1, u} R) :=
  have := preservesSmallestLimits_of_preservesLimits (ModuleCat.uliftFunctor.{u + 1, u} R)
  inferInstance

attribute [local instance] preservesLimitsOfShape_uliftFunctor

variable (N) in
/-- **The sections of `N` on the affine objects of `Cris(X/S)`, lifted to the universe `u + 1`,
are those of the universe lift of `N`**, as presheaves of `Γ(S, 𝒪_S)`-modules. -/
def sectionsULiftIso :
    crystalSectionsPresheaf (restrictSheafOfModules N) ⋙
        ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤) ≅
      (AffineCris.ι S).op ⋙
        (basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S) (bigBaseRingHom S)).obj
          ((bigModuleULift S).obj N) :=
  NatIso.ofComponents (fun T ↦ LinearEquiv.toModuleIso
    (X₁ := (crystalSectionsPresheaf (restrictSheafOfModules N) ⋙
        ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).obj T)
    (X₂ := ((AffineCris.ι S).op ⋙
        (basePresheaf.{0, u, u + 1, u, u} (crystallineStructureSheaf S) (bigBaseRingHom S)).obj
          ((bigModuleULift S).obj N)).obj T)
    (m₁ := ModuleCat.isModule _) (m₂ := ModuleCat.isModule _)
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        have e : algebraMap Γ(S.S.scheme, ⊤) (sectionsDPRing S T.unop.obj.obj) a =
            ((bigBaseRingHom S a).val (op T.unop.obj.obj) : sectionsDPRing S T.unop.obj.obj) :=
          congrArg (fun φ ↦ φ.hom a) (Scheme.Hom.appLE_eq_app T.unop.obj.obj.toBase.hom)
        exact congrArg ULift.up (congrArg (fun r : sectionsDPRing S T.unop.obj.obj ↦
          r • @id ((restrictSheafOfModules N).val.obj (op T.unop.obj)) x.down) e)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl })
    (fun k ↦ rfl)

/-- **The products `D_x` of the smooth-lift objects in `AffineCris S` and in `CRIS(X/S)` agree**:
the comparison map is an isomorphism. -/
theorem isIso_interComparison_affineCrisι {n : ℕ} (x : Fin (n + 1) → ι) :
    IsIso (interComparison (D := cechObjects hp L) (D' := affineObject hp L) (AffineCris.ι S)
      (fun i ↦ 𝟙 ((L i).object hp)) x) := by
  have : HasProduct fun a ↦ (AffineCris.ι S).obj (affineObject hp L (x a)) :=
    inferInstanceAs (HasProduct fun a ↦ cechObjects hp L (x a))
  have e : interComparison (D := cechObjects hp L) (D' := affineObject hp L) (AffineCris.ι S)
      (fun i ↦ 𝟙 ((L i).object hp)) x =
        piComparison (AffineCris.ι S) fun a ↦ affineObject hp L (x a) :=
    inter_hom_ext _ fun a ↦ (interComparison_comp_interπ _ _ x a).trans
      ((Category.comp_id _).trans
        (piComparison_comp_π (AffineCris.ι S) (fun a ↦ affineObject hp L (x a)) a).symm)
  rw [e]
  exact (PreservesProduct.iso (AffineCris.ι S) _).isIso_hom

/-- The comparison of the cosimplicial objects of a presheaf on `CRIS(X/S)` along the smooth-lift
objects, in `CRIS(X/S)` and in `AffineCris S`, is an isomorphism. -/
instance isIso_cosimplicialComparison_affineCrisι
    (P : (Thickening S)ᵒᵖ ⥤ ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) :
    IsIso ((cosimplicialComparison (D := cechObjects hp L) (D' := affineObject hp L) _
      (AffineCris.ι S) (fun i ↦ 𝟙 ((L i).object hp))).app P) :=
  isIso_cosimplicialComparison_app _ _ (fun _ x ↦ isIso_interComparison_affineCrisι hp L x) P

/-- **Column zero of the Čech–de Rham double complex is the Čech complex of `N`**: lifted to the
module universe `u + 1`, the Moore complex of `∏_x N(D_x) ⊗ Ω^0_{D_x}` is the Čech complex
`Č(D, N)` of the smooth-lift objects in `CRIS(X/S)`, through `N(T) ⊗ Ω^0_T = N(T)` and the
identification of the products `D_x` in `AffineCris S` and in `CRIS(X/S)`. -/
def cechDeRhamColumnZeroIso :
    ((ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).mapHomologicalComplex _).obj
        ((alternatingCofaceMapComplex _).obj ((cechDeRhamDoubleComplex hp L N hN).X 0)) ≅
      (cechFunctor (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)).obj
        ((bigModuleULift S).obj N) :=
  (Stacks.CechPushforward.alternatingCofaceMapComplexCompMapHomologicalComplexIso _).app _ ≪≫
    (alternatingCofaceMapComplex _).mapIso
      ((Stacks.CechPushforward.cosimplicialObjectFunctorCompWhiskeringIso.{0} _
          (simplicialObject (affineObject hp L))).app _ ≪≫
        (cosimplicialFunctor (affineObject hp L) _).mapIso
          (Functor.isoWhiskerRight
              (crystalDeRhamPresheafDegreeZeroIso (isQuasicoherentOnSite_restrictSheafOfModules hN))
              _ ≪≫
            sectionsULiftIso N) ≪≫
        (asIso ((cosimplicialComparison (D := cechObjects hp L) (D' := affineObject hp L) _
          (AffineCris.ι S) (fun i ↦ 𝟙 ((L i).object hp))).app _)).symm)

/-- **The cohomology of column zero of the Čech–de Rham double complex is Čech cohomology**:
`H^j` of the Moore complex of `∏_x N(D_x) ⊗ Ω^0_{D_x}`, lifted to the universe `u + 1`, is
`H^j(Č(D, N))`, as `Γ(S, 𝒪_S)`-modules. -/
def cechDeRhamColumnZeroHomologyIso (j : ℕ) :
    (ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).obj
        (((alternatingCofaceMapComplex _).obj ((cechDeRhamDoubleComplex hp L N hN).X 0)).homology
          j) ≅
      ((cechFunctor (crystallineStructureSheaf S) (bigBaseRingHom S) (cechObjects hp L)).obj
        ((bigModuleULift S).obj N)).homology j :=
  (ShortComplex.mapHomologyIso
      (((alternatingCofaceMapComplex _).obj ((cechDeRhamDoubleComplex hp L N hN).X 0)).sc j)
      (ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤))).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ j).mapIso (cechDeRhamColumnZeroIso hp L hN)

end ColumnZero

/-! ### The Čech–de Rham double complex computes crystalline cohomology -/

section Main

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe v₂ v₃

variable (hU : ∀ x, ∃ i, x ∈ U i)
  [HasDerivedCategory.{v₂} (BigModuleSheaf S)]
  [HasDerivedCategory.{v₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]

/-- **The Čech–de Rham double complex computes crystalline cohomology**: for `N` quasi-coherent
on `CRIS(X/S)` and `j : ℕ`, the `j`-th cohomology of the total complex of
`B^{a}(⦋n⦌) = ∏_{x : Fin (n + 1) → ι} N(D_x) ⊗ Ω^a_{D_x}`, lifted to the universe `u + 1`, is
`H^j(CRIS(X/S), N)` as a `Γ(S, 𝒪_S)`-module. -/
def cechDeRhamHomologyIso (j : ℕ) :
    (ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).obj
        ((((Crystalline.CosimplicialDoubleComplex.functor (ModuleCat.{u} Γ(S.S.scheme, ⊤))).obj
          (cechDeRhamDoubleComplex hp L N hN)).total (ComplexShape.up ℤ)).homology (j : ℤ)) ≅
      (DerivedCategory.Plus.homologyFunctor _ (j : ℤ)).obj
        ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N)) :=
  (ModuleCat.uliftFunctor.{u + 1, u} Γ(S.S.scheme, ⊤)).mapIso (cechHomologyIsoTotal hp L hN j) ≪≫
    cechDeRhamColumnZeroHomologyIso hp L hN j ≪≫ cechEnvelopeComplexHomologyIso hp hU L N hN j

end Main

end Crystalline.GlobalCrystallineSituation.CechEnvelope
