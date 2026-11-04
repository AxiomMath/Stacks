module

public import StacksFrontier.AlgebraicGeometry.MayerVietorisHgroup.Basic
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits

/-!
# Cohomology of a scheme covered by two affine opens with affine intersection

Let `X` be a scheme, `U` and `V` affine opens with `U ⊔ V = ⊤` and `U ⊓ V` affine, and `F` a
quasi-coherent `𝒪_X`-module. The Mayer--Vietoris sequence for global sections, taken in
`Γ(X, 𝒪_X)`-modules, together with the vanishing of the higher cohomology of a quasi-coherent
module on an affine open ([Stacks, Tag 01XB]), gives

* `Hⁿ(X, F) = 0` for `n ≥ 2`;
* `H¹(X, F)` is the cokernel of the difference of restrictions
  `Γ(U, F) ⊞ Γ(V, F) ⟶ Γ(U ⊓ V, F)`, as a `Γ(X, 𝒪_X)`-module.

This is the two-term Čech complex of the covering. Working with `Γ(X, 𝒪_X)`-modules rather than
abelian groups makes the identification linear over any ring mapping to `Γ(X, 𝒪_X)`.

## Main definitions

* `Stacks.Cohomology.TwoAffineCech.cechDifferential`: the difference of the two restriction
  maps, as a natural transformation of `Γ(X, 𝒪_X)`-module-valued functors.

## Main results

* `Stacks.Cohomology.TwoAffineCech.isZero_rightDerived_of_two_le`: vanishing in degrees `≥ 2`.
* `Stacks.Cohomology.TwoAffineCech.rightDerivedOneIsoCokernel`: `H¹` is the cokernel of the
  Čech differential.
* `Stacks.Cohomology.TwoAffineCech.rightDerivedZeroIsoKernel`: `H⁰` is the kernel of the Čech
  differential.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.AbsoluteMayerVietoris Stacks.Cohomology.RestrictionCover

universe u

namespace Stacks.Cohomology.TwoAffineCech

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

variable (X : Scheme.{u})

/-- Global sections of an `𝒪_X`-module, as a `Γ(X, 𝒪_X)`-module. -/
abbrev Γmod : SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤)) :=
  SheafOfModules.evaluation X.ringCatSheaf (op ⊤)

/-- The global sections functor `Γmod X` is additive. -/
instance : (Γmod X).Additive := by
  dsimp [Γmod, SheafOfModules.evaluation]
  infer_instance

/-- The sections over an open `W`, read as a `Γ(X, 𝒪_X)`-module through restriction. -/
abbrev sectionsOver (W : X.Opens) :
    SheafOfModules.{u} X.ringCatSheaf ⥤ ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤)) :=
  restrictedSections X.ringCatSheaf (Γmod X) W

/-- Sections over `W`, forgotten to abelian groups, are `Γ(W, -)`. -/
def sectionsOverForgetIso (W : X.Opens) :
    sectionsOver X W ⋙ forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u} ≅
      secF X.ringCatSheaf W :=
  eqToIso (restrictedSections_secF_top X.ringCatSheaf W)

/-- **Higher cohomology of the sections over an affine open vanishes on quasi-coherent
modules**: for `W` affine, `F` quasi-coherent and `n > 0`, the `n`-th right derived functor of
`sectionsOver X W` vanishes on `F`. -/
theorem isZero_rightDerived_sectionsOver (W : X.Opens) (hW : IsAffineOpen W)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (hn : 0 < n) : IsZero (((sectionsOver X W).rightDerived n).obj F) := by
  have hAb : IsZero (Hgroup X.ringCatSheaf W n F) :=
    Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F W hW n hn
  have e := (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (sectionsOver X W)
    (forget₂ (ModuleCat.{u} (X.ringCatSheaf.obj.obj (op ⊤))) AddCommGrpCat.{u})
    (secF X.ringCatSheaf W) (sectionsOverForgetIso X W) n).app F
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero (hAb.of_iso e))

variable (U V : X.Opens)

/-- **The Čech differential** `Γ(U, -) ⊞ Γ(V, -) ⟶ Γ(U ⊓ V, -)`, the difference of the two
restrictions, as a natural transformation of `Γ(X, 𝒪_X)`-module-valued functors. -/
abbrev cechDifferential : sectionsOver X U ⊞ sectionsOver X V ⟶ sectionsOver X (U ⊓ V) :=
  toIntersection X.ringCatSheaf (Γmod X) U V

/-- The augmentation `Γ(X, -) ⟶ Γ(U, -) ⊞ Γ(V, -)`. -/
abbrev cechAugmentation : Γmod X ⟶ sectionsOver X U ⊞ sectionsOver X V :=
  toCover X.ringCatSheaf (Γmod X) U V

variable (hUV : U ⊔ V = ⊤)

/-- The connecting morphism of the Mayer--Vietoris sequence for `Γ(X, 𝒪_X)`-modules. -/
abbrev mvDelta (n : ℕ) : (sectionsOver X (U ⊓ V)).rightDerived n ⟶ (Γmod X).rightDerived (n + 1) :=
  CategoryTheory.rightDerivedDelta (cechAugmentation X U V) (cechDifferential X U V)
    (toCover_comp_toIntersection X.ringCatSheaf (Γmod X) U V)
    (fun M hM => shortExact_on_injectives X.ringCatSheaf (Γmod X) U V hUV M hM) n

/-- **The Mayer--Vietoris sequence for `Γ(X, 𝒪_X)`-modules.** -/
theorem mayerVietoris_exact (n : ℕ) (F : SheafOfModules.{u} X.ringCatSheaf) :
    (ComposableArrows.mk₅ ((NatTrans.rightDerived (cechAugmentation X U V) n).app F)
      ((NatTrans.rightDerived (cechDifferential X U V) n).app F)
      ((mvDelta X U V hUV n).app F)
      ((NatTrans.rightDerived (cechAugmentation X U V) (n + 1)).app F)
      ((NatTrans.rightDerived (cechDifferential X U V) (n + 1)).app F)).Exact :=
  CategoryTheory.exact_rightDerived_composableArrows₅ (cechAugmentation X U V)
    (cechDifferential X U V) (toCover_comp_toIntersection X.ringCatSheaf (Γmod X) U V)
    (fun M hM => shortExact_on_injectives X.ringCatSheaf (Γmod X) U V hUV M hM)
    (injectiveResolution F) n

variable {U V}

/-- The middle term of the derived sequence vanishes in positive degrees when `U` and `V` are
affine and `F` is quasi-coherent. -/
theorem isZero_rightDerived_biprod (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (hn : 0 < n) : IsZero (((sectionsOver X U ⊞ sectionsOver X V).rightDerived n).obj F) := by
  refine IsZero.of_iso ?_ ((Functor.rightDerivedBiprodIso (sectionsOver X U)
    (sectionsOver X V) n).app F ≪≫ evalBiprodIso _ _ F)
  exact (biprod_isZero_iff _ _).mpr ⟨isZero_rightDerived_sectionsOver X U hU F n hn,
    isZero_rightDerived_sectionsOver X V hV F n hn⟩

include hUV in
/-- **Vanishing of `Hⁿ(X, F)` for `n ≥ 2`** on a scheme covered by two affine opens with affine
intersection. -/
theorem isZero_rightDerived_of_two_le (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV' : IsAffineOpen (U ⊓ V)) (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) :
    IsZero (((Γmod X).rightDerived n).obj F) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact ((mayerVietoris_exact X U V hUV m F).exact 2).isZero_X₂
    ((isZero_rightDerived_sectionsOver X (U ⊓ V) hUV' F m (by omega)).eq_of_src _ _)
    ((isZero_rightDerived_biprod X hU hV F (m + 1) (by omega)).eq_of_tgt _ _)

/-- For `U`, `V` affine and `F` quasi-coherent, the Mayer--Vietoris connecting morphism
`H⁰(U ⊓ V, F) ⟶ H¹(X, F)` is an epimorphism. -/
theorem epi_mvDelta_zero (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (F : X.Modules) [F.IsQuasicoherent] :
    Epi ((mvDelta X U V hUV 0).app F) :=
  ((mayerVietoris_exact X U V hUV 0 F).exact 2).epi_f
    ((isZero_rightDerived_biprod X hU hV F 1 (by omega)).eq_of_tgt _ _)

/-! ### Degree zero: the derived functors in degree zero are the functors themselves -/

/-- Restriction to `W` followed by pushforward along the inclusion preserves finite limits. -/
instance preservesFiniteLimits_restrictPush (W : X.Opens) :
    PreservesFiniteLimits (restrictPush X.ringCatSheaf W) := by
  have : (ExtensionByZeroModules.jStar W X.ringCatSheaf).IsRightAdjoint :=
    (ExtensionByZeroModules.jShriekAdjunction W X.ringCatSheaf).isRightAdjoint
  have : (ExtensionByZeroModules.jPush W X.ringCatSheaf).IsRightAdjoint :=
    (ExtensionByZeroModules.jStarAdjunction W X.ringCatSheaf).isRightAdjoint
  dsimp only [restrictPush]
  infer_instance

/-- The sections over an open `W`, as a `Γ(X, 𝒪_X)`-module, preserve finite limits. -/
instance preservesFiniteLimits_sectionsOver (W : X.Opens) :
    PreservesFiniteLimits (sectionsOver X W) := by
  dsimp only [sectionsOver, restrictedSections]
  infer_instance

/-- The biproduct of two finite-limit-preserving functors into an abelian category preserves
finite limits. -/
theorem preservesFiniteLimits_biprod {A B : Type*} [Category A] [Category B] [Abelian B]
    (F G : A ⥤ B) [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⊞ G) := by
  let : HasFiniteBiproducts B := HasFiniteBiproducts.of_hasFiniteProducts
  apply (ObjectProperty.preservesFiniteLimits (J := A) (C := B)).prop_of_isColimit
    (BinaryBiproduct.isColimit F G)
  rintro (_ | _) <;> change PreservesFiniteLimits _ <;> assumption

/-- The biproduct `sectionsOver X U ⊞ sectionsOver X V` preserves finite limits. -/
instance preservesFiniteLimits_sectionsOver_biprod (U V : X.Opens) :
    PreservesFiniteLimits (sectionsOver X U ⊞ sectionsOver X V) :=
  preservesFiniteLimits_biprod _ _

/-- The global sections functor `Γmod X` preserves finite limits. -/
instance preservesFiniteLimits_Γmod : PreservesFiniteLimits (Γmod X) := by
  dsimp only [Γmod]
  infer_instance

variable (U V : X.Opens) (hUV : U ⊔ V = ⊤)

/-- The Čech differential commutes with the comparison maps to the zeroth right derived
functors. -/
theorem toRightDerivedZero_comm (F : SheafOfModules.{u} X.ringCatSheaf) :
    (cechDifferential X U V).app F ≫
        (asIso ((sectionsOver X (U ⊓ V)).toRightDerivedZero.app F)).hom =
      (asIso ((sectionsOver X U ⊞ sectionsOver X V).toRightDerivedZero.app F)).hom ≫
        (NatTrans.rightDerived (cechDifferential X U V) 0).app F :=
  (Functor.toRightDerivedZero_naturality_app (cechDifferential X U V) F).symm

include hUV in
/-- **`H¹(X, F)` is the cokernel of the Čech differential**, for `X = U ∪ V` with `U`, `V`
affine and `F` quasi-coherent. -/
def rightDerivedOneIsoCokernel (hU : IsAffineOpen U) (hV : IsAffineOpen V) (F : X.Modules)
    [F.IsQuasicoherent] :
    ((Γmod X).rightDerived 1).obj F ≅ cokernel ((cechDifferential X U V).app F) := by
  have hex := (mayerVietoris_exact X U V hUV 0 F).exact 1
  have hw := (mayerVietoris_exact X U V hUV 0 F).toIsComplex.zero 1
  let S := ShortComplex.mk ((NatTrans.rightDerived (cechDifferential X U V) 0).app F)
    ((mvDelta X U V hUV 0).app F) hw
  have hS : S.Exact := hex
  have : Epi S.g := epi_mvDelta_zero X hUV hU hV F
  exact (IsColimit.coconePointUniqueUpToIso (hS.gIsCokernel) (cokernelIsCokernel _)) ≪≫
    (cokernel.mapIso _ _ _ _ (toRightDerivedZero_comm X U V F)).symm

include hUV in
/-- **`H⁰(X, F)` is the kernel of the Čech differential.** -/
def rightDerivedZeroIsoKernel (F : X.Modules) :
    ((Γmod X).rightDerived 0).obj F ≅ kernel ((cechDifferential X U V).app F) := by
  have hex := (mayerVietoris_exact X U V hUV 0 F).exact 0
  have hw := (mayerVietoris_exact X U V hUV 0 F).toIsComplex.zero 0
  let S := ShortComplex.mk ((NatTrans.rightDerived (cechAugmentation X U V) 0).app F)
    ((NatTrans.rightDerived (cechDifferential X U V) 0).app F) hw
  have hS : S.Exact := hex
  have : Mono S.f :=
    CategoryTheory.mono_rightDerived_zero_app (cechAugmentation X U V)
      (cechDifferential X U V) (toCover_comp_toIntersection X.ringCatSheaf (Γmod X) U V)
      (fun M hM => shortExact_on_injectives X.ringCatSheaf (Γmod X) U V hUV M hM) F
  exact (IsLimit.conePointUniqueUpToIso (hS.fIsKernel) (kernelIsKernel _)) ≪≫
    (kernel.mapIso _ _ _ _ (toRightDerivedZero_comm X U V F)).symm

end Stacks.Cohomology.TwoAffineCech
