module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksCore.CategoryTheory.Abelian.ShortExact
public import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.ModuleGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive

/-!
# Extensions of quasi-coherent modules on affine schemes

Let `X` be an affine scheme and let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` be a short exact sequence of
`𝒪_X`-modules. If two of the three terms are quasi-coherent then so is the third, which is
[Stacks, Tag 01IE].

## Main results

* `Stacks.AlgebraicGeometry.QuasicoherentExtension.isQuasicoherent_left_of_shortExact`: the left
  term is quasi-coherent if the middle and right terms are.
* `Stacks.AlgebraicGeometry.QuasicoherentExtension.isQuasicoherent_middle_of_shortExact`: the
  middle term is quasi-coherent if both outer terms are.
* `Stacks.AlgebraicGeometry.QuasicoherentExtension.isQuasicoherent_right_of_shortExact`: the right
  term is quasi-coherent if the left and middle terms are.

## Implementation notes

An affine scheme is Mathlib's `AlgebraicGeometry.IsAffine` predicate rather than a chosen
isomorphism with a spectrum. The derived category instances are
`CategoryTheory.HasDerivedCategory.standard`, installed as local instances.

## References

* [Stacks Project, Tag 01IE](https://stacks.math.columbia.edu/tag/01IE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.AlgebraicGeometry.QuasicoherentExtension

noncomputable section

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Right acyclicity of global sections on an affine scheme -/

/-- The bounded below derived functor of an additive functor out of a category with enough
injectives is everywhere defined. -/
private lemma hasRightDerivedFunctor_of_additive {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive] :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso C) :=
  have := (HomotopyCategory.Plus.localizerMorphism_derives
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh)).hasPointwiseRightDerivedFunctor
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

attribute [local instance] hasRightDerivedFunctor_of_additive

/-- An object whose `ℕ`-indexed higher right derived functors vanish in positive degrees is right
acyclic for a left exact functor. -/
private lemma rightAcyclic_of_isZero_rightDerived {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (A : C)
    (h : ∀ n : ℕ, 0 < n → IsZero ((F.rightDerived n).obj A)) : F.rightAcyclic A := by
  refine ((F.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus A).2 inferInstance).2 ?_
  intro i hi
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff F
    (m := (n : ℤ)) (n := n) rfl A).2 (h n (by exact_mod_cast hi))

/-- A quasi-coherent module on an affine scheme is right acyclic for the global sections
functor. -/
private lemma rightAcyclic_moduleGlobalSections (X : Scheme.{u}) [IsAffine X] (F : X.Modules)
    [F.IsQuasicoherent] : (AlgebraicGeometry.moduleGlobalSections X).rightAcyclic F := by
  have : EnoughInjectives (X.Modules) := IsGrothendieckAbelian.enoughInjectives
  refine rightAcyclic_of_isZero_rightDerived (AlgebraicGeometry.moduleGlobalSections X) F
    fun n hn ↦ ?_
  exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F ⊤
        (isAffineOpen_top X) n hn)
      ((Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso
        X.ringCatSheaf ⊤ n).app F)))

/-- Global sections over an affine scheme are exact on a short exact sequence with quasi-coherent
outer terms. -/
private lemma shortExact_map_moduleGlobalSections (X : Scheme.{u}) [IsAffine X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (AlgebraicGeometry.moduleGlobalSections X)).ShortExact := by
  have : EnoughInjectives (X.Modules) := IsGrothendieckAbelian.enoughInjectives
  exact ((Functor.rightAcyclic_and_shortExact_map_of_shortExact
      (AlgebraicGeometry.moduleGlobalSections X) S hS).1
    (rightAcyclic_moduleGlobalSections X S.X₁) (rightAcyclic_moduleGlobalSections X S.X₃)).2

/-! ### The middle term on a spectrum -/

/-- In a short exact sequence of modules on `Spec R`, the middle term is quasi-coherent if both
outer terms are. -/
private lemma isQuasicoherent_middle_onSpec (R : CommRingCat.{u})
    (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent := by
  have hΓ : (S.map (moduleSpecΓFunctor (R := R))).ShortExact := by
    show (S.map (AlgebraicGeometry.moduleGlobalSections (Spec R) ⋙
      ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).inv.hom)).ShortExact
    exact (shortExact_map_moduleGlobalSections (Spec R) S hS).map_of_exact
      (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).inv.hom)
  have hTilde : ((S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R)).ShortExact :=
    hΓ.map_of_exact (tilde.functor R)
  let φ : (S.map (moduleSpecΓFunctor (R := R))).map (tilde.functor R) ⟶ S :=
    { τ₁ := S.X₁.fromTildeΓ
      τ₂ := S.X₂.fromTildeΓ
      τ₃ := S.X₃.fromTildeΓ
      comm₁₂ := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality S.f |>.symm
      comm₂₃ := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality S.g |>.symm }
  exact (isQuasicoherent_iff_isIso_fromTildeΓ S.X₂).2
    (ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' φ hTilde hS
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁)
      (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃))

/-- Restriction along `e.inv` followed by restriction along `e.hom` is isomorphic to the
identity. -/
private def restrictFunctorInvCompHomIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    Scheme.Modules.restrictFunctor e.inv ⋙ Scheme.Modules.restrictFunctor e.hom ≅ 𝟭 _ :=
  (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
    Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId

/-- Restriction of modules along an isomorphism of schemes is an equivalence. -/
private lemma restrictFunctor_isEquivalence_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.restrictFunctor e.inv).IsEquivalence :=
  Functor.IsEquivalence.mk' (Scheme.Modules.restrictFunctor e.hom)
    (restrictFunctorInvCompHomIso e).symm (restrictFunctorInvCompHomIso e.symm)

/-! ### Quasi-coherence of the terms of a short exact sequence -/

/-- In a short exact sequence of modules on an affine scheme, the left term is quasi-coherent if
the middle and right terms are. -/
@[stacks 01IE "left term"]
lemma isQuasicoherent_left_of_shortExact {X : Scheme.{u}} [IsAffine X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₁.IsQuasicoherent :=
  have h : (kernel S.g).IsQuasicoherent := inferInstance
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) hS.fIsKernel) h

/-- In a short exact sequence of modules on an affine scheme, the middle term is quasi-coherent if
both outer terms are. -/
@[stacks 01IE "middle term"]
lemma isQuasicoherent_middle_of_shortExact {X : Scheme.{u}} [IsAffine X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    S.X₂.IsQuasicoherent := by
  let e := X.isoSpec
  let F := Scheme.Modules.restrictFunctor e.inv
  have : F.IsEquivalence := restrictFunctor_isEquivalence_of_iso e
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  have h₁ : ((S.map F).X₁).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor e.inv S.X₁
  have h₃ : ((S.map F).X₃).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor e.inv S.X₃
  have h₂ : (F.obj S.X₂).IsQuasicoherent :=
    isQuasicoherent_middle_onSpec _ (S.map F) (hS.map_of_exact F)
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((restrictFunctorInvCompHomIso e).app S.X₂)
    (Scheme.Modules.isQuasicoherent_restrictFunctor e.hom (F.obj S.X₂))

/-- In a short exact sequence of modules on an affine scheme, the right term is quasi-coherent if
the left and middle terms are. -/
@[stacks 01IE "right term"]
lemma isQuasicoherent_right_of_shortExact {X : Scheme.{u}} [IsAffine X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] :
    S.X₃.IsQuasicoherent :=
  have h : (cokernel S.f).IsQuasicoherent := inferInstance
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS.gIsCokernel) h

end

end Stacks.AlgebraicGeometry.QuasicoherentExtension

end
