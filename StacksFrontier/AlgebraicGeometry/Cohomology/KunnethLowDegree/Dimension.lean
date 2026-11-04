module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import StacksFrontier.AlgebraicGeometry.Cohomology.KunnethLowDegree.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.FreenessOverDVR.TrivialityExample
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.ProperHigherDirectImageQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.ProperQcoh.Basic

/-!
# Dimension of `Γ(Y, R¹π₂_* 𝒪)` for a product over a field

For `X` and `Y` proper and geometrically integral over a field `k` and `π₂ : X ×_k Y ⟶ Y`,
`Γ(Y, R¹π₂_* 𝒪)` has dimension `h¹(X, 𝒪_X)` over `k`: by flat base change
`R¹π₂_* 𝒪 ≅ fY^* R¹fX_* 𝒪_X`, a quasi-coherent module on `Spec k` is free on a basis of its
sections, which are `H¹(X, 𝒪_X)` ([Stacks, Tag 01XK]), the inverse image of a free module is free
and `Γ(Y, 𝒪_Y) = k` ([Stacks, Tag 0BUG]).

## Main results

* `Stacks.KunnethLowDegree.isoFreeOfSpecField`: a quasi-coherent module on `Spec k` is free.
* `Stacks.KunnethLowDegree.finrank_globalSections_rightDerived_snd`.

## References

* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

open Stacks.AlgebraicGeometry.HigherDirectImageQcoh
  (cohomologyIsoGlobalSectionsRightDerivedPushforward)

namespace Stacks.KunnethLowDegree

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k]

/-- The ring homomorphism `k ⟶ Γ(T, 𝒪_T)` of a scheme over `k`. -/
abbrev kOf {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) : k →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom

/-- **A quasi-coherent module on the spectrum of a field is free on a basis of its sections.** -/
def isoFreeOfSpecField (N : (Spec (.of k)).Modules) [N.IsQuasicoherent] :
    N ≅ SheafOfModules.free (R := (Spec (.of k)).ringCatSheaf)
      (Module.Basis.ofVectorSpaceIndex k (moduleSpecΓFunctor.obj N)) :=
  (asIso N.fromTildeΓ).symm ≪≫
    (tilde.functor (CommRingCat.of k)).mapIso
      (Module.Basis.ofVectorSpace k (moduleSpecΓFunctor.obj N)).repr.toModuleIso ≪≫
    tildeFinsupp _

/-- For a morphism of schemes `p : T ⟶ T'`, the map `p.appLE ⊤ ⊤ h` equals `p.appTop`. -/
theorem appLE_top_top {T T' : Scheme.{u}} (p : T ⟶ T') (h : (⊤ : T.Opens) ≤ p ⁻¹ᵁ ⊤) :
    p.appLE ⊤ ⊤ h = p.appTop :=
  (congrArg (fun g => p.app ⊤ ≫ g) ((congrArg T.presheaf.map
    (Subsingleton.elim (homOfLE h).op (𝟙 _))).trans (T.presheaf.map_id _))).trans
      (Category.comp_id _)

/-- The `k`-structure of `cohomologyOverField` is the one along `kOf`. -/
theorem kOf_eq {T : Scheme.{u}} (p : T ⟶ Spec (.of k)) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ ⊤ (by simp)).hom = kOf p := by
  rw [appLE_top_top]

/-- **The ring of global functions of a proper geometrically integral scheme over an
algebraically closed field is one-dimensional.** -/
theorem finrank_globalSections_kOf [IsAlgClosed k] {T : Scheme.{u}} (p : T ⟶ Spec (.of k))
    [IsProper p] [GeometricallyIntegral p] :
    letI : Module k Γ(T, ⊤) := Module.compHom _ (kOf p)
    Module.finrank k Γ(T, ⊤) = 1 := by
  have : IsIntegral T := GeometricallyIntegral.isIntegral_of_subsingleton p
  exact finrank_globalSections_eq_one k p

/-- The dimension of a product of copies of the global functions. -/
theorem finrank_pi_globalSections [IsAlgClosed k] {T : Scheme.{u}} (p : T ⟶ Spec (.of k))
    [IsProper p] [GeometricallyIntegral p] (r : ℕ) :
    Module.finrank k ((ModuleCat.restrictScalars (kOf p)).obj
      (ModuleCat.of Γ(T, ⊤) (Fin r → Γ(T, ⊤)))) = r ∧
    FiniteDimensional k ((ModuleCat.restrictScalars (kOf p)).obj
      (ModuleCat.of Γ(T, ⊤) (Fin r → Γ(T, ⊤)))) := by
  let : Algebra k Γ(T, ⊤) := (kOf p).toAlgebra
  have h1 : Module.finrank k Γ(T, ⊤) = 1 := finrank_globalSections_kOf p
  have hfin : FiniteDimensional k Γ(T, ⊤) := Module.finite_of_finrank_eq_succ h1
  let e : ((ModuleCat.restrictScalars (kOf p)).obj
      (ModuleCat.of Γ(T, ⊤) (Fin r → Γ(T, ⊤)))) ≃ₗ[k] (Fin r → Γ(T, ⊤)) :=
    { AddEquiv.refl _ with map_smul' := fun _ _ => rfl }
  refine ⟨?_, Module.Finite.equiv e.symm⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  simp [h1]


/-- **`H¹(X, 𝒪_X)` is the space of sections of `R¹fX_* 𝒪_X` on `Spec k`** ([Stacks, Tag 01XK]),
as `k`-vector spaces. -/
def sectionsRightDerivedLinearEquiv {X : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [QuasiCompact fX]
    [QuasiSeparated fX] :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward fX).rightDerived 1).obj
        (SheafOfModules.unit X.ringCatSheaf)) ≃ₗ[k]
      cohomologyOverField k fX (SheafOfModules.unit X.ringCatSheaf) 1 :=
  ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).mapIso
      ((moduleGlobalSections (Spec (.of k))).mapIso
        (@Stacks.AlgebraicGeometry.HigherDirectImageQcoh.derivedPlusIsoNat _ _ _ _ _ _
          (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _
          (Scheme.Modules.pushforward fX) _ (SheafOfModules.unit X.ringCatSheaf) 1).symm) ≪≫
    (ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of k)).inv.hom).mapIso
      ((cohomologyIsoGlobalSectionsRightDerivedPushforward fX 1).app
        ⟨SheafOfModules.unit X.ringCatSheaf, inferInstance⟩).symm ≪≫
    (ModuleCat.restrictScalarsComp'App _ _ (kOf fX) rfl _).symm ≪≫
    (ModuleCat.restrictScalars (kOf fX)).mapIso
      (@Stacks.AlgebraicGeometry.HigherDirectImageQcoh.derivedPlusIsoNat _ _ _ _ _ _
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _ (moduleGlobalSections X)
        _ (SheafOfModules.unit X.ringCatSheaf) 1) ≪≫
    eqToIso (congrArg (fun φ => (ModuleCat.restrictScalars φ).obj
      (((moduleGlobalSections X).rightDerived 1).obj (SheafOfModules.unit X.ringCatSheaf)))
      (kOf_eq fX).symm)).toLinearEquiv

/-- **`Γ(Y, R¹π₂_* 𝒪)` has dimension `h¹(X, 𝒪_X)`** for `π₂ : X ×_k Y ⟶ Y`, `X` proper and
`Y` proper geometrically integral over an algebraically closed field `k`. -/
theorem finrank_globalSections_rightDerived_snd [IsAlgClosed k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) (fY : Y ⟶ Spec (.of k)) [IsProper fX] [IsProper fY]
    [GeometricallyIntegral fY] :
    FiniteDimensional k ((ModuleCat.restrictScalars (kOf fY)).obj ((moduleGlobalSections Y).obj
      (((Scheme.Modules.pushforward (pullback.snd fX fY)).rightDerived 1).obj
        (SheafOfModules.unit (pullback fX fY).ringCatSheaf)))) ∧
    Module.finrank k ((ModuleCat.restrictScalars (kOf fY)).obj ((moduleGlobalSections Y).obj
      (((Scheme.Modules.pushforward (pullback.snd fX fY)).rightDerived 1).obj
        (SheafOfModules.unit (pullback fX fY).ringCatSheaf)))) =
      Module.finrank k (cohomologyOverField k fX (SheafOfModules.unit X.ringCatSheaf) 1) := by
  classical
  have := forall_finiteDimensional_cohomologyOverField_unit k fX 1
  let N := ((Scheme.Modules.pushforward fX).rightDerived 1).obj
    (SheafOfModules.unit X.ringCatSheaf)
  have : N.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.Tag0EX4ProperQcoh.isQuasicoherent_rightDerived fX
      (SheafOfModules.unit X.ringCatSheaf) 1
  let V := moduleSpecΓFunctor.obj N
  let e := sectionsRightDerivedLinearEquiv fX
  have : FiniteDimensional k V := Module.Finite.equiv e.symm
  let b := Module.Basis.ofVectorSpace k V
  let ι := Module.Basis.ofVectorSpaceIndex k V
  have : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  let r := Module.finrank k V
  have hr : Fintype.card ι = r := (Module.finrank_eq_card_basis b).symm
  let eι : ι ≃ ULift.{u} (Fin r) := (Fintype.equivFinOfCardEq hr).trans Equiv.ulift.symm
  let E : (moduleGlobalSections Y).obj
      (((Scheme.Modules.pushforward (pullback.snd fX fY)).rightDerived 1).obj
        (SheafOfModules.unit (pullback fX fY).ringCatSheaf)) ≅
      ModuleCat.of Γ(Y, ⊤) (Fin r → Γ(Y, ⊤)) :=
    (moduleGlobalSections Y).mapIso (rightDerivedSndUnitIso fX fY ≪≫
      (Scheme.Modules.pullback fY).mapIso (isoFreeOfSpecField N) ≪≫
      Scheme.Modules.pullbackFreeIso fY ι ≪≫
      (SheafOfModules.freeFunctor (R := Y.ringCatSheaf)).mapIso eι.toIso) ≪≫
    Stacks.AlgebraicGeometry.FreenessOverDVR.moduleGlobalSectionsFreeIso Y r
  let Ek := ((ModuleCat.restrictScalars (kOf fY)).mapIso E).toLinearEquiv
  obtain ⟨h1, h2⟩ := finrank_pi_globalSections fY r
  refine ⟨Module.Finite.equiv Ek.symm, ?_⟩
  rw [Ek.finrank_eq, h1, ← e.finrank_eq]

end Stacks.KunnethLowDegree

end
