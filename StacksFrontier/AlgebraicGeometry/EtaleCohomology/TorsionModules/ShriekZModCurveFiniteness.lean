module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.ShriekConstantCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveCohomologyTheorem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.AbelianShriekConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ExtensionByZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.DenseSubsiteGlobalCohomology

/-!
# Finite cohomology of `j_!(ℤ/ℓ)` on a curve

Let `k` be an algebraically closed field, `X` a separated scheme of finite type over `k` of
dimension at most one, `j : U ⟶ X` an étale morphism with `U` quasi-compact and quasi-separated,
and `ℓ` a prime. The abelian sheaf `j_!(ℤ/ℓ)` on `X_étale` is constructible (Stacks 03S8) and
killed by `ℓ`, so by statements (4) and (5) of Situation 0A52 (Tags 0A56 and 0A57) its
cohomology groups are finite if `ℓ` is prime to the characteristic of `k`, and also if `X` is
proper. This file records that, at every coefficient universe.

## Main results

* `Stacks.EtaleCohomology.extensionByZeroUliftIso`: extension by zero commutes with the universe
  lift of the coefficients.
* `Stacks.EtaleCohomology.isConstructibleEtaleAbelianSheaf_extensionByZero_constantSheaf`: the
  extension by zero from an object of the small étale site of Tag 021B of a finite constant
  sheaf, read on Mathlib's site, is constructible (Stacks 03S8 (2)).
* `Stacks.EtaleCohomology.finite_rightDerived_etaleAbelianShriekConstant_zmod`: the finiteness of
  `H^q(X, j_!(ℤ/ℓ))`.

## Implementation notes

Statements (4) and (5) are applied at the coefficients `AddCommGrpCat.{u + 1}`, where Stacks 03S8
(2) is available on the site of Tag 021B, and carried to `AddCommGrpCat.{max (u + 1) r}` by the
universe lift (`Stacks.EtaleCohomology.finite_sheafH_of_etaleUlift_iso`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

section Ulift

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]

/-- **Extension by zero commutes with the universe lift of the coefficients**: the universe lift
preserves colimits, hence pointwise left Kan extensions, and sheafification on the small étale
site. -/
def extensionByZeroUliftIso :
    etaleUlift.{r} U ⋙ extensionByZero.{u, r} j ≅ extensionByZero.{u, 0} j ⋙ etaleUlift.{r} X :=
  asIso (coefficientPullbackTwoSquare (Scheme.Etale.smallEtaleCompose j) U.smallEtaleTopology
    X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{r, u + 1}).natTrans

/-- The universe lift of `j_!(A̲)` is `j_!` of the constant sheaf on the universe lift of `A`. -/
def etaleAbelianShriekConstantUliftIso :
    etaleAbelianShriekConstant.{u, 0} j ⋙ etaleUlift.{r} X ≅
      AddCommGrpCat.uliftFunctor.{r, u + 1} ⋙ etaleAbelianShriekConstant.{u, r} j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (extensionByZeroUliftIso.{u, r} j).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (constantCommuteCompose U.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{r, u + 1}) _ ≪≫
    Functor.associator _ _ _

end Ulift

section Constructible

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (U : SmallEtale B X.obj X.property)
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) AddCommGrpCat.{u + 1}]

/-- The transport to the small étale site of Tag 021B of `j_!(A̲)` on Mathlib's site, for the
structure morphism `j` of an object `U` of the former, is the extension by zero of `A̲` there.
Extension by zero commutes with the passage between the two sites
(`AlgebraicGeometry.SmallEtale.sheafEquivExtensionByZeroIso`), and so does the constant sheaf. -/
def sheafEquivInverseAbelianShriekConstantIso (A : AddCommGrpCat.{u + 1}) :
    haveI : Etale (B.inclusion.map U.obj.hom) := U.property
    (SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}).inverse.obj
        ((etaleAbelianShriekConstant.{u, 0} (B.inclusion.map U.obj.hom)).obj A) ≅
      (abelianExtensionByZero B X.obj X.property U).obj
        ((constantSheaf (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
          AddCommGrpCat.{u + 1}).obj A) := by
  haveI : Etale (B.inclusion.map U.obj.hom) := U.property
  let E := SmallEtale.sheafEquiv B X.obj X.property AddCommGrpCat.{u + 1}
  let EU := SmallEtale.sheafEquiv B U.obj.left.1 U.obj.left.property AddCommGrpCat.{u + 1}
  let iT := SmallEtale.sheafEquivExtensionByZeroIso B X.obj X.property U AddCommGrpCat.{u + 1}
    (extensionByZeroAdj.{u, 0} (B.inclusion.map U.obj.hom))
    (abelianExtensionByZeroAdjunction B X.obj X.property U)
  let rc := (Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    U.obj.left.1.smallEtaleTopology
    (SmallEtale.toEtaleSite B U.obj.left.1 U.obj.left.property) AddCommGrpCat.{u + 1}).app A
  let d : EU.functor.obj ((constantSheaf (SmallEtale.topology B U.obj.left.1
        U.obj.left.property) AddCommGrpCat.{u + 1}).obj A) ≅
      (constantSheaf U.obj.left.1.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A :=
    EU.functor.mapIso rc.symm ≪≫ EU.counitIso.app _
  exact E.inverse.mapIso ((extensionByZero.{u, 0} (B.inclusion.map U.obj.hom)).mapIso d.symm ≪≫
      iT.app _) ≪≫ E.unitIso.symm.app _

/-- **Stacks 03S8 (2) read on Mathlib's small étale site.** For an object `U` of the small étale
site of Tag 021B of a quasi-compact quasi-separated `X`, with `U` quasi-compact and
quasi-separated and structure morphism `j`, and a finite abelian group `A`, the abelian sheaf
`j_!(A̲)` on Mathlib's small étale site of `X` is constructible. -/
theorem isConstructibleEtaleAbelianSheaf_extensionByZero_constantSheaf
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj]
    (A : AddCommGrpCat.{u + 1}) [Finite A] :
    haveI : Etale (B.inclusion.map U.obj.hom) := U.property
    IsConstructibleEtaleAbelianSheaf.{u, 0} B X.obj X.property
      ((etaleAbelianShriekConstant.{u, 0} (B.inclusion.map U.obj.hom)).obj A) :=
  isConstructibleAbelianSheaf_congr B X (sheafEquivInverseAbelianShriekConstantIso B X U A).symm
    (isConstructibleAbelianSheaf_abelianShriekConstant B X A U)

end Constructible

section Finiteness

attribute [local instance] hasExt_sheaf_smallEtale_succ
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp
  Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ

/-- **`H^q(X, j_!(ℤ/ℓ))` is finite on a curve** (Tags 0A56 and 0A57 for the constructible sheaf
`j_!(ℤ/ℓ)`, Stacks 03S8). Let `k` be algebraically closed, `X` separated of finite type over `k`
of dimension at most one, `U` a quasi-compact quasi-separated object of the small étale site of
Tag 021B of `X` with structure morphism `j`, and `ℓ` a prime which is prime to the characteristic
of `k` or such that `X` is proper. Then `H^q(X, j_!(ℤ/ℓ))` is finite for every `q`, at every
coefficient universe. -/
theorem finite_rightDerived_etaleAbelianShriekConstant_zmod {k : Type u} [Field k]
    [IsAlgClosed k] (B : BigEtaleSite.{u}) (X : B.Scheme) (π : X.obj ⟶ Spec (.of k))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    (hdim : topologicalKrullDim X.obj ≤ 1) (U : SmallEtale B X.obj X.property)
    [CompactSpace U.obj.left.obj] [QuasiSeparatedSpace U.obj.left.obj]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ) :
    haveI : Etale (B.inclusion.map U.obj.hom) := U.property
    Finite (((Sheaf.Γ X.obj.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).obj
      ((etaleAbelianShriekConstant.{u, r} (B.inclusion.map U.obj.hom)).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) r} (ZMod ℓ))))) := by
  have : Etale (B.inclusion.map U.obj.hom) := U.property
  have : CompactSpace X.obj := QuasiCompact.compactSpace_of_compactSpace π
  have : QuasiSeparatedSpace X.obj := quasiSeparatedSpace_of_quasiSeparated π
  have := SmallEtale.isRightAdjoint_smallEtalePushforward_addCommGrpCat.{u, 0} B
  have := SmallEtale.hasWeakSheafify_over_addCommGrpCat.{u, 0} B
  let j := B.inclusion.map U.obj.hom
  let A₀ := AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))
  let G₀ := (etaleAbelianShriekConstant.{u, 0} j).obj A₀
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : Finite A₀ := inferInstanceAs (Finite (ULift (ZMod ℓ)))
  have hA : ((ℓ : ℤ) • 𝟙 A₀) = 0 := by
    refine AddCommGrpCat.ext fun x => ?_
    apply ULift.ext
    show (ℓ : ℤ) • x.down = 0
    rw [zsmul_eq_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]
  have hG : ((ℓ : ℤ) • 𝟙 G₀) = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_zsmul, hA, Functor.map_zero]
  have hsec : ∀ (V : X.obj.Etaleᵒᵖ) (x : G₀.obj.obj V), ℓ • x = 0 := fun V x => by
    rw [← natCast_zsmul]
    exact (Stacks.Cohomology.ZModSheaf.zsmul_id_eq_zero_iff G₀ ℓ).1 hG V x
  have htors : Stacks.Torsion.torsionSheafProperty X.obj.smallEtaleTopology G₀ := fun V x =>
    ⟨⊤, X.obj.smallEtaleTopology.top_mem V, fun W g _ => ⟨ℓ, hℓ.pos, hsec _ _⟩⟩
  let S : TorsionSheafSituation.{u, 0} :=
    { k := k, X := X.obj, structureMorphism := π, dimension_le_one := hdim, F := G₀,
      isTorsion := htors }
  have hc : IsConstructibleEtaleAbelianSheaf.{u, 0} B S.X X.property S.F :=
    isConstructibleEtaleAbelianSheaf_extensionByZero_constantSheaf B X U A₀
  have h₀ : Finite (Sheaf.H.{u + 1} G₀ q) := by
    rcases hℓp with hcop | hprop
    · exact S.finiteCohomologyOfPrimeToCharacteristic B X.property hc
        (fun V x => ⟨⊤, X.obj.smallEtaleTopology.top_mem V, fun W g _ =>
          ⟨ℓ, hℓ.pos, hcop, hsec _ _⟩⟩) q
    · exact S.finiteCohomologyOfIsProper B X.property hprop hc q
  let eL : AddCommGrpCat.uliftFunctor.{r, u + 1}.obj A₀ ≅
      AddCommGrpCat.of (ULift.{max (u + 1) r} (ZMod ℓ)) :=
    (AddEquiv.ulift.trans (AddEquiv.ulift.trans AddEquiv.ulift.symm)).toAddCommGrpIso
  let e : (etaleUlift.{r} X.obj).obj G₀ ≅
      (etaleAbelianShriekConstant.{u, r} j).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) r} (ZMod ℓ))) :=
    (etaleAbelianShriekConstantUliftIso.{u, r} j).app A₀ ≪≫
      (etaleAbelianShriekConstant.{u, r} j).mapIso eL
  exact @Finite.of_equiv _ _ (finite_sheafH_of_etaleUlift_iso.{max (u + 1) r} e q h₀)
    ((Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{r} X.obj.smallEtaleTopology
      q).app _).addCommGroupIsoToAddEquiv.toEquiv.symm

/-- **`H^q(Y, e_!(ℤ/ℓ))` is finite on a curve, for any étale `e : W ⟶ Y` with `W` affine.** This
is `finite_rightDerived_etaleAbelianShriekConstant_zmod` read on a big étale site containing `Y`
and `W`, of whose small étale site over `Y` the morphism `e` is an object. -/
theorem finite_rightDerived_etaleAbelianShriekConstant_zmod_of_isAffine {k : Type u} [Field k]
    [IsAlgClosed k] {Y : Scheme.{u}} (π : Y ⟶ Spec (.of k)) [IsSeparated π]
    [LocallyOfFiniteType π] [QuasiCompact π] (hdim : topologicalKrullDim Y ≤ 1) {W : Scheme.{u}}
    (e : W ⟶ Y) [Etale e] [IsAffine W] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓp : ℓ.Coprime (ringExpChar k) ∨ IsProper π) (q : ℕ) :
    Finite (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) r}).rightDerived q).obj
      ((etaleAbelianShriekConstant.{u, r} e).obj
        (AddCommGrpCat.of (ULift.{max (u + 1) r} (ZMod ℓ))))) := by
  obtain ⟨B, hB⟩ := BigEtaleSite.exists_contains_of_small ({Y, W} : Set Scheme.{u})
  have hY : B.Contains Y := hB Y (by simp)
  have hW : B.Contains W := hB W (by simp)
  let U : SmallEtale B Y hY :=
    ⟨Over.mk (ObjectProperty.homMk e : B.obj W hW ⟶ B.obj Y hY), (inferInstance : Etale e)⟩
  have : CompactSpace U.obj.left.obj := inferInstanceAs (CompactSpace W)
  have : QuasiSeparatedSpace U.obj.left.obj := inferInstanceAs (QuasiSeparatedSpace W)
  exact finite_rightDerived_etaleAbelianShriekConstant_zmod.{u, r} B (B.obj Y hY) π hdim U ℓ hℓ
    hℓp q

end Finiteness

end Stacks.EtaleCohomology

end
