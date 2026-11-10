module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.DescentResolutionQuasiIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangeResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareTransComposition
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowTruncation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedFibreBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedSectionsRestriction

/-!
# Toward the base change map for sheaves of modules from the one for abelian sheaves

Two ingredients for comparing the base change map `g⁻¹ Rf_* ⟶ Rf'_* g'⁻¹` of sheaves of
`Λ`-modules (`Stacks.EtaleCohomology.etaleModuleDerivedBaseChange`) with the abelian one
(`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, through which the base change maps on
higher direct images `Stacks.EtaleCohomology.higherBaseChangeMapAb` are defined).

* The abelian derived base change map is invertible at `F[0]` when every
  `higherBaseChangeMapAb q` is invertible at `F`
  (`Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_app_single_of_forall`): an
  isomorphism of `D⁺` is one on every cohomology sheaf, both sides vanish in negative degrees, and
  in degree `q ≥ 0` the cohomology of the derived map is the degree-`q` map.
* The underived abelian base change map `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is the
  comparison `Stacks.EtaleCohomology.etaleAbelianBaseChange.{u, 0}` (the coefficient universe of
  the sheaves of `ℤ/N`-modules) conjugated by the identification of the two inverse images
  (`Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange_zero`).

The statements are made in the standard model `HasDerivedCategory.standard`, in which
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` is stated.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleDerivedBaseChangeAb_app_single_of_forall`.
* `Stacks.EtaleCohomology.smallEtalePullbackAbIsoInverseImage_inv`.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange_zero`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

section Generic

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The abelian derived base change map at `F[0]` from all the higher base change maps.** If
the base change maps `f'⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` are invertible for every `q`, the derived
base change map is invertible at `F[0]`: an isomorphism of `D⁺` is one on every cohomology sheaf,
both sides vanish in negative degrees, and in degree `q ≥ 0` the cohomology of the derived map is
the degree-`q` map (`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_iff`). -/
theorem isIso_smallEtaleDerivedBaseChangeAb_app_single_of_forall
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (hq : ∀ q : ℕ, IsIso ((higherBaseChangeMapAb f' g h e w q).app F)) :
    IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
      ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj
        F)) := by
  refine (DerivedCategory.Plus.isIso_iff _).2 fun n => ?_
  rcases lt_or_ge n 0 with hn | hn
  · let F₀ := (DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F
    have h1 : ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj F₀).IsGE 0 :=
      Functor.isGE_rightDerivedFunctorPlus_obj _ F₀ 0
    have h2 : ((smallEtalePullbackAb f').rightDerivedFunctorPlus.obj
        ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj F₀)).IsGE 0 :=
      Functor.isGE_rightDerivedFunctorPlus_obj _ _ 0
    have h3 : ((smallEtalePullbackAb e).rightDerivedFunctorPlus.obj F₀).IsGE 0 :=
      Functor.isGE_rightDerivedFunctorPlus_obj _ F₀ 0
    have h4 : ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.obj
        ((smallEtalePullbackAb e).rightDerivedFunctorPlus.obj F₀)).IsGE 0 :=
      Functor.isGE_rightDerivedFunctorPlus_obj _ _ 0
    have hs := DerivedCategory.Plus.isZero_homology_of_isGE
      ((smallEtalePullbackAb f').rightDerivedFunctorPlus.obj
        ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj F₀)) 0 n hn
    have ht := DerivedCategory.Plus.isZero_homology_of_isGE
      ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.obj
        ((smallEtalePullbackAb e).rightDerivedFunctorPlus.obj F₀)) 0 n hn
    exact ⟨⟨ht.to_ _, hs.eq_of_src _ _, ht.eq_of_src _ _⟩⟩
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact (isIso_higherBaseChangeMapAb_app_iff f' g h e w q F).1 (hq q)

end Generic

section Bridge

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The identification of the two inverse images of abelian étale sheaves, read in the other
direction, is the canonical comparison of left adjoints taken in the other order. -/
theorem smallEtalePullbackAbIsoInverseImage_inv {X Y : Scheme.{u}} (c : X ⟶ Y) :
    (smallEtalePullbackAbIsoInverseImage c).inv =
      (Adjunction.leftAdjointUniq (etaleAbelianInverseImageDirectImageAdj.{u, 0} c)
        (smallEtaleAdjunctionAb c)).hom :=
  NatTrans.ext (funext fun F => Adjunction.leftAdjointUniq_inv_app _ _ F)

/-- **The two underived étale base change comparisons of a square agree**, with coefficients in
`AddCommGrpCat.{max (u + 1) 0}`: `Stacks.EtaleCohomology.smallEtaleBaseChangeAb f' g h e w` is
`Stacks.EtaleCohomology.etaleAbelianBaseChange.{u, 0} g f' e h w.symm` conjugated by the
identification `Stacks.EtaleCohomology.smallEtalePullbackAbIsoInverseImage` of the two inverse
images. This is `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange` in the
coefficient universe of the sheaves of `ℤ/N`-modules, whose comparisons with abelian sheaves are
stated with `Stacks.EtaleCohomology.etaleAbelianBaseChange.{u, 0}`; the proof is the same. -/
theorem smallEtaleBaseChangeAb_eq_etaleAbelianBaseChange_zero :
    smallEtaleBaseChangeAb f' g h e w =
      Functor.whiskerLeft (smallEtalePushforwardAb g) (smallEtalePullbackAbIsoInverseImage f').hom ≫
        etaleAbelianBaseChange.{u, 0} g f' e h w.symm ≫
        Functor.whiskerRight (smallEtalePullbackAbIsoInverseImage e).inv
          (smallEtalePushforwardAb h) := by
  have e1 : (conjugateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, 0} f')
        (smallEtaleAdjunctionAb f')).symm (𝟙 (etaleAbelianDirectImage.{u, 0} f')) =
      (smallEtalePullbackAbIsoInverseImage f').hom :=
    Stacks.CategoryTheory.conjugateEquiv_symm_id _ _
  have e2 : (conjugateEquiv (smallEtaleAdjunctionAb e)
        (etaleAbelianInverseImageDirectImageAdj.{u, 0} e)).symm
          (𝟙 (etaleAbelianDirectImage.{u, 0} e)) =
      (smallEtalePullbackAbIsoInverseImage e).inv :=
    (Stacks.CategoryTheory.conjugateEquiv_symm_id _ _).trans
      (smallEtalePullbackAbIsoInverseImage_inv e).symm
  have e3 := etaleAbelianBaseChange_eq_mateEquiv_symm_directImageCompIso.{u, 0} g f' e h
    w.symm (e ≫ g) rfl w.symm
  have hmate := Stacks.CategoryTheory.mateEquiv_symm_eq_whiskerLeft_whiskerRight
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} e) (smallEtaleAdjunctionAb e)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} f') (smallEtaleAdjunctionAb f')
    (TwoSquare.mk _ _ _ _
      ((etaleAbelianDirectImageCompIso'.{u, 0} e g (e ≫ g) rfl).hom ≫
        (etaleAbelianDirectImageCompIso'.{u, 0} h f' (e ≫ g) w.symm).inv))
  refine (smallEtaleBaseChangeAb_eq_mateEquiv_symm_pushforwardCompIso f' g h e w (e ≫ g) rfl
    w.symm).trans (hmate.trans ?_)
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans ?_ (congrArg
    (fun t => Functor.whiskerLeft (etaleAbelianDirectImage.{u, 0} g)
        (smallEtalePullbackAbIsoInverseImage f').hom ≫ t ≫
      Functor.whiskerRight (smallEtalePullbackAbIsoInverseImage e).inv
        (etaleAbelianDirectImage.{u, 0} h)) e3.symm)
  have hc : ∀ {C : Type _} [Category C] {A₀ A₁ A₂ A₃ : C} {a a' : A₀ ⟶ A₁} {m : A₁ ⟶ A₂}
      {b b' : A₂ ⟶ A₃}, a = a' → b = b' → a ≫ m ≫ b = a' ≫ m ≫ b' := by
    intro _ _ _ _ _ _ _ _ _ _ _ ha hb
    rw [ha, hb]
  exact hc (congrArg (Functor.whiskerLeft (etaleAbelianDirectImage.{u, 0} g)) e1)
    (congrArg (fun z => Functor.whiskerRight z (etaleAbelianDirectImage.{u, 0} h)) e2)

end Bridge

end Stacks.EtaleCohomology

end
