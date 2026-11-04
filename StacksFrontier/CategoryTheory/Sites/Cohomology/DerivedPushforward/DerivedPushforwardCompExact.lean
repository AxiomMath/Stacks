module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.AdjunctionForRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.Composition
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningDerivedUnitDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedAmplitudeOfDerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor

/-!
# The derived pushforward followed by an exact functor

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let
`Φ : Mod(O_D) ⥤ B` be an exact functor to an abelian category. Then `Rf_*` followed by the
functor `Φ` induces on derived categories is a right derived functor of `f_*` followed by `Φ`:
its comparison map is invertible at K-injective complexes, which over the Grothendieck abelian
`Mod(O_C)` characterizes right derived functors
(`Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective`).

## Main definitions

* `derivedPushforwardCompExactUnit`: the comparison `K(Φ ∘ f_*) ⟶ Φ(Rf_*)`.

## Main results

* `isRightDerivedFunctor_derivedPushforward_comp_mapDerivedCategory`:
  `Φ ∘ Rf_*` is a right derived functor of `Φ ∘ f_*`.
* `isLE_derivedPushforward_obj_of_isDerivedLimit`: `Rf_*` keeps `D^{≤ c}`, with no lower bound,
  on objects whose cohomology satisfies a property `P` along which truncation towers converge.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

universe w w'

attribute [local instance] HasDerivedCategory.standard

variable {X Y : AlgebraicGeometry.RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y)
  {B : Type*} [Category* B] [Abelian B] [HasDerivedCategory B]
  (Φ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤ B) [Φ.Additive]
  [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- The comparison `K(Φ ∘ f_*) ⟶ Φ(Rf_*)` induced by the comparison `derivedPushforwardUnit`
of `Rf_*`. -/
def derivedPushforwardCompExactUnit :
    (f.pushforwardTopos ⋙ Φ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ (derivedPushforward f ⋙ Φ.mapDerivedCategory) :=
  (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ Φ.mapDerivedCategoryFactorsh.symm ≪≫
      (Functor.associator _ _ _).symm).hom ≫
    Functor.whiskerRight (derivedPushforwardUnit f) Φ.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The comparison `K(Φ ∘ f_*) ⟶ Φ(Rf_*)` is invertible at K-injective complexes. -/
theorem isIso_derivedPushforwardCompExactUnit_app_of_isKInjective
    (I : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hI : I.IsKInjective) :
    IsIso ((derivedPushforwardCompExactUnit f Φ).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) := by
  have := isIso_derivedPushforwardUnit_app_of_isKInjective f I hI
  simp only [derivedPushforwardCompExactUnit, NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Φ ∘ Rf_*` is a right derived functor of `Φ ∘ f_*`. -/
theorem isRightDerivedFunctor_derivedPushforward_comp_mapDerivedCategory :
    (derivedPushforward f ⋙ Φ.mapDerivedCategory).IsRightDerivedFunctor
      (derivedPushforwardCompExactUnit f Φ)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) := by
  have := SheafOfModules.isGrothendieckAbelianU.{w, w, w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  exact Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_of_isIso_app_isKInjective
    _ _ _ _ (isIso_derivedPushforwardCompExactUnit_app_of_isKInjective f Φ)

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Rf_*` of `M[n]` lies in degrees `≤ n` as soon as `Rf_*(M[0])` has no cohomology in
positive degrees. -/
theorem isLE_derivedPushforward_singleFunctor_obj
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (h : ∀ p : ℕ, 0 < p → IsZero ((DerivedCategory.homologyFunctor _ (p : ℤ)).obj
      ((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (n : ℤ) : ((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ n).obj M)).IsLE n := by
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f)
    (derivedPushforwardUnit f) (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) ℤ
  have hzero : ((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ 0).obj M)).IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro p hp
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, p = k := ⟨p.toNat, by omega⟩
    exact h k (by omega)
  have hs : (((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ 0).obj M))⟦-n⟧).IsLE
      (n + 0) :=
    DerivedCategory.TStructure.t.isLE_shift _ 0 (-n) (n + 0) (by omega)
  have hs' : DerivedCategory.TStructure.t.IsLE
      ((derivedPushforward f ⋙ shiftFunctor _ (-n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj M)) (n + 0) := hs
  have := DerivedCategory.TStructure.t.isLE_of_iso
    ((((derivedPushforward f).commShiftIso (-n)).app
      ((DerivedCategory.singleFunctor _ 0).obj M)).symm ≪≫
      (derivedPushforward f).mapIso
        (((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).app M)) (n + 0)
  simpa using this

attribute [local instance] Stacks.DerivedLimit.hasProduct_truncGETower

omit [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- `Rf_*` keeps `D^{≤ c}` on objects whose cohomology satisfies `P`, with no lower bound,
given an exact functor `Φ : Mod(O_D) ⥤ Ab` reflecting zero objects such that `Φ ∘ f_*` commutes
with countable products, the vanishing of the higher cohomology of `Rf_*` on modules satisfying
`P`, and the convergence of the truncation towers of objects with cohomology in `P`. -/
theorem isLE_derivedPushforward_obj_of_isDerivedLimit
    [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [HasProductsOfShape ℕ (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (Ψ : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤ AddCommGrpCat.{w'})
    [Ψ.Additive] [PreservesFiniteLimits Ψ] [PreservesFiniteColimits Ψ]
    [PreservesLimitsOfShape (Discrete ℕ) (f.pushforwardTopos ⋙ Ψ)]
    (hΨ : ∀ Z, IsZero (Ψ.obj Z) → IsZero Z)
    (P : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
    (hsingle : ∀ M, P M → ∀ p : ℕ, 0 < p → IsZero ((DerivedCategory.homologyFunctor _ (p : ℤ)).obj
      ((derivedPushforward f).obj ((DerivedCategory.singleFunctor _ 0).obj M))))
    (hlim : ∀ E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      (∀ q : ℤ, P ((DerivedCategory.homologyFunctor _ q).obj E)) →
        IsDerivedLimit (Stacks.DerivedLimit.truncGETower _ E) E)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : ∀ q : ℤ, P ((DerivedCategory.homologyFunctor _ q).obj E)) (c : ℤ) (hc : E.IsLE c) :
    ((derivedPushforward f).obj E).IsLE c := by
  have := SheafOfModules.isGrothendieckAbelianU.{w, w, w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  have := isRightDerivedFunctor_derivedPushforward_comp_mapDerivedCategory f Ψ
  have h := Stacks.DerivedLimit.isLE_rightDerived_obj_of_isLE_of_isDerivedLimit P
    (f.pushforwardTopos ⋙ Ψ) (derivedPushforward f ⋙ Ψ.mapDerivedCategory)
    (derivedPushforwardCompExactUnit f Ψ)
    (fun M hM n ↦ by
      have := isLE_derivedPushforward_singleFunctor_obj f M (hsingle M hM) n
      exact Stacks.Homology.isLE_mapDerivedCategory_obj _ _ n)
    hlim E hE c hc
  have : (Ψ.mapDerivedCategory.obj ((derivedPushforward f).obj E)).IsLE c := h
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact hΨ _ ((DerivedCategory.isZero_of_isLE _ c i hi).of_iso
    ((Ψ.mapDerivedCategoryHomologyIso i).app _).symm)

end Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

end
