module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportIntegralCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafExcisionIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicTowerWeights
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality

/-!
# `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ) ≅ Hⁱ_c(Y_k̄, φ_* F ⊗ ℚ_ℓ)` along a finite morphism

Let `j_X : X ⟶ X̄` and `j_Y : Y ⟶ Ȳ` be compactifications over a finite field `k`, and let
`φ : X ⟶ Y` be the restriction of an integral morphism `φ̄ : X̄ ⟶ Ȳ` over `k` with
`X = X̄ ×_Ȳ Y` (so `φ` is integral, for instance finite; then `φ_! = φ_*`). For an ℓ-adic sheaf
`F` on `X` and an ℓ-adic sheaf `G` on `Y` whose tower of levels is the direct image of the tower
of `F`, `Gₙ ≅ φ_* Fₙ` compatibly with the transition maps,

`Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ) ≅ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`,

and the isomorphism carries the geometric Frobenius `π_Y^*` to `π_X^*`. In particular the two
Frobenius endomorphisms have the same characteristic polynomial. No hypothesis on the dimension is
made.

This is the step of the reduction of the weight bound of Weil II
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH); Deligne, Weil II 3.3) in which a curve
finite étale over an open of `𝔸¹` is replaced by that open, and in which, in the induction on the
dimension, a variety finite over an open of `𝔸ⁿ` is replaced by that open. It is the levelwise
`RΓ_c(X_k̄, K) ≅ RΓ_c(Y_k̄, φ_* K)` of
`Stacks.EtaleCohomology.compactSupportFrobeniusCohomologyIntegralIso`, read on the towers of levels
(`Stacks.EtaleCohomology.LAdicSheaf.padicTower`) and passed to the rational limit.

## Main definitions

* `Stacks.EtaleCohomology.compactSupportFrobeniusFunctorIntegralIso`: `RΓ_c(X_k̄, -) ≅
  RΓ_c(Y_k̄, φ_* -)` as a natural isomorphism of functors of bounded below complexes.
* `Stacks.EtaleCohomology.compactSupportSheafCohomologyIntegralIso`: `Hⁱ_c(X_k̄, -) ≅
  Hⁱ_c(Y_k̄, φ_* -)` on sheaves.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso`:
  `Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ) ≅ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` for `G = φ_* F` levelwise.
* `AlgebraicGeometry.SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso`: the direct image on the
  small étale sites of a big étale site is Mathlib's direct image, through
  `AlgebraicGeometry.SmallEtale.sheafEquiv`.
* `Stacks.EtaleCohomology.LAdicSheaf.padicTowerDirectImageIso`: if the levels of `G` are the direct
  images of the levels of `F` on the small étale sites of the big étale site, compatibly with the
  transition maps, then the tower of `G` is the direct image of the tower of `F`; this is the
  hypothesis of the comparison above.

## Main results

All in the namespace `Stacks.EtaleCohomology.LAdicSheaf`:

* `rationalGeometricCompactlySupportedCohomologyIntegralIso_hom_frobenius`: the isomorphism
  intertwines the geometric Frobenius endomorphisms.
* `charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_integral`: their characteristic
  polynomials agree.
* `isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff_of_integral`:
  their weight bounds agree.

## References

* [Stacks Project, Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)
* P. Deligne, *La conjecture de Weil II*, Publ. Math. IHÉS 52 (1980), 3.3.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize

/-! ### `RΓ_c` and `Hⁱ_c` along an integral morphism of compactifications, as functors -/

section Functor

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {U V : Scheme.{u}}
  (fU : U ⟶ Spec (.of k)) (jU : CompactificationOf (Over.mk fU))
  (fV : V ⟶ Spec (.of k)) (jV : CompactificationOf (Over.mk fV))
  (φ : V ⟶ U) (φb : jV.space ⟶ jU.space) [IsIntegralHom φb] (hφb : φb ≫ jU.toBase = jV.toBase)
  (sq : IsPullback φ jV.immersion jU.immersion φb) (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`RΓ_c(V_k̄, -) ≅ RΓ_c(U_k̄, φ_* -)`**, as a natural isomorphism of functors of the bounded
below complex on `V`, for the restriction `φ : V ⟶ U` of an integral morphism of compactifications
with `V = V̄ ×_Ū U`. -/
public def compactSupportFrobeniusFunctorIntegralIso :
    compactSupportFrobeniusFunctor.{u, 0} Λ fV jV kbar ≅
      (etaleModuleDirectImage.{u, 0} Λ φ).mapCochainComplexPlus ⋙
        compactSupportFrobeniusFunctor.{u, 0} Λ fU jU kbar :=
  NatIso.ofComponents (compactSupportFrobeniusCohomologyIntegralIso Λ fU jU fV jV φ φb hφb sq kbar)
    (fun x => compactSupportFrobeniusCohomologyIntegralIso_hom_naturality Λ fU jU fV jV φ φb hφb sq
      kbar x)

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The natural isomorphism `RΓ_c(V_k̄, -) ≅ RΓ_c(U_k̄, φ_* -)` carries the canonical Frobenius of
`V` to that of `U`. -/
public theorem compactSupportFrobeniusFunctorIntegralIso_hom_frobenius :
    canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ fV jV kbar p q hcard ≫
        (compactSupportFrobeniusFunctorIntegralIso Λ fU jU fV jV φ φb hφb sq kbar).hom =
      (compactSupportFrobeniusFunctorIntegralIso Λ fU jU fV jV φ φb hφb sq kbar).hom ≫
        Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ φ).mapCochainComplexPlus
          (canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ fU jU kbar p q hcard) := by
  ext K : 2
  exact compactSupportFrobeniusCohomologyIntegralIso_hom_frobenius Λ fU jU fV jV φ φb hφb sq kbar
    p q hcard K

/-- **`Hⁱ_c(V_k̄, G) ≅ Hⁱ_c(U_k̄, φ_* G)`**, naturally in the sheaf `G` of `Λ`-modules on `V`. -/
public def compactSupportSheafCohomologyIntegralIso (i : ℤ) :
    compactSupportSheafCohomology Λ fV jV kbar i ≅
      etaleModuleDirectImage.{u, 0} Λ φ ⋙ compactSupportSheafCohomology Λ fU jU kbar i :=
  singlePlusHomologyIso (etaleModuleDirectImage.{u, 0} Λ φ) _ _
    (compactSupportFrobeniusFunctorIntegralIso Λ fU jU fV jV φ φb hφb sq kbar) i

/-- The identification `Hⁱ_c(V_k̄, -) ≅ Hⁱ_c(U_k̄, φ_* -)` carries `π_V^*` to `π_U^*`. -/
public theorem compactSupportSheafCohomologyIntegralIso_hom_frobenius (i : ℤ) :
    compactSupportSheafFrobenius Λ fV jV kbar p q hcard i ≫
        (compactSupportSheafCohomologyIntegralIso Λ fU jU fV jV φ φb hφb sq kbar i).hom =
      (compactSupportSheafCohomologyIntegralIso Λ fU jU fV jV φ φb hφb sq kbar i).hom ≫
        Functor.whiskerLeft (etaleModuleDirectImage.{u, 0} Λ φ)
          (compactSupportSheafFrobenius Λ fU jU kbar p q hcard i) :=
  singlePlusHomologyIso_hom_comm _ _ _ _ _ _
    (compactSupportFrobeniusFunctorIntegralIso_hom_frobenius Λ fU jU fV jV φ φb hφb sq kbar p q
      hcard) i

end Functor

/-! ### The bounded direct image, read on Mathlib's small étale site -/

section Bounded

universe v' u'

variable (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (A : Type u') [Category.{v'} A]
  [HasLimitsOfSize.{u, u} A]

/-- **The direct image of the bounded small étale site is Mathlib's**, read through the
equivalences `AlgebraicGeometry.SmallEtale.sheafEquiv` of the two presentations of the small étale
sites: the conjugate of `AlgebraicGeometry.SmallEtale.toEtaleSitePushforwardBaseChangeIso`. -/
public def _root_.AlgebraicGeometry.SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso :
    B.smallPushforward f A ⋙ (SmallEtale.sheafEquiv B S.1 S.property A).functor ≅
      (SmallEtale.sheafEquiv B T.1 T.property A).functor ⋙
        (Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map f)).sheafPushforwardContinuous
          A S.obj.smallEtaleTopology T.obj.smallEtaleTopology :=
  Functor.isoWhiskerRight
      ((Functor.leftUnitor _).symm ≪≫
        Functor.isoWhiskerRight (SmallEtale.sheafEquiv B T.1 T.property A).unitIso _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (SmallEtale.toEtaleSitePushforwardBaseChangeIso B f A).symm ≪≫
        (Functor.associator _ _ _).symm) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (SmallEtale.sheafEquiv B S.1 S.property A).counitIso ≪≫
    Functor.rightUnitor _

end Bounded

/-! ### The tower of levels of a direct image -/

section Tower

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X Y : B.Scheme} [IsNoetherian X.1] [IsNoetherian Y.1] (π : X ⟶ Y)
  (F : LAdicSheaf B X ℓ) (G : LAdicSheaf B Y ℓ)
  (ε : ∀ n, LAdicSheaf.padicLevel B Y ℓ G n ≅
    (B.smallPushforward π (ModuleCat.{u + 1} ℤ_[ℓ])).obj (LAdicSheaf.padicLevel B X ℓ F n))
  (hε : ∀ n, LAdicSheaf.padicTransition B Y ℓ G n ≫ (ε n).hom =
    (ε (n + 1)).hom ≫ (B.smallPushforward π (ModuleCat.{u + 1} ℤ_[ℓ])).map
      (LAdicSheaf.padicTransition B X ℓ F n))

/-- The components of `LAdicSheaf.padicTowerDirectImageIso`. -/
public abbrev LAdicSheaf.padicTowerDirectImageApp (n : ℕ) :
    (LAdicSheaf.padicTower B Y ℓ G).obj (op n) ⟶
      (LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map π)).obj
        (op n) :=
  (SmallEtale.sheafEquiv B Y.1 Y.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map (ε n).hom ≫
    (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B π (ModuleCat.{u + 1} ℤ_[ℓ])).hom.app
      (LAdicSheaf.padicLevel B X ℓ F n)

include hε in
/-- The components of `LAdicSheaf.padicTowerDirectImageApp` commute with the transition maps. -/
public theorem LAdicSheaf.padicTowerDirectImageApp_naturality (n : ℕ) :
    (LAdicSheaf.padicTower B Y ℓ G).map (homOfLE (n.le_add_right 1)).op ≫
        LAdicSheaf.padicTowerDirectImageApp B ℓ π F G ε n =
      LAdicSheaf.padicTowerDirectImageApp B ℓ π F G ε (n + 1) ≫
        (LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleDirectImage.{u, 0} ℤ_[ℓ]
          (B.inclusion.map π)).map (homOfLE (n.le_add_right 1)).op := by
  have key : (SmallEtale.sheafEquiv B Y.1 Y.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (LAdicSheaf.padicTransition B Y ℓ G n) ≫
      (SmallEtale.sheafEquiv B Y.1 Y.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map (ε n).hom ≫
      (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B π (ModuleCat.{u + 1} ℤ_[ℓ])).hom.app
        (LAdicSheaf.padicLevel B X ℓ F n) =
      (SmallEtale.sheafEquiv B Y.1 Y.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
        (ε (n + 1)).hom ≫
      (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B π (ModuleCat.{u + 1} ℤ_[ℓ])).hom.app
        (LAdicSheaf.padicLevel B X ℓ F (n + 1)) ≫
      ((Stacks.EtaleCohomology.smallEtaleBaseChange (B.inclusion.map π)).sheafPushforwardContinuous
          (ModuleCat.{u + 1} ℤ_[ℓ]) Y.obj.smallEtaleTopology X.obj.smallEtaleTopology).map
        ((SmallEtale.sheafEquiv B X.1 X.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.map
          (LAdicSheaf.padicTransition B X ℓ F n)) := by
    rw [← Functor.map_comp_assoc, hε n, Functor.map_comp, Category.assoc]
    congr 1
    exact (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B π
      (ModuleCat.{u + 1} ℤ_[ℓ])).hom.naturality (LAdicSheaf.padicTransition B X ℓ F n)
  rw [LAdicSheaf.padicTower_map_succ, Functor.comp_map, LAdicSheaf.padicTower_map_succ]
  exact key.trans (Category.assoc _ _ _).symm

/-- The comparison of the tower of levels of `G` with the direct image of that of `F`. -/
public def LAdicSheaf.padicTowerDirectImageHom :
    LAdicSheaf.padicTower B Y ℓ G ⟶
      LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map π) :=
  NatTrans.ofOpSequence (LAdicSheaf.padicTowerDirectImageApp B ℓ π F G ε)
    (LAdicSheaf.padicTowerDirectImageApp_naturality B ℓ π F G ε hε)

/-- **The tower of levels of a direct image is the direct image of the tower of levels**: if the
levels of an ℓ-adic sheaf `G` on `Y` are, compatibly with the transition maps, the direct images
along `π : X ⟶ Y` of the levels of an ℓ-adic sheaf `F` on `X`, on the small étale sites of the
big étale site, then the same holds for the towers on Mathlib's small étale sites. -/
public def LAdicSheaf.padicTowerDirectImageIso :
    LAdicSheaf.padicTower B Y ℓ G ≅
      LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map π) :=
  NatIso.ofComponents
    (fun n => (SmallEtale.sheafEquiv B Y.1 Y.property (ModuleCat.{u + 1} ℤ_[ℓ])).functor.mapIso
        (ε n.unop) ≪≫
      (SmallEtale.sheafEquivFunctorPushforwardBaseChangeIso B π (ModuleCat.{u + 1} ℤ_[ℓ])).app
        (LAdicSheaf.padicLevel B X ℓ F n.unop))
    (fun f => (LAdicSheaf.padicTowerDirectImageHom B ℓ π F G ε hε).naturality f)

end Tower

/-! ### ℓ-adic sheaves -/

section LAdic

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X Y : B.Scheme} [IsNoetherian X.1] [IsNoetherian Y.1]
  {k : Type u} [Field k] [Fintype k]
  (fX : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fX] [QuasiCompact fX] [IsSeparated fX]
  (jX : CompactificationOf (Over.mk fX))
  (fY : Y.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fY] [QuasiCompact fY] [IsSeparated fY]
  (jY : CompactificationOf (Over.mk fY))
  (φ : X.1 ⟶ Y.1) (φb : jX.space ⟶ jY.space) [IsIntegralHom φb] (hφb : φb ≫ jY.toBase = jX.toBase)
  (sq : IsPullback φ jX.immersion jY.immersion φb) (kbar : Type u) [Field kbar] [Algebra k kbar]
  (F : LAdicSheaf B X ℓ) (G : LAdicSheaf B Y ℓ)
  (e : LAdicSheaf.padicTower B Y ℓ G ≅
    LAdicSheaf.padicTower B X ℓ F ⋙ etaleModuleDirectImage.{u, 0} ℤ_[ℓ] φ)

/-- **The inverse systems `n ↦ Hⁱ_c(Y_k̄, Gₙ)` and `n ↦ Hⁱ_c(X_k̄, Fₙ)` are isomorphic** when the
tower of levels of `G` is the direct image along `φ` of the tower of levels of `F`. -/
public def LAdicSheaf.geometricCompactlySupportedCohomologySystemIntegralIso (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystem B Y ℓ fY jY kbar G i ≅
      LAdicSheaf.geometricCompactlySupportedCohomologySystem B X ℓ fX jX kbar F i :=
  (LAdicSheaf.padicTowerCohomologyIso B Y ℓ fY jY kbar G i).symm ≪≫
    Functor.isoWhiskerRight e (compactSupportSheafCohomology ℤ_[ℓ] fY jY kbar i) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (LAdicSheaf.padicTower B X ℓ F)
      (compactSupportSheafCohomologyIntegralIso ℤ_[ℓ] fY jY fX jX φ φb hφb sq kbar i).symm ≪≫
    LAdicSheaf.padicTowerCohomologyIso B X ℓ fX jX kbar F i

/-- **`Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ) ≅ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`** when the tower of levels of `G` is the direct
image along `φ` of the tower of levels of `F`, for the restriction `φ` of an integral morphism of
compactifications. -/
public def LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso (i : ℤ) :
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar G i ≅
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ fX jX kbar F i :=
  (rationalLim.{u + 1} (ℓ := ℓ)).mapIso
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemIntegralIso B ℓ fX jX fY jY φ φb hφb sq
      kbar F G e i)

include φ φb hφb sq e in
/-- `Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ)` is finite dimensional when `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is. -/
public theorem LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_integral
    (i : ℤ) [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ fX jX kbar F i)] :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar G i) :=
  LinearEquiv.finiteDimensional
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso B ℓ fX jX fY jY φ φb hφb
      sq kbar F G e i).symm.toLinearEquiv

include φ φb hφb sq e in
/-- `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` is finite dimensional when `Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ)` is. -/
public theorem LAdicSheaf.finiteDimensional_rationalGeometricCompactlySupportedCohomology_of_integral'
    (i : ℤ) [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar G i)] :
    FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ fX jX kbar F i) :=
  LinearEquiv.finiteDimensional
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso B ℓ fX jX fY jY φ φb hφb
      sq kbar F G e i).toLinearEquiv

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The isomorphism of inverse systems intertwines the geometric Frobenius of `Y` and of `X`. -/
public theorem LAdicSheaf.geometricCompactlySupportedCohomologySystemIntegralIso_hom_frobenius
    (i : ℤ) :
    LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B Y ℓ fY jY kbar G i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] fY jY kbar p q hcard) ≫
      (LAdicSheaf.geometricCompactlySupportedCohomologySystemIntegralIso B ℓ fX jX fY jY φ φb hφb
        sq kbar F G e i).hom =
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemIntegralIso B ℓ fX jX fY jY φ φb hφb
        sq kbar F G e i).hom ≫
      LAdicSheaf.geometricCompactlySupportedCohomologySystemPullback B X ℓ fX jX kbar F i
        (canonicalCompactSupportFrobeniusNatTrans.{u, 0} ℤ_[ℓ] fX jX kbar p q hcard) := by
  have hY := (CommSq.vert_inv
    ⟨LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B Y ℓ fY jY kbar p q hcard G i⟩).w
  have hX := LAdicSheaf.padicTowerCohomologyIso_hom_frobenius B X ℓ fX jX kbar p q hcard F i
  have hmid : Functor.whiskerLeft (LAdicSheaf.padicTower B Y ℓ G)
        (compactSupportSheafFrobenius ℤ_[ℓ] fY jY kbar p q hcard i) ≫
      (Functor.isoWhiskerRight e (compactSupportSheafCohomology ℤ_[ℓ] fY jY kbar i)).hom ≫
      (Functor.associator _ _ _).hom ≫
      (Functor.isoWhiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafCohomologyIntegralIso ℤ_[ℓ] fY jY fX jX φ φb hφb sq kbar i).symm).hom =
      (Functor.isoWhiskerRight e (compactSupportSheafCohomology ℤ_[ℓ] fY jY kbar i)).hom ≫
      (Functor.associator _ _ _).hom ≫
      (Functor.isoWhiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafCohomologyIntegralIso ℤ_[ℓ] fY jY fX jX φ φb hφb sq kbar i).symm).hom ≫
      Functor.whiskerLeft (LAdicSheaf.padicTower B X ℓ F)
        (compactSupportSheafFrobenius ℤ_[ℓ] fX jX kbar p q hcard i) := by
    ext n : 2
    have he := (compactSupportSheafFrobenius ℤ_[ℓ] fY jY kbar p q hcard i).naturality (e.hom.app n)
    have hI := congrArg (fun t => NatTrans.app t ((LAdicSheaf.padicTower B X ℓ F).obj n))
      (compactSupportSheafCohomologyIntegralIso_hom_frobenius ℤ_[ℓ] fY jY fX jX φ φb hφb sq kbar p
        q hcard i)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hI
    have hI' := (CommSq.vert_inv
      (g := (compactSupportSheafCohomologyIntegralIso ℤ_[ℓ] fY jY fX jX φ φb hφb sq kbar
        i).app ((LAdicSheaf.padicTower B X ℓ F).obj n))
      (h := (compactSupportSheafCohomologyIntegralIso ℤ_[ℓ] fY jY fX jX φ φb hφb sq kbar
        i).app ((LAdicSheaf.padicTower B X ℓ F).obj n)) ⟨hI⟩).w
    simp only [Iso.app_inv] at hI'
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.associator_hom_app,
      Iso.symm_hom, Category.id_comp]
    simp only [Functor.whiskerRight_app] at hI'
    have he' : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).map
          ((canonicalCompactSupportFrobeniusNatTrans ℤ_[ℓ] fY jY kbar p q hcard).app
            ((sheafSingleComplex ℤ_[ℓ]).obj ((LAdicSheaf.padicTower B Y ℓ G).obj n))) ≫
          (compactSupportSheafCohomology ℤ_[ℓ] fY jY kbar i).map (e.hom.app n) =
        (compactSupportSheafCohomology ℤ_[ℓ] fY jY kbar i).map (e.hom.app n) ≫
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} ℤ_[ℓ]) i).map
            ((canonicalCompactSupportFrobeniusNatTrans ℤ_[ℓ] fY jY kbar p q hcard).app
              ((sheafSingleComplex ℤ_[ℓ]).obj ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] φ).obj
                ((LAdicSheaf.padicTower B X ℓ F).obj n)))) := he.symm
    rw [← Category.assoc, he', Category.assoc, hI']
  simp only [LAdicSheaf.geometricCompactlySupportedCohomologySystemIntegralIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc]
  rw [reassoc_of% hY, reassoc_of% hmid, hX]

/-- **The isomorphism `Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ) ≅ Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` carries `π_Y^*` to `π_X^*`.** -/
public theorem LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso_hom_frobenius
    (i : ℤ) :
    LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Y ℓ fY jY kbar p q hcard G i ≫
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso B ℓ fX jX fY jY φ φb
        hφb sq kbar F G e i).hom =
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso B ℓ fX jX fY jY φ φb hφb
        sq kbar F G e i).hom ≫
      LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ fX jX kbar p q hcard F i := by
  have h := congrArg (rationalLim.{u + 1} (ℓ := ℓ)).map
    (LAdicSheaf.geometricCompactlySupportedCohomologySystemIntegralIso_hom_frobenius B ℓ fX jX fY
      jY φ φb hφb sq kbar F G e p q hcard i)
  simp only [Functor.map_comp] at h
  exact h

include φ φb hφb sq e in
/-- **The geometric Frobenius endomorphisms of `Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ)` and `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` have
the same characteristic polynomial.** -/
public theorem LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_integral
    (i : ℤ) [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar G i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ fX jX kbar F i)] :
    (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Y ℓ fY jY kbar p q hcard G
        i).hom.charpoly =
      (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ fX jX kbar p q hcard F
        i).hom.charpoly := by
  set E := LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso B ℓ fX jX fY jY φ φb
    hφb sq kbar F G e i
  rw [← E.toLinearEquiv.charpoly_conj]
  congr 1
  ext v
  have h := congrArg (fun t => t.hom (E.toLinearEquiv.symm v))
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyIntegralIso_hom_frobenius B ℓ fX jX fY
      jY φ φb hφb sq kbar F G e p q hcard i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
  exact h.trans (congrArg _ (E.toLinearEquiv.apply_symm_apply v))

include φ φb hφb sq e in
/-- **The weight bound on `Hⁱ_c(Y_k̄, G ⊗ ℚ_ℓ)` is the weight bound on `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)`.** -/
public theorem LAdicSheaf.isCharpolyNormMixedOfWeightLE_rationalGeometricCompactlySupportedFrobenius_iff_of_integral
    (i : ℤ) [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B Y ℓ fY jY kbar G i)]
    [FiniteDimensional ℚ_[ℓ]
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ fX jX kbar F i)]
    {q' : ℕ} {ι : ℚ_[ℓ] →+* ℂ} {b : ℤ} :
    IsCharpolyNormMixedOfWeightLE q' ι b
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B Y ℓ fY jY kbar p q hcard G
          i).hom ↔
      IsCharpolyNormMixedOfWeightLE q' ι b
        (LAdicSheaf.rationalGeometricCompactlySupportedFrobenius B X ℓ fX jX kbar p q hcard F
          i).hom := by
  unfold IsCharpolyNormMixedOfWeightLE
  rw [LAdicSheaf.charpoly_rationalGeometricCompactlySupportedFrobenius_eq_of_integral B ℓ fX jX fY
    jY φ φb hφb sq kbar F G e p q hcard i]

end LAdic

end Stacks.EtaleCohomology

end
