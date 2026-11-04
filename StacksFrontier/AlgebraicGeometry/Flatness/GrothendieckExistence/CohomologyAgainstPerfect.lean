module

public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.DerivedLimitObject
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.LevelCohomology
public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.DerivedLimitTransport
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsTensorPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.TensorPerfectRightAdjoint
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedSectionsTensorQCohOrthogonal
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedCategory.Bridge.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology of `K ⊗^L E` against a perfect object

In Situation [Stacks, Tag 0DIB] let `K` be the object of [Stacks, Tag 0DIC]. For a perfect object
`E` of `D(𝒪_X)` the cohomology `M = RΓ(X, K ⊗^L E)` is a pseudo-coherent object of `D(A)` and the
canonical map `M ⊗^L_A A_n ⟶ RΓ(X_n, K_n ⊗^L E|_{X_n})` is an isomorphism in `D(A_n)`
([Stacks, Tag 0DID]).

## Main definitions

* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.cohomology`:
  `M = RΓ(X, K ⊗^L E)`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.cohomologyMap`: the
  canonical map `M ⟶ M_n` of `D(A)`, pull derived global sections back to `X_n` and apply the
  canonical map `K|_{X_n} ⟶ K_n`.
* `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.cohomologyTransition`: the
  transition map `M_{n+1} ⟶ M_n` of `D(A_{n+1})` determined by `φ_n`.

## References

* [Stacks Project, Tag 0DID](https://stacks.math.columbia.edu/tag/0DID)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
* [Stacks Project, Tag 0DIC](https://stacks.math.columbia.edu/tag/0DIC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPullback derivedAdjunction)
open AlgebraicGeometry.LerayOver Stacks.Duality Stacks.Duality.Coherator

universe u

namespace Stacks.Duality.Coherator

variable (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]

/-- **The cone of the coherator counit is right orthogonal to `D_QCoh(𝒪_X)`.** For `L` in
`D(𝒪_X)` complete the counit `ι DQ_X L ⟶ L` of the coherator adjunction to a distinguished triangle
`ι DQ_X L ⟶ L ⟶ Z ⟶`. Every morphism to `Z` from an object with quasi-coherent cohomology vanishes:
post-composition with the counit is bijective on morphisms out of such an object, by the adjunction
and full faithfulness of `ι`, and [Stacks, Tag 0CQQ] applies. -/
theorem hom_eq_zero_of_counit_distTriang (L Z : DerivedCategory X.Modules) (g : L ⟶ Z)
    (h : Z ⟶ ((quasiCoherentι X).obj ((derivedCoherator X).obj L))⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((derivedCoheratorAdjunction X).counit.app L) g h ∈ distTriang _)
    (Q : DerivedCategory X.Modules)
    (hQ : DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf) Q)
    (φ : Q ⟶ Z) : φ = 0 := by
  have hP : Stacks.Triangulated.RightOrthogonal.InvariantUnderAllShifts
      (C := DerivedCategory X.Modules)
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)) :=
    fun n A hA => ⟨_, DerivedCategoryB.derivedCategoryB_shift_mem _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X) n hA,
      ⟨Iso.refl _⟩⟩
  refine ((Stacks.Triangulated.RightOrthogonal.inRightOrthogonal_iff_postcomp_bijective _ hP _
    hT).2 (fun A hA => ?_)) Q hQ φ
  have hb : (fun u : (quasiCoherentι X).obj ⟨A, hA⟩ ⟶
        (quasiCoherentι X).obj ((derivedCoherator X).obj L) =>
          u ≫ (derivedCoheratorAdjunction X).counit.app L) =
      ((derivedCoheratorAdjunction X).homEquiv _ _).symm ∘
        (ObjectProperty.fullyFaithfulι _).homEquiv.symm := by
    funext u
    rw [Function.comp_apply, Adjunction.homEquiv_counit]
    exact (congrArg (· ≫ (derivedCoheratorAdjunction X).counit.app L)
      ((ObjectProperty.fullyFaithfulι _).map_preimage u)).symm
  exact hb ▸ ((derivedCoheratorAdjunction X).homEquiv _ _).symm.bijective.comp
    (ObjectProperty.fullyFaithfulι _).homEquiv.symm.bijective

/-- **A triangulated functor which kills the right orthogonal of `D_QCoh(𝒪_X)` inverts the
coherator counit.** Its image of the cone of `ι DQ_X L ⟶ L` vanishes, by
`Stacks.Duality.Coherator.hom_eq_zero_of_counit_distTriang`. -/
theorem isIso_map_counit_of_isZero {D : Type*} [Category D] [Preadditive D] [HasZeroObject D]
    [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (H : DerivedCategory X.Modules ⥤ D) [H.CommShift ℤ] [H.IsTriangulated]
    (L : DerivedCategory X.Modules)
    (hH : ∀ Z : DerivedCategory X.Modules,
      (∀ Q : DerivedCategory X.Modules, DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf) Q → ∀ φ : Q ⟶ Z, φ = 0) →
      IsZero (H.obj Z)) :
    IsIso (H.map ((derivedCoheratorAdjunction X).counit.app L)) := by
  obtain ⟨Z, g, h, hT⟩ :=
    distinguished_cocone_triangle ((derivedCoheratorAdjunction X).counit.app L)
  exact (Triangle.isZero₃_iff_isIso₁ _ (H.map_distinguished _ hT)).1
    (hH Z (hom_eq_zero_of_counit_distTriang X L Z g h hT))

end Stacks.Duality.Coherator

namespace AlgebraicGeometry.LerayOver

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory ModuleCat.hasDerivedCategory

section TensorSections

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

/-- Derived global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` commute with shifts. -/
instance sections_commShift : (sections f).CommShift ℤ :=
  Functor.IsRightDerivedFunctor.commShift (sections f) (sectionsUnit f) (qis X) ℤ

/-- Derived global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` form a triangulated functor. -/
instance sections_isTriangulated : (sections f).IsTriangulated :=
  Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X.toRingedSpace)
    _ _ _

/-- Derived global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(A)` preserve countable products. -/
instance sections_preservesCountableProducts :
    PreservesLimitsOfShape (Discrete ℕ) (sections f) :=
  ⟨fun {K} => Stacks.Injectives.preservesLimit_discrete_of_isRightDerivedFunctor (baseSections f)
    (sections f) (sectionsUnit f) K⟩

variable (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))

/-- The functor `- ⊗^L E` on `D(𝒪_X)` commutes with shifts. -/
instance tensor_flip_commShift : ((tensor X).flip.obj E).CommShift ℤ :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
    X.toRingedSpace.sheaf).commShift_left E

/-- The functor `- ⊗^L E` on `D(𝒪_X)` is triangulated. -/
instance tensor_flip_isTriangulated : ((tensor X).flip.obj E).IsTriangulated :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.toRingedSpace.sheaf).exact_left E

/-- For perfect `E`, the functor `- ⊗^L E` on `D(𝒪_X)` preserves countable products. -/
theorem tensor_flip_preservesCountableProducts
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E) :
    PreservesLimitsOfShape (Discrete ℕ) ((tensor X).flip.obj E) :=
  (RingedSite.preservesLimitsOfSize_derivedTensor_flip_obj_of_isPerfect.{0, 0}
    (Stacks.SheafOfModules.ringedSite X.sheaf) E
    (Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect X.toRingedSpace E
      ((RingedSpace.isPerfect_iff_perfectComplexes_isPerfect E).1 hE))).preservesLimitsOfShape

end TensorSections

section BaseChange

/-- The base change map of a composite with an isomorphism `res_φ c` is invertible when the base
change map of the first factor is: it is that map followed by `c`. -/
theorem isIso_derivedBaseChangeComparison_comp_map {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) {X : DerivedCategory (ModuleCat.{u} R)} {Y Y' : DerivedCategory (ModuleCat.{u} S)}
    (θ : X ⟶ (ModuleCat.restrictScalars φ).mapDerivedCategory.obj Y) (c : Y ⟶ Y')
    [IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} φ θ)] [IsIso c] :
    IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} φ
      (θ ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map c)) := by
  have h : StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} φ
      (θ ≫ (ModuleCat.restrictScalars φ).mapDerivedCategory.map c) =
        StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} φ θ ≫ c := by
    dsimp only [StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison]
    rw [Adjunction.homEquiv_naturality_right_symm]
  rw [h]
  infer_instance

variable {B C : Type u} [CommRing B] [CommRing C] (χ : B →+* C) {X X' X'' : Scheme.{u}}
  (f' : X' ⟶ Spec (CommRingCat.of B)) (f'' : X'' ⟶ Spec (CommRingCat.of C)) (i : X' ⟶ X)
  (j : X'' ⟶ X') (h : X'' ⟶ X) (hh : j ≫ i = h)
  (wj : j ≫ f' = f'' ≫ Spec.map (CommRingCat.ofHom χ))

/-- **The transition map has invertible base change map** when the pullback of derived global
sections along `j` has, at `K' ⊗^L Li^* E`, and `φ : Lj^* K' ⟶ K''` is invertible: the remaining
factors are invertible maps of derived global sections ([Stacks, Tag 079U] and [Stacks, Tag 0D5S]
for the composite of derived pullbacks). -/
theorem isIso_derivedBaseChangeComparison_tensorTransitionMap
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))
    (K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)))
    (K'' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X''.toRingedSpace)))
    (φ : (derivedPullback j.toLRSHom.toShHom).obj K' ⟶ K'') [IsIso φ]
    (hθ : IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} χ
      (pullbackSectionsMap χ f' f'' j wj
        (((tensor X').obj K').obj ((derivedPullback i.toLRSHom.toShHom).obj E))))) :
    IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u} χ
      (tensorTransitionMap χ f' f'' i j h hh wj E K' K'' φ)) := by
  have : IsIso (pullbackCompMap i j h hh E) := by
    subst hh
    rw [pullbackCompMap_rfl]
    exact Iso.isIso_hom ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      j.toLRSHom.toShHom i.toLRSHom.toShHom).app E)
  have h₁ := @isIso_derivedBaseChangeComparison_comp_map _ _ _ _ χ _ _ _
    (pullbackSectionsMap χ f' f'' j wj
      (((tensor X').obj K').obj ((derivedPullback i.toLRSHom.toShHom).obj E)))
    ((sections f'').map (pullbackTensorHom j K' ((derivedPullback i.toLRSHom.toShHom).obj E) ≫
      ((tensor X'').map φ).app
        ((derivedPullback j.toLRSHom.toShHom).obj ((derivedPullback i.toLRSHom.toShHom).obj E))))
    hθ inferInstance
  exact @isIso_derivedBaseChangeComparison_comp_map _ _ _ _ χ _ _ _ _
    ((sections f'').map (((tensor X'').obj K'').map (pullbackCompMap i j h hh E))) h₁
    inferInstance

end BaseChange

end AlgebraicGeometry.LerayOver

namespace AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory ModuleCat.hasDerivedCategory

variable (S : DerivedExistenceSituation.{u})

/-- The projection `A ⟶ A_n` out of the inverse-limit ring factors through `A_{n+1}`. -/
theorem limit_π_hom_eq_transition_comp (n : ℕ) :
    (limit.π S.system (op n)).hom = (S.system.map (homOfLE (Nat.le_succ n)).op).hom.comp
        (limit.π S.system (op (n + 1))).hom :=
  (congrArg CommRingCat.Hom.hom (limit.w S.system (homOfLE (Nat.le_succ n)).op)).symm

/-- The square `X_n ⟶ X`, `X_n ⟶ Spec A_n` over `Spec A_n ⟶ Spec A`. -/
theorem levelProjection_w (n : ℕ) :
    schemeProjection S.system S.X n ≫ S.X.hom =
      levelStructure S.system S.X n ≫ Spec.map (CommRingCat.ofHom (limit.π S.system (op n)).hom) :=
  pullback.condition

/-- The square `X_n ⟶ X_{n+1}`, `X_n ⟶ Spec A_n` over `Spec A_n ⟶ Spec A_{n+1}`. -/
theorem levelTransition_w (n : ℕ) :
    S.transitionScheme n ≫ levelStructure S.system S.X (n + 1) =
      levelStructure S.system S.X n ≫ Spec.map
          (CommRingCat.ofHom (S.system.map (homOfLE (Nat.le_succ n)).op).hom) :=
  S.transition_snd n

variable (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)))

/-- **`M = RΓ(X, K ⊗^L E)`**, an object of `D(A)`, for `K` the object of [Stacks, Tag 0DIC]. -/
abbrev cohomology : DerivedCategory (ModuleCat.{u} ↑(limit S.system)) :=
  (derivedGlobalSectionsOver S.X.hom).obj (((tensor S.X.left).obj S.limitObject).obj E)

/-- **The canonical map `M ⟶ M_n`** of `D(A)`: pull `RΓ(X, K ⊗^L E)` back to `X_n`, identify
`(K ⊗^L E)|_{X_n}` with `K|_{X_n} ⊗^L E|_{X_n}` and apply the canonical map `K|_{X_n} ⟶ K_n`
adjoint to the projection `K ⟶ R(i_n)_* K_n`. Its adjoint `M ⊗^L_A A_n ⟶ M_n` is the canonical
isomorphism of [Stacks, Tag 0DID]. -/
def cohomologyMap (n : ℕ) :
    S.cohomology E ⟶
      (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
        (S.levelCohomology E n) :=
  tensorPullbackMap (limit.π S.system (op n)).hom S.X.hom (levelStructure S.system S.X n)
    (schemeProjection S.system S.X n) (S.levelProjection_w n) E S.limitObject (S.K n)
    (((derivedAdjunction (S.levelInclusion n)).homEquiv _ _).symm (S.limitProjection n))

/-- **The transition map `M_{n+1} ⟶ M_n`** of `D(A_{n+1})` determined by `φ_n`. -/
def cohomologyTransition (n : ℕ) :
    S.levelCohomology E (n + 1) ⟶
      (ModuleCat.restrictScalars
          (S.system.map (homOfLE (Nat.le_succ n)).op).hom).mapDerivedCategory.obj
        (S.levelCohomology E n) :=
  tensorTransitionMap (S.system.map (homOfLE (Nat.le_succ n)).op).hom
      (levelStructure S.system S.X (n + 1))
    (levelStructure S.system S.X n) (schemeProjection S.system S.X (n + 1)) (S.transitionScheme n)
    (schemeProjection S.system S.X n) (S.transition_fst n) (S.levelTransition_w n) E
    (S.K (n + 1)) (S.K n) (S.φ n)

/-! ### The tower of cohomologies -/

/-- The comparison of the standard model of `D(𝒪_X)`, at which the situation is given, with the
locally small model, at which the coherator and the derived limit of [Stacks, Tag 0DIC] live. -/
abbrev modelComparison :=
  StacksDraft.DerivedModel.modelEquiv (HasDerivedCategory.standard S.X.left.Modules)
    (Scheme.Modules.hasDerivedCategory S.X.left)

/-- `RΓ(X, - ⊗^L E) : D(𝒪_X) ⥤ D(A)`. -/
abbrev tensorSections :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)) ⥤
      DerivedCategory (ModuleCat.{u} ↑(limit S.system)) :=
  (tensor S.X.left).flip.obj E ⋙ sections S.X.hom

/-- The map `RΓ(X, R(iₙ)_* Kₙ ⊗^L E) ⟶ RΓ(Xₙ, Kₙ ⊗^L E|_{Xₙ})` of `D(A)`: pull back to `Xₙ` and
apply the counit `L(iₙ)^* R(iₙ)_* Kₙ ⟶ Kₙ`. It is invertible for perfect `E`
(`AlgebraicGeometry.LerayOver.isIso_tensorPullbackMap_counit`, [Stacks, Tag 0B54]). -/
def towerSectionsMap (n : ℕ) :
    (S.tensorSections E).obj ((derivedPushforward (S.levelInclusion n)).obj (S.K n)) ⟶
      (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
        (S.levelCohomology E n) :=
  tensorPullbackMap (limit.π S.system (op n)).hom S.X.hom (levelStructure S.system S.X n)
    (schemeProjection S.system S.X n) (S.levelProjection_w n) E
    ((derivedPushforward (S.levelInclusion n)).obj (S.K n)) (S.K n)
    ((derivedAdjunction (S.levelInclusion n)).counit.app (S.K n))

/-- The transition `res_{A_{n+1}}(M_{n+1}) ⟶ res_{A_n}(M_n)` of `D(A)` of the system to which
[Stacks, Tag 0CQF] is applied. -/
def cohomologyTransitionRestricted (n : ℕ) :
    (ModuleCat.restrictScalars (limit.π S.system (op (n + 1))).hom).mapDerivedCategory.obj
        (S.levelCohomology E (n + 1)) ⟶
      (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
        (S.levelCohomology E n) :=
  (ModuleCat.restrictScalars (limit.π S.system (op (n + 1))).hom).mapDerivedCategory.map
      (S.cohomologyTransition E n) ≫
    (StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp.{u, u}
        (limit.π S.system (op (n + 1))).hom
      (S.system.map (homOfLE (Nat.le_succ n)).op).hom (limit.π S.system (op n)).hom
          (S.limit_π_hom_eq_transition_comp n)).hom.app
        (S.levelCohomology E n)

/-- `RΓ(X, g ⊗^L E)` followed by `towerSectionsMap` is the map determined by the adjoint of `g`. -/
private theorem tensorSections_map_comp_towerSectionsMap (n : ℕ)
    {G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace))}
    (g : G ⟶ (derivedPushforward (S.levelInclusion n)).obj (S.K n)) :
    (S.tensorSections E).map g ≫ S.towerSectionsMap E n =
      tensorPullbackMap (limit.π S.system (op n)).hom S.X.hom (levelStructure S.system S.X n)
        (schemeProjection S.system S.X n) (S.levelProjection_w n) E G (S.K n)
        (((derivedAdjunction (S.levelInclusion n)).homEquiv _ _).symm g) :=
  (tensorPullbackMap_naturality (limit.π S.system (op n)).hom S.X.hom
      (levelStructure S.system S.X n)
    (schemeProjection S.system S.X n) (S.levelProjection_w n) E g (S.K n)
    ((derivedAdjunction (S.levelInclusion n)).counit.app (S.K n))).trans
      (congrArg (fun β => tensorPullbackMap (limit.π S.system (op n)).hom S.X.hom
        (levelStructure S.system S.X n) (schemeProjection S.system S.X n) (S.levelProjection_w n) E
        G (S.K n) β) (Adjunction.homEquiv_counit _ _ _ _).symm)

/-- The maps `S.towerSectionsMap E n` are compatible with the transition maps of the tower and
`S.cohomologyTransitionRestricted E n`. -/
theorem towerSectionsMap_transition (n : ℕ) :
    (S.tensorSections E).map (S.towerTransition n) ≫ S.towerSectionsMap E n =
      S.towerSectionsMap E (n + 1) ≫ S.cohomologyTransitionRestricted E n := by
  have h := tensorPullbackMap_comp (limit.π S.system (op (n + 1))).hom
      (S.system.map (homOfLE (Nat.le_succ n)).op).hom
    (limit.π S.system (op n)).hom (S.limit_π_hom_eq_transition_comp n) S.X.hom
        (levelStructure S.system S.X (n + 1))
    (levelStructure S.system S.X n) (schemeProjection S.system S.X (n + 1)) (S.transitionScheme n)
    (schemeProjection S.system S.X n) (S.transition_fst n) (S.levelProjection_w (n + 1))
    (S.levelTransition_w n) (S.levelProjection_w n) E
    ((derivedPushforward (S.levelInclusion (n + 1))).obj (S.K (n + 1))) (S.K (n + 1)) (S.K n)
    (S.φ n) (𝟙 _)
  have e₁ := S.tensorSections_map_comp_towerSectionsMap E (n + 1) (𝟙 _)
  rw [(S.tensorSections E).map_id, Category.id_comp] at e₁
  rw [← Category.id_comp (S.towerTransition n)]
  exact (S.tensorSections_map_comp_towerSectionsMap E n _).trans
    (h.symm.trans (congrArg (· ≫ _) e₁.symm))

end AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

/-! ### The projections, at the locally small model -/

namespace AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

variable (S : DerivedExistenceSituation.{u})

/-- The counit `ι DQ_X(R lim Kₙ) ⟶ R lim Kₙ` of the coherator adjunction, at the locally small
model. -/
abbrev coheratorCounit : (quasiCoherentι S.X.left).obj S.coheratorLimit ⟶ S.derivedLimit :=
  (derivedCoheratorAdjunction S.X.left).counit.app S.derivedLimit

/-- The projection `K ⟶ R(iₙ)_* Kₙ` is the image of `ι DQ_X(R lim Kₙ) ⟶ R lim Kₙ ⟶ R(iₙ)_* Kₙ`
under the comparison of models, followed by the unit of the comparison. -/
theorem limitProjection_eq (n : ℕ) :
    S.limitProjection n = S.modelComparison.inverse.map (S.coheratorCounit ≫ S.derivedLimitπ n) ≫
      S.modelComparison.unitIso.inv.app (S.tower.obj (op n)) :=
  Adjunction.homEquiv_counit _ _ _ _

end AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

namespace AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] SheafOfModules.hasDerivedCategory
  AlgebraicGeometry.Scheme.Modules.hasDerivedCategory ModuleCat.hasDerivedCategory

variable (S : DerivedExistenceSituation.{u})
  (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)))

/-- **The canonical map `M ⟶ M_n` factors through `RΓ(X, R(iₙ)_* Kₙ ⊗^L E)`**: it is
`RΓ(X, πₙ ⊗ 1)` followed by
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.towerSectionsMap`. -/
theorem tensorSections_map_limitProjection_comp_towerSectionsMap (n : ℕ) :
    (S.tensorSections E).map (S.limitProjection n) ≫ S.towerSectionsMap E n =
      S.cohomologyMap E n :=
  S.tensorSections_map_comp_towerSectionsMap E n _

/-- `D(A)` has countable products ([Stacks, Tag 07KC]): products of modules are exact. -/
local instance (R : Type u) [CommRing R] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

/-- The functor `RΓ(X, - ⊗^L E)` commutes with shifts. -/
instance tensorSections_commShift : (S.tensorSections E).CommShift ℤ :=
  Functor.CommShift.comp _ _

/-- The functor `RΓ(X, - ⊗^L E)` is triangulated. -/
instance tensorSections_isTriangulated : (S.tensorSections E).IsTriangulated :=
  inferInstance

/-- `RΓ(X, - ⊗^L E)` read on `D(𝒪_X)` in the spelling `S.X.left.Modules` of `𝒪_X`-modules, the
target of the comparison of models. -/
def tensorSectionsModules :
    DerivedCategory S.X.left.Modules ⥤ DerivedCategory (ModuleCat.{u} ↑(limit S.system)) :=
  S.tensorSections E

/-- The functor `S.tensorSectionsModules E` commutes with shifts. -/
instance tensorSectionsModules_commShift : (S.tensorSectionsModules E).CommShift ℤ :=
  S.tensorSections_commShift E

/-- The functor `S.tensorSectionsModules E` is triangulated. -/
instance tensorSectionsModules_isTriangulated : (S.tensorSectionsModules E).IsTriangulated :=
  S.tensorSections_isTriangulated E

/-- `RΓ(X, - ⊗^L E)` commutes with countable products for perfect `E`
(`AlgebraicGeometry.LerayOver.tensor_flip_preservesCountableProducts`, [Stacks, Tag 08U1]). -/
theorem preservesLimitsOfShape_tensorSectionsModules
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    PreservesLimitsOfShape (Discrete ℕ) (S.tensorSectionsModules E) := by
  have := tensor_flip_preservesCountableProducts E hE
  exact (inferInstance : PreservesLimitsOfShape (Discrete ℕ) (S.tensorSections E))

/-- **`RΓ(X, - ⊗^L E)` inverts the coherator counit** for perfect `E`: it kills the right
orthogonal of `D_QCoh(𝒪_X)` ([Stacks, Tag 0DIE]'s lemma
`AlgebraicGeometry.isZero_derivedGlobalSectionsOver_derivedTensor_of_forall_hom_eq_zero`), which
contains the cone of `ι DQ_X L ⟶ L`
(`Stacks.Duality.Coherator.hom_eq_zero_of_counit_distTriang`). -/
theorem isIso_tensorSections_map_coheratorCounit
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    IsIso ((S.modelComparison.inverse ⋙ S.tensorSectionsModules E).map S.coheratorCounit) := by
  have : (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf :
      ObjectProperty S.X.left.Modules).IsClosedUnderIsomorphisms :=
    inferInstanceAs (SheafOfModules.isQuasicoherent S.X.left.ringCatSheaf).IsClosedUnderIsomorphisms
  refine isIso_map_counit_of_isZero S.X.left
    (S.modelComparison.inverse ⋙ S.tensorSectionsModules E) S.derivedLimit (fun Z hZ => ?_)
  refine isZero_derivedGlobalSectionsOver_derivedTensor_of_forall_hom_eq_zero S.X.hom E
    (S.modelComparison.inverse.obj Z) hE (fun Q hQ φ => ?_)
  have h₁ : S.modelComparison.functor.map φ ≫ S.modelComparison.counitIso.hom.app Z = 0 :=
    hZ _ ((@StacksDraft.DerivedModel.derivedCategoryB_modelEquiv_functor_obj_iff _ _ _ _ this
      (HasDerivedCategory.standard S.X.left.Modules)
      (Scheme.Modules.hasDerivedCategory S.X.left) Q).2
      fun n => hQ n) _
  have h₂ : S.modelComparison.functor.map φ = 0 :=
    (cancel_mono (S.modelComparison.counitIso.hom.app Z)).1 (h₁.trans zero_comp.symm)
  exact S.modelComparison.functor.map_injective
    (h₂.trans (S.modelComparison.functor.map_zero _ _).symm)

/-- The image of the unit of the comparison of models commutes with the transitions of the tower.
-/
theorem tensorSections_map_unitIso_inv_naturality (n : ℕ) :
    (S.modelComparison.inverse ⋙ S.tensorSectionsModules E).map
        (S.towerLocallySmall.map (homOfLE (Nat.le_succ n)).op) ≫
      (S.tensorSections E).map (S.modelComparison.unitIso.inv.app (S.tower.obj (op n))) =
    (S.tensorSections E).map (S.modelComparison.unitIso.inv.app (S.tower.obj (op (n + 1)))) ≫
      (S.tensorSections E).map (S.towerTransition n) := by
  rw [← S.tower_map_succ n]
  exact ((S.tensorSections E).map_comp _ _).symm.trans
    ((congrArg (S.tensorSections E).map
      (S.modelComparison.unitIso.inv.naturality (S.tower.map (homOfLE (Nat.le_succ n)).op))).trans
        ((S.tensorSections E).map_comp _ _))

/-- **The distinguished triangle presenting `M`.** For perfect `E` there is a distinguished
triangle `M ⟶ ∏ₙ Mₙ ⟶ ∏ₙ Mₙ ⟶ M[1]` in `D(A)` whose middle map is `1 - transitions` and whose
first map has components the canonical maps `M ⟶ Mₙ`. It is the image of the derived-limit
triangle of `R lim Kₙ` under `RΓ(X, - ⊗^L E)`, which commutes with countable products
([Stacks, Tag 0DIE]'s lemma `RingedSite.preservesLimitsOfSize_derivedTensor_flip_obj_of_isPerfect`
and [Stacks, Tag 08U1]), precomposed with the invertible image of
`K = DQ_X(R lim Kₙ) ⟶ R lim Kₙ` and transported along the identifications
`RΓ(X, R(iₙ)_* Kₙ ⊗^L E) = Mₙ` ([Stacks, Tag 0B54]). -/
theorem exists_distTriang_cohomology
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    ∃ (p : S.cohomology E ⟶ ∏ᶜ fun n : ℕ =>
        (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
          (S.levelCohomology E n))
      (δ : (∏ᶜ fun n : ℕ =>
          (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
          (S.levelCohomology E n)) ⟶ (S.cohomology E)⟦(1 : ℤ)⟧),
      Triangle.mk p (Pi.lift fun n : ℕ =>
          Pi.π (fun n : ℕ =>
              (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
            (S.levelCohomology E n)) n -
          Pi.π (fun n : ℕ =>
              (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
            (S.levelCohomology E n)) (n + 1) ≫ S.cohomologyTransitionRestricted E n) δ ∈
        distTriang _ ∧
      ∀ n : ℕ, p ≫ Pi.π (fun n : ℕ =>
          (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
            (S.levelCohomology E n)) n = S.cohomologyMap E n := by
  have := S.preservesLimitsOfShape_tensorSectionsModules E hE
  let H := S.modelComparison.inverse ⋙ S.tensorSectionsModules E
  obtain ⟨δ₀, hT₀⟩ := Stacks.Injectives.isDerivedLimit_map_of_preservesProduct H
    S.towerLocallySmall S.derivedLimit S.derivedLimitToProduct
    S.isDerivedLimit_derivedLimit.choose_spec
  have hψ : ∀ n, IsIso (S.towerSectionsMap E n) := fun n =>
    isIso_tensorPullbackMap_counit (limit.π S.system (op n)).hom S.X.hom
        (levelStructure S.system S.X n)
      (schemeProjection S.system S.X n) (S.levelProjection_w n) E hE (S.K n)
  let χ : ∀ n : ℕ, H.obj (S.towerLocallySmall.obj (op n)) ≅
      (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
        (S.levelCohomology E n) := fun n =>
    (S.tensorSections E).mapIso (S.modelComparison.unitIso.app (S.tower.obj (op n))).symm ≪≫
      @asIso _ _ _ _ (S.towerSectionsMap E n) (hψ n)
  have hχ : ∀ n : ℕ, (χ (n + 1)).hom ≫ S.cohomologyTransitionRestricted E n =
      H.map (S.towerLocallySmall.map (homOfLE (Nat.le_succ n)).op) ≫ (χ n).hom := fun n =>
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (S.towerSectionsMap_transition E n).symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ S.towerSectionsMap E n)
        (S.tensorSections_map_unitIso_inv_naturality E n).symm).trans (Category.assoc _ _ _))))
  have hT₁ := distTriang_derivedLimit_of_iso _ (S.cohomologyTransitionRestricted E) χ hχ _ δ₀ hT₀
  have := S.isIso_tensorSections_map_coheratorCounit E hE
  have hT₂ := distTriang_derivedLimit_precomp_iso (Y := fun n : ℕ =>
      (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
        (S.levelCohomology E n)) (S.cohomologyTransitionRestricted E)
    (asIso (H.map S.coheratorCounit)) _ _ hT₁
  refine ⟨_, _, hT₂, fun n => ?_⟩
  have h₁ : piComparison H (fun n : ℕ => S.towerLocallySmall.obj (op n)) ≫
      (Limits.Pi.map fun n => (χ n).hom) ≫ Pi.π (fun n : ℕ =>
        (ModuleCat.restrictScalars (limit.π S.system (op n)).hom).mapDerivedCategory.obj
          (S.levelCohomology E n)) n =
      H.map (Pi.π (fun n : ℕ => S.towerLocallySmall.obj (op n)) n) ≫ (χ n).hom := by
    rw [Limits.Pi.map_π, ← Category.assoc, piComparison_comp_π]
  have h₂ : H.map S.coheratorCounit ≫ H.map S.derivedLimitToProduct ≫
      H.map (Pi.π (fun n : ℕ => S.towerLocallySmall.obj (op n)) n) =
        H.map (S.coheratorCounit ≫ S.derivedLimitπ n) := by
    rw [derivedLimitπ, H.map_comp, H.map_comp]
  have h₃ : H.map (S.coheratorCounit ≫ S.derivedLimitπ n) ≫ (χ n).hom =
      (S.tensorSections E).map (S.limitProjection n) ≫ S.towerSectionsMap E n := by
    rw [S.limitProjection_eq n]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ S.towerSectionsMap E n) ((S.tensorSections E).map_comp _ _).symm)
  refine Eq.trans ?_ ((congrArg (· ≫ (χ n).hom) h₂).trans
    (h₃.trans (S.tensorSections_map_limitProjection_comp_towerSectionsMap E n)))
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₁)))).trans
      ((congrArg (_ ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm))

/-! ### Assembly -/

/-- `Xₙ = Xₙ₊₁ ×_{Spec Aₙ₊₁} Spec Aₙ`: the square of the transition `Xₙ ⟶ Xₙ₊₁` over
`Spec Aₙ ⟶ Spec Aₙ₊₁` is cartesian, by pasting the cartesian squares defining `Xₙ` and `Xₙ₊₁`
as base changes of `X`. -/
theorem isPullback_transitionScheme (n : ℕ) :
    IsPullback (S.transitionScheme n) (levelStructure S.system S.X n)
      (levelStructure S.system S.X (n + 1))
      (Spec.map (CommRingCat.ofHom (S.system.map (homOfLE (Nat.le_succ n)).op).hom)) := by
  have big : IsPullback (S.transitionScheme n ≫ schemeProjection S.system S.X (n + 1))
      (levelStructure S.system S.X n) S.X.hom
      (baseTransition S.system n ≫ baseProjection S.system (n + 1)) := by
    rw [S.transition_fst n, ← S.baseProjection_eq n]
    exact IsPullback.of_hasPullback S.X.hom (baseProjection S.system n)
  exact IsPullback.of_right big (S.transition_snd n)
    (IsPullback.of_hasPullback S.X.hom (baseProjection S.system (n + 1)))

/-- **[Stacks, Tag 0DID], given flat base change for the transitions.** If, for every `n`, the
pullback of derived global sections along `Xₙ ⟶ Xₙ₊₁` at `Kₙ₊₁ ⊗^L E|_{Xₙ₊₁}` has invertible base
change map, then `M = RΓ(X, K ⊗^L E)` is pseudo-coherent and the canonical maps
`M ⊗^L_A Aₙ ⟶ Mₙ` are isomorphisms: [Stacks, Tag 0CQF] applies to the system `(Mₙ)` and the
triangle of
`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.exists_distTriang_cohomology`.
-/
theorem isPseudoCoherent_cohomology_and_isIso_of_isIso_transition
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E)
    (hθ : ∀ n : ℕ, IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u}
      (S.system.map (homOfLE (Nat.le_succ n)).op).hom
          (LerayOver.pullbackSectionsMap (S.system.map (homOfLE (Nat.le_succ n)).op).hom
        (levelStructure S.system S.X (n + 1)) (levelStructure S.system S.X n) (S.transitionScheme n)
        (S.levelTransition_w n) (S.levelTensor E (n + 1))))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (S.cohomology E) ∧
      ∀ n : ℕ, IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u}
        (limit.π S.system (op n)).hom (S.cohomologyMap E n)) := by
  obtain ⟨p, δ, hT, hp⟩ := S.exists_distTriang_cohomology E hE
  have hpc : ∀ n, StacksDraft.PseudoCoherence.IsPseudoCoherent (S.levelCohomology E n) :=
    S.isPseudoCoherent_levelCohomology E hE.isPseudoCoherent
  have hbc : ∀ n, IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u}
      (S.system.map (homOfLE (Nat.le_succ n)).op).hom (S.cohomologyTransition E n)) := fun n =>
    have := S.φ_isIso n
    isIso_derivedBaseChangeComparison_tensorTransitionMap
        (S.system.map (homOfLE (Nat.le_succ n)).op).hom
      (levelStructure S.system S.X (n + 1)) (levelStructure S.system S.X n)
      (schemeProjection S.system S.X (n + 1)) (S.transitionScheme n)
      (schemeProjection S.system S.X n) (S.transition_fst n) (S.levelTransition_w n) E
      (S.K (n + 1)) (S.K n) (S.φ n) (hθ n)
  obtain ⟨h₁, h₂⟩ :=
    StacksDraft.DerivedInverseLimit.derivedLimit_isPseudoCoherent_and_baseChange_iso.{u, u}
    S.system (limit.cone S.system) (limit.isLimit S.system) (S.levelCohomology E)
    (S.cohomologyTransition E) S.transition_surjective (fun n => S.transition_locallyNilpotent n)
    (Or.inl hpc) hbc (S.cohomology E) p δ hT
  exact ⟨h₁, fun n => hp n ▸ h₂ n⟩

/-- **[Stacks, Tag 0DID].** In Situation [Stacks, Tag 0DIB] let `K` be as in
[Stacks, Tag 0DIC]. For any perfect object `E` of `D(𝒪_X)` the cohomology
`M = RΓ(X, K ⊗^L E)` is a pseudo-coherent object of `D(A)` and there is a canonical isomorphism
`RΓ(X_n, K_n ⊗^L E|_{X_n}) = M ⊗^L_A A_n` in `D(A_n)`, where `E|_{X_n}` is the derived pullback
of `E` to `X_n`.

Here `K` is `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.limitObject`, `M`
is `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.cohomology`, and the
canonical isomorphism is the base change map `M ⊗^L_A A_n ⟶ RΓ(X_n, K_n ⊗^L E|_{X_n})` adjoint to
the canonical map `M ⟶ RΓ(X_n, K_n ⊗^L E|_{X_n})`
(`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.cohomologyMap`): pull back
along `X_n ⟶ X`, identify `(K ⊗^L E)|_{X_n} = K|_{X_n} ⊗^L E|_{X_n}`, and apply the canonical map
`K|_{X_n} ⟶ K_n`.

The proof is the source's. `RΓ(X, - ⊗^L E)` carries the derived-limit triangle of
`K = DQ_X(R lim K_n)` to a triangle presenting `M` as `R lim M_n` for `M_n = RΓ(X_n, K_n ⊗^L E_n)`
(`AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation.exists_distTriang_cohomology`);
the `M_n` are pseudo-coherent ([Stacks, Tag 0CSD]) with `M_{n+1} ⊗^L A_n = M_n` by flat base
change; and [Stacks, Tag 0CQF] concludes. -/
@[stacks 0DID]
theorem isPseudoCoherent_cohomology_and_isIso
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (S.cohomology E) ∧
      ∀ n : ℕ, IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u}
        (limit.π S.system (op n)).hom (S.cohomologyMap E n)) := by
  refine S.isPseudoCoherent_cohomology_and_isIso_of_isIso_transition E hE fun n => ?_
  have := S.proper
  have := S.flat
  exact LerayOver.isIso_derivedBaseChangeComparison_pullbackSectionsMap
      (S.system.map (homOfLE (Nat.le_succ n)).op).hom
    (levelStructure S.system S.X (n + 1)) (levelStructure S.system S.X n) (S.transitionScheme n)
    (S.isPullback_transitionScheme n) (S.levelTensor E (n + 1))
    (isQuasicoherentDerived_of_isPseudoCoherent (schemeAt S.system S.X (n + 1)) _
      (S.isPseudoCoherent_levelTensor E hE.isPseudoCoherent (n + 1)))

/-- The first assertion of [Stacks, Tag 0DID]: `M = RΓ(X, K ⊗^L E)` is pseudo-coherent. -/
theorem isPseudoCoherent_cohomology
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (S.cohomology E) :=
  (S.isPseudoCoherent_cohomology_and_isIso E hE).1

/-- The second assertion of [Stacks, Tag 0DID]: the canonical map
`M ⊗^L_A A_n ⟶ RΓ(X_n, K_n ⊗^L E|_{X_n})` is an isomorphism. -/
theorem isIso_derivedBaseChangeComparison_cohomologyMap
    (hE : RingedSpace.IsPerfect (X := S.X.left.toRingedSpace) E) (n : ℕ) :
    IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, u, u}
      (limit.π S.system (op n)).hom (S.cohomologyMap E n)) :=
  (S.isPseudoCoherent_cohomology_and_isIso E hE).2 n

end AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation

end
