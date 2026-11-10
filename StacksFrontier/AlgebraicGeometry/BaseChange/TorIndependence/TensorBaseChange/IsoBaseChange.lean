module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.RingCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.TensorBaseChange.SchemeToRing
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebraLiftedPresentation
public import StacksFrontier.Homology.Tor.IndependenceBaseChange
public import StacksFrontier.Cotangent.EtaleVanishing

/-!
# The map of Stacks 0DJ7 when the vertical arrows are isomorphisms

Let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a commutative square of schemes in which `f` and `f'` are isomorphisms. Then for `K ∈ D(𝒪_X)`,
`K' ∈ D(𝒪_{X'})` and `φ : L(g')^*K ⟶ K'`, the map of Stacks 0DJ7 at `(K, K', φ)` is an
isomorphism at every point of `X'` and in every degree exactly when `φ` is an isomorphism.

At the level of rings: for a square of rings `R → A`, `R → R'`, `A → A'`, `R' → A'` in which
`R → A` and `R' → A'` are bijective, the map of Stacks 0DJ7 at an isomorphism
`φ : K ⊗^L_A A' ≅ K'` is an isomorphism in every degree.

## Main results

* `RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_of_bijective`
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_of_isIso`
* `AlgebraicGeometry.isIso_of_isIso_baseChangeCohomologyMap_of_isIso`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

attribute [local instance] HasDerivedCategory.standard

variable {R A R' A' : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [Algebra R A] [Algebra R R'] [Algebra R A'] [Algebra A A'] [Algebra R' A']
  [IsScalarTower R A A'] [IsScalarTower R R' A']

/-- In a square of rings whose vertical arrows are bijective, the comparison of Stacks 065Z
between derived base change over `R` and over `A` is an isomorphism. -/
theorem isIso_squareDerivedComparison_of_bijective (hA : Function.Bijective (algebraMap R A))
    (hA' : Function.Bijective (algebraMap R' A')) :
    IsIso (squareDerivedComparison (R := R) (A := A) (R' := R') (A' := A')) := by
  have : Algebra.IsPushout R A R' A' :=
    ⟨IsBaseChange.of_bijective_of_surjective_algebraMap hA.2 hA'⟩
  have : Module.Flat R A :=
    Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R A) hA).symm
  have key := derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u, u, u + 1, u + 1,
    u + 1, u + 1} (A' := A') (CommAlgCat.torIndependent_of_flat R A R')
  let e := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap R R')
  let e' := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
    (algebraMap A A')
  exact @key e.functor e'.functor e.comparison e'.comparison e.isLeftDerived e'.isLeftDerived

/-- **The map of Stacks 0DJ7 for a square with bijective vertical arrows.** If `R → A` and
`R' → A'` are bijective and `φ : K ⊗^L_A A' ⟶ K'` is an isomorphism, then the map
`H^n(K ⊗^L_R R') ⊗_{A ⊗_R R'} A' ⟶ H^n(K')` is an isomorphism. -/
theorem isIso_ringBaseChangeCohomologyMap_of_bijective
    (hA : Function.Bijective (algebraMap R A)) (hA' : Function.Bijective (algebraMap R' A'))
    (K : DerivedCategory (ModuleCat.{u} A)) (K' : DerivedCategory (ModuleCat.{u} A'))
    (φ : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A A')).functor.obj K ⟶ K') [hφ : IsIso φ] (n : ℤ) :
    IsIso (ringBaseChangeCohomologyMap (R := R) (R' := R') K K' φ n) := by
  have := isIso_squareDerivedComparison_of_bijective hA hA'
  have hq : IsIso (cohomologyComparisonMap (R := R) (R' := R') K K' φ n) := by
    unfold cohomologyComparisonMap
    infer_instance
  let := (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A')).toAlgebra
  let : IsScalarTower (A ⊗[R] R') A'
      ((ModuleCat.restrictScalars (baseChangeTensorRingMap (R := R) (A := A) (R' := R')
        (A' := A'))).obj ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') n).obj K')) :=
    ⟨fun b a x => mul_smul (baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') b) a x⟩
  refine (isIso_ringBaseChangeCohomologyMap_iff_isBaseChange K K' φ n).2 ?_
  refine IsBaseChange.of_bijective_of_surjective_algebraMap ?_
    (ConcreteCategory.bijective_of_isIso (cohomologyComparisonMap (R := R) (R' := R') K K' φ n))
  intro a'
  obtain ⟨r, rfl⟩ := hA'.2 a'
  exact ⟨(1 : A) ⊗ₜ[R] r, by
    change baseChangeTensorRingMap (R := R) (A := A) (R' := R') (A' := A') ((1 : A) ⊗ₜ[R] r) = _
    rw [baseChangeTensorRingMap_tmul, map_one, one_mul]⟩

end RingTheory.TorIndependence

namespace AlgebraicGeometry

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

attribute [local instance] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}

/-- **The map of Stacks 0DJ7 at an isomorphism, for a square with invertible vertical arrows.**
If `f` and `f'` are isomorphisms and `φ : L(g')^*K ⟶ K'` is an isomorphism, then the map of
Stacks 0DJ7 at `(K, K', φ)` is an isomorphism at every point of `X'` and in every degree. -/
theorem isIso_baseChangeCohomologyMap_of_isIso [IsIso f] [IsIso f'] (w : g' ≫ f = f' ≫ g)
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K') [IsIso φ] (x' : X') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' w K K' φ x' n) := by
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x')) :=
    ((f.stalkMap (g' x')).hom).toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x')) :=
    (baseStalkMap f g f' g' w x').toAlgebra
  let : Algebra (S.presheaf.stalk (f (g' x'))) (X'.presheaf.stalk x') :=
    (((g'.stalkMap x').hom).comp ((f.stalkMap (g' x')).hom)).toAlgebra
  let : Algebra (X.presheaf.stalk (g' x')) (X'.presheaf.stalk x') :=
    ((g'.stalkMap x').hom).toAlgebra
  let : Algebra (S'.presheaf.stalk (f' x')) (X'.presheaf.stalk x') :=
    ((f'.stalkMap x').hom).toAlgebra
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (X.presheaf.stalk (g' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (S.presheaf.stalk (f (g' x'))) (S'.presheaf.stalk (f' x'))
      (X'.presheaf.stalk x') := IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  have hc : IsIso ((derivedPullbackStalkIso g' x').inv.app K ≫
      (derivedStalkFunctor x').map φ) :=
    IsIso.comp_isIso' (Iso.isIso_inv ((derivedPullbackStalkIso g' x').app K))
      (Functor.map_isIso _ φ)
  refine (isIso_baseChangeCohomologyMap_iff_ring f g f' g' w K K' φ x' n).2 ?_
  exact RingTheory.TorIndependence.isIso_ringBaseChangeCohomologyMap_of_bijective
    (ConcreteCategory.bijective_of_isIso (f.stalkMap (g' x')))
    (ConcreteCategory.bijective_of_isIso (f'.stalkMap x')) _ _ _ (hφ := hc) n

/-- **Condition (1) of Stacks 0DJ8 for a square with invertible vertical arrows.** If `f` and
`f'` are isomorphisms and the map of Stacks 0DJ7 at `(K, K', φ)` is an isomorphism at every point
of `X'` and in every degree, then `φ : L(g')^*K ⟶ K'` is an isomorphism. -/
theorem isIso_of_isIso_baseChangeCohomologyMap_of_isIso [IsIso f] [IsIso f']
    (w : g' ≫ f = f' ≫ g) (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (derivedPullback g'.toLRSHom.toShHom).obj K ⟶ K')
    (h : ∀ (x' : X') (n : ℤ), IsIso (baseChangeCohomologyMap f g f' g' w K K' φ x' n)) :
    IsIso φ := by
  have hst : ∀ x' : X', IsIso ((derivedStalkFunctor x').map φ) := fun x' => by
    refine (DerivedCategory.isIso_iff _ _).2 fun n => ?_
    have h1 := isIso_baseChangeCohomologyMap_of_eq w K K' (𝟙 _ ≫ φ) φ (Category.id_comp φ) x'
      n (h x' n)
    have h2 := baseChangeCohomologyMap_comp f g f' g' w K _ K' (𝟙 _) φ x' n
    have h3 := isIso_baseChangeCohomologyMap_of_isIso w K _ (𝟙 _) x' n
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ h3 (h2 ▸ h1)
  refine (Stacks.Cohomology.StalkwiseIso.isIso_iff_forall_derivedStalk_isIso
    X'.ringCatSheaf φ).2 fun x' => ?_
  exact (isIso_derivedStalkFunctor_map_iff x' φ).1 (hst x')

end AlgebraicGeometry
