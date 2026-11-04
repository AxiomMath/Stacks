module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedDualExactPairing
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedPullbackMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPullbackPerfect
public import StacksFrontier.CategoryTheory.Monoidal.Rigid
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModulePullbackBounded
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExtConeOrthogonality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ApproximationTriangle

/-!
# Morphisms out of the derived pullback of a dual

Let `g : Y' ⟶ Y` be a morphism of algebraic spaces and `K` a perfect object of `D(𝒪_Y)` with dual
`K^∨ = R𝓗om(K, 𝒪_Y)`. Derived pullback `Lg^*` is a strong monoidal functor (Stacks 07A4) and
`K^∨` is a dual of `K` (Stacks 0FPV), so `Lg^*K^∨` is a dual of `Lg^*K` in `D(𝒪_{Y'})`, and
hence isomorphic to the dual `(Lg^*K)^∨` of the perfect object `Lg^*K`. These, and the
insensitivity of `Ext` into bounded below objects to the pullback of a morphism which is an
isomorphism on high cohomology, are used to compute the base change of the complex of
Stacks 0DKL.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDualExactPairing`: the exact pairing of
  `Lg^*K` and `Lg^*K^∨`.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackDualIso`: `Lg^*(K^∨) ≅ (Lg^*K)^∨`.

## Main results

* `AlgebraicGeometry.Space.bijective_comp_smallEtaleDerivedModulePullback_shiftedHom`: `Ext`
  into an object bounded below does not see the derived pullback of a morphism which is an
  isomorphism on cohomology in high degrees.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {Y Y' : AlgebraicSpaces B S hS}

/-- **The derived pullback of a perfect object and of its dual form an exact pairing**: the image
under the strong monoidal functor `Lg^*` of the exact pairing of `K` and `K^∨`. -/
@[instance_reducible]
def smallEtaleDerivedPullbackDualExactPairing (g : Y' ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K) :
    @ExactPairing _ _ (smallEtaleDerivedMonoidal Y')
      ((smallEtaleDerivedModulePullback B S hS g).obj K)
      ((smallEtaleDerivedModulePullback B S hS g).obj (smallEtaleDerivedDual B S hS Y K)) :=
  @ExactPairing.map _ _ _ _ (smallEtaleDerivedMonoidal Y) (smallEtaleDerivedMonoidal Y')
    (smallEtaleDerivedModulePullback B S hS g) (smallEtaleDerivedPullbackMonoidal g) K _
    (smallEtaleDerivedDualExactPairing Y K hK)

/-- **`Ext` against the derived pullback of a morphism that is an isomorphism in high degrees.**
If `c : P ⟶ L` in `D(𝒪_Y)` is an isomorphism on `Hʲ` for `j > s`, then for every `M ∈ D(𝒪_{Y'})`
concentrated in degrees `≥ a` precomposition with `Lg^*c` is bijective on
`Hom(Lg^*L, M[i]) ⟶ Hom(Lg^*P, M[i])` as soon as `i + s + 2 ≤ a`: the cone of `c` lies in degrees
`≤ s`, its derived pullback is the cone of `Lg^*c` and lies in degrees `≤ s` as `Lg^*` is right
t-exact. -/
theorem bijective_comp_smallEtaleDerivedModulePullback_shiftedHom (g : Y' ⟶ Y)
    {P L : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (c : P ⟶ L) (s : ℤ)
    (hc : ∀ j : ℤ, s < j → IsIso ((DerivedCategory.homologyFunctor _ j).map c))
    (M : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')))
    (a : ℤ) [M.IsGE a] (i : ℤ) (hi : i + s + 2 ≤ a) :
    Function.Bijective (fun e : (smallEtaleDerivedModulePullback B S hS g).obj L ⟶ M⟦i⟧ =>
      (smallEtaleDerivedModulePullback B S hS g).map c ≫ e) := by
  obtain ⟨Q, β, γ, hT⟩ := Pretriangulated.distinguished_cocone_triangle c
  have hQ : Q.IsLE s := by
    rw [DerivedCategory.isLE_iff]
    intro j hj
    exact CategoryTheory.isZero_homology_obj₃_of_distinguished (s + 1) _ hT
      (fun k hk => hc k (by omega)) (hc (s + 1) (by omega)).epi_of_iso j (by omega)
  have hT' := (smallEtaleDerivedModulePullback B S hS g).map_distinguished _ hT
  have : ((smallEtaleDerivedModulePullback B S hS g).obj
      (Pretriangulated.Triangle.mk c β γ).obj₃).IsLE s :=
    isLE_smallEtaleDerivedModulePullback_obj g Q s hQ
  exact DerivedCategory.bijective_comp_shiftedHom_of_isLE_of_isGE _ _ _ hT' s M a i hi

/-- **Derived pullback commutes with duals of perfect objects**: `Lg^*(K^∨) ≅ (Lg^*K)^∨`, both
being right duals of `Lg^*K` (`Lg^*K^∨` through `smallEtaleDerivedPullbackDualExactPairing`,
`(Lg^*K)^∨` because `Lg^*K` is perfect, Stacks 08H6), and right duals being unique. -/
def smallEtaleDerivedPullbackDualIso (g : Y' ⟶ Y)
    (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hK : RingedSite.IsPerfect (smallEtaleRingedSite B S hS Y.1 Y.2) K) :
    (smallEtaleDerivedModulePullback B S hS g).obj (smallEtaleDerivedDual B S hS Y K) ≅
      smallEtaleDerivedDual B S hS Y' ((smallEtaleDerivedModulePullback B S hS g).obj K) :=
  @rightDualIso _ _ (smallEtaleDerivedMonoidal Y') _ _ _
    (smallEtaleDerivedPullbackDualExactPairing g K hK)
    (smallEtaleDerivedDualExactPairing Y' _ (isPerfect_smallEtaleDerivedModulePullback g K hK))

end AlgebraicGeometry.Space

end
