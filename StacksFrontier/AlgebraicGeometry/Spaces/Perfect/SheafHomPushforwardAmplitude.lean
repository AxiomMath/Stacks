module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforwardLeftTExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PushforwardSheafHomHomotopyColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackAmplitude

/-!
# An amplitude bound for `R𝓗om`, and `Lg^*` of a derived colimit, on algebraic spaces

The proof of [Stacks, Tag 0DKY] compares the terms of the inverse system
`n ↦ R𝓗om(Kₙ, E)` through the cones `Cₙ` of the transition maps of a system `(Kₙ)` of
approximations of a pseudo-coherent object: each `Cₙ` lies in `D^{≤ -n-1}` and `E` lies in
`D^{≥ a}`, so `R𝓗om(Cₙ, E)` lies in `D^{≥ a + n + 1}`. This file proves the bound behind that
step on an arbitrary algebraic space, and that the derived pullback along any morphism of
algebraic spaces carries derived colimits to derived colimits, which is how the source's
formula is carried to an arbitrary base change.

## Main results

* `AlgebraicGeometry.Space.isHomotopyColimit_smallEtaleDerivedModulePullback`: `Lg^*` carries
  `hocolim Kₙ` to `hocolim Lg^*Kₙ`.
* `AlgebraicGeometry.Space.isGE_smallEtaleDerivedSheafHom`: if `K ∈ D^{≤ d}(𝒪_X)` and
  `E ∈ D^{≥ b}(𝒪_X)` then `R𝓗om(K, E) ∈ D^{≥ b - d}(𝒪_X)`.
* `AlgebraicGeometry.Space.hasCoproducts_derivedCategory_ringedToposStructureRingSheaf`: countable
  direct sums in `D(𝒪_X)` in the spelling over the small étale ringed topos.

## Implementation notes

`Lg^*` is triangulated (`AlgebraicGeometry.Space.isTriangulated_smallEtaleDerivedModulePullback`)
and a left adjoint (`AlgebraicGeometry.Space.smallEtaleDerivedModuleAdjunction`), so it preserves
direct sums, and `CategoryTheory.Pretriangulated.IsHomotopyColimit.map` applies. That lemma is
stated over the structure sheaf of the small étale ringed topos, the spelling of `Lg^*`.

The bound is `AlgebraicGeometry.RingedSite.isGE_derivedSheafHom` on the equi-universe model of
the small étale site, transported along the exact equivalence of module categories
`AlgebraicGeometry.Space.modulesEquivModelModules`, which preserves cohomology sheaves in both
directions.

## References

* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] abelian_ringedToposStructureRingSheafModules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `D(𝒪_X)`, in the spelling over the structure sheaf of the small étale ringed topos at which
`Lf^*` and `R𝓗om` are stated, has countable direct sums ([Stacks, Tag 07D9]). -/
instance hasCoproducts_derivedCategory_ringedToposStructureRingSheaf
    (X : AlgebraicSpaces B S hS) :
    HasCoproducts.{0}
      (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))) :=
  hasCoproducts_derivedModules B S hS X

variable {X Y : AlgebraicSpaces B S hS}

/-- **`Lg^*` preserves derived colimits**: for a morphism `g : X ⟶ Y` of algebraic spaces and
`K = hocolim Kₙ` in `D(𝒪_Y)`, `Lg^*K = hocolim Lg^*Kₙ` in `D(𝒪_X)`. `Lg^*` is triangulated and,
being a left adjoint, preserves direct sums. -/
theorem isHomotopyColimit_smallEtaleDerivedModulePullback (g : X ⟶ Y)
    (F : ℕ ⥤ DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    {K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))}
    (hK : IsHomotopyColimit F K) :
    IsHomotopyColimit (F ⋙ smallEtaleDerivedModulePullback B S hS g)
      ((smallEtaleDerivedModulePullback B S hS g).obj K) := by
  let : (smallEtaleDerivedModulePullback B S hS g).CommShift ℤ :=
    commShift_smallEtaleDerivedModulePullback B S hS g
  have : (smallEtaleDerivedModulePullback B S hS g).IsTriangulated :=
    isTriangulated_smallEtaleDerivedModulePullback B S hS g
  have : PreservesColimit (Discrete.functor F.obj) (smallEtaleDerivedModulePullback B S hS g) :=
    (smallEtaleDerivedModuleAdjunction B S hS g).leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape.preservesColimit
  exact hK.map (smallEtaleDerivedModulePullback B S hS g)

/-- **`Rf_*` is left t-exact**, stated over the structure sheaf of the small étale ringed topos,
the spelling of `Lf^*` and `R𝓗om`: this is
`AlgebraicGeometry.Space.isGE_derivedModulePushforward_obj_of_isGE` read in that spelling. -/
theorem isGE_derivedModulePushforward_obj_of_isGE_ringedTopos
    (f : X ⟶ Y) (K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (n : ℤ) (hK : K.IsGE n) : ((derivedModulePushforward B S hS f).obj K).IsGE n :=
  isGE_derivedModulePushforward_obj_of_isGE B S hS f K n hK

/-- **The derived internal Hom of a bounded-above object into a bounded-below object is bounded
below** on an algebraic space: if `K ∈ D^{≤ d}(𝒪_X)` and `E ∈ D^{≥ b}(𝒪_X)`, then
`R𝓗om(K, E) ∈ D^{≥ b - d}(𝒪_X)`. -/
theorem isGE_smallEtaleDerivedSheafHom (K E : derivedModules B S hS X) (d b : ℤ)
    (hK : K.IsLE d) (hE : E.IsGE b) :
    (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj E).IsGE (b - d) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O))
  have : (modulesEquivModelModules B S hS X.1 X.2).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have := hK
  have hK' := Stacks.Homology.isLE_mapDerivedCategory_obj
    (modulesEquivModelModules B S hS X.1 X.2).functor K d
  have hE' := Stacks.Cohomology.DerivedInternalHomPullback.isGE_mapDerivedCategory_obj
    (modulesEquivModelModules B S hS X.1 X.2).functor E b hE
  exact Stacks.Cohomology.DerivedInternalHomPullback.isGE_mapDerivedCategory_obj
    (modulesEquivModelModules B S hS X.1 X.2).inverse _ (b - d)
    (RingedSite.isGE_derivedSheafHom (smallEtaleModelRingedSite B S hS X.1 X.2) _ _ d b hK' hE')

end AlgebraicGeometry.Space

end
