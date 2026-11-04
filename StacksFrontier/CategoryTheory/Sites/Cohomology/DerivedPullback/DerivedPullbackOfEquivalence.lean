module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalenceModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.LocalizationAtRepresentableSheaf

/-!
# The derived pullback along an equivalence of ringed topoi

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi whose direct image of
sheaves of sets is an equivalence and whose structure map is an isomorphism. The pullback `f^*`
of sheaves of modules is then an exact equivalence, so the derived pullback `Lf^*` of
Stacks 06YY is the functor `f^*` induces on derived categories, and is an equivalence.

## Main results

* `isEquivalence_derivedPullback_of_isEquivalence_derivedPullbackOfEquivalence`: if the direct
  image of `f` is an equivalence and its structure map is an isomorphism, then `Lf^*` is an
  equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

-- no global `HasDerivedCategory` instance on sheaves of modules over a ringed topos
attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Cohomology.DerivedPullbackOfToposHom

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The derived pullback along an equivalence of ringed topoi is an equivalence**: the
pullback of sheaves of modules is an exact equivalence, so `Lf^*` is the induced functor on
derived categories, which is an equivalence. -/
theorem isEquivalence_derivedPullback_of_isEquivalence_derivedPullbackOfEquivalence
    (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp]
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor quasiIsoTarget] :
    (derivedPullback f).IsEquivalence := by
  have := f.pullbackModules_preservesFiniteColimits
  have : (f.toModulesHom.pullbackModules).Additive :=
    Functor.additive_of_preserves_binary_products _
  have := Stacks.Injectives.mapDerivedCategory_isEquivalence f.toModulesHom.pullbackModules
  exact Functor.isEquivalence_of_iso (derivedPullbackIsoMapDerivedCategory f).symm

end Stacks.Cohomology.DerivedPullbackOfToposHom
