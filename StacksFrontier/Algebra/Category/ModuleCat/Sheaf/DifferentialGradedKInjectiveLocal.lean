module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeWeakCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullback
public import
  StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedSumsProducts
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjectiveLifting
public import StacksFrontier.CategoryTheory.Functor.Derived.Absolute

/-!
# Locality of K-injective differential graded modules, and derived extensions

Let `X` be a ringed site and `A` a sheaf of differential graded algebras on it. A right
differential graded `A`-module which is K-injective and graded injective is local for the
quasi-isomorphisms of `K(Mod(A, d))`: precomposition with a quasi-isomorphism is a bijection on
homotopy classes of morphisms into it. Surjectivity is
[Stacks, Tag 0FSX](https://stacks.math.columbia.edu/tag/0FSX), and injectivity is
`SheafOfModules.DifferentialGradedModule.homotopic_zero_of_comp_homotopic_zero`.

Consequently every functor out of `K(Mod(A, d))` has a right derived extension along the
localization `K(Mod(A, d)) ⥤ D(A, d)` as soon as K-injective resolutions exist, which is the
mechanism of [Stacks, Tag 0FTN](https://stacks.math.columbia.edu/tag/0FTN). The argument needs
neither a triangulated structure on `K(Mod(A, d))` nor a calculus of fractions for the
quasi-isomorphisms.

For a morphism of ringed sites out of `X` with a homomorphism `φ : B ⟶ f_*A` of sheaves of
differential graded algebras, this produces the derived pushforward
`Rf_* : D(A, d) ⥤ D(B, d)` as the right derived extension of `K(f_*)` followed by the
localization, together with its canonical comparison map `β : K(f_*) ⋙ Q' ⟶ Q ⋙ Rf_*`.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedPushforward` is `Rf_*` and
  `SheafOfModules.DifferentialGradedModule.pushforwardComparison` is its comparison map `β`.

## Main results

* `hasPointwiseRightDerivedFunctor_of_hasKInjectiveResolutions`, in the namespace
  `SheafOfModules.DifferentialGradedModule`: every functor out of the homotopy category has a
  right derived extension along the localization, given K-injective resolutions.
* `SheafOfModules.DifferentialGradedModule.isRightDerivedFunctor_derivedPushforward`: `Rf_*` is
  the right derived functor of `K(f_*) ⋙ Q'` with unit `β`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w u' v' a'

namespace SheafOfModules.DifferentialGradedModule

variable {X : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  [HasSheafify X.J AddCommGrpCat.{max u v w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]

/-- Every functor out of the homotopy category of right differential graded `A`-modules has a
right derived extension along the localization `K(Mod(A, d)) ⥤ D(A, d)`, given K-injective
resolutions. -/
theorem hasPointwiseRightDerivedFunctor_of_hasKInjectiveResolutions
    (hres : HasKInjectiveResolutions.{u, v, w} A)
    {H : Type*} [Category H] (F : HomotopyCategory.{u, v, max u v w} A ⥤ H) :
    F.HasPointwiseRightDerivedFunctor (quasiIsomorphisms.{u, v, max u v w} A) := by
  refine Functor.hasPointwiseRightDerivedFunctor_of_coresolutions
    (L := toDerivedCategory.{u, v, max u v w} A) _ F fun K => ?_
  obtain ⟨I, f, hf, hGI, hKI⟩ := hres K.as
  exact ⟨(HomotopyCategory.quotient A).obj I, (HomotopyCategory.quotient A).map f,
    (quasiIsomorphisms_quotient_map_iff f).2 hf,
    fun Y => bijective_toDerivedCategory_map hres Y hKI hGI⟩

/-- Every functor out of the homotopy category of right differential graded `A`-modules has a
right derived functor with respect to the quasi-isomorphisms, given K-injective resolutions. -/
theorem hasRightDerivedFunctor_of_hasKInjectiveResolutions
    (hres : HasKInjectiveResolutions.{u, v, w} A)
    {H : Type*} [Category H] (F : HomotopyCategory.{u, v, max u v w} A ⥤ H) :
    F.HasRightDerivedFunctor (quasiIsomorphisms.{u, v, max u v w} A) :=
  have := hasPointwiseRightDerivedFunctor_of_hasKInjectiveResolutions hres F
  F.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor
    (quasiIsomorphisms.{u, v, max u v w} A)

section DerivedPushforward

variable {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'}
  {R' : Sheaf J' RingCat.{u}} {B : DifferentialGradedAlgebra.{u, a'} R'}
  [HasSheafify J' AddCommGrpCat.{max u v w}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  {g : C' ⥤ X.C} [g.IsContinuous J' X.J]
  {σ : R'.obj ⟶ g.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}

/-- The derived pushforward `Rf_* : D(A, d) ⥤ D(B, d)` along a morphism of ringed sites with a
homomorphism `φ : B ⟶ f_*A` of sheaves of differential graded algebras: the right derived
extension of the direct image `K(f_*)` followed by the localization. -/
noncomputable def derivedPushforward (hres : HasKInjectiveResolutions.{u, v, w} A)
    (φ : DifferentialGradedAlgebra.SemilinearHom g σ B A) :
    derivedCategory.{u, v, max u v w} A ⥤ derivedCategory.{u, a', max u v w} B :=
  have := hasRightDerivedFunctor_of_hasKInjectiveResolutions hres
    (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B)
  (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B).totalRightDerived
    (toDerivedCategory.{u, v, max u v w} A) (quasiIsomorphisms.{u, v, max u v w} A)

/-- The canonical comparison map `β : K(f_*) ⋙ Q' ⟶ Q ⋙ Rf_*` of the derived pushforward, the
unit of its right derived extension. -/
noncomputable def pushforwardComparison (hres : HasKInjectiveResolutions.{u, v, w} A)
    (φ : DifferentialGradedAlgebra.SemilinearHom g σ B A) :
    homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B ⟶
      toDerivedCategory.{u, v, max u v w} A ⋙ derivedPushforward hres φ :=
  have := hasRightDerivedFunctor_of_hasKInjectiveResolutions hres
    (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B)
  (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B).totalRightDerivedUnit
    (toDerivedCategory.{u, v, max u v w} A) (quasiIsomorphisms.{u, v, max u v w} A)

/-- The derived pushforward is the right derived functor of the direct image followed by the
localization, with the comparison map as its unit. -/
theorem isRightDerivedFunctor_derivedPushforward
    (hres : HasKInjectiveResolutions.{u, v, w} A)
    (φ : DifferentialGradedAlgebra.SemilinearHom g σ B A) :
    (derivedPushforward hres φ).IsRightDerivedFunctor (pushforwardComparison hres φ)
      (quasiIsomorphisms.{u, v, max u v w} A) := by
  have := hasRightDerivedFunctor_of_hasKInjectiveResolutions hres
    (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B)
  exact inferInstanceAs ((Functor.totalRightDerived
      (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B)
      (toDerivedCategory.{u, v, max u v w} A)
      (quasiIsomorphisms.{u, v, max u v w} A)).IsRightDerivedFunctor
    (Functor.totalRightDerivedUnit
      (homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', max u v w} B)
      (toDerivedCategory.{u, v, max u v w} A)
      (quasiIsomorphisms.{u, v, max u v w} A))
    (quasiIsomorphisms.{u, v, max u v w} A))

end DerivedPushforward

end SheafOfModules.DifferentialGradedModule

end
