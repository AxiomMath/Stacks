module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFunctor

/-!
# Derived pullback-tensor along a composition

Let `f` and `g` be two morphisms of ringed sites which compose, each carrying the data of
Tag 0FTE: a homomorphism of sheaves of differential graded algebras, a pullback of differential
graded modules and a bimodule to tensor with. The two functors of Tag 0FTE compose to a functor
`K(Mod(ℬ'', d)) ⥤ K(Mod(𝒜', d))`, and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullbackTensorFunctor`
attaches a left derived extension to each factor. The composite of those two derived extensions
is a left derived extension of the composite: the first functor carries good modules to good
modules, so the counit of the second is invertible on the objects in the image of the first.

This is the content of Tag 0FTI for derived pullback, stated for the pullback-tensor functors it
specializes. Two things are proved. First the composite *is* the left derived functor, with the
composed counit, `isLeftDerivedFunctor_derivedPullbackTensorCompCounit`; this is strictly
stronger than a comparison at each object, because a left derived functor is a right Kan
extension and so is determined up to a unique isomorphism. Second, by that determinacy, any
left derived extension of a functor identified with the composite — in particular the derived
pullback-tensor functor attached to the composite morphism of ringed sites — is isomorphic to
it, `exists_iso_derivedPullbackTensorComp`, by a natural isomorphism of functors of the derived
categories and not merely an isomorphism at each object.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedPullbackTensorCompCounit` is the counit of the
  composite: the counit of the first derived extension carried by the second, followed by the
  counit of the second evaluated on the image of the first.

## Main results

* `SheafOfModules.DifferentialGradedModule.isIso_derivedPullbackTensorCompCounit_app_of_isGood`:
  the composed counit is an isomorphism at every good right differential graded `ℬ''`-module.
* `SheafOfModules.DifferentialGradedModule.isLeftDerivedFunctor_derivedPullbackTensorCompCounit`:
  **Tag 0FTI.** The composite of the two derived extensions is the left derived functor of the
  composite of the two functors of Tag 0FTE.
* `SheafOfModules.DifferentialGradedModule.exists_iso_derivedPullbackTensorComp`: consequently,
  for any functor of the derived categories which is a left derived extension of a functor
  identified with that composite, there is an isomorphism to the composite of the two derived
  extensions compatible with the two counits.

## Implementation notes

**What is assumed beyond the two situations.** One statement: that the first functor of
Tag 0FTE carries a good right differential graded `ℬ''`-module to a good right differential
graded `ℬ`-module. That is the goodness half of Tag 0FSI(2), proved in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodAcyclicDifferentialGradedModule.lean` as
`SheafOfModules.DifferentialGradedModule.isGood_pullback_of_isGood`, and it is a hypothesis here
because the notion of goodness used for the resolutions is a parameter of
`GoodResolutionData`. Nothing about any derived functor is assumed.

**Why the identification of the composite is an input of the last result and not of the
others.** The first two results are about the composite functor of Tag 0FTE itself, and need no
identification of it with anything. Identifying that composite with the functor attached to the
composite morphism of ringed sites is a statement about pullbacks of differential graded modules
— the composite of two pullbacks is a pullback along the composite,
`SheafOfModules.DifferentialGradedModule.PullbackData.transIso` — and about the associativity of
the tensor product; it is the conclusion of neither of the tags above, so it enters
`exists_iso_derivedPullbackTensorComp` as the datum `e`.

## References

* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
* [Stacks Project, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE)
* [Stacks Project, Tag 0FTF](https://stacks.math.columbia.edu/tag/0FTF)
* [Stacks Project, Tag 0FSI](https://stacks.math.columbia.edu/tag/0FSI)
-/

@[expose] public section

open CategoryTheory

universe t a z a' z' a₂ m m' m₂ m₃ s v u v' u' v₂ u₂

namespace SheafOfModules

namespace DifferentialGradedModule

section Composition

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {C₂ : Type u₂} [Category.{v₂} C₂] {J₂ : GrothendieckTopology C₂}
  {R₂ : Sheaf J₂ RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{s}] [J.WEqualsLocallyBijective AddCommGrpCat.{s}]
  [HasSheafify J' AddCommGrpCat.{m'}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m'}]
  [HasSheafify J₂ AddCommGrpCat.{m₃}] [J₂.WEqualsLocallyBijective AddCommGrpCat.{m₃}]
  {w : C' ⥤ C} {σ : R'.obj ⟶ w.op ⋙ R.obj}
  {w₂ : C₂ ⥤ C'} {σ₂ : R₂.obj ⟶ w₂.op ⋙ R'.obj}
  {A A' : DifferentialGradedAlgebra.{t, a} R} {B Btilde : DifferentialGradedAlgebra.{t, a'} R'}
  {B₂ : DifferentialGradedAlgebra.{t, a₂} R₂}
  {φ : DifferentialGradedAlgebra.SemilinearHom w σ B A}
  {φ₂ : DifferentialGradedAlgebra.SemilinearHom w₂ σ₂ B₂ Btilde}
  {N : DifferentialGradedBimodule.{t, a, z} A A'}
  {N₂ : DifferentialGradedBimodule.{t, a', z'} Btilde B}
  {P : PullbackData.{t, a, m, v, u, a', m'} φ}
  {D : TensorFunctorData.{t, a, m, z, s} A A' N}
  {g : GoodResolutionData.{t, a', m', v', u'} B}
  {P₂ : PullbackData.{t, a', m₂, v', u', a₂, m₃} φ₂}
  {D₂ : TensorFunctorData.{t, a', m₂, z', m'} Btilde B N₂}
  {g₂ : GoodResolutionData.{t, a₂, m₃, v₂, u₂} B₂}
  [(quasiIsomorphisms.{t, a', m'} B).HasRightCalculusOfFractions]
  [(quasiIsomorphisms.{t, a₂, m₃} B₂).HasRightCalculusOfFractions]

/-- The counit of the composite of the two derived extensions: the counit of the first, carried
by the second derived extension, followed by the counit of the second, evaluated on the image of
the first functor of Tag 0FTE. -/
noncomputable def derivedPullbackTensorCompCounit
    (E : P.HomotopyExtension) (hE : PullbackTensorExactnessData P D g)
    (E₂ : P₂.HomotopyExtension) (hE₂ : PullbackTensorExactnessData P₂ D₂ g₂) :
    toDerivedCategory B₂ ⋙ derivedPullbackTensor E₂ hE₂ ⋙ derivedPullbackTensor E hE ⟶
      (HomotopyCategory.pullbackTensor E₂ D₂ ⋙ HomotopyCategory.pullbackTensor E D) ⋙
        toDerivedCategory A' :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (derivedPullbackTensorCounit E₂ hE₂) (derivedPullbackTensor E hE) ≫
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (HomotopyCategory.pullbackTensor E₂ D₂)
          (derivedPullbackTensorCounit E hE) ≫ (Functor.associator _ _ _).inv

/-- The component of the composed counit at an object, with the associators discharged. -/
theorem derivedPullbackTensorCompCounit_app
    (E : P.HomotopyExtension) (hE : PullbackTensorExactnessData P D g)
    (E₂ : P₂.HomotopyExtension) (hE₂ : PullbackTensorExactnessData P₂ D₂ g₂)
    (X : HomotopyCategory.{t, a₂, m₃} B₂) :
    (derivedPullbackTensorCompCounit E hE E₂ hE₂).app X =
      (derivedPullbackTensor E hE).map ((derivedPullbackTensorCounit E₂ hE₂).app X) ≫
        (derivedPullbackTensorCounit E hE).app
          ((HomotopyCategory.pullbackTensor E₂ D₂).obj X) := by
  simp [derivedPullbackTensorCompCounit]

variable (E : P.HomotopyExtension) (hE : PullbackTensorExactnessData P D g)
  (E₂ : P₂.HomotopyExtension) (hE₂ : PullbackTensorExactnessData P₂ D₂ g₂)
  (hgood : ∀ Q : DifferentialGradedModule.{t, a₂, m₃} B₂, g₂.IsGood Q →
    g.IsGood ((pullbackTensorFunctor P₂ D₂).obj Q))

include hE hE₂ hgood

omit [(quasiIsomorphisms.{t, a', m'} B).HasRightCalculusOfFractions]
  [(quasiIsomorphisms.{t, a₂, m₃} B₂).HasRightCalculusOfFractions] in
/-- The composite of the two functors of Tag 0FTE, followed by the localization functor, inverts
the quasi-isomorphisms between objects represented by good modules: the first functor carries
such a quasi-isomorphism to one between objects represented by good modules, where the second
inverts it. -/
theorem isIso_pullbackTensorComp_map_of_objectProperty
    {X Y : HomotopyCategory.{t, a₂, m₃} B₂} (ss : X ⟶ Y)
    (hss : quasiIsomorphisms.{t, a₂, m₃} B₂ ss) (hX : g₂.objectProperty X)
    (hY : g₂.objectProperty Y) :
    IsIso (((HomotopyCategory.pullbackTensor E₂ D₂ ⋙ HomotopyCategory.pullbackTensor E D) ⋙
      toDerivedCategory A').map ss) :=
  isIso_pullbackTensor_map_of_objectProperty E hE
    ((HomotopyCategory.pullbackTensor E₂ D₂).map ss)
    (quasiIsomorphisms_pullbackTensor_map_of_objectProperty E₂ hE₂ ss hss hX hY)
    (hgood X.as hX) (hgood Y.as hY)

/-- The composed counit is an isomorphism at every good right differential graded `ℬ''`-module:
the counit of the first derived extension is invertible there, hence so is its image under the
second derived extension, and the counit of the second is invertible at the image of a good
module, which is good. -/
theorem isIso_derivedPullbackTensorCompCounit_app_of_isGood
    {Q : DifferentialGradedModule.{t, a₂, m₃} B₂} (hQ : g₂.IsGood Q) :
    IsIso ((derivedPullbackTensorCompCounit E hE E₂ hE₂).app
      ((HomotopyCategory.quotient B₂).obj Q)) := by
  rw [derivedPullbackTensorCompCounit_app]
  have h₂ : IsIso ((derivedPullbackTensorCounit E hE).app
      ((HomotopyCategory.pullbackTensor E₂ D₂).obj ((HomotopyCategory.quotient B₂).obj Q))) :=
    isIso_derivedPullbackTensorCounit_app_of_isGood E hE (hgood Q hQ)
  have := isIso_derivedPullbackTensorCounit_app_of_isGood E₂ hE₂ hQ
  have := h₂
  infer_instance

/-- **Tag 0FTI.** Derived pullback-tensor along `f` after derived pullback-tensor along `g` is
the left derived functor of the composite of the two functors of Tag 0FTE, with the composed
counit: it is a right Kan extension along the localization functor
`K(Mod(ℬ'', d)) → D(ℬ'', d)`, so it is determined by the composite up to a unique compatible
isomorphism. -/
theorem isLeftDerivedFunctor_derivedPullbackTensorCompCounit :
    (derivedPullbackTensor E₂ hE₂ ⋙ derivedPullbackTensor E hE).IsLeftDerivedFunctor
      (derivedPullbackTensorCompCounit E hE E₂ hE₂) (quasiIsomorphisms.{t, a₂, m₃} B₂) :=
  LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
    (quasiIsomorphisms.{t, a₂, m₃} B₂) g₂.objectProperty g₂.exists_objectProperty _
    (fun ss hss hX hY =>
      isIso_pullbackTensorComp_map_of_objectProperty E hE E₂ hE₂ hgood ss hss hX hY)
    (toDerivedCategory B₂) _ (derivedPullbackTensorCompCounit E hE E₂ hE₂)
    (fun _X hX => isIso_derivedPullbackTensorCompCounit_app_of_isGood E hE E₂ hE₂ hgood hX)

/-- **Tag 0FTI, as an isomorphism of functors.** Let `K` be a functor of the homotopy categories
identified with the composite of the two functors of Tag 0FTE — for derived pullback this is the
functor of the composite morphism of ringed sites, the composite of two pullbacks being a
pullback along the composition — and let `Λ` be a functor of the derived categories with a
transformation to the image of `K` which is invertible at every good module. Then `Λ` is
isomorphic to the composite of the two derived extensions, by an isomorphism carrying the
composed counit to that transformation. -/
theorem exists_iso_derivedPullbackTensorComp
    (K : HomotopyCategory.{t, a₂, m₃} B₂ ⥤ HomotopyCategory.{t, a, s} A')
    (e : HomotopyCategory.pullbackTensor E₂ D₂ ⋙ HomotopyCategory.pullbackTensor E D ≅ K)
    (Λ : derivedCategory.{t, a₂, m₃} B₂ ⥤ derivedCategory.{t, a, s} A')
    (β : toDerivedCategory B₂ ⋙ Λ ⟶ K ⋙ toDerivedCategory A')
    (hβ : ∀ Q : DifferentialGradedModule.{t, a₂, m₃} B₂, g₂.IsGood Q →
      IsIso (β.app ((HomotopyCategory.quotient B₂).obj Q))) :
    ∃ ε : derivedPullbackTensor E₂ hE₂ ⋙ derivedPullbackTensor E hE ≅ Λ,
      Functor.whiskerLeft (toDerivedCategory B₂) ε.hom ≫ β =
        derivedPullbackTensorCompCounit E hE E₂ hE₂ ≫
          Functor.whiskerRight e.hom (toDerivedCategory A') := by
  have := isLeftDerivedFunctor_derivedPullbackTensorCompCounit E hE E₂ hE₂ hgood
  exact LeftDerivedByResolutions.exists_leftDerivedIso_of_resolutions
    (quasiIsomorphisms.{t, a₂, m₃} B₂) g₂.objectProperty g₂.exists_objectProperty _ _
    (Functor.isoWhiskerRight e (toDerivedCategory A'))
    (fun ss hss hX hY =>
      isIso_pullbackTensorComp_map_of_objectProperty E hE E₂ hE₂ hgood ss hss hX hY)
    (toDerivedCategory B₂) _ Λ (derivedPullbackTensorCompCounit E hE E₂ hE₂) β
    (fun X hX => hβ X.as hX)

end Composition

end DifferentialGradedModule

end SheafOfModules

end
