module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackSectionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.AdjunctionUnitTruncations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomCoproducts
public import StacksFrontier.CategoryTheory.Triangulated.DerivedLimitOfAHomotopyColimit
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit

/-!
# Direct image of the derived internal Hom out of a homotopy colimit

Let `f : X ⟶ Y` be a morphism of algebraic spaces, let `K = hocolim Kₙ` in `D(𝒪_X)` and let
`E` be an object of `D(𝒪_X)`. The proof of [Stacks, Tag 0DKY] computes

`Rf_* R𝓗om(K, E) = R lim Rf_* R𝓗om(Kₙ, E)`

and, for `L = hocolim Lₙ` in `D(𝒪_Y)`, `R𝓗om(L, 𝒪_Y) = R lim R𝓗om(Lₙ, 𝒪_Y)`. So as soon as the
two inverse systems `n ↦ Rf_* R𝓗om(Kₙ, E)` and `n ↦ R𝓗om(Lₙ, 𝒪_Y)` are isomorphic, the objects
`Rf_* R𝓗om(K, E)` and `R𝓗om(L, 𝒪_Y)` are isomorphic. This file proves these three facts.

## Main results

* `AlgebraicGeometry.Space.isDerivedLimit_smallEtaleDerivedSheafHom_of_isHomotopyColimit`: on an
  algebraic space, `R𝓗om(hocolim Kₙ, E) = R lim R𝓗om(Kₙ, E)` for every system `(Kₙ)` and
  every `E` ([Stacks, Tag 0A0A], first step of its proof, which needs no perfectness).
* `AlgebraicGeometry.Space.isDerivedLimit_derivedModulePushforward`: `Rf_*` carries a derived
  limit to a derived limit ([Stacks, Tag 0A07] for algebraic spaces).
* `AlgebraicGeometry.Space.nonempty_derivedModulePushforward_sheafHom_iso_dual`: if
  `K = hocolim Kₙ`, `L = hocolim Lₙ` and the inverse systems `Rf_* R𝓗om(Kₙ, E)` and
  `R𝓗om(Lₙ, 𝒪_Y)` are isomorphic, then `Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_Y)`. This is the last
  display of the proof of [Stacks, Tag 0DKY].

## Implementation notes

`R𝓗om` on an algebraic space is `AlgebraicGeometry.Space.smallEtaleDerivedSheafHom`, the derived
internal Hom of the equi-universe model of the small étale ringed site read through the derived
equivalence `AlgebraicGeometry.Space.smallEtaleModelDerivedEquivalence`. The first result is
therefore `AlgebraicGeometry.RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit'` on
the model, transported along the two halves of that equivalence: the functor carries derived
colimits to derived colimits (`CategoryTheory.Pretriangulated.IsHomotopyColimit.map`) and the
inverse, being a right adjoint, carries derived limits to derived limits
(`Stacks.Injectives.isDerivedLimit_map_rightAdjoint`).

## References

* [Stacks Project, Tag 0A07](https://stacks.math.columbia.edu/tag/0A07)
* [Stacks Project, Tag 0A0A](https://stacks.math.columbia.edu/tag/0A0A)
* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `D(𝒪_X)` has countable products: it is the derived category of a Grothendieck abelian
category ([Stacks, Tag 07D9]). -/
instance hasProducts_derivedModules (X : AlgebraicSpaces B S hS) :
    HasProducts.{0} (derivedModules B S hS X) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  haveI : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_ringedToposStructureRingSheaf B S hS X
  haveI : HasProducts.{u} (derivedModules B S hS X) :=
    (Stacks.Injectives.hasProducts_derivedCategory _ : HasProducts.{u} _)
  hasProducts_shrink.{0, u}

/-- `D(𝒪_X)` has countable direct sums: it is the derived category of a Grothendieck abelian
category ([Stacks, Tag 07D9]). -/
instance hasCoproducts_derivedModules (X : AlgebraicSpaces B S hS) :
    HasCoproducts.{0} (derivedModules B S hS X) :=
  letI := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  haveI : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X.1 X.2) :=
    isGrothendieckAbelian_ringedToposStructureRingSheaf B S hS X
  haveI : HasCoproducts.{u} (derivedModules B S hS X) :=
    (Stacks.Injectives.hasCoproducts_derivedCategory _ : HasCoproducts.{u} _)
  hasCoproducts_shrink.{0, u}

section SheafHom

variable {X : AlgebraicSpaces B S hS}

/-- The inverse system `n ↦ R𝓗om(Kₙ, E)` of derived internal Homs out of the terms of a system
`(Kₙ)` of objects of `D(𝒪_X)`, for an algebraic space `X`. -/
abbrev smallEtaleDerivedSheafHomSystem
    (F : ℕ ⥤ derivedModules B S hS X)
    (E : derivedModules B S hS X) :
    ℕᵒᵖ ⥤ derivedModules B S hS X :=
  F.op ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj E

/-- **Derived internal Hom out of a derived colimit on an algebraic space.** If
`K = hocolim Kₙ` in `D(𝒪_X)`, then `R𝓗om(K, E) = R lim R𝓗om(Kₙ, E)` for every `E`. -/
theorem isDerivedLimit_smallEtaleDerivedSheafHom_of_isHomotopyColimit
    (F : ℕ ⥤ derivedModules B S hS X)
    (E : derivedModules B S hS X)
    {K : derivedModules B S hS X}
    (hK : IsHomotopyColimit F K) :
    IsDerivedLimit (smallEtaleDerivedSheafHomSystem B S hS F E)
      (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj E) := by
  let := HasDerivedCategory.standard (Modules.{u, u} B S hS X.1 X.2)
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleModelRingedSite B S hS X.1 X.2).O))
  have : (modulesEquivModelModules B S hS X.1 X.2).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  have h₁ := RingedSite.isDerivedLimit_derivedSheafHom_of_isHomotopyColimit'
    (smallEtaleModelRingedSite B S hS X.1 X.2) _
    ((modulesEquivModelModules B S hS X.1 X.2).functor.mapDerivedCategory.obj E)
    (hK.map (modulesEquivModelModules B S hS X.1 X.2).functor.mapDerivedCategory)
  have : (modulesEquivModelModules B S hS X.1 X.2).inverse.mapDerivedCategory.IsRightAdjoint :=
    (Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
      (modulesEquivModelModules B S hS X.1 X.2)).toAdjunction.isRightAdjoint
  obtain ⟨_, h₂⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint
    (modulesEquivModelModules B S hS X.1 X.2).inverse.mapDerivedCategory _ _ h₁
  exact h₂

end SheafHom

section Pushforward

variable {X Y : AlgebraicSpaces B S hS}

/-- **`Rf_*` carries derived limits to derived limits** for a morphism of algebraic spaces
([Stacks, Tag 0A07]): it is a right adjoint, of `Lf^*`, and triangulated. -/
theorem isDerivedLimit_derivedModulePushforward (f : X ⟶ Y)
    (F : ℕᵒᵖ ⥤ derivedModules B S hS X)
    {K : derivedModules B S hS X} (hK : IsDerivedLimit F K) :
    IsDerivedLimit (F ⋙ derivedModulePushforward B S hS f)
      ((derivedModulePushforward B S hS f).obj K) := by
  have : (derivedModulePushforward B S hS f).IsRightAdjoint :=
    (smallEtaleDerivedModuleAdjunction B S hS f).isRightAdjoint
  obtain ⟨_, h⟩ := Stacks.Injectives.isDerivedLimit_map_rightAdjoint
    (derivedModulePushforward B S hS f) F K hK
  exact h

/-- **The last display of the proof of [Stacks, Tag 0DKY].** Let `f : X ⟶ Y` be a morphism of
algebraic spaces, `K = hocolim Kₙ` in `D(𝒪_X)`, `L = hocolim Lₙ` in `D(𝒪_Y)` and `E` an object of
`D(𝒪_X)`. If the inverse systems `n ↦ Rf_* R𝓗om(Kₙ, E)` and `n ↦ R𝓗om(Lₙ, 𝒪_Y)` are
isomorphic, then `Rf_* R𝓗om(K, E) ≅ R𝓗om(L, 𝒪_Y)`. -/
theorem nonempty_derivedModulePushforward_sheafHom_iso_dual (f : X ⟶ Y)
    (F : ℕ ⥤ derivedModules B S hS X)
    (G : ℕ ⥤ derivedModules B S hS Y)
    (E : derivedModules B S hS X)
    {K : derivedModules B S hS X}
    {L : derivedModules B S hS Y}
    (hK : IsHomotopyColimit F K) (hL : IsHomotopyColimit G L)
    (e : smallEtaleDerivedSheafHomSystem B S hS F E ⋙ derivedModulePushforward B S hS f ≅
      G.op ⋙ (smallEtaleDerivedSheafHom B S hS Y).flip.obj
        (structureObject B S hS Y)) :
    Nonempty ((derivedModulePushforward B S hS f).obj
        (((smallEtaleDerivedSheafHom B S hS X).obj (op K)).obj E) ≅
      smallEtaleDerivedDual B S hS Y L) :=
  Stacks.DerivedCategory.AdjunctionUnitTruncations.nonempty_iso_of_isDerivedLimit _ _ _
    (IsDerivedLimit.of_natIso e (isDerivedLimit_derivedModulePushforward B S hS f _
      (isDerivedLimit_smallEtaleDerivedSheafHom_of_isHomotopyColimit B S hS F E hK)))
    (isDerivedLimit_smallEtaleDerivedSheafHom_of_isHomotopyColimit B S hS G _ hL)

end Pushforward

end AlgebraicGeometry.Space

end
