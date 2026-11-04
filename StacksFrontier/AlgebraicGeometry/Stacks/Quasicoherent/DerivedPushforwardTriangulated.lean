module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.WeakSerreClassRightDerivedFunctorPlus
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.DerivedPushforwardQuasicoherent

/-!
# The derived direct image of an algebraic stack is triangulated, and its cohomology

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and let
`Rf_* : D⁺(𝒪_𝒳) ⥤ D⁺(𝒪_𝒴)` be the total right derived functor of the direct image of
**Stacks 06WE** on fppf modules, at module universe `u + 1`
(`AlgebraicGeometry.Stack.fppfDerivedPushforwardPlusOfStacks`).

This file proves the two homological facts the diagram of **Stacks 07BC** rests on.

* `Rf_*` carries distinguished triangles to distinguished triangles: it is a triangulated functor
  (**Stacks 0159**), by `CategoryTheory.Functor.isTriangulated_rightDerivedFunctorPlus`.
* The cohomology of `Rf_*K` is controlled by the higher direct images of the cohomology of `K`:
  if `Rᵖf_*` carries a class `P` of modules on `𝒳` into a weak Serre class `Q` of modules on `𝒴`
  in every degree, then `Rf_*` carries the complexes with cohomology in `P` to complexes with
  cohomology in `Q`. This is the spectral sequence `Rᵖf_*Hᵠ(K) ⇒ Rᵖ⁺ᵠf_*K` of the source's proof
  of **Stacks 07BC**, run through part (4) of **Stacks 0132**, as
  `CategoryTheory.Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj` does for any additive
  functor out of an abelian category with enough injectives.

## Main results

* `AlgebraicGeometry.Stack.derivedPushforwardMapsDistinguished_fppfDerivedPushforwardPlusOfStacks`:
  `Rf_*` carries distinguished triangles to distinguished triangles.
* `AlgebraicGeometry.Stack.fppfDerivedPushforwardPlusOfStacks_obj_mem_of_higherDirectImage`:
  the cohomology of `Rf_*K` lies in a weak Serre class `Q` as soon as that of `K` lies in a class
  which every `Rᵖf_*` carries into `Q`.

## References

* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0159](https://stacks.math.columbia.edu/tag/0159)
* [Stacks Project, Tag 015J](https://stacks.math.columbia.edu/tag/015J)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 07BC](https://stacks.math.columbia.edu/tag/07BC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u w

namespace AlgebraicGeometry.Stack

attribute [local instance] hasSheafify_fppfAssociatedTopology_succ
  wEqualsLocallyBijective_fppfAssociatedTopology_succ

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)]
  [HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)]

/-- **The derived direct image of a 1-morphism of algebraic stacks carries distinguished
triangles to distinguished triangles.** `Rf_*` is the total right derived functor of an additive
functor out of an abelian category with enough injectives, and such a functor is triangulated
(**Stacks 0159**); the third morphism of the image triangle is the image of the third morphism
followed by the commutation isomorphism of `Rf_*` with the shift. -/
theorem derivedPushforwardMapsDistinguished_fppfDerivedPushforwardPlusOfStacks (f : 𝒳 ⟶ 𝒴) :
    DerivedPushforwardMapsDistinguished B S hS f := by
  let := additive_fppfModuleSheafPushforwardOfStacks B S hS f
  let := enoughInjectives_fppfModulesUnivLESucc B S hS 𝒳
  let := Functor.commShiftRightDerivedFunctorPlus (fppfModuleSheafPushforwardOfStacks B S hS f)
  have := Functor.isTriangulated_rightDerivedFunctorPlus
    (fppfModuleSheafPushforwardOfStacks B S hS f)
  intro T hT
  exact ⟨_, Functor.map_distinguished
    (fppfModuleSheafPushforwardOfStacks B S hS f).rightDerivedFunctorPlus T hT⟩

/-- **The cohomology of a derived direct image, from the higher direct images of the
cohomology.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks, `P` an isomorphism-closed
class of fppf modules on `𝒳` and `Q` a weak Serre class of fppf modules on `𝒴`, and suppose that
every higher direct image `Rᵖf_*` (**Stacks 06WE**) carries `P` into `Q`. Then for every `K` in
`D⁺(𝒪_𝒳)` all of whose cohomology modules lie in `P`, every cohomology module of `Rf_*K` lies in
`Q`.

This is the spectral sequence `Rᵖf_*Hᵠ(K) ⇒ Rᵖ⁺ᵠf_*K` of the proof of **Stacks 07BC**: its second
page lies in `Q`, and a weak Serre class containing a page of a convergent bounded spectral
sequence contains its abutment (**Stacks 0132** part (4)). -/
theorem fppfDerivedPushforwardPlusOfStacks_obj_mem_of_higherDirectImage (f : 𝒳 ⟶ 𝒴)
    (P : ObjectProperty (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳))
    [P.IsClosedUnderIsomorphisms]
    (Q : ObjectProperty (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)) [Q.IsWeakSerreClass]
    (hPQ : ∀ M, P M → ∀ p : ℕ,
      Q ((moduleSheafHigherDirectImage.{u, u + 1, u, u + 1, u} B S hS 𝒳.val.val.p
        𝒴.val.val.p 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
        (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor_comp_p f.hom)
        (B.baseTopology .fppf) (B.baseTopology_le_topology .fppf) p).obj M))
    (K : DerivedCategory.Plus (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳))
    (hK : DerivedCategoryB.derivedCategoryB P (DerivedCategory.Plus.ι.obj K)) :
    DerivedCategoryB.derivedCategoryB Q
      (DerivedCategory.Plus.ι.obj ((fppfDerivedPushforwardPlusOfStacks B S hS f).obj K)) := by
  let := additive_fppfModuleSheafPushforwardOfStacks B S hS f
  let := enoughInjectives_fppfModulesUnivLESucc B S hS 𝒳
  exact (@Functor.derivedCategoryBPlus_rightDerivedFunctorPlus_obj _ _ _
    ‹HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒳)› _ _ _ _
    ‹HasDerivedCategory.{u + 2} (fppfModulesUnivLE.{u, w, u + 1} B S hS 𝒴)›
    (fppfModuleSheafPushforwardOfStacks B S hS f) _ P _ Q _ hPQ K (fun q => by exact hK q)).2

end AlgebraicGeometry.Stack

end
