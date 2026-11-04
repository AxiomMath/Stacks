module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafifiedPullbackComparisonTransposeSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtalePullbackComparisonComposition

/-!
# Stacks 075D (1) for the sheafified comparison map of Stacks 06WC

`AlgebraicGeometry.Stack.restrictModulePullbackComparison_comp` is **Stacks 075D (1)** for the
comparison map

`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}`

of **Stacks 06WC**, as a law about *presheaves* of modules.  When `F` is locally quasi-coherent
(**Stacks 06WJ**) each restriction `F|_{U_ét}` is a *sheaf* on the small étale site, and the
identification of sections of **Stacks 076T** uses the comparison in its sheafified form: as the
morphism of sheaves of modules out of
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison` which the sheafification bijection
produces from `c_φ`.  This file carries the composition law to that form.

## Why this is not the presheaf law restated

The sheafified comparison is a morphism out of a value of a *left adjoint* — the sheafified
Stacks 06WC pullback — so it has no formula on sections, and neither does the interchange term
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` of the law, which is assembled out
of the comparisons that uniqueness of a left adjoint provides.  The law is therefore proved by
transposing it, which is exactly what
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison_map_comp_of_presheafHomEquiv` does: its
hypothesis is a law about the presheaf adjuncts, and
`AlgebraicGeometry.Stack.restrictModulePullbackComparison_adjunct` identifies the adjunct of
`c_φ` with the direct-image comparison of Stacks 06WC, where Stacks 075D (1) applies
on the nose.

## Main definitions

* `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleSheaf`: the restriction `F|_{U_ét}` of
  **Stacks 06WJ** read as a sheaf of modules on the small étale site, over the sheaf condition
  local quasi-coherence supplies, with
  `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleSheaf_val` reading off its underlying
  presheaf.

## Main results

* `AlgebraicGeometry.Stack.sheafifiedRestrictModulePullbackComparison_comp`: **Stacks 075D (1)
  for the sheafified comparison map of Stacks 06WC.**  The sheafified Stacks 06WC pullback along
  `φ` of the sheafified comparison below `ψ`, followed by the sheafified comparison below `φ`, is
  `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` followed by the sheafified
  comparison below `ψ ∘ φ`.

## Implementation notes

No hypothesis on the arrows is used, and neither comparison map is assumed invertible: clause (b)
of **Stacks 06WK** — invertibility over a whole slice `𝒳/x` — is strictly stronger than
hypothesis (b) of **Stacks 076T** and is nowhere needed for a composition law.  The only
hypotheses are the three sheaf conditions, one at each of the three objects, which is what makes
the sheafified form of the comparison exist at all.

Four definitions are locally irreducible for the one theorem:
`AlgebraicGeometry.smallEtaleBaseChange` and `CategoryTheory.Over.post`, which the comparison of
the two spellings of a pushforward would otherwise reduce to the pullback cones the base-change
functor is built from, and `AlgebraicGeometry.Stack.baseStructureSheaf` and
`AlgebraicGeometry.Stack.baseRingStructureSheaf`, which the restriction of scalars along the
identity would otherwise reduce the structure sheaf of **Stacks 06TV** to.  Without the
latter two, elaborating the statement alone exceeds four million heartbeats, reducing
`baseStructureSheaf` 11 580 times; with them the file checks in a second.  Nothing outside this
file sees the attribute, and no statement depends on it.

No Stacks tag is registered here.  Stacks 075D (1) is tagged where it is proved, on
`AlgebraicGeometry.Stack.restrictModulePullbackComparison_comp` and on the direct-image statement
it comes from; what this file does is carry that law across the sheafification bijection.

## References

* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v v₁

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)

/-- **The restriction `F|_{U_ét}` of Stacks 06WJ as a sheaf of modules on the small étale site of
the scheme below an object.**  The restriction is a presheaf of modules for any `F`; local
quasi-coherence makes it a sheaf, and that sheaf condition is the one argument here. -/
noncomputable def restrictModuleToSmallEtaleSheaf (w : 𝒳)
    (hw : Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj w).left.1 (contains_base B E h S hS p w))
      (restrictModuleToSmallEtale B E h S hS p hp w τ hτ F).presheaf) :
    SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj w).left.1
      (contains_base B E h S hS p w)) :=
  ⟨restrictModuleToSmallEtale B E h S hS p hp w τ hτ F, hw⟩

/-- The underlying presheaf of modules of
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleSheaf` is the restriction of Stacks 06WJ it is
built from.

The definition is deliberately not an `abbrev`.  Unification against it has to be stopped at the
sheaf: with the sheaf reducible, matching the source of a morphism out of the sheafified
Stacks 06WC pullback unfolds the restriction into the structure sheaf of Stacks 06TV that indexes
it, and that does not terminate inside any heartbeat budget. -/
theorem restrictModuleToSmallEtaleSheaf_val (w : 𝒳)
    (hw : Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj w).left.1 (contains_base B E h S hS p w))
      (restrictModuleToSmallEtale B E h S hS p hp w τ hτ F).presheaf) :
    (restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F w hw).val =
      restrictModuleToSmallEtale B E h S hS p hp w τ hτ F :=
  rfl

variable {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z)

attribute [local irreducible] AlgebraicGeometry.smallEtaleBaseChange CategoryTheory.Over.post
  AlgebraicGeometry.Stack.baseStructureSheaf AlgebraicGeometry.Stack.baseRingStructureSheaf

/-- **Stacks 075D (1) for the sheafified comparison map `c_φ` of Stacks 06WC.**  For arrows
`φ : x ⟶ y` and `ψ : y ⟶ z` of `𝒳` lying over morphisms of schemes `a : U ⟶ V` and `b : V ⟶ W`,
and a presheaf of modules `F` whose small étale restrictions at the three objects are sheaves,
the sheafified Stacks 06WC pullback along `φ` of the sheafified comparison below `ψ`, followed by
the sheafified comparison below `φ`, is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` followed by the sheafified
comparison below `ψ ∘ φ`.

Both sides are morphisms out of a value of a left adjoint, so the law is proved by transposing
it: `AlgebraicGeometry.Stack.sheafifiedPullbackComparison_map_comp_of_presheafHomEquiv` reduces
it to the corresponding law for the presheaf adjuncts,
`AlgebraicGeometry.Stack.restrictModulePullbackComparison_adjunct` identifies each of those
adjuncts with the direct-image comparison of Stacks 06WC, and what is left is
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_comp`.

No hypothesis on the arrows is used; in particular neither comparison map is assumed
invertible. -/
theorem sheafifiedRestrictModulePullbackComparison_comp
    (hx : Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).presheaf)
    (hy : Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj y).left.1 (contains_base B E h S hS p y))
      (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F).presheaf)
    (hz : Presheaf.IsSheaf
      (SmallEtale.topology E (p.obj z).left.1 (contains_base B E h S hS p z))
      (restrictModuleToSmallEtale B E h S hS p hp z τ hτ F).presheaf) :
    (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
          (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (SmallEtale.structureSheaf E (p.obj y).left.1
              (contains_base B E h S hS p y)).obj)).homEquiv _
                (restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F y hy)).symm
            (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F)) ≫
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv _
              (restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F x hx)).symm
          (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F) =
      (sheafifiedPullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).hom.app
          (restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F z hz) ≫
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj)).homEquiv _
              (restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F x hx)).symm
          (restrictModulePullbackComparison B E h S hS p hp (φ ≫ ψ) τ hτ F) := by
  have hadj : ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).homEquiv
          (restrictModuleToSmallEtale B E h S hS p hp z τ hτ F)
          (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)
          (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F) ≫
        (PresheafOfModules.pushforward.{u}
            (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).map
          ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
              (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv
            (restrictModuleToSmallEtale B E h S hS p hp y τ hτ F)
            (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F)
            (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F))) ≫
      presheafPushforwardCompCellAt B E h S hS p hp τ hτ φ ψ
          (restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F x hx) =
    (PresheafOfModules.pullbackPushforwardAdjunction.{u}
          (smallEtaleStructureComparison B E h S hS p hp (φ ≫ ψ) τ hτ)).homEquiv
        (restrictModuleToSmallEtale B E h S hS p hp z τ hτ F)
        (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F)
      (restrictModulePullbackComparison B E h S hS p hp (φ ≫ ψ) τ hτ F) := by
    rw [restrictModulePullbackComparison_adjunct, restrictModulePullbackComparison_adjunct,
      restrictModulePullbackComparison_adjunct, presheafPushforwardCompCellAt_eq]
    exact restrictModulePushforwardComparison_comp B E h S hS p hp τ hτ φ ψ F
  have key := sheafifiedPullbackComparison_map_comp_of_presheafHomEquiv
    B E h S hS p hp τ hτ φ ψ
    (𝒩 := restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F z hz)
    (𝒩' := restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F y hy)
    (𝓜 := restrictModuleToSmallEtaleSheaf B E h S hS p hp τ hτ F x hx)
    (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F)
    (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F)
    (restrictModulePullbackComparison B E h S hS p hp (φ ≫ ψ) τ hτ F) hadj
  exact key

end AlgebraicGeometry.Stack

end
