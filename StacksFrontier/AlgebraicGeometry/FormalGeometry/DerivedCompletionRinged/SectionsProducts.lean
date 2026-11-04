module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.LocalCalculation
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Pushforward
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
import all StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
import StacksCore.Tactic.StacksAttribute

/-!
# Countable products and scalars for derived sections over an object

Let `(𝒞, 𝒪)` be a ringed site, `U` an object of `𝒞` and `ρ : A ⟶ 𝒪(U)` a ring map. This file
proves that `Γ(U, -)` and its total right derived functor `RΓ(U, -) : D(𝒪) ⥤ D(A)` of
`LocalCalculation.lean` commute with countable products, and that over a *terminal* object they
carry multiplication by a local section of `𝒪` to the scalar action.

These are two of the three hypotheses of
`AlgebraicGeometry.RingedSite.isDerivedCompleteAt_map_of_center`: an additive functor which
preserves the countable power of an object and which matches two scalars carries `T(K, a) = 0` to
`T(F K, b) = 0`.

## Main results

* `AlgebraicGeometry.RingedSite.preservesProducts_moduleSectionsOver`: `Γ(U, -)` preserves
  countable products.
* `AlgebraicGeometry.RingedSite.preservesProducts_derivedSectionsOver`: `RΓ(U, -)` preserves
  countable products.
* `AlgebraicGeometry.RingedSite.moduleSectionsOver_map_terminalSectionToEnd`: over a terminal
  object, `Γ(U, -)` carries multiplication by `ρ a` to multiplication by `a`.

## Implementation notes

*The underived statement.* `Γ(U, -)` is `SheafOfModules.evaluation` at `U` followed by
restriction of scalars along `ρ`. Limits of sheaves of modules are computed sectionwise, which
is Mathlib's `SheafOfModules.evaluationPreservesLimitsOfShape`, and restriction of scalars
preserves limits whose sections form a small type, which is
`ModuleCat.preservesLimit_restrictScalars`. The latter is applied pointwise rather than through
the `IsRightAdjoint` instance of restriction of scalars, which does not synthesize at these
universes.

*The derived statement.* The countable products of `D(𝒪)` are not termwise — a countable product
of epimorphisms of sheaves need not be an epimorphism, so Grothendieck's AB4* fails and the
products come from K-injective resolutions
(`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`). What makes the
derived functor preserve them anyway is that the *target* `ModuleCat A` does satisfy AB4*:
`Stacks.Injectives.preservesLimit_discrete_of_isRightDerivedFunctor` of
`StacksFrontier/Homology/Injectives/DerivedCategory/DerivedLimit.lean` derives product preservation
for a right derived functor of a product-preserving additive functor out of a Grothendieck
abelian category into such a target. That lemma is `private`, and is reached by `import all` of
its module rather than re-proved — the same device
`StacksFrontier/Homology/DerivedCategory/KInjectiveProducts.lean` uses for
`CochainComplex.isLimit_fan_Q_pi`. The public wrapper in that file,
`Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor` ([Stacks, Tag 08U1]), concludes about
derived limits of towers instead, which is not the `PreservesLimitsOfShape` instance that
`isDerivedCompleteAt_map_of_center` consumes.

*The scalar statement.* Multiplication by a section over a terminal object is
`Stacks.SheafOfModules.terminalSectionToEnd`, which is the spelling the derived-completeness
predicate of [Stacks, Tag 0999] uses. Over the terminal object itself the restriction map along
the unique arrow is the identity, so the endomorphism of the module of sections is multiplication
by the section; through `ρ` that is the action of `a`. A terminal object is what the predicate
lands one in: its condition at an object `U` of `𝒞` is tested on the slice site `𝒞/U`, where
`id : U ⟶ U` is terminal.

### What this does not give, and what is missing for [Stacks, Tag 0CQI]

The general case of [Stacks, Tag 0CQI] needs, as the first step of the source's argument for
[Stacks, Tag 0A0G], that `RΓ(U, -)` carry an object derived complete along `ℐ` to one derived
complete along `I = (f_1, …, f_r) ⊂ 𝒪(U)`, with no hypothesis on `ℐ`. The three inputs for that
are the two proved here and one that is not available: the derived-completeness predicate tests
`K` at `U` through its restriction `K|_U` to the slice site, so the transport has to be performed
by derived *global* sections on `(𝒞/U, 𝒪_U)`, and that requires the identification

```
RΓ(U, K) = RΓ(𝒞/U, K|_U)
```

as an isomorphism of functors `D(𝒪) ⥤ D(A)`. This library has it only after passing to cohomology
and only for sections with the module structure forgotten:
`Stacks.Cohomology.Localization.cohomologyOverObjectIsoRestriction` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/Localization/RestrictionOfModules.lean`
([Stacks, Tag 0D6F]) whiskers the functor comparison with a homology functor and is stated for
`AddCommGrpCat`-valued sections. The `A`-linear, functor-level form is what is needed and is not
proved; the ingredients of the uniqueness argument are all in that file
(`rightDerived_of_kInjectives`, `derivedUnit_isIsoOnKInjective`, `isKInjective_over`).

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
* [Stacks Project, Tag 0CQI](https://stacks.math.columbia.edu/tag/0CQI)
* [Stacks Project, Tag 0D6F](https://stacks.math.columbia.edu/tag/0D6F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard

section Products

variable (X : RingedSite.{u, u, u}) (U : X.C)
  {A : Type u} [CommRing A]
  (ρ : A →+* ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj (op U))

/-- **`Γ(U, -)` preserves countable products.** Limits of sheaves of modules are computed
sectionwise, and restriction of scalars preserves them. -/
instance preservesProducts_moduleSectionsOver :
    PreservesLimitsOfShape (Discrete ℕ) (moduleSectionsOver X U ρ) :=
  @comp_preservesLimitsOfShape _ _ _ _ _ _ _ _ _ _
    (SheafOfModules.evaluationPreservesLimitsOfShape _ _ _)
    { preservesLimit := fun {F} => ModuleCat.preservesLimit_restrictScalars ρ F }

/-- **`RΓ(U, -)` preserves countable products.** A right derived functor of an additive,
countable-product-preserving functor out of a Grothendieck abelian category does, as soon as the
target abelian category has exact countable products — which `ModuleCat A` has, and
`SheafOfModules 𝒪` has not. This is the instance
`AlgebraicGeometry.RingedSite.isDerivedCompleteAt_map_of_center` asks for. -/
instance preservesProducts_derivedSectionsOver :
    PreservesLimitsOfShape (Discrete ℕ) (derivedSectionsOver X U ρ) where
  preservesLimit {G} :=
    Stacks.Injectives.preservesLimit_discrete_of_isRightDerivedFunctor
      (moduleSectionsOver X U ρ) (derivedSectionsOver X U ρ)
      (derivedSectionsOverUnit X U ρ) G

/-- The structure sheaf of a ringed site is a sheaf of commutative rings, in the spelling
instance search needs for `Stacks.SheafOfModules.terminalSectionToEnd`. -/
instance isMulCommutative_ringSheafObj (V : X.Cᵒᵖ) :
    IsMulCommutative (((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.obj V) :=
  inferInstanceAs (IsMulCommutative (X.O.obj.obj V))

/-- **Sections over a terminal object turn multiplication by a section into the scalar action.**
If `T` is terminal and `a : A` acts on `𝒪`-modules by multiplication by `ρ a ∈ 𝒪(T)`, then
sections over `T` carry that multiplication to multiplication by `a` on the `A`-module of
sections, because restricting along the unique arrow `T ⟶ T` is the identity. -/
theorem moduleSectionsOver_map_terminalSectionToEnd (hT : IsTerminal U) (a : A)
    (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (moduleSectionsOver X U ρ).map
        ((Stacks.SheafOfModules.terminalSectionToEnd
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U hT (ρ a)).app M) =
      a • 𝟙 ((moduleSectionsOver X U ρ).obj M) := by
  have key :
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj.map (hT.from U).op (ρ a) = ρ a := by
    rw [show hT.from U = 𝟙 U from hT.hom_ext _ _]
    simp
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have h := Stacks.SheafOfModules.terminalSectionToEnd_apply
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U hT (ρ a) M (op U) x
  rw [key] at h
  exact h

end Products

end AlgebraicGeometry.RingedSite

end
