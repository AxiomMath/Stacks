module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.InjectiveTensor
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.HigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite

/-!
# The projection formula for the higher direct images along a finite locally free module

Let `f : X ⟶ Y` be a morphism of schemes, `ℱ` an `𝒪_X`-module and `ℰ` a **finite locally free**
`𝒪_Y`-module in the sense of [Stacks, Tag 01C6]. This file proves the two clauses of
[Stacks, Tag 01E8] that `StacksFrontier/AlgebraicGeometry/ProjectionFormula/HigherDirectImage.lean`
proves only for an *invertible* `ℰ`:

* `R^q f_*(ℱ ⊗_{𝒪_X} f^*ℰ) ≅ (R^q f_*ℱ) ⊗_{𝒪_Y} ℰ` for every `q`, naturally in `ℱ`;
* the same in the bounded below derived category, `D(- ⊗ f^*ℰ) ⋙ Rf_* ≅ Rf_* ⋙ D(- ⊗ ℰ)`.

Rank one is not assumed anywhere, and there is no hypothesis on `f`, on `ℱ` or on the degree.

## Main results

* `Stacks.ProjectionFormula.derivedPushforwardTensorRightFiniteLocallyFreePlusIso`: **the `D⁺`
  clause of [Stacks, Tag 01E8]** for a finite locally free module.
* `Stacks.ProjectionFormula.higherDirectImageProjectionFormulaFiniteLocallyFreeIso`: **the higher
  direct image clause of [Stacks, Tag 01E8]** for a finite locally free module.

## Main definitions

* `Stacks.ProjectionFormula.tensorRightOfIsoTensorRight`: the identification of tensoring on
  the right in the tensor-product bifunctor of a ringed space with tensoring on the right in the
  monoidal structure of `Stacks.SheafOfModules.OnSpace.monoidal`.
* `Stacks.ProjectionFormula.pushforwardTensorRightFiniteLocallyFreeNatIso`: the degree-zero
  formula as a natural isomorphism of functors.

## The route, and why it is the source's own

[Stacks, Tag 01E8] argues as follows. Choose an injective resolution `ℱ → ℐ^•`. Since `f^*ℰ` is
finite locally free too, `f^*ℰ ⊗_{𝒪_X} ℐ^•` is *again* an injective resolution, by
[Stacks, Tag 01E7]; so `Rf_*(ℱ ⊗ f^*ℰ)` is computed by `f_*(ℐ^• ⊗ f^*ℰ)`, and everything reduces
to the degree-zero identity `f_*(𝒢 ⊗_{𝒪_X} f^*ℰ) ≅ f_*𝒢 ⊗_{𝒪_Y} ℰ` natural in `𝒢`, which is
"immediate for a free module, and the general case follows by working locally on `Y`".

Both halves of that are already in this repository, and this file does no new mathematics.

* The degree-zero identity, in exactly the tag's generality on `ℰ`, is
  `Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree` — the
  locality-on-the-target argument of `ProjectionFormula/Locality.lean` run at the local free
  model. Its invertibility statement is about
  `Stacks.AffineProjectionFormula.projectionFormulaMap`, which is the *same term* as the
  `Stacks.ProjectionFormula.projectionFormulaMap'` that `pushforwardTensorRightNatTrans` is
  assembled from: both are `adjunctionTensorMap` of the pullback adjunction at the comparison of
  [Stacks, Tag 01CD], so the two cross by `rfl`.
* [Stacks, Tag 01E7] is
  `Stacks.SheafOfModules.OnSpace.injective_tensorSheaf_of_finiteLocallyFree`, for a ringed space
  and a general finite locally free module. It is what replaces the observation, available only
  in the invertible case, that tensoring is an *equivalence* and therefore preserves injectives
  for free; the module documentation of `ProjectionFormula/HigherDirectImage.lean` records that
  the invertible proof does not need Tag 01E7, which is true of that proof only.

With those two, the engine is the same one the invertible case uses:
`Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`, which asks of the two tensor
functors only that they be *additive and exact* — never that they be equivalences — and asks of
the first that it carry injectives to objects right acyclic for `f_*`.

## Implementation notes

*Exactness of `- ⊗ ℰ` comes from the left dual, not from flatness.* A finite locally free module
is locally a direct summand of a finite free one
(`Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree`), hence has a
left dual `ℰ^∨` by [Stacks, Tag 0FNV] (`Stacks.SheafOfModules.OnSpace.dualSheafExactPairing`).
An exact pairing gives *both* adjunctions `- ⊗ ℰ ⊣ - ⊗ ℰ^∨` and `ℰ^∨ ⊗ - ⊣ ℰ ⊗ -`, so `- ⊗ ℰ`
is a left adjoint — whence it preserves colimits — and, transported across the braiding
`Stacks.SheafOfModules.OnSpace.tensorLeftTensorRightIso`, a right adjoint too — whence it
preserves limits. This is the same package
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/LocallyFiniteFreeSummand/InjectiveTensor.lean`
uses for Tag 01E7, so no new flatness theory is needed and the competing `IsFlat` spellings are not
touched.

*The monoidal spelling and the bifunctor spelling.* `tensorRightInvertible` is tensoring on the
right in the tensor-product *bifunctor* `Stacks.RingedSpace.tensorSheaf`, while the dual and its
adjunctions live in the *monoidal* structure `Stacks.SheafOfModules.OnSpace.monoidal`. The two
agree: on objects by `rfl` (`Stacks.ProjectionFormula.tensorRightInvertible_obj` and
`monoidal_tensorObj`), and on morphisms by
`Stacks.SheafOfModules.OnSpace.tensorHom_eq`. `tensorRightOfIsoTensorRight` is that
identification, and it is the only new plumbing in this file. Crossing it, and crossing the
finite-local-freeness hypothesis, is done by supplying the instance arguments positionally: the
two spellings of the structure sheaf of rings are equal by `rfl`, so a `@`-application
typechecks, while instance *synthesis* does not cross between them.

*Which of the several spellings of Tag 01C6 is the hypothesis.* The class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`, the one carrying the attribute for
[Stacks, Tag 01C6], is used, because it is what Tag 01E7 and the pullback statement
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme` ask for. The degree-zero
theorem instead asks for the pointwise predicate
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree` written out; the two are the same notion
and `Stacks.Modules.isFiniteLocallyFree_iff_localGenerators` is the passage between them. No new
bridge is written here.

*The tag's conclusion is read with the two tensor factors exchanged*, as in
`ProjectionFormula/FiniteLocallyFree.lean`. [Stacks, Tag 01E8] asserts
`ℰ ⊗_{𝒪_Y} R^q f_*ℱ ≅ R^q f_*(f^*ℰ ⊗_{𝒪_X} ℱ)`, while the isomorphisms here go
`R^q f_*(ℱ ⊗_{𝒪_X} f^*ℰ) ≅ (R^q f_*ℱ) ⊗_{𝒪_Y} ℰ`; the two differ by the symmetry of the tensor
product on each side, which is an isomorphism of the source with the source and of the target
with the target, and by the direction of an isomorphism. The tag's "functorial in `ℱ`" is
literal here: the `D⁺` clause and the degreewise clause are isomorphisms of *functors*, and the
module-level statement is one of them evaluated at `ℱ`.

*`tensorRightInvertible` has no invertibility in it.* Despite its name it is literally
`Stacks.ProjectionFormula.tensorRightOf` at the tensor-product bifunctor of a ringed space, with
no hypothesis on the module; likewise `pushforwardTensorRightNatTrans`. Both are reused verbatim.

*What this file does not do.* It does not lift the restriction to a morphism of *schemes*; that
is `ProjectionFormula/HigherDirectImageRingedSpace.lean`. Nothing in the present file adds a
scheme hypothesis of its own — Tag 01E7, the dual, the exactness and the derived base change are
all stated for ringed spaces or for arbitrary abelian categories — and the scheme hypothesis
enters only through the degree-zero clause, where `ProjectionFormula/Locality.lean` glues
invertibility of the projection-formula map over an open cover of the target using the
restriction functor of a scheme and base change along the restriction square. Both of those have
ringed-space counterparts in the library, and
`ProjectionFormula/LocalityRingedSpace.lean` runs the same gluing with them; the statements here
are kept because they are cheaper and have consumers.

*What is not claimed.* As in the invertible case, the isomorphism is not identified with a
canonical map in positive degree; none is constructed anywhere in this development. In degree
zero it *is* the canonical map, by construction.

## References

* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 01E7](https://stacks.math.columbia.edu/tag/01E7)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf TopCat.Presheaf.IsSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.RingedSpace
open scoped CategoryTheory.Prod

universe u

namespace Stacks.ProjectionFormula

attribute [local instance] HasDerivedCategory.standard

-- As in `ProjectionFormula/HigherDirectImage.lean`: instance search reaches for
-- `HomotopyCategory.Plus.hasPointwiseRightDerivedFunctorAt_of_injective`, which applies at an
-- arbitrary object, before the instance deducing the same conclusion from `EnoughInjectives`.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### Tensoring on the right by a finite locally free module is exact -/

section Exact

attribute [local instance] Stacks.SheafOfModules.OnSpace.monoidal

open MonoidalCategory

/-- **The bifunctor spelling of tensoring on the right is the monoidal one.** On objects the two
agree by `rfl`; on morphisms
`Stacks.SheafOfModules.OnSpace.tensorHom_eq` together with
`CategoryTheory.MonoidalCategory.tensorHom_id` rewrites the monoidal whiskering to the same
thing.

The ambient category is ascribed at the
`Stacks.SheafOfModules.TensorStalkRingedSpace.structureSheafRing` spelling, because that is the
one carrying the monoidal instance; left to itself, `tensorRightOf` at
`Stacks.RingedSpace.tensorSheaf` would fix it at `Stacks.RingedSpace.structureRingSheaf`, which
is the same sheaf of rings by `rfl` but a different key for instance synthesis. The naturality
square is assembled as a term rather than by `rw`, because a rewrite motive is checked at a
transparency at which those two spellings are not yet equal. -/
def tensorRightOfIsoTensorRight (W : AlgebraicGeometry.RingedSpace.{u, u})
    (E : SheafOfModules.{u} (structureSheafRing W)) :
    tensorRightOf (C := SheafOfModules.{u} (structureSheafRing W))
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.sheaf)))
        E ≅ MonoidalCategory.tensorRight E :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B g
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact (Stacks.SheafOfModules.OnSpace.tensorHom_eq W g (𝟙 E)).symm.trans
      (tensorHom_id g E))

section RingedSpace

variable (W : AlgebraicGeometry.RingedSpace.{u, u})
  (E : SheafOfModules.{u} (structureSheafRing W))
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- A finite locally free module has a left dual, by [Stacks, Tag 0FNV]. -/
private theorem nonempty_exactPairing_dualSheaf :
    Nonempty (ExactPairing E (Stacks.SheafOfModules.OnSpace.dualSheaf W E)) :=
  ⟨Stacks.SheafOfModules.OnSpace.dualSheafExactPairing W E
    (Stacks.SheafOfModules.OnSpace.isLocallyFiniteFreeSummand_of_isFiniteLocallyFree W E)⟩

/-- **Tensoring on the right by a finite locally free module is a left adjoint**, with right
adjoint `- ⊗ ℰ^∨`: a finite locally free module is locally a direct summand of a finite free one,
so it has a left dual by [Stacks, Tag 0FNV]. -/
theorem isLeftAdjoint_tensorRight : Functor.IsLeftAdjoint (MonoidalCategory.tensorRight E) := by
  obtain ⟨_⟩ := nonempty_exactPairing_dualSheaf W E
  exact (tensorRightAdjunction E
    (Stacks.SheafOfModules.OnSpace.dualSheaf W E)).isLeftAdjoint

/-- **Tensoring on the left by a finite locally free module is a right adjoint**, with left
adjoint `ℰ^∨ ⊗ -`: the same left dual of [Stacks, Tag 0FNV], read on the other side. -/
theorem isRightAdjoint_tensorLeft : Functor.IsRightAdjoint (MonoidalCategory.tensorLeft E) := by
  obtain ⟨_⟩ := nonempty_exactPairing_dualSheaf W E
  exact (tensorLeftAdjunction E
    (Stacks.SheafOfModules.OnSpace.dualSheaf W E)).isRightAdjoint

/-- `- ⊗ ℰ` preserves finite colimits, being a left adjoint. -/
theorem preservesFiniteColimits_tensorRight :
    PreservesFiniteColimits (MonoidalCategory.tensorRight E) := by
  have := isLeftAdjoint_tensorRight W E
  infer_instance

/-- `- ⊗ ℰ` preserves zero morphisms, being a left adjoint. -/
theorem preservesZeroMorphisms_tensorRight :
    (MonoidalCategory.tensorRight E).PreservesZeroMorphisms := by
  have := isLeftAdjoint_tensorRight W E
  infer_instance

/-- `- ⊗ ℰ` preserves finite limits: `ℰ ⊗ -` is a right adjoint, and the braiding
`Stacks.SheafOfModules.OnSpace.tensorLeftTensorRightIso` identifies the two. -/
theorem preservesFiniteLimits_tensorRight :
    PreservesFiniteLimits (MonoidalCategory.tensorRight E) := by
  have := isRightAdjoint_tensorLeft W E
  have : PreservesFiniteLimits (MonoidalCategory.tensorLeft E) := inferInstance
  exact preservesFiniteLimits_of_natIso
    (Stacks.SheafOfModules.OnSpace.tensorLeftTensorRightIso W E)

end RingedSpace

section SchemeSpelling

variable (Z : Scheme.{u}) (E : Z.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- The finite local freeness of `ℰ`, re-spelled at the ringed space `Z.toRingedSpace`. It has to
be a declaration of its own: the hypothesis cannot be re-ascribed inline inside the
`@`-applications below. -/
theorem isFiniteLocallyFree_toRingedSpace :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (E : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) := hE

/-- **Tensoring on the right by a finite locally free module preserves finite limits.** -/
instance preservesFiniteLimits_tensorRight_of_isFiniteLocallyFree :
    PreservesFiniteLimits (tensorRightInvertible Z E) := by
  have h1 : PreservesFiniteLimits (MonoidalCategory.tensorRight
      (C := SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) E) :=
    @preservesFiniteLimits_tensorRight Z.toRingedSpace E (isFiniteLocallyFree_toRingedSpace Z E)
  exact @preservesFiniteLimits_of_natIso _ _ _ _ _ _
    (tensorRightOfIsoTensorRight Z.toRingedSpace E).symm h1

/-- **Tensoring on the right by a finite locally free module preserves finite colimits.** -/
instance preservesFiniteColimits_tensorRight_of_isFiniteLocallyFree :
    PreservesFiniteColimits (tensorRightInvertible Z E) := by
  have h1 : PreservesFiniteColimits (MonoidalCategory.tensorRight
      (C := SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) E) :=
    @preservesFiniteColimits_tensorRight Z.toRingedSpace E (isFiniteLocallyFree_toRingedSpace Z E)
  exact @preservesFiniteColimits_of_natIso _ _ _ _ _ _
    (tensorRightOfIsoTensorRight Z.toRingedSpace E).symm h1

/-- **Tensoring on the right by a finite locally free module is additive**, preserving binary
products and the zero object. -/
instance additive_tensorRight_of_isFiniteLocallyFree : (tensorRightInvertible Z E).Additive := by
  have := preservesFiniteLimits_tensorRight_of_isFiniteLocallyFree Z E
  have : (tensorRightInvertible Z E).PreservesZeroMorphisms := by
    have h0 : (MonoidalCategory.tensorRight
        (C := SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) E).PreservesZeroMorphisms :=
      @preservesZeroMorphisms_tensorRight Z.toRingedSpace E (isFiniteLocallyFree_toRingedSpace Z E)
    exact @Functor.preservesZeroMorphisms_of_iso _ _ _ _ _ _ _ _ h0
      (tensorRightOfIsoTensorRight Z.toRingedSpace E).symm
  exact Functor.additive_of_preserves_binary_products _

/-- **[Stacks, Tag 01E7]**: an injective module tensored on the right by a finite locally free
module is injective. This is
`Stacks.SheafOfModules.OnSpace.injective_tensorSheaf_of_finiteLocallyFree` with the two tensor
factors exchanged along the braiding of the tensor product. -/
theorem injective_tensorRightInvertible_obj_of_isFiniteLocallyFree (I : Z.Modules)
    (hI : Injective I) :
    Injective ((tensorRightInvertible Z E).obj I) := by
  have hI' : Injective (I : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) := hI
  have h : Injective
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.sheaf).obj (E)).obj (I))) :=
    @Stacks.SheafOfModules.OnSpace.injective_tensorSheaf_of_finiteLocallyFree
      Z.toRingedSpace I E hI' (isFiniteLocallyFree_toRingedSpace Z E)
  exact Injective.of_iso
    (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap Z.toRingedSpace E I) h

end SchemeSpelling

end Exact

/-! ### The degree-zero formula, as a natural isomorphism -/

section Zero

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Y.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **[Stacks, Tag 01C6] is stable under inverse image**: the pullback of a finite locally free
module is finite locally free. This is
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme`, made an instance at the
`AlgebraicGeometry.Scheme.Modules.pullback` spelling, which instance search does not reach on its
own. -/
@[ega "0 5.4.5" "special case"]
instance isFiniteLocallyFree_schemeModulesPullback :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.pullback_scheme f E hE

/-- **The projection formula for a finite locally free module, in degree zero and naturally in
the module on the source**: `(- ⊗_{𝒪_X} f^*ℰ) ⋙ f_* ≅ f_* ⋙ (- ⊗_{𝒪_Y} ℰ)`. Each component is
invertible by
`Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree`, whose
hypothesis is the pointwise form of finite local freeness that
`Stacks.Modules.isFiniteLocallyFree_iff_localGenerators` supplies. -/
def pushforwardTensorRightFiniteLocallyFreeNatIso :
    tensorRightInvertible X ((Scheme.Modules.pullback f).obj E) ⋙
        Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward f ⋙ tensorRightInvertible Y E :=
  haveI : ∀ A, IsIso ((pushforwardTensorRightNatTrans f E).app A) := fun A =>
    Stacks.AffineProjectionFormula.isIso_projectionFormulaMap_of_isFiniteLocallyFree f A E
      fun x => (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators E).mpr hE x
  haveI := NatIso.isIso_of_isIso_app (pushforwardTensorRightNatTrans f E)
  (asIso (pushforwardTensorRightNatTrans f E)).symm

/-- **An injective module tensored by `f^*ℰ` is right acyclic for `f_*`**: it is again
injective by [Stacks, Tag 01E7], `f^*ℰ` being finite locally free, and an injective object is
right acyclic for every additive functor ([Stacks, Tag 0157]). -/
theorem rightAcyclic_pushforward_tensorRightFiniteLocallyFree (I : X.Modules)
    (hI : Injective I) :
    (Scheme.Modules.pushforward f).rightAcyclic
      ((tensorRightInvertible X ((Scheme.Modules.pullback f).obj E)).obj I) :=
  have := injective_tensorRightInvertible_obj_of_isFiniteLocallyFree X
    ((Scheme.Modules.pullback f).obj E) I hI
  Functor.rightAcyclic_of_injective (Scheme.Modules.pushforward f) _

end Zero

/-! ### The projection formula in every degree, and in `D⁺` -/

section Higher

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : Y.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The projection formula in `D⁺` for a morphism of schemes**: for `f : X ⟶ Y` and a
**finite locally free** `𝒪_Y`-module `ℰ`,

`D(- ⊗_{𝒪_X} f^*ℰ) ⋙ Rf_* ≅ Rf_* ⋙ D(- ⊗_{𝒪_Y} ℰ)`

as functors `D⁺(𝒪_X) ⥤ D⁺(𝒪_Y)`: the projection formula in the bounded below derived category,
for an arbitrary morphism of schemes, every object of `D⁺(𝒪_X)` and `ℰ` of arbitrary rank.

Tensoring by a finite locally free module is additive and exact, by the left dual of
[Stacks, Tag 0FNV], and carries injectives to injectives by [Stacks, Tag 01E7]; the degree-zero
formula `pushforwardTensorRightFiniteLocallyFreeNatIso` is then upgraded to the derived
categories by `Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso`. -/
def derivedPushforwardTensorRightFiniteLocallyFreePlusIso :
    (tensorRightInvertible X ((Scheme.Modules.pullback f).obj E)).mapDerivedCategoryPlus ⋙
        (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ≅
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
        (tensorRightInvertible Y E).mapDerivedCategoryPlus :=
  Stacks.Cohomology.BoundedBelowComplexes.derivedBaseChangePlusIso
    (tensorRightInvertible X ((Scheme.Modules.pullback f).obj E))
    (tensorRightInvertible Y E)
    (Scheme.Modules.pushforward f) (Scheme.Modules.pushforward f)
    (pushforwardTensorRightFiniteLocallyFreeNatIso f E)
    (rightAcyclic_pushforward_tensorRightFiniteLocallyFree f E)

/-- **The projection formula for the higher direct images along a finite locally free module, as
a natural isomorphism of functors**: `(- ⊗_{𝒪_X} f^*ℰ) ⋙ R^n f_* ≅ R^n f_* ⋙ (- ⊗_{𝒪_Y} ℰ)`,
for every integer `n`, for an arbitrary morphism of schemes.

Since `R^n f_* = (·[0]) ⋙ Rf_* ⋙ H^n`, this is read off the `D⁺` clause by the two comparisons
an exact functor satisfies on `D⁺`:
`Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle` and
`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`. -/
def higherDirectImageTensorRightFiniteLocallyFreeIso (n : ℤ) :
    tensorRightInvertible X ((Scheme.Modules.pullback f).obj E) ⋙
        (Scheme.Modules.pushforward f).rightDerivedPlus n ≅
      (Scheme.Modules.pushforward f).rightDerivedPlus n ⋙ tensorRightInvertible Y E :=
  Functor.isoWhiskerRight
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (tensorRightInvertible X ((Scheme.Modules.pullback f).obj E)) 0).symm
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor Y.Modules n) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor X.Modules 0)
      (Functor.isoWhiskerRight (derivedPushforwardTensorRightFiniteLocallyFreePlusIso f E)
        (DerivedCategory.Plus.homologyFunctor Y.Modules n)) ≪≫
    Functor.isoWhiskerLeft
      (DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
        (Scheme.Modules.pushforward f).rightDerivedFunctorPlus)
      (Functor.isoWhiskerRight
          (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusIso (tensorRightInvertible Y E))
          (DerivedCategory.Plus.homologyFunctor Y.Modules n) ≪≫
        Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (tensorRightInvertible Y E) n)

/-- **The projection formula for higher direct images along a morphism of schemes**: for
`f : X ⟶ Y`, an arbitrary `𝒪_X`-module `ℱ` and a **finite locally free** `𝒪_Y`-module `ℰ`,

`R^n f_*(ℱ ⊗_{𝒪_X} f^*ℰ) ≅ (R^n f_*ℱ) ⊗_{𝒪_Y} ℰ`

for every integer `n`. This is `higherDirectImageTensorRightFiniteLocallyFreeIso` evaluated at
`ℱ`. The tag's `q ≥ 0` is the case `n = (q : ℤ)`; nothing in the argument restricts the degree. -/
def higherDirectImageProjectionFormulaFiniteLocallyFreeIso (F : X.Modules) (n : ℤ) :
    ((Scheme.Modules.pushforward f).rightDerivedPlus n).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj (F)).obj
          (((Scheme.Modules.pullback f).obj E)))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj
          ((((Scheme.Modules.pushforward f).rightDerivedPlus n).obj F))).obj (E)) :=
  (higherDirectImageTensorRightFiniteLocallyFreeIso f E n).app F

end Higher

end Stacks.ProjectionFormula

end
