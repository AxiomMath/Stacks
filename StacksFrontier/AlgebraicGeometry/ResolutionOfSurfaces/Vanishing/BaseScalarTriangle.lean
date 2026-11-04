module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedGlobalSectionsSmul
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessLinear
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.ModificationATorsion

/-!
# The triangle of derived global sections of multiplication by a base scalar

Let `A` be a commutative ring and `X` a scheme over `Spec A`. For `a ∈ A` whose multiplication
on `𝒪_X` is injective, the short exact sequence

`0 ⟶ 𝒪_X ⟶ 𝒪_X ⟶ 𝒪_X/a𝒪_X ⟶ 0`

of multiplication by `a` and its cokernel gives, on applying `A`-linear derived global sections,
a distinguished triangle in `D(A)` **whose first morphism is multiplication by `a`**. That last
point is the whole content: a morphism out of an object killed by `a` — the residue field of a
local ring at a maximal ideal containing `a`, for instance — is annihilated by it, which is how
[Stacks, Tag 0AXC] factors such a morphism through the derived global sections of the cokernel.

## Main results

* `AlgebraicGeometry.baseSmulModules_eq_smul_id`: the bridge for the scalar. Multiplication by a
  base scalar in the form `AlgebraicGeometry.baseSmulModules` is the scalar action of
  `AlgebraicGeometry.modulesLinear` on the identity.
* `AlgebraicGeometry.baseSmulUnit_shortExact`: the sequence is short exact.
* `AlgebraicGeometry.shortComplexBridge`: the bridge for a short complex between the two
  spellings of the category of `𝒪_X`-modules.
* `AlgebraicGeometry.derivedGlobalSectionsSmulTriangle`, `..._distinguished` and `..._mor₁`: the
  triangle, that it is distinguished, and that its first morphism is `a • 𝟙`.

## Implementation notes

*Two spellings of one category, and the bridges between them.* The multiplication whose cokernel
[Stacks, Tag 0AXK] takes is `AlgebraicGeometry.baseSmulModules`, an endomorphism of a sheaf of
modules written at the `SheafOfModules X.ringCatSheaf` spelling of that category; the linearity
of derived global sections, `AlgebraicGeometry.derivedGlobalSectionsOver_map_smul_id`, is stated
for `X : Over (Spec (.of A))` with the scalar action of `AlgebraicGeometry.modulesLinear` at the
`X.left.Modules` spelling. The two spellings are definitionally equal but carry separately
declared `Category` and `Preadditive` instances which instance search does not cross, as the
implementation notes of `StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean` record, and
`modulesLinear` is a `def` and not an instance because the base ring is not determined by the
sheaf of rings — so it is introduced with `letI` wherever it is used, as
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/BaseRingLinear.lean` instructs.

Accordingly the crossings are made by passing terms, at two named bridges and nowhere else:
`baseSmulModules_eq_smul_id` for the scalar and `shortComplexBridge` for the sequence. A rewrite
cannot do this — its motive is elaborated at reducible transparency, where the two spellings are
distinct — while a term application needs no motive and defeq at default transparency suffices.

*The model.* `HasDerivedCategory` is supplied by the imported instances
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `ModuleCat.hasDerivedCategory`, the
locally small model, which is the model of the vanishing files that consume this file:
`Vanishing/PuncturedBaseCohomology.lean` and its two successors resolve the class the same way,
so `derivedGlobalSectionsSmulTriangle` has `AlgebraicGeometry.derivedGlobalSectionsStructureSheaf`
as its first vertex on the nose. A `attribute [local instance] HasDerivedCategory.standard` line
here would be inert — those imported instances win against it — and raising it to a high priority
would move the triangle into the standard model, where it no longer meets the statement of
[Stacks, Tag 0AXC]. The one statement that had to be generalised for this is
`AlgebraicGeometry.derivedGlobalSectionsOver_map_smul_id` of
`StacksFrontier/AlgebraicGeometry/ProperSupportCoherent/ExtFinitenessLinear.lean`, whose file does
raise `HasDerivedCategory.standard` to a high priority; the generalisation
`AlgebraicGeometry.derivedGlobalSectionsOver_map_smul_id_of_hasDerivedCategory` takes the two
`HasDerivedCategory`
instances as binders and so holds in either model, and is the form used here.

## References

* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
* [Stacks Project, Tag 0AXK](https://stacks.math.columbia.edu/tag/0AXK)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] (X : Over (Spec (CommRingCat.of A)))

/-- **The bridge between the two spellings of multiplication by a base scalar.**
`AlgebraicGeometry.baseSmulModules`, written at the `SheafOfModules X.ringCatSheaf` spelling of
the category of `𝒪_X`-modules, is the scalar action of `AlgebraicGeometry.modulesLinear` on the
identity, written at the `X.left.Modules` spelling. Both act on sections over an open by the
image of the scalar in the functions on that open. -/
theorem baseSmulModules_eq_smul_id (a : A) (M : X.left.Modules) :
    letI : Linear A X.left.Modules := modulesLinear A X
    baseSmulModules X.left X.hom a M = a • 𝟙 M := by
  let : Linear A X.left.Modules := modulesLinear A X
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  ext x
  rfl

/-- **The sequence `0 ⟶ 𝒪_X ⟶ 𝒪_X ⟶ 𝒪_X/a𝒪_X ⟶ 0` of multiplication by a base scalar is short
exact**, as soon as that multiplication is injective. It is stated at the
`SheafOfModules X.ringCatSheaf` spelling, and before the derived category enters, because that
is where the cokernel instances of the category are found. -/
theorem baseSmulUnit_shortExact (a : A)
    (hmono : Mono (baseSmulModules X.left X.hom a
      (SheafOfModules.unit X.left.ringCatSheaf))) :
    (ShortComplex.cokernelSequence (baseSmulModules X.left X.hom a
      (SheafOfModules.unit X.left.ringCatSheaf))).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := hmono
  epi_g := inferInstance

/-- **The bridge for a short complex.** A short complex of `𝒪_X`-modules written at the
`SheafOfModules X.ringCatSheaf` spelling, read at the `X.left.Modules` spelling. The two
categories are definitionally equal but carry separately declared `Category` and `Preadditive`
instances, so the crossing is made here, once, by passing a term. -/
def shortComplexBridge (S : ShortComplex (SheafOfModules.{u} X.left.ringCatSheaf)) :
    ShortComplex X.left.Modules := S

/-- Short exactness crosses the bridge: it is the same three conditions. -/
theorem shortExact_shortComplexBridge
    {S : ShortComplex (SheafOfModules.{u} X.left.ringCatSheaf)} (hS : S.ShortExact) :
    (shortComplexBridge X S).ShortExact := hS


/-- **The triangle `RΓ(X, 𝒪_X) ⟶ RΓ(X, 𝒪_X) ⟶ RΓ(X, 𝒪_X/a𝒪_X) ⟶` in `D(A)`**, the image under
`A`-linear derived global sections of the triangle of the short exact sequence of multiplication
by a base scalar. -/
def derivedGlobalSectionsSmulTriangle (a : A)
    (hmono : Mono (baseSmulModules X.left X.hom a
      (SheafOfModules.unit X.left.ringCatSheaf))) :
    Triangle (DerivedCategory (ModuleCat.{u} A)) :=
  (derivedGlobalSectionsOver X.hom).mapTriangle.obj
    (shortExact_shortComplexBridge X (baseSmulUnit_shortExact X a hmono)).singleTriangle

/-- The triangle is distinguished: `A`-linear derived global sections is a triangulated
functor. -/
theorem derivedGlobalSectionsSmulTriangle_distinguished (a : A)
    (hmono : Mono (baseSmulModules X.left X.hom a
      (SheafOfModules.unit X.left.ringCatSheaf))) :
    derivedGlobalSectionsSmulTriangle X a hmono ∈
      distTriang (DerivedCategory (ModuleCat.{u} A)) :=
  (derivedGlobalSectionsOver X.hom).map_distinguished _
    (shortExact_shortComplexBridge X
      (baseSmulUnit_shortExact X a hmono)).singleTriangle_distinguished

/-- **The first morphism of the triangle is multiplication by the scalar.** The single functor
and `A`-linear derived global sections are both `A`-linear, so each carries `a • 𝟙` to `a • 𝟙`;
the bridge `baseSmulModules_eq_smul_id` is what puts the multiplication in that form. -/
theorem derivedGlobalSectionsSmulTriangle_mor₁ (a : A)
    (hmono : Mono (baseSmulModules X.left X.hom a
      (SheafOfModules.unit X.left.ringCatSheaf))) :
    (derivedGlobalSectionsSmulTriangle X a hmono).mor₁ =
      a • 𝟙 ((derivedGlobalSectionsSmulTriangle X a hmono).obj₁) := by
  let : Linear A X.left.Modules := modulesLinear A X
  change (derivedGlobalSectionsOver X.hom).map
      ((DerivedCategory.singleFunctor X.left.Modules 0).map
        (baseSmulModules X.left X.hom a X.left.unitModule)) = _
  rw [baseSmulModules_eq_smul_id, Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  exact derivedGlobalSectionsOver_map_smul_id_of_hasDerivedCategory X a _

end AlgebraicGeometry

end
