module

public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertible
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingFunctorBridge
public import StacksFrontier.RingTheory.Dualizing.InvertibleHomologySingle
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.StalkInvertibleCanonical
import all StacksFrontier.RingTheory.Dualizing.InvertibleHomologySingle

/-!
# An invertible dualizing complex makes the scheme Gorenstein

Let `X` be a locally Noetherian scheme carrying a dualizing complex `ω_X^•`
(`Stacks.Duality.IsDualizingComplex`, [Stacks, Tag 0A87]). This file proves the direction

**`ω_X^•` is an invertible object of `D(𝒪_X)` ⟹ `X` is Gorenstein**

of [Stacks, Tag 0BFQ], clause (1)(a).

## Main definitions

* `AlgebraicGeometry.derivedStalkSpellingFunctorIsoAnyModel` — the comparison of the two
  spellings of the derived stalk functor, at an **arbitrary** model of `D(𝒪_X)`.

## Main results

* `Stacks.Duality.isInvertible_derivedStalkFunctor_of_isInvertible` — an invertible object of
  `D(𝒪_X)` has invertible derived stalks, in the local-ring spelling `D(𝒪_{X,x})`.
* `Stacks.Duality.isGorenstein_of_isInvertible_dualizingComplex` — the direction
  "invertible ⟹ Gorenstein" of [Stacks, Tag 0BFQ], clause (1)(a). The clause itself, as an
  equivalence, is `Stacks.Duality.isGorenstein_iff_isInvertible_dualizingComplex`.

## What was already there, and what this adds

Clause (1)(a) is a statement about *Gorensteinness*: `X` is Gorenstein if and only if `ω_X^•` is
invertible. What the library provides beforehand is the stalkwise
*input* to the direction proved here —
`Stacks.SheafOfModules.DerivedTensorStalk.isInvertible_derivedStalk`, "an invertible object of
`D(𝒪)` has an invertible derived stalk at every point" — which says nothing about Gorensteinness
on its own. Composing it with clause (1)(b),
`Stacks.Duality.isGorensteinLocalRing_stalk_iff_isInvertible_derivedStalk`, is what produces the
clause, and the composition is not immediate: the two are stated over the two different spellings
of the stalk ring, and crossing between them is the work of this file.

## The converse

The converse — `X` Gorenstein ⟹ `ω_X^•` invertible in `D(𝒪_X)` — is
`Stacks.Duality.isInvertible_dualizingComplex_of_isGorenstein`, and the equivalence is
`Stacks.Duality.isGorenstein_iff_isInvertible_dualizingComplex`, both in
`StacksFrontier/AlgebraicGeometry/Duality/GorensteinSchemes/DualizingInvertible.lean`. It is not a
stalkwise argument: passing through stalks does not help, because invertibility of an object is
not a stalkwise condition. It follows the source, affine locally: over an affine open the
dualizing complex is the complex associated to a dualizing complex over a Gorenstein ring, which
is invertible, and invertibility in `D(𝒪_X)` is local on a covering by opens
(`Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction`), through the
mate of the slice tensor comparison being an isomorphism
(`Stacks.Cohomology.SliceDerivedSheafHom.isIso_derivedSheafHomRestrictionTranspose`).

## Implementation notes

*Two spellings of the stalk ring, and why they have to be crossed.* The stalkwise input
is over `Stacks.SheafOfModules.DerivedTensorStalk.stalkRing X.sheaf x`, the `RingCat`-valued stalk
of the sheaf of rings, because that is the ring
`AlgebraicGeometry.SheafOfModules.stalkFunctor` takes its modules over. Clause (1)(b) is over the
local ring `𝒪_{X,x} = X.presheaf.stalk x`, the `CommRingCat`-valued stalk, because that is what
"`𝒪_{X,x}` is Gorenstein" is about. The two rings are isomorphic, by
`AlgebraicGeometry.ringCatStalkRingEquiv`, and not equal.

The crossing is not done by transporting a monoidal structure. It goes through the characterisation
of invertibility over a local ring as *being a shifted copy of the ring*,
`Dualizing.isInvertible_iff_exists_iso_single`: that is a statement about one object, so it
transports along `Dualizing.restrictScalarsEquivSingleIso` — restriction of scalars along a ring
isomorphism takes the ring in degree `n` to the ring in degree `n` — with no coherence to check.
The local-ring hypothesis at the `RingCat` spelling is `IsLocalRing` moved across the same ring
equivalence.

*Extending the derived-stalk spelling bridge to an arbitrary model.*
`AlgebraicGeometry.derivedStalkSpellingFunctorIso` and
`AlgebraicGeometry.derivedStalkSpellingFunctorIsoOfRingSheaf` are stated at
`HasDerivedCategory.standard`, and not by choice: they mention
`AlgebraicGeometry.SheafOfModules.derivedStalkFunctor`, which is itself declared under an
`attribute [local instance] HasDerivedCategory.standard` with no free `HasDerivedCategory` binder,
so the model of `D(𝒪_X)` is baked into its type. Using them would force the model of `D(𝒪_X)` in
clause (1)(a) to be the standard one, whereas clause (1)(b) leaves it a free instance argument.
`derivedStalkSpellingFunctorIsoAnyModel` below is the same comparison —
the same two lines, `Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso`
applied to `AlgebraicGeometry.modulesRingCatStalkFunctorIso` and split by
`mapDerivedCategoryCompIso` — stated with `(modulesRingCatStalkFunctor x).mapDerivedCategory` in
place of `AlgebraicGeometry.SheafOfModules.derivedStalkFunctor X.ringCatSheaf x`. Those two
functors are the same functor, as the shared bridge's own documentation records; writing the first
is what keeps the model of `D(𝒪_X)` a free instance argument. The stalk side stays at the standard
model, which is not a restriction either: the symmetric monoidal structure of [Stacks, Tag 0FNQ],
for which invertibility over the stalk is asserted, exists only there.

*The monoidal structure on `D(𝒪_X)`.* It is `AlgebraicGeometry.Scheme.Modules.derivedMonoidal`,
the structure of [Stacks, Tag 0FPT] read at a scheme, which is the stalkwise input's
own structure `Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal X.sheaf` retyped at
`X.Modules`; `AlgebraicGeometry.Scheme.Modules.mod_sheaf_eq` is the `rfl` behind that.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0AWW](https://stacks.math.columbia.edu/tag/0AWW)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0FNQ](https://stacks.math.columbia.edu/tag/0FNQ)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.PerfectComplexTriangles
open Stacks.SheafOfModules.DerivedTensorStalk

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-! ### The spelling bridge at an arbitrary model of `D(𝒪_X)` -/

variable {X : Scheme.{u}} (x : X) [HasDerivedCategory.{u + 1} X.Modules]

/-- **The two derived stalk functors differ by restriction of scalars**, at an arbitrary model of
`D(𝒪_X)`.

This is `AlgebraicGeometry.derivedStalkSpellingFunctorIso` with the `RingCat`-stalk side written
`(modulesRingCatStalkFunctor x).mapDerivedCategory` instead of
`AlgebraicGeometry.SheafOfModules.derivedStalkFunctor X.ringCatSheaf x`. The two are the same
functor; the point of the rewriting is that the latter is declared with the model of `D(𝒪_X)`
baked in at `HasDerivedCategory.standard`, so a statement mentioning it cannot leave that model a
free instance argument, while this one can. The proof is the shared bridge's, unchanged. -/
public def derivedStalkSpellingFunctorIsoAnyModel :
    AlgebraicGeometry.derivedStalkFunctor x ≅
      (modulesRingCatStalkFunctor x).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (ringCatStalkRingEquiv x).symm.toRingHom).mapDerivedCategory :=
  (mapDerivedCategoryIsoOfNatIso _ _ (modulesRingCatStalkFunctorIso x)).symm ≪≫
    mapDerivedCategoryCompIso (modulesRingCatStalkFunctor x)
      (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv x).symm.toRingHom)

end AlgebraicGeometry

namespace Stacks.Duality

variable {X : Scheme.{u}} [HasDerivedCategory.{u + 1} X.Modules]

/-- **An invertible object of `D(𝒪_X)` has invertible derived stalks**, in the local-ring
spelling: the derived stalk at `x` over `𝒪_{X,x}` is invertible for the symmetric monoidal
structure of [Stacks, Tag 0FNQ].

This is `Stacks.SheafOfModules.DerivedTensorStalk.isInvertible_derivedStalk`, which is stated over
the `RingCat`-valued stalk of the sheaf of rings, read over the local ring `𝒪_{X,x}`. The two
rings are isomorphic and not equal, so the transport is real work; it goes through
`Dualizing.isInvertible_iff_exists_iso_single`, invertibility over a local ring being the property
of being a shifted copy of the ring, which transports along a ring isomorphism by
`Dualizing.restrictScalarsEquivSingleIso`. -/
public theorem isInvertible_derivedStalkFunctor_of_isInvertible (x : X)
    (K : DerivedCategory X.Modules)
    (hK : letI := Scheme.Modules.derivedMonoidal X
      CategoryTheory.MonoidalCategory.IsInvertible K) :
    letI := (DerivedCategory.Invertible.derivedCategory_symmetricMonoidalCategory
      (X.presheaf.stalk x)).choose
    CategoryTheory.MonoidalCategory.IsInvertible ((derivedStalkFunctor x).obj K) := by
  let : HasDerivedCategory.{u + 1} (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) :=
    inferInstanceAs (HasDerivedCategory.{u + 1} X.Modules)
  let : CommRing (stalkRing X.sheaf x : Type u) :=
    StacksDraft.StalkTensor.commRing_stalk_ringSheaf X.sheaf x
  let : IsLocalRing (stalkRing X.sheaf x : Type u) :=
    (ringCatStalkRingEquiv (X := X) x).symm.isLocalRing
  -- Invertibility of the derived stalk at the `RingCat` spelling of the stalk ring, read as
  -- "the derived stalk is a shifted copy of the stalk ring".
  obtain ⟨n, ⟨e⟩⟩ := (Dualizing.isInvertible_iff_exists_iso_single
    (B := (stalkRing X.sheaf x : Type u)) ((derivedStalk X.sheaf x).obj K)).mp
      (Stacks.SheafOfModules.DerivedTensorStalk.isInvertible_derivedStalk X.sheaf x K hK)
  -- The same, over the local ring, is invertibility there.
  refine (Dualizing.isInvertible_iff_exists_iso_single
    (B := ToType (X.presheaf.stalk x)) ((derivedStalkFunctor x).obj K)).mpr ⟨n, ⟨?_⟩⟩
  refine (derivedStalkSpellingFunctorIsoAnyModel x).app K ≪≫ ?_
  refine (ModuleCat.restrictScalars
    (ringCatStalkRingEquiv (X := X) x).symm.toRingHom).mapDerivedCategory.mapIso e ≪≫ ?_
  exact Dualizing.restrictScalarsEquivSingleIso (ringCatStalkRingEquiv (X := X) x).symm n

/-- **Stacks Project, Tag 0BFQ, clause (1)(a), the direction "invertible ⟹ Gorenstein".** A
locally Noetherian scheme carrying a dualizing complex which is an invertible object of `D(𝒪_X)`
is a Gorenstein scheme.

The converse, and the whole of clause (1)(a) as an equivalence, is
`Stacks.Duality.isGorenstein_iff_isInvertible_dualizingComplex` in
`StacksFrontier/AlgebraicGeometry/Duality/GorensteinSchemes/DualizingInvertible.lean`. -/
public theorem isGorenstein_of_isInvertible_dualizingComplex [IsLocallyNoetherian X]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K)
    (hinv : letI := Scheme.Modules.derivedMonoidal X
      CategoryTheory.MonoidalCategory.IsInvertible K) :
    AlgebraicGeometry.IsGorenstein X where
  isGorensteinLocalRing x :=
    (isGorensteinLocalRing_stalk_iff_isInvertible_derivedStalk K hK x).mpr
      (isInvertible_derivedStalkFunctor_of_isInvertible x K hinv)

end Stacks.Duality

end
