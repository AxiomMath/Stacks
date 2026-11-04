module

public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPowerPullbackMulCore
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower

/-!
# Pullback commutes with the tensor powers, multiplicatively

Let `f : X ⟶ S` be a morphism of schemes and `M` an `𝒪_S`-module. Iterating the comparison of
Stacks Tag 01CD gives a comparison `f^*(M^{⊗ n}) ≅ (f^*M)^{⊗ n}` in every nonnegative degree, and
this file proves that it is **compatible with the addition law** `M^{⊗ n} ⊗ M^{⊗ m} ⟶ M^{⊗(n+m)}`
of the powers: pulling the addition law back and then splitting the powers agrees with splitting
first and multiplying afterwards. That is the commuting square

    f^*(M^{⊗n} ⊗ M^{⊗m}) ──f^*(add)──> f^*(M^{⊗(n+m)})
           │                                   │
     (01CD, then the two comparisons)          │ the comparison in degree n+m
           v                                   v
    (f^*M)^{⊗n} ⊗ (f^*M)^{⊗m} ───add────> (f^*M)^{⊗(n+m)}

and it needs **no `eqToHom`**: both exponents are natural numbers and `n + m` is the same natural
number on both sides, so no reindexing of degrees occurs.

The square is the only thing a *graded-ring* map out of a graded ring of sections needs beyond the
degreewise maps, so this is what upgrades the degreewise family of additive maps
`Γ(S, M^{⊗n}) → Γ(X, (f^*M)^{⊗n})` to a map of graded rings.

## Main definitions

* `Stacks.TensorPowerPullbackMul.pullbackPowComparison`: the comparison
  `f^*(M^{⊗n}) ⟶ (f^*M)^{⊗n}` on a morphism of ringed spaces, by induction on `n`. In degree zero
  it is `Stacks.PullbackTensorCoherence.pullbackUnitComparison`, `f^*𝒪_S ⟶ 𝒪_X`, and the step is
  the comparison of Stacks Tag 01CD.
* `Stacks.TensorPowerPullbackMul.pullbackPowComparisonIso`: the same comparison as an
  isomorphism.
* `Stacks.TensorPowerPullbackMul.powModules` and `powModulesAdd`: the nonnegative tensor powers of
  an `𝒪_X`-module and their addition law, written in the **instance-free** vocabulary of
  `StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPower.lean` — `Stacks.Ample.unitModule`
  for the zeroth power and `Stacks.RelativeVeryAmple.tensorModules` for the products — so that no
  monoidal instance is needed to state anything about them.
* `Stacks.TensorPowerPullbackMul.pullbackPowModulesIso`: the comparison
  `f^*(M^{⊗n}) ≅ (f^*M)^{⊗n}` on a morphism of **schemes**, in that instance-free vocabulary. Its
  degree-zero value is `Stacks.RelativeAmple.pullbackUnitModuleIso` and its step is
  `Stacks.RelativeVeryAmple.pullbackTensorModulesIso`, both on the nose.

## Main results

* `Stacks.TensorPowerPullbackMul.pullbackPowComparison_powAdd`: **the square, on a morphism of
  ringed spaces.**
* `Stacks.TensorPowerPullbackMul.pullbackPowModulesIso_powModulesAdd`: **the square, on a morphism
  of schemes and in the instance-free vocabulary.** This is the statement a consumer composes
  with.
* `Stacks.TensorPowerPullbackMul.pullbackPowModulesIso_zero` and `..._succ`: the comparison is
  `Stacks.RelativeAmple.pullbackUnitModuleIso` in degree zero, and in degree `n + 1` it is
  `Stacks.RelativeVeryAmple.pullbackTensorModulesIso` followed by the comparison in degree `n`
  whiskered by `f^*M`. So it is the same construction as
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`, degree by degree, with the addition law
  of monoidal structure 3 below in place of the one of structure 1.

## Implementation notes

**The spelling decision, and why it is forced.** This repository carries three monoidal structures
on the sheaves of modules over a ringed space, and they are *not* definitionally equal:

1. `Stacks.SheafInternalHom.monoidalCategory` — the localization of the objectwise structure along
   sheafification, with unit iso `Iso.refl`. This is where `AlgebraicGeometry.SheafOfModules.
   tensorPow`, hence `Stacks.Ample.tensorPowModule` and `Stacks.Ample.tensorPowModuleAddIso`, live.
2. `Stacks.SheafOfModules.monoidalCategory` — the same localization with unit iso
   `Stacks.SheafOfModules.sheafifyUnitIso`, so with a *different* unit object. This is where
   `Stacks.PullbackMonoidalSheaf.pullbackMonoidal`, the monoidal structure of `f^*` obtained from
   the localization, lives.
3. `Stacks.PullbackGradedAlgebra.monoidalCategory` — `Stacks.TensorSheafWorld.monoidalCategory`,
   whose tensor product is `Stacks.SheafOfModules.TensorSheafification.tensorSheaf` and whose unit
   is `SheafOfModules.unit` **on the nose**. This is where the coherences of Stacks Tag 01CD
   (`Stacks.PullbackTensorCoherence`) and the monoidal structure of `f^*` whose tensorator *is* the
   comparison of Tag 01CD (`pullbackComparisonMonoidal`) live.

Everything below is written in structure 3, and that is the only choice that makes the square
provable with what the repository has: it is the unique structure in which the cotensorator of
`f^*` is the comparison of Tag 01CD, and it is also the structure whose tensor
product and unit object are *definitionally* `Stacks.RelativeVeryAmple.tensorModules` and
`Stacks.Ample.unitModule`, so the statements become instance-free. Concretely, each of
`Stacks.RelativeVeryAmple.tensorModules X A B = A ⊗ B`, `Stacks.Ample.unitModule X = 𝟙_ _`,
`(Stacks.RelativeVeryAmple.pullbackTensorModulesIso f A B).hom = pullbackTensorComparison _ A B`
and `(Stacks.RelativeAmple.pullbackUnitModuleIso f).hom = pullbackUnitComparison _` holds by `rfl`
in structure 3, and that is what `powModules`, `powModulesAdd` and `pullbackPowModulesIso`
exploit. Neither of the first two holds in structure 1, and the last two have no counterpart
there, the comparison of Tag 01CD being retyped at structure 3 only.

**What is *not* instance-free, and why.** The functoriality of the tensor product in its two
arguments is written `⊗ₘ` rather than `Stacks.RelativeVeryAmple.tensorModulesMapIso`. The latter
is `CategoryTheory.Functor.mapIso` of the tensor bifunctor, and that is *not* the
`⊗ₘ` of structure 3 on the nose (nor is `u ⊗ₘ 𝟙 = u ▷ _`), so spelling the square with it would
need a bridge computing the whiskerings of structure 3 against the bifunctor, which no file
provides. Consumers of the square therefore need
`attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory` in scope, exactly as
`Stacks.PullbackTensorCoherence` already requires; every *object* occurring in it is still in the
instance-free vocabulary.

**The crossing that is not made here.** `Stacks.Ample.tensorPowModule` and
`Stacks.Ample.tensorPowModuleAddIso` live in structure 1, whose tensor product is not
`tensorSheaf` and whose unit is not `SheafOfModules.unit`; so `powModules X A n` and
`Stacks.Ample.tensorPowModule X A (n : ℤ)` are isomorphic but not equal, and the same square for
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` is not proved here. It is proved in
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPowerPullbackAddIso.lean`, as
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso_tensorPowModuleAddIso`, by a different route:
the *source* of `tensorPowModuleAddIso` is already the tensor product sheaf, so the square can be
stated in structure 3 with the powers of structure 1 as mere objects, and no identification of the
two structures is needed. What that argument needs of the powers is only that they carry an
associative, right-unital multiplication, which is why its abstract form
`Stacks.TensorPowerPullbackMul.comparison_mulFamily` takes the family of objects and the
multiplication as data rather than as tensor powers.

**Only the oplax half of the monoidal structure is used.** `pullbackPowComparison` and the square
are stated for the cotensorator, i.e. for the comparison of Tag 01CD itself rather than for its
inverse; the isomorphism `pullbackPowComparisonIso` is a packaging of the same morphism. This
matters because the comparison, not its inverse, is the datum with a formula on local sections.

**Universes.** Everything is at a single universe `u`, forced by
`RingedSpaceModuleAdjunction.modulePullback`, which exists only for `RingedSpace.{u, u}` with
modules in `u`. Nothing is narrowed relative to the imports.

**No `@[stacks]` attribute.** Tag 01CD is carried by `Stacks.RingedSpace.comparisonIso` and Tag
01CU by the addition law of the powers; the result below is a compatibility of those two, not a
new result of the Stacks Project, so tagging it would register a result twice.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD) — pullback commutes with
  the tensor product of sheaves of modules.
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU) — the tensor powers of an
  invertible module and their canonical multiplication.
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA) — the tensor product of
  sheaves of modules.

## What is not done

The identification of the three monoidal structures. Nothing below depends on it, and the square
for `Stacks.Ample.tensorPowModuleAddIso` no longer does either (see "The crossing that is not made
here"), so the only thing it would now buy is the collapse of the two families of powers
`powModules X A n` and `Stacks.Ample.tensorPowModule X A (n : ℤ)` into one. That remains the dedup
which `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackTensorCoherence.lean` records as owed
in its implementation notes, and which would in addition make
`Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal` and
`Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal` one datum.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.GradedSections (powAdd)
open Stacks.PullbackTensorCoherence

universe u

namespace Stacks.TensorPowerPullbackMul

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-! ### On a morphism of ringed spaces -/

section RingedSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (M : SheafOfModules.{u} (structureRingSheaf Y))

/-- **The comparison `f^*(M^{⊗ n}) ⟶ (f^*M)^{⊗ n}`**, by induction on `n`: the degree-zero value
is the structure-sheaf comparison `f^*𝒪_Y ⟶ 𝒪_X` and the step is the comparison of Stacks Tag
01CD. This is `Stacks.TensorPowerPullbackMul.natTensorPowComparison` for the monoidal structure on
`f^*` whose cotensorator is that comparison. -/
def pullbackPowComparison (n : ℕ) :
    (pullbackFunctor f).obj (natTensorPow M n) ⟶ natTensorPow ((pullbackFunctor f).obj M) n :=
  letI := pullbackComparisonMonoidal f
  natTensorPowComparison (pullbackFunctor f) M n

/-- In degree zero the comparison is the structure-sheaf comparison of
`Stacks.PullbackTensorCoherence.pullbackUnitComparison`. -/
theorem pullbackPowComparison_zero : pullbackPowComparison f M 0 = pullbackUnitComparison f := rfl

/-- In degree `n + 1` the comparison is the comparison of Stacks Tag 01CD followed by the
comparison in degree `n` whiskered by `f^*M`. -/
theorem pullbackPowComparison_succ (n : ℕ) :
    pullbackPowComparison f M (n + 1) =
      pullbackTensorComparison f (natTensorPow M n) M ≫
        (pullbackPowComparison f M n ▷ (pullbackFunctor f).obj M) := rfl

/-- **The comparison of the tensor powers is multiplicative**, on a morphism of ringed spaces: the
image under `f^*` of the addition law `M^{⊗ n} ⊗ M^{⊗ m} ⟶ M^{⊗ (n+m)}`, followed by the
comparison in degree `n + m`, is the comparison of Stacks Tag 01CD followed by the two comparisons
and the addition law of the powers of `f^*M`.

This is `Stacks.TensorPowerPullbackMul.natTensorPowComparison_powAdd` at the monoidal structure of
`f^*` whose cotensorator is the comparison of Tag 01CD. -/
theorem pullbackPowComparison_powAdd (n m : ℕ) :
    (pullbackFunctor f).map (powAdd M n m) ≫ pullbackPowComparison f M (n + m) =
      pullbackTensorComparison f (natTensorPow M n) (natTensorPow M m) ≫
        (pullbackPowComparison f M n ⊗ₘ pullbackPowComparison f M m) ≫
          powAdd ((pullbackFunctor f).obj M) n m :=
  let := pullbackComparisonMonoidal f
  natTensorPowComparison_powAdd (pullbackFunctor f) M n m

/-- **The comparison of the tensor powers as an isomorphism**, the comparison of Stacks Tag 01CD
and the structure-sheaf comparison both being invertible. -/
def pullbackPowComparisonIso (n : ℕ) :
    (pullbackFunctor f).obj (natTensorPow M n) ≅ natTensorPow ((pullbackFunctor f).obj M) n :=
  letI := pullbackComparisonMonoidal f
  natTensorPowComparisonIso (pullbackFunctor f) M n

/-- The forward map of `pullbackPowComparisonIso f M n` is `pullbackPowComparison f M n`. -/
@[simp]
theorem pullbackPowComparisonIso_hom (n : ℕ) :
    (pullbackPowComparisonIso f M n).hom = pullbackPowComparison f M n :=
  let := pullbackComparisonMonoidal f
  natTensorPowComparisonIso_hom (pullbackFunctor f) M n

end RingedSpace

/-! ### The powers of an `𝒪_X`-module, with no monoidal instance -/

section Powers

/-- **The nonnegative tensor powers of an `𝒪_X`-module**, read in the instance-free vocabulary of
`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/TensorPower.lean`. This is
`Stacks.TensorPowers.natTensorPow` for the monoidal structure of Stacks Tag 01CA whose tensor
product is the tensor product sheaf; `powModules_zero` and `powModules_succ` identify the zeroth
power with `Stacks.Ample.unitModule` and the step with
`Stacks.RelativeVeryAmple.tensorModules`, both on the nose. No invertibility of `A` is needed,
and — unlike `Stacks.Ample.tensorPowModule` — no monoidal instance is needed to state anything
about these. -/
def powModules (X : Scheme.{u}) (A : X.Modules) (n : ℕ) : X.Modules :=
  natTensorPow (C := SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) A n

/-- The zeroth tensor power `powModules X A 0` is `Stacks.Ample.unitModule X`. -/
theorem powModules_zero (X : Scheme.{u}) (A : X.Modules) :
    powModules X A 0 = Stacks.Ample.unitModule X := rfl

/-- The tensor power `powModules X A (n + 1)` is the tensor product of `powModules X A n`
with `A`. -/
theorem powModules_succ (X : Scheme.{u}) (A : X.Modules) (n : ℕ) :
    powModules X A (n + 1) =
      Stacks.RelativeVeryAmple.tensorModules X (powModules X A n) A := rfl

/-- **The addition law for `Stacks.TensorPowerPullbackMul.powModules`**,
`A^{⊗ n} ⊗ A^{⊗ m} ⟶ A^{⊗ (n+m)}`, in the instance-free vocabulary. This is
`Stacks.GradedSections.powAdd`: a right unitor in degree `(n, 0)` and an associator inverse
followed by a whiskering in degree `(n, m + 1)`. -/
def powModulesAdd (X : Scheme.{u}) (A : X.Modules) (n m : ℕ) :
    Stacks.RelativeVeryAmple.tensorModules X (powModules X A n) (powModules X A m) ⟶
      powModules X A (n + m) :=
  powAdd (C := SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)) A n m

end Powers

/-! ### On a morphism of schemes, with no monoidal instance -/

section Scheme

variable {X S : Scheme.{u}} (f : X ⟶ S) (M : S.Modules)

/-- **Pullback commutes with the nonnegative tensor powers of an `𝒪_S`-module**,
`f^*(M^{⊗ n}) ≅ (f^*M)^{⊗ n}`, in the instance-free vocabulary of
`Stacks.TensorPowerPullbackMul.powModules`. The degree-zero value is
`Stacks.RelativeAmple.pullbackUnitModuleIso` and the step is
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso`, Stacks Tag 01CD on a morphism of schemes;
both on the nose, by `pullbackPowModulesIso_zero` and `pullbackPowModulesIso_succ`. Unlike
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` this needs no invertibility of `M`. -/
def pullbackPowModulesIso (n : ℕ) :
    (pullbackFunctor f.toLRSHom.toShHom).obj (powModules S M n) ≅
      powModules X ((pullbackFunctor f.toLRSHom.toShHom).obj M) n :=
  pullbackPowComparisonIso f.toLRSHom.toShHom M n

/-- In degree zero, `pullbackPowModulesIso f M 0` is
`Stacks.RelativeAmple.pullbackUnitModuleIso f`. -/
theorem pullbackPowModulesIso_zero :
    (pullbackPowModulesIso f M 0).hom = (Stacks.RelativeAmple.pullbackUnitModuleIso f).hom := rfl

/-- In degree `n + 1`, `pullbackPowModulesIso f M (n + 1)` is
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso f (powModules S M n) M` followed by
`pullbackPowModulesIso f M n` tensored on the right with `f^*M`. -/
theorem pullbackPowModulesIso_succ (n : ℕ) :
    (pullbackPowModulesIso f M (n + 1)).hom =
      (Stacks.RelativeVeryAmple.pullbackTensorModulesIso f (powModules S M n) M).hom ≫
        ((pullbackPowModulesIso f M n).hom ▷
          (pullbackFunctor f.toLRSHom.toShHom).obj M) := rfl

/-- **The multiplicativity square, on a morphism of schemes.** Pulling back the addition law of
the tensor powers and then splitting the power in degree `n + m` agrees with splitting first — by
`Stacks.RelativeVeryAmple.pullbackTensorModulesIso`, Stacks Tag 01CD on a morphism of schemes, and
then the comparisons in degrees `n` and `m` — and multiplying afterwards.

No `eqToHom` occurs: both degrees are natural numbers and `n + m` is literally the same natural
number on the two sides.

The only thing here that is not in the instance-free vocabulary is the functoriality `⊗ₘ` of the
tensor product in its two arguments; see the implementation notes for why it is not spelled
`Stacks.RelativeVeryAmple.tensorModulesMapIso`. -/
theorem pullbackPowModulesIso_powModulesAdd (n m : ℕ) :
    (pullbackFunctor f.toLRSHom.toShHom).map (powModulesAdd S M n m) ≫
        (pullbackPowModulesIso f M (n + m)).hom =
      (Stacks.RelativeVeryAmple.pullbackTensorModulesIso f (powModules S M n)
            (powModules S M m)).hom ≫
        ((pullbackPowModulesIso f M n).hom ⊗ₘ (pullbackPowModulesIso f M m).hom) ≫
          powModulesAdd X ((pullbackFunctor f.toLRSHom.toShHom).obj M) n m :=
  pullbackPowComparison_powAdd f.toLRSHom.toShHom M n m

end Scheme

end Stacks.TensorPowerPullbackMul

end
