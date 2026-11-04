module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.QuasiCoherentGenerator
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.GeneratorClauses
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.DerivedPullbackSingleFlat
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.QuasiCoherentGenerator
import StacksCore.Tactic.StacksAttribute

/-!
# The twists generate on a quasi-compact locally closed subscheme of projective space

This is the second consequence [Stacks, Tag 0BQT] draws from its remark: for `X` a quasi-compact
**locally closed** subscheme of `P^n_A`, the object

`𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`,

placed in degree zero, is a generator of `D_QCoh(𝒪_X)`.

The argument is the source's. A locally closed subscheme is an immersion `i : X ⟶ P^n_A`, which
factors as a closed immersion followed by an open immersion ([Stacks, Tag 01IO] part (5)); a
closed immersion is affine, so `i` lies in the multiplicative closure of the affine morphisms and
the open immersions, and the remark's clause
`Stacks.Duality.DerivedPushforward.conditions_of_multiplicativeClosure` applies to it. Its
condition (3) says that `Li^*` carries a generator of `D_QCoh(𝒪_{P^n_A})` to a generator of
`D_QCoh(𝒪_X)`. The generator on `P^n_A` is `𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)` by [Stacks, Tag 0A9V],
`Stacks.AlgebraicGeometry.ExampleGenerator.isWeakTriangulatedGenerator_twistSumQCoh`, and
`Li^*` of it is the displayed object: the direct sum of the twists is a flat module, so `Li^*`
is computed on it by the degreewise pullback
(`Stacks.Duality.derivedPullbackSingleIsoOfFlat`), and the pullback functor — a left adjoint,
hence additive — carries the direct sum to the direct sum of the pullbacks.

## Main definitions

* `Stacks.Duality.DerivedPushforward.restrictedTwistFamily` — the family
  `i^*𝒪(0), i^*𝒪(-1), …, i^*𝒪(-n)` of `𝒪_X`-modules.
* `Stacks.Duality.DerivedPushforward.restrictedTwistSumModule` — their direct sum.
* `Stacks.Duality.DerivedPushforward.restrictedTwistSum` — that direct sum in degree zero, as an
  object of `D_QCoh(𝒪_X)`.
* `Stacks.Duality.DerivedPushforward.restrictedTwistSumIso` — the identification of
  `Li^*(𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n))` with it.

## Main results

* `Stacks.Duality.DerivedPushforward.immersion_mem_multiplicativeClosure` — an immersion of
  schemes is a finite composite of affine morphisms and open immersions.
* `isWeakTriangulatedGenerator_restrictedTwistSum`, in the namespace
  `Stacks.Duality.DerivedPushforward` — **[Stacks, Tag 0BQT]**, the consequence for a
  quasi-compact locally closed subscheme of `P^n_A`.

## Implementation notes

*`P^n_A` is `Proj A[T₀, …, Tₙ]`*, the model the twisting sheaves of [Stacks, Tag 01MN] and the
Koszul complexes of [Stacks, Tag 0BQS] are built over, so no base change to the integral model
`AlgebraicGeometry.projectiveSpaceOverRing` appears and the twists are the Serre twists
themselves.

*The model of the derived categories* is the locally small one, as in
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/PullbackGenerator.lean`.

*The source's hypotheses.* "Quasi-compact locally closed subscheme" is `[IsImmersion i]`
together with `[CompactSpace X]`; quasi-separatedness of `X` is then automatic, an immersion
being quasi-separated and `P^n_A` being quasi-separated.

## References

* [Stacks Project, Tag 0BQT](https://stacks.math.columbia.edu/tag/0BQT)
* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 01IO](https://stacks.math.columbia.edu/tag/01IO)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ExampleGenerator

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace Stacks.Duality.DerivedPushforward

/-! ### An immersion is a composite of an affine morphism and an open immersion -/

/-- **An immersion of schemes lies in the multiplicative closure of the affine morphisms and the
open immersions.** -/
theorem immersion_mem_multiplicativeClosure {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] :
    ((@IsAffineHom) ⊔ (@IsOpenImmersion) :
      MorphismProperty (Scheme.{u})).multiplicativeClosure f := by
  obtain ⟨Z, c, o, hc, ho, hco⟩ :=
    (IsImmersion.isImmersion_iff_exists (f := f)).mp inferInstance
  let : IsClosedImmersion c := hc
  let : IsOpenImmersion o := ho
  have hc' : ((@IsAffineHom) ⊔ (@IsOpenImmersion) :
      MorphismProperty (Scheme.{u})) c := Or.inl inferInstance
  have ho' : ((@IsAffineHom) ⊔ (@IsOpenImmersion) :
      MorphismProperty (Scheme.{u})) o := Or.inr ho
  rw [← hco]
  exact MorphismProperty.multiplicativeClosure.comp_of c o
    (MorphismProperty.multiplicativeClosure.of c hc') ho'

/-! ### The restricted twists -/

variable {A : Type u} [CommRing A] {n : ℕ} {W : Scheme.{u}}
  (i : W ⟶ AlgebraicGeometry.Proj (polyGrading A n))

/-- The family `i^*𝒪(0), i^*𝒪(-1), …, i^*𝒪(-n)` of `𝒪_W`-modules, for a morphism
`i : W ⟶ P^n_A`. -/
def restrictedTwistFamily : Fin (n + 1) → W.Modules :=
  fun j => (Scheme.Modules.pullback i).obj (twistFamily A n j)

/-- **The module `𝒪_W ⊕ 𝒪_W(-1) ⊕ ⋯ ⊕ 𝒪_W(-n)`** on a scheme `W` over `P^n_A`. -/
def restrictedTwistSumModule : W.Modules := ⨁ restrictedTwistFamily i

/-- Each restricted twist `i^*𝒪(-j)` is a quasi-coherent `𝒪_W`-module. -/
instance isQuasicoherent_restrictedTwistFamily (j : Fin (n + 1)) :
    (restrictedTwistFamily i j).IsQuasicoherent :=
  inferInstanceAs (((Scheme.Modules.pullback i).obj (twistFamily A n j)).IsQuasicoherent)

/-- The module `𝒪_W ⊕ 𝒪_W(-1) ⊕ ⋯ ⊕ 𝒪_W(-n)` is quasi-coherent. -/
instance isQuasicoherent_restrictedTwistSumModule :
    (restrictedTwistSumModule i).IsQuasicoherent := by
  let := Stacks.ConstantSheaf.isClosedUnderFiniteCoproducts_of_isWeakSerreClass
    (SheafOfModules.isQuasicoherent W.ringCatSheaf)
  exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso
    (biproduct.isoCoproduct (restrictedTwistFamily i)).symm
    ((SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_coproduct
      (fun j => isQuasicoherent_restrictedTwistFamily i j))

/-- **`𝒪_W ⊕ 𝒪_W(-1) ⊕ ⋯ ⊕ 𝒪_W(-n)` in degree zero, as an object of `D_QCoh(𝒪_W)`.** -/
def restrictedTwistSum : Stacks.Duality.quasiCoherentDerivedCategory W :=
  ⟨(DerivedCategory.singleFunctor W.Modules 0).obj (restrictedTwistSumModule i),
    derivedCategoryB_singleFunctor_obj _ (isQuasicoherent_restrictedTwistSumModule i)⟩

/-- **`Li^*(𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)) ≅ 𝒪_W ⊕ 𝒪_W(-1) ⊕ ⋯ ⊕ 𝒪_W(-n)`**, on underlying objects of
`D(𝒪_W)`. -/
def derivedPullbackTwistSumObjIso :
    (Stacks.Duality.derivedPullback i).obj (twistSumQCoh A n).obj ≅
      (DerivedCategory.singleFunctor W.Modules 0).obj (restrictedTwistSumModule i) :=
  (Stacks.Duality.derivedPullback i).mapIso (twistSumModuleSingleIso A n).symm ≪≫
    Stacks.Duality.derivedPullbackSingleIsoOfFlat i (twistSumModule A n)
      (isFlat_twistSumModule A n) 0 ≪≫
    (DerivedCategory.singleFunctor W.Modules 0).mapIso
      ((Scheme.Modules.pullback i).mapBiproduct (twistFamily A n))

/-- **`Li^*(𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)) ≅ 𝒪_W ⊕ 𝒪_W(-1) ⊕ ⋯ ⊕ 𝒪_W(-n)`** in `D_QCoh(𝒪_W)`. -/
def restrictedTwistSumIso :
    (Stacks.Duality.quasiCoherentDerivedPullback' i).obj (twistSumQCoh A n) ≅
      restrictedTwistSum i :=
  (DerivedCategoryB.derivedCategoryB (A := W.Modules)
    (SheafOfModules.isQuasicoherent W.ringCatSheaf)).isoMk
    (derivedPullbackTwistSumObjIso i)

/-! ### The clause -/

/-- For `i : W ⟶ P^n_A` an immersion with `W` quasi-compact, the object
`𝒪_W ⊕ 𝒪_W(-1) ⊕ ⋯ ⊕ 𝒪_W(-n)`, placed in degree zero, generates `D_QCoh(𝒪_W)`. -/
@[stacks 0BQT "the second consequence drawn from the remark: for X a quasi-compact locally \
  closed subscheme of P^n_A, the object O_X ⊕ O_X(-1) ⊕ … ⊕ O_X(-n) is a generator for \
  D_QCoh(O_X)"]
theorem isWeakTriangulatedGenerator_restrictedTwistSum [IsImmersion i] [CompactSpace W] :
    (ObjectProperty.singleton (restrictedTwistSum i)).IsWeakTriangulatedGenerator := by
  let : QuasiSeparatedSpace W := quasiSeparatedSpace_of_quasiSeparated i
  exact isWeakTriangulatedGenerator_of_iso (restrictedTwistSumIso i)
    (conditions_of_multiplicativeClosure (immersion_mem_multiplicativeClosure i)
      (twistSumQCoh A n) (isWeakTriangulatedGenerator_twistSumQCoh A n)).2.2

end Stacks.Duality.DerivedPushforward

end
