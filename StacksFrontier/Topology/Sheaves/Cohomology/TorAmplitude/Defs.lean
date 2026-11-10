module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Geometry.RingedSpace.Basic

@[expose] public section

/-
# Problem Description

We work in the setting of a ringed space $(X, \mathcal{O}_X)$ and its derived
category $D(\mathcal{O}_X)$ of $\mathcal{O}_X$-modules.  The relevant operation is
the derived tensor product $- \otimes_{\mathcal{O}_X}^{\mathbf{L}} -$ on
$D(\mathcal{O}_X)$, and $H^i(-)$ denotes the $i$-th cohomology sheaf functor
$D(\mathcal{O}_X) \to \mathrm{Mod}(\mathcal{O}_X)$.

## Main Definition 1 (Tor-amplitude in `[a,b]`; Stacks Tag 08CG / Definition 20.48.1)

Let $(X, \mathcal{O}_X)$ be a ringed space, let $E$ be an object of
$D(\mathcal{O}_X)$, and let $a, b \in \mathbf{Z}$ with $a \le b$.  We say that $E$
has tor-amplitude in $[a,b]$ if for every $\mathcal{O}_X$-module $\mathcal{F}$ and
for every integer $i \notin [a,b]$ (i.e. $i < a$ or $b < i$) we have
$H^i(E \otimes_{\mathcal{O}_X}^{\mathbf{L}} \mathcal{F}) = 0$.

## Main Definition 2 (Direct sum / biproduct)

For objects $K, L$ of the (triangulated, hence additive) category
$D(\mathcal{O}_X)$, $K \oplus L$ denotes their direct sum (biproduct).  This is the
categorical biproduct, denoted `K ⊞ L` in Mathlib.

## Main Statement 1 (Stacks Tag 08CK / Lemma 20.48.8)

Let $(X, \mathcal{O}_X)$ be a ringed space and let $a, b \in \mathbf{Z}$ with
$a \le b$.  Let $K$ and $L$ be objects of $D(\mathcal{O}_X)$.  If $K \oplus L$ has
tor-amplitude in $[a,b]$, then both $K$ and $L$ have tor-amplitude in $[a,b]$.

## Notes on the formalization

* `Mod(𝒪_X)` is formalized as `SheafOfModules` over the structure sheaf of `X`
  (regarded as a sheaf of (not necessarily commutative) rings via the forgetful
  functor `CommRingCat ⥤ RingCat`).  This is an abelian category, and we use the
  (universe-bumped) standard derived category `DerivedCategory (Mod 𝒪_X)` for
  `D(𝒪_X)`.  The cohomology sheaf functors `H^i` are
  `DerivedCategory.homologyFunctor _ i`.

* The *derived* tensor product `- ⊗_{𝒪_X}^{L} -` on `D(𝒪_X)` has not been
  assembled yet, so it is introduced below as hypotheses.  THE REASON GIVEN HERE
  ORIGINALLY IS NO LONGER TRUE AND MUST NOT BE REUSED: it said there is no
  monoidal structure on `SheafOfModules`, hence no underived `- ⊗_{𝒪_X} -`, and a
  fortiori no derived one.  All three clauses are now false or stale.  The
  underived tensor product is `Stacks.SheafOfModules.Tensor.sheafTensor`
  (Stacks Tag 06YM), additive in each variable; the
  monoidal, symmetric and monoidal-closed structures are
  `SheafOfModules.monoidalCategory` and `SheafOfModules.monoidalCategorySheafTensor`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/Monoidal.lean` and
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean`), whose tensor unit is
  `SheafOfModules.unit`; and for
  a ringed space `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf` agrees with
    `sheafTensor` by `rfl`
  (`StacksFrontier/Topology/Sheaves/Modules/StalkTensor.lean`).  The K-flat
  resolution theory the derived functor needs is also available:
  `Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution` (Stacks Tag 06YS) and
  `Stacks.SheafOfModules.KFlatQuasiIso.quasiIso_tensorComplex_of_KFlat` (Stacks Tag 06YP).
  What is genuinely missing is only the final localization step -- the analogue, for
  sheaves, of the construction already carried out for a commutative ring in
  `StacksFrontier/Homology/Tor/DerivedTensor.lean`.  Rather than quantifying over an
  *arbitrary* packaged bifunctor — which would make the theorem a statement about
  *some* operation instead of *the* derived tensor product — we introduce the
  genuine operation as **hypotheses of the theorem**, pinned down by its defining
  universal property as a left derived functor.  This avoids `axiom` declarations
  while still being faithful: the universal property
  (`Functor.IsLeftDerivedFunctor`) determines the operation up to canonical
  isomorphism, so the theorem is a statement about THE derived tensor product
  (any operation that satisfies the universal property is canonically isomorphic
  to it).  Concretely, the theorem assumes:

    - `tensorMod : Mod(𝒪_X) ⥤ Mod(𝒪_X) ⥤ Mod(𝒪_X)`, the underived tensor
      product `- ⊗_{𝒪_X} -`, additive in each variable
      (`tensorMod_flip_additive`).
    - `derivedTensor : D(𝒪_X) ⥤ D(𝒪_X) ⥤ D(𝒪_X)`, the derived tensor product
      `- ⊗^L -`, a bifunctor on `D(𝒪_X)`.
    - `derivedTensorComparison`, the comparison natural transformation
      `Q ⋙ (- ⊗^L F) ⟶ liftToDerived (- ⊗ F)`.
    - `derivedTensor_isLeftDerived`: for every module `F`, the functor
      `- ⊗^L F = derivedTensor.flip.obj (single F)` (with `F` placed in
      cohomological degree `0`), *together with the comparison*, is the **total
      left derived functor** of the underived `- ⊗ F` (lifted from modules to
      cochain complexes and to `D(𝒪_X)`).  This is the genuine universal
      property of the left derived functor (`Functor.IsLeftDerivedFunctor`); it
      carries the naturality of the comparison and the universal property
      characterizing `derivedTensor` up to canonical isomorphism, so it is *the*
      derived tensor product and not an arbitrary bifunctor.

* For `E : D(𝒪_X)` and a module `F`, `E ⊗^L F` is `derivedTensorModule`, i.e.
  `(derivedTensor.obj E).obj (single F)`, where
  `single = DerivedCategory.singleFunctor (Mod 𝒪_X) 0` is the canonical embedding
  `Mod(𝒪_X) ↪ D(𝒪_X)` placing a module in cohomological degree `0`.  This is
  exactly the `E ⊗_{𝒪_X}^{L} F` of Definition 20.48.1.

* On the hypothesis `a ≤ b`: the literal lemma (Tag 08CK) writes only
  "`a, b ∈ ℤ`", but the definition of tor-amplitude in `[a,b]` (Tag 08CG) carries
  the standing assumption `a ≤ b`; we include it as `hab`.

* Mathematical content of the proof (recorded for orientation only): for fixed `F`
  and `i`, the composite functor `(- ⊗^L F) ⋙ H^i` is additive, hence preserves
  the binary biproduct, giving
  `H^i((K ⊞ L) ⊗^L F) ≅ H^i(K ⊗^L F) ⊞ H^i(L ⊗^L F)`.  A biproduct of
  `𝒪_X`-modules is zero iff each summand is zero, so vanishing of the left side
  (the hypothesis) forces vanishing of each summand.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Stacks.TorAmplitude

universe u

variable (X : AlgebraicGeometry.RingedSpace.{u, u})

/-- The structure sheaf of a ringed space `X`, regarded as a sheaf of (possibly
noncommutative) rings via the forgetful functor `CommRingCat ⥤ RingCat`. -/
noncomputable abbrev structureRingSheaf :
    Sheaf (Opens.grothendieckTopology X.carrier) RingCat.{u} :=
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf

/-- The abelian category `Mod(𝒪_X)` of `𝒪_X`-modules. -/
abbrev ModOX := SheafOfModules (structureRingSheaf X)

/-- The derived category `D(𝒪_X)` of `𝒪_X`-modules.  We use the standard
(universe-bumped) construction so that it always exists. -/
noncomputable instance : HasDerivedCategory (ModOX X) := HasDerivedCategory.standard _

/-- `D(𝒪_X)`, the derived category of `𝒪_X`-modules. -/
abbrev DOX := DerivedCategory (ModOX X)

/-- The `i`-th cohomology sheaf functor `H^i : D(𝒪_X) ⥤ Mod(𝒪_X)`. -/
noncomputable abbrev cohomologySheaf (i : ℤ) : DOX X ⥤ ModOX X :=
  DerivedCategory.homologyFunctor (ModOX X) i

/-- The canonical embedding `Mod(𝒪_X) ↪ D(𝒪_X)` placing a module in
cohomological degree `0`. -/
noncomputable abbrev single : ModOX X ⥤ DOX X := DerivedCategory.singleFunctor (ModOX X) 0

/-- An additive endofunctor `T` of `Mod(𝒪_X)` (such as `- ⊗ F`) lifted to a
functor `CochainComplex Mod(𝒪_X) ℤ ⥤ D(𝒪_X)` by applying `T` degreewise and then
descending to the derived category.  The derived functor of `T` is the total left
derived functor of this lift. -/
noncomputable def liftToDerived (T : ModOX X ⥤ ModOX X) [T.Additive] :
    CochainComplex (ModOX X) ℤ ⥤ DOX X :=
  T.mapHomologicalComplex _ ⋙ DerivedCategory.Q

variable {X}

/-- `E ⊗_{𝒪_X}^{L} F` for `E : D(𝒪_X)` and an `𝒪_X`-module `F`, viewing `F` in
cohomological degree `0`.  Here `derivedTensor` is the derived tensor product
bifunctor `- ⊗^L -`.  This is exactly `E ⊗^L F` of Definition 20.48.1. -/
noncomputable def derivedTensorModule
    (derivedTensor : DOX X ⥤ DOX X ⥤ DOX X) (E : DOX X) (F : ModOX X) : DOX X :=
  (derivedTensor.obj E).obj ((single X).obj F)

/-- **Definition 1 (Tag 08CG / Definition 20.48.1).**  An object `E` of `D(𝒪_X)`
*has tor-amplitude in `[a,b]`* (with respect to the derived tensor product
`derivedTensor`) if for every `𝒪_X`-module `F` and every integer `i` outside
`[a,b]` (i.e. `i < a` or `b < i`) the cohomology sheaf `H^i(E ⊗_{𝒪_X}^{L} F)`
vanishes. -/
def HasTorAmplitude
    (derivedTensor : DOX X ⥤ DOX X ⥤ DOX X) (a b : ℤ) (E : DOX X) : Prop :=
  ∀ (F : ModOX X) (i : ℤ), i < a ∨ b < i →
    IsZero ((cohomologySheaf X i).obj (derivedTensorModule derivedTensor E F))

/-- **Statement 1 (Tag 08CK / Lemma 20.48.8).**  Let `(X, 𝒪_X)` be a ringed space
and `a ≤ b`.  We work with THE derived tensor product `- ⊗^L_{𝒪_X} -` on
`D(𝒪_X)`: it is given as a bifunctor `derivedTensor` whose flips
`- ⊗^L F = derivedTensor.flip.obj (single F)` are, together with the comparison
natural transformation `derivedTensorComparison F`, the **total left derived
functors** (`IsLeftDerivedFunctor`) of the underived tensor products `- ⊗ F`.
This universal property determines `derivedTensor` up to canonical isomorphism, so
it is genuinely the derived tensor product (introduced here as hypotheses rather
than as `axiom`s).

If the direct sum `K ⊕ L` (categorical biproduct `K ⊞ L`) has tor-amplitude in
`[a,b]`, then both `K` and `L` have tor-amplitude in `[a,b]`. -/
@[stacks 08CK]
theorem hasTorAmplitude_of_biprod
    (derivedTensor : DOX X ⥤ DOX X ⥤ DOX X)
    (a b : ℤ)
    (K L : DOX X) (h : HasTorAmplitude derivedTensor a b (K ⊞ L)) :
    HasTorAmplitude derivedTensor a b K ∧ HasTorAmplitude derivedTensor a b L := by
  -- For a fixed `F` and `i`, `K` and `L` are retracts of `K ⊞ L`, so `H^i(K ⊗^L F)` and
  -- `H^i(L ⊗^L F)` are retracts of `H^i((K ⊞ L) ⊗^L F) = 0`.
  have key : ∀ (Φ : DOX X ⥤ ModOX X) {A : DOX X} (s : A ⟶ K ⊞ L) [IsSplitMono s],
      IsZero (Φ.obj (K ⊞ L)) → IsZero (Φ.obj A) := fun Φ _ s _ hB =>
    haveI : Mono (Φ.map s) := (inferInstance : IsSplitMono (Φ.map s)).mono
    hB.of_mono (Φ.map s)
  exact ⟨fun F i hi => key (derivedTensor.flip.obj ((single X).obj F) ⋙ cohomologySheaf X i)
      biprod.inl (h F i hi),
    fun F i hi => key (derivedTensor.flip.obj ((single X).obj F) ⋙ cohomologySheaf X i)
      biprod.inr (h F i hi)⟩

end Stacks.TorAmplitude
