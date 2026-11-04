module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude and Tor dimension

Let `R` be a commutative ring. An object `K` of the derived category `D(R)` has *Tor amplitude
in `[a, b]`* when, for every `R`-module `M`, the cohomology of `K ⊗ᴸ M[0]` vanishes in every
degree outside `[a, b]`. It has *finite Tor dimension* when some finite interval works. A module
`M` has *Tor dimension at most `d`* when `M[0]` has Tor amplitude in `[-d, 0]`.

## Main definitions

* `StacksDraft.TorAmplitude.tensorModuleRight`: ordinary tensoring on the right, with
  independent ring and module universes.
* `StacksDraft.TorAmplitude.HasTorAmplitude`: Tor amplitude in `[a, b]`, Stacks 0652 (1).
* `StacksDraft.TorAmplitude.HasFiniteTorDimension`: finite Tor dimension, Stacks 0652 (2).
* `StacksDraft.TorAmplitude.HasTorDimensionLE`: Tor dimension of a module, Stacks 0652 (3).
* `StacksDraft.TorAmplitude.ModuleHasFiniteTorDimension`: finite Tor dimension of a module,
  Stacks 0652 (4).

## Implementation notes

Mathlib does not currently package the derived tensor product on `D(R)`. The definitions
therefore take a bifunctor `derivedTensor` together with a `comparison` to termwise ordinary
tensor product and the universal property `isLeftDerived` saying that each functor `- ⊗ᴸ M[0]`
is the total left derived functor of `- ⊗ M`. Together these pin `derivedTensor` down as *the*
derived tensor product rather than allowing an arbitrary operation.

Ordinary tensoring is defined directly by `tensorModuleRight`, so that the ring and the module
live in independent universes; in equal universes it is definitionally the monoidal tensor
functor. Vanishing of a cohomology module is expressed categorically by `IsZero`.

## References

* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace StacksDraft.TorAmplitude

universe u v

@[expose] public section

/-- A cochain complex `K` is *bounded above* if there is an `N` with `K^n = 0` for all `n > N`.

This lives here, rather than beside its first consumer, because it is shared: the Tor-amplitude
layer, the flat-representative results and the derived-comparison layer all need it, and two
modules declaring `StacksDraft.TorAmplitude.BoundedAbove` separately would make them
non-simultaneously-importable even though the definitions agree. -/
public def BoundedAbove {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{v} R) ℤ) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N < n → IsZero (K.X n)

/-- Ordinary tensoring on the right by `M`, with independent ring and module universes. -/
public def tensorModuleRight {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    ModuleCat.{v} R ⥤ ModuleCat.{v} R where
  obj N := ModuleCat.of R (TensorProduct R N M)
  map f := ModuleCat.ofHom (f.hom.rTensor M)
  map_id N := ModuleCat.hom_ext (LinearMap.rTensor_id M N)
  map_comp f g := ModuleCat.hom_ext (LinearMap.rTensor_comp M g.hom f.hom)

public instance {R : Type u} [CommRing R] (M : ModuleCat.{v} R) :
    (tensorModuleRight M).Additive where
  map_add {_ _ f g} := ModuleCat.hom_ext (LinearMap.rTensor_add M f.hom g.hom)

/-- An object `K` of `D(R)` has Tor amplitude in `[a, b]` if, for every `R`-module `M`, the
cohomology of `K ⊗ᴸ[R] M[0]` vanishes in every degree outside `[a, b]`.

The `comparison` and `_isLeftDerived` arguments certify that `derivedTensor` is the total left
derived functor of ordinary tensor product in the first variable. -/
@[stacks 0652 "(1)", sga "4½ Rapport 4.5" "tor-dimension ≤ r", sga "6 I 5.2" "Tor-amp(F) ⊂ [m,n]"]
public def HasTorAmplitude {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{v} R)]
    (derivedTensor :
      DerivedCategory (ModuleCat.{v} R) ⥤
        DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R))
    (comparison : ∀ M : ModuleCat.{v} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (_isLeftDerived : ∀ M : ModuleCat.{v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) : Prop :=
  ∀ (M : ModuleCat.{v} R) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
      ((derivedTensor.obj K).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)))

/-- An object of `D(R)` has finite Tor dimension if it has Tor amplitude in some finite
integer interval. -/
@[stacks 0652 "(2)",
  sga "4½ Rapport 4.5" "finite tor dimension",
  sga "5 I 1.10" "affine case (torf)", sga "6 I 5.2" "finite flat amplitude"]
public def HasFiniteTorDimension {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{v} R)]
    (derivedTensor :
      DerivedCategory (ModuleCat.{v} R) ⥤
        DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R))
    (comparison : ∀ M : ModuleCat.{v} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{v} R)) : Prop :=
  ∃ a b : ℤ, HasTorAmplitude derivedTensor comparison isLeftDerived K a b

/-- An `R`-module `M` has Tor dimension at most `d` if `M[0]` has Tor amplitude in
`[-d, 0]`. -/
@[stacks 0652 "(3)", sga "4 XVII 4.1.9" "module over a ring", sga "4½ Rapport 4.5" "module case"]
public def HasTorDimensionLE {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{v} R)]
    (derivedTensor :
      DerivedCategory (ModuleCat.{v} R) ⥤
        DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R))
    (comparison : ∀ N : ModuleCat.{v} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)))
    (M : ModuleCat.{v} R) (d : ℤ) : Prop :=
  HasTorAmplitude derivedTensor comparison isLeftDerived
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) (-d) 0

/-- An `R`-module `M` has finite Tor dimension if `M[0]` has finite Tor dimension as an
object of `D(R)`. -/
@[stacks 0652 "(4)"]
public def ModuleHasFiniteTorDimension {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{v} R)]
    (derivedTensor :
      DerivedCategory (ModuleCat.{v} R) ⥤
        DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R))
    (comparison : ∀ N : ModuleCat.{v} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj N)).IsLeftDerivedFunctor
        (comparison N)
        (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ)))
    (M : ModuleCat.{v} R) : Prop :=
  HasFiniteTorDimension derivedTensor comparison isLeftDerived
    ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)

/-! ### The certificate as a single datum

The four predicates above take the bifunctor, the comparison and the universal property as three
separate arguments, which is convenient where they are quantified one statement at a time but
unwieldy where two rings are involved and each carries its own. `CertifiedDerivedTensoring`
bundles exactly those three fields and nothing else — in particular it does *not* carry the
K-flat comparison or the exactness of
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral`, which are a strictly richer datum
and would make any statement assuming them a weaker statement than Stacks 0652's.

The ring universe and the module universe stay independent, as they are throughout this file. -/

/-- A derived tensor product certified as the total left derived functor of ordinary tensoring
with each module placed in degree zero: the bifunctor, the comparison with termwise tensoring,
and the `IsLeftDerivedFunctor` certificate. This is exactly the datum Stacks 0652 reads Tor
amplitude off. -/
public structure CertifiedDerivedTensoring (R : Type u) [CommRing R]
    [HasDerivedCategory (ModuleCat.{v} R)] where
  /-- The derived tensor bifunctor. -/
  tensor : DerivedCategory (ModuleCat.{v} R) ⥤
    DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R)
  /-- Comparison with ordinary termwise tensoring by a module placed in degree zero. -/
  comparison : ∀ M : ModuleCat.{v} R,
    DerivedCategory.Q ⋙ tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  /-- The comparison exhibits each `- ⊗ᴸ M[0]` as the total left derived functor of `- ⊗ M`. -/
  isLeftDerived : ∀ M : ModuleCat.{v} R,
    (tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsLeftDerivedFunctor
      (comparison M)
      (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))

/-- Tor amplitude in `[a, b]` read off a bundled certificate. This is `HasTorAmplitude` at the
certificate's three fields, so it is the same proposition and not a second notion. -/
public def CertifiedDerivedTensoring.HasTorAmplitudeIn {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{v} R)] (D : CertifiedDerivedTensoring.{u, v} R)
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) : Prop :=
  HasTorAmplitude D.tensor D.comparison D.isLeftDerived K a b

/-- Unfolding the bundled form, for rewriting against statements phrased at the three separate
arguments. -/
public theorem CertifiedDerivedTensoring.hasTorAmplitudeIn_iff {R : Type u} [CommRing R]
    [HasDerivedCategory (ModuleCat.{v} R)] (D : CertifiedDerivedTensoring.{u, v} R)
    (K : DerivedCategory (ModuleCat.{v} R)) (a b : ℤ) :
    D.HasTorAmplitudeIn K a b ↔
      HasTorAmplitude D.tensor D.comparison D.isLeftDerived K a b := Iff.rfl

end

end StacksDraft.TorAmplitude
