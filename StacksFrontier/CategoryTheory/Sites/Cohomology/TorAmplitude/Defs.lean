module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude on a ringed site

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(O)` in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`, the bifunctor datum of Stacks 06YU. An object `E`
of `D(O)` has *Tor amplitude in `[a, b]`* when, for every sheaf of `O`-modules `F`, the derived
tensor product of `E` with `F` placed in degree zero has vanishing cohomology in every degree
outside `[a, b]`.

This file holds that predicate and nothing else, so that the lemmas about Tor amplitude — its
behaviour along distinguished triangles, along direct sums, and the perfectness criterion — are
all stated about one notion.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude`: Tor amplitude in an interval,
  measured against a derived tensor product on `D(O)`.
* `Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension`: Tor amplitude in some
  interval.
* `Stacks.SheafOfModules.DerivedTensorProduct.HasTorDimensionLE`: Tor dimension at most `n` for
  a sheaf of modules.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_iff_lt_or_lt`: the defining
  condition with the interval complement spelled as two strict inequalities.
* `Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.of_iso` and
  `Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.mono`: Tor amplitude transports
  along an isomorphism and is inherited by every larger interval.

## Implementation notes

Tor amplitude is stated against a *given* derived tensor product datum `T` rather than against
a canonical choice. That is deliberate: the interface
`Stacks.SheafOfModules.DerivedTensorProduct` is universe-polymorphic in the two site universes
and in the universe of the sections, while the construction of an inhabitant of it is available
only on a diagonal, because the K-flat resolutions it rests on are. Phrasing Tor amplitude
against `T` therefore keeps all four universes free, and instantiating `T` specialises every
consequence.

The complement of the interval is spelled `i ∉ Set.Icc a b`, as for the ringed-space predicate
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`; `hasTorAmplitude_iff_lt_or_lt` converts to the
two-inequality spelling in which the source phrases it.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

namespace Stacks.SheafOfModules.DerivedTensorProduct

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The exact endofunctor `- ⊗^L_O F[0]` of `D(O)` attached to an `O`-module `F`, for the
derived tensor product `T`. -/
noncomputable abbrev tensorModule (T : DerivedTensorProduct.{u, v, w, d} X)
    (F : RingedSite.Modules.{u, v, w} X) :
    RingedSite.DerivedModules.{u, v, w, d} X ⥤ RingedSite.DerivedModules.{u, v, w, d} X :=
  T.tensor.flip.obj ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F)

/-- **Stacks 08FZ (1).** An object `E` of `D(O)` has *Tor amplitude in `[a, b]`* for the derived
tensor product `T` if, for every sheaf of `O`-modules `F`, the derived tensor product of `E`
with `F` placed in degree zero has vanishing cohomology in every degree outside `[a, b]`. -/
@[stacks 08FZ "tor amplitude in an interval",
  sga "6 I 5.2" "Tor-amp(F) ⊂ [m,n]",
  sga "4½ Rapport 4.5" "sheaf tor-dimension ≤ r", sga "4 XVII 4.1.9" "(i)"]
noncomputable def HasTorAmplitude
    (T : DerivedTensorProduct.{u, v, w, d} X) (E : RingedSite.DerivedModules.{u, v, w, d} X)
    (a b : ℤ) : Prop :=
  ∀ (F : RingedSite.Modules.{u, v, w} X) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).obj
      ((T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F)))

/-- Non-membership in `Set.Icc a b` as the two strict inequalities `i < a` and `b < i`. -/
private theorem notMem_Icc_iff_lt_or_lt {a b i : ℤ} : i ∉ Set.Icc a b ↔ i < a ∨ b < i := by
  simp only [Set.mem_Icc, not_and_or, not_le]

/-- Tor amplitude in `[a, b]`, with the complement of the interval spelled as the two strict
inequalities `i < a` and `b < i` in which the source phrases it. -/
theorem hasTorAmplitude_iff_lt_or_lt (T : DerivedTensorProduct.{u, v, w, d} X)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) (a b : ℤ) :
    HasTorAmplitude T E a b ↔
      ∀ (F : RingedSite.Modules.{u, v, w} X) (i : ℤ), i < a ∨ b < i →
        IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).obj
          ((T.tensor.obj E).obj
            ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F))) := by
  simp only [HasTorAmplitude, notMem_Icc_iff_lt_or_lt]

/-- **Tor amplitude transports along an isomorphism** of `D(O)`. -/
theorem HasTorAmplitude.of_iso {T : DerivedTensorProduct.{u, v, w, d} X}
    {E E' : RingedSite.DerivedModules.{u, v, w, d} X} (e : E ≅ E') {a b : ℤ}
    (h : HasTorAmplitude T E a b) : HasTorAmplitude T E' a b := fun F i hi =>
  (h F i hi).of_iso
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).mapIso
      ((T.tensor.mapIso e).app
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F)).symm)

/-- **Tor amplitude in an interval holds in every larger interval.** -/
theorem HasTorAmplitude.mono {T : DerivedTensorProduct.{u, v, w, d} X}
    {E : RingedSite.DerivedModules.{u, v, w, d} X} {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    (h : HasTorAmplitude T E a b) : HasTorAmplitude T E a' b' := fun F i hi =>
  h F i (by rw [notMem_Icc_iff_lt_or_lt] at hi ⊢; omega)

/-- **Stacks 08FZ (2).** An object `E` of `D(O)` has *finite Tor dimension* for the derived
tensor product `T` if it has Tor amplitude in some interval. -/
@[stacks 08FZ "finite tor dimension",
  sga "6 I 5.2" "finite flat amplitude",
  sga "4½ Rapport 4.5" "sheaf case, finite"]
noncomputable def HasFiniteTorDimension (T : DerivedTensorProduct.{u, v, w, d} X)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) : Prop :=
  ∃ a b : ℤ, HasTorAmplitude T E a b

/-- Finite Tor dimension with the interval produced, which is how the definition is used. -/
theorem hasFiniteTorDimension_iff (T : DerivedTensorProduct.{u, v, w, d} X)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) :
    HasFiniteTorDimension T E ↔ ∃ a b : ℤ, a ≤ b ∧ HasTorAmplitude T E a b := by
  refine ⟨fun ⟨a, b, h⟩ => ⟨min a b, max a b, min_le_max, fun F i hi => h F i ?_⟩,
    fun ⟨a, b, _, h⟩ => ⟨a, b, h⟩⟩
  simp only [notMem_Icc_iff_lt_or_lt] at hi ⊢
  omega

/-- **Stacks 08FZ, the last sentence.** A sheaf of `O`-modules `F` has *Tor dimension at most
`n`* when `F[0]`, viewed as an object of `D(O)`, has Tor amplitude in `[-n, 0]`. -/
@[stacks 08FZ "tor dimension of a module",
  sga "4½ Rapport 4.5" "sheaf module case",
  sga "4 XVII 4.1.9" "module case"]
noncomputable def HasTorDimensionLE (T : DerivedTensorProduct.{u, v, w, d} X)
    (F : RingedSite.Modules.{u, v, w} X) (n : ℤ) : Prop :=
  HasTorAmplitude T
    ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F) (-n) 0

end Stacks.SheafOfModules.DerivedTensorProduct

end
