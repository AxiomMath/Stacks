module

public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedCharacterization
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlatAndDerivedPullback.StrictlyPerfectIsKFlat
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor amplitude on a ringed space

Tag 08CQ characterises the perfect objects of `D(O_X)` on a ringed space as those which are
pseudo-coherent and locally of finite Tor dimension. This file states the Tor-amplitude conditions
of Tag 08CG against the derived tensor product of Tag 06YU, and constructs the local derived
approximations of a perfect complex in the sense of Tag 08CC part (1).

## Main definitions

* `Stacks.Cohomology.TorAmplitude.derTensor`: the derived tensor product on `D(O_X)` for a ringed
  space, obtained from the ringed-site construction of Tag 06YU at the site of opens of `X`.
* `Stacks.Cohomology.TorAmplitude.HasTorAmplitude`,
  `Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension`,
  `Stacks.Cohomology.TorAmplitude.LocallyHasFiniteTorDimension` and
  `Stacks.Cohomology.TorAmplitude.HasTorDimensionLE`: the four clauses of Tag 08CG, stated
  against `derTensor`.

## Main results

* `Stacks.Cohomology.TorAmplitude.exists_local_derived_approximation_of_isPerfectComplex`: a
  perfect complex admits, near every point and for every `m`, a local strictly perfect derived
  approximation in the sense of Tag 08CC part (1).

## Implementation notes

The derived tensor product is not a hypothesis: `derTensor` is
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct` at `X.sheaf`, whose comparison
fields compute it from K-flat representatives.

The instance `HasDerivedCategory` is registered by hand at the spelling
`Stacks.DerivedTensor.RingedSite.Modules X.sheaf`, which is `OXMod X` by `rfl`: an instance at one
spelling of a non-reducible definition does not fire at the other.

The universes of the space, its structure sheaf and its modules coincide, while the hom universe
of the derived category stays independent.

`exists_local_derived_approximation_of_model` takes its model data in binders and is proved as a
term, and `exists_local_derived_approximation_of_isPerfectComplex` takes the cover apart with
`Exists.choose` rather than `obtain`: destructuring with `obtain` against the dependent goal makes
`cases` build a motive and forces the `HasDerivedCategory` instances under the binder through
`whnf`, which exhausts the default heartbeat budget.

## References

* [Stacks Project, Tag 08CQ](https://stacks.math.columbia.edu/tag/08CQ)
* [Stacks Project, Tag 08CG](https://stacks.math.columbia.edu/tag/08CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

namespace Stacks.Cohomology.TorAmplitude

universe u d d' v₁ u₁

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{d} C]

/-- The image in the derived category of a quasi-isomorphism is an isomorphism on every
cohomology functor. -/
theorem isIso_homologyFunctor_map_Q_map {P Q' : CochainComplex C ℤ} (f : P ⟶ Q')
    (hf : QuasiIso f) (j : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map f)) := by
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := C) f).2 hf
  exact Functor.map_isIso _ _

/-- The image in the derived category of a quasi-isomorphism is an epimorphism on every
cohomology functor. -/
theorem epi_homologyFunctor_map_Q_map {P Q' : CochainComplex C ℤ} (f : P ⟶ Q')
    (hf : QuasiIso f) (j : ℤ) :
    Epi ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map f)) :=
  have := isIso_homologyFunctor_map_Q_map f hf j
  IsIso.epi_of_iso _

end Abstract

section TorAmplitude

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u} X)]

/-- `HasDerivedCategory` for `Stacks.DerivedTensor.RingedSite.Modules X.sheaf`, which is
`OXMod X` by `rfl`. -/
local instance hasDerivedCategoryModules :
    HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules X.sheaf) :=
  inferInstanceAs (HasDerivedCategory.{d} (OXMod.{u} X))

/-- The derived tensor product on `D(O_X)` for a ringed space `X`: the canonical derived tensor
product of the ringed site of opens of `X`. -/
@[sga "4½ Etat_0 6.2" "ringed space ⊗^L", sga "4 XVII 4.1.7" "(i), ringed space"]
def derTensor (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)] :
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.{d, u} X.sheaf :=
  Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct X.sheaf

/-- An object of `D(O_X)` has Tor amplitude in `[a, b]` when its derived tensor product with
every `O_X`-module, placed in degree `0`, has vanishing cohomology in every degree outside
`[a, b]`. -/
@[stacks 08CG "tor amplitude in an interval, at the derived tensor product of Tag 06YU",
  sga "6 I 5.2" "Tor-amp(F) ⊂ [m,n]",
  sga "4½ Rapport 4.5" "sheaf tor-dimension ≤ r", sga "4 XVII 4.1.9" "ringed space, (i)"]
def HasTorAmplitude (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]
    (E : DerivedCategory (OXMod.{u} X)) (a b : ℤ) : Prop :=
  ∀ (F : OXMod.{u} X) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u} X) i).obj
      (((derTensor X).tensor.obj E).obj
        ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj F)))

/-- An object of `D(O_X)` has finite Tor dimension when it has Tor amplitude in some interval
`[a, b]`. -/
@[stacks 08CG "finite tor dimension, at the derived tensor product of Tag 06YU",
  sga "6 I 5.2" "finite flat amplitude",
  sga "4½ Rapport 4.5" "sheaf case, finite"]
abbrev HasFiniteTorDimension (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]
    (E : DerivedCategory (OXMod.{u} X)) : Prop :=
  ∃ a b : ℤ, HasTorAmplitude X E a b

/-- An `O_X`-module `F` has Tor dimension at most `n` when `F[0]`, viewed in `D(O_X)`, has Tor
amplitude in `[-n, 0]`. -/
@[stacks 08CG "tor dimension of a module, at the derived tensor product of Tag 06YU",
  sga "4½ Rapport 4.5" "sheaf module case",
  sga "4 XVII 4.1.9" "ringed space, module"]
def HasTorDimensionLE (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]
    (F : OXMod.{u} X) (n : ℤ) : Prop :=
  HasTorAmplitude X ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj F) (-n) 0

/-- An `O_X`-module `F` has Tor dimension at most `n` if and only if the cohomology of
`F[0] ⊗^L G[0]` vanishes outside `[-n, 0]` for every `O_X`-module `G`. -/
theorem hasTorDimensionLE_iff (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u} X)]
    (F : OXMod.{u} X) (n : ℤ) :
    HasTorDimensionLE X F n ↔
      ∀ (G : OXMod.{u} X) (i : ℤ), i ∉ Set.Icc (-n) 0 →
        IsZero ((DerivedCategory.homologyFunctor (OXMod.{u} X) i).obj
          (((derTensor X).tensor.obj
              ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj F)).obj
            ((DerivedCategory.singleFunctor (OXMod.{u} X) 0).obj G))) :=
  Iff.rfl

/-- Restriction of `O_X`-modules to an open preserves finite limits. -/
local instance restrictModules_preservesFiniteLimits (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : PreservesFiniteLimits
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U) :=
  Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteLimits X U

/-- Restriction of `O_X`-modules to an open preserves finite colimits. -/
local instance restrictModules_preservesFiniteColimits (X : RingedSpace.{u, u})
    (U : Opens X.carrier) : PreservesFiniteColimits
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X U) :=
  inferInstance

/-- An object of `D(O_X)` locally has finite Tor dimension when its restriction to each member of
some open cover has finite Tor dimension. -/
@[stacks 08CG "locally finite tor dimension, at the Tag 06YU tensor on each open subspace"]
def LocallyHasFiniteTorDimension (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (OXMod.{u} X)]
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u} (X.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u} X)) : Prop :=
  ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i : I, HasFiniteTorDimension (X.restrict (U i).isOpenEmbedding)
      ((AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X
        (U i)).mapDerivedCategory.obj E)

end TorAmplitude

section PseudoCoherence

variable {X : RingedSpace.{u, u}}
variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u} (X.restrict U.isOpenEmbedding))]

/-- A quasi-isomorphism `P ⟶ F|_V` from a strictly perfect complex on an open `V ∋ x` gives, for
every `m`, a local derived approximation of `F` near `x`: a map in the derived category which is
an isomorphism on cohomology above `m` and an epimorphism on cohomology in degree `m`. -/
theorem exists_local_derived_approximation_of_model (m : ℤ)
    (F : CochainComplex (OXMod.{u} X) ℤ) (x : X.carrier)
    (V : Opens X.carrier) (hxV : x ∈ V)
    (P : CochainComplex (OXMod.{u} (X.restrict V.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P) (f : P ⟶
      AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex F V) (hq : QuasiIso f) :
    ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P' : CochainComplex (OXMod.{u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P' ∧
        ∃ α : DerivedCategory.Q.obj P' ⟶
            DerivedCategory.Q.obj
              (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex F U),
          (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor _ m).map α) :=
  ⟨V, hxV, P, hP, DerivedCategory.Q.map f,
    fun j _ => isIso_homologyFunctor_map_Q_map f hq j,
    epi_homologyFunctor_map_Q_map f hq m⟩

/-- A perfect complex `F` admits, near every point `x` and for every `m`, a local derived
approximation by a strictly perfect complex: an open `U ∋ x`, a strictly perfect complex `P` on
`U` and a map `P ⟶ F|_U` in the derived category which is an isomorphism on cohomology above `m`
and an epimorphism on cohomology in degree `m`. -/
theorem exists_local_derived_approximation_of_isPerfectComplex
    (F : CochainComplex (OXMod.{u} X) ℤ)
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfectComplex F) (m : ℤ) :
    ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        ∃ α : DerivedCategory.Q.obj P ⟶
            DerivedCategory.Q.obj
              (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex F U),
          (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor _ m).map α) := by
  intro x
  have hx : x ∈ iSup hF.choose_spec.choose := by
    rw [hF.choose_spec.choose_spec.1]; trivial
  have hi := Opens.mem_iSup.mp hx
  have hmod := hF.choose_spec.choose_spec.2 hi.choose
  exact exists_local_derived_approximation_of_model m F x _ hi.choose_spec hmod.choose
    hmod.choose_spec.1 hmod.choose_spec.2.choose hmod.choose_spec.2.choose_spec

end PseudoCoherence

end Stacks.Cohomology.TorAmplitude

end
