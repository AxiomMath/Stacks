module

public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.ClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.CapClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedSubschemeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatModuleRelativeCycle
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertCycleClass
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.HilbertFlatness
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative
public import StacksFrontier.AlgebraicGeometry.Flatness.FlatteningFunctor.FlatInDimensionsGE
public import StacksCore.Tactic.StacksAttribute

/-!
# Cycle classes of modules and closed subschemes flat over the base

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally of finite type and let
`r ≥ 0`. For a quasi-coherent `𝒪_X`-module `F` of finite type whose support meets every fibre
in dimension at most `r`, the family `[F/X/S]_r` of `r`-cycles on the fibres of `X/S` is a
relative `r`-cycle as soon as `F` is flat over `S` in dimensions `≥ r`; the same then holds for
the family `[Z/X/S]_r` of a closed subscheme `Z ⊆ X` flat over `S` in dimensions `≥ r`.
Consequently the cycle-class homomorphism out of the free abelian group on `Hilb(X/S, r)` takes
its values in the group `z(X/S, r)` of relative `r`-cycles, not merely in the group of all
families of `r`-cycles on fibres.

## Main definitions

* `Stacks.Chow.relativeCycleClassMap` — the cycle-class homomorphism from the free abelian group
  on `Hilb(X/S, r)` to the group `z(X/S, r)` of relative `r`-cycles.
* `Stacks.Chow.HilbertCycleDatum.ofFlat` — over a locally Noetherian base and for `f` of finite
  type, a closed subscheme flat and of relative dimension at most `r` over `S` is a member of
  `Hilb(X/S, r)`.

## Main results

* `Stacks.Chow.isRelativeCycle_familyAssociatedToModule` — Tag 0H56: `[F/X/S]_r` is a relative
  `r`-cycle when `F` is flat over `S` in dimensions `≥ r`.
* `Stacks.Chow.isRelativeCycle_familyAssociatedToClosedSubscheme` — Tag 0H57: the same for the
  family `[Z/X/S]_r` of a closed subscheme.
* `Stacks.Chow.topologicalKrullDim_pullback_fiberClosedSubscheme_closedPoint_le` and
  `Stacks.Chow.specializationCycle_familyAssociatedToClosedSubscheme_of_genericFibre` —
  Tag 0H4J: for a closed subscheme flat over a discrete valuation ring whose generic fibre has
  dimension at most `r`, the special fibre has dimension at most `r` and
  `sp_{Y/R}([Z_K]_r) = [Z_κ]_r`.
* `Stacks.Chow.topologicalKrullDim_supp_fiberClosedSubscheme_closedPoint_le` and
  `Stacks.Chow.specializationCycle_familyAssociatedToClosedSubscheme` — the same two clauses of
  Tag 0H4J read for the support of `i_* 𝒪_Z` and for the family `[i_* 𝒪_Z/Y/Spec R]_r`.
* `Stacks.Chow.relativeCycleClassMap_of` — the value of the cycle-class homomorphism on a
  generator of the free abelian group.

## Implementation notes

The valuative condition defining a relative `r`-cycle quantifies over all discrete valuation
rings `R` and all morphisms `Spec R ⟶ S`, and compares the generic and the closed member of the
base change along such a morphism. The proof of Tag 0H56 is therefore the composite of two
inputs: the base change clause of Tag 0H4R along an arbitrary morphism of bases, which rewrites
the two members as the members of the family associated to the pulled-back module, and the
specialization formula over a discrete valuation ring, which identifies them. Flatness over the
base in dimensions `≥ r` passes to the pullback by
`AlgebraicGeometry.IsFlatOverInDimensionsGE`'s base change stability, which is Tag 0CWF.

Tags 0H56 and 0H57 state flatness over the base in dimensions `≥ r` in the form Stacks
Definition 0CWG gives it, namely the bound `dim < r` on the locus of each fibre where the module
fails to be flat over the base;
`AlgebraicGeometry.isFlatOverInDimensionsGE_iff_forall_topologicalKrullDim_lt` passes between
that bound and the named condition inside the proofs.

Tag 0H4J is Tag 0H4I for the module `𝒪_Z`: its hypothesis is honest flatness of `Z` over the
discrete valuation ring, which gives flatness of `i_* 𝒪_Z` over the base at every point of `Y`
by `Stacks.Chow.isFlatOver_pushforwardStructureSheaf`, and its bound is on the generic fibre
alone, the bound on the special fibre being part of its conclusion. It carries no finiteness
hypothesis: `i_* 𝒪_Z` is of finite type by
`Stacks.Chow.isFiniteType_pushforwardStructureSheaf` and quasi-coherent by
`Stacks.Modules.isQuasicoherent_pushforwardStructureSheaf`, a closed immersion being affine.
Passing from the module to the closed subscheme itself — from `Supp((i_* 𝒪_Z)_s)` to `Z_s`, and
from `[i_* 𝒪_Z/Y/Spec R]_r` to `[Z/Y/Spec R]_r` — is the source's reference to Chow Homology,
Lemma 42.10.3: `Stacks.Chow.topologicalKrullDim_pullback_fiberι_eq_supp` for the first and
`Stacks.Chow.familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule` for the second.

The members of `Hilb(X/S, r)` are flat over the base in every dimension, by
`Stacks.Chow.HilbertCycleDatum.isFlatOverInDimensionsGE_structureModule`, since flatness of
`Z ⟶ S` is part of their data; so the cycle-class homomorphism into `z(X/S, r)` needs no
flatness input beyond that datum.

Equation 0H58 takes `f` of finite type. The homomorphism is built for `f` locally of finite type:
quasi-compactness of `f` is used neither for the family `[Z/X/S]_r` nor for Lemma 0H57. A member
of `Hilb(X/S, r)` carries flatness, finite presentation and quasi-compactness of `Z ⟶ S`; under
the source's hypotheses the last two are automatic, which is
`Stacks.Chow.HilbertCycleDatum.ofFlat`, so the domain is the source's `Hilb(X/S, r)`.

## References

* [Stacks Project, Lemma 0H56](https://stacks.math.columbia.edu/tag/0H56)
* [Stacks Project, Lemma 0H4J](https://stacks.math.columbia.edu/tag/0H4J)
* [Stacks Project, Equation 0H58](https://stacks.math.columbia.edu/tag/0H58)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- The fibrewise support of a quasi-coherent module of finite type has dimension at most `r`
over every point of the base. This is the side condition under which the family `[F/X/S]_r` of
`r`-cycles on the fibres of `X/S` is defined. -/
abbrev FiberSupportDimensionLE {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (r : ℕ) : Prop :=
  ∀ s : S, topologicalKrullDim
    (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤ (r : WithBot ℕ∞)

/-! ### The cycle of a module flat over the base is a relative cycle -/

/-- **Stacks Project, Lemma 0H56.** Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of
finite type and let `F` be a quasi-coherent `𝒪_X`-module of finite type whose fibrewise support
has dimension at most `r`. If `F` is flat over `S` in dimensions `≥ r`, then `[F/X/S]_r` is a
relative `r`-cycle on `X/S`.

Flatness over `S` in dimensions `≥ r` is spelled out as Stacks Definition 0CWG defines it: for
every point `s` of `S` the locus in the fibre `X_s` where `F` fails to be flat over `S` has
dimension less than `r`. -/
@[stacks 0H56 "the source's hypothesis that the module is flat over the base in dimensions at \
least r, Stacks Definition 0CWG, written out as the dimension bound on the non-flat locus"]
theorem isRelativeCycle_familyAssociatedToModule {r : ℕ} {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent]
    (hF : ∀ s : S, topologicalKrullDim
      ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom F (f.fiberι s y)} < (r : WithBot ℕ∞))
    (hdim : FiberSupportDimensionLE f F r) :
    IsRelativeCycle f r (familyAssociatedToModule f F r hdim) :=
  isRelativeCycle_familyAssociatedToModule_of_isFlatOverInDimensionsGE f F r
    ((isFlatOverInDimensionsGE_iff_forall_topologicalKrullDim_lt f F r).mpr hF) hdim

/-! ### The cycle of a closed subscheme flat over the base -/

/-- The direct image of the structure sheaf of a closed subscheme `Z ⊆ X` under the closed
immersion. Its cycle on the fibre over `s` is the cycle `[Z_s]_r` of Tag 02QY, so the family of
cycles it determines is the family `[Z/X/S]_r` of Tag 0H4S. -/
abbrev structureSheafPushforward {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    X.Modules :=
  (Scheme.Modules.pushforward i).obj (Ample.unitModule Z)

/-- **Stacks Project, Lemma 0H57.** Let `S` be locally Noetherian, let `f : X ⟶ S` be locally of
finite type and let `i : Z ⟶ X` be a closed immersion. If the structure sheaf of `Z`, viewed on
`X`, is flat over `S` in dimensions `≥ r` and its fibrewise support has dimension at most `r`,
then `[Z/X/S]_r` is a relative `r`-cycle on `X/S`.

This is the proof of the source: the cycle of a closed subscheme is the cycle of its structure
sheaf by Tag 02QY, so Tag 0H56 applies to the direct image of that structure sheaf.

Flatness over `S` in dimensions `≥ r` is spelled out as Stacks Definition 0CWG defines it: for
every point `s` of `S` the locus in the fibre `X_s` where `i_* 𝒪_Z` fails to be flat over `S`
has dimension less than `r`. -/
@[stacks 0H57 "the source's hypothesis that the structure sheaf is flat over the base in \
dimensions at least r, Stacks Definition 0CWG, written out as the dimension bound on the \
non-flat locus"]
theorem isRelativeCycle_familyAssociatedToClosedSubscheme {r : ℕ} {X S Z : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (i : Z ⟶ X)
    [IsClosedImmersion i] [(structureSheafPushforward i).IsFiniteType]
    [(structureSheafPushforward i).IsQuasicoherent]
    (hZ : ∀ s : S, topologicalKrullDim
      ↥{y : f.fiber s | ¬ IsFlatOverAt f.toLRSHom.toShHom (structureSheafPushforward i)
        (f.fiberι s y)} < (r : WithBot ℕ∞))
    (hdim : FiberSupportDimensionLE f (structureSheafPushforward i) r) :
    IsRelativeCycle f r (familyAssociatedToModule f (structureSheafPushforward i) r hdim) :=
  isRelativeCycle_familyAssociatedToModule f (structureSheafPushforward i) hZ hdim

/-! ### Closed subschemes flat over a discrete valuation ring -/

/-- **Stacks Project, Lemma 0H4J**, the dimension clause for the support of `i_* 𝒪_Z`. Let `R`
be a discrete valuation ring with fraction field `K` and residue field `κ`, let `Y` be locally
of finite type over `R`, let `r ≥ 0` and let `Z ⊆ Y` be a closed subscheme flat over `R`. If
`dim(Supp((i_* 𝒪_Z)_K)) ≤ r`, then `dim(Supp((i_* 𝒪_Z)_κ)) ≤ r`.

With `𝒪_Z` for the module this is the dimension clause of Tag 0H4I; it is the tag's own
statement `dim(Z_K) ≤ r ⟹ dim(Z_κ) ≤ r` read through
`Stacks.Chow.topologicalKrullDim_pullback_fiberι_eq_supp`, which is what
`Stacks.Chow.topologicalKrullDim_pullback_fiberClosedSubscheme_closedPoint_le` below does. -/
@[stacks 0H4J "the dimension bound on the special fibre, for the support of i_* 𝒪_Z"]
theorem topologicalKrullDim_supp_fiberClosedSubscheme_closedPoint_le {r : ℕ} {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (.of R)) [LocallyOfFiniteType p] (i : Z ⟶ Y) [IsClosedImmersion i]
    [Flat (i ≫ p)]
    (hK : topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pullback (p.fiberι (genericPoint (Spec (.of R))))).obj
        (structureSheafPushforward i))) ≤ (r : WithBot ℕ∞)) :
    topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pullback (p.fiberι (IsLocalRing.closedPoint R))).obj
        (structureSheafPushforward i))) ≤ (r : WithBot ℕ∞) :=
  topologicalKrullDim_supp_fiberModule_closedPoint_le p (structureSheafPushforward i)
    (isFlatOver_pushforwardStructureSheaf i p) r hK

/-- **Stacks Project, Lemma 0H4J**, the specialization formula for the family of `i_* 𝒪_Z`. Let
`R` be a discrete valuation ring with fraction field `K` and residue field `κ`, let `Y` be
locally of finite type over `R`, let `r ≥ 0` and let `Z ⊆ Y` be a closed subscheme flat over `R`
with `dim(Supp((i_* 𝒪_Z)_K)) ≤ r`. Then the specialization map `sp_{Y/R}` carries the member of
`[i_* 𝒪_Z/Y/Spec R]_r` over the generic point to its member over the closed point.

With `𝒪_Z` for the module this is the specialization clause of Tag 0H4I; the bound on every
fibre that the family `[Z/Y/Spec R]_r` consumes comes from the bound on the generic fibre by
`Stacks.Chow.topologicalKrullDim_supp_fiberModule_le_of_genericFibre`. The tag's own formula
`sp_{Y/R}([Z_K]_r) = [Z_κ]_r`, for the family `[Z/Y/Spec R]_r` of the closed subscheme itself,
is `Stacks.Chow.specializationCycle_familyAssociatedToClosedSubscheme_of_genericFibre` below. -/
@[stacks 0H4J "the specialization formula for the family of i_* 𝒪_Z"]
theorem specializationCycle_familyAssociatedToClosedSubscheme {r : ℕ} {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType p] (i : Z ⟶ Y) [IsClosedImmersion i] [Flat (i ≫ p)]
    (hK : topologicalKrullDim (SheafOfModules.supp
      ((Scheme.Modules.pullback (p.fiberι (genericPoint (Spec (.of R))))).obj
        (structureSheafPushforward i))) ≤ (r : WithBot ℕ∞)) :
    specializationCycle p r
        (familyAssociatedToModule p (structureSheafPushforward i) r
          (topologicalKrullDim_supp_fiberModule_le_of_genericFibre p
            (structureSheafPushforward i) (isFlatOver_pushforwardStructureSheaf i p) r hK)
          (genericPoint (Spec (.of R)))) =
      familyAssociatedToModule p (structureSheafPushforward i) r
        (topologicalKrullDim_supp_fiberModule_le_of_genericFibre p
          (structureSheafPushforward i) (isFlatOver_pushforwardStructureSheaf i p) r hK)
        (IsLocalRing.closedPoint R) :=
  specializationCycle_familyAssociatedToModule p (structureSheafPushforward i)
    (isFlatOver_pushforwardStructureSheaf i p) r hK

/-! ### Tag 0H4J for the closed subscheme itself -/

/-- The fibre `Z_s = Z ×_X X_s` of a closed subscheme `i : Z ⟶ X` over a point `s` of the base
and the support of `i_* 𝒪_Z` on the fibre `X_s` have the same dimension: by
`Stacks.Chow.supp_pullback_fiberι_pushforwardStructureSheaf` that support is the image of `Z_s`
under the closed immersion `Z_s ⟶ X_s`, hence homeomorphic to `Z_s`. -/
theorem topologicalKrullDim_pullback_fiberι_eq_supp {X S Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ S) (s : S) :
    topologicalKrullDim (pullback i (f.fiberι s) : Scheme.{u}) =
      topologicalKrullDim (SheafOfModules.supp
        ((Scheme.Modules.pullback (f.fiberι s)).obj (structureSheafPushforward i))) := by
  rw [supp_pullback_fiberι_pushforwardStructureSheaf]
  exact IsHomeomorph.topologicalKrullDim_eq _ (IsClosedImmersion.isClosedEmbedding
    (pullback.snd i (f.fiberι s))).isEmbedding.toHomeomorph.isHomeomorph

/-- **Stacks Project, Lemma 0H4J**, the bound on every fibre. Let `R` be a discrete valuation
ring, let `Y` be locally of finite type over `R`, let `r ≥ 0` and let `Z ⊆ Y` be a closed
subscheme flat over `R` with `dim(Z_K) ≤ r`. Then `dim(Z_s) ≤ r` for every point `s` of
`Spec R`.

This is the bound of Tag 0H3X over a discrete valuation ring, applied to `i_* 𝒪_Z`: flatness of
`Z` over `R` is flatness of `i_* 𝒪_Z` over `R` by
`Stacks.Chow.isFlatOver_pushforwardStructureSheaf`, and the two dimensions agree by
`Stacks.Chow.topologicalKrullDim_pullback_fiberι_eq_supp`. -/
theorem topologicalKrullDim_pullback_fiberι_le_of_genericFibre {r : ℕ} {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType p] (i : Z ⟶ Y) [IsClosedImmersion i] [Flat (i ≫ p)]
    (hK : topologicalKrullDim (pullback i (p.fiberι (genericPoint (Spec (.of R)))) :
      Scheme.{u}) ≤ (r : WithBot ℕ∞)) (s : Spec (.of R)) :
    topologicalKrullDim (pullback i (p.fiberι s) : Scheme.{u}) ≤ (r : WithBot ℕ∞) := by
  rw [topologicalKrullDim_pullback_fiberι_eq_supp i p s]
  exact topologicalKrullDim_supp_fiberModule_le_of_genericFibre p (structureSheafPushforward i)
    (isFlatOver_pushforwardStructureSheaf i p) r
    (le_of_eq_of_le (topologicalKrullDim_pullback_fiberι_eq_supp i p _).symm hK) s

/-- **Stacks Project, Lemma 0H4J.** Let `R` be a discrete valuation ring with fraction field `K`
and residue field `κ`, let `Y` be locally of finite type over `R`, let `r ≥ 0` and let `Z ⊆ Y` be
a closed subscheme flat over `R`. If `dim(Z_K) ≤ r`, then `dim(Z_κ) ≤ r`.

This is the previous bound at the closed point of `Spec R`. -/
@[stacks 0H4J "the dimension bound on the special fibre"]
theorem topologicalKrullDim_pullback_fiberClosedSubscheme_closedPoint_le {r : ℕ} {R : Type u}
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (.of R)) [LocallyOfFiniteType p] (i : Z ⟶ Y) [IsClosedImmersion i]
    [Flat (i ≫ p)]
    (hK : topologicalKrullDim (pullback i (p.fiberι (genericPoint (Spec (.of R)))) :
      Scheme.{u}) ≤ (r : WithBot ℕ∞)) :
    topologicalKrullDim (pullback i (p.fiberι (IsLocalRing.closedPoint R)) :
      Scheme.{u}) ≤ (r : WithBot ℕ∞) :=
  topologicalKrullDim_pullback_fiberι_le_of_genericFibre p i hK (IsLocalRing.closedPoint R)

/-- **Stacks Project, Lemma 0H4J.** Let `R` be a discrete valuation ring with fraction field `K`
and residue field `κ`, let `Y` be locally of finite type over `R`, let `r ≥ 0` and let `Z ⊆ Y` be
a closed subscheme flat over `R` with `dim(Z_K) ≤ r`. Then the specialization homomorphism
`sp_{Y/R}` of Section 0H4H carries `[Z_K]_r` to `[Z_κ]_r`.

This is the proof of the source: the family `[Z/Y/Spec R]_r` of the closed subscheme is the
family `[i_* 𝒪_Z/Y/Spec R]_r` of its structure sheaf by Chow Homology, Lemma 42.10.3, which is
`Stacks.Chow.familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule`, and for that family
the formula is the specialization clause of Tag 0H4I. The bound on every fibre that the
identification consumes comes from the bound on the generic fibre by
`Stacks.Chow.topologicalKrullDim_pullback_fiberι_le_of_genericFibre`. -/
@[stacks 0H4J "the specialization formula"]
theorem specializationCycle_familyAssociatedToClosedSubscheme_of_genericFibre {r : ℕ}
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {Y Z : Scheme.{u}}
    (p : Y ⟶ Spec (.of R)) [LocallyOfFiniteType p] (i : Z ⟶ Y) [IsClosedImmersion i]
    [Flat (i ≫ p)]
    (hK : topologicalKrullDim (pullback i (p.fiberι (genericPoint (Spec (.of R)))) :
      Scheme.{u}) ≤ (r : WithBot ℕ∞)) :
    specializationCycle p r
        (familyAssociatedToClosedSubscheme p i r (genericPoint (Spec (.of R)))) =
      familyAssociatedToClosedSubscheme p i r (IsLocalRing.closedPoint R) := by
  rw [familyAssociatedToClosedSubscheme_eq_familyAssociatedToModule p i r
    (topologicalKrullDim_pullback_fiberι_le_of_genericFibre p i hK)]
  exact specializationCycle_familyAssociatedToClosedSubscheme p i
    (le_of_eq_of_le (topologicalKrullDim_pullback_fiberι_eq_supp i p _).symm hK)

/-! ### The cycle-class homomorphism into the group of relative cycles -/

/-- The family `[Z/X/S]_r` of a member of `Hilb(X/S, r)` is a relative `r`-cycle: its structure
sheaf is flat over `S` in every dimension, flatness of `Z ⟶ S` being part of the datum. -/
theorem isRelativeCycle_cycleFamily {r : ℕ} {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (Z : HilbertCycleDatum f r) :
    IsRelativeCycle f r (Z.cycleFamily f) :=
  isRelativeCycle_familyAssociatedToModule f Z.structureModule
    ((isFlatOverInDimensionsGE_iff_forall_topologicalKrullDim_lt f Z.structureModule r).mp
      (Z.isFlatOverInDimensionsGE_structureModule r))
    (Z.structureModule_fiberSupport_dimension_le f)

/-- **The members of `Hilb(X/S, r)` in the Noetherian setting.** Let `S` be locally Noetherian
and let `f : X ⟶ S` be of finite type. A closed subscheme `Z ⊆ X`, given by its ideal sheaf,
such that `Z ⟶ S` is flat and of relative dimension at most `r` is a member of `Hilb(X/S, r)`:
the remaining conditions of the datum, that `Z ⟶ S` is of finite presentation, hold
automatically, `Z ⟶ S` being of finite type over a locally Noetherian scheme (Tag 01TX). So
under the hypotheses of Equation 0H58 the type `Stacks.Chow.HilbertCycleDatum f r` is the set
`Hilb(X/S, r)` of the source. -/
def HilbertCycleDatum.ofFlat {r : ℕ} {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsLocallyNoetherian S] (I : X.IdealSheafData)
    [Flat (I.subschemeι ≫ f)] (hdim : RelativeDimensionLE (I.subschemeι ≫ f) r) :
    HilbertCycleDatum f r where
  ideal := I
  flat := inferInstance
  locallyFinitePresentation := inferInstance
  quasiCompact := inferInstance
  relativeDimensionLE := hdim

/-- The ideal sheaf of `HilbertCycleDatum.ofFlat f I hdim` is `I`. -/
@[simp]
theorem HilbertCycleDatum.ofFlat_ideal {r : ℕ} {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsLocallyNoetherian S] (I : X.IdealSheafData)
    [Flat (I.subschemeι ≫ f)] (hdim : RelativeDimensionLE (I.subschemeι ≫ f) r) :
    (HilbertCycleDatum.ofFlat f I hdim).ideal = I :=
  rfl

/-- **Stacks Project, Equation 0H58.** Let `S` be locally Noetherian, let `f : X ⟶ S` be locally
of finite type and let `r ≥ 0`. The cycle-class homomorphism from the free abelian group on
`Hilb(X/S, r)` to the group `z(X/S, r)` of relative `r`-cycles on `X/S`, sending `∑ nᵢ [Zᵢ]` to
`∑ nᵢ [Zᵢ/X/S]_r`. It refines the homomorphism of Tag 0H6V, whose values are families of
`r`-cycles on fibres, by cutting its codomain down to the relative cycles: each `[Zᵢ/X/S]_r` is
a relative `r`-cycle by Lemma 0H57.

The source takes `f` of finite type; quasi-compactness of `f` is not needed, so it is not
assumed. Under the source's hypotheses the members of `Hilb(X/S, r)` are exactly the closed
subschemes flat and of relative dimension at most `r` over `S`, by
`Stacks.Chow.HilbertCycleDatum.ofFlat`. -/
@[stacks 0H58 "the homomorphism into z(X/S, r)"]
def relativeCycleClassMap {r : ℕ} {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] :
    FreeAbelianGroup (HilbertCycleDatum f r) →+ relativeCycles f r :=
  FreeAbelianGroup.lift fun Z => ⟨Z.cycleFamily f, isRelativeCycle_cycleFamily f Z⟩

/-- **Stacks Project, Equation 0H58.** On a generator the cycle-class homomorphism into
`z(X/S, r)` is the family of cycles `[Z/X/S]_r` of the closed subscheme. -/
@[stacks 0H58 "on generators"]
theorem relativeCycleClassMap_of {r : ℕ} {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] (Z : HilbertCycleDatum f r) :
    (relativeCycleClassMap f (FreeAbelianGroup.of Z)).1 = Z.cycleFamily f :=
  congrArg Subtype.val (FreeAbelianGroup.lift_apply_of _ _)

/-- **Stacks Project, Equation 0H58.** The cycle-class homomorphism into `z(X/S, r)` is the
homomorphism of Tag 0H6V followed by the inclusion of the relative cycles into the families of
`r`-cycles on fibres. -/
@[stacks 0H58 "compatibility with the homomorphism of Tag 0H6V"]
theorem relativeCycleClassMap_val {r : ℕ} {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S]
    (α : FreeAbelianGroup (HilbertCycleDatum f r)) :
    (relativeCycleClassMap f α).1 = cycleClassMap f r α := by
  induction α using FreeAbelianGroup.induction_on with
  | zero => simp only [map_zero, ZeroMemClass.coe_zero]
  | of Z => rw [relativeCycleClassMap_of, cycleClassMap_of]
  | neg Z h => rw [map_neg, map_neg, NegMemClass.coe_neg, h]
  | add a b ha hb => rw [map_add, map_add, AddMemClass.coe_add, ha, hb]

end Stacks.Chow

end
