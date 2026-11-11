module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.GroupTheory.FreeAbelianGroup
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.AssociatedToModule
public import StacksFrontier.AlgebraicGeometry.Descent.Finiteness.PushforwardFinite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportPullback.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.RestrictScalars
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Abelian
public import StacksCore.Tactic.StacksAttribute

/-!
# The cycle class of a flat finitely presented closed subscheme

Let `f : X ⟶ S` be a morphism locally of finite presentation and let `r ≥ 0`. The set
`Hilb(X/S, r)` consists of the closed subschemes `Z ⊆ X` whose structure morphism `Z ⟶ S` is flat,
of finite presentation (locally of finite presentation, quasi-compact and quasi-separated) and of
relative dimension at most `r`. Such a `Z` has every fibre `Z_s` of
dimension at most `r`, so the pushforward of its structure sheaf to `X` is a quasi-coherent module
of finite type whose support meets each fibre of `f` in dimension at most `r`, and the construction
of the family of cycles associated to a module therefore applies to it: the resulting family is
`[Z/X/S]_r`. Extending additively from the generators gives the homomorphism

`free abelian group on Hilb(X/S, r) ⟶ families of r-cycles on the fibres of X/S`,

sending `∑ nᵢ [Zᵢ]` to `∑ nᵢ [Zᵢ/X/S]_r`.

## Main definitions

* `Stacks.Chow.HilbertSubscheme` — a member of `Hilb(X/S, r)`: a closed subscheme of `X`,
  flat and of finite presentation over `S`, of relative dimension at most `r`.
* `Stacks.Chow.HilbertCycleDatum` — the same without the quasi-separatedness of `Z ⟶ S`; for
  `f` quasi-separated it is the same set (`HilbertSubscheme.equivHilbertCycleDatum`).
* `Stacks.Chow.HilbertCycleDatum.cycleFamily` — the family `[Z/X/S]_r` of `r`-cycles on the
  fibres of `X/S` attached to such a subscheme.
* `Stacks.Chow.hilbertCycleClassMap` — the displayed homomorphism out of the free abelian group
  on `Hilb(X/S, r)`.
* `Stacks.Chow.cycleClassMap` — the same homomorphism out of the free abelian group on
  `HilbertCycleDatum f r`, used by the rest of the library.

## Main results

* `Stacks.Chow.HilbertCycleDatum.structureModule_fiberSupport_dimension_le` — the support of
  the pushed-forward structure sheaf has dimension at most `r` on every fibre of `f`.
* `Stacks.Chow.hilbertCycleClassMap_of` — on a generator the homomorphism is the family
  `[Z/X/S]_r`.
* `Stacks.Chow.cycleClassMap_eq_comp`, `Stacks.Chow.range_cycleClassMap` — for `f`
  quasi-separated, `cycleClassMap` is the homomorphism of Tag 0H6V, with the same image.

## Implementation notes

A closed subscheme of `X` is recorded by its ideal sheaf, as `Scheme.IdealSheafData`, and the
three conditions on it are stated for the composite `Z ⟶ X ⟶ S`; "of finite presentation" is
`LocallyOfFinitePresentation` together with `QuasiCompact` and `QuasiSeparated` (Tag 01TP).
`HilbertCycleDatum` records only the first two; its quasi-separatedness is automatic when `f` is
quasi-separated, which `HilbertSubscheme` records as a field. Local finite type of that composite,
needed to state the relative dimension condition, is deduced from finite presentation rather
than assumed.

The source takes `f` to be of finite presentation, but only `LocallyOfFinitePresentation f` is
assumed here: quasi-compactness and quasi-separatedness of `f` are never used. Each member of
`Hilb(X/S, r)` carries the finite presentation of its own structure morphism `Z ⟶ S` as part of
its data, and the associated
family of Tag 0H4Q needs no more of `f` than local finite type. So the homomorphism exists, and
is determined on generators, at this larger generality.

The dimension bound on the fibrewise support of the module is obtained from the dimension bound
on the fibres of `Z ⟶ S` and not the other way round: the support of the pushforward lies in the
image of the closed immersion, so the support of its pullback to `X_s` lies in the image of
`Z_s ⟶ X_s`, which is an embedding onto a subspace of dimension at most `r`. The comparison of
`Z_s` with `X_s` is made pointwise, by sending a point of `Z_s` to the point of `X_s` with the
same image in `X`, rather than through the pasting isomorphism of the two pullback squares; the
relative dimension bound of Tag 02NJ is pointwise, so it is turned into a bound on the dimension
of the whole fibre through the description of the dimension of a space as the supremum of its
local dimensions.

## References

* [Stacks Project, Tag 0H6V](https://stacks.math.columbia.edu/tag/0H6V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.QcohLimits

universe u

namespace Stacks.Chow

/-! ### The support of a direct image along a closed immersion -/

/-- The support of the direct image of a module along a closed immersion is contained in the
image of that immersion. -/
private theorem supp_pushforward_subset_range {X Y : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (F : Y.Modules) :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj F) ⊆ Set.range (i : Y → X) := by
  intro x hx
  change ∃ a : ((Scheme.Modules.pushforward i).obj F).presheaf.stalk x, a ≠ 0 at hx
  by_contra hnot
  let G : TopCat.Sheaf AddCommGrpCat.{u} Y.toTopCat := ⟨F.presheaf, F.isSheaf⟩
  have hz : IsZero (((Scheme.Modules.pushforward i).obj F).presheaf.stalk x) := by
    change IsZero (TopCat.Presheaf.stalk
      ((closedInclusionPushforward Y.toTopCat X.toTopCat i.base).obj G).1 x)
    exact closedInclusion_pushforward_stalk_isZero_of_not_mem_range
      Y.toTopCat X.toTopCat i.base i.isClosedEmbedding G x hnot
  obtain ⟨a, ha⟩ := hx
  exact ha (Subsingleton.elim (h := AddCommGrpCat.isZero_iff_subsingleton.mp hz) a 0)

/-! ### Fibres of a morphism of bounded relative dimension -/

/-- If `f` has relative dimension at most `d`, then the local dimension of the fibre `f⁻¹(y)` at
a point `z` is at most `d`. -/
public theorem topologicalKrullDimAt_fiber_le_of_relativeDimensionLE {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {d : ℕ} (hf : RelativeDimensionLE f d) {x : X} {y : Y}
    (hxy : f x = y) (z : f.fiber y) (hx : x = f.fiberι y z) :
    topologicalKrullDimAt (f.fiber y) z ≤ (d : WithBot ℕ∞) := by
  subst y
  have hpoint : f.asFiber x = z := by
    apply (f.fiberHomeo (f x)).injective
    apply Subtype.ext
    change f.fiberι (f x) (f.asFiber x) = f.fiberι (f x) z
    simpa only [f.fiberι_asFiber] using hx
  simpa only [relativeDimensionLEAt_iff, hpoint] using hf x

/-- A morphism of relative dimension at most `d` has fibres of dimension at most `d`. -/
public theorem topologicalKrullDim_fiber_le_of_relativeDimensionLE {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {d : ℕ} (hf : RelativeDimensionLE f d) (y : Y) :
    topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞) := by
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun z => ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim]
  exact topologicalKrullDimAt_fiber_le_of_relativeDimensionLE f hf
    (Set.mem_singleton_iff.mp (f.fiberHomeo y z).2) z rfl

/-! ### The fibre of a composite inside the fibre of its second factor -/

/-- A point of the fibre `f.fiber s` maps into the preimage `f ⁻¹' {s}` of `s`. -/
private theorem fiberι_mem_preimage {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (a : f.fiber s) :
    f.fiberι s a ∈ f ⁻¹' {s} :=
  (f.fiberHomeo s a).2

/-- The map from the fibre of a composite `T ⟶ X ⟶ S` over `s` to the fibre of `X ⟶ S` over
`s`, induced by `T ⟶ X`. -/
private def fiberOfComp {T X S : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ S) (s : S)
    (a : (i ≫ f).fiber s) : f.fiber s :=
  (f.fiberHomeo s).symm ⟨i ((i ≫ f).fiberι s a), fiberι_mem_preimage (i ≫ f) s a⟩

/-- The map of fibres is compatible with the inclusions of the fibres into the total spaces. -/
private theorem fiberι_fiberOfComp {T X S : Scheme.{u}} (i : T ⟶ X) (f : X ⟶ S) (s : S)
    (a : (i ≫ f).fiber s) :
    f.fiberι s (fiberOfComp i f s a) = i ((i ≫ f).fiberι s a) :=
  f.fiberι_fiberHomeo_symm s _

/-- The map of fibres is an embedding. -/
private theorem isEmbedding_fiberOfComp {T X S : Scheme.{u}} (i : T ⟶ X) [IsPreimmersion i]
    (f : X ⟶ S) (s : S) : Topology.IsEmbedding (fiberOfComp i f s) := by
  refine (f.fiberι s).isEmbedding.of_comp_iff.mp ?_
  have hfun : (f.fiberι s : f.fiber s → X) ∘ fiberOfComp i f s =
      (i : T → X) ∘ ((i ≫ f).fiberι s : (i ≫ f).fiber s → T) :=
    funext fun a => fiberι_fiberOfComp i f s a
  rw [hfun]
  exact i.isEmbedding.comp ((i ≫ f).fiberι s).isEmbedding

/-- The image of the map of fibres is the part of the fibre of `f` lying over the image of `i`.
-/
private theorem range_fiberOfComp {T X S : Scheme.{u}} (i : T ⟶ X) [IsPreimmersion i]
    (f : X ⟶ S) (s : S) :
    Set.range (fiberOfComp i f s) = (f.fiberι s) ⁻¹' Set.range (i : T → X) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro b ⟨a, rfl⟩
    exact ⟨(i ≫ f).fiberι s a, (fiberι_fiberOfComp i f s a).symm⟩
  · rintro b ⟨t, ht⟩
    have hts : t ∈ Set.range ((i ≫ f).fiberι s : (i ≫ f).fiber s → T) := by
      rw [Scheme.Hom.range_fiberι]
      change (i ≫ f) t ∈ ({s} : Set S)
      rw [Scheme.Hom.comp_apply, ht]
      exact fiberι_mem_preimage f s b
    obtain ⟨a, ha⟩ := hts
    exact ⟨a, (f.fiberι s).isEmbedding.injective
      ((fiberι_fiberOfComp i f s a).trans ((congrArg i ha).trans ht))⟩

/-- The dimension of the fibrewise support of a direct image along a closed immersion is bounded
by the dimension of the corresponding fibre of the subscheme. -/
private theorem topologicalKrullDim_supp_pullback_le {T X S : Scheme.{u}} (i : T ⟶ X)
    [IsClosedImmersion i] (f : X ⟶ S) (s : S) (M : T.Modules)
    [((Scheme.Modules.pushforward i).obj M).IsFiniteType] {r : ℕ}
    (hdim : topologicalKrullDim ((i ≫ f).fiber s) ≤ (r : WithBot ℕ∞)) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj
      ((Scheme.Modules.pushforward i).obj M))) ≤ (r : WithBot ℕ∞) := by
  have hsub : SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj
      ((Scheme.Modules.pushforward i).obj M)) ⊆ Set.range (fiberOfComp i f s) := by
    rw [SheafOfModules.supp_pullback, range_fiberOfComp]
    exact Set.preimage_mono (supp_pushforward_subset_range i M)
  calc
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj
          ((Scheme.Modules.pushforward i).obj M))) ≤
        topologicalKrullDim (Set.range (fiberOfComp i f s)) :=
      (Topology.IsInducing.subtypeVal.codRestrict fun x => hsub x.2).topologicalKrullDim_le
    _ = topologicalKrullDim ((i ≫ f).fiber s) :=
      ((isEmbedding_fiberOfComp i f s).toHomeomorph.isHomeomorph.topologicalKrullDim_eq _).symm
    _ ≤ (r : WithBot ℕ∞) := hdim

/-! ### The members of `Hilb(X/S, r)` -/

/-- A closed subscheme `Z ⊆ X`, given by its ideal sheaf, whose structure morphism `Z ⟶ S` is
flat, locally of finite presentation, quasi-compact, and of relative dimension at most `r`.

This omits the quasi-separatedness of `Z ⟶ S` that "of finite presentation" (Tag 01TP) includes,
so for a general `f` it is a larger set than `Hilb(X/S, r)`. When `f` is quasi-separated, as it is
in the source, where `f` is of finite presentation, the closed immersion `Z ⟶ X` makes `Z ⟶ S`
quasi-separated automatically, and `HilbertSubscheme.equivHilbertCycleDatum` identifies the two
sets. `Hilb(X/S, r)` itself is `HilbertSubscheme`. -/
structure HilbertCycleDatum {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ) where
  /-- The ideal sheaf cutting out the closed subscheme `Z ⊆ X`. -/
  ideal : X.IdealSheafData
  /-- `Z ⟶ S` is flat. -/
  flat : Flat (ideal.subschemeι ≫ f)
  /-- `Z ⟶ S` is locally of finite presentation. -/
  locallyFinitePresentation : LocallyOfFinitePresentation (ideal.subschemeι ≫ f)
  /-- `Z ⟶ S` is quasi-compact; together with the previous field, of finite presentation. -/
  quasiCompact : QuasiCompact (ideal.subschemeι ≫ f)
  /-- `Z ⟶ S` has relative dimension at most `r`, in the sense of Tag 02NJ. -/
  relativeDimensionLE :
    letI : LocallyOfFiniteType (ideal.subschemeι ≫ f) := by infer_instance
    RelativeDimensionLE (ideal.subschemeι ≫ f) r

namespace HilbertCycleDatum

variable {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}

/-- The structure sheaf of the closed subscheme `Z`, pushed forward to an `𝒪_X`-module. Its
associated cycles on the fibres of `X/S` are the cycles of the fibres of `Z`. -/
abbrev structureModule (Z : HilbertCycleDatum f r) : X.Modules :=
  (Scheme.Modules.pushforward Z.ideal.subschemeι).obj
    (SheafOfModules.unit Z.ideal.subscheme.ringCatSheaf)

/-- The pushed-forward structure sheaf of a closed subscheme is of finite type. -/
instance structureModule_isFiniteType (Z : HilbertCycleDatum f r) :
    Z.structureModule.IsFiniteType :=
  (isFiniteType_iff_pushforward_isFiniteType Z.ideal.subschemeι _).mp
    (structureSheaf_isFiniteType Z.ideal.subscheme)

/-- The pushed-forward structure sheaf of a closed subscheme is quasi-coherent. -/
instance structureModule_isQuasicoherent (Z : HilbertCycleDatum f r) :
    Z.structureModule.IsQuasicoherent :=
  (affine_isQuasicoherent_restrictScalars_iff Z.ideal.subschemeι _).2
    (affinePushforward_isQuasicoherent Z.ideal.subschemeι _
      (Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _))

/-- The support of the pushed-forward structure sheaf has dimension at most `r` on every fibre
of `f`. -/
theorem structureModule_fiberSupport_dimension_le (f : X ⟶ S)
    [LocallyOfFinitePresentation f] {r : ℕ} (Z : HilbertCycleDatum f r) (s : S) :
    topologicalKrullDim (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj
      Z.structureModule)) ≤ (r : WithBot ℕ∞) :=
  topologicalKrullDim_supp_pullback_le Z.ideal.subschemeι f s _
    (topologicalKrullDim_fiber_le_of_relativeDimensionLE (Z.ideal.subschemeι ≫ f)
      Z.relativeDimensionLE s)

/-- The family `[Z/X/S]_r` of `r`-cycles on the fibres of `X/S` attached to a member of
`Hilb(X/S, r)`: the family associated to the pushforward of the structure sheaf of `Z`, whose
member over `s` is the cycle `[Z_s]_r` of the fibre. -/
def cycleFamily (f : X ⟶ S) [LocallyOfFinitePresentation f] {r : ℕ}
    (Z : HilbertCycleDatum f r) : FamilyOfCycles f r :=
  familyAssociatedToModule f Z.structureModule r
    (Z.structureModule_fiberSupport_dimension_le f)

end HilbertCycleDatum

/-! ### The cycle-class homomorphism -/

/-- The homomorphism from the free abelian group on `HilbertCycleDatum f r` to the families of
`r`-cycles on the fibres of `X/S`, sending `∑ nᵢ [Zᵢ]` to `∑ nᵢ [Zᵢ/X/S]_r`. When `f` is
quasi-separated it agrees with `hilbertCycleClassMap`, the homomorphism of Tag 0H6V, under the
identification `HilbertSubscheme.equivHilbertCycleDatum` (`cycleClassMap_eq_comp`). -/
def cycleClassMap {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f] (r : ℕ) :
    FreeAbelianGroup (HilbertCycleDatum f r) →+ FamilyOfCycles f r :=
  FreeAbelianGroup.lift fun Z => Z.cycleFamily f

/-- On a generator the homomorphism `cycleClassMap` is the family of cycles `[Z/X/S]_r` of the
closed subscheme. -/
theorem cycleClassMap_of {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (r : ℕ) (Z : HilbertCycleDatum f r) :
    cycleClassMap f r (FreeAbelianGroup.of Z) = Z.cycleFamily f :=
  FreeAbelianGroup.lift_apply_of _ _

/-! ### `Hilb(X/S, r)` and the homomorphism of Tag 0H6V -/

/-- A member of `Hilb(X/S, r)`: a closed subscheme `Z ⊆ X`, given by its ideal sheaf, whose
structure morphism `Z ⟶ S` is flat, of finite presentation (locally of finite presentation,
quasi-compact and quasi-separated, Tag 01TP), and of relative dimension at most `r`. -/
@[stacks 0H6V "the set Hilb(X/S, r)"]
structure HilbertSubscheme {X S : Scheme.{u}} (f : X ⟶ S) (r : ℕ)
    extends HilbertCycleDatum f r where
  /-- `Z ⟶ S` is quasi-separated; with `locallyFinitePresentation` and `quasiCompact`, of finite
  presentation. -/
  quasiSeparated : QuasiSeparated (ideal.subschemeι ≫ f)

/-- When `f` is quasi-separated (in particular when `f` is of finite presentation), every closed
subscheme `Z ⊆ X` has `Z ⟶ S` quasi-separated, so `Hilb(X/S, r)` is `HilbertCycleDatum f r`. -/
def HilbertSubscheme.equivHilbertCycleDatum {X S : Scheme.{u}} (f : X ⟶ S) [QuasiSeparated f]
    (r : ℕ) : HilbertSubscheme f r ≃ HilbertCycleDatum f r where
  toFun Z := Z.toHilbertCycleDatum
  invFun Z := ⟨Z, inferInstance⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The homomorphism of Tag 0H6V from the free abelian group on `Hilb(X/S, r)` to the families of
`r`-cycles on the fibres of `X/S`, sending `∑ nᵢ [Zᵢ]` to `∑ nᵢ [Zᵢ/X/S]_r`. -/
@[stacks 0H6V "the homomorphism; for `f` locally of finite presentation"]
def hilbertCycleClassMap {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (r : ℕ) : FreeAbelianGroup (HilbertSubscheme f r) →+ FamilyOfCycles f r :=
  FreeAbelianGroup.lift fun Z => Z.cycleFamily f

/-- On a generator `[Z]` the homomorphism of Tag 0H6V is the family of cycles `[Z/X/S]_r`. -/
@[stacks 0H6V "on generators"]
theorem hilbertCycleClassMap_of {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (r : ℕ) (Z : HilbertSubscheme f r) :
    hilbertCycleClassMap f r (FreeAbelianGroup.of Z) = Z.cycleFamily f :=
  FreeAbelianGroup.lift_apply_of _ _

/-- The homomorphism of Tag 0H6V factors through `cycleClassMap` by forgetting the
quasi-separatedness of `Z ⟶ S`. -/
theorem hilbertCycleClassMap_eq_comp {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (r : ℕ) :
    hilbertCycleClassMap f r =
      (cycleClassMap f r).comp (FreeAbelianGroup.map HilbertSubscheme.toHilbertCycleDatum) := by
  ext Z
  simp [hilbertCycleClassMap_of, cycleClassMap_of]

/-- For `f` quasi-separated, `cycleClassMap` is the homomorphism of Tag 0H6V transported along
`HilbertSubscheme.equivHilbertCycleDatum`. -/
theorem cycleClassMap_eq_comp {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiSeparated f] (r : ℕ) :
    cycleClassMap f r = (hilbertCycleClassMap f r).comp
      (FreeAbelianGroup.map (HilbertSubscheme.equivHilbertCycleDatum f r).symm) := by
  ext Z
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, FreeAbelianGroup.map_of_apply,
    cycleClassMap_of, hilbertCycleClassMap_of]
  rfl

/-- For `f` quasi-separated, `cycleClassMap` and the homomorphism of Tag 0H6V have the same
image. -/
theorem range_cycleClassMap {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    [QuasiSeparated f] (r : ℕ) :
    (cycleClassMap f r).range = (hilbertCycleClassMap f r).range := by
  refine le_antisymm ?_ ?_
  · rw [cycleClassMap_eq_comp]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rw [hilbertCycleClassMap_eq_comp]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩

end Stacks.Chow

end
