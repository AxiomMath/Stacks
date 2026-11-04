module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LeftDualBoundedAboveOnASite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Restriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.DirectSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.BoundedAbovePreservation
public import StacksFrontier.Algebra.Homology.StupidTruncation

/-!
# The finite Tor amplitude of Stacks 0FPV, on a ringed site

Let `(C, O)` be a ringed site, let `N` be a left dual of `M` in the monoidal category `D(O)` of
Stacks 0FPT, and suppose `M` is concentrated in degrees `≤ b`. Then every object `V` of `C`
admits a covering family along each member `W` of which `M|_W` has **Tor amplitude in `[c, b]`**
for some `c`.

This is the source's third truncation, the one that reads *"Thus we find that we may assume `M`
is a direct summand in `D(O)` of a bounded complex of flat modules. In particular, we find `M`
has finite tor amplitude."* Being bounded above, `M` is represented by a complex `M^•` of flat
modules with `M^i = 0` for `i > b` (Stacks 05T7 applied to the flat covers of Stacks 03EW, which
is `Stacks.Cohomology.DerivedPullbackOnRingedTopoi.exists_flatRepresentative_of_isLE`); the
sections `fᵢ` occurring in `η(1) = ∑ᵢ fᵢ ⊗ gᵢ` sit in finitely many degrees, all `≥ c` for `c`
small enough, so they all lift through the **brutal truncation** `σ^{≥c}M^•`, and `M|_W` is a
retract of that truncation by
`AlgebraicGeometry.RingedSite.exists_presieve_localRetract`. The truncation is a bounded complex
of flat modules, so its restriction to the slice has Tor amplitude in `[c, b]` by Stacks 08G1,
and Tor amplitude passes to a retract.

Nothing below is a clause of a tag; this is a step of a proof, so no `@[stacks …]` attribute is
attached.

## Main results

* `AlgebraicGeometry.RingedSite.exists_presieve_hasTorAmplitude_of_exactPairing`: the statement
  above, with the interval `[c, b]` exhibited.
* `AlgebraicGeometry.RingedSite.locallyHasFiniteTorDimension_of_exactPairing_of_isLE`: the same
  conclusion in the shape Stacks 08G8 consumes — such an `M` *locally has finite Tor dimension*.

## Implementation notes

**Why the brutal truncation and not the canonical one.**
`AlgebraicGeometry.RingedSite.exists_presieve_isLE`, the first truncation, cuts `M^•` *above* with
`τ_{≤ b}`, whose top term is a module of cocycles and so carries no flatness. Here the cut is
*below*, and the brutal truncation `HomologicalComplex.stupidTrunc` is used precisely because it
keeps the terms of `M^•` unchanged — `σ^{≥c}M^•` has the terms `M^i` for `i ≥ c` and zero below, so
flatness of the terms survives it, which is what Stacks 08G1 needs. It is also what makes the
inclusion `σ^{≥c}M^• ⟶ M^•` a degreewise monomorphism and an isomorphism in every degree `≥ c`, the
two properties the retract step consumes: the mono hypothesis of
`Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f_general` and the lifting of the
prescribed sections.

**Why the hypothesis `M.IsLE b` is not removed here.** The bounded above flat representative
exists only for a bounded above object, and the first truncation delivers that bound only *after
restricting to a slice*. Composing the two steps is therefore a statement about the slice
`(C/W, O|_W)` — which is again a `RingedSite.{u, u, u}` — and not a strengthening of this
statement; it is the same reduction Stacks 08G8 performs on Stacks 08G7 in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/PerfectnessCriterion.lean`, and it is
carried out there and not here.

**The derived tensor product is a parameter.** Tor amplitude on the slice over `W` is measured
against a derived tensor product datum *on that slice*, and no datum on `C` measures anything on
`C/W`; this is the same reason
`Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension` takes a family `T`.
Nothing below compares two data: the Tor amplitude of the truncation is read off its own flat
representative on the slice, by the direction of Stacks 08G1 which needs no input.

## References

* [Stacks Project, Tag 0FPV](https://stacks.math.columbia.edu/tag/0FPV)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)

## Provenance
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open ComplexShape (embeddingUpIntGE)

universe u

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.SheafOfModules.DerivedTensorProduct
open Stacks.DerivedTensor.ExtensionByZero (restriction)

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory
attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ W : X.C, HasSheafify (X.J.over W) AddCommGrpCat.{u}]
  [∀ W : X.C, (X.J.over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K L : Stacks.SheafOfModules.DerivedMonoidal.Complexes X.O),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [hTorTensor : ∀ W : X.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over W).O).Additive]
  [hTorTensorObj : ∀ (W : X.C) (A : RingedSite.Modules.{u, u, u} (X.over W)),
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over W).O).obj A).Additive]
  [hTorBifunctor : ∀ (W : X.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (X.over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over W).O) (ComplexShape.up ℤ)]

/-- The tensor bifunctor of a slice is additive, at the spelling Stacks 08G1 needs. -/
local instance torTensorAdditive' (W : X.C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over W).O).Additive :=
  hTorTensor W

/-- The tensor bifunctor of a slice is additive in its second variable. -/
local instance torTensorObjAdditive' (W : X.C) (A : RingedSite.Modules.{u, u, u} (X.over W)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over W).O).obj A).Additive :=
  hTorTensorObj W A

/-- Total complexes of the tensor bifunctor of a slice exist. -/
local instance torHasMapBifunctor' (W : X.C)
    (K L : CochainComplex (RingedSite.Modules.{u, u, u} (X.over W)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over W).O) (ComplexShape.up ℤ) :=
  hTorBifunctor W K L

/-- **The finite Tor amplitude of the proof of Stacks 0FPV, on a ringed site.** If `M` has a left
dual in `D(O)` and is concentrated in degrees `≤ b`, then every object `V` of `C` admits a
covering family over each member `W` of which `M|_W` has Tor amplitude in `[c, b]` for some `c`:
it is a retract of the brutal truncation `σ^{≥c}M^•|_W` of a flat representative of `M`
concentrated in degrees `≤ b`, and that truncation is a bounded complex of flat modules.

The upper end of the interval is the given bound `b`; the lower end is determined by the degrees
of the finitely many sections of the terms of `M^•` through which the coevaluation factors over
`W`, so it depends on `W` and is exhibited existentially. -/
theorem exists_presieve_hasTorAmplitude_of_exactPairing (V : X.C)
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (pair : letI := derivedMonoidal X.O; ExactPairing M N) (b : ℤ) (hb : M.IsLE b)
    (T : ∀ W : X.C, Stacks.SheafOfModules.DerivedTensorProduct (X.over W)) :
    ∃ S : Presieve V, Sieve.generate S ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (h : W ⟶ V), S h →
        ∃ c : ℤ, HasTorAmplitude (T W)
          ((restriction X W).mapDerivedCategory.obj M) c b := by
  classical
  let := derivedMonoidal X.O
  let := pair
  obtain ⟨Mc, hMflat, hMLE, ⟨eM⟩⟩ :=
    Stacks.Cohomology.DerivedPullbackOnRingedTopoi.exists_flatRepresentative_of_isLE X M b hb
  have hMk : Stacks.SheafOfModules.DerivedMonoidal.KFlat X.O Mc :=
    Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O Mc ⟨b, hMLE⟩ hMflat
  obtain ⟨Nc, pN, hNk, hNflat, hpN, -⟩ :=
    Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution X.O
      (DerivedCategory.Q.objPreimage N)
  have hN' : IsIso (DerivedCategory.Q.map pN) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := Stacks.SheafOfModules.DerivedMonoidal.Mod X.O) pN).2 hpN
  obtain ⟨S, hS, hdata⟩ := exists_presieve_localRetract X V M N pair Mc Nc eM
    (asIso (DerivedCategory.Q.map pN) ≪≫ DerivedCategory.Q.objObjPreimageIso N) hMk hNk
  refine ⟨S, hS, fun {W} h hh => ?_⟩
  obtain ⟨κ, hκ, deg, a, hR⟩ := hdata h hh
  obtain ⟨c, hc⟩ : ∃ c : ℤ, ∀ i, c ≤ deg i :=
    ⟨-(∑ i : κ, |deg i|), fun i => neg_le.1 ((neg_le_abs _).trans
      (Finset.single_le_sum (f := fun i : κ => |deg i|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ i)))⟩
  refine ⟨c, ?_⟩
  -- the truncation vanishes below `c` and its inclusion is an isomorphism from `c` on
  have hz : ∀ i, i < c → IsZero ((Mc.stupidTrunc (embeddingUpIntGE c)).X i) := fun i hi =>
    Mc.isZero_stupidTrunc_X (embeddingUpIntGE c) i
      (by rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]; omega)
  have hiso : ∀ p, c ≤ p → IsIso ((Mc.ιStupidTrunc (embeddingUpIntGE c)).f p) := fun p hp =>
    Mc.isIso_ιStupidTrunc_f (embeddingUpIntGE c)
      (i := (p - c).toNat) (by change c + ((p - c).toNat : ℤ) = p; omega)
  -- the inclusion of the brutal truncation is a degreewise monomorphism
  let : ∀ p, Mono ((Mc.ιStupidTrunc (embeddingUpIntGE c)).f p) := fun p => by
    by_cases hp : c ≤ p
    · have := hiso p hp
      infer_instance
    · exact (hz p (not_le.1 hp)).mono _
  have hmono : Mono ((Mc.ιStupidTrunc (embeddingUpIntGE c) ▷ Nc).f 1) :=
    Stacks.Cohomology.LeftDualPerfect.mono_mapBifunctorMap_f_general
      (Mc.ιStupidTrunc (embeddingUpIntGE c)) hNflat 1
  obtain ⟨r⟩ := hR (Mc.stupidTrunc (embeddingUpIntGE c))
    (Mc.ιStupidTrunc (embeddingUpIntGE c)) hmono fun i =>
    ⟨(@inv _ _ _ _ ((Mc.ιStupidTrunc (embeddingUpIntGE c)).f (deg i))
        (hiso _ (hc i))).val.app (op W) (a i),
      congrArg (fun ψ => ψ.val.app (op W) (a i)) (@IsIso.inv_hom_id _ _ _ _ _ (hiso _ (hc i)))⟩
  -- the truncation is a complex of flat modules concentrated in `[c, b]`
  have hflatT : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((Mc.stupidTrunc (embeddingUpIntGE c)).X i) := by
    intro i
    by_cases hi : c ≤ i
    · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso X.O
        (StacksDraft.StupidTruncation.stupidTruncGEXIso Mc c i hi).symm (hMflat i)
    · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero X.O (hz i (not_le.1 hi))
  have hzeroT : ∀ i : ℤ, i ∉ Set.Icc c b →
      IsZero ((Mc.stupidTrunc (embeddingUpIntGE c)).X i) := by
    intro i hi
    by_cases hic : c ≤ i
    · exact (Mc.isZero_of_isStrictlyLE b i (not_le.1 fun hib => hi ⟨hic, hib⟩)).of_iso
        (StacksDraft.StupidTruncation.stupidTruncGEXIso Mc c i hic)
    · exact hz i (not_le.1 hic)
  have hamp : HasTorAmplitude (T W)
      ((restriction X W).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (Mc.stupidTrunc (embeddingUpIntGE c)))) c b :=
    hasTorAmplitude_of_flatRepresentative (T W) _ c b
      (X.restrictComplex (Mc.stupidTrunc (embeddingUpIntGE c)) W)
      (fun i => Stacks.SheafOfModules.FlatRestriction.isFlat_over X W _ (hflatT i))
      (fun i hi => (restriction X W).map_isZero (hzeroT i hi))
      (((restriction X W).mapDerivedCategoryFactors.app
        (Mc.stupidTrunc (embeddingUpIntGE c))).symm)
  exact hasTorAmplitude_of_retract (T W) r.i r.r r.retract c b hamp

/-- **An object of `D(O)` with a left dual which is bounded above locally has finite Tor
dimension**, Stacks 08FZ (3), which is the form the perfectness criterion of Stacks 08G8 consumes.
Every object of `C` carries the covering family of
`AlgebraicGeometry.RingedSite.exists_presieve_hasTorAmplitude_of_exactPairing`, and the interval it
exhibits over each member is nonempty on the right by construction. -/
theorem locallyHasFiniteTorDimension_of_exactPairing_of_isLE
    (M N : Stacks.SheafOfModules.DerivedMonoidal.DerivedModules X.O)
    (pair : letI := derivedMonoidal X.O; ExactPairing M N) (b : ℤ) (hb : M.IsLE b)
    (T : ∀ W : X.C, Stacks.SheafOfModules.DerivedTensorProduct (X.over W)) :
    LocallyHasFiniteTorDimension T M := by
  intro U
  obtain ⟨S, hS, hdata⟩ := exists_presieve_hasTorAmplitude_of_exactPairing X U M N pair b hb T
  refine ⟨S, hS, fun {W} h hh => ?_⟩
  obtain ⟨c, hc⟩ := hdata h hh
  exact ⟨c, b, hc⟩

end AlgebraicGeometry.RingedSite

end
