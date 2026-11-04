module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionDepth
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtensionUniqueness
import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.UnramifiedCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteTypeII.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.DifferentialsAndValuative.EtaleFlatUnramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.RingTheory.Depth.Dimension
public import Mathlib.RingTheory.KrullDimension.Module
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Purity of the branch locus: étaleness of the canonical extension

Let `j : U ⟶ X` be an open immersion into a locally Noetherian scheme whose complement consists
of points at which `𝒪_X` has depth at least two, and let `π : V ⟶ U` be finite étale. The
preceding files of this directory build the canonical extension `Y = Spec_X(𝓑)` for
`𝓑 = (π ≫ j)_* 𝒪_V` and prove, one at a time, the assertions that [Stacks, Tag 0EY6] makes
about it: that `𝓑` is coherent and reflexive, that `Y ⟶ X` is finite, that `V = Y ×_X U`, that
the local rings of `Y` off the cover have depth at least two, and that `Y ⟶ X` is the only
finite morphism with those last two properties.

This file proves the pointwise criterion that the tag states next: at a point of `Y` the
structure morphism is étale exactly when it is flat. One direction is formal, since étale is
flat plus G-unramified. The other is the substance. Flatness holds on an open `W` of `Y` (the
flat locus is open, [Stacks, Tag 05IM], the base having locally finite weakly associated points
because its structure sheaf is coherent); over the cover the morphism is étale already, because
there it *is* the cover; and at a point of `W` outside the cover the depth bound forces the
local ring to have Krull dimension at least two, so the point is neither a generic point of a
component nor one-dimensional, while every one-dimensional generization of it lies over the
cover and is therefore unramified. That is exactly the hypothesis list of [Stacks, Tag 0BJH],
which upgrades flat to étale at the point.

## Main results

* `etaleAt_iff_isFlatAt_extendedEtale` — at a point of the canonical extension, the structure
  morphism is étale if and only if it is flat.
* `etale_iff_isFiniteLocallyFree_extendedEtale` — the structure morphism is étale if and only if
  `𝓑` is finite locally free over `𝒪_X`.
* `exists_finite_schemeWeaklyAssociatedPoints_inter` — a locally Noetherian scheme has locally
  finitely many weakly associated points, the hypothesis under which the flat locus is open.

The clause asserting that `Y ⟶ X` is the *unique* finite morphism whose base change along `j` is
the given cover and whose local rings off the cover have depth at least two is proved in the
preceding files of this directory. Its covering set is four declarations, one per conjunct, each
carrying `@[stacks 0EY6 "unique_extension"]` in the file that proves it:

* `isFinite_extendedEtaleToBase` — `Y ⟶ X` is finite.
* `extendedEtaleCoverMap_isPullback` — `V = Y ×_X U`, as a cartesian square.
* `extendedEtale_depth_ge_two` — the local rings of `Y` off the cover have depth at least two.
* `extendedEtale_unique` — any other such finite morphism is uniquely isomorphic to this one.

## Implementation notes

A tag attribute here is written with a clause string, `@[stacks 0EY6 "etale_iff_flat"]` and the
like, which is this repository's record that a covering set covers one named clause of a
multi-clause tag rather than the whole tag. The clauses of `0EY6` are `algebra`,
`flat_base_change`, `unique_extension`, `larger_open`, `etale_iff_flat` and `etale_iff_free`;
`algebra` carries its own clause string at the end of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/ExtendedEtale/Algebra.lean`, and a clause with
no covering set in this library carries no attribute anywhere.

The earlier policy in this directory was to record coverage in prose and withhold the attribute.
That is superseded: a clause whose attribute is described in a docstring but never written is
recorded nowhere a reader or a scanner can find it, and the clause string is exactly the device
that makes writing it safe.

The `unique_extension` covering set is spread over four files, and the clause is a statement
about the four together. Its depth conjunct is stated with
`Stacks.RelativeSpec.relativeSpectrum` and the other three with
`Stacks.RelativeSpec.gluedSpectrum`; these are the two spellings of the same scheme, as
`isFinite_relativeSpectrum_extendedEtaleSituation` records.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 0BJH](https://stacks.math.columbia.edu/tag/0BJH)
* [Stacks Project, Tag 05IM](https://stacks.math.columbia.edu/tag/05IM)
* [Stacks Project, Tag 00LK](https://stacks.math.columbia.edu/tag/00LK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

/-! ### Depth is bounded by the Krull dimension -/

/-- The depth of a local ring along its maximal ideal is at most its Krull dimension. -/
private alias depth_le_ringKrullDim := Module.depth_le_ringKrullDim

/-! ### The base has locally finite weakly associated points -/

/-- **A locally Noetherian scheme has locally finitely many weakly associated points.** Every
point has an affine open neighbourhood, which is quasi-compact; on a locally Noetherian scheme
the weakly associated points of the structure sheaf are its associated points
([Stacks, Tag 05AR]), and a coherent module has finitely many associated points in a
quasi-compact open ([Stacks, Tag 05AF]).

This is the hypothesis under which the flat locus of a morphism locally of finite type is open,
[Stacks, Tag 05IM]. -/
@[ega "IV 3.1.6" "special case"]
public theorem exists_finite_schemeWeaklyAssociatedPoints_inter (X : Scheme.{u})
    [IsLocallyNoetherian X] (x : X) :
    ∃ W : X.Opens, x ∈ W ∧
      (Stacks.Divisors.schemeWeaklyAssociatedPoints X ∩ (W : Set X)).Finite := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  refine ⟨W, hxW, ?_⟩
  have hcoh : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
  show (Stacks.Divisors.weaklyAssociatedPoints
    (SheafOfModules.unit X.ringCatSheaf) ∩ (W : Set X)).Finite
  rw [← AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints X
    (SheafOfModules.unit X.ringCatSheaf)]
  exact AlgebraicGeometry.associatedPoints_inter_finite
    (SheafOfModules.unit X.ringCatSheaf) W hW.isCompact

/-! ### Étale at a point exactly when flat at that point -/

/-- **The `etale_iff_flat` clause of [Stacks, Tag 0EY6].** Let `j : U ⟶ X` be an open immersion
into a locally Noetherian scheme whose complement carries depth at least two and let
`π : V ⟶ U` be finite étale. At every point of the canonical extension `Y = Spec_X(𝓑)`, for
`𝓑 = (π ≫ j)_* 𝒪_V`, the structure morphism `Y ⟶ X` is étale if and only if it is flat.

Forwards this is one half of "étale is flat and G-unramified". Backwards, write `W` for the flat
locus of `Y ⟶ X`, an open subscheme by [Stacks, Tag 05IM] since the base has locally finite
weakly associated points, and let `y ∈ W`. If `y` lies over the open `j(U)` then `Y ⟶ X` is
étale at `y` outright, because over `j(U)` it is the finite étale cover `π`
(`extendedEtaleCoverMap_isPullback`). Otherwise the depth clause
(`extendedEtale_depth_ge_two`) gives `depth 𝒪_{Y, y} ≥ 2`, hence `dim 𝒪_{Y, y} ≥ 2`; so `y` is
not a generic point of a component of `W`, and any `z ⤳ y` with `dim 𝒪_{W, z} = 1` must lie over
`j(U)`, where `Y ⟶ X` is étale and so unramified. Those are the hypotheses of
[Stacks, Tag 0BJH], which turns flatness at `y` into étaleness at `y`. -/
@[stacks 0EY6 "etale_iff_flat"]
public theorem etaleAt_iff_isFlatAt_extendedEtale {U X V : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    let Y := gluedSpectrum (extendedEtaleSituation j π hdepth)
    ∀ y : Y.scheme,
      EtaleAt Y.toBase y ↔ IsFlatAt Y.toBase.toLRSHom.toShHom y := by
  intro Y y
  constructor
  · exact fun hEt =>
      ((AlgebraicGeometry.etaleAt_iff_isFlatAt_and_gUnramifiedAt Y.toBase y).mp hEt).1
  · intro hflat
    let f := Y.toBase
    have : IsFinite f := isFinite_relativeSpectrum_extendedEtaleSituation j π hdepth
    have : LocallyOfFiniteType f := inferInstance
    have : IsLocallyNoetherian (extendedEtaleSituation j π hdepth).base := by
      show IsLocallyNoetherian X
      infer_instance
    -- the flat locus, open because the base has locally finite weakly associated points
    let W : Y.scheme.Opens :=
      ⟨{z : Y.scheme | IsFlatAt f.toLRSHom.toShHom z},
        AlgebraicGeometry.isOpen_setOf_isFlatAt_of_locallyOfFiniteType_of_locally_finite_weakAss
          f (exists_finite_schemeWeaklyAssociatedPoints_inter X)⟩
    have hyW : y ∈ W := hflat
    have hdepthY : ∀ z : Y.scheme, f z ∉ (j.opensRange : Set X) →
        (2 : ℕ∞) ≤ Module.depth (Y.scheme.presheaf.stalk z)
          (IsLocalRing.maximalIdeal (Y.scheme.presheaf.stalk z))
          (Y.scheme.presheaf.stalk z) :=
      extendedEtale_depth_ge_two j π hdepth
    -- over the open subscheme the structure morphism is the cover, hence étale
    let g := extendedEtaleCoverMap j π hdepth
    have hpb := extendedEtaleCoverMap_isPullback j π hdepth
    have : IsOpenImmersion g := MorphismProperty.of_isPullback hpb inferInstance
    have hEtCover : ∀ z : Y.scheme, f z ∈ (j.opensRange : Set X) → EtaleAt f z := by
      intro z hz
      obtain ⟨v, hv⟩ := exists_preimage_of_mem_opensRange j f π g hpb z hz
      have hEt : EtaleAt (g ≫ f) v := by
        have hgf : g ≫ f = π ≫ j := extendedEtaleCoverMap_comp_toBase j π hdepth
        rw [hgf]
        exact (AlgebraicGeometry.etale_iff_forall_etaleAt (π ≫ j)).mp inferInstance v
      rw [← hv]
      exact etaleAt_of_etaleAt_isOpenImmersion_comp g f v hEt
    -- a point of `W` whose local ring has dimension below two lies over the open subscheme
    have hcoverOf (z : W.toScheme) (n : ℕ∞) (hn : n < 2)
        (hz : ringKrullDim (W.toScheme.presheaf.stalk z) = n) :
        f (W.ι z) ∈ (j.opensRange : Set X) := by
      by_contra hnot
      rw [ringKrullDim_eq_of_ringEquiv
        (asIso (W.ι.stalkMap z)).commRingCatIsoToRingEquiv.symm] at hz
      exact absurd (by exact_mod_cast ((WithBot.coe_le_coe.mpr (hdepthY _ hnot)).trans
        (depth_le_ringKrullDim _)).trans_eq hz) (not_le.2 hn)
    by_cases hycover : f y ∈ (j.opensRange : Set X)
    · exact hEtCover y hycover
    · let yW : W.toScheme := ⟨y, hyW⟩
      have : Flat (W.ι ≫ f) :=
        AlgebraicGeometry.flat_of_subset_setOf_isFlatAt f W fun z hz => hz
      have : LocallyOfFiniteType (W.ι ≫ f) := inferInstance
      have : IsLocallyNoetherian W.toScheme :=
        LocallyOfFiniteType.isLocallyNoetherian (W.ι ≫ f)
      have hquasi : AlgebraicGeometry.quasiFiniteAt (W.ι ≫ f) yW := by
        have : LocallyQuasiFinite (W.ι ≫ f) := inferInstance
        exact (AlgebraicGeometry.forall_quasiFiniteAt_iff (W.ι ≫ f)).2
          ⟨inferInstance, inferInstance⟩ yW
      have hEtW := AlgebraicGeometry.etaleAt_of_flat_of_unramifiedAt_codimensionOne
        (W.ι ≫ f) yW hquasi (fun hygen => hycover (hcoverOf yW 0 (by norm_num)
          (AlgebraicGeometry.ringKrullDim_stalk_eq_zero_of_mem_genericPoints
            W.toScheme yW hygen))) (by
          intro z _ hdimW
          exact unramifiedAt_isOpenImmersion_comp W.ι f z
            ((AlgebraicGeometry.etaleAt_iff_smoothAt_and_unramifiedAt f (W.ι z)).mp
              (hEtCover (W.ι z) (hcoverOf z 1 (by norm_num) hdimW))).2)
      simpa [f, yW] using etaleAt_of_etaleAt_isOpenImmersion_comp W.ι f yW hEtW

/-! ### Étale exactly when the extension algebra is finite locally free -/

/-- **The `etale_iff_free` clause of [Stacks, Tag 0EY6].** The structure morphism of the
canonical extension `Y = Spec_X(𝓑)` is étale if and only if `𝓑 = (π ≫ j)_* 𝒪_V` is finite
locally free as an `𝒪_X`-module.

The chain is: étale means étale at every point
(`AlgebraicGeometry.etale_iff_forall_etaleAt`); at every point étale is flat
(`etaleAt_iff_isFlatAt_extendedEtale`); flat at every point means flat
(`AlgebraicGeometry.Flat.iff_flat_stalkMap`); and for a morphism over a locally Noetherian base
finite plus flat is finite locally free ([Stacks, Tag 02KB]), which for an affine morphism is
finite local freeness of the direct image of its structure sheaf ([Stacks, Tag 02KA]). That
direct image is `𝓑` itself, because `Y` is the relative spectrum of `𝓑`
(`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`). -/
@[stacks 0EY6 "etale_iff_free"]
public theorem etale_iff_isFiniteLocallyFree_extendedEtale {U X V : Scheme.{u}}
    [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j]
    (π : V ⟶ U) [IsFinite π] [Etale π]
    (hdepth : ∀ x : X, x ∉ (j.opensRange : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) :
    let Y := gluedSpectrum (extendedEtaleSituation j π hdepth)
    Etale Y.toBase ↔
      _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) := by
  intro Y
  have : _root_.SheafOfModules.IsCoherent
      (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) :=
    extendedEtaleAlgebra_isCoherent j π hdepth
  have : (pushforwardAlgebra (π ≫ j)).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  have : IsLocallyNoetherian (extendedEtaleSituation j π hdepth).base :=
    inferInstanceAs (IsLocallyNoetherian X)
  have hfin : IsFinite Y.toBase :=
    isFinite_relativeSpectrum_extendedEtaleSituation j π hdepth
  have haff : IsAffineHom Y.toBase := isAffineHom_extendedEtaleToBase j π hdepth
  -- the direct image of the structure sheaf of the extension is the extension algebra itself
  have emod : AlgebraSheaf.underlyingModule (pushforwardAlgebra Y.toBase) ≅
      AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j)) :=
    (AlgebraSheaf.underlyingModuleFunctor X).mapIso
      (pushforwardAlgebraIso (pushforwardAlgebra (π ≫ j)))
  calc Etale Y.toBase
      ↔ ∀ y : Y.scheme, EtaleAt Y.toBase y :=
        AlgebraicGeometry.etale_iff_forall_etaleAt Y.toBase
    _ ↔ ∀ y : Y.scheme, IsFlatAt Y.toBase.toLRSHom.toShHom y :=
        forall_congr' (etaleAt_iff_isFlatAt_extendedEtale j π hdepth)
    _ ↔ Flat Y.toBase := (AlgebraicGeometry.Flat.iff_flat_stalkMap Y.toBase).symm
    _ ↔ _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          (AlgebraSheaf.underlyingModule (pushforwardAlgebra (π ≫ j))) := by
        refine ⟨fun hflat => ?_, fun hfree => ?_⟩
        · have hmor : Stacks.Morphisms.IsFiniteLocallyFree Y.toBase :=
            (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian
              Y.toBase).2 ⟨hfin, hflat⟩
          have hsrc : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
              (AlgebraSheaf.underlyingModule (pushforwardAlgebra Y.toBase)) :=
            hmor.toIsFiniteLocallyFree
          exact _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
            (h := hsrc) emod
        · have hsrc : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
              (AlgebraSheaf.underlyingModule (pushforwardAlgebra Y.toBase)) :=
            _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
              (h := hfree) emod.symm
          have hmor : Stacks.Morphisms.IsFiniteLocallyFree Y.toBase :=
            (Stacks.Morphisms.isFiniteLocallyFree_iff Y.toBase).2 ⟨haff, hsrc⟩
          exact ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_of_isLocallyNoetherian
            Y.toBase).1 hmor).2

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
