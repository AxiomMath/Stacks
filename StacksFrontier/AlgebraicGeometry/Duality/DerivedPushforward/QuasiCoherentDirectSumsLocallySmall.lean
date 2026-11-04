module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSums
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundRestrict
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QcqsRightAdjoint
import StacksCore.Tactic.StacksAttribute

/-!
# `Rf_*` commutes with arbitrary direct sums on `D_QCoh`, at the locally small model

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. The derived direct
image `Rf_* : D_QCoh(𝒪_X) ⟶ D_QCoh(𝒪_S)` commutes with direct sums indexed by an arbitrary type
of the scheme universe. This is [Stacks, Tag 08DZ], and
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean` proves it
at `CategoryTheory.HasDerivedCategory.standard`. This file proves it at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

The model matters, and not for bookkeeping: [Stacks, Tag 0A8G] asks for direct sums indexed by
the *morphism universe* of the category, and only at the locally small model is that universe the
`u` indexing the direct sums of `𝒪_X`-modules. At `standard` the morphisms live in
`Type (u + 1)` and the hypothesis `HasCoproducts.{u + 1}` is false rather than unavailable, so
the standard-model form of Tag 08DZ cannot discharge the hypothesis of
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward`, which is
[Stacks, Tag 0A9E]. The locally small form below does.

The single thing that pinned the argument to `standard` was [Stacks, Tag 08D5] part (2) in the
form used over a quasi-compact open of the target. That is now
`Stacks.Duality.exists_isLE_derivedPushforwardPullback_obj_locallySmall`, and everything else the
argument uses is already stated at a free `HasDerivedCategory` binder: the dévissage of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/BoundedDirectSums.lean`, the
cohomological-bound lemmas for direct sums of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/HomologyDirectSums.lean`, the
triangle-cutting lemmas of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/QuasiCoherentDirectSums.lean` itself,
and the direct sums in `D_QCoh` of
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/DirectSums.lean`, which are already at
the locally small model.

## Main results

Names are relative to the namespace `Stacks.Duality.DerivedPushforward`.

* `LocallySmall.isIso_sigmaComparison_of_isQuasicoherent`: the comparison
  `⨁ᵢ Rf_*(Eᵢ) ⟶ Rf_*(⨁ᵢ Eᵢ)` is invertible for a family of objects of `D(𝒪_X)` with
  quasi-coherent cohomology.
* `LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward`:
  **[Stacks, Tag 08DZ]** at the locally small model, with the quasi-coherence of the cohomology
  of `Rf_*E` as a hypothesis.
* `LocallySmall.preservesColimitsOfShape_discrete_qcqsRestrictedDerivedPushforward`: the same
  for the canonical restricted functor of `qcqsRestrictedDerivedPushforward`, the hypothesis
  discharged by [Stacks, Tag 08D5] part (1).
* `isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isCompactlyGenerated` and
  `exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward_of_isCompactlyGenerated`:
  the argument of [Stacks, Tag 0A9E] with compact generation of `D_QCoh(𝒪_X)` as its only
  hypothesis; the tag itself is `isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`.

## Implementation notes

The argument is the one of the standard-model file, transcribed with the model changed; see the
module documentation there for the mathematics. Three statements of that file are not usable here
because they are stated with the model resolved at definition time rather than as a binder —
`derivedPullbackOpen`, `preservesColimitsOfShape_discrete_derivedPullbackOpen` and
`isGE_derivedPullbackOpen_obj` — so they are restated below with
`(Scheme.Modules.pullback j).mapDerivedCategory` written out. The triangle-cutting lemmas of the
same file *are* usable, being stated for an arbitrary abelian category with an arbitrary
`HasDerivedCategory` instance.

**No `attribute [local instance] HasDerivedCategory.standard`.** The standard model is never a
global instance, so every `DerivedCategory Z.Modules` below resolves to the locally small
instance, uniquely.

**Compact generation.** The two statements below take compact generation of `D_QCoh(𝒪_X)`,
`CategoryTheory.Pretriangulated.IsCompactlyGenerated`, as a hypothesis: it is proved for every
quasi-compact quasi-separated scheme in
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/QcqsCompactGeneration.lean`, which
imports this file, and [Stacks, Tag 0A9E] with no hypothesis is stated there.

## References

* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DT](https://stacks.math.columbia.edu/tag/08DT)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 09IS](https://stacks.math.columbia.edu/tag/09IS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Opposite TopologicalSpace

universe u

namespace Stacks.Duality.DerivedPushforward.LocallySmall

attribute [local instance] AlgebraicGeometry.pullback_preservesFiniteLimits_of_isOpenImmersion

/-- The comparison morphism of a composite is invertible when those of both factors are. -/
private theorem isIso_sigmaComparison_comp_of_isIso {C D E : Type*} [Category* C] [Category* D]
    [Category* E] {J : Type*} (R : C ⥤ D) (S : D ⥤ E) (X : J → C) [HasCoproduct X]
    [HasCoproduct fun j ↦ R.obj (X j)] [HasCoproduct fun j ↦ S.obj (R.obj (X j))]
    [IsIso (sigmaComparison R X)] [IsIso (sigmaComparison S fun j ↦ R.obj (X j))] :
    IsIso (sigmaComparison (R ⋙ S) X) := by
  rw [sigmaComparison_comp]
  infer_instance

/-! ### Pullback to an open of the target -/

section Pullback

variable {S V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]

/-- Pullback along an open immersion of the target preserves direct sums, at the locally small
model: pullback does, being a left adjoint, hence so does its action on cochain complexes, and the
localization functor is essentially surjective and preserves direct sums. -/
theorem preservesColimitsOfShape_discrete_derivedPullbackOpen (α : Type u) :
    PreservesColimitsOfShape (Discrete α) ((Scheme.Modules.pullback j).mapDerivedCategory) := by
  have h₁ : PreservesColimitsOfShape (Discrete α)
      ((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ)) := inferInstance
  have h₂ : PreservesColimitsOfShape (Discrete α) (DerivedCategory.Q (C := V.Modules)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts V.Modules α
  have h₃ : PreservesColimitsOfShape (Discrete α)
      ((Scheme.Modules.pullback j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) := comp_preservesColimitsOfShape _ _
  have h₄ : PreservesColimitsOfShape (Discrete α)
      (DerivedCategory.Q ⋙ (Scheme.Modules.pullback j).mapDerivedCategory) :=
    (preservesColimitsOfShape_iff_of_natIso
      (Scheme.Modules.pullback j).mapDerivedCategoryFactors).2 h₃
  have h₅ : PreservesColimitsOfShape (Discrete α) (DerivedCategory.Q (C := S.Modules)) :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts S.Modules α
  exact preservesColimitsOfShape_discrete_of_essSurj_comp
    DerivedCategory.Q (Scheme.Modules.pullback j).mapDerivedCategory α

/-- Pullback along an open immersion of the target preserves lower cohomological bounds, at the
locally small model: it is exact, so it commutes with the cohomology functors. -/
theorem isGE_derivedPullbackOpen_obj (E : DerivedCategory S.Modules) (n : ℤ) (hE : E.IsGE n) :
    (((Scheme.Modules.pullback j).mapDerivedCategory).obj E).IsGE n := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have := hE
  exact ((Scheme.Modules.pullback j).map_isZero (E.isZero_of_isGE n i hi)).of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.pullback j) i).app E)

/-- The comparison morphism of pullback along an open immersion is invertible, at the locally
small model. -/
private theorem isIso_sigmaComparison_pullbackOpen {α : Type u}
    (F : α → DerivedCategory S.Modules) :
    IsIso (sigmaComparison ((Scheme.Modules.pullback j).mapDerivedCategory) F) :=
  isIso_sigmaComparison_of_preservesColimit _ _
    (preservesColimitsOfShape_discrete_derivedPullbackOpen j α).preservesColimit

end Pullback

/-! ### The derived direct image followed by pullback to an open of the target -/

section Local

variable {X S : Scheme.{u}} (f : X ⟶ S) {V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]

/-- The derived direct image along `f`, followed by pullback to an open `V ⊆ S`, at the locally
small model. -/
abbrev derivedPushforwardRestrict : DerivedCategory X.Modules ⥤ DerivedCategory V.Modules :=
  Stacks.Duality.derivedPushforward f ⋙ (Scheme.Modules.pullback j).mapDerivedCategory

/-- `Rf_*` followed by pullback to an open of the target preserves lower cohomological bounds:
`Rf_*` moves cohomology to the right and pullback along an open immersion is exact. -/
theorem isGE_derivedPushforwardRestrict_obj (E : DerivedCategory X.Modules) (n : ℤ)
    (hE : E.IsGE n) : ((derivedPushforwardRestrict f j).obj E).IsGE n := by
  have := hE
  exact isGE_derivedPullbackOpen_obj j _ n
    (Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward f) E n)

end Local

/-! ### Quasi-coherence of a direct sum -/

/-- The cohomology sheaves of a direct sum of objects with quasi-coherent cohomology are
quasi-coherent: cohomology commutes with direct sums, and quasi-coherent modules are closed
under them. -/
theorem isQuasicoherent_homology_sigmaObj {X : Scheme.{u}} {α : Type u}
    (E : α → DerivedCategory X.Modules)
    (hqc : ∀ k (i : ℤ), ((DerivedCategory.homologyFunctor X.Modules i).obj (E k)).IsQuasicoherent)
    (i : ℤ) : ((DerivedCategory.homologyFunctor X.Modules i).obj (∐ E)).IsQuasicoherent := by
  have hpres : PreservesColimit (Discrete.functor E)
      (DerivedCategory.homologyFunctor X.Modules i) :=
    (Stacks.Duality.preservesColimitsOfShape_derivedHomologyFunctor X.Modules i).preservesColimit
  refine (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (PreservesCoproduct.iso (DerivedCategory.homologyFunctor X.Modules i) E).symm ?_
  exact Stacks.Duality.DerivedPushforward.isQuasicoherent_sigmaObj X _ fun k ↦ hqc k i

/-! ### The two cuts, and the statement over an affine open of the target -/

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f]

section Open
variable {V : Scheme.{u}} (j : V ⟶ S) [IsOpenImmersion j]

/-- **The upper cut.** For a family lying in degrees `≥ a`, the direct-sum comparison morphism
of `Rf_*` followed by pullback to a quasi-compact open of the target is invertible in every
degree `q`: the triangle `τ_{≤ q}E ⟶ E ⟶ τ_{> q}E` has its third vertex carried into degrees
`≥ q + 1`, which `H^q` and `H^{q-1}` do not see, and its first vertex lies in the window
`[a, q]`, where the dévissage of
`Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isGE_isLE` applies. -/
theorem isIso_homologyMap_sigmaComparison_of_isGE {α : Type u}
    (Z : α → DerivedCategory X.Modules) (a : ℤ)
    (hge : ∀ k, (Z k).IsGE a) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor V.Modules q).map
      (sigmaComparison (derivedPushforwardRestrict f j) Z)) := by
  have hvan : ∀ (k : α) (m : ℤ), m < q + 1 →
      IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
        ((derivedPushforwardRestrict f j).obj
          ((DerivedCategory.TStructure.t.truncGT q).obj (Z k)))) := fun k m hm ↦
    DerivedCategory.isZero_of_isGE _ (q + 1) m hm
      (hX := isGE_derivedPushforwardRestrict_obj f j _ (q + 1) inferInstance)
  have hsum : ∀ m : ℤ, m < q + 1 → IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
      ((derivedPushforwardRestrict f j).obj
        (∐ fun k ↦ (DerivedCategory.TStructure.t.truncGT q).obj (Z k)))) := fun m hm ↦
    DerivedCategory.isZero_of_isGE _ (q + 1) m hm
      (hX := isGE_derivedPushforwardRestrict_obj f j _ (q + 1)
        (Stacks.Duality.isGE_sigmaObj X.Modules _ (q + 1) fun _ ↦ inferInstance))
  have hbase : IsIso ((DerivedCategory.homologyFunctor V.Modules q).map
      (sigmaComparison (derivedPushforwardRestrict f j)
        fun k ↦ (DerivedCategory.TStructure.t.truncLE q).obj (Z k))) := by
    have hb : IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f)
        (fun k ↦ (DerivedCategory.TStructure.t.truncLE q).obj (Z k))) := by
      refine Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isGE_isLE
        f a q _ (fun k ↦ ?_) (fun _ ↦ ?_)
      · have := hge k
        infer_instance
      · infer_instance
    have := hb
    have := isIso_sigmaComparison_pullbackOpen j
      (fun k ↦ (Stacks.Duality.derivedPushforward f).obj
        ((DerivedCategory.TStructure.t.truncLE q).obj (Z k)))
    have := isIso_sigmaComparison_comp_of_isIso (Stacks.Duality.derivedPushforward f)
      ((Scheme.Modules.pullback j).mapDerivedCategory)
      (fun k ↦ (DerivedCategory.TStructure.t.truncLE q).obj (Z k))
    infer_instance
  exact Stacks.Duality.DerivedPushforward.isIso_homologyMap_sigmaComparison_of_isIso_obj₁
    (derivedPushforwardRestrict f j)
    (fun k ↦ Triangle.mk
      ((DerivedCategory.TStructure.t.truncLEι q).app (Z k))
      ((DerivedCategory.TStructure.t.truncGTπ q).app (Z k))
      ((DerivedCategory.TStructure.t.truncGTδLE q).app (Z k)))
    (fun k ↦ DerivedCategory.TStructure.t.triangleLEGT_distinguished q (Z k)) q
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ q fun k ↦ hvan k q (by omega))
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ (q - 1)
      fun k ↦ hvan k (q - 1) (by omega))
    (hsum q (by omega)) (hsum (q - 1) (by omega)) hbase

variable [CompactSpace V]

/-- **The two cuts together.** For a family of objects of `D(𝒪_X)` with quasi-coherent
cohomology, the direct-sum comparison morphism of `Rf_*` followed by pullback to a quasi-compact
open of the target is invertible in every degree `q`. The triangle
`τ_{≤ q - N}E ⟶ E ⟶ τ_{> q - N}E`, with `N` the bound of [Stacks, Tag 08D5] part (2), has its
first vertex carried into degrees `≤ q - 1`, which `H^q` and `H^{q+1}` do not see, and its third
vertex lies in degrees `≥ q - N + 1`, where
`Stacks.Duality.DerivedPushforward.LocallySmall.isIso_homologyMap_sigmaComparison_of_isGE`
applies. -/
theorem isIso_homologyMap_sigmaComparison_pullback {α : Type u}
    (E : α → DerivedCategory X.Modules)
    (hqc : ∀ (k : α) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj (E k)).IsQuasicoherent) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor V.Modules q).map
      (sigmaComparison (derivedPushforwardRestrict f j) E)) := by
  obtain ⟨N, hN⟩ := Stacks.Duality.exists_isLE_derivedPushforwardPullback_obj_locallySmall f j
  have hqcW : ∀ (k : α) (i : ℤ), ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE (q - N)).obj (E k))).IsQuasicoherent := fun k i ↦
    Stacks.Duality.isQuasicoherent_homology_truncLE (E k) (hqc k) (q - N) i
  have hvan : ∀ (k : α) (m : ℤ), q - 1 < m →
      IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
        ((derivedPushforwardRestrict f j).obj
          ((DerivedCategory.TStructure.t.truncLE (q - N)).obj (E k)))) := fun k m hm ↦
    DerivedCategory.isZero_of_isLE _ (q - N + N - 1) m (by omega)
      (hX := hN _ (q - N) (hqcW k) inferInstance)
  have hsum : ∀ m : ℤ, q - 1 < m → IsZero ((DerivedCategory.homologyFunctor V.Modules m).obj
      ((derivedPushforwardRestrict f j).obj
        (∐ fun k ↦ (DerivedCategory.TStructure.t.truncLE (q - N)).obj (E k)))) := fun m hm ↦
    DerivedCategory.isZero_of_isLE _ (q - N + N - 1) m (by omega)
      (hX := hN _ (q - N) (fun i ↦ isQuasicoherent_homology_sigmaObj _ hqcW i)
        (Stacks.Duality.isLE_sigmaObj X.Modules _ (q - N) fun _ ↦ inferInstance))
  exact Stacks.Duality.DerivedPushforward.isIso_homologyMap_sigmaComparison_of_isIso_obj₃
    (derivedPushforwardRestrict f j)
    (fun k ↦ Triangle.mk
      ((DerivedCategory.TStructure.t.truncLEι (q - N)).app (E k))
      ((DerivedCategory.TStructure.t.truncGTπ (q - N)).app (E k))
      ((DerivedCategory.TStructure.t.truncGTδLE (q - N)).app (E k)))
    (fun k ↦ DerivedCategory.TStructure.t.triangleLEGT_distinguished (q - N) (E k)) q
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ q fun k ↦ hvan k q (by omega))
    (Stacks.Duality.isZero_homologyFunctor_sigmaObj V.Modules _ (q + 1)
      fun k ↦ hvan k (q + 1) (by omega))
    (hsum q (by omega)) (hsum (q + 1) (by omega))
    (isIso_homologyMap_sigmaComparison_of_isGE f j
      (fun k ↦ (DerivedCategory.TStructure.t.truncGT (q - N)).obj (E k)) (q - N + 1)
      (fun _ ↦ inferInstance) q)

end Open

/-- **`Rf_*` commutes with arbitrary direct sums of objects with quasi-coherent cohomology**, at
the locally small model. Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of
schemes and let `E` be a family of objects of `D(𝒪_X)` with quasi-coherent cohomology sheaves,
indexed by a type of the scheme universe. Then the canonical morphism
`⨁ₖ Rf_*(Eₖ) ⟶ Rf_*(⨁ₖ Eₖ)` is an isomorphism.

Invertibility is tested on each cohomology sheaf and is local on `S`, so it is enough to check
it after restriction to each affine open `U ⊆ S`; restriction is isomorphic to pullback, pullback
commutes with the cohomology functors, and over an affine open the statement is
`Stacks.Duality.DerivedPushforward.LocallySmall.isIso_homologyMap_sigmaComparison_pullback`. -/
theorem isIso_sigmaComparison_of_isQuasicoherent {α : Type u}
    (E : α → DerivedCategory X.Modules)
    (hqc : ∀ (k : α) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj (E k)).IsQuasicoherent) :
    IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f) E) := by
  rw [DerivedCategory.isIso_iff]
  intro q
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_restrict _
    (fun U : S.affineOpens ↦ (U : S.Opens)) (IsOpenCover.mk (iSup_affineOpens_eq_top S))
    fun U ↦ ?_
  have hA : IsAffine (U : S.Opens).toScheme := U.2
  have hC : CompactSpace (U : S.Opens).toScheme :=
    Scheme.compactSpace_of_isAffine (U : S.Opens).toScheme
  have hloc := isIso_homologyMap_sigmaComparison_pullback f (U : S.Opens).ι E hqc q
  have := isIso_sigmaComparison_pullbackOpen (U : S.Opens).ι
    (fun k ↦ (Stacks.Duality.derivedPushforward f).obj (E k))
  have hstep : IsIso ((DerivedCategory.homologyFunctor (U : S.Opens).toScheme.Modules q).map
      ((Scheme.Modules.pullback (U : S.Opens).ι).mapDerivedCategory.map
        (sigmaComparison (Stacks.Duality.derivedPushforward f) E))) := by
    rw [sigmaComparison_comp, Functor.map_comp] at hloc
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor (U : S.Opens).toScheme.Modules q).map
        (sigmaComparison ((Scheme.Modules.pullback (U : S.Opens).ι).mapDerivedCategory)
          (fun k ↦ (Stacks.Duality.derivedPushforward f).obj (E k)))) _
  have hpb := (NatIso.isIso_map_iff
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (Scheme.Modules.pullback (U : S.Opens).ι) q)
    (sigmaComparison (Stacks.Duality.derivedPushforward f) E)).1 hstep
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictFunctorIsoPullback (U : S.Opens).ι) _).2 hpb

/-! ### [Stacks, Tag 08DZ] at the locally small model -/

/-- **`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_S)` commutes with direct sums** at the locally small model,
with the quasi-coherence of the cohomology sheaves of `Rf_*E` taken as a hypothesis.

The inclusion of `D_QCoh` preserves direct sums, because the quasi-coherent objects are closed
under them ([Stacks, Tag 08DT],
`Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts`), and reflects
isomorphisms, being fully faithful; and the restricted functor followed by the inclusion on the
target *is* the inclusion on the source followed by `Rf_*`, where
`Stacks.Duality.DerivedPushforward.LocallySmall.isIso_sigmaComparison_of_isQuasicoherent`
applies. -/
theorem preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward
    (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
      ((DerivedCategory.homologyFunctor S.Modules i).obj
        ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)
    (α : Type u) :
    PreservesColimitsOfShape (Discrete α)
      (Stacks.Duality.quasiCoherentDerivedPushforward f hpush) := by
  have hclX := Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts X α
  have hclS := Stacks.Duality.DerivedPushforward.derivedQuasicoherent_isClosedUnderCoproducts S α
  refine preservesColimitsOfShape_discrete_of_isIso_sigmaComparison _ fun Ê ↦ ?_
  have hiX : PreservesColimitsOfShape (Discrete α)
      (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf))) := inferInstance
  have hiS : PreservesColimitsOfShape (Discrete α)
      (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := S.Modules)
        (SheafOfModules.isQuasicoherent S.ringCatSheaf))) := inferInstance
  have hRf : IsIso (sigmaComparison (Stacks.Duality.derivedPushforward f)
      (fun k ↦ (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf))).obj (Ê k))) :=
    isIso_sigmaComparison_of_isQuasicoherent f _ fun k i ↦ (Ê k).2 i
  have hiXc : IsIso (sigmaComparison (ObjectProperty.ι
      (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf))) Ê) :=
    isIso_sigmaComparison_of_preservesColimit _ Ê hiX.preservesColimit
  have hcomp := isIso_sigmaComparison_comp_of_isIso (ObjectProperty.ι
    (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf))) (Stacks.Duality.derivedPushforward f) Ê
  have hiSc : IsIso (sigmaComparison (ObjectProperty.ι
      (DerivedCategoryB.derivedCategoryB (A := S.Modules)
        (SheafOfModules.isQuasicoherent S.ringCatSheaf)))
      (fun k ↦ (Stacks.Duality.quasiCoherentDerivedPushforward f hpush).obj (Ê k))) :=
    isIso_sigmaComparison_of_preservesColimit _ _ hiS.preservesColimit
  exact isIso_sigmaComparison_of_isIso_comp
    (Stacks.Duality.quasiCoherentDerivedPushforward f hpush)
    (ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := S.Modules)
      (SheafOfModules.isQuasicoherent S.ringCatSheaf))) Ê inferInstance hcomp hiSc

end Stacks.Duality.DerivedPushforward.LocallySmall

namespace Stacks.Duality.DerivedPushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f] [CompactSpace Y]

/-- **[Stacks, Tag 08DZ] at the locally small model, for the canonical restricted functor.** Let
`f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of schemes with `Y` quasi-compact.
Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with direct sums indexed by any type of the
scheme universe — which at this model is also the morphism universe of the category, so this is
the hypothesis [Stacks, Tag 0A8G] asks for.

`DerivedPushforward.preservesColimitsOfShape_discrete_qcqsQuasiCoherentDerivedPushforward` is
the same statement at `CategoryTheory.HasDerivedCategory.standard`, where `HasCoproducts` of the
morphism universe is false and the statement therefore cannot be fed to Brown representability. -/
@[stacks 08DZ "at the locally small model, which is the one Brown representability runs at"]
instance preservesColimitsOfShape_discrete_qcqsRestrictedDerivedPushforward (α : Type u) :
    PreservesColimitsOfShape (Discrete α) (qcqsRestrictedDerivedPushforward f) :=
  LocallySmall.preservesColimitsOfShape_discrete_quasiCoherentDerivedPushforward f _ α

/-- **The argument of [Stacks, Tag 0A9E] with compact generation as its only hypothesis.**
Let `f : X ⟶ Y` be
a quasi-compact and quasi-separated morphism of schemes with `Y` quasi-compact and suppose
`D_QCoh(𝒪_X)` is compactly generated. Then `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right
adjoint — the twisted inverse image `f^×`.

This is `Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward` with
its direct-sum hypothesis discharged by [Stacks, Tag 08DZ] at the locally small model. The tag,
for a morphism of quasi-compact quasi-separated schemes and with compact generation discharged,
is `Stacks.Duality.DerivedPushforward.isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_qcqs`. -/
theorem isLeftAdjoint_qcqsRestrictedDerivedPushforward_of_isCompactlyGenerated
    (hX : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X)) :
    (qcqsRestrictedDerivedPushforward f).IsLeftAdjoint :=
  isLeftAdjoint_qcqsRestrictedDerivedPushforward f hX

/-- **The argument of [Stacks, Tag 0A9E] with the adjoint exhibited as exact**, with compact
generation of `D_QCoh(𝒪_X)` as its only hypothesis.
This is the extra information Brown representability returns and that the
source records alongside existence. -/
theorem exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward_of_isCompactlyGenerated
    (hX : IsCompactlyGenerated.{u} (Stacks.Duality.quasiCoherentDerivedCategory X)) :
    ∃ (a : _) (adj : qcqsRestrictedDerivedPushforward f ⊣ a) (_ : a.CommShift ℤ),
      adj.IsTriangulated :=
  exists_isTriangulated_rightAdjoint_qcqsRestrictedDerivedPushforward f hX

end Stacks.Duality.DerivedPushforward

end
