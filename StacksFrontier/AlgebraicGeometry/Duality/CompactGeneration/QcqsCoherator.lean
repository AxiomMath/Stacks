module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.AffineQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.KoszulOrthogonality.AffineComparison
public import StacksFrontier.AlgebraicGeometry.InductionPrinciple.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.MayerVietorisTriangle
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardAnyModel
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.UnboundedMayerVietorisTriangle
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories
public import StacksCore.Tactic.StacksAttribute

/-!
# The coherator of a quasi-compact quasi-separated scheme

Let `X` be a quasi-compact and quasi-separated scheme. [Stacks, Tag 0CR0] asserts that the
inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint `DQ_X`, the coherator.

## Main definitions

* `Stacks.Duality.Coherator.quasiCoherentProp`: `D_QCoh(𝒪_X)` as a property of the objects of
  `D(𝒪_X)`.
* `Stacks.Duality.Coherator.coreflective`: the extension product `D_QCoh(𝒪_X) ⋆ D_QCoh(𝒪_X)ᗮ`.

## Main results

* `Stacks.Duality.Coherator.coreflective_eq_top_iff`: the inclusion has a right adjoint if and
  only if every object of `D(𝒪_X)` lies in `coreflective X`.
* `Stacks.Duality.Coherator.coreflective_derivedPushforward`: for an open immersion `j : T ⟶ X`
  such that `Rj_*` preserves quasi-coherence of cohomology and the coherator of `T` exists,
  `Rj_*L` lies in `coreflective X` for every `L` in `D(𝒪_T)`.
* `Stacks.Duality.Coherator.coreflective_eq_top`: every object of `D(𝒪_X)` is an extension of
  an object right orthogonal to `D_QCoh(𝒪_X)` by an object of `D_QCoh(𝒪_X)`.
* `Stacks.Duality.Coherator.isLeftAdjoint_quasiCoherentι`: the inclusion
  `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint.
* `Stacks.Duality.Coherator.exists_isTriangulated_rightAdjoint_quasiCoherentι`: the same with
  the coherator exhibited as an exact functor.

## Implementation notes

The derived categories are the locally small ones,
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`.

## References

* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0CQS](https://stacks.math.columbia.edu/tag/0CQS)
* [Stacks Project, Tag 0CQR](https://stacks.math.columbia.edu/tag/0CQR)
* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 08DR](https://stacks.math.columbia.edu/tag/08DR)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
  CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality.Coherator

/-! ### The decomposable objects -/

/-- `D_QCoh(𝒪_X)`, the complexes of `𝒪_X`-modules with quasi-coherent cohomology, as a property of
the objects of `D(𝒪_X)`. Its inclusion is `Stacks.Duality.Coherator.quasiCoherentι X`. -/
abbrev quasiCoherentProp (X : Scheme.{u}) : ObjectProperty (DerivedCategory X.Modules) :=
  DerivedCategoryB.derivedCategoryB (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)

/-- `D_QCoh(𝒪_X)` is a triangulated subcategory of `D(𝒪_X)`. -/
instance isTriangulated_quasiCoherentProp (X : Scheme.{u}) : (quasiCoherentProp X).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated (A := X.Modules) _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)

/-- The objects `K` of `D(𝒪_X)` sitting in a distinguished triangle `E' ⟶ K ⟶ Q ⟶ E'[1]` with
`E'` in `D_QCoh(𝒪_X)` and `Q` right orthogonal to `D_QCoh(𝒪_X)`. -/
abbrev coreflective (X : Scheme.{u}) : ObjectProperty (DerivedCategory X.Modules) :=
  (quasiCoherentProp X).extensionProduct (quasiCoherentProp X).rightOrthogonal

/-- **[Stacks, Tag 0CQR]**: the decomposable objects form a triangulated subcategory. -/
instance isTriangulated_coreflective (X : Scheme.{u}) : (coreflective X).IsTriangulated :=
  isTriangulated_extensionProduct_of_le_rightOrthogonal _ _ le_rfl

/-- **[Stacks, Tag 0CQS] for `D_QCoh(𝒪_X) ⊆ D(𝒪_X)`**: the inclusion has a right adjoint if and
only if every object of `D(𝒪_X)` is decomposable. -/
theorem coreflective_eq_top_iff (X : Scheme.{u}) :
    coreflective X = ⊤ ↔ (quasiCoherentι X).IsLeftAdjoint :=
  ((isLeftAdjoint_ι_iff_extensionProduct_rightOrthogonal_eq_top_and_isSaturated
    (quasiCoherentProp X)).1).symm

/-! ### Direct image along an open immersion -/

section OpenImmersion

variable {X T : Scheme.{u}} (j : T ⟶ X) [IsOpenImmersion j]

/-- Direct image along an open immersion carries the right orthogonal of `D_QCoh(𝒪_T)` into the
right orthogonal of `D_QCoh(𝒪_X)`. -/
theorem rightOrthogonal_derivedPushforward (Q : DerivedCategory T.Modules)
    (hQ : (quasiCoherentProp T).rightOrthogonal Q) :
    (quasiCoherentProp X).rightOrthogonal ((derivedPushforward j).obj Q) := by
  intro M g hM
  let adj := OpenImmersion.derivedRestrictPushforwardAdjunction j
  rw [← (adj.homEquiv M Q).apply_symm_apply g,
    hQ ((adj.homEquiv M Q).symm g) (OpenImmersion.derivedCategoryB_derivedRestrict j M hM),
    Adjunction.homEquiv_unit, Functor.map_zero, comp_zero]

/-- Let `j : T ⟶ X` be an open immersion such that `Rj_*` preserves quasi-coherence of cohomology
and `D_QCoh(𝒪_T) ⥤ D(𝒪_T)` has a right adjoint. Then `Rj_*L` is decomposable in `D(𝒪_X)` for
every `L` in `D(𝒪_T)`. -/
theorem coreflective_derivedPushforward
    (hpush : ∀ (L : quasiCoherentDerivedCategory T) (i : ℤ),
      ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((derivedPushforward j).obj L.obj)).IsQuasicoherent)
    (hT : (quasiCoherentι T).IsLeftAdjoint) (L : DerivedCategory T.Modules) :
    coreflective X ((derivedPushforward j).obj L) := by
  obtain ⟨E, Q, f, g, h, hTr, hE, hQ⟩ : coreflective T L := by
    rw [(coreflective_eq_top_iff T).2 hT]; trivial
  let adj := OpenImmersion.derivedRestrictPushforwardAdjunction j
  let : (derivedPushforward j).CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  let : (derivedPushforward j).IsTriangulated := adj.isTriangulated_rightAdjoint
  exact ⟨_, _, _, _, _, (derivedPushforward j).map_distinguished _ hTr,
    hpush ⟨E, hE⟩, rightOrthogonal_derivedPushforward j Q hQ⟩

end OpenImmersion

/-! ### The induction -/

section Induction

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]

/-- For an affine open `W` of a quasi-compact quasi-separated scheme `X` and every `K` in
`D(𝒪_X)`, the object `Rj_{W,*}(K|_W)` is decomposable. -/
theorem coreflective_restrictPushforward_of_isAffineOpen (W : X.Opens) (hW : IsAffineOpen W)
    (K : DerivedCategory X.Modules) :
    coreflective X ((restrictPushforwardFunctor W).obj K) := by
  have : IsAffine W.toScheme := hW
  exact coreflective_derivedPushforward W.ι
    (isQuasicoherent_homology_derivedPushforward_opens W)
    (Stacks.Duality.AffineGeneration.isLeftAdjoint_derivedQuasiCoherentι_of_isAffine W.toScheme)
    _

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- If `Rj_{W,*}(K|_W)` is decomposable for `W = U`, `V` and `U ∩ V`, then it is for
`W = U ∪ V`. -/
theorem coreflective_restrictPushforward_sup (U V : X.Opens) (K : DerivedCategory X.Modules)
    (hU : coreflective X ((restrictPushforwardFunctor U).obj K))
    (hV : coreflective X ((restrictPushforwardFunctor V).obj K))
    (hUV : coreflective X ((restrictPushforwardFunctor (U ⊓ V)).obj K)) :
    coreflective X ((restrictPushforwardFunctor (U ⊔ V)).obj K) := by
  obtain ⟨f, g, δ, hT⟩ := exists_distTriang_restrictPushforward_sup U V K
  have hmid : coreflective X
      ((restrictPushforwardFunctor U).obj K ⊞ (restrictPushforwardFunctor V).obj K) :=
    (coreflective X).ext_of_isTriangulatedClosed₂ _
      (binaryBiproductTriangle_distinguished _ _) hU hV
  exact (coreflective X).ext_of_isTriangulatedClosed₁ _ hT hmid hUV

/-- **Every object of `D(𝒪_X)` is decomposable** for a quasi-compact quasi-separated scheme `X`:
it fits in a distinguished triangle `E' ⟶ K ⟶ Q ⟶ E'[1]` with `E'` in `D_QCoh(𝒪_X)` and `Q` right
orthogonal to `D_QCoh(𝒪_X)`. -/
theorem coreflective_eq_top : coreflective X = ⊤ := by
  have key : ∀ K : DerivedCategory X.Modules,
      coreflective X ((restrictPushforwardFunctor (⊤ : X.Opens)).obj K) :=
    Stacks.AlgebraicGeometry.InductionPrinciple.induction_top
      (fun W : X.Opens => ∀ K : DerivedCategory X.Modules,
        coreflective X ((restrictPushforwardFunctor W).obj K))
      (fun W hW K => coreflective_restrictPushforward_of_isAffineOpen X W hW K)
      (fun U V _ _ hU hV hUV K => coreflective_restrictPushforward_sup X U V K (hU K) (hV K)
        (hUV K))
  exact eq_top_iff.2 fun K _ => (coreflective X).prop_of_iso (restrictPushforwardTopIso K) (key K)

/-- Let `X` be a quasi-compact and quasi-separated scheme. The inclusion functor
`D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a right adjoint `DQ_X`. -/
@[stacks 0CR0]
theorem isLeftAdjoint_quasiCoherentι : (quasiCoherentι X).IsLeftAdjoint :=
  (coreflective_eq_top_iff X).1 (coreflective_eq_top X)

/-- For a quasi-compact quasi-separated scheme `X` the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` has a
right adjoint `DQ_X` together with a `Functor.CommShift ℤ` structure making the adjunction
triangulated. -/
@[stacks 0CR0 "the coherator is exact"]
theorem exists_isTriangulated_rightAdjoint_quasiCoherentι :
    ∃ (DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
      (adj : quasiCoherentι X ⊣ DQ) (_ : DQ.CommShift ℤ), adj.IsTriangulated := by
  have := isLeftAdjoint_quasiCoherentι X
  let adj := Adjunction.ofIsLeftAdjoint (quasiCoherentι X)
  let : (quasiCoherentι X).rightAdjoint.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  exact ⟨_, adj, inferInstance, Adjunction.IsTriangulated.mk' adj⟩

end Induction

end Stacks.Duality.Coherator

end
