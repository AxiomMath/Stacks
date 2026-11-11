module

public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusGoesDown
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import Mathlib.CategoryTheory.MorphismProperty.Concrete
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0CE3] with no hypothesis beyond the tag's own

Let `k` be a field, let `g : X ⟶ Spec k` be proper with `dim X ≤ 1` and let `f : Y ⟶ X` be a
finite morphism which is a closed immersion over a dense open `U ⊆ X`. [Stacks, Tag 0CE3] asserts
`dim_k H¹(Y, 𝒪_Y) ≤ dim_k H¹(X, 𝒪_X)`, that is `genus (f ≫ g) ≤ genus g`.

`AlgebraicGeometry.genus_le_of_isAffineHom_of_isZero`
(`StacksFrontier/AlgebraicGeometry/Curves/GenusCurve/GenusGoesDown.lean`) proves the cohomological
argument of the source from three inputs carried as hypotheses: `H¹(X, coker φ) = 0`,
`H²(X, ker φ) = 0` and finite dimensionality of `H¹(X, 𝒪_X)`, for `φ : 𝒪_X ⟶ f_*𝒪_Y` the
canonical comparison map. This file discharges all three from the tag's own hypotheses, so the
inequality holds unconditionally.

Two of the three are immediate from the library:

* `H²(X, ker φ) = 0` is Grothendieck vanishing by dimension alone,
  `AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le` with `d = 1 < 2 = i`;
* `H¹(X, 𝒪_X)` is finite dimensional by
  `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isProper`, fed the coherence of the
  structure sheaf, `Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit`.

The third is the content of this file. By clause (3) of [Stacks, Tag 0AYT]
(`AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero`) it suffices
that the support of `coker φ` have dimension at most zero, and by
`AlgebraicGeometry.topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne` that holds
as soon as the support misses the generic points of the one-dimensional components of `X`. A
dense open of a Noetherian space contains every such generic point
(`Stacks.Topology.mem_of_dense_of_mem_genericPoints`), so what has to be proved is that
`coker φ` has vanishing stalk at every point of `U`, which is the local statement that `f` is a
closed immersion over `U`.

That last step is where the work is.
`AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_pushforwardUnitHom`
makes the stalk of `φ` at `f y` surjective from three inputs: `f` closed, the fibre of `f` over
`f y` confined to `y`, and **surjectivity** — not invertibility — of the local ring map
`f.stalkMap y`. The hypothesis of the tag is `IsClosedImmersion (pullback.snd f U.ι)`, which is
`IsClosedImmersion (f ∣_ U)` up to the canonical identification of the base change of `f` along
an open immersion with the restriction of `f`
(`AlgebraicGeometry.pullbackRestrictIsoRestrict`), and `AlgebraicGeometry.IsClosedImmersion`
carries exactly the surjectivity of the stalk maps of `f ∣_ U` and the injectivity of its
underlying map. Transporting those two across
`AlgebraicGeometry.morphismRestrictStalkMap` and `AlgebraicGeometry.morphismRestrict_base_coe`
produces the first two inputs for a point of `Y` above `U`, which is
`AlgebraicGeometry.surjective_stalkMap_of_mem_of_morphismRestrict` and
`AlgebraicGeometry.preimage_singleton_subset_of_isClosedImmersion_morphismRestrict` below.

A point of `U` need not be in the image of `f`, and then there is no point of `Y` to run that
argument at; the cokernel's stalk vanishes there for a different reason, namely that the stalk of
`f_*𝒪_Y` itself vanishes off the (closed) image of `f`. That is
`AlgebraicGeometry.notMem_supp_cokernel_pushforwardUnitHom_of_notMem_range`, from
`Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport.supp_pushforward_subset`.

## Main results

* `Stacks.Topology.mem_of_dense_of_mem_genericPoints`: a dense open of a Noetherian space
  contains every generic point of an irreducible component.
* `AlgebraicGeometry.surjective_stalkMap_of_mem_of_morphismRestrict` and
  `AlgebraicGeometry.preimage_singleton_subset_of_isClosedImmersion_morphismRestrict`: a morphism
  restricting to a closed immersion over an open has surjective stalk maps, and one-point fibres,
  at the points above that open.
* `AlgebraicGeometry.notMem_supp_cokernel_pushforwardUnitHom_of_notMem_range`: off the image of a
  closed morphism `f` the cokernel of `𝒪_X ⟶ f_*𝒪_Y` has vanishing stalk.
* `AlgebraicGeometry.notMem_supp_cokernel_pushforwardUnitHom_of_mem`: **the cokernel of
  `𝒪_X ⟶ f_*𝒪_Y` has vanishing stalk at every point of an open over which `f` is a closed
  immersion.**
* `AlgebraicGeometry.genus_le_of_isFinite_of_isClosedImmersion_over_dense_open`:
  **[Stacks, Tag 0CE3]**, `genus (f ≫ g) ≤ genus g`, with no hypothesis beyond the tag's own.

## Implementation notes

The hypothesis is stated as `IsClosedImmersion (pullback.snd f U.ι)`, the base change of `f`
along the open immersion `U.ι`, which is the source's "closed immersion over `U`".
`AlgebraicGeometry.morphismRestrict` is that base change composed with an isomorphism, so the
two readings are interchanged by multiplicativity of `AlgebraicGeometry.IsClosedImmersion`; the
proof works with `f ∣_ U`, for which Mathlib has the comparison of stalk maps.

Surjectivity of a stalk map is transported along `AlgebraicGeometry.morphismRestrictStalkMap` by
`CategoryTheory.MorphismProperty.arrow_mk_iso_iff` at
`CategoryTheory.MorphismProperty.surjective CommRingCat`, which is the shape in which Mathlib
itself proves that `AlgebraicGeometry.SurjectiveOnStalks` is local at the target.

## References

* [Stacks Project, Tag 0CE3](https://stacks.math.columbia.edu/tag/0CE3)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ComponentDegrees
open Stacks.AlgebraicGeometry.CurveEulerBridge
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent
open Stacks.AlgebraicGeometry.FiniteSurjectiveCoherentSupport

universe u

namespace Stacks.Topology

/-- **A dense open of a Noetherian space contains every generic point of an irreducible
component.** An irreducible component of a Noetherian space has a nonempty open subset, which the
dense open meets, and a generic point lies in every open meeting its component. -/
@[ega "0 2.1.4" "special case"]
theorem mem_of_dense_of_mem_genericPoints {T : Type u} [TopologicalSpace T] [NoetherianSpace T]
    {V : Set T} (hV : IsOpen V) (hVd : Dense V) {η : T} (hη : η ∈ genericPoints T) : η ∈ V := by
  obtain ⟨W, hWo, hWne, hWsub⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hη
  obtain ⟨x, hxV, hxW⟩ := hVd.exists_mem_open hWo hWne
  exact ((show IsGenericPoint η (closure ({η} : Set T)) from rfl).mem_open_set_iff hV).2
    ⟨x, hWsub hxW, hxV⟩

end Stacks.Topology

namespace AlgebraicGeometry

/-! ### A morphism which is a closed immersion over an open -/

section Restrict

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)

/-- **A morphism whose restriction over an open is surjective on stalks has surjective stalk maps
at the points above that open.** The stalk map of `f ∣_ U` at a point of `f ⁻¹ᵁ U` is isomorphic,
as an arrow of `CommRingCat`, to the stalk map of `f` at the underlying point of `Y`. -/
theorem surjective_stalkMap_of_mem_of_morphismRestrict [SurjectiveOnStalks (f ∣_ U)]
    {y : Y} (hy : f.base y ∈ U) : Function.Surjective (f.stalkMap y) :=
  (MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.surjective CommRingCat)
    (morphismRestrictStalkMap f U ⟨y, hy⟩)).mp
      (SurjectiveOnStalks.stalkMap_surjective (f ∣_ U) ⟨y, hy⟩)

/-- **A morphism which is a closed immersion over an open has one-point fibres above that open.**
A point with the same image as `y` lies above `U` too, and the underlying map of `f ∣_ U` is
injective. -/
theorem preimage_singleton_subset_of_isClosedImmersion_morphismRestrict
    [IsClosedImmersion (f ∣_ U)] {y : Y} (hy : f.base y ∈ U) :
    f.base ⁻¹' {f.base y} ⊆ {y} := by
  intro w hw
  have hwb : f.base w = f.base y := hw
  have hwU : f.base w ∈ U := hwb ▸ hy
  exact Subtype.ext_iff.mp ((f ∣_ U).isClosedEmbedding.injective
    (show (f ∣_ U).base ⟨w, hwU⟩ = (f ∣_ U).base ⟨y, hy⟩ from
      Subtype.ext (((morphismRestrict_base_coe f U ⟨w, hwU⟩).trans hwb).trans
        (morphismRestrict_base_coe f U ⟨y, hy⟩).symm)))

/-- The restriction of `f` over an open `U` is the base change of `f` along `U.ι` up to the
canonical isomorphism, so it is a closed immersion as soon as that base change is. -/
theorem isClosedImmersion_morphismRestrict_of_isClosedImmersion_pullback_snd
    (h : IsClosedImmersion (pullback.snd f U.ι)) : IsClosedImmersion (f ∣_ U) := by
  have := h
  have h' : IsClosedImmersion
      ((pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd f U.ι) := inferInstance
  exact h'

end Restrict

/-! ### The support of the cokernel of the comparison map -/

section Cokernel

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- **Off the image of a closed morphism the cokernel of `𝒪_X ⟶ f_*𝒪_Y` has vanishing stalk.**
The image is closed, so the support of `f_*𝒪_Y` is contained in it; at a point outside, the stalk
of `f_*𝒪_Y` is already zero and the stalk map of the comparison is trivially onto. -/
theorem notMem_supp_cokernel_pushforwardUnitHom_of_notMem_range [UniversallyClosed f] {y : X}
    (hy : y ∉ Set.range f.base) :
    y ∉ _root_.SheafOfModules.supp (cokernel (Scheme.Modules.pushforwardUnitHom f)) := by
  have hcl : IsClosed (Set.range f.base) := by
    rw [← Set.image_univ]; exact f.isClosedMap _ isClosed_univ
  have hsub := supp_pushforward_subset f (Scheme.Modules.unitModule Y) hcl Set.Subset.rfl
  have hsing : Subsingleton ((Scheme.Modules.pushforwardUnit f).presheaf.stalk y) :=
    not_nontrivial_iff_subsingleton.mp fun hn =>
      hy (hsub ((_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ y).mpr hn))
  exact (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel _ y).1
    fun _ => ⟨0, Subsingleton.elim _ _⟩

/-- **The cokernel of `𝒪_X ⟶ f_*𝒪_Y` has vanishing stalk at every point of an open over which
`f` is a closed immersion.** At a point of `U` in the image of `f` the fibre is the single point
above it and the local ring map there is onto, so the stalk of the comparison map is onto by
`AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_pushforwardUnitHom`; at a point of
`U` outside the image the stalk of `f_*𝒪_Y` vanishes. -/
theorem notMem_supp_cokernel_pushforwardUnitHom_of_mem [UniversallyClosed f] (U : X.Opens)
    [IsClosedImmersion (f ∣_ U)] {y : X} (hy : y ∈ U) :
    y ∉ _root_.SheafOfModules.supp (cokernel (Scheme.Modules.pushforwardUnitHom f)) := by
  by_cases hr : y ∈ Set.range f.base
  · obtain ⟨x, rfl⟩ := hr
    exact (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel _ _).1
      (Scheme.Modules.surjective_stalkLinearMap_pushforwardUnitHom f x f.isClosedMap
        (preimage_singleton_subset_of_isClosedImmersion_morphismRestrict f U hy)
        (surjective_stalkMap_of_mem_of_morphismRestrict f U hy))
  · exact notMem_supp_cokernel_pushforwardUnitHom_of_notMem_range f hr

end Cokernel

/-! ### Tag 0CE3 -/

/-- **[Stacks, Tag 0CE3].** Let `k` be a field, let `g : X ⟶ Spec k` be proper with
`dim X ≤ 1`, and let `f : Y ⟶ X` be finite and a closed immersion over a dense open `U ⊆ X`.
Then the genus of `Y` is at most the genus of `X`, that is
`dim_k H¹(Y, 𝒪_Y) ≤ dim_k H¹(X, 𝒪_X)`.

The hypotheses are exactly the source's: `X` proper over `k` of dimension at most one, `f`
finite, and `f` a closed immersion over the dense open `U`. The proof applies the cohomological
step `AlgebraicGeometry.genus_le_of_isAffineHom_of_isZero`, whose three inputs are proved here
from those hypotheses; see the module docstring. -/
@[stacks 0CE3]
theorem genus_le_of_isFinite_of_isClosedImmersion_over_dense_open
    (k : Type u) [Field k] {X Y : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsProper g]
    (f : Y ⟶ X) [IsFinite f] (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    (U : X.Opens) (hdense : Dense (U : Set X))
    (hclosed : IsClosedImmersion (pullback.snd f U.ι)) :
    genus (f ≫ g) ≤ genus g := by
  have : IsClosedImmersion (f ∣_ U) :=
    isClosedImmersion_morphismRestrict_of_isClosedImmersion_pullback_snd f U hclosed
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isProper_over_field k g
  have : IsNoetherian X := isNoetherian_of_isProper_over_field k g
  have : NoetherianSpace (X : Type u) := IsNoetherian.noetherianSpace
  have : IsLocallyNoetherian Y :=
    isLocallyNoetherian_of_isProper_over_field k (f ≫ g)
  -- Coherence of the four modules built from the comparison map.
  have hOX : (SheafOfModules.unit X.ringCatSheaf).IsCoherent := isCoherent_unit k g
  have hOY : (SheafOfModules.unit Y.ringCatSheaf).IsCoherent := isCoherent_unit k (f ≫ g)
  have hP : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit Y.ringCatSheaf)) :=
    isCoherent_pushforward_of_isFinite f _
  have hQ : SheafOfModules.IsCoherent (cokernel (Scheme.Modules.pushforwardUnitHom f)) :=
    isCoherent_cokernel (Scheme.Modules.pushforwardUnitHom f)
  -- The cokernel's support misses the generic points of the one-dimensional components, hence
  -- has dimension at most zero.
  have hgen : ∀ y ∈ genericPointsOne X,
      y ∉ _root_.SheafOfModules.supp (cokernel (Scheme.Modules.pushforwardUnitHom f)) :=
    fun y hy => notMem_supp_cokernel_pushforwardUnitHom_of_mem f U
      (Stacks.Topology.mem_of_dense_of_mem_genericPoints U.isOpen hdense
        (mem_genericPointsOne_iff.mp hy).1)
  have hsupp : topologicalKrullDim
      (_root_.SheafOfModules.supp (cokernel (structureSheafToPushforward f)) : Set X) ≤ 0 :=
    topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hdim
      (cokernel (Scheme.Modules.pushforwardUnitHom f)) hQ hgen
  have hQ' : SheafOfModules.IsCoherent (cokernel (structureSheafToPushforward f)) := hQ
  -- The three cohomological inputs.
  have hcoker : IsZero
      (cohomologyOverField k g (cokernel (structureSheafToPushforward f)) 1) :=
    @isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k _ X g _
      (cokernel (structureSheafToPushforward f)) hQ' hsupp 1 (by norm_num)
  have hker : IsZero (cohomologyOverField k g (kernel (structureSheafToPushforward f)) 2) :=
    isZero_cohomologyOverField_of_topologicalKrullDim_le k g
      (kernel (structureSheafToPushforward f)) (d := 1) (i := 2) hdim (by norm_num)
  have hfin : FiniteDimensional k (cohomologyOverField k g (structureSheafModule X) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k g (structureSheafModule X) 1
  exact genus_le_of_isAffineHom_of_isZero k g f hcoker hker hfin

end AlgebraicGeometry

end
