module

public import Mathlib.Topology.Irreducible
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Bijective
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleBasics.NormalCrossings.Components
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupChain
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Iterated

/-!
# The components of an inverse image under a blowup at a closed point

Let `f : W ⟶ Y` be a morphism which is an isomorphism over the complement of a closed point `w`
of `Y` and whose image contains every other point of `Y` — the blowup of `Y` at the reduced point
`{w}` is such a morphism, by [Stacks, Tag 02OS]. Let `E ⊆ Y` be a closed subscheme. Then every
irreducible component of the inverse image of `E` is accounted for: it either lies in the fibre
over `w`, where it is a maximal irreducible subset of that fibre, or it is the *strict transform*
of an irreducible component of `E`, namely the closure of the part of the inverse image of that
component lying off the fibre over `w`.

This is the first sentence of the proof of [Stacks, Tag 0BIC] — "the inverse image `Z'` of `Z` is
supported on the strict transform of `Z` and the exceptional divisor" — and it is what lets one
case-split a component of an inverse image when checking a property of the components of `Z`
against the components of `Z'`.

## Main definitions

* `Stacks.ResolutionOfSurfaces.IsExceptionalFibreComponent` — a closed subset of the blowup at a
  closed point `a` which is maximal among the irreducible subsets of the fibre over `a`.
* `Stacks.ResolutionOfSurfaces.reducedStrictTransform` — the reduced closed subscheme on the
  closure of the part of the inverse image of a closed subscheme lying off that fibre.

## Main results

* `Stacks.ResolutionOfSurfaces.maximal_or_exists_component_coe_support_componentIdeal_comap` — the
  decomposition for an arbitrary morphism which is an isomorphism off a closed point, stated on
  supports.
* `Stacks.ResolutionOfSurfaces.isExceptionalFibreComponent_or_exists_eq_reducedStrictTransform` —
  the decomposition for the blowup at a closed point, stated as an identity of ideal sheaves.
* `Stacks.ResolutionOfSurfaces.forall_componentIdeal_comap_blowUp` and
  `Stacks.ResolutionOfSurfaces.forall_componentIdeal_comap_of_pointBlowupChain` — the induction
  the decomposition is for: a property of closed subschemes which holds of every exceptional
  fibre component and passes to reduced strict transforms holds of every irreducible component of
  the inverse image, along one blowup and along a whole chain of blowups at closed points.

## Implementation notes

The argument is topological. The two hypotheses that carry the geometry of the blowup are
injectivity of `f` off the fibre over `w` and openness of the images of the opens of that
complement; both come from [Stacks, Tag 02OS] in the form
`AlgebraicGeometry.isIso_blowUpToBase_restrict_of_subset_compl_support`, and surjectivity off `w`
from `AlgebraicGeometry.exists_blowUpToBase_eq_of_notMem_support`. No irreducibility of the
exceptional fibre is assumed: a component lying in that fibre is only identified as a *maximal
irreducible subset* of it, which is what the statement can honestly say without the global form
of part (1) of [Stacks, Tag 0AGQ].

Irreducible components of a closed subscheme are matched with maximal irreducible subsets of its
support in the ambient scheme through the closed embedding `Scheme.IdealSheafData.subschemeι`, so
that the comparison between the components of `E` and those of `E.comap f` happens entirely among
subsets of `Y` and of `W`. A component is recovered from its support because
`Stacks.Divisors.componentIdeal` is reduced.

## References

* [Stacks Project, Tag 0BIC](https://stacks.math.columbia.edu/tag/0BIC)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0AGQ](https://stacks.math.columbia.edu/tag/0AGQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.Divisors

universe u

namespace Stacks.ResolutionOfSurfaces

/-! ### The topological decomposition -/

section Topology

variable {W Y : Type*} [TopologicalSpace W] [TopologicalSpace Y] {f : W → Y}

/-- Off the fibre over `w`, the preimage of an irreducible set is irreducible as soon as that set
is not reduced to `w`. -/
private theorem isIrreducible_preimage_sdiff {w : Y}
    (hsurj : ∀ y : Y, y ≠ w → y ∈ Set.range f)
    (hinj : Set.InjOn f ((f ⁻¹' {w})ᶜ))
    (hopen : ∀ U : Set W, IsOpen U → IsOpen (f '' (U \ f ⁻¹' {w})))
    {C : Set Y} (hC : IsIrreducible C) (hne : (C \ {w}).Nonempty) :
    IsIrreducible (f ⁻¹' C \ f ⁻¹' {w}) := by
  refine ⟨?_, fun U₁ U₂ hU₁ hU₂ ⟨x₁, hx₁, hx₁U⟩ ⟨x₂, hx₂, hx₂U⟩ => ?_⟩
  · obtain ⟨y, hyC, hyw⟩ := hne
    obtain ⟨x, rfl⟩ := hsurj y hyw
    exact ⟨x, hyC, hyw⟩
  · have h₁ : (C ∩ f '' (U₁ \ f ⁻¹' {w})).Nonempty :=
      ⟨f x₁, hx₁.1, ⟨x₁, ⟨hx₁U, hx₁.2⟩, rfl⟩⟩
    have h₂ : (C ∩ f '' (U₂ \ f ⁻¹' {w})).Nonempty :=
      ⟨f x₂, hx₂.1, ⟨x₂, ⟨hx₂U, hx₂.2⟩, rfl⟩⟩
    obtain ⟨y, hyC, hy₁, hy₂⟩ := hC.2 _ _ (hopen _ hU₁) (hopen _ hU₂) h₁ h₂
    obtain ⟨z₁, ⟨hz₁U, hz₁E⟩, rfl⟩ := hy₁
    obtain ⟨z₂, ⟨hz₂U, hz₂E⟩, hz₂⟩ := hy₂
    have hz : z₁ = z₂ := hinj hz₁E hz₂E hz₂.symm
    exact ⟨z₁, ⟨hyC, hz₁E⟩, hz₁U, hz ▸ hz₂U⟩

/-- **The topological content of the decomposition of an inverse image into strict transforms and
the exceptional fibre.** Let `f` be a continuous map which is a homeomorphism off the fibre over a
closed point `w` and whose image contains every other point. Then a maximal irreducible subset `D`
of the preimage of a closed set `S` either lies in the fibre over `w`, where it is a maximal
irreducible subset of that fibre, or is the closure of the part off the fibre of the preimage of a
maximal irreducible subset of `S`. -/
private theorem maximal_preimage_cases (hcont : Continuous f) {w : Y}
    (hsurj : ∀ y : Y, y ≠ w → y ∈ Set.range f) (hw : IsClosed ({w} : Set Y))
    (hinj : Set.InjOn f ((f ⁻¹' {w})ᶜ))
    (hopen : ∀ U : Set W, IsOpen U → IsOpen (f '' (U \ f ⁻¹' {w})))
    {S : Set Y} (hS : IsClosed S) {D : Set W}
    (hD : Maximal (fun D' : Set W => IsIrreducible D' ∧ D' ⊆ f ⁻¹' S) D) :
    Maximal (fun D' : Set W => IsIrreducible D' ∧ D' ⊆ f ⁻¹' {w}) D ∨
      ∃ C : Set Y, Maximal (fun C' : Set Y => IsIrreducible C' ∧ C' ⊆ S) C ∧
        D = closure (f ⁻¹' C \ f ⁻¹' {w}) := by
  obtain ⟨⟨hDirr, hDsub⟩, hDmax⟩ := hD
  by_cases hDE : D ⊆ f ⁻¹' {w}
  · left
    obtain ⟨x, hxD⟩ := hDirr.1
    have hwS : w ∈ S := by
      have h := hDsub hxD
      rwa [Set.mem_preimage, show f x = w from hDE hxD] at h
    exact ⟨⟨hDirr, hDE⟩, fun D' hD' hsub => hDmax
      ⟨hD'.1, hD'.2.trans (Set.preimage_mono (Set.singleton_subset_iff.mpr hwS))⟩ hsub⟩
  · right
    have hne : (D ∩ (f ⁻¹' {w})ᶜ).Nonempty := Set.inter_compl_nonempty_iff.mpr hDE
    have hdense : D ⊆ closure (D ∩ (f ⁻¹' {w})ᶜ) :=
      subset_closure_inter_of_isPreirreducible_of_isOpen hDirr.2
        (hw.preimage hcont).isOpen_compl hne
    set C : Set Y := closure (f '' D)
    have hCirr : IsIrreducible C := (hDirr.image f hcont.continuousOn).closure
    have hCS : C ⊆ S := hS.closure_subset_iff.mpr (Set.image_subset_iff.mpr hDsub)
    have hDC : D ⊆ f ⁻¹' C := fun x hxD => subset_closure ⟨x, hxD, rfl⟩
    have hCw : (C \ {w}).Nonempty := by
      obtain ⟨x, hxD, hxE⟩ := hne
      exact ⟨f x, subset_closure ⟨x, hxD, rfl⟩, hxE⟩
    have key : ∀ C' : Set Y, IsIrreducible C' → C' ⊆ S → C ⊆ C' →
        D = closure (f ⁻¹' C' \ f ⁻¹' {w}) ∧ C' ⊆ C := by
      intro C' hC'irr hC'S hCC'
      have hC'w : (C' \ {w}).Nonempty := hCw.mono (Set.sdiff_subset_sdiff_left hCC')
      have hirr' : IsIrreducible (f ⁻¹' C' \ f ⁻¹' {w}) :=
        isIrreducible_preimage_sdiff hsurj hinj hopen hC'irr hC'w
      have hD'sub : closure (f ⁻¹' C' \ f ⁻¹' {w}) ⊆ f ⁻¹' S :=
        (hS.preimage hcont).closure_subset_iff.mpr fun x hx => Set.mem_preimage.mpr (hC'S hx.1)
      have hDD' : D ⊆ closure (f ⁻¹' C' \ f ⁻¹' {w}) :=
        hdense.trans (closure_mono fun x hx => ⟨hCC' (hDC hx.1), hx.2⟩)
      have hEq : D = closure (f ⁻¹' C' \ f ⁻¹' {w}) :=
        subset_antisymm hDD' (hDmax ⟨hirr'.closure, hD'sub⟩ hDD')
      refine ⟨hEq, ?_⟩
      have h1 : C' \ {w} ⊆ f '' D := by
        intro y hy
        obtain ⟨x, rfl⟩ := hsurj y hy.2
        exact ⟨x, hEq ▸ subset_closure ⟨hy.1, hy.2⟩, rfl⟩
      have h2 : C' ⊆ closure (C' \ {w}) :=
        subset_closure_inter_of_isPreirreducible_of_isOpen hC'irr.2 hw.isOpen_compl
          (let ⟨y, hy⟩ := hC'w; ⟨y, hy.1, hy.2⟩)
      exact h2.trans (closure_mono h1)
    exact ⟨C, ⟨⟨hCirr, hCS⟩, fun C' hC' hCC' => (key C' hC'.1 hC'.2 hCC').2⟩,
      (key C hCirr hCS Set.Subset.rfl).1⟩

end Topology

/-! ### Irreducible components through a closed embedding -/

section Embedding

variable {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y] {ι : Z → Y}

/-- An embedding reflects irreducibility of subsets of its range. -/
private theorem isIrreducible_preimage_of_subset_range (hι : Topology.IsEmbedding ι) {A : Set Y}
    (hA : IsIrreducible A) (hran : A ⊆ Set.range ι) : IsIrreducible (ι ⁻¹' A) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := hA.1
    obtain ⟨x, rfl⟩ := hran hy
    exact ⟨x, hy⟩
  · intro U₁ U₂ hU₁ hU₂ h₁ h₂
    obtain ⟨V₁, hV₁open, rfl⟩ := hι.isInducing.isOpen_iff.mp hU₁
    obtain ⟨V₂, hV₂open, rfl⟩ := hι.isInducing.isOpen_iff.mp hU₂
    obtain ⟨x₁, hx₁D, hx₁U⟩ := h₁
    obtain ⟨x₂, hx₂D, hx₂U⟩ := h₂
    obtain ⟨y, hyD, hy₁, hy₂⟩ :=
      hA.2 V₁ V₂ hV₁open hV₂open ⟨ι x₁, hx₁D, hx₁U⟩ ⟨ι x₂, hx₂D, hx₂U⟩
    obtain ⟨x, rfl⟩ := hran hyD
    exact ⟨x, hyD, hy₁, hy₂⟩

/-- The image of an irreducible component of the source of an embedding is maximal among the
irreducible subsets of the range. -/
private theorem maximal_image_of_mem_irreducibleComponents (hι : Topology.IsEmbedding ι)
    {C : Set Z} (hC : C ∈ irreducibleComponents Z) :
    Maximal (fun A : Set Y => IsIrreducible A ∧ A ⊆ Set.range ι) (ι '' C) := by
  refine ⟨⟨hC.1.image ι hι.continuous.continuousOn, Set.image_subset_range _ _⟩,
    fun A hA hsub => ?_⟩
  rw [← Set.image_preimage_eq_of_subset hA.2] at hsub ⊢
  exact Set.image_mono (hC.2 (isIrreducible_preimage_of_subset_range hι hA.1 hA.2)
    ((Set.image_subset_image_iff hι.injective).mp hsub))

/-- Conversely, a maximal irreducible subset of the range of an embedding is the image of an
irreducible component of the source. -/
private theorem exists_mem_irreducibleComponents_image_eq (hι : Topology.IsEmbedding ι)
    {A : Set Y} (hA : Maximal (fun A' : Set Y => IsIrreducible A' ∧ A' ⊆ Set.range ι) A) :
    ∃ C ∈ irreducibleComponents Z, ι '' C = A := by
  have himg : ι '' (ι ⁻¹' A) = A := Set.image_preimage_eq_of_subset hA.1.2
  refine ⟨ι ⁻¹' A, ⟨isIrreducible_preimage_of_subset_range hι hA.1.1 hA.1.2, fun B hB hsub => ?_⟩,
    himg⟩
  refine Set.image_subset_iff.mp (hA.2 ⟨hB.image ι hι.continuous.continuousOn,
    Set.image_subset_range _ _⟩ ?_)
  rw [← himg]
  exact Set.image_mono hsub

end Embedding

/-! ### Scheme-level statements -/

section Schemes

/-- A morphism that restricts to an isomorphism over an open `V` carries an open of the source,
cut down to the inverse image of `V`, to an open of the target. -/
private theorem isOpen_image_inter_preimage_of_isIso_morphismRestrict {W Y : Scheme.{u}}
    (f : W ⟶ Y) (V : Y.Opens) [IsIso (f ∣_ V)] {A : Set W} (hA : IsOpen A) :
    IsOpen (f.base '' (A ∩ f.base ⁻¹' (V : Set Y))) := by
  have hemb : Topology.IsOpenEmbedding ((f ⁻¹ᵁ V).ι ≫ f).base := by
    rw [← morphismRestrict_ι, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact V.ι.isOpenEmbedding.comp (f ∣_ V).isOpenEmbedding
  have hop := hemb.isOpenMap ((f ⁻¹ᵁ V).ι.base ⁻¹' A) (hA.preimage (f ⁻¹ᵁ V).ι.continuous)
  convert hop using 1
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp,
    Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
  rfl

/-- **The components of an inverse image under a morphism which is an isomorphism off a closed
point.** Let `f : W ⟶ Y` be an isomorphism over the complement of a closed point `w` of `Y`, every
other point of `Y` being in its image, and let `E` be a closed subscheme of `Y`. Then every
irreducible component of the inverse image of `E` either lies in the fibre over `w`, where it is
a maximal irreducible subset of that fibre, or is the *strict transform* of an irreducible
component of `E`: the closure of the part of the inverse image of that component lying off the
fibre over `w`.

This is the topological decomposition the source of [Stacks, Tag 0BIC] uses in its first
paragraph, where it reads "the inverse image `Z'` of `Z` is supported on the strict transform of
`Z` and the exceptional divisor". -/
public theorem maximal_or_exists_component_coe_support_componentIdeal_comap {W Y : Scheme.{u}}
    (f : W ⟶ Y) (w : Y) (hw : IsClosed ({w} : Set Y))
    [IsIso (f ∣_ (⟨{w}ᶜ, hw.isOpen_compl⟩ : Y.Opens))]
    (hsurj : ∀ y : Y, y ≠ w → y ∈ Set.range f.base) (E : Y.IdealSheafData)
    (C : irreducibleComponents (E.comap f).subscheme) :
    Maximal (fun D : Set W => IsIrreducible D ∧ D ⊆ f.base ⁻¹' {w})
        ((componentIdeal (E.comap f) C).support : Set W) ∨
      ∃ C' : irreducibleComponents E.subscheme,
        ((componentIdeal (E.comap f) C).support : Set W) =
          closure (f.base ⁻¹' ((componentIdeal E C').support : Set Y) \ f.base ⁻¹' {w}) := by
  have hcomp : ∀ {A : Scheme.{u}} (D : A.IdealSheafData) (C : irreducibleComponents D.subscheme),
      ((componentIdeal D C).support : Set A) = D.subschemeι '' (C : Set D.subscheme) := by
    intro A D C
    rw [componentIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (D.subschemeι.isClosedEmbedding.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ C.2)).closure_eq
  set V : Y.Opens := ⟨{w}ᶜ, hw.isOpen_compl⟩
  have hVcoe : (V : Set Y) = ({w} : Set Y)ᶜ := rfl
  have hinj : Set.InjOn f.base ((f.base ⁻¹' {w})ᶜ) := by
    have h := Stacks.StrictTransform.injOn_preimage_of_isIso_morphismRestrict f V
    rwa [hVcoe, Set.preimage_compl] at h
  have hopen : ∀ A : Set W, IsOpen A → IsOpen (f.base '' (A \ f.base ⁻¹' {w})) := by
    intro A hA
    have h := isOpen_image_inter_preimage_of_isIso_morphismRestrict f V hA
    rwa [hVcoe, Set.preimage_compl, ← Set.sdiff_eq] at h
  have hsupp : ((E.comap f).support : Set W) = f.base ⁻¹' (E.support : Set Y) := by
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have hD : Maximal (fun D : Set W => IsIrreducible D ∧ D ⊆ f.base ⁻¹' (E.support : Set Y))
      ((componentIdeal (E.comap f) C).support : Set W) := by
    have h := maximal_image_of_mem_irreducibleComponents
      (E.comap f).subschemeι.isClosedEmbedding.isEmbedding C.2
    rw [(E.comap f).range_subschemeι, hsupp] at h
    rwa [hcomp]
  obtain hcase | ⟨Cset, hCmax, hEq⟩ :=
    maximal_preimage_cases f.continuous hsurj hw hinj hopen E.support.isClosed hD
  · exact Or.inl hcase
  · refine Or.inr ?_
    have hCran : Maximal
        (fun A : Set Y => IsIrreducible A ∧ A ⊆ Set.range E.subschemeι.base) Cset := by
      rwa [E.range_subschemeι]
    obtain ⟨C', hC', hC'img⟩ := exists_mem_irreducibleComponents_image_eq
      E.subschemeι.isClosedEmbedding.isEmbedding hCran
    exact ⟨⟨C', hC'⟩, by rw [hEq, hcomp, hC'img]⟩

/-! ### The blowup at a closed point -/

/-- **[Stacks, Tag 02OS] at a reduced closed point.** The blowup of a scheme at a reduced closed
point is an isomorphism over the complement of that point. -/
public theorem isIso_morphismRestrict_blowUpToBase_vanishingIdeal_singleton {Y : Scheme.{u}}
    (w : Y) (hw : IsClosed ({w} : Set Y)) :
    IsIso (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y)) ∣_
      (⟨{w}ᶜ, hw.isOpen_compl⟩ : Y.Opens)) := by
  refine isIso_blowUpToBase_restrict_of_subset_compl_support _ _ fun z hz => ?_
  simp only [Set.mem_compl_iff, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact hz

/-- Every point of a scheme other than the centre of a blowup at a reduced closed point is in the
image of that blowup. -/
public theorem mem_range_blowUpToBase_vanishingIdeal_singleton {Y : Scheme.{u}} (w : Y)
    (hw : IsClosed ({w} : Set Y)) (y : Y) (hy : y ≠ w) :
    y ∈ Set.range (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y))).base := by
  obtain ⟨z, hz⟩ := exists_blowUpToBase_eq_of_notMem_support
    (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds Y)) (x := y) (by
      simp only [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact hy)
  exact ⟨z, hz⟩

/-- A component of a closed subscheme is the reduced structure on its own support. -/
private theorem vanishingIdeal_support_componentIdeal {W : Scheme.{u}} (D : W.IdealSheafData)
    (C : irreducibleComponents D.subscheme) :
    Scheme.IdealSheafData.vanishingIdeal (componentIdeal D C).support = componentIdeal D C := by
  rw [componentIdeal]
  exact congrArg Scheme.IdealSheafData.vanishingIdeal
    (Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal _))

/-- A component of a closed subscheme whose support is a given closed set is the reduced structure
on that set. -/
private theorem componentIdeal_eq_vanishingIdeal {W : Scheme.{u}} (D : W.IdealSheafData)
    (C : irreducibleComponents D.subscheme) {T : Closeds W}
    (hT : ((componentIdeal D C).support : Set W) = (T : Set W)) :
    componentIdeal D C = Scheme.IdealSheafData.vanishingIdeal T := by
  rw [← vanishingIdeal_support_componentIdeal D C, Closeds.ext hT]

/-- A closed subset of the blowup at a closed point `a` is an **exceptional fibre component**
when it is maximal among the irreducible subsets of the fibre over `a`. -/
public def IsExceptionalFibreComponent {A : Scheme.{u}} (a : A) (ha : IsClosed ({a} : Set A))
    (T : Closeds
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)))) : Prop :=
  Maximal (fun D : Set
      (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))) =>
    IsIrreducible D ∧ D ⊆ (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))).base ⁻¹' {a}) (T : Set _)

/-- The **reduced strict transform** of a closed subscheme under the blowup at a closed point:
the reduced structure on the closure of the part of the inverse image lying off the fibre over
that point. -/
public def reducedStrictTransform {A : Scheme.{u}} (a : A) (ha : IsClosed ({a} : Set A))
    (I : A.IdealSheafData) :
    (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure
    ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{a}, ha⟩ : Closeds A))).base ⁻¹' (I.support : Set A) \
      (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{a}, ha⟩ : Closeds A))).base ⁻¹' {a}), isClosed_closure⟩

section OneBlowup

variable {W : Scheme.{u}} (w : W) (hw : IsClosed ({w} : Set W))

/-- Local abbreviation for the centre of the blowup, matching the shape
`Stacks.ResolutionOfSurfaces.PointBlowupChain` uses. -/
local notation3 "centre" => Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)

/-- **The decomposition of the inverse image under one blowup at a closed point.** Every
irreducible component of the inverse image of a closed subscheme `E` under the blowup of `W` at a
closed point `w` is either an exceptional fibre component or the reduced strict transform of an
irreducible component of `E`.

This is the first sentence of the source's proof of [Stacks, Tag 0BIC]: "the inverse image `Z'` of
`Z` is supported on the strict transform of `Z` and the exceptional divisor". -/
public theorem isExceptionalFibreComponent_or_exists_eq_reducedStrictTransform
    (E : W.IdealSheafData)
    (C : irreducibleComponents (E.comap (blowUpToBase centre)).subscheme) :
    IsExceptionalFibreComponent w hw
        (componentIdeal (E.comap (blowUpToBase centre)) C).support ∨
      ∃ C' : irreducibleComponents E.subscheme,
        componentIdeal (E.comap (blowUpToBase centre)) C =
          reducedStrictTransform w hw (componentIdeal E C') := by
  have := isIso_morphismRestrict_blowUpToBase_vanishingIdeal_singleton w hw
  obtain hmax | ⟨C', hC'eq⟩ := maximal_or_exists_component_coe_support_componentIdeal_comap
    (blowUpToBase centre) w hw (mem_range_blowUpToBase_vanishingIdeal_singleton w hw) E C
  · exact Or.inl hmax
  · refine Or.inr ⟨C', ?_⟩
    rw [reducedStrictTransform]
    exact componentIdeal_eq_vanishingIdeal _ C
      (T := ⟨closure ((blowUpToBase centre).base ⁻¹'
        ((componentIdeal E C').support : Set W) \
        (blowUpToBase centre).base ⁻¹' {w}), isClosed_closure⟩) hC'eq

/-- **One blowup at a closed point.** A property of closed subschemes which holds of every
exceptional fibre component and passes to reduced strict transforms holds of every irreducible
component of the inverse image of `E` under the blowup at a closed point, as soon as it holds of
every irreducible component of `E`. -/
public theorem forall_componentIdeal_comap_blowUp (Q : ∀ A : Scheme.{u}, A.IdealSheafData → Prop)
    (hexc : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A))
      (T : Closeds (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)))),
      IsExceptionalFibreComponent a ha T → Q _ (Scheme.IdealSheafData.vanishingIdeal T))
    (hstr : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A)) (I : A.IdealSheafData),
      Q A I → Q _ (reducedStrictTransform a ha I))
    (E : W.IdealSheafData)
    (hE : ∀ C : irreducibleComponents E.subscheme, Q W (componentIdeal E C))
    (C : irreducibleComponents (E.comap (blowUpToBase centre)).subscheme) :
    Q (blowUp centre) (componentIdeal (E.comap (blowUpToBase centre)) C) := by
  obtain hmax | ⟨C', hC'⟩ :=
    isExceptionalFibreComponent_or_exists_eq_reducedStrictTransform w hw E C
  · have h := hexc W w hw (componentIdeal (E.comap (blowUpToBase centre)) C).support hmax
    rwa [vanishingIdeal_support_componentIdeal] at h
  · rw [hC']
    exact hstr W w hw (componentIdeal E C') (hE C')

end OneBlowup

/-- **The components of an inverse image along a chain of blowups at closed points.** A property
of closed subschemes which holds of every maximal irreducible piece of an exceptional fibre and
which passes from a closed subscheme to its strict transform under a blowup at a closed point
holds of every irreducible component of the inverse image of `E` along a chain of blowups at
closed points, as soon as it holds of every irreducible component of `E`.

This is the inductive half of the first paragraph of the source's proof of [Stacks, Tag 0BIC]:
"the inverse image `Z'` of `Z` is supported on the strict transform of `Z` and the exceptional
divisor", from which the source concludes that "in this process we do not produce additional
singular components of dimension 1". The two hypotheses are the one-step geometric facts the
source appeals to there: regularity of the exceptional curve, which is part (1) of
[Stacks, Tag 0AGQ], and the behaviour of a strict transform. -/
public theorem forall_componentIdeal_comap_of_pointBlowupChain
    (Q : ∀ A : Scheme.{u}, A.IdealSheafData → Prop)
    (hexc : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A))
      (T : Closeds (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)))),
      IsExceptionalFibreComponent a ha T → Q _ (Scheme.IdealSheafData.vanishingIdeal T))
    (hstr : ∀ (A : Scheme.{u}) (a : A) (ha : IsClosed ({a} : Set A)) (I : A.IdealSheafData),
      Q A I → Q _ (reducedStrictTransform a ha I))
    {Y V : Scheme.{u}} {T : Set Y} {f : V ⟶ Y} (hf : PointBlowupChain Y T V f)
    (E : Y.IdealSheafData) (hE : ∀ C : irreducibleComponents E.subscheme, Q Y (componentIdeal E C))
    (C : irreducibleComponents (E.comap f).subscheme) :
    Q V (componentIdeal (E.comap f) C) := by
  suffices h : ∀ (V' : Scheme.{u}) (f' : V' ⟶ Y), PointBlowupChain Y T V' f' →
      ∀ J : V'.IdealSheafData, J = E.comap f' →
        ∀ C' : irreducibleComponents J.subscheme, Q V' (componentIdeal J C') from
    h V f hf _ rfl C
  intro V' f' hf'
  induction hf' with
  | refl =>
      intro J hJ C'
      rw [Scheme.IdealSheafData.comap_id] at hJ
      subst hJ
      exact hE C'
  | @step W h hh w hw _hwT ih =>
      intro J hJ
      rw [Scheme.IdealSheafData.comap_comp] at hJ
      subst hJ
      exact forall_componentIdeal_comap_blowUp w hw Q hexc hstr (E.comap h) (ih _ rfl)

end Schemes

end Stacks.ResolutionOfSurfaces

end
