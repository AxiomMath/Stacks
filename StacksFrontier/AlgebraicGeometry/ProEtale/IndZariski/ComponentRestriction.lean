module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Basic
public import StacksFrontier.Topology.Connected.ClopenIntersectionCompact
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.Algebra.Category.AlgCat.FilteredColimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Closed subsets of connected components of an affine spectrum

The inverse image in `Spec A` of a closed subset of the space of connected components of
`Spec A` is itself the spectrum of a surjective ind-Zariski `A`-algebra. That algebra is the
filtered colimit of the localizations of `A` at the idempotents cutting out the clopen subsets
containing the given inverse image.

## Main results

* `AlgebraicGeometry.ProEtale.exists_surjective_indZariski_range_comap_eq_preimage_components`
  constructs the algebra and identifies its spectrum with the prescribed subset.

## Implementation notes

The homeomorphism onto the inverse image is expressed by the embedding of spectra together with
equality of its range and that inverse image. The embedding also follows from surjectivity of
the ring map, but is recorded explicitly as part of the result.

## References

* [Stacks Project, Tag 097C](https://stacks.math.columbia.edu/tag/097C)
-/

@[expose] public noncomputable section

open Topology TopologicalSpace
open CategoryTheory CategoryTheory.Limits PrimeSpectrum ConnectedComponents

universe u

namespace AlgebraicGeometry.ProEtale

/-- The forgetful functor from commutative `A`-algebras to commutative rings preserves filtered
colimits. -/
instance commAlgCat_forget₂_preservesFilteredColimits (A : Type u) [CommRing A] :
    PreservesFilteredColimits (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}) := by
  change PreservesFilteredColimits
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙ Under.forget (CommRingCat.of A))
  infer_instance

/-- The forgetful functor from commutative `A`-algebras to types preserves filtered colimits. -/
instance commAlgCat_forget_preservesFilteredColimits (A : Type u) [CommRing A] :
    PreservesFilteredColimits (forget (CommAlgCat.{u} A)) := by
  change PreservesFilteredColimits
    ((forget₂ (CommAlgCat.{u} A) CommRingCat.{u}) ⋙ forget CommRingCat.{u})
  infer_instance

/-- The localization of `A` at the idempotent cutting out a clopen subset of `Spec A`. -/
private abbrev RestrictClopen (A : Type u) [CommRing A]
    (W : TopologicalSpace.Clopens (PrimeSpectrum A)) : Type u :=
  Localization.Away (PrimeSpectrum.isIdempotentElemEquivClopens.symm W).val

private instance restrictClopenStandardOpenImmersion (A : Type u) [CommRing A]
    (W : TopologicalSpace.Clopens (PrimeSpectrum A)) :
    Algebra.IsStandardOpenImmersion A (RestrictClopen A W) :=
  ⟨(PrimeSpectrum.isIdempotentElemEquivClopens.symm W).val, inferInstance⟩

/-- The spectrum of the localization at a clopen subset is that clopen subset. -/
private theorem restrictClopen_range (A : Type u) [CommRing A]
    (W : TopologicalSpace.Clopens (PrimeSpectrum A)) :
    Set.range (PrimeSpectrum.comap (algebraMap A (RestrictClopen A W))) = (W : Set _) := by
  rw [PrimeSpectrum.localization_away_comap_range (RestrictClopen A W)
    (PrimeSpectrum.isIdempotentElemEquivClopens.symm W).val]
  exact congrArg Opens.carrier (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm W)

/-- Two `A`-algebra maps out of a localization at a clopen subset are equal. -/
private theorem restrictClopen_algHom_ext {A : Type u} [CommRing A]
    {W : TopologicalSpace.Clopens (PrimeSpectrum A)} {S : Type*} [CommRing S] [Algebra A S]
    (f g : RestrictClopen A W →ₐ[A] S) : f = g :=
  Subsingleton.elim (h := IsLocalization.algHom_subsingleton
    (Submonoid.powers (PrimeSpectrum.isIdempotentElemEquivClopens.symm W).val)) f g

/-- The restriction map between the localizations at two nested clopen subsets. -/
private def restrictClopen_map (A : Type u) [CommRing A]
    {W₁ W₂ : TopologicalSpace.Clopens (PrimeSpectrum A)} (h : W₁ ≤ W₂) :
    RestrictClopen A W₂ →ₐ[A] RestrictClopen A W₁ := by
  let e₁ := (PrimeSpectrum.isIdempotentElemEquivClopens.symm W₁).val
  let e₂ := (PrimeSpectrum.isIdempotentElemEquivClopens.symm W₂).val
  have hdvd : e₂ ∣ e₁ := by
    refine ⟨e₁, ?_⟩
    rw [mul_comm]
    exact (PrimeSpectrum.isIdempotentElemEquivClopens.symm.monotone h).symm
  let f : RestrictClopen A W₂ →+* RestrictClopen A W₁ :=
    IsLocalization.Away.lift (S := RestrictClopen A W₂) e₂
      (IsLocalization.Away.isUnit_of_dvd (x := e₁) hdvd)
  exact
    { toRingHom := f
      commutes' := fun r => by
        simp [f, IsLocalization.Away.lift_eq] }

/-- The diagram of localizations of `A` at the clopen subsets of `Spec A` containing a given
subset, indexed by those clopen subsets ordered by inclusion. -/
private def restrictionDiag (A : Type u) [CommRing A] (Z : Set (PrimeSpectrum A)) :
    {W : TopologicalSpace.Clopens (PrimeSpectrum A) // Z ≤ W}ᵒᵖ ⥤ CommAlgCat A where
  obj W := CommAlgCat.of A (RestrictClopen A W.unop.val)
  map {_X _Y} f := CommAlgCat.ofHom (restrictClopen_map A f.unop.le)
  map_id _ := CommAlgCat.hom_ext <| restrictClopen_algHom_ext _ _
  map_comp _ _ := CommAlgCat.hom_ext <| restrictClopen_algHom_ext _ _

/-- The colimit of the diagram of localizations at the clopen subsets containing `Z`. -/
private abbrev restrictionRing (A : Type u) [CommRing A] (Z : Set (PrimeSpectrum A)) : Type u :=
  colimit (C := CommAlgCat A) (restrictionDiag A Z)

private instance restrictionIndexNonempty (A : Type u) [CommRing A] (Z : Set (PrimeSpectrum A)) :
    Nonempty {W : TopologicalSpace.Clopens (PrimeSpectrum A) // Z ≤ W} :=
  ⟨⟨⊤, le_top⟩⟩

private instance restrictionIndexCofiltered (A : Type u) [CommRing A]
    (Z : Set (PrimeSpectrum A)) :
    IsCofiltered {W : TopologicalSpace.Clopens (PrimeSpectrum A) // Z ≤ W} where
  cone_objs X Y := ⟨⟨X.1 ⊓ Y.1, le_inf X.2 Y.2⟩,
    CategoryTheory.homOfLE (Subtype.mk_le_mk.mpr inf_le_left),
    CategoryTheory.homOfLE (Subtype.mk_le_mk.mpr inf_le_right), trivial⟩
  cone_maps X _ _ _ := ⟨X, CategoryTheory.CategoryStruct.id X, Subsingleton.elim _ _⟩

/-- Each localization at a clopen subset is a quotient of `A`, hence so is the colimit. -/
private theorem restrictionRing_surjective (A : Type u) [CommRing A]
    (Z : Set (PrimeSpectrum A)) : Function.Surjective (algebraMap A (restrictionRing A Z)) := by
  intro x
  let D := restrictionDiag A Z
  obtain ⟨⟨j⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget (CommAlgCat A)) (colimit.isColimit D)) x
  obtain ⟨a, ha⟩ := IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
    (S := RestrictClopen A j.1) _ (PrimeSpectrum.isIdempotentElemEquivClopens.symm j.1).prop y
  refine ⟨a, ?_⟩
  simp only [Functor.mapCocone_ι_app, colimit.cocone_ι,
    CategoryTheory.ConcreteCategory.hom_ofHom] at hy
  rw [← hy, ← ha]
  exact ((colimit.ι D (Opposite.op j)).hom.commutes a).symm

/-- The vanishing locus of the kernel of `A → RestrictClopen A W` is `W`. -/
private theorem restrictionClopen_zeroLocusKer (A : Type u) [CommRing A]
    (W : TopologicalSpace.Clopens (PrimeSpectrum A)) :
    PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap A (RestrictClopen A W)) : Set A) = W := by
  rw [← range_comap_of_surjective (RestrictClopen A W)
    (algebraMap A (RestrictClopen A W))
    (IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem _
      (PrimeSpectrum.isIdempotentElemEquivClopens.symm W).prop), restrictClopen_range]

/-- Every stage of the colimit kills at least the elements the colimit kills. -/
private theorem restriction_ker_le (A : Type u) [CommRing A]
    {Z : Set (PrimeSpectrum A)} {W : TopologicalSpace.Clopens (PrimeSpectrum A)} (hW : Z ≤ W) :
    RingHom.ker (algebraMap A (RestrictClopen A W)) ≤
      RingHom.ker (algebraMap A (restrictionRing A Z)) := by
  intro a ha
  rw [RingHom.mem_ker] at ha ⊢
  let ι := (colimit.ι (restrictionDiag A Z) (Opposite.op ⟨W, hW⟩)).hom
  calc algebraMap A (restrictionRing A Z) a
      = ι (algebraMap A (RestrictClopen A W) a) := (ι.commutes a).symm
    _ = ι 0 := congrArg ι ha
    _ = 0 := map_zero _

/-- Every point of `Z` lies in the vanishing locus of the kernel of `A → restrictionRing A Z`. -/
private theorem subset_zeroLocus_ker_restrictionRing (A : Type u) [CommRing A]
    (Z : Set (PrimeSpectrum A)) :
    Z ⊆ PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap A (restrictionRing A Z)) : Set A) := by
  intro p hp
  rw [PrimeSpectrum.mem_zeroLocus]
  intro a ha
  rw [SetLike.mem_coe, RingHom.mem_ker] at ha
  let D := restrictionDiag A Z
  let ιtop :=
    colimit.ι D (Opposite.op ⟨(⊤ : TopologicalSpace.Clopens (PrimeSpectrum A)), le_top⟩)
  have heq : ιtop.hom (algebraMap A (RestrictClopen A ⊤) a) =
      ιtop.hom (0 : RestrictClopen A ⊤) :=
    (ιtop.hom.commutes a).trans (ha.trans (map_zero ιtop.hom).symm)
  obtain ⟨k, f, g, hfg⟩ := (Types.FilteredColimit.isColimit_eq_iff
    (D ⋙ forget (CommAlgCat A))
    (isColimitOfPreserves (forget (CommAlgCat A)) (colimit.isColimit D))).mp heq
  let W := k.unop.val
  have hmap : (D ⋙ forget (CommAlgCat A)).map f
      (algebraMap A (RestrictClopen A ⊤) a) = algebraMap A (RestrictClopen A W) a :=
    ((D.map f).hom.commutes a)
  have ha0 : algebraMap A (RestrictClopen A W) a = 0 := by
    rw [← hmap, hfg]
    exact map_zero ((D.map g).hom)
  have hker : RingHom.ker (algebraMap A (RestrictClopen A W)) ≤ p.asIdeal := by
    rw [← SetLike.coe_subset_coe, ← PrimeSpectrum.mem_zeroLocus]
    exact restrictionClopen_zeroLocusKer A W ▸ k.unop.property hp
  exact hker (RingHom.mem_ker.mpr ha0)

/-- A closed union of connected components `Z` contains the vanishing locus of the kernel of
`A → restrictionRing A Z`. -/
private theorem zeroLocus_ker_restrictionRing_subset (A : Type u) [CommRing A]
    {Z : Set (PrimeSpectrum A)} (hZc : IsClosed Z) (hZu : IsUnionOfConnectedComponents Z) :
    PrimeSpectrum.zeroLocus (RingHom.ker (algebraMap A (restrictionRing A Z)) : Set A) ⊆ Z := by
  intro p hp
  have hpW : ∀ W : TopologicalSpace.Clopens (PrimeSpectrum A), Z ≤ W → p ∈ (W : Set _) := by
    intro W hW
    rw [← restrictionClopen_zeroLocusKer A W]
    exact PrimeSpectrum.zeroLocus_anti_mono (restriction_ker_le A hW) hp
  obtain ⟨ι, U, hU, hZ⟩ :=
    isIntersectionOfClopens_of_isClosed_of_isUnionOfConnectedComponents
      (X := PrimeSpectrum A) (T := Z) hZc hZu
  rw [hZ]
  exact Set.mem_iInter.mpr fun i => hpW ⟨U i, hU i⟩ (hZ ▸ Set.iInter_subset U i)

/-- **Stacks Project, Tag 097C.** A closed union of connected components of an affine spectrum
is the spectrum of a surjective ind-Zariski algebra, homeomorphic to that union via
contraction. -/
@[stacks 097C]
theorem exists_surjective_indZariski_range_comap_eq_preimage_components
    (A : Type u) [CommRing A]
    (T : Set (ConnectedComponents (PrimeSpectrum A))) (hT : IsClosed T) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B),
      IsIndZariski.{u, u, u} A B ∧
      Function.Surjective (algebraMap A B) ∧
      IsEmbedding (PrimeSpectrum.comap (algebraMap A B)) ∧
      Set.range (PrimeSpectrum.comap (algebraMap A B)) =
        ((↑) : PrimeSpectrum A → ConnectedComponents (PrimeSpectrum A)) ⁻¹' T := by
  classical
  let Z : Set (PrimeSpectrum A) :=
    ((↑) : PrimeSpectrum A → ConnectedComponents (PrimeSpectrum A)) ⁻¹' T
  let B := restrictionRing A Z
  refine ⟨B, inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · change ObjectProperty.ind.{u} (fun C : CommAlgCat.{u} A => Algebra.IsLocalIso A C)
      (CommAlgCat.of A (ULift.{u} B))
    exact ⟨_, inferInstance, inferInstance,
      (ColimitPresentation.colimit (restrictionDiag A Z)).ofIso
        (CommAlgCat.isoMk ULift.algEquiv.symm), fun W => by
      change Algebra.IsLocalIso A (RestrictClopen A W.unop.val)
      infer_instance⟩
  · exact restrictionRing_surjective A Z
  · exact PrimeSpectrum.isClosedEmbedding_comap_of_surjective B (algebraMap A B)
      (restrictionRing_surjective A Z) |>.toIsEmbedding
  · rw [range_comap_of_surjective B (algebraMap A B) (restrictionRing_surjective A Z)]
    exact Set.Subset.antisymm
      (zeroLocus_ker_restrictionRing_subset A (hT.preimage ConnectedComponents.continuous_coe)
        fun x hx y hy => by
          have hxy : (y : ConnectedComponents (PrimeSpectrum A)) = x :=
            ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq hy).symm
          simpa [Z, hxy] using hx)
      (subset_zeroLocus_ker_restrictionRing A Z)

end AlgebraicGeometry.ProEtale

end
