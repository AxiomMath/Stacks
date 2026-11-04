module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.FlatAndRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.Properness
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleSplitting.TrivialSection
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# The projection of the projective bundle of a finite locally free module

Let `ℰ` be a module on a scheme `X`, finite locally free of constant rank `n + 1`, and
`π : 𝐏(ℰ) ⟶ X` the projection of its projective bundle, the relative `Proj` of `Sym(ℰ)`. This
file proves that `π` is flat, locally of finite type, and of relative dimension `n`: three of
the four assertions of Tag 02TX, now for an arbitrary finite locally free `ℰ` of constant rank
rather than a free one.

All three are local on the base. Over an open `V` on which `ℰ` is free of rank `n + 1`, the
part `π ⁻¹ V` of the bundle lying over `V` is the bundle `𝐏(𝒪_V^{n+1})`, by an isomorphism over
`V`: Tag 01O3's base-change comparison at the open immersion `V ⟶ X`, followed by the cartesian
square of the restriction of `π` to `V`. The free bundle is flat, locally of finite type and of
relative dimension `n` (Stacks 01OE), and these transport.

## Main results

* `AlgebraicGeometry.Scheme.Hom.fiberHomeoMorphismRestrict`: the fibre of the restriction of a
  morphism over an open of its target is homeomorphic to the fibre of the morphism.
* `AlgebraicGeometry.relativeDimension_of_forall_exists_morphismRestrict`: relative dimension
  is local on the target.
* `Stacks.ProjectiveBundle.exists_iso_morphismRestrict_free`: over a neighbourhood of every
  point, `π` is the projection of the projective bundle of a free module.
* `Stacks.ProjectiveBundle.flat_toBase`, `Stacks.ProjectiveBundle.locallyOfFiniteType_toBase`
  and `Stacks.ProjectiveBundle.relativeDimension_toBase`: **`π` is flat, locally of finite type,
  and of relative dimension `n`.**

## References

* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 01OE](https://stacks.math.columbia.edu/tag/01OE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.SymGraded

universe u

namespace AlgebraicGeometry

/-! ### Relative dimension is local on the target -/

/-- The inclusion of `f ⁻¹ V` intertwines `f ∣_ V` with `f`, on points. -/
theorem Scheme.Hom.apply_ι_preimage {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (y : (f ⁻¹ᵁ V).toScheme) : f ((f ⁻¹ᵁ V).ι y) = V.ι ((f ∣_ V) y) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, morphismRestrict_ι]

/-- A point of `f ⁻¹ V` over a point of `V` lies, as a point of `X`, over the same point. -/
theorem Scheme.Hom.ι_mem_preimage_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    (V : S.Opens) (s : V.toScheme) (y : (f ∣_ V) ⁻¹' {s}) :
    (f ⁻¹ᵁ V).ι y.1 ∈ f ⁻¹' {V.ι s} := by
  have h : (f ∣_ V) y.1 = s := y.2
  show f ((f ⁻¹ᵁ V).ι y.1) = V.ι s
  rw [f.apply_ι_preimage, h]

/-- The set-theoretic fibre of the restriction `f ∣_ V` over a point of `V` is homeomorphic to
the set-theoretic fibre of `f`, by the inclusion of `f ⁻¹ V`. -/
def Scheme.Hom.preimageHomeoMorphismRestrict {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (s : V.toScheme) : (f ∣_ V) ⁻¹' {s} ≃ₜ f ⁻¹' {V.ι s} := by
  refine (Equiv.ofBijective
    (Set.codRestrict ((f ⁻¹ᵁ V).ι ∘ Subtype.val) _ (f.ι_mem_preimage_morphismRestrict V s))
    ⟨?_, ?_⟩).toHomeomorphOfIsInducing ?_
  · intro a b hab
    have h := congrArg Subtype.val hab
    simp only [Set.val_codRestrict_apply, Function.comp_apply] at h
    exact Subtype.ext ((f ⁻¹ᵁ V).ι.isOpenEmbedding.injective h)
  · rintro ⟨x, hx⟩
    have hx' : f x = V.ι s := hx
    have hxr : x ∈ Set.range (f ⁻¹ᵁ V).ι := by
      rw [Scheme.Opens.range_ι]
      change f x ∈ V
      have hr : V.ι s ∈ Set.range V.ι := ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι] at hr
      rw [hx']
      exact hr
    obtain ⟨y, rfl⟩ := hxr
    refine ⟨⟨y, ?_⟩, rfl⟩
    change (f ∣_ V) y = s
    rw [f.apply_ι_preimage] at hx'
    exact V.ι.isOpenEmbedding.injective hx'
  · exact ((f ⁻¹ᵁ V).ι.isOpenEmbedding.isInducing.comp
      Topology.IsInducing.subtypeVal).codRestrict _

/-- **The fibre of the restriction of a morphism over an open of its target is homeomorphic to
the fibre of the morphism** over the corresponding point. -/
def Scheme.Hom.fiberHomeoMorphismRestrict {X S : Scheme.{u}} (f : X ⟶ S) (V : S.Opens)
    (s : V.toScheme) : (f ∣_ V).fiber s ≃ₜ f.fiber (V.ι s) :=
  ((f ∣_ V).fiberHomeo s).trans
    ((f.preimageHomeoMorphismRestrict V s).trans (f.fiberHomeo (V.ι s)).symm)

/-- **Relative dimension is local on the target.** If every point of the target has an open
neighbourhood over which the restriction of `f` has relative dimension `d`, then so does `f`. -/
theorem relativeDimension_of_forall_exists_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] {d : ℕ}
    (H : ∀ s : S, ∃ (V : S.Opens) (_ : s ∈ V) (_ : LocallyOfFiniteType (f ∣_ V)),
      RelativeDimension (f ∣_ V) d) :
    RelativeDimension f d := by
  intro s hne
  obtain ⟨V, hs, _, hV⟩ := H s
  have hsr : s ∈ Set.range V.ι := by rwa [Scheme.Opens.range_ι]
  obtain ⟨t, rfl⟩ := hsr
  have e := f.fiberHomeoMorphismRestrict V t
  obtain ⟨heq, hdim⟩ := hV t ⟨e.symm hne.some⟩
  refine ⟨Equidimensional.of_homeomorph e.symm heq, ?_⟩
  rw [← IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph]
  exact hdim

end AlgebraicGeometry

/-- Flatness is local on the target. Mathlib derives this from
`AlgebraicGeometry.HasRingHomProperty`, through an instance that instance search does not find
from here; it is named so that it can be supplied. -/
alias isZariskiLocalAtTarget_flat := Stacks.Descent.flat_isZariskiLocalAtTarget

/-- Local finite type is local on the target; see `isZariskiLocalAtTarget_flat`. -/
theorem isZariskiLocalAtTarget_locallyOfFiniteType :
    IsZariskiLocalAtTarget (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (P := @LocallyOfFiniteType)
    (Q := RingHom.FiniteType)

namespace Stacks.ProjectiveBundle

variable {X : Scheme.{u}} (E : X.Modules) (hqc : IsQuasicoherentPieces E)

/-- **Over an open on which `ℰ` is free of rank `n + 1`, the bundle is the bundle of the free
module.** The part `π ⁻¹ U` of `𝐏(ℰ)` lying over `U` is `𝐏(𝒪_U^{n+1})`, by an isomorphism
carrying the projection of the latter to the restriction of `π`: Tag 01O3's base-change
comparison at the open immersion `U ⟶ X`, followed by the cartesian square of `π ∣_ U`. -/
theorem exists_iso_morphismRestrict_of_restrict_free [E.IsQuasicoherent] (n : ℕ) (U : X.Opens)
    (hfree : Nonempty (E.restrict U.ι ≅
      SheafOfModules.free.{u} (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    ∃ Φ : (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U.toScheme)
        (coordIndex.{u} n)) (isQuasicoherentPieces_free (X := U.toScheme)
          (coordIndex.{u} n)))).scheme ≅
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U).toScheme,
      Φ.hom ≫ ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ∣_ U) =
        (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U.toScheme)
          (coordIndex.{u} n)) (isQuasicoherentPieces_free (X := U.toScheme)
            (coordIndex.{u} n)))).toBase := by
  have hE : freeModule (X := U.toScheme) (coordIndex.{u} n) ≅
      (Scheme.Modules.pullback U.ι).obj E :=
    hfree.some.symm ≪≫ (Scheme.Modules.restrictFunctorIsoPullback U.ι).app E
  obtain ⟨e, he⟩ := AlgebraicGeometry.projectiveBundleBaseChangeComparison U.ι E hqc
    (freeModule (X := U.toScheme) (coordIndex.{u} n)) (isQuasicoherentPieces_free _) hE
  have hsq := isPullback_morphismRestrict (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase U
  let e' : (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U.toScheme)
      (coordIndex.{u} n)) (isQuasicoherentPieces_free (X := U.toScheme)
        (coordIndex.{u} n)))).scheme ≅
      pullback U.ι (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase := e
  have he' : e'.hom ≫ pullback.fst U.ι (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase =
      (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U.toScheme)
        (coordIndex.{u} n)) (isQuasicoherentPieces_free (X := U.toScheme)
          (coordIndex.{u} n)))).toBase := he
  refine ⟨e' ≪≫ hsq.isoPullback.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, IsPullback.isoPullback_inv_fst]
  exact he'

/-- Every point of the base has an open neighbourhood on which a module finite locally free of
rank `r` is free of rank `r`: the pointwise form of Tag 01C6's rank predicate. -/
theorem exists_restrict_free (r : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U), Nonempty (E.restrict U.ι ≅
      SheafOfModules.free.{u} (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) :=
  (AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_iff E r).mpr hE x

/-- **Over a neighbourhood of every point, the projective bundle of a module finite locally free
of rank `n + 1` is the projective bundle of the free module of that rank**, by an isomorphism
over the neighbourhood. -/
theorem exists_iso_morphismRestrict_free (n : ℕ)
    [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U)
      (Φ : (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U.toScheme)
        (coordIndex.{u} n)) (isQuasicoherentPieces_free (X := U.toScheme)
          (coordIndex.{u} n)))).scheme ≅
        ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ⁻¹ᵁ U).toScheme),
      Φ.hom ≫ ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ∣_ U) =
        (relativeProj (schemeSheafGradedAlgebra (freeModule (X := U.toScheme)
          (coordIndex.{u} n)) (isQuasicoherentPieces_free (X := U.toScheme)
            (coordIndex.{u} n)))).toBase := by
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  obtain ⟨U, hxU, hfree⟩ := exists_restrict_free E (n + 1) x
  obtain ⟨Φ, hΦ⟩ := exists_iso_morphismRestrict_of_restrict_free E hqc n U hfree
  exact ⟨U, hxU, Φ, hΦ⟩

/-- A property local on the target, holding for the projection of every free projective bundle
of rank `n + 1`, holds for that of a finite locally free module of that rank. -/
private theorem property_toBase_of_free (P : MorphismProperty Scheme.{u})
    (hP : IsZariskiLocalAtTarget P) (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)]
    (h : ∀ Y : Scheme.{u}, P (freeProjectiveBundle (X := Y) n).toBase) :
    P (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
  intro x
  obtain ⟨U, hxU, Φ, hΦ⟩ := exists_iso_morphismRestrict_free E hqc n x
  refine ⟨U, hxU, ?_⟩
  rw [(Iso.eq_inv_comp Φ).mpr hΦ]
  exact (P.cancel_left_of_respectsIso Φ.inv _).2 (h _)

/-- **Stacks 02TX, the flatness assertion.** The projection of the projective bundle of a module
finite locally free of constant rank is flat. Flatness is local on the base, and over an open
trivialising the module the projection is that of `𝐏(𝒪^{n+1})`, which is flat. -/
theorem flat_toBase (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    Flat (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase :=
  property_toBase_of_free E hqc (@Flat) isZariskiLocalAtTarget_flat.{u} n fun _ => inferInstance

/-- **Stacks 02TX, the finite-type assertion.** The projection of the projective bundle of a
module finite locally free of constant rank is locally of finite type. -/
theorem locallyOfFiniteType_toBase (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    LocallyOfFiniteType (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase :=
  property_toBase_of_free E hqc (@LocallyOfFiniteType)
    isZariskiLocalAtTarget_locallyOfFiniteType.{u} n fun _ => inferInstance

/-- **The projection of the projective bundle of a module finite locally free of constant rank
is proper.** This is `Stacks.ProjectiveBundleSplitting.isProper_schemeProjectiveBundleToBase`,
with the rank hypothesis in place of finite local freeness. -/
theorem isProper_toBase (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    IsProper (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase := by
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E (n + 1)
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  exact Stacks.ProjectiveBundleSplitting.isProper_schemeProjectiveBundleToBase E hqc

/-- **Stacks 02TX, the relative-dimension assertion.** The projection of the projective bundle of
a module finite locally free of constant rank `n + 1` has relative dimension `n`. Relative
dimension is a condition on the fibres, each fibre lies over a trivialising open, and there the
projection is that of `𝐏(𝒪^{n+1})`, of relative dimension `n`. -/
theorem relativeDimension_toBase (n : ℕ)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (n + 1)] :
    haveI := locallyOfFiniteType_toBase E hqc n
    RelativeDimension (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase n := by
  have := locallyOfFiniteType_toBase E hqc n
  refine relativeDimension_of_forall_exists_morphismRestrict _ fun x => ?_
  obtain ⟨U, hxU, Φ, hΦ⟩ := exists_iso_morphismRestrict_free E hqc n x
  have := isZariskiLocalAtTarget_locallyOfFiniteType.{u}
  have hloc : LocallyOfFiniteType
      ((relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (P := @LocallyOfFiniteType) inferInstance U
  refine ⟨U, hxU, hloc, ?_⟩
  have hΦ' : Φ.symm.hom ≫ (freeProjectiveBundle (X := U.toScheme) n).toBase =
      (relativeProj (schemeSheafGradedAlgebra E hqc)).toBase ∣_ U := by
    rw [Iso.symm_hom, (Iso.eq_inv_comp Φ).mpr hΦ]
  exact relativeDimension_of_iso_over Φ.symm _ _ hΦ'
    (relativeDimension_freeProjectiveBundleToBase U.toScheme n)

end Stacks.ProjectiveBundle

end
