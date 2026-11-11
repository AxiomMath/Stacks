module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-!
# Integrality and local factoriality across two open immersions

Let `M` be an integral scheme which is locally factorial, in the sense that every point has an
affine open neighbourhood whose ring of sections is a unique factorization monoid. Let
`a b : M ⟶ V` be two open immersions and let `V'` be an open subscheme of `V` covered by the
images of `a` and `b`, meeting both. Then `V'` is again integral and locally factorial.

Irreducibility comes from the fact that an open set covered by two irreducible open sets whose
common part inside it is nonempty is irreducible; reducedness is checked on stalks, which are
stalks of `M`; local factoriality is transported along the open immersions, using that a basic
open of an affine open has as ring of sections a localization of the ring of sections of the
affine open.

## Main results

* `AlgebraicGeometry.isIrreducible_of_subset_union_of_isOpen`: the topological statement.
* `AlgebraicGeometry.isIntegral_and_locallyFactorial_of_openImmersions`: the statement above.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A set squeezed between a preirreducible set and its closure is preirreducible. -/
theorem isPreirreducible_of_subset_closure {X : Type*} [TopologicalSpace X] {S T : Set X}
    (hT : IsPreirreducible T) (hTS : T ⊆ S) (hST : S ⊆ closure T) : IsPreirreducible S := by
  intro u v hu hv ⟨x, hxS, hxu⟩ ⟨y, hyS, hyv⟩
  have h₁ : (T ∩ u).Nonempty := (closure_inter_open_nonempty_iff hu).mp ⟨x, hST hxS, hxu⟩
  have h₂ : (T ∩ v).Nonempty := (closure_inter_open_nonempty_iff hv).mp ⟨y, hST hyS, hyv⟩
  obtain ⟨z, hzT, hz⟩ := hT u v hu hv h₁ h₂
  exact ⟨z, hTS hzT, hz⟩

/-- An open set `O` covered by two irreducible open sets `A` and `B` with `O ∩ A ∩ B` nonempty
is irreducible. -/
theorem isIrreducible_of_subset_union_of_isOpen {X : Type*} [TopologicalSpace X]
    {A B O : Set X} (hA : IsIrreducible A) (hB : IsIrreducible B) (hAo : IsOpen A)
    (hBo : IsOpen B) (hO : IsOpen O) (hcov : O ⊆ A ∪ B) (hmeet : (O ∩ A ∩ B).Nonempty) :
    IsIrreducible O := by
  have hT : IsPreirreducible (O ∩ A ∩ B) :=
    hA.2.open_subset ((hO.inter hAo).inter hBo) (fun _ h ↦ h.1.2)
  refine ⟨hmeet.mono (fun _ h ↦ h.1.1), isPreirreducible_of_subset_closure hT
    (fun _ h ↦ h.1.1) ?_⟩
  intro x hxO
  rcases hcov hxO with hxA | hxB
  · have := subset_closure_inter_of_isPreirreducible_of_isOpen hA.2 (hO.inter hBo)
      (by obtain ⟨z, ⟨hzO, hzA⟩, hzB⟩ := hmeet; exact ⟨z, hzA, hzO, hzB⟩) hxA
    refine closure_mono (fun z hz ↦ ?_) this
    exact ⟨⟨hz.2.1, hz.1⟩, hz.2.2⟩
  · have := subset_closure_inter_of_isPreirreducible_of_isOpen hB.2 (hO.inter hAo)
      (by obtain ⟨z, ⟨hzO, hzA⟩, hzB⟩ := hmeet; exact ⟨z, hzB, hzO, hzA⟩) hxB
    refine closure_mono (fun z hz ↦ ?_) this
    exact ⟨⟨hz.2.1, hz.2.2⟩, hz.1⟩

/-- The stalk of the target of an open immersion out of a reduced scheme, at a point of the
image, is reduced. -/
theorem isReduced_stalk_of_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsReduced X] {y : Y} (hy : y ∈ Set.range f) : _root_.IsReduced (Y.presheaf.stalk y) := by
  obtain ⟨x, rfl⟩ := hy
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact isReduced_of_injective e e.injective

/-- Local factoriality transported along an open immersion: if `a : M ⟶ V` is an open
immersion out of a locally factorial scheme and `x` is a point of an open `V'` of `V` lying in
the image of `a`, then `x` has an affine open neighbourhood in `V'` whose ring of sections is a
unique factorization monoid. -/
theorem exists_affineOpens_uniqueFactorizationMonoid_of_isOpenImmersion {M V : Scheme.{u}}
    (hufd : ∀ x : M, ∃ U : M.affineOpens, x ∈ (U : Set M) ∧ UniqueFactorizationMonoid Γ(M, U))
    (a : M ⟶ V) [IsOpenImmersion a] (V' : V.Opens) (x : V'.toScheme) (m : M)
    (hm : a m = V'.ι x) :
    ∃ U : V'.toScheme.affineOpens, x ∈ (U : Set V'.toScheme) ∧
      UniqueFactorizationMonoid Γ(V'.toScheme, U) := by
  obtain ⟨U, hmU, hU⟩ := hufd m
  have hmV' : m ∈ a ⁻¹ᵁ V' := by
    change a m ∈ V'
    rw [hm]
    exact x.2
  obtain ⟨f, hfle, hmf⟩ := U.2.exists_basicOpen_le (V := a ⁻¹ᵁ V') ⟨m, hmV'⟩ hmU
  have : IsLocalization.Away f Γ(M, M.basicOpen f) := U.2.isLocalization_basicOpen f
  have hD : UniqueFactorizationMonoid Γ(M, M.basicOpen f) :=
    UniqueFactorizationMonoid.of_isLocalization (Submonoid.powers f) _
  have hWle : a ''ᵁ M.basicOpen f ≤ V' := (a.image_mono hfle).trans (a.image_preimage_le V')
  have hWaff : IsAffineOpen (a ''ᵁ M.basicOpen f) :=
    (U.2.basicOpen f).image_of_isOpenImmersion a
  have heq : V'.ι ''ᵁ (V'.ι ⁻¹ᵁ (a ''ᵁ M.basicOpen f)) = a ''ᵁ M.basicOpen f := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hWle
  have key : ∀ W : V.Opens, W = a ''ᵁ M.basicOpen f → UniqueFactorizationMonoid Γ(V, W) := by
    rintro _ rfl
    exact (a.appIso (M.basicOpen f)).symm.commRingCatIsoToRingEquiv.toMulEquiv
      |>.uniqueFactorizationMonoid hD
  refine ⟨⟨V'.ι ⁻¹ᵁ (a ''ᵁ M.basicOpen f),
    hWaff.preimage_of_isOpenImmersion V'.ι (by rwa [Scheme.Opens.opensRange_ι])⟩, ?_, ?_⟩
  · change V'.ι x ∈ a ''ᵁ M.basicOpen f
    rw [← hm]
    exact Set.mem_image_of_mem _ hmf
  · exact (V'.ι.appIso _).commRingCatIsoToRingEquiv.toMulEquiv.uniqueFactorizationMonoid
      (key _ heq)

/-- Let `M` be an integral, locally factorial scheme, `a b : M ⟶ V` open immersions and `V'`
an open of `V` covered by the images of `a` and `b` and meeting both. Then `V'` is integral and
locally factorial. -/
theorem isIntegral_and_locallyFactorial_of_openImmersions {M V : Scheme.{u}} [IsIntegral M]
    (hufd : ∀ x : M, ∃ U : M.affineOpens, x ∈ (U : Set M) ∧ UniqueFactorizationMonoid Γ(M, U))
    (a b : M ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b] (V' : V.Opens)
    (hcover : (V' : Set V) ⊆ Set.range a ∪ Set.range b)
    (hmeet : ((V' : Set V) ∩ Set.range a ∩ Set.range b).Nonempty) :
    IsIntegral V'.toScheme ∧
      ∀ x : V'.toScheme, ∃ U : V'.toScheme.affineOpens, x ∈ (U : Set V'.toScheme) ∧
        UniqueFactorizationMonoid Γ(V'.toScheme, U) := by
  refine ⟨?_, fun x ↦ ?_⟩
  · have hirr : IsIrreducible (V' : Set V) :=
      isIrreducible_of_subset_union_of_isOpen
        (by simpa only [Set.image_univ] using
          (IrreducibleSpace.isIrreducible_univ M).image a a.continuous.continuousOn)
        (by simpa only [Set.image_univ] using
          (IrreducibleSpace.isIrreducible_univ M).image b b.continuous.continuousOn)
        a.isOpenEmbedding.isOpen_range b.isOpenEmbedding.isOpen_range V'.isOpen hcover hmeet
    have : IrreducibleSpace V'.toScheme := Subtype.irreducibleSpace hirr
    have : ∀ x : V'.toScheme, _root_.IsReduced (V'.toScheme.presheaf.stalk x) := by
      intro x
      have : _root_.IsReduced (V.presheaf.stalk (V'.ι x)) := by
        rcases hcover x.2 with hx | hx
        · exact isReduced_stalk_of_isOpenImmersion a hx
        · exact isReduced_stalk_of_isOpenImmersion b hx
      let e := (asIso (V'.ι.stalkMap x)).commRingCatIsoToRingEquiv
      exact isReduced_of_injective e.symm e.symm.injective
    have : IsReduced V'.toScheme := isReduced_of_isReduced_stalk _
    exact isIntegral_of_irreducibleSpace_of_isReduced _
  · rcases hcover x.2 with ⟨m, hm⟩ | ⟨m, hm⟩
    · exact exists_affineOpens_uniqueFactorizationMonoid_of_isOpenImmersion hufd a V' x m hm
    · exact exists_affineOpens_uniqueFactorizationMonoid_of_isOpenImmersion hufd b V' x m hm

end AlgebraicGeometry
