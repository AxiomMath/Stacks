module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsEtaleReduction
public import StacksFrontier.AlgebraicGeometry.DeRham.CoordinateConeExceptional
public import StacksCore.Tactic.StacksAttribute

/-!
# The coordinate situation over an affine base

Over an affine base `T` with `R = Γ(T, 𝒪_T)`, the coordinate situation `𝐀^m_T ⊆ 𝐀^{m+n}_T` of
[Stacks, Tag 0FUE] is isomorphic, over `T ≅ Spec R`, to the coordinate subspace
`Spec R[x₁, …, x_m] ⊆ Spec R[x₁, …, x_m, y₁, …, y_n]` of Section 50.16 of the source, in which
[Stacks, Tag 0FUR] is proved. This file records that identification and transports clauses
(1) and (2) of [Stacks, Tag 0FUR] — the case of [Stacks, Tag 0FUU] for the coordinate
situation — to an arbitrary affine base, along it.

## Main results

* `Stacks.DeRham.exists_isPullback_coordinateSubspaceEmbedding_coordinateEmbedding`: the
  identification, as a cartesian square of isomorphisms.
* `Stacks.DeRham.isIso_blowupFormsDirectImage_coordinateSubspaceEmbedding_of_isAffine` and
  `Stacks.DeRham.isIso_exceptionalFormsDirectImage_coordinateSubspaceEmbedding_of_isAffine`:
  clauses (1) and (2) of [Stacks, Tag 0FUU] for the coordinate situation over an affine base,
  for `n ≥ 1`.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_isClosedImmersion
  Stacks.MoreMorphisms.coordinateEmbedding_isClosedImmersion

namespace Stacks.DeRham

section AffineBase

variable (T : Scheme.{u}) [IsAffine T]

/-- The spectra of two polynomial rings whose variables are matched by an equivalence. -/
def specRenameIso {σ : Type u} {τ : Type} (e : σ ≃ τ) :
    Spec (.of (MvPolynomial σ Γ(T, ⊤))) ≅ Spec (.of (MvPolynomial τ Γ(T, ⊤))) where
  hom := Spec.map
    (CommRingCat.ofHom (MvPolynomial.renameEquiv Γ(T, ⊤) e).symm.toRingEquiv.toRingHom)
  inv := Spec.map (CommRingCat.ofHom (MvPolynomial.renameEquiv Γ(T, ⊤) e).toRingEquiv.toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext1
    exact RingHom.ext fun x => (MvPolynomial.renameEquiv Γ(T, ⊤) e).symm_apply_apply x
  inv_hom_id := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext1
    exact RingHom.ext fun x => (MvPolynomial.renameEquiv Γ(T, ⊤) e).apply_symm_apply x

/-- Relative affine `σ`-space over an affine base `T`, as the spectrum of a polynomial ring over
`Γ(T, ⊤)` in variables indexed by `τ`, matched with `σ` by `e : σ ≃ τ`. -/
def affineSpaceIsoSpecRename {σ : Type u} {τ : Type} (e : σ ≃ τ) :
    AffineSpace σ T ≅ Spec (.of (MvPolynomial τ Γ(T, ⊤))) :=
  AffineSpace.isoOfIsAffine _ T ≪≫ specRenameIso T e

/-- The inverse of `affineSpaceIsoSpecRename T e` is the spectrum of the renaming of variables
along `e`, followed by the inverse of `AffineSpace.isoOfIsAffine`. -/
theorem affineSpaceIsoSpecRename_inv {σ : Type u} {τ : Type} (e : σ ≃ τ) :
    (affineSpaceIsoSpecRename T e).inv =
      Spec.map (CommRingCat.ofHom (MvPolynomial.renameEquiv Γ(T, ⊤) e).toRingEquiv.toRingHom) ≫
        (AffineSpace.isoOfIsAffine σ T).inv :=
  rfl

/-- The inverse of `affineSpaceIsoSpecRename T e`, followed by the structure morphism of
`𝔸(σ; T)`, is the spectrum of the constant-coefficient map `C`, followed by `T.isoSpec.inv`. -/
theorem affineSpaceIsoSpecRename_inv_over {σ : Type u} {τ : Type} (e : σ ≃ τ) :
    (affineSpaceIsoSpecRename T e).inv ≫ 𝔸(σ; T) ↘ T =
      Spec.map (CommRingCat.ofHom (C : Γ(T, ⊤) →+* MvPolynomial τ Γ(T, ⊤))) ≫ T.isoSpec.inv := by
  rw [affineSpaceIsoSpecRename_inv, Category.assoc, AffineSpace.isoOfIsAffine_inv_over,
    ← Spec.map_comp_assoc]
  congr 2
  ext r
  simp

/-- `Spec.map φ` pulls the global section `ΓSpecIso.inv a` back to `ΓSpecIso.inv (φ a)`. -/
private theorem appTop_spec_map_ΓSpecIso_inv {A B : CommRingCat.{u}} (φ : A ⟶ B) (a : A) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso B).inv (φ a) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- The inverse of `affineSpaceIsoSpecRename T e` pulls the coordinate function `k` of
`𝔸(σ; T)` back to the global section `X (e k)` of the spectrum of the polynomial ring. -/
theorem affineSpaceIsoSpecRename_inv_appTop_coord {σ : Type u} {τ : Type} (e : σ ≃ τ) (k : σ) :
    (affineSpaceIsoSpecRename T e).inv.appTop (AffineSpace.coord T k) =
      (Scheme.ΓSpecIso (.of (MvPolynomial τ Γ(T, ⊤)))).inv (X (e k)) := by
  rw [affineSpaceIsoSpecRename_inv, Scheme.Hom.comp_appTop]
  simp only [CommRingCat.comp_apply, AffineSpace.isoOfIsAffine_inv_appTop_coord]
  rw [appTop_spec_map_ΓSpecIso_inv]
  congr 1
  simp

/-- **Over an affine base the coordinate subspace of relative affine space is the coordinate
subspace of the spectrum of a polynomial ring.** -/
theorem affineSpaceIsoSpecRename_inv_comp_coordinateSubspaceEmbedding (m n : ℕ) :
    (affineSpaceIsoSpecRename T (Equiv.ulift.{u} (α := Fin m))).inv ≫
        Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding T m n =
      Stacks.MoreMorphisms.coordinateEmbedding Γ(T, ⊤) m n ≫
        (affineSpaceIsoSpecRename T ((Equiv.ulift.{u}.trans finSumFinEquiv.symm :
          ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n))).inv := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Category.assoc, Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_over,
      affineSpaceIsoSpecRename_inv_over, Category.assoc, affineSpaceIsoSpecRename_inv_over,
      Stacks.MoreMorphisms.coordinateEmbedding, ← Spec.map_comp_assoc]
    congr 2
    ext r
    simp [Stacks.MoreMorphisms.coordinateProjection]
  · rintro ⟨k⟩
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
    simp only [CommRingCat.comp_apply]
    rw [Stacks.MoreMorphisms.coordinateEmbedding, affineSpaceIsoSpecRename_inv_appTop_coord,
      appTop_spec_map_ΓSpecIso_inv]
    induction k using Fin.addCases with
    | left j =>
      rw [Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_firstCoordinate,
        affineSpaceIsoSpecRename_inv_appTop_coord]
      congr 1
      simp [Stacks.MoreMorphisms.coordinateProjection]
    | right j =>
      rw [Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_lastCoordinate]
      simp [Stacks.MoreMorphisms.coordinateProjection]

/-- The identification of relative affine space with the spectrum of a polynomial ring lies over
the identification `T ≅ Spec Γ(T, ⊤)`. -/
theorem affineSpaceIsoSpecRename_hom_comp (m n : ℕ) :
    (affineSpaceIsoSpecRename T ((Equiv.ulift.{u}.trans finSumFinEquiv.symm :
      ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n))).hom ≫
        coordinateAmbientToBase Γ(T, ⊤) m n =
      (AffineSpace.over (ULift.{u} (Fin (m + n))) T).hom ≫ T.isoSpec.hom := by
  rw [← Iso.eq_inv_comp, ← Category.assoc,
    show (affineSpaceIsoSpecRename T ((Equiv.ulift.{u}.trans finSumFinEquiv.symm :
          ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n))).inv ≫
        (AffineSpace.over (ULift.{u} (Fin (m + n))) T).hom = _ from
      affineSpaceIsoSpecRename_inv_over T _, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- **The coordinate situation over an affine base is the coordinate situation of Section 50.16**:
a cartesian square of isomorphisms over `T ≅ Spec Γ(T, ⊤)`. -/
theorem isPullback_coordinateSubspaceEmbedding_coordinateEmbedding (m n : ℕ) :
    IsPullback (affineSpaceIsoSpecRename T (Equiv.ulift.{u} (α := Fin m))).hom
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding T m n)
      (Stacks.MoreMorphisms.coordinateEmbedding Γ(T, ⊤) m n)
      (affineSpaceIsoSpecRename T ((Equiv.ulift.{u}.trans finSumFinEquiv.symm :
        ULift.{u} (Fin (m + n)) ≃ Fin m ⊕ Fin n))).hom := by
  refine IsPullback.of_horiz_isIso ⟨?_⟩
  rw [← cancel_epi (affineSpaceIsoSpecRename T (Equiv.ulift.{u} (α := Fin m))).inv,
    Iso.inv_hom_id_assoc, ← Category.assoc,
    affineSpaceIsoSpecRename_inv_comp_coordinateSubspaceEmbedding, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- **Clause (1) of [Stacks, Tag 0FUU] for the coordinate situation over an affine base**, for
`n ≥ 1`: it is clause (1) of [Stacks, Tag 0FUR], transported along the identification with the
coordinate situation of Section 50.16. -/
theorem isIso_blowupFormsDirectImage_coordinateSubspaceEmbedding_of_isAffine (m n : ℕ)
    (hn : 1 ≤ n) (a : ℕ) :
    IsIso (blowupFormsDirectImage (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding T m n)
      (AffineSpace.over (ULift.{u} (Fin (m + n))) T).hom (a : ℤ)) := by
  have := CoordinateCone.quasiCompact_blowUpToBase_coordinateEmbedding Γ(T, ⊤) m n
  exact isIso_blowupFormsDirectImage_of_isPullback (coordinateAmbientToBase Γ(T, ⊤) m n)
    (AffineSpace.over (ULift.{u} (Fin (m + n))) T).hom
    (isPullback_coordinateSubspaceEmbedding_coordinateEmbedding T m n) T.isoSpec.hom
    (affineSpaceIsoSpecRename_hom_comp T m n) a
    (CoordinateCone.isIso_blowupFormsDirectImage_coordinateEmbedding Γ(T, ⊤) m n hn a)

/-- **Clause (2) of [Stacks, Tag 0FUU] for the coordinate situation over an affine base**, for
`n ≥ 1`: it is clause (2) of [Stacks, Tag 0FUR], transported along the identification with the
coordinate situation of Section 50.16. -/
theorem isIso_exceptionalFormsDirectImage_coordinateSubspaceEmbedding_of_isAffine (m n : ℕ)
    (hn : 1 ≤ n) (a : ℕ) :
    IsIso (exceptionalFormsDirectImage (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding T m n)
      (AffineSpace.over (ULift.{u} (Fin (m + n))) T).hom (a : ℤ)) := by
  have := CoordinateCone.quasiCompact_blowUpToBase_coordinateEmbedding Γ(T, ⊤) m n
  exact isIso_exceptionalFormsDirectImage_of_isPullback (coordinateAmbientToBase Γ(T, ⊤) m n)
    (AffineSpace.over (ULift.{u} (Fin (m + n))) T).hom
    (isPullback_coordinateSubspaceEmbedding_coordinateEmbedding T m n) T.isoSpec.hom
    (affineSpaceIsoSpecRename_hom_comp T m n) a
    (CoordinateCone.isIso_exceptionalFormsDirectImage_coordinateEmbedding Γ(T, ⊤) m n hn a)

end AffineBase

/-! ### Restricting the base to an affine open -/

section RestrictBase

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- Over an open `V` of the base, the centre restricted to `f⁻¹(V)` followed by `f` restricted to
`V` is the restriction of `i ≫ f`. -/
theorem restrictCentre_comp_morphismRestrict (V : S.Opens) :
    restrictCentre i (f ⁻¹ᵁ V) ≫ f ∣_ V = (i ≫ f) ∣_ V := by
  rw [morphismRestrict_comp, restrictCentre, Scheme.Hom.resLE_eq_morphismRestrict]

/-- A centre with empty interior restricts to a centre with empty interior. -/
theorem interior_range_restrictCentre (hint : interior (Set.range i.base) = ∅) (U : X.Opens) :
    interior (Set.range (restrictCentre i U).base) = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
  have hopen : IsOpen (U.ι.base '' interior (Set.range (restrictCentre i U).base)) :=
    U.ι.isOpenEmbedding.isOpenMap _ isOpen_interior
  have hsub : U.ι.base '' interior (Set.range (restrictCentre i U).base) ⊆ Set.range i.base := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := interior_subset hy
    refine ⟨(i ⁻¹ᵁ U).ι z, ?_⟩
    have h := congrArg (fun g => g z)
      (Scheme.Hom.resLE_comp_ι i (le_rfl : i ⁻¹ᵁ U ≤ i ⁻¹ᵁ U))
    simp only [Scheme.Hom.comp_apply] at h
    exact h.symm
  have := interior_maximal hsub hopen
  rw [hint] at this
  exact this ⟨x, hx, rfl⟩

/-- The centre restricted over an affine open of the base is smooth over that open. -/
private theorem smooth_restrictCentre_comp_morphismRestrict (V : S.Opens)
    [Smooth (i ≫ f)] :
    Smooth (restrictCentre i (f ⁻¹ᵁ V) ≫ f ∣_ V) := by
  rw [restrictCentre_comp_morphismRestrict]
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_morphismRestrict (i ≫ f) V).flip inferInstance

variable [Smooth f] [Smooth (i ≫ f)]

/-- **[Stacks, Tag 0FUU], clause (1).** Let `f : X ⟶ S` be smooth and let `i : Z ⟶ X` be a closed
immersion with `Z` smooth over `S`, of positive codimension at every point, i.e. containing no
nonempty open subset of `X`. Let `b : X' ⟶ X` be the blowing up of `X` along `Z`. Then for every
`a ≥ 0` the canonical map `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` is an isomorphism.

The positivity of the codimension is not stated in the source, and it is needed: where `Z`
contains an open subset `W` of `X` the ideal of the centre vanishes on `W`, the blowup is empty
over `W` (`AlgebraicGeometry.isEmpty_blowUp_bot`), and `𝒪_W = Ω^0_{W/S} ⟶ b_*Ω^0 = 0` is not an
isomorphism — for instance for `Z = X = S = Spec k`. The source's proof reduces to the
coordinate situation `𝐀^m_S ⊆ 𝐀^{m+n}_S` of Section 50.16, where `n ≥ 1`, and that is exactly
what the hypothesis provides in the charts of [Stacks, Tag 0FUE]. -/
@[stacks 0FUU "clause (1), corrected: false as written when Z contains a nonempty open of X \
(counterexample Z = X = S = Spec k: the blowup is empty and O_X → b_*O = 0), so stated for Z \
containing no nonempty open of X (positive codimension everywhere)"]
theorem isIso_blowupFormsDirectImage_of_smooth (hint : interior (Set.range i.base) = ∅) (a : ℕ) :
    IsIso (blowupFormsDirectImage i f (a : ℤ)) := by
  have := quasiCompact_blowUpToBase_of_smooth f i
  have hcov : ∀ V : S.affineOpens, IsIso ((Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).map
      (blowupFormsDirectImage i f (a : ℤ))) := by
    intro V
    have : IsAffine V.1.toScheme := V.2
    have := smooth_restrictCentre_comp_morphismRestrict f i V.1
    have h := isIso_blowupFormsDirectImage_of_coordinate (f ∣_ V.1)
      (restrictCentre i (f ⁻¹ᵁ V.1)) (interior_range_restrictCentre i hint _) a
      (fun m n hn => isIso_blowupFormsDirectImage_coordinateSubspaceEmbedding_of_isAffine
        V.1.toScheme m n hn a)
    exact isIso_pullback_map_blowupFormsDirectImage_of_isPullback f (f ∣_ V.1)
      (isPullback_restrictCentre i (f ⁻¹ᵁ V.1)) V.1.ι (morphismRestrict_ι f V.1).symm a h
  refine Scheme.Modules.isIso_of_isIso_pullback_ι (fun V : S.affineOpens => f ⁻¹ᵁ V.1) ?_ _ hcov
  rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

/-- **[Stacks, Tag 0FUU], clause (2).** Let `f : X ⟶ S` be smooth and let `i : Z ⟶ X` be a closed
immersion with `Z` smooth over `S`, of positive codimension at every point, i.e. containing no
nonempty open subset of `X`. Let `p : E ⟶ Z` be the projection onto the centre of the
exceptional divisor of the blowing up of `X` along `Z`. Then for every `a ≥ 0` the canonical
map `Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` is an isomorphism.

As for clause (1), the positivity of the codimension is not stated in the source and is needed:
for `Z = X` the exceptional divisor is empty and `𝒪_Z ⟶ p_*𝒪_E = 0` is not an isomorphism. -/
@[stacks 0FUU "clause (2), corrected: false as written when Z contains a nonempty open of X \
(counterexample Z = X = S = Spec k: E is empty and O_Z → p_*O_E = 0), so stated for Z \
containing no nonempty open of X (positive codimension everywhere)"]
theorem isIso_exceptionalFormsDirectImage_of_smooth (hint : interior (Set.range i.base) = ∅)
    (a : ℕ) : IsIso (exceptionalFormsDirectImage i f (a : ℤ)) := by
  have := quasiCompact_blowUpToBase_of_smooth f i
  have hcov : ∀ V : S.affineOpens, IsIso ((Scheme.Modules.pullback (i ⁻¹ᵁ f ⁻¹ᵁ V.1).ι).map
      (exceptionalFormsDirectImage i f (a : ℤ))) := by
    intro V
    have : IsAffine V.1.toScheme := V.2
    have := smooth_restrictCentre_comp_morphismRestrict f i V.1
    have h := isIso_exceptionalFormsDirectImage_of_coordinate (f ∣_ V.1)
      (restrictCentre i (f ⁻¹ᵁ V.1)) (interior_range_restrictCentre i hint _) a
      (fun m n hn => isIso_exceptionalFormsDirectImage_coordinateSubspaceEmbedding_of_isAffine
        V.1.toScheme m n hn a)
    exact isIso_pullback_map_exceptionalFormsDirectImage_of_isPullback f (f ∣_ V.1)
      (isPullback_restrictCentre i (f ⁻¹ᵁ V.1)) V.1.ι (morphismRestrict_ι f V.1).symm a h
  refine Scheme.Modules.isIso_of_isIso_pullback_ι (fun V : S.affineOpens => i ⁻¹ᵁ f ⁻¹ᵁ V.1)
    ?_ _ hcov
  rw [← Scheme.Hom.preimage_iSup, ← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top,
    Scheme.Hom.preimage_top, Scheme.Hom.preimage_top]

end RestrictBase

end Stacks.DeRham

end
