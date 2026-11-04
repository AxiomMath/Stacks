module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import StacksFrontier.AlgebraicGeometry.DeRham.ArtinianRigidity.Charts

/-!
# Chart bases of `X` and of the trivial deformation `X'`

Let `A` be an Artinian local ring with a coefficient field `σ`, and let `f : X ⟶ Spec A` be
smooth. An open `V` of a scheme `g : Y ⟶ Spec A` *has étale coordinates* if `Γ(Y, V)` is étale
over a polynomial ring over `Γ(Spec A, ⊤)`, compatibly with `g`. We show that the affine opens of
`X` with étale coordinates whose special fibre lies in the special fibre of such an open of
`X' = X₀ ×_{A/𝔪} Spec A` form a basis of `X`, and symmetrically for `X'`. The key point is that
both special fibres `X₀ ⟶ X` and `X₀ ⟶ X'` are surjective closed immersions, since `Spec A` has
a single point. As a consequence, the projections `q : W_N ⟶ X` and `q' : W_N ⟶ X'` from the
graph neighbourhood are affine.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.DeRhamRigidity

variable {A : CommRingCat.{u}}

/-- An open `V` of a scheme `g : Y ⟶ Spec A` **has étale coordinates** if the map
`Γ(Spec A, ⊤) ⟶ Γ(Y, V)` factors through an étale map from a polynomial ring
`Γ(Spec A, ⊤)[x_1, …, x_d]`. -/
def HasEtaleCoords {Y : Scheme.{u}} (g : Y ⟶ Spec A) (V : Y.Opens) : Prop :=
  ∃ (d : ℕ) (e : MvPolynomial (Fin d) Γ(Spec A, ⊤) →+* Γ(Y, V)),
    e.comp MvPolynomial.C = (g.appLE ⊤ V le_top).hom ∧ e.Etale

/-- Basic opens of an open with étale coordinates have étale coordinates. -/
theorem HasEtaleCoords.basicOpen {Y : Scheme.{u}} {g : Y ⟶ Spec A} {V : Y.Opens}
    (hV : IsAffineOpen V) (h : HasEtaleCoords g V) (s : Γ(Y, V)) :
    HasEtaleCoords g (Y.basicOpen s) := by
  obtain ⟨d, e, he, het⟩ := h
  refine ⟨d, (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom.comp e, ?_, ?_⟩
  · rw [RingHom.comp_assoc, he, ← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (g.appLE_map _ _)
  · have := hV.isLocalization_basicOpen s
    have hloc : (Y.presheaf.map (homOfLE (Y.basicOpen_le s)).op).hom.Etale :=
      RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway s)
    exact RingHom.Etale.stableUnderComposition _ _ het hloc

variable [IsLocalRing A] [IsArtinianRing A]

/-- `Spec A` has a single point, so an open of it containing a point is everything. -/
theorem eq_top_of_mem_specArtinian {U : (Spec A).Opens} {x : Spec A} (hx : x ∈ U) : U = ⊤ := by
  have : Subsingleton (PrimeSpectrum A) := Ring.KrullDimLE.subsingleton_primeSpectrum A
  exact eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum A) x y) ▸ hx

/-- **Charts with étale coordinates.** For `g : Y ⟶ Spec A` smooth, every point of an open `O`
has an affine open neighbourhood inside `O` with étale coordinates. -/
theorem exists_hasEtaleCoords {Y : Scheme.{u}} (g : Y ⟶ Spec A) [Smooth g] {O : Y.Opens} {y : Y}
    (hy : y ∈ O) : ∃ U : Y.Opens, IsAffineOpen U ∧ HasEtaleCoords g U ∧ y ∈ U ∧ U ≤ O := by
  obtain ⟨U₀, -, V, hV, hyV, e, hst⟩ := Smooth.exists_isStandardSmooth g y
  obtain rfl : U₀ = ⊤ := eq_top_of_mem_specArtinian (e hyV)
  obtain ⟨s, hsO, hys⟩ := hV.exists_basicOpen_le ⟨y, hy⟩ hyV
  obtain ⟨d, φ, hφ, hφe⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial hst
  exact ⟨Y.basicOpen s, hV.basicOpen s, HasEtaleCoords.basicOpen hV ⟨d, φ, hφ, hφe⟩ s, hys, hsO⟩


/-- **Nested charts.** Let `g : Y ⟶ Spec A` and `h : Z ⟶ Spec A` be smooth and let `a : P ⟶ Y`
be a surjective closed immersion and `b : P ⟶ Z` any morphism. Then every point of an open
`O ⊆ Y` has an affine neighbourhood `U ⊆ O` with étale coordinates such that `a⁻¹ U ⊆ b⁻¹ V`
for some affine open `V ⊆ Z` with étale coordinates. -/
theorem exists_hasEtaleCoords_nested {Y Z P : Scheme.{u}} (g : Y ⟶ Spec A) (h : Z ⟶ Spec A)
    [Smooth g] [Smooth h] (a : P ⟶ Y) (b : P ⟶ Z) [Surjective a] [IsClosedImmersion a]
    {O : Y.Opens} {y : Y} (hy : y ∈ O) :
    ∃ U : Y.Opens, (IsAffineOpen U ∧ HasEtaleCoords g U ∧ ∃ V : Z.Opens, IsAffineOpen V ∧
      HasEtaleCoords h V ∧ a ⁻¹ᵁ U ≤ b ⁻¹ᵁ V) ∧ y ∈ U ∧ U ≤ O := by
  obtain ⟨p, rfl⟩ := a.surjective y
  obtain ⟨V, hV, hcV, hpV, -⟩ := exists_hasEtaleCoords h (O := ⊤) (y := b p) trivial
  obtain ⟨T, hT, hTe⟩ := a.isClosedEmbedding.isInducing.isOpen_iff.mp (b ⁻¹ᵁ V).isOpen
  have hT' (q : P) : a q ∈ T ↔ q ∈ b ⁻¹ᵁ V := Set.ext_iff.1 hTe q
  obtain ⟨U, hU, hcU, hpU, hUO⟩ := exists_hasEtaleCoords g (O := O ⊓ ⟨T, hT⟩) ⟨hy, (hT' p).2 hpV⟩
  refine ⟨U, ⟨hU, hcU, V, hV, hcV, fun q hq => ?_⟩, hpU, hUO.trans inf_le_left⟩
  exact (hT' q).1 (hUO hq).2

/-- `Spec (A/𝔪) ⟶ Spec A` is surjective, since `Spec A` has a single point. -/
instance surjective_specMap_residueMap : Surjective (Spec.map (residueMap A)) := by
  have : Subsingleton (PrimeSpectrum A) := Ring.KrullDimLE.subsingleton_primeSpectrum A
  refine ⟨fun x => ?_⟩
  obtain ⟨y⟩ := (inferInstance : Nonempty (PrimeSpectrum (A ⧸ maximalIdeal A)))
  exact ⟨y, Subsingleton.elim (α := PrimeSpectrum A) _ _⟩

variable {σ : A ⧸ maximalIdeal A →+* A}
  (hσ : (Ideal.Quotient.mk (maximalIdeal A)).comp σ = RingHom.id _)
  {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- The special fibre `X₀ ⟶ X'` of the trivial deformation is a closed immersion. -/
instance isClosedImmersion_trivialIncl : IsClosedImmersion (trivialIncl hσ f) :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion.{u}) (isPullback_trivialIncl hσ f).flip
    inferInstance

/-- The special fibre `X₀ ⟶ X'` of the trivial deformation is surjective. -/
instance surjective_trivialIncl : Surjective (trivialIncl hσ f) :=
  MorphismProperty.of_isPullback (P := @Surjective.{u}) (isPullback_trivialIncl hσ f).flip
    inferInstance

/-- **The chart basis of `X`**: affine opens `U ⊆ X` with étale coordinates whose special fibre
lies in the special fibre of an affine open `V ⊆ X'` with étale coordinates. -/
theorem isBasis_chartsFst [Smooth f] :
    TopologicalSpace.Opens.IsBasis {U : X.Opens | IsAffineOpen U ∧ HasEtaleCoords f U ∧
      ∃ V : (trivialDef σ f).Opens, IsAffineOpen V ∧ HasEtaleCoords (trivialMap σ f) V ∧
        specialIncl f ⁻¹ᵁ U ≤ trivialIncl hσ f ⁻¹ᵁ V} :=
  TopologicalSpace.Opens.isBasis_iff_nbhd.2 fun hy =>
    exists_hasEtaleCoords_nested f (trivialMap σ f) (specialIncl f) (trivialIncl hσ f) hy

/-- **The chart basis of `X'`**: affine opens `V ⊆ X'` with étale coordinates whose special fibre
lies in the special fibre of an affine open `U ⊆ X` with étale coordinates. -/
theorem isBasis_chartsSnd [Smooth f] :
    TopologicalSpace.Opens.IsBasis {V : (trivialDef σ f).Opens | IsAffineOpen V ∧
      HasEtaleCoords (trivialMap σ f) V ∧ ∃ U : X.Opens, IsAffineOpen U ∧ HasEtaleCoords f U ∧
        trivialIncl hσ f ⁻¹ᵁ V ≤ specialIncl f ⁻¹ᵁ U} :=
  TopologicalSpace.Opens.isBasis_iff_nbhd.2 fun hy =>
    exists_hasEtaleCoords_nested (trivialMap σ f) f (trivialIncl hσ f) (specialIncl f) hy

variable [IsSeparated f] (N : ℕ)

/-- The `0`-th graph neighbourhood is empty. -/
instance isEmpty_graphNbhd_zero : IsEmpty (graphNbhd hσ f 0) := by
  have h : graphIdealSheaf hσ f ^ 0 = ⊤ := by
    ext U
    simp
  unfold graphNbhd
  rw [h]
  infer_instance

/-- **The projection `q : W_N ⟶ X` is affine.** -/
instance isAffineHom_graphNbhdFst [Smooth f] : IsAffineHom (graphNbhdFst hσ f N) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨U, ⟨hU, -, V, hV, -, hUV⟩, hxU, -⟩ :=
    exists_hasEtaleCoords_nested f (trivialMap σ f) (specialIncl f) (trivialIncl hσ f)
      (O := ⊤) (y := x) trivial
  refine ⟨U, hxU, hU, ?_⟩
  rcases eq_or_ne N 0 with rfl | hN
  · convert isAffineOpen_bot _
    exact TopologicalSpace.Opens.ext (Set.eq_empty_of_isEmpty _)
  · rw [← graphNbhdFst_preimage hσ f N hUV hN]
    exact (isAffineOpen_box f hU hV).preimage _

/-- **The projection `q' : W_N ⟶ X'` is affine.** -/
instance isAffineHom_graphNbhdSnd [Smooth f] : IsAffineHom (graphNbhdSnd hσ f N) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨V, ⟨hV, -, U, hU, -, hVU⟩, hxV, -⟩ :=
    exists_hasEtaleCoords_nested (trivialMap σ f) f (trivialIncl hσ f) (specialIncl f)
      (O := ⊤) (y := x) trivial
  refine ⟨V, hxV, hV, ?_⟩
  rcases eq_or_ne N 0 with rfl | hN
  · convert isAffineOpen_bot _
    exact TopologicalSpace.Opens.ext (Set.eq_empty_of_isEmpty _)
  · rw [← graphNbhdSnd_preimage hσ f N hVU hN]
    exact (isAffineOpen_box f hU hV).preimage _

end Stacks.DeRhamRigidity
