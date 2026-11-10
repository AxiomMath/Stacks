module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.RegularPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularBoundedCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.CohomologyGapSplitting
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.PerfectFibreBands
public import StacksFrontier.AlgebraicGeometry.TwistedSheaf.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.SchemeModules
public import StacksFrontier.CategoryTheory.Preadditive.AdditiveFunctorBiprod

/-!
# Splitting a sequence of perfect complexes into a stable and a receding band

Let `W` be a regular Noetherian scheme of finite dimension `d`, let `m` be a natural number and
let `K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` be a sequence of perfect objects of `D(𝒪_W)` whose cohomology is
concentrated in the union of the *stable band* `[-m, m]` and the *receding band* `[-m-n, m-n]`,
and whose transition maps are isomorphisms on cohomology throughout the stable band once
`n > 2m`. Then for all `n > 2m + d` the object `Kₙ` is the direct sum of a perfect object `A`
concentrated in `[-m, m]` and independent of `n`, and a perfect object `Cₙ` concentrated in
`[-m-n, m-n]`, compatibly with the transition maps: each `tₙ` is the direct sum of an
automorphism of `A` and a morphism `Cₙ ⟶ Cₙ₊₁`.

Once `n > 2m + d` the two bands are separated by a gap of `d` consecutive degrees, so
[Stacks, Tag 0FZ4] splits `Kₙ` as `τ^{≤ -m-1} Kₙ ⊕ τ^{≥ -m} Kₙ`; the first summand carries the
receding band and the second the stable band. The stable summands for different `n` are
identified by the truncations `τ^{≥ -m}(tₙ)` of the transition maps, which are isomorphisms
because they are so on cohomology. Compatibility holds for *any* choice of splitting, because
both off-diagonal components of a transition map vanish: the component `Cₙ ⟶ A` because the
receding band lies strictly below the stable one, which the `t`-structure already sees, and the
component `A ⟶ Cₙ₊₁` by the `Hom`-vanishing of [Stacks, Tag 0FZ3] part (2).

## Main definitions

* `AlgebraicGeometry.InBands` is the union of the stable band `[-m, m]` and the receding band
  `[-m-n, m-n]`, as a predicate on degrees.

## Main results

* `AlgebraicGeometry.exists_stable_biprod_of_isRegular` is the splitting, on a regular Noetherian
  scheme of finite dimension.
* `AlgebraicGeometry.exists_stable_biprod_of_smooth` is the splitting for the product of two
  schemes smooth, quasi-compact and locally of finite type over a field, which is where the
  regularity, the Noetherian property and the finiteness of the dimension come from.
* `AlgebraicGeometry.isNoetherian_pullback_of_smooth` and
  `AlgebraicGeometry.exists_topologicalKrullDim_eq_natCast_of_locallyOfFiniteType` supply the
  two standing properties of that product which are not instances.

## Implementation notes

Two hypotheses of the two main results are not proved here. They are stated so as to be
literally the conclusions of the two cohomological assertions about the sequence that precede
the splitting in the source, and are therefore meant to be discharged by applying those
assertions, not assumed about the sequence at hand.

* `hband`, the *kernel-level band vanishing*: for every `n` and every degree `i` outside
  `InBands m n`, the cohomology sheaf `H^i(Kₙ)` vanishes.
* `hstable`, the *stable-band transition isomorphisms*: for every `n > 2m` and every `i` in the
  stable band `[-m, m]`, the map `H^i(tₙ)` is an isomorphism.

Everything else is either proved here or carried with a justification.

* `hvan` is `AlgebraicGeometry.SeparatedCohomologyHomVanishing`, the `Hom`-vanishing of
  [Stacks, Tag 0FZ3] part (2). It is already the hypothesis of
  `AlgebraicGeometry.exists_iso_biprod_truncLE_truncGE`, the form of [Stacks, Tag 0FZ4] used
  here, so carrying it adds nothing to what that result needs anyway; being a statement about
  arbitrary pairs of bounded complexes with coherent cohomology, it says nothing about the
  sequence `Kₙ`.
* `hperf`, perfectness of each `Kₙ`, is the source's standing hypothesis that the sequence lies
  in `D_perf(𝒪_W)`. Through [Stacks, Tag 0FDC] it supplies the boundedness and the coherence of
  the cohomology that [Stacks, Tag 0FZ4] consumes, and it comes back for the two summands, which
  are again bounded with coherent cohomology.
* The dimension of the scheme enters as a natural number `d` with `topologicalKrullDim W = d`.
  For a product of two quasi-compact schemes locally of finite type over a field this holds as
  soon as the product is nonempty, which is why `exists_stable_biprod_of_smooth` assumes the
  product nonempty: on the empty product the dimension is `⊥` and no such `d` exists.
* `exists_stable_biprod_of_smooth` also takes `IsNoetherian (X ×_k Y)` as an instance, because
  the statement of `SeparatedCohomologyHomVanishing` needs it. It is not a redundant assumption
  in substance: `isNoetherian_pullback_of_smooth` derives it from the other hypotheses.

The source's equality `Kₙ = A ⊕ Cₙ` is read as the existence of an isomorphism, since the
splitting of a triangle is not canonical. The witnesses are explicit: `A` is the stable
truncation `τ^{≥ -m} K_N` at the first admissible index `N = 2m + d + 1`, and `Cₙ` is the
receding truncation `τ^{≤ -m-1} Kₙ`. With these choices the automorphism of `A` attached to a
transition map is forced to be an isomorphism, but not to be the identity, because the splitting
isomorphisms are chosen independently for each `n`.

## References

* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
* [Stacks Project, Tag 0FZ4](https://stacks.math.columbia.edu/tag/0FZ4)
* [Stacks Project, Tag 0FZ3](https://stacks.math.columbia.edu/tag/0FZ3)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 056S](https://stacks.math.columbia.edu/tag/056S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Generalities on biproducts and zero objects -/

/-- A morphism between two zero objects is an isomorphism. -/
public theorem isIso_of_isZero_of_isZero {C : Type*} [Category C] [Limits.HasZeroMorphisms C]
    {A B : C} (hA : Limits.IsZero A) (hB : Limits.IsZero B) (φ : A ⟶ B) : IsIso φ :=
  ⟨0, hA.eq_of_src _ _, hB.eq_of_tgt _ _⟩

/-- A morphism of biproducts whose two off-diagonal components vanish is the direct sum of its
two diagonal components. -/
public theorem eq_biprod_map_of_offDiag_eq_zero {C : Type*} [Category C] [Preadditive C]
    {A₁ B₁ A₂ B₂ : C} [Limits.HasBinaryBiproduct A₁ B₁] [Limits.HasBinaryBiproduct A₂ B₂]
    (φ : A₁ ⊞ B₁ ⟶ A₂ ⊞ B₂) (h₁ : biprod.inl ≫ φ ≫ biprod.snd = 0)
    (h₂ : biprod.inr ≫ φ ≫ biprod.fst = 0) :
    φ = biprod.map (biprod.inl ≫ φ ≫ biprod.fst) (biprod.inr ≫ φ ≫ biprod.snd) := by
  refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
    simp [h₁, h₂]

/-! ### Coherence of the cohomology of a truncation -/


/-- A zero sheaf of modules is coherent. -/
public theorem isCoherent_of_isZero_modules {W : Scheme.{u}} {M : W.Modules}
    (hM : Limits.IsZero M) : M.IsCoherent :=
  have := CoherentAbelian.coherentModules_containsZero (R := W.ringCatSheaf)
  have := CoherentAbelian.coherentModules_isClosedUnderIsomorphisms (R := W.ringCatSheaf)
  ObjectProperty.prop_of_isZero (P := fun M : SheafOfModules W.ringCatSheaf => M.IsCoherent) hM

/-- Truncating from below preserves coherence of the cohomology: at and above the truncation
degree the cohomology is that of the object, and below it the cohomology vanishes. -/
public theorem isCoherent_homology_obj_truncGE {W : Scheme.{u}}
    (K : DerivedCategory W.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W.Modules i).obj K).IsCoherent) (c i : ℤ) :
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((DerivedCategory.TStructure.t.truncGE c).obj K)).IsCoherent := by
  by_cases hic : c ≤ i
  · have := DerivedCategory.isIso_homologyMap_truncGEπ_app c i hic K
    exact AlgebraicGeometry.isCoherent_of_moduleIso
      (asIso ((DerivedCategory.homologyFunctor W.Modules i).map
        ((DerivedCategory.TStructure.t.truncGEπ c).app K))) (hK i)
  · exact isCoherent_of_isZero_modules (DerivedCategory.isZero_of_isGE _ c i (by omega))

/-- Truncating from above preserves coherence of the cohomology: below the truncation degree the
cohomology is that of the object, and above it the cohomology vanishes. -/
public theorem isCoherent_homology_obj_truncLE {W : Scheme.{u}}
    (K : DerivedCategory W.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W.Modules i).obj K).IsCoherent) (c i : ℤ) :
    ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE c).obj K)).IsCoherent := by
  by_cases hic : i ≤ c
  · have : IsIso ((DerivedCategory.homologyFunctor W.Modules i).map
        ((DerivedCategory.TStructure.t.truncLEι c).app K)) := by
      change IsIso ((DerivedCategory.homologyFunctor W.Modules i).map
        ((DerivedCategory.TStructure.t.truncLTι (c + 1)).app K))
      exact DerivedCategory.isIso_homologyMap_truncLTι_app (c + 1) i (by omega) K
    exact AlgebraicGeometry.isCoherent_of_moduleIso
      (asIso ((DerivedCategory.homologyFunctor W.Modules i).map
        ((DerivedCategory.TStructure.t.truncLEι c).app K))).symm (hK i)
  · exact isCoherent_of_isZero_modules (DerivedCategory.isZero_of_isLE _ c i (by omega))

/-! ### The two bands -/

/-- **The stable truncation is concentrated in the stable band.** If the cohomology of `K` lives
in the two bands, that of `τ^{≥ -m} K` lives in `[-m, m]`: below `-m` the truncation has no
cohomology at all, and above `m` its cohomology is that of `K`, in degrees outside both bands. -/
public theorem isZero_homology_truncGE_of_band_vanishing {W : Scheme.{u}} (m n : ℕ)
    (K : DerivedCategory W.Modules)
    (hK : ∀ i : ℤ, ¬ InBands m n i →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj K))
    (i : ℤ) (hi : i < -(m : ℤ) ∨ (m : ℤ) < i) :
    Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj K)) := by
  rcases hi with hi | hi
  · exact DerivedCategory.isZero_of_isGE _ (-(m : ℤ)) i hi
  · have := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(m : ℤ)) i (by omega) K
    refine (hK i ?_).of_iso (asIso ((DerivedCategory.homologyFunctor W.Modules i).map
      ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K))).symm
    rintro (⟨-, h⟩ | ⟨-, h⟩) <;> omega

/-- **The receding truncation is concentrated in the receding band.** If the cohomology of `K`
lives in the two bands, that of `τ^{≤ -m-1} K` lives in `[-m-n, m-n]`: in the degrees it retains
its cohomology is that of `K`, and the degrees outside the receding band that it retains are
outside both bands. -/
public theorem isZero_homology_truncLE_of_band_vanishing {W : Scheme.{u}} (m n : ℕ)
    (K : DerivedCategory W.Modules)
    (hK : ∀ i : ℤ, ¬ InBands m n i →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj K))
    (i : ℤ) (hi : i < -(m : ℤ) - (n : ℤ) ∨ (m : ℤ) - (n : ℤ) < i) :
    Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE (-(m : ℤ) - 1)).obj K)) := by
  by_cases hic : i ≤ -(m : ℤ) - 1
  · have : IsIso ((DerivedCategory.homologyFunctor W.Modules i).map
        ((DerivedCategory.TStructure.t.truncLEι (-(m : ℤ) - 1)).app K)) := by
      change IsIso ((DerivedCategory.homologyFunctor W.Modules i).map
        ((DerivedCategory.TStructure.t.truncLTι (-(m : ℤ) - 1 + 1)).app K))
      exact DerivedCategory.isIso_homologyMap_truncLTι_app (-(m : ℤ) - 1 + 1) i (by omega) K
    refine (hK i ?_).of_iso (asIso ((DerivedCategory.homologyFunctor W.Modules i).map
      ((DerivedCategory.TStructure.t.truncLEι (-(m : ℤ) - 1)).app K)))
    rcases hi with hi | hi
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega
    · rintro (⟨h, -⟩ | ⟨-, h⟩) <;> omega
  · exact DerivedCategory.isZero_of_isLE _ (-(m : ℤ) - 1) i (by omega)

/-- **The stable truncations of the terms of the sequence are identified by its transition
maps.** A morphism which is an isomorphism on cohomology throughout the stable band, between two
objects whose cohomology lives in the two bands, has an isomorphism for its stable truncation:
outside `[-m, m]` both stable truncations have vanishing cohomology, and inside it the stable
truncations have the cohomology of the objects themselves. -/
public theorem isIso_truncGE_map_of_band_vanishing {W : Scheme.{u}} (m n : ℕ)
    (K L : DerivedCategory W.Modules) (φ : K ⟶ L)
    (hK : ∀ i : ℤ, ¬ InBands m n i →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj K))
    (hL : ∀ i : ℤ, ¬ InBands m (n + 1) i →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj L))
    (hφ : ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor W.Modules i).map φ)) :
    IsIso ((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).map φ) := by
  rw [DerivedCategory.isIso_iff]
  intro i
  by_cases hi : i < -(m : ℤ) ∨ (m : ℤ) < i
  · exact isIso_of_isZero_of_isZero
      (isZero_homology_truncGE_of_band_vanishing m n K hK i hi)
      (isZero_homology_truncGE_of_band_vanishing m (n + 1) L hL i hi) _
  · push Not at hi
    obtain ⟨hi₁, hi₂⟩ := hi
    have := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(m : ℤ)) i hi₁ K
    have := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(m : ℤ)) i hi₁ L
    have := hφ i hi₁ hi₂
    have hnat : (DerivedCategory.homologyFunctor W.Modules i).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K) ≫
        (DerivedCategory.homologyFunctor W.Modules i).map
          ((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).map φ) =
        (DerivedCategory.homologyFunctor W.Modules i).map φ ≫
        (DerivedCategory.homologyFunctor W.Modules i).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app L) := by
      rw [← Functor.map_comp, ← Functor.map_comp,
        ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).naturality φ).symm]
      rfl
    exact IsIso.of_isIso_fac_left hnat

/-! ### Compatibility of a transition map with the splitting -/

/-- **A morphism between two objects split into a common stable band and two separated receding
bands is the direct sum of an isomorphism of the stable parts and a morphism of the receding
parts.** The off-diagonal component from the receding part of the source to the stable part of
the target vanishes because the receding band lies strictly below the stable one; the one from
the stable part of the source to the receding part of the target vanishes by the `Hom`-vanishing
of [Stacks, Tag 0FZ3] part (2), which is the hypothesis `hvan`. The stable component is an
isomorphism because it is one on cohomology: outside `[-m, m]` the stable part has no cohomology,
and inside it the receding parts have none, so the cohomology of the stable component is that of
the morphism itself. -/
public theorem exists_iso_biprod_map_of_separated_bands {W : Scheme.{u}} [IsNoetherian W]
    (hW : IsRegular W) (d : ℕ) (hd : topologicalKrullDim ↥W = (d : WithBot ℕ∞))
    (hvan : SeparatedCohomologyHomVanishing W d) (m n : ℕ) (hn : 2 * m + d < n)
    (A C₁ C₂ : DerivedCategory W.Modules)
    (hAbdd : DerivedCategory.TStructure.t.bounded A)
    (hC₂bdd : DerivedCategory.TStructure.t.bounded C₂)
    (hAcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W.Modules i).obj A).IsCoherent)
    (hC₂coh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W.Modules i).obj C₂).IsCoherent)
    (hAGE : DerivedCategory.TStructure.t.IsGE A (-(m : ℤ)))
    (hAzero : ∀ i : ℤ, (i < -(m : ℤ) ∨ (m : ℤ) < i) →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj A))
    (hC₁zero : ∀ i : ℤ, (m : ℤ) - (n : ℤ) < i →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj C₁))
    (hC₂zero : ∀ i : ℤ, (m : ℤ) - (n : ℤ) - 1 < i →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj C₂))
    (K L : DerivedCategory W.Modules) (φ : K ⟶ L)
    (hφ : ∀ i : ℤ, -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor W.Modules i).map φ))
    (ε : K ≅ A ⊞ C₁) (δ : L ≅ A ⊞ C₂) :
    ∃ (a : A ≅ A) (c : C₁ ⟶ C₂), φ ≫ δ.hom = ε.hom ≫ biprod.map a.hom c := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : A ⊞ C₁ ⟶ A ⊞ C₂, ψ = ε.inv ≫ φ ≫ δ.hom := ⟨_, rfl⟩
  have hC₁LE : DerivedCategory.TStructure.t.IsLE C₁ ((m : ℤ) - (n : ℤ)) :=
    (DerivedCategory.isLE_iff C₁ ((m : ℤ) - (n : ℤ))).2 hC₁zero
  have h₂ : biprod.inr ≫ ψ ≫ biprod.fst = 0 :=
    DerivedCategory.TStructure.t.zero_of_isLE_of_isGE _ ((m : ℤ) - (n : ℤ)) (-(m : ℤ))
      (by omega) hC₁LE hAGE
  have h₁ : biprod.inl ≫ ψ ≫ biprod.snd = 0 :=
    have hsub : Subsingleton (A ⟶ C₂) :=
      hvan hW hd A C₂ hAbdd hC₂bdd hAcoh hC₂coh ((m : ℤ) - (n : ℤ))
        (fun i hi => hAzero i (Or.inl (by omega))) fun i hi => hC₂zero i (by omega)
    hsub.elim _ _
  have hmap := eq_biprod_map_of_offDiag_eq_zero ψ h₁ h₂
  have hiso : IsIso (biprod.inl ≫ ψ ≫ biprod.fst) := by
    rw [DerivedCategory.isIso_iff]
    intro i
    by_cases hi : i < -(m : ℤ) ∨ (m : ℤ) < i
    · exact isIso_of_isZero_of_isZero (hAzero i hi) (hAzero i hi) _
    · push Not at hi
      obtain ⟨hi₁, hi₂⟩ := hi
      have := isIso_map_biprod_inl_of_isZero (DerivedCategory.homologyFunctor W.Modules i)
        (A := A) (B := C₁) (hC₁zero i (by omega))
      have := isIso_map_biprod_fst_of_isZero (DerivedCategory.homologyFunctor W.Modules i)
        (A := A) (B := C₂) (hC₂zero i (by omega))
      have := hφ i hi₁ hi₂
      have : IsIso ((DerivedCategory.homologyFunctor W.Modules i).map ψ) := by
        rw [hψ, Functor.map_comp, Functor.map_comp]
        infer_instance
      rw [Functor.map_comp, Functor.map_comp]
      infer_instance
  refine ⟨asIso (biprod.inl ≫ ψ ≫ biprod.fst), biprod.inr ≫ ψ ≫ biprod.snd, ?_⟩
  rw [asIso_hom, ← hmap, hψ, Iso.hom_inv_id_assoc]

/-! ### The dimension of a nonempty scheme of finite type over a field -/

/-- **A nonempty quasi-compact scheme locally of finite type over a field has dimension a natural
number.** The dimension is not `⊤` because the scheme is quasi-compact and locally of finite type
over a field, and not `⊥` because it is nonempty, so the closure of a point is an irreducible
closed subset. -/
public theorem exists_topologicalKrullDim_eq_natCast_of_locallyOfFiniteType (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [CompactSpace ↥X]
    (hX : Nonempty ↥X) :
    ∃ n : ℕ, topologicalKrullDim ↥X = (n : WithBot ℕ∞) := by
  have hne : topologicalKrullDim ↥X ≠ ⊤ :=
    topologicalKrullDim_ne_top_of_locallyOfFiniteType k p
  have hnn : (0 : WithBot ℕ∞) ≤ topologicalKrullDim ↥X :=
    have : Nonempty (IrreducibleCloseds ↥X) :=
      ⟨⟨closure {Classical.arbitrary ↥X}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    Order.krullDim_nonneg
  have hbot : topologicalKrullDim ↥X ≠ ⊥ := fun hb => by simp [hb] at hnn
  obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hytop : y ≠ ⊤ := by
    intro ht
    apply hne
    rw [← hy, ht]
    rfl
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hytop
  refine ⟨n, ?_⟩
  rw [← hy, ← hn]
  rfl

/-- **The product of two schemes smooth, quasi-compact and locally of finite type over a field is
a Noetherian scheme.** It is regular by [Stacks, Tag 056S], hence locally Noetherian, and it is
quasi-compact over the quasi-compact base. -/
public theorem isNoetherian_pullback_of_smooth (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    [Smooth f] [Smooth g] :
    IsNoetherian (pullback f g) :=
  have : CompactSpace ↥(pullback f g) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f g ≫ f)
  isNoetherian_of_isRegular (isRegular_of_smooth_over_field (pullback.fst f g ≫ f))

/-! ### The splitting -/

/-- **The splitting of a sequence of perfect complexes into a stable and a receding band.** Let
`W` be a regular Noetherian scheme of dimension `d`, let `m : ℕ` and let `K₀ ⟶ K₁ ⟶ ⋯` be a
sequence of perfect objects of `D(𝒪_W)` whose cohomology lives in the stable band `[-m, m]`
together with the receding band `[-m-n, m-n]`, and whose transition maps are isomorphisms on
cohomology throughout the stable band once `n > 2m`. Then for `n > 2m + d` the object `Kₙ` is the
direct sum of a perfect object `A` concentrated in `[-m, m]` and independent of `n`, and a
perfect object `Cₙ` concentrated in `[-m-n, m-n]`, and each transition map is the direct sum of
an automorphism of `A` and a morphism `Cₙ ⟶ Cₙ₊₁`.

The witnesses are `A = τ^{≥ -m} K_N` for `N = 2m + d + 1` and `Cₙ = τ^{≤ -m-1} Kₙ`. -/
public theorem exists_stable_biprod_of_isRegular {W : Scheme.{u}} [IsNoetherian W]
    (hW : IsRegular W) (d : ℕ) (hd : topologicalKrullDim ↥W = (d : WithBot ℕ∞))
    (hvan : SeparatedCohomologyHomVanishing W d)
    (K : ℕ → DerivedCategory W.Modules) (t : ∀ n, K n ⟶ K (n + 1)) (m : ℕ)
    (hperf : ∀ n, RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) (K n))
    (hband : ∀ (n : ℕ) (i : ℤ), ¬ InBands m n i →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj (K n)))
    (hstable : ∀ (n : ℕ) (i : ℤ), 2 * m < n → -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor W.Modules i).map (t n))) :
    ∃ (N : ℕ) (A : DerivedCategory W.Modules) (C : ℕ → DerivedCategory W.Modules),
      RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) A ∧
      (∀ n, N ≤ n → RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace) (C n)) ∧
      (∀ i : ℤ, (i < -(m : ℤ) ∨ (m : ℤ) < i) →
        Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj A)) ∧
      (∀ n, N ≤ n → ∀ i : ℤ, (i < -(m : ℤ) - (n : ℤ) ∨ (m : ℤ) - (n : ℤ) < i) →
        Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj (C n))) ∧
      ∃ e : (∀ n : ℕ, N ≤ n → (K n ≅ A ⊞ C n)),
        ∀ (n : ℕ) (hn : N ≤ n),
          ∃ (a : A ≅ A) (c : C n ⟶ C (n + 1)),
            t n ≫ (e (n + 1) (by omega)).hom = (e n hn).hom ≫ biprod.map a.hom c := by
  let hDC : HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} W.toRingedSpace) :=
    HasDerivedCategory.standard W.Modules
  -- Boundedness and coherence of each term of the sequence, from perfectness through Tag 0FDC.
  have hbc : ∀ n, DerivedCategoryB.derivedCategoryBBounded
      (fun M : W.Modules => M.IsCoherent) (K n) := fun n =>
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect_of_isRegular
      W hW (K n) (hperf n)
  have hKcoh : ∀ (n : ℕ) (i : ℤ),
      ((DerivedCategory.homologyFunctor W.Modules i).obj (K n)).IsCoherent := fun n => (hbc n).2
  have hKbdd : ∀ n, DerivedCategory.TStructure.t.bounded (K n) := by
    intro n
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ := hbc n
    exact ⟨⟨a, (DerivedCategory.isGE_iff (K n) a).2 ha⟩,
      ⟨b, (DerivedCategory.isLE_iff (K n) b).2 hb⟩⟩
  -- The band concentration of the two families of truncations.
  have hAzero : ∀ i : ℤ, (i < -(m : ℤ) ∨ (m : ℤ) < i) →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj
        ((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj (K (2 * m + d + 1)))) :=
    fun i hi => isZero_homology_truncGE_of_band_vanishing m (2 * m + d + 1)
      (K (2 * m + d + 1)) (hband (2 * m + d + 1)) i hi
  have hCzero : ∀ (n : ℕ) (i : ℤ), (i < -(m : ℤ) - (n : ℤ) ∨ (m : ℤ) - (n : ℤ) < i) →
      Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj
        ((DerivedCategory.TStructure.t.truncLE (-(m : ℤ) - 1)).obj (K n))) :=
    fun n i hi => isZero_homology_truncLE_of_band_vanishing m n (K n) (hband n) i hi
  -- Coherence of the cohomology of the two families of truncations.
  have hAcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj (K (2 * m + d + 1)))).IsCoherent :=
    fun i => isCoherent_homology_obj_truncGE (K (2 * m + d + 1)) (hKcoh (2 * m + d + 1))
      (-(m : ℤ)) i
  have hCcoh : ∀ (n : ℕ) (i : ℤ), ((DerivedCategory.homologyFunctor W.Modules i).obj
      ((DerivedCategory.TStructure.t.truncLE (-(m : ℤ) - 1)).obj (K n))).IsCoherent :=
    fun n i => isCoherent_homology_obj_truncLE (K n) (hKcoh n) (-(m : ℤ) - 1) i
  -- Boundedness of the two families of truncations.
  have hAbdd : DerivedCategory.TStructure.t.bounded
      ((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj (K (2 * m + d + 1))) := by
    obtain ⟨-, ⟨b, hb⟩⟩ := hKbdd (2 * m + d + 1)
    have : (K (2 * m + d + 1)).IsLE b := hb
    exact ⟨⟨-(m : ℤ), inferInstance⟩, ⟨b, inferInstance⟩⟩
  have hCbdd : ∀ n, DerivedCategory.TStructure.t.bounded
      ((DerivedCategory.TStructure.t.truncLE (-(m : ℤ) - 1)).obj (K n)) := by
    intro n
    obtain ⟨⟨a, ha⟩, -⟩ := hKbdd n
    have : (K n).IsGE a := ha
    exact ⟨⟨a, inferInstance⟩, ⟨-(m : ℤ) - 1, inferInstance⟩⟩
  -- Perfectness of the two families of truncations, by the other direction of Tag 0FDC.
  have hAperf : RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace)
      ((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj (K (2 * m + d + 1))) :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular
      hW _ ⟨⟨⟨-(m : ℤ), fun i hi => hAzero i (Or.inl hi)⟩,
        ⟨(m : ℤ), fun i hi => hAzero i (Or.inr hi)⟩⟩, hAcoh⟩
  have hCperf : ∀ n, RingedSpace.IsPerfect.{u, u + 1} (X := W.toRingedSpace)
      ((DerivedCategory.TStructure.t.truncLE (-(m : ℤ) - 1)).obj (K n)) := fun n =>
    Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_of_isBoundedCoherent_of_isRegular
      hW _ ⟨⟨⟨-(m : ℤ) - (n : ℤ), fun i hi => hCzero n i (Or.inl hi)⟩,
        ⟨(m : ℤ) - (n : ℤ), fun i hi => hCzero n i (Or.inr hi)⟩⟩, hCcoh n⟩
  -- The stable truncations of the terms are all isomorphic to the one at the first index.
  have hchain : ∀ n : ℕ, 2 * m + d + 1 ≤ n →
      Nonempty ((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj (K (2 * m + d + 1)) ≅
        (DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj (K n)) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨Iso.refl _⟩
    | succ n hn ih =>
        obtain ⟨θ⟩ := ih
        have := isIso_truncGE_map_of_band_vanishing m n (K n) (K (n + 1)) (t n) (hband n)
          (hband (n + 1)) fun i h₁ h₂ => hstable n i (by omega) h₁ h₂
        exact ⟨θ ≪≫ asIso ((DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).map (t n))⟩
  -- The splitting of Tag 0FZ4 across the gap between the two bands.
  have hsplit : ∀ n : ℕ, 2 * m + d + 1 ≤ n →
      Nonempty (K n ≅ (DerivedCategory.TStructure.t.truncGE (-(m : ℤ))).obj
        (K (2 * m + d + 1)) ⊞
        (DerivedCategory.TStructure.t.truncLE (-(m : ℤ) - 1)).obj (K n)) := by
    intro n hn
    have hgap : ∀ i : ℤ, -(m : ℤ) - (d : ℤ) < i → i < -(m : ℤ) - (d : ℤ) + (d : ℤ) →
        Limits.IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj (K n)) := by
      intro i hi₁ hi₂
      refine hband n i ?_
      rintro (⟨h, -⟩ | ⟨-, h⟩) <;> omega
    obtain ⟨e₀⟩ := exists_iso_biprod_truncLE_truncGE W hW d hd hvan (K n) (hKbdd n) (hKcoh n)
      (-(m : ℤ) - (d : ℤ)) hgap
    rw [show -(m : ℤ) - (d : ℤ) + (d : ℤ) = -(m : ℤ) from by ring] at e₀
    obtain ⟨θ⟩ := hchain n hn
    exact ⟨e₀ ≪≫ biprod.braiding _ _ ≪≫ biprod.mapIso θ.symm (Iso.refl _)⟩
  refine ⟨2 * m + d + 1, _, _, hAperf, fun n _ => hCperf n, hAzero, fun n _ => hCzero n,
    fun n hn => (hsplit n hn).some, ?_⟩
  intro n hn
  exact exists_iso_biprod_map_of_separated_bands hW d hd hvan m n (by omega) _ _ _ hAbdd
    (hCbdd (n + 1)) hAcoh (hCcoh (n + 1)) inferInstance hAzero
    (fun i hi => hCzero n i (Or.inr hi))
    (fun i hi => hCzero (n + 1) i (Or.inr (by push_cast; omega))) (K n) (K (n + 1)) (t n)
    (fun i h₁ h₂ => hstable n i (by omega) h₁ h₂) _ _

/-- **The splitting of a sequence of perfect complexes on a product of smooth schemes.** Let `X`
and `Y` be quasi-compact schemes, smooth and locally of finite type over a field `k`, with
`X ×_k Y` nonempty, and let `K₀ ⟶ K₁ ⟶ ⋯` be a sequence of perfect objects of
`D(𝒪_{X ×_k Y})` whose cohomology lives in the stable band `[-m, m]` together with the receding
band `[-m-n, m-n]`, and whose transition maps are isomorphisms on cohomology throughout the
stable band once `n > 2m`. Then for all large `n` the object `Kₙ` is the direct sum of a perfect
object `A` concentrated in `[-m, m]` and independent of `n`, and a perfect object `Cₙ`
concentrated in `[-m-n, m-n]`, compatibly with the transition maps.

The product of two schemes smooth over `k` is smooth over `k`, hence regular by
[Stacks, Tag 056S]; it is quasi-compact over the base, hence Noetherian, and of finite dimension
because it is nonempty, quasi-compact and locally of finite type over `k`.

The band hypotheses `hband` and `hstable` are the conclusions of parts (1) and (2) of
[Stacks, Tag 0FZ9], which are *not* proved in this development; see the coverage note in the
module docstring. -/
@[stacks 0FZ9 "part (3) in kernel-level form, taking parts (1) and (2) as hband/hstable; those \
ARE proved, in PerfectFibreBands and FibreStableTransitions, and are discharged in \
exists_stable_biprod_of_smooth_of_fibreTransforms. Carries 0FZ3(2) as hvan and non-emptiness \
of the product as hne, neither of which the source has"]
public theorem exists_stable_biprod_of_smooth (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [LocallyOfFiniteType g] [QuasiCompact g]
    [Smooth f] [Smooth g] [IsNoetherian (pullback f g)] (hne : Nonempty ↥(pullback f g))
    (hvan : ∀ d : ℕ, SeparatedCohomologyHomVanishing (pullback f g) d)
    (K : ℕ → DerivedCategory (pullback f g).Modules) (t : ∀ n, K n ⟶ K (n + 1)) (m : ℕ)
    (hperf : ∀ n, RingedSpace.IsPerfect.{u, u + 1}
      (X := (pullback f g).toRingedSpace) (K n))
    (hband : ∀ (n : ℕ) (i : ℤ), ¬ InBands m n i →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj (K n)))
    (hstable : ∀ (n : ℕ) (i : ℤ), 2 * m < n → -(m : ℤ) ≤ i → i ≤ (m : ℤ) →
      IsIso ((DerivedCategory.homologyFunctor (pullback f g).Modules i).map (t n))) :
    ∃ (N : ℕ) (A : DerivedCategory (pullback f g).Modules)
      (C : ℕ → DerivedCategory (pullback f g).Modules),
      RingedSpace.IsPerfect.{u, u + 1} (X := (pullback f g).toRingedSpace) A ∧
      (∀ n, N ≤ n →
        RingedSpace.IsPerfect.{u, u + 1} (X := (pullback f g).toRingedSpace) (C n)) ∧
      (∀ i : ℤ, (i < -(m : ℤ) ∨ (m : ℤ) < i) →
        Limits.IsZero ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj A)) ∧
      (∀ n, N ≤ n → ∀ i : ℤ, (i < -(m : ℤ) - (n : ℤ) ∨ (m : ℤ) - (n : ℤ) < i) →
        Limits.IsZero ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj (C n))) ∧
      ∃ e : (∀ n : ℕ, N ≤ n → (K n ≅ A ⊞ C n)),
        ∀ (n : ℕ) (hn : N ≤ n),
          ∃ (a : A ≅ A) (c : C n ⟶ C (n + 1)),
            t n ≫ (e (n + 1) (by omega)).hom = (e n hn).hom ≫ biprod.map a.hom c := by
  have hreg : IsRegular (pullback f g) :=
    isRegular_of_smooth_over_field (pullback.fst f g ≫ f)
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_eq_natCast_of_locallyOfFiniteType k
    (pullback.fst f g ≫ f) hne
  exact exists_stable_biprod_of_isRegular hreg d hd (hvan d) K t m hperf hband hstable

end AlgebraicGeometry

end
