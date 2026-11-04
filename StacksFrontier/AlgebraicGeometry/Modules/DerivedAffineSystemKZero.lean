module

public import StacksFrontier.AlgebraicGeometry.Chow.RationalIntersection.SupportedWeightOperator
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedAffineSystem
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckGroupImageKernel

/-!
# The Euler characteristic of a long exact sequence in a Grothendieck group

Let `𝒜` be an abelian category and let
`⋯ → Aⱼ₊₁ → Bⱼ₊₁ → Cⱼ₊₁ →δ Aⱼ → Bⱼ → Cⱼ → ⋯ → A₀ → B₀ → C₀ → 0`
be a long exact sequence in `𝒜`, indexed by `j ∈ ℕ`, with `C_{N+1} = 0`. Writing `Kⱼ` for the
image of `δ : Cⱼ₊₁ → Aⱼ`, exactness gives `[Aⱼ] - [Bⱼ] + [Cⱼ] = [Kⱼ] + [Kⱼ₋₁]` in `K₀(𝒜)` (with
`K₋₁ = 0`, as `B₀ → C₀` is onto), so the alternating sum telescopes:

  `∑_{j ≤ N} (-1)ʲ ([Aⱼ] - [Bⱼ] + [Cⱼ]) = (-1)ᴺ [K_N] = 0`.

For coherent modules supported in a closed subset `W` of a locally Noetherian scheme `X` this is
stated for sequences of `𝒪_X`-modules, with coherence and support as hypotheses, in the
Grothendieck group `K₀(Coh_W(X))`: the inclusion of `Coh_W(X)` into all `𝒪_X`-modules is fully
faithful, so the morphisms lift, and it reflects exactness. It applies to the long exact sequence
of semilinear derived functors `⋯ → Lⱼ Φ₁(f) → Lⱼ Φ₂(f) → Lⱼ Φ₃(f) → Lⱼ₋₁ Φ₁(f) → ⋯` of a
morphism `f : F' ⟶ F` of coherent modules supported in `W`, under finiteness and vanishing
hypotheses on the `Φᵢ`.

## Main definitions

* `Stacks.Chow.coherentSupportedInMk`: a coherent `𝒪_X`-module supported in `T`, as an object of
  `Coh_T(X)`.

## Main results

* `KZero.sum_range_neg_one_pow_zsmul_eq_zero`: the Euler characteristic of a long exact sequence
  with finitely many nonzero terms vanishes in `K₀(𝒜)`.
* `Stacks.Chow.sum_range_neg_one_pow_zsmul_supportedCoherentKZero_eq_zero`: the same in
  `K₀(Coh_W(X))` for a long exact sequence of coherent `𝒪_X`-modules supported in `W`.
* `Stacks.SemilinearArrowFunctor.sum_range_neg_one_pow_zsmul_derivedSheaf_eq_zero`: the case of
  the long exact sequence of a short exact sequence of semilinear functors on arrows.

## Implementation notes

Only `C_{N+1} = 0` is assumed, which is what the telescoping uses; it holds when all terms vanish
above `N`. The two coherence predicates of the library for sheaves of modules on a ringed space
have the same fields; the hypotheses are stated with `SheafOfModules.IsCoherent`, the predicate
of `Stacks.Modules.AffineSystem.isCoherent_sheaf`, and converted field by field to the predicate
cutting out `Coh(X)`.

## References

* [Stacks Project, Tag 02MU](https://stacks.math.columbia.edu/tag/02MU), for `K₀` of an abelian
  category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace KZero

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- A telescoping identity in an abelian group: if `t₀ = k₀` and `tⱼ₊₁ = kⱼ₊₁ + kⱼ`, the
alternating sum of the `tⱼ` for `j ≤ N` is `(-1)ᴺ k_N`. -/
theorem sum_range_neg_one_pow_zsmul_telescope {G : Type*} [AddCommGroup G] (t k : ℕ → G)
    (h0 : t 0 = k 0) (hs : ∀ j, t (j + 1) = k (j + 1) + k j) (N : ℕ) :
    ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j • t j = (-1 : ℤ) ^ N • k N := by
  induction N with
  | zero => simp [h0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hs, pow_succ, mul_neg_one, neg_smul, smul_add, neg_smul]
    abel

/-- For an exact sequence `X₁ → X₂ → X₃`, the class of `X₂` is the sum of the classes of the images
of the two maps. -/
private theorem mk_eq_image_add_image_of_exact (S : ShortComplex 𝒜) (hS : S.Exact) :
    mk 𝒜 S.X₂ = mk 𝒜 (Abelian.image S.f) + mk 𝒜 (Abelian.image S.g) := by
  rw [mk_eq_kernel_add_image S.g, ← mk_image_eq_mk_kernel _ hS]

/-- **The Euler characteristic of a long exact sequence vanishes.** For a long exact sequence
`⋯ → Aⱼ →aⱼ Bⱼ →bⱼ Cⱼ →dⱼ₋₁ Aⱼ₋₁ → ⋯ → A₀ → B₀ → C₀ → 0` in an abelian category with
`C_{N+1} = 0`, the alternating sum `∑_{j ≤ N} (-1)ʲ ([Aⱼ] - [Bⱼ] + [Cⱼ])` vanishes in `K₀`. -/
theorem sum_range_neg_one_pow_zsmul_eq_zero {A B C : ℕ → 𝒜} (a : ∀ j, A j ⟶ B j)
    (b : ∀ j, B j ⟶ C j) (d : ∀ j, C (j + 1) ⟶ A j) (hab : ∀ j, a j ≫ b j = 0)
    (hbd : ∀ j, b (j + 1) ≫ d j = 0) (hda : ∀ j, d j ≫ a j = 0)
    (h₂ : ∀ j, (ShortComplex.mk _ _ (hab j)).Exact)
    (h₃ : ∀ j, (ShortComplex.mk _ _ (hbd j)).Exact)
    (h₁ : ∀ j, (ShortComplex.mk _ _ (hda j)).Exact) [Epi (b 0)] (N : ℕ)
    (hN : IsZero (C (N + 1))) :
    ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j • (mk 𝒜 (A j) - mk 𝒜 (B j) + mk 𝒜 (C j)) = 0 := by
  have hC0 : mk 𝒜 (C 0) = mk 𝒜 (Abelian.image (b 0)) := by
    rw [mk_eq_image_add_cokernel (b 0), mk_eq_zero_of_isZero (isZero_cokernel_of_epi _),
      add_zero]
  rw [sum_range_neg_one_pow_zsmul_telescope _ (fun j => mk 𝒜 (Abelian.image (d j)))
    (by rw [mk_eq_image_add_image_of_exact _ (h₁ 0), mk_eq_image_add_image_of_exact _ (h₂ 0), hC0]
        abel)
    (fun j => by
      rw [mk_eq_image_add_image_of_exact _ (h₁ (j + 1)),
        mk_eq_image_add_image_of_exact _ (h₂ (j + 1)), mk_eq_image_add_image_of_exact _ (h₃ j)]
      abel) N,
    mk_eq_zero_of_isZero (hN.of_epi (Abelian.factorThruImage (d N))), smul_zero]

end KZero

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- A coherent `𝒪_X`-module supported in a set `T`, as an object of `Coh_T(X)`. -/
def coherentSupportedInMk {T : Set X} (M : X.Modules) (hM : _root_.SheafOfModules.IsCoherent M)
    (hT : SheafOfModules.supp M ⊆ T) : (coherentSupportedIn T).FullSubcategory :=
  ⟨⟨M, ⟨hM.1, hM.2⟩⟩, hT⟩

/-- The underlying `𝒪_X`-module of `coherentSupportedInMk M`. -/
@[simp]
lemma coherentSupportedInMk_obj_obj {T : Set X} (M : X.Modules)
    (hM : _root_.SheafOfModules.IsCoherent M) (hT : SheafOfModules.supp M ⊆ T) :
    (coherentSupportedInMk M hM hT).obj.obj = M :=
  rfl

variable [IsLocallyNoetherian X]

/-- **The Euler characteristic of a long exact sequence of coherent modules with supports.** Let
`W` be a closed subset of a locally Noetherian scheme `X` and
`⋯ → Aⱼ →aⱼ Bⱼ →bⱼ Cⱼ →dⱼ₋₁ Aⱼ₋₁ → ⋯ → A₀ → B₀ → C₀ → 0` a long exact sequence of coherent
`𝒪_X`-modules supported in `W`, with `C_{N+1} = 0`. Then
`∑_{j ≤ N} (-1)ʲ ([Aⱼ] - [Bⱼ] + [Cⱼ]) = 0` in `K₀(Coh_W(X))`. -/
theorem sum_range_neg_one_pow_zsmul_supportedCoherentKZero_eq_zero {W : Closeds X}
    {A B C : ℕ → X.Modules} (a : ∀ j, A j ⟶ B j) (b : ∀ j, B j ⟶ C j)
    (d : ∀ j, C (j + 1) ⟶ A j) (hab : ∀ j, a j ≫ b j = 0) (hbd : ∀ j, b (j + 1) ≫ d j = 0)
    (hda : ∀ j, d j ≫ a j = 0) (h₂ : ∀ j, (ShortComplex.mk _ _ (hab j)).Exact)
    (h₃ : ∀ j, (ShortComplex.mk _ _ (hbd j)).Exact)
    (h₁ : ∀ j, (ShortComplex.mk _ _ (hda j)).Exact) (hb : Epi (b 0))
    (hA : ∀ j, _root_.SheafOfModules.IsCoherent (A j))
    (hB : ∀ j, _root_.SheafOfModules.IsCoherent (B j))
    (hC : ∀ j, _root_.SheafOfModules.IsCoherent (C j))
    (hsA : ∀ j, SheafOfModules.supp (A j) ⊆ W) (hsB : ∀ j, SheafOfModules.supp (B j) ⊆ W)
    (hsC : ∀ j, SheafOfModules.supp (C j) ⊆ W) (N : ℕ) (hN : IsZero (C (N + 1))) :
    ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j •
      (KZero.mk _ (coherentSupportedInMk (A j) (hA j) (hsA j)) -
        KZero.mk _ (coherentSupportedInMk (B j) (hB j) (hsB j)) +
        KZero.mk _ (coherentSupportedInMk (C j) (hC j) (hsC j)) :
          supportedCoherentKZero W) = 0 := by
  let ι := (coherentSupportedIn (W : Set X)).ι ⋙
    (Stacks.SheafOfModules.coherentModules X.ringCatSheaf).ι
  have FF : ι.FullyFaithful :=
    (ObjectProperty.fullyFaithfulι _).comp (ObjectProperty.fullyFaithfulι _)
  have : ι.Faithful := FF.faithful
  have : ι.Full := FF.full
  let A' := fun j => coherentSupportedInMk (A j) (hA j) (hsA j)
  let B' := fun j => coherentSupportedInMk (B j) (hB j) (hsB j)
  let C' := fun j => coherentSupportedInMk (C j) (hC j) (hsC j)
  let a' : ∀ j, A' j ⟶ B' j := fun j => FF.preimage (a j)
  let b' : ∀ j, B' j ⟶ C' j := fun j => FF.preimage (b j)
  let d' : ∀ j, C' (j + 1) ⟶ A' j := fun j => FF.preimage (d j)
  have ha : ∀ j, ι.map (a' j) = a j := fun j => FF.map_preimage _
  have hb' : ∀ j, ι.map (b' j) = b j := fun j => FF.map_preimage _
  have hd : ∀ j, ι.map (d' j) = d j := fun j => FF.map_preimage _
  have hab' : ∀ j, a' j ≫ b' j = 0 := fun j => FF.map_injective (by
    rw [Functor.map_comp, ha, hb', Functor.map_zero]; exact hab j)
  have hbd' : ∀ j, b' (j + 1) ≫ d' j = 0 := fun j => FF.map_injective (by
    rw [Functor.map_comp, hb', hd, Functor.map_zero]; exact hbd j)
  have hda' : ∀ j, d' j ≫ a' j = 0 := fun j => FF.map_injective (by
    rw [Functor.map_comp, hd, ha, Functor.map_zero]; exact hda j)
  have hex : ∀ {P Q R : (coherentSupportedIn (W : Set X)).FullSubcategory} (u : P ⟶ Q)
      (v : Q ⟶ R) (w : u ≫ v = 0),
      (ShortComplex.mk (ι.map u) (ι.map v)
        (by rw [← Functor.map_comp, w, Functor.map_zero])).Exact →
        (ShortComplex.mk u v w).Exact := fun u v w h =>
    ι.reflects_exact_of_faithful _ h
  have : Epi (b' 0) := ι.epi_of_epi_map (by rw [hb']; exact hb)
  have hN' : IsZero (C' (N + 1)) := IsZero.of_full_of_faithful_of_isZero ι _ hN
  exact KZero.sum_range_neg_one_pow_zsmul_eq_zero a' b' d' hab' hbd' hda'
    (fun j => hex _ _ _ (by simp only [ha, hb']; exact h₂ j))
    (fun j => hex _ _ _ (by simp only [hb', hd]; exact h₃ j))
    (fun j => hex _ _ _ (by simp only [hd, ha]; exact h₁ j)) N hN'

end Stacks.Chow

namespace Stacks.SemilinearArrowFunctor

open Modules Chow SimplicialProjectiveResolution

variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] {F' F : Y.Modules} [F'.IsQuasicoherent]
  [F.IsQuasicoherent] [F'.IsFiniteType] [F.IsFiniteType] (f : F' ⟶ F)
  {Φ₁ Φ₂ Φ₃ : SemilinearArrowFunctor.{u}} {α : Φ₁ ⟶ Φ₂} {β : Φ₂ ⟶ Φ₃}

/-- **The Euler characteristic of the long exact sequence of semilinear derived functors.** Let
`0 → Φ₁ → Φ₂ → Φ₃ → 0` be a short exact sequence of semilinear functors on arrows commuting with
flat base change, with finite derived modules at arrows of finite modules over Noetherian rings
and derived modules vanishing at arrows with zero terms. For a morphism `f : F' ⟶ F` of
quasi-coherent modules of finite type supported in a closed `W` of a locally Noetherian scheme,
with `L_{N+1} Φ₃(f) = 0`, the alternating sum `∑_{j ≤ N} (-1)ʲ ([Lⱼ Φ₁(f)] - [Lⱼ Φ₂(f)] +
[Lⱼ Φ₃(f)])` vanishes in `K₀(Coh_W(Y))`. -/
theorem sum_range_neg_one_pow_zsmul_derivedSheaf_eq_zero (h : ShortExact α β)
    (hΦ₁ : Φ₁.HasFlatBaseChange) (hΦ₂ : Φ₂.HasFlatBaseChange) (hΦ₃ : Φ₃.HasFlatBaseChange)
    (hfin : ∀ Φ ∈ ({Φ₁, Φ₂, Φ₃} : Set SemilinearArrowFunctor.{u}), ∀ (j : ℕ)
      (A : CommRingCat.{u}), IsNoetherianRing A →
      ∀ (X : ComposableArrows (ModuleCat.{u} A) 1), Module.Finite A X.left →
        Module.Finite A X.right → ∀ P : SimplicialProjectiveResolution X,
          Module.Finite A (P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j))
    (hzero : ∀ Φ ∈ ({Φ₁, Φ₂, Φ₃} : Set SemilinearArrowFunctor.{u}), ∀ (j : ℕ)
      (A : CommRingCat.{u}) (X : ComposableArrows (ModuleCat.{u} A) 1),
      IsZero X.left → IsZero X.right → ∀ P : SimplicialProjectiveResolution X,
        IsZero (P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j))
    {W : Closeds Y} (hF' : SheafOfModules.supp F' ⊆ W) (hF : SheafOfModules.supp F ⊆ W)
    (N : ℕ) (hN : IsZero (Φ₃.derivedSheaf f hΦ₃ (N + 1))) :
    ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j •
      (KZero.mk _ (coherentSupportedInMk (Φ₁.derivedSheaf f hΦ₁ j)
          (Φ₁.isCoherent_derivedSheaf f hΦ₁ j (hfin Φ₁ (by simp) j))
          (supp_derivedSheaf_subset_of_subset f hΦ₁ j (hzero Φ₁ (by simp) j) hF' hF)) -
        KZero.mk _ (coherentSupportedInMk (Φ₂.derivedSheaf f hΦ₂ j)
          (Φ₂.isCoherent_derivedSheaf f hΦ₂ j (hfin Φ₂ (by simp) j))
          (supp_derivedSheaf_subset_of_subset f hΦ₂ j (hzero Φ₂ (by simp) j) hF' hF)) +
        KZero.mk _ (coherentSupportedInMk (Φ₃.derivedSheaf f hΦ₃ j)
          (Φ₃.isCoherent_derivedSheaf f hΦ₃ j (hfin Φ₃ (by simp) j))
          (supp_derivedSheaf_subset_of_subset f hΦ₃ j (hzero Φ₃ (by simp) j) hF' hF)) :
          supportedCoherentKZero W) = 0 :=
  sum_range_neg_one_pow_zsmul_supportedCoherentKZero_eq_zero
    (fun j => derivedSheafMap f α hΦ₁ hΦ₂ j) (fun j => derivedSheafMap f β hΦ₂ hΦ₃ j)
    (fun j => derivedSheafδ f h hΦ₁ hΦ₃ j)
    (fun j => derivedSheafMap_comp_derivedSheafMap f h hΦ₁ hΦ₂ hΦ₃ j)
    (fun j => derivedSheafMap_comp_derivedSheafδ f h hΦ₁ hΦ₂ hΦ₃ j)
    (fun j => derivedSheafδ_comp_derivedSheafMap f h hΦ₁ hΦ₂ hΦ₃ j)
    (fun j => exact_derivedSheafMap f h hΦ₁ hΦ₂ hΦ₃ j)
    (fun j => exact_derivedSheafMap_derivedSheafδ f h hΦ₁ hΦ₂ hΦ₃ j)
    (fun j => exact_derivedSheafδ_derivedSheafMap f h hΦ₁ hΦ₂ hΦ₃ j)
    (epi_derivedSheafMap_zero f h hΦ₂ hΦ₃) _ _ _ _ _ _ N hN

end Stacks.SemilinearArrowFunctor
