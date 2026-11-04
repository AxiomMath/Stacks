module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineCoverVanishing.SeparatedCover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# One degree bound for the cohomology over every inverse image in a basis of the target

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S`
quasi-compact. There is a single integer `N = N(X, S, f)` and a basis `B` of the topology of `S`
consisting of affine opens such that

`H ᵖ(f⁻¹V, ℱ) = 0` for every `V ∈ B`, every quasi-coherent `𝒪_X`-module `ℱ` and every `p ≥ N`.

The bound depends on neither `V` nor `ℱ`. This is the integer the proof of clause (3) of
[Stacks, Tag 01XJ] extracts from [Stacks, Tag 071L]: the source covers `S` by finitely many
affine opens `S₁, …, S_m`, covers each `f⁻¹Sⱼ` by finitely many affine opens `U_{j1}, …, U_{jtⱼ}`,
and takes `N` to be the maximum over `j` of the bound of [Stacks, Tag 071L] attached to that
covering. What makes the same `N` work over every `V` is that intersecting the covering with
`f⁻¹V` changes none of the numbers it is built from: `W ⊓ f⁻¹V` is again affine for `W ⊆ f⁻¹Sⱼ`
affine and `V ⊆ Sⱼ` affine, so an affine covering of an intersection `⋂_{i ∈ I} U_{ji}` meets
`f⁻¹V` in an affine covering of `(⋂_{i ∈ I} U_{ji}) ⊓ f⁻¹V` of the same size.

## Main results

* `AlgebraicGeometry.isAffineOpen_inf_preimage_of_le_preimage`: an affine open of `X` inside
  `f⁻¹T`, for `T ⊆ S` affine, meets the inverse image of an affine open `V ≤ T` in an affine
  open.
* `AlgebraicGeometry.minimalAffineCoverCardinality_inf_preimage_le`: intersecting with such an
  `f⁻¹V` does not increase the affine covering number.
* `AlgebraicGeometry.isBasis_affineOpen_le_cover`: the affine opens contained in some member of a
  given open covering of `S` form a basis of the topology of `S`.
* `Stacks.Cohomology.AffineCover.exists_isZero_hgroup_preimage_of_isBasis`: the uniform bound
  itself.

## Implementation notes

The vanishing is obtained inside the ambient scheme `X`, over the open `f⁻¹V`, by
`Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_finset_cover` — the form of
[Stacks, Tag 071L] stated over a sub-open rather than over `⊤`. Nothing is transported to
`f⁻¹V` regarded as a scheme in its own right.

`X` is *not* assumed quasi-separated, and it need not be: only `f` is. All the opens the
induction intersects lie inside one `f⁻¹Sⱼ`, which is quasi-separated because `f` is and `Sⱼ` is
affine, and that is exactly the hypothesis
`Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_finset_cover_of_inter_isCompact`
asks for.

The index set of the covering of `f⁻¹Sⱼ` is `Fin (tⱼ)`, and the empty subset `I = ∅` has to be
treated separately in the bound, because `Finset.inf` over the empty finset is `⊤` rather than
`f⁻¹Sⱼ`; there the open in question is `f⁻¹V` itself, covered by the `tⱼ` affine opens
`U_{ji} ⊓ f⁻¹V`.

## References

* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
* [Stacks Project, Tag 01XI](https://stacks.math.columbia.edu/tag/01XI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-! ### Affine opens meeting an inverse image -/

/-- **An affine open above an affine open meets an inverse image affinely.** Let `f : X ⟶ S`, let
`T ⊆ S` be an affine open, let `W ⊆ f⁻¹T` be an affine open of `X` and let `V ≤ T` be an affine
open of `S`. Then `W ⊓ f⁻¹V` is an affine open of `X`.

The restriction `W ⟶ T` of `f` is a morphism of affine schemes, hence an affine morphism, so the
inverse image in `W` of the affine open `V` of `T` is affine; and an affine open of `W` is an
affine open of `X`, because `W ⟶ X` is an open immersion. -/
theorem isAffineOpen_inf_preimage_of_le_preimage (f : X ⟶ S) {W : X.Opens} {T V : S.Opens}
    (hW : IsAffineOpen W) (hT : IsAffineOpen T) (hV : IsAffineOpen V)
    (hWT : W ≤ f ⁻¹ᵁ T) (hVT : V ≤ T) : IsAffineOpen (W ⊓ f ⁻¹ᵁ V) := by
  have : IsAffine W.toScheme := hW
  have : IsAffine T.toScheme := hT
  have himage : T.ι ''ᵁ (T.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hVT
  have hpre : IsAffineOpen (f.resLE T W hWT ⁻¹ᵁ (T.ι ⁻¹ᵁ V)) :=
    (hV.preimage_of_isOpenImmersion T.ι (hVT.trans (Scheme.Opens.opensRange_ι T).ge)).preimage _
  rw [Scheme.Hom.resLE_preimage, himage] at hpre
  have himg := hpre.image_of_isOpenImmersion W.ι
  rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at himg

/-- An affine open cover of `A ⊆ f⁻¹T` by `n` opens gives one of `A ⊓ f⁻¹V` by `n` opens. -/
private theorem minimalAffineCoverCardinality_inf_preimage_le_of_iSup_eq (f : X ⟶ S)
    {A : X.Opens} {T V : S.Opens} (hT : IsAffineOpen T) (hV : IsAffineOpen V)
    (hAT : A ≤ f ⁻¹ᵁ T) (hVT : V ≤ T) {n : ℕ} (W : Fin n → X.Opens)
    (hW : ∀ i, IsAffineOpen (W i)) (hWcover : iSup W = A) :
    minimalAffineCoverCardinality (A ⊓ f ⁻¹ᵁ V) ≤ n := by
  refine Nat.sInf_le ⟨fun i ↦ W i ⊓ f ⁻¹ᵁ V, fun i ↦
    isAffineOpen_inf_preimage_of_le_preimage f (hW i) hT hV
      (((le_iSup W i).trans hWcover.le).trans hAT) hVT, ?_⟩
  rw [← iSup_inf_eq, hWcover]

/-- **Intersecting with an inverse image does not increase the affine covering number.** Let
`A ⊆ f⁻¹T` be a quasi-compact open of `X`, with `T ⊆ S` affine, and let `V ≤ T` be an affine open
of `S`. Then `A ⊓ f⁻¹V` needs no more affine opens to cover it than `A` does: a minimal affine
covering of `A` meets `f⁻¹V` in an affine covering of `A ⊓ f⁻¹V` of the same size, by
`AlgebraicGeometry.isAffineOpen_inf_preimage_of_le_preimage`. -/
theorem minimalAffineCoverCardinality_inf_preimage_le (f : X ⟶ S) {A : X.Opens} {T V : S.Opens}
    (hA : IsCompact (A : Set X)) (hT : IsAffineOpen T) (hV : IsAffineOpen V)
    (hAT : A ≤ f ⁻¹ᵁ T) (hVT : V ≤ T) :
    minimalAffineCoverCardinality (A ⊓ f ⁻¹ᵁ V) ≤ minimalAffineCoverCardinality A := by
  classical
  obtain ⟨W, hW, hWcover⟩ := exists_affine_cover_card_eq A hA
  exact minimalAffineCoverCardinality_inf_preimage_le_of_iSup_eq f hT hV hAT hVT W hW hWcover

/-- **A finite intersection of quasi-compact opens inside a quasi-separated open is
quasi-compact.** The empty intersection is excluded, since `Finset.inf` of the empty finset is
`⊤`. -/
theorem isCompact_finset_inf {ι : Type*} {Z : X.Opens} (hZ : IsQuasiSeparated (Z : Set X))
    (V : ι → X.Opens) (hVZ : ∀ i, V i ≤ Z) (hVc : ∀ i, IsCompact ((V i : X.Opens) : Set X))
    {J : Finset ι} (hJ : J.Nonempty) : IsCompact ((J.inf V : X.Opens) : Set X) := by
  classical
  induction hJ using Finset.Nonempty.cons_induction with
  | singleton a => simpa using hVc a
  | cons a s ha hs ih =>
    obtain ⟨b, hb⟩ := hs
    have hsle : (s.inf V : X.Opens) ≤ Z := (Finset.inf_le hb).trans (hVZ b)
    rw [Finset.inf_cons]
    simpa using hZ ((V a : X.Opens) : Set X) ((s.inf V : X.Opens) : Set X)
      (fun x hx ↦ hVZ a hx) (V a).2 (hVc a) (fun x hx ↦ hsle hx) (s.inf V).2 ih

/-- **The degree bound attached to an affine covering of an inverse image.** Let `T ⊆ S` be an
affine open with `f⁻¹T` quasi-separated, covered by the affine opens `U i`, `i < n`, and let
`V ≤ T` be an affine open. For every finite set `J` of indices,
`#J + t(f⁻¹V ⊓ ⋂_{i ∈ J} U i) - 1 ≤ n + max_I t(⋂_{i ∈ I} U i)`, where `t` is
`AlgebraicGeometry.minimalAffineCoverCardinality`. -/
private theorem card_add_minimalAffineCoverCardinality_inf_preimage_le (f : X ⟶ S) {T V : S.Opens}
    (hT : IsAffineOpen T) (hV : IsAffineOpen V) (hVT : V ≤ T)
    (hTqs : IsQuasiSeparated ((f ⁻¹ᵁ T : X.Opens) : Set X))
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hUcover : iSup U = f ⁻¹ᵁ T)
    (J : Finset (Fin n)) :
    J.card + minimalAffineCoverCardinality ((f ⁻¹ᵁ V : X.Opens) ⊓ J.inf U) - 1 ≤
      n + Finset.univ.sup fun I : Finset (Fin n) ↦ minimalAffineCoverCardinality (I.inf U) := by
  have hUle : ∀ i, U i ≤ f ⁻¹ᵁ T := fun i ↦ (le_iSup U i).trans hUcover.le
  have hJcard : J.card ≤ n := by simpa using Finset.card_le_univ J
  rcases J.eq_empty_or_nonempty with rfl | hJne
  · have hsmall : minimalAffineCoverCardinality
        ((f ⁻¹ᵁ V : X.Opens) ⊓ (∅ : Finset (Fin n)).inf U) ≤ n := by
      have h := minimalAffineCoverCardinality_inf_preimage_le_of_iSup_eq f hT hV le_rfl hVT
        U hU hUcover
      simpa [inf_eq_right.mpr (Scheme.Hom.preimage_mono f hVT)] using h
    simp only [Finset.card_empty]
    omega
  · obtain ⟨i₀, hi₀⟩ := id hJne
    have hJle : J.inf U ≤ f ⁻¹ᵁ T := (Finset.inf_le hi₀).trans (hUle i₀)
    have h1 : minimalAffineCoverCardinality ((f ⁻¹ᵁ V : X.Opens) ⊓ J.inf U) ≤
        minimalAffineCoverCardinality (J.inf U) := by
      have h := minimalAffineCoverCardinality_inf_preimage_le f
        (isCompact_finset_inf hTqs U hUle (fun i ↦ (hU i).isCompact) hJne) hT hV hJle hVT
      rwa [inf_comm] at h
    have h2 : minimalAffineCoverCardinality (J.inf U) ≤ Finset.univ.sup
        (fun I : Finset (Fin n) ↦ minimalAffineCoverCardinality (I.inf U)) :=
      Finset.le_sup (f := fun I : Finset (Fin n) ↦ minimalAffineCoverCardinality (I.inf U))
        (Finset.mem_univ J)
    omega

/-! ### The affine opens below a covering form a basis -/

/-- **The affine opens contained in a member of a covering form a basis.** If the opens `W i`
cover the scheme `S`, then the affine opens of `S` contained in some `W i` form a basis of the
topology of `S`: an affine open of a basis neighbourhood inside `U ⊓ W i` works. -/
@[ega "I 2.1.3" "more general"]
theorem isBasis_affineOpen_le_cover {ι : Type*} (W : ι → S.Opens) (hW : ⨆ i, W i = ⊤) :
    Opens.IsBasis {V : S.Opens | IsAffineOpen V ∧ ∃ i, V ≤ W i} := by
  rw [Opens.isBasis_iff_nbhd]
  intro U x hx
  have hxtop : x ∈ ⨆ i, W i := by
    rw [hW]
    exact trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxtop
  obtain ⟨V, hVmem, hxV, hVle⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (show x ∈ U ⊓ W i from ⟨hx, hi⟩)
  exact ⟨V, ⟨hVmem, i, hVle.trans inf_le_right⟩, hxV, hVle.trans inf_le_left⟩

end AlgebraicGeometry

namespace Stacks.Cohomology.AffineCover

variable {X S : Scheme.{u}}

/-- **One degree bound for the cohomology over every inverse image in a basis of the target.**
Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S`
quasi-compact. Then there is an integer `N` and a basis `B` of the topology of `S` consisting of
affine opens with `H ᵖ(f⁻¹V, ℱ) = 0` for every `V ∈ B`, every quasi-coherent `𝒪_X`-module `ℱ`
and every `p ≥ N`.

This is the integer the proof of clause (3) of [Stacks, Tag 01XJ] takes from
[Stacks, Tag 071L]. Cover `S` by affine opens `T₁, …, T_m` and each `f⁻¹Tⱼ` — quasi-compact,
because `f` is — by affine opens `U_{j1}, …, U_{jtⱼ}`, and let

`N = max ⱼ (tⱼ + max_{I ⊆ {1, …, tⱼ}} t(⋂_{i ∈ I} U_{ji}))`,

where `t` is the affine covering number `AlgebraicGeometry.minimalAffineCoverCardinality`. The
basis is the set of affine opens of `S` contained in some `Tⱼ`. For such a `V`, inside `Tⱼ`, the
open `f⁻¹V` is covered by the `tⱼ` opens `U_{ji} ⊓ f⁻¹V`, and
`Stacks.Cohomology.AffineCover.isZero_cohomologyPresheaf_of_finset_cover_of_inter_isCompact`
applies to the family `U_{ji}` over
the sub-open `f⁻¹V`: its bound is controlled by `N` because intersecting with `f⁻¹V` leaves every
affine covering number in sight unchanged
(`AlgebraicGeometry.minimalAffineCoverCardinality_inf_preimage_le`).

No quasi-separatedness of `X` is used: every intersection the induction forms happens inside one
`f⁻¹Tⱼ`, which is quasi-separated by `AlgebraicGeometry.Scheme.Hom.isQuasiSeparated_preimage`. -/
theorem exists_isZero_hgroup_preimage_of_isBasis (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ (N : ℕ) (B : Set S.Opens), Opens.IsBasis B ∧ (∀ V ∈ B, IsAffineOpen V) ∧
      ∀ V ∈ B, ∀ F : X.Modules, F.IsQuasicoherent → ∀ p : ℕ, N ≤ p →
        IsZero (Hgroup X.ringCatSheaf (f ⁻¹ᵁ V) p F) := by
  classical
  obtain ⟨m, T, hTaff, hTcover⟩ := exists_fin_affine_cover_of_isCompact (⊤ : S.Opens)
    (by simpa using isCompact_univ (X := S))
  have hpreCompact : ∀ j : Fin m, IsCompact ((f ⁻¹ᵁ T j : X.Opens) : Set X) :=
    fun j ↦ f.isCompact_preimage (hTaff j).isCompact
  have hpreQS : ∀ j : Fin m, IsQuasiSeparated ((f ⁻¹ᵁ T j : X.Opens) : Set X) :=
    fun j ↦ f.isQuasiSeparated_preimage (hTaff j).isQuasiSeparated
  have hcov : ∀ j : Fin m, ∃ n, ∃ U : Fin n → X.Opens,
      (∀ i, IsAffineOpen (U i)) ∧ iSup U = f ⁻¹ᵁ T j :=
    fun j ↦ exists_fin_affine_cover_of_isCompact _ (hpreCompact j)
  choose t U hUaff hUcover using hcov
  refine ⟨Finset.univ.sup fun j : Fin m ↦ t j + Finset.univ.sup
      fun I : Finset (Fin (t j)) ↦ minimalAffineCoverCardinality (I.inf (U j)),
    {V : S.Opens | IsAffineOpen V ∧ ∃ j, V ≤ T j},
    isBasis_affineOpen_le_cover T hTcover, fun _ hV ↦ hV.1, ?_⟩
  intro V hV F hF p hp
  obtain ⟨hVaff, j, hVT⟩ := hV
  let _ : F.IsQuasicoherent := hF
  let _ : HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  have hbound : t j + Finset.univ.sup
      (fun I : Finset (Fin (t j)) ↦ minimalAffineCoverCardinality (I.inf (U j))) ≤ p :=
    le_trans (Finset.le_sup (f := fun j : Fin m ↦ t j + Finset.univ.sup
      fun I : Finset (Fin (t j)) ↦ minimalAffineCoverCardinality (I.inf (U j)))
      (Finset.mem_univ j)) hp
  have hUle : ∀ i, U j i ≤ f ⁻¹ᵁ T j := fun i ↦ (le_iSup (U j) i).trans (hUcover j).le
  have hUcompact : ∀ i, IsCompact ((U j i : X.Opens) : Set X) := fun i ↦ (hUaff j i).isCompact
  have hUsep : ∀ i, Scheme.IsSeparated ((U j i : X.Opens) : Scheme) := fun i ↦ by
    have : IsAffine (U j i).toScheme := hUaff j i
    infer_instance
  have hVle : (f ⁻¹ᵁ V : X.Opens) ≤ f ⁻¹ᵁ T j := fun x hx ↦ hVT hx
  have hinter : ∀ (i : Fin (t j)) (T' : X.Opens), T' ≤ f ⁻¹ᵁ V → IsCompact (T' : Set X) →
      IsCompact ((T' ⊓ U j i : X.Opens) : Set X) := fun i T' hT' hT'c ↦ by
    simpa using hpreQS j (T' : Set X) ((U j i : X.Opens) : Set X)
      (fun x hx ↦ hVle (hT' hx)) T'.2 hT'c (fun x hx ↦ hUle i hx) (U j i).2 (hUcompact i)
  have hcover : (f ⁻¹ᵁ V : X.Opens) ⊓ (Finset.univ : Finset (Fin (t j))).sup (U j) = f ⁻¹ᵁ V := by
    have hsup : (Finset.univ : Finset (Fin (t j))).sup (U j) = f ⁻¹ᵁ T j := by
      simpa [Finset.sup_eq_iSup] using hUcover j
    rw [hsup, inf_eq_left.mpr hVle]
  refine (isZero_hgroup_iff_isZero_cohomologyPresheaf (f ⁻¹ᵁ V) F p).mpr ?_
  have hvan := isZero_cohomologyPresheaf_of_finset_cover_of_inter_isCompact (f ⁻¹ᵁ V)
    (f.isCompact_preimage hVaff.isCompact) (U j) hUcompact hUsep hinter F Finset.univ _
    (fun J _ ↦ card_add_minimalAffineCoverCardinality_inf_preimage_le f (hTaff j) hVaff hVT
      (hpreQS j) (U j) (hUaff j) (hUcover j) J) p hbound
  rwa [hcover] at hvan

end Stacks.Cohomology.AffineCover

end
