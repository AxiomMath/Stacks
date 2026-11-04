module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.UniversallyClosedTest
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Universal closedness is tested inside the size cutoff of a big fppf site

`AlgebraicGeometry.UniversallyClosed` asks that *every* base change of a morphism of schemes be
a closed map, with no bound on the size of the base. A big fppf site `B` in the sense of
**Stacks 021A** contains only schemes below a cardinal cutoff, so a condition formulated inside
such a site — for instance the point-set closedness of **Stacks 03HI**, whose quantifier runs
over algebraic spaces over `S` — a priori gives closedness of a *restricted* class of base
changes only. This file closes that gap: for a morphism between two schemes inside `B`,
closedness of the base changes along morphisms from schemes inside `B` already implies
universal closedness.

## Main results

* `AlgebraicGeometry.universallyClosed_of_bounded_closed_baseChanges`: the size-cutoff bridge.
* `AlgebraicGeometry.affineCoverPolynomial_size_lt`: the polynomial algebra on the affine opens of
  a scheme inside a big fppf site, over a ring whose spectrum is inside that site, again has
  spectrum inside it. This is what puts the test scheme of the closedness argument — the affine
  space whose coordinates are indexed by a cover of the source — inside the site, both here and
  for the same argument at the level of algebraic spaces.
* `AlgebraicGeometry.BigFppfSite.contains_affineSpace`: relative affine `n`-space over a scheme
  inside the site is again inside the site.

## Implementation notes

The hypothesis is applied three times, to three bases that are all inside `B` because the
cutoff is a strong limit closed under fibre products and countable coproducts.

* Along the identity of the target, giving that the morphism is itself a closed map.
* Along the spectrum of a residue field of the target composed with the coordinate inclusion
  into a polynomial algebra over it, indexed by an affine cover of the corresponding fibre.
  This gives that the fibre is quasi-compact, by the affine-cover argument of
  `compactSpace_of_affineCoverPolynomial_closed`. With the previous point, the morphism is a
  proper map of topological spaces and in particular quasi-compact as a morphism of schemes.
* Along the projection of affine `n`-space over the target, for every `n`. With quasi-compactness
  in hand, **Stacks 05JX** turns that into universal closedness.

The size estimates are the ones collected in `StacksFrontier.AlgebraicGeometry.Size.Cutoff`:
`AlgebraicGeometry.Scheme.size_Spec_lt_of_mk_le` and
`AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType` for spectra of rings,
`AlgebraicGeometry.Scheme.size_pullback_lt` for fibre products,
`AlgebraicGeometry.Scheme.size_sigmaObj_lt` for coproducts, and
`AlgebraicGeometry.Scheme.size_le_of_mono_quasiCompact` for the residue field spectrum.

## References

* [Stacks Project, Tag 03XD](https://stacks.math.columbia.edu/tag/03XD)
* [Stacks Project, Tag 05JX](https://stacks.math.columbia.edu/tag/05JX)
* [Stacks Project, Tag 021A](https://stacks.math.columbia.edu/tag/021A)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open MvPolynomial TopologicalSpace PrimeSpectrum Cardinal

universe u

namespace AlgebraicGeometry

/-- A morphism to the spectrum of a field has compact source as soon as its base change to the
affine space indexed by an affine cover of that source is a closed map: the complement of the
union, over the index set, of the intersection of a coordinate basic open with the
corresponding cover member is closed, and its image misses a suitable point, which forces
finitely many cover members to suffice. -/
private theorem compactSpace_of_affineCoverPolynomial_closed
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    (hclosed : IsClosedMap
      (pullback.snd f (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : K →+* MvPolynomial X.directedAffineCover.I₀ K))))) :
    CompactSpace X := by
  classical
  let 𝒰 : X.OpenCover := X.directedAffineCover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := i.2
  have (i : 𝒰.I₀) : CompactSpace (𝒰.X i) := Scheme.compactSpace_of_isAffine _
  let U (i : 𝒰.I₀) : X.Opens := (𝒰.f i).opensRange
  let T : Scheme := Spec (.of <| MvPolynomial 𝒰.I₀ K)
  let q : T ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom MvPolynomial.C)
  let Ti (i : 𝒰.I₀) : T.Opens := basicOpen (MvPolynomial.X i)
  let fT : pullback f q ⟶ T := pullback.snd f q
  let p : pullback f q ⟶ X := pullback.fst f q
  let Z : Set (pullback f q :) :=
    (⨆ i : 𝒰.I₀, fT ⁻¹ᵁ (Ti i) ⊓ p ⁻¹ᵁ (U i) : (pullback f q).Opens)ᶜ
  have hZ : IsClosed Z := by
    simp only [Z, isClosed_compl_iff, Opens.coe_iSup, Opens.coe_inf, Opens.map_coe]
    exact isOpen_iUnion fun i ↦ (fT.continuous.1 _ (Ti i).2).inter
      (p.continuous.1 _ (U i).2)
  let Zc : T.Opens := ⟨(fT '' Z)ᶜ, (hclosed _ hZ).isOpen_compl⟩
  let ψ : MvPolynomial 𝒰.I₀ K →ₐ[K] K := MvPolynomial.aeval (fun _ ↦ 1)
  let t : T := Spec.map (CommRingCat.ofHom ψ.toRingHom) default
  have ht (i : 𝒰.I₀) : t ∈ Ti i := show ψ (.X i) ≠ 0 by simp [ψ]
  have htZc : t ∈ Zc := by
    rintro ⟨z, hz, hzt⟩
    change z ∉ (⨆ i : 𝒰.I₀, fT ⁻¹ᵁ Ti i ⊓ p ⁻¹ᵁ U i : (pullback f q).Opens) at hz
    apply hz
    apply TopologicalSpace.Opens.mem_iSup.mpr
    refine ⟨𝒰.idx (p z), ?_⟩
    constructor
    · show fT z ∈ Ti (𝒰.idx (p z))
      rw [hzt]
      exact ht _
    · simpa [U] using 𝒰.covers (p z)
  obtain ⟨U', ⟨g, rfl⟩, htU', hU'le⟩ :=
    Opens.isBasis_iff_nbhd.mp isBasis_basic_opens htZc
  let σ : Finset 𝒰.I₀ := MvPolynomial.vars g
  let φ : MvPolynomial 𝒰.I₀ K →+* MvPolynomial 𝒰.I₀ K :=
    (MvPolynomial.aeval fun i : 𝒰.I₀ ↦ if i ∈ σ then MvPolynomial.X i else 0).toRingHom
  let t' : T := Spec.map (CommRingCat.ofHom φ) t
  have ht'g : t' ∈ PrimeSpectrum.basicOpen g :=
    show φ g ∉ t.asIdeal from
      (show φ g = g from aeval_ite_mem_eq_self g subset_rfl).symm ▸ htU'
  have h : t' ∉ fT '' Z := hU'le ht'g
  suffices ⋃ i ∈ σ, (U i).1 = Set.univ from
    ⟨this ▸ Finset.isCompact_biUnion _ fun i _ ↦ isCompact_range (𝒰.f i).continuous⟩
  rw [Set.iUnion₂_eq_univ_iff]
  contrapose! h
  obtain ⟨x, hx⟩ := h
  obtain ⟨z, rfl, hzr⟩ :=
    Scheme.Pullback.exists_preimage_pullback x t' (Subsingleton.elim (f x) (q t'))
  suffices ∀ i, t ∈ (Ti i).comap ⟨_, continuous_comap φ⟩ → p z ∉ U i from
    ⟨z, by simpa [Z, p, fT, hzr]⟩
  intro i hi₁ hi₂
  rw [comap_basicOpen, show φ (.X i) = 0 by simpa [φ] using (hx i · hi₂),
    basicOpen_zero] at hi₁
  exact hi₁.elim

-- The cardinal estimates across the coproduct and polynomial ring need extra reduction steps.
/-- The polynomial algebra over a ring `K` on the affine opens of a scheme `X` inside the site
has spectrum inside the site: the disjoint union of `X` and `Spec K` is in the site, both
cardinalities are bounded by its size, and the cutoff is a strong limit.

This is what makes the test scheme of the closedness argument of **Stacks 04XW** — affine space
over the base whose coordinates are indexed by an affine cover of the source — an object of the
site, so that a closedness condition quantified inside the site applies to it. It is used both
by `AlgebraicGeometry.universallyClosed_of_bounded_closed_baseChanges` below, for schemes, and
by `AlgebraicGeometry.Space.isQuasiCompact_of_universallyClosed`, for algebraic spaces. -/
theorem affineCoverPolynomial_size_lt (B : BigFppfSite.{u})
    {X : Scheme.{u}} (hX : X.size < B.cutoff)
    (K : Type u) [CommRing K] (hK : (Spec (.of K)).size < B.cutoff) :
    (Spec (.of (MvPolynomial X.directedAffineCover.I₀ K))).size < B.cutoff := by
  let A : ULift.{u} WalkingPair → Scheme.{u} := fun i => i.down.casesOn X (Spec (.of K))
  let Wsum : Scheme := ∐ A
  have hWsum : Wsum.size < B.cutoff := by
    apply Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
      (ι := ULift.{u} WalkingPair) (Y := A) (by simp)
    intro b
    rcases b with ⟨b⟩
    cases b with
    | left => simpa [A] using hX
    | right => simpa [A] using hK
  let W : Scheme := X ⨿ Spec (.of K)
  have hW : W.size < B.cutoff := by
    rwa [Scheme.size_congr (coprodIsoSigma X (Spec (.of K)))]
  have hXW : X.size ≤ W.size :=
    Scheme.size_le_of_mono_locallyOfFinitePresentation (coprod.inl : X ⟶ W)
  have hKW : (Spec (.of K)).size ≤ W.size :=
    Scheme.size_le_of_mono_locallyOfFinitePresentation (coprod.inr : Spec (.of K) ⟶ W)
  have hKcard : Cardinal.mk K ≤ W.size := by
    rw [Scheme.size_Spec] at hKW
    exact (le_max_right _ _).trans hKW
  have hIcard : Cardinal.mk X.directedAffineCover.I₀ ≤ W.size :=
    X.mk_affineOpens_le_size.trans hXW
  have hpoly : Cardinal.mk (MvPolynomial X.directedAffineCover.I₀ K) ≤ W.size ^ ℵ₀ := by
    calc
      Cardinal.mk (MvPolynomial X.directedAffineCover.I₀ K) ≤
          Cardinal.mk K ⊔ Cardinal.mk X.directedAffineCover.I₀ ⊔ ℵ₀ :=
            MvPolynomial.cardinalMk_le_max
      _ ≤ W.size := sup_le (sup_le hKcard hIcard) W.aleph0_le_size
      _ ≤ W.size ^ ℵ₀ := Cardinal.self_le_power _ one_le_aleph0
  exact Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (CommRingCat.of (MvPolynomial X.directedAffineCover.I₀ K)) hW hpoly

/-- **Affine `n`-space over a scheme inside the site is inside the site.** It is the fibre
product of that scheme with the spectrum of a polynomial ring over `ℤ` in `n` variables, which
is of finite type over `Spec ℤ`, and the cutoff is a strong prelimit closed under fibre
products. -/
theorem BigFppfSite.contains_affineSpace (B : BigFppfSite.{u})
    {X : Scheme.{u}} (hX : B.Contains X) (n : ℕ) :
    B.Contains (AffineSpace (ULift.{u} (Fin n)) X) := by
  let R : Type u := ULift ℤ
  let A : Type u := MvPolynomial (ULift.{u} (Fin n)) R
  have hR : (Spec (.of R)).size < B.cutoff := by
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff (Cardinal.mk_le_aleph0.trans_lt B.aleph0_lt_cutoff)
  have hA : (Spec (.of A)).size < B.cutoff :=
    Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit R A hR
  show (pullback (terminal.from X) (terminal.from (Spec (.of A)))).size < B.cutoff
  exact Scheme.size_pullback_lt _ _ hX hA

/-- If the base change of `f` along `g` is a closed map, so is the second projection of any
pullback square on `f` and `g`. -/
private theorem isClosedMap_of_isPullback {X Y Z P : Scheme.{u}} {f : X ⟶ Y} {g : Z ⟶ Y}
    {a : P ⟶ X} {b : P ⟶ Z} (sq : IsPullback a b f g)
    (h : IsClosedMap (pullback.snd f g)) : IsClosedMap b := by
  rw [← sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback f g)]
  exact h.comp (sq.isoIsPullback _ _ (IsPullback.of_hasPullback f g)).hom.isClosedMap

/-- **The size-cutoff bridge.** A morphism of schemes *inside* a big fppf site is universally
closed as soon as its base changes along morphisms from schemes inside that site are closed
maps — even though `AlgebraicGeometry.UniversallyClosed` quantifies over base changes by *all*
schemes.

This is what makes a point-set closedness condition quantified over algebraic spaces over `S`,
as in **Stacks 03HI**, strong enough to give Mathlib's `UniversallyClosed`. -/
theorem universallyClosed_of_bounded_closed_baseChanges
    (B : BigFppfSite.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hX : B.Contains X) (hY : B.Contains Y)
    (hclosed : ∀ (Z : Scheme.{u}) (_ : B.Contains Z) (g : Z ⟶ Y),
      IsClosedMap (pullback.snd f g)) : UniversallyClosed f := by
  classical
  have hclosedF : IsClosedMap f :=
    isClosedMap_of_isPullback (IsPullback.of_horiz_isIso (by simp) : IsPullback (𝟙 X) f f (𝟙 Y))
      (hclosed Y hY (𝟙 Y))
  have hcompactFiber (y : Y) : IsCompact (f ⁻¹' {y}) := by
    let K := Y.residueField y
    let fy := Y.fromSpecResidueField y
    let F := pullback f fy
    have hK : B.Contains (Spec (.of K)) := (Scheme.size_le_of_mono_quasiCompact fy).trans_lt hY
    have hF : B.Contains F := Scheme.size_pullback_lt f fy hX hK
    let q : Spec (.of (MvPolynomial F.directedAffineCover.I₀ K)) ⟶ Spec (.of K) :=
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial F.directedAffineCover.I₀ K))
    have hq : B.Contains (Spec (.of (MvPolynomial F.directedAffineCover.I₀ K))) :=
      affineCoverPolynomial_size_lt B hF K hK
    have hclosedPoly : IsClosedMap (pullback.snd (pullback.snd f fy) q) := by
      exact isClosedMap_of_isPullback ((IsPullback.of_hasPullback _ q).paste_horiz
        (IsPullback.of_hasPullback f fy)) (hclosed _ hq (q ≫ fy))
    have : CompactSpace F :=
      compactSpace_of_affineCoverPolynomial_closed (pullback.snd f fy) hclosedPoly
    rw [← Scheme.range_fromSpecResidueField, ← Scheme.Pullback.range_fst]
    exact isCompact_range (Scheme.Hom.continuous (pullback.fst f fy))
  have hproper : IsProperMap (f : X → Y) :=
    (isProperMap_iff_isClosedMap_and_compact_fibers).2
      ⟨f.continuous, hclosedF, hcompactFiber⟩
  have : QuasiCompact f := ⟨fun _ _ hK => hproper.isCompact_preimage hK⟩
  have htest : ∀ n : ℕ, IsClosedMap (AffineSpace.map (ULift.{u} (Fin n)) f) := by
    intro n
    let Z := AffineSpace (ULift.{u} (Fin n)) Y
    let proj : Z ⟶ Y := AffineSpace (ULift.{u} (Fin n)) Y ↘ Y
    have hZ : B.Contains Z := B.contains_affineSpace hY n
    exact isClosedMap_of_isPullback (AffineSpace.isPullback_map (n := ULift.{u} (Fin n)) f).flip
      (hclosed Z hZ proj)
  exact ((universallyClosed_tfae f).out 3 1).mp htest

end AlgebraicGeometry

end
