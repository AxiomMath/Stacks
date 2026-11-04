module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniEvaluationMatrix
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.DenseFlatLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange

/-!
# The universal family over an open of the parameter space, and the open where it is flat

Work in the standing situation of the Bertini theorems ([Stacks, Tag 0G47]) and write
`q : H_univ → 𝔸^r_k` for the universal family. The proof of [Stacks, Tag 0FD6] is a statement
about a nonempty open of the parameter space, so every step of it may be run over a nonempty
open `W ⊂ 𝔸^r_k` chosen in advance. This module sets that up: it introduces `q⁻¹(W) → 𝔸^r_k`,
the restriction of `q` to the part of `H_univ` over `W` — still a morphism to the *whole*
parameter space, so that the dimension count of
`StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.NonSmoothLocusFibreDimension` applies to it
verbatim — and proves that a dimension bound for *its* non-smooth locus already gives `hsing`.

The point of running the argument over an open is **flatness**. The morphism `q` is of finite
type over the integral scheme `𝔸^r_k`, so generic flatness ([Stacks, Tag 052B]) provides a dense
— hence nonempty, `𝔸^r_k` being irreducible — open `W` over which it becomes flat, with no
hypothesis beyond `X` being of finite type over `k`. Flatness of `q⁻¹(W) → 𝔸^r_k` is what the
Jacobian criterion of
`StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.ZeroSchemeStalkRegular` consumes, and the
restriction to `W` costs nothing because the conclusion of Tag 0FD6 is itself only a statement
over some nonempty open.

## Main definitions

* `Stacks.Bertini.FamilyDivisors.universalDivisorSchemeOver`: the open `q⁻¹(W)` of `H_univ`.
* `Stacks.Bertini.FamilyDivisors.universalFamilyMapOver`: the morphism `q⁻¹(W) → 𝔸^r_k`.
* `Stacks.Bertini.FamilyDivisors.nonSmoothToXOver`: the projection to `X` of the non-smooth locus
  of that morphism.

## Main results

* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_flat_universalFamilyMapOver`: **the
  nonempty open of the parameter space over which the universal family is flat**, from generic
  flatness.
* `Stacks.Bertini.FamilyDivisors.smoothLocus_universalFamilyMapOver`: the smooth locus of the
  restriction is the part of the smooth locus of `q` lying over `W`.
* `Stacks.Bertini.FamilyDivisors.mem_smoothLocus_of_isPullback_of_mem_smoothLocus`: **from the
  divisor to the morphism.** Over an open where the family is flat, a point at which the divisor
  of a `k'`-point is smooth over `k'` is a point of smoothness of `q`.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_fiber_le_over`:
  **`hsing` from a fibre bound over `W` only.** If the fibres of `Σ_W → X` have dimension at
  most `r - (n + 1)`, there is a nonempty open `U ⊂ 𝔸^r_k` with `q ⁻¹ᵁ U` inside the smooth
  locus of `q` — the open being `W ⊓ U'` for the open `U'` the count produces.
* `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_closedPoints_over`:
  **`hsing` with no dimension data assumed.** The same conclusion from a bound by `r - 1` on the
  sum of the dimension of the fibre of `Σ_W → X` over a closed point `x` of `X` and the local
  dimension of `X` at `x`; nothing is assumed about `dim X`, and a closed point where `X` has
  smaller dimension may have a larger fibre.
* `Stacks.Bertini.FamilyDivisors.topologicalKrullDim_fiber_nonSmoothToXOver_le_of_closedPoints`:
  the fibre bound for `Σ_W → X` from a closed subset of `q⁻¹(W)` containing its non-smooth
  closed points, the analogue over `W` of
  `Stacks.Bertini.FamilyDivisors.topologicalKrullDim_fiber_nonSmoothToX_le_of_closedPoints`.

## Implementation notes

`q⁻¹(W) → 𝔸^r_k` is written as the open immersion `q⁻¹(W) → H_univ` followed by `q`, rather than
as `AlgebraicGeometry.Scheme.Hom.resLE` into `W`: the target is then the affine space the
dimension count needs, the smooth locus is compared with that of `q` by
`AlgebraicGeometry.Scheme.Hom.preimage_smoothLocus_eq`, and flatness transfers from the
restriction `q ∣_ W` because an open immersion is flat and flatness is stable under composition.

Nothing here is a restriction of the *parameter space* `𝔸^r_X`; the open `W` is pulled back to
`H_univ` directly, so no comparison of two presentations of `q⁻¹(W)` is needed — contrast
`StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniFlatFamily`, which restricts `𝔸^r_X` and
pays for it with the isomorphism
`Stacks.Bertini.FamilyDivisors.restrictedUniversalFamilyIso`.

No `@[stacks]` attribute is attached: these are steps inside the proof of Tag 0FD6.

## References

* [Stacks Project, Tag 0FD6](https://stacks.math.columbia.edu/tag/0FD6)
* [Stacks Project, Tag 0G47](https://stacks.math.columbia.edu/tag/0G47)
* [Stacks Project, Tag 052B](https://stacks.math.columbia.edu/tag/052B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

namespace Stacks.Bertini.FamilyDivisors

variable (D : FamilyDivisors.{u, v})

/-- **`q` is quasi-compact** when `X` is quasi-compact over `k`: a closed immersion followed by
the base change `𝔸^r_X → 𝔸^r_k` of `X → Spec k`. -/
instance quasiCompact_universalFamilyMap [QuasiCompact D.toBase] :
    QuasiCompact D.universalFamilyMap :=
  haveI := D.quasiCompact_parameterBaseMap
  MorphismProperty.comp_mem _ _ _ inferInstance inferInstance

variable (W : D.parameterBase.Opens)

/-- **The part `q⁻¹(W)` of the universal divisor lying over an open `W` of the parameter
space.** -/
abbrev universalDivisorSchemeOver : D.universalDivisorScheme.Opens := D.universalFamilyMap ⁻¹ᵁ W

/-- **The universal family restricted to the part over `W`**, as a morphism to the whole
parameter space `𝔸^r_k`. -/
def universalFamilyMapOver : (D.universalDivisorSchemeOver W).toScheme ⟶ D.parameterBase :=
  (D.universalDivisorSchemeOver W).ι ≫ D.universalFamilyMap

/-- The restriction of the universal family over `W` is locally of finite presentation. -/
instance locallyOfFinitePresentation_universalFamilyMapOver [Smooth D.toBase] :
    LocallyOfFinitePresentation (D.universalFamilyMapOver W) :=
  inferInstanceAs (LocallyOfFinitePresentation
    ((D.universalDivisorSchemeOver W).ι ≫ D.universalFamilyMap))

/-- The open `q⁻¹(W)` of a noetherian universal divisor is a noetherian space. -/
instance noetherianSpace_universalDivisorSchemeOver
    [NoetherianSpace D.universalDivisorScheme] :
    NoetherianSpace (D.universalDivisorSchemeOver W).toScheme :=
  (D.universalDivisorSchemeOver W).ι.isOpenEmbedding.isInducing.noetherianSpace

/-- **The smooth locus of the restriction is the part of the smooth locus of `q` over `W`.**
Smoothness at a point is unchanged by passing to an open neighbourhood of it in the source. -/
theorem smoothLocus_universalFamilyMapOver [Smooth D.toBase] :
    (D.universalFamilyMapOver W).smoothLocus =
      (D.universalDivisorSchemeOver W).ι ⁻¹ᵁ D.universalFamilyMap.smoothLocus :=
  (Scheme.Hom.preimage_smoothLocus_eq _ _).symm

/-- **The universal family becomes flat over a nonempty open of the parameter space.** The
morphism `q` is of finite type and quasi-compact over the integral scheme `𝔸^r_k`, so generic
flatness ([Stacks, Tag 052B]) makes it flat over a dense open, and a dense open of the
irreducible space `𝔸^r_k` is nonempty.

This is the input the Jacobian criterion needs, and the restriction to an open of the parameter
space costs nothing in [Stacks, Tag 0FD6], whose conclusion is a statement over a nonempty
open. -/
theorem exists_nonempty_opens_flat_universalFamilyMapOver [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [QuasiCompact D.toBase] :
    ∃ W : D.parameterBase.Opens, (W : Set D.parameterBase).Nonempty ∧
      Flat (D.universalFamilyMapOver W) := by
  have := D.irreducibleSpace_parameterBase
  have : LocallyOfFiniteType D.universalFamilyMap := D.locallyOfFiniteType_universalFamily
  obtain ⟨W, hW, hflat, -⟩ :=
    exists_dense_open_flat_finitePresentation_structureSheaf D.universalFamilyMap
  refine ⟨W, hW.nonempty, ?_⟩
  rw [universalFamilyMapOver, ← Scheme.Hom.resLE_comp_ι (f := D.universalFamilyMap) (U := W)
    (V := D.universalFamilyMap ⁻¹ᵁ W) le_rfl]
  infer_instance

/-- **From the divisor to the morphism, over an open where the family is flat.** Let `W` be an
open of the parameter space over which `q⁻¹(W) → 𝔸^r_k` is flat, let `a` be the coordinate tuple
of a `k'`-point of `W`, and let the square of `H`, `H_univ`, `Spec k'` and `𝔸^r_k` be cartesian,
presenting `H` as the divisor of that point. Then `q` is smooth at the image of every point of
`H` at which `H → Spec k'` is smooth.

This is the step of the proof of [Stacks, Tag 0FD6] which turns smoothness of the divisor `H_a`
— what the Jacobian criterion delivers — into smoothness of the morphism `q`, and it is exactly
where flatness is used: the smooth locus of a base change is the inverse image of the smooth
locus ([Stacks, Tag 02V4]) as soon as the morphism or the base change map is flat, and the point
of `𝔸^r_k` classifying `a` is not flat, so the flatness has to come from `q` itself. Over the
whole of `𝔸^r_k` it is unavailable; over `W` it is
`Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_flat_universalFamilyMapOver`. -/
theorem mem_smoothLocus_of_isPullback_of_mem_smoothLocus [Smooth D.toBase]
    (hflat : Flat (D.universalFamilyMapOver W)) {K : Type u} [Field K] [Algebra D.k K]
    (a : Fin (Module.finrank D.k D.V) → K)
    (ha : ∀ p : Spec (.of K), D.parameterPoint a p ∈ W) {H : Scheme.{u}}
    (c : H ⟶ D.universalDivisorScheme) (g : H ⟶ Spec (.of K))
    (hsq : IsPullback c g D.universalFamilyMap (D.parameterPoint a))
    [LocallyOfFinitePresentation g] (z : H) (hz : z ∈ g.smoothLocus) :
    c.base z ∈ D.universalFamilyMap.smoothLocus := by
  have hrange : Set.range c ⊆ Set.range (D.universalDivisorSchemeOver W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show D.universalFamilyMap.base (c.base y) ∈ W
    rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]
    exact ha _
  have hbig := (IsOpenImmersion.isPullback_lift_id c
    (D.universalDivisorSchemeOver W).ι hrange).paste_vert hsq
  rw [Category.id_comp] at hbig
  have hfac : IsOpenImmersion.lift (D.universalDivisorSchemeOver W).ι c hrange ≫
      (D.universalDivisorSchemeOver W).ι = c := IsOpenImmersion.lift_fac _ _ _
  have hlift : g.smoothLocus =
      IsOpenImmersion.lift (D.universalDivisorSchemeOver W).ι c hrange ⁻¹ᵁ
        (D.universalFamilyMapOver W).smoothLocus :=
    have := hflat
    Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hbig (Or.inl hflat)
  rw [hlift, Scheme.Hom.mem_preimage, D.smoothLocus_universalFamilyMapOver W,
    Scheme.Hom.mem_preimage] at hz
  rwa [← Scheme.Hom.comp_apply, hfac] at hz

/-! ### The dimension count over `W` -/

/-- **The structure morphism `q⁻¹(W) → Spec k`.** -/
def universalDivisorToBaseOver : (D.universalDivisorSchemeOver W).toScheme ⟶ Spec (.of D.k) :=
  (D.universalDivisorSchemeOver W).ι ≫ D.universalDivisorToBase

/-- The structure morphism `q⁻¹(W) → Spec k` is locally of finite type. -/
instance locallyOfFiniteType_universalDivisorToBaseOver [LocallyOfFiniteType D.toBase] :
    LocallyOfFiniteType (D.universalDivisorToBaseOver W) :=
  inferInstanceAs (LocallyOfFiniteType
    ((D.universalDivisorSchemeOver W).ι ≫ D.universalDivisorToBase))

/-- **`q⁻¹(W) → 𝔸^r_k` lies over `Spec k`.** -/
theorem universalFamilyMapOver_comp_over :
    D.universalFamilyMapOver W ≫ (𝔸(D.basisIndex; Spec (.of D.k)) ↘ Spec (.of D.k)) =
      D.universalDivisorToBaseOver W := by
  rw [universalFamilyMapOver, universalDivisorToBaseOver, Category.assoc,
    D.universalFamilyMap_comp_over]

/-- **The projection `Σ_W → X`** of the non-smooth locus of `q⁻¹(W) → 𝔸^r_k` to the ambient
scheme. -/
def nonSmoothToXOver [Smooth D.toBase] :
    (D.universalFamilyMapOver W).nonSmoothSubscheme ⟶ D.X :=
  (D.universalFamilyMapOver W).nonSmoothSubschemeι ≫ (D.universalDivisorSchemeOver W).ι ≫
    D.universalDivisor.subschemeι ≫ D.parameterProjection

/-- **The projection `Σ_W → X` lies over `Spec k`**, which is the compatibility square the
dimension count consumes. -/
theorem nonSmoothToXOver_comp_toBase [Smooth D.toBase] :
    D.nonSmoothToXOver W ≫ D.toBase =
      (D.universalFamilyMapOver W).nonSmoothSubschemeι ≫ D.universalDivisorToBaseOver W := by
  rw [nonSmoothToXOver, universalDivisorToBaseOver, universalDivisorToBase]
  simp only [Category.assoc]

/-- The projection `Σ_W → X` is locally of finite type. -/
instance locallyOfFiniteType_nonSmoothToXOver [Smooth D.toBase] :
    LocallyOfFiniteType (D.nonSmoothToXOver W) := by
  rw [nonSmoothToXOver]
  have h₁ : LocallyOfFiniteType D.parameterProjection :=
    inferInstanceAs (LocallyOfFiniteType (𝔸(D.basisIndex; D.X) ↘ D.X))
  exact MorphismProperty.comp_mem _ _ _ inferInstance (MorphismProperty.comp_mem _ _ _
    inferInstance (MorphismProperty.comp_mem _ _ _ inferInstance h₁))

/-- A nonempty open `U'` over which the restriction to `q⁻¹(W)` is smooth gives the nonempty open
`W ⊓ U'` over which `q` is smooth. -/
private theorem exists_nonempty_opens_subset_smoothLocus_of_restricted [Smooth D.toBase]
    (hW : (W : Set D.parameterBase).Nonempty) (U' : D.parameterBase.Opens)
    (hU' : (U' : Set D.parameterBase).Nonempty)
    (hsub : ((D.universalFamilyMapOver W ⁻¹ᵁ U' : (D.universalDivisorSchemeOver W).toScheme.Opens) :
      Set (D.universalDivisorSchemeOver W).toScheme) ⊆
        (D.universalFamilyMapOver W).smoothLocus) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) := by
  have := D.irreducibleSpace_parameterBase
  obtain ⟨y, -, hy⟩ := (IrreducibleSpace.isIrreducible_univ D.parameterBase).2
    (W : Set D.parameterBase) (U' : Set D.parameterBase) W.isOpen U'.isOpen
    (let ⟨y, hy⟩ := hW; ⟨y, trivial, hy⟩) (let ⟨y, hy⟩ := hU'; ⟨y, trivial, hy⟩)
  refine ⟨W ⊓ U', ⟨y, hy⟩, fun z hz => ?_⟩
  have := hsub (by change (⟨z, hz.1⟩ : (D.universalDivisorSchemeOver W).toScheme) ∈
    D.universalFamilyMapOver W ⁻¹ᵁ U'; exact hz.2)
  rwa [D.smoothLocus_universalFamilyMapOver W] at this

/-- **`hsing` from a fibre bound over `W` only.** With `r` the dimension of the linear system,
suppose `dim X ≤ n`, suppose `n + 1 ≤ r`, and suppose every fibre of the projection
`Σ_W → X` of the non-smooth locus of `q⁻¹(W) → 𝔸^r_k` has local dimension at most
`r - (n + 1)`. Then there is a nonempty open `U ⊂ 𝔸^r_k` whose preimage under `q` lies in the
smooth locus of `q`.

The dimension count produces a nonempty open `U'` over which the *restricted* family is smooth;
intersecting it with `W` — which is legitimate because `𝔸^r_k` is irreducible, so two nonempty
opens meet — turns that into a statement about `q` itself, every point of `q ⁻¹ᵁ (W ⊓ U')` being
a point of `q⁻¹(W)`. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_fiber_le_over [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] [NoetherianSpace D.universalDivisorScheme]
    (hW : (W : Set D.parameterBase).Nonempty) {n : ℕ}
    (hnr : n + 1 ≤ Nat.card D.basisIndex)
    (hX : topologicalKrullDim D.X ≤ (n : WithBot ℕ∞))
    (hfib : ∀ z : (D.universalFamilyMapOver W).nonSmoothSubscheme,
      topologicalKrullDimAt ((D.nonSmoothToXOver W).fiber (D.nonSmoothToXOver W z))
          ((D.nonSmoothToXOver W).asFiber z) ≤
        ((Nat.card D.basisIndex - (n + 1) : ℕ) : WithBot ℕ∞)) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) := by
  have := D.irreducibleSpace_parameterBase
  obtain ⟨U', hU', hsub⟩ :=
    AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus_of_fiber_le D.k
      D.basisIndex (D.universalFamilyMapOver W) (D.universalDivisorToBaseOver W)
      (D.universalFamilyMapOver_comp_over W) D.toBase (D.nonSmoothToXOver W)
      (D.nonSmoothToXOver_comp_toBase W) hnr hX hfib
  exact D.exists_nonempty_opens_subset_smoothLocus_of_restricted W hW U' hU' hsub

/-- **`hsing` from a fibre-plus-target bound over the closed points of `X`, over `W` only.**
With `r` the dimension of the linear system, suppose `1 ≤ r` and suppose that over every closed
point `x` of `X` the dimension of the fibre of `Σ_W → X` and the local dimension of `X` at `x`
add up to at most `r - 1`. Then there is a nonempty open `U ⊂ 𝔸^r_k` whose preimage under `q`
lies in the smooth locus of `q`.

This is `Stacks.Bertini.FamilyDivisors.exists_nonempty_opens_subset_smoothLocus_of_fiber_le_over`
with the two separate bounds `dim X ≤ n` and `dim Σ_x ≤ r - (n + 1)` replaced by the single
bound on their sum. Nothing is assumed about the dimension of `X`: the local dimension at `x`
appears in the hypothesis itself, so a closed point where `X` has small dimension is allowed to
have a fibre of correspondingly larger dimension, which is what happens when `X` is not
equidimensional. The underlying count is
`AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus_of_closedPoints`;
the passage from closed points of `X` to closed points of `Σ_W`, which the count asks for, is
Tag 01TB — a point closed in `Σ_W` maps to a point closed in `X` — together with the local
dimension of a fibre being at most the dimension of that fibre. -/
theorem exists_nonempty_opens_subset_smoothLocus_of_closedPoints_over
    [Smooth D.toBase] [LocallyOfFiniteType D.toBase]
    [NoetherianSpace D.universalDivisorScheme] (hW : (W : Set D.parameterBase).Nonempty)
    (hr : 1 ≤ Nat.card D.basisIndex)
    (hclosed : ∀ x : D.X, IsClosed ({x} : Set D.X) →
      topologicalKrullDim ((D.nonSmoothToXOver W).fiber x) + topologicalKrullDimAt D.X x ≤
        ((Nat.card D.basisIndex - 1 : ℕ) : WithBot ℕ∞)) :
    ∃ U : D.parameterBase.Opens, (U : Set D.parameterBase).Nonempty ∧
      ((D.universalFamilyMap ⁻¹ᵁ U : D.universalDivisorScheme.Opens) :
          Set D.universalDivisorScheme) ⊆
        (D.universalFamilyMap.smoothLocus : Set D.universalDivisorScheme) := by
  have := D.irreducibleSpace_parameterBase
  let := D.jacobsonSpace_X
  have hfib : ∀ z : (D.universalFamilyMapOver W).nonSmoothSubscheme,
      IsClosed ({z} : Set (D.universalFamilyMapOver W).nonSmoothSubscheme) →
      topologicalKrullDimAt ((D.nonSmoothToXOver W).fiber (D.nonSmoothToXOver W z))
          ((D.nonSmoothToXOver W).asFiber z) +
          topologicalKrullDimAt D.X (D.nonSmoothToXOver W z) ≤
        ((Nat.card D.basisIndex - 1 : ℕ) : WithBot ℕ∞) := by
    intro z hz
    have hpz : IsClosed ({D.nonSmoothToXOver W z} : Set D.X) :=
      (D.nonSmoothToXOver W).closePoints_subset_preimage_closedPoints hz
    exact le_trans (add_le_add (topologicalKrullDimAt_le_topologicalKrullDim
      ((D.nonSmoothToXOver W).asFiber z)) le_rfl) (hclosed _ hpz)
  obtain ⟨U', hU', hsub⟩ :=
    AlgebraicGeometry.exists_nonempty_opens_preimage_subset_smoothLocus_of_closedPoints
      D.k D.basisIndex (D.universalFamilyMapOver W) (D.universalDivisorToBaseOver W)
      (D.universalFamilyMapOver_comp_over W) D.toBase (D.nonSmoothToXOver W)
      (D.nonSmoothToXOver_comp_toBase W) hr hfib
  exact D.exists_nonempty_opens_subset_smoothLocus_of_restricted W hW U' hU' hsub

/-! ### Reduction of the fibre bound over `W` to the closed points -/

/-- **`q⁻¹(W)` is a Jacobson space**, being locally of finite type over the field `k`. -/
theorem jacobsonSpace_universalDivisorSchemeOver [LocallyOfFiniteType D.toBase] :
    JacobsonSpace (D.universalDivisorSchemeOver W).toScheme :=
  let : JacobsonSpace (Spec (CommRingCat.of D.k)) := inferInstance
  LocallyOfFiniteType.jacobsonSpace (D.universalDivisorToBaseOver W)

/-- **`Σ_W` is a Jacobson space**, being locally of finite type over `X`, which is itself
locally of finite type over the field `k`. -/
theorem jacobsonSpace_nonSmoothSubschemeOver [Smooth D.toBase] [LocallyOfFiniteType D.toBase] :
    JacobsonSpace (D.universalFamilyMapOver W).nonSmoothSubscheme :=
  let := D.jacobsonSpace_X
  LocallyOfFiniteType.jacobsonSpace (D.nonSmoothToXOver W)

/-- **The fibre bound at every point of `Σ_W` from the bound over the closed points of `X`.** -/
theorem fiber_nonSmoothToXOver_le_of_isClosed_singleton [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] {m : ℕ}
    (hclosed : ∀ x : D.X, IsClosed {x} →
      topologicalKrullDim ((D.nonSmoothToXOver W).fiber x) ≤ (m : WithBot ℕ∞))
    (z : (D.universalFamilyMapOver W).nonSmoothSubscheme) :
    topologicalKrullDimAt ((D.nonSmoothToXOver W).fiber (D.nonSmoothToXOver W z))
        ((D.nonSmoothToXOver W).asFiber z) ≤ (m : WithBot ℕ∞) :=
  let := D.jacobsonSpace_X
  let := D.jacobsonSpace_nonSmoothSubschemeOver W
  AlgebraicGeometry.fiberDimensionAt_le_of_isClosed_singleton_target (D.nonSmoothToXOver W)
    hclosed z

/-- **The fibre of `Σ_W → X` over `x`, read inside `q⁻¹(W)`.** Any subset of `q⁻¹(W)` containing
the points of `q⁻¹(W)` which lie over `x` and at which `q` is not smooth bounds the dimension of
the scheme-theoretic fibre. -/
theorem topologicalKrullDim_fiber_nonSmoothToXOver_le_of_subset [Smooth D.toBase] (x : D.X)
    {d : WithBot ℕ∞} (Z : Set (D.universalDivisorSchemeOver W).toScheme)
    (hZ : {w : (D.universalDivisorSchemeOver W).toScheme |
        w ∉ (D.universalFamilyMapOver W).smoothLocus ∧
        D.parameterProjection.base (D.universalDivisor.subschemeι.base
          ((D.universalDivisorSchemeOver W).ι.base w)) = x} ⊆ Z)
    (hdim : topologicalKrullDim Z ≤ d) :
    topologicalKrullDim ((D.nonSmoothToXOver W).fiber x) ≤ d := by
  set ι := (D.universalFamilyMapOver W).nonSmoothSubschemeι with hιdef
  have hemb : Topology.IsEmbedding ι.base := ι.isClosedEmbedding.isEmbedding
  set A : Set (D.universalFamilyMapOver W).nonSmoothSubscheme :=
    (D.nonSmoothToXOver W).base ⁻¹' {x} with hAdef
  have himg : ι.base '' A ⊆ Z := by
    rintro _ ⟨z, hz, rfl⟩
    exact hZ ⟨Scheme.Hom.notMem_smoothLocus_nonSmoothSubschemeι _ z, hz⟩
  refine AlgebraicGeometry.topologicalKrullDim_fiber_le_of_preimage_subset
    (D.nonSmoothToXOver W) x A (le_refl _) ?_
  exact le_trans (le_of_eq (IsHomeomorph.topologicalKrullDim_eq _
    (hemb.homeomorphImage A).isHomeomorph)) (le_trans (topologicalKrullDim_le_of_subset himg)
      hdim)

/-- **The non-smooth points of `q⁻¹(W)` over a closed point `x` of `X` form a closed set.** -/
theorem isClosed_nonSmooth_over_over [Smooth D.toBase] {x : D.X} (hx : IsClosed {x}) :
    IsClosed {w : (D.universalDivisorSchemeOver W).toScheme |
      w ∉ (D.universalFamilyMapOver W).smoothLocus ∧
      D.parameterProjection.base (D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w)) = x} := by
  have h₁ : IsClosed (((D.universalFamilyMapOver W).smoothLocus :
      Set (D.universalDivisorSchemeOver W).toScheme)ᶜ) :=
    Scheme.Hom.isClosed_compl_smoothLocus (D.universalFamilyMapOver W)
  have h₂ : IsClosed (((D.universalDivisorSchemeOver W).ι ≫ D.universalDivisor.subschemeι ≫
      D.parameterProjection).base ⁻¹' {x}) :=
    hx.preimage ((D.universalDivisorSchemeOver W).ι ≫ D.universalDivisor.subschemeι ≫
      D.parameterProjection).base.hom.continuous
  exact h₁.inter h₂

/-- **The closed-point form of the fibre bound over `W`.** Let `x` be a closed point of `X` and
let `L` be a closed subset of `q⁻¹(W)` of dimension at most `d`. If every point of `q⁻¹(W)`
which is closed in `q⁻¹(W)`, lies over `x`, and is a point of non-smoothness of the restricted
family belongs to `L`, then the fibre of `Σ_W → X` over `x` has dimension at most `d`. -/
theorem topologicalKrullDim_fiber_nonSmoothToXOver_le_of_closedPoints [Smooth D.toBase]
    [LocallyOfFiniteType D.toBase] {x : D.X} (hx : IsClosed {x}) {d : WithBot ℕ∞}
    (L : Set (D.universalDivisorSchemeOver W).toScheme) (hL : IsClosed L)
    (hmem : ∀ w : (D.universalDivisorSchemeOver W).toScheme, IsClosed {w} →
      w ∉ (D.universalFamilyMapOver W).smoothLocus →
      D.parameterProjection.base (D.universalDivisor.subschemeι.base
        ((D.universalDivisorSchemeOver W).ι.base w)) = x → w ∈ L)
    (hdim : topologicalKrullDim L ≤ d) :
    topologicalKrullDim ((D.nonSmoothToXOver W).fiber x) ≤ d :=
  let := D.jacobsonSpace_universalDivisorSchemeOver W
  D.topologicalKrullDim_fiber_nonSmoothToXOver_le_of_subset W x L
    (Set.subset_of_isClosed_of_closedPoints_subset (D.isClosed_nonSmooth_over_over W hx) hL
      (fun w hw hwc ↦ hmem w hwc hw.1 hw.2)) hdim

end Stacks.Bertini.FamilyDivisors

end
