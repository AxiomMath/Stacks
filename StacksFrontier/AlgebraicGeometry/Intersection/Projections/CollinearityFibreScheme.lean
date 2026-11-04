module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityRatioLinear
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceDimension

/-!
# The scheme-theoretic fibre of the collinearity locus over a rational point

Let `V` be a vector space over a field `k` and `𝐏(V) = Proj (Sym_k V)`. The triple product
`𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)` is formed as `(𝐏(V) ×_k 𝐏(V)) ×_k 𝐏(V)`, so the projection
`AlgebraicGeometry.ProjectiveSpaceOfModule.prFst` to the first two factors is the base change of
the structure morphism `𝐏(V) ⟶ Spec k` along `𝐏(V) ×_k 𝐏(V) ⟶ Spec k`. A `k`-rational point of
`𝐏(V) ×_k 𝐏(V)` — a morphism `pt : Spec k ⟶ 𝐏(V) ×_k 𝐏(V)` over `Spec k` — therefore produces a
**section** `𝐏(V) ⟶ 𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)` of that base change, and the resulting square is
again a pullback. That makes the section a homeomorphism of `𝐏(V)` onto the scheme-theoretic
fibre `prFst.fiber q`: the fibre of `prFst` over a `k`-rational point **is** `𝐏(V)`.

This is the step the dimension count of [Stacks, Tag 0B1R] needs, and the shape it needs it in.
Every dimension-theoretic input is phrased with `AlgebraicGeometry.Scheme.Hom.fiber` — the bound
`AlgebraicGeometry.topologicalKrullDim_le_of_isClosed_singleton_fiber_add_target` asks for
`topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)`, and so do Tag 0B2L part (2b) and Tag 05F7 —
so the set-level identification of the collinear triples over a pair of distinct closed points,
`ProjectiveSpaceOfModule.mem_collinearLocus_iff_mem_linearSubspace_lineSubmodule`, is of no use to
them until it is known to compute that fibre's underlying space. Composing the section with that
identification does exactly this: the fibre of
`AlgebraicGeometry.ProjectiveSpaceOfModule.collinearProj` over a `k`-rational point whose two
projections are distinct closed points is homeomorphic to the line joining them, and therefore has
dimension one.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.prodTwoFst` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.prodTwoSnd`: the two projections of `𝐏(V) ×_k 𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.rationalFibreSection`: the section
  `𝐏(V) ⟶ 𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)`, `x ↦ (q, x)`, attached to a `k`-rational point `q` of
  `𝐏(V) ×_k 𝐏(V)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.prFstFiberHomeomorph`: the homeomorphism of `𝐏(V)`
  with the scheme-theoretic fibre of `prFst` over a `k`-rational point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.collinearProjFiberHomeomorph`: the homeomorphism of
  the scheme-theoretic fibre of `collinearProj` over a `k`-rational point with the line joining
  its two projections.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isPullback_rationalFibreSection`: **the square
  exhibiting the section as the base change of `prFst` along the rational point** is a pullback.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_rationalFibreSection`: the section's image is
  exactly the set-theoretic fibre of `prFst`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_fiber_prFst`: **the fibre of
  `prFst` over a `k`-rational point has the dimension of `𝐏(V)`.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.range_collinearFibreToProj`: **the collinear triples
  over a `k`-rational point, read in the fibre, are exactly the points of the line** joining the
  two projections of that point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_fiber_collinearProj`: **the
  scheme-theoretic fibre of `collinearProj` over a `k`-rational point whose two projections are
  distinct closed points has dimension one.**

## Implementation notes

The pullback square is obtained by cancelling the known one: pasted with the defining square of
the triple product it gives the square whose two horizontal arrows are identities, because `pt`
is a morphism over `Spec k` and the section's second component is the identity of `𝐏(V)`. That is
`CategoryTheory.IsPullback.of_right` against `CategoryTheory.IsPullback.of_id_fst`, and it is the
whole of the argument; no residue field is computed, and the identification
`κ(q) = k` that a direct comparison of `prFst.fiber q = pullback prFst (fromSpecResidueField q)`
with `Spec k ×_{𝐏(V) × 𝐏(V)} (𝐏(V) × 𝐏(V) × 𝐏(V))` would need never appears.

Only the image of the section is read off the pullback square, through
`AlgebraicGeometry.Scheme.Pullback.range_fst`. That the section is a topological embedding is
cheaper still: it is a section of `pr₃`, so `Topology.IsEmbedding.of_leftInverse` applies, and no
scheme-theoretic property of it is used. The two facts together make it a homeomorphism onto
`prFst ⁻¹' {q}`, which `AlgebraicGeometry.Scheme.Hom.fiberHomeo` turns into the statement about
`AlgebraicGeometry.Scheme.Hom.fiber`.

The rational point is given as a morphism `pt : Spec k ⟶ 𝐏(V) ×_k 𝐏(V)` over `Spec k` together
with the identification `Set.range pt.base = {q}` of its image, rather than through
`AlgebraicGeometry.IsRationalPoint`: that is the data the argument uses, and it is the form in
which a closed point of a scheme of finite type over an algebraically closed field hands one
over.

## Where this is used

The whole of [Stacks, Tag 0B1R] — the decomposition
`Y ∩ r_p^{-1}(r_p(Z)) = (Y ∩ Z) ∪ E` together with the bound
`dim E ≤ dim Y + dim Z + 1 - n` — is
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_inter_projectionCone_eq` in
`StacksFrontier/AlgebraicGeometry/Intersection/Projections/ProjectionConeDimension.lean`, which
carries the attribute. The fibre dimension proved here is one of the inputs to its count: it is
what makes the fibres of the incidence variety over `(Y ∖ Z) × Z` one-dimensional at the closed
points, hence `dim T ≤ dim Y + dim Z + 1`.

Irreducibility of the incidence variety is **not** needed: the count reaches the general fibre of
`T ⟶ 𝐏(V)` through
`AlgebraicGeometry.exists_isOpen_forall_topologicalKrullDim_fiber_add_le_of_ne_top`, which applies
part (2b) of Tag 0B2L to the irreducible components of the source one at a time.

Nothing here restricts the two projections of the rational point to be distinct except where the
line is named: the homeomorphism with the fibre of `prFst` holds for every `k`-rational point. On
the diagonal the fibre of `collinearProj` is the whole of `𝐏(V)` rather than a line, two
coincident points making every triple collinear, so the dimension-one statement does need the
two projections to differ, and the projection of the collinearity locus is not flat.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 05F7](https://stacks.math.columbia.edu/tag/05F7)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### The two projections of `𝐏(V) ×_k 𝐏(V)` -/

/-- The projection of `𝐏(V) ×_k 𝐏(V)` to its first factor. -/
public def prodTwoFst : prodTwo k V ⟶ projectiveSpaceOfModule k V :=
  pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V)

/-- The projection of `𝐏(V) ×_k 𝐏(V)` to its second factor. -/
public def prodTwoSnd : prodTwo k V ⟶ projectiveSpaceOfModule k V :=
  pullback.snd (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V)

/-- The first projection of the triple product factors through the first two factors. -/
public theorem pr₁_eq_prFst_comp : pr₁ k V = prFst k V ≫ prodTwoFst k V := rfl

/-- The second projection of the triple product factors through the first two factors. -/
public theorem pr₂_eq_prFst_comp : pr₂ k V = prFst k V ≫ prodTwoSnd k V := rfl

variable {k} in
/-- **`Spec k` is a single point**, so a morphism out of it has a singleton image. This is what
produces the identification of the image of a rational point that the results below ask for. -/
public theorem range_base_eq_singleton {W : Scheme.{u}} (ptm : Spec (CommRingCat.of k) ⟶ W)
    (x₀ : Spec (CommRingCat.of k)) : Set.range ptm.base = {ptm.base x₀} := by
  have : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    ⟨fun a b => Subsingleton.elim (α := PrimeSpectrum k) a b⟩
  ext y
  refine ⟨?_, ?_⟩
  · rintro ⟨w, rfl⟩
    exact congrArg ptm.base (Subsingleton.elim w x₀)
  · rintro rfl
    exact ⟨x₀, rfl⟩

/-! ### The section of the triple product attached to a rational point of the double product -/

/-- **The section of the triple product attached to a `k`-rational point of `𝐏(V) ×_k 𝐏(V)`**:
the morphism `x ↦ (q, x)` built from a morphism `pt : Spec k ⟶ 𝐏(V) ×_k 𝐏(V)` over `Spec k`.
It is a section of the third projection, and the square it forms with `prFst` and `pt` is a
pullback. -/
public def rationalFibreSection (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) :
    projectiveSpaceOfModule k V ⟶ prodThree k V :=
  pullback.lift (projectiveSpaceOfModuleToSpec k V ≫ pt) (𝟙 _) (by
    rw [Category.assoc, hpt, Category.comp_id, Category.id_comp])

variable {k V} in
/-- The first two components of the section are the rational point. -/
public theorem rationalFibreSection_comp_prFst (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) :
    rationalFibreSection k V pt hpt ≫ prFst k V =
      projectiveSpaceOfModuleToSpec k V ≫ pt :=
  pullback.lift_fst _ _ _

variable {k V} in
/-- **The section is a section of the third projection** of the triple product. -/
public theorem rationalFibreSection_comp_pr₃ (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) :
    rationalFibreSection k V pt hpt ≫ pr₃ k V = 𝟙 _ :=
  pullback.lift_snd _ _ _

variable {k V} in
/-- The third projection of a point of the section's image is the point it came from. -/
public theorem pr₃_base_rationalFibreSection (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) (x : projectiveSpaceOfModule k V) :
    (pr₃ k V).base ((rationalFibreSection k V pt hpt).base x) = x := by
  rw [← Scheme.Hom.comp_apply, rationalFibreSection_comp_pr₃]
  rfl

variable {k V} in
/-- **The section exhibits `𝐏(V)` as the base change of `prFst` along the rational point.** The
square is the defining pullback square of the triple product with the square whose horizontal
arrows are the identities cancelled off it: the latter is a pullback because `pt` is a morphism
over `Spec k` and the section's third component is the identity. -/
public theorem isPullback_rationalFibreSection (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) :
    IsPullback (rationalFibreSection k V pt hpt) (projectiveSpaceOfModuleToSpec k V)
      (prFst k V) pt := by
  refine IsPullback.of_right (h₁₂ := pr₃ k V) ?_
    (rationalFibreSection_comp_prFst pt hpt)
    (IsPullback.of_hasPullback (prodTwoToSpec k V) (projectiveSpaceOfModuleToSpec k V)).flip
  rw [rationalFibreSection_comp_pr₃, hpt]
  exact IsPullback.of_id_fst

variable {k V} in
/-- **The image of the section is the set-theoretic fibre of `prFst`** over the rational point.
This is `AlgebraicGeometry.Scheme.Pullback.range_fst` read through the pullback square, the
comparison isomorphism being a homeomorphism. -/
public theorem range_rationalFibreSection (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) :
    Set.range (rationalFibreSection k V pt hpt).base =
      (prFst k V).base ⁻¹' Set.range pt.base := by
  have h := isPullback_rationalFibreSection pt hpt
  have hcomp : rationalFibreSection k V pt hpt =
      h.isoPullback.hom ≫ pullback.fst (prFst k V) pt := h.isoPullback_hom_fst.symm
  have hsurj : Function.Surjective (h.isoPullback.hom).base := fun y =>
    ⟨(h.isoPullback.inv).base y, by
      rw [← Scheme.Hom.comp_apply, h.isoPullback.inv_hom_id]; rfl⟩
  rw [← Scheme.Pullback.range_fst (prFst k V) pt, hcomp]
  show Set.range ((pullback.fst (prFst k V) pt).base ∘ (h.isoPullback.hom).base) = _
  rw [Set.range_comp, hsurj.range_eq, Set.image_univ]

variable {k V} in
/-- **The section is a topological embedding**: it is a section of the third projection, so its
base map has a continuous left inverse. -/
public theorem isEmbedding_rationalFibreSection (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) :
    Topology.IsEmbedding (rationalFibreSection k V pt hpt).base :=
  Topology.IsEmbedding.of_leftInverse (pr₃_base_rationalFibreSection pt hpt)
    (pr₃ k V).base.hom.continuous (rationalFibreSection k V pt hpt).base.hom.continuous

variable {k V} in
/-- Every point of the triple product lying over the rational point is in the image of the
section, and is recovered from its third projection. -/
public theorem rationalFibreSection_base_pr₃_base (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) {t : prodThree k V}
    (ht : (prFst k V).base t ∈ Set.range pt.base) :
    (rationalFibreSection k V pt hpt).base ((pr₃ k V).base t) = t := by
  obtain ⟨x, hx⟩ := (range_rationalFibreSection pt hpt).ge ht
  rw [← hx, pr₃_base_rationalFibreSection]

/-! ### The fibre of `prFst` over a rational point is `𝐏(V)` -/

variable {k V} in
/-- **The fibre of `prFst` over a `k`-rational point of `𝐏(V) ×_k 𝐏(V)` is `𝐏(V)`.** The section
attached to the point is an embedding whose image is the set-theoretic fibre, and
`AlgebraicGeometry.Scheme.Hom.fiberHomeo` identifies that set with the scheme-theoretic fibre. -/
public def prFstFiberHomeomorph (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) {q : prodTwo k V}
    (hq : Set.range pt.base = {q}) :
    projectiveSpaceOfModule k V ≃ₜ (prFst k V).fiber q :=
  ((isEmbedding_rationalFibreSection pt hpt).toHomeomorph.trans
    (Homeomorph.setCongr (by rw [range_rationalFibreSection pt hpt, hq]))).trans
      ((prFst k V).fiberHomeo q).symm

variable {k V} in
/-- **The fibre of `prFst` over a `k`-rational point has the dimension of `𝐏(V)`.** -/
public theorem topologicalKrullDim_fiber_prFst (pt : Spec (.of k) ⟶ prodTwo k V)
    (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _) {q : prodTwo k V}
    (hq : Set.range pt.base = {q}) :
    topologicalKrullDim ((prFst k V).fiber q) =
      topologicalKrullDim (projectiveSpaceOfModule k V) :=
  (IsHomeomorph.topologicalKrullDim_eq _
    (prFstFiberHomeomorph pt hpt hq).isHomeomorph).symm

/-! ### The fibre of `collinearProj` over a rational point is the line -/

variable {k V} in
/-- The morphism from the scheme-theoretic fibre of `collinearProj` over a point of
`𝐏(V) ×_k 𝐏(V)` to `𝐏(V)` recording the third projection of a collinear triple. -/
public def collinearFibreToProj (q : prodTwo k V) :
    (collinearProj k V).fiber q ⟶ projectiveSpaceOfModule k V :=
  (collinearProj k V).fiberι q ≫ collinearProj₃ k V

variable {k V} in
/-- The morphism from the scheme-theoretic fibre of `collinearProj` to the triple product. -/
private def collinearFibreToProdThree (q : prodTwo k V) :
    (collinearProj k V).fiber q ⟶ prodThree k V :=
  (collinearProj k V).fiberι q ≫ collinearSubschemeι k V

variable {k V} in
private theorem collinearFibreToProj_base (q : prodTwo k V)
    (w : (collinearProj k V).fiber q) :
    (collinearFibreToProj q).base w =
      (pr₃ k V).base ((collinearFibreToProdThree q).base w) := rfl

variable {k V} in
private theorem collinearFibreToProdThree_base (q : prodTwo k V)
    (w : (collinearProj k V).fiber q) :
    (collinearFibreToProdThree q).base w =
      (collinearSubschemeι k V).base (((collinearProj k V).fiberι q).base w) := rfl

variable {k V} in
private theorem collinearProj_base (c : collinearSubscheme k V) :
    (collinearProj k V).base c = (prFst k V).base ((collinearSubschemeι k V).base c) := rfl

variable {k V} in
private theorem isEmbedding_collinearFibreToProdThree (q : prodTwo k V) :
    Topology.IsEmbedding (collinearFibreToProdThree q).base := by
  have h₁ := (collinearProj k V).fiberι q |>.isEmbedding
  have h₂ : Topology.IsEmbedding ⇑(collinearSubschemeι k V) :=
    have := isClosedImmersion_collinearSubschemeι k V
    (collinearSubschemeι k V).isEmbedding
  exact h₂.comp h₁

variable {k V} in
private theorem prFst_base_collinearFibreToProdThree (q : prodTwo k V)
    (w : (collinearProj k V).fiber q) :
    (prFst k V).base ((collinearFibreToProdThree q).base w) = q := by
  rw [collinearFibreToProdThree_base, ← collinearProj_base]
  exact ((collinearProj k V).range_fiberι q).le ⟨w, rfl⟩

variable {k V} in
private theorem mem_collinearLocus_collinearFibreToProdThree (q : prodTwo k V)
    (w : (collinearProj k V).fiber q) :
    (collinearFibreToProdThree q).base w ∈ collinearLocus k V := by
  rw [← range_collinearSubschemeι k V]
  exact ⟨(collinearProj k V).fiberι q w, rfl⟩

variable {k V} in
/-- **The collinear triples over a `k`-rational point, read in the scheme-theoretic fibre, are
exactly the points of the line joining the two projections of that point.** Both containments
come from
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_collinearLocus_iff_mem_linearSubspace_lineSubmodule`
through the section of
`AlgebraicGeometry.ProjectiveSpaceOfModule.rationalFibreSection`, which identifies the points of
the triple product over the rational point with the points of `𝐏(V)`. -/
public theorem range_collinearFibreToProj [IsAlgClosed k] [Module.Finite k V]
    (pt : Spec (.of k) ⟶ prodTwo k V) (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _)
    {q : prodTwo k V} (hq : Set.range pt.base = {q})
    (hcl₁ : IsClosed ({(prodTwoFst k V).base q} : Set (projectiveSpaceOfModule k V)))
    (hcl₂ : IsClosed ({(prodTwoSnd k V).base q} : Set (projectiveSpaceOfModule k V)))
    (hne : (prodTwoFst k V).base q ≠ (prodTwoSnd k V).base q) :
    Set.range (collinearFibreToProj q).base =
      linearSubspace k V
        (lineSubmodule k V ((prodTwoFst k V).base q) ((prodTwoSnd k V).base q)) := by
  -- the collinearity criterion for such a point
  have hiff : ∀ t : prodThree k V, (prFst k V).base t = q →
      (t ∈ collinearLocus k V ↔ (pr₃ k V).base t ∈
        linearSubspace k V
          (lineSubmodule k V ((prodTwoFst k V).base q) ((prodTwoSnd k V).base q))) := by
    intro t ht
    -- the two first projections of `t`
    have e₁ : (pr₁ k V).base t = (prodTwoFst k V).base q := by
      rw [pr₁_eq_prFst_comp, Scheme.Hom.comp_apply, ht]
    have e₂ : (pr₂ k V).base t = (prodTwoSnd k V).base q := by
      rw [pr₂_eq_prFst_comp, Scheme.Hom.comp_apply, ht]
    have h := mem_collinearLocus_iff_mem_linearSubspace_lineSubmodule k V
      (x := t) (e₁ ▸ hcl₁) (e₂ ▸ hcl₂) (by rw [e₁, e₂]; exact hne)
    rw [e₁, e₂] at h
    exact h
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    have ht := prFst_base_collinearFibreToProdThree q w
    have hcol := mem_collinearLocus_collinearFibreToProdThree q w
    rw [collinearFibreToProj_base]
    exact (hiff _ ht).mp hcol
  · intro hx
    have htq : (prFst k V).base ((rationalFibreSection k V pt hpt).base x) = q := by
      rw [← Scheme.Hom.comp_apply, rationalFibreSection_comp_prFst pt hpt,
        Scheme.Hom.comp_apply]
      exact hq.le (Set.mem_range_self _)
    have ht₃ : (pr₃ k V).base ((rationalFibreSection k V pt hpt).base x) = x :=
      pr₃_base_rationalFibreSection pt hpt x
    have hcol : (rationalFibreSection k V pt hpt).base x ∈ collinearLocus k V :=
      (hiff _ htq).mpr (by rw [ht₃]; exact hx)
    obtain ⟨c, hc⟩ : (rationalFibreSection k V pt hpt).base x ∈
        Set.range (collinearSubschemeι k V).base := by
      rw [range_collinearSubschemeι k V]; exact hcol
    have hcq : (collinearProj k V).base c = q := by
      rw [collinearProj_base, hc, htq]
    obtain ⟨w, hw⟩ : c ∈ Set.range ((collinearProj k V).fiberι q).base :=
      ((collinearProj k V).range_fiberι q).ge hcq
    refine ⟨w, ?_⟩
    rw [collinearFibreToProj_base, collinearFibreToProdThree_base, hw, hc, ht₃]

variable {k V} in
/-- **The fibre of `collinearProj` over a `k`-rational point whose two projections are distinct
closed points is the line joining them.** -/
public def collinearProjFiberHomeomorph [IsAlgClosed k] [Module.Finite k V]
    (pt : Spec (.of k) ⟶ prodTwo k V) (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _)
    {q : prodTwo k V} (hq : Set.range pt.base = {q})
    (hcl₁ : IsClosed ({(prodTwoFst k V).base q} : Set (projectiveSpaceOfModule k V)))
    (hcl₂ : IsClosed ({(prodTwoSnd k V).base q} : Set (projectiveSpaceOfModule k V)))
    (hne : (prodTwoFst k V).base q ≠ (prodTwoSnd k V).base q) :
    (collinearProj k V).fiber q ≃ₜ
      linearSubspace k V
        (lineSubmodule k V ((prodTwoFst k V).base q) ((prodTwoSnd k V).base q)) :=
  have hemb : Topology.IsEmbedding (collinearFibreToProj q).base := by
    refine ((isEmbedding_rationalFibreSection pt hpt).of_comp_iff).mp ?_
    have hfun : (rationalFibreSection k V pt hpt).base ∘ (collinearFibreToProj q).base =
        (collinearFibreToProdThree q).base := by
      funext w
      rw [Function.comp_apply, collinearFibreToProj_base]
      exact rationalFibreSection_base_pr₃_base pt hpt
        (by rw [hq, prFst_base_collinearFibreToProdThree q w]; rfl)
    rw [hfun]
    exact isEmbedding_collinearFibreToProdThree q
  hemb.toHomeomorph.trans
    (Homeomorph.setCongr
      (range_collinearFibreToProj pt hpt hq hcl₁ hcl₂ hne))

variable {k V} in
/-- **The scheme-theoretic fibre of `collinearProj` over a `k`-rational point whose two
projections are distinct closed points has dimension one.** This is the fibre dimension the
count of [Stacks, Tag 0B1R] runs on, in the
`AlgebraicGeometry.Scheme.Hom.fiber` spelling that the dimension theorems consume. -/
public theorem topologicalKrullDim_fiber_collinearProj [IsAlgClosed k] [Module.Finite k V]
    (pt : Spec (.of k) ⟶ prodTwo k V) (hpt : pt ≫ prodTwoToSpec k V = 𝟙 _)
    {q : prodTwo k V} (hq : Set.range pt.base = {q})
    (hcl₁ : IsClosed ({(prodTwoFst k V).base q} : Set (projectiveSpaceOfModule k V)))
    (hcl₂ : IsClosed ({(prodTwoSnd k V).base q} : Set (projectiveSpaceOfModule k V)))
    (hne : (prodTwoFst k V).base q ≠ (prodTwoSnd k V).base q) :
    topologicalKrullDim ((collinearProj k V).fiber q) = 1 :=
  (IsHomeomorph.topologicalKrullDim_eq _
      (collinearProjFiberHomeomorph pt hpt hq hcl₁ hcl₂ hne).isHomeomorph).trans
    (topologicalKrullDim_linearSubspace_lineSubmodule hcl₁ hcl₂ hne)

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
