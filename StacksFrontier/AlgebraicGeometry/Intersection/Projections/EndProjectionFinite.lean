module

public import StacksFrontier.AlgebraicGeometry.Intersection.ProperIntersections.Defs
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTranslate
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.FiniteProjection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.SubvarietyIntersection

/-!
# The projective transformation attached to an endomorphism is finite on its domain

Let `V` be a finite-dimensional vector space over an algebraically closed field, let `g` be an
endomorphism of `V` and let `S ⊆ U(g)` be a closed subset of `𝐏(V)` lying in the domain of
definition of `r_g`. Then the morphism `r_g|_S : S ⟶ 𝐏(V)` is *finite*, and consequently the
image `r_g(S)` has the same dimension as `S`.

This is the first of the three ingredients the source of Tag 0B1S gestures at when it closes the
analysis of the determinant hypersurface with *"Some details omitted"*: *the morphism
`r_g|_X : X → r_g(X)` is finite, hence `dim r_g(X) = dim X`*. It is proved here for an arbitrary
endomorphism, not only for one of corank one: the source's reason — that the fibres of a
projection away from a point are affine lines — is replaced by the reason behind it, namely that
`r_g` is an *affine* morphism, being induced by a graded ring homomorphism, exactly as for the
linear projection in `StacksFrontier.AlgebraicGeometry.Variety.Projective.FiniteProjection`. An
affine proper morphism is finite.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.isAffineHom_endProjection`: `r_g` is affine.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isFinite_endProjection_of_isClosedImmersion`:
  `r_g|_X` is finite for every closed subscheme `X` of `𝐏(V)` lying in `U(g)`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_le_endProjectionImage` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_eq`: the
  image `r_g(S)` of a closed `S ⊆ U(g)` has the dimension of `S`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.nonempty_endProjectionImage_inter`: **`r_g(X)` still
  meets `Y`**, for `X, Y` closed subvarieties meeting properly and meeting at all.

## Implementation notes

The lower bound `dim S ≤ dim r_g(S)` is where finiteness is used, through Tag 0B2L part (2a),
`AlgebraicGeometry.topologicalKrullDim_le_fiber_add_imageClosure`: the dimension of an
irreducible source is at most the local dimension of a fibre plus the dimension of the reduced
closure of the image, and for a finite morphism the fibres are zero-dimensional. The upper bound
needs no finiteness and is not proved here: it is
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_le` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTranslate`, which also
supplies that `r_g` is a morphism over the ground field and that the image is closed.

`S` enters the fibre-dimension machinery as the reduced closed subscheme
`Scheme.IdealSheafData.vanishingIdeal ⟨S, hS⟩`, whose space is homeomorphic to `S` along its
closed immersion; the factorization of that immersion through the open `U(g)` is unique, the
inclusion of an open being a monomorphism, so the finiteness asserted of
`j ≫ r_g` is finiteness of `r_g|_S`.

The construction of the reduced closed subscheme on `S` and of its lift along the open immersion
of `U(g)` is the one in the proof of
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isProper_range_eq_endProjectionImage` there.
It is repeated rather than cited because that statement produces the morphism existentially and
asserts only properness, while the bound below needs *this* morphism and needs it to be finite;
merging the two would mean giving that module the import on which affineness rests.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B1P](https://stacks.math.columbia.edu/tag/0B1P)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0B2W](https://stacks.math.columbia.edu/tag/0B2W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- **`r_g` is an affine morphism**, being induced by a graded ring homomorphism. -/
public instance isAffineHom_endProjection (g : V →ₗ[k] V) :
    IsAffineHom (endProjection k V g) :=
  isAffineHom_mapHom _ _ _

section Finite

variable {k V}

/-- **`r_g` is finite on a closed subscheme contained in its domain of definition.**

Let `i : X ⟶ 𝐏(V)` be a closed immersion and let `j` be a factorization of `i` through the open
`U(g)`. Then `r_g|_X = j ≫ r_g` is a finite morphism `X ⟶ 𝐏(V)`: it is affine because `j` is a
closed immersion and `r_g` is affine, and it is proper because composing it with the structure
morphism of `𝐏(V)` gives the structure morphism of `X`, which is proper, while `𝐏(V)` is
separated over the ground field. An affine proper morphism is finite. -/
public theorem isFinite_endProjection_of_isClosedImmersion [FiniteDimensional k V]
    [Nontrivial V] {X : Scheme.{u}} (i : X ⟶ projectiveSpaceOfModule k V)
    [IsClosedImmersion i] (g : V →ₗ[k] V) (j : X ⟶ (endDomain k V g).toScheme)
    (hj : j ≫ (endDomain k V g).ι = i) :
    IsFinite (j ≫ endProjection k V g) := by
  have hji : IsClosedImmersion (j ≫ (endDomain k V g).ι) := by
    rw [hj]; infer_instance
  have hjclosed : IsClosedImmersion j := IsClosedImmersion.of_comp j (endDomain k V g).ι
  have hproper : IsProper ((j ≫ endProjection k V g) ≫ projectiveSpaceOfModuleToSpec k V) := by
    rw [Category.assoc, endProjection_comp_toSpec, ← Category.assoc, hj]
    infer_instance
  have hproper' : IsProper (j ≫ endProjection k V g) :=
    IsProper.of_comp _ (projectiveSpaceOfModuleToSpec k V)
  have hint : IsIntegralHom (j ≫ endProjection k V g) :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨hint, inferInstance⟩

end Finite

/-- The underlying space of a closed immersion has the dimension of its range. -/
private theorem topologicalKrullDim_eq_range_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] : topologicalKrullDim X = topologicalKrullDim ↥(Set.range f.base) :=
  IsHomeomorph.topologicalKrullDim_eq _
    (IsClosedImmersion.isClosedEmbedding f).isEmbedding.toHomeomorph.isHomeomorph

/-- **The image of an irreducible closed subset of `U(g)` under `r_g` is at least as big as the
subset.** This is the half of the source's first omitted ingredient that finiteness is needed
for: Tag 0B2L part (2a) bounds the dimension of the irreducible source by the local dimension of
a fibre plus the dimension of the reduced closure of the image, and for a finite morphism the
fibres are zero-dimensional. The opposite inequality holds for an arbitrary closed subset and
needs no finiteness; it is
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_le` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTranslate`, whose
construction of the reduced closed subscheme on `S` and of its lift along the open immersion of
`U(g)` is the one repeated here; what is not available there is the finiteness, which rests on
the affineness of `mapHom` and hence on an import that module does not have.

This is the irreducible case; `topologicalKrullDim_le_endProjectionImage` removes that hypothesis
by reading the dimension of a closed set off the closures of its points. -/
private theorem topologicalKrullDim_le_endProjectionImage_of_isIrreducible [IsAlgClosed k]
    [FiniteDimensional k V]
    [Nontrivial V] (g : V →ₗ[k] V) {S : Set (projectiveSpaceOfModule k V)}
    (hS : IsClosed S) (hirr : IsIrreducible S)
    (hSg : S ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    topologicalKrullDim ↥S ≤ topologicalKrullDim ↥(endProjectionImage k V g S) := by
  have : LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
    have := isProper_projectiveSpaceOfModuleToSpec k V
    infer_instance
  set I : (projectiveSpaceOfModule k V).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal ⟨S, hS⟩ with hI
  have hrange : Set.range I.subschemeι.base = S := by
    rw [hI, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hhomeo : topologicalKrullDim ↥S = topologicalKrullDim I.subscheme := by
    rw [← hrange]
    exact (topologicalKrullDim_eq_range_of_isClosedImmersion I.subschemeι).symm
  have hirrI : IrreducibleSpace I.subscheme :=
    (IsClosedImmersion.isClosedEmbedding
        I.subschemeι).isEmbedding.toHomeomorph.irreducibleSpace_iff.mpr
      (by rw [hrange]; exact Subtype.irreducibleSpace hirr)
  have hsub : Set.range I.subschemeι.base ⊆ Set.range (endDomain k V g).ι.base := by
    rw [hrange, Scheme.Opens.range_ι]
    exact hSg
  set j := IsOpenImmersion.lift (endDomain k V g).ι I.subschemeι hsub with hjdef
  have hjfac : j ≫ (endDomain k V g).ι = I.subschemeι := IsOpenImmersion.lift_fac _ _ _
  have hcomp : ∀ y, (endDomain k V g).ι.base (j.base y) = I.subschemeι.base y := by
    intro y
    rw [← hjfac, Scheme.Hom.comp_base]
    rfl
  have hrj : Set.range j.base = (endDomain k V g).ι.base ⁻¹' S := by
    refine Set.Subset.antisymm ?_ fun x hx => ?_
    · rintro _ ⟨y, rfl⟩
      rw [Set.mem_preimage, hcomp, ← hrange]
      exact ⟨y, rfl⟩
    · obtain ⟨y, hy⟩ : (endDomain k V g).ι.base x ∈ Set.range I.subschemeι.base := by
        rw [hrange]; exact hx
      exact ⟨y, (endDomain k V g).ι.isOpenEmbedding.injective (by rw [hcomp, hy])⟩
  have hrf : Set.range (j ≫ endProjection k V g).base = endProjectionImage k V g S := by
    rw [endProjectionImage, ← hrj, Scheme.Hom.comp_base]
    simp only [TopCat.coe_comp, Set.range_comp]
  have hfin : IsFinite (j ≫ endProjection k V g) :=
    isFinite_endProjection_of_isClosedImmersion I.subschemeι g j hjfac
  have hfac : (j ≫ endProjection k V g) ≫ projectiveSpaceOfModuleToSpec k V =
      I.subschemeι ≫ projectiveSpaceOfModuleToSpec k V := by
    rw [Category.assoc, endProjection_comp_toSpec, ← Category.assoc, hjfac]
  have : LocallyOfFiniteType (I.subschemeι ≫ projectiveSpaceOfModuleToSpec k V) :=
    inferInstance
  have himgclosed : IsClosed (endProjectionImage k V g S) :=
    isClosed_endProjectionImage k V g hS hSg
  obtain ⟨x₀, hx₀⟩ := hirr.nonempty
  obtain ⟨y₀, -⟩ : ∃ y₀ : I.subscheme, I.subschemeι.base y₀ = x₀ := by
    rw [← Set.mem_range, hrange]; exact hx₀
  have hfib : topologicalKrullDimAt ((j ≫ endProjection k V g).fiber
      ((j ≫ endProjection k V g).base y₀)) ((j ≫ endProjection k V g).asFiber y₀) = 0 := by
    refine (quasiFiniteAt_iff_fiberDimensionAt_eq_zero (j ≫ endProjection k V g) y₀).mp
      ⟨?_, (j ≫ endProjection k V g).quasiFiniteAt y₀⟩
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      (projectiveSpaceOfModule k V).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ ((j ≫ endProjection k V g).base y₀)) isOpen_univ
    obtain ⟨-, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      I.subscheme.isBasis_affineOpens.exists_subset_of_mem_open hxU
        ((j ≫ endProjection k V g) ⁻¹ᵁ U).2
    exact ⟨⟨U, hU⟩, ⟨W, hW⟩, hxW, hWU,
      (j ≫ endProjection k V g).finiteType_appLE hU hW hWU⟩
  have h2a := AlgebraicGeometry.topologicalKrullDim_le_fiber_add_imageClosure k
    (I.subschemeι ≫ projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V)
    (j ≫ endProjection k V g) hfac y₀
  rw [hfib, zero_add] at h2a
  have hcl : Set.range (fun y : I.subscheme => (j ≫ endProjection k V g).base y) =
      endProjectionImage k V g S := hrf
  set J : (projectiveSpaceOfModule k V).IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range (fun y : I.subscheme =>
        (j ≫ endProjection k V g).base y))) with hJ
  have hsets : Set.range J.subschemeι.base = endProjectionImage k V g S := by
    rw [hJ, Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure, hcl,
      himgclosed.closure_eq]
  have hsubdim : topologicalKrullDim J.subscheme =
      topologicalKrullDim ↥(endProjectionImage k V g S) := by
    rw [topologicalKrullDim_eq_range_of_isClosedImmersion J.subschemeι, hsets]
  rw [hsubdim, ← hhomeo] at h2a
  exact h2a

/-- **The image of a closed subset of `U(g)` under `r_g` is at least as big as the subset.** This
is the half of the source's first omitted ingredient that finiteness is needed for. No
irreducibility is asked: on a quasi-sober space the dimension of a closed subset is bounded by the
dimensions of the closures of its points, and the closure of a point of `S` is an irreducible
closed subset of `U(g)` whose translate sits inside the translate of `S`. The opposite inequality
holds for an arbitrary closed subset too and needs no finiteness; it is
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_le` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.MovingFamilyTranslate`.

The non-irreducible case is what the clause-(2) bad locus of Tag 0B1S consumes: the fibre of the
incidence correspondence over a class `[g]` is `X ∩ r_g⁻¹(Y)`, which has no reason to be
irreducible, and the bound wanted of it is on the dimension of its translate `r_g(X) ∩ Y`. -/
public theorem topologicalKrullDim_le_endProjectionImage [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (g : V →ₗ[k] V) {S : Set (projectiveSpaceOfModule k V)}
    (hS : IsClosed S)
    (hSg : S ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    topologicalKrullDim ↥S ≤ topologicalKrullDim ↥(endProjectionImage k V g S) := by
  refine topologicalKrullDim_le_of_forall_closure hS fun x hx => ?_
  have hsub : closure ({x} : Set (projectiveSpaceOfModule k V)) ⊆ S :=
    hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)
  have hmono : endProjectionImage k V g (closure ({x} : Set (projectiveSpaceOfModule k V))) ⊆
      endProjectionImage k V g S :=
    Set.image_mono (Set.preimage_mono hsub)
  exact (topologicalKrullDim_le_endProjectionImage_of_isIrreducible k V g isClosed_closure
    isIrreducible_singleton.closure (hsub.trans hSg)).trans
      (topologicalKrullDim_le_of_subset hmono)

/-- **The image of a closed subset of `U(g)` under `r_g` has the dimension of the subset** — the
source's first omitted ingredient, "`r_g|_X : X → r_g(X)` is finite, hence
`dim r_g(X) = dim X`". Each inequality is cited: the upper bound is
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_le`, which
needs no finiteness, and the lower bound is
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_le_endProjectionImage`. -/
public theorem topologicalKrullDim_endProjectionImage_eq [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (g : V →ₗ[k] V) {S : Set (projectiveSpaceOfModule k V)}
    (hS : IsClosed S)
    (hSg : S ⊆ (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    topologicalKrullDim ↥(endProjectionImage k V g S) = topologicalKrullDim ↥S :=
  le_antisymm (topologicalKrullDim_endProjectionImage_le k V g hS hSg)
    (topologicalKrullDim_le_endProjectionImage k V g hS hSg)

/-- **A translate of `X` meets `Y` as soon as the dimensions add up.** For closed
subvarieties `X, Y` of `𝐏(V)` with `dim 𝐏(V) ≤ dim X + dim Y` and an endomorphism `g` whose domain
of definition contains `X`, the translate `r_g(X)` meets `Y`: it is a closed subvariety of the
same dimension as `X`, and two closed subvarieties of `𝐏(V)` whose dimensions add up to at least
`dim 𝐏(V)` meet. -/
public theorem nonempty_endProjectionImage_inter_of_le [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (g : V →ₗ[k] V)
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (hle : topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(X : Set (projectiveSpaceOfModule k V)) +
        topologicalKrullDim ↥(Y : Set (projectiveSpaceOfModule k V)))
    (hdom : (X : Set (projectiveSpaceOfModule k V)) ⊆
      (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    (endProjectionImage k V g (X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty := by
  have hXc : IsClosed (X : Set (projectiveSpaceOfModule k V)) := X.isClosed'
  have hXirr : IsIrreducible (X : Set (projectiveSpaceOfModule k V)) := X.isIrreducible'
  have hle' : topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(endProjectionImage k V g
          (X : Set (projectiveSpaceOfModule k V))) +
        topologicalKrullDim ↥(Y : Set (projectiveSpaceOfModule k V)) := by
    rw [topologicalKrullDim_endProjectionImage_eq k V g hXc hdom]
    exact hle
  exact nonempty_inter_projectiveSpaceOfModule
    (isClosed_endProjectionImage k V g hXc hdom) Y.isClosed'
    (isIrreducible_endProjectionImage k V g hdom hXirr).nonempty
    Y.isIrreducible'.nonempty hle'

/-- **`r_g(X)` still meets `Y`.** Let `X, Y` be closed subvarieties of `𝐏(V)` which intersect
properly and which do meet, and let `g` be an endomorphism of `V` with `X ⊆ U(g)`. Then `r_g(X)`
meets `Y`.

This is the ingredient the source of Tag 0B1S takes from the projective dimension theorem
(Varieties, Lemma 33.34.3): proper intersection together with `X ∩ Y ≠ ∅` forces
`dim 𝐏(V) ≤ dim X + dim Y`, and `r_g(X)` is a closed subset of the same dimension as `X`
(`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_endProjectionImage_eq` above), so
Tag 0B2R applies to the pair `r_g(X)`, `Y`. No invertibility of `g` is needed: the dimension of
the image is that of `X` for an arbitrary endomorphism whose domain of definition contains `X`.

This is where the hypothesis `X ∩ Y ≠ ∅` of Tag 0B1S does its work. -/
public theorem nonempty_endProjectionImage_inter [IsAlgClosed k] [FiniteDimensional k V]
    [Nontrivial V] (g : V →ₗ[k] V)
    (X Y : IrreducibleCloseds (projectiveSpaceOfModule k V)) (hXY : IntersectProperly X Y)
    (hXYne : ((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty)
    (hdom : (X : Set (projectiveSpaceOfModule k V)) ⊆
      (endDomain k V g : Set (projectiveSpaceOfModule k V))) :
    (endProjectionImage k V g (X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V))).Nonempty := by
  obtain ⟨x₀, hx₀⟩ := hXYne
  have : Nonempty (IrreducibleCloseds ↥((X : Set (projectiveSpaceOfModule k V)) ∩
      (Y : Set (projectiveSpaceOfModule k V)))) :=
    ⟨⟨closure {(⟨x₀, hx₀⟩ : ↥((X : Set (projectiveSpaceOfModule k V)) ∩
        (Y : Set (projectiveSpaceOfModule k V))))},
      isIrreducible_singleton.closure, isClosed_closure⟩⟩
  refine nonempty_endProjectionImage_inter_of_le k V g X Y ?_ hdom
  calc topologicalKrullDim (projectiveSpaceOfModule k V)
      = 0 + topologicalKrullDim (projectiveSpaceOfModule k V) := (zero_add _).symm
    _ ≤ topologicalKrullDim ↥((X : Set (projectiveSpaceOfModule k V)) ∩
          (Y : Set (projectiveSpaceOfModule k V))) +
        topologicalKrullDim (projectiveSpaceOfModule k V) := add_le_add Order.krullDim_nonneg le_rfl
    _ ≤ _ := hXY

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
