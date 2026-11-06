module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.DegreeOneOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalDecomposition
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFiniteUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteUnionRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionZeroLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent

/-!
# The degree induction of Stacks 03XW

Stacks 03XW considers an étale morphism `t : T' ⟶ T` of affine schemes, a separated and locally
quasi-finite morphism `f : X ⟶ T` of algebraic spaces and an open subspace `V' ⊆ T' ×_T X` which
is quasi-affine over `T'`, and asserts that the image `U` of `V'` in `X` is a quasi-compact open
subspace of `X` which is representable. Everything in that conclusion except representability is
`AlgebraicGeometry.Space.isOpenSubspace_isQuasiCompactSpace_image_of_isQuasiAffineHom` in
`StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage`; representability is an induction on an
integer bounding the degrees of the fibres of `t`, and this file runs that induction and proves
the tag.

The conclusion of the induction at each stage is that the base change `T' ×_T U` is
representable, and the passage from there to representability of `U` itself is the descent of
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_pullback_of_surjectiveEtaleChart`
(`StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent`) along the surjective
étale covering `{T' ⟶ W}` of the open image `W ⊆ T` of `t`. That descent is packaged here as
`AlgebraicGeometry.Space.isRepresentable_image_of_isRepresentable_pullback_image`, and the
point-set bookkeeping which lets it be applied — every section of the image `U` has, after
composition with `f`, image inside the image of `t` — is
`AlgebraicGeometry.Space.range_map_app_subset_range_map_of_mem_image`.

The base case of the induction is a bound of one: then `t` is an open immersion
(`AlgebraicGeometry.isOpenImmersion_of_boundsFiberDegrees_one`, which is the proof's use of
Tag 025G), `T' ×_T X ⟶ X` is a monomorphism, and so the image `U` of `V'` *is* `V'`, which is a
quasi-affine scheme over the affine `T'` by Tag 03WM.

The inductive step is the third and fourth paragraphs of the source. Write `T'' = T' ×_T T'`,
with projections `pr₀, pr₁` and diagonal `Δ`, and let `T^* ⊆ T''` be the open affine subscheme
complementary to the image of `Δ`
(`AlgebraicGeometry.offDiagonal` of
`StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.EtaleDiagonalDecomposition`); the degrees
of the fibres of `T^* ⟶ T'` drop by one, which is
`AlgebraicGeometry.boundsFiberDegrees_offDiagonal_fst` there, and `T^*` is again an object of the
site by `AlgebraicGeometry.exists_restrict_bigFppfOver`. Writing `X' = T' ×_T X`,
`X'' = T'' ×_{T'} X'` and `X^* = T^* ×_{T'} X'`, with `p₀, p₁ : X'' ⟶ X'` the base changes of
`pr₀, pr₁`, the induction hypothesis applied to `T^* ⟶ T'` and the open subspace
`p₀⁻¹(V') ∩ X^*` — quasi-affine over `T^*` because it is the base change of `V' ⟶ T'` along the
*other* projection — produces an open subspace `U^* ⊆ X'`, and
`T' ×_T U = p₁(p₀⁻¹(V')) = V' ∪ U^*`
is representable by the two-member glueing of
`StacksFrontier.AlgebraicGeometry.Spaces.FiniteUnionRepresentable`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.range_map_app_subset_range_map_of_mem_image`: a section of the image
  subspace has, after composition with `f`, image inside the image of `t`.
* `AlgebraicGeometry.Space.isPullback_pullback_ι_pullback_snd`: **`T' ×_T U = U ×_X (T' ×_T X)`.**
  For a subfunctor `G` of `X` the fibre product of `G ⟶ X` with `T' ×_T X ⟶ X` is a fibre
  product of `G ⟶ yoneda.obj T` with `yoneda.map t`.
* `AlgebraicGeometry.Space.isRepresentable_pullback_ι_comp_of_isRepresentable`: the resulting
  transfer of representability.
* `AlgebraicGeometry.Space.isRepresentable_pullback_image_of_isOpenImmersion` and
  `AlgebraicGeometry.Space.isRepresentable_pullback_image_of_boundsFiberDegrees_one`: **the base
  case of the induction**, in the two forms in which it is used.
* `AlgebraicGeometry.Space.exists_bigFppfOver_offDiagonal`: **`T^*` as an object of the site**,
  affine, with its projection to `T'` étale of fibre degrees one lower, and covering `T''`
  together with the diagonal.
* `AlgebraicGeometry.Space.isRepresentable_image_of_isRepresentable_pullback_image`: **the last
  paragraph of Stacks 03XW**, packaged: representability of `T' ×_T U` makes `U` representable.
* `AlgebraicGeometry.Space.isRepresentable_image_of_isQuasiAffineHom`: **representability of the
  image**, the content of Stacks 03XW which the induction supplies.
* `AlgebraicGeometry.Space.isOpenSubspace_isQuasiCompactSpace_isRepresentable_image`:
  **Stacks 03XW.** The image of `V'` in `X` is a quasi-compact open subspace of `X` which is
  representable.

## Implementation notes

The integer bounding the fibre degrees is produced by Tag 03JA
(`AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite`), applied to the étale
morphism `t` of affine schemes; the induction is then run on a natural number `n` with the bound
`n + 1`, so that the base case is the bound one of Tag 025G.

The inductive statement is not a definition: it is the body of the private
`∀ n, ...` statement `isRepresentable_pullback_image_of_boundsFiberDegrees_aux`, proved by
`induction` on `n`, so that no auxiliary `Prop`-valued definition has to be introduced.

The identification `p₁(p₀⁻¹(V')) = V' ∪ U^*` is carried out on point sets and transported back
by the order isomorphism of Tag 03BZ. On point sets it is two instances of
`AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback` — the first turning
`|T' ×_T U| = p⁻¹(p(|V'|))` into `p₁(p₀⁻¹(|V'|))`, the second recognising the preimage of `V'`
in `X^*` — followed by the clopen decomposition of `T''`: a point of `X''` lies either over the
diagonal, where `p₀` and `p₁` agree because `X' ⟶ X''` is a section of both, or over `T^*`,
where it comes from `X^*`. The three cartesian squares this needs are assembled from the
pasting lemmas by the three private lemmas `isPullback_otherProjection`,
`isPullback_otherProjection_of_isPullback` and `isPullback_diagonalSection`, which are statements
about an arbitrary category.

The isomorphism of the image with the subspace in the base case is obtained from Tag 03MD
(`AlgebraicGeometry.Space.isIso_of_presheaf_isOpenImmersion_of_presheafSurjective`): the
canonical morphism from `V'` to the image is an open immersion by cancelling the monomorphism
`U.ι` out of `V' ⟶ X` (`CategoryTheory.MorphismProperty.presheaf_of_comp_mono`), and it is
surjective on points because the point set of the image is by construction the image of the
point set of `V'` and `U.ι` is injective on points. The point set of the image is read off by
Tag 03BZ, `AlgebraicGeometry.Space.range_pointsMap_ι_openSubspaceOfPoints`.

## References

* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03JH](https://stacks.math.columbia.edu/tag/03JH)
* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
* [Stacks Project, Tag 03WM](https://stacks.math.columbia.edu/tag/03WM)
* [Stacks Project, Tag 03WU](https://stacks.math.columbia.edu/tag/03WU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Pullbacks of presheaves of types on the site, supplied directly: under Mathlib v4.35.0 the
instance search for `HasPullback` there first tries `Adhesive.hasPullback_of_mono_left` and times
out searching for `Mono`. -/
local instance (priority := high) hasPullback_presheaf_ImageRepresentableInduction
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ H) (g : G ⟶ H) : HasPullback f g :=
  HasLimitsOfShape.has_limit _

/-! ### Sections of the image lie over the image of `t` -/

/-- A section over an object `a` of the site of the image `U ⊆ X` of an open subspace
`V' ⊆ T' ×_T X` has, after composition with `f : X ⟶ yoneda.obj T`, underlying morphism of
schemes whose image lies inside the image of `t`.

This is what lets the last paragraph of the proof of Stacks 03XW factor `U ⟶ yoneda.obj T`
through the open image `W ⊆ T` of `t`, along which the descent is taken; the factorisation
itself is `AlgebraicGeometry.Space.exists_lift_yoneda_of_forall_exists_factor`.

The argument is on points. A point of the scheme underlying `a` gives a field-valued point of
the represented presheaf (`AlgebraicGeometry.Space.exists_fieldValuedPoint_schemePoint_eq`),
whose image under the section lies in the point set of `U`, hence is the image of a point of
`V'`; and a point of `V'` maps to `T` through `T'`, because
`V'.ι ≫ pullback.snd ≫ f = V'.ι ≫ pullback.fst ≫ yoneda.map t`. Comparing the two along the
bijection of Tag 03BX between the points of a represented presheaf and the points of the
representing scheme (`AlgebraicGeometry.Space.pointsToScheme`) gives the assertion about scheme
points. -/
theorem range_map_app_subset_range_map_of_mem_image
    {T' T : BigFppfOver B S hS} {t : T' ⟶ T}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T)
    (V : Subfunctor (pullback (yoneda.map t) f))
    (a : (BigFppfOver B S hS)ᵒᵖ)
    (x : (openSubspaceOfPoints B S hS X
      (Set.range (pointsMap B S hS V.toFunctor
        (V.ι ≫ pullback.snd (yoneda.map t) f)))).toFunctor.obj a) :
    Set.range ((BigFppfOver.toScheme B S hS).map (f.app a x.1)) ⊆
      Set.range ((BigFppfOver.toScheme B S hS).map t) := by
  rintro - ⟨z, rfl⟩
  obtain ⟨p, hp⟩ := exists_fieldValuedPoint_schemePoint_eq B S hS a.unop z
  have hmem := (mem_openSubspaceOfPoints_iff B S hS _ x.1).1 x.2
  obtain ⟨v, hv⟩ := hmem (Set.mem_range_self (p.class B S hS (yoneda.obj a.unop)))
  have hyeq : yoneda.map (f.app a x.1) = yonedaEquiv.symm x.1 ≫ f := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_yoneda_map, yonedaEquiv_comp, Equiv.apply_symm_apply]
  have key : pointsMap B S hS (yoneda.obj T') (yoneda.map t)
      (pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst (yoneda.map t) f) v) =
      pointsMap B S hS (yoneda.obj a.unop) (yoneda.map (f.app a x.1))
        (p.class B S hS (yoneda.obj a.unop)) := by
    rw [← pointsMap_comp_apply, Category.assoc, pullback.condition, ← Category.assoc,
      pointsMap_comp_apply, hv, hyeq, pointsMap_comp_apply]
  refine ⟨pointsToScheme B S hS T'
    (pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst (yoneda.map t) f) v), ?_⟩
  rw [← pointsToScheme_pointsMap_yoneda, key, pointsToScheme_pointsMap_yoneda,
    pointsToScheme_class, hp]

/-! ### `T' ×_T U` as a subspace of `T' ×_T X` -/

/-- **`T' ×_T U = U ×_X (T' ×_T X)`.** For a subfunctor `G` of a presheaf `X` on the big fppf
site of `S` with a morphism `f : X ⟶ yoneda.obj T` and a morphism `t : T' ⟶ T` of the site, the
fibre product of the inclusion `G ⟶ X` with the projection `T' ×_T X ⟶ X` is a fibre product of
`G ⟶ yoneda.obj T` with `yoneda.map t`.

This is the two squares of the diagram of Stacks 03XW pasted vertically. It is the step which
turns the conclusion of the induction — that `T' ×_T U` is a scheme — into a statement about an
open subspace of `T' ×_T X`, which is the shape in which the fourth paragraph of the proof
produces it. -/
theorem isPullback_pullback_ι_pullback_snd
    {T' T : BigFppfOver B S hS} (t : T' ⟶ T)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T) (G : Subfunctor X) :
    IsPullback (pullback.fst G.ι (pullback.snd (yoneda.map t) f))
      (pullback.snd G.ι (pullback.snd (yoneda.map t) f) ≫ pullback.fst (yoneda.map t) f)
      (G.ι ≫ f) (yoneda.map t) :=
  (IsPullback.of_hasPullback G.ι (pullback.snd (yoneda.map t) f)).paste_vert
    (IsPullback.of_hasPullback (yoneda.map t) f).flip

/-- A presheaf with a cartesian square onto `c, d` is representable once any other one is. -/
private theorem isRepresentable_of_isPullback_of_isPullback
    {P P' F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {a : P ⟶ F} {b : P ⟶ G} {a' : P' ⟶ F}
    {b' : P' ⟶ G} {c : F ⟶ H} {d : G ⟶ H} (sq : IsPullback a b c d) (sq' : IsPullback a' b' c d)
    (h : P.IsRepresentable) : P'.IsRepresentable :=
  have _h := h
  Functor.IsRepresentable.mk' (P.reprW ≪≫ sq.isoIsPullback _ _ sq')

/-- Representability of `U ×_X (T' ×_T X)` gives representability of `T' ×_T U`.

This is `AlgebraicGeometry.Space.isPullback_pullback_ι_pullback_snd` read as a transfer of
representability between the two chosen fibre products. -/
theorem isRepresentable_pullback_ι_comp_of_isRepresentable
    {T' T : BigFppfOver B S hS} (t : T' ⟶ T)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T) (G : Subfunctor X)
    (h : (pullback G.ι (pullback.snd (yoneda.map t) f)).IsRepresentable) :
    (pullback (G.ι ≫ f) (yoneda.map t)).IsRepresentable :=
  isRepresentable_of_isPullback_of_isPullback (isPullback_pullback_ι_pullback_snd t f G)
    (IsPullback.of_hasPullback (G.ι ≫ f) (yoneda.map t)) h

/-! ### The base case of the induction -/

/-- **The base case of the degree induction of Stacks 03XW.** In the situation of that tag with
`t : T' ⟶ T` an open immersion — which is what a bound of one on the degrees of the fibres of an
étale `t` gives, by `AlgebraicGeometry.isOpenImmersion_of_boundsFiberDegrees_one` — the base
change `T' ×_T U` of the image `U` of `V'` in `X` is representable.

For an open immersion `t` the projection `T' ×_T X ⟶ X` is a monomorphism, so `V'` maps
isomorphically onto its image `U`; and `V'` is representable because it is quasi-affine over the
affine `T'` (Tag 03WM,
`AlgebraicGeometry.Space.isRepresentable_of_isQuasiAffineHom_openSubspace`). Finally
`U ⟶ yoneda.obj T` factors through `yoneda.map t` — along the inverse of that isomorphism — and
a fibre product of `q ≫ yoneda.map t` with the monomorphism `yoneda.map t` is the source of `q`,
so `T' ×_T U` is `U` itself.

Separatedness and local quasi-finiteness of `f`, affineness of `T` and algebraicity of `X` are
hypotheses of the tag which this case does not use; they are omitted. -/
theorem isRepresentable_pullback_image_of_isOpenImmersion
    {T' T : BigFppfOver B S hS} (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    {t : T' ⟶ T} (ht : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map t))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T)
    (V : Subfunctor (pullback (yoneda.map t) f)) (hV : IsOpenSubspace B S hS V)
    (hVqa : IsQuasiAffineHom B S hS (V.ι ≫ pullback.fst (yoneda.map t) f)) :
    (pullback ((openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))).ι ≫ f) (yoneda.map t)).IsRepresentable := by
  have hmt : Mono t := inverseImage_isOpenImmersion_le_monomorphisms t ht
  have hmyt : Mono (yoneda.map t) := inferInstance
  have hsnd : IsOpenImmersion B S hS (pullback.snd (yoneda.map t) f) :=
    presheaf_of_isPullback B S hS (IsPullback.of_hasPullback (yoneda.map t) f)
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ t).2 ht)
  have hViso := isIso_lift_range_pointsMap_of_isOpenImmersion B S hS hsnd hV
  set U := openSubspaceOfPoints B S hS X
    (Set.range (pointsMap B S hS V.toFunctor
      (V.ι ≫ pullback.snd (yoneda.map t) f))) with hU
  set j := Subfunctor.lift (V.ι ≫ pullback.snd (yoneda.map t) f)
    (range_le_openSubspaceOfPoints_range_pointsMap
      (V.ι ≫ pullback.snd (yoneda.map t) f)) with hjdef
  have hj : j ≫ U.ι = V.ι ≫ pullback.snd (yoneda.map t) f := Subfunctor.lift_ι _ _
  have hVrep : V.toFunctor.IsRepresentable :=
    (isRepresentable_of_isQuasiAffineHom_openSubspace hT' t f V hVqa).1
  have _hUrep : U.toFunctor.IsRepresentable :=
    Functor.IsRepresentable.mk' (V.toFunctor.reprW ≪≫ asIso j)
  set q : U.toFunctor ⟶ yoneda.obj T' :=
    inv j ≫ V.ι ≫ pullback.fst (yoneda.map t) f with hq
  have hfac : U.ι ≫ f = q ≫ yoneda.map t := by
    rw [hq, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc
      (V.ι) (pullback.snd (yoneda.map t) f) f, ← hj, Category.assoc,
      IsIso.inv_hom_id_assoc]
  have sq : IsPullback (𝟙 U.toFunctor) q (U.ι ≫ f) (yoneda.map t) := by
    rw [hfac]
    exact IsPullback.of_horiz_isIso_mono ⟨Category.id_comp _⟩
  exact isRepresentable_of_isPullback_of_isPullback sq
    (IsPullback.of_hasPullback (U.ι ≫ f) (yoneda.map t)) inferInstance

/-- **The base case of the degree induction of Stacks 03XW, in the form the induction states
it.** In the situation of that tag with the degrees of the fibres of the étale `t : T' ⟶ T`
bounded by one, the base change `T' ×_T U` of the image `U` of `V'` in `X` is representable.

This is `AlgebraicGeometry.Space.isRepresentable_pullback_image_of_isOpenImmersion` composed with
`AlgebraicGeometry.isOpenImmersion_of_boundsFiberDegrees_one`, which is the proof's use of
Tag 025G.

Separatedness and local quasi-finiteness of `f`, affineness of `T` and algebraicity of `X` are
hypotheses of the inductive statement which this case does not use; they are omitted. -/
theorem isRepresentable_pullback_image_of_boundsFiberDegrees_one
    {T' T : BigFppfOver B S hS} (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    {t : T' ⟶ T} (ht : Etale ((BigFppfOver.toScheme B S hS).map t))
    (hdeg : BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map t) ((1 : ℕ) : ℤ))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ yoneda.obj T)
    (V : Subfunctor (pullback (yoneda.map t) f)) (hV : IsOpenSubspace B S hS V)
    (hVqa : IsQuasiAffineHom B S hS (V.ι ≫ pullback.fst (yoneda.map t) f)) :
    (pullback ((openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))).ι ≫ f) (yoneda.map t)).IsRepresentable := by
  have _ht := ht
  exact isRepresentable_pullback_image_of_isOpenImmersion hT'
    (isOpenImmersion_of_boundsFiberDegrees_one _ hdeg) f V hV hVqa


/-! ### Three cartesian squares of the inductive step

The step compares three base changes of one morphism `p₁ : P ⟶ Y₁`, where `P` is itself a fibre
product `Y₁ ×_{Y₀} X`: the base change along `α`, which is `Q`; the base change along a second
morphism `β` agreeing with `α` over `Y₀`, which is again `Q`; and `P` itself, along a section
`δ` of `β`. In the application `Y₁ = T'`, `Y₀ = T`, `P = T' ×_T X`, `A = T' ×_T T'` and
`α, β` are the two projections. The three lemmas are statements about an arbitrary category and
are assembled from the pasting lemmas for cartesian squares. -/

/-- A base change `Q` of `p₁ : P ⟶ Y₁` along `α : A ⟶ Y₁` is also a base change of `p₁` along
any `β : A ⟶ Y₁` agreeing with `α` over `Y₀`, provided `P` is a fibre product `Y₁ ×_{Y₀} X`.

The comparison morphism `v` is characterised by its two components `hv₁` and `hv₂`; it exists
because `P` is a fibre product. The square is cartesian because the big square obtained by
pasting it onto the one exhibiting `P` is the one exhibiting `Q`, the two differing only by the
hypothesis `α ≫ t = β ≫ t`. -/
private theorem isPullback_otherProjection {C : Type*} [Category C]
    {Y₀ Y₁ X A P Q : C} {t : Y₁ ⟶ Y₀} {f : X ⟶ Y₀} {α β : A ⟶ Y₁}
    {p₁ : P ⟶ Y₁} {p₂ : P ⟶ X} {r₁ : Q ⟶ A} {r₂ : Q ⟶ P} {v : Q ⟶ P}
    (hP : IsPullback p₁ p₂ t f) (hQ : IsPullback r₁ r₂ α p₁)
    (hv₁ : v ≫ p₁ = r₁ ≫ β) (hv₂ : v ≫ p₂ = r₂ ≫ p₂) (hαβ : α ≫ t = β ≫ t) :
    IsPullback v r₁ p₁ β := by
  have hbig : IsPullback (v ≫ p₂) r₁ f (β ≫ t) := by
    rw [hv₂, ← hαβ]
    exact hQ.flip.paste_horiz hP.flip
  exact hbig.of_right hv₁ hP.flip

/-- If moreover `α` and `β` themselves exhibit `A` as the fibre product `Y₁ ×_{Y₀} Y₁`, then the
comparison morphism `v` of `AlgebraicGeometry.Space.isPullback_otherProjection` exhibits `Q` as
the fibre product `P ×_X P`.

This is the square `X'' = X' ×_X X'` of Stacks 03XW. -/
private theorem isPullback_otherProjection_of_isPullback {C : Type*} [Category C]
    {Y₀ Y₁ X A P Q : C} {t : Y₁ ⟶ Y₀} {f : X ⟶ Y₀} {α β : A ⟶ Y₁}
    {p₁ : P ⟶ Y₁} {p₂ : P ⟶ X} {r₁ : Q ⟶ A} {r₂ : Q ⟶ P} {v : Q ⟶ P}
    (hP : IsPullback p₁ p₂ t f) (hQ : IsPullback r₁ r₂ α p₁)
    (hv₁ : v ≫ p₁ = r₁ ≫ β) (hv₂ : v ≫ p₂ = r₂ ≫ p₂) (hαβ : IsPullback α β t t) :
    IsPullback v r₂ p₂ p₂ := by
  have hA : IsPullback v r₁ p₁ β := isPullback_otherProjection hP hQ hv₁ hv₂ hαβ.w
  have hs : IsPullback v (r₁ ≫ α) (p₁ ≫ t) t := hA.paste_vert hαβ.flip
  rw [hQ.w, hP.w] at hs
  exact hs.of_bot hv₂ hP.flip

/-- A section `δ` of `β` makes `P` the base change of `Q` along `δ`.

This is the diagonal square `X' = T' ×_{T''} X''` of Stacks 03XW: the section is the relative
diagonal of `X' ⟶ X`, and it is a section of both projections. The morphism `d` is characterised
by its first component `hd₁` and the fact `hdv` that it is a section of the comparison
morphism `v`; the square is then cartesian because pasting it onto the square of
`AlgebraicGeometry.Space.isPullback_otherProjection` gives the identity square. -/
private theorem isPullback_diagonalSection {C : Type*} [Category C]
    {Y₀ Y₁ X A P Q : C} {t : Y₁ ⟶ Y₀} {f : X ⟶ Y₀} {α β : A ⟶ Y₁}
    {p₁ : P ⟶ Y₁} {p₂ : P ⟶ X} {r₁ : Q ⟶ A} {r₂ : Q ⟶ P} {v : Q ⟶ P}
    (hP : IsPullback p₁ p₂ t f) (hQ : IsPullback r₁ r₂ α p₁)
    (hv₁ : v ≫ p₁ = r₁ ≫ β) (hv₂ : v ≫ p₂ = r₂ ≫ p₂) (hαβ : α ≫ t = β ≫ t)
    {δ : Y₁ ⟶ A} (hδβ : δ ≫ β = 𝟙 Y₁) {d : P ⟶ Q} (hd₁ : d ≫ r₁ = p₁ ≫ δ)
    (hdv : d ≫ v = 𝟙 P) : IsPullback d p₁ r₁ δ := by
  have hA : IsPullback v r₁ p₁ β := isPullback_otherProjection hP hQ hv₁ hv₂ hαβ
  have hs : IsPullback (d ≫ v) p₁ p₁ (δ ≫ β) := by
    rw [hdv, hδβ]
    exact IsPullback.of_id_fst
  exact hs.of_right hd₁ hA

/-- A subfunctor which is the base change of an open subspace of an algebraic space along a
morphism of algebraic spaces is an open subspace. -/
private theorem isOpenSubspace_of_isPullback
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {Z : Subfunctor X} {N : Subfunctor Y}
    {l : N.toFunctor ⟶ Z.toFunctor} {g : Y ⟶ X} (sq : IsPullback l N.ι Z.ι g)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsOpenSubspace B S hS Z) : IsOpenSubspace B S hS N :=
  ⟨(isAlgebraicSpace_pullback B S hS Z.ι g hZ.1 hY hX).of_iso
      (sq.isoIsPullback _ _ (IsPullback.of_hasPullback Z.ι g)).symm,
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sq hZ.2⟩

/-- In a cartesian square of presheaves, the range on points of one leg is the preimage of the
range of the opposite leg. -/
private theorem preimage_range_pointsMap_of_isPullback
    {W W' Z Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {c : W' ⟶ W} {p' : W' ⟶ Z'} {p : W ⟶ Z}
    {h : Z' ⟶ Z} (sq : IsPullback c p' p h) :
    pointsMap B S hS Z' h ⁻¹' Set.range (pointsMap B S hS W p) =
      Set.range (pointsMap B S hS W' p') := by
  have := preimage_image_pointsMap_of_isPullback B S hS sq Set.univ
  rwa [Set.image_univ, Set.preimage_univ, Set.image_univ] at this

/-! ### `T^*` as an object of the site -/

/-- **`T^*` of the third paragraph of Stacks 03XW, as an object of the site.** For an étale
morphism `t : T' ⟶ T` of affine objects of the big fppf category over `S` whose fibre degrees
are bounded by `n + 1`, the open affine subscheme of `T'' = T' ×_T T'` complementary to the
image of the diagonal is again an object of the site; its first projection to `T'` is étale with
fibre degrees bounded by `n`, and together with the diagonal it covers `T''`.

The subscheme is `AlgebraicGeometry.offDiagonal` of the morphism of schemes underlying `t`,
transported to `T''` along the comparison isomorphism of
`AlgebraicGeometry.Space.preservesLimitsOfShape_walkingCospan_toScheme` and realised in the site
by `AlgebraicGeometry.exists_restrict_bigFppfOver`; the degree drop is
`AlgebraicGeometry.boundsFiberDegrees_offDiagonal_fst` and the covering is
`AlgebraicGeometry.coe_offDiagonal`. Separatedness of `t`, which `offDiagonal` needs, is
automatic for a morphism of affine schemes. -/
theorem exists_bigFppfOver_offDiagonal
    {T' T : BigFppfOver B S hS} (t : T' ⟶ T)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    (ht : Etale ((BigFppfOver.toScheme B S hS).map t))
    (n : ℕ)
    (hdeg : BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map t) ((n + 1 : ℕ) : ℤ)) :
    ∃ (Tst : BigFppfOver B S hS) (j : Tst ⟶ pullback t t),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Tst) ∧
      Etale ((BigFppfOver.toScheme B S hS).map (j ≫ pullback.fst t t)) ∧
      BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map (j ≫ pullback.fst t t)) (n : ℤ) ∧
      ∀ z : ((BigFppfOver.toScheme B S hS).obj (pullback t t) : Scheme.{u}),
        z ∈ Set.range ((BigFppfOver.toScheme B S hS).map (pullback.diagonal t)) ∨
        z ∈ Set.range ((BigFppfOver.toScheme B S hS).map j) := by
  have := hT
  have := hT'
  have := ht
  have : _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map t) :=
    inferInstance
  have hpres : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hsq : IsPullback ((BigFppfOver.toScheme B S hS).map (pullback.fst t t))
      ((BigFppfOver.toScheme B S hS).map (pullback.snd t t))
      ((BigFppfOver.toScheme B S hS).map t) ((BigFppfOver.toScheme B S hS).map t) :=
    (IsPullback.of_hasPullback t t).map (BigFppfOver.toScheme B S hS)
  set e := hsq.isoPullback with he
  have hefst : e.hom ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map t)
      ((BigFppfOver.toScheme B S hS).map t) =
      (BigFppfOver.toScheme B S hS).map (pullback.fst t t) := hsq.isoPullback_hom_fst
  have hesnd : e.hom ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map t)
      ((BigFppfOver.toScheme B S hS).map t) =
      (BigFppfOver.toScheme B S hS).map (pullback.snd t t) := hsq.isoPullback_hom_snd
  obtain ⟨Tst, j, hjoi, hjrange, -⟩ :=
    exists_restrict_bigFppfOver (pullback t t)
      (e.hom ⁻¹ᵁ offDiagonal ((BigFppfOver.toScheme B S hS).map t))
  have hjoi' : _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map j ≫ e.hom) := by
    have := hjoi
    infer_instance
  have hcomprange : ∀ {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z),
      Set.range ((a ≫ b) : X → Z) = b '' Set.range (a : X → Y) := by
    intro X Y Z a b
    rw [← Set.range_comp]
    rfl
  have hrange : Set.range (((BigFppfOver.toScheme B S hS).map j ≫ e.hom) :
      _ → ((pullback ((BigFppfOver.toScheme B S hS).map t)
        ((BigFppfOver.toScheme B S hS).map t) : Scheme.{u}) : Type u)) =
      (offDiagonal ((BigFppfOver.toScheme B S hS).map t) : Set _) := by
    have hsurj : Function.Surjective ((e.hom : _ → _)) := fun y => by
      obtain ⟨x, hx⟩ := e.hom.homeomorph.surjective y
      exact ⟨x, hx⟩
    rw [hcomprange, hjrange, Scheme.Hom.coe_preimage]
    exact Set.image_preimage_eq _ hsurj
  have hoi2 : _root_.AlgebraicGeometry.IsOpenImmersion
      (offDiagonal ((BigFppfOver.toScheme B S hS).map t)).ι := inferInstance
  set k := IsOpenImmersion.isoOfRangeEq ((BigFppfOver.toScheme B S hS).map j ≫ e.hom)
    (offDiagonal ((BigFppfOver.toScheme B S hS).map t)).ι
    (by rw [hrange, Scheme.Opens.range_ι]) with hk
  have hkfac : k.hom ≫ (offDiagonal ((BigFppfOver.toScheme B S hS).map t)).ι =
      (BigFppfOver.toScheme B S hS).map j ≫ e.hom :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hinj : Function.Injective ((e.hom : _ → _)) := fun a b hab =>
    e.hom.homeomorph.injective hab
  have hdfac : (BigFppfOver.toScheme B S hS).map (pullback.diagonal t) ≫ e.hom =
      pullback.diagonal ((BigFppfOver.toScheme B S hS).map t) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hefst, ← Functor.map_comp, pullback.diagonal_fst,
        CategoryTheory.Functor.map_id, pullback.diagonal_fst]
    · rw [Category.assoc, hesnd, ← Functor.map_comp, pullback.diagonal_snd,
        CategoryTheory.Functor.map_id, pullback.diagonal_snd]
  have hmapfac : (BigFppfOver.toScheme B S hS).map (j ≫ pullback.fst t t) =
      k.hom ≫ (offDiagonal ((BigFppfOver.toScheme B S hS).map t)).ι ≫
        pullback.fst ((BigFppfOver.toScheme B S hS).map t)
          ((BigFppfOver.toScheme B S hS).map t) := by
    rw [← Category.assoc, hkfac, Functor.map_comp, Category.assoc, hefst]
  refine ⟨Tst, j, ?_, ?_, ?_, ?_⟩
  · have : IsAffine (offDiagonal ((BigFppfOver.toScheme B S hS).map t)).toScheme :=
      isAffine_offDiagonal ((BigFppfOver.toScheme B S hS).map t)
    exact IsAffine.of_isIso k.hom
  · rw [hmapfac]
    have h1 : Etale ((offDiagonal ((BigFppfOver.toScheme B S hS).map t)).ι ≫
        pullback.fst ((BigFppfOver.toScheme B S hS).map t)
          ((BigFppfOver.toScheme B S hS).map t)) :=
      inferInstance
    infer_instance
  · rw [hmapfac]
    have hr : MorphismProperty.RespectsIso
        (fun {_ _ : Scheme.{u}} (p : _ ⟶ _) ↦ BoundsFiberDegrees p (n : ℤ)) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact MorphismProperty.RespectsIso.precomp
      (fun {_ _ : Scheme.{u}} (p : _ ⟶ _) ↦ BoundsFiberDegrees p (n : ℤ)) k.hom _
      (boundsFiberDegrees_offDiagonal_fst ((BigFppfOver.toScheme B S hS).map t) n hdeg)
  · intro z
    by_cases hz : z ∈ Set.range ((BigFppfOver.toScheme B S hS).map j)
    · exact Or.inr hz
    · refine Or.inl ?_
      have hzn : e.hom z ∉ (offDiagonal ((BigFppfOver.toScheme B S hS).map t) : Set _) := by
        intro hmem
        exact hz (by rw [hjrange, Scheme.Hom.coe_preimage]; exact hmem)
      rw [coe_offDiagonal, Set.mem_compl_iff, not_not] at hzn
      obtain ⟨y, hy⟩ := hzn
      refine ⟨y, hinj ?_⟩
      rw [← hy, ← hdfac]
      rfl

/-! ### The last paragraph: descent of representability to the image -/

/-- **The last paragraph of Stacks 03XW.** In the situation of that tag, representability of the
base change `T' ×_T U` of the image `U` of `V'` in `X` makes `U` itself representable.

The morphism `U ⟶ yoneda.obj T` factors through the open image `W ⊆ T` of `t`
(`AlgebraicGeometry.Space.exists_openImage_surjective_etale` and
`AlgebraicGeometry.Space.exists_lift_yoneda_of_forall_exists_factor`, applied section by section
through `AlgebraicGeometry.Space.range_map_app_subset_range_map_of_mem_image`), and `T' ⟶ W` is a
surjective étale chart of `W`. The factored morphism is separated and locally quasi-finite
because `U ⟶ yoneda.obj T` is and `yoneda.obj W ⟶ yoneda.obj T` is a monomorphism which is étale
after every representable base change; and `T' ×_W U = T' ×_T U` because `W ⟶ T` is a
monomorphism (`CategoryTheory.Limits.pullbackIsPullbackOfCompMono`). So
`AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_pullback_of_surjectiveEtaleChart`
applies.

Affineness of `T` and of `T'` and quasi-affineness of `V' ⟶ T'` are hypotheses of the tag which
this paragraph does not use; they are omitted. -/
theorem isRepresentable_image_of_isRepresentable_pullback_image
    {T' T : BigFppfOver B S hS} {t : T' ⟶ T}
    (ht : Etale ((BigFppfOver.toScheme B S hS).map t))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {f : X ⟶ yoneda.obj T} (hsep : IsSeparated B S hS f)
    (hlqf : IsLocallyQuasiFinite B S hS f)
    (V : Subfunctor (pullback (yoneda.map t) f)) (hV : IsOpenSubspace B S hS V)
    (hrep : (pullback ((openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))).ι ≫ f) (yoneda.map t)).IsRepresentable) :
    (openSubspaceOfPoints B S hS X
      (Set.range (pointsMap B S hS V.toFunctor
        (V.ι ≫ pullback.snd (yoneda.map t) f)))).toFunctor.IsRepresentable := by
  obtain ⟨W, q, w, hqw, hwoi, hwrange, hqsurj, hqet, hwfac⟩ :=
    exists_openImage_surjective_etale t ht
  set U := openSubspaceOfPoints B S hS X (Set.range (pointsMap B S hS V.toFunctor
    (V.ι ≫ pullback.snd (yoneda.map t) f))) with hUdef
  have hP : IsAlgebraicSpace B S hS (pullback (yoneda.map t) f) :=
    isAlgebraicSpace_pullback B S hS (yoneda.map t) f (isAlgebraicSpace_yoneda B S hS T')
      hX (isAlgebraicSpace_yoneda B S hS T)
  have hUopen : IsOpenSubspace B S hS U :=
    isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale hP hX
      (isEtale_pullback_snd_yoneda_map ht f) hV
  have hmw : Mono w := inverseImage_isOpenImmersion_le_monomorphisms w hwoi
  have hmyw : Mono (yoneda.map w) := inferInstance
  have hfac : ∀ (a : (BigFppfOver B S hS)ᵒᵖ) (x : U.toFunctor.obj a),
      ∃ h : a.unop ⟶ W, h ≫ w = (U.ι ≫ f).app a x := by
    intro a x
    exact hwfac (f.app a x.1) (range_map_app_subset_range_map_of_mem_image f V a x)
  obtain ⟨g, hg⟩ := exists_lift_yoneda_of_forall_exists_factor (f := U.ι ≫ f) hmw hfac
  have hsepUf : IsSeparated B S hS (U.ι ≫ f) :=
    isSeparated_comp B S hS U.ι f (isSeparated_of_mono U.ι inferInstance) hsep
  have hlqfUf : IsLocallyQuasiFinite B S hS (U.ι ≫ f) :=
    holdsOnEveryEtaleChart_etale_comp B S hS U.ι f
      (presheaf_etale_of_isOpenImmersion B S hS hUopen.2) hlqf
  have hwet : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map w) := by
    refine (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ w).2 ?_
    have := hwoi
    infer_instance
  have hsepg : IsSeparated B S hS g :=
    isSeparated_of_comp_mono g (yoneda.map w) hmyw (by rw [hg]; exact hsepUf)
  have hlqfg : IsLocallyQuasiFinite B S hS g :=
    holdsOnEveryEtaleChart_of_comp_etale g (yoneda.map w) hwet (by rw [hg]; exact hlqfUf)
  have sq : IsPullback (pullback.fst g (yoneda.map q)) (pullback.snd g (yoneda.map q))
      (g ≫ yoneda.map w) (yoneda.map q ≫ yoneda.map w) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono g (yoneda.map q) (yoneda.map w))
  rw [hg, ← Functor.map_comp, hqw] at sq
  have hrep' : (pullback g (yoneda.map q)).IsRepresentable :=
    isRepresentable_of_isPullback_of_isPullback (IsPullback.of_hasPullback (U.ι ≫ f)
      (yoneda.map t)) sq hrep
  exact isRepresentable_of_isRepresentable_pullback_of_surjectiveEtaleChart hUopen.1 g
    hsepg hlqfg hqsurj hqet hrep'

/-! ### The induction -/

/-- **The degree induction of Stacks 03XW.** For every `n`, in the situation of that tag with the
degrees of the fibres of the étale `t : T' ⟶ T` bounded by `n + 1`, the base change `T' ×_T U` of
the image `U` of `V'` in `X` is representable.

The statement is phrased as a single `∀ n, ...` and proved by induction on `n`, so that no
`Prop`-valued auxiliary definition is needed; `n + 1` rather than `n` is the bound so that the
base case is the bound one of Tag 025G, which is
`AlgebraicGeometry.Space.isRepresentable_pullback_image_of_boundsFiberDegrees_one`.

The step is the third and fourth paragraphs of the source; see the module docstring. -/
private theorem isRepresentable_pullback_image_of_boundsFiberDegrees_aux :
    ∀ (n : ℕ) {T' T : BigFppfOver B S hS},
      IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj T') →
      ∀ {t : T' ⟶ T}, Etale ((BigFppfOver.toScheme B S hS).map t) →
      BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map t) ((n + 1 : ℕ) : ℤ) →
      ∀ {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X →
      ∀ {f : X ⟶ yoneda.obj T}, IsSeparated B S hS f → IsLocallyQuasiFinite B S hS f →
      ∀ V : Subfunctor (pullback (yoneda.map t) f), IsOpenSubspace B S hS V →
      IsQuasiAffineHom B S hS (V.ι ≫ pullback.fst (yoneda.map t) f) →
      (pullback ((openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))).ι ≫ f) (yoneda.map t)).IsRepresentable := by
  intro n
  induction n with
  | zero =>
    intro T' T _hT hT' t ht hdeg X _hX f _hsep _hlqf V hV hVqa
    exact isRepresentable_pullback_image_of_boundsFiberDegrees_one hT' ht
      (by exact_mod_cast hdeg) _ V hV hVqa
  | succ n ih =>
    intro T' T hT hT' t ht hdeg X hX f hsep hlqf V hV hVqa
    -- the ambient base change `X' = T' ×_T X`
    set pf := pullback.fst (yoneda.map t) f with hpf
    set ps := pullback.snd (yoneda.map t) f with hps
    have hP : IsPullback pf ps (yoneda.map t) f := IsPullback.of_hasPullback (yoneda.map t) f
    -- `T'' = T' ×_T T'`, its two projections and its diagonal
    set aa := pullback.fst t t with haa
    set bb := pullback.snd t t with hbb
    set α := yoneda.map aa with hα
    set β := yoneda.map bb with hβ
    set δ := yoneda.map (pullback.diagonal t) with hδ
    have hαβsq : IsPullback α β (yoneda.map t) (yoneda.map t) :=
      (IsPullback.of_hasPullback t t).map yoneda
    -- the comparison `A ×_{T'} X' ⟶ X'` for the two projections `a, b : A ⟶ T'` over `T`
    have hcomp : ∀ {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a b : A ⟶ yoneda.obj T'),
        a ≫ yoneda.map t = b ≫ yoneda.map t →
        ∃ v : pullback a pf ⟶ pullback (yoneda.map t) f,
          v ≫ pf = pullback.fst a pf ≫ b ∧ v ≫ ps = pullback.snd a pf ≫ ps ∧
          IsPullback v (pullback.fst a pf) pf b := by
      intro A a b hab
      have hcond : (pullback.fst a pf ≫ b) ≫ yoneda.map t = (pullback.snd a pf ≫ ps) ≫ f := by
        rw [Category.assoc, ← hab, ← Category.assoc, pullback.condition, Category.assoc, hP.w,
          Category.assoc]
      exact ⟨pullback.lift _ _ hcond, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
        isPullback_otherProjection hP (IsPullback.of_hasPullback a pf) (pullback.lift_fst _ _ _)
          (pullback.lift_snd _ _ _) hab⟩
    -- `X'' = T'' ×_{T'} X'` and its two projections `p₁` and `p₀ = v`
    set qf := pullback.fst α pf with hqf
    set qs := pullback.snd α pf with hqs
    have hQ : IsPullback qf qs α pf := IsPullback.of_hasPullback α pf
    obtain ⟨v, hv1, hv2, -⟩ := hcomp α β hαβsq.w
    have hvself : IsPullback v qs ps ps :=
      isPullback_otherProjection_of_isPullback hP hQ hv1 hv2 hαβsq
    -- the relative diagonal of `X' ⟶ X`, a section of both projections
    have hδα : δ ≫ α = 𝟙 (yoneda.obj T') := by
      rw [hδ, hα, ← Functor.map_comp, haa, pullback.diagonal_fst,
        CategoryTheory.Functor.map_id]
    have hδβ : δ ≫ β = 𝟙 (yoneda.obj T') := by
      rw [hδ, hβ, ← Functor.map_comp, hbb, pullback.diagonal_snd,
        CategoryTheory.Functor.map_id]
    have hdcond : (pf ≫ δ) ≫ α = 𝟙 _ ≫ pf := by
      rw [Category.assoc, hδα, Category.comp_id, Category.id_comp]
    set d := pullback.lift (pf ≫ δ) (𝟙 _) hdcond with hd
    have hd1 : d ≫ qf = pf ≫ δ := pullback.lift_fst _ _ _
    have hd2 : d ≫ qs = 𝟙 _ := pullback.lift_snd _ _ _
    have hdv : d ≫ v = 𝟙 _ := by
      refine hP.hom_ext ?_ ?_
      · rw [Category.assoc, hv1, ← Category.assoc, hd1, Category.assoc, hδβ,
          Category.comp_id, Category.id_comp]
      · rw [Category.assoc, hv2, ← Category.assoc, hd2, Category.id_comp]
    have hdsq : IsPullback d pf qf δ :=
      isPullback_diagonalSection hP hQ hv1 hv2 hαβsq.w hδβ hd1 hdv
    -- `T^*`, the off-diagonal piece, and the degree drop
    obtain ⟨Tst, j, hTstAff, hqEt, hqDeg, hcover⟩ :=
      exists_bigFppfOver_offDiagonal t hT hT' ht (n + 1) hdeg
    set q := j ≫ aa with hq
    set q' := j ≫ bb with hq'
    set jj := yoneda.map j with hjj
    -- `X^* = T^* ×_{T'} X'`
    set sf := pullback.fst (yoneda.map q) pf with hsf
    set ss := pullback.snd (yoneda.map q) pf with hss
    have hQs : IsPullback sf ss (yoneda.map q) pf := IsPullback.of_hasPullback _ _
    have hjjα : jj ≫ α = yoneda.map q := by rw [hjj, hα, ← Functor.map_comp]
    have hjjβ : jj ≫ β = yoneda.map q' := by rw [hjj, hβ, ← Functor.map_comp]
    have hqq' : yoneda.map q ≫ (yoneda.map t) = yoneda.map q' ≫ (yoneda.map t) := by
      rw [← Functor.map_comp, ← Functor.map_comp, hq, hq', Category.assoc,
        Category.assoc, haa, hbb, pullback.condition]
    obtain ⟨vs, hvs1, hvs2, hvssq⟩ := hcomp (yoneda.map q) (yoneda.map q') hqq'
    -- the comparison `X^* ⟶ X''`
    have hmmcond : (sf ≫ jj) ≫ α = ss ≫ pf := by
      rw [Category.assoc, hjjα, hQs.w]
    set mm := pullback.lift (sf ≫ jj) ss hmmcond with hmm
    have hmm1 : mm ≫ qf = sf ≫ jj := pullback.lift_fst _ _ _
    have hmm2 : mm ≫ qs = ss := pullback.lift_snd _ _ _
    have hmmsq : IsPullback sf mm jj qf := by
      refine IsPullback.of_bot ?_ hmm1.symm hQ
      rw [hmm2, hjjα]
      exact hQs
    have hmmv : mm ≫ v = vs := by
      refine hP.hom_ext ?_ ?_
      · rw [Category.assoc, hv1, ← Category.assoc, hmm1, Category.assoc, hjjβ, hvs1]
      · rw [Category.assoc, hv2, ← Category.assoc, hmm2, hvs2]
    -- algebraicity of the two base changes
    have hX' : IsAlgebraicSpace B S hS (pullback (yoneda.map t) f) :=
      isAlgebraicSpace_pullback B S hS (yoneda.map t) f (isAlgebraicSpace_yoneda B S hS T') hX
        (isAlgebraicSpace_yoneda B S hS T)
    have hXs : IsAlgebraicSpace B S hS (pullback (yoneda.map q) pf) :=
      isAlgebraicSpace_pullback B S hS (yoneda.map q) pf
        (isAlgebraicSpace_yoneda B S hS Tst) hX' (isAlgebraicSpace_yoneda B S hS T')
    -- the open subspace `p₀⁻¹(V') ∩ X^*`, quasi-affine over `T^*` by base change
    set Vs := Subfunctor.preimage V vs with hVs
    obtain ⟨Vlift, hVslift⟩ : ∃ l, IsPullback l Vs.ι V.ι vs :=
      ⟨_, Subfunctor.isPullback_lift V vs Vs fun _ _ => Iff.rfl⟩
    have hVsOpen : IsOpenSubspace B S hS Vs :=
      isOpenSubspace_of_isPullback hVslift hX' hXs hV
    have hVsqa : IsQuasiAffineHom B S hS (Vs.ι ≫ sf) :=
      IsQuasiAffineHom.of_isPullback (hVslift.paste_vert hvssq) hVqa
    -- separatedness and local quasi-finiteness of `X' ⟶ T'`, by base change
    have hsep' : IsSeparated B S hS pf := by
      have hfac : pf = (pullbackSymmetry (yoneda.map t) f).hom ≫ pullback.snd f (yoneda.map t) :=
        (pullbackSymmetry_hom_comp_snd _ _).symm
      rw [hfac]
      exact isSeparated_comp B S hS _ _ (isSeparated_of_isIso B S hS _)
        (isSeparated_pullbackSnd B S hS (yoneda.map t) hsep)
    have hlqf' : IsLocallyQuasiFinite B S hS pf :=
      IsLocallyQuasiFinite.of_isPullback B S hS hP hX (isAlgebraicSpace_yoneda B S hS T) hlqf
    -- the induction hypothesis, and the descent of the image it produces
    have hih := ih hT' hTstAff hqEt hqDeg hX' hsep' hlqf' Vs hVsOpen hVsqa
    set Us := openSubspaceOfPoints B S hS (pullback (yoneda.map t) f)
      (Set.range (pointsMap B S hS Vs.toFunctor (Vs.ι ≫ ss))) with hUs
    have hUsrep : Us.toFunctor.IsRepresentable :=
      isRepresentable_image_of_isRepresentable_pullback_image hqEt hX' hsep' hlqf' Vs
        hVsOpen hih
    have hUsOpen : IsOpenSubspace B S hS Us :=
      isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale hXs hX'
        (isEtale_pullback_snd_yoneda_map hqEt pf) hVsOpen
    have hVrep : V.toFunctor.IsRepresentable :=
      (isRepresentable_of_isQuasiAffineHom_openSubspace hT' t f V hVqa).1
    have hsup : ((V ⊔ Us).sheafify (BigFppfOver.topology B S hS)).toFunctor.IsRepresentable :=
      isRepresentable_sheafify_sup hX'.isSheaf hV.2 hUsOpen.2 hVrep hUsrep
    have hsupOpen : IsOpenSubspace B S hS
        ((V ⊔ Us).sheafify (BigFppfOver.topology B S hS)) :=
      isOpenSubspace_sheafify_sup hX'.isSheaf hV.2 hUsOpen.2 hVrep hUsrep
    -- the image `U ⊆ X` and its preimage `T' ×_T U ⊆ X'`
    set U := openSubspaceOfPoints B S hS X
      (Set.range (pointsMap B S hS V.toFunctor (V.ι ≫ ps))) with hU
    set K := Subfunctor.preimage U ps with hK
    obtain ⟨Klift, hKlift⟩ : ∃ l, IsPullback l K.ι U.ι ps :=
      ⟨_, Subfunctor.isPullback_lift U ps K fun _ _ => Iff.rfl⟩
    have hUOpen : IsOpenSubspace B S hS U :=
      isOpenSubspace_openSubspaceOfPoints_range_comp_of_isEtale hX' hX
        (isEtale_pullback_snd_yoneda_map ht f) hV
    have hKOpen : IsOpenSubspace B S hS K := isOpenSubspace_of_isPullback hKlift hX hX' hUOpen
    have hKrange : Set.range (pointsMap B S hS K.toFunctor K.ι) =
        pointsMap B S hS (pullback (yoneda.map t) f) ps ⁻¹'
          (pointsMap B S hS (pullback (yoneda.map t) f) ps ''
            Set.range (pointsMap B S hS V.toFunctor V.ι)) := by
      rw [← preimage_range_pointsMap_of_isPullback hKlift, hU,
        range_pointsMap_ι_openSubspaceOfPoints, pointsMap_comp, Set.range_comp]
    -- the decomposition `p₁(p₀⁻¹(V')) = V' ∪ U^*` on point sets
    have hsub : Set.range (pointsMap B S hS K.toFunctor K.ι) ⊆
        Set.range (pointsMap B S hS V.toFunctor V.ι) ∪
          Set.range (pointsMap B S hS Us.toFunctor Us.ι) := by
      rw [hKrange, preimage_image_pointsMap_of_isPullback B S hS hvself]
      rintro - ⟨wpt, hwpt, rfl⟩
      rcases hcover (pointsToScheme B S hS (pullback t t)
          (pointsMap B S hS _ qf wpt)) with ⟨y0, hy0⟩ | ⟨y0, hy0⟩
      · obtain ⟨y1, hy1⟩ := surjective_pointsToScheme B S hS T' y0
        have hkey : pointsMap B S hS _ qf wpt =
            pointsMap B S hS (yoneda.obj T') δ y1 := by
          refine injective_pointsToScheme B S hS (pullback t t) ?_
          rw [hδ, pointsToScheme_pointsMap_yoneda, hy1, hy0]
        obtain ⟨v0, hv0a, -⟩ := exists_points_of_isPullback B S hS hdsq wpt y1 hkey
        refine Set.mem_union_left _ ?_
        have h1 : pointsMap B S hS _ qs wpt = v0 := by
          rw [← hv0a, ← pointsMap_comp_apply, hd2, pointsMap_id]
          rfl
        have h2 : pointsMap B S hS _ v wpt = v0 := by
          rw [← hv0a, ← pointsMap_comp_apply, hdv, pointsMap_id]
          rfl
        rw [h1, ← h2]
        exact hwpt
      · obtain ⟨y1, hy1⟩ := surjective_pointsToScheme B S hS Tst y0
        have hkey : pointsMap B S hS (yoneda.obj Tst) jj y1 =
            pointsMap B S hS _ qf wpt := by
          refine injective_pointsToScheme B S hS (pullback t t) ?_
          rw [hjj, pointsToScheme_pointsMap_yoneda, hy1, hy0]
        obtain ⟨u, -, hub⟩ := exists_points_of_isPullback B S hS hmmsq y1 wpt hkey
        refine Set.mem_union_right _ ?_
        have hvu : pointsMap B S hS _ vs u = pointsMap B S hS _ v wpt := by
          rw [← hmmv, pointsMap_comp_apply, hub]
        have humem : u ∈ Set.range (pointsMap B S hS Vs.toFunctor Vs.ι) := by
          rw [← preimage_range_pointsMap_of_isPullback hVslift, Set.mem_preimage, hvu]
          exact hwpt
        obtain ⟨u0, hu0⟩ := humem
        rw [hUs, range_pointsMap_ι_openSubspaceOfPoints]
        refine ⟨u0, ?_⟩
        rw [pointsMap_comp_apply, hu0, ← hmm2, pointsMap_comp_apply, hub]
    -- the two open subspaces of `X'` agree, so `T' ×_T U` is representable
    have hmono : ∀ {G H : Subfunctor (pullback (yoneda.map t) f)}, G ≤ H →
        Set.range (pointsMap B S hS G.toFunctor G.ι) ⊆
          Set.range (pointsMap B S hS H.toFunctor H.ι) := by
      intro G H hGH
      rw [← Subfunctor.homOfLe_ι hGH, pointsMap_comp, Set.range_comp]
      exact Set.image_subset_range _ _
    have hKle : K ≤ (V ⊔ Us).sheafify (BigFppfOver.topology B S hS) :=
      le_of_range_pointsMap_ι_subset B S hS hsupOpen
        (hsub.trans (Set.union_subset
          (hmono (le_sup_left.trans ((V ⊔ Us).le_sheafify _)))
          (hmono (le_sup_right.trans ((V ⊔ Us).le_sheafify _)))))
    have hVleK : V ≤ K :=
      le_of_range_pointsMap_ι_subset B S hS hKOpen
        (by rw [hKrange]; exact Set.subset_preimage_image _ _)
    have hUsleK : Us ≤ K := by
      refine le_of_range_pointsMap_ι_subset B S hS hKOpen ?_
      rw [hKrange, hUs, range_pointsMap_ι_openSubspaceOfPoints]
      rintro - ⟨u0, rfl⟩
      have hmor : (Vs.ι ≫ ss) ≫ ps = (Vlift ≫ V.ι) ≫ ps := by
        rw [Category.assoc, ← hvs2, ← Category.assoc, ← hVslift.w, Category.assoc]
      have hpt : pointsMap B S hS Vs.toFunctor ((Vs.ι ≫ ss) ≫ ps) u0 =
          pointsMap B S hS Vs.toFunctor ((Vlift ≫ V.ι) ≫ ps) u0 := by rw [hmor]
      rw [Set.mem_preimage, ← pointsMap_comp_apply, hpt, pointsMap_comp_apply,
        pointsMap_comp_apply]
      exact ⟨_, ⟨_, rfl⟩, rfl⟩
    have hsheafX' : Presieve.IsSheaf (BigFppfOver.topology B S hS) (pullback (yoneda.map t) f) :=
      (isSheaf_iff_isSheaf_of_type _ _).1 hX'.isSheaf
    have hsheafK : Presieve.IsSheaf (BigFppfOver.topology B S hS) K.toFunctor :=
      (isSheaf_iff_isSheaf_of_type _ _).1 hKOpen.1.isSheaf
    have hKeq : K = (V ⊔ Us).sheafify (BigFppfOver.topology B S hS) :=
      le_antisymm hKle (Subfunctor.sheafify_le (V ⊔ Us) K
        (sup_le hVleK hUsleK) hsheafX' hsheafK)
    have hKrep : K.toFunctor.IsRepresentable := hKeq ▸ hsup
    refine isRepresentable_pullback_ι_comp_of_isRepresentable t f U ?_
    exact isRepresentable_of_isPullback_of_isPullback hKlift
      (IsPullback.of_hasPullback U.ι ps) hKrep

/-! ### Stacks 03XW -/

/-- **Representability of the image, Stacks 03XW.** In the situation of that tag — `t : T' ⟶ T`
an étale morphism of affine objects of the big fppf category over `S`, `f : X ⟶ yoneda.obj T` a
separated and locally quasi-finite morphism of algebraic spaces over `S`, and `V'` an open
subspace of `T' ×_T X` which is quasi-affine over `T'` — the image of `V'` in `X` is
representable.

The fibre degrees of `t` are universally bounded by Tag 03JA
(`AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite`, applicable because an
étale morphism is locally of finite type and locally quasi-finite and an affine scheme is
quasi-compact), so the bound may be taken of the form `n + 1`; the induction
`AlgebraicGeometry.Space.isRepresentable_pullback_image_of_boundsFiberDegrees_aux` then makes
`T' ×_T U` representable and
`AlgebraicGeometry.Space.isRepresentable_image_of_isRepresentable_pullback_image` descends that
to `U`. -/
theorem isRepresentable_image_of_isQuasiAffineHom
    {T' T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    {t : T' ⟶ T} (ht : Etale ((BigFppfOver.toScheme B S hS).map t))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {f : X ⟶ yoneda.obj T} (hsep : IsSeparated B S hS f)
    (hlqf : IsLocallyQuasiFinite B S hS f)
    (V : Subfunctor (pullback (yoneda.map t) f)) (hV : IsOpenSubspace B S hS V)
    (hVqa : IsQuasiAffineHom B S hS (V.ι ≫ pullback.fst (yoneda.map t) f)) :
    (openSubspaceOfPoints B S hS X
      (Set.range (pointsMap B S hS V.toFunctor
        (V.ι ≫ pullback.snd (yoneda.map t) f)))).toFunctor.IsRepresentable := by
  have := hT
  have := hT'
  have := ht
  have hcs : CompactSpace ((BigFppfOver.toScheme B S hS).obj T' : Scheme.{u}) := inferInstance
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map t) := inferInstance
  have hlqfs : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map t) := inferInstance
  obtain ⟨m, hm⟩ :=
    hasUniversallyBoundedFibers_of_locallyQuasiFinite ((BigFppfOver.toScheme B S hS).map t)
  obtain ⟨n, hnm⟩ : ∃ n : ℕ, m ≤ ((n + 1 : ℕ) : ℤ) := ⟨m.toNat, by push_cast; omega⟩
  have hdeg : BoundsFiberDegrees ((BigFppfOver.toScheme B S hS).map t) ((n + 1 : ℕ) : ℤ) := by
    intro y
    obtain ⟨r, hr, hrk⟩ := hm y
    exact ⟨r, hr.trans hnm, hrk⟩
  exact isRepresentable_image_of_isRepresentable_pullback_image ht hX hsep hlqf V hV
    (isRepresentable_pullback_image_of_boundsFiberDegrees_aux n hT hT' ht hdeg hX hsep hlqf
      V hV hVqa)

/-- **Stacks 03XW.** Let `t : T' ⟶ T` be an étale morphism of affine objects of the big fppf
category over `S`, let `f : X ⟶ yoneda.obj T` be a separated and locally quasi-finite morphism
of algebraic spaces over `S`, and let `V'` be an open subspace of `T' ×_T X` which is
quasi-affine over `T'`. Then the image of `V'` in `X` is a quasi-compact open subspace of `X`
which is representable.

The image is the subspace cut out by the image of the point set of `V'`, whose own point set is
that image by Tag 03BZ. Openness and quasi-compactness are
`AlgebraicGeometry.Space.isOpenSubspace_isQuasiCompactSpace_image_of_isQuasiAffineHom` and
representability is `AlgebraicGeometry.Space.isRepresentable_image_of_isQuasiAffineHom`. -/
@[stacks 03XW]
theorem isOpenSubspace_isQuasiCompactSpace_isRepresentable_image
    {T' T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T'))
    {t : T' ⟶ T} (ht : Etale ((BigFppfOver.toScheme B S hS).map t))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    {f : X ⟶ yoneda.obj T} (hsep : IsSeparated B S hS f)
    (hlqf : IsLocallyQuasiFinite B S hS f)
    (V : Subfunctor (pullback (yoneda.map t) f)) (hV : IsOpenSubspace B S hS V)
    (hVqa : IsQuasiAffineHom B S hS (V.ι ≫ pullback.fst (yoneda.map t) f)) :
    IsOpenSubspace B S hS (openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))) ∧
      IsQuasiCompactSpace B S hS (openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))).toFunctor ∧
      (openSubspaceOfPoints B S hS X
        (Set.range (pointsMap B S hS V.toFunctor
          (V.ι ≫ pullback.snd (yoneda.map t) f)))).toFunctor.IsRepresentable :=
  ⟨(isOpenSubspace_isQuasiCompactSpace_image_of_isQuasiAffineHom hT' ht hX f V hV hVqa).1,
    (isOpenSubspace_isQuasiCompactSpace_image_of_isQuasiAffineHom hT' ht hX f V hV hVqa).2,
    isRepresentable_image_of_isQuasiAffineHom hT hT' ht hX hsep hlqf V hV hVqa⟩

end AlgebraicGeometry.Space

end
