module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism

/-!
# A finite subfamily of the atlas covering a quasi-compact point of a formal algebraic space

Let `S` be a scheme contained in a big fppf site `B`, let `X` be a formal algebraic space over
`S` and let `c : h_T ⟶ X` be a point of `X` with values in an object `T` of the big fppf
category over `S`. Definition **Stacks 0AIM** gives `X` an atlas `{Xᵢ ⟶ X}` of affine formal
algebraic spaces mapping to it representably and étale and jointly surjective; the base changes
`Vᵢ = Xᵢ ×_X T` are then objects of the site, by **Stacks 0AIG** in the form
`AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_isEtale_of_isAffineFormal`, and the
morphisms `Vᵢ ⟶ T` are étale and jointly surjective on points.

This file extracts a *finite* such subfamily when the underlying space of `T` is compact — in
particular when `T` is affine. That is the step the existence half of the proof of
**Stacks 0AQD** needs before it can replace the chosen charts by a single affine formal
algebraic space: a coproduct of affine formal algebraic spaces over the site is again one only
for a finite index, `AlgebraicGeometry.FormalSpace.finiteCoproductsAffineFormal`.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_finite_atlas_pullback_cover_of_compactSpace`: the finite
  subfamily, for a point of `X` with compact underlying space.
* `AlgebraicGeometry.FormalSpace.exists_finite_atlas_pullback_cover_of_isAffine`: the same for
  an affine object of the site.

## What is assumed

Nothing. In particular this is *not* the implication (1) ⇒ (2) of **Stacks 0AJ9**, which is the
hypothesis `hFiniteRefinement` of
`AlgebraicGeometry.FormalSpace.tfae_isQuasiCompactSpace`: there the finite subfamily must still
cover `X`, which needs quasi-compactness of `X` itself and the étale covering of its reduction.
Here only the *base changes along one point* are asked to cover, and only compactness of that
point's source is used, so the finite subcover is a statement about the underlying topological
space of an object of the site. The two are independent, and nothing below routes through
`AlgebraicGeometry.FormalSpace.CoproductsRepresentableEtale`, which is unproved.

## Implementation notes

The three steps are:

* *Joint surjectivity.* Local surjectivity of `∐ᵢ Xᵢ ⟶ X` makes the supremum of the image
  sieves of the atlas arrows at the section `c` a covering sieve,
  `AlgebraicGeometry.FormalSpace.family_imageSieve_mem`; refining that sieve by one of the
  site's chosen covering families, `AlgebraicGeometry.Space.exists_covering_refining_sieve`,
  exhibits every point of `T` in the image of a morphism of the site which lifts to some `Xᵢ`,
  and such a lift factors through `Vᵢ` by the universal property of the fibre product.
* *Openness.* `Vᵢ ⟶ T` is étale, so its image is open. Étaleness is read off from the étaleness
  of the atlas arrow after a represented base change through
  `AlgebraicGeometry.Space.isEtaleULift_uliftYoneda_map_iff`, the comparison isomorphism between
  `h_{Vᵢ}` and the fibre product of presheaves being absorbed by the fact that étaleness after a
  represented base change respects isomorphisms.
* *Finiteness.* The underlying space of `T` is compact, so the open cover by those images has a
  finite subcover; the corresponding subfamily of the atlas is the conclusion.

The conclusion keeps the whole fibre product datum — the atlas members, their arrows to `X`, the
objects of the site representing the base changes, and the pullback squares — because a consumer
needs the squares to recognise the finite family as a subfamily of an atlas rather than as an
unrelated étale covering of `T`. The index type of the subfamily is a subtype of the index type
of the atlas and so lives in `Type (u + 1)`, which is what the finite coproduct lemmas of this
library consume.

## References

* [Stacks Project, Tag 0AIG](https://stacks.math.columbia.edu/tag/0AIG)
* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
* [Stacks Project, Tag 0AQD](https://stacks.math.columbia.edu/tag/0AQD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The base change `V ⟶ T` of a morphism of sheaves along a point `c : h_T ⟶ X` is étale
when the fibre product is represented by `V` and the base change is étale. -/
private theorem etale_map_of_isPullback {X Z : FppfSheaf B S hS} (g : Z ⟶ X)
    {T V : BigFppfOver B S hS} (q : V ⟶ T) (c : uliftYoneda.{u + 1}.obj T ⟶ X.obj)
    (ξ : uliftYoneda.{u + 1}.obj V ⟶ Z.obj)
    (hsq : IsPullback ξ (uliftYoneda.{u + 1}.map q) g.hom c)
    (hfst : Space.IsEtaleULift.{u + 1} B S hS (pullback.fst c g.hom)) :
    Etale ((BigFppfOver.toScheme B S hS).map q) := by
  let Y := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)
  let P := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  rw [← Space.isEtaleULift_uliftYoneda_map_iff.{u + 1, u} B S hS q]
  intro U φ hφ
  have he : Y.map q = hsq.flip.isoPullback.hom ≫ pullback.fst c g.hom :=
    hsq.flip.isoPullback_hom_fst.symm
  rw [he, ← Category.assoc]
  exact hfst U _ (((P.relative Y).cancel_right_of_respectsIso φ _).mpr hφ)

/-- If `∐ᵢ Xᵢ ⟶ X` is locally surjective, then the base changes `Vᵢ ⟶ T` of the `Xᵢ ⟶ X` along a
point `c : h_T ⟶ X` are jointly surjective on points of `T`. -/
private theorem exists_mem_range_of_isLocallySurjective {X : FppfSheaf B S hS}
    {I : Type (u + 1)} (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f))
    {T : BigFppfOver B S hS} (c : uliftYoneda.{u + 1}.obj T ⟶ X.obj)
    {V : I → BigFppfOver B S hS} (q : ∀ i, V i ⟶ T)
    {ξ : ∀ i, uliftYoneda.{u + 1}.obj (V i) ⟶ (Xi i).obj}
    (hsq : ∀ i, IsPullback (ξ i) (uliftYoneda.{u + 1}.map (q i)) (f i).hom c)
    (x : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i)) := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let C := BigFppfOver B S hS
  let Y := uliftYoneda.{u + 1} (C := C)
  have hmem := family_imageSieve_mem J Xi X f hcover T (uliftYonedaEquiv c)
  rw [GrothendieckTopology.mem_over_iff] at hmem
  obtain ⟨E, hE, hER⟩ := AlgebraicGeometry.Space.exists_covering_refining_sieve B hmem
  have hEF := B.isFppfCovering_of_isCovering hE
  rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
    PreZeroHypercover.presieve₀, Presieve.map_ofArrows,
    Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff] at hEF
  obtain ⟨j, y, hy⟩ := hEF.1 x
  let T₀ : C := Over.mk (E.f j ≫ T.hom)
  let b : T₀ ⟶ T := Over.homMk (E.f j)
  have hb := (Sieve.overEquiv_iff _ _).mp (hER _ _ ⟨j⟩)
  change (⨆ i, Presheaf.imageSieve (f i).hom (uliftYonedaEquiv c)) b at hb
  simp only [iSup, Sieve.sSup_apply, Set.mem_range] at hb
  obtain ⟨_, ⟨i, rfl⟩, z, hz⟩ := hb
  let m : Y.obj T₀ ⟶ (Xi i).obj := uliftYonedaEquiv.symm z
  have hw : m ≫ (f i).hom = Y.map b ≫ c := by
    apply uliftYonedaEquiv.injective
    rw [uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hz.trans (uliftYonedaEquiv_naturality.{u + 1} c b.op)
  let r : T₀ ⟶ V i := Y.preimage ((hsq i).lift m (Y.map b) hw)
  have hr : r ≫ q i = b := by
    apply Y.map_injective
    rw [Y.map_comp, Y.map_preimage]
    exact (hsq i).lift_snd m (Y.map b) hw
  refine ⟨i, (BigFppfOver.toScheme B S hS).map r y, ?_⟩
  rwa [← Scheme.Hom.comp_apply, ← Functor.map_comp, hr]

/-- **A finite subfamily of a covering family whose base changes cover a compact point.** Let
`{Xᵢ ⟶ X}` be a family as in Definition **Stacks 0AIM** — affine formal algebraic spaces mapping
to `X` representably by algebraic spaces and étale, jointly surjective as a map of sheaves — and
let `c : h_T ⟶ X` be a point of `X` with values in an object `T` of the big fppf category over
`S` whose underlying space is compact. Then every base change `Xᵢ ×_X T` is represented by an
object `Vᵢ` of the site, every `Vᵢ ⟶ T` is étale, and a finite set of indices already covers `T`
on points.

This is `AlgebraicGeometry.FormalSpace.exists_finite_atlas_pullback_cover_of_compactSpace` for
an arbitrary such family rather than for the atlas carried by a proof that `X` is a formal
algebraic space, and it keeps the indices: the finite subfamily is the family restricted to `s`,
so a consumer can still use what it knows about the given members. -/
theorem exists_finset_pullback_cover_of_compactSpace {X : FppfSheaf B S hS}
    {I : Type (u + 1)} (Xi : I → FppfSheaf B S hS) (f : ∀ i, Xi i ⟶ X)
    (hXi : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i))
    (hf : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi)
    (hcover : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f))
    {T : BigFppfOver B S hS} [CompactSpace ((BigFppfOver.toScheme B S hS).obj T)]
    (c : uliftYoneda.{u + 1}.obj T ⟶ X.obj) :
    ∃ (s : Finset I) (V : I → BigFppfOver B S hS) (q : ∀ i, V i ⟶ T)
      (ξ : ∀ i, uliftYoneda.{u + 1}.obj (V i) ⟶ (Xi i).obj),
      (∀ i, IsPullback (ξ i) (uliftYoneda.{u + 1}.map (q i)) (f i).hom c) ∧
      (∀ i, Etale ((BigFppfOver.toScheme B S hS).map (q i))) ∧
      ∀ x : (BigFppfOver.toScheme B S hS).obj T,
        ∃ i ∈ s, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q i)) := by
  classical
  -- Stacks 0AIG: every atlas arrow is representable by objects of the site
  choose V q ξ hsq using fun i ↦ relativelyRepresentable_of_isEtale_of_isAffineFormal
    B S hS (f i) (hXi i) (hf i).1 (hf i).2 c
  -- étaleness of the atlas arrow after the represented base change along `c`
  -- each `Vᵢ ⟶ T` is étale, the comparison isomorphism being absorbed
  have hq i : Etale ((BigFppfOver.toScheme B S hS).map (q i)) :=
    etale_map_of_isPullback B S hS (f i) (q i) c (ξ i) (hsq i) ((hf i).2 T c)
  -- the images are open and the space is compact, so finitely many of them suffice
  have hOopen i : IsOpen (Set.range ((BigFppfOver.toScheme B S hS).map (q i))) := by
    have := hq i
    exact (Scheme.Hom.isOpenMap ((BigFppfOver.toScheme B S hS).map (q i))).isOpen_range
  -- every point of `T` is met by some member of the base-changed family
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover _ hOopen fun x _ ↦
    Set.mem_iUnion.2 (exists_mem_range_of_isLocallySurjective B S hS Xi f hcover c q hsq x)
  refine ⟨s, V, q, ξ, hsq, hq, fun x ↦ ?_⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact ⟨i, hi, hx⟩


/-- **A finite subfamily of the atlas whose base changes cover a compact point.** Let `X` be a
formal algebraic space over `S` and let `c : h_T ⟶ X` be a morphism from the universe-lifted
Yoneda presheaf of an object `T` of the big fppf category over `S` whose underlying space is
compact. Then there are finitely many affine formal algebraic spaces `Xₖ`, mapping to `X`
representably and étale as in Definition **Stacks 0AIM**, whose base changes along `c` are
represented by objects `Vₖ` of the site, are étale over `T`, and cover `T` on points.

Joint surjectivity of the full atlas is the content of
`AlgebraicGeometry.FormalSpace.family_imageSieve_mem`; the base changes are objects of the site
by **Stacks 0AIG**; the images are open because the base changes are étale; and the subfamily is
finite because the space is compact. -/
theorem exists_finite_atlas_pullback_cover_of_compactSpace {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {T : BigFppfOver B S hS}
    [CompactSpace ((BigFppfOver.toScheme B S hS).obj T)]
    (c : uliftYoneda.{u + 1}.obj T ⟶ X.obj) :
    ∃ (K : Type (u + 1)) (Xi : K → FppfSheaf B S hS) (f : ∀ k, Xi k ⟶ X)
      (V : K → BigFppfOver B S hS) (q : ∀ k, V k ⟶ T)
      (ξ : ∀ k, uliftYoneda.{u + 1}.obj (V k) ⟶ (Xi k).obj),
      Finite K ∧
      (∀ k, IsAffineFormalAlgebraicSpace B S hS (Xi k)) ∧
      (∀ k, ∃ hfk : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f k).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f k).hom hfk) ∧
      (∀ k, IsPullback (ξ k) (uliftYoneda.{u + 1}.map (q k)) (f k).hom c) ∧
      (∀ k, Etale ((BigFppfOver.toScheme B S hS).map (q k))) ∧
      ∀ x : (BigFppfOver.toScheme B S hS).obj T,
        ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q k)) := by
  obtain ⟨-, I, Xi, f, hXi, hf, hcover⟩ := hX
  obtain ⟨s, V, q, ξ, hsq, hq, hcov⟩ :=
    exists_finset_pullback_cover_of_compactSpace B S hS Xi f hXi hf hcover c
  refine ⟨{i : I // i ∈ s}, fun k ↦ Xi k.1, fun k ↦ f k.1, fun k ↦ V k.1, fun k ↦ q k.1,
    fun k ↦ ξ k.1, inferInstance, fun k ↦ hXi k.1, fun k ↦ hf k.1, fun k ↦ hsq k.1,
    fun k ↦ hq k.1, fun x ↦ ?_⟩
  obtain ⟨i, hi, hx⟩ := hcov x
  exact ⟨⟨i, hi⟩, hx⟩

/-- **A finite subfamily of the atlas whose base changes cover an affine point.** This is
`AlgebraicGeometry.FormalSpace.exists_finite_atlas_pullback_cover_of_compactSpace` for an object
of the big fppf category over `S` whose underlying scheme is affine, which is the form in which
the existence half of the proof of **Stacks 0AQD** needs it: there the base `T` is the source of
the single surjective flat quasi-compact morphism of affines to which
`AlgebraicGeometry.FormalSpace.isSheaf_fpqc_of_isSheafFor_singleton_affine_of_formal` reduces the
tag. The underlying space of an affine scheme is compact. -/
theorem exists_finite_atlas_pullback_cover_of_isAffine {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (c : uliftYoneda.{u + 1}.obj T ⟶ X.obj) :
    ∃ (K : Type (u + 1)) (Xi : K → FppfSheaf B S hS) (f : ∀ k, Xi k ⟶ X)
      (V : K → BigFppfOver B S hS) (q : ∀ k, V k ⟶ T)
      (ξ : ∀ k, uliftYoneda.{u + 1}.obj (V k) ⟶ (Xi k).obj),
      Finite K ∧
      (∀ k, IsAffineFormalAlgebraicSpace B S hS (Xi k)) ∧
      (∀ k, ∃ hfk : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f k).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f k).hom hfk) ∧
      (∀ k, IsPullback (ξ k) (uliftYoneda.{u + 1}.map (q k)) (f k).hom c) ∧
      (∀ k, Etale ((BigFppfOver.toScheme B S hS).map (q k))) ∧
      ∀ x : (BigFppfOver.toScheme B S hS).obj T,
        ∃ k, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q k)) :=
  let := hT
  let : CompactSpace ((BigFppfOver.toScheme B S hS).obj T) :=
    Scheme.compactSpace_of_isAffine _
  exists_finite_atlas_pullback_cover_of_compactSpace B S hS hX c

end AlgebraicGeometry.FormalSpace

end
