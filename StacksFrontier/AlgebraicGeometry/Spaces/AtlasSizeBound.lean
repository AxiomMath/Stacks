module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductAlgebraic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValued

/-!
# Algebraic spaces with a size bound on the atlas

`AlgebraicGeometry.IsAlgebraicSpace` asks for *some* surjective étale atlas by an object of the
site.  An induction which glues algebraic spaces out of families of algebraic spaces cannot use
that bare existence: the coproduct of the atlases has to lie in the site again, and whether it
does depends on how large the atlases are.  This file introduces the bookkeeping that carries a
bound through such an induction,
`AlgebraicGeometry.Space.IsAlgebraicSpaceAtlasSizeLE`, and proves the one closure property the
induction needs — that a coproduct of algebraic spaces whose atlases are bounded by `μ`, over an
index type of cardinality at most `μ`, is again an algebraic space with an atlas bounded by `μ`.

## Main definitions

* `AlgebraicGeometry.Space.IsAlgebraicSpaceAtlasSizeLE`: an fppf sheaf which is an algebraic
  space over `S` and admits a surjective étale atlas by an object of the site whose underlying
  scheme has size at most `μ`.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_size_le`: the disjoint union inside the
  site of a family of objects of uniformly bounded size, with both its universal property and
  its own size bound.  `AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_le` is the
  same statement without the bound.
* `AlgebraicGeometry.Space.IsAlgebraicSpaceAtlasSizeLE.mono` and
  `AlgebraicGeometry.Space.IsAlgebraicSpaceAtlasSizeLE.of_iso`: the bound is monotone in `μ` and
  invariant under isomorphism of presheaves.
* `AlgebraicGeometry.Space.isAlgebraicSpaceAtlasSizeLE_coproduct`: **Stacks 02WQ with the
  bound**.  A coproduct of algebraic spaces with atlases bounded by `μ`, over an index type of
  cardinality at most `μ`, is an algebraic space with an atlas bounded by `μ`.

## Implementation notes

The bound is on the *underlying scheme of the atlas object*, not on the atlas morphism, and it
is an inequality rather than membership of the site: `μ < B.cutoff` is carried separately, by
the one statement that needs it.  This is what makes the predicate composable — the bound of the
glued atlas is the bound of the members, with no cardinal arithmetic accumulating along the
induction.

`isAlgebraicSpaceAtlasSizeLE_coproduct` is `AlgebraicGeometry.isAlgebraicSpace_coproduct` with
the disjoint union of the atlases supplied instead of assumed, and with the atlas of the
coproduct read off the same disjoint union; that atlas is the one
`AlgebraicGeometry.isAlgebraicSpace_coproduct` itself constructs, so no second glueing is
performed.  `AlgebraicGeometry.isAlgebraicSpace_coproduct_of_size_le` proves the same algebraicity
statement from the same bounds, but discards the disjoint union and so cannot state the bound on
the resulting atlas.

## References

* [Stacks Project, Tag 02WQ](https://stacks.math.columbia.edu/tag/02WQ)
* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public section

open Cardinal CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The disjoint union inside the site of a size-bounded family, with its own size bound.**

`AlgebraicGeometry.BigFppfOver.exists_isColimit_cofan_of_size_le` produces the same object with
the same universal property but does not record how large it is, which is exactly what an
induction that glues again has to know.  The underlying scheme is the disjoint union of the
underlying schemes, so the bound is `AlgebraicGeometry.schemeSize_coproduct_le` at the same `μ`;
the universal property is inherited from the disjoint union of schemes because the inclusion of
the site into schemes is fully faithful and a morphism out of the disjoint union commutes with
the structure morphisms as soon as its restrictions do. -/
theorem BigFppfOver.exists_isColimit_cofan_size_le {K : Type u} (R : K → BigFppfOver B S hS)
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hK : #K ≤ μ)
    (hsize : ∀ k, ((BigFppfOver.toScheme B S hS).obj (R k)).size ≤ μ) :
    ∃ (Z : BigFppfOver B S hS) (c : ∀ k, R k ⟶ Z), Nonempty (IsColimit (Cofan.mk Z c)) ∧
      ((BigFppfOver.toScheme B S hS).obj Z).size ≤ μ := by
  classical
  have hle : (∐ fun k => (BigFppfOver.toScheme B S hS).obj (R k)).size ≤ μ :=
    schemeSize_coproduct_le _ μ hℵ hK hsize
  have hZsize : (∐ fun k => (BigFppfOver.toScheme B S hS).obj (R k)).size < B.cutoff :=
    hle.trans_lt hμ
  set Z : BigFppfOver B S hS := Over.mk (B.inclusion.preimage (X := B.obj hZsize)
    (Y := B.obj hS)
    (show B.inclusion.obj (B.obj hZsize) ⟶ B.inclusion.obj (B.obj hS) from
      Sigma.desc fun k => B.inclusion.map (R k).hom)) with hZdef
  have hZhom : B.inclusion.map Z.hom = Sigma.desc fun k => B.inclusion.map (R k).hom :=
    B.inclusion.map_preimage _
  have hc : ∀ k, ∃ ψ : R k ⟶ Z, (BigFppfOver.toScheme B S hS).map ψ =
      Sigma.ι (fun k => (BigFppfOver.toScheme B S hS).obj (R k)) k := by
    intro k
    refine BigFppfOver.exists_hom_of_comp_eq B S hS _ ?_
    rw [hZhom, Sigma.ι_comp_desc]
  choose c hcmap using hc
  have key : ∀ t : Cofan R, ∃! m : Z ⟶ t.pt, ∀ k, c k ≫ m = t.inj k := by
    intro t
    obtain ⟨m, hm⟩ : ∃ m : Z ⟶ t.pt, (BigFppfOver.toScheme B S hS).map m =
        Sigma.desc fun k => (BigFppfOver.toScheme B S hS).map (t.inj k) := by
      refine BigFppfOver.exists_hom_of_comp_eq B S hS _ ?_
      rw [hZhom]
      refine Sigma.hom_ext _ _ fun k => ?_
      rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
      exact (Functor.map_comp B.inclusion (t.inj k).left t.pt.hom).symm.trans
        (congrArg B.inclusion.map (Over.w (t.inj k)))
    refine ⟨m, fun k => (BigFppfOver.toScheme B S hS).map_injective ?_, fun m' hm' => ?_⟩
    · rw [Functor.map_comp, hcmap k, hm, Sigma.ι_comp_desc]
    · refine (BigFppfOver.toScheme B S hS).map_injective (Sigma.hom_ext _ _ fun k => ?_)
      rw [hm, Sigma.ι_comp_desc, ← hcmap k, ← Functor.map_comp, hm' k]
  exact ⟨Z, c, ⟨Cofan.IsColimit.mk _ (fun t => (key t).choose)
    (fun t k => (key t).choose_spec.1 k) fun t m hm => (key t).choose_spec.2 m hm⟩, hle⟩

namespace Space

/-- An fppf sheaf on the big fppf site of `S` is an **algebraic space with atlas of size at most
`μ`** when it is an algebraic space over `S` and admits a surjective étale atlas by an object of
the site whose underlying scheme has size at most `μ`.

This is the invariant carried through a glueing induction: the bound on the atlas of the glued
space is the bound on the atlases of the pieces. -/
def IsAlgebraicSpaceAtlasSizeLE (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (μ : Cardinal.{u}) :
    Prop :=
  IsAlgebraicSpace B S hS F ∧
    ∃ (W : BigFppfOver B S hS) (a : yoneda.obj W ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) a ∧
      ((BigFppfOver.toScheme B S hS).obj W).size ≤ μ

variable {B S hS}

/-- The bound on the atlas is monotone. -/
theorem IsAlgebraicSpaceAtlasSizeLE.mono {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {μ ν : Cardinal.{u}} (h : IsAlgebraicSpaceAtlasSizeLE B S hS F μ) (hμν : μ ≤ ν) :
    IsAlgebraicSpaceAtlasSizeLE B S hS F ν := by
  obtain ⟨halg, W, a, hsurj, het, hsize⟩ := h
  exact ⟨halg, W, a, hsurj, het, hsize.trans hμν⟩

/-- Being an algebraic space with an atlas of size at most `μ` is invariant under isomorphism of
presheaves: the atlas of the one is the atlas of the other composed with the isomorphism, whose
object — hence whose size — is unchanged. -/
theorem IsAlgebraicSpaceAtlasSizeLE.of_iso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ≅ G)
    {μ : Cardinal.{u}} (h : IsAlgebraicSpaceAtlasSizeLE B S hS G μ) :
    IsAlgebraicSpaceAtlasSizeLE B S hS F μ := by
  obtain ⟨halg, W, a, hsurj, het, hsize⟩ := h
  exact ⟨isAlgebraicSpace_of_iso B S hS e.symm halg, W, a ≫ e.inv,
    MorphismProperty.RespectsIso.postcomp _ e.inv a hsurj,
    MorphismProperty.RespectsIso.postcomp _ e.inv a het, hsize⟩

/-- **Stacks 02WQ with a bound on the atlas.** A coproduct of algebraic spaces over `S` whose
atlases are bounded in size by an infinite cardinal `μ` below the cutoff of the site, indexed by
a type of cardinality at most `μ`, is an algebraic space over `S` with an atlas bounded by `μ`.

The disjoint union of the atlases lies in the site by
`AlgebraicGeometry.BigFppfSite.contains_sigma_of_size_le` and is their coproduct in the site by
`AlgebraicGeometry.BigFppfOver.isColimit_cofan_sigmaOver`, so
`AlgebraicGeometry.isAlgebraicSpace_coproduct` applies; its atlas is that disjoint union, whose
size is bounded by `AlgebraicGeometry.schemeSize_coproduct_le`. -/
theorem isAlgebraicSpaceAtlasSizeLE_coproduct (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {I : Type u} (F : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    {μ : Cardinal.{u}} (hℵ : ℵ₀ ≤ μ) (hμ : μ < B.cutoff) (hI : #I ≤ μ)
    (hF : ∀ i, IsAlgebraicSpaceAtlasSizeLE B S hS (F i) μ)
    (G : Sheaf (BigFppfOver.topology B S hS) (Type u))
    (ι : ∀ i, (⟨F i, (hF i).1.isSheaf⟩ :
      Sheaf (BigFppfOver.topology B S hS) (Type u)) ⟶ G)
    (hG : IsColimit (Cofan.mk G ι)) :
    IsAlgebraicSpaceAtlasSizeLE B S hS G.obj μ := by
  classical
  have halg : ∀ i, IsAlgebraicSpace B S hS (F i) := fun i => (hF i).1
  choose W a hsurj het hsize using fun i => (hF i).2
  obtain ⟨V, j, ⟨hV⟩, hVsize⟩ :=
    BigFppfOver.exists_isColimit_cofan_size_le B S hS W hℵ hμ hI hsize
  obtain ⟨v, hfac⟩ := exists_hom_yoneda_of_isColimit_cofan ι a hV
  have halgG : IsAlgebraicSpace B S hS G.obj :=
    isAlgebraicSpace_coproduct B S hS F halg G ι hG W a hsurj het V j hV
  have key := fun {P₀ : MorphismProperty Scheme.{u}} =>
    presheaf_inverseImage_of_isColimit_cofan (P₀ := P₀) ι hG
      (fun i => (halg i).diagonal_representable) hV hfac
  exact ⟨halgG, V, v, key inferInstance hsurj,
    key (HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale) (Q := RingHom.Etale)) het,
    hVsize⟩

end Space

end AlgebraicGeometry

end
