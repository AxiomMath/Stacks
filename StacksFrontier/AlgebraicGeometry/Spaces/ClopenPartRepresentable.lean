module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineRelationRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleClopenPartUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent

/-!
# Representability of the open-and-closed piece of Stacks 082H

The finiteness clause of Stacks 082H needs the open-and-closed piece `V` of the decomposition
to be an affine scheme. `StacksFrontier/AlgebraicGeometry/Spaces/AffineRelationRepresentable.lean`
proves that an algebraic space which is the coequalizer of an affine equivalence relation with
finite locally free projections is representable by an affine object of the site, and this file
supplies the hypotheses of that statement which concern the atlas rather than the relation.

The piece `V` is the open subspace of the ambient space `P` cut out by the image of `|Z₁|`,
and the atlas is the factorisation `l : h_{Z₁} ⟶ V` of the étale morphism `z : h_{Z₁} ⟶ P`
through it. Two things have to be said about `l`: that it is étale, and that it is surjective,
both in the relatively representable sense. Étaleness is transported from `z` along the
monomorphism `V ⟶ P`, because the represented base changes of `l` are represented base changes
of `z`. Surjectivity is *not* transported — `z` is not surjective onto `P` — but `l` is
surjective on points, and for a morphism from a scheme to an algebraic space Tag 03H5 says
that point surjectivity is the relatively representable notion.

## Main definitions

No new definitions are introduced.

## Main results

* `CategoryTheory.MorphismProperty.relative_of_comp_mono`: the relative form of a morphism
  property passes from `f ≫ i` to `f` when `i` is a monomorphism.
* `AlgebraicGeometry.Space.isEtale_of_comp_mono`: a morphism of algebraic spaces whose
  composite with a monomorphism is étale is étale.
* `AlgebraicGeometry.Space.presheafEtale_of_isEtale_yoneda`: an étale morphism from a
  representable presheaf is étale in the relatively representable sense.
* `AlgebraicGeometry.Space.exists_kernelPair_of_relativelyRepresentable`: a relatively
  representable morphism from a representable presheaf has its kernel pair given by two
  morphisms of the site.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_isEtale_comp_mono_of_affine_kernelPair`: an
  algebraic space with a monomorphism into another presheaf, carrying a morphism from an affine
  object of the site which is étale into that presheaf and surjective on points, and whose
  kernel pair is affine with finite locally free projections, is representable by an affine
  object of the site.
* `AlgebraicGeometry.Space.exists_iso_yoneda_lift_openSubspaceOfPoints_range`: the same for the
  open subspace cut out by the image of the points of an étale morphism, which is the piece of
  Stacks 082H.

## Implementation notes

Cancelling a monomorphism out of a pullback square is the only categorical content, and it is
*not* proved here: it is the existing `CategoryTheory.IsPullback.of_comp_mono` of
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.PointsOfFibresFiniteDecent`, which takes the
commutativity of the inner square as a hypothesis. That hypothesis is free when the composing
morphism is a monomorphism — it is `(cancel_mono i).mp` applied to the outer square's own
commutativity — so it is discharged inline at the one call site in
`CategoryTheory.MorphismProperty.relative_of_comp_mono`. Mathlib's
`CategoryTheory.IsPullback.of_bot` would also give this, at the
cost of exhibiting the square `T ⟶ V ⟶ P` over `T` as a pullback, which is the same argument
written twice.

The transport of étaleness is stated for the space-level predicate
`AlgebraicGeometry.Space.IsEtale` of Tag 03FR, which quantifies over étale charts of the
source; the relatively representable form for a morphism *out of a representable* is then the
case of the identity chart, which needs
`CategoryTheory.MorphismProperty.presheaf_of_isIso`. At the toolchain of this development
`CategoryTheory.MorphismProperty.RespectsIso` is not found by instance search for
`AlgebraicGeometry.Etale`, so it is supplied explicitly from
`CategoryTheory.MorphismProperty.IsStableUnderBaseChange.respectsIso` with the property given
by name.

What remains of the finiteness clause of Stacks 082H after this file is the hypothesis `hker`:
that the kernel pair of the atlas is affine with finite locally free projections. In the source
that is the step "since `f` is separated, `V ⟶ U` is separated and `R` is closed in
`Z₁ ×_U Z₁`; since `Z₁ ⟶ U` is finite, the projections `s, t : R ⟶ Z₁` are finite" — together
with `AlgebraicGeometry.isFiniteLocallyFree_of_etale_of_isFinite` for the passage from finite
to finite locally free. It is not proved here. Neither is the existence of the étale
neighbourhood `(U, u) ⟶ (Y, y)` and of `z` itself, which is steps 1 to 5 of the source proof.
Nothing here carries the tag 082H.

## References

* [Stacks Project, Tag 0262](https://stacks.math.columbia.edu/tag/0262)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u


namespace CategoryTheory.MorphismProperty

/-- **The relative form of a morphism property passes through a monomorphism.** If `f ≫ i`
satisfies `P.relative F` and `i` is a monomorphism, then so does `f`: the representing object
of a base change of `f` along a morphism `g` from the image of an object is the representing
object of the base change of `f ≫ i` along `g ≫ i`, by
`CategoryTheory.IsPullback.of_comp_mono`. -/
theorem relative_of_comp_mono {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) [F.Full] [F.Faithful] (P : MorphismProperty C) [P.RespectsIso]
    {X Y Z : D} (f : X ⟶ Y) (i : Y ⟶ Z) [Mono i] (h : P.relative F (f ≫ i)) :
    P.relative F f :=
  MorphismProperty.relative.of_exists fun _ g =>
    ⟨h.rep.pullback (g ≫ i), h.rep.fst (g ≫ i), h.rep.snd (g ≫ i),
      IsPullback.of_comp_mono
        ((cancel_mono i).mp (by
          simpa only [Category.assoc] using (h.rep.isPullback (g ≫ i)).w))
        (h.rep.isPullback (g ≫ i)), h.property_snd (g ≫ i)⟩

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Étaleness through a monomorphism -/

/-- Pulling étaleness back along `BigFppfOver.toScheme` respects isomorphisms. -/
private theorem respectsIso_inverseImage_etale :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).RespectsIso :=
  haveI : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Etale.{u})
  MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)

/-- **A morphism of algebraic spaces whose composite with a monomorphism is étale is
étale.** For every étale chart `φ` of the source, `φ ≫ f ≫ i` is étale in the relatively
representable sense, and `CategoryTheory.MorphismProperty.relative_of_comp_mono` removes the
monomorphism. -/
theorem isEtale_of_comp_mono {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G) (i : G ⟶ H)
    [Mono i] (h : IsEtale B S hS (f ≫ i)) : IsEtale B S hS f := by
  have := respectsIso_inverseImage_etale B S hS
  intro U φ hφ
  refine MorphismProperty.relative_of_comp_mono yoneda _ (φ ≫ f) i ?_
  rw [Category.assoc]
  exact h U φ hφ

/-- **An étale morphism from a representable presheaf is étale in the relatively representable
sense.** This is the case of the identity chart in the definition of Tag 03FR. -/
theorem presheafEtale_of_isEtale_yoneda {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ G) (h : IsEtale B S hS f) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f := by
  have := respectsIso_inverseImage_etale B S hS
  have : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
    haveI : MorphismProperty.ContainsIdentities (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have h0 := h U (𝟙 (yoneda.obj U)) (MorphismProperty.presheaf_of_isIso _ (𝟙 (yoneda.obj U)))
  rwa [Category.id_comp] at h0

/-! ### The kernel pair of a relatively representable atlas -/

/-- **The kernel pair of a relatively representable morphism out of a representable presheaf
is given by two morphisms of the site.** The representing object of the base change of the
morphism along itself is the relation scheme, and its two projections are the two structural
morphisms of the representability datum, the first one read through the full faithfulness of
Yoneda. -/
theorem exists_kernelPair_of_relativelyRepresentable
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {U : BigFppfOver B S hS} (f : yoneda.obj U ⟶ G)
    (hrep : yoneda.relativelyRepresentable f) :
    ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
      IsPullback (yoneda.map s) (yoneda.map t) f f :=
  ⟨hrep.pullback f, yoneda.preimage (hrep.fst f), hrep.snd f, by
    rw [Functor.map_preimage]
    exact hrep.isPullback f⟩

/-! ### Representability of the piece -/

/-- **An algebraic space with an affine étale atlas and affine finite locally free kernel pair
is representable.** Let `V` be an algebraic space over `S` with a monomorphism `i` into a
presheaf `H`, and let `l : h_{Z₁} ⟶ V` be a morphism from an object of the site with affine
underlying scheme such that `l ≫ i` is étale and `l` is surjective on points. Suppose the
kernel pair of `l` is given by two morphisms `s, t : R ⟶ Z₁` of the site with `R` affine and
both projections finite locally free. Then `V` is representable by an object of the site with
affine underlying scheme, by an isomorphism carrying `l` to a morphism of the site.

Étaleness of `l` itself is `AlgebraicGeometry.Space.isEtale_of_comp_mono` followed by
`AlgebraicGeometry.Space.presheafEtale_of_isEtale_yoneda`; surjectivity in the relatively
representable sense is Tag 03H5
(`AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda`); and the conclusion is
`AlgebraicGeometry.Space.exists_iso_yoneda_of_kernelPair_of_affine_finiteLocallyFree`. -/
theorem exists_iso_yoneda_of_isEtale_comp_mono_of_affine_kernelPair
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {V H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    (i : V ⟶ H) [Mono i] {Z₁ : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z₁)]
    (l : yoneda.obj Z₁ ⟶ V) (hetale : IsEtale B S hS (l ≫ i))
    (hsurj : IsSurjective B S hS l)
    (hker : ∃ (R : BigFppfOver B S hS) (s t : R ⟶ Z₁),
      IsPullback (yoneda.map s) (yoneda.map t) l l ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj R) ∧
        Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s) ∧
        Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t)) :
    ∃ (V₀ : BigFppfOver B S hS) (π₀ : Z₁ ⟶ V₀) (e : V ≅ yoneda.obj V₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) ∧ l ≫ e.hom = yoneda.map π₀ := by
  obtain ⟨R, s, t, hR, hRaff, hsFLF, htFLF⟩ := hker
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj R) := hRaff
  have hpE := presheafEtale_of_isEtale_yoneda B S hS l (isEtale_of_comp_mono B S hS l i hetale)
  have hpS := (presheafSurjective_iff_isSurjective_yoneda B S hS V hV Z₁ l).mpr hsurj
  exact exists_iso_yoneda_of_kernelPair_of_affine_finiteLocallyFree B S hS s t hsFLF htFLF
    hV l hR hpS hpE

/-- **Representability of the open-and-closed piece of Stacks 082H.** Let `P` be an algebraic
space over `S`, let `z : h_{Z₁} ⟶ P` be étale with `Z₁` an object of the site with affine
underlying scheme, and suppose the image of `|Z₁|` in `|P|` is open. If the kernel pair of the
factorisation of `z` through the open subspace cut out by that image is given by two morphisms
of the site with affine relation scheme and finite locally free projections, then that open
subspace is representable by an object of the site with affine underlying scheme.

This is
`AlgebraicGeometry.Space.exists_iso_yoneda_of_isEtale_comp_mono_of_affine_kernelPair` with the
monomorphism the inclusion of the subspace, the étaleness hypothesis read off `z` through
`CategoryTheory.Subfunctor.lift_ι`, and the point surjectivity
`AlgebraicGeometry.Space.isSurjective_lift_openSubspaceOfPoints_range`. The subspace is an
algebraic space by `AlgebraicGeometry.Space.isOpenSubspace_openSubspaceOfPoints`. -/
theorem exists_iso_yoneda_lift_openSubspaceOfPoints_range
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {Z₁ : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj Z₁)]
    (z : yoneda.obj Z₁ ⟶ P) (hze : IsEtale B S hS z)
    (hopen : _root_.IsOpen (Set.range (pointsMap B S hS (yoneda.obj Z₁) z)))
    (hker : ∃ (R : BigFppfOver B S hS) (s t : R ⟶ Z₁),
      IsPullback (yoneda.map s) (yoneda.map t)
          (Subfunctor.lift z (range_le_openSubspaceOfPoints_range_pointsMap z))
          (Subfunctor.lift z (range_le_openSubspaceOfPoints_range_pointsMap z)) ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj R) ∧
        Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map s) ∧
        Stacks.Morphisms.IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map t)) :
    ∃ (V₀ : BigFppfOver B S hS) (π₀ : Z₁ ⟶ V₀)
      (e : (openSubspaceOfPoints B S hS P
        (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))).toFunctor ≅ yoneda.obj V₀),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V₀) ∧
        Subfunctor.lift z (range_le_openSubspaceOfPoints_range_pointsMap z) ≫ e.hom =
          yoneda.map π₀ := by
  have hVs : IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS P (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))) :=
    isOpenSubspace_openSubspaceOfPoints B S hS hP _ hopen
  refine exists_iso_yoneda_of_isEtale_comp_mono_of_affine_kernelPair B S hS hVs.1
    (openSubspaceOfPoints B S hS P
      (Set.range (pointsMap B S hS (yoneda.obj Z₁) z))).ι _ ?_
    (isSurjective_lift_openSubspaceOfPoints_range B S hS z) hker
  rw [Subfunctor.lift_ι]
  exact hze

end AlgebraicGeometry.Space

end
