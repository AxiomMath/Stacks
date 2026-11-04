module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.EtaleAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SectionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# An open copy of an étale neighbourhood inside a base change

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` and let `x` be a point of
`|X|` at which `f` is étale. The open subspace `U ⊆ X` on which `f` is étale is then an étale
neighbourhood of the image of `x` in `|Y|`, and the base change `U ×_Y X` contains a copy of
`U` itself: the graph of the inclusion `U ⟶ X`. That graph is an open immersion, so the copy is
an open subspace mapping *isomorphically* onto `U`, and it carries a point lying over `x` in
`|X|` and over the distinguished point in `|U|`.

When `f` is separated the graph is moreover a closed immersion, being a section of the
separated base change `U ×_Y X ⟶ U`, so the copy is open *and closed*.

## Main results

* `AlgebraicGeometry.Space.isOpenImmersion_pullbackLift_id_of_isEtale`: the graph of a morphism
  over the base is an open immersion as soon as the morphism is an open immersion and the
  structure morphism of its source is étale.
* `AlgebraicGeometry.Space.exists_etale_neighbourhood_isIso_openSubspace_of_isEtaleAt`: the
  étale neighbourhood together with the open subspace of the base change mapping isomorphically
  onto it.
* `AlgebraicGeometry.Space.exists_etale_neighbourhood_isIso_clopenSubspace_of_isEtaleAt`: the
  same with the copy open and closed, for a separated `f`.

## Implementation notes

`AlgebraicGeometry.Space.IsEtaleAt` is by definition the existence of an open subspace of the
source containing the point on which the morphism is étale, so the étale neighbourhood is read
off the hypothesis with no further work; its structure morphism is the composite of the
inclusion with `f`, which the hypothesis asserts to be étale.

The graph of `a : U ⟶ X` over `Y` is `CategoryTheory.Limits.pullback.lift (𝟙 U) a`. Openness of
the graph is *not* proved from the relative diagonal of `f`, which would need `f` unramified
everywhere, but from the relative diagonal of the étale `g : U ⟶ Y`, in the form
`AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_section`: the graph factors through the
base change `(U ×_Y X) ×_X U`, of which it is a *section* over `U`, and that base change is
étale over `U` because the second projection `U ×_Y X ⟶ X` is a base change of `g`. The
remaining factor `(U ×_Y X) ×_X U ⟶ U ×_Y X` is a base change of `a`, hence an open immersion.
That the hypothesis on `a` is openness rather than étaleness is what makes the composite an
open immersion rather than merely an étale morphism; no cancellation property of étaleness is
used.

The copy itself is `CategoryTheory.Subfunctor.range` of the graph. The graph is a monomorphism,
being a section, so `CategoryTheory.Subfunctor.toRange` of it is an isomorphism, and the
composite of the inclusion of the range with the first projection is its inverse — which is
what the `IsIso` clause says. Being an open subspace is
`AlgebraicGeometry.Space.isOpenSubspace_subfunctorRange` and being a closed subspace is
`AlgebraicGeometry.Space.isClosedSubspace_range_of_isClosedImmersion`.

The conclusion is the shape of [Stacks, Tag 0ADU]
(`AlgebraicGeometry.Space.exists_etale_decomposition_isFinite_point_of_isQuasiFiniteAt`) with
the finiteness of the distinguished piece strengthened to invertibility. It is *not* the
algebraic-space form of [Stacks, Tag 04HL]: that tag asks, for each of finitely many points of
one fibre, for a whole finite family of copies exhausting the points of the fibre above it, and
produces them by splitting the unramified part completely, which is [Stacks, Tag 04HH]. Only
the distinguished copy — the one containing the prescribed point — is obtained here, and
nothing in this file carries a Stacks tag. The scheme case of 04HL is
`AlgebraicGeometry.exists_etaleNeighborhood_openCopies_cover_fibers`.

## References

* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
* [Stacks Project, Tag 04HH](https://stacks.math.columbia.edu/tag/04HH)
* [Stacks Project, Tag 04HL](https://stacks.math.columbia.edu/tag/04HL)
* [Stacks Project, Tag 04RH](https://stacks.math.columbia.edu/tag/04RH)
* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Graph

variable {X Y U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {g : U ⟶ Y} {a : U ⟶ X}

/-- **The graph of an open immersion over an étale base is an open immersion.**

Let `f : X ⟶ Y` and `g : U ⟶ Y` be morphisms of algebraic spaces over `S` with `g` étale, and
let `a : U ⟶ X` satisfy `a ≫ f = g`. If `a` is an open immersion then so is the graph
`(𝟙 U, a) : U ⟶ U ×_Y X`.

The graph is a section of the base change `(U ×_Y X) ×_X U ⟶ U` of the second projection
`U ×_Y X ⟶ X`, which is étale because it is a base change of `g`; a section of an étale
morphism is an open immersion. Composing with the base change `(U ×_Y X) ×_X U ⟶ U ×_Y X` of
`a` gives the graph. -/
theorem isOpenImmersion_pullbackLift_id_of_isEtale
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hU : IsAlgebraicSpace B S hS U) (hcomm : 𝟙 U ≫ g = a ≫ f)
    (hg : IsEtale B S hS g) (ha : IsOpenImmersion B S hS a) :
    IsOpenImmersion B S hS (pullback.lift (𝟙 U) a hcomm) := by
  have hP : IsAlgebraicSpace B S hS (pullback g f) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS g f hU hX hY
  have hsnd : IsEtale B S hS (pullback.snd g f) :=
    isEtale_pullback_snd B S hS hX hY hU g f hg
  have hQ : IsAlgebraicSpace B S hS (pullback (pullback.snd g f) a) :=
    _root_.AlgebraicGeometry.isAlgebraicSpace_pullback B S hS (pullback.snd g f) a hP hU hX
  have hQsnd : IsEtale B S hS (pullback.snd (pullback.snd g f) a) :=
    isEtale_pullback_snd B S hS hU hX hP (pullback.snd g f) a hsnd
  have hfst : IsOpenImmersion B S hS (pullback.fst (pullback.snd g f) a) :=
    have _ : (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
      MorphismProperty.relative_isStableUnderBaseChange _
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback (pullback.snd g f) a).flip ha
  have hside : pullback.lift (𝟙 U) a hcomm ≫ pullback.snd g f = 𝟙 U ≫ a := by
    rw [Category.id_comp]
    exact pullback.lift_snd _ _ _
  have hsection : pullback.lift (pullback.lift (𝟙 U) a hcomm) (𝟙 U) hside ≫
      pullback.snd (pullback.snd g f) a = 𝟙 U := pullback.lift_snd _ _ _
  have hΓ : IsOpenImmersion B S hS
      (pullback.lift (pullback.lift (𝟙 U) a hcomm) (𝟙 U) hside) :=
    isOpenImmersion_of_isEtale_of_section B S hS hQ hU
      (pullback.snd (pullback.snd g f) a) hQsnd
      (pullback.lift (pullback.lift (𝟙 U) a hcomm) (𝟙 U) hside) hsection
  have hlift : pullback.lift (𝟙 U) a hcomm =
      pullback.lift (pullback.lift (𝟙 U) a hcomm) (𝟙 U) hside ≫
        pullback.fst (pullback.snd g f) a := (pullback.lift_fst _ _ _).symm
  rw [hlift]
  exact isOpenImmersion_comp B S hS _ _ hΓ hfst

/-- The inclusion of the range of the graph of `a : U ⟶ X`, followed by the first projection of
`U ×_Y X`, is an isomorphism: it is the inverse of `CategoryTheory.Subfunctor.toRange` of the
graph, which is invertible because the graph is a monomorphism. -/
theorem isIso_range_ι_comp_pullbackFst_pullbackLift_id (hcomm : 𝟙 U ≫ g = a ≫ f) :
    IsIso ((Subfunctor.range (pullback.lift (𝟙 U) a hcomm)).ι ≫ pullback.fst g f) := by
  have hfst : pullback.lift (𝟙 U) a hcomm ≫ pullback.fst g f = 𝟙 U := pullback.lift_fst _ _ _
  have hmono : Mono (pullback.lift (𝟙 U) a hcomm) := mono_of_mono_fac hfst
  have hinv : inv (Subfunctor.toRange (pullback.lift (𝟙 U) a hcomm)) =
      (Subfunctor.range (pullback.lift (𝟙 U) a hcomm)).ι ≫ pullback.fst g f :=
    IsIso.inv_eq_of_hom_inv_id (by rw [← Category.assoc, Subfunctor.toRange_ι]; exact hfst)
  rw [← hinv]
  infer_instance

/-- The range of the graph of `a : U ⟶ X` carries a point over any prescribed point of `|U|`
and over its image in `|X|`: the image of that point under
`CategoryTheory.Subfunctor.toRange` of the graph. -/
theorem exists_point_range_pullbackLift_id (hcomm : 𝟙 U ≫ g = a ≫ f)
    (u : points B S hS U) (x : points B S hS X) (hx : pointsMap B S hS U a u = x) :
    ∃ v : points B S hS (Subfunctor.range (pullback.lift (𝟙 U) a hcomm)).toFunctor,
      pointsMap B S hS (Subfunctor.range (pullback.lift (𝟙 U) a hcomm)).toFunctor
          ((Subfunctor.range (pullback.lift (𝟙 U) a hcomm)).ι ≫ pullback.fst g f) v = u ∧
        pointsMap B S hS (Subfunctor.range (pullback.lift (𝟙 U) a hcomm)).toFunctor
          ((Subfunctor.range (pullback.lift (𝟙 U) a hcomm)).ι ≫ pullback.snd g f) v = x := by
  refine ⟨pointsMap B S hS U (Subfunctor.toRange (pullback.lift (𝟙 U) a hcomm)) u, ?_, ?_⟩
  · rw [← pointsMap_comp_apply, ← Category.assoc, Subfunctor.toRange_ι, pullback.lift_fst,
      pointsMap_id, id_eq]
  · rw [← pointsMap_comp_apply, ← Category.assoc, Subfunctor.toRange_ι, pullback.lift_snd, hx]

end Graph

/-- The graph of the inclusion of the étale locus of `f` at `x`, with the open copy it spans. -/
private theorem exists_etale_neighbourhood_graph
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) (hf : IsEtaleAt B S hS f x) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U) (g : U ⟶ Y)
      (u : points B S hS U) (Γ : U ⟶ pullback g f),
      Γ ≫ pullback.fst g f = 𝟙 U ∧ IsEtale B S hS g ∧
      pointsMap B S hS U g u = pointsMap B S hS X f x ∧
      IsOpenSubspace B S hS (Subfunctor.range Γ) ∧
      IsIso ((Subfunctor.range Γ).ι ≫ pullback.fst g f) ∧
      ∃ v : points B S hS (Subfunctor.range Γ).toFunctor,
        pointsMap B S hS _ ((Subfunctor.range Γ).ι ≫ pullback.fst g f) v = u ∧
        pointsMap B S hS _ ((Subfunctor.range Γ).ι ≫ pullback.snd g f) v = x := by
  obtain ⟨U₀, hU₀, x₀, hx₀, hetale⟩ := hf
  have hcomm : 𝟙 U₀.toFunctor ≫ (U₀.ι ≫ f) = U₀.ι ≫ f := Category.id_comp _
  exact ⟨U₀.toFunctor, hU₀.1, U₀.ι ≫ f, x₀, pullback.lift (𝟙 U₀.toFunctor) U₀.ι hcomm,
    pullback.lift_fst _ _ _, hetale, by rw [pointsMap_comp_apply, hx₀],
    isOpenSubspace_subfunctorRange B S hS hU₀.1
      (isOpenImmersion_pullbackLift_id_of_isEtale B S hS hX hY hU₀.1 hcomm hetale hU₀.2),
    isIso_range_ι_comp_pullbackFst_pullbackLift_id B S hS hcomm,
    exists_point_range_pullbackLift_id B S hS hcomm x₀ x hx₀⟩

/-- **An étale neighbourhood over which the base change has an open copy of itself.**

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` which is étale at a point `x` of
`|X|`. Then there are an algebraic space `U` over `S`, an **étale** morphism `g : U ⟶ Y` and a
point `u` of `|U|` over the image of `x`, together with an **open** subspace `V` of `U ×_Y X`
such that `V ⟶ U` is an **isomorphism** and some point of `|V|` lies over `x` in `|X|` and over
`u` in `|U|`.

The neighbourhood is the open subspace of `X` on which `f` is étale and the copy is the range
of the graph of its inclusion. See the module documentation for why this is not the
algebraic-space form of [Stacks, Tag 04HL]. -/
theorem exists_etale_neighbourhood_isIso_openSubspace_of_isEtaleAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) (hf : IsEtaleAt B S hS f x) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U) (g : U ⟶ Y)
      (u : points B S hS U) (V : Subfunctor (pullback g f)),
      IsEtale B S hS g ∧
      pointsMap B S hS U g u = pointsMap B S hS X f x ∧
      IsOpenSubspace B S hS V ∧
      IsIso (V.ι ≫ pullback.fst g f) ∧
      ∃ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst g f) v = u ∧
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.snd g f) v = x := by
  obtain ⟨U, hU, g, u, Γ, -, hg, hu, hV, hiso, hv⟩ :=
    exists_etale_neighbourhood_graph B S hS hX hY f x hf
  exact ⟨U, hU, g, u, _, hg, hu, hV, hiso, hv⟩

/-- **An étale neighbourhood over which the base change has an open and closed copy of
itself.**

Let `f : X ⟶ Y` be a **separated** morphism of algebraic spaces over `S` which is étale at a
point `x` of `|X|`. Then there are an algebraic space `U` over `S`, an **étale** morphism
`g : U ⟶ Y` and a point `u` of `|U|` over the image of `x`, together with an **open and
closed** subspace `V` of `U ×_Y X` such that `V ⟶ U` is an **isomorphism** and some point of
`|V|` lies over `x` in `|X|` and over `u` in `|U|`.

This is the conclusion of [Stacks, Tag 0ADU] with the finiteness of the distinguished piece
strengthened to invertibility, at the price of étaleness at the point in place of
quasi-finiteness. The copy is closed because it is the range of a section of the separated base
change `U ×_Y X ⟶ U`, by part (5) of [Stacks, Tag 03KP]. -/
theorem exists_etale_neighbourhood_isIso_clopenSubspace_of_isEtaleAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) (x : points B S hS X) (hsep : IsSeparated B S hS f)
    (hf : IsEtaleAt B S hS f x) :
    ∃ (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS U) (g : U ⟶ Y)
      (u : points B S hS U) (V : Subfunctor (pullback g f)),
      IsEtale B S hS g ∧
      pointsMap B S hS U g u = pointsMap B S hS X f x ∧
      IsOpenSubspace B S hS V ∧
      IsClosedSubspace B S hS V ∧
      IsIso (V.ι ≫ pullback.fst g f) ∧
      ∃ v : points B S hS V.toFunctor,
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.fst g f) v = u ∧
        pointsMap B S hS V.toFunctor (V.ι ≫ pullback.snd g f) v = x := by
  obtain ⟨U, hU, g, u, Γ, hfst, hg, hu, hV, hiso, hv⟩ :=
    exists_etale_neighbourhood_graph B S hS hX hY f x hf
  exact ⟨U, hU, g, u, _, hg, hu, hV,
    isClosedSubspace_range_of_isClosedImmersion B S hS _ hU
      (isClosedImmersion_of_isSeparated_of_section B S hS (pullback.fst g f)
        (isSeparated_pullbackFst B S hS g hsep) Γ hfst),
    hiso, hv⟩

end AlgebraicGeometry.Space

end
