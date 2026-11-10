module

public import Mathlib.CategoryTheory.Extensive
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFiniteReduction

/-!
# Restricting the Tag 02LN decomposition along a further base change

`StacksFrontier/AlgebraicGeometry/Spaces/EtaleSplitQuasiFiniteReduction.lean` carries out the first
three paragraphs of the proof of Stacks 082H as far as the scheme level: it produces an affine
object `Z` of the site étale over the base change, the morphism `τ : Z ⟶ Y₀` of the site, an
elementary étale neighbourhood `U` of the distinguished point of the affine base, and the
open-and-closed decomposition of `Z ×_{Y₀} U` indexed by `Option (Fin m)` that More on Morphisms
02LN supplies, the piece attached to `some i` being finite over `U`. It also produces, separately,
an affine *object of the site* sitting inside that neighbourhood by an open immersion `κ`.

The two are not yet matched up: the decomposition lives over `U`, which is a bare scheme, while
`AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite` needs its data over
an object of the site. This file performs the matching, which is the restriction of the
decomposition along `κ`, and then the assembly of the finitely many pieces attached to `some`
into a single object of the site finite over the base.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.exists_comparison_of_comp_eq` produces the comparison morphism
  `X ×_Z V ⟶ X ×_Z U` induced by a morphism `κ : V ⟶ U` over `Z`, with its two factorisations.
* `AlgebraicGeometry.isPullback_pullback_snd_of_comparison` identifies that comparison morphism as
  a base change: the square with the two second projections on its sides and `κ` along its bottom
  is cartesian. This is what makes every property stable under base change descend from the
  decomposition to its restriction.
* `AlgebraicGeometry.exists_restricted_decomposition_of_isIso_sigmaDesc` is the restriction itself:
  a finite family of open-and-closed immersions into `X ×_Z U` whose induced morphism from the
  coproduct is an isomorphism restricts, along any `κ : V ⟶ U` over `Z`, to a finite family of
  open-and-closed immersions into `X ×_Z V` with the same property, each member being a base
  change of the corresponding member over `U`.
* `AlgebraicGeometry.isOpenImmersion_sigmaDesc_some_of_isIso_sigmaDesc` states that the morphism
  induced by the part of such a family indexed by `some` is an open immersion.
* `AlgebraicGeometry.exists_apply_eq_of_isIso_sigmaDesc` says that a family inducing an
  isomorphism out of the coproduct is jointly surjective on points, which is what lets the two
  fibre clauses of Tag 02LN discriminate the piece a given point lies in.
* `AlgebraicGeometry.Space.exists_siteObject_isFinite_of_pullback_decomposition` merges the
  restricted pieces: if each piece attached to `some i` is finite over the base, then there is an
  object `Z₁` of the big fppf site, a morphism `ζ : Z₁ ⟶ Zu` of the site whose underlying morphism
  of schemes is finite, and an open immersion `θ` from the underlying scheme of `Z₁` to
  `Z ×_{Y₀} Zu` compatible with `ζ`. Its last clause says moreover that, given the two fibre
  clauses of Tag 02LN over a point of the neighbourhood hit by a point `u'` of `Zu`, the fibre of
  `ζ` over `u'` is the part of the fibre of the second projection lying over the prescribed
  points.
* `AlgebraicGeometry.Space.exists_siteObject_isFinite_part_of_isQuasiFiniteAt` chains that onto the
  scheme-level results of
  `StacksFrontier/AlgebraicGeometry/Spaces/EtaleSplitQuasiFiniteReduction.lean`, delivering the
  whole of the first three paragraphs of the proof of Stacks 082H over an object of the site rather
  than over a bare scheme, together with the distinguished point and the two conditions on its
  fibre. This is the result the remaining presheaf-level step consumes.

## Implementation notes

The target of the restricted decomposition is `X ×_Z w` for a morphism `w` carrying an *equation*
`κ ≫ g = w`, rather than the composite `κ ≫ g` itself. This is forced by the shape of
`AlgebraicGeometry.Space.exists_affine_siteObject_of_etaleNeighborhood`, which produces the
identity `κ ≫ U.toBase = (BigFppfOver.toScheme B S hS).map ν` as a proposition and not as a
definitional unfolding; every statement here therefore takes `w` and `hw` and reduces to the
composite case by `subst`.

Three clauses of the restricted decomposition are *not* proved by a lemma of this file, because
instance search already supplies them: `AlgebraicGeometry.IsOpenImmersion`,
`AlgebraicGeometry.IsClosedImmersion` and `AlgebraicGeometry.IsFinite` of a first projection are
all obtained by `inferInstance` from Mathlib's base-change instances once the corresponding
property of the second argument is in scope. Only the isomorphism clause needs a named input, and
that input is Mathlib's `CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_fst` applied at
`AlgebraicGeometry.Scheme`, which is finitary extensive; pullbacks in schemes therefore distribute
over the finite coproduct and the restricted family still exhausts the restricted total space.

Mathlib's `CategoryTheory.Limits.pullbackLeftPullbackSndIso` is the isomorphism underlying
`AlgebraicGeometry.isPullback_pullback_snd_of_comparison`; the cartesian square is stated and
proved directly from `CategoryTheory.IsPullback.of_right` instead, since what the consumers need
is the square and not the isomorphism.

The merge is `AlgebraicGeometry.isFinite_sigmaDesc`, Stacks 0CYI, which is already available for
an arbitrary finite index type, so no hypothesis of affineness on the individual pieces is used —
the source's remark that the pieces may be taken affine is not needed. Placing the coproduct in
the site uses `AlgebraicGeometry.Space.contains_of_locallyOfFiniteType_of_quasiCompact`, whose two
hypotheses both follow from finiteness of the merged morphism by instance search.

The two conditions on the fibre over the distinguished point are carried along the restriction by
a point-level case split over the index type `Option (Fin m)` of the decomposition: the piece a
point lies in is found by `AlgebraicGeometry.exists_apply_eq_of_isIso_sigmaDesc`, the clause of
Tag 02LN attached to `some` pins its image under the first projection, and the clause attached to
`none` excludes that case when the image is one of the prescribed points. The converse inclusion
needs a point of a restricted piece built from the pair of its projections, which is Mathlib's
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` — the scheme-level analogue of Tag
03H4, whose presheaf-level form is `AlgebraicGeometry.Space.exists_points_of_isPullback`.

What remains between this file and
`AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite` is the presheaf-level
assembly: the étale morphism `yoneda.obj Z₁ ⟶ pullback g f` built from `θ`, and the conversion of
the two conditions on the fibre from schemes to presheaves. Nothing here carries the tag 082H,
and nothing here is the tag.

## References

* [Stacks Project, Tag 02LN](https://stacks.math.columbia.edu/tag/02LN)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 0CYI](https://stacks.math.columbia.edu/tag/0CYI)
* [Stacks Project, Tag 082H](https://stacks.math.columbia.edu/tag/082H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The comparison morphism of a further base change -/

/-- **The comparison morphism induced by a morphism of the second factor.** Let `f : X ⟶ Z` and
`g : U ⟶ Z` be morphisms of schemes and let `κ : V ⟶ U` satisfy `κ ≫ g = w`. Then there is a
morphism `X ×_Z V ⟶ X ×_Z U` whose composite with the first projection is the first projection
and whose composite with the second projection is the second projection followed by `κ`. -/
theorem exists_comparison_of_comp_eq {X Z Us Vs : Scheme.{u}} (f : X ⟶ Z) (g : Us ⟶ Z)
    (κ : Vs ⟶ Us) {w : Vs ⟶ Z} (hw : κ ≫ g = w) :
    ∃ ρ : pullback f w ⟶ pullback f g,
      ρ ≫ pullback.fst f g = pullback.fst f w ∧
      ρ ≫ pullback.snd f g = pullback.snd f w ≫ κ := by
  subst hw
  exact ⟨pullback.lift (pullback.fst f (κ ≫ g)) (pullback.snd f (κ ≫ g) ≫ κ)
    (by rw [pullback.condition, Category.assoc]), pullback.lift_fst .., pullback.lift_snd ..⟩

/-- **The comparison morphism is a base change along `κ`.** In the situation of
`AlgebraicGeometry.exists_comparison_of_comp_eq`, the square whose top is the comparison morphism,
whose sides are the two second projections and whose bottom is `κ` is cartesian. Consequently
every property of morphisms of schemes stable under base change passes from the second projection
of `X ×_Z U` to that of `X ×_Z V`.

Mathlib's `CategoryTheory.Limits.pullbackLeftPullbackSndIso` is the same fact in the form of an
isomorphism `(X ×_Z U) ×_U V ≅ X ×_Z V`; the cartesian square is obtained here directly from
`CategoryTheory.IsPullback.of_right`, pasting the square of `X ×_Z U` onto the right of the square
of `X ×_Z V`. -/
theorem isPullback_pullback_snd_of_comparison {X Z Us Vs : Scheme.{u}} (f : X ⟶ Z) (g : Us ⟶ Z)
    (κ : Vs ⟶ Us) {w : Vs ⟶ Z} (hw : κ ≫ g = w) (ρ : pullback f w ⟶ pullback f g)
    (h₁ : ρ ≫ pullback.fst f g = pullback.fst f w)
    (h₂ : ρ ≫ pullback.snd f g = pullback.snd f w ≫ κ) :
    IsPullback ρ (pullback.snd f w) (pullback.snd f g) κ := by
  subst hw
  refine IsPullback.of_right ?_ h₂ (IsPullback.of_hasPullback f g)
  rw [h₁]
  exact IsPullback.of_hasPullback f (κ ≫ g)

/-! ### The restricted decomposition -/

/-- **A finite open-and-closed decomposition of `X ×_Z U` restricts along `κ : V ⟶ U`.** Let
`f : X ⟶ Z` and `g : U ⟶ Z` be morphisms of schemes, let `κ : V ⟶ U` satisfy `κ ≫ g = w`, and let
`ι a : Q a ⟶ X ×_Z U`, indexed by a finite type, be open immersions which are also closed
immersions and for which the induced morphism out of the coproduct is an isomorphism. Then there
is a family `ι' a : Q' a ⟶ X ×_Z V` with the same three properties, together with morphisms
`j a : Q' a ⟶ Q a` exhibiting each `ι' a` composed with the second projection as the base change
of `ι a` composed with the second projection along `κ`, and compatibly with the first projections.

This is the restriction of the decomposition of Tag 02LN performed in the proof of Stacks 082H
when the étale neighbourhood is shrunk to an affine open. The restricted pieces are the pullbacks
of the pieces along the comparison morphism of
`AlgebraicGeometry.exists_comparison_of_comp_eq`; the two immersion clauses are Mathlib's
base-change instances, the cartesian clause is
`AlgebraicGeometry.isPullback_pullback_snd_of_comparison` pasted onto the defining square of the
pullback, and the isomorphism clause is
`CategoryTheory.FinitaryPreExtensive.isIso_sigmaDesc_fst`, which applies because
`AlgebraicGeometry.Scheme` is finitary extensive. -/
theorem exists_restricted_decomposition_of_isIso_sigmaDesc {X Z Us Vs : Scheme.{u}} (f : X ⟶ Z)
    (g : Us ⟶ Z) (κ : Vs ⟶ Us) {w : Vs ⟶ Z} (hw : κ ≫ g = w)
    {α : Type} [Finite α] {Q : α → Scheme.{u}} (ι : ∀ a, Q a ⟶ pullback f g)
    (hιo : ∀ a, IsOpenImmersion (ι a)) (hιc : ∀ a, IsClosedImmersion (ι a))
    (hιiso : IsIso (Sigma.desc ι)) :
    ∃ (Q' : α → Scheme.{u}) (ι' : ∀ a, Q' a ⟶ pullback f w) (j : ∀ a, Q' a ⟶ Q a),
      (∀ a, IsOpenImmersion (ι' a)) ∧
      (∀ a, IsClosedImmersion (ι' a)) ∧
      IsIso (Sigma.desc ι') ∧
      (∀ a, IsPullback (j a) (ι' a ≫ pullback.snd f w) (ι a ≫ pullback.snd f g) κ) ∧
      (∀ a, ι' a ≫ pullback.fst f w = j a ≫ ι a ≫ pullback.fst f g) := by
  obtain ⟨ρ, h₁, h₂⟩ := exists_comparison_of_comp_eq f g κ hw
  have hιo' := hιo
  have hιc' := hιc
  refine ⟨fun a ↦ pullback ρ (ι a), fun a ↦ pullback.fst ρ (ι a), fun a ↦ pullback.snd ρ (ι a),
    fun a ↦ inferInstance, fun a ↦ inferInstance,
    FinitaryPreExtensive.isIso_sigmaDesc_fst ι ρ hιiso,
    fun a ↦ ((IsPullback.of_hasPullback ρ (ι a)).flip).paste_vert
      (isPullback_pullback_snd_of_comparison f g κ hw ρ h₁ h₂), fun a ↦ ?_⟩
  rw [← h₁, ← Category.assoc, pullback.condition, Category.assoc]

/-- **The `some`-part of a finite open-and-closed decomposition is an open immersion.** If a family
`ι : ∀ a : Option α, Q a ⟶ T` indexed by `Option α` for a finite `α` induces an isomorphism out of
the coproduct, then the morphism induced by the subfamily indexed by `some` is an open immersion.

This is what makes the merged object of
`AlgebraicGeometry.Space.exists_siteObject_isFinite_of_pullback_decomposition` étale over the total
space, which is what the presheaf-level assembly of Stacks 082H needs of it. The morphism factors
as the inclusion of the subcoproduct followed by the isomorphism, and the inclusion of the
subcoproduct is an open immersion by `AlgebraicGeometry.isOpenImmersion_sigmaDesc`: the ranges of
distinct coproduct inclusions of schemes are disjoint
(`AlgebraicGeometry.disjoint_opensRange_sigmaι`), and `some` is injective. No disjointness
hypothesis on the `ι a` themselves is used. -/
theorem isOpenImmersion_sigmaDesc_some_of_isIso_sigmaDesc {α : Type} [Finite α] {T : Scheme.{u}}
    {Q : Option α → Scheme.{u}} (ι : ∀ a, Q a ⟶ T) (hiso : IsIso (Sigma.desc ι)) :
    IsOpenImmersion (Sigma.desc fun i : α ↦ ι (some i)) := by
  have hsub : IsOpenImmersion (Sigma.desc fun i : α ↦ Sigma.ι Q (some i)) :=
    isOpenImmersion_sigmaDesc (fun i : α ↦ Q (some i))
      (fun i : α ↦ Sigma.ι Q (some i)) fun i j hij ↦ by
        simpa [Function.onFun_apply, disjoint_iff, TopologicalSpace.Opens.ext_iff] using
          disjoint_opensRange_sigmaι Q (some i) (some j) (by simpa using hij)
  have hfac : ((Sigma.desc fun i : α ↦ Sigma.ι Q (some i)) ≫ Sigma.desc ι) =
      Sigma.desc fun i : α ↦ ι (some i) :=
    Sigma.hom_ext _ _ fun i ↦ by rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
  rw [← hfac]
  infer_instance

/-- **Every point of the target of an exhausting family is in the image of one of its members.**
If the morphism induced by a family `ι : ∀ a, Q a ⟶ T` out of the coproduct is an isomorphism,
then every point of `T` is the image of a point of some `Q a`.

This is what makes the decomposition of Tag 02LN usable on points: a point of `Z ×_{Y₀} U` over
the distinguished point of `U` lies in exactly one piece, and which piece it lies in is what the
two fibre clauses of Tag 02LN discriminate. The point of the coproduct is produced by
`AlgebraicGeometry.sigmaOpenCover`, whose members are the coproduct inclusions, and transported
through the inverse of the induced morphism. -/
theorem exists_apply_eq_of_isIso_sigmaDesc {α : Type} [Small.{u} α] {T : Scheme.{u}}
    {Q : α → Scheme.{u}} (ι : ∀ a, Q a ⟶ T) (hiso : IsIso (Sigma.desc ι)) (x : T) :
    ∃ (a : α) (q : Q a), ι a q = x := by
  obtain ⟨a, q, hq⟩ : ∃ (a : α) (q : Q a),
      Sigma.ι Q a q = (asIso (Sigma.desc ι)).inv x := (sigmaOpenCover Q).exists_eq _
  refine ⟨a, q, ?_⟩
  rw [← Scheme.inv_hom_apply (asIso (Sigma.desc ι)) x, ← hq, ← Scheme.Hom.comp_apply,
    asIso_hom, Sigma.ι_comp_desc]

/-- **A point of the restricted `some`-part over `u'` lies over one of the prescribed points.**
Let `ρ : X ×_Z V ⟶ X ×_Z U` be the comparison morphism of
`AlgebraicGeometry.exists_comparison_of_comp_eq`, let `κ u' = pt`, and suppose every point of
`Q a` lying over `pt` lies over `z a`. Then every point of the coproduct of the restricted pieces
whose image lies over `u'` has image lying over one of the `z a`. -/
theorem exists_fst_eq_of_snd_eq_of_comparison {X Z Us Vs : Scheme.{u}} {f : X ⟶ Z}
    {g : Us ⟶ Z} {κ : Vs ⟶ Us} {w : Vs ⟶ Z} {ρ : pullback f w ⟶ pullback f g}
    (h₁ : ρ ≫ pullback.fst f g = pullback.fst f w)
    (h₂ : ρ ≫ pullback.snd f g = pullback.snd f w ≫ κ)
    {α : Type} [Finite α] {Q : α → Scheme.{u}} (ι : ∀ a, Q a ⟶ pullback f g) {pt : Us}
    {u' : Vs} (hu' : κ u' = pt) {z : α → X}
    (hz : ∀ a q, (ι a ≫ pullback.snd f g) q = pt → (ι a ≫ pullback.fst f g) q = z a)
    (y : (∐ fun a ↦ pullback ρ (ι a) : Scheme.{u}))
    (hy : pullback.snd f w ((Sigma.desc fun a ↦ pullback.fst ρ (ι a)) y) = u') :
    ∃ a, pullback.fst f w ((Sigma.desc fun a ↦ pullback.fst ρ (ι a)) y) = z a := by
  obtain ⟨a, q, rfl⟩ : ∃ (a : α) (q : ↥(pullback ρ (ι a))),
    Sigma.ι (fun a ↦ pullback ρ (ι a)) a q = y := (sigmaOpenCover _).exists_eq y
  have hω : (Sigma.desc fun a ↦ pullback.fst ρ (ι a)) (Sigma.ι (fun a ↦ pullback ρ (ι a)) a q) =
      pullback.fst ρ (ι a) q := by
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  rw [hω] at hy ⊢
  have hρq : ρ (pullback.fst ρ (ι a) q) = ι a (pullback.snd ρ (ι a) q) := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  refine ⟨a, ?_⟩
  rw [← h₁, Scheme.Hom.comp_apply, hρq, ← Scheme.Hom.comp_apply]
  refine hz a _ ?_
  rw [Scheme.Hom.comp_apply, ← hρq, ← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, hy, hu']

/-- **A point over `u'` and a prescribed point lies in the restricted `some`-part.** In the
situation of `AlgebraicGeometry.exists_fst_eq_of_snd_eq_of_comparison`, let `ι` be indexed by
`Option α` and induce an isomorphism out of the coproduct, and suppose no point of `Q none` over
`pt` lies over `z`. Then every point of `X ×_Z V` over `u'` and over `z` is in the image of the
restricted pieces attached to `some`. -/
theorem mem_range_sigmaDesc_of_fst_eq_of_comparison {X Z Us Vs : Scheme.{u}} {f : X ⟶ Z}
    {g : Us ⟶ Z} {κ : Vs ⟶ Us} {w : Vs ⟶ Z} {ρ : pullback f w ⟶ pullback f g}
    (h₁ : ρ ≫ pullback.fst f g = pullback.fst f w)
    (h₂ : ρ ≫ pullback.snd f g = pullback.snd f w ≫ κ)
    {α : Type} [Finite α] {Q : Option α → Scheme.{u}} (ι : ∀ a, Q a ⟶ pullback f g)
    (hιiso : IsIso (Sigma.desc ι)) {pt : Us} {u' : Vs} (hu' : κ u' = pt) {z : X}
    (hnone : ∀ q : Q none,
      (ι none ≫ pullback.snd f g) q = pt → (ι none ≫ pullback.fst f g) q ≠ z)
    (ω : ↥(pullback f w)) (hsnd : pullback.snd f w ω = u') (hfst : pullback.fst f w ω = z) :
    ω ∈ Set.range (Sigma.desc fun i : α ↦ pullback.fst ρ (ι (some i))) := by
  have hptω : pullback.snd f g (ρ ω) = pt := by
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, hsnd, hu']
  have hfstω : pullback.fst f g (ρ ω) = z := by rwa [← Scheme.Hom.comp_apply, h₁]
  obtain ⟨a, q, hq⟩ := exists_apply_eq_of_isIso_sigmaDesc ι hιiso (ρ ω)
  cases a with
  | none =>
    exact (hnone q (by rwa [Scheme.Hom.comp_apply, hq]) (by rwa [Scheme.Hom.comp_apply, hq])).elim
  | some i =>
    obtain ⟨q', hq', -⟩ := Scheme.Pullback.exists_preimage_pullback (f := ρ) (g := ι (some i))
      ω q hq.symm
    exact ⟨Sigma.ι (fun i : α ↦ pullback ρ (ι (some i))) i q',
      by rwa [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Merging the finite pieces into a single object of the site -/

/-- **The finitely many finite pieces of the restricted decomposition assemble into one object of
the site, finite over the base.** Let `τ : Z ⟶ Y₀` and `ν : Zu ⟶ Y₀` be morphisms of the big fppf
category over `S`, let `g : U ⟶ Y₀` be a morphism of schemes and let `κ : Zu ⟶ U` satisfy
`κ ≫ g = ν` on underlying schemes. Given a family `ι a : Q a ⟶ Z ×_{Y₀} U` indexed by
`Option (Fin m)` whose members attached to `some i` are finite over `U`, there is an object `Z₁` of
the big fppf category over `S`, a morphism `ζ : Z₁ ⟶ Zu` whose underlying morphism of schemes is
finite, and a morphism `θ` from the underlying scheme of `Z₁` to `Z ×_{Y₀} Zu` which is an open
immersion and whose composite with the second projection is the underlying morphism of `ζ`.

That `θ` moreover identifies fibres is the last clause of the conclusion, stated for every point
`u'` of the underlying scheme of `Zu` carried by `κ` to a point `pt` of `U` and every family
`z₁, …, z_m` of points of the underlying scheme of `Z` for which the two fibre clauses of Tag
02LN hold over `pt` — the piece attached to `some i` meets the fibre over `pt` only in points
lying over `z_i`, and the piece attached to `none` meets it in no point lying over any `z_i`. For
such `u'` and `z`, the fibre of `ζ` over `u'` is identified with the part of the fibre of the
second projection over `u'` lying over one of the `z_i`:

* every point of the underlying scheme of `Z₁` which `ζ` carries to `u'` is carried by
  `θ` followed by the first projection to one of the `z_i`;
* every point of `Z ×_{Y₀} Zu` which the second projection carries to `u'` and the first
  projection carries to one of the `z_i` is in the image of `θ`.

These are the two conditions on the fibre over the distinguished point that Stacks 082H needs,
in the scheme-level form that
`AlgebraicGeometry.Space.forall_exists_pointsMap_eq_of_fibre_schemePoints` and
`AlgebraicGeometry.Space.mem_range_pointsMap_of_schemePoint_range` consume. They are obtained by
pulling a point back along the comparison morphism, discriminating by
`AlgebraicGeometry.exists_apply_eq_of_isIso_sigmaDesc` which piece of the decomposition its image
lies in, and — for the second — producing a point of the restricted piece from the pair of its
projections by Mathlib's
`AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`, the scheme-level analogue of Tag
03H4. The two 02LN clauses are hypotheses *of that last clause of the conclusion* rather than of
the theorem, which keeps the statement a strict extension of the merge on its own: a caller that
wants only `Z₁`, `ζ` and `θ` supplies nothing for them.

The open-and-closed clauses of the decomposition are not used, and no hypothesis of affineness on
the individual pieces is used either — the source's remark that they may be taken affine is not
needed. The object produced is the coproduct of the restricted pieces attached to `some`. The
restriction of each piece is `AlgebraicGeometry.isPullback_pullback_snd_of_comparison`, their merge
is `AlgebraicGeometry.isFinite_sigmaDesc` (Stacks 0CYI, available at an arbitrary finite index
type), the open immersion is
`AlgebraicGeometry.isOpenImmersion_sigmaDesc_some_of_isIso_sigmaDesc` applied to the restricted
family, and the passage into the site is
`AlgebraicGeometry.Space.contains_of_locallyOfFiniteType_of_quasiCompact` followed by
`AlgebraicGeometry.Space.exists_siteObject_toScheme_map_eq` — a finite morphism is both locally of
finite type and quasi-compact, so the size bound of Stacks 000R (5) applies with no further
hypothesis. -/
theorem exists_siteObject_isFinite_of_pullback_decomposition {Y₀ Zu Z : BigFppfOver B S hS}
    {Us : Scheme.{u}} {g : Us ⟶ (BigFppfOver.toScheme B S hS).obj Y₀} (τ : Z ⟶ Y₀) (ν : Zu ⟶ Y₀)
    (κ : (BigFppfOver.toScheme B S hS).obj Zu ⟶ Us)
    (hκ : κ ≫ g = (BigFppfOver.toScheme B S hS).map ν)
    {m : ℕ} {Q : Option (Fin m) → Scheme.{u}}
    (ι : ∀ a, Q a ⟶ pullback ((BigFppfOver.toScheme B S hS).map τ) g)
    (hιiso : IsIso (Sigma.desc ι))
    (hιfin : ∀ i, _root_.AlgebraicGeometry.IsFinite
      (ι (some i) ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ) g)) :
    ∃ (Z₁ : BigFppfOver B S hS) (ζ : Z₁ ⟶ Zu)
      (θ : (BigFppfOver.toScheme B S hS).obj Z₁ ⟶
        pullback ((BigFppfOver.toScheme B S hS).map τ) ((BigFppfOver.toScheme B S hS).map ν)),
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map ζ) ∧
      _root_.AlgebraicGeometry.IsOpenImmersion θ ∧
      θ ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν) =
        (BigFppfOver.toScheme B S hS).map ζ ∧
      ∀ (pt : Us) (u' : (BigFppfOver.toScheme B S hS).obj Zu), κ u' = pt →
        ∀ zz : Fin m → (BigFppfOver.toScheme B S hS).obj Z,
          (∀ (i : Fin m) (q : Q (some i)),
            (ι (some i) ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ) g) q = pt →
              (ι (some i) ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map τ) g) q = zz i) →
          (∀ q : Q none,
            (ι none ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ) g) q = pt →
              ∀ i, (ι none ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map τ) g) q ≠ zz i) →
          (∀ t : (BigFppfOver.toScheme B S hS).obj Z₁,
            (BigFppfOver.toScheme B S hS).map ζ t = u' →
              ∃ j, (θ ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map τ)
                ((BigFppfOver.toScheme B S hS).map ν)) t = zz j) ∧
          (∀ ω : ↥(pullback ((BigFppfOver.toScheme B S hS).map τ)
                ((BigFppfOver.toScheme B S hS).map ν)),
            pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
                ((BigFppfOver.toScheme B S hS).map ν) ω = u' →
              (∃ j, pullback.fst ((BigFppfOver.toScheme B S hS).map τ)
                ((BigFppfOver.toScheme B S hS).map ν) ω = zz j) →
                ω ∈ Set.range θ) := by
  obtain ⟨ρ, h₁, h₂⟩ := exists_comparison_of_comp_eq
    ((BigFppfOver.toScheme B S hS).map τ) g κ hκ
  have hfin : ∀ i : Fin m, _root_.AlgebraicGeometry.IsFinite (pullback.fst ρ (ι (some i)) ≫
      pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
        ((BigFppfOver.toScheme B S hS).map ν)) := fun i ↦
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      ((IsPullback.of_hasPullback ρ (ι (some i))).flip.paste_vert
        (isPullback_pullback_snd_of_comparison ((BigFppfOver.toScheme B S hS).map τ) g κ hκ ρ
          h₁ h₂)) (hιfin i)
  have hmerge : _root_.AlgebraicGeometry.IsFinite
      (Sigma.desc fun i : Fin m ↦ pullback.fst ρ (ι (some i)) ≫
        pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν)) := by
    have := hfin
    infer_instance
  have hoi : _root_.AlgebraicGeometry.IsOpenImmersion
      (Sigma.desc fun i : Fin m ↦ pullback.fst ρ (ι (some i))) :=
    isOpenImmersion_sigmaDesc_some_of_isIso_sigmaDesc (fun a ↦ pullback.fst ρ (ι a))
      (FinitaryPreExtensive.isIso_sigmaDesc_fst ι ρ hιiso)
  obtain ⟨Z₁, ζ, e, hζ⟩ := exists_siteObject_toScheme_map_eq B S hS
    (contains_of_locallyOfFiniteType_of_quasiCompact B S hS
      (Sigma.desc fun i : Fin m ↦ pullback.fst ρ (ι (some i)) ≫
        pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν)))
    (Sigma.desc fun i : Fin m ↦ pullback.fst ρ (ι (some i)) ≫
      pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
        ((BigFppfOver.toScheme B S hS).map ν))
  have hθfac : (e.hom ≫ Sigma.desc fun i : Fin m ↦ pullback.fst ρ (ι (some i))) ≫
      pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
        ((BigFppfOver.toScheme B S hS).map ν) =
      (BigFppfOver.toScheme B S hS).map ζ := by
    rw [hζ, Category.assoc]
    congr 1
    exact Sigma.hom_ext _ _ fun i ↦ by rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
  refine ⟨Z₁, ζ, e.hom ≫ Sigma.desc fun i : Fin m ↦ pullback.fst ρ (ι (some i)),
    by rw [hζ]; infer_instance, inferInstance, hθfac, ?_⟩
  intro pt u' hu' zz hsome hnone
  refine ⟨fun t ht ↦ ?_, ?_⟩
  · simpa only [Scheme.Hom.comp_apply] using exists_fst_eq_of_snd_eq_of_comparison h₁ h₂
      (fun i : Fin m ↦ ι (some i)) hu' hsome (e.hom t)
      (by rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Category.assoc, hθfac])
  · rintro ω hsnd ⟨j, hfst⟩
    obtain ⟨y, rfl⟩ := mem_range_sigmaDesc_of_fst_eq_of_comparison h₁ h₂ ι hιiso hu'
      (fun q hq ↦ hnone q hq j) ω hsnd hfst
    exact ⟨e.inv y, by rw [Scheme.Hom.comp_apply, Scheme.inv_hom_apply]⟩

/-! ### The first three paragraphs of Stacks 082H, delivered inside the site -/

/-- **The finite part of the splitting of Tag 02LN, as an object of the site finite over an affine
object of the site.** In the situation of
`AlgebraicGeometry.Space.exists_etaleNeighbourhood_decomposition_of_isQuasiFiniteAt` — a separated
morphism `k₁ : P ⟶ h_{Y₀}`, locally of finite type, from an algebraic space over `S` to a
representable presheaf with affine underlying scheme, and finitely many points of `|P|` over a
point `u` of `|h_{Y₀}|` at which `k₁` is quasi-finite — there are objects `Zu`, `Z₁` and `Z` of the
big fppf category over `S` with `Zu` and `Z` affine, a morphism `ν : Zu ⟶ Y₀` of the site which is
étale on underlying schemes, an étale chart `b : h_Z ⟶ P` with `τ : Z ⟶ Y₀` underlying `b ≫ k₁`, a
morphism `ζ : Z₁ ⟶ Zu` of the site which is **finite** on underlying schemes, and an **open
immersion** `θ` from the underlying scheme of `Z₁` into `Z ×_{Y₀} Zu` whose composite with the
second projection is the underlying morphism of `ζ`.

The distinguished point is carried too: a point `u'` of the underlying scheme of `Zu` lying over
the point of the affine base corresponding to `u`, a number `m` and a family `z₁, …, z_m` of
points of the underlying scheme of `Z` such that

* the points of `|Z|` in the family are exactly those whose image in `|P|` is one of the `wⱼ`;
* every point of the underlying scheme of `Z₁` which `ζ` carries to `u'` is carried by `θ`
  followed by the first projection to one of the `z_i`;
* every point of `Z ×_{Y₀} Zu` which the second projection carries to `u'` and the first
  projection carries to one of the `z_i` is in the image of `θ`;
* every `wⱼ` is the image on points, under `b`, of a point of the underlying scheme of `Z`.

The last clause is the chart hitting the prescribed points. It is what the presheaf-level step
needs in order to produce the point of `|Z|` that
`AlgebraicGeometry.Space.mem_range_pointsMap_of_schemePoint_range` consumes, and it is carried
unchanged from
`AlgebraicGeometry.Space.exists_etaleNeighbourhood_decomposition_of_isQuasiFiniteAt`.

This is the whole of the first three paragraphs of the proof of Stacks 082H, delivered over an
object of the site rather than over a bare scheme: the scheme-level content is
`AlgebraicGeometry.Space.exists_etaleNeighbourhood_decomposition_of_isQuasiFiniteAt`, the affine
shrinking inside the site is
`AlgebraicGeometry.Space.exists_affine_siteObject_of_etaleNeighborhood`, and the restriction and
merge are `AlgebraicGeometry.Space.exists_siteObject_isFinite_of_pullback_decomposition`. The
hypothesis list is exactly that of
`AlgebraicGeometry.Space.exists_etaleNeighbourhood_decomposition_of_isQuasiFiniteAt`: the three
clauses on points are the two fibre clauses of Tag 02LN restricted along `κ` and the
identification of the prescribed points of the chart, all of them conclusions of results already
proved, so nothing is assumed for them.

It is **not** the tag. What Stacks 082H asserts and this does not is the presheaf-level
consequence: an étale morphism `h_{Z₁} ⟶ P` whose composite with `k₁` is `h_ζ`, which is what
`AlgebraicGeometry.Space.exists_clopen_part_isFinite_of_isEtale_of_isFinite` consumes. Its two
conditions on the fibre over the distinguished point are the two point clauses here, after
`AlgebraicGeometry.Space.forall_exists_pointsMap_eq_of_fibre_schemePoints` and
`AlgebraicGeometry.Space.mem_range_pointsMap_of_schemePoint_range` convert them from schemes to
presheaves. -/
theorem exists_siteObject_isFinite_part_of_isQuasiFiniteAt
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    {Y₀ : BigFppfOver B S hS} (hY₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₀))
    (k₁ : P ⟶ yoneda.obj Y₀) (hsep : IsSeparated B S hS k₁)
    (hft : IsLocallyOfFiniteType B S hS k₁)
    (u : points B S hS (yoneda.obj Y₀))
    {p : ℕ} (w : Fin p → points B S hS P)
    (hwu : ∀ j, pointsMap B S hS P k₁ (w j) = u)
    (hwqf : ∀ j, IsQuasiFiniteAt B S hS k₁ (w j)) :
    ∃ (Zu Z₁ Z : BigFppfOver B S hS) (ν : Zu ⟶ Y₀) (ζ : Z₁ ⟶ Zu) (τ : Z ⟶ Y₀)
      (b : yoneda.obj Z ⟶ P)
      (θ : (BigFppfOver.toScheme B S hS).obj Z₁ ⟶
        pullback ((BigFppfOver.toScheme B S hS).map τ) ((BigFppfOver.toScheme B S hS).map ν))
      (u' : (BigFppfOver.toScheme B S hS).obj Zu) (m : ℕ)
      (zz : Fin m → (BigFppfOver.toScheme B S hS).obj Z),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Zu) ∧
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) ∧
      _root_.AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map ν) ∧
      IsEtale B S hS b ∧
      yoneda.map τ = b ≫ k₁ ∧
      _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map ζ) ∧
      _root_.AlgebraicGeometry.IsOpenImmersion θ ∧
      θ ≫ pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map ν) =
        (BigFppfOver.toScheme B S hS).map ζ ∧
      (BigFppfOver.toScheme B S hS).map ν u' = pointsToScheme B S hS Y₀ u ∧
      (∀ t : (BigFppfOver.toScheme B S hS).obj Z₁,
        (BigFppfOver.toScheme B S hS).map ζ t = u' →
          ∃ j, (θ ≫ pullback.fst ((BigFppfOver.toScheme B S hS).map τ)
            ((BigFppfOver.toScheme B S hS).map ν)) t = zz j) ∧
      (∀ ω : ↥(pullback ((BigFppfOver.toScheme B S hS).map τ)
            ((BigFppfOver.toScheme B S hS).map ν)),
        pullback.snd ((BigFppfOver.toScheme B S hS).map τ)
            ((BigFppfOver.toScheme B S hS).map ν) ω = u' →
          (∃ j, pullback.fst ((BigFppfOver.toScheme B S hS).map τ)
            ((BigFppfOver.toScheme B S hS).map ν) ω = zz j) →
            ω ∈ Set.range θ) ∧
      (∀ a : (BigFppfOver.toScheme B S hS).obj Z, a ∈ Set.range zz ↔
        pointsMap B S hS (yoneda.obj Z) b ((pointsEquivScheme B S hS Z).symm a)
          ∈ Set.range w) ∧
      (∀ j, ∃ a : (BigFppfOver.toScheme B S hS).obj Z,
        pointsMap B S hS (yoneda.obj Z) b
          ((pointsEquivScheme B S hS Z).symm a) = w j) := by
  obtain ⟨Z, b, τ, m, z, U, hUel, Q, ι, hιo, hιc, hιiso, v, hιfin, hZaff, hbE, hτ,
    hv, hfib, hnone, hzrange, hhit⟩ :=
    exists_etaleNeighbourhood_decomposition_of_isQuasiFiniteAt B S hS hP hY₀ k₁ hsep hft u w
      hwu hwqf
  obtain ⟨Zu, ν, κ, u', hZuaff, hκoi, hκfac, hνet, hκpt, hνpt⟩ :=
    exists_affine_siteObject_of_etaleNeighborhood B S hS hY₀ U
  obtain ⟨Z₁, ζ, θ, hζfin, hθoi, hθfac, hθpt⟩ :=
    exists_siteObject_isFinite_of_pullback_decomposition B S hS τ ν κ hκfac ι hιiso hιfin
  obtain ⟨hθpts, hθrange⟩ := hθpt U.point u' hκpt z
    (fun i q hq ↦ by
      have hqv : q ∈ ({v i} : Set (Q (some i))) := hfib i ▸ hq
      rw [hqv]; exact hv i)
    hnone
  exact ⟨Zu, Z₁, Z, ν, ζ, τ, b, θ, u', m, z, hZuaff, hZaff, hνet, hbE, hτ, hζfin, hθoi,
    hθfac, hνpt, hθpts, hθrange, hzrange, hhit⟩

end Space

end AlgebraicGeometry

end
