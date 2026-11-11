module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLimitExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Separated

/-!
# The limit situation for algebraic spaces, and descent of coverings by opens

Situation 084R of the Stacks project fixes a scheme `S`, a directed inverse system of
algebraic spaces over `S` with affine transition morphisms whose stages are quasi-compact
and quasi-separated, its limit `X`, and a chosen index `0`. This file records that situation
as a structure, together with the facts about it that follow from Stacks 07SF.

It also proves parts (2) and (3) of Stacks 01Z4 in the form the source states them: the
descent of an equality of inverse images of quasi-compact opens given at two different stages,
and the descent of a covering by opens, along a limit of schemes with affine transition
morphisms.

## Main definitions

* `AlgebraicGeometry.Space.LimitSituation` is Situation 084R: a directed index set with a
  chosen element, an inverse system of algebraic spaces over it with affine transition
  morphisms, each stage quasi-compact and quasi-separated, and a limiting cone with the
  given presheaf as its vertex.
* `AlgebraicGeometry.Space.LimitSituation.cone` is that limiting cone, with
  `AlgebraicGeometry.Space.LimitSituation.isLimitCone` and
  `AlgebraicGeometry.Space.LimitSituation.hasLimit`.

## Main results

* `AlgebraicGeometry.exists_map_preimage_eq_map_preimage_of_preimage_eq` is **part (2) of
  Stacks 01Z4**: quasi-compact opens of two stages `X_i` and `X_{i'}` with the same inverse
  image in the limit have the same inverse image in some stage mapping to both.
* `AlgebraicGeometry.exists_iSup_map_preimage_eq_top` is **part (3) of Stacks 01Z4**: if the
  inverse images in the limit of a family of opens of one stage cover the limit, then their
  inverse images in some earlier stage cover that stage.
* `AlgebraicGeometry.Space.LimitSituation.isAffineHom_π_of_isSiteSmall` is Stacks 07SF (1) in the
  situation: every projection from the limit to a stage is affine.
* `AlgebraicGeometry.Space.LimitSituation.const` exhibits a quasi-compact and
  quasi-separated algebraic space as its own limit situation, over the one-element index
  set, and `AlgebraicGeometry.Space.LimitSituation.ofIso` transports a limit situation along
  an isomorphism.

## Implementation notes

*Parts (2) and (3) of Stacks 01Z4.* Mathlib carries part (1) of that tag as
`AlgebraicGeometry.exists_preimage_eq`, and tags part (2) on
`AlgebraicGeometry.exists_map_preimage_eq_map_preimage`, whose two opens lie in one stage,
while the source allows two stages `i` and `i'`. The two-stage statement follows by first
pulling both opens back to a common stage below `i` and `i'`, where they stay quasi-compact
because affine morphisms are quasi-compact; it is
`AlgebraicGeometry.exists_map_preimage_eq_map_preimage_of_preimage_eq` below.
`AlgebraicGeometry.exists_preimage_eq'`, `AlgebraicGeometry.exists_map_preimage_eq_map_preimage'`
and `AlgebraicGeometry.exists_map_eq_top'` carry the Mathlib content with the index morphism
universe freed. Part (3) is an immediate consequence of
`AlgebraicGeometry.exists_map_eq_top'`, since a preimage of opens commutes with suprema, so a
family covers exactly when its supremum is everything, and the statement for one open is the
statement for a family. Mathlib tags parts (1) and (2) but leaves `exists_map_eq_top`
untagged, so part (3) of the tag is carried here, by
`AlgebraicGeometry.exists_iSup_map_preimage_eq_top` below. Two hypotheses of the source are
not needed and are not imposed: the family need
not be finite, and its members need not be quasi-compact. What *is* needed, and is part of
Situation 086P, is that every stage is quasi-compact; that is where
`AlgebraicGeometry.exists_map_eq_top'` uses the compactness argument of Stacks 01Z3.

This matters beyond the tag. The proof of Stacks 09YC produces, at a large enough
stage `i`, affine opens `V_{i, j}` of a stage `Y_i` whose inverse images in `Y` are the
members of a chosen finite affine open covering of `Y`, citing Stacks 0827 — and then ends.
Nothing in it shows that the `V_{i, j}` cover `Y_i`, and that does not follow from what it
cites: 0827 and 01Z4 (1) deliver only the equality of inverse images, which constrains the
`V_{i, j}` solely along the image of `Y ⟶ Y_i`. Nor is it true as stated at the stage `i`
that 0827 returns. For a two-element index set `0 ≤ 1` take `Y_0 = Spec(k[x])` and
`Y_1 = Spec(k[x, 1/x])` with the localization, an affine morphism, as transition. Both
stages are affine, hence quasi-compact and quasi-separated as Situation 086P asks. The
index set has a largest element, so `1` is terminal in it and `op 1` is initial in its
opposite, and the limit of the system is therefore the stage there
(`CategoryTheory.Limits.limitOfDiagramInitial`): `Y = Y_1`. The single quasi-compact open
`V_{0, 1} = D(x) ⊂ Y_0` has inverse image all of `Y`, the localization map factoring
through `D(x)`, so its inverse image covers `Y`, while `V_{0, 1} ≠ Y_0` misses the origin.
What part (3) supplies is
exactly the one thing that repairs this: a *later* stage `i' ≥ i`, there `i' = 1`, at which
the inverse images do cover. By the point in the proof of 09YC where this is needed the
stages `Y_i` are already schemes, Stacks 07SR having been applied, so the scheme-level
statement proved here is the one that argument wants.

*The situation.* The index is a directed preorder with a chosen element, and the inverse
system is a functor out of its opposite, exactly as in the scheme-level twin
`AlgebraicGeometry.DescentSituation` (Situation 086P) in
`StacksFrontier/AlgebraicGeometry/Perfect/Limits.lean`, whose field names this structure
follows — 084R and 086P are the same situation one level apart, so the twin to agree with is
the one carrying the other tag of the pair, rather than
`AlgebraicGeometry.Space.NoetherianApproximation`, which is a different situation that merely
happens to live in the same category. Unlike there, the index set is a *field*: the
situation is attached to a presheaf `X` and asserts a system having it as limit, so the
index cannot be a parameter. The
`Preorder` and `IsDirected` fields are re-exported as instances on `LimitSituation.I`, which
is what makes `A.Iᵒᵖ` a cofiltered category by instance synthesis and so lets the
inverse-limit machinery of this development be applied to `A.system` directly.

Quasi-separatedness is the absolute notion of Stacks 03BS (3), as in
`AlgebraicGeometry.Space.NoetherianApproximation`, so a containment hypothesis on the
terminal scheme is carried; quasi-compactness is Stacks 03E3.

*The limit.* `X = lim X_i` is recorded as a limiting cone of presheaves with vertex `X`. As
in `AlgebraicGeometry.Space.NoetherianApproximation`, this is equivalent to the source's
limit in the category of algebraic spaces, that category being a full subcategory of
presheaves which contains the representables; and limits of this shape exist
unconditionally, so no size hypothesis is needed to *state* the situation. The smallness
condition `AlgebraicGeometry.Space.IsSiteSmall` of Stacks 07SF is needed to recognize such a
limit as an algebraic space, and it reappears as an explicit hypothesis on the results that use
that tag. Under its cofinality alternative only the cardinality of the index *set* occurs: the
morphisms of a preorder are subsingletons, so the bound on the hom types which
`AlgebraicGeometry.Space.isAffineHom_limitπ_of_isSiteSmall` asks for is automatic here, and
`AlgebraicGeometry.Space.IsSiteSmall.of_lt_cof_op` records that.

*What is not here.* Stacks 0827, that a quasi-compact open subspace of `X` is the inverse
image of a quasi-compact open subspace of some stage, is not proved in this file and nothing
here carries that tag. It is proved elsewhere, as
`AlgebraicGeometry.Space.exists_isOpenSubspace_isQuasiCompactSpace_preimage_eq` in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/DescendOpens.lean`, and not by the route the
source takes: rather than applying 01Z4 (1) to an étale presentation of the limit as a limit
of schemes, that proof runs on the topology of points throughout, through Stacks 086V, 04NN
and 03BZ, so it needs no such presentation and drops the quasi-compactness and
quasi-separatedness of the stages. It does carry the two size hypotheses of Stacks 07SF.

The étale presentation itself is partly available. Each stage `U_i = X_i ×_{X_0} U_0` *is*
representable, by the implication (2) ⇒ (1) of Stacks 03WG applied to the transition
morphisms exactly as in the proof of
`AlgebraicGeometry.Space.relativelyRepresentable_limitπ`; and Stacks 07SF (2),
`AlgebraicGeometry.Space.isLimitPullbackLimitOverPost`, exhibits `X ×_{X_0} U_0` as their
limit — but as a limit of *presheaves*, whereas a scheme-level consumer needs a limiting cone
of **schemes**. For an **affine** chart `U_0` such a cone is available:
`AlgebraicGeometry.Space.AffineChartSystem.LimitBridge.schemeIsLimit`, from
`AlgebraicGeometry.Space.AffineChartSystem.limitBridge` in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/AffineChartSystem.lean`, which lifts the diagram
through Yoneda and places its limit in the size-bounded site by the covering-by-affine-opens
argument of `AlgebraicGeometry.Space.relativelyRepresentable_limitπ`. For a general, in
particular non-affine, test object — which is what the relation `U_0 ×_{X_0} U_0` of a
presentation is — that argument has not been redone, and the limits of schemes built inside
the proof of Stacks 07SG,
`AlgebraicGeometry.Space.exists_quotient_presentation_of_affine_transition` in
`StacksFrontier/AlgebraicGeometry/Spaces/Limits/QuotientPresentation.lean`, are private and are
not placed back in the site.

## References

* [Stacks Project, Tag 084R](https://stacks.math.columbia.edu/tag/084R)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 0827](https://stacks.math.columbia.edu/tag/0827)
* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 09YC](https://stacks.math.columbia.edu/tag/09YC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal Opposite

universe v u

namespace AlgebraicGeometry

/-! ### Descending a covering by opens along a limit of schemes -/

/-- **Stacks 01Z4, part (2).** Let `X = lim X_i` be the limit of a cofiltered inverse system
of schemes with affine transition morphisms. If quasi-compact opens `U ⊆ X_i` and
`V ⊆ X_{i'}` have the same inverse image in `X`, then there are transition morphisms
`X_j ⟶ X_i` and `X_j ⟶ X_{i'}` along which `U` and `V` have the same inverse image in `X_j`.

The source asks the stages to be quasi-compact and quasi-separated as well (Situation 086P);
that is not used. Both opens are first pulled back to a stage `k` mapping to `i` and `i'`
(`CategoryTheory.IsCofilteredOrEmpty.cone_objs`), where they are again quasi-compact since affine
morphisms are quasi-compact, and the single-stage case
`AlgebraicGeometry.exists_map_preimage_eq_map_preimage'` applies there. -/
@[stacks 01Z4 "(2)"]
theorem exists_map_preimage_eq_map_preimage_of_preimage_eq {I : Type u} [Category.{v} I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] {i i' : I} {U : (D.obj i).Opens}
    {V : (D.obj i').Opens} (hU : IsCompact (U : Set (D.obj i)))
    (hV : IsCompact (V : Set (D.obj i'))) (H : c.π.app i ⁻¹ᵁ U = c.π.app i' ⁻¹ᵁ V) :
    ∃ (j : I) (f : j ⟶ i) (f' : j ⟶ i'), D.map f ⁻¹ᵁ U = D.map f' ⁻¹ᵁ V := by
  obtain ⟨k, g, g', -⟩ := IsCofilteredOrEmpty.cone_objs i i'
  have H' : c.π.app k ⁻¹ᵁ D.map g ⁻¹ᵁ U = c.π.app k ⁻¹ᵁ D.map g' ⁻¹ᵁ V := by
    simpa only [← Scheme.Hom.comp_preimage, c.w] using H
  obtain ⟨j, f, hj⟩ := exists_map_preimage_eq_map_preimage' D c hc
    (QuasiCompact.isCompact_preimage _ U.isOpen hU)
    (QuasiCompact.isCompact_preimage _ V.isOpen hV) H'
  exact ⟨j, f ≫ g, f ≫ g', by simpa only [Functor.map_comp, Scheme.Hom.comp_preimage] using hj⟩

/-- **Stacks 01Z4, part (3).** Let `X = lim X_i` be the limit of a cofiltered inverse system
of quasi-compact schemes with affine transition morphisms. If a family of opens of a stage
`X_i` has inverse images in `X` covering `X`, then for some transition morphism
`X_j ⟶ X_i` the inverse images of the family in `X_j` cover `X_j`.

The source states this for a finite family of quasi-compact opens. Neither hypothesis is
used: a preimage of opens commutes with arbitrary suprema, so the statement for the single
open `⨆ k, V k` is the statement for the family. What the proof does use, and what
Situation 086P provides, is that every stage is quasi-compact.

The single-open case is Mathlib's `AlgebraicGeometry.exists_map_eq_top`, used here through
`AlgebraicGeometry.exists_map_eq_top'`, its index-morphism-universe-free form, and the step
from one open to a family is `AlgebraicGeometry.Scheme.Hom.preimage_iSup`. Mathlib records the
tag for parts (1) and (2) on `AlgebraicGeometry.exists_preimage_eq` and
`AlgebraicGeometry.exists_map_preimage_eq_map_preimage`; its `exists_map_eq_top` carries no
tag, so part (3) is recorded here. -/
@[stacks 01Z4 "(3)"]
theorem exists_iSup_map_preimage_eq_top {I : Type u} [Category.{v} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i : I, CompactSpace (D.obj i)]
    {i : I} {ι : Type*} (V : ι → (D.obj i).Opens)
    (hV : (⨆ k, c.π.app i ⁻¹ᵁ V k) = ⊤) :
    ∃ (j : I) (f : j ⟶ i), (⨆ k, D.map f ⁻¹ᵁ V k) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup] at hV
  obtain ⟨j, f, hj⟩ := exists_map_eq_top' D c hc (⨆ k, V k) hV
  exact ⟨j, f, by rwa [Scheme.Hom.preimage_iSup] at hj⟩

namespace Space

/-! ### Situation 084R -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Situation 084R.** A *limit situation* for a presheaf `X` on the big fppf site of `S`:
a directed index set with a chosen element, an inverse system of algebraic spaces over `S`
indexed by it whose transition morphisms are affine and whose stages are quasi-compact and
quasi-separated, and an identification of `X` with the limit of that system.

This is the algebraic-space analogue of `AlgebraicGeometry.DescentSituation`, which is
Situation 086P for schemes, and the two have the same fields. By Stacks 07SF the limit of
such a system *is* an algebraic space over `S`, so the situation is not vacuous for a
reason it should not be: `AlgebraicGeometry.Space.LimitSituation.const` builds one for every
quasi-compact quasi-separated algebraic space. -/
@[stacks 084R]
structure LimitSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) where
  /-- The directed set indexing the system. -/
  I : Type u
  /-- Its order. -/
  [preorder : Preorder I]
  /-- A directed set is directed. -/
  [isDirected : IsDirected I (· ≤ ·)]
  /-- The inverse system, a functor out of the opposite of the index set. -/
  system : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u
  /-- Every stage is an algebraic space over `S`. -/
  isAlgebraicSpace (i : I) : IsAlgebraicSpace B S hS (system.obj (op i))
  /-- Every transition morphism of the inverse system is affine. -/
  transition_affine {i j : Iᵒᵖ} (f : i ⟶ j) : IsAffineHom B S hS (system.map f)
  /-- Every stage is quasi-compact. -/
  quasiCompact (i : I) : IsQuasiCompactSpace B S hS (system.obj (op i))
  /-- Every stage is quasi-separated. -/
  quasiSeparated (i : I) : IsAbsolutelyQuasiSeparated B S hS hZ (system.obj (op i))
  /-- The projections from `X` to the stages. -/
  π : (Functor.const Iᵒᵖ).obj X ⟶ system
  /-- They exhibit `X` as the limit of the system. -/
  isLimit : IsLimit (Cone.mk X π)
  /-- The chosen index of the system. -/
  base : I

/-! ### Affineness of an isomorphism -/

/-- An isomorphism of presheaves on the big fppf site of `S` is an affine morphism: a base
change of it along any morphism from an affine object of the site is represented by that
same object. -/
theorem isAffineHom_of_isIso (f : X ⟶ Y) [IsIso f] : IsAffineHom B S hS f := fun Z g =>
  ⟨Z, g ≫ inv f, 𝟙 _, by
    simpa using IsPullback.of_vert_isIso (fst := g ≫ inv f) (snd := (𝟙 _ : _ ⟶ _)) ⟨by simp⟩⟩

namespace LimitSituation

variable (A : LimitSituation B S hS hZ X)

/-- The index set of a limit situation carries the order its `preorder` field supplies. -/
instance : Preorder A.I := A.preorder

/-- The index set of a limit situation is directed. -/
instance : IsDirected A.I (· ≤ ·) := A.isDirected

/-- The index set of a limit situation is nonempty, the chosen index being an element. -/
instance : Nonempty A.I := ⟨A.base⟩

/-- The limiting cone of a limit situation, with vertex the presheaf the situation is
attached to. -/
@[simps pt π]
def cone : Cone A.system := Cone.mk X A.π

/-- The cone of a limit situation is limiting. -/
def isLimitCone : IsLimit A.cone := A.isLimit

/-- The inverse system of a limit situation has a limit, namely the presheaf the situation
is attached to. -/
theorem hasLimit : HasLimit A.system := ⟨⟨A.cone, A.isLimitCone⟩⟩

/-- The morphisms of the index category of a limit situation are subsingletons, a preorder
being a thin category, so their cardinality is below any infinite cardinal. -/
theorem mk_hom_lt_aleph0 (i j : A.Iᵒᵖ) : #(i ⟶ j) < ℵ₀ :=
  have : Finite (i ⟶ j) := Finite.of_subsingleton
  lt_aleph0_of_finite _

/-- The opposite of the index set of a limit situation has the same cardinality as the index
set itself. -/
theorem mk_op : #A.Iᵒᵖ = #A.I := mk_congr (Opposite.equivToOpposite (α := A.I)).symm

/-! ### Consequences of Stacks 07SF -/

/-- **Stacks 07SF, part (1), in Situation 084R.** Every projection from the limit of a limit
situation to one of its stages is affine, provided the inverse system is small for the site,
`AlgebraicGeometry.Space.IsSiteSmall`: either the index set has cardinality below the
cofinality of the site's size cutoff — then
`AlgebraicGeometry.Space.IsSiteSmall.of_lt_cof_op` supplies the hypothesis, the bound on the
hom types being automatic because the morphisms of a preorder are subsingletons — or the
transition morphisms of the system are monomorphisms, with nothing asked of the index.

The tag is carried by `AlgebraicGeometry.Space.isAffineHom_limitπ`; this is that result
transported to the cone the situation carries, and so is not a second tag site. -/
theorem isAffineHom_π_of_isSiteSmall (hb : IsSiteSmall B S hS A.system) (i : A.Iᵒᵖ) :
    IsAffineHom B S hS (A.π.app i) := by
  have := A.hasLimit
  have hlim := isAffineHom_limitπ_of_isSiteSmall B S hS A.system hb
    (fun {_ _} f => A.transition_affine f) i
  have he : (A.isLimitCone.conePointUniqueUpToIso (limit.isLimit A.system)).hom ≫
      limit.π A.system i = A.π.app i :=
    A.isLimitCone.conePointUniqueUpToIso_hom_comp (limit.isLimit A.system) i
  have hiso : IsAffineHom B S hS
      (A.isLimitCone.conePointUniqueUpToIso (limit.isLimit A.system)).hom :=
    isAffineHom_of_isIso _
  rw [← he]
  exact isAffineHom_comp B S hS _ _ hiso hlim

/-- **Stacks 07SF, part (1), in Situation 084R.** Every projection from the limit of a limit
situation to one of its stages is affine, provided the index set is small enough for the
site: it has cardinality below the cofinality of the site's size cutoff.

The bound on the hom types that `AlgebraicGeometry.Space.isAffineHom_limitπ` also asks for
is automatic, the morphisms of a preorder being subsingletons.

The tag is carried by `AlgebraicGeometry.Space.isAffineHom_limitπ`; this is that result
transported to the cone the situation carries, and so is not a second tag site. -/
theorem isAffineHom_π (hSize : #A.I < B.cutoff.ord.cof) (i : A.Iᵒᵖ) :
    IsAffineHom B S hS (A.π.app i) :=
  A.isAffineHom_π_of_isSiteSmall (Space.IsSiteSmall.of_lt_cof_op hSize) i

/-! ### Transport and the base case -/

/-- A limit situation for `X` is a limit situation for any presheaf isomorphic to `X`: the
system is unchanged and the projections are composed with the inverse of the
isomorphism. -/
def ofIso (e : X ≅ Y) : LimitSituation B S hS hZ Y where
  I := A.I
  system := A.system
  isAlgebraicSpace := A.isAlgebraicSpace
  transition_affine := A.transition_affine
  quasiCompact := A.quasiCompact
  quasiSeparated := A.quasiSeparated
  π := (Functor.const _).map e.inv ≫ A.π
  isLimit := A.isLimit.ofIsoLimit (Cone.ext e (fun j => by simp))
  base := A.base

/-- **The base case.** A quasi-compact and quasi-separated algebraic space over `S` is its
own limit situation: take the constant inverse system over the one-element index set. -/
noncomputable def const (hX : IsAlgebraicSpace B S hS X)
    (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X) :
    LimitSituation B S hS hZ X where
  I := PUnit.{u + 1}
  system := (Functor.const _).obj X
  isAlgebraicSpace _ := hX
  transition_affine _ := isAffineHom_id X
  quasiCompact _ := hqc
  quasiSeparated _ := hqs
  π := 𝟙 _
  isLimit := isLimitConstCone _ X
  base := PUnit.unit

end LimitSituation

end Space

end AlgebraicGeometry

end
