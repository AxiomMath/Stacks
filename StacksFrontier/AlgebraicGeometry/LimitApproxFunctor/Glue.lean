module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.GlueOverlap
public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.GluePair

/-!
# Functoriality of glueing two schemes along a common open subscheme

Let `f : W ⟶ X` and `g : W ⟶ Y` be open immersions, so that `AlgebraicGeometry.Scheme.gluePair`
`f g` glues `X` to `Y` along `W`.  A second such pair `f' : W' ⟶ X'`, `g' : W' ⟶ Y'` together
with a triple of morphisms `w : W ⟶ W'`, `x : X ⟶ X'`, `y : Y ⟶ Y'` commuting with the two
pairs induces a morphism of the glueings.  This file builds that morphism, proves the two
identities which make the construction functorial, and identifies the two legs of the source
glueing as the inverse images of the two legs of the target glueing.

This is the content of gap (b) of Tag 07RN at the level of a single glueing: at each finite
stage of the approximating system the model of the part already approximated is glued to an
affine scheme along their common open, and the transition morphisms of the new system are the
induced morphisms of glueings.

## What is proved, and the route

* `AlgebraicGeometry.Scheme.gluePairInl_eq_gluePairInr_iff`: a point of the first leg of a
  glueing is a point of the second exactly when both come from one point of the common open
  subscheme.  This is Mathlib's `AlgebraicGeometry.Scheme.IsLocallyDirected.ι_eq_ι_iff` for the
  two-legged wide span, where the only index carrying morphisms to both legs is the apex, so
  that the two transition morphisms in the statement are forced to be `f` and `g`.

* `AlgebraicGeometry.Scheme.preimage_opensRange_gluePairInl` and
  `AlgebraicGeometry.Scheme.preimage_opensRange_gluePairInr` — the two legs of a glueing meet
  exactly in the common open subscheme — are imported from
  `StacksFrontier.AlgebraicGeometry.Limits.FiniteTypeApproximation.GlueOverlap` and used below.

* `AlgebraicGeometry.Scheme.gluePairMap` is the induced morphism, defined as
  `AlgebraicGeometry.Scheme.gluePairDesc` of the two composites with the legs of the target;
  the compatibility it needs is the commutation of the triple with the two pairs together with
  `AlgebraicGeometry.Scheme.gluePair_condition`.  Its two defining equations
  `AlgebraicGeometry.Scheme.gluePairInl_gluePairMap` and
  `AlgebraicGeometry.Scheme.gluePairInr_gluePairMap` come for free from the universal property,
  and from them `AlgebraicGeometry.Scheme.gluePairMap_id` and
  `AlgebraicGeometry.Scheme.gluePairMap_comp` follow by
  `AlgebraicGeometry.Scheme.gluePair_hom_ext`.

* `AlgebraicGeometry.Scheme.preimage_opensRange_gluePairInl_gluePairMap`: if the common open
  subschemes correspond, in the sense that the inverse image of the image of `g'` under `y` is
  the image of `g`, then the first leg of the source glueing is the inverse image of the first
  leg of the target glueing.  The proof needs no case analysis on the source point in the
  inclusion that matters: the image of a point under the induced morphism lies inside the image
  of the first leg of the target, hence inside its image of the whole of `X'`, so the point
  itself comes from the first leg of the source.  Only the reverse inclusion is a computation,
  and it is one application of the leg equation.  With
  `AlgebraicGeometry.IsOpenImmersion.isPullback` this gives
  `AlgebraicGeometry.Scheme.isPullback_gluePairInl_gluePairMap`, the cartesian square an
  approximating system requires of its open subsystem.

* `AlgebraicGeometry.Scheme.isAffineHom_gluePairMap`: the induced morphism is affine as soon as
  `x` and `y` are and the two common opens correspond.  Affineness is local on the target, the
  two legs cover the target glueing by
  `AlgebraicGeometry.Scheme.gluePair_opensRange_sup`, and over each leg the induced morphism is,
  by the two cartesian squares, the corresponding member of the triple.

## Universe situation

Everything here is in one scheme universe, with no index category in sight; the glueing is a
colimit over `CategoryTheory.Limits.WidePushoutShape WalkingPair`, which is a small category in
any universe.  No universe is tied to another.

## Transparency gotchas

* Membership in the inverse image of an open under a morphism of schemes is *not* syntactically
  the membership of the image of the point, so no rewrite reaches inside one.  Each step that
  moves between the two forms here is an `exact` or a `show` up to definitional equality.

* `AlgebraicGeometry.Scheme.Hom.opensRange` takes the open-immersion instance as an argument, so
  rewriting a morphism underneath it fails with a motive error.  Where that is needed —
  `AlgebraicGeometry.preimage_opensRange_of_isPullback` in the sibling file — the rewrite is done
  by `simp only`, which transports the instance, rather than by `rewrite`.

* The instance `AlgebraicGeometry.HasAffineProperty` for affine morphisms is *not* found by
  instance search at the default transparency for types, so neither
  `CategoryTheory.MorphismProperty.RespectsIso` nor
  `AlgebraicGeometry.IsZariskiLocalAtTarget` for affine morphisms is available as written.
  Mathlib's own file on affine morphisms turns a compiler option on for exactly this, declaration
  by declaration.  Here the same effect is obtained inside one section by making
  `CategoryTheory.MorphismProperty` and `AlgebraicGeometry.AffineTargetMorphismProperty`
  reducible for implicit arguments, which is enough for both instances to fire.  Reading the
  failure as a missing result would be a mistake: both instances exist.

## What is NOT done here

Nothing here mentions a diagram of schemes, an inverse limit or the approximation structure of
Tag 07RN.  The induction over the finitely many affine opens — gap (c) — is untouched, and so is
step (iii), the identification of the ambient scheme as the inverse limit of the glued stages.
No inhabitant of `AlgebraicGeometry.Scheme.FiniteTypeApproximation` is built here, Tag 07RN is
not proved, and no tag attribute is attached to anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

section Points

variable {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]

/-- A point of the first leg of a glueing is a point of the second leg exactly when both come
from one point of the common open subscheme. -/
lemma gluePairInl_eq_gluePairInr_iff {p : X} {q : Y} :
    gluePairInl f g p = gluePairInr f g q ↔ ∃ z : W, f z = p ∧ g z = q := by
  rw [IsLocallyDirected.ι_eq_ι_iff]
  constructor
  · rintro ⟨k, fi, fj, z, hzi, hzj⟩
    cases fi <;> cases fj
    exact ⟨z, hzi, hzj⟩
  · rintro ⟨z, hz₁, hz₂⟩
    exact ⟨none, WidePushoutShape.Hom.init WalkingPair.left,
      WidePushoutShape.Hom.init WalkingPair.right, z, hz₁, hz₂⟩

end Points

section Map

variable {W X Y W' X' Y' : Scheme.{u}} {f : W ⟶ X} {g : W ⟶ Y} {f' : W' ⟶ X'} {g' : W' ⟶ Y'}
  [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion f'] [IsOpenImmersion g']
  (w : W ⟶ W') (x : X ⟶ X') (y : Y ⟶ Y')

/-- The morphism of glueings induced by a triple of morphisms commuting with the two pairs of
open immersions being glued along. -/
noncomputable def gluePairMap (hx : f ≫ x = w ≫ f') (hy : g ≫ y = w ≫ g') :
    gluePair f g ⟶ gluePair f' g' :=
  gluePairDesc f g (x ≫ gluePairInl f' g') (y ≫ gluePairInr f' g') <| by
    rw [reassoc_of% hx, reassoc_of% hy, gluePair_condition]

variable (hx : f ≫ x = w ≫ f') (hy : g ≫ y = w ≫ g')

/-- The induced morphism of glueings restricts to the given morphism on the first legs. -/
@[reassoc (attr := simp)]
lemma gluePairInl_gluePairMap :
    gluePairInl f g ≫ gluePairMap w x y hx hy = x ≫ gluePairInl f' g' :=
  gluePairInl_desc _ _ _ _ _

/-- The induced morphism of glueings restricts to the given morphism on the second legs. -/
@[reassoc (attr := simp)]
lemma gluePairInr_gluePairMap :
    gluePairInr f g ≫ gluePairMap w x y hx hy = y ≫ gluePairInr f' g' :=
  gluePairInr_desc _ _ _ _ _

/-- The induced morphism of glueings sends the image of a point `p` of the first leg to the image
of `x p`. -/
lemma gluePairInl_gluePairMap_apply (p : X) :
    gluePairMap w x y hx hy (gluePairInl f g p) = gluePairInl f' g' (x p) := by
  rw [← Scheme.Hom.comp_apply, gluePairInl_gluePairMap, Scheme.Hom.comp_apply]

/-- The induced morphism of glueings sends the image of a point `q` of the second leg to the image
of `y q`. -/
lemma gluePairInr_gluePairMap_apply (q : Y) :
    gluePairMap w x y hx hy (gluePairInr f g q) = gluePairInr f' g' (y q) := by
  rw [← Scheme.Hom.comp_apply, gluePairInr_gluePairMap, Scheme.Hom.comp_apply]

/-- If `y ⁻¹ᵁ U` is the image of `g` and the image of `q` under `φ` lies in the range of `a'`,
then `q` lies in the image of `g`. -/
private lemma exists_eq_of_apply_mem_opensRange {W B B' G G' A' : Scheme.{u}} {g : W ⟶ B}
    {U : B'.Opens} {y : B ⟶ B'} {b : B ⟶ G} {b' : B' ⟶ G'} {a' : A' ⟶ G'} [IsOpenImmersion a']
    [IsOpenImmersion g] (φ : G ⟶ G') (hU : y ⁻¹ᵁ U = g.opensRange)
    (hpre : ∀ r, b' r ∈ a'.opensRange → r ∈ U) (q : B) (hφ : φ (b q) = b' (y q))
    (h : φ (b q) ∈ a'.opensRange) : ∃ z, g z = q :=
  hU.le (show q ∈ y ⁻¹ᵁ U from hpre _ (hφ ▸ h))

/-- The first leg of the source glueing is the inverse image of the first leg of the target
glueing, as soon as the common open subscheme is the inverse image of the common open
subscheme. -/
lemma preimage_opensRange_gluePairInl_gluePairMap
    (hg : y ⁻¹ᵁ g'.opensRange = g.opensRange) :
    gluePairMap w x y hx hy ⁻¹ᵁ (gluePairInl f' g').opensRange =
      (gluePairInl f g).opensRange := by
  refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := gluePair_jointly_surjective f g t
    · exact ⟨p, rfl⟩
    · obtain ⟨z, hz⟩ := exists_eq_of_apply_mem_opensRange (b := gluePairInr f g)
        (b' := gluePairInr f' g') (a' := gluePairInl f' g') _ hg
        (fun r hr ↦ (preimage_opensRange_gluePairInl f' g').le hr) q
        (gluePairInr_gluePairMap_apply w x y hx hy q) ht
      exact ⟨f z, ((gluePairInl_eq_gluePairInr_iff f g).mpr ⟨z, rfl, hz⟩).trans rfl⟩
  · obtain ⟨p, rfl⟩ := ht
    exact ⟨x p, (gluePairInl_gluePairMap_apply w x y hx hy p).symm⟩

/-- The second leg of the source glueing is the inverse image of the second leg of the target
glueing, as soon as the common open subscheme is the inverse image of the common open
subscheme. -/
lemma preimage_opensRange_gluePairInr_gluePairMap
    (hf : x ⁻¹ᵁ f'.opensRange = f.opensRange) :
    gluePairMap w x y hx hy ⁻¹ᵁ (gluePairInr f' g').opensRange =
      (gluePairInr f g).opensRange := by
  refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := gluePair_jointly_surjective f g t
    · obtain ⟨z, hz⟩ := exists_eq_of_apply_mem_opensRange (b := gluePairInl f g)
        (b' := gluePairInl f' g') (a' := gluePairInr f' g') _ hf
        (fun r hr ↦ (preimage_opensRange_gluePairInr f' g').le hr) p
        (gluePairInl_gluePairMap_apply w x y hx hy p) ht
      exact ⟨g z, (((gluePairInl_eq_gluePairInr_iff f g).mpr ⟨z, hz, rfl⟩).symm).trans rfl⟩
    · exact ⟨q, rfl⟩
  · obtain ⟨q, rfl⟩ := ht
    exact ⟨y q, (gluePairInr_gluePairMap_apply w x y hx hy q).symm⟩

/-- **The first legs form a cartesian square.** -/
lemma isPullback_gluePairInl_gluePairMap (hg : y ⁻¹ᵁ g'.opensRange = g.opensRange) :
    IsPullback x (gluePairInl f g) (gluePairInl f' g') (gluePairMap w x y hx hy) :=
  IsOpenImmersion.isPullback _ _ _ _ (gluePairInl_gluePairMap w x y hx hy)
    (preimage_opensRange_gluePairInl_gluePairMap w x y hx hy hg)

/-- **The second legs form a cartesian square.** -/
lemma isPullback_gluePairInr_gluePairMap (hf : x ⁻¹ᵁ f'.opensRange = f.opensRange) :
    IsPullback y (gluePairInr f g) (gluePairInr f' g') (gluePairMap w x y hx hy) :=
  IsOpenImmersion.isPullback _ _ _ _ (gluePairInr_gluePairMap w x y hx hy)
    (preimage_opensRange_gluePairInr_gluePairMap w x y hx hy hf)

section Affine

attribute [local implicit_reducible] CategoryTheory.MorphismProperty
  AlgebraicGeometry.AffineTargetMorphismProperty

/-- The restriction of a morphism to the image of an open immersion is affine as soon as the
second leg of a cartesian square over that open immersion is. -/
private lemma isAffineHom_morphismRestrict_of_isPullback {A B A' B' : Scheme.{u}} {m : A ⟶ B}
    {iB : B' ⟶ B} [IsOpenImmersion iB] {iA : A' ⟶ A} {m' : A' ⟶ B'}
    (h : IsPullback iA m' m iB) [IsAffineHom m'] : IsAffineHom (m ∣_ iB.opensRange) := by
  have : HasPullback m iB := h.hasPullback
  refine (MorphismProperty.arrow_mk_iso_iff (P := @IsAffineHom)
    (morphismRestrictOpensRange m iB)).mpr ?_
  rw [← h.isoPullback_inv_snd,
    MorphismProperty.cancel_left_of_respectsIso (P := @IsAffineHom)]
  infer_instance

/-- **A morphism of glueings is affine as soon as its two legs are.**  Affineness is local on
the target and the two legs of the target glueing cover it; over each of them the morphism is,
by the two cartesian squares, the corresponding leg of the triple. -/
lemma isAffineHom_gluePairMap [IsAffineHom x] [IsAffineHom y]
    (hf : x ⁻¹ᵁ f'.opensRange = f.opensRange) (hg : y ⁻¹ᵁ g'.opensRange = g.opensRange) :
    IsAffineHom (gluePairMap w x y hx hy) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun b : Bool ↦ cond b (gluePairInl f' g').opensRange (gluePairInr f' g').opensRange)
    (iSup_bool_eq.trans (gluePair_opensRange_sup f' g')) fun b ↦ ?_
  cases b with
  | true =>
    exact isAffineHom_morphismRestrict_of_isPullback
      (isPullback_gluePairInl_gluePairMap w x y hx hy hg).flip
  | false =>
    exact isAffineHom_morphismRestrict_of_isPullback
      (isPullback_gluePairInr_gluePairMap w x y hx hy hf).flip

end Affine

end Map

section Identities

variable {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion g]

/-- The morphism of glueings induced by identities is the identity. -/
@[simp]
lemma gluePairMap_id (hx : f ≫ 𝟙 X = 𝟙 W ≫ f) (hy : g ≫ 𝟙 Y = 𝟙 W ≫ g) :
    gluePairMap (𝟙 W) (𝟙 X) (𝟙 Y) hx hy = 𝟙 (gluePair f g) :=
  gluePair_hom_ext f g (by simp) (by simp)

end Identities

section Comp

variable {W X Y W' X' Y' W'' X'' Y'' : Scheme.{u}} {f : W ⟶ X} {g : W ⟶ Y} {f' : W' ⟶ X'}
  {g' : W' ⟶ Y'} {f'' : W'' ⟶ X''} {g'' : W'' ⟶ Y''}
  [IsOpenImmersion f] [IsOpenImmersion g] [IsOpenImmersion f'] [IsOpenImmersion g']
  [IsOpenImmersion f''] [IsOpenImmersion g'']
  {w : W ⟶ W'} {x : X ⟶ X'} {y : Y ⟶ Y'} {w' : W' ⟶ W''} {x' : X' ⟶ X''} {y' : Y' ⟶ Y''}

/-- The morphism of glueings induced by composite triples is the composite of the induced
morphisms. -/
lemma gluePairMap_comp (hx : f ≫ x = w ≫ f') (hy : g ≫ y = w ≫ g')
    (hx' : f' ≫ x' = w' ≫ f'') (hy' : g' ≫ y' = w' ≫ g'')
    (hxc : f ≫ x ≫ x' = (w ≫ w') ≫ f'') (hyc : g ≫ y ≫ y' = (w ≫ w') ≫ g'') :
    gluePairMap (w ≫ w') (x ≫ x') (y ≫ y') hxc hyc =
      gluePairMap w x y hx hy ≫ gluePairMap w' x' y' hx' hy' :=
  gluePair_hom_ext f g (by simp) (by simp)

end Comp

end AlgebraicGeometry.Scheme
