module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.Reindex

/-!
# The overlap in its two guises

In the one-affine-open step of Tag 07RN the overlap of the part already approximated with the
affine open being added appears **twice over, as two different objects**:

* as `V.ι ⁻¹ᵁ Y`, an open of the *scheme* `V` — which is where step (i)
  (`AlgebraicGeometry.exists_stage_preimage_eq_inf`) descends it to a finite stage, where the
  compatible family of its models lives, and where Tag 01Z0 computes its ring of sections;

* as `V ⊓ Y`, an open of the *ambient scheme* `S` — which is where the cone of step (iii)
  (`AlgebraicGeometry.gluePairFunctorCone`) wants it, since that cone is built from the
  two-element cover `{V, Y}` of `S` and its glueing condition is stated along `V ⊓ Y`.

This file identifies the two and carries the limiting cone over the overlap models, which comes
with the first vertex, across to the second, so that all three cones of step (iii) are built over
opens of `S`.

## Main definitions

* `AlgebraicGeometry.Scheme.overlapIso`: the isomorphism `V ⊓ Y ≅ V.ι ⁻¹ᵁ Y`.
* `AlgebraicGeometry.coneExtend`: a cone re-based along a morphism into its vertex.
* `AlgebraicGeometry.overlapCone`: the restricted cone over the overlap models, re-based onto
  `V ⊓ Y`.

## Main results

* `AlgebraicGeometry.Scheme.opensRange_homOfLE_inf_left` and
  `AlgebraicGeometry.Scheme.opensRange_homOfLE_inf_right`: the inclusion of `V ⊓ Y` into `V` has
  image `V.ι ⁻¹ᵁ Y`, and into `Y` has image `Y.ι ⁻¹ᵁ V`.  The second is the shape of the
  hypothesis `hYr` of `AlgebraicGeometry.preimage_opensRange_gluePairFunctorCone_right`.
* `AlgebraicGeometry.Scheme.overlapIso_hom_ι`: composed with the inclusion of the overlap into
  `V`, the isomorphism is the inclusion of `V ⊓ Y` into `V`.
* `AlgebraicGeometry.isLimitConeExtend`: a cone re-based along an isomorphism of the vertex is
  limiting if the original was; this is the pattern of
  `AlgebraicGeometry.Scheme.FiniteTypeApproximation.ofIso`, stated for a bare cone.
* `AlgebraicGeometry.isLimitOverlapCone` and `AlgebraicGeometry.overlapCone_app_comp_ι`: the
  re-based cone is limiting and compatible with the inclusion of `V ⊓ Y` into `V`; the latter is
  the hypothesis `hXW` of `AlgebraicGeometry.gluePairFunctorCone`.

## Implementation notes

`AlgebraicGeometry.Scheme.overlapIso` is `AlgebraicGeometry.Scheme.Hom.isoOpensRange` of the
inclusion followed by `AlgebraicGeometry.Scheme.isoOfEq` at the image computation.

`AlgebraicGeometry.Scheme.homOfLE` is built through `IsOpenImmersion.lift`, so its action on a
point is not reduced by reflexivity.  Mathlib's `AlgebraicGeometry.Scheme.homOfLE_apply` states
the equation at the coercion of an open to a *scheme*, while the pointwise arguments here meet it
at the coercion of an open to a *set*; the two differ by one unfolding and a rewrite with the
Mathlib form does not match.  `AlgebraicGeometry.Scheme.homOfLE_coe` is the same equation at the
spelling that appears, proved by applying `AlgebraicGeometry.Scheme.homOfLE_ι` to the point.
Membership in an inverse image is not syntactically membership of the image of the point, so the
two image computations move between the forms by `change` and never by rewriting.

`AlgebraicGeometry.overlapCone_app_comp_ι` is proved as a chain of `congrArg` steps rather than
by `rw`: the cone's legs are `AlgebraicGeometry.Scheme.Hom.resLE` applications under a `def`, and
a rewrite aimed at them fails its motive check.

The index category is free — objects in `w`, morphisms in `v`, schemes in `u`.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v w u

namespace AlgebraicGeometry

/-! ### Moving a cone along a morphism of the vertex -/

/-- A cone re-based along a morphism into its vertex. -/
noncomputable def coneExtend {J : Type w} [Category.{v} J] {D : J ⥤ Scheme.{u}} (c : Cone D)
    {X : Scheme.{u}} (e : X ⟶ c.pt) : (Functor.const J).obj X ⟶ D where
  app j := e ≫ c.π.app j
  naturality {j k} u := by
    refine (Category.id_comp _).trans ?_
    refine (congrArg (fun m ↦ e ≫ m) (c.w u)).symm.trans ?_
    exact (Category.assoc _ _ _).symm

/-- The leg of the re-based cone `AlgebraicGeometry.coneExtend c e` at `j` is `e` followed by the
leg of `c` at `j`. -/
@[simp]
lemma coneExtend_app {J : Type w} [Category.{v} J] {D : J ⥤ Scheme.{u}} (c : Cone D)
    {X : Scheme.{u}} (e : X ⟶ c.pt) (j : J) : (coneExtend c e).app j = e ≫ c.π.app j := rfl

/-- A cone re-based along an isomorphism of the vertex is limiting if the original was. -/
noncomputable def isLimitConeExtend {J : Type w} [Category.{v} J] {D : J ⥤ Scheme.{u}}
    {c : Cone D} (hc : IsLimit c) {X : Scheme.{u}} (e : X ≅ c.pt) :
    IsLimit (Cone.mk X (coneExtend c e.hom)) :=
  IsLimit.ofIsoLimit hc (Cone.ext e.symm fun _ ↦ (Iso.inv_hom_id_assoc e _).symm)

/-! ### The two guises of the overlap -/

namespace Scheme

variable (S : Scheme.{u})

/-- The action of `AlgebraicGeometry.Scheme.homOfLE` on the underlying point, at the spelling the
pointwise arguments below meet. -/
lemma homOfLE_coe {U V : S.Opens} (e : U ≤ V) (x : (U : Scheme.{u})) :
    ((S.homOfLE e) x).1 = x.1 :=
  congrArg (fun k : (U : Scheme.{u}) ⟶ S ↦ k x) (S.homOfLE_ι e)

/-- The image of `S.homOfLE e` for `e : U ≤ V` is the inverse image of `Y` when `U ⊆ Y` and `U`
is exactly the part of `V` inside `Y`. -/
private lemma opensRange_homOfLE_eq_preimage {U V Y : S.Opens} (e : U ≤ V) (hY : U ≤ Y)
    (h : ∀ x ∈ V, x ∈ Y → x ∈ U) : (S.homOfLE e).opensRange = V.ι ⁻¹ᵁ Y := by
  refine le_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨z, rfl⟩ := hx
    change ((S.homOfLE e) z).1 ∈ Y
    rw [S.homOfLE_coe]
    exact hY z.2
  · exact ⟨⟨x.1, h _ x.2 hx⟩, Subtype.ext (S.homOfLE_coe _ _)⟩

variable (V Y : S.Opens)

/-- **The inclusion of `V ⊓ Y` into `V` has image the inverse image of `Y`.** -/
lemma opensRange_homOfLE_inf_left :
    (S.homOfLE (inf_le_left : V ⊓ Y ≤ V)).opensRange = V.ι ⁻¹ᵁ Y :=
  opensRange_homOfLE_eq_preimage S _ inf_le_right fun _ hx hy ↦ ⟨hx, hy⟩

/-- **The inclusion of `V ⊓ Y` into `Y` has image the inverse image of `V`.**  This is the shape
of the hypothesis `hYr` of
`AlgebraicGeometry.preimage_opensRange_gluePairFunctorCone_right`. -/
lemma opensRange_homOfLE_inf_right :
    (S.homOfLE (inf_le_right : V ⊓ Y ≤ Y)).opensRange = Y.ι ⁻¹ᵁ V :=
  opensRange_homOfLE_eq_preimage S _ inf_le_left fun _ hx hy ↦ ⟨hy, hx⟩

/-- **The overlap in its two guises.**  The intersection `V ⊓ Y`, an open of the ambient scheme,
is isomorphic to `V.ι ⁻¹ᵁ Y`, an open of the scheme `V`. -/
noncomputable def overlapIso :
    ((V ⊓ Y : S.Opens) : Scheme.{u}) ≅ ((V.ι ⁻¹ᵁ Y : (V : Scheme.{u}).Opens) : Scheme.{u}) :=
  (S.homOfLE (inf_le_left : V ⊓ Y ≤ V)).isoOpensRange ≪≫
    (V : Scheme.{u}).isoOfEq (opensRange_homOfLE_inf_left S V Y)

/-- **The one equation the overlap isomorphism is used through.**  Composed with the inclusion of
the overlap into `V`, it is the inclusion of `V ⊓ Y` into `V`. -/
@[reassoc]
lemma overlapIso_hom_ι :
    (overlapIso S V Y).hom ≫ (V.ι ⁻¹ᵁ Y : (V : Scheme.{u}).Opens).ι =
      S.homOfLE (inf_le_left : V ⊓ Y ≤ V) := by
  rw [overlapIso, Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι,
    Scheme.Hom.isoOpensRange_hom_ι]

end Scheme

/-! ### The overlap cone, re-based onto the ambient scheme -/

section OverlapCone

variable {S : Scheme.{u}} (V Y : S.Opens) {J : Type w} [Category.{v} J] {D : J ⥤ Scheme.{u}}
  (p : (Functor.const J).obj ((V : Scheme.{u})) ⟶ D) (W : ∀ j, (D.obj j).Opens)
  (hW : ∀ ⦃j k : J⦄ (u : j ⟶ k), D.map u ⁻¹ᵁ W k = W j)
  (hT : ∀ j, (Cone.mk ((V : Scheme.{u})) p).π.app j ⁻¹ᵁ W j = V.ι ⁻¹ᵁ Y)

/-- **The cone over the overlap models, with vertex the overlap read as an open of the ambient
scheme.** -/
noncomputable def overlapCone :
    (Functor.const J).obj ((V ⊓ Y : S.Opens) : Scheme.{u}) ⟶ compatibleOpensDiagram D W hW :=
  coneExtend (compatibleOpensCone D (Cone.mk ((V : Scheme.{u})) p) W hW _ hT)
    (Scheme.overlapIso S V Y).hom

/-- The re-based overlap cone is limiting if the restricted cone was. -/
noncomputable def isLimitOverlapCone
    (hlim : IsLimit (compatibleOpensCone D (Cone.mk ((V : Scheme.{u})) p) W hW _ hT)) :
    IsLimit (Cone.mk (((V ⊓ Y : S.Opens) : Scheme.{u})) (overlapCone V Y p W hW hT)) :=
  isLimitConeExtend hlim (Scheme.overlapIso S V Y)

/-- **The re-based overlap cone is compatible with the inclusion of the overlap into `V`.**  This
is the hypothesis `hXW` of `AlgebraicGeometry.gluePairFunctorCone`. -/
lemma overlapCone_app_comp_ι (j : J) :
    (overlapCone V Y p W hW hT).app j ≫ (W j).ι =
      S.homOfLE (inf_le_left : V ⊓ Y ≤ V) ≫ p.app j := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun m ↦ (Scheme.overlapIso S V Y).hom ≫ m)
    (Scheme.Hom.resLE_comp_ι (p.app j) (hT j).ge)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun m ↦ m ≫ p.app j) (Scheme.overlapIso_hom_ι S V Y)

end OverlapCone

end AlgebraicGeometry
