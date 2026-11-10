module

public import StacksFrontier.AlgebraicGeometry.LimitApproxClose.OpenCoverGlue

/-!
# The cone of step (iii): the ambient scheme over the glued stages

Let `S` be covered by two opens `U₁` and `U₂`, let `Dx`, `Dy` be diagrams of schemes with cones
from `U₁` and from `U₂`, and let `Dw` be a common diagram mapping into both by `α` and `β` with
open-immersion components, compatibly with the inclusion of `U₁ ⊓ U₂` into each.  Then `S` is the
vertex of a cone over the diagram of glued stages `AlgebraicGeometry.gluePairFunctor α β`, and the
two legs of the glueing pull back along it to `U₁` and `U₂`.

This is the cone of step (iii) of the one-affine-open step of Tag 07RN; its limiting property
is `AlgebraicGeometry.isLimitGluePairFunctorCone`.  In the application `U₁` is the part already
approximated, `U₂` is the affine open being added, `Dx` is the system of its models, `Dy` the
system of spectra of the finite-type subalgebras, `Dw` the system of models of the overlap, and
the cone is the family of morphisms `S ⟶ V_k ⊔_{W_k} Spec A` that the Stacks proof gets from the
pushout square.

## Main results

* `AlgebraicGeometry.opens_eq_of_iso_preimage_eq`: two opens with the same inverse image along an
  isomorphism are equal.
* `AlgebraicGeometry.gluePairOpensDescApp`: the leg at one stage, read on the glueing of the two
  opens.
* `AlgebraicGeometry.gluePairFunctorCone`: the cone of step (iii).
* `AlgebraicGeometry.preimage_opensRange_gluePairFunctorCone_left` and
  `AlgebraicGeometry.preimage_opensRange_gluePairFunctorCone_right`: the two inverse-image
  conditions that `AlgebraicGeometry.isLimitOfCompatibleOpensPair` asks for.

## Implementation notes

Every statement about the cone is checked on the glueing of the two opens, where
`AlgebraicGeometry.Scheme.gluePair_jointly_surjective` applies, rather than on `S`, and is
transported to `S` by `AlgebraicGeometry.opens_eq_of_iso_preimage_eq`; working directly on `S`
would need the action of the inverse of the identifying isomorphism on points, which is not
reduced by anything.

The leg `AlgebraicGeometry.gluePairOpensDescApp` is `AlgebraicGeometry.Scheme.gluePairDesc` of
the two cone legs followed by the two legs of the target glueing.  Its single condition is the
two compatibilities together with `AlgebraicGeometry.Scheme.gluePair_condition`; a cover-based
construction would need a condition for every ordered pair of members instead.  Its defining
equations are stated by hand as simp lemmas: unfolding the definition with `rw` is not possible,
and the equations hold by the universal property rather than by reflexivity.

The cone `AlgebraicGeometry.gluePairFunctorCone` is obtained by composing with the inverse of the
isomorphism identifying `S` with that glueing.  Naturality is
`AlgebraicGeometry.Scheme.gluePair_hom_ext` against the two defining equations of the transition
morphism of the glued stages.

The two inverse-image conditions need one hypothesis beyond the cone data, which is the
geometric content of the step: the inverse image of the *other* diagram's open along the *other*
cone is the overlap.  Without it a point of `U₂` outside `U₁` could land on the first leg of the
glued stage, and the first leg would pull back to more than `U₁`.  Membership in an inverse image
is not syntactically membership of the image of the point, so each step that moves between the
two is a `change` up to definitional equality rather than a rewrite.

The index category is free — objects in `w`, morphisms in `v`, schemes in `u` — as for
`AlgebraicGeometry.gluePairFunctor`.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 01YT](https://stacks.math.columbia.edu/tag/01YT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe v w u

namespace AlgebraicGeometry

/-- Two opens with the same inverse image along an isomorphism are equal. -/
lemma opens_eq_of_iso_preimage_eq {X Y : Scheme.{u}} (e : X ≅ Y) {A B : Y.Opens}
    (h : e.hom ⁻¹ᵁ A = e.hom ⁻¹ᵁ B) : A = B := by
  have h1 : ∀ C : Y.Opens, e.inv ⁻¹ᵁ (e.hom ⁻¹ᵁ C) = C := fun C ↦ by
    rw [← Scheme.Hom.comp_preimage, e.inv_hom_id]
    rfl
  rw [← h1 A, h, h1 B]

section Cone

variable {J : Type w} [Category.{v} J] {Dw Dx Dy : J ⥤ Scheme.{u}} (α : Dw ⟶ Dx) (β : Dw ⟶ Dy)
  [∀ j, IsOpenImmersion (α.app j)] [∀ j, IsOpenImmersion (β.app j)]
  {S : Scheme.{u}} (U₁ U₂ : S.Opens)
  (pX : (Functor.const J).obj (U₁ : Scheme.{u}) ⟶ Dx)
  (pY : (Functor.const J).obj (U₂ : Scheme.{u}) ⟶ Dy)
  (pW : (Functor.const J).obj ((U₁ ⊓ U₂ : S.Opens) : Scheme.{u}) ⟶ Dw)
  (hXW : ∀ j, S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ pX.app j = pW.app j ≫ α.app j)
  (hYW : ∀ j, S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ pY.app j = pW.app j ≫ β.app j)

/-- The leg of the cone of step (iii) at one stage, read on the glueing of the two opens. -/
noncomputable def gluePairOpensDescApp
    (pW : (Functor.const J).obj ((U₁ ⊓ U₂ : S.Opens) : Scheme.{u}) ⟶ Dw)
    (hXW : ∀ j, S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ pX.app j = pW.app j ≫ α.app j)
    (hYW : ∀ j, S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂) ≫ pY.app j = pW.app j ≫ β.app j)
    (j : J) :
    Scheme.gluePair (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
        (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ⟶
      Scheme.gluePair (α.app j) (β.app j) :=
  Scheme.gluePairDesc _ _ (pX.app j ≫ Scheme.gluePairInl (α.app j) (β.app j))
    (pY.app j ≫ Scheme.gluePairInr (α.app j) (β.app j)) (by
      rw [← Category.assoc, ← Category.assoc, hXW j, hYW j, Category.assoc, Category.assoc,
        Scheme.gluePair_condition])

/-- The leg `AlgebraicGeometry.gluePairOpensDescApp` restricted to the first open of the glueing
is the first cone leg followed by the first leg of the target glueing. -/
@[simp]
lemma gluePairInl_gluePairOpensDescApp (j : J) :
    Scheme.gluePairInl (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
          (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ≫
        gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j =
      pX.app j ≫ Scheme.gluePairInl (α.app j) (β.app j) :=
  Scheme.gluePairInl_desc _ _ _ _ _

/-- The leg `AlgebraicGeometry.gluePairOpensDescApp` restricted to the second open of the glueing
is the second cone leg followed by the second leg of the target glueing. -/
@[simp]
lemma gluePairInr_gluePairOpensDescApp (j : J) :
    Scheme.gluePairInr (S.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁))
          (S.homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) ≫
        gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j =
      pY.app j ≫ Scheme.gluePairInr (α.app j) (β.app j) :=
  Scheme.gluePairInr_desc _ _ _ _ _

include hXW hYW in
/-- The legs `AlgebraicGeometry.gluePairOpensDescApp` are natural: the leg at `k` is the leg at
`j` followed by the transition morphism of the glued stages along `u : j ⟶ k`. -/
lemma gluePairOpensDescApp_naturality ⦃j k : J⦄ (u : j ⟶ k) :
    gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW k =
      gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j ≫
        Scheme.gluePairMap (Dw.map u) (Dx.map u) (Dy.map u)
          (α.naturality u).symm (β.naturality u).symm := by
  have hX : pX.app k = pX.app j ≫ Dx.map u := by simpa using pX.naturality u
  have hY : pY.app k = pY.app j ≫ Dy.map u := by simpa using pY.naturality u
  refine Scheme.gluePair_hom_ext _ _ ?_ ?_
  · rw [gluePairInl_gluePairOpensDescApp, ← Category.assoc,
      gluePairInl_gluePairOpensDescApp, Category.assoc,
      Scheme.gluePairInl_gluePairMap, ← Category.assoc, hX]
  · rw [gluePairInr_gluePairOpensDescApp, ← Category.assoc,
      gluePairInr_gluePairOpensDescApp, Category.assoc,
      Scheme.gluePairInr_gluePairMap, ← Category.assoc, hY]

variable (hS : U₁ ⊔ U₂ = ⊤)

/-- **The cone of step (iii).**  The ambient scheme over the diagram of glued stages. -/
noncomputable def gluePairFunctorCone :
    (Functor.const J).obj S ⟶ gluePairFunctor α β where
  app j := (Scheme.gluePairOpensIso S U₁ U₂ hS).inv ≫
    gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j
  naturality {j k} u := by
    refine (Category.id_comp _).trans ?_
    exact (congrArg (fun m ↦ (Scheme.gluePairOpensIso S U₁ U₂ hS).inv ≫ m)
      (gluePairOpensDescApp_naturality α β U₁ U₂ pX pY pW hXW hYW u)).trans
      (Category.assoc _ _ _).symm

/-- Precomposed with the isomorphism identifying the glueing of the two opens with `S`, the cone
`AlgebraicGeometry.gluePairFunctorCone` is the leg `AlgebraicGeometry.gluePairOpensDescApp`. -/
lemma gluePairOpensIso_hom_gluePairFunctorCone_app (j : J) :
    (Scheme.gluePairOpensIso S U₁ U₂ hS).hom ≫
        (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS).app j =
      gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j :=
  Iso.hom_inv_id_assoc _ _

include hS in
/-- **The cone restricted to the first open is the first given cone.**  Together with its
companion this is the leg equation that identifies the restricted cones of
`AlgebraicGeometry.isLimitOfCompatibleOpensPair` with the cones whose limiting property is
already known, through `AlgebraicGeometry.compatibleOpensDiagramIso`. -/
lemma ι_gluePairFunctorCone_app_left (j : J) :
    U₁.ι ≫ (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS).app j =
      pX.app j ≫ Scheme.gluePairInl (α.app j) (β.app j) := by
  rw [← Scheme.gluePairInl_gluePairOpensHom S U₁ U₂, ← Scheme.gluePairOpensIso_hom S U₁ U₂ hS,
    Category.assoc, gluePairOpensIso_hom_gluePairFunctorCone_app]
  exact gluePairInl_gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j

include hS in
/-- **The cone restricted to the second open is the second given cone.** -/
lemma ι_gluePairFunctorCone_app_right (j : J) :
    U₂.ι ≫ (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS).app j =
      pY.app j ≫ Scheme.gluePairInr (α.app j) (β.app j) := by
  rw [← Scheme.gluePairInr_gluePairOpensHom S U₁ U₂, ← Scheme.gluePairOpensIso_hom S U₁ U₂ hS,
    Category.assoc, gluePairOpensIso_hom_gluePairFunctorCone_app]
  exact gluePairInr_gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j

/-- The leg `AlgebraicGeometry.gluePairOpensDescApp` on a point of the first open of the glueing. -/
private lemma gluePairOpensDescApp_inl_apply (j : J) (p : (U₁ : Scheme.{u})) :
    gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j (Scheme.gluePairInl _ _ p) =
      Scheme.gluePairInl (α.app j) (β.app j) (pX.app j p) := by
  rw [← Scheme.Hom.comp_apply, gluePairInl_gluePairOpensDescApp, Scheme.Hom.comp_apply]

/-- The leg `AlgebraicGeometry.gluePairOpensDescApp` on a point of the second open of the
glueing. -/
private lemma gluePairOpensDescApp_inr_apply (j : J) (q : (U₂ : Scheme.{u})) :
    gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j (Scheme.gluePairInr _ _ q) =
      Scheme.gluePairInr (α.app j) (β.app j) (pY.app j q) := by
  rw [← Scheme.Hom.comp_apply, gluePairInr_gluePairOpensDescApp, Scheme.Hom.comp_apply]

include hS in
/-- **The first leg of the glued stages pulls back along the cone to the first open.**  This is
one of the two inverse-image conditions of `AlgebraicGeometry.isLimitOfCompatibleOpensPair`.

The hypothesis is the geometric content of step (iii): the inverse image, along the cone from the
*second* open, of the image of the second diagram is the overlap. -/
lemma preimage_opensRange_gluePairFunctorCone_left
    (hYr : ∀ j, pY.app j ⁻¹ᵁ (β.app j).opensRange = U₂.ι ⁻¹ᵁ U₁) (j : J) :
    (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS).app j ⁻¹ᵁ
        ((gluePairFunctorInl α β).app j).opensRange = U₁ := by
  refine opens_eq_of_iso_preimage_eq (Scheme.gluePairOpensIso S U₁ U₂ hS) ?_
  rw [← Scheme.Hom.comp_preimage, gluePairOpensIso_hom_gluePairFunctorCone_app,
    Scheme.gluePairOpensIso_hom, Scheme.preimage_gluePairOpensHom_left]
  refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := Scheme.gluePair_jointly_surjective _ _ t
    · exact ⟨p, rfl⟩
    · have h3 : gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j
          (Scheme.gluePairInr _ _ q) ∈
          (Scheme.gluePairInl (α.app j) (β.app j)).opensRange := ht
      rw [gluePairOpensDescApp_inr_apply] at h3
      have h4 : pY.app j q ∈ Scheme.gluePairInr (α.app j) (β.app j) ⁻¹ᵁ
        (Scheme.gluePairInl (α.app j) (β.app j)).opensRange := h3
      have hq : q.1 ∈ U₁ :=
        (hYr j).le ((Scheme.preimage_opensRange_gluePairInl (α.app j) (β.app j)).le h4)
      exact ⟨⟨q.1, hq⟩, Scheme.gluePairInl_eq_gluePairInr_of_val_eq S U₁ U₂ ⟨q.1, hq⟩ q rfl⟩
  · obtain ⟨p, rfl⟩ := ht
    change gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j (Scheme.gluePairInl _ _ p) ∈
      (Scheme.gluePairInl (α.app j) (β.app j)).opensRange
    rw [gluePairOpensDescApp_inl_apply]
    exact ⟨pX.app j p, rfl⟩

include hS in
/-- **The second leg of the glued stages pulls back along the cone to the second open.** -/
lemma preimage_opensRange_gluePairFunctorCone_right
    (hXr : ∀ j, pX.app j ⁻¹ᵁ (α.app j).opensRange = U₁.ι ⁻¹ᵁ U₂) (j : J) :
    (gluePairFunctorCone α β U₁ U₂ pX pY pW hXW hYW hS).app j ⁻¹ᵁ
        ((gluePairFunctorInr α β).app j).opensRange = U₂ := by
  refine opens_eq_of_iso_preimage_eq (Scheme.gluePairOpensIso S U₁ U₂ hS) ?_
  rw [← Scheme.Hom.comp_preimage, gluePairOpensIso_hom_gluePairFunctorCone_app,
    Scheme.gluePairOpensIso_hom, Scheme.preimage_gluePairOpensHom_right]
  refine le_antisymm (fun t ht ↦ ?_) (fun t ht ↦ ?_)
  · obtain ⟨p, rfl⟩ | ⟨q, rfl⟩ := Scheme.gluePair_jointly_surjective _ _ t
    · have h3 : gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j
          (Scheme.gluePairInl _ _ p) ∈
          (Scheme.gluePairInr (α.app j) (β.app j)).opensRange := ht
      rw [gluePairOpensDescApp_inl_apply] at h3
      have h4 : pX.app j p ∈ Scheme.gluePairInl (α.app j) (β.app j) ⁻¹ᵁ
        (Scheme.gluePairInr (α.app j) (β.app j)).opensRange := h3
      have hp : p.1 ∈ U₂ :=
        (hXr j).le ((Scheme.preimage_opensRange_gluePairInr (α.app j) (β.app j)).le h4)
      exact ⟨⟨p.1, hp⟩,
        (Scheme.gluePairInl_eq_gluePairInr_of_val_eq S U₁ U₂ p ⟨p.1, hp⟩ rfl).symm⟩
    · exact ⟨q, rfl⟩
  · obtain ⟨q, rfl⟩ := ht
    change gluePairOpensDescApp α β U₁ U₂ pX pY pW hXW hYW j (Scheme.gluePairInr _ _ q) ∈
      (Scheme.gluePairInr (α.app j) (β.app j)).opensRange
    rw [gluePairOpensDescApp_inr_apply]
    exact ⟨pY.app j q, rfl⟩

end Cone

end AlgebraicGeometry
