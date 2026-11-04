module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.Pushout.AffineGluing

/-!
# Sections of a pushout of presheafed spaces, and two consequences for schemes

[Stacks Project, Tag 0E25] asserts, for the pushout `Y ⨿_Z X` of a closed immersion
`i : Z ⟶ X` and an integral morphism `j : Z ⟶ Y`, that

```
𝒪_{Y ⨿_Z X} = b_* 𝒪_Y ×_{c_* 𝒪_Z} a_* 𝒪_X
```

as sheaves of rings, where `a`, `b` are the two canonical maps and `c = a ∘ i = b ∘ j`.  Read
on an open `U` of the pushout, that identity says exactly that the square of rings

```
Γ(Y ⨿_Z X, U) ---> Γ(Y, b ⁻¹ᵁ U)
      |                  |
      v                  v
Γ(X, a ⁻¹ᵁ U) ---> Γ(Z, c ⁻¹ᵁ U)
```

is cartesian.  This file proves that statement for an arbitrary colimit of a span of
*presheafed spaces* over `CommRingCat`, where it needs no hypothesis at all: it is Mathlib's
componentwise description of the structure presheaf of a colimit,
`AlgebraicGeometry.PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit`, read through the
duality `WalkingSpanᵒᵖ ≌ WalkingCospan`.

It also proves two scheme-level ingredients of the same tag which are independent of the
global gluing construction: that an affine morphism to a common target supplies the
affine-neighbourhood condition of [Stacks Project, Tag 0ECI], and that a morphism which is an
isomorphism on sections over the affine opens inside `U` is an isomorphism after restriction
to `U`.

## Main definitions

* `Stacks.Pushout.spanOpCone` is the cone over a `WalkingSpanᵒᵖ`-shaped diagram determined by
  its two nontrivial legs.

## Main results

* `Stacks.Pushout.isPullback_of_isLimit_spanOp`: a limit cone over a `WalkingSpanᵒᵖ`-shaped
  diagram has its two nontrivial legs forming a cartesian square.  This is the converse of
  `Stacks.Pushout.isLimitOfIsPullbackSpanOp`.
* `Stacks.Pushout.isPullback_app_colimit_span`: the sections of a colimit of a span of
  presheafed spaces over any open form a cartesian square.
* `Stacks.Pushout.exists_isAffineOpen_image_fibre_of_isAffineHom`: an affine morphism to a
  common target supplies the fibre condition of Situation 0ECI.
* `Stacks.Pushout.isIso_morphismRestrict_of_forall_isIso_app`: being an isomorphism on
  sections over the affine opens contained in `U` makes the restriction over `U` an
  isomorphism.

## Implementation notes

The two nontrivial maps of the cartesian square of sections are the images under
`AlgebraicGeometry.PresheafedSpace.componentwiseDiagram` of `WalkingSpan.Hom.fst` and
`WalkingSpan.Hom.snd`.  By the `@[simps]` equations of that definition they are
`(F.map _).c.app _` followed by transport along the equality of the two preimages of `U` in
the apex of the span, which is the shape in which Tag 0E25 states the identity.  No separate
unfolding lemma is provided for that reason.

`Stacks.Pushout.spanOpCone` is built by hand rather than transported along
`CategoryTheory.Limits.walkingSpanOpEquiv`, because the identity morphism of
`CategoryTheory.Limits.WidePushoutShape` is `WidePushoutShape.Hom.id`, reached through the
standalone `CategoryStruct` instance `WidePushoutShape.struct`, while `op_id` is stated for
the `Quiver` instance coming from `Category`.  The two spellings are definitionally but not
syntactically equal, so `simp [op_id]` does not fire on the identity case of the naturality
square; a `change` to `𝟙 (op i)`, checked at default transparency, is what repairs it.  No
transparency option is used anywhere in this file.

`Stacks.Pushout.isIso_morphismRestrict_of_forall_isIso_app` deliberately does *not* go through
`IsAffineHom (a ∣_ U)`: that instance is not found by `inferInstance` on this Mathlib
revision, and the proof of the corresponding tagged statement reaches for
`backward.isDefEq.respectTransparency false` because of it.  Applying
`AlgebraicGeometry.isIso_morphismRestrict_iff_isIso_app` to `a` itself on the affine open
`U.ι ''ᵁ V` of the target, and transporting with
`AlgebraicGeometry.morphismRestrictRestrict`, removes the need for both.

Nothing here carries a Stacks attribute.  The sections statement is proved for a colimit of
presheafed spaces, which is strictly weaker than the sheaf-level assertion of Tag 0E25 for the
pushout *of schemes*: that needs the pushout to be a scheme, which is the global gluing step
and is not done.  Claiming the tag would overstate what is proved, as in
`StacksFrontier.AlgebraicGeometry.Pushout.IntegralFibre`.

## References

* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.Pushout

/-! ### Cones over a diagram indexed by `WalkingSpanᵒᵖ` -/

/-- The cone, over a diagram indexed by `WalkingSpanᵒᵖ`, determined by a pair of morphisms to
the two nonzero objects whose composites to the zero object agree.  The leg at
`WalkingSpan.zero` is that common composite. -/
def spanOpCone {C : Type*} [Category C] {D : WalkingSpanᵒᵖ ⥤ C} {W : C}
    (h₁ : W ⟶ D.obj (op WalkingSpan.left)) (h₂ : W ⟶ D.obj (op WalkingSpan.right))
    (hw : h₁ ≫ D.map WalkingSpan.Hom.fst.op = h₂ ≫ D.map WalkingSpan.Hom.snd.op) :
    Cone D where
  pt := W
  π :=
    { app := fun k =>
        match k with
        | ⟨none⟩ => h₁ ≫ D.map WalkingSpan.Hom.fst.op
        | ⟨some WalkingPair.left⟩ => h₁
        | ⟨some WalkingPair.right⟩ => h₂
      naturality := by
        rintro ⟨i⟩ ⟨k⟩ ⟨_ | p⟩
        · change _ ≫ _ = _ ≫ D.map (𝟙 (op i))
          simp
        · cases p
          · exact (Category.id_comp _).trans rfl
          · exact (Category.id_comp _).trans hw }

/-- **The legs of a limit cone over a `WalkingSpanᵒᵖ`-shaped diagram form a cartesian
square.**  This is the converse of `Stacks.Pushout.isLimitOfIsPullbackSpanOp`. -/
theorem isPullback_of_isLimit_spanOp {C : Type*} [Category C] {D : WalkingSpanᵒᵖ ⥤ C}
    {c : Cone D} (hc : IsLimit c) :
    IsPullback (c.π.app (op WalkingSpan.left)) (c.π.app (op WalkingSpan.right))
      (D.map WalkingSpan.Hom.fst.op) (D.map WalkingSpan.Hom.snd.op) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    ((c.w WalkingSpan.Hom.fst.op).trans (c.w WalkingSpan.Hom.snd.op).symm)
    (fun s => hc.lift (spanOpCone s.fst s.snd s.condition))
    (fun s => hc.fac _ (op WalkingSpan.left)) (fun s => hc.fac _ (op WalkingSpan.right)) ?_)
  intro s m hm₁ hm₂
  refine hc.uniq (spanOpCone s.fst s.snd s.condition) m ?_
  rintro ⟨_ | (_ | _)⟩
  · rw [← c.w WalkingSpan.Hom.fst.op]
    exact (Category.assoc m _ _).symm.trans (congrArg (· ≫ D.map WalkingSpan.Hom.fst.op) hm₁)
  · exact hm₁
  · exact hm₂

/-! ### Sections of a colimit of presheafed spaces -/

/-- The leg of `Stacks.Pushout.colimitSectionsCone` at an index is the structure-sheaf
component of the corresponding colimit inclusion. -/
lemma colimitSectionsCone_app {J : Type*} [Category J]
    [HasColimitsOfShape J TopCat.{u}] [HasLimitsOfShape Jᵒᵖ CommRingCat.{u}]
    (F : J ⥤ PresheafedSpace CommRingCat.{u}) [HasColimit F]
    (U : Opens (colimit F).carrier) (k : J) :
    (colimitSectionsCone F U).π.app (op k) = (colimit.ι F k).c.app (op U) := by
  rw [colimitSectionsCone_π, PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]

/-- **The structure sheaf of a pushout of presheafed spaces is a fibre product.**  For a span
`X ⟵ Z ⟶ Y` of presheafed spaces over `CommRingCat` and an open `U` of the colimit, the
square formed by the two structure-sheaf components of the colimit inclusions and the two maps
of the componentwise diagram is cartesian.

Read in the orientation of [Stacks Project, Tag 0E25] this is the identity
`𝒪_{Y ⨿_Z X} = b_* 𝒪_Y ×_{c_* 𝒪_Z} a_* 𝒪_X` of sheaves of rings, evaluated on `U`; use
`CategoryTheory.IsPullback.flip` to exchange the two legs. -/
theorem isPullback_app_colimit_span {Z X Y : PresheafedSpace CommRingCat.{u}}
    (i : Z ⟶ X) (j : Z ⟶ Y) (U : Opens (colimit (span i j)).carrier) :
    IsPullback ((colimit.ι (span i j) WalkingSpan.left).c.app (op U))
      ((colimit.ι (span i j) WalkingSpan.right).c.app (op U))
      ((PresheafedSpace.componentwiseDiagram (span i j) U).map WalkingSpan.Hom.fst.op)
      ((PresheafedSpace.componentwiseDiagram (span i j) U).map WalkingSpan.Hom.snd.op) := by
  have h := isPullback_of_isLimit_spanOp (colimitSectionsConeIsLimit (span i j) U)
  rwa [colimitSectionsCone_app, colimitSectionsCone_app] at h

/-! ### Two scheme-level ingredients of Tag 0E25 -/

/-- **An affine morphism supplies the fibre condition of Situation 0ECI.**  If `a : X ⟶ P` is
affine and the square `i`, `j`, `a`, `b` commutes, then for every `y : Y` the image under `i`
of the fibre of `j` over `y` lies in a single affine open of `X`, namely the preimage under
`a` of an affine open neighbourhood of `b y`. -/
theorem exists_isAffineOpen_image_fibre_of_isAffineHom {X Y Z P : Scheme.{u}} {i : Z ⟶ X}
    {j : Z ⟶ Y} {a : X ⟶ P} {b : Y ⟶ P} [IsAffineHom a] (h : CommSq i j a b) (y : Y) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ z : Z, j z = y → i z ∈ U := by
  obtain ⟨V, hV, hy, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show b y ∈ (⊤ : P.Opens) from trivial)
  refine ⟨a ⁻¹ᵁ V, hV.preimage a, fun z hz ↦ ?_⟩
  change a (i z) ∈ V
  rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply, hz]
  exact hy

/-- **An affine morphism which is an isomorphism on sections over an open is an isomorphism
there.**  If `a : X ⟶ P` is affine and `a.app W` is an isomorphism for every affine open
`W ≤ U`, then `a ∣_ U` is an isomorphism.

Being an isomorphism is Zariski-local at the target, so it suffices to check it after
restricting further to an affine open `V` of `U`; there
`AlgebraicGeometry.morphismRestrictRestrict` identifies `(a ∣_ U) ∣_ V` with
`a ∣_ (U.ι ''ᵁ V)`, and `AlgebraicGeometry.isIso_morphismRestrict_iff_isIso_app` turns that
into the hypothesis at `U.ι ''ᵁ V`. -/
theorem isIso_morphismRestrict_of_forall_isIso_app {X P : Scheme.{u}} (a : X ⟶ P)
    [IsAffineHom a] (U : P.Opens)
    (h : ∀ W : P.Opens, IsAffineOpen W → W ≤ U → IsIso (a.app W)) :
    IsIso (a ∣_ U) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro x
  obtain ⟨V, hV, hx, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : U.toScheme.Opens) from trivial)
  refine ⟨V, hx, ?_⟩
  have hVP : IsAffineOpen (U.ι ''ᵁ V) := hV.image_of_isOpenImmersion U.ι
  have hle : U.ι ''ᵁ V ≤ U := by simpa using U.ι.image_le_opensRange V
  have : IsIso (a ∣_ (U.ι ''ᵁ V)) :=
    (isIso_morphismRestrict_iff_isIso_app a hVP).mpr (h _ hVP hle)
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict a U V)).mpr this

end Stacks.Pushout

end
