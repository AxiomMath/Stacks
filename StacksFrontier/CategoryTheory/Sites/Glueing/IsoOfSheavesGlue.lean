module

public import StacksFrontier.CategoryTheory.Sites.Glueing.MapsOfSheavesGlue

/-!
# Isomorphisms of sheaves glue

Stacks 04TQ says that a compatible family of *maps* of restricted sheaves on a covering glues
to a unique map; this file adds that the glued map is an *isomorphism* as soon as each member
of the family is one, with no further hypothesis. The inverses form a compatible family too, so
they glue; and the two composites restrict to identities on the covering, hence are identities
by the uniqueness half of 04TQ.

This is the statement that makes a property of a sheaf expressible as "isomorphic to a given
sheaf" local on the site: it is what turns a local identification of a sheaf with a
representable into a global one, which is the last step of a descent argument for
representability (for instance in Stacks 03RV).

## Main results

* `Stacks.SheafMapGluing.restrictHomAlong_eq` — `restrictHomAlong` written out, by `rfl`.
* `Stacks.SheafMapGluing.restrictHomAlong_id` and `Stacks.SheafMapGluing.restrictHomAlong_comp_hom`
  — restriction of
  a map of restricted sheaves is functorial in the map. These are the two laws
  `Stacks.SheafMapGluing.restrictHomAlong_comp` does not cover: it composes two *restrictions*,
    these
  compose two *maps*.
* `Stacks.SheafMapGluing.isIso_restrictHomAlong` — the restriction of an isomorphism is an
  isomorphism,
  with inverse the restriction of the inverse.
* `Stacks.SheafMapGluing.compatibleOnOverlaps_inv` — the inverses of a compatible family of
  isomorphisms
  form a compatible family.
* `Stacks.SheafMapGluing.iso_of_sheaves_glue` — **the main result**: a compatible family of
  isomorphisms
  of the restrictions of two sheaves to the members of a covering glues to a unique
  isomorphism of their restrictions to the covered object.

## Implementation notes

`Stacks.SheafMapGluing.restrictHomAlong` is conjugation by a component of the coherence isomorphism
`Stacks.SheafMapGluing.overPullbackOverMapPullbackIso` around the image of the map under
`CategoryTheory.GrothendieckTopology.overMapPullback`, so functoriality in the map is the
functoriality of `overMapPullback` plus one cancellation of the coherence isomorphism; both
laws are proved that way rather than componentwise.

The isomorphism is produced as an existence statement together with the restriction identities
rather than as a definition, because the glued map itself is already only characterized by
those identities (`Stacks.SheafMapGluing.maps_of_sheaves_glue` is an `∃!`), and the uniqueness
  clause is
carried along.

## References

* [Stacks Project, Tag 04TQ](https://stacks.math.columbia.edu/tag/04TQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.GrothendieckTopology Limits

namespace Stacks.SheafMapGluing

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
variable {A : Type*} [Category A]

/-! ### Restriction of a map of restricted sheaves is functorial in the map -/

/-- `Stacks.SheafMapGluing.restrictHomAlong` written out: conjugation of the image of the map under
`CategoryTheory.GrothendieckTopology.overMapPullback` by the coherence isomorphism.

This is stated as a lemma proved by `rfl` rather than used through the automatic equation
lemma of the definition, because `rw [restrictHomAlong]` mints the constant
`Stacks.SheafMapGluing.restrictHomAlong.eq_1` into whichever module performs the rewrite, and two
  modules
that both mint it are mutually unimportable under the module system. -/
theorem restrictHomAlong_eq {Z W : C} (g : W ⟶ Z) (F G : Sheaf J A)
    (φ : RestrictedHom J F G Z) :
    restrictHomAlong J g F G φ =
      ((overPullbackOverMapPullbackIso J g (A := A)).app F).inv ≫
        (J.overMapPullback A g).map φ ≫
          ((overPullbackOverMapPullbackIso J g (A := A)).app G).hom :=
  rfl

/-- Restricting the identity map gives the identity map. -/
theorem restrictHomAlong_id {Z W : C} (g : W ⟶ Z) (F : Sheaf J A) :
    restrictHomAlong J g F F (𝟙 ((J.overPullback A Z).obj F)) =
      𝟙 ((J.overPullback A W).obj F) := by
  have h : (J.overMapPullback A g).map (𝟙 ((J.overPullback A Z).obj F)) ≫
      ((overPullbackOverMapPullbackIso J g (A := A)).app F).hom =
      ((overPullbackOverMapPullbackIso J g (A := A)).app F).hom := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.id_comp _
  rw [restrictHomAlong_eq, h]
  exact ((overPullbackOverMapPullbackIso J g (A := A)).app F).inv_hom_id

/-- Restricting a composite of maps gives the composite of the restrictions. -/
theorem restrictHomAlong_comp_hom {Z W : C} (g : W ⟶ Z) (F G H : Sheaf J A)
    (φ : RestrictedHom J F G Z) (χ : RestrictedHom J G H Z) :
    restrictHomAlong J g F H (φ ≫ χ) =
      restrictHomAlong J g F G φ ≫ restrictHomAlong J g G H χ := by
  rw [restrictHomAlong_eq, restrictHomAlong_eq, restrictHomAlong_eq,
    CategoryTheory.Functor.map_comp]
  rw [Category.assoc, Category.assoc, Category.assoc,
    Iso.hom_inv_id_assoc ((overPullbackOverMapPullbackIso J g (A := A)).app G)]

/-- Restricting an isomorphism and then its inverse gives the identity. -/
private theorem restrictHomAlong_hom_inv_id {Z W : C} (g : W ⟶ Z) (F G : Sheaf J A)
    (φ : RestrictedHom J F G Z) [IsIso φ] :
    restrictHomAlong J g F G φ ≫ restrictHomAlong J g G F (inv φ) = 𝟙 _ := by
  rw [← restrictHomAlong_comp_hom, IsIso.hom_inv_id, restrictHomAlong_id]

/-- Restricting the inverse of an isomorphism and then the isomorphism gives the identity. -/
private theorem restrictHomAlong_inv_hom_id {Z W : C} (g : W ⟶ Z) (F G : Sheaf J A)
    (φ : RestrictedHom J F G Z) [IsIso φ] :
    restrictHomAlong J g G F (inv φ) ≫ restrictHomAlong J g F G φ = 𝟙 _ := by
  rw [← restrictHomAlong_comp_hom, IsIso.inv_hom_id, restrictHomAlong_id]

/-- **The restriction of an isomorphism is an isomorphism.** Its inverse is the restriction of
the inverse. -/
theorem isIso_restrictHomAlong {Z W : C} (g : W ⟶ Z) (F G : Sheaf J A)
    (φ : RestrictedHom J F G Z) [IsIso φ] :
    IsIso (restrictHomAlong J g F G φ) :=
  ⟨_, restrictHomAlong_hom_inv_id J g F G φ, restrictHomAlong_inv_hom_id J g F G φ⟩

/-- The restriction of the inverse of an isomorphism is the inverse of its restriction. -/
theorem restrictHomAlong_inv {Z W : C} (g : W ⟶ Z) (F G : Sheaf J A)
    (φ : RestrictedHom J F G Z) [IsIso φ] :
    restrictHomAlong J g G F (inv φ) =
      haveI := isIso_restrictHomAlong J g F G φ
      inv (restrictHomAlong J g F G φ) :=
  haveI := isIso_restrictHomAlong J g F G φ
  IsIso.eq_inv_of_hom_inv_id (restrictHomAlong_hom_inv_id J g F G φ)

/-! ### Gluing an isomorphism -/

variable [HasPullbacks C] (F G : Sheaf J A) (U : C)
variable {I : Type*} (Ui : I → C) (f : ∀ i, Ui i ⟶ U)

/-- **The inverses of a compatible family of isomorphisms are compatible.** Each side of the
compatibility equation is an isomorphism whose inverse is the restriction of the inverse, and
inverses of equal isomorphisms are equal. -/
theorem compatibleOnOverlaps_inv (φ : ∀ i, RestrictedHom J F G (Ui i))
    (hφ : CompatibleOnOverlaps J F G U Ui f φ) (hiso : ∀ i, IsIso (φ i)) :
    CompatibleOnOverlaps J G F U Ui f (fun i => haveI := hiso i; inv (φ i)) := by
  intro i j
  have := hiso i
  have := hiso j
  rw [restrictHomAlong_inv, restrictHomAlong_inv]
  have := isIso_restrictHomAlong J (pullback.fst (f i) (f j)) F G (φ i)
  have := isIso_restrictHomAlong J (pullback.snd (f i) (f j)) F G (φ j)
  exact IsIso.inv_eq_inv.2 (hφ i j)

/-- **Isomorphisms of sheaves glue.** Let `{f i : U i ⟶ U}` be a covering in `J` and let
`φ i : F|_{C/U i} ≅ G|_{C/U i}` be isomorphisms of the restrictions which agree on the
overlaps. Then there is a unique map `ψ : F|_{C/U} ⟶ G|_{C/U}` restricting to the `φ i`, and
it is an isomorphism.

The hypothesis is only that each `φ i` be an isomorphism: being an isomorphism is a local
property of a map of sheaves, so nothing further has to be checked. -/
theorem iso_of_sheaves_glue
    (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i))
    (hφ : CompatibleOnOverlaps J F G U Ui f φ) (hiso : ∀ i, IsIso (φ i)) :
    ∃! ψ : RestrictedHom J F G U,
      IsIso ψ ∧ ∀ i, restrictHomAlong J (f i) F G ψ = φ i := by
  obtain ⟨ψ, hψ⟩ := glued_existence J F G U Ui f hcov φ hφ
  obtain ⟨ψ', hψ'⟩ := glued_existence J G F U Ui f hcov
    (fun i => have := hiso i; inv (φ i)) (compatibleOnOverlaps_inv J F G U Ui f φ hφ hiso)
  have hleft : ψ ≫ ψ' = 𝟙 _ := by
    refine glued_uniqueness J F F U Ui f hcov _ _ fun i => ?_
    have := hiso i
    rw [restrictHomAlong_comp_hom, hψ i, hψ' i, IsIso.hom_inv_id, restrictHomAlong_id]
  have hright : ψ' ≫ ψ = 𝟙 _ := by
    refine glued_uniqueness J G G U Ui f hcov _ _ fun i => ?_
    have := hiso i
    rw [restrictHomAlong_comp_hom, hψ i, hψ' i, IsIso.inv_hom_id, restrictHomAlong_id]
  refine ⟨ψ, ⟨⟨ψ', hleft, hright⟩, hψ⟩, fun χ hχ => ?_⟩
  exact glued_uniqueness J F G U Ui f hcov χ ψ fun i => by rw [hχ.2 i, hψ i]

/-- **Isomorphisms of sheaves glue, packaged as an isomorphism.** -/
theorem exists_iso_of_sheaves_glue
    (hcov : Sieve.generate (Presieve.ofArrows Ui f) ∈ J U)
    (φ : ∀ i, RestrictedHom J F G (Ui i))
    (hφ : CompatibleOnOverlaps J F G U Ui f φ) (hiso : ∀ i, IsIso (φ i)) :
    ∃ e : (J.overPullback A U).obj F ≅ (J.overPullback A U).obj G,
      ∀ i, restrictHomAlong J (f i) F G e.hom = φ i := by
  obtain ⟨ψ, ⟨hψiso, hψ⟩, -⟩ := iso_of_sheaves_glue J F G U Ui f hcov φ hφ hiso
  exact ⟨@asIso _ _ _ _ ψ hψiso, hψ⟩

end Stacks.SheafMapGluing

end
