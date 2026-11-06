module

public import StacksFrontier.CategoryTheory.Sites.CharacterTwist

/-!
# The character twist along an isomorphism of the acted-on object

Let `C` be a site, let `i : W ≅ W'` be an isomorphism of objects of `C` and let a group `G` act
by automorphisms on both, compatibly with `i`.  A character `χ : G → ℤˣ` then twists the free
abelian sheaf on each, and the two twists agree:

`ℤ(χ)_W ≅ ℤ(χ)_{W'}`.

Both corepresent the `χ`-semi-invariant sections — over `W` on one side and over `W'` on the
other — and restricting sections along `i` identifies those two subgroups.  So the comparison is
again the Yoneda-style one.

This is what lets a twist formed on a geometric object be read on an isomorphic one, which is
needed whenever a construction is available only for a representable object while the twist of
interest is formed on something isomorphic to it.

## Main definitions

* `CategoryTheory.characterSectionsCongr` is the identification of the `χ`-semi-invariant
  sections over `W'` with those over `W`, by restriction along `i`.
* `CategoryTheory.characterTwistCongrComparison` is the comparison morphism
  `ℤ(χ)_{W'} ⟶ ℤ(χ)_W`, and `CategoryTheory.characterTwistCongr` the resulting isomorphism.

## Main results

* `CategoryTheory.mem_characterSections_map_hom`: restriction along `i` takes
  `χ`-semi-invariant sections over `W'` to `χ`-semi-invariant sections over `W`.
* `CategoryTheory.isIso_characterTwistCongrComparison`: **the comparison morphism is an
  isomorphism.**

## Implementation notes

Compatibility of the two actions with `i` is asked in the form
`(act g).asIso.hom ≫ i.hom = i.hom ≫ (act' g).asIso.hom`, which is the shape a geometric transport
produces.  It is not asked that `act'` be conjugate to `act` as a monoid homomorphism, which
would be the same demand in a less usable form.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
-/

@[expose] public noncomputable section

universe w v u

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C] {W W' : C} {G : Type w} [Group G]
    (i : W ≅ W') (act : G →* Aut W) (act' : G →* Aut W')
    (hact : ∀ g : G, (act g).asIso.hom ≫ i.hom = i.hom ≫ (act' g).asIso.hom) (χ : G →* ℤˣ)

include hact in
/-- **Restriction along `i` takes `χ`-semi-invariant sections over `W'` to `χ`-semi-invariant
sections over `W`.** -/
theorem mem_characterSections_map_hom (F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {s : F.obj (op W')} (hs : s ∈ characterSections W' act' χ F) :
    (F.map i.hom.op) s ∈ characterSections W act χ F := by
  intro g
  calc (F.map ((act g).asIso.hom).op) ((F.map i.hom.op) s)
      = (F.map (((act g).asIso.hom ≫ i.hom).op)) s := by
        rw [op_comp, F.map_comp]
        rfl
    _ = (F.map ((i.hom ≫ (act' g).asIso.hom).op)) s := by rw [hact g]
    _ = (F.map i.hom.op) ((F.map ((act' g).asIso.hom).op) s) := by
        rw [op_comp, F.map_comp]
        rfl
    _ = (F.map i.hom.op) ((χ g : ℤ) • s) := by rw [hs g]
    _ = (χ g : ℤ) • (F.map i.hom.op) s := by rw [map_zsmul]

include hact in
/-- Restriction along the inverse of `i` takes `χ`-semi-invariant sections back. -/
theorem mem_characterSections_map_inv (F : Cᵒᵖ ⥤ AddCommGrpCat.{v})
    {t : F.obj (op W)} (ht : t ∈ characterSections W act χ F) :
    (F.map i.inv.op) t ∈ characterSections W' act' χ F :=
  mem_characterSections_map_hom i.symm act' act (fun g => by
    rw [Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hact g, Iso.inv_hom_id_assoc]) χ F ht

/-- Restricting twice along `i` and its inverse is the identity on sections. -/
theorem map_inv_op_map_hom_op (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (s : F.obj (op W')) :
    (F.map i.inv.op) ((F.map i.hom.op) s) = s := by
  rw [show (F.map i.inv.op) ((F.map i.hom.op) s) = (F.map i.hom.op ≫ F.map i.inv.op) s from rfl,
    ← F.map_comp, ← op_comp, i.inv_hom_id, op_id, F.map_id]
  rfl

/-- Restricting twice along the inverse of `i` and `i` is the identity on sections. -/
theorem map_hom_op_map_inv_op (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) (t : F.obj (op W)) :
    (F.map i.hom.op) ((F.map i.inv.op) t) = t :=
  map_inv_op_map_hom_op i.symm F t

/-- **The `χ`-semi-invariant sections over `W'` are those over `W`**, by restriction along
`i`. -/
def characterSectionsCongr (F : Cᵒᵖ ⥤ AddCommGrpCat.{v}) :
    characterSections W' act' χ F ≃+ characterSections W act χ F where
  toFun s := ⟨(F.map i.hom.op) s.1, mem_characterSections_map_hom i act act' hact χ F s.2⟩
  invFun t := ⟨(F.map i.inv.op) t.1, mem_characterSections_map_inv i act act' hact χ F t.2⟩
  left_inv s := Subtype.ext (map_inv_op_map_hom_op i F s.1)
  right_inv t := Subtype.ext (map_hom_op_map_inv_op i F t.1)
  map_add' s s' := Subtype.ext (map_add (F.map i.hom.op).hom s.1 s'.1)

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}]

/-- The identification of the maps out of the two twists: both are the `χ`-semi-invariant
sections, over `W` on one side and over `W'` on the other. -/
def characterTwistCongrHomCompare (F : Sheaf J AddCommGrpCat.{v}) :
    (characterTwist W act χ J ⟶ F) ≃ (characterTwist W' act' χ J ⟶ F) :=
  (characterTwistHomEquiv W act χ J F).trans
    (((characterSectionsCongr i act act' hact χ F.obj).toEquiv.symm).trans
      (characterTwistHomEquiv W' act' χ J F).symm)

/-- The underlying section of the identification is the restriction along `i` of the one it
started from. -/
theorem characterTwistCongrHomCompare_section (F : Sheaf J AddCommGrpCat.{v})
    (u : characterTwist W act χ J ⟶ F) :
    ((characterTwistHomEquiv W' act' χ J F
        (characterTwistCongrHomCompare i act act' hact χ J F u)) : F.obj.obj (op W')) =
      (F.obj.map i.inv.op) ((characterTwistHomEquiv W act χ J F u) : F.obj.obj (op W)) := by
  show ((characterTwistHomEquiv W' act' χ J F ((characterTwistHomEquiv W' act' χ J F).symm
    ((characterSectionsCongr i act act' hact χ F.obj).symm
      (characterTwistHomEquiv W act χ J F u)))).1) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- **The comparison morphism `ℤ(χ)_{W'} ⟶ ℤ(χ)_W`.** -/
def characterTwistCongrComparison :
    characterTwist W' act' χ J ⟶ characterTwist W act χ J :=
  characterTwistCongrHomCompare i act act' hact χ J _ (𝟙 _)

/-- **The comparison morphism induces the identification of maps out of the two twists.** -/
theorem characterTwistCongrComparison_comp {F : Sheaf J AddCommGrpCat.{v}}
    (u : characterTwist W act χ J ⟶ F) :
    characterTwistCongrComparison i act act' hact χ J ≫ u =
      characterTwistCongrHomCompare i act act' hact χ J F u := by
  refine (characterTwistHomEquiv W' act' χ J F).injective (Subtype.ext ?_)
  have h3 : ((characterTwistHomEquiv W act χ J F u) : F.obj.obj (op W)) =
      (u.hom.app (op W)) ((characterTwistHomEquiv W act χ J (characterTwist W act χ J) (𝟙 _)) :
        (characterTwist W act χ J).obj.obj (op W)) := by
    rw [← characterTwistHomEquiv_comp W act χ J (𝟙 _) u, Category.id_comp]
  rw [characterTwistCongrHomCompare_section,
    characterTwistHomEquiv_comp W' act' χ J (characterTwistCongrComparison i act act' hact χ J) u,
    characterTwistCongrComparison, characterTwistCongrHomCompare_section, h3]
  exact NatTrans.naturality_apply u.hom i.inv.op _

/-- **The two twists agree.**  The comparison morphism is an isomorphism, because
precomposition with it is the bijection of `characterTwistCongrHomCompare` on maps into every
coefficient sheaf. -/
theorem isIso_characterTwistCongrComparison :
    IsIso (characterTwistCongrComparison i act act' hact χ J) := by
  obtain ⟨u, hu⟩ := (characterTwistCongrHomCompare i act act' hact χ J
    (characterTwist W' act' χ J)).surjective (𝟙 _)
  have h1 : characterTwistCongrComparison i act act' hact χ J ≫ u = 𝟙 _ := by
    rw [characterTwistCongrComparison_comp]
    exact hu
  refine ⟨u, h1, ?_⟩
  refine (characterTwistCongrHomCompare i act act' hact χ J
    (characterTwist W act χ J)).injective ?_
  simp only [← characterTwistCongrComparison_comp]
  rw [← Category.assoc, h1, Category.id_comp, Category.comp_id]

/-- **The twist of an object is the twist of an isomorphic one**, for compatible actions. -/
def characterTwistCongr :
    characterTwist W' act' χ J ≅ characterTwist W act χ J :=
  @asIso _ _ _ _ _ (isIso_characterTwistCongrComparison i act act' hact χ J)

end CategoryTheory

end
