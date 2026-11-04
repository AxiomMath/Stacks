module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Transporting the sheaf condition for one presheaf and one presieve

Every transport of sheaves along an equivalence of sites available in Mathlib is a statement
about *sheaf categories*: `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv` and its relatives
carry a sheaf to a sheaf.  None of them can be used to *establish* a sheaf condition, because they
presuppose it.  This file supplies the elementary statements that can: the sheaf condition
`CategoryTheory.Presieve.IsSheafFor`, for a single presheaf and a single presieve, is transported

* along an equivalence of categories,
* between a category and a slice of it,
* along an isomorphism of the object the presieve lives on.

The three together move a sheaf condition across a localization equivalence `C/X ≌ D` — the shape
in which Stacks 06W0 identifies the localization of the site of a category fibred in groupoids at
an object with the big site of the scheme below it.

## Main results

* `CategoryTheory.Presieve.isSheafFor_map_iff_of_isEquivalence`: for `F : C ⥤ D` an equivalence of
  categories, the sheaf condition for a presheaf `P` on `D` and the image presieve `R.map F` is
  the sheaf condition for the restricted presheaf `F.op ⋙ P` and `R`.
* `CategoryTheory.Presieve.isSheafFor_functorPullback_overForget_iff`: the sheaf condition for a
  presheaf `P` on `C` and a presieve `R` on `W.left` is the sheaf condition, on the slice
  `Over X`, for the restricted presheaf and the presieve of arrows into `W` lying over `R`.
* `CategoryTheory.Presieve.isSheafFor_ofArrows_comp_iso_iff`: the sheaf condition for a family of
  arrows is unchanged by composing them with an isomorphism of their common target.

## Implementation notes

Each statement is proved first for a family of arrows and then, where it is useful, for an
arbitrary presieve by way of `CategoryTheory.Presieve.exists_eq_ofArrows`.  For a family of arrows
`CategoryTheory.Presieve.isSheafFor_arrows_iff` reduces the sheaf condition to the existence of a
unique amalgamation of every compatible family of elements, and the amalgamation statements on the
two sides of each transport are *the same statement*: `F.op ⋙ P` has the same sections and the
same restriction maps as `P`, and the forgetful functor of a slice has the same sections as the
presheaf it restricts.  So the only thing to prove each time is that the two compatibility
conditions agree, and that is what the `Compatible` lemmas below do.
-/

@[expose] public section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Presieve

open Category Opposite

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-! ### Along an equivalence of categories -/

section Equivalence

variable (F : C ⥤ D) [F.IsEquivalence] (P : Dᵒᵖ ⥤ Type w)

/-- **Compatibility is unchanged by an equivalence of categories.**  A family of elements of a
presheaf `P` on `D`, indexed by the images `F.map (f i)` of a family of arrows of `C`, is
compatible exactly when it is compatible as a family of elements of the restricted presheaf
`F.op ⋙ P` indexed by the `f i` themselves.

One direction is functoriality.  The other needs all three properties of an equivalence: an
arbitrary pair of arrows of `D` into the images `F.obj (Y i)` is, up to the isomorphism
`F.obj (F.objPreimage Z) ≅ Z`, the image of a pair of arrows of `C` (fullness and essential
surjectivity), the relation between them descends (faithfulness), and restriction along that
isomorphism is injective. -/
theorem Arrows.compatible_map_iff {X : C} {I : Type*} {Y : I → C} (f : ∀ i, Y i ⟶ X)
    (x : ∀ i, P.obj (op (F.obj (Y i)))) :
    Arrows.Compatible P (fun i ↦ F.map (f i)) x ↔ Arrows.Compatible (F.op ⋙ P) f x := by
  refine ⟨fun hx i j Z gi gj h ↦ hx i j (F.obj Z) (F.map gi) (F.map gj)
    (by simp only [← F.map_comp, h]), fun hx i j Z gi gj h ↦ ?_⟩
  set ι : F.obj (F.objPreimage Z) ≅ Z := F.objObjPreimageIso Z
  have hgi : F.map (F.preimage (ι.hom ≫ gi)) = ι.hom ≫ gi := F.map_preimage _
  have hgj : F.map (F.preimage (ι.hom ≫ gj)) = ι.hom ≫ gj := F.map_preimage _
  have key : F.preimage (ι.hom ≫ gi) ≫ f i = F.preimage (ι.hom ≫ gj) ≫ f j :=
    F.map_injective (by rw [F.map_comp, F.map_comp, hgi, hgj, assoc, assoc, h])
  have e : P.map (F.map (F.preimage (ι.hom ≫ gi))).op (x i) =
      P.map (F.map (F.preimage (ι.hom ≫ gj))).op (x j) :=
    hx i j _ (F.preimage (ι.hom ≫ gi)) (F.preimage (ι.hom ≫ gj)) key
  have hbij : Function.Bijective (P.map ι.hom.op) := by
    rw [← isIso_iff_bijective]
    infer_instance
  refine hbij.1 ?_
  simpa only [hgi, hgj, op_comp, P.map_comp, types_comp_apply] using e

/-- **The sheaf condition for a family of arrows is transported along an equivalence of
categories.**  For `F : C ⥤ D` an equivalence and `P` a presheaf on `D`, the sheaf condition for
`P` and the family of images `F.map (f i)` is the sheaf condition for the restricted presheaf
`F.op ⋙ P` and the family `f i`. -/
theorem isSheafFor_ofArrows_map_iff_of_isEquivalence {X : C} {I : Type*} {Y : I → C}
    (f : ∀ i, Y i ⟶ X) :
    IsSheafFor P (ofArrows (fun i ↦ F.obj (Y i)) fun i ↦ F.map (f i)) ↔
      IsSheafFor (F.op ⋙ P) (ofArrows Y f) := by
  rw [isSheafFor_arrows_iff, isSheafFor_arrows_iff]
  exact ⟨fun h x hx ↦ h x ((Arrows.compatible_map_iff F P f x).2 hx),
    fun h x hx ↦ h x ((Arrows.compatible_map_iff F P f x).1 hx)⟩

/-- **The sheaf condition for a presieve is transported along an equivalence of categories.**  For
`F : C ⥤ D` an equivalence and `P` a presheaf on `D`, the sheaf condition for `P` and the image
presieve `R.map F` is the sheaf condition for the restricted presheaf `F.op ⋙ P` and `R`. -/
theorem isSheafFor_map_iff_of_isEquivalence {X : C} (R : Presieve X) :
    IsSheafFor P (R.map F) ↔ IsSheafFor (F.op ⋙ P) R := by
  obtain ⟨I, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [map_ofArrows]
  exact isSheafFor_ofArrows_map_iff_of_isEquivalence F P f

end Equivalence

/-! ### Between a category and a slice of it -/

section Slice

variable {X : C} (P : Cᵒᵖ ⥤ Type w)

/-- **Compatibility is unchanged by passing to a slice.**  A family of elements of a presheaf `P`
on `C`, indexed by a family of arrows `g i : Z i ⟶ W` of `Over X`, is compatible exactly when it
is compatible as a family of elements of the restriction of `P` to `Over X` indexed by the same
family.

Both conditions quantify over the pairs of arrows that agree after composition into `W.left`: an
object of `Over X` carrying such a pair of arrows of `Over X` is determined by the composite,
because `W` is an object over `X`, and conversely a pair of arrows of `C` has a unique such source
over `X`. -/
theorem Arrows.compatible_over_iff {W : Over X} {I : Type*} {Z : I → Over X} (g : ∀ i, Z i ⟶ W)
    (x : ∀ i, P.obj (op (Z i).left)) :
    Arrows.Compatible ((Over.forget X).op ⋙ P) g x ↔
      Arrows.Compatible P (fun i ↦ (g i).left) x := by
  refine ⟨fun hx i j T ai aj h ↦ ?_, fun hx i j T ai aj h ↦
    hx i j T.left ai.left aj.left (by simpa using congrArg CommaMorphism.left h)⟩
  have h' : ai ≫ (g i).left = aj ≫ (g j).left := h
  have haj : aj ≫ (Z j).hom = (Over.mk (ai ≫ (Z i).hom)).hom := by
    show aj ≫ (Z j).hom = ai ≫ (Z i).hom
    rw [← Over.w (g i), ← Over.w (g j), ← assoc, ← assoc, h']
  exact hx i j (Over.mk (ai ≫ (Z i).hom)) (Over.homMk ai rfl) (Over.homMk aj haj)
    (by ext; simpa using h)

/-- The arrows of `Over X` into `W` that lie over a family of arrows into `W.left` are exactly the
arrows of `Over X` whose image under the forgetful functor is in the family. -/
theorem functorPullback_overForget_ofArrows (W : Over X) {I : Type*} {Y : I → C}
    (f : ∀ i, Y i ⟶ W.left) :
    functorPullback (X := W) (Over.forget X) (ofArrows Y f) =
      ofArrows (fun i ↦ Over.mk (f i ≫ W.hom))
        fun i ↦ (Over.homMk (f i) rfl : Over.mk (f i ≫ W.hom) ⟶ W) := by
  refine (Presieve.overEquiv W).injective ?_
  show map (Over.forget X) _ = map (Over.forget X) _
  rw [map_functorPullback_overForget, map_ofArrows]
  rfl

/-- **The sheaf condition for a family of arrows is transported between a category and a slice of
it.**  For a family of arrows `g i : Z i ⟶ W` of `Over X`, the sheaf condition on `Over X` for the
restriction of a presheaf `P` on `C` and that family is the sheaf condition for `P` and the family
of underlying arrows of `C`. -/
theorem isSheafFor_ofArrows_over_iff {W : Over X} {I : Type*} {Z : I → Over X}
    (g : ∀ i, Z i ⟶ W) :
    IsSheafFor ((Over.forget X).op ⋙ P) (ofArrows Z g) ↔
      IsSheafFor P (ofArrows (fun i ↦ (Z i).left) fun i ↦ (g i).left) := by
  rw [isSheafFor_arrows_iff, isSheafFor_arrows_iff]
  exact ⟨fun h x hx ↦ h x ((Arrows.compatible_over_iff P g x).2 hx),
    fun h x hx ↦ h x ((Arrows.compatible_over_iff P g x).1 hx)⟩

/-- **The sheaf condition for a presieve is transported between a category and a slice of it.**
For `W` an object of `Over X` and `R` a presieve on `W.left`, the sheaf condition for a presheaf
`P` on `C` and `R` is the sheaf condition, on `Over X`, for the restriction of `P` and the
presieve of arrows into `W` lying over `R`. -/
theorem isSheafFor_functorPullback_overForget_iff (W : Over X) (R : Presieve W.left) :
    IsSheafFor ((Over.forget X).op ⋙ P) (functorPullback (X := W) (Over.forget X) R) ↔
      IsSheafFor P R := by
  obtain ⟨I, Y, f, rfl⟩ := R.exists_eq_ofArrows
  rw [functorPullback_overForget_ofArrows, isSheafFor_ofArrows_over_iff]
  rfl

end Slice

/-! ### Along an isomorphism of the target -/

/-- **The sheaf condition for a family of arrows only depends on the isomorphism class of their
common target.**  Composing a family of arrows with an isomorphism of their target does not change
the sheaf condition for it.

This is the target-side counterpart of `CategoryTheory.Presieve.isSheafFor_ofArrows_comp_iff`,
which does the same for isomorphisms of the sources. -/
theorem isSheafFor_ofArrows_comp_iso_iff (P : Cᵒᵖ ⥤ Type w) {X X' : C} (e : X ≅ X') {I : Type*}
    (Y : I → C) (f : ∀ i, Y i ⟶ X) :
    IsSheafFor P (ofArrows Y fun i ↦ f i ≫ e.hom) ↔ IsSheafFor P (ofArrows Y f) := by
  have h := isSheafFor_pullback_iff P (Sieve.ofArrows Y fun i ↦ f i ≫ e.hom) e.hom
  rw [Sieve.pullback_ofArrows_of_iso] at h
  simp only [assoc, Iso.hom_inv_id, comp_id] at h
  rw [Sieve.ofArrows, Sieve.ofArrows, ← isSheafFor_iff_generate, ← isSheafFor_iff_generate] at h
  exact h.symm

end CategoryTheory.Presieve

end
