module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible

/-!
# Injective and surjective maps of sheaves of sets

A map `φ : F ⟶ G` of sheaves of sets is *injective* if `φ : F(U) → G(U)` is injective for every
object `U`, and *surjective* if for every object `U` and every section `s ∈ G(U)` there is a
covering `{U i → U}` such that each restriction `s|_{U i}` is in the image of
`φ : F(U i) → G(U i)`. These are `CategoryTheory.Sheaf.IsLocallyInjective` (by
`CategoryTheory.Sheaf.isLocallyInjective_iff_injective`) and
`CategoryTheory.Sheaf.IsLocallySurjective`.

If `φ : F ⟶ G` is a map of presheaves and every object of `C` has a covering by objects on which
`φ` is bijective on sections, then `F^# ⟶ G^#` is an isomorphism.

## Main results

* `CategoryTheory.Presheaf.isLocallyInjective_of_hasEnoughObjects_injective` and
  `CategoryTheory.Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective`: a map of
  presheaves which is injective, respectively surjective, on the sections over the members of a
  covering of every object is locally injective, respectively locally surjective.
* `CategoryTheory.Presheaf.isIso_presheafToSheaf_map_of_hasEnoughObjects_bijective`: a map of
  presheaves which is bijective on the sections over the members of a covering of every object
  becomes an isomorphism after sheafification.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

universe w v' v u u'

variable {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D] {FD : D → D → Type*} {CD : D → Type w}
  [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
  (J : GrothendieckTopology C) {F G : Cᵒᵖ ⥤ D} (φ : F ⟶ G) {B : ObjectProperty C}

/-- A sieve contains a covering if it contains every arrow factoring through some arrow
`f : V ⟶ X` with `B V`, once every object has a covering by objects satisfying `B`. -/
private theorem mem_of_forall_comp_of_hasEnoughObjects {X : C} (S : Sieve X)
    (hB : J.HasEnoughObjects B)
    (h : ∀ ⦃V : C⦄ (f : V ⟶ X), B V → ∀ ⦃W : C⦄ (a : W ⟶ V), S (a ≫ f)) : S ∈ J X := by
  obtain ⟨I, V, f, hf, hBV⟩ := hB X
  refine J.superset_covering ?_ hf
  rintro W g hg
  obtain ⟨i, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  exact h (f i) (hBV i) a

/-- If every object of `C` has a covering by objects on which `φ` is injective on sections,
then `φ` is locally injective. -/
theorem isLocallyInjective_of_hasEnoughObjects_injective
    (hB : J.HasEnoughObjects B) (hinj : ∀ ⦃U : C⦄, B U → Function.Injective (φ.app (op U))) :
    IsLocallyInjective J φ where
  equalizerSieve_mem {X} x y h := by
    refine mem_of_forall_comp_of_hasEnoughObjects J _ hB fun V f hV W a => ?_
    have key : F.map f.op x = F.map f.op y :=
      hinj hV (by rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h])
    rw [Presheaf.equalizerSieve_apply, op_comp, F.map_comp, ConcreteCategory.comp_apply,
      ConcreteCategory.comp_apply, key]

/-- If every object of `C` has a covering by objects on which `φ` is surjective on sections,
then `φ` is locally surjective. -/
theorem isLocallySurjective_of_hasEnoughObjects_surjective
    (hB : J.HasEnoughObjects B) (hsurj : ∀ ⦃U : C⦄, B U → Function.Surjective (φ.app (op U))) :
    IsLocallySurjective J φ where
  imageSieve_mem {_} s :=
    mem_of_forall_comp_of_hasEnoughObjects J _ hB fun _ f hV _ a =>
      (imageSieve φ s).downward_closed (hsurj hV (G.map f.op s)) a

/-- Let `φ : F ⟶ G` be a map of presheaves on a site `(C, J)`. If every object of `C` has a
covering by objects `U` for which `φ` is bijective on sections over `U`, then the map of
sheafifications `F^# ⟶ G^#` is an isomorphism. -/
@[stacks 0H6Y "Bijectivity of a map of presheaves on a family of objects covering every
  object makes the induced map of sheafifications an isomorphism."]
theorem isIso_presheafToSheaf_map_of_hasEnoughObjects_bijective
    [HasWeakSheafify J D] [J.WEqualsLocallyBijective D]
    (hB : J.HasEnoughObjects (fun U => Function.Bijective (φ.app (op U)))) :
    IsIso ((presheafToSheaf J D).map φ) := by
  rw [← J.W_iff]
  have := isLocallyInjective_of_hasEnoughObjects_injective J φ hB fun _ h => h.injective
  have := isLocallySurjective_of_hasEnoughObjects_surjective J φ hB fun _ h => h.surjective
  exact J.W_of_isLocallyBijective φ

end CategoryTheory.Presheaf

namespace CategoryTheory

add_to_stacks 00WM "(1) A map of sheaves is injective, in the sense of 00WM (1) that it is
  injective on the sections over every object, exactly when it is locally injective in
  Mathlib's sense. Mathlib's class is stated for an arbitrary concrete category of values;
  this lemma is what identifies it with the pointwise-injectivity definition of 00WM (1)."
  CategoryTheory.Sheaf.isLocallyInjective_iff_injective

add_to_stacks 00WM "(2) The predicate of 00WM (2): every section of the target is locally, on
  a covering, in the image. Mathlib's single field `imageSieve_mem` is that condition."
  CategoryTheory.Sheaf.IsLocallySurjective

end CategoryTheory
