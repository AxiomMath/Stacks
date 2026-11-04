module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallyBijective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sheafification on sites with essentially small slices

Let `(C, J)` be a site whose objects and morphisms live in arbitrary universes, and suppose that
for every object `X` the slice category `Over X` is essentially `u`-small. This file shows that
presheaves on `C` of abelian groups in `Type u` admit a sheafification, and that the morphisms
of such presheaves which become isomorphisms after sheafification are exactly the locally
bijective ones.

## Main results

In the namespace `CategoryTheory.GrothendieckTopology`:

* `hasSheafify_addCommGrpCat_of_essentiallySmall_over`: abelian presheaves with sections in
  `Type u` can be sheafified, by a left exact functor.
* `wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over`: for those presheaves the
  weak equivalences are the locally bijective morphisms.

## Implementation notes

The sheafification is the plus construction `P⁺(X) = colim_{S ∈ (J.Cover X)ᵒᵖ} H⁰(S, P)`
applied twice, and the only issue is that it involves `u`-small data:

* a sieve on `X` is determined by the isomorphism classes of objects of `Over X` it contains,
  so the covering sieves of `X` form a `u`-small poset
  (`CategoryTheory.GrothendieckTopology.small_cover_of_essentiallySmall_over`), over whose
  opposite colimits of abelian groups exist and are computed on underlying sets, this poset being
  filtered;
* a compatible family of sections over a covering sieve `S` is determined by its values on
  representatives of the isomorphism classes of `Over X`, since an isomorphism over `X` gives a
  relation of `S` identifying the two values; so the multiequalizers defining `H⁰(S, P)` exist
  (`CategoryTheory.GrothendieckTopology.hasMultiequalizer_index_addCommGrpCat`).

The library's proofs that the map to the plus construction is locally injective and locally
surjective are stated for presheaves of types at the universe of the site; their arguments run
unchanged for abelian presheaves once these colimits and multiequalizers are available.

## References

* [Stacks Project, Tag 00W1](https://stacks.math.columbia.edu/tag/00W1)
* [Stacks Project, Tag 00WM](https://stacks.math.columbia.edu/tag/00WM)
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type v} [Category.{w} C]

/-- A sieve contains `f` if and only if it contains the structure map of any object of the slice
isomorphic to `Over.mk f`. -/
private theorem sieve_apply_iff_of_iso {X Y : C} (R : Sieve X) {f : Y ⟶ X} {Z : Over X}
    (i : Over.mk f ≅ Z) : R f ↔ R Z.hom := by
  constructor
  · intro hf
    rw [← Over.w i.inv]
    exact R.downward_closed hf _
  · intro hf
    have := R.downward_closed hf i.hom.left
    rwa [Over.w i.hom] at this

/-- The sieves on an object whose slice is essentially `u`-small form a `u`-small type: a sieve
is determined by the isomorphism classes of objects of the slice that it contains. -/
theorem Sieve.small_of_essentiallySmall_over (X : C) [EssentiallySmall.{u} (Over X)] :
    Small.{u} (Sieve X) := by
  let e := equivSmallModel.{u} (Over X)
  refine small_of_injective
    (f := fun S : Sieve X => {Z : SmallModel.{u} (Over X) | S (e.inverse.obj Z).hom}) ?_
  intro S T h
  have key : ∀ (R : Sieve X) {Y : C} (f : Y ⟶ X),
      R f ↔ R (e.inverse.obj (e.functor.obj (Over.mk f))).hom :=
    fun R Y f => sieve_apply_iff_of_iso R (e.unitIso.app _)
  ext Y f
  rw [key S, key T]
  exact Set.ext_iff.1 h _

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

/-- The covering sieves of an object whose slice is essentially `u`-small form a `u`-small
type. -/
theorem small_cover_of_essentiallySmall_over (X : C) [EssentiallySmall.{u} (Over X)] :
    Small.{u} (J.Cover X) :=
  have := Sieve.small_of_essentiallySmall_over.{u} X
  small_of_injective (f := fun S : J.Cover X => (S : Sieve X)) fun _ _ h => Subtype.ext h

/-- The opposite of the poset of covering sieves of an object whose slice is essentially
`u`-small is an essentially `u`-small category. -/
theorem essentiallySmall_cover_op_of_essentiallySmall_over (X : C)
    [EssentiallySmall.{u} (Over X)] : EssentiallySmall.{u} (J.Cover X)ᵒᵖ :=
  have := J.small_cover_of_essentiallySmall_over.{u} X
  inferInstance

/-- On an object whose slice is essentially `u`-small, colimits over the opposite of the poset of
covering sieves exist in the category of abelian groups in `Type u`. -/
theorem hasColimitsOfShape_cover_op_addCommGrpCat (X : C) [EssentiallySmall.{u} (Over X)] :
    HasColimitsOfShape (J.Cover X)ᵒᵖ AddCommGrpCat.{u} :=
  have := J.essentiallySmall_cover_op_of_essentiallySmall_over.{u} X
  hasColimitsOfShape_of_essentiallySmall _ _

/-- On an object whose slice is essentially `u`-small, the forgetful functor from abelian groups
in `Type u` preserves colimits over the opposite of the poset of covering sieves, this category
being filtered and essentially `u`-small. -/
theorem preservesColimitsOfShape_cover_op_forget_addCommGrpCat (X : C)
    [EssentiallySmall.{u} (Over X)] :
    PreservesColimitsOfShape (J.Cover X)ᵒᵖ (forget AddCommGrpCat.{u}) :=
  have := J.essentiallySmall_cover_op_of_essentiallySmall_over.{u} X
  have : IsFiltered (SmallModel.{u} (J.Cover X)ᵒᵖ) :=
    IsFiltered.of_equivalence (equivSmallModel.{u} (J.Cover X)ᵒᵖ)
  preservesColimitsOfShape_of_equiv (equivSmallModel.{u} (J.Cover X)ᵒᵖ).symm _

/-- On an object whose slice is essentially `u`-small, the multiequalizer of a presheaf of
abelian groups in `Type u` over a covering sieve exists: a compatible family of sections is
determined by its values on representatives of the isomorphism classes of the slice. -/
theorem hasMultiequalizer_index_addCommGrpCat {X : C} [EssentiallySmall.{u} (Over X)]
    (S : J.Cover X) (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : HasMultiequalizer (S.index P) := by
  rw [HasMultiequalizer, AddCommGrpCat.hasLimit_iff_small_sections]
  let e := equivSmallModel.{u} (Over X)
  refine small_of_injective (f := fun s (Z : SmallModel.{u} (Over X))
    (h : S.1 (e.inverse.obj Z).hom) => s.1 (WalkingMulticospan.left (⟨_, _, h⟩ : S.Arrow))) ?_
  intro s t hst
  have hl : ∀ I : S.Arrow, s.1 (.left I) = t.1 (.left I) := by
    intro I
    let i : Over.mk I.f ≅ e.inverse.obj (e.functor.obj (Over.mk I.f)) := e.unitIso.app _
    have h : S.1 (e.inverse.obj (e.functor.obj (Over.mk I.f))).hom :=
      (sieve_apply_iff_of_iso S.1 i).1 I.hf
    let I' : S.Arrow := ⟨_, _, h⟩
    let r : S.Relation := Cover.Relation.mk' (fst := I) (snd := I')
      { Z := I.Y, g₁ := 𝟙 _, g₂ := i.hom.left, w := by simp [I'] }
    have key (x : ((S.index P).multicospan ⋙ forget AddCommGrpCat).sections) :
        x.1 (.left I) = P.map i.hom.left.op (x.1 (.left I')) := by
      have h₁ :=
        (x.2 (WalkingMulticospan.Hom.fst r)).trans (x.2 (WalkingMulticospan.Hom.snd r)).symm
      change P.map (𝟙 I.Y).op (x.1 (.left I)) = P.map i.hom.left.op (x.1 (.left I')) at h₁
      simp only [op_id, Functor.map_id] at h₁
      exact h₁
    rw [key s, key t]
    exact congrArg _ (congr_fun (congr_fun hst _) h)
  refine Subtype.ext (funext fun j => ?_)
  cases j with
  | left I => exact hl I
  | right r =>
    rw [← s.2 (WalkingMulticospan.Hom.fst r), ← t.2 (WalkingMulticospan.Hom.fst r)]
    exact congrArg _ (hl _)

section Sheafification

variable [∀ X : C, EssentiallySmall.{u} (Over X)]

attribute [local instance] hasColimitsOfShape_cover_op_addCommGrpCat
  preservesColimitsOfShape_cover_op_forget_addCommGrpCat hasMultiequalizer_index_addCommGrpCat

/-- The opposite of the poset of covering sieves is `u`-small, as a type. -/
private theorem small_cover_op (X : C) : Small.{u} (J.Cover X)ᵒᵖ :=
  have := J.small_cover_of_essentiallySmall_over.{u} X
  small_of_injective (f := Opposite.unop) Opposite.unop_injective

attribute [local instance] small_cover_op

/-- **Sheafification of abelian presheaves with small sections on a site with essentially small
slices.** Let `(C, J)` be a site, with objects and morphisms in arbitrary universes, such that the
slice category over each object is essentially `u`-small. Then presheaves on `C` of abelian groups
in `Type u` admit a sheafification, and it preserves finite limits. -/
@[sga "3 IV 4.3.16" "partial"]
theorem hasSheafify_addCommGrpCat_of_essentiallySmall_over : HasSheafify J AddCommGrpCat.{u} :=
  inferInstance

open Presheaf Plus

/-- The map to the plus construction of a presheaf of abelian groups in `Type u` on a site with
essentially `u`-small slices is locally injective. -/
private theorem isLocallyInjective_toPlus_addCommGrpCat (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsLocallyInjective J (J.toPlus P) where
  equalizerSieve_mem {X} x y h := by
    rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
    obtain ⟨W, h₁, h₂, eq⟩ := h
    exact J.superset_covering (fun Y f hf => congr_fun (congr_arg Subtype.val eq) ⟨Y, f, hf⟩) W.2

/-- The map to the plus construction of a presheaf of abelian groups in `Type u` on a site with
essentially `u`-small slices is locally surjective. -/
private theorem isLocallySurjective_toPlus_addCommGrpCat (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsLocallySurjective J (J.toPlus P) where
  imageSieve_mem x := by
    obtain ⟨S, x, rfl⟩ := exists_rep x
    refine J.superset_covering (fun Y f hf => ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
    rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
    refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
    ext ⟨Z, g, hg⟩
    simpa using!
      x.2 { fst.hf := hf, snd.hf := S.1.downward_closed hf g, r.g₁ := g, r.g₂ := 𝟙 Z, .. }

/-- **Locally bijective maps of abelian presheaves with small sections on a site with essentially
small slices.** Let `(C, J)` be a site, with objects and morphisms in arbitrary universes, such
that the slice category over each object is essentially `u`-small. Then a morphism of presheaves
on `C` of abelian groups in `Type u` becomes an isomorphism after sheafification if and only if it
is locally injective and locally surjective. -/
theorem wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over :
    J.WEqualsLocallyBijective AddCommGrpCat.{u} := by
  have := J.hasSheafify_addCommGrpCat_of_essentiallySmall_over
  have hinj (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
      IsLocallyInjective J (CategoryTheory.toSheafify J P) := by
    have := J.isLocallyInjective_toPlus_addCommGrpCat P
    have := J.isLocallyInjective_toPlus_addCommGrpCat (J.plusObj P)
    have : IsLocallyInjective J (J.toSheafify P) := by
      dsimp [GrothendieckTopology.toSheafify]
      rw [plusMap_toPlus]
      exact (isLocallyInjective_comp J _ _ :
        IsLocallyInjective J (J.toPlus P ≫ J.toPlus (J.plusObj P)))
    rw [← toSheafify_plusPlusIsoSheafify_hom]
    infer_instance
  have hsurj (P : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
      IsLocallySurjective J (CategoryTheory.toSheafify J P) := by
    have := J.isLocallySurjective_toPlus_addCommGrpCat P
    have := J.isLocallySurjective_toPlus_addCommGrpCat (J.plusObj P)
    have : IsLocallySurjective J (J.toSheafify P) := by
      dsimp [GrothendieckTopology.toSheafify]
      rw [plusMap_toPlus]
      exact (isLocallySurjective_comp J _ _ :
        IsLocallySurjective J (J.toPlus P ≫ J.toPlus (J.plusObj P)))
    rw [← toSheafify_plusPlusIsoSheafify_hom]
    infer_instance
  exact WEqualsLocallyBijective.mk' J AddCommGrpCat.{u}

end Sheafification

end GrothendieckTopology

end CategoryTheory

end
