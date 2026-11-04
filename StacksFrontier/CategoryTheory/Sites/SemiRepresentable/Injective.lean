module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.Sites.SemiRepresentable.InverseImage
public import StacksFrontier.Homology.Injectives.Sheaf.InternalHomExact
public import StacksCore.Tactic.StacksAttribute

/-!
# Localization at a semi-representable object preserves injective abelian sheaves

Let `(C, J)` be a site and `K = ⨿ i, K.obj i` a semi-representable object of `C`. The inverse
image `j⁻¹ : Ab(C) ⥤ Ab(C / K)` along the localization at `K` sends injective abelian sheaves
to injective abelian sheaves.

Sheaves on `C / K` are families of sheaves on the component slices and `j⁻¹` is the family of
the one-component inverse images, so the statement reduces to the one-component case, where
`j⁻¹` is a right adjoint whose left adjoint — extension by zero — is exact. That exactness is
the content of Stacks 01DR and is already available as
`StacksDraft.Homology.Injectives.Sheaf`'s `extensionByZero_preservesMonos`.

## Main results

* `CategoryTheory.SemiRepresentable.injective_localizationInverseImage_obj`: **Stacks 0D88**,
  the inverse image along the localization at a semi-representable object preserves injective
  abelian sheaves.

## Implementation notes

An object of a product category is injective as soon as each of its components is: a
monomorphism in a product category is a monomorphism in each factor, so the lifts can be
chosen one factor at a time. That is `injective_of_forall` below.

The coefficient universe is `max u v t` for an arbitrary `t`, where `u` and `v` are the object
and morphism universes of the site. It must contain `u` and `v`, because that is where abelian
sheaves on `C` and on every slice of `C` have a sheafification
(`Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp`) and where extension by zero is
exact, but is otherwise free. The index universe `w` of the semi-representable object does not
enter: the decomposition of sheaves on the disjoint-union site holds for coefficients in any
category.

## References

* [Stacks Project, Tag 0D88](https://stacks.math.columbia.edu/tag/0D88)
* [Stacks Project, Tag 01DR](https://stacks.math.columbia.edu/tag/01DR)
-/

@[expose] public section

namespace CategoryTheory.SemiRepresentable

open CategoryTheory CategoryTheory.Limits

universe u v w t u' a b c

/-- An object of a product of categories is injective as soon as each of its components is. -/
theorem injective_of_forall {ι : Type a} {A : ι → Type b} [∀ i, Category.{c} (A i)]
    {I : ∀ i, A i} (hI : ∀ i, Injective (I i)) : Injective I := by
  classical
  refine ⟨fun {X Y} g f hf => ?_⟩
  have hmono (i : ι) : Mono (f i) := by
    constructor
    intro Z g' h' eq
    let W : ∀ j, A j := fun j => if hj : j = i then hj.symm ▸ Z else X j
    let t : W i ≅ Z := eqToIso (by simp [W])
    let G (k : Z ⟶ X i) : W ⟶ X := fun j =>
      if hj : j = i then by cases hj; exact t.hom ≫ k
      else eqToHom (by simp [W, hj])
    have hcomp : G g' ≫ f = G h' ≫ f := by
      funext j
      by_cases hj : j = i
      · subst j
        simpa [G, Category.assoc] using congrArg (fun k => t.hom ≫ k) eq
      · simp [G, W, hj]
    have hGH : G g' = G h' := (cancel_mono f).1 hcomp
    apply (cancel_epi t.hom).1
    simpa [G] using congrFun hGH i
  choose h hh using fun i => by
    have : Mono (f i) := hmono i
    exact (hI i).factors (g i) (f i)
  exact ⟨h, funext hh⟩

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)

/-- **Stacks 0D88.** The inverse image along the localization at a semi-representable object
sends injective abelian sheaves to injective abelian sheaves. -/
@[stacks 0D88 "injectives are preserved"]
theorem injective_localizationInverseImage_obj
    (I : Sheaf J AddCommGrpCat.{max u v t}) [Injective I] :
    Injective ((localizationInverseImage J K AddCommGrpCat.{max u v t}).obj I) := by
  have : HasSheafify J AddCommGrpCat.{max u v t} :=
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u, v, t}
  have : ∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{max u v t} := fun U =>
    Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{max u v, v, t} (J := J.over U)
  have hcomp : ∀ i, Injective
      ((J.overPullback AddCommGrpCat.{max u v t} (K.obj i)).obj I) := fun i =>
    overPullback_preservesInjective.{v, u, max u v t} J (K.obj i) I
  have hfam : Injective ((componentInverseImage J K AddCommGrpCat.{max u v t}).obj I) :=
    injective_of_forall hcomp
  let e := (formalCoproductSliceSheavesEquivalence J K AddCommGrpCat.{max u v t}).1
  exact (e.map_injective_iff _).1 (Injective.of_iso
    ((localizationInverseImageCompEquivalenceIso J K AddCommGrpCat.{max u v t}).app I).symm hfam)

end CategoryTheory.SemiRepresentable

end
