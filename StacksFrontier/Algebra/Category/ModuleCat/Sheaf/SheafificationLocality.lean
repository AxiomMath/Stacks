module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective

/-!
# Sheafifying a map of presheaves of modules which is invertible on a covering family

Let `(C, J)` be a site, let `R` be a sheaf of rings on it and let `f : P ⟶ Q` be a map of
presheaves of `R`-modules. If the objects on which `f` is invertible on sections cover every
object of `C`, then the induced map of sheafifications `P^# ⟶ Q^#` is an isomorphism.

This is the presheaf-of-modules form of
`CategoryTheory.Presheaf.isIso_presheafToSheaf_map_of_hasEnoughObjects_bijective`
(Stacks 0H6Y), which says the same thing for presheaves valued in a concrete category. The
reduction is that `PresheafOfModules.sheafification` inverts exactly the maps whose underlying
map of abelian-group-valued presheaves is locally bijective.

## Main results

* `PresheafOfModules.isIso_sheafification_map_of_isIso_evaluation`: invertibility of `f` on
  sections over a covering family of objects makes the sheafification of `f` an isomorphism.

## Implementation notes

The hypothesis is phrased with `IsIso` of the evaluation functor applied to `f`, rather than
with bijectivity of the underlying map of sections, because that is the form in which consumers
obtain it: the evaluation of a presheaf of modules at an object lands in a category of modules,
where invertibility is what the surrounding derived-functor arguments produce. Bijectivity of
the underlying map of abelian groups is then read off with
`ConcreteCategory.bijective_of_isIso`, the two being the same condition.

The object property `B` is arbitrary rather than being the locus of invertibility itself, which
is the convenient form at the use site; it is no weaker, since
`GrothendieckTopology.HasEnoughObjects` is monotone in its object property.

## References

* [Stacks Project, Tag 0H6Y](https://stacks.math.columbia.edu/tag/0H6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PresheafOfModules

universe w' v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w'}}
  [HasSheafify J AddCommGrpCat.{w'}] [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **Stacks 0H6Y for presheaves of modules.** If a map `f` of presheaves of `R`-modules is
invertible on sections over the members of a family of objects covering every object of the
site, then the induced map of sheafifications is an isomorphism. -/
theorem isIso_sheafification_map_of_isIso_evaluation
    {B : ObjectProperty C} (hB : J.HasEnoughObjects B)
    {P Q : PresheafOfModules.{w'} R.obj} (f : P ⟶ Q)
    (hf : ∀ ⦃U : C⦄, B U → IsIso ((evaluation R.obj (op U)).map f)) :
    IsIso ((sheafification (𝟙 R.obj)).map f) := by
  let φ := (toPresheaf R.obj).map f
  have hbij : ∀ ⦃U : C⦄, B U → Function.Bijective (φ.app (op U)) := fun U hU => by
    have := hf hU
    exact ConcreteCategory.bijective_of_isIso ((evaluation R.obj (op U)).map f)
  have := Presheaf.isLocallyInjective_of_hasEnoughObjects_injective J φ hB
    fun _ hU => (hbij hU).1
  have := Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective J φ hB
    fun _ hU => (hbij hU).2
  show ((MorphismProperty.isomorphisms _).inverseImage (sheafification (𝟙 R.obj))) f
  rw [← inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact J.W_of_isLocallyBijective φ

end PresheafOfModules

end
