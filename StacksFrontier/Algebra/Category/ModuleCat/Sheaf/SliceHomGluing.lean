module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionMonoidal

/-!
# Morphisms of sheaves of modules glue over a covering family

Let `(C, 𝒪)` be a ringed site.  A family of morphisms `ℱ|_{Yᵢ} ⟶ 𝒢|_{Yᵢ}` of `𝒪`-modules, over a
family `Y` of objects covering the final object, which agree after relocalization to any common
refinement, extends to a unique morphism `ℱ ⟶ 𝒢`.

This is [Stacks, Tag 03EM] in the form a local-to-global construction consumes.  The content is
already in the tree at the level of *presheaves* of modules, as
`existsUnique_hom_of_isCompatible`; what this file adds is the passage to sheaves of modules,
which is that result and `SheafOfModules.hom_ext`, because `SheafOfModules.Hom` is a one-field
structure wrapping a morphism of the underlying presheaves of modules.  The same two steps are
carried out for the small étale site by
`AlgebraicGeometry.Space.existsUnique_sheafHom_of_isCompatible_smallEtale`; here they are done
once for a general ringed site at the strict spelling.

## Main results

* `Stacks.SheafOfModules.Strict.internalHom_isSheaf_forget_mod`: [Stacks, Tag 03EM] at the strict
  spelling, on underlying sets.
* `Stacks.SheafOfModules.Strict.existsUnique_sheafHom_of_isCompatible`: **the gluing.**

## Implementation notes

Both bridges between the internal-hom development's spelling and the strict one hold by `rfl` at
a general site: `mod_val_eq_presheafOfModules` identifies the two presheaf-of-modules categories
and `restrFun_map_val` identifies relocalization of the underlying presheaf morphism with
restriction of the morphism of sheaves.  Only the first had a general-site counterpart in the
tree (`over_val_eq_restrFun`, at the level of objects); the morphism-level one existed only for
the big fppf site.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04TQ](https://stacks.math.columbia.edu/tag/04TQ)
-/

@[expose] public section
open CategoryTheory Limits
noncomputable section
universe v u
namespace Stacks.SheafOfModules.Strict
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  (R : Sheaf J CommRingCat.{max u v})

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- The `𝒪`-modules of the strict development are the presheaves of modules that the
internal-hom development consumes, on the nose. -/
theorem mod_val_eq_presheafOfModules :
    PresheafOfModules.{max u v} (Oforget R.obj) =
      PresheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf R).obj := rfl

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- Restriction of a morphism of `𝒪`-modules to a slice site, on underlying presheaves. -/
theorem restrFun_map_val (W : C) {A B : Mod R} (f : A ⟶ B) :
    (restrFun R.obj W).map f.val =
      ((SliceRestriction.overFunctor R.obj (isSheaf_ringSheaf R) W).map f).val := rfl

variable [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}]

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **Stacks 03EM at the strict spelling**: the internal hom into an `𝒪`-module is a sheaf, read
on underlying sets. -/
theorem internalHom_isSheaf_forget_mod (A B : Mod R) :
    Presheaf.IsSheaf J ((internalHom R.obj A.val B.val).presheaf ⋙ CategoryTheory.forget _) :=
  internalHom_isSheaf_forget _ A.val B.val B.isSheaf

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- **Morphisms of `𝒪`-modules glue over a covering family.** -/
theorem existsUnique_sheafHom_of_isCompatible (A B : Mod R)
    {ι : Type*} {Y : ι → C} (hY : J.CoversTop Y)
    {α : Presheaf.FamilyOfElementsOnObjects
      ((internalHom R.obj A.val B.val).presheaf ⋙ CategoryTheory.forget _) Y}
    (hα : α.IsCompatible) :
    ∃! φ : A ⟶ B, ∀ i, (restrFun R.obj (Y i)).map φ.val = α i := by
  obtain ⟨ψ, hψ, huniq⟩ := existsUnique_hom_of_isCompatible R.obj A.val B.val hY
    (internalHom_isSheaf_forget_mod R A B) hα
  exact ⟨⟨ψ⟩, hψ, fun φ hφ => SheafOfModules.hom_ext (huniq φ.val hφ)⟩

omit [HasWeakSheafify J AddCommGrpCat.{max u v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{max u v}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{max u v}] in
/-- `existsUnique_sheafHom_of_isCompatible` at the spelling the restriction functor uses for its
source.  The two spellings of `Mod 𝒪` are definitionally equal and the crossing is not
reducible, so neither unification inside a tactic nor instance search passes between them; the
crossing is taken here, once, at the `:=`. -/
theorem existsUnique_sheafHom_of_isCompatible_ss
    (A B : SheafOfModules.{max u v}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf R.obj (isSheaf_ringSheaf R)))
    {ι : Type*} {Y : ι → C} (hY : J.CoversTop Y)
    {α : Presheaf.FamilyOfElementsOnObjects
      ((internalHom R.obj A.val B.val).presheaf ⋙ CategoryTheory.forget _) Y}
    (hα : α.IsCompatible) :
    ∃! φ : A ⟶ B, ∀ i, (restrFun R.obj (Y i)).map φ.val = α i :=
  existsUnique_sheafHom_of_isCompatible R A B hY hα

end Stacks.SheafOfModules.Strict
end
end
