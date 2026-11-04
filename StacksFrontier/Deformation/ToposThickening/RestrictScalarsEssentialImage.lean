module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardEssentialImage
public import StacksFrontier.Deformation.ToposThickening.ExtensionDifference

/-!
# The essential image of restriction of scalars along a locally surjective map of ring sheaves

Let `α : R ⟶ S` be a map of sheaves of rings on a site which is locally surjective. A sheaf of
`R`-modules is isomorphic to the restriction of scalars along `α` of a sheaf of `S`-modules
exactly when, section by section, the kernel of `α` annihilates it.

Both implications are already available: the forward one is
`Stacks.Sheaves.PushforwardEssentialImage.smul_eq_zero_of_essImage_restrictScalars`, which needs
neither local surjectivity nor any hypothesis on the source of the functor, and the converse is
`Deformation.ToposThickening.descendModule`, which divides `R` section by section by the kernel
of `α`, transports the module structure across that quotient, and sheafifies at the identity of
the underlying presheaf. This file is the `iff` they assemble to.

This is the module-theoretic half of the essential-image criterion of Stacks 08M3. The criterion
as the source states it is about the direct image of modules along a closed immersion of ringed
topoi, which factors as this restriction of scalars after a direct image on modules; the
statements below say nothing about that second factor. See the implementation notes.

## Main results

* `Deformation.ToposThickening.essImage_restrictScalars_of_smul_eq_zero`: a sheaf of `R`-modules
  annihilated by the kernel of a locally surjective `α : R ⟶ S` is in the essential image of
  restriction of scalars along `α`.
* `Deformation.ToposThickening.essImage_restrictScalars_iff`: that membership of the essential
  image is equivalent to the annihilation condition.

## Implementation notes

The annihilation condition is stated as membership of `RingHom.ker` on sections, which is the
form the forward half uses; `Deformation.ToposThickening.descendModule` states the same
hypothesis as the equation `α U a = 0`, and the two are definitionally the same condition.

The hypotheses are exactly those of `descendModule`: local surjectivity of `α` and nothing else.
In particular no hypothesis about a morphism of topoi, about a closed immersion, or about
commutativity of the rings is needed, and the section universe of the modules is the section
universe of the rings, as it is for `descendModule`.

What these statements do **not** give is the essential image of the direct image
`Mod(O) ⥤ Mod(O')` of a closed immersion of ringed topoi. That functor is a direct image on
modules followed by restriction of scalars along the structure map, and only the second factor is
treated here; the first needs the essential surjectivity of the direct image on modules onto the
modules over the direct image of the structure sheaf, which is the remaining input recorded in
the implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardEssentialImage.lean` and which is not
available. For that reason the statements below carry no Stacks tag.

The natural home of this file is beside the two halves it combines, in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/`; it sits here because that is where
`Deformation.ToposThickening.descendModule` currently lives.

## References

* [Stacks Project, Lemma 18.29.2 (Tag 08M3)](https://stacks.math.columbia.edu/tag/08M3)
-/

@[expose] public section

open CategoryTheory

universe v u w

namespace Deformation.ToposThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{w}} (α : R ⟶ S) [Presheaf.IsLocallySurjective J α.hom]

/-- A sheaf of `R`-modules annihilated, section by section, by the kernel of a locally
surjective map of sheaves of rings `α : R ⟶ S` is isomorphic to the restriction of scalars
along `α` of a sheaf of `S`-modules.

This is the converse half of the essential-image criterion of Stacks 08M3 for restriction of
scalars; the module over `S` is the one produced by
`Deformation.ToposThickening.descendModule`. -/
theorem essImage_restrictScalars_of_smul_eq_zero (M : SheafOfModules.{w} R)
    (hM : ∀ (U : Cᵒᵖ) (a : R.obj.obj U), a ∈ RingHom.ker (α.hom.app U).hom →
      ∀ m : M.val.obj U, a • m = 0) :
    (SheafOfModules.restrictScalars.{w} α).essImage M := by
  obtain ⟨N, e⟩ := descendModule α M (fun U a ha m => hM U a ha m)
  exact ⟨N, ⟨e⟩⟩

/-- **The essential-image criterion for restriction of scalars.** For a locally surjective map
`α : R ⟶ S` of sheaves of rings, a sheaf of `R`-modules is in the essential image of restriction
of scalars along `α` exactly when the kernel of `α` annihilates it section by section.

This is the module-theoretic content of the essential-image assertion of Stacks 08M3. -/
theorem essImage_restrictScalars_iff (M : SheafOfModules.{w} R) :
    (SheafOfModules.restrictScalars.{w} α).essImage M ↔
      ∀ (U : Cᵒᵖ) (a : R.obj.obj U), a ∈ RingHom.ker (α.hom.app U).hom →
        ∀ m : M.val.obj U, a • m = 0 := by
  refine ⟨fun hM U a ha m => ?_, essImage_restrictScalars_of_smul_eq_zero α M⟩
  exact Stacks.Sheaves.PushforwardEssentialImage.smul_eq_zero_of_essImage_restrictScalars
    (𝟭 (SheafOfModules.{w} S)) hM U a ha m

end Deformation.ToposThickening

end
