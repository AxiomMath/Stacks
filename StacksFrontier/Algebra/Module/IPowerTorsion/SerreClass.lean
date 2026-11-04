module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.IPowerTorsion

/-!
# Ideal-power torsion modules form a Serre class

For a finitely generated ideal `I` of a commutative ring `R`, the `R`-modules all of whose
elements are annihilated by positive powers of `I` form a Serre subcategory of the abelian
category of `R`-modules: the class contains a zero object, is stable under passing to submodules
and quotients, and is stable under extensions.

## Main results

* `isSerreClass_isIPowerTorsion`: the `I`-power torsion modules form a Serre class in
  `ModuleCat R`.

## Implementation notes

The full subcategory of the source is represented by its object property on `ModuleCat R`, and
stability under extensions is exactly the second half of
`torsionBySet_quotient_primaryComponent_eq_bot_and_isIPowerTorsion_of_exact`, transported from
linear maps to short exact sequences of `ModuleCat R`.

## References

* [The Stacks Project, Tag 0A6K](https://stacks.math.columbia.edu/tag/0A6K)
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

/-- **Stacks 0A6K.** The modules annihilated elementwise by positive powers of a finitely
generated ideal form a Serre subcategory of the category of modules. -/
@[stacks 0A6K]
public theorem isSerreClass_isIPowerTorsion
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    CategoryTheory.ObjectProperty.IsSerreClass
      ((fun M : ModuleCat.{v} R => IsIPowerTorsion R M I) :
        CategoryTheory.ObjectProperty (ModuleCat.{v} R)) := by
  let P : CategoryTheory.ObjectProperty (ModuleCat.{v} R) :=
    fun M => IsIPowerTorsion R M I
  let hExt :=
    (torsionBySet_quotient_primaryComponent_eq_bot_and_isIPowerTorsion_of_exact.{u,
      v, v, v, v} I hI).2
  show P.IsSerreClass
  refine
    { exists_zero := ?_
      prop_of_mono := ?_
      prop_of_epi := ?_
      prop_X₂_of_shortExact := ?_ }
  · exact ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, fun x =>
      ⟨1, by simp, fun a _ => by rw [Subsingleton.elim x 0, smul_zero]⟩⟩
  · intro X Y f _ hY x
    obtain ⟨n, hn, hnx⟩ := hY (f x)
    exact ⟨n, hn, fun a ha => (ModuleCat.mono_iff_injective f).mp inferInstance <| by
      simpa using hnx a ha⟩
  · intro X Y f _ hX y
    obtain ⟨x, rfl⟩ := (ModuleCat.epi_iff_surjective f).mp inferInstance y
    obtain ⟨n, hn, hnx⟩ := hX x
    exact ⟨n, hn, fun a ha => by simpa using congr_arg f (hnx a ha)⟩
  · intro S hS h₁ h₃
    exact hExt S.X₁ S.X₂ S.X₃ S.f.hom S.g.hom
      ((ModuleCat.mono_iff_injective S.f).mp hS.mono_f)
      ((CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
      ((ModuleCat.epi_iff_surjective S.g).mp hS.epi_g) h₁ h₃

end
