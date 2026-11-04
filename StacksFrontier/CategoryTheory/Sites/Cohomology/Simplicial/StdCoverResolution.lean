module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeOfSimplicialModules
import StacksCore.Tactic.StacksAttribute

/-!
# Resolutions of a presheaf of modules by standard covers

Let `R` be a presheaf of rings on a small category `C`. Every presheaf of `R`-modules receives an
epimorphism from `PresheafOfModules.stdCover'`, the coproduct indexed by its sections of the free
presheaves of modules on the universe-lifted representables, and those are projective
(`PresheafOfModules.uliftFreeYonedaProjective'`). So [Stacks, Tag 05T7] applies to the object
property "zero or a standard cover" and resolves any presheaf of modules by standard covers.

This is the dévissage that the proof of [Stacks, Tag 08RX] runs: an arbitrary module is replaced
by a bounded above complex built from the generators `j_{U!}R_U`, for which the statement to be
proved is accessible. The declarations below are the base-category-free form of
`Stacks.SimplicialModules.IsStdCover` and its two companions, which are the same statements at
`C = Δ`; the proof of [Stacks, Tag 09D2] needs them on the simplicial site `Δ × C` of
[Stacks, Tag 09D0] instead, and nothing in them is special to `Δ`.

## Main definitions

* `PresheafOfModules.IsStdCover`: the object property of being zero or isomorphic to a standard
  cover. Zero is included because [Stacks, Tag 05T7] asks the property to contain it.

## Main results

* `PresheafOfModules.exists_isStdCover_epi`: every presheaf of modules is a quotient of one with
  that property, namely of its own standard cover.
* `PresheafOfModules.exists_isStdCover_resolution`: consequently every presheaf of modules,
  placed in degree zero, receives a quasi-isomorphism from a cochain complex concentrated in
  degrees `≤ 0` each of whose terms is zero or a standard cover.

## References

* [Stacks Project, Tag 05T7](https://stacks.math.columbia.edu/tag/05T7)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 09D2](https://stacks.math.columbia.edu/tag/09D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u₀

namespace PresheafOfModules

variable {C : Type u₀} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{max u₀ u}}

/-- **The objects a resolution by standard covers is built from**: a presheaf of modules is
either zero or isomorphic to the standard cover `PresheafOfModules.stdCover'` of some presheaf of
modules. The zero object is included so that the property contains zero, which is what
[Stacks, Tag 05T7] asks for. -/
def IsStdCover : ObjectProperty (PresheafOfModules.{max u₀ u} R) :=
  fun N => IsZero N ∨ ∃ N' : PresheafOfModules.{max u₀ u} R, Nonempty (N ≅ N'.stdCover')

/-- The object property `PresheafOfModules.IsStdCover` contains a zero object. -/
instance : (IsStdCover (R := R)).ContainsZero := by
  obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := PresheafOfModules.{max u₀ u} R)
  exact ⟨Z, hZ, Or.inl hZ⟩

/-- Every presheaf of modules is a quotient of an object with the property
`PresheafOfModules.IsStdCover`, namely of its own standard cover. -/
theorem exists_isStdCover_epi (N : PresheafOfModules.{max u₀ u} R) :
    ∃ (N' : PresheafOfModules.{max u₀ u} R) (_ : IsStdCover N') (p : N' ⟶ N), Epi p :=
  ⟨N.stdCover', Or.inr ⟨N, ⟨Iso.refl _⟩⟩, N.fromStdCover', inferInstance⟩

/-- **A resolution of a presheaf of modules by standard covers**, [Stacks, Tag 05T7] for the
object property `PresheafOfModules.IsStdCover`: every presheaf of modules `M` receives a
quasi-isomorphism from a cochain complex concentrated in degrees `≤ 0` each of whose terms is
zero or a `PresheafOfModules.stdCover'`. -/
theorem exists_isStdCover_resolution (M : PresheafOfModules.{max u₀ u} R) :
    ∃ (L : CochainComplex (PresheafOfModules.{max u₀ u} R) ℤ)
      (π : L ⟶ (HomologicalComplex.single (PresheafOfModules.{max u₀ u} R)
        (ComplexShape.up ℤ) 0).obj M)
      (_ : QuasiIso π) (_ : ∀ n, IsStdCover (L.X n)), L.IsStrictlyLE 0 := by
  obtain ⟨L, π, -, hq, hP, hLE⟩ :=
    (CochainComplex.exists_quasiIso_prop (IsStdCover (R := R)) exists_isStdCover_epi 0).1
      ((HomologicalComplex.single (PresheafOfModules.{max u₀ u} R) (ComplexShape.up ℤ) 0).obj M)
  exact ⟨L, π, hq, hP, hLE⟩

/-- **A resolution of a bounded above complex of presheaves of modules by standard covers**,
[Stacks, Tag 05T7] for the object property `PresheafOfModules.IsStdCover`: a complex of presheaves
of modules whose cohomology vanishes in degrees `> a` receives a quasi-isomorphism from a complex
vanishing in degrees `> a` each of whose terms is zero or a standard cover.

This is the form of [Stacks, Tag 03EW] that the proof of [Stacks, Tag 08RX] uses: "every such
complex is quasi-isomorphic to a bounded above complex whose terms are direct sums of
`j_{U!}O_U`". -/
theorem exists_isStdCover_resolution_of_isLE (a : ℤ)
    (K : CochainComplex (PresheafOfModules.{max u₀ u} R) ℤ) [K.IsLE a] :
    ∃ (L : CochainComplex (PresheafOfModules.{max u₀ u} R) ℤ) (f : L ⟶ K) (_ : QuasiIso f)
      (_ : ∀ n, IsStdCover (L.X n)), L.IsStrictlyLE a :=
  (CochainComplex.exists_quasiIso_prop (IsStdCover (R := R)) exists_isStdCover_epi a).2 K

end PresheafOfModules

end
