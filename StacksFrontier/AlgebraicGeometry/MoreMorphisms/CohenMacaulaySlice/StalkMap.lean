module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.RingTheory.Koszul.FlatQuotient

/-!
# Stalk maps of a morphism locally of finite presentation

If `f : X ⟶ S` is locally of finite presentation, then for every `x : X` the induced map on
local rings `𝒪_{S, f x} ⟶ 𝒪_{X, x}` is *essentially of finite presentation*: the local ring
`𝒪_{X, x}` is a localization of an `𝒪_{S, f x}`-algebra of finite presentation.

## Main results

* `Stacks.AlgebraicGeometry.essentiallyOfFinitePresentation_stalkMap`: the stalk map of a
  morphism locally of finite presentation is essentially of finite presentation.

The statement does not need flatness of `f`, which the Stacks Project assumes.

## References

* [Stacks Project, Lemma 37.13.8 (Tag 05I8)](https://stacks.math.columbia.edu/tag/05I8)
* [Stacks Project, Tag 00QM](https://stacks.math.columbia.edu/tag/00QM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace Stacks.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **The stalk map is the localization of a map of sections.**  Let `U` be an affine open of
`S` containing `f x` and `V` an affine open of `X` containing `x` and mapping into `U`.  Then
the germ of `f.appLE U V` at `x` is the stalk map of `f` at `x`. -/
theorem germ_comp_appLE_eq_stalkMap_comp_germ (f : X ⟶ S) {x : X}
    {U : S.Opens} {V : X.Opens} (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    (X.presheaf.germ V x hx).hom.comp (f.appLE U V hVU).hom =
      (f.stalkMap x).hom.comp (S.presheaf.germ U (f x) (hVU hx)).hom := by
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, f.germ_stalkMap U x (hVU hx)]
  simp [Scheme.Hom.appLE]

/-- **The stalk map of a morphism locally of finite presentation is essentially of finite
presentation.**  For `f : X ⟶ S` locally of finite presentation and `x : X`, the local ring
`𝒪_{X, x}` is a localization of an `𝒪_{S, f x}`-algebra of finite presentation. -/
theorem essentiallyOfFinitePresentation_stalkMap (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) :
    (f.stalkMap x).hom.EssentiallyOfFinitePresentation := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have hU' : IsAffineOpen U := hU
  have hV' : IsAffineOpen V := hV
  let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  have : Algebra.FinitePresentation Γ(S, U) Γ(X, V) := f.finitePresentation_appLE hU hV hVU
  let : Algebra Γ(S, U) (S.presheaf.stalk (f x)) :=
    S.presheaf.algebra_section_stalk ⟨f x, hVU hxV⟩
  let : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  let : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let : Algebra Γ(S, U) (X.presheaf.stalk x) :=
    ((X.presheaf.germ V x hxV).hom.comp (f.appLE U V hVU).hom).toAlgebra
  have : IsScalarTower Γ(S, U) Γ(X, V) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower Γ(S, U) (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' (germ_comp_appLE_eq_stalkMap_comp_germ f hVU hxV)
  let p : Ideal Γ(S, U) := (hU'.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
  let q : Ideal Γ(X, V) := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : IsLocalization.AtPrime (S.presheaf.stalk (f x)) p :=
    hU'.isLocalization_stalk ⟨f x, hVU hxV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q := hV'.isLocalization_stalk ⟨x, hxV⟩
  have hcomap : q.comap (f.appLE U V hVU).hom = p :=
    congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE U hU' V hV' hVU hxV)
  have hMN : Algebra.algebraMapSubmonoid Γ(X, V) p.primeCompl ≤ q.primeCompl := by
    rintro _ ⟨s, hs, rfl⟩ hmem
    exact hs (hcomap ▸ Ideal.mem_comap.mpr hmem)
  exact Koszul.essentiallyOfFinitePresentation_localization p.primeCompl q.primeCompl hMN

end Stacks.AlgebraicGeometry

end
