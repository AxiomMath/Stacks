module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Generators
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-!
# A free rank-one module of sections on an affine open is a generator

Let `M` be a quasi-coherent module on a scheme `X`, let `A` be an affine open and let
`t ∈ Γ(M, A)` be a section with `r ↦ r • t` a bijection `Γ(X, A) → Γ(M, A)`.  Then `t`
generates `M` over *every* open inside `A`, that is, `t` is a
`Stacks.SheafOfModules.GeneratorSections`.

This is the step that converts the commutative algebra of
`StacksFrontier/AlgebraicGeometry/Variety/NoetherianDimensionOne/PuncturedFreeness.lean` — an
invertible module of sections becomes free after shrinking the chart — into the sheaf-theoretic
input of `Stacks.PicSurjectiveOpen.exists_isInvertible_modulePullback_iso`.  Bijectivity over
`A` alone is of course not enough for an arbitrary module sheaf; what makes the passage work is
quasi-coherence, through which the stalk of `M` at a point of `A` is a localization of
`Γ(M, A)`.

## Main results

* `Stacks.PicSurjectiveOpen.notMem_maximalIdeal_smul_top_germ_of_bijective_smul`: the germ of
  such a `t` at a point of `A` does not lie in `𝔪_y M_y`.
* `Stacks.PicSurjectiveOpen.generatorSections_of_bijective_smul`: **the statement above**.

## The proof

Two of the three clauses of `IsLocalizedModule` for the germ map
`Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ` are used, and each does one half.

Surjectivity says every element of `M_y` becomes a germ of a section over `A` after
multiplication by a function not vanishing at `y`; such a function is a unit in `𝒪_{X,y}`, and
every section over `A` is `r • t`, so `M_y = 𝒪_{X,y} · germ_y t`.  Were `germ_y t` in
`𝔪_y M_y`, writing each stalk element appearing in such an expression as a multiple of
`germ_y t` would give `germ_y t = a • germ_y t` with `a ∈ 𝔪_y`, hence `germ_y t = 0` because
`1 - a` is a unit.

The third clause then says `c • t = 0` in `Γ(M, A)` for some `c` not vanishing at `y`;
injectivity of `r ↦ r • t` forces `c = 0`, which no element of the complement of a prime can
be.  So invertibility of `M` is *not* needed for the germ statement — only for the passage
from germs to sections, which is
`Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top`.

## References

* [Stacks Project, Tag 09NA](https://stacks.math.columbia.edu/tag/09NA)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.PicSurjectiveOpen

variable {X : Scheme.{u}}

/-- Every element of the stalk at a point of an affine open is an `𝒪_{X,y}`-multiple of the germ
of a section whose multiples exhaust the sections over that open. -/
theorem exists_smul_germ_eq_of_surjective_smul (M : X.Modules) [M.IsQuasicoherent]
    {A : X.Opens} (hA : IsAffineOpen A) (t : Γ(M, A))
    (hsurj : Function.Surjective fun r : Γ(X, A) => r • t) {y : X} (hy : y ∈ A)
    (m : M.presheaf.stalk y) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule M y
    ∃ c : X.presheaf.stalk y, m = c • (M.presheaf.germ A y hy).hom t := by
  let := Stacks.ModuleStalkSpecialization.stalkModule M y
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule M hy
  let : Algebra Γ(X, A) (X.presheaf.stalk y) := (X.presheaf.germ A y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk y) (hA.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hA.isLocalization_stalk ⟨y, hy⟩
  have := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ M hA hy
  obtain ⟨⟨s, c⟩, hsc⟩ :=
    IsLocalizedModule.surj (hA.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl
      (Stacks.ModuleStalkSpecialization.germₗ M hy) m
  obtain ⟨r, hr⟩ := hsurj s
  have hcu : IsUnit ((X.presheaf.germ A y hy).hom (c : Γ(X, A))) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y)
      (hA.primeIdealOf ⟨y, hy⟩).asIdeal (c : Γ(X, A))).mpr c.2
  obtain ⟨u, hu⟩ := hcu
  refine ⟨(u⁻¹ : (X.presheaf.stalk y)ˣ) * (X.presheaf.germ A y hy).hom r, ?_⟩
  have hgerm : (Stacks.ModuleStalkSpecialization.germₗ M hy) s
      = (X.presheaf.germ A y hy).hom r • (M.presheaf.germ A y hy).hom t := by
    rw [← hr]
    exact Stacks.ModuleStalkSpecialization.germ_smul M hy r t
  have hsc' : ((X.presheaf.germ A y hy).hom (c : Γ(X, A))) • m
      = (X.presheaf.germ A y hy).hom r • (M.presheaf.germ A y hy).hom t := by
    rw [← hgerm, ← hsc]
    rfl
  rw [mul_smul, ← hsc', ← hu]
  exact (inv_smul_smul u m).symm

/-- **The germ of a free generator of the sections on an affine open generates the stalk.** For
`M` quasi-coherent, `A` affine and `r ↦ r • t` a bijection `Γ(X, A) → Γ(M, A)`, the germ of `t`
at a point `y` of `A` does not lie in `𝔪_y M_y`. -/
theorem notMem_maximalIdeal_smul_top_germ_of_bijective_smul (M : X.Modules) [M.IsQuasicoherent]
    {A : X.Opens} (hA : IsAffineOpen A) (t : Γ(M, A))
    (hbij : Function.Bijective fun r : Γ(X, A) => r • t) {y : X} (hy : y ∈ A) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule M y
    (M.presheaf.germ A y hy).hom t ∉
      maximalIdeal (X.presheaf.stalk y) • (⊤ : Submodule (X.presheaf.stalk y)
        (M.presheaf.stalk y)) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule M y
  let := Stacks.ModuleStalkSpecialization.sectionsStalkModule M hy
  let : Algebra Γ(X, A) (X.presheaf.stalk y) := (X.presheaf.germ A y hy).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk y) (hA.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hA.isLocalization_stalk ⟨y, hy⟩
  have := Stacks.ModuleStalkSpecialization.isLocalizedModule_germₗ M hA hy
  intro hmem
  -- The germ of `t` is a multiple of itself by an element of the maximal ideal.
  have key : ∃ a ∈ maximalIdeal (X.presheaf.stalk y),
      (M.presheaf.germ A y hy).hom t = a • (M.presheaf.germ A y hy).hom t := by
    refine Submodule.smul_induction_on
      (p := fun z => ∃ a ∈ maximalIdeal (X.presheaf.stalk y),
        z = a • (M.presheaf.germ A y hy).hom t) hmem ?_ ?_
    · intro a ha n _
      obtain ⟨c, hc⟩ := exists_smul_germ_eq_of_surjective_smul M hA t hbij.surjective hy n
      exact ⟨a * c, Ideal.mul_mem_right _ _ ha, by rw [hc, mul_smul]⟩
    · rintro z z' ⟨a, ha, hza⟩ ⟨a', ha', hza'⟩
      exact ⟨a + a', Submodule.add_mem _ ha ha', by rw [hza, hza', ← add_smul]⟩
  obtain ⟨a, ha, hta⟩ := key
  -- Hence the germ of `t` vanishes, `1 - a` being a unit.
  have hunit : IsUnit (1 - a) := isUnit_one_sub_self_of_mem_nonunits a ha
  have hzero : Stacks.ModuleStalkSpecialization.germₗ M hy t = 0 := by
    have h : (1 - a) • (M.presheaf.germ A y hy).hom t = 0 := by
      rw [sub_smul, one_smul, ← hta, sub_self]
    exact hunit.smul_eq_zero.mp h
  -- The third clause of `IsLocalizedModule` then contradicts injectivity.
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := (hA.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl)
    (f := Stacks.ModuleStalkSpecialization.germₗ M hy) (x₁ := t) (x₂ := 0)
    (by rw [map_zero]; exact hzero)
  rw [smul_zero] at hc
  have hc0 : (c : Γ(X, A)) = 0 := by
    refine hbij.injective ?_
    show (c : Γ(X, A)) • t = (0 : Γ(X, A)) • t
    rw [zero_smul]
    exact hc
  exact c.2 (hc0 ▸ (hA.primeIdealOf ⟨y, hy⟩).asIdeal.zero_mem)

/-- **A free rank-one module of sections on an affine open is a generator.** If `M` is an
invertible module on a scheme, `A` an affine open and `r ↦ r • t` a bijection
`Γ(X, A) → Γ(M, A)`, then `t` generates `M` over every open inside `A`, not only over `A`
itself. -/
def generatorSectionsOfBijectiveSmul (M : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property M]
    {A : X.Opens} (hA : IsAffineOpen A) (t : Γ(M, A))
    (hbij : Function.Bijective fun r : Γ(X, A) => r • t) :
    Stacks.SheafOfModules.GeneratorSections X.toRingedSpace M A := by
  refine ⟨t, fun V hV => ?_⟩
  refine Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    M t V hV fun z hz => ?_
  rw [Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace M.val z]
  exact notMem_maximalIdeal_smul_top_germ_of_bijective_smul M hA t hbij (hV hz)

end Stacks.PicSurjectiveOpen

end
