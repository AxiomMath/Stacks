module

public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.IdealSheafSections
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Scheme.Immersion.IdealSheafQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quasi-coherent sheaf of ideals of a closed subscheme

A closed subscheme of a scheme `X` is recorded by an `AlgebraicGeometry.Scheme.IdealSheafData`,
and it has a quasi-coherent sheaf of ideals `ℐ ⊆ 𝒪_X`, here an object of `X.Modules` together
with a monomorphism into the structure sheaf. **Along the support every section of the ideal
vanishes.**

For the *reduced* closed subscheme structure on a closed subset `Z` ([Stacks, Tag 01J3]):

* at a point **outside** `Z` the ideal contains the unit section over some neighbourhood;
* at a point **of** `Z` every section of the ideal has germ in the maximal ideal.

## Main definitions

* `Stacks.IdealSheafModules.sheaf`: **the quasi-coherent sheaf of ideals** of an
  `AlgebraicGeometry.Scheme.IdealSheafData`, as an object of `X.Modules`.
* `Stacks.IdealSheafModules.ι`: its monomorphism into `Stacks.Ample.unitModule X`.
* `Stacks.ComplementIdeal.data`: the reduced closed subscheme structure on a closed subset, as
  affine-local ideal data — Mathlib's `AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal`.
* `Stacks.ComplementIdeal.sheaf` and `Stacks.ComplementIdeal.ι`: the two definitions above at
  that ideal data.

## Main results

* `Stacks.IdealSheafModules.isQuasicoherent_sheaf` and `Stacks.IdealSheafModules.mono_ι`:
  `Stacks.IdealSheafModules.sheaf` is a quasi-coherent sheaf of ideals.
* `Stacks.IdealSheafModules.germ_app_ι_mem_maximalIdeal` and
  `Stacks.IdealSheafModules.mapFun_ι_mem_maximalSmul`: **along the support every section of the
  ideal sheaf vanishes.**
* `Stacks.IdealSheafModules.exists_app_ι_eq_one`: on an affine open whose ideal contains `1`,
  some section of the ideal sheaf *is* the unit section.
* `Stacks.ComplementIdeal.exists_section_app_eq_one`: **off `Z` the ideal is the unit ideal.**
* `Stacks.ComplementIdeal.germ_app_mem_maximalIdeal`: **along `Z` every section of the ideal
  vanishes.**

## References

* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.ComplementIdeal

/-! ### The stalk of the structure sheaf as a module over itself -/

open scoped Stacks.ModuleStalk in
/-- **`𝔪_x · (𝒪_X)_x` is `𝔪_x`** under the identification `Stacks.Ample.unitStalkEquiv` of the
stalk of `𝒪_X` as a module over itself with `𝒪_{X,x}`. -/
theorem mem_maximalSmul_iff_unitStalkFun_mem (X : Scheme.{u}) (x : X)
    (m : TopCat.Presheaf.stalk (C := Ab.{u}) (Stacks.Ample.unitModule X).presheaf x) :
    m ∈ Stacks.ModuleStalk.maximalSmul (Stacks.Ample.unitModule X) x ↔
      Stacks.Ample.unitStalkFun X x m ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  refine ⟨Stacks.Ample.mem_maximalIdeal_of_mem_maximalSmul X x, fun hm => ?_⟩
  have hrec : (Stacks.Ample.unitStalkEquiv X x).symm
      (Stacks.Ample.unitStalkFun X x m) = m :=
    (Stacks.Ample.unitStalkEquiv X x).symm_apply_apply m
  have hsmul : (Stacks.Ample.unitStalkEquiv X x).symm
      (Stacks.Ample.unitStalkFun X x m) =
      Stacks.Ample.unitStalkFun X x m • (Stacks.Ample.unitStalkEquiv X x).symm 1 := by
    rw [← LinearEquiv.map_smul]
    exact congrArg _ (by rw [smul_eq_mul, mul_one])
  rw [← hrec, hsmul]
  exact Stacks.ModuleStalk.smul_mem_maximalSmul_of_mem_maximalIdeal hm _

/-- **The germ of the unit section of `𝒪_X` over an open set avoids `𝔪_x · (𝒪_X)_x`.** This is
`Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one` over an arbitrary open set rather than over
`⊤`. -/
theorem germ_one_notMem_maximalSmul (X : Scheme.{u}) (x : X) (V : X.Opens) (hx : x ∈ V) :
    ((Stacks.Ample.unitModule X).presheaf.germ V x hx).hom
        (show Γ(Stacks.Ample.unitModule X, V) from (1 : Γ(X, V))) ∉
      Stacks.ModuleStalk.maximalSmul (Stacks.Ample.unitModule X) x := by
  intro h
  rw [mem_maximalSmul_iff_unitStalkFun_mem, Stacks.Ample.unitStalkFun_germ, map_one] at h
  exact IsLocalRing.notMem_maximalIdeal.mpr isUnit_one h

end Stacks.ComplementIdeal

namespace Stacks.IdealSheafModules

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-! ### The ideal sheaf of a closed subscheme -/

/-- **The quasi-coherent sheaf of ideals of a closed subscheme**, as an object of `X.Modules`. -/
noncomputable def sheaf : X.Modules := Stacks.Divisors.idealSheafOfModules I

/-- The inclusion of the ideal sheaf into the structure sheaf. -/
noncomputable def ι : sheaf I ⟶ Stacks.Ample.unitModule X := Stacks.Divisors.idealInclusion I

/-- The ideal sheaf is a subsheaf of the structure sheaf. -/
instance mono_ι : Mono (ι I) := by
  have h : Mono (Stacks.Divisors.idealInclusion I) := by
    change Mono (kernel.ι _)
    infer_instance
  exact h

/-- **The ideal sheaf is quasi-coherent.** -/
instance isQuasicoherent_sheaf : (sheaf I).IsQuasicoherent := by
  have : Stacks.ClosedImmersion.IsClosedImmersion I.subschemeι.toLRSHom.toShHom :=
    ((Stacks.AlgebraicGeometry.ClosedImmersionTFAE.closedImmersion_tfae
      I.subschemeι).out 1 6).mp (inferInstance : IsClosedImmersion _)
  exact Stacks.ClosedImmersion.isQuasicoherent_idealSheaf _ _ I.subschemeι.toLRSHom

/-- On sections, the inclusion of the ideal sheaf is
`Stacks.Divisors.idealSheafSection`. -/
theorem app_ι (V : X.Opens) (s : Γ(sheaf I, V)) :
    (ι I).app V s = Stacks.Divisors.idealSheafSection I s :=
  rfl

/-- **A section of the ideal sheaf is annihilated by the closed immersion.** -/
theorem subschemeι_app_app_ι (V : X.Opens) (s : Γ(sheaf I, V)) :
    I.subschemeι.app V (show Γ(X, V) from (ι I).app V s) = 0 :=
  Stacks.Divisors.subschemeι_app_idealSheafSection I s

/-! ### The vanishing along the support -/

/-- **Along the support the sections of the ideal sheaf vanish**: the germ at a point of
`I.support` of a section of `ℐ` lies in the maximal ideal of the local ring there. -/
theorem germ_app_ι_mem_maximalIdeal {y : X} (hy : y ∈ I.support) (V : X.Opens)
    (hyV : y ∈ V) (s : Γ(sheaf I, V)) :
    (X.presheaf.germ V y hyV).hom ((ι I).app V s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  obtain ⟨z, hz⟩ : y ∈ Set.range I.subschemeι.base := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact hy
  subst hz
  rw [IsLocalRing.mem_maximalIdeal]
  intro hunit
  have hmap := Scheme.Hom.germ_stalkMap_apply I.subschemeι V z hyV ((ι I).app V s)
  rw [subschemeι_app_app_ι, map_zero] at hmap
  refine not_isUnit_zero
    (M₀ := ToType (I.subscheme.presheaf.stalk z)) ?_
  rw [← hmap]
  exact hunit.map _

/-- **Along the support the ideal sheaf lands in `𝔪_y · (𝒪_X)_y`** — the stalk form of
`Stacks.IdealSheafModules.germ_app_ι_mem_maximalIdeal`. -/
theorem mapFun_ι_mem_maximalSmul {y : X} (hy : y ∈ I.support)
    (g : TopCat.Presheaf.stalk (C := Ab.{u}) (sheaf I).presheaf y) :
    Stacks.ModuleStalk.mapFun (ι I) y g ∈
      Stacks.ModuleStalk.maximalSmul (Stacks.Ample.unitModule X) y := by
  obtain ⟨V, hyV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq (sheaf I).presheaf g
  rw [Stacks.ModuleStalk.mapFun_germ,
    Stacks.ComplementIdeal.mem_maximalSmul_iff_unitStalkFun_mem,
    Stacks.Ample.unitStalkFun_germ]
  exact germ_app_ι_mem_maximalIdeal I hy V hyV s

/-! ### The unit section where the ideal is everything -/

/-- **Where the ideal contains `1` the ideal sheaf contains the unit section**: on an affine open
whose ideal contains the unit, some section of the ideal sheaf is the unit section of `𝒪_X`. -/
theorem exists_app_ι_eq_one (V : X.affineOpens)
    (hV : (1 : Γ(X, (V : X.Opens))) ∈ I.ideal V) :
    ∃ s : Γ(sheaf I, (V : X.Opens)), (ι I).app (V : X.Opens) s =
      show Γ(Stacks.Ample.unitModule X, (V : X.Opens)) from (1 : Γ(X, (V : X.Opens))) :=
  (Stacks.Divisors.mem_ideal_iff_exists_idealSheafSection I V 1).mp hV

end Stacks.IdealSheafModules

namespace Stacks.ComplementIdeal

variable (X : Scheme.{u})

/-! ### The reduced closed subscheme on a closed set -/

/-- The reduced closed subscheme structure on a closed subset of a scheme, as affine-local ideal
data: Mathlib's vanishing ideal sheaf of [Stacks, Tag 01J3]. -/
@[ega "III 2.6.2.5" "Construction of J"]
noncomputable def data (Z : Closeds X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal Z

/-- The support of the vanishing ideal data of a closed set is that closed set. -/
theorem coe_support_data (Z : Closeds X) : ((data X Z).support : Set X) = (Z : Set X) :=
  Scheme.IdealSheafData.coe_support_vanishingIdeal Z

/-- A point of the closed set is a point of the support of its vanishing ideal. -/
theorem mem_support_data (Z : Closeds X) {y : X} (hy : y ∈ Z) : y ∈ (data X Z).support := by
  rw [← SetLike.mem_coe, coe_support_data]
  exact hy

/-- A point outside the closed set is outside the support of its vanishing ideal. -/
theorem notMem_support_data (Z : Closeds X) {x : X} (hx : x ∉ Z) : x ∉ (data X Z).support :=
  fun hc => hx (by rw [← SetLike.mem_coe, ← coe_support_data X Z]; exact hc)

/-- **The quasi-coherent sheaf of ideals of the reduced closed subscheme on a closed subset**,
as an object of `X.Modules`. -/
noncomputable def sheaf (Z : Closeds X) : X.Modules :=
  Stacks.IdealSheafModules.sheaf (data X Z)

/-- The inclusion of the ideal sheaf into the structure sheaf. -/
noncomputable def ι (Z : Closeds X) : sheaf X Z ⟶ Stacks.Ample.unitModule X :=
  Stacks.IdealSheafModules.ι (data X Z)

/-- The ideal sheaf is a subsheaf of the structure sheaf. -/
instance mono_ι (Z : Closeds X) : Mono (ι X Z) :=
  Stacks.IdealSheafModules.mono_ι (data X Z)

/-- **The ideal sheaf is quasi-coherent.** -/
instance isQuasicoherent_sheaf (Z : Closeds X) : (sheaf X Z).IsQuasicoherent :=
  Stacks.IdealSheafModules.isQuasicoherent_sheaf (data X Z)

/-- On sections, the inclusion of the ideal sheaf is
`Stacks.Divisors.idealSheafSection`. -/
theorem app_ι (Z : Closeds X) (V : X.Opens) (s : Γ(sheaf X Z, V)) :
    (ι X Z).app V s = Stacks.Divisors.idealSheafSection (data X Z) s :=
  rfl

/-- **A section of the ideal sheaf is annihilated by the closed immersion.** -/
theorem subschemeι_app_app_ι (Z : Closeds X) (V : X.Opens) (s : Γ(sheaf X Z, V)) :
    (data X Z).subschemeι.app V (show Γ(X, V) from (ι X Z).app V s) = 0 :=
  Stacks.IdealSheafModules.subschemeι_app_app_ι (data X Z) V s

/-! ### The two properties -/

/-- **Along the closed set the sections of the ideal sheaf vanish**: the germ at a point of `Z`
of a section of `ℐ_Z` lies in the maximal ideal of the local ring there. -/
theorem germ_app_mem_maximalIdeal (Z : Closeds X) {y : X} (hy : y ∈ Z) (V : X.Opens)
    (hyV : y ∈ V) (s : Γ(sheaf X Z, V)) :
    (X.presheaf.germ V y hyV).hom ((ι X Z).app V s) ∈
      IsLocalRing.maximalIdeal (X.presheaf.stalk y) :=
  Stacks.IdealSheafModules.germ_app_ι_mem_maximalIdeal (data X Z)
    (mem_support_data X Z hy) V hyV s

/-- **Along the closed set the ideal sheaf lands in `𝔪_y · (𝒪_X)_y`** — the stalk form of
`Stacks.ComplementIdeal.germ_app_mem_maximalIdeal`. -/
theorem mapFun_ι_mem_maximalSmul (Z : Closeds X) {y : X} (hy : y ∈ Z)
    (g : TopCat.Presheaf.stalk (C := Ab.{u}) (sheaf X Z).presheaf y) :
    Stacks.ModuleStalk.mapFun (ι X Z) y g ∈
      Stacks.ModuleStalk.maximalSmul (Stacks.Ample.unitModule X) y :=
  Stacks.IdealSheafModules.mapFun_ι_mem_maximalSmul (data X Z) (mem_support_data X Z hy) g

/-- **Off the closed set the ideal sheaf is the unit ideal**: a point outside `Z` has an open
neighbourhood over which the unit section of `𝒪_X` is a section of `ℐ_Z`. -/
theorem exists_section_app_eq_one (Z : Closeds X) {x : X} (hx : x ∉ Z) :
    ∃ (V : X.Opens) (_ : x ∈ V) (s : Γ(sheaf X Z, V)),
      (ι X Z).app V s = show Γ(Stacks.Ample.unitModule X, V) from (1 : Γ(X, V)) := by
  obtain ⟨U, hxU, hU⟩ :=
    Stacks.Divisors.exists_affineOpens_ideal_eq_top (data X Z) (notMem_support_data X Z hx)
  obtain ⟨s, hs⟩ := Stacks.IdealSheafModules.exists_app_ι_eq_one (data X Z) U
    (hU ▸ Submodule.mem_top)
  exact ⟨(U : X.Opens), hxU, s, hs⟩

/-- **Off the closed set the ideal sheaf has a germ outside `𝔪_x · (𝒪_X)_x`** — the stalk form of
`Stacks.ComplementIdeal.exists_section_app_eq_one`. -/
theorem exists_mapFun_ι_notMem_maximalSmul (Z : Closeds X) {x : X} (hx : x ∉ Z) :
    ∃ g : TopCat.Presheaf.stalk (C := Ab.{u}) (sheaf X Z).presheaf x,
      Stacks.ModuleStalk.mapFun (ι X Z) x g ∉
        Stacks.ModuleStalk.maximalSmul (Stacks.Ample.unitModule X) x := by
  obtain ⟨V, hxV, s, hs⟩ := exists_section_app_eq_one X Z hx
  refine ⟨((sheaf X Z).presheaf.germ V x hxV).hom s, ?_⟩
  rw [Stacks.ModuleStalk.mapFun_germ, hs]
  exact germ_one_notMem_maximalSmul X x V hxV

end Stacks.ComplementIdeal

end
