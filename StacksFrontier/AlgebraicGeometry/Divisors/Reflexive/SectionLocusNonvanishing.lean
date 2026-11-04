module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionIsomorphismLocus

/-!
# The isomorphism locus of a section of an invertible module is its nonvanishing locus

Let `ℱ` be an `𝒪_X`-module on a scheme and `s ∈ Γ(X, ℱ)` a global section.  Two loci are
attached to `s`:

* `AlgebraicGeometry.sectionIsomorphismLocus ℱ s`, the set of points where `s : 𝒪_{X, x} → ℱ_x`
  is an isomorphism — the open `U` of [Stacks, Tag 0EBN];
* `Stacks.SheafOfModules.nonvanishingLocus ℱ s`, the set of points where the germ of `s` is not
  in `𝔪_x ℱ_x` — the open `X_s` of [Stacks, Tag 01CY].

When `ℱ` is invertible these coincide, and that is what [Stacks, Tag 0EBN] uses when it says
that `U ∩ V` is "the set of points where `s|_V` generates this invertible module": it is how the
locus `U` of the tag is fed to [Stacks, Tag 01PW] (2), which is stated about a nonvanishing open.

This file proves that identification and the locality of the isomorphism locus under restriction
to an open; the quasi-compactness of the inclusion `j : U → X` is a Mathlib instance.

## Main definitions

* `AlgebraicGeometry.restrictSections`: the restriction to an open of a global section.

## Main results

* `Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_of_bijective_toSpanSingleton`: the
  algebraic content — a free generator of a module over a local ring is not in `𝔪 M`.
* `Stacks.SheafOfModules.mem_nonvanishingLocus_of_bijective_stalkMapL`: a point where the
  section is a stalkwise isomorphism lies in the nonvanishing locus.
* `Stacks.SheafOfModules.mem_nonvanishingLocus_iff_bijective_stalkMapL`: for an invertible
  module the two conditions are equivalent.
* `AlgebraicGeometry.sectionIsomorphismLocus_eq_nonvanishingLocus`: **the two loci of an
  invertible module are equal.**
* `AlgebraicGeometry.sectionIsomorphismLocus_restrict`: **the isomorphism locus is local on the
  base.**

## Implementation notes

**Which inclusion was already available.**  One half of the identification is
`Stacks.SheafOfModules.bijective_stalkMapL_of_mem_nonvanishingLocus` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleTrivialization.lean`, which is where a
trivialization `ℱ ⊗ 𝒩 ≅ 𝒪_X` is used.  The other half is proved here and needs no invertibility
hypothesis: through `Stacks.SheafOfModules.unitStalkLinearEquiv` the stalk of `s : 𝒪_X ⟶ ℱ` is
the map `r ↦ r • s_x`, so bijectivity says `s_x` freely generates `ℱ_x`, and then
`s_x ∈ 𝔪_x ℱ_x` would carry back to `1 ∈ 𝔪_x` along the bijection.  No Nakayama argument and no
finiteness hypothesis on `ℱ_x` is involved.

**Locality of the locus.**  The locus is defined by invertibility of a stalk map of sheaves of
abelian groups; `AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso` identifies the stalk of a
restricted module with the stalk of the original at the image point, and the comparison
`𝒪_X|_V ≅ 𝒪_V` of `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` contributes an isomorphism
which cancels.  The restricted section has to be named for this to be stated at all, and
`AlgebraicGeometry.restrictSections` is defined as the adjoint of the restricted morphism
precisely so that `AlgebraicGeometry.unitHomEquiv_symm_restrictSections` holds by
`Equiv.symm_apply_apply` rather than by a computation with sections.

**Quasi-compactness of `j`.**  The second sentence of the source's proof, that `j : U → X` is
quasi-compact, cites Properties, Lemma 28.5.3, which is [Stacks, Tag 01OX]; the open-immersion
case is a Mathlib instance, so instance search supplies it and nothing is stated here.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

/-! ### The algebraic content -/

/-- **A free generator of a module over a local ring does not lie in `𝔪 M`.**  If `r ↦ r • σ` is
a bijection `R → M` then `σ ∉ 𝔪 • M`: the bijection carries `𝔪 • R = 𝔪` onto `𝔪 • M`, so `σ`
lying in `𝔪 • M` would force `1 ∈ 𝔪`. -/
theorem notMem_maximalIdeal_smul_top_of_bijective_toSpanSingleton
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {σ : M} (h : Function.Bijective (LinearMap.toSpanSingleton R M σ)) :
    σ ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
  intro hσ
  have hsurj : LinearMap.range (LinearMap.toSpanSingleton R M σ) = ⊤ :=
    LinearMap.range_eq_top.2 h.2
  have hmap : Submodule.map (LinearMap.toSpanSingleton R M σ)
      (IsLocalRing.maximalIdeal R • (⊤ : Submodule R R))
      = IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
    rw [Submodule.map_smul'', Submodule.map_top, hsurj]
  rw [← hmap] at hσ
  obtain ⟨r, hr, hre⟩ := hσ
  have hone : LinearMap.toSpanSingleton R M σ 1 = σ := by
    rw [LinearMap.toSpanSingleton_apply, one_smul]
  have h1 : r = 1 := h.1 (hre.trans hone.symm)
  have hle : IsLocalRing.maximalIdeal R • (⊤ : Submodule R R)
      ≤ IsLocalRing.maximalIdeal R :=
    Submodule.smul_le.2 fun a ha n _ => by
      rw [smul_eq_mul]
      exact Ideal.mul_mem_right n _ ha
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    ((Ideal.eq_top_iff_one _).2 (h1 ▸ hle hr))

/-! ### The two loci agree -/

section RingedSpace

variable {X : RingedSpace.{u, u}} [∀ y : X.carrier, IsLocalRing (ringStalk X y)]

/-- **At a point where a global section induces an isomorphism of stalks it does not vanish.**
Through `Stacks.SheafOfModules.unitStalkLinearEquiv` the stalk of `s : 𝒪_X ⟶ L` is the map
`r ↦ r • s_x`, so its bijectivity says `s_x` is a free generator of `L_x`, and
`notMem_maximalIdeal_smul_top_of_bijective_toSpanSingleton` then puts `s_x` outside `𝔪_x L_x`.

No invertibility hypothesis is needed for this direction; the converse,
`Stacks.SheafOfModules.bijective_stalkMapL_of_mem_nonvanishingLocus`, is where a trivialization
of `L` enters. -/
theorem mem_nonvanishingLocus_of_bijective_stalkMapL
    (L : _root_.SheafOfModules.{u} (structureSheafRing X)) (s : L.sections) (x : X.carrier)
    (h : Function.Bijective (stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val
      L.val (L.unitHomEquiv.symm s).val x)) :
    x ∈ nonvanishingLocus L s := by
  have hcomp : (stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val L.val
        (L.unitHomEquiv.symm s).val x) ∘ (unitStalkLinearEquiv X x)
      = LinearMap.toSpanSingleton (ringStalk X x) (grpStalk X L.val x) (globalGerm L s x) :=
    funext (stalkMapL_unitStalkLinearEquiv L s x)
  have hspan : Function.Bijective
      (LinearMap.toSpanSingleton (ringStalk X x) (grpStalk X L.val x) (globalGerm L s x)) := by
    rw [← hcomp]
    exact h.comp (unitStalkLinearEquiv X x).bijective
  exact notMem_maximalIdeal_smul_top_of_bijective_toSpanSingleton hspan

/-- **For an invertible module the nonvanishing locus of a global section is exactly the locus
where the section induces an isomorphism of stalks.**  This is the identification
[Stacks, Tag 0EBN] makes when it says that `U ∩ V` is the set of points where `s|_V` generates
the invertible module `ℱ|_V`. -/
theorem mem_nonvanishingLocus_iff_bijective_stalkMapL
    (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    [IsInvertible X.presheaf (structureSheafRing X).property L] (s : L.sections)
    (x : X.carrier) :
    x ∈ nonvanishingLocus L s ↔
      Function.Bijective (stalkMapL X (_root_.SheafOfModules.unit (structureSheafRing X)).val
        L.val (L.unitHomEquiv.symm s).val x) := by
  refine ⟨fun hx => ?_, mem_nonvanishingLocus_of_bijective_stalkMapL L s x⟩
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  exact bijective_stalkMapL_of_mem_nonvanishingLocus ψ s x hx

end RingedSpace

end Stacks.SheafOfModules

/-! ### On a scheme -/

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Membership of `AlgebraicGeometry.sectionIsomorphismLocus` read as bijectivity of the
`𝒪_{X, x}`-linear stalk map of [Stacks, Tag 01CB].  The two are the same statement: the locus is
defined by invertibility of the stalk of `𝒪_X ⟶ ℱ` in sheaves of abelian groups, and
`Stacks.SheafOfModules.bijective_stalkFunctor_iff` says that this is bijectivity of the linear
stalk map. -/
theorem mem_sectionIsomorphismLocus_iff_bijective_stalkMapL (F : X.Modules)
    (s : F.sections) (x : X) :
    x ∈ sectionIsomorphismLocus F s ↔
      Function.Bijective (Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL
        X.toRingedSpace
        (_root_.SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val F.val
        (F.unitHomEquiv.symm s).val x) :=
  mem_sectionIsomorphismLocus_iff F s x

/-- **The identification [Stacks, Tag 0EBN] uses**: for an invertible `𝒪_X`-module the locus
where a global section induces an isomorphism of stalks is exactly its nonvanishing locus, the
set of points where the section generates the module.  This is the step of the source's proof
that reads `U ∩ V` as the set of points where `s|_V` generates `ℱ|_V`. -/
theorem sectionIsomorphismLocus_eq_nonvanishingLocus (F : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property F]
    (s : F.sections) :
    sectionIsomorphismLocus F s
      = Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) F s := by
  have hloc : ∀ y : X.toRingedSpace.carrier,
      IsLocalRing (Stacks.SheafOfModules.TensorStalkRingedSpace.ringStalk X.toRingedSpace y) :=
    fun y => X.isLocalRing y
  exact Set.ext fun x => (mem_sectionIsomorphismLocus_iff_bijective_stalkMapL F s x).trans
    (Stacks.SheafOfModules.mem_nonvanishingLocus_iff_bijective_stalkMapL
      (X := X.toRingedSpace) F s x).symm

/-! ### Locality of the isomorphism locus -/

/-- Membership of `AlgebraicGeometry.sectionIsomorphismLocus` as invertibility of the image of
the section's morphism under "restrict to the stalk at `x`". -/
theorem mem_sectionIsomorphismLocus_iff_isIso_map (F : X.Modules) (s : F.sections) (x : X) :
    x ∈ sectionIsomorphismLocus F s ↔
      IsIso ((Scheme.Modules.toPresheaf X ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (F.unitHomEquiv.symm s)) :=
  Iff.rfl

/-- The restriction to an open `V ⊆ X` of a global section of an `𝒪_X`-module, as a global
section of the restricted module.  It is the adjoint of the restriction of the morphism
`𝒪_X ⟶ ℱ` attached to the section, read through
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`. -/
def restrictSections (V : X.Opens) (F : X.Modules) (s : F.sections) :
    (Scheme.Modules.restrict F V.ι).sections :=
  (Scheme.Modules.restrict F V.ι).unitHomEquiv
    ((Scheme.Modules.restrictUnitIso V.ι).inv ≫
      (Scheme.Modules.restrictFunctor V.ι).map (F.unitHomEquiv.symm s))

/-- The morphism `𝒪_V ⟶ ℱ|_V` attached to the restricted section is the restriction of the
morphism attached to the section. -/
theorem unitHomEquiv_symm_restrictSections (V : X.Opens) (F : X.Modules) (s : F.sections) :
    (Scheme.Modules.restrict F V.ι).unitHomEquiv.symm (restrictSections V F s)
      = (Scheme.Modules.restrictUnitIso V.ι).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).map (F.unitHomEquiv.symm s) :=
  Equiv.symm_apply_apply _ _

/-- **The isomorphism locus of a section is local on the base**: the locus of the restricted
section on an open `V` is the preimage in `V` of the locus on `X`.

The locus is defined by invertibility of a stalk map, restriction along an open immersion
commutes with taking stalks (`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`), and the
comparison `𝒪_X|_V ≅ 𝒪_V` contributes an isomorphism which may be cancelled.  No hypothesis on
`V` or on `ℱ` is needed.

This is the statement recorded as missing in the module docstring of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/SectionLocusCodimension.lean`. -/
theorem sectionIsomorphismLocus_restrict (V : X.Opens) (F : X.Modules) (s : F.sections) :
    sectionIsomorphismLocus (Scheme.Modules.restrict F V.ι) (restrictSections V F s)
      = V.ι.base ⁻¹' sectionIsomorphismLocus F s := by
  ext y
  rw [mem_sectionIsomorphismLocus_iff_isIso_map, Set.mem_preimage,
    mem_sectionIsomorphismLocus_iff_isIso_map, unitHomEquiv_symm_restrictSections]
  have hmc : (Scheme.Modules.toPresheaf V.toScheme ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((Scheme.Modules.restrictUnitIso V.ι).inv ≫
          (Scheme.Modules.restrictFunctor V.ι).map (F.unitHomEquiv.symm s))
      = (Scheme.Modules.toPresheaf V.toScheme ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
          (Scheme.Modules.restrictUnitIso V.ι).inv ≫
        (Scheme.Modules.restrictFunctor V.ι ⋙ Scheme.Modules.toPresheaf V.toScheme ⋙
          TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map (F.unitHomEquiv.symm s) :=
    Functor.map_comp _ _ _
  rw [hmc]
  have : IsIso (Scheme.Modules.restrictUnitIso V.ι).inv := Iso.isIso_inv _
  have : IsIso ((Scheme.Modules.toPresheaf V.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        (Scheme.Modules.restrictUnitIso V.ι).inv) :=
    Functor.map_isIso _ _
  rw [isIso_comp_left_iff]
  exact NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso V.ι y) _

end AlgebraicGeometry

end
