module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal

/-!
# The difference of two lifts of a map of algebraic spaces is a derivation

Let `B` be a big fppf site, `S` a scheme contained in it, `X` an algebraic space over `S` and
`Z ⊆ X` a closed subspace which is a **first-order thickening**, with inclusion `i : Z ⟶ X` and
defining ideal sheaf `𝓘 ⊆ 𝒪_X`, so that `𝓘² = 0` on every object of the small étale site.

Let `R` be a sheaf of rings on the small étale site of `X`, let `φ : R₀ ⟶ R` be a morphism of
sheaves of rings, and let `f, g : R ⟶ 𝒪_X` be two morphisms of sheaves of rings which

* become equal after the structure map `i^♯ : 𝒪_X ⟶ i_*𝒪_Z` of the inclusion, and
* agree on `R₀`, that is `φ ≫ f = φ ≫ g`.

Then the sectionwise difference `f - g` takes values in `𝓘` and is a derivation of `R` over
`R₀` with values in `𝓘`: it is additive, it satisfies the Leibniz rule for the `R`-action on
`𝓘` obtained by restricting scalars along `f`, it kills `R₀`, and it commutes with restriction.

## Main definitions

* `AlgebraicGeometry.Space.liftDifference`: the sectionwise difference `f - g`, as a section of
  the defining ideal of the first-order thickening.

## Main results

* `AlgebraicGeometry.Space.mul_eq_zero_of_mem_definingIdealAt`: two sections of the defining
  ideal of a first-order thickening have product zero.
* `AlgebraicGeometry.Space.liftDifference_add` and
  `AlgebraicGeometry.Space.liftDifference_smul_add_smul`: additivity and the Leibniz rule.
* `AlgebraicGeometry.Space.liftDifference_app_eq_zero`: the derivation kills `R₀`.
* `AlgebraicGeometry.Space.liftDifference_naturality`: the derivation commutes with the
  restriction maps of the small étale site.
* `AlgebraicGeometry.Space.liftDifference_eq_zero_of_apply_eq`: the derivation annihilates a
  section on which the two maps agree.
* `AlgebraicGeometry.Space.firstOrderConormalModuleι_liftDifference`: carried by
  `AlgebraicGeometry.Space.firstOrderConormalModuleIso` into the conormal module `i_*𝒞_{Z/X}` and
  included back into `𝒪_X` by `AlgebraicGeometry.Space.firstOrderConormalModuleι`, the derivation
  is `f - g`.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
-/

@[expose] public section

open CategoryTheory
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

/-- If the product of the two differences `a - c` and `b - d` vanishes, then
`a * b - c * d = a * (b - d) + b * (a - c)`. -/
private theorem mul_sub_mul_eq_of_mul_sub_eq_zero {A : Type*} [CommRing A] {a b c d : A}
    (h : (a - c) * (b - d) = 0) : a * b - c * d = a * (b - d) + b * (a - c) := by
  linear_combination -h

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} (Z : ClosedSubspaces B S hS X.1)

/-! ### The defining ideal of a first-order thickening is square zero on sections -/

/-- The product of two sections of the defining ideal of a closed subspace `Z ⊆ X` which is a
first-order thickening, over the same object of the small étale site of `X`, vanishes. -/
theorem mul_eq_zero_of_mem_definingIdealAt (hZ : IsFirstOrderThickening B S hS X Z.1)
    {U : (SmallEtale B S hS X.1)ᵒᵖ} {u v : (structureRingSheaf B S hS X).obj.obj U}
    (hu : u ∈ definingIdealAt B S hS X Z U) (hv : v ∈ definingIdealAt B S hS X Z U) :
    u * v = 0 := by
  have h := hZ.2 U.unop
  rw [Submodule.pow_succ, Submodule.pow_one] at h
  exact (Submodule.eq_bot_iff _).mp h _ (Ideal.mul_mem_mul hu hv)

/-! ### The difference of two lifts -/

variable {R₀ R : Sheaf (SmallEtale.topology B S hS X.1) RingCat.{u}}
  (φ : R₀ ⟶ R) (f g : R ⟶ structureRingSheaf B S hS X)

/-- The difference of two maps into the structure sheaf which agree on a closed subspace: if
`f, g : R ⟶ 𝒪_X` become equal after the structure map `i^♯ : 𝒪_X ⟶ i_*𝒪_Z` of the inclusion of
a closed subspace `Z ⊆ X`, the sectionwise difference `f - g`, as a section of the defining ideal
of `Z`, the sectionwise kernel of `i^♯`. -/
noncomputable def liftDifference
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r : R.obj.obj U) :
    definingIdealAt B S hS X Z U :=
  ⟨f.hom.app U r - g.hom.app U r, by
    have h : ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom
          (f.hom.app U r) =
        ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom
          (g.hom.app U r) :=
      ConcreteCategory.congr_hom (congrArg (fun t => t.hom.app U) hfg) r
    change _ ∈ RingHom.ker
      ((structureSharp B S hS (subspaceInclusion B S hS X Z)).hom.app U).hom
    rw [RingHom.mem_ker, map_sub, h, sub_self]⟩

/-- The underlying section of `AlgebraicGeometry.Space.liftDifference` is the difference of the
two maps. -/
@[simp]
theorem liftDifference_coe
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r : R.obj.obj U) :
    ((liftDifference B S hS Z f g hfg U r : definingIdealAt B S hS X Z U) :
        (structureRingSheaf B S hS X).obj.obj U) =
      f.hom.app U r - g.hom.app U r :=
  rfl

/-- The difference of two lifts is additive. -/
theorem liftDifference_add
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r s : R.obj.obj U) :
    liftDifference B S hS Z f g hfg U (r + s) =
      liftDifference B S hS Z f g hfg U r + liftDifference B S hS Z f g hfg U s :=
  Subtype.ext (by
    rw [liftDifference_coe, AddMemClass.coe_add, liftDifference_coe, liftDifference_coe, map_add,
      map_add]
    abel)

/-- The difference of two lifts takes a difference of sections to the difference of its values. -/
theorem liftDifference_sub
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r s : R.obj.obj U) :
    liftDifference B S hS Z f g hfg U (r - s) =
      liftDifference B S hS Z f g hfg U r - liftDifference B S hS Z f g hfg U s :=
  Subtype.ext (by
    rw [liftDifference_coe, AddSubgroupClass.coe_sub, liftDifference_coe, liftDifference_coe,
      map_sub, map_sub]
    abel)

/-- The Leibniz rule for the difference `D` of two lifts into a first-order thickening, for the
`R`-action on the defining ideal obtained by restricting scalars along `f`:
`D (r * s) = f r • D s + f s • D r`. -/
theorem liftDifference_smul_add_smul (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r s : R.obj.obj U) :
    liftDifference B S hS Z f g hfg U (r * s) =
      f.hom.app U r • liftDifference B S hS Z f g hfg U s +
        f.hom.app U s • liftDifference B S hS Z f g hfg U r :=
  Subtype.ext (by
    have hz := mul_eq_zero_of_mem_definingIdealAt B S hS Z hZ
      (liftDifference B S hS Z f g hfg U r).2 (liftDifference B S hS Z f g hfg U s).2
    rw [liftDifference_coe, liftDifference_coe] at hz
    rw [liftDifference_coe, AddMemClass.coe_add, Submodule.coe_smul, Submodule.coe_smul,
      smul_eq_mul, smul_eq_mul, liftDifference_coe, liftDifference_coe, map_mul, map_mul]
    exact mul_sub_mul_eq_of_mul_sub_eq_zero
      (A := ToType ((structureSheaf B S hS X.1 X.2).obj.obj U)) hz)

/-- The difference of two lifts vanishes on a section on which the two maps agree. -/
private theorem liftDifference_eq_zero_of_agree
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    {U : (SmallEtale B S hS X.1)ᵒᵖ} {r : R.obj.obj U}
    (hr : f.hom.app U r = g.hom.app U r) :
    liftDifference B S hS Z f g hfg U r = 0 :=
  Subtype.ext (by rw [liftDifference_coe, hr, sub_self, ZeroMemClass.coe_zero])

/-- If the two maps agree on `R₀`, their difference vanishes on sections coming from `R₀`. -/
theorem liftDifference_app_eq_zero
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    (hφ : φ ≫ f = φ ≫ g) (U : (SmallEtale B S hS X.1)ᵒᵖ) (r : R₀.obj.obj U) :
    liftDifference B S hS Z f g hfg U (φ.hom.app U r) = 0 :=
  liftDifference_eq_zero_of_agree B S hS Z f g hfg (ConcreteCategory.congr_hom
    (congrArg (fun t => t.hom.app U) hφ) r)

/-- The difference of two lifts annihilates a section on which the two maps agree. -/
theorem liftDifference_eq_zero_of_apply_eq
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    {U : (SmallEtale B S hS X.1)ᵒᵖ} {r : R.obj.obj U}
    (hr : f.hom.app U r = g.hom.app U r) :
    liftDifference B S hS Z f g hfg U r = 0 :=
  liftDifference_eq_zero_of_agree B S hS Z f g hfg hr

/-- The difference of two lifts commutes with the restriction maps of the small étale site. -/
theorem liftDifference_naturality
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    {U V : (SmallEtale B S hS X.1)ᵒᵖ} (h : U ⟶ V) (r : R.obj.obj U) :
    ((structureRingSheaf B S hS X).obj.map h).hom
        ((liftDifference B S hS Z f g hfg U r : definingIdealAt B S hS X Z U) :
          (structureRingSheaf B S hS X).obj.obj U) =
      ((liftDifference B S hS Z f g hfg V ((R.obj.map h).hom r) :
        definingIdealAt B S hS X Z V) : (structureRingSheaf B S hS X).obj.obj V) := by
  rw [liftDifference_coe, liftDifference_coe, map_sub]
  exact congrArg₂ (· - ·) (ConcreteCategory.congr_hom (f.hom.naturality h) r).symm
    (ConcreteCategory.congr_hom (g.hom.naturality h) r).symm

/-! ### Reading the difference through the conormal module -/

/-- The difference of two lifts into a first-order thickening, carried into the pushed-forward
conormal module `i_*𝒞_{Z/X}` by `AlgebraicGeometry.Space.firstOrderConormalModuleIso` and
included back into `𝒪_X` by `AlgebraicGeometry.Space.firstOrderConormalModuleι`, is `f - g`. -/
theorem firstOrderConormalModuleι_liftDifference (hZ : IsFirstOrderThickening B S hS X Z.1)
    (hfg : f ≫ structureSharp B S hS (subspaceInclusion B S hS X Z) =
      g ≫ structureSharp B S hS (subspaceInclusion B S hS X Z))
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r : R.obj.obj U) :
    (firstOrderConormalModuleι B S hS Z hZ).val.app U
        ((firstOrderConormalModuleIso B S hS Z hZ).hom.val.app U
          (liftDifference B S hS Z f g hfg U r)) =
      f.hom.app U r - g.hom.app U r := by
  change ((firstOrderConormalModuleIso B S hS Z hZ).hom ≫
      firstOrderConormalModuleι B S hS Z hZ).val.app U
    (liftDifference B S hS Z f g hfg U r) = _
  rw [firstOrderConormalModuleIso_hom_comp_firstOrderConormalModuleι B S hS Z hZ]
  rfl

end AlgebraicGeometry.Space

end
