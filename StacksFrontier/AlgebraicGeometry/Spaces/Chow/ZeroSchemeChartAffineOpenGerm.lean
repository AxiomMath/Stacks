module

public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ZeroSchemeChartDeltaDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local equations of an ideal sheaf on an affine open, and the kernel of a composite

Let `x` be a point of a scheme `Y`, `U ∋ x` an affine open and `a` a function on `U` generating
the ideal which an ideal sheaf `D` attaches to `U`. Then the germ of `a` at `x` generates the
stalk of `D`, is a nonzerodivisor of `𝒪_{Y,x}` if `a` is one on `U`, and lies in the maximal
ideal if `x` lies in the support of `D`.

`StacksFrontier/AlgebraicGeometry/Spaces/Chow/ZeroSchemeChartDeltaDimension.lean` has these three
consequences for `U = ⊤` on an **affine** scheme and for the ideal sheaf
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop` induced by an ideal of global sections.
This file states them for an arbitrary affine *open* of an arbitrary scheme and an arbitrary
ideal sheaf.

It also proves two structural lemmas with no affineness: the δ-dimension drop at a closed
subscheme which has a nonzerodivisor local equation **somewhere** around each of its points, and
the kernel of a composite of two closed immersions in terms of an ideal sheaf pulling back to the
kernel of the inner one.

## Main results

* `AlgebraicGeometry.Scheme.germ_mem_nonZeroDivisors_stalk`,
  `AlgebraicGeometry.Scheme.germ_isSMulRegular_stalk`: the germ at a point of an affine open of a
  nonzerodivisor there is a nonzerodivisor of the local ring.
* `AlgebraicGeometry.Scheme.germ_mem_maximalIdeal_of_mem_support`: at a point of the support of an
  ideal sheaf the germ of a section of the ideal is not a unit.
* `Stacks.Chow.schemeDeltaDimension_subschemeι_le_of_forall_exists_affineOpen`: **the δ-dimension
  drop with no affineness.**  An ideal sheaf with a nonzerodivisor local equation on some affine
  open around each point of its support cuts out a closed subscheme of δ-dimension one less than a
  bound for the ambient scheme.
* `Stacks.Chow.cycleAssociatedToClosedSubscheme_eq_ker_subschemeι`: the cycle of Stacks 02QU of a
  closed immersion is the cycle of the closed subscheme cut out by its kernel.
* `AlgebraicGeometry.Scheme.ker_comp_eq_sup_of_ker_eq_comap`: **the kernel of a composite of
  closed immersions, with no affineness.**  If the kernel of `p₂ : T ⟶ M` is the inverse image
  along a closed immersion `p₁ : M ⟶ Y` of an ideal sheaf `E` on `Y`, then the kernel of
  `p₂ ≫ p₁` is `p₁.ker ⊔ E`.

## Implementation notes

The affine statements in `ZeroSchemeChartDeltaDimension.lean` are not special cases of these:
they are stated for `AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop`, whose ideal over `⊤` is
the given ideal of global sections only because the scheme is affine, whereas these are stated for
the ideal an arbitrary ideal sheaf attaches to the affine open.  The third of them, the
principality of the stalk, needs no generalisation at all:
`AlgebraicGeometry.IdealSheafData.stalk_eq_span_germ_of_ideal_eq_span` already states it for an
arbitrary ideal sheaf and an arbitrary affine open.

`AlgebraicGeometry.Scheme.ker_comp_eq_sup_of_ker_eq_comap` is the ideal-sheaf form of
`AlgebraicGeometry.Scheme.ker_comp_eq_sup_ofIdealTop`, which asks for both `Y` and `M` affine
because it compares ideals of global sections.  Here the comparison is made over each affine open
`U` of `Y` separately: `p₁ ⁻¹ᵁ U` is affine because a closed immersion is an affine morphism, the
sections of a composite are the composite of the sections, and the preimage along the surjection
`p₁.app U` of the extension of an ideal is that ideal together with the kernel
(`Ideal.comap_map_of_surjective`); the surjection is
`AlgebraicGeometry.Scheme.Hom.app_surjective`.

## References

* [Stacks Project, Tag 0EPI](https://stacks.math.columbia.edu/tag/0EPI)
* [Stacks Project, Tag 0EQL](https://stacks.math.columbia.edu/tag/0EQL)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

/-- **A nonzerodivisor on an affine open has nonzerodivisor germs.**  The germ at a point of an
affine open of a nonzerodivisor on that open is a nonzerodivisor of the local ring. -/
@[ega "IV 20.1.3" "special case"]
theorem germ_mem_nonZeroDivisors_stalk {Y : Scheme.{u}} (U : Y.affineOpens) {g : Γ(Y, U.1)}
    (hg : g ∈ nonZeroDivisors Γ(Y, U.1)) (y : Y) (hyU : y ∈ U.1) :
    (Y.presheaf.germ U.1 y hyU).hom g ∈ nonZeroDivisors (Y.presheaf.stalk y) := by
  let : Algebra Γ(Y, U.1) (Y.presheaf.stalk y) :=
    (Y.presheaf.germ U.1 y hyU).hom.toAlgebra
  have := U.2.isLocalization_stalk ⟨y, hyU⟩
  have : Module.Flat Γ(Y, U.1) (Y.presheaf.stalk y) :=
    IsLocalization.flat (Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
  have hstalk : IsLeftRegular ((Y.presheaf.germ U.1 y hyU).hom g) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Y.presheaf.stalk y) hg
  exact isRegular_iff_mem_nonZeroDivisors.1 (isLeftRegular_iff_isRegular.1 hstalk)

/-- The germ of a nonzerodivisor on an affine open is a regular element of the local ring. -/
theorem germ_isSMulRegular_stalk {Y : Scheme.{u}} (U : Y.affineOpens) {g : Γ(Y, U.1)}
    (hg : g ∈ nonZeroDivisors Γ(Y, U.1)) (y : Y) (hyU : y ∈ U.1) :
    IsSMulRegular (Y.presheaf.stalk y) ((Y.presheaf.germ U.1 y hyU).hom g) :=
  (isRegular_iff_mem_nonZeroDivisors.2 (germ_mem_nonZeroDivisors_stalk U hg y hyU)).left

/-- **At a point of the support of an ideal sheaf the germ of a section of the ideal is not a
unit.** -/
theorem germ_mem_maximalIdeal_of_mem_support {Y : Scheme.{u}} (I : Y.IdealSheafData)
    (U : Y.affineOpens) {g : Γ(Y, U.1)} (hgI : g ∈ I.ideal U) (y : Y) (hyU : y ∈ U.1)
    (hy : y ∈ I.support) :
    (Y.presheaf.germ U.1 y hyU).hom g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) hyU, Scheme.mem_zeroLocus_iff] at hy
  exact (IsLocalRing.mem_maximalIdeal _).2 fun h => hy g hgI ((Y.mem_basicOpen g y hyU).2 h)

end AlgebraicGeometry.Scheme

namespace Stacks.Chow

open _root_.AlgebraicGeometry

/-- **The δ-dimension drop at a closed subscheme with a nonzerodivisor local equation around each
of its points.**  If the ambient scheme has δ-dimension at most `k + 1`, and every point of the
support of an ideal sheaf `Dz` has *some* affine open neighbourhood on which the ideal of `Dz`
contains a nonzerodivisor, then the closed subscheme cut out by `Dz` has δ-dimension at most
`k`. -/
theorem schemeDeltaDimension_subschemeι_le_of_forall_exists_affineOpen
    (C : ChowSituation.{u}) {Y : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    (Dz : Y.IdealSheafData) {k : ℤ}
    (hY : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (hloc : ∀ y ∈ Dz.support, ∃ (U : Y.affineOpens), y ∈ U.1 ∧ ∃ (a : Γ(Y, U.1)),
      a ∈ nonZeroDivisors Γ(Y, U.1) ∧ a ∈ Dz.ideal U) :
    schemeDeltaDimension C (Dz.subschemeι ≫ f) ≤ (k : EInt) := by
  refine schemeDeltaDimension_comp_le_of_forall_exists_nonZeroDivisors_stalk C f _ hY fun w => ?_
  have hmem : Dz.subschemeι w ∈ Dz.support := by
    have : Dz.subschemeι w ∈ Set.range Dz.subschemeι := ⟨w, rfl⟩
    rwa [Scheme.IdealSheafData.range_subschemeι] at this
  obtain ⟨U, hyU, a, ha, haI⟩ := hloc _ hmem
  exact ⟨_, AlgebraicGeometry.Scheme.germ_mem_nonZeroDivisors_stalk U ha _ hyU,
    AlgebraicGeometry.Scheme.germ_mem_maximalIdeal_of_mem_support Dz U haI _ hyU hmem⟩

/-- **The cycle of Stacks 02QU of a closed immersion is the cycle of the closed subscheme its
kernel cuts out.** -/
theorem cycleAssociatedToClosedSubscheme_eq_ker_subschemeι
    (C : ChowSituation.{u}) {Y W : Scheme.{u}} (f : Y ⟶ C.S) [LocallyOfFiniteType f]
    (j : W ⟶ Y) [IsClosedImmersion j] (k : ℤ) :
    cycleAssociatedToClosedSubscheme C f j k =
      cycleAssociatedToClosedSubscheme C f j.ker.subschemeι k := by
  have hker : j.ker.subschemeι.ker = j.ker := Scheme.IdealSheafData.ker_subschemeι _
  have : IsIso (IsClosedImmersion.lift j.ker.subschemeι j hker.le) :=
    IsClosedImmersion.isIso_lift j.ker.subschemeι j hker
  exact cycleAssociatedToClosedSubscheme_eq_of_iso C f j j.ker.subschemeι
    (asIso (IsClosedImmersion.lift j.ker.subschemeι j hker.le))
    (IsClosedImmersion.lift_fac j.ker.subschemeι j hker.le) k

end Stacks.Chow

namespace AlgebraicGeometry.Scheme

/-- **The kernel of a composite of closed immersions, with no affineness.**  Let `p₁ : M ⟶ Y` be
a closed immersion, let `p₂ : T ⟶ M` be quasi-compact, and let `E` be an ideal sheaf on `Y` whose
inverse image along `p₁` is the kernel of `p₂`.  Then the kernel of `p₂ ≫ p₁` is the kernel of
`p₁` together with `E`. -/
theorem ker_comp_eq_sup_of_ker_eq_comap {T M Y : Scheme.{u}} (p₂ : T ⟶ M) (p₁ : M ⟶ Y)
    [IsClosedImmersion p₁] [QuasiCompact p₂] (E : Y.IdealSheafData)
    (h : p₂.ker = E.comap p₁) :
    (p₂ ≫ p₁).ker = p₁.ker ⊔ E := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  have hpre : IsAffineOpen (p₁ ⁻¹ᵁ U.1) := U.2.preimage p₁
  have h2 : RingHom.ker (p₂.app (p₁ ⁻¹ᵁ U.1)).hom = Ideal.map (p₁.app U.1).hom (E.ideal U) := by
    rw [← Scheme.Hom.ker_apply p₂ ⟨p₁ ⁻¹ᵁ U.1, hpre⟩, h,
      Stacks.IdealSheaf.ideal_comap_appLE E p₁ U ⟨p₁ ⁻¹ᵁ U.1, hpre⟩ le_rfl,
      Scheme.Hom.appLE_eq_app]
  have hcomp : RingHom.ker ((p₂ ≫ p₁).app U.1).hom =
      Ideal.comap (p₁.app U.1).hom (RingHom.ker (p₂.app (p₁ ⁻¹ᵁ U.1)).hom) :=
    (RingHom.comap_ker _ _).symm
  have hL : (p₂ ≫ p₁).ker.ideal U = E.ideal U ⊔ RingHom.ker (p₁.app U.1).hom := by
    rw [Scheme.Hom.ker_apply (p₂ ≫ p₁) U, hcomp, h2,
      Ideal.comap_map_of_surjective _ (Scheme.Hom.app_surjective p₁ U.1 U.2) (E.ideal U)]
    rfl
  have hR : (p₁.ker ⊔ E).ideal U = RingHom.ker (p₁.app U.1).hom ⊔ E.ideal U := by
    rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, Scheme.Hom.ker_apply]
  rw [hL, hR, sup_comm]

end AlgebraicGeometry.Scheme

end
