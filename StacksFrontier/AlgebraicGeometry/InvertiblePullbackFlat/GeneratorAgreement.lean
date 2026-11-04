module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.ChartSaturation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Two generating sections of an invertible module differ by a unit

The uniqueness sentence of the penultimate paragraph of [Stacks, Tag 0BD7] — "`g` and `g'`
differ (multiplicatively) by an element of `𝒪_{Y, y}^*`" — is read upstairs here, where it is a
statement about the two sections `φ^*(g) s` and `φ^*(g') s` of `ℒ` rather than about the
multipliers: on an open on which both generate `ℒ` at every point, their ratio is a unit of the
structure sheaf there.

This is the input the descent of the multipliers needs and the one nothing in this tree produced:
`Stacks.SheafOfModules.generatingLocus_smul_of_isUnit` and
`Stacks.SheafOfModules.mem_generatingLocus_iff_of_restrictₛₗ_eq_smul` *consume* a unit relating
two sections, and `Stacks.InvertiblePullback.forall_mem_generatingLocus_iff_of_exists_base_unit`
consumes one that comes from the base.

## Main results

* `Stacks.SheafOfModules.exists_isUnit_smul_restrictₛₗ_of_subset_generatingLocus`: on an open
  contained in both generating loci, the two sections differ by a unit.
* `Stacks.SheafOfModules.isOpen_inter_generatingLocus`: the open on which the previous result is
  applied — the intersection of two generating loci — is open.
* `Stacks.SheafOfModules.exists_isUnit_smul_grpGerm_of_mem_generatingLocus`: the same relation on
  the stalk at a single point of both generating loci.
* `Stacks.SheafOfModules.exists_isUnit_smul_eq_generator_of_subset_generatingLocus`: a section
  generating at every point of an open, read against a chosen trivialization of `ℒ` there, is a
  *unit* multiple of it. This is the form assumption (5) of [Stacks, Tag 0BD7] is cashed in at:
  one section of `ℒ` on the generic fibre, an affine chart of the generic fibre on which `ℒ` is
  trivial, and the resulting coordinate is a unit of the ring of that chart.

## Implementation notes

The scalar is produced by `Stacks.SheafOfModules.generatorRatio`, whose two arguments are
`Stacks.SheafOfModules.GeneratorSections` over the common open; those are supplied by
`Stacks.SheafOfModules.generatorSectionsOfForallGermNotMemMaximalIdeal`, whose `val` is by
definition the restriction of the given section, so the ratio relates the restrictions
themselves and not merely some pair of generators.

The scalar is bound at the `X.presheaf` spelling of the sections of the structure sheaf rather
than returned as a unit of `(structureSheaf X.sheaf).obj.obj (op W)`: that is the spelling at
which `Stacks.SheafOfModules.generatingLocus_smul_of_isUnit` and its consumers take their
scalars, and the two differ for instance search even though they are equal by `rfl`.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  (L : _root_.SheafOfModules.{u} (structureSheafRing X))
  [IsInvertible X.presheaf (structureSheafRing X).property L]

/-- A section generating at every point of `W` is a unit multiple of any generator over `W`. -/
private theorem exists_isUnit_smul_eq_generator_aux
    {U W : Opens X.carrier} (t : L.val.obj (op U)) (hWU : W ≤ U)
    (hW : (W : Set X.carrier) ⊆ generatingLocus L t) (gen : GeneratorSections X L W) :
    ∃ c : X.presheaf.obj (op W), IsUnit c ∧
      L.val.restrictₛₗ (homOfLE hWU).op t = c • gen.val :=
  let g : GeneratorSections X L W :=
    generatorSectionsOfForallGermNotMemMaximalIdeal L t W hWU fun _ hz =>
      notMem_maximalIdeal_smul_of_mem_generatingLocus L (hW hz) (hWU hz)
  ⟨generatorRatio L W gen g,
    isUnit_of_smul_eq_generator L W gen g _ (generatorRatio_spec L W gen g),
    generatorRatio_spec L W gen g⟩

/-- **The uniqueness clause of [Stacks, Tag 0BD7], upstairs.** Two sections of an invertible `ℒ`
that both generate every stalk over an open `W` differ there by a unit of `𝒪_X(W)`. -/
theorem exists_isUnit_smul_restrictₛₗ_of_subset_generatingLocus
    {U U' W : Opens X.carrier} (t : L.val.obj (op U)) (t' : L.val.obj (op U'))
    (hWU : W ≤ U) (hWU' : W ≤ U')
    (hW : (W : Set X.carrier) ⊆ generatingLocus L t)
    (hW' : (W : Set X.carrier) ⊆ generatingLocus L t') :
    ∃ c : X.presheaf.obj (op W), IsUnit c ∧
      L.val.restrictₛₗ (homOfLE hWU).op t = c • L.val.restrictₛₗ (homOfLE hWU').op t' := by
  exact exists_isUnit_smul_eq_generator_aux L t hWU hW
    (generatorSectionsOfForallGermNotMemMaximalIdeal L t' W hWU' fun z hz =>
      notMem_maximalIdeal_smul_of_mem_generatingLocus L (hW' hz) (hWU' hz))

/-- The intersection of the generating loci of two sections of an invertible module is open. -/
theorem isOpen_inter_generatingLocus {U U' : Opens X.carrier} (t : L.val.obj (op U))
    (t' : L.val.obj (op U')) :
    IsOpen (generatingLocus L t ∩ generatingLocus L t') :=
  (isOpen_generatingLocus L t).inter (isOpen_generatingLocus L t')

/-- **A section generating at every point of an open is a unit times any trivialization
there.** The open carries a generator `gen` of `ℒ`; the section `t` generates at every point of
it; so the coordinate of `t` against `gen` is a unit of `𝒪_X` on that open, not merely a
nonvanishing germ at one point.

This is where a *global* trivializing section is worth more than invertibility of `ℒ`:
invertibility makes every point of `X` lie in the generating locus of *some* section, which
gives a unit only after shrinking the open to that section's locus, while one section
generating at every point of `W` gives a unit on the whole of `W`. -/
@[ega "0 5.5.2" "partial"]
theorem exists_isUnit_smul_eq_generator_of_subset_generatingLocus
    {U W : Opens X.carrier} (t : L.val.obj (op U)) (hWU : W ≤ U)
    (hW : (W : Set X.carrier) ⊆ generatingLocus L t) (gen : GeneratorSections X L W) :
    ∃ c : X.presheaf.obj (op W), IsUnit c ∧
      L.val.restrictₛₗ (homOfLE hWU).op t = c • gen.val :=
  exists_isUnit_smul_eq_generator_aux L t hWU hW gen

/-- **The uniqueness clause of [Stacks, Tag 0BD7] on a stalk.** At a point at which two sections
of an invertible `ℒ` both generate, their germs differ by a unit of the local ring — the form in
which `AlgebraicGeometry.exists_isUnit_mul_eq_of_isUnit_stalkMap` consumes the relation. -/
theorem exists_isUnit_smul_grpGerm_of_mem_generatingLocus
    {U U' : Opens X.carrier} (t : L.val.obj (op U)) (t' : L.val.obj (op U'))
    {x : X.carrier} (hx : x ∈ generatingLocus L t) (hx' : x ∈ generatingLocus L t')
    (hxU : x ∈ U) (hxU' : x ∈ U') :
    ∃ c : ringStalk X x, IsUnit c ∧
      grpGerm X L.val x U hxU t = c • grpGerm X L.val x U' hxU' t' := by
  let W : Opens X.carrier := ⟨_, isOpen_inter_generatingLocus L t t'⟩
  have hxW : x ∈ W := ⟨hx, hx'⟩
  have hWU : W ≤ U := fun z hz => generatingLocus_le L t hz.1
  have hWU' : W ≤ U' := fun z hz => generatingLocus_le L t' hz.2
  obtain ⟨c, hc, hcc⟩ := exists_isUnit_smul_restrictₛₗ_of_subset_generatingLocus L t t' hWU hWU'
    (fun _ hz => hz.1) (fun _ hz => hz.2)
  refine ⟨ringGerm X x W hxW c, hc.map (ringGerm X x W hxW), ?_⟩
  have hres : ∀ (V : Opens X.carrier) (hVW : W ≤ V) (hxV : x ∈ V) (v : L.val.obj (op V)),
      grpGerm X L.val x W hxW (L.val.restrictₛₗ (homOfLE hVW).op v)
        = grpGerm X L.val x V hxV v := fun V hVW hxV v =>
    TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) L.val.presheaf (homOfLE hVW) x hxW v
  rw [← hres U hWU hxU t, ← hres U' hWU' hxU' t', hcc,
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule_germ_smul]

end Stacks.SheafOfModules

end
