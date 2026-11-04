module

public import StacksFrontier.AlgebraicGeometry.TensorPowerTrivialize.GeneralModule

/-!
# Two trivializations of a sheaf of modules over one object differ by a unit

Let `𝒪` be a sheaf of commutative rings on a site and `M` a sheaf of `𝒪`-modules which is
**trivial over an object `U`**, meaning that its restriction to the localized site over `U` is
isomorphic to the structure sheaf there. Such a trivialization `e` singles out the section
`Stacks.SheafOfModules.TensorGenerator.generator` of `M` over `U` that it sends to `1`.

Two trivializations of the same `M` over the same `U` single out two such sections, and this file
proves that **they differ by a unit of the functions on `U`**; and, on the way, that every section
of `M` over `U` is a function multiple of either of them, so that a trivialized module has
rank one on sections in the elementary sense.

This is the relative analogue of
`Stacks.GradedRing.exists_unit_smul_of_bijective_toSpanSingleton`, which says the same for two
generators of a rank-one module over a commutative ring, and it is the input that the canonicity
of Tag 02NC's comparison over one chart of the base consumes: the degreewise effect of rescaling
the local section by a function is
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.psiSectionAt_eq_degreeScale_comp`, and what that
lemma takes as given — that two sections trivializing the twisting module over one open are
related by such a rescaling — is what is proved here.

## Main definitions

* `Stacks.SheafOfModules.TensorGenerator.coord`: the coordinate of a section of `M` over `U` in a
  trivialization — the function whose multiple of the generator it is.
* `Stacks.SheafOfModules.TensorGenerator.rep`: the section of `M` over `U` that a function
  represents in a trivialization. `rep` and `coord` are mutually inverse, and `rep e 1` is the
  generator.

## Main results

* `Stacks.SheafOfModules.TensorGenerator.coord_generator`: a trivialization carries its own
  generator to `1`.
* `Stacks.SheafOfModules.TensorGenerator.smul_generator`: **every section of `M` over `U` is a
  function multiple of the generator**, the function being its coordinate.
* `Stacks.SheafOfModules.TensorGenerator.bijective_smul_generator`: multiplication by the
  generator is a bijection from the functions on `U` to the sections of `M` over `U`. This is the
  hypothesis shape of `Stacks.GradedRing.exists_unit_smul_of_bijective_toSpanSingleton`.
* `Stacks.SheafOfModules.TensorGenerator.exists_unit_smul_generator`: **two trivializations of
  `M` over `U` have generators differing by a unit of the functions on `U`.**

## Implementation notes

Nothing here touches the tensor product, the sheafification or the monoidal structure: the whole
argument runs inside the single `ModuleCat` isomorphism that a trivialization induces on the
sections over the terminal object `𝟙 U` of the localized site, read off from the two triangle
identities of the isomorphism of sheaves of modules.

**No statement below mentions the sections of `SheafOfModules.unit`**, and that is forced rather
than stylistic. `(SheafOfModules.unit R).val.obj X` is the ring `R.obj.obj X` only after
unfolding `PresheafOfModules.unit`, which instance search does not do, so at that type there is
no `One` instance and no `SMul` instance: neither `1` nor `c • t` elaborates there, and type
ascription does not help. The functions on `U` are therefore spelled
`(TensorSheafification.structureSheaf 𝒪 h𝒪).obj.obj (op U)` and the sections of `M`
`M.val.obj (op U)` — at which spellings the action *is* found — and the crossing into the
localized site happens only inside `coord` and `rep`, in term position, where a function argument
is checked against the expected type and the two spellings are definitionally equal. The same
phenomenon on the consuming side is recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeCanonical`.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.SheafOfModules.TensorSheafification

universe v u w

namespace Stacks.SheafOfModules.TensorGenerator

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{w})
  (h𝒪 : Presheaf.IsSheaf J (structureRingPresheaf 𝒪))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (U : C)
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  (M : SheafOfModules.{w} (structureSheaf 𝒪 h𝒪))
  (e : M.over U ≅ SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U))

/-- The coordinate of a section of `M` over `U` in a trivialization of `M` there: the function on
`U` whose multiple of the generator the section is. -/
def coord (t : M.val.obj (op U)) : (structureSheaf 𝒪 h𝒪).obj.obj (op U) :=
  (e.hom.val.app (op (Over.mk (𝟙 U)))).hom t

/-- The section of `M` over `U` that a function on `U` represents in a trivialization. -/
def rep (r : (structureSheaf 𝒪 h𝒪).obj.obj (op U)) : M.val.obj (op U) :=
  (e.inv.val.app (op (Over.mk (𝟙 U)))).hom r

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **The generator is what `1` represents.** -/
theorem rep_one : rep 𝒪 h𝒪 U M e 1 = generator 𝒪 h𝒪 U M e := rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- The coordinate map of a trivialization is linear. -/
theorem coord_smul (r : (structureSheaf 𝒪 h𝒪).obj.obj (op U)) (t : M.val.obj (op U)) :
    coord 𝒪 h𝒪 U M e (r • t) = r * coord 𝒪 h𝒪 U M e t :=
  (e.hom.val.app (op (Over.mk (𝟙 U)))).hom.map_smul r t

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- The representation map of a trivialization is linear: it turns multiplication of functions
into the action of a function on a section. -/
theorem rep_mul (r s : (structureSheaf 𝒪 h𝒪).obj.obj (op U)) :
    rep 𝒪 h𝒪 U M e (r * s) = r • rep 𝒪 h𝒪 U M e s :=
  (e.inv.val.app (op (Over.mk (𝟙 U)))).hom.map_smul r s

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- Representing a function and reading its coordinate off again gives the function back. -/
theorem coord_rep (r : (structureSheaf 𝒪 h𝒪).obj.obj (op U)) :
    coord 𝒪 h𝒪 U M e (rep 𝒪 h𝒪 U M e r) = r :=
  congrArg (fun k : SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U) ⟶
      SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U) =>
    (k.val.app (op (Over.mk (𝟙 U)))).hom r) e.inv_hom_id

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- Reading the coordinate of a section and representing it again gives the section back. -/
theorem rep_coord (t : M.val.obj (op U)) :
    rep 𝒪 h𝒪 U M e (coord 𝒪 h𝒪 U M e t) = t :=
  congrArg (fun k : M.over U ⟶ M.over U => (k.val.app (op (Over.mk (𝟙 U)))).hom t) e.hom_inv_id

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **A trivialization carries its own generator to `1`.** -/
theorem coord_generator : coord 𝒪 h𝒪 U M e (generator 𝒪 h𝒪 U M e) = 1 :=
  (congrArg (coord 𝒪 h𝒪 U M e) (rep_one 𝒪 h𝒪 U M e).symm).trans (coord_rep 𝒪 h𝒪 U M e 1)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **A function multiple of the generator is what that function represents.** -/
theorem smul_generator_eq_rep (r : (structureSheaf 𝒪 h𝒪).obj.obj (op U)) :
    r • generator 𝒪 h𝒪 U M e = rep 𝒪 h𝒪 U M e r :=
  (congrArg (fun y => r • y) (rep_one 𝒪 h𝒪 U M e)).symm.trans
    ((rep_mul 𝒪 h𝒪 U M e r 1).symm.trans (congrArg (rep 𝒪 h𝒪 U M e) (mul_one r)))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **Every section of `M` over `U` is a function multiple of the generator**, the function being
its coordinate in the trivialization. -/
theorem smul_generator (t : M.val.obj (op U)) :
    coord 𝒪 h𝒪 U M e t • generator 𝒪 h𝒪 U M e = t :=
  (smul_generator_eq_rep 𝒪 h𝒪 U M e (coord 𝒪 h𝒪 U M e t)).trans (rep_coord 𝒪 h𝒪 U M e t)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **Multiplication by the generator is a bijection from the functions on `U` to the sections of
`M` over `U`.** This is the hypothesis shape of
`Stacks.GradedRing.exists_unit_smul_of_bijective_toSpanSingleton`, so a trivialized sheaf of
modules has rank one on sections over `U` in the elementary sense. -/
theorem bijective_smul_generator :
    Function.Bijective fun r : (structureSheaf 𝒪 h𝒪).obj.obj (op U) =>
      r • generator 𝒪 h𝒪 U M e := by
  refine ⟨fun r s hrs => ?_, fun t => ⟨coord 𝒪 h𝒪 U M e t, smul_generator 𝒪 h𝒪 U M e t⟩⟩
  have h := congrArg (coord 𝒪 h𝒪 U M e) hrs
  rwa [coord_smul, coord_smul, coord_generator, mul_one, mul_one] at h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify (J.over U) AddCommGrpCat.{w}] in
/-- **Two trivializations of `M` over `U` have generators differing by a unit of the functions on
`U`.**

This is the relative form of `Stacks.GradedRing.exists_unit_smul_of_bijective_toSpanSingleton`:
each trivialization expresses the other's generator as a function multiple of its own, and the
two functions multiply to `1` because a trivialization takes its own generator to `1` and is
linear. -/
theorem exists_unit_smul_generator
    (e' : M.over U ≅ SheafOfModules.unit (SliceRestriction.sliceStructureSheaf 𝒪 h𝒪 U)) :
    ∃ u : ((structureSheaf 𝒪 h𝒪).obj.obj (op U))ˣ,
      generator 𝒪 h𝒪 U M e' =
        (u : (structureSheaf 𝒪 h𝒪).obj.obj (op U)) • generator 𝒪 h𝒪 U M e := by
  have hvu : coord 𝒪 h𝒪 U M e' (generator 𝒪 h𝒪 U M e) *
      coord 𝒪 h𝒪 U M e (generator 𝒪 h𝒪 U M e') = 1 := by
    have hfix : (coord 𝒪 h𝒪 U M e' (generator 𝒪 h𝒪 U M e) *
        coord 𝒪 h𝒪 U M e (generator 𝒪 h𝒪 U M e')) • generator 𝒪 h𝒪 U M e =
        generator 𝒪 h𝒪 U M e := by
      rw [mul_smul, smul_generator 𝒪 h𝒪 U M e (generator 𝒪 h𝒪 U M e'),
        smul_generator 𝒪 h𝒪 U M e' (generator 𝒪 h𝒪 U M e)]
    have hcoord := congrArg (coord 𝒪 h𝒪 U M e) hfix
    rw [coord_smul, coord_generator, mul_one] at hcoord
    exact hcoord
  exact ⟨⟨coord 𝒪 h𝒪 U M e (generator 𝒪 h𝒪 U M e'),
      coord 𝒪 h𝒪 U M e' (generator 𝒪 h𝒪 U M e), by rw [mul_comm]; exact hvu, hvu⟩,
    (smul_generator 𝒪 h𝒪 U M e (generator 𝒪 h𝒪 U M e')).symm⟩

end Stacks.SheafOfModules.TensorGenerator

end
