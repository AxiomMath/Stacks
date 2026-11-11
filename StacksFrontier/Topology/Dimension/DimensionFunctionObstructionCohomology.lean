module

public import StacksFrontier.AlgebraicGeometry.Thickenings.PicardSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.SquareZeroExtensionBoundaryDerivation
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.LocalTriviality
public import StacksFrontier.Topology.Sheaves.Sheaf.LocallyConstantInt
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction to a dimension function is an element of `H¹(X, ℤ)` (Stacks 02ID)

Let `X` be a catenary, locally Noetherian, sober topological space. Tag 02IC covers `X` by opens
`U i` carrying dimension functions `δ i`, and tag 02IB makes the differences `δ i - δ j` locally
constant on the overlaps; `TopologicalSpace.DimensionFunction.obstruction` is the class of that
Čech `1`-cocycle in `Ȟ¹(𝒰, ℤ)`. This file carries the class into sheaf cohomology `H¹(X, ℤ)` of
the constant sheaf `ℤ`, shows that the resulting element does not depend on the cover or on the
local dimension functions, and that it vanishes exactly when `X` has a global dimension function.

Three inputs do the work.

* The comparison `Ȟ¹(𝒰, ℱ) → H¹(X, ℱ)` of tag 01EQ,
  `Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections`, is injective
  (`Stacks.Cohomology.SheafTorsor.cechH1ToRightDerivedSections_injective`, tag 0B8R), so the
  image vanishes exactly when the Čech class does.
* The comparison is compatible with refinement
  (`Stacks.Cohomology.SquareZeroBoundary.cechH1ToRightDerivedSections_refinement`), and on a
  common refinement two families of local dimension functions give the same Čech class, because
  their differences are locally constant (tag 02IB). So the element is intrinsic.
* The coefficient sheaf of the Čech construction, the locally constant `ℤ`-valued functions, is
  the constant sheaf `ℤ` (`TopCat.constantSheafIsoLocallyConstantInt`).

## Main definitions

* `TopologicalSpace.DimensionFunction.obstructionH1`: the image in `H¹(X, ℤ)` of the obstruction
  class of a cover with local dimension functions.
* `TopologicalSpace.DimensionFunction.dimensionObstruction`: the obstruction element of
  `H¹(X, ℤ)` of a catenary, locally Noetherian, sober space.
* `TopologicalSpace.DimensionFunction.dimensionObstructionExt`: the same element in Mathlib's
  `Ext`-group cohomology `Sheaf.H ℤ 1`.

## Main results

* `TopologicalSpace.DimensionFunction.obstructionH1_eq`: independence of the cover and of the local
  dimension functions.
* `TopologicalSpace.DimensionFunction.nonempty_dimensionFunction_iff_dimensionObstruction_eq_zero`
  (**02ID**): a dimension function exists if and only if the obstruction element of `H¹(X, ℤ)`
  vanishes; `nonempty_dimensionFunction_iff_dimensionObstructionExt_eq_zero` is the same statement
  in `Sheaf.H`.

## Implementation notes

`H¹(X, ℤ)` is `Stacks.Cohomology.SheafTorsor.sheafCohomologyOne`, the first right-derived functor
of global sections, evaluated at Mathlib's constant sheaf
`(constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj (AddCommGrpCat.of (ULift ℤ))`;
the value is `ULift ℤ`, as in `Sheaf.H`, so that a space in any universe is covered. The
identification with `Sheaf.H` is `Stacks.Thickenings.sheafCohomologyOneExtEquiv`.
-/

@[expose] public section

universe u w

open CategoryTheory Opposite TopologicalSpace

namespace TopologicalSpace.DimensionFunction

variable {X : TopCat.{u}}

/-- First sheaf cohomology carried along an isomorphism of abelian sheaves. -/
noncomputable def sheafCohomologyOneMapIso
    {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (e : F ≅ G) :
    Stacks.Cohomology.SheafTorsor.sheafCohomologyOne.{u, u} X F ≅
      Stacks.Cohomology.SheafTorsor.sheafCohomologyOne.{u, u} X G :=
  letI : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    Stacks.Injectives.abelianSheaf_enoughInjectives X
  (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op (⊤ : Opens X))).rightDerived 1).mapIso e

/-- An isomorphism of abelian groups carries an element to zero if and only if it is zero. -/
theorem iso_hom_apply_eq_zero_iff {A B : AddCommGrpCat.{u}} (e : A ≅ B) (x : ToType A) :
    e.hom x = 0 ↔ x = 0 := by
  constructor
  · intro h
    simpa using congrArg e.inv h
  · intro h
    rw [h, map_zero]

/-- A cover by opens of a family is a cover of `⊤`. -/
theorem top_eq_iSup_of_forall_mem {I : Type*} {U : I → Opens X} (hcov : ∀ x : X, ∃ i, x ∈ U i) :
    (⊤ : Opens X) = ⨆ i, U i :=
  le_antisymm (fun x _ => Opens.mem_iSup.mpr (hcov x)) le_top

variable [QuasiSober X] [T0Space X]

/-- On one cover, two families of local dimension functions have the same obstruction class: the
discrepancy cocycles differ by the Čech coboundary of the locally constant differences
`δ i - ε i` (tag 02IB). -/
theorem obstruction_eq_obstruction (hX : IsLocallyNoetherianSpace X) {I : Type*}
    (U : I → Opens X) (δ ε : ∀ i, DimensionFunction (U i : Set X)) :
    obstruction hX U δ = obstruction hX U ε := by
  rw [obstruction, obstruction, CechCochains.cls, CechCochains.cls, QuotientAddGroup.eq,
    CechCochains.coboundaries1, AddSubgroup.mem_comap, AddMonoidHom.mem_range]
  have hlc : ∀ k : I, IsLocallyConstant (fun p : (U k : Set X) => δ k p - ε k p) := by
    intro k
    have : QuasiSober (U k : Set X) :=
      Topology.IsOpenEmbedding.quasiSober (U k).isOpen.isOpenEmbedding_subtypeVal
    exact isLocallyConstant_sub (hX.subtype _) (δ k) (ε k)
  set t : CechCochains.Cochain U (locallyConstantIntPresheaf X) 0 :=
    fun k => locallyConstantRes (CechCochains.inter_le U k 0) ⟨_, hlc (k 0)⟩ with ht
  refine ⟨t, ?_⟩
  funext i
  refine LocallyConstant.ext fun x => ?_
  have hx : ∀ k, x.1 ∈ U (i k) := fun k => CechCochains.inter_le U i k x.2
  have h0 : CechCochains.evalAt U t (i ∘ (0 : Fin 2).succAbove)
      (CechCochains.inter_le_omit U i 0 x.2) = δ (i 1) ⟨x.1, hx 1⟩ - ε (i 1) ⟨x.1, hx 1⟩ := rfl
  have h1 : CechCochains.evalAt U t (i ∘ (1 : Fin 2).succAbove)
      (CechCochains.inter_le_omit U i 1 x.2) = δ (i 0) ⟨x.1, hx 0⟩ - ε (i 0) ⟨x.1, hx 0⟩ := rfl
  change CechCochains.evalAt U (CechCochains.cechD U _ 0 t) i x.2 =
    -(δ (i 0) ⟨x.1, hx 0⟩ - δ (i 1) ⟨x.1, hx 1⟩) + (ε (i 0) ⟨x.1, hx 0⟩ - ε (i 1) ⟨x.1, hx 1⟩)
  rw [CechCochains.evalAt_cechD, Fin.sum_univ_two, h0, h1]
  norm_num
  ring

/-- Refining the cover carries the obstruction class to the obstruction class of the restricted
dimension functions. -/
theorem refinementCechH1_obstruction (hX : IsLocallyNoetherianSpace X) {I K : Type*}
    (U : I → Opens X) (V : K → Opens X) (r : K → I) (hr : ∀ k, V k ≤ U (r k))
    (δ : ∀ i, DimensionFunction (U i : Set X)) :
    CechCochains.refinementCechH1 U V r hr _ (obstruction hX U δ) =
      obstruction hX V (fun k => (δ (r k)).comp
        (isOpenEmbedding_inclusion (U (r k)).isOpen (V k).isOpen (hr k))) := by
  rw [obstruction, obstruction, CechCochains.refinementCechH1_cls]
  congr 1

/-- **The obstruction in `H¹(X, ℤ)` of a cover with local dimension functions**: the image of the
Čech obstruction class under the comparison `Ȟ¹(𝒰, ℤ) → H¹(X, ℤ)` of tag 01EQ, with coefficients
identified with the constant sheaf `ℤ`. -/
noncomputable def obstructionH1 (hX : IsLocallyNoetherianSpace X) {I : Type w} (U : I → Opens X)
    (hU : (⊤ : Opens X) = ⨆ i, U i) (δ : ∀ i, DimensionFunction (U i : Set X)) :
    ToType (Stacks.Cohomology.SheafTorsor.sheafCohomologyOne.{u, u} X
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) :=
  (sheafCohomologyOneMapIso (TopCat.constantSheafIsoLocallyConstantInt X).symm).hom
    (Stacks.Cohomology.CechOne.cechH1ToRightDerivedSections X ⊤ U hU
      (TopCat.locallyConstantIntSheaf X : TopCat.Sheaf AddCommGrpCat.{max u u} X)
      (obstruction hX U δ))

/-- The obstruction in `H¹(X, ℤ)` vanishes exactly when the Čech obstruction class does: the
comparison `Ȟ¹(𝒰, ℤ) → H¹(X, ℤ)` is injective (tag 0B8R). -/
theorem obstructionH1_eq_zero_iff (hX : IsLocallyNoetherianSpace X) {I : Type w}
    (U : I → Opens X) (hU : (⊤ : Opens X) = ⨆ i, U i) (δ : ∀ i, DimensionFunction (U i : Set X)) :
    obstructionH1 hX U hU δ = 0 ↔ obstruction hX U δ = 0 := by
  exact (iso_hom_apply_eq_zero_iff _ _).trans
    (map_eq_zero_iff _ (Stacks.Cohomology.SheafTorsor.cechH1ToRightDerivedSections_injective
      (TopCat.locallyConstantIntSheaf X : TopCat.Sheaf AddCommGrpCat.{max u u} X) U hU))

/-- **The obstruction in `H¹(X, ℤ)` is intrinsic**: it depends neither on the cover nor on the
local dimension functions. Both covers are compared on the cover by pairwise intersections, where
the comparison with `H¹` is compatible with refinement and the two restricted families have the
same Čech class. -/
theorem obstructionH1_eq (hX : IsLocallyNoetherianSpace X) {I K : Type w}
    (U : I → Opens X) (hU : (⊤ : Opens X) = ⨆ i, U i) (δ : ∀ i, DimensionFunction (U i : Set X))
    (V : K → Opens X) (hV : (⊤ : Opens X) = ⨆ k, V k)
    (ε : ∀ k, DimensionFunction (V k : Set X)) :
    obstructionH1 hX U hU δ = obstructionH1 hX V hV ε := by
  let W : I × K → Opens X := fun p => U p.1 ⊓ V p.2
  have hW : (⊤ : Opens X) = ⨆ p, W p := CechCochains.eq_iSup_inf_of_eq_iSup U hU hV
  have h₁ : ∀ p, W p ≤ U p.1 := fun _ => inf_le_left
  have h₂ : ∀ p, W p ≤ V p.2 := fun _ => inf_le_right
  have e₁ := Stacks.Cohomology.SquareZeroBoundary.cechH1ToRightDerivedSections_refinement U W
    Prod.fst h₁ hU hW
    (TopCat.locallyConstantIntSheaf X : TopCat.Sheaf AddCommGrpCat.{max u u} X)
    (obstruction hX U δ)
  have e₂ := Stacks.Cohomology.SquareZeroBoundary.cechH1ToRightDerivedSections_refinement V W
    Prod.snd h₂ hV hW
    (TopCat.locallyConstantIntSheaf X : TopCat.Sheaf AddCommGrpCat.{max u u} X)
    (obstruction hX V ε)
  rw [obstructionH1, obstructionH1]
  refine congrArg _ (e₁.symm.trans (Eq.trans ?_ e₂))
  exact congrArg _ ((refinementCechH1_obstruction hX U W Prod.fst h₁ δ).trans
    ((obstruction_eq_obstruction hX W _ _).trans
      (refinementCechH1_obstruction hX V W Prod.snd h₂ ε).symm))

/-- **The obstruction element of `H¹(X, ℤ)`** of a catenary, locally Noetherian, sober space: the
image of the obstruction class of the cover by the neighbourhoods with dimension functions of
tag 02IC. By `obstructionH1_eq` every cover with local dimension functions gives this element
(`obstructionH1_eq_dimensionObstruction`). -/
noncomputable def dimensionObstruction (hLN : IsLocallyNoetherianSpace X)
    (hCat : IsTopologicallyCatenary X) :
    ToType (Stacks.Cohomology.SheafTorsor.sheafCohomologyOne.{u, u} X
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))) :=
  obstructionH1 hLN (exists_cover_dimensionFunction hLN hCat).choose
    (top_eq_iSup_of_forall_mem fun x =>
      ⟨x, (exists_cover_dimensionFunction hLN hCat).choose_spec.choose_spec x⟩)
    (exists_cover_dimensionFunction hLN hCat).choose_spec.choose

/-- Every cover by opens carrying dimension functions computes the obstruction element. -/
theorem obstructionH1_eq_dimensionObstruction (hLN : IsLocallyNoetherianSpace X)
    (hCat : IsTopologicallyCatenary X) {I : Type u} (U : I → Opens X)
    (hU : (⊤ : Opens X) = ⨆ i, U i) (δ : ∀ i, DimensionFunction (U i : Set X)) :
    obstructionH1 hLN U hU δ = dimensionObstruction hLN hCat :=
  obstructionH1_eq hLN U hU δ _ _ _

/-- **Stacks 02ID.** On a catenary, locally Noetherian, sober topological space `X`, the
obstruction to having a dimension function is an element of `H¹(X, ℤ)`: the element
`dimensionObstruction` of first sheaf cohomology of the constant sheaf `ℤ`, which does not depend
on any choice (`obstructionH1_eq_dimensionObstruction`), vanishes if and only if `X` has a
dimension function.

The element is the image of the Čech class of the cocycle `δ i - δ j` of local dimension
functions (tags 02IC and 02IB) under the injective comparison `Ȟ¹(𝒰, ℤ) → H¹(X, ℤ)`. -/
@[stacks 02ID "the obstruction element of H¹(X, ℤ), first right-derived global sections of the \
constant sheaf ℤ, independent of all choices, vanishes iff a dimension function exists"]
theorem nonempty_dimensionFunction_iff_dimensionObstruction_eq_zero
    (hLN : IsLocallyNoetherianSpace X) (hCat : IsTopologicallyCatenary X) :
    Nonempty (DimensionFunction X) ↔ dimensionObstruction hLN hCat = 0 := by
  rw [dimensionObstruction, obstructionH1_eq_zero_iff]
  exact exists_dimensionFunction_iff_obstruction_eq_zero hLN _
    (fun x => ⟨x, (exists_cover_dimensionFunction hLN hCat).choose_spec.choose_spec x⟩) _

/-- The obstruction element in Mathlib's `Ext`-group cohomology `Sheaf.H ℤ 1`, through the
identification `Stacks.Thickenings.sheafCohomologyOneExtEquiv` of first right-derived global
sections with `Ext¹(ℤ, -)`. -/
noncomputable def dimensionObstructionExt (hLN : IsLocallyNoetherianSpace X)
    (hCat : IsTopologicallyCatenary X) :
    Sheaf.H.{u} ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) 1 :=
  (Stacks.Thickenings.sheafCohomologyOneExtEquiv X
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))).hom (dimensionObstruction hLN hCat)

/-- **Stacks 02ID**, with `H¹(X, ℤ)` read as Mathlib's `Sheaf.H`: on a catenary, locally
Noetherian, sober topological space a dimension function exists if and only if the obstruction
element of `Sheaf.H ℤ 1` vanishes. -/
@[stacks 02ID "the same statement with H¹(X, ℤ) read as Mathlib's Ext-group cohomology Sheaf.H"]
theorem nonempty_dimensionFunction_iff_dimensionObstructionExt_eq_zero
    (hLN : IsLocallyNoetherianSpace X) (hCat : IsTopologicallyCatenary X) :
    Nonempty (DimensionFunction X) ↔ dimensionObstructionExt hLN hCat = 0 := by
  exact (nonempty_dimensionFunction_iff_dimensionObstruction_eq_zero hLN hCat).trans
    (iso_hom_apply_eq_zero_iff _ _).symm

end TopologicalSpace.DimensionFunction
