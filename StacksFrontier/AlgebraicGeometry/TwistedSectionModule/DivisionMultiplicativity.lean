module

public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalar
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.InvertibleSection
public import StacksFrontier.AlgebraicGeometry.TwistedSectionModule.OpenRestriction
public import StacksFrontier.AlgebraicGeometry.SectionRingGeometric.UnitScalarSupplement

/-!
# The division by a power of a section is multiplicative

Stacks Tag 0B5I's local datum asks its comparison map to be linear over the sections of the
structure sheaf, and `Stacks.TwistedSections.localizationLiftOfDegree_smul` reduces that to one
identity about the family of divisions: dividing `a · t` by `s ^ (m + n)` must be the value of a
ring map on `a / sᵐ` times the division of `t` by `sⁿ`. **This file proves that identity**, at each
of the three levels the division is stated at, for a numerator `a` that is *itself* already
presented as `e · sᵐ` with `e` of degree zero — which is what a fraction `a / sᵐ` being in the
image of the degree-zero part amounts to.

The scalar is an endomorphism of the monoidal unit, and
`Stacks.SectionRingGeometric.unitScalarOnSite` turns it into a section of the structure sheaf. On
the slice site over an open `V` that section is a function on `V`, which is the module structure
`StandardOpenHomData.app` is asked to respect.

## Main results

* `Stacks.TwistedSections.comp_unitAct`: **the endomorphisms of the monoidal unit are central**,
  and `mulMap_unit` identifies multiplication by a degree-zero section of the section ring with
  that central action.
* `Stacks.TwistedSections.shiftBySection_unitComp`: **multiplication by `s` commutes with
  composing by an endomorphism of the monoidal unit**, and `shiftPow_unitComp` the same for the
  iterated multiplication. The degree-zero factor has to be moved past `s`, which is
  `Stacks.TwistedSections.comp_unitAct`: the endomorphisms of the monoidal unit are central, with
  no braiding.
* `Stacks.TwistedSections.powerDivision_unitComp`: dividing `e · t` by `sᵏ` is `e` times the
  division of `t`.
* `Stacks.TwistedSections.powerDivision_gsmul_unitComp`: **the multiplicativity of the
  division.** Dividing `(e · sᵐ) · t` by `s ^ (n + m)` is `e` times the division of `t` by `sⁿ`.
* `Stacks.TwistedSections.monoidalDivision_gsmul_unitComp` and
  `Stacks.TwistedSections.openDivision_gsmul_unitComp`: the same after a monoidal functor, and on
  a scheme with the quotient read as a section of `ℱ` over `V`. In the last one the scalar is a
  function on `V`, namely `Stacks.TwistedSections.sliceUnitScalar`, which is
  `Stacks.TwistedSections.sliceEndoScalar` — the function of an arbitrary endomorphism of the
  slice site's monoidal unit — at the degree-zero section carried to the slice.

## Implementation notes

**Why the degree-zero factor is a composition and not a `gsmul`.** A section of `L ^⊗ 0` is a
morphism `𝟙_ C ⟶ 𝟙_ C`, and a twisted section of degree `k` is a morphism `𝟙_ C ⟶ F ⊙ k`, so the
action of the former on the latter *is* composition, with no unitor and no transport. Writing it
as `Stacks.TwistedSections.gsmul` would put a reindexing along `0 + k = k` in front of every
statement for nothing.

**Why `e ≫ sectionPowOfDegree s m` and not an arbitrary numerator.**
`Stacks.TwistedSections.gsmul a t` for an arbitrary `a` of degree `m • d` is not a product of two
divisions: the fraction `a / sᵐ` need not be a section of the structure sheaf at all. The
hypothesis that it is one is exactly that `a` factors as `e · sᵐ` with `e` of degree zero, and that
factorisation is the input here.

**The one object-level identity avoided.** `twistPow (𝟙_ C) L k` and
`Stacks.TensorPowers.natTensorPow L k` are not definitionally equal (see the
implementation notes of `StacksFrontier/AlgebraicGeometry/TwistedSectionModule/Monoidal.lean`), so
the division of `a` by `sᵐ` is *not* available as a twisted section of the unit and the
factorisation is taken as a hypothesis rather than produced. What replaces the missing identity
is `Stacks.GradedSections.mulMap`, which is the iterated whiskering of a degree-zero section at
the tensor powers, and `Stacks.TwistedSections.actMap_comp`, which identifies it with the
iterated whiskering of the composite.

The two objects are, however, *propositionally* equal, by a two-line induction on `k` from
`Stacks.TwistedSections.twistPow_succ` and `Stacks.TensorPowers.natTensorPow_succ`. The identity
is not stated anywhere, for a stronger reason than that nothing in this file
consumes it: the factorisation of an arbitrary numerator is produced with **no division at
`F := 𝟙_`** at all. A power of an invertible section is invertible
(`Stacks.TwistedSections.isIso_sectionPow`), so after restriction to an open where `s` is
invertible the factor is `a|_V ≫ (sᵐ|_V)⁻¹`, a morphism `𝟙_ ⟶ 𝟙_` on the nose. See
`Stacks.TwistedSections.exists_sliceFactor` and
`Stacks.TwistedSections.openDivision_gsmul_chartRingMap`
(`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/ChartLinearity.lean`).

**The scalar is an honest function on `V`, and now also an honest *global* function restricted.**
`Stacks.TwistedSections.sliceUnitScalar L V e` is the restriction to `V` of
`Stacks.SectionRingGeometric.schemeUnitScalar X e`, by
`Stacks.TwistedSections.sliceUnitScalar_eq`
(`StacksFrontier/AlgebraicGeometry/TwistedSectionModule/SliceSectionBridge.lean`). That is what puts
`openDivision_gsmul_unitComp` in reach of `Stacks.SectionRingChartMap.numMap`, whose defining
identity is on restrictions of global sections, and it needs no coherence for the lax unit of the
restriction: the slice-unit bridge differs from restriction of global sections by one invertible
factor, which cancels.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory DirectSum
open Stacks.GradedSections (powSections mul mulMap sectionRing HasTrivialSelfBraiding powCongr)
open Stacks.TensorPowers (natTensorPow)

universe w v u

namespace Stacks.TwistedSections

/-! ### An arbitrary monoidal category -/

section Central

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]


/-- **The action of an endomorphism of the monoidal unit on an object**, by the left unit
constraint. -/
def unitAct (e : 𝟙_ C ⟶ 𝟙_ C) (B : C) : B ⟶ B :=
  (λ_ B).inv ≫ e ▷ B ≫ (λ_ B).hom

/-- Whiskering an endomorphism of the unit by the unit itself is conjugation by the unit
constraint: the two unitors of `𝟙_ C` agree. -/
theorem leftUnitor_inv_comp_whiskerRight_unit (e : 𝟙_ C ⟶ 𝟙_ C) :
    (λ_ (𝟙_ C)).inv ≫ e ▷ (𝟙_ C) = e ≫ (λ_ (𝟙_ C)).inv := by
  simp [unitors_inv_equal]

/-- **The endomorphisms of the monoidal unit are central.** Composing a morphism out of the unit
with the action of `e` is the same as precomposing it with `e`. This is Eckmann–Hilton: one
instance of `CategoryTheory.MonoidalCategory.whisker_exchange` and the naturality of the unit
constraint, with no braiding. -/
theorem comp_unitAct (e : 𝟙_ C ⟶ 𝟙_ C) {B : C} (f : 𝟙_ C ⟶ B) :
    f ≫ unitAct e B = e ≫ f := by
  rw [unitAct, ← Category.assoc, leftUnitor_inv_naturality, Category.assoc,
    whisker_exchange_assoc, ← Category.assoc, leftUnitor_inv_comp_whiskerRight_unit]
  simp

/-- The action of an endomorphism of the unit on the unit is itself. -/
theorem unitAct_unit (e : 𝟙_ C ⟶ 𝟙_ C) : unitAct e (𝟙_ C) = e := by
  simpa using comp_unitAct e (𝟙 (𝟙_ C))

/-- The action is compatible with whiskering: acting on `B ⊗ L` is acting on `B`. -/
theorem unitAct_whiskerRight (e : 𝟙_ C ⟶ 𝟙_ C) (B L : C) :
    unitAct e B ▷ L = unitAct e (B ⊗ L) := by
  rw [unitAct, unitAct]
  simp

/-- **Multiplication by a degree-zero section is the action of that endomorphism of the unit.**
`Stacks.GradedSections.mulMap e j` whiskers `e` by `j` copies of `L`, and `unitAct_whiskerRight`
says that is the action on the `j`-th tensor power. -/
theorem mulMap_unit (L : C) (e : powSections L 0) : ∀ j : ℕ,
    mulMap e j = unitAct e (natTensorPow L j) ≫ powCongr L (Nat.zero_add j).symm
  | 0 => by
      rw [Stacks.GradedSections.mulMap_zero]
      change e = unitAct e (𝟙_ C) ≫ 𝟙 _
      exact (unitAct_unit e).symm.trans (Category.comp_id _).symm
  | j + 1 => by
      have hw : unitAct e (natTensorPow L j) ▷ L = unitAct e (natTensorPow L (j + 1)) :=
        unitAct_whiskerRight e (natTensorPow L j) L
      rw [Stacks.GradedSections.mulMap_succ, mulMap_unit L e j, comp_whiskerRight,
        hw, Stacks.GradedSections.powCongr_whiskerRight L
          (Nat.zero_add j).symm (Nat.zero_add (j + 1)).symm]
      rfl

/-- **A degree-zero section can be moved past a section of any tensor power.** The left side is
the product `e · s` and the right side the product `s · e`, and no braiding is needed for it:
multiplication by a degree-zero section is the action of a central endomorphism of the unit. -/
theorem comp_mulMap_unit {d : ℕ} {L : C} (s : powSections L d) (e : powSections L 0) :
    s ≫ mulMap e d = (e ≫ s) ≫ powCongr L (Nat.add_comm d 0) := by
  rw [mulMap_unit L e d, ← Category.assoc]
  exact eq_whisker (comp_unitAct e s) _

end Central

section Abstract

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {F L : C}
  [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive]


omit [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive] in
/-- Reindexing the degree commutes with composing by an endomorphism of the monoidal unit:
both are compositions, so this is associativity. -/
theorem twistCongr_unitComp {m m' : ℕ} (h : m = m') (e : powSections L 0)
    (y : twistSections F L m) :
    twistCongr h (e ≫ y) = e ≫ twistCongr h y := by
  rw [twistCongr, twistCongr]
  exact Category.assoc _ _ _

omit [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive] in
/-- **Multiplication by `s` commutes with composing by a degree-zero section.** The iterated
whiskering of `e ≫ y` splits as the iterated whiskering of `e` — which is
`Stacks.GradedSections.mulMap e` — followed by that of `y`, and the first factor is then moved
past `s` by `comp_mulMap_unit`. -/
theorem shiftBySection_unitComp {d : ℕ} (s : powSections L d) (e : powSections L 0) {m : ℕ}
    (y : twistSections F L m) :
    shiftBySection s (e ≫ y) = e ≫ shiftBySection s y := by
  have key : actMap (e ≫ y) d =
      mulMap e d ≫ actMap y (0 + d) ≫
        eqToHom (congrArg (twistPow F L) (Nat.add_assoc m 0 d).symm) :=
    actMap_comp e y d
  rw [shiftBySection_eq, shiftBySection_eq, key, ← Category.assoc, comp_mulMap_unit]
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans (whisker_eq e ?_))
  rw [eqToHom_comp_actMap_assoc y (Nat.add_comm d 0) (eqToHom
      (congrArg (twistPow F L) (Nat.add_assoc m 0 d).symm))]
  simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

omit [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive] in
/-- **The `k`-fold multiplication by `s` commutes with composing by a degree-zero section.** -/
theorem shiftPow_unitComp {d : ℕ} (s : powSections L d) (e : powSections L 0) (k : ℕ)
    (u : twistSections F L 0) :
    shiftPow s k (e ≫ u) = e ≫ shiftPow s (F := F) k u := by
  induction k with
  | zero => rfl
  | succ k ih => rw [shiftPow_succ, shiftPow_succ, ih, shiftBySection_unitComp]

/-- **Dividing `e · t` by `sᵏ` is `e` times the division of `t`**, for `e` of degree zero. The
division is the inverse of the `k`-fold multiplication, which commutes with `e`. -/
theorem powerDivision_unitComp {d : ℕ} (s : powSections L d) [IsIso s] (k : ℕ)
    (e : powSections L 0) (w : twistSections F L (d * k)) :
    powerDivision s k (e ≫ w) = e ≫ powerDivision s (F := F) k w :=
  (bijective_shiftPow s (F := F) k).injective (by
    rw [shiftPow_powerDivision, shiftPow_unitComp, shiftPow_powerDivision])

/-- Dividing the `m`-fold multiplication of `t` by `s ^ (n + m)` is dividing `t` by `sⁿ`. -/
private theorem powerDivision_twistCongr_shiftIter {d : ℕ} (s : powSections L d) [IsIso s]
    (n m : ℕ) (t : twistSections F L (d * n)) :
    powerDivision s (n + m)
        (twistCongr ((Nat.add_comm (d * n) (d * m)).trans (mul_add_degree d n m))
          (shiftIter s t m))
      = powerDivision s n t := by
  have h := isPowerInvariant_powerDivision s (F := F) n m t
  rwa [gsmul_sectionPow_eq_shiftIter, twistCongr_trans] at h

/-- The numerator `(e · sᵐ) · t` is the `m`-fold multiplication of `e ≫ t` by `s`. -/
private theorem gsmul_unitComp_sectionPowOfDegree {d : ℕ} (s : powSections L d) (m : ℕ)
    (e : powSections L 0) (n : ℕ) (t : twistSections F L (d * n)) :
    gsmul (e ≫ sectionPowOfDegree s m) t
      = twistCongr (Nat.add_comm (d * n) (d * m)) (e ≫ shiftIter s t m) := by
  rw [gsmul_def, shiftIter_eq_actMap]
  exact congrArg (twistCongr _) (Category.assoc _ _ _)

/-- **The multiplicativity of the division, in the iterated-multiplication spelling.** Dividing
`e · sᵐ · t` by `s ^ (n + m)` is `e` times the division of `t` by `sⁿ`: the `e` comes out by
`powerDivision_unitComp`, and what is left is the power-invariance
`Stacks.TwistedSections.isPowerInvariant_powerDivision`. -/
theorem powerDivision_unitComp_shiftIter {d : ℕ} (s : powSections L d) [IsIso s] (n m : ℕ)
    (e : powSections L 0) (t : twistSections F L (d * n)) :
    powerDivision s (n + m)
        (twistCongr ((Nat.add_comm (d * n) (d * m)).trans (mul_add_degree d n m))
          (e ≫ shiftIter s t m))
      = e ≫ powerDivision s n t := by
  rw [twistCongr_unitComp, powerDivision_unitComp, powerDivision_twistCongr_shiftIter]

/-- **The multiplicativity of the division.** For a numerator presented as `(e · sᵐ) · t` with `e`
of degree zero, dividing by `s ^ (n + m)` is `e` times the division of `t` by `sⁿ`. This is the
identity `Stacks.TwistedSections.localizationLiftOfDegree_smul` asks for, with the scalar still an
endomorphism of the monoidal unit. -/
theorem powerDivision_gsmul_unitComp {d : ℕ} (s : powSections L d) [IsIso s] (n m : ℕ)
    (e : powSections L 0) (t : twistSections F L (d * n)) :
    powerDivision s (n + m)
        (twistCongr (mul_add_degree d n m) (gsmul (e ≫ sectionPowOfDegree s m) t))
      = e ≫ powerDivision s n t := by
  rw [gsmul_unitComp_sectionPowOfDegree, twistCongr_trans]
  exact powerDivision_unitComp_shiftIter s n m e t

end Abstract

/-! ### After a monoidal functor -/

section Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type*} [Category D] [MonoidalCategory D] (G : C ⥤ D) [G.Monoidal]
  {F L : C} [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive]
  [Preadditive D] [G.Additive]
  [(_root_.CategoryTheory.MonoidalCategory.tensorRight (G.obj L)).Additive]


omit [Preadditive C] [(_root_.CategoryTheory.MonoidalCategory.tensorRight L).Additive]
  [Preadditive D] [G.Additive]
  [(_root_.CategoryTheory.MonoidalCategory.tensorRight (G.obj L)).Additive] in
/-- **Carrying a twisted section along `G` commutes with composing by a degree-zero section.**
The lax unit of `G` and its oplax counit cancel against each other, which is
`CategoryTheory.Functor.Monoidal.η_ε`. -/
theorem mapTwistSections_unitComp (e : powSections L 0) {m : ℕ} (w : twistSections F L m) :
    mapTwistSections G (e ≫ w) = mapPowSections G e ≫ mapTwistSections G w := by
  rw [mapTwistSections, mapTwistSections, mapPowSections, Functor.map_comp G e w]
  refine (whisker_eq _ (Category.assoc _ _ _)).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine whisker_eq _ (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine whisker_eq _ ?_
  exact ((Category.id_comp _).symm.trans (eq_whisker (Functor.Monoidal.η_ε G).symm _)).trans
    (Category.assoc _ _ _)

/-- **The multiplicativity of the division after a monoidal functor.** The scalar is the
degree-zero section carried along `G`. -/
theorem monoidalDivision_gsmul_unitComp {d : ℕ} (s : powSections L d)
    [IsIso (mapPowSections G s)] (n m : ℕ) (e : powSections L 0)
    (t : twistSections F L (d * n)) :
    monoidalDivision G s (n + m)
        (twistCongr (mul_add_degree d n m) (gsmul (e ≫ sectionPowOfDegree s m) t))
      = mapPowSections G e ≫ monoidalDivision G s (F := F) n t := by
  rw [monoidalDivision_apply, monoidalDivision_apply, gsmul_unitComp_sectionPowOfDegree,
    twistCongr_trans, mapTwistSections_twistCongr, mapTwistSections_unitComp,
    mapTwistSections_shiftIter, twistCongr_unitComp, powerDivision_unitComp,
    powerDivision_twistCongr_shiftIter]

end Monoidal

/-! ### On a scheme, with the quotient read as a section over an open -/

section Scheme

open AlgebraicGeometry Opposite
open Stacks.SheafInternalHom.SliceRestriction (schemeOpenRestriction schemeOverFunctorMonoidal
  schemeOpenUnitHomAddEquiv)
open Stacks.SheafOfModules.SliceRestriction (sliceRingPresheaf isSheaf_sliceRingPresheaf)
open Stacks.SectionProduct (globalSection)
open Stacks.GradedSections (powSections)

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive
  Stacks.SectionRingGeometric.presheafMonoidalPreadditiveStructure
  Stacks.SectionRingGeometric.sheafifyAdditive
  Stacks.SectionRingGeometric.tensorLeftAdditive
  Stacks.SectionRingGeometric.tensorRightAdditive
  Stacks.SheafInternalHom.SliceRestriction.schemeOverFunctorMonoidal

variable {X : Scheme.{u}}

/-- **An endomorphism of the monoidal unit of the modules on the slice site over `V`, read as a
function on `V`.** `Stacks.SectionRingGeometric.unitScalarOnSite` reads such an endomorphism as a
section of the structure sheaf over the terminal object `V ⟶ V` of the slice site, which is a
function on `V`. The module `L` names the type of the argument and nothing else: a section of the
zeroth tensor power is a morphism `𝟙_ ⟶ 𝟙_` whatever `L` is. -/
def sliceEndoScalar (L : X.Modules) (V : X.Opens)
    (e : powSections ((schemeOpenRestriction X V).obj L) 0) : Γ(X, V) :=
  Stacks.SectionRingGeometric.unitScalarOnSite (sliceRingPresheaf X.presheaf V)
    (isSheaf_sliceRingPresheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V)
    (Over.mk (𝟙 V)) e

/-- **A degree-zero section of the section ring, read as a function on an open `V`.** It is an
endomorphism of the monoidal unit of `X.Modules`; restricting it to the slice site over `V` gives
an endomorphism of the monoidal unit there, and
`Stacks.TwistedSections.sliceEndoScalar` reads that as a function on `V`. -/
def sliceUnitScalar (L : X.Modules) (V : X.Opens) (e : powSections L 0) : Γ(X, V) :=
  sliceEndoScalar L V (mapPowSections (schemeOpenRestriction X V) e)

/-- **The multiplicativity of the division over an open, with the scalar a function on that open.**
This is piece (iii) of Stacks Tag 0B5I's local datum — the 𝒪-linearity — in the shape
`Stacks.TwistedSections.localizationLiftOfDegree_smul` consumes, for a numerator presented as
`e · sᵐ` with `e` of degree zero: the division over `V` of `(e · sᵐ) · t` by `s ^ (n + m)` is the
function `sliceUnitScalar` of `e` times the division of `t` by `sⁿ`.

The scalar comes out as a function and not merely as an endomorphism because
`Stacks.SectionRingGeometric.globalSection_unitComp_onSite` is stated for an arbitrary terminal
object of an arbitrary site, and the slice site over `V` has `V ⟶ V` as one. -/
theorem openDivision_gsmul_unitComp (F L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (s : powSections L d) (V : X.Opens)
    (hV : V ≤ Stacks.NonvanishingOpen.nonvanishingOpen X (Stacks.TensorPowers.natTensorPow L d)
      (globalSection X _ s))
    (n m : ℕ) (e : powSections L 0) (t : twistSections F L (d * n)) :
    openDivision F L s V hV (n + m)
        (twistCongr (mul_add_degree d n m) (gsmul (e ≫ sectionPowOfDegree s m) t))
      = sliceUnitScalar L V e • openDivision F L s V hV n t := by
  have := isIso_mapPowSections_openRestriction L s hV
  change schemeOpenUnitHomAddEquiv V F
      (monoidalDivision (schemeOpenRestriction X V) s (n + m) _) = _
  rw [monoidalDivision_gsmul_unitComp (schemeOpenRestriction X V) s n m e t]
  exact Stacks.SectionRingGeometric.globalSection_unitComp_onSite (sliceRingPresheaf X.presheaf V)
    (isSheaf_sliceRingPresheaf X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) V)
    Over.mkIdTerminal (mapPowSections (schemeOpenRestriction X V) e)
    (monoidalDivision (schemeOpenRestriction X V) s n t)

end Scheme

end Stacks.TwistedSections

end
